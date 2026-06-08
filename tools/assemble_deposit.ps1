<#
assemble_deposit.ps1 - assemble the disposable deposit/ for a Zenodo version.

What it does (all reversible, nothing published):
  1. Wipes and rebuilds <repo>/deposit/ from an EXPLICIT manifest of canonical
     files (root docs/licences/metadata + src/ + lean/ source, scaffolding excluded).
  2. Regenerates deposit/SHA256SUMS.txt over every deposited file.
  3. Runs tools/validate_metadata.py against the assembled deposit (using the
     org-wide frozen boilerplate one level above the repo).
  4. STOPS. It never mints, pushes, tags, or contacts Zenodo. Minting a new
     version under the concept DOI is an operator-gated action done by hand.

The deposit/ tree is disposable: .gitignored except .gitkeep, assembled fresh
here, and safe to delete after the mint.

Usage:
    pwsh tools/assemble_deposit.ps1            # assemble + validate
    pwsh tools/assemble_deposit.ps1 -KeepOld   # do not wipe deposit/ first
#>
[CmdletBinding()]
param(
    [switch]$KeepOld
)

$ErrorActionPreference = 'Stop'

# --- locate the repo root (this script lives in <repo>/tools/) ---
$repo = (Resolve-Path (Join-Path $PSScriptRoot '..')).Path
$deposit = Join-Path $repo 'deposit'
$boiler = Join-Path (Split-Path $repo -Parent) '_boilerplate\disclosures.md'

Write-Host "repo     = $repo"
Write-Host "deposit  = $deposit"
Write-Host "boiler   = $boiler"

# --- EXPLICIT manifest: only these ship. Add new artifacts here, by hand. ---
$rootFiles = @(
    'delta_characterization.pdf',
    'delta_characterization.tex',
    'README.md',
    'METADATA.yml',
    'claims.jsonl',
    'COVER_LETTER.md',
    'CITATION.cff',
    '.zenodo.json',
    'LICENSE',
    'LICENSE-CODE'
)
$treeDirs = @('src', 'lean')   # copied recursively, then scaffolding pruned

# scaffolding that must never enter a deposit even if present in a tree dir
$pruneDirs  = @('.git', '.lake', 'build', '__pycache__', '.venv')
$pruneGlobs = @('*.olean', '*.pyc', '*.aux', '*.log', '*.out', '*.fls',
                '*.fdb_latexmk', '*.synctex.gz', '.DS_Store', 'Thumbs.db')

# --- 1. (re)create deposit/ ---
if (-not $KeepOld -and (Test-Path $deposit)) {
    Get-ChildItem $deposit -Force | Where-Object { $_.Name -ne '.gitkeep' } |
        Remove-Item -Recurse -Force
}
New-Item -ItemType Directory -Force -Path $deposit | Out-Null

# --- copy root files (verify each exists; a missing canonical file is fatal) ---
$missing = @()
foreach ($f in $rootFiles) {
    $src = Join-Path $repo $f
    if (Test-Path $src) {
        Copy-Item $src (Join-Path $deposit $f) -Force
    } else {
        $missing += $f
    }
}
if ($missing.Count) {
    throw "Missing canonical files (will NOT ship an incomplete deposit): $($missing -join ', ')"
}

# --- copy tree dirs, EXCLUDING scaffolding at copy time (robocopy /XD /XF) so the
#     regenerable bulk -- e.g. lean/.lake holds 120k+ Mathlib oleans -- is never
#     materialized into deposit/ in the first place. The prune loops below remain as
#     a fast belt-and-suspenders pass over the (now small) copied tree. ---
foreach ($d in $treeDirs) {
    $src = Join-Path $repo $d
    if (-not (Test-Path $src)) { throw "Missing tree dir: $d" }
    $dst = Join-Path $deposit $d
    New-Item -ItemType Directory -Force -Path $dst | Out-Null
    & robocopy $src $dst /E /XD @pruneDirs /XF @pruneGlobs `
        /NFL /NDL /NJH /NJS /NC /NS /NP | Out-Null
    # robocopy success is exit code 0-7; 8+ is a genuine failure.
    if ($LASTEXITCODE -ge 8) { throw "robocopy failed copying $d (exit $LASTEXITCODE)" }
    $global:LASTEXITCODE = 0
}
foreach ($pd in $pruneDirs) {
    Get-ChildItem $deposit -Recurse -Force -Directory -ErrorAction SilentlyContinue |
        Where-Object { $_.Name -eq $pd } | Remove-Item -Recurse -Force -ErrorAction SilentlyContinue
}
foreach ($pg in $pruneGlobs) {
    Get-ChildItem $deposit -Recurse -Force -File -Filter $pg -ErrorAction SilentlyContinue |
        Remove-Item -Force -ErrorAction SilentlyContinue
}

# --- 2. regenerate SHA256SUMS.txt (relative POSIX paths; excludes itself) ---
$sumsPath = Join-Path $deposit 'SHA256SUMS.txt'
Remove-Item $sumsPath -Force -ErrorAction SilentlyContinue
$lines = New-Object System.Collections.Generic.List[string]
Get-ChildItem $deposit -Recurse -File -Force |
    Where-Object { $_.Name -notin @('SHA256SUMS.txt', '.gitkeep') } |
    Sort-Object FullName |
    ForEach-Object {
        $rel = $_.FullName.Substring($deposit.Length + 1).Replace('\', '/')
        $h = (Get-FileHash $_.FullName -Algorithm SHA256).Hash.ToLower()
        $lines.Add("$h  $rel")
    }
[IO.File]::WriteAllText($sumsPath, ($lines -join "`n") + "`n", [Text.UTF8Encoding]::new($false))
Write-Host ("SHA256SUMS.txt: {0} files hashed (this is the authoritative upload manifest)" -f $lines.Count)

# --- 3. validate the assembled deposit ---
Write-Host "`n--- validating assembled deposit ---"
$py = (Get-Command python -ErrorAction SilentlyContinue)
if (-not $py) { throw "python not found on PATH; cannot run validator." }
& python (Join-Path $repo 'tools\validate_metadata.py') `
    --project $deposit --boilerplate $boiler
$rc = $LASTEXITCODE

Write-Host ""
if ($rc -ne 0) {
    Write-Host "*** DEPOSIT VALIDATION FAILED (exit $rc) - do NOT mint. ***"
    exit $rc
}

# --- 4. package the deposit as a single self-verifying zip ---
# Built strictly from SHA256SUMS.txt so nothing extra (.gitkeep, stray builds) can
# enter; the manifest itself is included so the archive is self-verifying. Files sit
# under a single top-level folder pcf-delta-v<version>/ matching the manifest paths.
$metaText = Get-Content (Join-Path $repo 'METADATA.yml') -Raw
$verMatch = [regex]::Match($metaText, '(?m)^version:\s*"?([0-9]+\.[0-9]+)"?')
if (-not $verMatch.Success) { throw "Could not read version from METADATA.yml" }
$ver = $verMatch.Groups[1].Value
$top = "pcf-delta-v$ver"
$zipStage = Join-Path ([IO.Path]::GetTempPath()) $top
$zipPath  = Join-Path $deposit "$top.zip"
Remove-Item $zipStage -Recurse -Force -ErrorAction SilentlyContinue
Remove-Item $zipPath  -Force -ErrorAction SilentlyContinue
New-Item -ItemType Directory -Force -Path $zipStage | Out-Null

$zn = 0
foreach ($line in Get-Content $sumsPath) {
    if (-not $line.Trim()) { continue }
    $rel = ($line -split '  ', 2)[1].Trim()
    $src = Join-Path $deposit ($rel -replace '/', '\')
    $dst = Join-Path $zipStage ($rel -replace '/', '\')
    New-Item -ItemType Directory -Force -Path (Split-Path $dst) | Out-Null
    Copy-Item $src $dst -Force
    $zn++
}
Copy-Item $sumsPath (Join-Path $zipStage 'SHA256SUMS.txt') -Force
Compress-Archive -Path $zipStage -DestinationPath $zipPath -CompressionLevel Optimal

# self-verify: extract to temp and re-hash against the bundled manifest
$zver = Join-Path ([IO.Path]::GetTempPath()) "$top-verify"
Remove-Item $zver -Recurse -Force -ErrorAction SilentlyContinue
Expand-Archive -Path $zipPath -DestinationPath $zver -Force
$zbase = Join-Path $zver $top
$zbad = 0
foreach ($line in Get-Content (Join-Path $zbase 'SHA256SUMS.txt')) {
    if (-not $line.Trim()) { continue }
    $sp = $line -split '  ', 2
    $f = Join-Path $zbase ($sp[1].Trim() -replace '/', '\')
    if (-not (Test-Path $f) -or
        (Get-FileHash $f -Algorithm SHA256).Hash.ToLower() -ne $sp[0].Trim()) { $zbad++ }
}
Remove-Item $zipStage, $zver -Recurse -Force -ErrorAction SilentlyContinue
if ($zbad -ne 0) { throw "Zip self-verify FAILED: $zbad file(s) mismatch." }
$zipHash = (Get-FileHash $zipPath -Algorithm SHA256).Hash.ToLower()
Write-Host ("zip: {0} ({1} content files + SHA256SUMS.txt; {2:N0} bytes)" -f `
    (Split-Path $zipPath -Leaf), $zn, (Get-Item $zipPath).Length)
Write-Host "zip SHA-256: $zipHash"

# --- 5. STOP: report, do not mint ---
Write-Host ""
Write-Host "Deposit assembled, validated, and packaged at: $deposit"
Write-Host ""
Write-Host "NEXT (operator-gated, by hand - this script does NOT do these):"
Write-Host "  * Upload deposit/$top.zip  (or the individual files in deposit/SHA256SUMS.txt)."
Write-Host "    Do NOT upload deposit/.gitkeep - it is a git placeholder, not deposit content."
Write-Host "  * On Zenodo, open concept 10.5281/zenodo.20578400 -> 'New version',"
Write-Host "    upload deposit/ contents, confirm METADATA.yml fields, then Publish."
Write-Host "  * The v$ver version DOI is minted by that Publish action."
Write-Host "  * After publish: record the v$ver version DOI in CITATION.cff, .zenodo.json,"
Write-Host "    METADATA.yml, INDEX.md; commit; then 'SIARC_OPERATOR=1 git push' and"
Write-Host "    push the v$ver tag."
exit 0
