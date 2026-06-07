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

# --- copy tree dirs, then prune scaffolding ---
foreach ($d in $treeDirs) {
    $src = Join-Path $repo $d
    if (-not (Test-Path $src)) { throw "Missing tree dir: $d" }
    Copy-Item $src (Join-Path $deposit $d) -Recurse -Force
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

# --- 4. STOP: report, do not mint ---
Write-Host "Deposit assembled and validated at: $deposit"
Write-Host ""
Write-Host "NEXT (operator-gated, by hand - this script does NOT do these):"
Write-Host "  * Upload exactly the files listed in deposit/SHA256SUMS.txt."
Write-Host "    Do NOT upload deposit/.gitkeep - it is a git placeholder, not deposit content."
Write-Host "  * On Zenodo, open concept 10.5281/zenodo.20578400 -> 'New version',"
Write-Host "    upload deposit/ contents, confirm METADATA.yml fields, then Publish."
Write-Host "  * The v1.1 version DOI is minted by that Publish action."
Write-Host "  * After publish: record the v1.1 version DOI in CITATION.cff, .zenodo.json,"
Write-Host "    METADATA.yml, INDEX.md; commit; then 'SIARC_OPERATOR=1 git push' and"
Write-Host "    push the v1.1 tag."
exit 0
