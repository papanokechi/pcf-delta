<#
.SYNOPSIS
  Deposit gate: refuses to report a deposit finished while ANY tracked file is
  uncommitted, or while the commits that carry them are unpushed.

.DESCRIPTION
  A version bump that exists only in a working tree has not happened.
  Neither has a proof, a manuscript, or a data file.

  This is the forward rule for step 3 of WALKTHROUGH_NEXT: pcf-delta's
  repository metadata said v1.3 for seven weeks while Zenodo served v1.4,
  because the corrected files were written, never committed, and nothing in
  the deposit procedure looked.

  SCOPE CORRECTION (2026-08-02). The first version of this gate checked four
  named version-bearing files. It was wired into assemble_deposit.ps1, whose
  zip carries 45 entries -- lean/, src/, the PDF, claims.jsonl, COVER_LETTER.md,
  LICENSE. Every one of those was outside the gate's scope. It would have
  returned 0, printing "Deposit gate: clean", over a deposit containing
  uncommitted proofs. Its per-line message was honest ("Version files
  committed") but its NAME, its exit code and its call site all asserted
  deposit-wide coverage it did not have. The demonstrating case is real:
  349 uncommitted lines of HermitePade.lean sat in the tree the same morning.

  A gate's scope must cover what its call site claims it covers. The whole
  tree is now checked; the four version files are still reported separately,
  because "your version bump is uncommitted" is a more useful diagnostic than
  "something is uncommitted".

  Call this BEFORE the success report in tools\assemble_deposit.ps1 -- not
  appended after it, and never after a terminal `exit`:

      & "$PSScriptRoot\check_deposit_clean.ps1" -RepoPath "$PSScriptRoot\.."
      if ($LASTEXITCODE -ne 0) { Write-Error "deposit not finished"; exit $LASTEXITCODE }

  Exit codes:
    0  clean       - working tree clean AND on the remote
    1  dirty       - some tracked path is uncommitted, staged or untracked
    2  unpushed    - committed but not on the remote
    3  CANNOT RUN  - not a git repo, detached HEAD, or origin/<branch> missing

  Exit 3 is deliberately distinct from exit 0. A gate that cannot run must not
  be indistinguishable from a gate that passed.

  -VersionFiles narrows only the SUPPLEMENTARY report, never the enforcement.
  -AllowPaths excludes paths from enforcement; use it explicitly and sparingly,
  and it is echoed on every run so an exclusion cannot be silent.
#>
[CmdletBinding()]
param(
    [string]   $RepoPath     = ".",
    [string[]] $VersionFiles = @("METADATA.yml", ".zenodo.json", "CITATION.cff", "README.md"),
    [string[]] $AllowPaths   = @(),
    [switch]   $WarnOnly
)

$ErrorActionPreference = 'Continue'
$repo = (Resolve-Path $RepoPath -ErrorAction SilentlyContinue)
if (-not $repo) { Write-Host "  GATE CANNOT RUN: path not found: $RepoPath"; exit 3 }

git -C $repo rev-parse --git-dir *> $null
if ($LASTEXITCODE -ne 0) { Write-Host "  GATE CANNOT RUN: not a git repository: $repo"; exit 3 }

# --- 1. NOTHING may be uncommitted -------------------------------------------
# Scope is the whole working tree, not a named list. The call site says
# "deposit", the zip carries every tracked file, so the gate must too.
# --porcelain already excludes .gitignored paths, so deposit/ does not self-trip.
$allDirty = @(git -C $repo status --porcelain 2>$null | Where-Object { $_ })

if ($AllowPaths.Count -gt 0) {
    Write-Host "  NOTE: $($AllowPaths.Count) path(s) excluded from enforcement by -AllowPaths:"
    $AllowPaths | ForEach-Object { Write-Host "    $_" }
    $allDirty = @($allDirty | Where-Object {
        $path = $_.Substring(3).Trim('"')
        -not ($AllowPaths | Where-Object { $path -like $_ })
    })
}

$dirty = @($allDirty)
if ($dirty.Count -gt 0) {
    Write-Host "  DEPOSIT NOT FINISHED - $($dirty.Count) path(s) uncommitted:"
    $dirty | ForEach-Object { Write-Host "    $_" }

    # Supplementary, more actionable diagnostic. Narrows the REPORT, never the check.
    $vf = @($dirty | Where-Object { $p = $_.Substring(3).Trim('"'); $VersionFiles -contains $p })
    if ($vf.Count -gt 0) {
        Write-Host "  Of these, $($vf.Count) are version-bearing (METADATA/zenodo/CITATION/README)."
        Write-Host "  A version bump that exists only in a working tree has not happened."
    } else {
        Write-Host "  Version files are committed, but deposit content is not."
        Write-Host "  The zip would carry bytes that exist in no commit."
    }
    if (-not $WarnOnly) { exit 1 }
}

# --- 2. and pushed ------------------------------------------------------------
# Compare against origin/<branch> explicitly. @{u} exits 128 on a branch with no
# tracking config, and pcf-delta's main is exactly such a branch -- a check
# written against @{u} would fail open on the repo it was written for.
$branch = (git -C $repo rev-parse --abbrev-ref HEAD 2>$null)
if (-not $branch -or $branch -eq "HEAD") {
    Write-Host "  GATE CANNOT RUN: detached HEAD - no branch to compare against."
    exit 3
}

git -C $repo rev-parse --verify --quiet "refs/remotes/origin/$branch" *> $null
if ($LASTEXITCODE -ne 0) {
    Write-Host "  GATE CANNOT RUN: origin/$branch does not exist locally. Run: git fetch origin"
    exit 3
}

$ahead = (git -C $repo rev-list --count "origin/$branch..HEAD" 2>$null)
if ([int]$ahead -gt 0) {
    Write-Host "  DEPOSIT NOT FINISHED - $ahead commit(s) not on origin/$branch."
    Write-Host "  Push before treating the deposit as complete (operator: SIARC_OPERATOR=1)."
    if (-not $WarnOnly) { exit 2 }
}

if ($dirty.Count -eq 0 -and [int]$ahead -eq 0) {
    $n = (git -C $repo ls-files | Measure-Object).Count
    Write-Host "  Deposit gate: clean. $n tracked path(s) committed and on origin/$branch."
    exit 0
}
exit 0
