param(
  [Parameter(ValueFromRemainingArguments = $true)]
  [string[]]$LakeArguments
)

$repositoryRoot = Split-Path -Parent $PSScriptRoot
$elanHome = Join-Path $repositoryRoot ".tools\elan-home"
$lakeExecutable = Join-Path $elanHome "bin\lake.exe"

if (-not (Test-Path -LiteralPath $lakeExecutable)) {
  throw "Project-local Lake executable was not found: $lakeExecutable"
}

$env:ELAN_HOME = $elanHome
& $lakeExecutable @LakeArguments
exit $LASTEXITCODE
