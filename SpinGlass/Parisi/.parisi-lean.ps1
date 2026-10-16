param([Parameter(ValueFromRemainingArguments=$true)][string[]]$TaskArgs)

# Locate the repository independently of the caller's working directory.
$taskRepoRoot = (Resolve-Path -LiteralPath (Join-Path $PSScriptRoot '../..') -ErrorAction Stop).Path
$taskPackagesRoot = Join-Path $taskRepoRoot '../.lake/spinglass/packages'
$taskGitDirs=@($taskRepoRoot.Replace('\','/')) + @(Get-ChildItem -LiteralPath $taskPackagesRoot -Directory -ErrorAction Stop | ForEach-Object { $_.FullName.Replace('\','/') })
$env:GIT_CONFIG_COUNT=[string]$taskGitDirs.Count
for ($taskIndex=0; $taskIndex -lt $taskGitDirs.Count; $taskIndex++) {
  [Environment]::SetEnvironmentVariable("GIT_CONFIG_KEY_$taskIndex",'safe.directory','Process')
  [Environment]::SetEnvironmentVariable("GIT_CONFIG_VALUE_$taskIndex",$taskGitDirs[$taskIndex],'Process')
}
Push-Location -LiteralPath $taskRepoRoot
try {
  & 'C:/Users/shuta/.elan/toolchains/leanprover--lean4---v4.34.0-rc2/bin/lake.exe' @TaskArgs
  $taskLakeExitCode = $LASTEXITCODE
}
finally {
  Pop-Location
}
exit $taskLakeExitCode
