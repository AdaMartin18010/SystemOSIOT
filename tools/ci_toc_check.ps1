Param(
  [int]$MaxLevel = 4,
  [int]$Workers = 8
)

Write-Host "[CI] Running TOC validation..."
python tools/toc_validate.py --max-level $MaxLevel --workers $Workers
if ($LASTEXITCODE -ne 0) {
  Write-Error "[CI] TOC validation failed"
  exit 2
}
Write-Host "[CI] TOC validation passed"
exit 0


