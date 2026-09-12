param(
  [ValidateSet('start','stop','status')]
  [string]$Action = 'status'
)

$hub = Split-Path -Parent $PSScriptRoot
$statePath = Join-Path $PSScriptRoot 'LOOP_CONTROL.json'
$bus = 'C:\Users\kross\Documents\Codex\mca-research1'

if(-not (Test-Path $bus)) { throw "Canonical bus not found: $bus" }

if(Test-Path $statePath) {
  $state = Get-Content -Raw $statePath | ConvertFrom-Json
} else {
  $state = [pscustomobject]@{ mode='STOPPED'; updatedAt=$null; canonicalBus=$bus; automation='grand-mca-codex-research-controller' }
}

if($Action -eq 'start') { $state.mode = 'ACTIVE' }
if($Action -eq 'stop') { $state.mode = 'STOPPED' }
$state.updatedAt = (Get-Date).ToUniversalTime().ToString('o')
$state | ConvertTo-Json -Depth 4 | Set-Content -Encoding UTF8 $statePath

"Mode: $($state.mode)"
"Canonical bus: $($state.canonicalBus)"
"Automation: $($state.automation)"
if($Action -eq 'start') { "Next: Scheduled -> Run now, or continue the main Codex task." }
if($Action -eq 'stop') { "Next: pause the automation in Scheduled to stop unattended runs." }
