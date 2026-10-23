# Lettuce Player uninstaller, run from Settings > Apps. Removes only what setup put there (and, if you say so, your
# data), never anything else that happens to be in the folder.
# Without questions:  uninstall.ps1 -Quiet [-KeepData]
param([switch]$Quiet, [switch]$KeepData)
Add-Type -AssemblyName System.Windows.Forms
$dir = $PSScriptRoot
$exe = Join-Path $dir 'LettucePlayer.exe'
$title = 'Uninstall Lettuce Player'

$keepData = [bool]$KeepData
if (-not $Quiet) {
    if ([Windows.Forms.MessageBox]::Show("Remove Lettuce Player from`n$dir ?", $title, 'OKCancel', 'Question') -ne 'OK') { exit }
    $keepData = [Windows.Forms.MessageBox]::Show(
        "Keep your library, playlists, stations, settings and the User_Music folder?`n`n(Yes keeps them for a later reinstall.)",
        $title, 'YesNo', 'Question') -eq 'Yes'
}

Get-Process LettucePlayer -ErrorAction SilentlyContinue | Where-Object { $_.Path -eq $exe } | Stop-Process -Force
Start-Sleep -Milliseconds 800
Set-Location $env:TEMP # out of the folder, so it can go

$items = 'LettucePlayer.exe', '_internal', 'assets', 'uninstall.ps1'
if (-not $keepData) { $items += 'data', 'User_Music' }
foreach ($item in $items) {
    $path = Join-Path $dir $item
    if (Test-Path $path) { Remove-Item -LiteralPath $path -Recurse -Force -ErrorAction SilentlyContinue }
}
if (-not (Get-ChildItem $dir -Force -ErrorAction SilentlyContinue)) { Remove-Item -LiteralPath $dir -Force -ErrorAction SilentlyContinue }

# shortcuts and the Settings > Apps entry go only if they are this copy's (another copy may be installed elsewhere)
$shell = New-Object -ComObject WScript.Shell
foreach ($link in (Join-Path ([Environment]::GetFolderPath('Programs')) 'Lettuce Player.lnk'),
                  (Join-Path ([Environment]::GetFolderPath('Desktop')) 'Lettuce Player.lnk')) {
    if ((Test-Path $link) -and $shell.CreateShortcut($link).TargetPath -eq $exe) { Remove-Item $link -Force }
}
$key = 'HKCU:\Software\Microsoft\Windows\CurrentVersion\Uninstall\LettucePlayer'
if ((Get-ItemProperty $key -ErrorAction SilentlyContinue).InstallLocation -eq $dir) { Remove-Item $key -Recurse -Force }

if (-not $Quiet) { [Windows.Forms.MessageBox]::Show('Lettuce Player was removed.', $title, 'OK', 'Information') | Out-Null }
