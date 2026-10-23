# Lettuce Player setup. IExpress unpacks this with app.zip (and voice.zip) into a temp folder and runs it.
# Installs for the current user only, so no admin rights are needed and the app can save its data next to itself.
# Your data (data\ and User_Music\) is never touched by a reinstall or an upgrade.
#
# Without a window:  install.ps1 -Quiet [-Target <folder>] [-NoVoice] [-NoDesktop] [-NoShortcuts]
#   -NoShortcuts also leaves out the Settings > Apps entry: just the files, e.g. a portable copy
param([switch]$Quiet, [string]$Target = (Join-Path $env:LOCALAPPDATA 'Programs\LettucePlayer'),
      [switch]$NoVoice, [switch]$NoDesktop, [switch]$NoShortcuts)
$ErrorActionPreference = 'Stop'
Add-Type -AssemblyName System.Windows.Forms, System.Drawing
$here = $PSScriptRoot

function Unzip($zip, $folder) {
    # Windows' own tar reads zip files and is far quicker than Expand-Archive
    $tar = Join-Path $env:windir 'System32\tar.exe'
    if (Test-Path $tar) {
        $p = Start-Process $tar -ArgumentList '-xf', "`"$zip`"", '-C', "`"$folder`"" -Wait -PassThru -WindowStyle Hidden
        if ($p.ExitCode -eq 0) { return }
    }
    Expand-Archive -LiteralPath $zip -DestinationPath $folder -Force
}

function Install-LettucePlayer($folder, $voice, $desktop, $shortcuts, $say) {
    $folder = [IO.Path]::GetFullPath($folder).TrimEnd('\') # as the uninstaller will see it, to know its own entry
    $exe = Join-Path $folder 'LettucePlayer.exe'
    New-Item -ItemType Directory -Force -Path $folder | Out-Null

    & $say 'Copying Lettuce Player...'
    # program files only: an old version's leftovers go, and so does voice when it isn't chosen this time
    $internal = Join-Path $folder '_internal'
    if (Test-Path $internal) { Remove-Item -Recurse -Force $internal }
    Unzip (Join-Path $here 'app.zip') $folder
    if ($voice) {
        & $say 'Copying voice control...'
        Unzip (Join-Path $here 'voice.zip') $folder
    }
    Copy-Item (Join-Path $here 'uninstall.ps1') (Join-Path $folder 'uninstall.ps1') -Force
    if (-not $shortcuts) { return }

    & $say 'Making shortcuts...'
    $shell = New-Object -ComObject WScript.Shell
    $links = @(Join-Path ([Environment]::GetFolderPath('Programs')) 'Lettuce Player.lnk')
    $desktopLink = Join-Path ([Environment]::GetFolderPath('Desktop')) 'Lettuce Player.lnk'
    if ($desktop) { $links += $desktopLink } elseif (Test-Path $desktopLink) { Remove-Item $desktopLink }
    foreach ($path in $links) {
        $link = $shell.CreateShortcut($path)
        $link.TargetPath = $exe
        $link.WorkingDirectory = $folder
        $link.IconLocation = "$exe,0"
        $link.Description = 'Lettuce Player'
        $link.Save()
    }

    # the uninstaller, listed in Settings > Apps
    $key = 'HKCU:\Software\Microsoft\Windows\CurrentVersion\Uninstall\LettucePlayer'
    New-Item -Path $key -Force | Out-Null
    $size = [int]((Get-ChildItem $folder -Recurse -File -ErrorAction SilentlyContinue | Measure-Object Length -Sum).Sum / 1KB)
    $values = @{
        DisplayName = 'Lettuce Player'; DisplayIcon = "$exe,0"; Publisher = 'Aaron M. Leonhard'; InstallLocation = $folder
        UninstallString = "powershell.exe -NoProfile -ExecutionPolicy Bypass -WindowStyle Hidden -File `"$folder\uninstall.ps1`""
    }
    foreach ($name in $values.Keys) { Set-ItemProperty -Path $key -Name $name -Value $values[$name] }
    foreach ($name in 'NoModify', 'NoRepair') { Set-ItemProperty -Path $key -Name $name -Value 1 -Type DWord }
    Set-ItemProperty -Path $key -Name EstimatedSize -Value $size -Type DWord
}

function Close-Running($folder, $ask) {
    $exe = Join-Path $folder 'LettucePlayer.exe'
    $running = Get-Process LettucePlayer -ErrorAction SilentlyContinue | Where-Object { $_.Path -eq $exe }
    if (-not $running) { return $true }
    if ($ask -and [Windows.Forms.MessageBox]::Show('Lettuce Player is open. Close it to continue?', 'Lettuce Player Setup',
                                                   'OKCancel', 'Question') -ne 'OK') { return $false }
    $running | Stop-Process -Force
    Start-Sleep -Milliseconds 800
    return $true
}

if ($Quiet) {
    if (-not (Close-Running $Target $false)) { exit 1 }
    Install-LettucePlayer $Target (-not $NoVoice) (-not $NoDesktop) (-not $NoShortcuts) { param($text) Write-Host $text }
    Write-Host "Installed to $Target"
    exit 0
}

# ---- the window ----------------------------------------------------------------------------------------------------
[Windows.Forms.Application]::EnableVisualStyles()
$form = New-Object Windows.Forms.Form
$form.Text = 'Lettuce Player Setup'
$form.ClientSize = New-Object Drawing.Size(460, 268)
$form.FormBorderStyle = 'FixedDialog'
$form.MaximizeBox = $false
$form.StartPosition = 'CenterScreen'
$form.Font = New-Object Drawing.Font('Segoe UI', 9)
$icon = Join-Path $here 'LettucePlayer.ico'
if (Test-Path $icon) { $form.Icon = New-Object Drawing.Icon($icon) }

function Add($control, $x, $y, $w, $h) {
    $control.Location = New-Object Drawing.Point($x, $y)
    $control.Size = New-Object Drawing.Size($w, $h)
    $form.Controls.Add($control)
    $control
}

$title = Add (New-Object Windows.Forms.Label) 20 16 420 28
$title.Text = 'Lettuce Player'
$title.Font = New-Object Drawing.Font('Segoe UI', 14, [Drawing.FontStyle]::Bold)

$folderLabel = Add (New-Object Windows.Forms.Label) 20 56 420 18
$folderLabel.Text = 'Install to:'
$folder = Add (New-Object Windows.Forms.TextBox) 20 76 330 24
$folder.Text = $Target
$browse = Add (New-Object Windows.Forms.Button) 358 75 82 26
$browse.Text = 'Browse...'
$browse.Add_Click({
    $dialog = New-Object Windows.Forms.FolderBrowserDialog
    $dialog.Description = 'Choose where to install Lettuce Player (a LettucePlayer folder is made inside it)'
    if ($dialog.ShowDialog() -eq 'OK') { $folder.Text = Join-Path $dialog.SelectedPath 'LettucePlayer' }
})

$voice = Add (New-Object Windows.Forms.CheckBox) 20 116 420 22
$voice.Text = 'Voice control (Vosk offline speech-to-text, about 120 MB more)'
$voice.Checked = -not $NoVoice
$voiceNote = Add (New-Object Windows.Forms.Label) 38 138 400 18
$voiceNote.Text = 'Lets you say "play <song>", "next", "pause" and more. Needs a microphone.'
$voiceNote.ForeColor = [Drawing.Color]::DimGray
$desktop = Add (New-Object Windows.Forms.CheckBox) 20 164 420 22
$desktop.Text = 'Desktop shortcut'
$desktop.Checked = -not $NoDesktop

$status = Add (New-Object Windows.Forms.Label) 20 200 240 40
$install = Add (New-Object Windows.Forms.Button) 270 224 82 30
$install.Text = 'Install'
$cancel = Add (New-Object Windows.Forms.Button) 358 224 82 30
$cancel.Text = 'Cancel'
$cancel.Add_Click({ $form.Close() })
$form.AcceptButton = $install
$form.CancelButton = $cancel

$install.Add_Click({
    $target = $folder.Text.Trim()
    $buttons = $install, $cancel, $browse
    try {
        if (-not (Close-Running $target $true)) { return }
        $buttons | ForEach-Object { $_.Enabled = $false }
        $form.Cursor = 'WaitCursor'
        Install-LettucePlayer $target $voice.Checked $desktop.Checked $true { param($text) $status.Text = $text; [Windows.Forms.Application]::DoEvents() }
        $form.Cursor = 'Default'
        $status.Text = ''
        $answer = [Windows.Forms.MessageBox]::Show("Lettuce Player is installed.`n`nOpen it now?", 'Lettuce Player Setup', 'YesNo', 'Information')
        if ($answer -eq 'Yes') { Start-Process (Join-Path $target 'LettucePlayer.exe') -WorkingDirectory $target }
        $form.Close()
    }
    catch {
        $form.Cursor = 'Default'
        $status.Text = ''
        [Windows.Forms.MessageBox]::Show("Setup didn't finish: $($_.Exception.Message)", 'Lettuce Player Setup', 'OK', 'Error') | Out-Null
        $buttons | ForEach-Object { $_.Enabled = $true }
    }
})

[void]$form.ShowDialog()
