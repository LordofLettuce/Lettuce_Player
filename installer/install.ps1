# Lettuce Player setup. IExpress unpacks this with app.zip (and voice.zip) into a temp folder and runs it.
# Installs for the current user only, so no admin rights are needed and the app can save its data next to itself.
# Your data (data\ and User_Music\) is never touched by a reinstall or an upgrade, except that the language picked
# here is written into data\settings.json (the app's other settings there stay as they are).
#
# Without a window:  install.ps1 -Quiet [-Target <folder>] [-Language en|ang|es|zh|ja|de|fr] [-NoVoice] [-NoDesktop] [-NoShortcuts]
#   -NoShortcuts also leaves out the Settings > Apps entry: just the files, e.g. a portable copy
# (Saved as UTF-8 with a byte order mark: Windows PowerShell needs it to read the languages' letters below)
param([switch]$Quiet, [string]$Target = (Join-Path $env:LOCALAPPDATA 'Programs\LettucePlayer'), [string]$Language = '',
      [switch]$NoVoice, [switch]$NoDesktop, [switch]$NoShortcuts)
$ErrorActionPreference = 'Stop'
Add-Type -AssemblyName System.Windows.Forms, System.Drawing
$here = $PSScriptRoot

# ---- languages: the app's (translations.py has its words), and setup's own words in each --------------------------
$Languages = [ordered]@{ en = 'English'; ang = 'Ænglisc (Old English)'; es = 'Español'; zh = '中文 (简体)'; ja = '日本語'; de = 'Deutsch'; fr = 'Français' }
$Words = @{
    en  = @{ Title = 'Lettuce Player Setup'; Language = 'Language:'; InstallTo = 'Install to:'; Browse = 'Browse...'
             Choose = 'Choose where to install Lettuce Player (a LettucePlayer folder is made inside it)'
             Voice = 'Voice control (Vosk offline speech-to-text, about 120 MB more)'
             VoiceNote = 'Lets you say "play <song>", "next", "pause" and more. Needs a microphone.'
             Desktop = 'Desktop shortcut'; Install = 'Install'; Cancel = 'Cancel'
             Copying = 'Copying Lettuce Player...'; CopyingVoice = 'Copying voice control...'; Shortcuts = 'Making shortcuts...'
             Open = 'Lettuce Player is open. Close it to continue?'; Done = "Lettuce Player is installed.`n`nOpen it now?"
             Failed = "Setup didn't finish: " }
    ang = @{ Title = 'Lēacplegeres Gesetnes'; Language = 'Gereord:'; InstallTo = 'Sete on:'; Browse = 'Sēc...'
             Choose = 'Ceos hwǣr Lēacplegere sceal bēon geset (LettucePlayer hord biþ þǣrinne geworht)'
             Voice = 'Stefnwealdung (Vosk, būtan nette, ymbe 120 MB mā)'
             VoiceNote = 'Þū miht secgan "play <song>", "next", "pause" and mā, on Englisc. Behōfaþ stefnhlystan.'
             Desktop = 'Bend on bēode'; Install = 'Sete'; Cancel = 'Forlǣt'
             Copying = 'Ēoweþ Lēacplegere...'; CopyingVoice = 'Ēoweþ stefnwealdunge...'; Shortcuts = 'Wyrcþ bendas...'
             Open = 'Lēacplegere is open. Belūc hine tō gānne forþ?'; Done = "Lēacplegere is geset.`n`nOpenian hine nū?"
             Failed = 'Gesetnes ne geendode: ' }
    es  = @{ Title = 'Instalación de Lettuce Player'; Language = 'Idioma:'; InstallTo = 'Instalar en:'; Browse = 'Examinar...'
             Choose = 'Elige dónde instalar Lettuce Player (se crea una carpeta LettucePlayer dentro)'
             Voice = 'Control por voz (Vosk, sin conexión, unos 120 MB más)'
             VoiceNote = 'Di "play <song>", "next", "pause" y más, en inglés. Necesita un micrófono.'
             Desktop = 'Acceso directo en el escritorio'; Install = 'Instalar'; Cancel = 'Cancelar'
             Copying = 'Copiando Lettuce Player...'; CopyingVoice = 'Copiando el control por voz...'; Shortcuts = 'Creando accesos directos...'
             Open = 'Lettuce Player está abierto. ¿Cerrarlo para continuar?'; Done = "Lettuce Player está instalado.`n`n¿Abrirlo ahora?"
             Failed = 'La instalación no terminó: ' }
    zh  = @{ Title = 'Lettuce Player 安装'; Language = '语言：'; InstallTo = '安装到：'; Browse = '浏览...'
             Choose = '选择 Lettuce Player 的安装位置（会在其中创建 LettucePlayer 文件夹）'
             Voice = '语音控制（Vosk 离线语音识别，约多占 120 MB）'
             VoiceNote = '可以说 "play <song>"、"next"、"pause" 等英文命令。需要麦克风。'
             Desktop = '桌面快捷方式'; Install = '安装'; Cancel = '取消'
             Copying = '正在复制 Lettuce Player...'; CopyingVoice = '正在复制语音控制...'; Shortcuts = '正在创建快捷方式...'
             Open = 'Lettuce Player 正在运行。关闭它以继续？'; Done = "Lettuce Player 已安装。`n`n现在打开吗？"
             Failed = '安装未完成：' }
    ja  = @{ Title = 'Lettuce Player セットアップ'; Language = '言語:'; InstallTo = 'インストール先:'; Browse = '参照...'
             Choose = 'Lettuce Player のインストール先を選んでください（中に LettucePlayer フォルダーが作られます）'
             Voice = '音声操作（Vosk のオフライン音声認識、約 120 MB 追加）'
             VoiceNote = '"play <song>"、"next"、"pause" などを英語で言えます。マイクが必要です。'
             Desktop = 'デスクトップにショートカット'; Install = 'インストール'; Cancel = 'キャンセル'
             Copying = 'Lettuce Player をコピー中...'; CopyingVoice = '音声操作をコピー中...'; Shortcuts = 'ショートカットを作成中...'
             Open = 'Lettuce Player が開いています。閉じて続けますか？'; Done = "Lettuce Player をインストールしました。`n`n今すぐ開きますか？"
             Failed = 'セットアップが完了しませんでした: ' }
    de  = @{ Title = 'Lettuce Player einrichten'; Language = 'Sprache:'; InstallTo = 'Installieren in:'; Browse = 'Durchsuchen...'
             Choose = 'Wähl, wohin Lettuce Player installiert wird (darin entsteht ein Ordner LettucePlayer)'
             Voice = 'Sprachsteuerung (Vosk, offline, etwa 120 MB mehr)'
             VoiceNote = 'Sag "play <song>", "next", "pause" und mehr, auf Englisch. Braucht ein Mikrofon.'
             Desktop = 'Verknüpfung auf dem Desktop'; Install = 'Installieren'; Cancel = 'Abbrechen'
             Copying = 'Lettuce Player wird kopiert...'; CopyingVoice = 'Sprachsteuerung wird kopiert...'; Shortcuts = 'Verknüpfungen werden angelegt...'
             Open = 'Lettuce Player ist geöffnet. Zum Fortfahren schließen?'; Done = "Lettuce Player ist installiert.`n`nJetzt öffnen?"
             Failed = 'Die Einrichtung wurde nicht abgeschlossen: ' }
    fr  = @{ Title = 'Installation de Lettuce Player'; Language = 'Langue :'; InstallTo = 'Installer dans :'; Browse = 'Parcourir...'
             Choose = "Choisissez où installer Lettuce Player (un dossier LettucePlayer y est créé)"
             Voice = 'Commande vocale (Vosk, hors ligne, environ 120 Mo de plus)'
             VoiceNote = 'Dites "play <song>", "next", "pause" et plus, en anglais. Il faut un micro.'
             Desktop = 'Raccourci sur le bureau'; Install = 'Installer'; Cancel = 'Annuler'
             Copying = 'Copie de Lettuce Player...'; CopyingVoice = 'Copie de la commande vocale...'; Shortcuts = 'Création des raccourcis...'
             Open = "Lettuce Player est ouvert. Le fermer pour continuer ?"; Done = "Lettuce Player est installé.`n`nL'ouvrir maintenant ?"
             Failed = "L'installation n'a pas abouti : " }
}

function Settings-Path($folder) { Join-Path $folder 'data\settings.json' }

function Default-Language($folder) {
    # an earlier install's choice, else the language Windows is in when the app speaks it, else English
    try {
        $saved = (Get-Content -Raw -Encoding UTF8 (Settings-Path $folder) | ConvertFrom-Json).language
        if ($Languages.Contains($saved)) { return $saved }
    } catch { }
    $windows = [Globalization.CultureInfo]::CurrentUICulture.TwoLetterISOLanguageName
    if ($Languages.Contains($windows)) { return $windows }
    return 'en'
}

function Save-Language($folder, $language) {
    # into the app's settings, keeping whatever else is saved there. Written without a byte order mark: the app's
    # JSON reader doesn't accept one
    $path = Settings-Path $folder
    New-Item -ItemType Directory -Force -Path (Split-Path $path) | Out-Null
    $settings = New-Object PSObject
    if (Test-Path $path) { try { $settings = Get-Content -Raw -Encoding UTF8 $path | ConvertFrom-Json } catch { } }
    $settings | Add-Member -NotePropertyName language -NotePropertyValue $language -Force
    [IO.File]::WriteAllText($path, ($settings | ConvertTo-Json -Depth 5), (New-Object Text.UTF8Encoding $false))
}

function Unzip($zip, $folder) {
    # Windows' own tar reads zip files and is far quicker than Expand-Archive
    $tar = Join-Path $env:windir 'System32\tar.exe'
    if (Test-Path $tar) {
        $p = Start-Process $tar -ArgumentList '-xf', "`"$zip`"", '-C', "`"$folder`"" -Wait -PassThru -WindowStyle Hidden
        if ($p.ExitCode -eq 0) { return }
    }
    Expand-Archive -LiteralPath $zip -DestinationPath $folder -Force
}

function Install-LettucePlayer($folder, $language, $voice, $desktop, $shortcuts, $say) {
    $folder = [IO.Path]::GetFullPath($folder).TrimEnd('\') # as the uninstaller will see it, to know its own entry
    $exe = Join-Path $folder 'LettucePlayer.exe'
    $w = $Words[$language]
    New-Item -ItemType Directory -Force -Path $folder | Out-Null

    & $say $w.Copying
    # program files only: an old version's leftovers go, and so does voice when it isn't chosen this time
    $internal = Join-Path $folder '_internal'
    if (Test-Path $internal) { Remove-Item -Recurse -Force $internal }
    Unzip (Join-Path $here 'app.zip') $folder
    if ($voice) {
        & $say $w.CopyingVoice
        Unzip (Join-Path $here 'voice.zip') $folder
    }
    Copy-Item (Join-Path $here 'uninstall.ps1') (Join-Path $folder 'uninstall.ps1') -Force
    Save-Language $folder $language
    if (-not $shortcuts) { return }

    & $say $w.Shortcuts
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

function Close-Running($folder, $ask, $language) {
    $exe = Join-Path $folder 'LettucePlayer.exe'
    $running = Get-Process LettucePlayer -ErrorAction SilentlyContinue | Where-Object { $_.Path -eq $exe }
    if (-not $running) { return $true }
    $w = $Words[$language]
    if ($ask -and [Windows.Forms.MessageBox]::Show($w.Open, $w.Title, 'OKCancel', 'Question') -ne 'OK') { return $false }
    $running | Stop-Process -Force
    Start-Sleep -Milliseconds 800
    return $true
}

if ($Quiet) {
    if (-not $Languages.Contains($Language)) { $Language = Default-Language $Target }
    if (-not (Close-Running $Target $false $Language)) { exit 1 }
    Install-LettucePlayer $Target $Language (-not $NoVoice) (-not $NoDesktop) (-not $NoShortcuts) { param($text) Write-Host $text }
    Write-Host "Installed to $Target"
    exit 0
}

# ---- the window ----------------------------------------------------------------------------------------------------
[Windows.Forms.Application]::EnableVisualStyles()
$form = New-Object Windows.Forms.Form
$form.ClientSize = New-Object Drawing.Size(460, 318)
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

# step one: the language, for the app and for the rest of this window ($languageBox: PowerShell's names ignore case,
# so $language would be the -Language parameter)
$languageLabel = Add (New-Object Windows.Forms.Label) 20 56 420 18
$languageBox = Add (New-Object Windows.Forms.ComboBox) 20 76 220 24
$languageBox.DropDownStyle = 'DropDownList'
$codes = @($Languages.Keys)
foreach ($code in $codes) { [void]$languageBox.Items.Add($Languages[$code]) }

$folderLabel = Add (New-Object Windows.Forms.Label) 20 112 420 18
$folder = Add (New-Object Windows.Forms.TextBox) 20 132 320 24
$folder.Text = $Target
$browse = Add (New-Object Windows.Forms.Button) 348 131 92 26 # (room for the longest word, German's)
$browse.Add_Click({
    $dialog = New-Object Windows.Forms.FolderBrowserDialog
    $dialog.Description = $Words[$codes[$languageBox.SelectedIndex]].Choose
    if ($dialog.ShowDialog() -eq 'OK') { $folder.Text = Join-Path $dialog.SelectedPath 'LettucePlayer' }
})

$voice = Add (New-Object Windows.Forms.CheckBox) 20 170 420 22
$voice.Checked = -not $NoVoice
$voiceNote = Add (New-Object Windows.Forms.Label) 38 192 404 32
$voiceNote.ForeColor = [Drawing.Color]::DimGray
$desktop = Add (New-Object Windows.Forms.CheckBox) 20 226 420 22
$desktop.Checked = -not $NoDesktop

$status = Add (New-Object Windows.Forms.Label) 20 262 240 40
$install = Add (New-Object Windows.Forms.Button) 250 274 92 30
$cancel = Add (New-Object Windows.Forms.Button) 348 274 92 30
$cancel.Add_Click({ $form.Close() })
$form.AcceptButton = $install
$form.CancelButton = $cancel

function Show-Words {
    # every word in the window in the chosen language
    $w = $Words[$codes[$languageBox.SelectedIndex]]
    $form.Text = $w.Title
    $languageLabel.Text = $w.Language
    $folderLabel.Text = $w.InstallTo
    $browse.Text = $w.Browse
    $voice.Text = $w.Voice
    $voiceNote.Text = $w.VoiceNote
    $desktop.Text = $w.Desktop
    $install.Text = $w.Install
    $cancel.Text = $w.Cancel
}
$languageBox.SelectedIndex = [Array]::IndexOf($codes, (Default-Language $Target))
Show-Words
$languageBox.Add_SelectedIndexChanged({ Show-Words })

$install.Add_Click({
    $target = $folder.Text.Trim()
    $code = $codes[$languageBox.SelectedIndex]
    $w = $Words[$code]
    $controls = $install, $cancel, $browse, $languageBox
    try {
        if (-not (Close-Running $target $true $code)) { return }
        $controls | ForEach-Object { $_.Enabled = $false }
        $form.Cursor = 'WaitCursor'
        Install-LettucePlayer $target $code $voice.Checked $desktop.Checked $true { param($text) $status.Text = $text; [Windows.Forms.Application]::DoEvents() }
        $form.Cursor = 'Default'
        $status.Text = ''
        $answer = [Windows.Forms.MessageBox]::Show($w.Done, $w.Title, 'YesNo', 'Information')
        if ($answer -eq 'Yes') { Start-Process (Join-Path $target 'LettucePlayer.exe') -WorkingDirectory $target }
        $form.Close()
    }
    catch {
        $form.Cursor = 'Default'
        $status.Text = ''
        [Windows.Forms.MessageBox]::Show("$($w.Failed)$($_.Exception.Message)", $w.Title, 'OK', 'Error') | Out-Null
        $controls | ForEach-Object { $_.Enabled = $true }
    }
})

[void]$form.ShowDialog()
