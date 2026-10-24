@echo off
rem Builds installer\LettucePlayerSetup.exe, one file to give people. Run from anywhere: installer\make_installer.bat
rem It builds the app (build.bat), packs it in two parts, the app and voice control (Vosk's library and speech model,
rem about 120 MB), and wraps them with setup (install.ps1) using IExpress, which comes with Windows. Setup asks whether
rem to install voice; without it, the app hides its voice button.
setlocal
cd /d "%~dp0.."
set "STAGE=%~dp0staging"
set "OUT=%~dp0LettucePlayerSetup.exe"

call "%~dp0..\build.bat"
if errorlevel 1 exit /b 1

if exist "%STAGE%" rmdir /s /q "%STAGE%"
mkdir "%STAGE%"
set "VOSKINFO="
for /d %%d in ("_internal\vosk-*.dist-info") do set "VOSKINFO=_internal/%%~nxd"
if not defined VOSKINFO (
    echo Vosk isn't in the build, so there is no voice control to offer.
    exit /b 1
)

rem Windows' own tar writes zip files (-a picks the format from the name)
echo Packing the app...
"%windir%\System32\tar.exe" -a -c -f "%STAGE%\app.zip" --exclude "_internal/vosk" --exclude "_internal/vosk_model" --exclude "%VOSKINFO%" LettucePlayer.exe _internal assets User_Music
if errorlevel 1 goto failed
echo Packing voice control...
"%windir%\System32\tar.exe" -a -c -f "%STAGE%\voice.zip" _internal/vosk _internal/vosk_model "%VOSKINFO%"
if errorlevel 1 goto failed
copy /y installer\install.ps1 "%STAGE%" >nul
copy /y installer\uninstall.ps1 "%STAGE%" >nul
copy /y assets\LettucePlayer.ico "%STAGE%" >nul

rem the IExpress recipe: unpack these files to a temp folder, then run setup with its console window hidden
(
echo [Version]
echo Class=IEXPRESS
echo SEDVersion=3
echo [Options]
echo PackagePurpose=InstallApp
echo ShowInstallProgramWindow=1
echo HideExtractAnimation=0
echo UseLongFileName=1
echo InsideCompressed=0
echo CAB_FixedSize=0
echo CAB_ResvCodeSigning=0
echo RebootMode=N
echo InstallPrompt=%%InstallPrompt%%
echo DisplayLicense=%%DisplayLicense%%
echo FinishMessage=%%FinishMessage%%
echo TargetName=%%TargetName%%
echo FriendlyName=%%FriendlyName%%
echo AppLaunched=%%AppLaunched%%
echo PostInstallCmd=%%PostInstallCmd%%
echo AdminQuietInstCmd=%%AdminQuietInstCmd%%
echo UserQuietInstCmd=%%UserQuietInstCmd%%
echo SourceFiles=SourceFiles
echo [Strings]
echo InstallPrompt=
echo DisplayLicense=
echo FinishMessage=
echo TargetName=%OUT%
echo FriendlyName=Lettuce Player Setup
echo AppLaunched=powershell.exe -NoProfile -ExecutionPolicy Bypass -WindowStyle Hidden -File install.ps1
echo PostInstallCmd=^<None^>
echo AdminQuietInstCmd=
echo UserQuietInstCmd=
echo FILE0="install.ps1"
echo FILE1="uninstall.ps1"
echo FILE2="app.zip"
echo FILE3="voice.zip"
echo FILE4="LettucePlayer.ico"
echo [SourceFiles]
echo SourceFiles0=%STAGE%\
echo [SourceFiles0]
echo %%FILE0%%=
echo %%FILE1%%=
echo %%FILE2%%=
echo %%FILE3%%=
echo %%FILE4%%=
) > "%STAGE%\setup.sed"

rem no /Q: IExpress fails in quiet mode, so its progress window shows while it works
echo Making the setup file (this takes a couple of minutes)...
if exist "%OUT%" del "%OUT%"
rem IExpress can't open a directive file whose path is in quotes ("Error opening the IExpress Self Extraction Directive
rem file"), and an unquoted path breaks on spaces: so it's run from the staging folder, given just the file's name
pushd "%STAGE%"
start "" /wait "%windir%\System32\iexpress.exe" /N setup.sed
popd
if not exist "%OUT%" goto failed
rmdir /s /q "%STAGE%"
echo Built %OUT%
exit /b 0

:failed
echo Making the installer failed.
exit /b 1
