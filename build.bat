@echo off
rem Builds LettucePlayer.exe next to User_Music. Run from anywhere: build.bat
cd /d "%~dp0"

taskkill /IM LettucePlayer.exe /F >nul 2>&1

rem --onedir: the app's files sit in _internal beside the exe, so it opens in under a second. A --onefile exe has to
rem unpack all of them to a temp folder on every launch, which took 4 to 5 seconds
Scripts\python.exe -m PyInstaller --noconfirm --onedir --windowed --name LettucePlayer --icon "%~dp0assets\LettucePlayer.ico" --add-data "%~dp0assets\LettucePlayer.ico;assets" --add-data "%~dp0audio_engine;audio_engine" --add-data "%~dp0vosk_model;vosk_model" --collect-all vosk --distpath dist --workpath build --specpath build speechVLC2.py
if errorlevel 1 (
    echo Build failed.
    exit /b 1
)

rem the exe needs its _internal folder next to it, so both are copied (the old _internal goes first)
copy /y dist\LettucePlayer\LettucePlayer.exe LettucePlayer.exe >nul
if exist _internal rmdir /s /q _internal
xcopy /e /i /q /y dist\LettucePlayer\_internal _internal >nul
rmdir /s /q dist build
echo Built %~dp0LettucePlayer.exe (keep the _internal folder beside it)
