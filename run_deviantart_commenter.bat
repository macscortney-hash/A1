@echo off
setlocal
cd /d "%~dp0"

set "PYTHON_EXE="
where python >nul 2>nul
if not errorlevel 1 set "PYTHON_EXE=python"
if "%PYTHON_EXE%"=="" (
  echo Python not found.
  pause
  exit /b 1
)

rem Kill anything already listening on 8796 first — an old python.exe left
rem running in the background (console closed via the X button instead of
rem Ctrl+C, or just hung) would otherwise keep serving its OLD in-memory copy
rem of this script forever: the check below sees *a* server already
rem answering on the port and opens the browser against that stale zombie
rem instead of the freshly-started one, silently discarding every code
rem change (including anything you just edited) and any impression that a
rem "restart" actually restarted something.
for /f "tokens=5" %%p in ('netstat -ano ^| findstr /R /C:"LISTENING" ^| findstr ":8796 "') do (
  taskkill /F /PID %%p >nul 2>nul
)

start "" powershell -NoProfile -WindowStyle Hidden -Command "for($i=0;$i -lt 30;$i++){try{$r=Invoke-WebRequest -UseBasicParsing 'http://127.0.0.1:8796' -TimeoutSec 1; if($r.StatusCode -eq 200){Start-Process 'http://localhost:8796'; break}}catch{}; Start-Sleep -Seconds 1}"

"%PYTHON_EXE%" -u "%~dp0deviantart_commenter_gui.py"
pause
