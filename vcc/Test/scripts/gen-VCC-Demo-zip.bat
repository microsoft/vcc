@echo off

setlocal
where /q hg
if errorlevel 1 echo ?Can't find hg command.&exit /b 1

cd %~dp0
if errorlevel 1 echo ?Can't change directory to script directory.&exit /b 1

call hg root >NUL:

if not "%ERRORLEVEL%" == "0" echo ?'hg root' returned an error.&exit /b 1

for /f "tokens=*" %%D in ('hg root') do cd /d %%~D

call hg archive -I vcc\Demo VCC_Demo.zip

if not "%ERRORLEVEL%" == "0" echo ?'hg archive' returned an error.&exit /b 1

dir VCC_Demo.zip
