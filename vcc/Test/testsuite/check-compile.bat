@echo off
setlocal
set HEADERS=%~dp0\..\..\Headers
for /r . %%C in (*.c) do (
  echo Compiling %%C
  cd /d %%~dpC
  cl.exe /nologo /c /I%HEADERS% %%~nxC
  if errorlevel 1 echo ERROR&exit /b 1
  del %%~nC.obj
)
