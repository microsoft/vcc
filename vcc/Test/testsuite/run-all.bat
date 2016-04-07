setlocal
cd %~dp0
..\..\Host\bin\debug\vcc.exe /smoke /s /time /smt:0.7 vcc3 examples3 vacid-0 old_tutorial ..\..\Demo ..\..\Docs\Tutorial\c
