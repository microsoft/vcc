#!/bin/sh
r="
...
540940
"


for f in $r ; do
 tf get /version:C$f
 rm -rf c:/felt/vcc2/vcc2host/bin/debug/*
 devenv.com c:/felt/Vcc2.sln /rebuild Debug
 rm -rf $f
 mkdir $f
 mkdir $f/bin
 cp -r c:/felt/vcc2/vcc2host/bin/debug/* $f/bin
 cp -r c:/felt/vcc2/headers $f
done
