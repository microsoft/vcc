#!/bin/sh

opts=$1
shift

if test -f "$opts" || test $# = 0 ; then
  echo "USAGE: $0 \"options\" file1.c file2.c ..."
  exit
fi

mkdir -p sx
for f in "$@" ; do
  vcc2 /st /b:/proverLog:sx/$(basename $f .c)-@FUNC@.sx $opts $f
done

chmod 644 sx/*.sx
perl -n -i -e 'if (/^\(LET/) { print "(DBG_VALID $_)\r\n" } else { print }' sx/*.sx
rm -f sx/*.bak

mkdir -p sx/valid
for f in sx/*.sx ; do
  grep -q '; Valid' $f || continue
  echo "VALID $f"
  mv $f sx/valid/$(basename $f | sed -e 's/\$/_/g')
done
bzip2 sx/valid/*.sx
