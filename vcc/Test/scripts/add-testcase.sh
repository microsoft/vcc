#!/bin/sh

opt=

case "$2" in
  vcc3/* )
  opt=-3
esac

case "$2" in
  vcc2/* | vcc2ns/* | vcc3/* )
    case "$1" in
      *.c )
	if grep -q ' _(' "$1" || grep -q '^_(' "$1" ; then
	  echo '`/newsyntax' >> "$2"
	fi
        cat "$1" >> "$2"
        echo '`' >> "$2"
        echo '`' >> "$2"
	sleep 1
	perl -p -i.bak -e 's/\r//g' "$2"
	sleep 1
	perl -p -i.bak -e 's/\n/\r\n/g' "$2"
	rm -f "$2".bak
        ./fix $opt "$2"
        ;;
    esac
esac
