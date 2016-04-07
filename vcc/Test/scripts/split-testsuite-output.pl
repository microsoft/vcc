#!/usr/bin/perl

open(E,">expected.txt");
open(A,">actual.txt");
sub both {my $l = shift;
print E $l;
print A $l;
}
$mode=0;
while (<>) {
s/\r//g;
/source\((\d+)\)/ and $line = $1;
s/^\*\*\* actual output:/*** OUTPUT [$line]:/ and $mode=1;
s/^\*\*\* expected output:/*** OUTPUT [$line]:/ and $mode=2;
/^\*\*\*$/ and do {$mode=0;next;};

if($mode==0){both($_);}
elsif($mode==1){print A $_;}
elsif($mode==2){print E $_;}
}
