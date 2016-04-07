#!usr/bin/perl

while (<>) {
  if (/[^a-zA-Z0-9](Warning|Error|GraveWarning)\s*\(.*, (\d+)/) { 
    $a="$ARGV: $_"; 
    print "double $a$h{$2}\n\n" if $h{$2} or $2 == 0; 
    $h{$2} = $a;
  }
}
