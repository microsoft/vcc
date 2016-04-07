#!/usr/bin/perl

$pref = '^\s*//\s*';
$pat = "assume|axiom";


while(<>) {
  push @lines, $_;
  $line++;
  if(/$pref$pat/) {
    $cm{$choices} = $line;
    $mc{$line} = $choices;
    $choices++;
  }
}

open(LOG, ">> mutate2.log");
print LOG "** start\n";

@xlines = (
 399, 337 
);

for($i=0;$i<@xlines;$i++) {
  #$num = int(rand($choices/10)) + 1;
  #$num = 20;
  $num =1;
  %u = ();
  $fn = "//";
  for($j=0;$j<$num;$j++) {
    #$k = int(rand($choices));
    $k = $mc{$xlines[$i]};
    $fn .= " $k:$cm{$k}";
    $u{$k} = 1;
  }
  $hd = $fn;
  $fn = "mut-$i.bpl";
  open(O,"> $fn") or die;
  $cur = 0;
  print O "$hd\r\n";
  for($j=0;$j<@lines;++$j) {
    $_ = $lines[$j];
    $cur++ if(/$pref$pat/);
    s/$pref// if not $u{$cur - 1};
    print O $_;
  }
  close(O);
  print LOG "FILE $fn\n";
  print LOG "HEAD $hd\n";
  print STDERR "$fn: ";
  system("Boogie /bv:i $fn /z3opt:/nosuchopt /proverLog:tmp.sx >/dev/null 2>/dev/null");
  print STDERR "Z ";
  for($j=0;$j<5; ++$j) {
    open(Z, "z3 MAM=0 /st /rs:$j tmp.sx 2>&1 |");
    print LOG "SEED $j\n";
    $inv = "";
    while(<Z>) {
      s/\r//g;
      /Invalid/ and $inv = "[X] ";
      /^time:\s*([\d.]+)/ and $t = $1;
      print LOG $_;
    }
    close(Z);
    print STDERR "$inv$t ";
  }
  print STDERR "\n";
}
