#!/usr/bin/perl

@lines = ();
@mask = ();

$div = 3;
$mul = 2;

$pat = '^\s*(assume|axiom) ';
$cmd = "./any-ok";

sub dmp(){
  my $k = 0;
  open(OUT, ">reduce-tmp.bpl");
  foreach (@lines) {
    if (/$pat/) {
      if (@mask[$k] < 0) {
        print OUT "// ";
      }
      $k++;
    }
    print OUT $_;
  }
  close(OUT);
}

while(<>) {
  push @lines, $_;
  /$pat/ and push @mask, 0;
}

$n=@mask;
print STDERR "$n ";
$k = 5;
for ($i=0; $i<$n; ) {
  for($j=$i;$j<$i+$k;$j++) {
    $mask[$j] = -1;
  }
  dmp();
  if (system("$cmd reduce-tmp.bpl") / 256 < 1) {
    print STDERR "S[$i/$k]";
    unlink("reduce-ok.bpl");
    rename("reduce-tmp.bpl", "reduce-ok.bpl");

    dmp();
    my $tmp = "reduce-$i-$k.bpl";
    unlink($tmp);
    rename("reduce-tmp.bpl", $tmp);

    $i += $k;
    $k *= $mul;
  } else {
    print STDERR "K[$i/$k]";
    if($k==1) {
      $mask[$i] = 1;
      $i++;
    } else {
      for($j=$i;$j<$i+$k;$j++) {
        $mask[$j] = 0;
      }
      $k /= $div;
      $k = int($k);
      $k = 1 if($k<1);
    }
  }
}
