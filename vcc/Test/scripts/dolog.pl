#!/usr/bin/perl

while (<>) {
  if (/^DIR (\S+) (\S+)/) {
    $id = $1;
    $seed = $2;
  }
  if (/^Time:.* ([\d.]+)s method ver/) {
    $time = $1;
    $seeds{$seed} = 1;
    $ids{$id} = 1;
    $time{($seed,$id)} = $time;
  }
}

my $csv = 0;
open (F,">res.csv");
sub p {
  my $x = shift;
  if($csv) {
   print F "$x,";
  }else{
    printf "%7.2f", $x;
  }
}

sub sep {
  if($csv) {
   print F "X,";
  }else{
    printf "  |";
  }
}

for my $id (sort (keys %ids)) {
  print F "$id," if $csv;
  print "$id  " if not $csv;
  $sum = 0;
  $cnt = 0;

  for my $seed (sort (keys %seeds)) {
    my $t = $time{($seed,$id)};
    if (defined $t) {
      $cnt++;
      $sum += $t;
    }
  }

  if($cnt>0) {
    $avg = $sum / $cnt;
    $var = 0;
    for my $seed (sort (keys %seeds)) {
      my $t = $time{($seed,$id)};
      if (defined $t) {
        $var += ($avg - $t) * ($avg - $t);
      }
    }
    $var = sqrt($var / $cnt);
    $var2 = 100 * $var / $avg;
    p($avg);
  } 

  sep();

  for my $seed (sort (keys %seeds)) {
    my $t = $time{($seed,$id)};
    p($t);
  }

  sep();
  p($var);
  p($var2);

  printf F "\n" if $csv;
  print "\n" if not $csv;
}
close(F);
