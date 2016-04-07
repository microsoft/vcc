#!/usr/bin/perl

sub median {
  my $tmp = shift;
  my @arr = split /\s+/, $tmp;
  my $len = @arr;
  @arr = sort {$a <=> $b} @arr;
  return $arr[int($len / 2)];
}

sub xmax {
  my $tmp = shift;
  my @arr = split /\s+/, $tmp;
  my $len = @arr;
  @arr = sort {$a <=> $b} @arr;
  return $arr[$len - 1];
}

sub xmin {
  my $tmp = shift;
  my @arr = split /\s+/, $tmp;
  @arr = sort {$a <=> $b} @arr;
  return $arr[0];
}

sub avg {
  my $tmp = shift;
  my @arr = split /\s+/, $tmp;
  my $len = @arr;
  my $s = 0;
  for my $k (@arr) { $s += $k }
  return $s / $len;
}

while(<>) {
  s/\r//g;
  chomp;
  if (/HEAD .. (.*)/) {
    %h = ();
    @nums = ();
    $lnid = $1;
    for my $n (split /\s+/, $1) {
      $n =~ s/.*://;
      if (not (defined $h{$n})) {
        push @nums, $n;
	$h{$n} = 1;
      }
    }
  }
  /: Valid/ and $valid = 1;
  if($valid and /^time:\s*([\d.]+)/) {
    $valid = 0;
    for my $n (@nums) { 
      $res{$n} .= " $1";
      $total{$lnid}  .= " $1";
    }
  }
}

open(F,"<minimal.bpl");
while(<F>){
s/\r//;
s/\n//;
push @lines, $_;
}

for (keys %total) {
  $total{$_} =~ s/^\s*//;
  printf "%8.2f, %8.2f, %8.2f, %8.2f, %s\n", median($total{$_}), avg($total{$_}), xmin($total{$_}), xmax($total{$_}), $_;
}
exit;

for (keys %res) {
  $res{$_} =~ s/^\s*//;
  printf "%6d, %8.2f, %8.2f, %8.2f, %8.2f, %s\n", $_, median($res{$_}), avg($res{$_}), xmin($res{$_}), xmax($res{$_}), $lines[$_ - 1];
}
