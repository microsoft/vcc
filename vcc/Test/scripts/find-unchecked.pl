#!/usr/bin/perl

$ignore = '(^(Shared|TestResults|files.txt)$)|(/(bin|obj|Debug|Release|Build)$)|(\.(ncb|suo|user)$)|((sync|cache)-[^/]+$)|(/(actual.txt|expected.txt|output.log|testsuite/tmp)$)';

if($ARGV[0] eq "sync") {
  open(F, "tf dir /recursive . |");
  open(O, ">files.txt");
  while(<F>) {
    s/\r//g;
    s/\n//g;
    s@/FELT@@;
    if (/^\$(.*):$/) { $dir = $1; }
    else { s/^\$//; print O "$dir/$_\n"; }
  }
  close(O);
  close(F);
  exit 0;
}

$lst = 0;
open(F,"<files.txt");
%f = ();
while(<F>) {
  s/\r//g;
  s/\n//g;
  s@^/@@;
  s@/$@@;
  $f{lc($_)} = 1;
  $lst++;
}
close(F);
$found = 0;
$wrong = 0;

sub search {
  my $dir = shift;
  opendir(my $dh, $dir) || die "can't opendir $dir: $!";
  foreach my $fn (readdir($dh)) {
    next if $fn eq "." or $fn eq "..";
    my $full = "$dir/$fn";
    $full =~ s@^\./@@;

    if ($f{lc($full)}) {
      $f{lc($full)}++;
      $found++;
      if (-d $full) {
        search($full);
      } else {
      }
    } else {
      next if $full =~ /$ignore/i;
      next if -l $full;
      $wrong++;
      if (-d $full) {
        print "DIR  $full\n";
      } else {
        print "FILE $full\n";
      }
    }
  }
  closedir $dh;
}

search(".");
print "found $found out of $lst in TFS, additionally $wrong junk\n";

#foreach my $k (keys %f) {
#  print "MISS $k\n" if ($f{$k} <= 1);
#}
