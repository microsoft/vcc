#!/usr/bin/perl

mkdir("out");

for my $f (@ARGV) {
  if (open(F, "< $f")) {
    my $n = 0;
    my $next_t = "";
    while (1) {
      my $t = $next_t;
      $next_t = "";
      my $b = 0;
      while (<F>) {
        s/\r//;
        next if /^`$/ && $t eq "";
	if (/^`\//) {
	} elsif (/`/) {
	  $b++;
	  if ($b >= 2) {
	    s/\n//;
	    s/`(.*)/`\n/;
	    $next_t = $1;
            $t .= $_;
	    last;
	  }
	}
        $t .= $_;
      }
      last if $t eq "";
      open(O, sprintf "> out/%s-%02d", $f, $n) or die;
      $t =~ s/\n/\r\n/g;
      print O $t;
      close(O);
      $n++;
    }
    close(F);
  } else {
    print "cannot open $f\n";
  }
}
