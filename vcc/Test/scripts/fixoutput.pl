#!/usr/bin/perl

my $outfile = shift;
open(F,"< $outfile");

while(<F>) {
  /------------- .*?([^\/\\]*) failed ---------------/ and $fn = $1;
  /source\((\d+)\)/ and $ln = $1;

  if (/^\*\*\*/) {
    if ($out eq "\n" || $out eq "\r\n") { $out = ""; }
    if ($copy == 1) {
      $outs{"$fn:$ln"} = $out;
      $fixes{$fn}++;
      #print "found fix $fn:$ln\n";
    } elsif ($copy == 2) {
      $prevs{"$fn:$ln"} = $out;
    }
    $copy = 0;
  } else {
    $out .= $_ if $copy;
  }

  /^\*\*\* actual output/ and do { $copy = 1; $out = ""; };
  /^\*\*\* expected output/ and do { $copy = 2; $out = ""; };
}

die "first file likely not compiler output" if (! %outs);

for (@ARGV) {
  my $fn = $_;
  my $line = 1;
  my $applied = 0;
  my $bn = $fn;
  $bn =~ s@.*[/\\]@@g;
  if(! $fixes{$bn}) {
    print "no fixes for $fn\n";
    next;
  }
  open(O,"> $fn.tmp");
  open(F,"< $fn");
  while(<F>) {
    $line++;
    my $l = $_;
    $l =~ s/(\r?\n)//g;
    # option:
    if ($l =~ /^`\//) {
      print O $_;
      next;
    }
    my $cr = $1;
    my $key = "$bn:$line";
    $key = "$bn:" . ($line - 1) if ($l =~ /^(\`|\/\*\`)(.+)/);
    if ($l =~ /^(\`|\/\*\`)(.*)/ && defined $outs{$key}) {
      print O "$1$cr";
      my $prev = "";
      if ($2 ne "") { $prev = "$2$cr"; }
      print "apply $key\n";
      print O $outs{$key};
      while (<F>) {
        $line++;
	my $l = $_;
	$l =~ s/[\n\r]//g;
	last if ($l =~ /^\`/);
	if ($l =~ /\`$/) {
	  s/(\`([\n\r]*))/$2/;
          $prev .= $_;
	  $_ = $1;
	  last;
	}
        $prev .= $_;
      }
      print O $_;
      $prev =~ s/\r//g;
      $prevs{$key} =~ s/\r//g;
      if ($prev eq $prevs{$key}) {
        $applied++;
      } else {
        print "mismatch of output:\n>>$prev<<\n>>$prevs{$key}<<\n";
	die;
      }
    } else {
      print O $_;
    }
  }
  close(F);
  close(O);
  if ($fixes{$bn} == $applied) {
    #open(F,">$fn") or system("tf edit $fn");
    open(F,">$fn") or chmod(0644, $fn);
    close(F);
    unlink $fn or die "cannot unlink $fn";
    rename ("$fn.tmp", $fn) or die "cannot mv $fn.tmp to $fn $!";
  } else {
    print "applied only $applied, but $fixes{$bn} found for $fn\n";
    die;
  }
}
