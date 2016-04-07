#!/usr/bin/perl


open(F, "< exceptions-vcc-to-vcc2.txt");
while(<F>) {
s/[\r\n]//g;
s/^\s*//;
s/\*$//;
$del{$_} = 1;
}


mkdir("out");

foreach my $f (@ARGV) {
  open(F, "<$f") or die;
  my $dir = $f;
  $dir =~ s/(.*)\/.*/$1/;
  #mkdir("out/$dir");
  my $outname = "out/$f";
  $outname =~ s@orig/@@;
  open(O,">$outname") or die;
  $first = 1;
  $output = 0;
  $test = "";
  $sal = 0;
  @lines = ();
  while(<F>) {
    push @lines, $_;
  }
  for($i=0;$i<@lines;$i++) {
    $_ = $lines[$i];
    my $tmp = $_;
    $tmp =~ s/[\r\n]//g;
    $tmp =~ s/^\s*//;
    $tmp =~ s/\*$//; 
    next if $del{$tmp};
    next if $tmp =~ /^#line/;
    next if $first and $tmp eq "";

    while (/__declspec.*SAL/ && $lines[$i + 1] =~ /__declspec.*SAL/) {
      $i++;
      s/[\r\n]//g;
      $_ .= " " . $lines[$i]; 
    }


    s/__(old|invariant|forall|exists|assert|assume|requires|ensures|writes|reads|checked|unchecked)/$1/g unless $output;
    s/__declspec\(Microsoft.Contracts.GenerateFrameAxiom\)/frameaxiom/g;
    s/__declspec\(Microsoft.Contracts.UseBitVectors\)/usebitvectors/g;
    s/__declspec\(Microsoft.Contracts.IntBoogieAttr, "vcs_max_splits", (.*?)\)\s*__declspec\(Microsoft.Contracts.IntBoogieAttr, "vcs_max_cost", 1\)/vcs_force_splits($1)/g;
    s/__vc(Universe|Empty)/set_\L$1/g;

    s/__vcIsFresh/is_fresh/g;
    s/__vcSet(In|Singleton|Difference|Empty)/set_\L$1/g;
    s/__vcSetEqual/set_eq/g;
    s/\bSet\b/ptrset/g;
    s/\bRegion\b/ptrset/g;

    s/__vcMatchI8/_vcc_match_long/g;
    s/__vcMatchU8/_vcc_match_ulong/g;

    s/__vcValid/_vcc_compat_typed/g;
    s/__vcRegion/_vcc_compat_region/g;
    s/__vcOverlaps/_vcc_compat_overlaps/g;

    s/__vcContains/set_subset/g;
    s/__vcJoin/set_union/g;

    s/__validpointer/typed/g;
    s/\(\([^\(\)]*\*\)__vcBaseZero\(([^\(\)]*)\)\) == [^\(\)]*/is_object_root($1)/g;
    s/__frees\(.*\)/allocates()/g;

    #SAL
    
    s/\)\s*__declspec/\) __declspec/g;
    $sal += s/__declspec\("SAL_notnull"\) __declspec\("SAL_writableTo\(elementCount\(""(.*)""\)\)"\) __declspec\("SAL_post"\) __declspec\("SAL_valid"\) __declspec\("SAL_deref"\) __declspec\("SAL_notreadonly"\)/__inout_ecount($1)/g;
    $sal += s/__declspec\("SAL_notnull"\) __declspec\("SAL_writableTo\(elementCount\(""(.*)""\)\)"\) __declspec\("SAL_post"\) __declspec\("SAL_valid"\) __declspec\("SAL_deref"\) __declspec\("SAL_notreadonly"\) __declspec\("SAL_pre"\) __declspec\("SAL_valid"\)/__inout_ecount($1)/g;
    $sal += s/__declspec\("SAL_pre"\) __declspec\("SAL_valid"\) __declspec\("SAL_pre"\) __declspec\("SAL_deref"\) __declspec\("SAL_readonly"\) __declspec\("SAL_pre"\) __declspec\("SAL_readableTo\(elementCount\(""(.*)""\)\)"\)/__in_ecount($1)/g;
    $sal += s/__declspec\("SAL_pre"\) __declspec\("SAL_valid"\) __declspec\("SAL_pre"\) __declspec\("SAL_deref"\) __declspec\("SAL_readonly"\)/__in/g;
    #there is an additional post/valid here. not sure about that
    $sal += s/__declspec\("SAL_pre"\) __declspec\("SAL_valid"\) __declspec\("SAL_post"\) __declspec\("SAL_valid"\) __declspec\("SAL_deref"\) __declspec\("SAL_readonly"\)/__in/;
    $sal += s/__declspec\("SAL_pre"\) __declspec\("SAL_valid"\) __declspec\("SAL_post"\) __declspec\("SAL_valid"\) __declspec\("SAL_deref"\) __declspec\("SAL_notreadonly"\)/__inout/g;

    $test .= $_;
    $first = 0;

    if ($tmp eq "`") {
      if ($output) {
        $output = 0;
	$first = 1;
	if ($sal) {
	  $test = "#include <vcc2.h>\r\n#include <sal.h>\r\n\r\n" . $test;
	} else {
	  $test = "#include <vcc2.h>\r\n\r\n" . $test;
	}
	print O $test;
	$sal = 0;
	$test = "";
      } else {
        $output = 1;
      }
    }
  }
  die "testcase $f has unbalanced output" unless $test eq "";
}
