#!/usr/bin/perl

$machine = "emicccnet";
$build = "vccPerf";

#$machine = "emicbld1";
#$build = "vcc";

$serv='http://emicbld1';
$list= $serv . "/ccnet/server/$machine/project/$build/ViewAllBuilds.aspx";

$max = 500;

sub process {
  my $fn = shift;
  open(F, "< $fn");
  
  while (<F>) {
    my $tmp = $_;
    chomp;
    while ($tmp =~ s/^([^<]+|<[^>]+>)//) {
      my $ln = $1;
      if ($ln =~ /<table.*/) {
        %tab = ();
	$tr = -1;
      } elsif ($ln =~ /<\/table/) {
        dotab();
	%tab=();
      } elsif ($ln =~ /<tr/) {
        $tr++; $td = 0;
      } elsif ($ln =~ /<td/) {
        $cur = "";
        $copy = 1;
      } elsif ($ln =~ /<\/td/) {
        $cur =~ s/^\s*//;
        $cur =~ s/\s*$//;
        #print "set $tr $td = '$cur'\n";
	$cur =~ s/\r//g;
	$cur =~ s/\n/ /g;
        $tab{($tr,$td)} = $cur;
	$td++;
      } elsif ($copy) {
        $cur .= $ln;
      }
    }
  }

  close(F);
}

my $the_mods;
my %the_time;
my $the_file;
my $the_date;
my $the_stat;
my $the_url;

sub dotab {
  if ($tab{(0,0)} =~ /^Modification/) {
    %mods = ();
    $the_mods = "";
    for (my $i=1;defined $tab{($i,1)};$i++) {
      my $msg = $tab{($i,3)};
      $msg =~ s/^(.{0,40}).*/$1/;
      my $per = $tab{($i,1)};
      $per =~ s/.*\\//;
      $mod = "$per: $msg \@ " .  $tab{($i,4)} . " ";
      if(defined $mods{$mod}) {}else {
      $mods{$mod} = 1;
      $the_mods .= $mod;
      }
    }
  } elsif ($tab{(0,4)} =~ /Verification/) {
    for (my $i=1;defined $tab{($i,1)};$i++) {
      $the_time{$tab{($i,0)}} .= "," . $tab{($i,4)};
    }
  } elsif ($tab{(0,0)} =~ /BUILD/) {
    my $f = "<font color='green'>PASS</font>";
    $f = "<font color='red'>FAIL</font>" if $tab{(0,0)} =~ /FAIL/;
    $f = "<font color='red'>EXCP</font>" if $tab{(0,0)} =~ /EXCEP/;
    $the_stat = $f;
    
    for (my $i=1;defined $tab{($i,1)};$i++) {
      $tab{($i,0)} =~ /Date of bu/ and $the_date = $tab{($i,1)};
    }
  } elsif ($tab{(0,0)} =~ m!ViewFarm.*href="([^"]+log(2\d+)[^"]+ViewBuildReport.aspx)"!) {
    $the_url = $1;
  }

}

$the_file = shift;

#$the_file = "examples,hv,examples/ArrayList.c.1,examples/BitMap.c.1,examples/List.c.1,examples/LockFreeStack.c.1,".
#            "examples/Rundown.c.1,examples/SingleList.c.1,examples/StackAsArray.c.1,examples/VolatileAbstractState.c.1,".
#	    "hv/absDesc.c.1,hv/absDesc1.c.1,hv/BitfieldsPerformance.c.1,hv/vpregs.c.1,hv/ValAbsRel.c.1"
#	   if $the_file eq "all";

$cache = "cache-$build";
mkdir($cache);
$k = 0;
if ($the_file eq "sync") {
open(L, "wget -nv $list -O - |");
@files = ();
while(<L>) {
  if (m!href="([^"]+log(2\d+)[^"]+ViewBuildReport.aspx)"!) {
    my ($no, $url) = ($2, $1);
    my $failed = "";
    /build-failed/ and $failed = "f";
    next if ($no cmp $first) < 0;
    last if $k++ > $max;
    my $n = "$cache/$no$failed.html";
    push @files, $n;
    next if -f $n;
    system("wget -nv '$serv$url' -O $n");
  }
}
} else {
while(<$cache/*>) {
  push @tmp, $_;
}
@tmp = reverse @tmp;
foreach(@tmp) {
  push @files, $_;
  last if $k++ > $max;
}
open(O,">results.html");
print O "<html><body><table>\n";
print O "<tr><th>Log file<th>Stat ";

sub hd() {
  for (split /,/, $the_file) {
    s/\.c\.1//;
    #s/.*\///;
    s/(.{5})/$1<br>/g;
    #if (length $_ > 10) {
    #  s/(.{0,10}).*/$1../;
    #}
    print O "<td>$_ ";
  }
  print O "<th>Message </tr>\n";
}

sub avg($) {
    my $x = shift;
    $x =~ s/^,//;
    my @tm = split /,/, $x;
    my $sum = 0;
    my $cnt = 0;
    for my $v (@tm) {
      $sum += $v;
      $cnt++;
    }
    
    if($cnt>0) {
      return (sprintf "%.2f", $sum / $cnt);
    } else {
      return "";
    }
}

sub pr_times() {
  my $html_tm = "";
  for (split /,/, $the_file) {
    my $a = avg($the_time{$_});

    my $st = "padding: 4px; text-align: right;";

    if (/\.c\.1$/) {
      $st .= " background-color: #eee; " 
    } else {
      $st .= " background-color: #ddf; " 
    }

    if ($prev{$_}) {
      my $diff = $a - $prev{$_};
      my $cur = $prev{$_};

      if ($a > 0) {
        if ($diff > 0.5 && ($diff / $a) > 0.05) {
          $st .= "font-weigth: bold; color: green;";
        } elsif ($diff < -0.5 && ($diff / $a) < -0.05) {
          $st .= "font-weigth: bold; color: red;";
        }
      }

      $html_tm .= "<td style='$st'>$cur</td>";
    } else {
      $html_tm .= "<td style='$st'>N/A</td>";
    }
    $prev{$_} = $a;
  }
  return $html_tm;
}

my $hd_done = 0;

for my $f (@files) {
  $the_date = "";
  $the_stat = "";
  %the_time = ();
  $the_mods = "";
  $the_url = "";
  process($f);

  my $cnt = 0;
  my $sum = 0;

  if ($the_file eq "all") {
    $the_file = "";
    for my $fn (sort (keys %the_time)) {
      if (avg($the_time{$fn}) > 0.5) {
        $the_file .= ",$fn";
      }
    }
    $the_file =~ s/^,//;
  }

  my $html_tm = pr_times();
  if ($hd_done) {
    print O "$pre $html_tm $post";
  } else {
    hd();
    $hd_done = 1;
  }

  $pre = sprintf "<tr><td><nobr><a href='%s'>%s</a></nobr> <td>%s ",
               $serv .$the_url, $the_date, $the_stat;
  $post = sprintf "<td>%s</tr>",   $the_mods;
}

#final
my $html_tm = pr_times();
print O "$pre $html_tm $post";

print O "</table></body></html>\n";
close(O);
chmod(0777, "results.html");
system("cmd /c results.html");
}

