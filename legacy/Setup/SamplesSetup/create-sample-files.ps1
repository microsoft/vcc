# Use like this:
# powershell -Command ".\create-sample-files.ps1 | Out-File -filepath 'Samples.Files.wxs' -encoding utf8"

function Hash([string]$string) {
  $local:hashAlgo = [System.Security.Cryptography.Sha1]::Create();
  $local:hashBytes = $hashAlgo.ComputeHash([Char[]]$string);
  $local:result = "";
  foreach ($byte in $hashBytes) { $result += "{0:X2}" -f $byte }
  $result.ToString()
}

$samplesConfig = @{
  Demo=@("vcc/Demo", "B6F1157C-C7E0-4291-8BBA-4BD6D84A120A");
  Tutorial=@("vcc/Docs/tutorial/c", "7E7B1920-5E02-4BBC-AB3F-8DDD689EFE63");
  examples3=@("vcc/Test/testsuite/examples3", "CA76AB4B-25BB-4C19-8200-42446DFF52D5");
  old_tutorial=@("vcc/Test/testsuite/old_tutorial", "B112E30E-253B-4050-9C73-7B5230CD4DBC");
  "vacid-0"=@("vcc/Test/testsuite/vacid-0", "D5500B06-A1FC-4A84-BB3C-10CAA51AC5D6");
  vcc2=@("vcc/Test/testsuite/vcc2ns", "E29B977C-9E77-4697-94E8-5A5BB4420496");
  vcc3=@("vcc/Test/testsuite/vcc3", "6790E5FB-5ECE-4445-B31D-1241E993220A");
  vscomp2010=@("vcc/Test/testsuite/vscomp2010", "BC0D7046-D91F-42F6-9E6E-65FB70C20426");
}

$samples = $samplesConfig.keys | Sort-Object

$hg_root = hg root
cd $hg_root

$directories = @();
$componentrefs = @();

[System.Console]::OutputEncoding = [System.Text.Encoding]::UTF8
'<?xml version="1.0" encoding="utf-8"?>'
'<Wix xmlns="http://schemas.microsoft.com/wix/2006/wi">'
'  <?define RootDir="..\..\.." ?>'

foreach ($sample in $samples) {
  $hgpath, $guid = $samplesConfig[$sample]
  $path = $hgpath -replace "/", "\"
  $samplehash = Hash($sample);
  $sampleid = "sample$samplehash";
  $dirid = "dir$samplehash";

  $directories += "      <Directory Id=`"$dirid`" Name=`"$sample`" />"
  $componentrefs += "      <ComponentRef Id=`"$sampleid`" /> <!-- $sample -->"

  hg manifest | Select-String -pattern "$hgpath/" | Sort-Object | foreach `
    -begin {
""
"  <Fragment>"
"    <DirectoryRef Id=`"$dirid`" FileSource=`"`$(var.RootDir)\$path`">"
"      <Component Id=`"$sampleid`" Guid=`"$guid`"><!-- $sample -->"
"        <RemoveFolder Id=`"$dirid`" On=`"uninstall`" />"
"        <RegistryValue Root=`"HKCU`" Key=`"Software\Microsoft Research\Vcc`" Name=`"$sampleid`" Type=`"integer`" Value=`"1`" KeyPath=`"yes`" />"
    } `
    -process {
      $file = Split-Path $_ -Resolve -Leaf
      $filehash = Hash("$sample\$file"); # ID's need to be globally unique. Renaming $sample will change all file IDs.
"        <File Id=`"fil{0}`" Name=`"{1}`" />" -f $filehash, $file
    } `
    -end {
"      </Component>"
"    </DirectoryRef>"
"  </Fragment>"
    }
}

''
'  <Fragment>'
'    <DirectoryRef Id="INSTALLLOCATION">'
$directories
'    </DirectoryRef>'
'  </Fragment>'

''
'  <Fragment>'
'    <ComponentGroup Id="all_samples">'
$componentrefs
'    </ComponentGroup>'
'  </Fragment>'

''
'</Wix>'
