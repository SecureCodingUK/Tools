#!/usr/bin/perl -w
# copyright Richard Braganza 2016

# for /F %i in ('Type output\output.txt') do @echo %i && D:\RBTools\FirewallReview\ASA_firewall_review_v1.x.pl %i >output\%i 2>>unhandled.txt
use strict;
use feature 'switch';
use Net::CIDR;
use Net::IP;
use Digest::SHA qw(sha256_base64);
use Digest::MD5;
use Data::Dumper;
# extended
# password lists in mem
# DONE - need to convert SRCport cisco mask to CIDR and destip mask to CIDR
# DONE - need to convert group objects
# DONE - need to set I/f IP addresses
# DONE - need to add allowed routes
# Try other firewalls
# need to run mapper


my $itoa64 = "./0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqr
+stuvwxyz";

sub pseudo_base64 {
    my $md5 = shift;
    my $s64 = "";
    for my $i (0..3) {
        my $v = unpack "V", substr($md5, $i*4, 4);
        for (1..4) {
            $s64 .= substr($itoa64, $v & 0x3f, 1);
            $v >>= 6;
        }
    }
    return $s64;
}

my $debug=1;
my $wordlist;
if (@ARGV) 
{
    $wordlist =  $ARGV[0];
}
my %OF; # objects found

############################################################################
# TYPE 4 decoding functions - ok I encode and see if it matches :)
sub Encode{
	my $data = shift;
    my $b64 = sha256_base64($data);
	$b64 =~ tr#A-Za-z0-9+\/#.\/0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz#;
	$b64 =~ s/(.{1,40}).*$/$1/;
	return $b64;
}


############################################################################
# Vigenere translation table for type 7 passwords
############################################################################
my @V=(0x64, 0x73, 0x66, 0x64, 0x3b, 0x6b, 0x66, 0x6f, 0x41, 0x2c, 0x2e,
    0x69, 0x79, 0x65, 0x77, 0x72, 0x6b, 0x6c, 0x64, 0x4a, 0x4b, 0x44,
    0x48, 0x53, 0x55, 0x42, 0x73, 0x67, 0x76, 0x63, 0x61, 0x36, 0x39,
    0x38, 0x33, 0x34, 0x6e, 0x63, 0x78, 0x76, 0x39, 0x38, 0x37, 0x33,
    0x32, 0x35, 0x34, 0x6b, 0x3b, 0x66, 0x67, 0x38, 0x37);
############################################################################

sub Decrypt
{
	my $pw=shift;           	                  # Retrieve input obfuscated password
	my $i=substr($pw,0,2);                        # Initial index into Vigenere translation table
	my $c=2;                                      # Initial pointer
	my $r="";                                     # Variable to hold cleartext password
	while ($c<length($pw))
	{   					    	                # Process each pair of hex values
		$r.=chr(hex(substr($pw,$c,2))^$V[$i++]);    # Vigenere reverse translation
		$c+=2;                                      # Move pointer to next hex pair
		$i%=53;                                     # Vigenere table wrap around
	}                                             #
	return $r;                                    # Return cleartext password
}
sub loadService
{
	my $rh =shift;
	my $group = shift; # name of the object group
	my $protocol = shift;
	my $service = shift;
	my $existing = '';
	if ( $debug )
	{
#		warn join '<>', "\t",$group, $protocol, $service;
	}
	push @{$$rh{$group}}, $protocol." ".$service;
}

sub loadNetwork
{
	my $rh =shift;
	my $group = shift; # name of the object group
	my $network = shift;
	my $mask = shift;
	my $existing = '';
	if ( $debug )
	{
		warn join '<>', "\t",$group, $network, $mask;
	}
	#get the address in CIDR form
	
	my $cidr;
	if ( $network =~ /\// )
	{
		$cidr = $network;
	}
	elsif ( $network =~ /tcp|udp/ ) 
	{
		# not a network but a service
		return '';
	}
	else
	{
		$cidr = Net::CIDR::addrandmask2cidr( $network,$mask);
	}
	# check what we have so far, each group
	foreach my $g (keys %$rh)
	{ 
		next if ($g eq $group);
		# for each network object
		# ignore service objects
		next if ($$rh{$g} && @{$$rh{$g}}>0 && @{$$rh{$g}}[0] !~ /\// );
		next if ($$rh{$g} && @{$$rh{$g}}>0 && @{$$rh{$g}}[0] !~ /tcp\s\d+/ );
		if ( Net::CIDR::cidrlookup( $cidr,@{$$rh{$g}} ))
		{
			$existing .= $g."\n";
		}
	}
	
	# if new, then add it
	if ( $existing eq '' )
	{
		push @{$$rh{$group}}, $cidr;
	}
	return $existing;
}
my %objs;

my $obj=0;
my $grp='';
my $type='';
my $if='';
my $intf='';
my $proto;
my @acls;
my %rules;
my $inactive =0;
my $i=0;
my %containers;
my @pswds;
my %pswds;
my %words; # keys will be the words from the file to use in password checks
my $contexts=0;
my @cntxts;
my %ifs;
my %acls;
my %pairs;
print "Used Cisco Parser v1.8\n";
while (<>)
{
	s/\r//msg;
	chomp;

	$i++;
	if ( /^\s*hostname\s+([^\s+]+)\s*$/ )
	{
		# assign previous context objects
		if ($contexts>0)
		{
			@{$cntxts[$contexts]{acls}}=@acls;	 
			%{$cntxts[$contexts]{obj}}=%objs;	 
			%{$cntxts[$contexts]{containers}}=%containers;	 
			%{$cntxts[$contexts]{interfaces}}=%ifs;	 
			# clear down the objects and containers for new context
			@acls=(); 
			undef %objs; 
			undef %containers; 
			undef %ifs; 
		}

		# now create a new context
		$contexts++;
		$cntxts[$contexts]{hostname}=$1;	 
		print "Contexts: $contexts, $cntxts[$contexts]{hostname}\n";

	}
	elsif( /^\s*ip\s+address\s+([\d\.]+)\s+([\d\.]+)\s*/i )
	{
		$ifs{$intf}{IPRange}= Net::CIDR::addrandmask2cidr($1,$2);
		$ifs{$intf}{IP}= $1;
		#print $ifs{$intf}{IP}," $_\n";
	}
	elsif( /^\s+no\s+ip\s+address\s*$/i ) 
	{
		delete $ifs{$intf} if (exists $ifs{$intf} );
	}
	elsif( /^\s+shutdown\s*$/i ) 
	{
		delete $ifs{$intf} if (exists $ifs{$intf} ) ;
	}
	elsif( /^\s+nameif\s+([^\s]+)\s*$/i ) 
	{
		$ifs{$intf}{Name}=$1;
		#print $ifs{$intf}{Name}," $_\n";
	}
	elsif( /^\s*access-group\s+([^\s]+)\s+(in|out)\s+interface\s+([^\s]+)\s*/i )
	{
#		warn $_;
		my $gname = $1;
		my $dir = $2;
		my $name = $3;
		foreach my $if (keys %ifs)
		{
		
			if ( $ifs{$if}{Name} && $ifs{$if}{Name} eq $name )
			{
				$ifs{$if}{ACL}{$dir}{ACLName}[0]=$gname;
				print "Access Group $gname affecting $dir on interface $name\n";
				foreach my $al (keys %acls)
				{
					next unless ( $al eq $gname );
					#print "$al found ",  join " ",${$acls{$al}}[0], "\n";
					$ifs{$if}{ACL}{$dir}{ACLName}[1] = \$acls{$al};
				}
				foreach my $acl (@{$ifs{$if}{ACL}{$dir}{ACLName}})
				{
					if (ref $acl )
					{
#						print Dumper $acl,"\n";
						print "\n";
					}
					else
					{
						print "\t$acl=";
					}
				}
				last;
			}
		}
		print "\n";
	}

	
	# A A
	# access-list Outside_access_in extended permit object-group DM_INLINE_SERVICE_2 any any
	elsif( /^\s*access-list\s+([^\s]+)\s+extended\s+(permit|deny)\s*?(?:tcp|udp|ip|object-group\s+[^\s]+|object\s+[^\s]+)?\s+?any[46]?\s+any[46]?\s*/i )
	{
		push@{$acls{$1}}, [ 
			Allow=>$2,
			SIP=>"0.0.0.0",
			SMask=>"0.0.0.0",
			DIP=>"0.0.0.0",
			DMask=>"0.0.0.0" 
		];
		$if =$1;
	 
		push @acls, $i." ".$if. join " ",$2,"0.0.0.0","0.0.0.0","0.0.0.0","0.0.0.0";
		$rules{$i} = $_;
		if ( /\s+inactive/ )
		{
			pop @acls;
		}
	}
	
	# A H
	# access-list RETURN extended permit tcp any host 10.108.74.21 eq https 
	elsif( /^\s*access-list\s+([^\s]+)\s+extended\s+(permit|deny)\s*?(?:tcp|udp|ip|object-group\s+[^\s]+|object\s+[^\s]+)?\s+?any[46]?\s+host\s+([^\s]+)\s*/i )
	{
		push@{$acls{$1}}, [ 
			Allow=>$2,
			SIP=>"0.0.0.0",
			SMask=>"0.0.0.0" ,
			DIP=>$3,
			DMask=>"255.255.255.255"
		];
		$if =$1;
	 
		push @acls, $i." ".$if. join " ",$2,"0.0.0.0","0.0.0.0",$3,"255.255.255.255";
		$rules{$i} = $_;
		if ( /\s+inactive/ )
		{
			pop @acls;
		}
	}

	#  A O
	# access-list Outside_access_in extended permit ip any object MS_PDW_VLAN1153
	elsif( /^\s*access-list\s+([^\s]+)\s+extended\s+(permit|deny)\s*?(?:tcp|udp|ip|object-group\s+[^\s]+|object\s+[^\s]+)?\s+?any[46]?\s+object(?:-group)?\s+([^\s]+)\s*/i )
	{
		$OF{$3} =1;
		my $acl_name =$1;
		my $allow = $2;
		my $sip = "0.0.0.0";
		my $smask = "0.0.0.0";
		my $dest_obj=$3;
		#warn ">>>".$dest_obj; #good
		if ( $containers{$dest_obj})
		{
			$rules{$i} = $_;
			foreach my $o ( @{$containers{$dest_obj}} )
			{
#				warn $o;
				$OF{$o}=1;
  
				my $ip = new Net::IP ($o);
				my ($dip,$dmask) =($ip->ip(), $ip->mask());
				push@{$acls{$acl_name}}, [
					Allow=>$allow,
					SIP=>$sip,
					SMask=>$smask,
					DIP=>$dip,
					DMask=>$dmask 
				];
				$if =$acl_name;

				push @acls, $i." ".$if. join " ",$allow,$sip,$smask,$dip,$dmask;
				if ( /\s+inactive/ )
				{
					pop @acls;
				}

			}
		}
	}

	# H A
	# access-list cap1 extended permit tcp host 10.171.0.28 any
	elsif( /^\s*access-list\s+([^\s]+)\s+extended\s+(permit|deny)\s*?(?:tcp|udp|ip|object-group\s+[^\s]+|object\s+[^\s]+)?\s+?host\s+([^\s]+)\s+(?:range\s+\d+\s+\d+\s+)?any[46]?\s*/i )
	{
		push@{$acls{$1}}, [ 
			Allow=>$2,
			SIP=>$3,
			SMask=>"255.255.255.255",
			DIP=>"0.0.0.0",
			DMask=>"0.0.0.0" 
		];
		$if =$1;
	 
		push @acls, $i." ".$if. join " ",$2,$3,"255.255.255.255","0.0.0.0","0.0.0.0";
		$rules{$i} = $_;
		if ( /\s+inactive/ )
		{
			pop @acls;
		}
	}
	
	# H H
	elsif( /^\s*access-list\s+([^\s]+)\s+extended\s+(permit|deny)\s*?(?:tcp|udp|ip|object-group\s+[^\s]+|object\s+[^\s]+)?\s+?host\s+([^\s]+)\s+host\s+([^\s]+)\s*/i )
	{
		push@{$acls{$1}}, [ 
			Allow=>$2,
			SIP=>$3,
			SMask=>"255.255.255.255",
			DIP=>$4,
			DMask=>"255.255.255.255" 
		];
		$if =$1;
	 
		push @acls, $i." ".$if. join " ",$2,$3,"255.255.255.255",$4,"255.255.255.255";
		$rules{$i} = $_;
		if ( /\s+inactive/ )
		{
			pop @acls;
		}
	}

	# H I M
	# access-list 150 extended permit ip host 10.162.236.105 10.236.104.0 255.255.255.0
	elsif( /^\s*access-list\s+([^\s]+)\s+extended\s+(permit|deny)\s*?(?:tcp|udp|ip|object-group\s+[^\s]+|object\s+[^\s]+)?\s+?host\s+([\d.]+)\s+([\d.]+)\s+([\d.]+)\s*/i )
	{
		push@{$acls{$1}}, [ 
			Allow=>$2,
			SIP=>$3,
			SMask=>"255.255.255.255",
			DIP=>$4,
			DMask=>$5 
		];
		$if =$1;
	 
		push @acls, $i." ".$if. join " ",$2,$3,"255.255.255.255",$4,$5;
		$rules{$i} = $_;
		if ( /\s+inactive/ )
		{
			pop @acls;
		}
	}
	
	# H OG
	elsif( /^\s*access-list\s+([^\s]+)\s+extended\s+(permit|deny)\s*?(?:tcp|udp|ip|object-group\s+[^\s]+|object\s+[^\s]+)?\s+?host\s+([^\s]+)\s+object(?:-group)?\s+([^\s]+)\s*/i )
	{
		$OF{$4} =1;
		my $acl_name =$1;
		my $allow = $2;
		my $sip = $3;
		my $smask = "255.255.255.255";
		my $dest_obj=$4;
		#warn ">>>".$dest_obj; #good
		if ( $containers{$dest_obj})
		{
			foreach my $o ( @{$containers{$dest_obj}} )
			{
#				warn $o;
				$OF{$o}=1;
  
				my $ip = new Net::IP ($o);
				my ($dip,$dmask) =($ip->ip(), $ip->mask());
				push@{$acls{$acl_name}}, [
					Allow=>$allow,
					SIP=>$sip,
					SMask=>$smask,
					DIP=>$dip,
					DMask=>$dmask 
				];
				$if =$acl_name;

				push @acls, $i." ".$if. join " ",$allow,$sip,$smask,$dip,$dmask;
				$rules{$i} = $_;
				if ( /\s+inactive/ )
				{
					pop @acls;
				}

			}
		}
	}

	
	# I M H
	# access-list INSIDE_access_in extended permit object-group DM_INLINE_SERVICE_1 10.0.0.0 255.0.0.0 host 10.110.6.190 log debugging 
	elsif( /^\s*access-list\s+([^\s]+)\s+extended\s+(permit|deny)\s*?(?:tcp|udp|ip|object-group\s+[^\s]+|object\s+[^\s]+)?\s+?([\d.]+)\s+([\d.]+)\s+host\s+([\d.]+)\s*/i )
	{
		push@{$acls{$1}}, [
			Allow=>$2,
			SIP=>$3,
			SMask=>$4,
			DIP=>$5,
			DMask=>"255.255.255.255" 
		];

		$if =$1;

		push @acls, $i." ".$if. join " ",$2,$3,$4,$5;
		$rules{$i} = $_;
		if ( /\s+inactive/ )
		{
			pop @acls;
		}
	}
	
	# I M I M
	# access-list INSIDE_access_in extended permit ip 10.0.0.0 255.0.0.0 10.110.96.0 255.255.240.0 
	elsif( /^\s*access-list\s+([^\s]+)\s+extended\s+(permit|deny)\s*?(?:tcp|udp|ip|object-group\s+[^\s]+|object\s+[^\s]+)?\s+?([\d.]+)\s+([\d.]+)\s+([\d.]+)\s+([\d.]+)\s*/i )
	{
		push@{$acls{$1}}, [ 
			Allow=>$2,
			SIP=>$3,
			SMask=>$4,
			DIP=>$5,
			DMask=>$6 
		];
		$if =$1;
	 
		push @acls, $i." ".$if. join " ",$2,$3,$4,$5,$6;
		$rules{$i} = $_;
		if ( /\s+inactive/ )
		{
			pop @acls;
		}
	}

	# I M OG
	elsif( /^\s*access-list\s+([^\s]+)\s+extended\s+(permit|deny)\s*?(?:tcp|udp|ip|object-group\s+[^\s]+|object\s+[^\s]+)?\s+?([\d.]+)\s+([\d.]+)\s+(?:eq\s[^\s]+\s+)?object(?:-group)?\s+([^\s]+)\s*/i )
	{
		$OF{$5} =1;
		my $acl_name =$1;
		my $allow = $2;
		my $sip = $3;
		my $smask = $4;
		my $dest_obj=$5;
		#warn ">>>".$dest_obj; #good
		if ( $containers{$dest_obj})
		{
			foreach my $o ( @{$containers{$dest_obj}} )
			{
#				warn $o;
				$OF{$o}=1;
  
				my $ip = new Net::IP ($o);
				my ($dip,$dmask) =($ip->ip(), $ip->mask());
				push@{$acls{$acl_name}}, [
					Allow=>$allow,
					SIP=>$sip,
					SMask=>$smask,
					DIP=>$dip,
					DMask=>$dmask 
				];
				$if =$acl_name;

				push @acls, $i." ".$if. join " ",$allow,$sip,$smask,$dip,$dmask;
				$rules{$i} = $_;
				if ( /\s+inactive/ )
				{
					pop @acls;
				}

			}
		}
	}

	# OG A
	# access-list RETURN extended permit tcp object-group DM_INLINE_NETWORK_141 any eq smtp
	elsif( /^\s*access-list\s+([^\s]+)\s+extended\s+(permit|deny)\s*?(?:tcp|udp|ip|object-group\s+[^\s]+|object\s+[^\s]+)?\s+?object(?:-group)?\s+([^\s]+)\s+any[46]?\s*/i )
	{
	warn "D1 $_ " if ($debug);
		my $acl_name =$1;
		my $allow = $2;
		my $src_obj=$3;
		my $dip = "0.0.0.0";
		my $dmask = "0.0.0.0";
#		warn $src_obj; #good
		if ( $containers{$src_obj})
		{
			foreach my $o ( @{$containers{$src_obj}} )
			{
#				warn $o;
				$OF{$o}=1;
  
				my $ip = new Net::IP ($o);
				my ($sip,$smask) =($ip->ip(), $ip->mask());
				push@{$acls{$acl_name}}, [
					Allow=>$allow,
					SIP=>$sip,
					SMask=>$smask,
					DIP=>$dip,
					DMask=>$dmask 
				];
				$if =$acl_name;

				push @acls, $i." ".$if. join " ",$allow,$sip,$smask,$dip, $dmask;
				$rules{$i} = $_;
				if ( /\s+inactive/ )
				{
					pop @acls;
				}

			}
		}
	}

	# OG H(I)
	#access-list OUTSIDE_access_in extended permit tcp object-group DM_INLINE_NETWORK_2 host 10.110.6.254 eq https log debugging interval 10 
	elsif( /^\s*access-list\s+([^\s]+)\s+extended\s+(permit|deny)\s*?(?:tcp|udp|ip|object-group\s+[^\s]+|object\s+[^\s]+)?\s+?object(?:-group)?\s+([^\s]+)\s+host\s+([\d.]+)\s*/i )
	{
	warn "D2 $_ " if ($debug);

		my $acl_name =$1;
		my $allow = $2;
		$OF{$3} =1;
		my $src_obj=$3;
		my $dip = $4;
		my $dmask = "255.255.255.255";
#		warn $src_obj; #good
		if ( $containers{$src_obj})
		{
			foreach my $o ( @{$containers{$src_obj}} )
			{
#				warn $o;
				$OF{$o}=1;
  
				my $ip = new Net::IP ($o);
				my ($sip,$smask) =($ip->ip(), $ip->mask());
				push@{$acls{$acl_name}}, [
					Allow=>$allow,
					SIP=>$sip,
					SMask=>$smask,
					DIP=>$dip,
					DMask=>$dmask 
				];
				$if =$acl_name;

				push @acls, $i." ".$if. join " ",$allow,$sip,$smask,$dip;
				$rules{$i} = $_;
				if ( /\s+inactive/ )
				{
					pop @acls;
				}

			}
		}
	}
	# OG HO
	# access-list RETURN extended permit tcp object-group Email_Servers host MIME-Sweeper_VIP eq smtp log
	elsif( /^\s*access-list\s+([^\s]+)\s+extended\s+(permit|deny)\s*?(?:tcp|udp|ip|object-group\s+[^\s]+|object\s+[^\s]+)?\s+?object(?:-group)?\s+([^\s]+)\s+host\s+([^\s]+)\s*/i )
	{
		warn "D3 $_ " if ($debug);
	
		my $acl_name =$1;
		my $allow = $2;
		$OF{$3} =1;
		$OF{$4} =1;
		my $src_obj=$3;
		my $dest_obj = $4;
#		warn $src_obj; #good
		if ( $containers{$src_obj} && $containers{$dest_obj} )
		{
			foreach my $so ( @{$containers{$src_obj}} )
			{
				$OF{$so}=1;
#				warn $so;
				my $soip = new Net::IP ($so);
				my ($sip,$smask) =($soip->ip(), $soip->mask());

				foreach my $do ( @{$containers{$dest_obj}} )
				{
#				warn $do;
					$OF{$do}=1;
					my $doip = new Net::IP ($do);
					my ($dip,$dmask) =($doip->ip(), $doip->mask());

					push@{$acls{$acl_name}}, [
						Allow=>$allow,
						SIP=>$sip,
						SMask=>$smask,
						DIP=>$dip,
						DMask=>$dmask 
					];
					$if =$acl_name;
					#warn join "<>",$allow,$sip,$smask,$dip, $dmask;
					push @acls, $i." ".$if. join " ",$allow,$sip,$smask,$dip, $dmask;
					$rules{$i} = $_;
					if ( /\s+inactive/ )
					{
						pop @acls;
					}
				}
			}
		}
	}
	

	
	# OG IM
	#access-list Outside_access_in extended permit tcp object-group DM_INLINE_NETWORK_18 10.123.72.0 255.255.252.0 object-group DM_INLINE_TCP_4
	elsif( /^\s*access-list\s+([^\s]+)\s+extended\s+(permit|deny)\s*?(?:tcp|udp|ip|object-group\s+[^\s]+|object\s+[^\s]+)?\s+?object(?:-group)?\s+([^\s]+)\s+([\d.]+)\s+([\d.]+)\s*/i )
	{
		warn "D4 $_ " if ($debug);

		my $acl_name =$1;
		my $allow = $2;
		$OF{$3} =1;
		my $src_obj=$3;
		my $dip = $4;
		my $dmask = $5;
#		warn $src_obj; #good
		if ( $containers{$src_obj})
		{
			foreach my $o ( @{$containers{$src_obj}} )
			{
#				warn $o;
				$OF{$o}=1;
  
				my $ip = new Net::IP ($o);
				my ($sip,$smask) =($ip->ip(), $ip->mask());
				push@{$acls{$acl_name}}, [
					Allow=>$allow,
					SIP=>$sip,
					SMask=>$smask,
					DIP=>$dip,
					DMask=>$dmask 
				];
				$if =$acl_name;

				push @acls, $i." ".$if. join " ",$allow,$sip,$smask,$dip,$dmask;
				$rules{$i} = $_;
				if ( /\s+inactive/ )
				{
					pop @acls;
				}
			}
		}
	}
	

	# OG OG
	# access-list outside_access_in extended permit tcp object-group DM_INLINE_NETWORK_1 object-group DM_INLINE_NETWORK_5 eq 1433
	elsif( /^\s*access-list\s+([^\s]+)\s+extended\s+(permit|deny)\s*?(?:tcp|udp|ip|object-group\s+[^\s]+|object\s+[^\s]+)\s+?object(?:-group)?\s+([^\s]+)\s+object(?:-group)?\s+([^\s]+)\s*/i )
	{
		warn "D5 $_ " if ($debug);
	
		my $acl_name =$1;
		my $allow = $2;
		$OF{$3} =1;
		$OF{$4} =1;
		my $src_obj=$3;
		my $dest_obj = $4;
#		warn $src_obj; #good
		if ( $containers{$src_obj} && $containers{$dest_obj} )
		{
			foreach my $so ( @{$containers{$src_obj}} )
			{
#				warn $so;
				$OF{$so}=1;
				my $soip = new Net::IP ($so);
				my ($sip,$smask) =($soip->ip(), $soip->mask());

				foreach my $do ( @{$containers{$dest_obj}} )
				{
#				warn $do;
					$OF{$do}=1;
					my $doip = new Net::IP ($do);
					my ($dip,$dmask) =($doip->ip(), $doip->mask());

					push@{$acls{$acl_name}}, [
						Allow=>$allow,
						SIP=>$sip,
						SMask=>$smask,
						DIP=>$dip,
						DMask=>$dmask 
					];
					$if =$acl_name;
					#warn join "<>",$allow,$sip,$smask,$dip, $dmask;
					push @acls, $i." ".$if. join " ",$allow,$sip,$smask,$dip, $dmask;
					$rules{$i} = $_;
					if ( /\s+inactive/ )
					{
						pop @acls;
					}
				}
			}
		}
	}


	# OG OM
	# access-list RETURN extended permit tcp object-group DM_INLINE_NETWORK_13 dca_dcb_Servers 255.255.255.0 eq 8080
	elsif( /^\s*access-list\s+([^\s]+)\s+extended\s+(permit|deny)\s*?(?:tcp|udp|ip|object-group\s+[^\s]+|object\s+[^\s]+)?\s+?object(?:-group)?\s+([^\s]+)\s+([^\s]+)\s+(255\.[\d.]+)\s*/i )
	{
		my $acl_name =$1;
		my $allow = $2;
		$OF{$3} =1;
		$OF{$4} =1;
		my $src_obj=$3;
		my $dest_obj = $4;
		warn $3;
		warn $4;
		warn $containers{$src_obj};
		warn $containers{$dest_obj};
		my $dmask =$5;
#		warn $src_obj; #good
		if ( $containers{$src_obj} && $containers{$dest_obj} )
		{
		warn "E";
			foreach my $so ( @{$containers{$src_obj}} )
			{
				warn $so;
				$OF{$so}=1;
				my $soip = new Net::IP ($so);
				my ($sip,$smask) =($soip->ip(), $soip->mask());

				foreach my $do ( @{$containers{$dest_obj}} )
				{
				warn "BBB $do";
					$OF{$do}=1;
#					my $doip = new Net::IP ($do);
#					my ($dip,$dmask) =($doip->ip(), $doip->mask());

					push@{$acls{$acl_name}}, [
						Allow=>$allow,
						SIP=>$sip,
						SMask=>$smask,
						DIP=>$do,
						DMask=>$dmask 
					];
					$if =$acl_name;
					#warn join "<>",$allow,$sip,$smask,$dip, $dmask;
					push @acls, $i." ".$if. join " ",$allow,$sip,$smask,$do, $dmask;
					$rules{$i} = $_;
					if ( /\s+inactive/ )
					{
						pop @acls;
					}
				}
			}
		}
	}
	
	elsif( /^\s*route\s+([^\s]+)\s+([^\s]+)\s+([^\s]+)\s+([^\s]+)\s*/i ) 
	{
		warn $_;
				my $name = $1;
		my $ip = $2;
		my $mask = $3;
		my $gw = $4;
		foreach my $if (keys %ifs)
		{
			if ( $ifs{$if}{Name} && $ifs{$if}{Name} eq $name )
			{
				push @{$ifs{$if}{Route}}, \[$2,$3,$4];
				print join "\n",$if, Dumper $ifs{$if}{Route};
				
				print "$1 Routes $2:$3 to $4\n";
				last;
			}
		}
	}
	elsif( /^\s*interface\s+([^\s]+)/i )
	{
		$intf=$1;
		$ifs{$1}{IP}='';
		#print "Found Interface: $1\n";
	}
	elsif ( /^\s*object-group\s+([^\s+]+)\s+([^\s]+)\s*$/ )
	{
		$obj=\$objs{$2};
		$grp=$2;
		$type=$1;

	}
	elsif ( /^\s*object-group\s+([^\s+]+)\s+([^\s]+)\s+([^\s]+)\s*$/ )
	{
		$obj=\$objs{$2};
		$grp=$2;
		$type=$1;
		$proto=$3;
	}
	elsif ( /^\s*object\s+([^\s+]+)\s+([^\s]+)\s*$/ )
	{
		$obj=\$objs{$2};
		$grp=$2;
		$type=$1;
	}
	elsif ( /^\s*name\s+([\d.]+)\s+([^\s]+)\s*/ )
	{
		$grp =$2;
		my $cidr = $1;
		my $c =  join " " ,split (/\./,$cidr);
		if ( (split (/\./,$cidr))[3] == 0 )
		{
			if ( (split (/\./,$cidr))[2] == 0 )
			{
				if ( (split (/\./,$cidr))[1] == 0 )
				{
					$cidr.= '/8';
				}
				else
				{
					$cidr.= '/16';
				}
			}
			else
			{
				$cidr.= '/24';
			}
		}
		else
		{
			$cidr.= '/32';
		}
		warn ">>Group $grp $cidr" if ($grp=~ /dca/);
		push @{$containers{$grp}}, $cidr;
	}
	elsif ($obj && /^\s*range\s+([\d.]+)\s+([\d.]+)\s*$/ )
	{
		# if seen before then the group must contain that object again?
		my $cidr = Net::CIDR::range2cidr( $1,$2);
		push @{$containers{$grp}}, $cidr;
	}
	
	elsif ($obj && /^\s*subnet\s+([\d.]+)\s+([\d.]+)\s*$/ )
	{
		# if seen before then the group must contain that object again?
		my $h =$1;
		my $f =loadNetwork( \%objs, $grp, $1, $2 );
		if ( $f ne '' )
		{
			#print "$type $grp contains host $f\n";
			chomp $f;
			push @{$containers{$grp}}, $f;
		}
		else
		{
			push @{$containers{$grp}}, $h."/32";
		}
	}
	elsif ($obj && /^\s*host\s+([^\s]+)\s*$/ )
	{
		# if seen before then the group must contain that object again?
		my $h =$1;
		my $f =loadNetwork( \%objs, $grp, $h, '255.255.255.255' );
		if ( $f ne '' )
		{
			#print "$type $grp contains host $f\n";
			chomp $f;
			push @{$containers{$grp}}, $f;
		}
		else
		{
			push @{$containers{$grp}}, $h."/32";
		}
	}
	elsif ($obj && /^\s*port-object\s+eq\s+([^\s]+)\s*$/ )
	{
		# if seen before then the group must contain that object again?
		my $s =$1;
		loadService( \%objs, $grp, $proto, $s );
	}
	elsif ($obj && /^\s*port-object\s+range\s+([^\s]+\s+[^\s]+)\s*$/ )
	{
		# if seen before then the group must contain that object again?
		my $s =$1;
		loadService( \%objs, $grp, $proto, $s );
	}
	elsif ($obj && /^\s*network-object\s+object\s+([^\s]+)$/ )
	{
		# if seen before then the group must contain that object again?
		my $h =$1;
		# expand any objects
		if ( $containers{$h} )
		{
			$OF{$h} =1;
			foreach ( @{$containers{$h}} )
			{
				push @{$containers{$grp}}, $_;

			}
		}
		else
		{
			my $f =loadNetwork( \%objs, $grp, $h, '255.255.255.255' );
			if ( $f ne '' )
			{
				#print "$type $grp contains host $f";
				chomp $f;
				push @{$containers{$grp}}, $f;
			}
		}
	}
	elsif ($obj && /^\s*network-object\s+(\d+\.\d+\.\d+\.\d+)\s+(\d+\.\d+\.\d+\.\d+)\s*$/ )
	{
		# if seen before then the group must contain that object again?
		my ($n,$m) =($1,$2);
		my $f =loadNetwork( \%objs, $grp, $n, $m );
		if ( $f ne '' )
		{
			#print "$type $grp $n $m is contained in network $f";
			chomp $f;
			push @{$containers{$grp}}, $f;
		}
	}
	elsif ($obj && /^\s*network-object\s+host\s+(\d+\.\d+\.\d+\.\d+)$/ )
	{
		# if seen before then the group must contain that object again?
		my $h =$1;
		#warn $h." IP $grp";
		my $f =loadNetwork( \%objs, $grp, $h, '255.255.255.255' );
		if ( $f ne '' )
		{
			warn "$type $grp contains host $f";
			chomp $f;
			push @{$containers{$grp}}, $f;
		}
	}
	elsif ($obj && /^\s*group-object\s+([^\s]+)\s*$/ )
	{
		# if seen grp object before then the group must contain that object again?
		my $g =$1;
		# get every object and find a match
		foreach my $h (keys %objs)
		{
			# match sure outer group and match are different
			if ( $g eq $h && $grp ne $g )
			{
				$OF{$h}=1;
				# take array of pobjects from matched group and see if in the outer group already
				foreach my $o (@{$objs{$h}})
				{
					$OF{$o}=1;
					
					my $f =loadNetwork( \%objs, $grp, $o, '255.255.255.255' );
					if ( $f ne '' )
					{
						print "$type $grp contains group object $f";
						chomp $f;
						push @{$containers{$grp}}, $f;
					}
				}
			}
		}
	}
	elsif ( /^access-list\s+([^\s]+)\s+(?:extended\s+)?(.*)$/ )
	{
#		next if ( $inactive && $if eq $1 );
		$if =$1;
		push @acls, $i." ".$if." ".$2;
		$rules{$i} = $_;
		if ( /\s+(inactive|remark|icmp|deny|standard|ethertype|ospf)/ )
		{
			pop @acls;
		}
		next if ( /remark|icmp|deny|standard|ethertype|ospf/ );
		warn "UNHANDLED Access List $cntxts[$contexts]{hostname} $_";;
	}
	# password analysis
	#type 5 default 'cisco' 
	elsif ( /\s+(2KFQnbNIdI\.2KYOU)\b/ )
	{
		push @pswds, ['5',$1,$_,1,'cisco'];
#		print "default type 5 password 'cisco' found: $_\n";
		$pswds{$_}='cisco';
	}
	#type 5 default blank
	elsif ( /\s+(8Ry2YjIyt7RRXU24)\b/ )
	{
		push @pswds, ['5',$1,$_,1,''];
#		print "default type 5 password '' (blank) found: $_\n";
		$pswds{$_}='';
	}
	#type 7 
	elsif ( /\s+password\s+7\s+([\dA-Za-z]+)\b/ )
	{
		my $c = $1;
		my $p = Decrypt($c);
		push @pswds, ['7',$c,$_,1,$p];
#		print "type 7 password $p found: $_\n";
		$pswds{$_}=$p;
	}
	elsif ( /\s+key\s+7\s+([\dA-Za-z]+)\b/ )
	{
		my $c = $1;
		my $p = Decrypt($c);
		push @pswds, ['7',$c,$_,1,$p];
#		print "type 7 key password $p found: $_\n";
		$pswds{$_}=$p;
	}
	#type 5
	elsif ( /\bsecret\s+5\s+([^\s]+)\b/ )
	{
		push @pswds, ['5',$1,$_,0,''];
		print "using type 5 password: $1 <> $_\n";

	}
	elsif ( /\bpassword\s+([^\s]+)\s+encrypted\b/ )
	{
		push @pswds, ['6',$1,$_,0,''];
#		print "using type MD5 password: $1 <> $_\n";

	}
	elsif ( /\bpasswd\s+([^\s]+)\s+encrypted\b/ )
	{
		push @pswds, ['6',$1,$_,0,''];
#		print "Using type MD5 password: $1 <> $_\n";

	}
	#type 4
	elsif ( /\bsecret\s+4\s+([^\s]+)\b/ )
	{
		push @pswds, ['4',$1,$_,0,''];
		
		print "using type 4 password: $_\n";
	}
	##########################
	# now create the wordlist
	##########################
	@words{split /\s+/,$_}=(); # horrible but efficient way to hash the words in the line into an existing hash word list
	
}
# finish off assigning any contexts
@{$cntxts[$contexts]{acls}}=@acls;	 
%{$cntxts[$contexts]{obj}}=%objs;	 
%{$cntxts[$contexts]{containers}}=%containers;	 
%{$cntxts[$contexts]{interfaces}}=%ifs;	 
@acls=(); 
undef %objs; 
undef %containers; 
undef %ifs; 
print "Found $contexts Contexts\n";

##########################
# Did the user pass in a password list?
##########################
if ( $wordlist )
{
	open WL, $wordlist or die "No $wordlist wordlist seen $!\n";
	while (<WL>)
	{
		s/\r//msg;
		chomp;
		$words{$_}=$_;
	}
}
# crack the type 4 and 5s :)
foreach my $ra (@pswds)
{
	if ($$ra[3] == 0 ) # not solved yet
	{
		# try every solved password
		foreach my $p (keys %pswds)
		{
			print "Tried $pswds{$p} <> ".Encode( $pswds{$p} )."\n";
			if ( $$ra[0] eq '4' && $$ra[1] eq Encode( $pswds{$p} ) ) # a type 4
			{
				# we have a type 4 match
				$$ra[3]=1; # solved
				$$ra[4]=$pswds{$p};
				$pswds{$$ra[2]}=$pswds{$p};
			}
			elsif ( $$ra[0] eq '5' ) # a type 5 ....
			{
				#warn join "<>", split (/\$/, $$ra[1]);
				my $salt = (split /\$/, $$ra[1])[2]; # pull out salt from type 5 hash
#print "Testing $pswds{$p} $$ra[1]\n";
				if ( !$salt )
				{
					warn "No salt found ??? $$ra[1] <> $$ra[2]";

				}
#warn "openssl passwd -1 -salt \"$salt\" -table $pswds{$p} |" ; 
				open CMD, "openssl passwd -1 -salt \"$salt\" -table $pswds{$p} |" or next;
				while (<CMD>)
				{
					s/\r//msg;
					chomp;
					my ($w,$e) = split /\s+/,$_;
#print "\t$_\n";
					#warn "$w $e <> $$ra[1]";
					if ( $e && $e ne '' && $e eq $$ra[1] ) # we have cracked it
					{
						$$ra[3]=1; # solved
						$$ra[4]=$pswds{$p};
						$pswds{$$ra[2]}=$pswds{$p};
						last;
					}
				}
				close CMD;
			}
			elsif ( $$ra[0] eq '6' ) # a type 5 MD5 ....
			{
#print "Testing $pswds{$p} $$ra[1]\n";
				my $passw = $pswds{$p} ;
				if ( length($passw) <16 )
				{
					$passw .= "\0" x (16-length($passw));  # pad with zeros
				}
				my $e= pseudo_base64(Digest::MD5::md5($passw));
				if ( $e ne '' && $e eq $$ra[1] ) # we have cracked it
				{
					$$ra[3]=1; # solved
					$$ra[4]=$pswds{$p};
					$pswds{$$ra[2]}=$pswds{$p};
				}
			}
		}
	}
#warn "not solved yet";
	# if still not solved....
	if ($$ra[3] == 0 ) # not solved yet
	{
		my $c=0;
		# try every word
		foreach my $p (keys %words)
		{
			next unless ($p =~/\w/);
			if ( $$ra[0] eq '4' && $$ra[1] eq Encode( $p ) ) # a type 4
			{
				# we have a type 4 match
				$$ra[3]=1; # solved
				$$ra[4]=$p;
				$pswds{$c++}=$p;
			}
			elsif ( $$ra[0] eq '5' ) # a type 5 ....
			{
				#warn join "<>", split (/\$/, $$ra[1]);
				my $salt = (split /\$/, $$ra[1])[2]; # pull out salt from type 5 hash
#print "Testing $pswds{$p} $$ra[1]\n";
				if ( !$salt )
				{
					warn "No salt found ??? $$ra[1] <> $$ra[2]";

				}
				open CMD, "openssl passwd -1 -salt $salt -table $p |" or next;
				while (<CMD>)
				{
					s/\r//msg;
					chomp;
					my ($w,$e) = split /\s+/,$_;
#print "\t$_\n";
					#warn "$w $e <> $$ra[1]";
					if ( $e eq $$ra[1] ) # we have cracked it
					{
						$$ra[3]=1; # solved
						$$ra[4]=$p;
						$pswds{$c++}=$p;
						last;
					}
				}
				close CMD;
			}
			elsif ( $$ra[0] eq '6' ) # a type 5 MD5 ....
			{
#print "Testing $pswds{$p} $$ra[1]\n";
				my $passw = $pswds{$p} ;
				next unless ( $passw && $passw ne '' );
				if ( length($passw) <16)
				{
					$passw .= "\0" x (16-length($passw));  # pad with zeros
				}
				my $e= pseudo_base64(Digest::MD5::md5($passw));
				if ( $e ne '' && $e eq $$ra[1] ) # we have cracked it
				{
					$$ra[3]=1; # solved
					$$ra[4]=$pswds{$p};
					$pswds{$$ra[2]}=$pswds{$p};
				}
			}
		}
#		print "longshot use of config file as a wordlist gave $c matches\n";
	}
	
}
my %OL ; # overlapping rules
# what passwords did we find and decrypt/decode
print "###################################\n";
print "Passwords found and decrypted\n";
print "###################################\n";
print join "\n", (map{ "FOUND:'$pswds{$_}' in $_" } keys %pswds), "\n";
print "###################################\n";
print "Group containing Groups analysis\n";
print "###################################\n";
# at this point the objects hash contains groups as keys pointing to arrays of network and port objects
# for each context
# set obj and containers
for (my $ctx =1; $ctx<=$contexts; $ctx++)
{
	print "###################################\n";
	print "###################################\n";
	print $cntxts[$ctx]{hostname},"\n";
	print "###################################\n";
	print "###################################\n";
	%objs = %{$cntxts[$ctx]{obj}};
	%containers = %{$cntxts[$ctx]{containers}};
	%ifs = %{$cntxts[$ctx]{interfaces}};
	@acls = @{$cntxts[$ctx]{acls}};
	print "\t###################################\n";
	print "\tGot groups\n";
	print "\t###################################\n\t";
	print join "\n\t", keys %objs, "\n";
	print "\t###################################\n";
	print "\tGot ACLs\n";
	print "\t###################################\n\t";

	print join  "\n\t",@acls,"\n";

	print "\t###################################\n";
	print "\tUnused Objects analysis\n";
	print "\t###################################\n";

	my %directlyUnused;
	# see if objects used directly
	foreach $obj ( keys %objs )
	{
		my $used=0;
		if ( $OF{$obj} )
		{
			$used=1;
		}
		if ( !$used)
		{
			$directlyUnused{ $obj}=1;
		}
	}

	# so check if enclosing groups have the object and they are directly used
	foreach my $d (keys %directlyUnused)
	{
		foreach my $c (keys %containers)
		{
			next if ($d eq $c);
			foreach my $o ( @{$containers{$c}} )
			{
				if ($d eq $o )
				{
					# unused group is contained
					# is the container unused?
					if ( exists $directlyUnused{ $c} )
					{
						$directlyUnused{ $c}=1;					
					}
					else
					{
						$directlyUnused{ $obj}=0;
					}
				}
			}
		}
	}
	foreach my $d (keys %directlyUnused)
	{
		if ($directlyUnused{$d} == 1)
		{
			print "\t$d object is not used in the configuration\n";
		}
	}
	print "\t###################################\n";
	print "\tOverly permissive rule analysis\n";
	print "\tThis will not pick up any any any\n";
	print "\t###################################\n";
	foreach my $acl (@acls)
	{
		# any destination
		if ($acl =~ /\s+permit\s+(ip|tcp|udp)\s+([^\s]+\s)+?any\s+/)
		{
			print "\tAny destination IP $acl\n";
		}
		# any source
		elsif ($acl =~ /\s+permit\s+(ip|tcp|udp).*?\s+any\s+/)
		{
			print "\tAny source IP $acl\n";
		}
		
	}
	print "\t###################################\n";
	print "\tOverlapping rules analysis\n";
	print "\tmatches objects against any rule as well\n";
	print "\tthis does not match services yet\n";
	print "\t###################################\n";
	my @missed;
	my @obj_types = ( 
					q/\bobject-group\s+([^\s]+)/,
					q/\b(any)\b/,
					q/\bhost\s+(\d+\.\d+\.\d+\.\d+)/,
					q/(\d+\.\d+\.\d+\.\d+\s+\d+\.\d+\.\d+\.\d+)/
					);
	my @service_types = (
						q/\b(range\s+\d+\s+\d+)/,
						q/\b(eq\s+[^\s]+)/,
						q/\b(any)\b/,
						q/\b(echo)\b/,
						q/\s*$/
					);
	my $proto_match = q/\s+([^\s]+)/;
	# create all the acl match variants
	my @acl_matches;
	foreach my $sobj (@obj_types)
	{
		foreach my $dobj (@obj_types)
		{
			foreach my $srv (@service_types)
			{
				if ( $srv eq q/\s*$/ )
				{
					$obj = $proto_match.q/\s+/.$sobj.q/\s+/.$dobj.q/(\s*)$/;
				}
				else
				{
					$obj = $proto_match.q/\s+/.$sobj.q/\s+/.$dobj.q/\s+/.$srv;
				}
				push @acl_matches, qr/$obj/;
			}
		}
	}
	# now match the acls to the standardised acl patterns to
	# create an array of an array, each row containing an acl split into 4: original acl, src, dest and service   
	my @simp_acls;
	foreach my $acl (@acls)
	{
		given ($acl)
		{
			when (@acl_matches)
			{
				push @simp_acls, [$acl, $2, $3, $4, $1 ];
			}
			default
			{
				push @missed, $acl;
			}
		}
	}
	my @temp_acls;
	# need to normalise the simplified acls - i.e. expand objects
	foreach my $racl (@simp_acls)
	{
		# foreach reference to an acl
		# see if src is a object
		if ( $$racl[1] =~ /[a-zA-Z]/ && $$racl[1] ne 'any'  )
		{
			$obj = $$racl[1];
			foreach my $o ( @{$objs{$obj}} )
			{
		# 	if it is expand src object into all its components and add to temp array
				$$racl[1]=$o;
				next unless ( $o =~/\// );
				# only interested in CIDR
				#print $o,"<SRC expand $obj\n";
				push @temp_acls, $racl;
			}
		}
		# else add to temp array
		else
		{
			if ( $$racl[1] !~ /\// && $$racl[1] !~ /^any$/ )
			{
				### need to make addresses CIDR
				if ( $$racl[1] =~ (/^\d+\.\d+\.\d+\.\d+$/))
				{
					$$racl[1].='/32';
					push @temp_acls, $racl ;

				}
				### need to make address and masks CIDR
				elsif ( $$racl[1] =~ (/^(\d+\.\d+\.\d+\.\d+)\s+(\d+\.\d+\.\d+\.\d+)$/))
				{
	#warn "C $1 $2";
					$$racl[1]= Net::CIDR::addrandmask2cidr( $1, $2);
					push @temp_acls, $racl ;

				}
				else
				{
					warn "Bad Source IP ". $$racl[1];
				}
			}
			else
			{
				push @temp_acls, $racl ;
			}
		}
	}
	my @nacls;
	# take temp array and do same - expand any dest objs
	foreach my $racl (@temp_acls)
	{
		# foreach reference to an acl
		# see if dest is a object
		if ( $$racl[2] =~ /[a-zA-Z]/ && $$racl[2] ne 'any' )
		{
			$obj = $$racl[2];
			foreach my $o ( @{$objs{$obj}} )
			{
		# 	if it is expand dest object into all its components and add to norm array
				$$racl[2]=$o;
				next unless ( $o =~/\// );
				# only interested in CIDR
				#print $o,"<DEST expand $obj\n";
				push @nacls, $racl;
			}
		}
		# else add to normalised array
		else
		{
			if ( $$racl[2] !~ /\//  && $$racl[2] !~ /^any$/ )
			{
				### need to make addresses CIDR
				if ( $$racl[2] =~ (/^\d+\.\d+\.\d+\.\d+$/))
				{
					$$racl[2].='/32';
					push @nacls, $racl ;

				}
				### need to make address and masks CIDR
				elsif ( $$racl[2] =~ (/^(\d+\.\d+\.\d+\.\d+)\s+(\d+\.\d+\.\d+\.\d+)$/))
				{
	#warn "D $1 $2";
					$$racl[2]= Net::CIDR::addrandmask2cidr( $1, $2);
					push @nacls, $racl ;

				}
				else
				{
				#	warn "Bad Source IP ". $$racl[2];
				}
			}
			else
			{
				push @nacls, $racl ;
			}
		}
	}

	# step through normalised acls and compare with other acls to see if overlap
	for ( my $j=0 ; $j< scalar @nacls; $j++)
	{
		for ( my $k=$j+1; $k< scalar @nacls; $k++)
		{
			# if same interface?
			my $ifj = @{$nacls[$j]}[0];
			my $ifk = @{$nacls[$k]}[0];
			$ifj =~ s/^\d+\s+//;
			$ifk =~ s/^\d+\s+//;
			$ifj =~ s/\s+.*$//;
			$ifk =~ s/\s+.*$//;
			
			if ( $ifj ne $ifk )
			{
				next;
			}
			if ( $debug)
			{
			# are source IPs the same or contained within or a match an 'any' rule
				if ( @{$nacls[$j]}[1] eq 'any' || @{$nacls[$k]}[1] eq 'any'  
					|| Net::CIDR::cidrlookup( @{$nacls[$j]}[1], @{$nacls[$k]}[1] ) )
				{
				# IP has been seen earlier
				# so check if same protocol and interface
					@{$nacls[$k]}[0] =~ /^(\d+)/;
					my $rule1=$1;
					@{$nacls[$j]}[0] =~ /^(\d+)/;
					my $rule2=$1;
					if ( @{$nacls[$j]}[4] eq @{$nacls[$k]}[4] && !$pairs{$rule1."__".$rule2})
					{
						print "\tOverlapping source IP rule overlap, ";
						print "affects rules:\n\t\t@{$nacls[$k]}[0]\n\t\t@{$nacls[$j]}[0]\n";
						my $r;
						if (@{$nacls[$k]}[0] =~ /^(\d+)/ )
						{
							print "\t\t$1 $rules{$1}\n";
							$r="$1 $rules{$1}";
						}
                                                if (@{$nacls[$j]}[0] =~ /^(\d+)/)
						{
							print "\t\t$1 $rules{$1}\n";
							push @{$OL{"$1 $rules{$1}"}}, $r;
							push @{$OL{$r}},"$1 $rules{$1}";
						}
						$pairs{$rule1."__".$rule2}=1;
					}
			
				}
			# are dest IPs the same or contained within or a match an 'any' rule
				if ( @{$nacls[$j]}[2] eq 'any' || @{$nacls[$k]}[2] eq 'any'  
					|| Net::CIDR::cidrlookup( @{$nacls[$j]}[2], @{$nacls[$k]}[2] ) )
				{
				# IP has been seen earlier
				# so check if same protocol
					@{$nacls[$k]}[0] =~ /^(\d+)/;
					my $rule1=$1;
					@{$nacls[$j]}[0] =~ /^(\d+)/;
					my $rule2=$1;
					if ( @{$nacls[$j]}[4] eq @{$nacls[$k]}[4] && !$pairs{$rule1."__".$rule2})
					{
						print "\tOverlapping dest IP rule overlap, ";
						print "affects rules:\n\t\t@{$nacls[$k]}[0]\n\t\t@{$nacls[$j]}[0]\n";
						my $r;
						if (@{$nacls[$k]}[0] =~ /^(\d+)/ )
						{
							print "\t\t$1 $rules{$1}\n";
							$r="$1 $rules{$1}";
						}
                                                if (@{$nacls[$j]}[0] =~ /^(\d+)/)
						{
							print "\t\t$1 $rules{$1}\n";
							push @{$OL{"$1 $rules{$1}"}}, $r;
							push @{$OL{$r}},"$1 $rules{$1}";
						}
						$pairs{$rule1."__".$rule2}=1;
					}
				}
			}
			# do src and dest overlap?
			if ( (@{$nacls[$j]}[1] eq 'any' || @{$nacls[$k]}[1] eq 'any'  
					|| Net::CIDR::cidrlookup( @{$nacls[$j]}[1], @{$nacls[$k]}[1] ) )
			&& ( @{$nacls[$j]}[2] eq 'any' || @{$nacls[$k]}[2] eq 'any'  
					|| Net::CIDR::cidrlookup( @{$nacls[$j]}[2], @{$nacls[$k]}[2] ) )
			&& ( @{$nacls[$k]}[0] ne @{$nacls[$j]}[0]))
			{
				# IP has been seen earlier
				# so check if same protocol
				@{$nacls[$k]}[0] =~ /^(\d+)/;
				my $rule1=$1;
				@{$nacls[$j]}[0] =~ /^(\d+)/;
				my $rule2=$1;
				if ( @{$nacls[$j]}[4] eq @{$nacls[$k]}[4] && !$pairs{$rule1."__".$rule2})
				{
					print "\tOverlapping SRC and DEST IP rule overlap, ";
					print "affects rules:\n\t\t@{$nacls[$k]}[0]\n\t\t@{$nacls[$j]}[0]\n";
					my $r;
					if (@{$nacls[$k]}[0] =~ /^(\d+)/ )
					{
						print "\t\t$1 $rules{$1}\n";
						$r="$1 $rules{$1}";
					}
					if (@{$nacls[$j]}[0] =~ /^(\d+)/)
					{
						print "\t\t$1 $rules{$1}\n";
						push @{$OL{"$1 $rules{$1}"}}, $r;
						push @{$OL{$r}},"$1 $rules{$1}";
					}
					$pairs{$rule1."__".$rule2}=1;
				}
			
			}

		}
	}
	print "\t###################################\n";
	print "\tOverlapping rules analysis\n";
	print "\tmatches objects against any rule as well\n";
	print "\tthis does not match services yet\n";
	print "\t###################################\n";
	foreach my $r (sort keys %OL)
	{
		print "\t\t$r overlaps:\n";
		foreach (@{$OL{$r}})
		{
			print "\t\t\t$_\n";
		}
	}
	print "\t###################################\n";
	print "\tACLs that we failed to understand in overlap analysis, please manually verify\n";
	print "\t###################################\n\t";
	print join "\n\t", @missed, "\n";
	print "\t###################################\n";
	print "\t###################################\n";
	print "Physical connections\n";
	foreach $if (keys %ifs)
	{
		#next if ($ifs{$if}{IP} eq '' );
		if ($contexts ==1 )
		{
			print "\t$cntxts[1]{hostname} $if\n";
		}
		else
		{
			print "\t$cntxts[1]{hostname} $cntxts[$ctx]{hostname} $if\n";
		}
		if (!exists $ifs{$if}{Name} )
		{
			$ifs{$if}{Name} = $if;
		}
		print "\t\t$ifs{$if}{Name} aka ".(exists $ifs{$if}{IPRange}? $ifs{$if}{IPRange} : $if)."\n";
		# routes
		foreach my $rroute ( @{$ifs{$if}{Route}} )
		{
			print "\t\t\tRoutes ",Net::CIDR::addrandmask2cidr(@{$$rroute}[0],@{$$rroute}[1]),"  via @{$$rroute}[2]\n";
		}

		# limited to ACLs
		print "\t\t\tACLs Allows Connection From:\n";
		foreach my $acl ( @{$ifs{$if}{ACL}{in}{ACLName}} )
		{
			if (ref $acl )
			{
				foreach my $acls (@$$acl)
				{
					my $scidr = Net::CIDR::addrandmask2cidr( (@{$acls})[3,5]);
					my $dcidr = Net::CIDR::addrandmask2cidr( (@{$acls})[7,9]);
#					next if ( $scidr eq $dcidr && $scidr eq "0.0.0.0/0" );
					print "\t\t\t\t\t$scidr to $dcidr\n";
				}
			}
			else
			{
				print "\t\t\t\t$acl\n";
			}
		}
		
	} 
	print "###################################\n";
}
