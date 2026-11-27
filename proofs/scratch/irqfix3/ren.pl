#!/usr/bin/perl -p
s/\bValidIrqHandlers\b/ValidIrqHandlersL/g;
s/\b(CA|VH|VI|RM|HK|HKM|CnCA|IhCA|RDPost|ESQ)\b/$1L/g;
s/\bInvCAd\b/InvCALd/g;
s/\bvi_/vil_/g; s/\bvh_/vhl_/g; s/\bca_/cal_/g; s/\brm_/rml_/g; s/\bhk_/hkl_/g; s/\bvimh_/vimhl_/g; s/\bvhu_/vhlu_/g;
s/\bokv_(lookupCap|lookupExtraCaps|deriveCap|getCap|decodeCnode|step)\b/okvl_$1/g;
s/\bokd_(decodeCnode|decodeIrqHandler|fl4Decode)\b/okdl_$1/g;
s/\b(ikp_vh_and|ik_vh_weaken|ik_bind_vh_carry)\b/{my $x=$1; $x=~s#vh#vhl#; $x}/ge;
s/\bvih_of_hV\b/vihl_of_hV/g;
s/\b(ht_recDelF|ht_recDelF_fin|ik_of_ht_rd|ht_of_ik_rd)\b/$1L/g;
s/\b(kentry_validIrqMasks|kirq_validIrqMasks|kentry_vih|kirq_vih)\b/$1L/g;
s/\bcal_side\b/cal_side/g;
s/namespace Fl4Proofs\.P3\.SInvV$/namespace Fl4Proofs.P3.SInvVL/; s/end Fl4Proofs\.P3\.SInvV$/end Fl4Proofs.P3.SInvVL/;
