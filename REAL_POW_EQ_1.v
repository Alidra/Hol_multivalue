Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_POW_EQ_1_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import REAL_POW_EQ_1_IMP_spec.
Require Import REAL_POW_NEG_spec.
Require Import REAL_POW_ONE_spec.
Require Import thm0_spec.
Require Import thm1006570_spec.
Require Import thm1007663_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1344310_spec.
Require Import thm1344311_spec.
Require Import thm13473_spec.
Require Import thm1365105_spec.
Require Import thm1365990_spec.
Require Import thm1366270_spec.
Require Import thm1366271_spec.
Require Import thm1366974_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1367763_spec.
Require Import thm1386578_spec.
Require Import thm1396750_spec.
Require Import thm1482981_spec.
Require Import thm1483436_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483450_spec.
Require Import thm1483460_spec.
Require Import thm1483476_spec.
Require Import thm1483480_spec.
Require Import thm1483488_spec.
Require Import thm1483508_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483521_spec.
Require Import thm1483525_spec.
Require Import thm1483527_spec.
Require Import thm1483529_spec.
Require Import thm1483531_spec.
Require Import thm1483554_spec.
Require Import thm1483568_spec.
Require Import thm1483574_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm1821_spec.
Require Import thm1823_spec.
Require Import thm1832_spec.
Require Import thm1834_spec.
Require Import thm1842_spec.
Require Import thm1855_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18946_spec.
Require Import thm18947_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm19158_spec.
Require Import thm19367_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm706885_spec.
Require Import thm82_spec.
Require Import thm912739_spec.
Require Import thm912803_spec.
Require Import thm940073_spec.
Require Import thm996238_spec.
Lemma lem1653684 (x : real) (a : real) : (term0 x a) = (term1 x a).
Proof. exact (@lem17160 (x = a) (x = (real_neg a))). Qed.
Lemma lem1653686 (x : real) (a : real) : (term2 x a) = (term2 x a).
Proof. exact (eq_refl (term2 x a)). Qed.
Lemma lem1653687 (x : real) (a : real) : (term3 x a) = (term4 x a).
Proof. exact (MK_COMB (@lem1653686 x a) (@lem1653684 x a)). Qed.
Lemma lem1653688 (x : real) (a : real) : (term5 x a) = (term3 x a).
Proof. exact (@lem17362 ((real_abs x) = a) (term6 x a)). Qed.
Lemma lem1653704 (x : real) (a : real) : (term5 x a) = (term4 x a).
Proof. exact (TRANS (@lem1653688 x a) (@lem1653687 x a)). Qed.
Lemma lem1653705 (x : real) (a : real) : ((real_abs x) = a) = ((term7 x a) = term8).
Proof. exact (@lem1483529 (real_abs x) a). Qed.
Lemma lem1653711 (x : real) (a : real) : (term7 x a) = (term9 x a).
Proof. exact (@lem1483519 (real_abs x) a). Qed.
Lemma lem1653716 (a : real) (x : real) : (term9 x a) = (term10 a x).
Proof. exact (@lem1483488 (term11 a) (real_abs x)). Qed.
Lemma lem1653718 (a : real) (x : real) : (term7 x a) = (term10 a x).
Proof. exact (TRANS (@lem1653711 x a) (@lem1653716 a x)). Qed.
Lemma lem1653719 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1653720 (a : real) (x : real) : (term12 x a) = (term13 a x).
Proof. exact (MK_COMB (@lem1653719) (@lem1653718 a x)). Qed.
Lemma lem1653721 : term8 = term8.
Proof. exact (eq_refl term8). Qed.
Lemma lem1653722 (a : real) (x : real) : ((term7 x a) = term8) = ((term10 a x) = term8).
Proof. exact (MK_COMB (@lem1653720 a x) (@lem1653721)). Qed.
Lemma lem1653723 (a : real) (x : real) : ((real_abs x) = a) = ((term10 a x) = term8).
Proof. exact (TRANS (@lem1653705 x a) (@lem1653722 a x)). Qed.
Lemma lem1653724 (x : real) (a : real) : (term14 x a) = (term15 x a).
Proof. exact (@lem1483554 x a). Qed.
Lemma lem1653730 (x : real) (a : real) : (real_sub x a) = (term16 x a).
Proof. exact (@lem1483519 x a). Qed.
Lemma lem1653735 (a : real) (x : real) : (term16 x a) = (term17 a x).
Proof. exact (@lem1483488 (term11 a) x). Qed.
Lemma lem1653737 (a : real) (x : real) : (real_sub x a) = (term17 a x).
Proof. exact (TRANS (@lem1653730 x a) (@lem1653735 a x)). Qed.
Lemma lem1653738 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1653739 (a : real) (x : real) : (term18 x a) = (term19 a x).
Proof. exact (MK_COMB (@lem1653738) (@lem1653737 a x)). Qed.
Lemma lem1653740 (a : real) (x : real) : (term19 a x) = (term20 a x).
Proof. exact (@lem1483512 (term17 a x)). Qed.
Lemma lem1653741 (a : real) (x : real) : (term20 a x) = (term21 a x).
Proof. exact (@lem1483508 (term11 a) term22 x). Qed.
Lemma lem1653742 (x : real) : (term11 x) = (term11 x).
Proof. exact (eq_refl (term11 x)). Qed.
Lemma lem1653743 (a : real) : (term23 a) = (term24 a).
Proof. exact (@lem1483476 term22 term22 a). Qed.
Lemma lem1653745 (m : nat) (n : nat) : (term25 m n) = (term26 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1653746 : term27 = term28.
Proof. exact (@lem1653745 term29 term29). Qed.
Lemma lem1653747 : (term30 = (BIT1 0)) = (term31 = term29).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1653748 : term31 = term29.
Proof. exact (EQ_MP (@lem1653747) (@lem940073)). Qed.
Lemma lem1653749 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1653750 : term28 = term32.
Proof. exact (MK_COMB (@lem1653749) (@lem1653748)). Qed.
Lemma lem1653751 : term27 = term32.
Proof. exact (TRANS (@lem1653746) (@lem1653750)). Qed.
Lemma lem1653752 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1653753 : term33 = term34.
Proof. exact (MK_COMB (@lem1653752) (@lem1653751)). Qed.
Lemma lem1653754 (a : real) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1653755 (a : real) : (term24 a) = (term35 a).
Proof. exact (MK_COMB (@lem1653753) (@lem1653754 a)). Qed.
Lemma lem1653756 (a : real) : (term23 a) = (term35 a).
Proof. exact (TRANS (@lem1653743 a) (@lem1653755 a)). Qed.
Lemma lem1653757 (a : real) : (term35 a) = a.
Proof. exact (@lem1483436 a). Qed.
Lemma lem1653758 (a : real) : (term23 a) = a.
Proof. exact (TRANS (@lem1653756 a) (@lem1653757 a)). Qed.
Lemma lem1653759 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1653760 (a : real) : (term36 a) = (real_add a).
Proof. exact (MK_COMB (@lem1653759) (@lem1653758 a)). Qed.
Lemma lem1653761 (a : real) (x : real) : (term21 a x) = (term16 a x).
Proof. exact (MK_COMB (@lem1653760 a) (@lem1653742 x)). Qed.
Lemma lem1653762 (a : real) (x : real) : (term20 a x) = (term16 a x).
Proof. exact (TRANS (@lem1653741 a x) (@lem1653761 a x)). Qed.
Lemma lem1653763 (a : real) (x : real) : (term19 a x) = (term16 a x).
Proof. exact (TRANS (@lem1653740 a x) (@lem1653762 a x)). Qed.
Lemma lem1653764 (x : real) (a : real) : (term37 x a) = (term37 x a).
Proof. exact (eq_refl (term37 x a)). Qed.
Lemma lem1653765 (a : real) (x : real) : ((term18 x a) = (term19 a x)) = ((term18 x a) = (term16 a x)).
Proof. exact (MK_COMB (@lem1653764 x a) (@lem1653763 a x)). Qed.
Lemma lem1653766 (a : real) (x : real) : (term18 x a) = (term16 a x).
Proof. exact (EQ_MP (@lem1653765 a x) (@lem1653739 a x)). Qed.
Lemma lem1653767 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1653768 (a : real) (x : real) : (term38 x a) = (term39 a x).
Proof. exact (MK_COMB (@lem1653767) (@lem1653766 a x)). Qed.
Lemma lem1653769 : term8 = term8.
Proof. exact (eq_refl term8). Qed.
Lemma lem1653770 (a : real) (x : real) : (term40 x a) = (term41 a x).
Proof. exact (MK_COMB (@lem1653768 a x) (@lem1653769)). Qed.
Lemma lem1653771 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1653772 (a : real) (x : real) : (term42 x a) = (term43 a x).
Proof. exact (MK_COMB (@lem1653771) (@lem1653737 a x)). Qed.
Lemma lem1653773 : term8 = term8.
Proof. exact (eq_refl term8). Qed.
Lemma lem1653774 (a : real) (x : real) : (term44 x a) = (term45 a x).
Proof. exact (MK_COMB (@lem1653772 a x) (@lem1653773)). Qed.
Lemma lem1653775 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1653776 (a : real) (x : real) : (term46 x a) = (term47 a x).
Proof. exact (MK_COMB (@lem1653775) (@lem1653774 a x)). Qed.
Lemma lem1653777 (a : real) (x : real) : (term15 x a) = (term48 a x).
Proof. exact (MK_COMB (@lem1653776 a x) (@lem1653770 a x)). Qed.
Lemma lem1653778 (a : real) (x : real) : (term14 x a) = (term48 a x).
Proof. exact (TRANS (@lem1653724 x a) (@lem1653777 a x)). Qed.
Lemma lem1653779 (x : real) (a : real) : (term49 x a) = (term50 x a).
Proof. exact (@lem1483554 x (real_neg a)). Qed.
Lemma lem1653786 (a : real) : (real_neg a) = (term11 a).
Proof. exact (@lem1483512 a). Qed.
Lemma lem1653789 (x : real) : (real_sub x) = (real_sub x).
Proof. exact (eq_refl (real_sub x)). Qed.
Lemma lem1653790 (x : real) (a : real) : (term51 x a) = (term52 x a).
Proof. exact (MK_COMB (@lem1653789 x) (@lem1653786 a)). Qed.
Lemma lem1653791 (x : real) (a : real) : (term52 x a) = (term53 x a).
Proof. exact (@lem1483519 x (term11 a)). Qed.
Lemma lem1653792 (a : real) : (term23 a) = (term24 a).
Proof. exact (@lem1483476 term22 term22 a). Qed.
Lemma lem1653794 (m : nat) (n : nat) : (term25 m n) = (term26 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1653795 : term27 = term28.
Proof. exact (@lem1653794 term29 term29). Qed.
Lemma lem1653796 : (term30 = (BIT1 0)) = (term31 = term29).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1653797 : term31 = term29.
Proof. exact (EQ_MP (@lem1653796) (@lem940073)). Qed.
Lemma lem1653798 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1653799 : term28 = term32.
Proof. exact (MK_COMB (@lem1653798) (@lem1653797)). Qed.
Lemma lem1653800 : term27 = term32.
Proof. exact (TRANS (@lem1653795) (@lem1653799)). Qed.
Lemma lem1653801 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1653802 : term33 = term34.
Proof. exact (MK_COMB (@lem1653801) (@lem1653800)). Qed.
Lemma lem1653803 (a : real) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1653804 (a : real) : (term24 a) = (term35 a).
Proof. exact (MK_COMB (@lem1653802) (@lem1653803 a)). Qed.
Lemma lem1653805 (a : real) : (term23 a) = (term35 a).
Proof. exact (TRANS (@lem1653792 a) (@lem1653804 a)). Qed.
Lemma lem1653806 (a : real) : (term35 a) = a.
Proof. exact (@lem1483436 a). Qed.
Lemma lem1653807 (a : real) : (term23 a) = a.
Proof. exact (TRANS (@lem1653805 a) (@lem1653806 a)). Qed.
Lemma lem1653808 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1653809 (x : real) (a : real) : (term53 x a) = (real_add x a).
Proof. exact (MK_COMB (@lem1653808 x) (@lem1653807 a)). Qed.
Lemma lem1653810 (a : real) (x : real) : (real_add x a) = (real_add a x).
Proof. exact (@lem1483488 a x). Qed.
Lemma lem1653811 (a : real) (x : real) : (term53 x a) = (real_add a x).
Proof. exact (TRANS (@lem1653809 x a) (@lem1653810 a x)). Qed.
Lemma lem1653812 (a : real) (x : real) : (term52 x a) = (real_add a x).
Proof. exact (TRANS (@lem1653791 x a) (@lem1653811 a x)). Qed.
Lemma lem1653813 (a : real) (x : real) : (term51 x a) = (real_add a x).
Proof. exact (TRANS (@lem1653790 x a) (@lem1653812 a x)). Qed.
Lemma lem1653814 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1653815 (a : real) (x : real) : (term54 x a) = (term55 a x).
Proof. exact (MK_COMB (@lem1653814) (@lem1653813 a x)). Qed.
Lemma lem1653816 (a : real) (x : real) : (term55 a x) = (term56 a x).
Proof. exact (@lem1483512 (real_add a x)). Qed.
Lemma lem1653823 (a : real) (x : real) : (term56 a x) = (term57 a x).
Proof. exact (@lem1483508 a term22 x). Qed.
Lemma lem1653824 (a : real) (x : real) : (term55 a x) = (term57 a x).
Proof. exact (TRANS (@lem1653816 a x) (@lem1653823 a x)). Qed.
Lemma lem1653825 (x : real) (a : real) : (term58 x a) = (term58 x a).
Proof. exact (eq_refl (term58 x a)). Qed.
Lemma lem1653826 (a : real) (x : real) : ((term54 x a) = (term55 a x)) = ((term54 x a) = (term57 a x)).
Proof. exact (MK_COMB (@lem1653825 x a) (@lem1653824 a x)). Qed.
Lemma lem1653827 (a : real) (x : real) : (term54 x a) = (term57 a x).
Proof. exact (EQ_MP (@lem1653826 a x) (@lem1653815 a x)). Qed.
Lemma lem1653828 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1653829 (a : real) (x : real) : (term59 x a) = (term60 a x).
Proof. exact (MK_COMB (@lem1653828) (@lem1653827 a x)). Qed.
Lemma lem1653830 : term8 = term8.
Proof. exact (eq_refl term8). Qed.
Lemma lem1653831 (a : real) (x : real) : (term61 x a) = (term62 a x).
Proof. exact (MK_COMB (@lem1653829 a x) (@lem1653830)). Qed.
Lemma lem1653832 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1653833 (a : real) (x : real) : (term63 x a) = (term64 a x).
Proof. exact (MK_COMB (@lem1653832) (@lem1653813 a x)). Qed.
Lemma lem1653834 : term8 = term8.
Proof. exact (eq_refl term8). Qed.
Lemma lem1653835 (a : real) (x : real) : (term65 x a) = (term66 a x).
Proof. exact (MK_COMB (@lem1653833 a x) (@lem1653834)). Qed.
Lemma lem1653836 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1653837 (a : real) (x : real) : (term67 x a) = (term68 a x).
Proof. exact (MK_COMB (@lem1653836) (@lem1653835 a x)). Qed.
Lemma lem1653838 (a : real) (x : real) : (term50 x a) = (term69 a x).
Proof. exact (MK_COMB (@lem1653837 a x) (@lem1653831 a x)). Qed.
Lemma lem1653839 (a : real) (x : real) : (term49 x a) = (term69 a x).
Proof. exact (TRANS (@lem1653779 x a) (@lem1653838 a x)). Qed.
Lemma lem1653840 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1653841 (a : real) (x : real) : (term70 x a) = (term71 a x).
Proof. exact (MK_COMB (@lem1653840) (@lem1653778 a x)). Qed.
Lemma lem1653842 (a : real) (x : real) : (term1 x a) = (term72 a x).
Proof. exact (MK_COMB (@lem1653841 a x) (@lem1653839 a x)). Qed.
Lemma lem1653843 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1653844 (a : real) (x : real) : (term2 x a) = (term73 a x).
Proof. exact (MK_COMB (@lem1653843) (@lem1653723 a x)). Qed.
Lemma lem1653845 (a : real) (x : real) : (term4 x a) = (term74 a x).
Proof. exact (MK_COMB (@lem1653844 a x) (@lem1653842 a x)). Qed.
Lemma lem1653852 (a : real) (x : real) : (term5 x a) = (term74 a x).
Proof. exact (TRANS (@lem1653704 x a) (@lem1653845 a x)). Qed.
Lemma lem1653866 (a : real) (x : real) : (term72 a x) = (term75 a x).
Proof. exact (@lem19158 (term66 a x) (term48 a x) (term62 a x)). Qed.
Lemma lem1653873 (a : real) (x : real) : (term76 a x) = (term77 a x).
Proof. exact (@lem19367 (term45 a x) (term41 a x) (term62 a x)). Qed.
Lemma lem1653880 (a : real) (x : real) : (term78 a x) = (term79 a x).
Proof. exact (@lem19367 (term45 a x) (term41 a x) (term66 a x)). Qed.
Lemma lem1653881 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1653882 (a : real) (x : real) : (term80 a x) = (term81 a x).
Proof. exact (MK_COMB (@lem1653881) (@lem1653880 a x)). Qed.
Lemma lem1653883 (a : real) (x : real) : (term75 a x) = (term82 a x).
Proof. exact (MK_COMB (@lem1653882 a x) (@lem1653873 a x)). Qed.
Lemma lem1653885 (a : real) (x : real) : (term72 a x) = (term82 a x).
Proof. exact (TRANS (@lem1653866 a x) (@lem1653883 a x)). Qed.
Lemma lem1653888 (a : real) (x : real) : (term73 a x) = (term73 a x).
Proof. exact (eq_refl (term73 a x)). Qed.
Lemma lem1653889 (a : real) (x : real) : (term74 a x) = (term83 a x).
Proof. exact (MK_COMB (@lem1653888 a x) (@lem1653885 a x)). Qed.
Lemma lem1653890 (a : real) (x : real) : (term83 a x) = (term84 a x).
Proof. exact (@lem19158 (term79 a x) ((term10 a x) = term8) (term77 a x)). Qed.
Lemma lem1653897 (a : real) (x : real) : (term85 a x) = (term86 a x).
Proof. exact (@lem19158 (term87 a x) ((term10 a x) = term8) (term88 a x)). Qed.
Lemma lem1653904 (a : real) (x : real) : (term89 a x) = (term90 a x).
Proof. exact (@lem19158 (term91 a x) ((term10 a x) = term8) (term92 a x)). Qed.
Lemma lem1653905 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1653906 (a : real) (x : real) : (term93 a x) = (term94 a x).
Proof. exact (MK_COMB (@lem1653905) (@lem1653904 a x)). Qed.
Lemma lem1653907 (a : real) (x : real) : (term84 a x) = (term95 a x).
Proof. exact (MK_COMB (@lem1653906 a x) (@lem1653897 a x)). Qed.
Lemma lem1653908 (a : real) (x : real) : (term83 a x) = (term95 a x).
Proof. exact (TRANS (@lem1653890 a x) (@lem1653907 a x)). Qed.
Lemma lem1653909 (a : real) (x : real) : (term74 a x) = (term95 a x).
Proof. exact (TRANS (@lem1653889 a x) (@lem1653908 a x)). Qed.
Lemma lem1653910 (a : real) (x : real) : (term5 x a) = (term95 a x).
Proof. exact (TRANS (@lem1653852 a x) (@lem1653909 a x)). Qed.
Lemma lem1653912 (a : real) (x : real) : (term96 a x) = (term97 a x).
Proof. exact (eq_refl (term96 a x)). Qed.
Lemma lem1653913 (a : real) (x : real) : (term97 a x) = (term96 a x).
Proof. exact (SYM (@lem1653912 a x)). Qed.
Lemma lem1653914 (a : real) (x : real) : (term96 a x) = (term98 a x).
Proof. exact (@lem1482981 (term99 a x) x). Qed.
Lemma lem1653915 (a : real) (x : real) : (term97 a x) = (term98 a x).
Proof. exact (TRANS (@lem1653913 a x) (@lem1653914 a x)). Qed.
Lemma lem1653916 (a : real) (x : real) : (term100 a x) = (term101 a x).
Proof. exact (eq_refl (term100 a x)). Qed.
Lemma lem1653917 (x : real) : (term102 x) = (term102 x).
Proof. exact (eq_refl (term102 x)). Qed.
Lemma lem1653918 (a : real) (x : real) : (term103 a x) = (term104 a x).
Proof. exact (MK_COMB (@lem1653917 x) (@lem1653916 a x)). Qed.
Lemma lem1653919 (a : real) (x : real) : (term105 a x) = (term106 a x).
Proof. exact (eq_refl (term105 a x)). Qed.
Lemma lem1653920 (x : real) : (term107 x) = (term107 x).
Proof. exact (eq_refl (term107 x)). Qed.
Lemma lem1653921 (a : real) (x : real) : (term108 a x) = (term109 a x).
Proof. exact (MK_COMB (@lem1653920 x) (@lem1653919 a x)). Qed.
Lemma lem1653922 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1653923 (a : real) (x : real) : (term110 a x) = (term111 a x).
Proof. exact (MK_COMB (@lem1653922) (@lem1653921 a x)). Qed.
Lemma lem1653924 (a : real) (x : real) : (term98 a x) = (term112 a x).
Proof. exact (MK_COMB (@lem1653923 a x) (@lem1653918 a x)). Qed.
Lemma lem1653925 (a : real) (x : real) : (term113 a x) = (term113 a x).
Proof. exact (eq_refl (term113 a x)). Qed.
Lemma lem1653926 (a : real) (x : real) : ((term97 a x) = (term98 a x)) = ((term97 a x) = (term112 a x)).
Proof. exact (MK_COMB (@lem1653925 a x) (@lem1653924 a x)). Qed.
Lemma lem1653927 (a : real) (x : real) : (term97 a x) = (term112 a x).
Proof. exact (EQ_MP (@lem1653926 a x) (@lem1653915 a x)). Qed.
Lemma lem1653928 (x : real) : (term114 x) = (term115 x).
Proof. exact (@lem1483527 x term8). Qed.
Lemma lem1653934 (x : real) : (term116 x) = (term117 x).
Proof. exact (@lem1483519 x term8). Qed.
Lemma lem1653936 (x : nat) : (term118 x) = term8.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1653937 : term119 = term8.
Proof. exact (@lem1653936 term29). Qed.
Lemma lem1653938 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1653939 (x : real) : (term117 x) = (term120 x).
Proof. exact (MK_COMB (@lem1653938 x) (@lem1653937)). Qed.
Lemma lem1653940 (x : real) : (term120 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1653941 (x : real) : (term117 x) = x.
Proof. exact (TRANS (@lem1653939 x) (@lem1653940 x)). Qed.
Lemma lem1653943 (x : real) : (term116 x) = x.
Proof. exact (TRANS (@lem1653934 x) (@lem1653941 x)). Qed.
Lemma lem1653944 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1653945 (x : real) : (term121 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1653944) (@lem1653943 x)). Qed.
Lemma lem1653946 : term8 = term8.
Proof. exact (eq_refl term8). Qed.
Lemma lem1653947 (x : real) : (term115 x) = (term114 x).
Proof. exact (MK_COMB (@lem1653945 x) (@lem1653946)). Qed.
Lemma lem1653948 (x : real) : (term114 x) = (term114 x).
Proof. exact (TRANS (@lem1653928 x) (@lem1653947 x)). Qed.
Lemma lem1653949 (a : real) (x : real) : ((term17 a x) = term8) = ((term122 a x) = term8).
Proof. exact (@lem1483529 (term17 a x) term8). Qed.
Lemma lem1653967 (a : real) (x : real) : (term122 a x) = (term123 a x).
Proof. exact (@lem1483519 (term17 a x) term8). Qed.
Lemma lem1653969 (x : nat) : (term118 x) = term8.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1653970 : term119 = term8.
Proof. exact (@lem1653969 term29). Qed.
Lemma lem1653971 (a : real) (x : real) : (term124 a x) = (term124 a x).
Proof. exact (eq_refl (term124 a x)). Qed.
Lemma lem1653972 (a : real) (x : real) : (term123 a x) = (term125 a x).
Proof. exact (MK_COMB (@lem1653971 a x) (@lem1653970)). Qed.
Lemma lem1653973 (a : real) (x : real) : (term125 a x) = (term17 a x).
Proof. exact (@lem1483450 (term17 a x)). Qed.
Lemma lem1653974 (a : real) (x : real) : (term123 a x) = (term17 a x).
Proof. exact (TRANS (@lem1653972 a x) (@lem1653973 a x)). Qed.
Lemma lem1653976 (a : real) (x : real) : (term122 a x) = (term17 a x).
Proof. exact (TRANS (@lem1653967 a x) (@lem1653974 a x)). Qed.
Lemma lem1653977 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1653978 (a : real) (x : real) : (term126 a x) = (term127 a x).
Proof. exact (MK_COMB (@lem1653977) (@lem1653976 a x)). Qed.
Lemma lem1653979 : term8 = term8.
Proof. exact (eq_refl term8). Qed.
Lemma lem1653980 (a : real) (x : real) : ((term122 a x) = term8) = ((term17 a x) = term8).
Proof. exact (MK_COMB (@lem1653978 a x) (@lem1653979)). Qed.
Lemma lem1653981 (a : real) (x : real) : ((term17 a x) = term8) = ((term17 a x) = term8).
Proof. exact (TRANS (@lem1653949 a x) (@lem1653980 a x)). Qed.
Lemma lem1653982 (a : real) (x : real) : (term45 a x) = (term128 a x).
Proof. exact (@lem1483525 (term17 a x) term8). Qed.
Lemma lem1654000 (a : real) (x : real) : (term122 a x) = (term123 a x).
Proof. exact (@lem1483519 (term17 a x) term8). Qed.
Lemma lem1654002 (x : nat) : (term118 x) = term8.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1654003 : term119 = term8.
Proof. exact (@lem1654002 term29). Qed.
Lemma lem1654004 (a : real) (x : real) : (term124 a x) = (term124 a x).
Proof. exact (eq_refl (term124 a x)). Qed.
Lemma lem1654005 (a : real) (x : real) : (term123 a x) = (term125 a x).
Proof. exact (MK_COMB (@lem1654004 a x) (@lem1654003)). Qed.
Lemma lem1654006 (a : real) (x : real) : (term125 a x) = (term17 a x).
Proof. exact (@lem1483450 (term17 a x)). Qed.
Lemma lem1654007 (a : real) (x : real) : (term123 a x) = (term17 a x).
Proof. exact (TRANS (@lem1654005 a x) (@lem1654006 a x)). Qed.
Lemma lem1654009 (a : real) (x : real) : (term122 a x) = (term17 a x).
Proof. exact (TRANS (@lem1654000 a x) (@lem1654007 a x)). Qed.
Lemma lem1654010 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1654011 (a : real) (x : real) : (term129 a x) = (term43 a x).
Proof. exact (MK_COMB (@lem1654010) (@lem1654009 a x)). Qed.
Lemma lem1654012 : term8 = term8.
Proof. exact (eq_refl term8). Qed.
Lemma lem1654013 (a : real) (x : real) : (term128 a x) = (term45 a x).
Proof. exact (MK_COMB (@lem1654011 a x) (@lem1654012)). Qed.
Lemma lem1654014 (a : real) (x : real) : (term45 a x) = (term45 a x).
Proof. exact (TRANS (@lem1653982 a x) (@lem1654013 a x)). Qed.
Lemma lem1654015 (a : real) (x : real) : (term66 a x) = (term130 a x).
Proof. exact (@lem1483525 (real_add a x) term8). Qed.
Lemma lem1654027 (a : real) (x : real) : (term131 a x) = (term132 a x).
Proof. exact (@lem1483519 (real_add a x) term8). Qed.
Lemma lem1654029 (x : nat) : (term118 x) = term8.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1654030 : term119 = term8.
Proof. exact (@lem1654029 term29). Qed.
Lemma lem1654031 (a : real) (x : real) : (term133 a x) = (term133 a x).
Proof. exact (eq_refl (term133 a x)). Qed.
Lemma lem1654032 (a : real) (x : real) : (term132 a x) = (term134 a x).
Proof. exact (MK_COMB (@lem1654031 a x) (@lem1654030)). Qed.
Lemma lem1654033 (a : real) (x : real) : (term134 a x) = (real_add a x).
Proof. exact (@lem1483450 (real_add a x)). Qed.
Lemma lem1654034 (a : real) (x : real) : (term132 a x) = (real_add a x).
Proof. exact (TRANS (@lem1654032 a x) (@lem1654033 a x)). Qed.
Lemma lem1654036 (a : real) (x : real) : (term131 a x) = (real_add a x).
Proof. exact (TRANS (@lem1654027 a x) (@lem1654034 a x)). Qed.
Lemma lem1654037 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1654038 (a : real) (x : real) : (term135 a x) = (term64 a x).
Proof. exact (MK_COMB (@lem1654037) (@lem1654036 a x)). Qed.
Lemma lem1654039 : term8 = term8.
Proof. exact (eq_refl term8). Qed.
Lemma lem1654040 (a : real) (x : real) : (term130 a x) = (term66 a x).
Proof. exact (MK_COMB (@lem1654038 a x) (@lem1654039)). Qed.
Lemma lem1654041 (a : real) (x : real) : (term66 a x) = (term66 a x).
Proof. exact (TRANS (@lem1654015 a x) (@lem1654040 a x)). Qed.
Lemma lem1654042 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1654043 (a : real) (x : real) : (term136 a x) = (term136 a x).
Proof. exact (MK_COMB (@lem1654042) (@lem1654014 a x)). Qed.
Lemma lem1654044 (a : real) (x : real) : (term91 a x) = (term91 a x).
Proof. exact (MK_COMB (@lem1654043 a x) (@lem1654041 a x)). Qed.
Lemma lem1654045 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1654046 (a : real) (x : real) : (term137 a x) = (term137 a x).
Proof. exact (MK_COMB (@lem1654045) (@lem1653981 a x)). Qed.
Lemma lem1654047 (a : real) (x : real) : (term106 a x) = (term106 a x).
Proof. exact (MK_COMB (@lem1654046 a x) (@lem1654044 a x)). Qed.
Lemma lem1654048 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1654049 (x : real) : (term107 x) = (term107 x).
Proof. exact (MK_COMB (@lem1654048) (@lem1653948 x)). Qed.
Lemma lem1654050 (a : real) (x : real) : (term109 a x) = (term109 a x).
Proof. exact (MK_COMB (@lem1654049 x) (@lem1654047 a x)). Qed.
Lemma lem1654051 (x : real) : (term138 x) = (term139 x).
Proof. exact (@lem1483525 term8 x). Qed.
Lemma lem1654057 (x : real) : (term140 x) = (term141 x).
Proof. exact (@lem1483519 term8 x). Qed.
Lemma lem1654062 (x : real) : (term141 x) = (term11 x).
Proof. exact (@lem1483448 (term11 x)). Qed.
Lemma lem1654064 (x : real) : (term140 x) = (term11 x).
Proof. exact (TRANS (@lem1654057 x) (@lem1654062 x)). Qed.
Lemma lem1654065 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1654066 (x : real) : (term142 x) = (term143 x).
Proof. exact (MK_COMB (@lem1654065) (@lem1654064 x)). Qed.
Lemma lem1654067 : term8 = term8.
Proof. exact (eq_refl term8). Qed.
Lemma lem1654068 (x : real) : (term139 x) = (term144 x).
Proof. exact (MK_COMB (@lem1654066 x) (@lem1654067)). Qed.
Lemma lem1654069 (x : real) : (term138 x) = (term144 x).
Proof. exact (TRANS (@lem1654051 x) (@lem1654068 x)). Qed.
Lemma lem1654070 (a : real) (x : real) : ((term145 a x) = term8) = ((term146 a x) = term8).
Proof. exact (@lem1483529 (term145 a x) term8). Qed.
Lemma lem1654071 : term8 = term8.
Proof. exact (eq_refl term8). Qed.
Lemma lem1654078 (x : real) : (real_neg x) = (term11 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1654087 (a : real) : (term147 a) = (term147 a).
Proof. exact (eq_refl (term147 a)). Qed.
Lemma lem1654090 (a : real) (x : real) : (term145 a x) = (term57 a x).
Proof. exact (MK_COMB (@lem1654087 a) (@lem1654078 x)). Qed.
Lemma lem1654091 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1654092 (a : real) (x : real) : (term148 a x) = (term149 a x).
Proof. exact (MK_COMB (@lem1654091) (@lem1654090 a x)). Qed.
Lemma lem1654093 (a : real) (x : real) : (term146 a x) = (term150 a x).
Proof. exact (MK_COMB (@lem1654092 a x) (@lem1654071)). Qed.
Lemma lem1654094 (a : real) (x : real) : (term150 a x) = (term151 a x).
Proof. exact (@lem1483519 (term57 a x) term8). Qed.
Lemma lem1654096 (x : nat) : (term118 x) = term8.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1654097 : term119 = term8.
Proof. exact (@lem1654096 term29). Qed.
Lemma lem1654098 (a : real) (x : real) : (term152 a x) = (term152 a x).
Proof. exact (eq_refl (term152 a x)). Qed.
Lemma lem1654099 (a : real) (x : real) : (term151 a x) = (term153 a x).
Proof. exact (MK_COMB (@lem1654098 a x) (@lem1654097)). Qed.
Lemma lem1654100 (a : real) (x : real) : (term153 a x) = (term57 a x).
Proof. exact (@lem1483450 (term57 a x)). Qed.
Lemma lem1654101 (a : real) (x : real) : (term151 a x) = (term57 a x).
Proof. exact (TRANS (@lem1654099 a x) (@lem1654100 a x)). Qed.
Lemma lem1654102 (a : real) (x : real) : (term150 a x) = (term57 a x).
Proof. exact (TRANS (@lem1654094 a x) (@lem1654101 a x)). Qed.
Lemma lem1654103 (a : real) (x : real) : (term146 a x) = (term57 a x).
Proof. exact (TRANS (@lem1654093 a x) (@lem1654102 a x)). Qed.
Lemma lem1654104 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1654105 (a : real) (x : real) : (term154 a x) = (term155 a x).
Proof. exact (MK_COMB (@lem1654104) (@lem1654103 a x)). Qed.
Lemma lem1654106 : term8 = term8.
Proof. exact (eq_refl term8). Qed.
Lemma lem1654107 (a : real) (x : real) : ((term146 a x) = term8) = ((term57 a x) = term8).
Proof. exact (MK_COMB (@lem1654105 a x) (@lem1654106)). Qed.
Lemma lem1654108 (a : real) (x : real) : ((term145 a x) = term8) = ((term57 a x) = term8).
Proof. exact (TRANS (@lem1654070 a x) (@lem1654107 a x)). Qed.
Lemma lem1654109 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1654110 (a : real) (x : real) : (term136 a x) = (term136 a x).
Proof. exact (MK_COMB (@lem1654109) (@lem1654014 a x)). Qed.
Lemma lem1654111 (a : real) (x : real) : (term91 a x) = (term91 a x).
Proof. exact (MK_COMB (@lem1654110 a x) (@lem1654041 a x)). Qed.
Lemma lem1654112 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1654113 (a : real) (x : real) : (term156 a x) = (term157 a x).
Proof. exact (MK_COMB (@lem1654112) (@lem1654108 a x)). Qed.
Lemma lem1654114 (a : real) (x : real) : (term101 a x) = (term158 a x).
Proof. exact (MK_COMB (@lem1654113 a x) (@lem1654111 a x)). Qed.
Lemma lem1654115 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1654116 (x : real) : (term102 x) = (term159 x).
Proof. exact (MK_COMB (@lem1654115) (@lem1654069 x)). Qed.
Lemma lem1654117 (a : real) (x : real) : (term104 a x) = (term160 a x).
Proof. exact (MK_COMB (@lem1654116 x) (@lem1654114 a x)). Qed.
Lemma lem1654118 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1654119 (a : real) (x : real) : (term111 a x) = (term111 a x).
Proof. exact (MK_COMB (@lem1654118) (@lem1654050 a x)). Qed.
Lemma lem1654120 (a : real) (x : real) : (term112 a x) = (term161 a x).
Proof. exact (MK_COMB (@lem1654119 a x) (@lem1654117 a x)). Qed.
Lemma lem1654132 (a : real) (x : real) : (term97 a x) = (term161 a x).
Proof. exact (TRANS (@lem1653927 a x) (@lem1654120 a x)). Qed.
Lemma lem1654134 (a : real) (x : real) : (term162 a x) = (term163 a x).
Proof. exact (eq_refl (term162 a x)). Qed.
Lemma lem1654135 (a : real) (x : real) : (term163 a x) = (term162 a x).
Proof. exact (SYM (@lem1654134 a x)). Qed.
Lemma lem1654136 (a : real) (x : real) : (term162 a x) = (term164 a x).
Proof. exact (@lem1482981 (term165 a x) x). Qed.
Lemma lem1654137 (a : real) (x : real) : (term163 a x) = (term164 a x).
Proof. exact (TRANS (@lem1654135 a x) (@lem1654136 a x)). Qed.
Lemma lem1654138 (a : real) (x : real) : (term166 a x) = (term167 a x).
Proof. exact (eq_refl (term166 a x)). Qed.
Lemma lem1654139 (x : real) : (term102 x) = (term102 x).
Proof. exact (eq_refl (term102 x)). Qed.
Lemma lem1654140 (a : real) (x : real) : (term168 a x) = (term169 a x).
Proof. exact (MK_COMB (@lem1654139 x) (@lem1654138 a x)). Qed.
Lemma lem1654141 (a : real) (x : real) : (term170 a x) = (term171 a x).
Proof. exact (eq_refl (term170 a x)). Qed.
Lemma lem1654142 (x : real) : (term107 x) = (term107 x).
Proof. exact (eq_refl (term107 x)). Qed.
Lemma lem1654143 (a : real) (x : real) : (term172 a x) = (term173 a x).
Proof. exact (MK_COMB (@lem1654142 x) (@lem1654141 a x)). Qed.
Lemma lem1654144 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1654145 (a : real) (x : real) : (term174 a x) = (term175 a x).
Proof. exact (MK_COMB (@lem1654144) (@lem1654143 a x)). Qed.
Lemma lem1654146 (a : real) (x : real) : (term164 a x) = (term176 a x).
Proof. exact (MK_COMB (@lem1654145 a x) (@lem1654140 a x)). Qed.
Lemma lem1654147 (a : real) (x : real) : (term177 a x) = (term177 a x).
Proof. exact (eq_refl (term177 a x)). Qed.
Lemma lem1654148 (a : real) (x : real) : ((term163 a x) = (term164 a x)) = ((term163 a x) = (term176 a x)).
Proof. exact (MK_COMB (@lem1654147 a x) (@lem1654146 a x)). Qed.
Lemma lem1654149 (a : real) (x : real) : (term163 a x) = (term176 a x).
Proof. exact (EQ_MP (@lem1654148 a x) (@lem1654137 a x)). Qed.
Lemma lem1654150 (a : real) (x : real) : (term41 a x) = (term178 a x).
Proof. exact (@lem1483525 (term16 a x) term8). Qed.
Lemma lem1654168 (a : real) (x : real) : (term179 a x) = (term180 a x).
Proof. exact (@lem1483519 (term16 a x) term8). Qed.
Lemma lem1654170 (x : nat) : (term118 x) = term8.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1654171 : term119 = term8.
Proof. exact (@lem1654170 term29). Qed.
Lemma lem1654172 (a : real) (x : real) : (term181 a x) = (term181 a x).
Proof. exact (eq_refl (term181 a x)). Qed.
Lemma lem1654173 (a : real) (x : real) : (term180 a x) = (term182 a x).
Proof. exact (MK_COMB (@lem1654172 a x) (@lem1654171)). Qed.
Lemma lem1654174 (a : real) (x : real) : (term182 a x) = (term16 a x).
Proof. exact (@lem1483450 (term16 a x)). Qed.
Lemma lem1654175 (a : real) (x : real) : (term180 a x) = (term16 a x).
Proof. exact (TRANS (@lem1654173 a x) (@lem1654174 a x)). Qed.
Lemma lem1654177 (a : real) (x : real) : (term179 a x) = (term16 a x).
Proof. exact (TRANS (@lem1654168 a x) (@lem1654175 a x)). Qed.
Lemma lem1654178 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1654179 (a : real) (x : real) : (term183 a x) = (term39 a x).
Proof. exact (MK_COMB (@lem1654178) (@lem1654177 a x)). Qed.
Lemma lem1654180 : term8 = term8.
Proof. exact (eq_refl term8). Qed.
Lemma lem1654181 (a : real) (x : real) : (term178 a x) = (term41 a x).
Proof. exact (MK_COMB (@lem1654179 a x) (@lem1654180)). Qed.
Lemma lem1654182 (a : real) (x : real) : (term41 a x) = (term41 a x).
Proof. exact (TRANS (@lem1654150 a x) (@lem1654181 a x)). Qed.
Lemma lem1654183 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1654184 (a : real) (x : real) : (term184 a x) = (term184 a x).
Proof. exact (MK_COMB (@lem1654183) (@lem1654182 a x)). Qed.
Lemma lem1654185 (a : real) (x : real) : (term92 a x) = (term92 a x).
Proof. exact (MK_COMB (@lem1654184 a x) (@lem1654041 a x)). Qed.
Lemma lem1654186 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1654187 (a : real) (x : real) : (term137 a x) = (term137 a x).
Proof. exact (MK_COMB (@lem1654186) (@lem1653981 a x)). Qed.
Lemma lem1654188 (a : real) (x : real) : (term171 a x) = (term171 a x).
Proof. exact (MK_COMB (@lem1654187 a x) (@lem1654185 a x)). Qed.
Lemma lem1654189 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1654190 (x : real) : (term107 x) = (term107 x).
Proof. exact (MK_COMB (@lem1654189) (@lem1653948 x)). Qed.
Lemma lem1654191 (a : real) (x : real) : (term173 a x) = (term173 a x).
Proof. exact (MK_COMB (@lem1654190 x) (@lem1654188 a x)). Qed.
Lemma lem1654192 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1654193 (a : real) (x : real) : (term184 a x) = (term184 a x).
Proof. exact (MK_COMB (@lem1654192) (@lem1654182 a x)). Qed.
Lemma lem1654194 (a : real) (x : real) : (term92 a x) = (term92 a x).
Proof. exact (MK_COMB (@lem1654193 a x) (@lem1654041 a x)). Qed.
Lemma lem1654195 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1654196 (a : real) (x : real) : (term156 a x) = (term157 a x).
Proof. exact (MK_COMB (@lem1654195) (@lem1654108 a x)). Qed.
Lemma lem1654197 (a : real) (x : real) : (term167 a x) = (term185 a x).
Proof. exact (MK_COMB (@lem1654196 a x) (@lem1654194 a x)). Qed.
Lemma lem1654198 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1654199 (x : real) : (term102 x) = (term159 x).
Proof. exact (MK_COMB (@lem1654198) (@lem1654069 x)). Qed.
Lemma lem1654200 (a : real) (x : real) : (term169 a x) = (term186 a x).
Proof. exact (MK_COMB (@lem1654199 x) (@lem1654197 a x)). Qed.
Lemma lem1654201 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1654202 (a : real) (x : real) : (term175 a x) = (term175 a x).
Proof. exact (MK_COMB (@lem1654201) (@lem1654191 a x)). Qed.
Lemma lem1654203 (a : real) (x : real) : (term176 a x) = (term187 a x).
Proof. exact (MK_COMB (@lem1654202 a x) (@lem1654200 a x)). Qed.
Lemma lem1654215 (a : real) (x : real) : (term163 a x) = (term187 a x).
Proof. exact (TRANS (@lem1654149 a x) (@lem1654203 a x)). Qed.
Lemma lem1654216 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1654217 (a : real) (x : real) : (term188 a x) = (term189 a x).
Proof. exact (MK_COMB (@lem1654216) (@lem1654132 a x)). Qed.
Lemma lem1654218 (a : real) (x : real) : (term90 a x) = (term190 a x).
Proof. exact (MK_COMB (@lem1654217 a x) (@lem1654215 a x)). Qed.
Lemma lem1654220 (a : real) (x : real) : (term191 a x) = (term192 a x).
Proof. exact (eq_refl (term191 a x)). Qed.
Lemma lem1654221 (a : real) (x : real) : (term192 a x) = (term191 a x).
Proof. exact (SYM (@lem1654220 a x)). Qed.
Lemma lem1654222 (a : real) (x : real) : (term191 a x) = (term193 a x).
Proof. exact (@lem1482981 (term194 a x) x). Qed.
Lemma lem1654223 (a : real) (x : real) : (term192 a x) = (term193 a x).
Proof. exact (TRANS (@lem1654221 a x) (@lem1654222 a x)). Qed.
Lemma lem1654224 (a : real) (x : real) : (term195 a x) = (term196 a x).
Proof. exact (eq_refl (term195 a x)). Qed.
Lemma lem1654225 (x : real) : (term102 x) = (term102 x).
Proof. exact (eq_refl (term102 x)). Qed.
Lemma lem1654226 (a : real) (x : real) : (term197 a x) = (term198 a x).
Proof. exact (MK_COMB (@lem1654225 x) (@lem1654224 a x)). Qed.
Lemma lem1654227 (a : real) (x : real) : (term199 a x) = (term200 a x).
Proof. exact (eq_refl (term199 a x)). Qed.
Lemma lem1654228 (x : real) : (term107 x) = (term107 x).
Proof. exact (eq_refl (term107 x)). Qed.
Lemma lem1654229 (a : real) (x : real) : (term201 a x) = (term202 a x).
Proof. exact (MK_COMB (@lem1654228 x) (@lem1654227 a x)). Qed.
Lemma lem1654230 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1654231 (a : real) (x : real) : (term203 a x) = (term204 a x).
Proof. exact (MK_COMB (@lem1654230) (@lem1654229 a x)). Qed.
Lemma lem1654232 (a : real) (x : real) : (term193 a x) = (term205 a x).
Proof. exact (MK_COMB (@lem1654231 a x) (@lem1654226 a x)). Qed.
Lemma lem1654233 (a : real) (x : real) : (term206 a x) = (term206 a x).
Proof. exact (eq_refl (term206 a x)). Qed.
Lemma lem1654234 (a : real) (x : real) : ((term192 a x) = (term193 a x)) = ((term192 a x) = (term205 a x)).
Proof. exact (MK_COMB (@lem1654233 a x) (@lem1654232 a x)). Qed.
Lemma lem1654235 (a : real) (x : real) : (term192 a x) = (term205 a x).
Proof. exact (EQ_MP (@lem1654234 a x) (@lem1654223 a x)). Qed.
Lemma lem1654236 (a : real) (x : real) : (term62 a x) = (term207 a x).
Proof. exact (@lem1483525 (term57 a x) term8). Qed.
Lemma lem1654260 (a : real) (x : real) : (term150 a x) = (term151 a x).
Proof. exact (@lem1483519 (term57 a x) term8). Qed.
Lemma lem1654262 (x : nat) : (term118 x) = term8.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1654263 : term119 = term8.
Proof. exact (@lem1654262 term29). Qed.
Lemma lem1654264 (a : real) (x : real) : (term152 a x) = (term152 a x).
Proof. exact (eq_refl (term152 a x)). Qed.
Lemma lem1654265 (a : real) (x : real) : (term151 a x) = (term153 a x).
Proof. exact (MK_COMB (@lem1654264 a x) (@lem1654263)). Qed.
Lemma lem1654266 (a : real) (x : real) : (term153 a x) = (term57 a x).
Proof. exact (@lem1483450 (term57 a x)). Qed.
Lemma lem1654267 (a : real) (x : real) : (term151 a x) = (term57 a x).
Proof. exact (TRANS (@lem1654265 a x) (@lem1654266 a x)). Qed.
Lemma lem1654269 (a : real) (x : real) : (term150 a x) = (term57 a x).
Proof. exact (TRANS (@lem1654260 a x) (@lem1654267 a x)). Qed.
Lemma lem1654270 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1654271 (a : real) (x : real) : (term208 a x) = (term60 a x).
Proof. exact (MK_COMB (@lem1654270) (@lem1654269 a x)). Qed.
Lemma lem1654272 : term8 = term8.
Proof. exact (eq_refl term8). Qed.
Lemma lem1654273 (a : real) (x : real) : (term207 a x) = (term62 a x).
Proof. exact (MK_COMB (@lem1654271 a x) (@lem1654272)). Qed.
Lemma lem1654274 (a : real) (x : real) : (term62 a x) = (term62 a x).
Proof. exact (TRANS (@lem1654236 a x) (@lem1654273 a x)). Qed.
Lemma lem1654275 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1654276 (a : real) (x : real) : (term136 a x) = (term136 a x).
Proof. exact (MK_COMB (@lem1654275) (@lem1654014 a x)). Qed.
Lemma lem1654277 (a : real) (x : real) : (term87 a x) = (term87 a x).
Proof. exact (MK_COMB (@lem1654276 a x) (@lem1654274 a x)). Qed.
Lemma lem1654278 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1654279 (a : real) (x : real) : (term137 a x) = (term137 a x).
Proof. exact (MK_COMB (@lem1654278) (@lem1653981 a x)). Qed.
Lemma lem1654280 (a : real) (x : real) : (term200 a x) = (term200 a x).
Proof. exact (MK_COMB (@lem1654279 a x) (@lem1654277 a x)). Qed.
Lemma lem1654281 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1654282 (x : real) : (term107 x) = (term107 x).
Proof. exact (MK_COMB (@lem1654281) (@lem1653948 x)). Qed.
Lemma lem1654283 (a : real) (x : real) : (term202 a x) = (term202 a x).
Proof. exact (MK_COMB (@lem1654282 x) (@lem1654280 a x)). Qed.
Lemma lem1654284 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1654285 (a : real) (x : real) : (term136 a x) = (term136 a x).
Proof. exact (MK_COMB (@lem1654284) (@lem1654014 a x)). Qed.
Lemma lem1654286 (a : real) (x : real) : (term87 a x) = (term87 a x).
Proof. exact (MK_COMB (@lem1654285 a x) (@lem1654274 a x)). Qed.
Lemma lem1654287 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1654288 (a : real) (x : real) : (term156 a x) = (term157 a x).
Proof. exact (MK_COMB (@lem1654287) (@lem1654108 a x)). Qed.
Lemma lem1654289 (a : real) (x : real) : (term196 a x) = (term209 a x).
Proof. exact (MK_COMB (@lem1654288 a x) (@lem1654286 a x)). Qed.
Lemma lem1654290 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1654291 (x : real) : (term102 x) = (term159 x).
Proof. exact (MK_COMB (@lem1654290) (@lem1654069 x)). Qed.
Lemma lem1654292 (a : real) (x : real) : (term198 a x) = (term210 a x).
Proof. exact (MK_COMB (@lem1654291 x) (@lem1654289 a x)). Qed.
Lemma lem1654293 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1654294 (a : real) (x : real) : (term204 a x) = (term204 a x).
Proof. exact (MK_COMB (@lem1654293) (@lem1654283 a x)). Qed.
Lemma lem1654295 (a : real) (x : real) : (term205 a x) = (term211 a x).
Proof. exact (MK_COMB (@lem1654294 a x) (@lem1654292 a x)). Qed.
Lemma lem1654307 (a : real) (x : real) : (term192 a x) = (term211 a x).
Proof. exact (TRANS (@lem1654235 a x) (@lem1654295 a x)). Qed.
Lemma lem1654309 (a : real) (x : real) : (term212 a x) = (term213 a x).
Proof. exact (eq_refl (term212 a x)). Qed.
Lemma lem1654310 (a : real) (x : real) : (term213 a x) = (term212 a x).
Proof. exact (SYM (@lem1654309 a x)). Qed.
Lemma lem1654311 (a : real) (x : real) : (term212 a x) = (term214 a x).
Proof. exact (@lem1482981 (term215 a x) x). Qed.
Lemma lem1654312 (a : real) (x : real) : (term213 a x) = (term214 a x).
Proof. exact (TRANS (@lem1654310 a x) (@lem1654311 a x)). Qed.
Lemma lem1654313 (a : real) (x : real) : (term216 a x) = (term217 a x).
Proof. exact (eq_refl (term216 a x)). Qed.
Lemma lem1654314 (x : real) : (term102 x) = (term102 x).
Proof. exact (eq_refl (term102 x)). Qed.
Lemma lem1654315 (a : real) (x : real) : (term218 a x) = (term219 a x).
Proof. exact (MK_COMB (@lem1654314 x) (@lem1654313 a x)). Qed.
Lemma lem1654316 (a : real) (x : real) : (term220 a x) = (term221 a x).
Proof. exact (eq_refl (term220 a x)). Qed.
Lemma lem1654317 (x : real) : (term107 x) = (term107 x).
Proof. exact (eq_refl (term107 x)). Qed.
Lemma lem1654318 (a : real) (x : real) : (term222 a x) = (term223 a x).
Proof. exact (MK_COMB (@lem1654317 x) (@lem1654316 a x)). Qed.
Lemma lem1654319 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1654320 (a : real) (x : real) : (term224 a x) = (term225 a x).
Proof. exact (MK_COMB (@lem1654319) (@lem1654318 a x)). Qed.
Lemma lem1654321 (a : real) (x : real) : (term214 a x) = (term226 a x).
Proof. exact (MK_COMB (@lem1654320 a x) (@lem1654315 a x)). Qed.
Lemma lem1654322 (a : real) (x : real) : (term227 a x) = (term227 a x).
Proof. exact (eq_refl (term227 a x)). Qed.
Lemma lem1654323 (a : real) (x : real) : ((term213 a x) = (term214 a x)) = ((term213 a x) = (term226 a x)).
Proof. exact (MK_COMB (@lem1654322 a x) (@lem1654321 a x)). Qed.
Lemma lem1654324 (a : real) (x : real) : (term213 a x) = (term226 a x).
Proof. exact (EQ_MP (@lem1654323 a x) (@lem1654312 a x)). Qed.
Lemma lem1654325 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1654326 (a : real) (x : real) : (term184 a x) = (term184 a x).
Proof. exact (MK_COMB (@lem1654325) (@lem1654182 a x)). Qed.
Lemma lem1654327 (a : real) (x : real) : (term88 a x) = (term88 a x).
Proof. exact (MK_COMB (@lem1654326 a x) (@lem1654274 a x)). Qed.
Lemma lem1654328 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1654329 (a : real) (x : real) : (term137 a x) = (term137 a x).
Proof. exact (MK_COMB (@lem1654328) (@lem1653981 a x)). Qed.
Lemma lem1654330 (a : real) (x : real) : (term221 a x) = (term221 a x).
Proof. exact (MK_COMB (@lem1654329 a x) (@lem1654327 a x)). Qed.
Lemma lem1654331 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1654332 (x : real) : (term107 x) = (term107 x).
Proof. exact (MK_COMB (@lem1654331) (@lem1653948 x)). Qed.
Lemma lem1654333 (a : real) (x : real) : (term223 a x) = (term223 a x).
Proof. exact (MK_COMB (@lem1654332 x) (@lem1654330 a x)). Qed.
Lemma lem1654334 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1654335 (a : real) (x : real) : (term184 a x) = (term184 a x).
Proof. exact (MK_COMB (@lem1654334) (@lem1654182 a x)). Qed.
Lemma lem1654336 (a : real) (x : real) : (term88 a x) = (term88 a x).
Proof. exact (MK_COMB (@lem1654335 a x) (@lem1654274 a x)). Qed.
Lemma lem1654337 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1654338 (a : real) (x : real) : (term156 a x) = (term157 a x).
Proof. exact (MK_COMB (@lem1654337) (@lem1654108 a x)). Qed.
Lemma lem1654339 (a : real) (x : real) : (term217 a x) = (term228 a x).
Proof. exact (MK_COMB (@lem1654338 a x) (@lem1654336 a x)). Qed.
Lemma lem1654340 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1654341 (x : real) : (term102 x) = (term159 x).
Proof. exact (MK_COMB (@lem1654340) (@lem1654069 x)). Qed.
Lemma lem1654342 (a : real) (x : real) : (term219 a x) = (term229 a x).
Proof. exact (MK_COMB (@lem1654341 x) (@lem1654339 a x)). Qed.
Lemma lem1654343 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1654344 (a : real) (x : real) : (term225 a x) = (term225 a x).
Proof. exact (MK_COMB (@lem1654343) (@lem1654333 a x)). Qed.
Lemma lem1654345 (a : real) (x : real) : (term226 a x) = (term230 a x).
Proof. exact (MK_COMB (@lem1654344 a x) (@lem1654342 a x)). Qed.
Lemma lem1654357 (a : real) (x : real) : (term213 a x) = (term230 a x).
Proof. exact (TRANS (@lem1654324 a x) (@lem1654345 a x)). Qed.
Lemma lem1654358 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1654359 (a : real) (x : real) : (term231 a x) = (term232 a x).
Proof. exact (MK_COMB (@lem1654358) (@lem1654307 a x)). Qed.
Lemma lem1654360 (a : real) (x : real) : (term86 a x) = (term233 a x).
Proof. exact (MK_COMB (@lem1654359 a x) (@lem1654357 a x)). Qed.
Lemma lem1654361 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1654362 (a : real) (x : real) : (term94 a x) = (term234 a x).
Proof. exact (MK_COMB (@lem1654361) (@lem1654218 a x)). Qed.
Lemma lem1654363 (a : real) (x : real) : (term95 a x) = (term235 a x).
Proof. exact (MK_COMB (@lem1654362 a x) (@lem1654360 a x)). Qed.
Lemma lem1654364 (a : real) (x : real) (h1 : term235 a x) : term235 a x.
Proof. exact (h1). Qed.
Lemma lem1654365 (a : real) (x : real) (h1 : term190 a x) : term190 a x.
Proof. exact (h1). Qed.
Lemma lem1654366 (a : real) (x : real) (h1 : term161 a x) : term161 a x.
Proof. exact (h1). Qed.
Lemma lem1654367 (a : real) (x : real) (h1 : term109 a x) : term109 a x.
Proof. exact (h1). Qed.
Lemma lem1654368 (a : real) (x : real) (h1 : term109 a x) : term106 a x.
Proof. exact (proj2 (@lem1654367 a x h1)). Qed.
Lemma lem1654370 (a : real) (x : real) (h1 : term109 a x) : term91 a x.
Proof. exact (proj2 (@lem1654368 a x h1)). Qed.
Lemma lem1654371 (a : real) (x : real) (h1 : term109 a x) : (term17 a x) = term8.
Proof. exact (proj1 (@lem1654368 a x h1)). Qed.
Lemma lem1654373 (a : real) (x : real) (h1 : term109 a x) : term45 a x.
Proof. exact (proj1 (@lem1654370 a x h1)). Qed.
Lemma lem1654375 (n : nat) (m : nat) : (term236 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1654376 : term237 = term238.
Proof. exact (@lem1654375 (NUMERAL 0) term29). Qed.
Lemma lem1654377 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1654378 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1654379 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem1654378 h1) (fun h1 : term238 = True => @lem1654377)). Qed.
Lemma lem1654380 : term238 = True.
Proof. exact (EQ_MP (@lem1654379) (@lem1654377)). Qed.
Lemma lem1654381 : term237 = True.
Proof. exact (TRANS (@lem1654376) (@lem1654380)). Qed.
Lemma lem1654382 : True = term237.
Proof. exact (SYM (@lem1654381)). Qed.
Lemma lem1654383 : term237.
Proof. exact (EQ_MP (@lem1654382) (@lem0)). Qed.
Lemma lem1654384 (a : real) (x : real) (h1 : term109 a x) : term240 a x.
Proof. exact (conj (@lem1654383) (@lem1654373 a x h1)). Qed.
Lemma lem1654386 (x : real) (y : real) : term241 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1654387 (a : real) (x : real) : term242 a x.
Proof. exact (@lem1654386 term32 (term17 a x)). Qed.
Lemma lem1654388 (a : real) (x : real) (h1 : term109 a x) : term243 a x.
Proof. exact (@lem1654387 a x (@lem1654384 a x h1)). Qed.
Lemma lem1654389 (a : real) (x : real) : (term244 a x) = (term17 a x).
Proof. exact (@lem1483460 (term17 a x)). Qed.
Lemma lem1654390 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1654391 (a : real) (x : real) : (term245 a x) = (term43 a x).
Proof. exact (MK_COMB (@lem1654390) (@lem1654389 a x)). Qed.
Lemma lem1654392 : term8 = term8.
Proof. exact (eq_refl term8). Qed.
Lemma lem1654393 (a : real) (x : real) : (term243 a x) = (term45 a x).
Proof. exact (MK_COMB (@lem1654391 a x) (@lem1654392)). Qed.
Lemma lem1654394 (a : real) (x : real) (h1 : term109 a x) : term45 a x.
Proof. exact (EQ_MP (@lem1654393 a x) (@lem1654388 a x h1)). Qed.
Lemma lem1654396 (y : real) : term246 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1654397 (a : real) (x : real) : term247 a x.
Proof. exact (@lem1654396 (term17 a x)). Qed.
Lemma lem1654398 (a : real) (x : real) (h1 : term109 a x) : term248 a x.
Proof. exact (@lem1654397 a x (@lem1654371 a x h1)). Qed.
Lemma lem1654399 (a : real) (x : real) (h1 : term109 a x) : term249 a x.
Proof. exact (@lem1654398 a x h1 term22). Qed.
Lemma lem1654400 (a : real) (x : real) : (term249 a x) = ((term20 a x) = term8).
Proof. exact (eq_refl (term249 a x)). Qed.
Lemma lem1654401 (a : real) (x : real) (h1 : term109 a x) : (term20 a x) = term8.
Proof. exact (EQ_MP (@lem1654400 a x) (@lem1654399 a x h1)). Qed.
Lemma lem1654402 (a : real) (x : real) : (term20 a x) = (term21 a x).
Proof. exact (@lem1483508 (term11 a) term22 x). Qed.
Lemma lem1654403 (x : real) : (term11 x) = (term11 x).
Proof. exact (eq_refl (term11 x)). Qed.
Lemma lem1654404 (a : real) : (term23 a) = (term24 a).
Proof. exact (@lem1483476 term22 term22 a). Qed.
Lemma lem1654406 (m : nat) (n : nat) : (term25 m n) = (term26 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1654407 : term27 = term28.
Proof. exact (@lem1654406 term29 term29). Qed.
Lemma lem1654408 : (term30 = (BIT1 0)) = (term31 = term29).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1654409 : term31 = term29.
Proof. exact (EQ_MP (@lem1654408) (@lem940073)). Qed.
Lemma lem1654410 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1654411 : term28 = term32.
Proof. exact (MK_COMB (@lem1654410) (@lem1654409)). Qed.
Lemma lem1654412 : term27 = term32.
Proof. exact (TRANS (@lem1654407) (@lem1654411)). Qed.
Lemma lem1654413 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1654414 : term33 = term34.
Proof. exact (MK_COMB (@lem1654413) (@lem1654412)). Qed.
Lemma lem1654415 (a : real) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1654416 (a : real) : (term24 a) = (term35 a).
Proof. exact (MK_COMB (@lem1654414) (@lem1654415 a)). Qed.
Lemma lem1654417 (a : real) : (term23 a) = (term35 a).
Proof. exact (TRANS (@lem1654404 a) (@lem1654416 a)). Qed.
Lemma lem1654418 (a : real) : (term35 a) = a.
Proof. exact (@lem1483436 a). Qed.
Lemma lem1654419 (a : real) : (term23 a) = a.
Proof. exact (TRANS (@lem1654417 a) (@lem1654418 a)). Qed.
Lemma lem1654420 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1654421 (a : real) : (term36 a) = (real_add a).
Proof. exact (MK_COMB (@lem1654420) (@lem1654419 a)). Qed.
Lemma lem1654422 (a : real) (x : real) : (term21 a x) = (term16 a x).
Proof. exact (MK_COMB (@lem1654421 a) (@lem1654403 x)). Qed.
Lemma lem1654423 (a : real) (x : real) : (term20 a x) = (term16 a x).
Proof. exact (TRANS (@lem1654402 a x) (@lem1654422 a x)). Qed.
Lemma lem1654424 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1654425 (a : real) (x : real) : (term250 a x) = (term251 a x).
Proof. exact (MK_COMB (@lem1654424) (@lem1654423 a x)). Qed.
Lemma lem1654426 : term8 = term8.
Proof. exact (eq_refl term8). Qed.
Lemma lem1654427 (a : real) (x : real) : ((term20 a x) = term8) = ((term16 a x) = term8).
Proof. exact (MK_COMB (@lem1654425 a x) (@lem1654426)). Qed.
Lemma lem1654428 (a : real) (x : real) (h1 : term109 a x) : (term16 a x) = term8.
Proof. exact (EQ_MP (@lem1654427 a x) (@lem1654401 a x h1)). Qed.
Lemma lem1654429 (a : real) (x : real) (h1 : term109 a x) : term252 a x.
Proof. exact (conj (@lem1654428 a x h1) (@lem1654394 a x h1)). Qed.
Lemma lem1654431 (x : real) (y : real) : term253 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1654432 (a : real) (x : real) : term254 a x.
Proof. exact (@lem1654431 (term16 a x) (term17 a x)). Qed.
Lemma lem1654433 (a : real) (x : real) (h1 : term109 a x) : term255 a x.
Proof. exact (@lem1654432 a x (@lem1654429 a x h1)). Qed.
Lemma lem1654434 (a : real) (x : real) : (term256 a x) = (term257 a x).
Proof. exact (@lem1483480 a (term11 a) (term11 x) x). Qed.
Lemma lem1654435 (a : real) : (term258 a) = (term259 a).
Proof. exact (@lem1483442 term22 a). Qed.
Lemma lem1654437 (m : nat) : (term260 m) = term8.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1654438 : term261 = term8.
Proof. exact (@lem1654437 term29). Qed.
Lemma lem1654439 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1654440 : term262 = term263.
Proof. exact (MK_COMB (@lem1654439) (@lem1654438)). Qed.
Lemma lem1654441 (a : real) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1654442 (a : real) : (term259 a) = (term264 a).
Proof. exact (MK_COMB (@lem1654440) (@lem1654441 a)). Qed.
Lemma lem1654443 (a : real) : (term258 a) = (term264 a).
Proof. exact (TRANS (@lem1654435 a) (@lem1654442 a)). Qed.
Lemma lem1654444 (a : real) : (term264 a) = term8.
Proof. exact (@lem1483446 a). Qed.
Lemma lem1654445 (a : real) : (term258 a) = term8.
Proof. exact (TRANS (@lem1654443 a) (@lem1654444 a)). Qed.
Lemma lem1654446 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1654447 (a : real) : (term265 a) = term266.
Proof. exact (MK_COMB (@lem1654446) (@lem1654445 a)). Qed.
Lemma lem1654448 (x : real) : (term267 x) = (term259 x).
Proof. exact (@lem1483440 term22 x). Qed.
Lemma lem1654450 (m : nat) : (term260 m) = term8.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1654451 : term261 = term8.
Proof. exact (@lem1654450 term29). Qed.
Lemma lem1654452 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1654453 : term262 = term263.
Proof. exact (MK_COMB (@lem1654452) (@lem1654451)). Qed.
Lemma lem1654454 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1654455 (x : real) : (term259 x) = (term264 x).
Proof. exact (MK_COMB (@lem1654453) (@lem1654454 x)). Qed.
Lemma lem1654456 (x : real) : (term267 x) = (term264 x).
Proof. exact (TRANS (@lem1654448 x) (@lem1654455 x)). Qed.
Lemma lem1654457 (x : real) : (term264 x) = term8.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1654458 (x : real) : (term267 x) = term8.
Proof. exact (TRANS (@lem1654456 x) (@lem1654457 x)). Qed.
Lemma lem1654459 (a : real) (x : real) : (term257 a x) = term268.
Proof. exact (MK_COMB (@lem1654447 a) (@lem1654458 x)). Qed.
Lemma lem1654460 (a : real) (x : real) : (term256 a x) = term268.
Proof. exact (TRANS (@lem1654434 a x) (@lem1654459 a x)). Qed.
Lemma lem1654461 : term268 = term8.
Proof. exact (@lem1483448 term8). Qed.
Lemma lem1654462 (a : real) (x : real) : (term256 a x) = term8.
Proof. exact (TRANS (@lem1654460 a x) (@lem1654461)). Qed.
Lemma lem1654463 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1654464 (a : real) (x : real) : (term269 a x) = term270.
Proof. exact (MK_COMB (@lem1654463) (@lem1654462 a x)). Qed.
Lemma lem1654465 : term8 = term8.
Proof. exact (eq_refl term8). Qed.
Lemma lem1654466 (a : real) (x : real) : (term255 a x) = term271.
Proof. exact (MK_COMB (@lem1654464 a x) (@lem1654465)). Qed.
Lemma lem1654467 (a : real) (x : real) (h1 : term109 a x) : term271.
Proof. exact (EQ_MP (@lem1654466 a x) (@lem1654433 a x h1)). Qed.
Lemma lem1654469 (n : nat) (m : nat) : (term236 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1654470 : term271 = term272.
Proof. exact (@lem1654469 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1654471 : term272 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1654472 : term271 = False.
Proof. exact (TRANS (@lem1654470) (@lem1654471)). Qed.
Lemma lem1654473 (a : real) (x : real) (h1 : term109 a x) : False.
Proof. exact (EQ_MP (@lem1654472) (@lem1654467 a x h1)). Qed.
Lemma lem1654474 (a : real) (x : real) (h1 : term160 a x) : term160 a x.
Proof. exact (h1). Qed.
Lemma lem1654475 (a : real) (x : real) (h1 : term160 a x) : term158 a x.
Proof. exact (proj2 (@lem1654474 a x h1)). Qed.
Lemma lem1654477 (a : real) (x : real) (h1 : term160 a x) : term91 a x.
Proof. exact (proj2 (@lem1654475 a x h1)). Qed.
Lemma lem1654478 (a : real) (x : real) (h1 : term160 a x) : (term57 a x) = term8.
Proof. exact (proj1 (@lem1654475 a x h1)). Qed.
Lemma lem1654479 (a : real) (x : real) (h1 : term160 a x) : term66 a x.
Proof. exact (proj2 (@lem1654477 a x h1)). Qed.
Lemma lem1654482 (n : nat) (m : nat) : (term236 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1654483 : term237 = term238.
Proof. exact (@lem1654482 (NUMERAL 0) term29). Qed.
Lemma lem1654484 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1654485 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1654486 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem1654485 h1) (fun h1 : term238 = True => @lem1654484)). Qed.
Lemma lem1654487 : term238 = True.
Proof. exact (EQ_MP (@lem1654486) (@lem1654484)). Qed.
Lemma lem1654488 : term237 = True.
Proof. exact (TRANS (@lem1654483) (@lem1654487)). Qed.
Lemma lem1654489 : True = term237.
Proof. exact (SYM (@lem1654488)). Qed.
Lemma lem1654490 : term237.
Proof. exact (EQ_MP (@lem1654489) (@lem0)). Qed.
Lemma lem1654491 (a : real) (x : real) (h1 : term160 a x) : term273 a x.
Proof. exact (conj (@lem1654490) (@lem1654479 a x h1)). Qed.
Lemma lem1654493 (x : real) (y : real) : term241 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1654494 (a : real) (x : real) : term274 a x.
Proof. exact (@lem1654493 term32 (real_add a x)). Qed.
Lemma lem1654495 (a : real) (x : real) (h1 : term160 a x) : term275 a x.
Proof. exact (@lem1654494 a x (@lem1654491 a x h1)). Qed.
Lemma lem1654496 (a : real) (x : real) : (term276 a x) = (real_add a x).
Proof. exact (@lem1483460 (real_add a x)). Qed.
Lemma lem1654497 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1654498 (a : real) (x : real) : (term277 a x) = (term64 a x).
Proof. exact (MK_COMB (@lem1654497) (@lem1654496 a x)). Qed.
Lemma lem1654499 : term8 = term8.
Proof. exact (eq_refl term8). Qed.
Lemma lem1654500 (a : real) (x : real) : (term275 a x) = (term66 a x).
Proof. exact (MK_COMB (@lem1654498 a x) (@lem1654499)). Qed.
Lemma lem1654501 (a : real) (x : real) (h1 : term160 a x) : term66 a x.
Proof. exact (EQ_MP (@lem1654500 a x) (@lem1654495 a x h1)). Qed.
Lemma lem1654503 (y : real) : term246 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1654504 (a : real) (x : real) : term278 a x.
Proof. exact (@lem1654503 (term57 a x)). Qed.
Lemma lem1654505 (a : real) (x : real) (h1 : term160 a x) : term279 a x.
Proof. exact (@lem1654504 a x (@lem1654478 a x h1)). Qed.
Lemma lem1654506 (a : real) (x : real) (h1 : term160 a x) : term280 a x.
Proof. exact (@lem1654505 a x h1 term32). Qed.
Lemma lem1654507 (a : real) (x : real) : (term280 a x) = ((term281 a x) = term8).
Proof. exact (eq_refl (term280 a x)). Qed.
Lemma lem1654508 (a : real) (x : real) (h1 : term160 a x) : (term281 a x) = term8.
Proof. exact (EQ_MP (@lem1654507 a x) (@lem1654506 a x h1)). Qed.
Lemma lem1654509 (a : real) (x : real) : (term281 a x) = (term57 a x).
Proof. exact (@lem1483460 (term57 a x)). Qed.
Lemma lem1654510 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1654511 (a : real) (x : real) : (term282 a x) = (term155 a x).
Proof. exact (MK_COMB (@lem1654510) (@lem1654509 a x)). Qed.
Lemma lem1654512 : term8 = term8.
Proof. exact (eq_refl term8). Qed.
Lemma lem1654513 (a : real) (x : real) : ((term281 a x) = term8) = ((term57 a x) = term8).
Proof. exact (MK_COMB (@lem1654511 a x) (@lem1654512)). Qed.
Lemma lem1654514 (a : real) (x : real) (h1 : term160 a x) : (term57 a x) = term8.
Proof. exact (EQ_MP (@lem1654513 a x) (@lem1654508 a x h1)). Qed.
Lemma lem1654515 (a : real) (x : real) (h1 : term160 a x) : term283 a x.
Proof. exact (conj (@lem1654514 a x h1) (@lem1654501 a x h1)). Qed.
Lemma lem1654517 (x : real) (y : real) : term253 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1654518 (a : real) (x : real) : term284 a x.
Proof. exact (@lem1654517 (term57 a x) (real_add a x)). Qed.
Lemma lem1654519 (a : real) (x : real) (h1 : term160 a x) : term285 a x.
Proof. exact (@lem1654518 a x (@lem1654515 a x h1)). Qed.
Lemma lem1654520 (a : real) (x : real) : (term286 a x) = (term287 a x).
Proof. exact (@lem1483480 (term11 a) a (term11 x) x). Qed.
Lemma lem1654521 (a : real) : (term267 a) = (term259 a).
Proof. exact (@lem1483440 term22 a). Qed.
Lemma lem1654523 (m : nat) : (term260 m) = term8.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1654524 : term261 = term8.
Proof. exact (@lem1654523 term29). Qed.
Lemma lem1654525 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1654526 : term262 = term263.
Proof. exact (MK_COMB (@lem1654525) (@lem1654524)). Qed.
Lemma lem1654527 (a : real) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1654528 (a : real) : (term259 a) = (term264 a).
Proof. exact (MK_COMB (@lem1654526) (@lem1654527 a)). Qed.
Lemma lem1654529 (a : real) : (term267 a) = (term264 a).
Proof. exact (TRANS (@lem1654521 a) (@lem1654528 a)). Qed.
Lemma lem1654530 (a : real) : (term264 a) = term8.
Proof. exact (@lem1483446 a). Qed.
Lemma lem1654531 (a : real) : (term267 a) = term8.
Proof. exact (TRANS (@lem1654529 a) (@lem1654530 a)). Qed.
Lemma lem1654532 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1654533 (a : real) : (term288 a) = term266.
Proof. exact (MK_COMB (@lem1654532) (@lem1654531 a)). Qed.
Lemma lem1654534 (x : real) : (term267 x) = (term259 x).
Proof. exact (@lem1483440 term22 x). Qed.
Lemma lem1654536 (m : nat) : (term260 m) = term8.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1654537 : term261 = term8.
Proof. exact (@lem1654536 term29). Qed.
Lemma lem1654538 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1654539 : term262 = term263.
Proof. exact (MK_COMB (@lem1654538) (@lem1654537)). Qed.
Lemma lem1654540 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1654541 (x : real) : (term259 x) = (term264 x).
Proof. exact (MK_COMB (@lem1654539) (@lem1654540 x)). Qed.
Lemma lem1654542 (x : real) : (term267 x) = (term264 x).
Proof. exact (TRANS (@lem1654534 x) (@lem1654541 x)). Qed.
Lemma lem1654543 (x : real) : (term264 x) = term8.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1654544 (x : real) : (term267 x) = term8.
Proof. exact (TRANS (@lem1654542 x) (@lem1654543 x)). Qed.
Lemma lem1654545 (a : real) (x : real) : (term287 a x) = term268.
Proof. exact (MK_COMB (@lem1654533 a) (@lem1654544 x)). Qed.
Lemma lem1654546 (a : real) (x : real) : (term286 a x) = term268.
Proof. exact (TRANS (@lem1654520 a x) (@lem1654545 a x)). Qed.
Lemma lem1654547 : term268 = term8.
Proof. exact (@lem1483448 term8). Qed.
Lemma lem1654548 (a : real) (x : real) : (term286 a x) = term8.
Proof. exact (TRANS (@lem1654546 a x) (@lem1654547)). Qed.
Lemma lem1654549 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1654550 (a : real) (x : real) : (term289 a x) = term270.
Proof. exact (MK_COMB (@lem1654549) (@lem1654548 a x)). Qed.
Lemma lem1654551 : term8 = term8.
Proof. exact (eq_refl term8). Qed.
Lemma lem1654552 (a : real) (x : real) : (term285 a x) = term271.
Proof. exact (MK_COMB (@lem1654550 a x) (@lem1654551)). Qed.
Lemma lem1654553 (a : real) (x : real) (h1 : term160 a x) : term271.
Proof. exact (EQ_MP (@lem1654552 a x) (@lem1654519 a x h1)). Qed.
Lemma lem1654555 (n : nat) (m : nat) : (term236 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1654556 : term271 = term272.
Proof. exact (@lem1654555 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1654557 : term272 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1654558 : term271 = False.
Proof. exact (TRANS (@lem1654556) (@lem1654557)). Qed.
Lemma lem1654559 (a : real) (x : real) (h1 : term160 a x) : False.
Proof. exact (EQ_MP (@lem1654558) (@lem1654553 a x h1)). Qed.
Lemma lem1654560 (a : real) (x : real) (h1 : term161 a x) : False.
Proof. exact (or_elim (@lem1654366 a x h1) (fun h0 : term109 a x => @lem1654473 a x h0) (fun h0 : term160 a x => @lem1654559 a x h0)). Qed.
Lemma lem1654561 (a : real) (x : real) (h1 : term187 a x) : term187 a x.
Proof. exact (h1). Qed.
Lemma lem1654562 (a : real) (x : real) (h1 : term173 a x) : term173 a x.
Proof. exact (h1). Qed.
Lemma lem1654563 (a : real) (x : real) (h1 : term173 a x) : term171 a x.
Proof. exact (proj2 (@lem1654562 a x h1)). Qed.
Lemma lem1654565 (a : real) (x : real) (h1 : term173 a x) : term92 a x.
Proof. exact (proj2 (@lem1654563 a x h1)). Qed.
Lemma lem1654566 (a : real) (x : real) (h1 : term173 a x) : (term17 a x) = term8.
Proof. exact (proj1 (@lem1654563 a x h1)). Qed.
Lemma lem1654568 (a : real) (x : real) (h1 : term173 a x) : term41 a x.
Proof. exact (proj1 (@lem1654565 a x h1)). Qed.
Lemma lem1654570 (n : nat) (m : nat) : (term236 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1654571 : term237 = term238.
Proof. exact (@lem1654570 (NUMERAL 0) term29). Qed.
Lemma lem1654572 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1654573 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1654574 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem1654573 h1) (fun h1 : term238 = True => @lem1654572)). Qed.
Lemma lem1654575 : term238 = True.
Proof. exact (EQ_MP (@lem1654574) (@lem1654572)). Qed.
Lemma lem1654576 : term237 = True.
Proof. exact (TRANS (@lem1654571) (@lem1654575)). Qed.
Lemma lem1654577 : True = term237.
Proof. exact (SYM (@lem1654576)). Qed.
Lemma lem1654578 : term237.
Proof. exact (EQ_MP (@lem1654577) (@lem0)). Qed.
Lemma lem1654579 (a : real) (x : real) (h1 : term173 a x) : term290 a x.
Proof. exact (conj (@lem1654578) (@lem1654568 a x h1)). Qed.
Lemma lem1654581 (x : real) (y : real) : term241 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1654582 (a : real) (x : real) : term291 a x.
Proof. exact (@lem1654581 term32 (term16 a x)). Qed.
Lemma lem1654583 (a : real) (x : real) (h1 : term173 a x) : term292 a x.
Proof. exact (@lem1654582 a x (@lem1654579 a x h1)). Qed.
Lemma lem1654584 (a : real) (x : real) : (term293 a x) = (term16 a x).
Proof. exact (@lem1483460 (term16 a x)). Qed.
Lemma lem1654585 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1654586 (a : real) (x : real) : (term294 a x) = (term39 a x).
Proof. exact (MK_COMB (@lem1654585) (@lem1654584 a x)). Qed.
Lemma lem1654587 : term8 = term8.
Proof. exact (eq_refl term8). Qed.
Lemma lem1654588 (a : real) (x : real) : (term292 a x) = (term41 a x).
Proof. exact (MK_COMB (@lem1654586 a x) (@lem1654587)). Qed.
Lemma lem1654589 (a : real) (x : real) (h1 : term173 a x) : term41 a x.
Proof. exact (EQ_MP (@lem1654588 a x) (@lem1654583 a x h1)). Qed.
Lemma lem1654591 (y : real) : term246 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1654592 (a : real) (x : real) : term247 a x.
Proof. exact (@lem1654591 (term17 a x)). Qed.
Lemma lem1654593 (a : real) (x : real) (h1 : term173 a x) : term248 a x.
Proof. exact (@lem1654592 a x (@lem1654566 a x h1)). Qed.
Lemma lem1654594 (a : real) (x : real) (h1 : term173 a x) : term295 a x.
Proof. exact (@lem1654593 a x h1 term32). Qed.
Lemma lem1654595 (a : real) (x : real) : (term295 a x) = ((term244 a x) = term8).
Proof. exact (eq_refl (term295 a x)). Qed.
Lemma lem1654596 (a : real) (x : real) (h1 : term173 a x) : (term244 a x) = term8.
Proof. exact (EQ_MP (@lem1654595 a x) (@lem1654594 a x h1)). Qed.
Lemma lem1654597 (a : real) (x : real) : (term244 a x) = (term17 a x).
Proof. exact (@lem1483460 (term17 a x)). Qed.
Lemma lem1654598 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1654599 (a : real) (x : real) : (term296 a x) = (term127 a x).
Proof. exact (MK_COMB (@lem1654598) (@lem1654597 a x)). Qed.
Lemma lem1654600 : term8 = term8.
Proof. exact (eq_refl term8). Qed.
Lemma lem1654601 (a : real) (x : real) : ((term244 a x) = term8) = ((term17 a x) = term8).
Proof. exact (MK_COMB (@lem1654599 a x) (@lem1654600)). Qed.
Lemma lem1654602 (a : real) (x : real) (h1 : term173 a x) : (term17 a x) = term8.
Proof. exact (EQ_MP (@lem1654601 a x) (@lem1654596 a x h1)). Qed.
Lemma lem1654603 (a : real) (x : real) (h1 : term173 a x) : term297 a x.
Proof. exact (conj (@lem1654602 a x h1) (@lem1654589 a x h1)). Qed.
Lemma lem1654605 (x : real) (y : real) : term253 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1654606 (a : real) (x : real) : term298 a x.
Proof. exact (@lem1654605 (term17 a x) (term16 a x)). Qed.
Lemma lem1654607 (a : real) (x : real) (h1 : term173 a x) : term299 a x.
Proof. exact (@lem1654606 a x (@lem1654603 a x h1)). Qed.
Lemma lem1654608 (a : real) (x : real) : (term300 a x) = (term301 a x).
Proof. exact (@lem1483480 (term11 a) a x (term11 x)). Qed.
Lemma lem1654609 (a : real) : (term267 a) = (term259 a).
Proof. exact (@lem1483440 term22 a). Qed.
Lemma lem1654611 (m : nat) : (term260 m) = term8.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1654612 : term261 = term8.
Proof. exact (@lem1654611 term29). Qed.
Lemma lem1654613 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1654614 : term262 = term263.
Proof. exact (MK_COMB (@lem1654613) (@lem1654612)). Qed.
Lemma lem1654615 (a : real) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1654616 (a : real) : (term259 a) = (term264 a).
Proof. exact (MK_COMB (@lem1654614) (@lem1654615 a)). Qed.
Lemma lem1654617 (a : real) : (term267 a) = (term264 a).
Proof. exact (TRANS (@lem1654609 a) (@lem1654616 a)). Qed.
Lemma lem1654618 (a : real) : (term264 a) = term8.
Proof. exact (@lem1483446 a). Qed.
Lemma lem1654619 (a : real) : (term267 a) = term8.
Proof. exact (TRANS (@lem1654617 a) (@lem1654618 a)). Qed.
Lemma lem1654620 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1654621 (a : real) : (term288 a) = term266.
Proof. exact (MK_COMB (@lem1654620) (@lem1654619 a)). Qed.
Lemma lem1654622 (x : real) : (term258 x) = (term259 x).
Proof. exact (@lem1483442 term22 x). Qed.
Lemma lem1654624 (m : nat) : (term260 m) = term8.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1654625 : term261 = term8.
Proof. exact (@lem1654624 term29). Qed.
Lemma lem1654626 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1654627 : term262 = term263.
Proof. exact (MK_COMB (@lem1654626) (@lem1654625)). Qed.
Lemma lem1654628 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1654629 (x : real) : (term259 x) = (term264 x).
Proof. exact (MK_COMB (@lem1654627) (@lem1654628 x)). Qed.
Lemma lem1654630 (x : real) : (term258 x) = (term264 x).
Proof. exact (TRANS (@lem1654622 x) (@lem1654629 x)). Qed.
Lemma lem1654631 (x : real) : (term264 x) = term8.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1654632 (x : real) : (term258 x) = term8.
Proof. exact (TRANS (@lem1654630 x) (@lem1654631 x)). Qed.
Lemma lem1654633 (a : real) (x : real) : (term301 a x) = term268.
Proof. exact (MK_COMB (@lem1654621 a) (@lem1654632 x)). Qed.
Lemma lem1654634 (a : real) (x : real) : (term300 a x) = term268.
Proof. exact (TRANS (@lem1654608 a x) (@lem1654633 a x)). Qed.
Lemma lem1654635 : term268 = term8.
Proof. exact (@lem1483448 term8). Qed.
Lemma lem1654636 (a : real) (x : real) : (term300 a x) = term8.
Proof. exact (TRANS (@lem1654634 a x) (@lem1654635)). Qed.
Lemma lem1654637 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1654638 (a : real) (x : real) : (term302 a x) = term270.
Proof. exact (MK_COMB (@lem1654637) (@lem1654636 a x)). Qed.
Lemma lem1654639 : term8 = term8.
Proof. exact (eq_refl term8). Qed.
Lemma lem1654640 (a : real) (x : real) : (term299 a x) = term271.
Proof. exact (MK_COMB (@lem1654638 a x) (@lem1654639)). Qed.
Lemma lem1654641 (a : real) (x : real) (h1 : term173 a x) : term271.
Proof. exact (EQ_MP (@lem1654640 a x) (@lem1654607 a x h1)). Qed.
Lemma lem1654643 (n : nat) (m : nat) : (term236 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1654644 : term271 = term272.
Proof. exact (@lem1654643 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1654645 : term272 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1654646 : term271 = False.
Proof. exact (TRANS (@lem1654644) (@lem1654645)). Qed.
Lemma lem1654647 (a : real) (x : real) (h1 : term173 a x) : False.
Proof. exact (EQ_MP (@lem1654646) (@lem1654641 a x h1)). Qed.
Lemma lem1654648 (a : real) (x : real) (h1 : term186 a x) : term186 a x.
Proof. exact (h1). Qed.
Lemma lem1654649 (a : real) (x : real) (h1 : term186 a x) : term185 a x.
Proof. exact (proj2 (@lem1654648 a x h1)). Qed.
Lemma lem1654651 (a : real) (x : real) (h1 : term186 a x) : term92 a x.
Proof. exact (proj2 (@lem1654649 a x h1)). Qed.
Lemma lem1654652 (a : real) (x : real) (h1 : term186 a x) : (term57 a x) = term8.
Proof. exact (proj1 (@lem1654649 a x h1)). Qed.
Lemma lem1654653 (a : real) (x : real) (h1 : term186 a x) : term66 a x.
Proof. exact (proj2 (@lem1654651 a x h1)). Qed.
Lemma lem1654656 (n : nat) (m : nat) : (term236 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1654657 : term237 = term238.
Proof. exact (@lem1654656 (NUMERAL 0) term29). Qed.
Lemma lem1654658 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1654659 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1654660 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem1654659 h1) (fun h1 : term238 = True => @lem1654658)). Qed.
Lemma lem1654661 : term238 = True.
Proof. exact (EQ_MP (@lem1654660) (@lem1654658)). Qed.
Lemma lem1654662 : term237 = True.
Proof. exact (TRANS (@lem1654657) (@lem1654661)). Qed.
Lemma lem1654663 : True = term237.
Proof. exact (SYM (@lem1654662)). Qed.
Lemma lem1654664 : term237.
Proof. exact (EQ_MP (@lem1654663) (@lem0)). Qed.
Lemma lem1654665 (a : real) (x : real) (h1 : term186 a x) : term273 a x.
Proof. exact (conj (@lem1654664) (@lem1654653 a x h1)). Qed.
Lemma lem1654667 (x : real) (y : real) : term241 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1654668 (a : real) (x : real) : term274 a x.
Proof. exact (@lem1654667 term32 (real_add a x)). Qed.
Lemma lem1654669 (a : real) (x : real) (h1 : term186 a x) : term275 a x.
Proof. exact (@lem1654668 a x (@lem1654665 a x h1)). Qed.
Lemma lem1654670 (a : real) (x : real) : (term276 a x) = (real_add a x).
Proof. exact (@lem1483460 (real_add a x)). Qed.
Lemma lem1654671 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1654672 (a : real) (x : real) : (term277 a x) = (term64 a x).
Proof. exact (MK_COMB (@lem1654671) (@lem1654670 a x)). Qed.
Lemma lem1654673 : term8 = term8.
Proof. exact (eq_refl term8). Qed.
Lemma lem1654674 (a : real) (x : real) : (term275 a x) = (term66 a x).
Proof. exact (MK_COMB (@lem1654672 a x) (@lem1654673)). Qed.
Lemma lem1654675 (a : real) (x : real) (h1 : term186 a x) : term66 a x.
Proof. exact (EQ_MP (@lem1654674 a x) (@lem1654669 a x h1)). Qed.
Lemma lem1654677 (y : real) : term246 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1654678 (a : real) (x : real) : term278 a x.
Proof. exact (@lem1654677 (term57 a x)). Qed.
Lemma lem1654679 (a : real) (x : real) (h1 : term186 a x) : term279 a x.
Proof. exact (@lem1654678 a x (@lem1654652 a x h1)). Qed.
Lemma lem1654680 (a : real) (x : real) (h1 : term186 a x) : term280 a x.
Proof. exact (@lem1654679 a x h1 term32). Qed.
Lemma lem1654681 (a : real) (x : real) : (term280 a x) = ((term281 a x) = term8).
Proof. exact (eq_refl (term280 a x)). Qed.
Lemma lem1654682 (a : real) (x : real) (h1 : term186 a x) : (term281 a x) = term8.
Proof. exact (EQ_MP (@lem1654681 a x) (@lem1654680 a x h1)). Qed.
Lemma lem1654683 (a : real) (x : real) : (term281 a x) = (term57 a x).
Proof. exact (@lem1483460 (term57 a x)). Qed.
Lemma lem1654684 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1654685 (a : real) (x : real) : (term282 a x) = (term155 a x).
Proof. exact (MK_COMB (@lem1654684) (@lem1654683 a x)). Qed.
Lemma lem1654686 : term8 = term8.
Proof. exact (eq_refl term8). Qed.
Lemma lem1654687 (a : real) (x : real) : ((term281 a x) = term8) = ((term57 a x) = term8).
Proof. exact (MK_COMB (@lem1654685 a x) (@lem1654686)). Qed.
Lemma lem1654688 (a : real) (x : real) (h1 : term186 a x) : (term57 a x) = term8.
Proof. exact (EQ_MP (@lem1654687 a x) (@lem1654682 a x h1)). Qed.
Lemma lem1654689 (a : real) (x : real) (h1 : term186 a x) : term283 a x.
Proof. exact (conj (@lem1654688 a x h1) (@lem1654675 a x h1)). Qed.
Lemma lem1654691 (x : real) (y : real) : term253 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1654692 (a : real) (x : real) : term284 a x.
Proof. exact (@lem1654691 (term57 a x) (real_add a x)). Qed.
Lemma lem1654693 (a : real) (x : real) (h1 : term186 a x) : term285 a x.
Proof. exact (@lem1654692 a x (@lem1654689 a x h1)). Qed.
Lemma lem1654694 (a : real) (x : real) : (term286 a x) = (term287 a x).
Proof. exact (@lem1483480 (term11 a) a (term11 x) x). Qed.
Lemma lem1654695 (a : real) : (term267 a) = (term259 a).
Proof. exact (@lem1483440 term22 a). Qed.
Lemma lem1654697 (m : nat) : (term260 m) = term8.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1654698 : term261 = term8.
Proof. exact (@lem1654697 term29). Qed.
Lemma lem1654699 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1654700 : term262 = term263.
Proof. exact (MK_COMB (@lem1654699) (@lem1654698)). Qed.
Lemma lem1654701 (a : real) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1654702 (a : real) : (term259 a) = (term264 a).
Proof. exact (MK_COMB (@lem1654700) (@lem1654701 a)). Qed.
Lemma lem1654703 (a : real) : (term267 a) = (term264 a).
Proof. exact (TRANS (@lem1654695 a) (@lem1654702 a)). Qed.
Lemma lem1654704 (a : real) : (term264 a) = term8.
Proof. exact (@lem1483446 a). Qed.
Lemma lem1654705 (a : real) : (term267 a) = term8.
Proof. exact (TRANS (@lem1654703 a) (@lem1654704 a)). Qed.
Lemma lem1654706 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1654707 (a : real) : (term288 a) = term266.
Proof. exact (MK_COMB (@lem1654706) (@lem1654705 a)). Qed.
Lemma lem1654708 (x : real) : (term267 x) = (term259 x).
Proof. exact (@lem1483440 term22 x). Qed.
Lemma lem1654710 (m : nat) : (term260 m) = term8.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1654711 : term261 = term8.
Proof. exact (@lem1654710 term29). Qed.
Lemma lem1654712 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1654713 : term262 = term263.
Proof. exact (MK_COMB (@lem1654712) (@lem1654711)). Qed.
Lemma lem1654714 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1654715 (x : real) : (term259 x) = (term264 x).
Proof. exact (MK_COMB (@lem1654713) (@lem1654714 x)). Qed.
Lemma lem1654716 (x : real) : (term267 x) = (term264 x).
Proof. exact (TRANS (@lem1654708 x) (@lem1654715 x)). Qed.
Lemma lem1654717 (x : real) : (term264 x) = term8.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1654718 (x : real) : (term267 x) = term8.
Proof. exact (TRANS (@lem1654716 x) (@lem1654717 x)). Qed.
Lemma lem1654719 (a : real) (x : real) : (term287 a x) = term268.
Proof. exact (MK_COMB (@lem1654707 a) (@lem1654718 x)). Qed.
Lemma lem1654720 (a : real) (x : real) : (term286 a x) = term268.
Proof. exact (TRANS (@lem1654694 a x) (@lem1654719 a x)). Qed.
Lemma lem1654721 : term268 = term8.
Proof. exact (@lem1483448 term8). Qed.
Lemma lem1654722 (a : real) (x : real) : (term286 a x) = term8.
Proof. exact (TRANS (@lem1654720 a x) (@lem1654721)). Qed.
Lemma lem1654723 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1654724 (a : real) (x : real) : (term289 a x) = term270.
Proof. exact (MK_COMB (@lem1654723) (@lem1654722 a x)). Qed.
Lemma lem1654725 : term8 = term8.
Proof. exact (eq_refl term8). Qed.
Lemma lem1654726 (a : real) (x : real) : (term285 a x) = term271.
Proof. exact (MK_COMB (@lem1654724 a x) (@lem1654725)). Qed.
Lemma lem1654727 (a : real) (x : real) (h1 : term186 a x) : term271.
Proof. exact (EQ_MP (@lem1654726 a x) (@lem1654693 a x h1)). Qed.
Lemma lem1654729 (n : nat) (m : nat) : (term236 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1654730 : term271 = term272.
Proof. exact (@lem1654729 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1654731 : term272 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1654732 : term271 = False.
Proof. exact (TRANS (@lem1654730) (@lem1654731)). Qed.
Lemma lem1654733 (a : real) (x : real) (h1 : term186 a x) : False.
Proof. exact (EQ_MP (@lem1654732) (@lem1654727 a x h1)). Qed.
Lemma lem1654734 (a : real) (x : real) (h1 : term187 a x) : False.
Proof. exact (or_elim (@lem1654561 a x h1) (fun h0 : term173 a x => @lem1654647 a x h0) (fun h0 : term186 a x => @lem1654733 a x h0)). Qed.
Lemma lem1654735 (a : real) (x : real) (h1 : term190 a x) : False.
Proof. exact (or_elim (@lem1654365 a x h1) (fun h0 : term161 a x => @lem1654560 a x h0) (fun h0 : term187 a x => @lem1654734 a x h0)). Qed.
Lemma lem1654736 (a : real) (x : real) (h1 : term233 a x) : term233 a x.
Proof. exact (h1). Qed.
Lemma lem1654737 (a : real) (x : real) (h1 : term211 a x) : term211 a x.
Proof. exact (h1). Qed.
Lemma lem1654738 (a : real) (x : real) (h1 : term202 a x) : term202 a x.
Proof. exact (h1). Qed.
Lemma lem1654739 (a : real) (x : real) (h1 : term202 a x) : term200 a x.
Proof. exact (proj2 (@lem1654738 a x h1)). Qed.
Lemma lem1654741 (a : real) (x : real) (h1 : term202 a x) : term87 a x.
Proof. exact (proj2 (@lem1654739 a x h1)). Qed.
Lemma lem1654742 (a : real) (x : real) (h1 : term202 a x) : (term17 a x) = term8.
Proof. exact (proj1 (@lem1654739 a x h1)). Qed.
Lemma lem1654744 (a : real) (x : real) (h1 : term202 a x) : term45 a x.
Proof. exact (proj1 (@lem1654741 a x h1)). Qed.
Lemma lem1654746 (n : nat) (m : nat) : (term236 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1654747 : term237 = term238.
Proof. exact (@lem1654746 (NUMERAL 0) term29). Qed.
Lemma lem1654748 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1654749 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1654750 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem1654749 h1) (fun h1 : term238 = True => @lem1654748)). Qed.
Lemma lem1654751 : term238 = True.
Proof. exact (EQ_MP (@lem1654750) (@lem1654748)). Qed.
Lemma lem1654752 : term237 = True.
Proof. exact (TRANS (@lem1654747) (@lem1654751)). Qed.
Lemma lem1654753 : True = term237.
Proof. exact (SYM (@lem1654752)). Qed.
Lemma lem1654754 : term237.
Proof. exact (EQ_MP (@lem1654753) (@lem0)). Qed.
Lemma lem1654755 (a : real) (x : real) (h1 : term202 a x) : term240 a x.
Proof. exact (conj (@lem1654754) (@lem1654744 a x h1)). Qed.
Lemma lem1654757 (x : real) (y : real) : term241 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1654758 (a : real) (x : real) : term242 a x.
Proof. exact (@lem1654757 term32 (term17 a x)). Qed.
Lemma lem1654759 (a : real) (x : real) (h1 : term202 a x) : term243 a x.
Proof. exact (@lem1654758 a x (@lem1654755 a x h1)). Qed.
Lemma lem1654760 (a : real) (x : real) : (term244 a x) = (term17 a x).
Proof. exact (@lem1483460 (term17 a x)). Qed.
Lemma lem1654761 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1654762 (a : real) (x : real) : (term245 a x) = (term43 a x).
Proof. exact (MK_COMB (@lem1654761) (@lem1654760 a x)). Qed.
Lemma lem1654763 : term8 = term8.
Proof. exact (eq_refl term8). Qed.
Lemma lem1654764 (a : real) (x : real) : (term243 a x) = (term45 a x).
Proof. exact (MK_COMB (@lem1654762 a x) (@lem1654763)). Qed.
Lemma lem1654765 (a : real) (x : real) (h1 : term202 a x) : term45 a x.
Proof. exact (EQ_MP (@lem1654764 a x) (@lem1654759 a x h1)). Qed.
Lemma lem1654767 (y : real) : term246 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1654768 (a : real) (x : real) : term247 a x.
Proof. exact (@lem1654767 (term17 a x)). Qed.
Lemma lem1654769 (a : real) (x : real) (h1 : term202 a x) : term248 a x.
Proof. exact (@lem1654768 a x (@lem1654742 a x h1)). Qed.
Lemma lem1654770 (a : real) (x : real) (h1 : term202 a x) : term249 a x.
Proof. exact (@lem1654769 a x h1 term22). Qed.
Lemma lem1654771 (a : real) (x : real) : (term249 a x) = ((term20 a x) = term8).
Proof. exact (eq_refl (term249 a x)). Qed.
Lemma lem1654772 (a : real) (x : real) (h1 : term202 a x) : (term20 a x) = term8.
Proof. exact (EQ_MP (@lem1654771 a x) (@lem1654770 a x h1)). Qed.
Lemma lem1654773 (a : real) (x : real) : (term20 a x) = (term21 a x).
Proof. exact (@lem1483508 (term11 a) term22 x). Qed.
Lemma lem1654774 (x : real) : (term11 x) = (term11 x).
Proof. exact (eq_refl (term11 x)). Qed.
Lemma lem1654775 (a : real) : (term23 a) = (term24 a).
Proof. exact (@lem1483476 term22 term22 a). Qed.
Lemma lem1654777 (m : nat) (n : nat) : (term25 m n) = (term26 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1654778 : term27 = term28.
Proof. exact (@lem1654777 term29 term29). Qed.
Lemma lem1654779 : (term30 = (BIT1 0)) = (term31 = term29).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1654780 : term31 = term29.
Proof. exact (EQ_MP (@lem1654779) (@lem940073)). Qed.
Lemma lem1654781 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1654782 : term28 = term32.
Proof. exact (MK_COMB (@lem1654781) (@lem1654780)). Qed.
Lemma lem1654783 : term27 = term32.
Proof. exact (TRANS (@lem1654778) (@lem1654782)). Qed.
Lemma lem1654784 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1654785 : term33 = term34.
Proof. exact (MK_COMB (@lem1654784) (@lem1654783)). Qed.
Lemma lem1654786 (a : real) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1654787 (a : real) : (term24 a) = (term35 a).
Proof. exact (MK_COMB (@lem1654785) (@lem1654786 a)). Qed.
Lemma lem1654788 (a : real) : (term23 a) = (term35 a).
Proof. exact (TRANS (@lem1654775 a) (@lem1654787 a)). Qed.
Lemma lem1654789 (a : real) : (term35 a) = a.
Proof. exact (@lem1483436 a). Qed.
Lemma lem1654790 (a : real) : (term23 a) = a.
Proof. exact (TRANS (@lem1654788 a) (@lem1654789 a)). Qed.
Lemma lem1654791 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1654792 (a : real) : (term36 a) = (real_add a).
Proof. exact (MK_COMB (@lem1654791) (@lem1654790 a)). Qed.
Lemma lem1654793 (a : real) (x : real) : (term21 a x) = (term16 a x).
Proof. exact (MK_COMB (@lem1654792 a) (@lem1654774 x)). Qed.
Lemma lem1654794 (a : real) (x : real) : (term20 a x) = (term16 a x).
Proof. exact (TRANS (@lem1654773 a x) (@lem1654793 a x)). Qed.
Lemma lem1654795 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1654796 (a : real) (x : real) : (term250 a x) = (term251 a x).
Proof. exact (MK_COMB (@lem1654795) (@lem1654794 a x)). Qed.
Lemma lem1654797 : term8 = term8.
Proof. exact (eq_refl term8). Qed.
Lemma lem1654798 (a : real) (x : real) : ((term20 a x) = term8) = ((term16 a x) = term8).
Proof. exact (MK_COMB (@lem1654796 a x) (@lem1654797)). Qed.
Lemma lem1654799 (a : real) (x : real) (h1 : term202 a x) : (term16 a x) = term8.
Proof. exact (EQ_MP (@lem1654798 a x) (@lem1654772 a x h1)). Qed.
Lemma lem1654800 (a : real) (x : real) (h1 : term202 a x) : term252 a x.
Proof. exact (conj (@lem1654799 a x h1) (@lem1654765 a x h1)). Qed.
Lemma lem1654802 (x : real) (y : real) : term253 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1654803 (a : real) (x : real) : term254 a x.
Proof. exact (@lem1654802 (term16 a x) (term17 a x)). Qed.
Lemma lem1654804 (a : real) (x : real) (h1 : term202 a x) : term255 a x.
Proof. exact (@lem1654803 a x (@lem1654800 a x h1)). Qed.
Lemma lem1654805 (a : real) (x : real) : (term256 a x) = (term257 a x).
Proof. exact (@lem1483480 a (term11 a) (term11 x) x). Qed.
Lemma lem1654806 (a : real) : (term258 a) = (term259 a).
Proof. exact (@lem1483442 term22 a). Qed.
Lemma lem1654808 (m : nat) : (term260 m) = term8.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1654809 : term261 = term8.
Proof. exact (@lem1654808 term29). Qed.
Lemma lem1654810 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1654811 : term262 = term263.
Proof. exact (MK_COMB (@lem1654810) (@lem1654809)). Qed.
Lemma lem1654812 (a : real) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1654813 (a : real) : (term259 a) = (term264 a).
Proof. exact (MK_COMB (@lem1654811) (@lem1654812 a)). Qed.
Lemma lem1654814 (a : real) : (term258 a) = (term264 a).
Proof. exact (TRANS (@lem1654806 a) (@lem1654813 a)). Qed.
Lemma lem1654815 (a : real) : (term264 a) = term8.
Proof. exact (@lem1483446 a). Qed.
Lemma lem1654816 (a : real) : (term258 a) = term8.
Proof. exact (TRANS (@lem1654814 a) (@lem1654815 a)). Qed.
Lemma lem1654817 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1654818 (a : real) : (term265 a) = term266.
Proof. exact (MK_COMB (@lem1654817) (@lem1654816 a)). Qed.
Lemma lem1654819 (x : real) : (term267 x) = (term259 x).
Proof. exact (@lem1483440 term22 x). Qed.
Lemma lem1654821 (m : nat) : (term260 m) = term8.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1654822 : term261 = term8.
Proof. exact (@lem1654821 term29). Qed.
Lemma lem1654823 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1654824 : term262 = term263.
Proof. exact (MK_COMB (@lem1654823) (@lem1654822)). Qed.
Lemma lem1654825 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1654826 (x : real) : (term259 x) = (term264 x).
Proof. exact (MK_COMB (@lem1654824) (@lem1654825 x)). Qed.
Lemma lem1654827 (x : real) : (term267 x) = (term264 x).
Proof. exact (TRANS (@lem1654819 x) (@lem1654826 x)). Qed.
Lemma lem1654828 (x : real) : (term264 x) = term8.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1654829 (x : real) : (term267 x) = term8.
Proof. exact (TRANS (@lem1654827 x) (@lem1654828 x)). Qed.
Lemma lem1654830 (a : real) (x : real) : (term257 a x) = term268.
Proof. exact (MK_COMB (@lem1654818 a) (@lem1654829 x)). Qed.
Lemma lem1654831 (a : real) (x : real) : (term256 a x) = term268.
Proof. exact (TRANS (@lem1654805 a x) (@lem1654830 a x)). Qed.
Lemma lem1654832 : term268 = term8.
Proof. exact (@lem1483448 term8). Qed.
Lemma lem1654833 (a : real) (x : real) : (term256 a x) = term8.
Proof. exact (TRANS (@lem1654831 a x) (@lem1654832)). Qed.
Lemma lem1654834 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1654835 (a : real) (x : real) : (term269 a x) = term270.
Proof. exact (MK_COMB (@lem1654834) (@lem1654833 a x)). Qed.
Lemma lem1654836 : term8 = term8.
Proof. exact (eq_refl term8). Qed.
Lemma lem1654837 (a : real) (x : real) : (term255 a x) = term271.
Proof. exact (MK_COMB (@lem1654835 a x) (@lem1654836)). Qed.
Lemma lem1654838 (a : real) (x : real) (h1 : term202 a x) : term271.
Proof. exact (EQ_MP (@lem1654837 a x) (@lem1654804 a x h1)). Qed.
Lemma lem1654840 (n : nat) (m : nat) : (term236 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1654841 : term271 = term272.
Proof. exact (@lem1654840 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1654842 : term272 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1654843 : term271 = False.
Proof. exact (TRANS (@lem1654841) (@lem1654842)). Qed.
Lemma lem1654844 (a : real) (x : real) (h1 : term202 a x) : False.
Proof. exact (EQ_MP (@lem1654843) (@lem1654838 a x h1)). Qed.
Lemma lem1654845 (a : real) (x : real) (h1 : term210 a x) : term210 a x.
Proof. exact (h1). Qed.
Lemma lem1654846 (a : real) (x : real) (h1 : term210 a x) : term209 a x.
Proof. exact (proj2 (@lem1654845 a x h1)). Qed.
Lemma lem1654848 (a : real) (x : real) (h1 : term210 a x) : term87 a x.
Proof. exact (proj2 (@lem1654846 a x h1)). Qed.
Lemma lem1654849 (a : real) (x : real) (h1 : term210 a x) : (term57 a x) = term8.
Proof. exact (proj1 (@lem1654846 a x h1)). Qed.
Lemma lem1654850 (a : real) (x : real) (h1 : term210 a x) : term62 a x.
Proof. exact (proj2 (@lem1654848 a x h1)). Qed.
Lemma lem1654853 (n : nat) (m : nat) : (term236 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1654854 : term237 = term238.
Proof. exact (@lem1654853 (NUMERAL 0) term29). Qed.
Lemma lem1654855 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1654856 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1654857 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem1654856 h1) (fun h1 : term238 = True => @lem1654855)). Qed.
Lemma lem1654858 : term238 = True.
Proof. exact (EQ_MP (@lem1654857) (@lem1654855)). Qed.
Lemma lem1654859 : term237 = True.
Proof. exact (TRANS (@lem1654854) (@lem1654858)). Qed.
Lemma lem1654860 : True = term237.
Proof. exact (SYM (@lem1654859)). Qed.
Lemma lem1654861 : term237.
Proof. exact (EQ_MP (@lem1654860) (@lem0)). Qed.
Lemma lem1654862 (a : real) (x : real) (h1 : term210 a x) : term303 a x.
Proof. exact (conj (@lem1654861) (@lem1654850 a x h1)). Qed.
Lemma lem1654864 (x : real) (y : real) : term241 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1654865 (a : real) (x : real) : term304 a x.
Proof. exact (@lem1654864 term32 (term57 a x)). Qed.
Lemma lem1654866 (a : real) (x : real) (h1 : term210 a x) : term305 a x.
Proof. exact (@lem1654865 a x (@lem1654862 a x h1)). Qed.
Lemma lem1654867 (a : real) (x : real) : (term281 a x) = (term57 a x).
Proof. exact (@lem1483460 (term57 a x)). Qed.
Lemma lem1654868 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1654869 (a : real) (x : real) : (term306 a x) = (term60 a x).
Proof. exact (MK_COMB (@lem1654868) (@lem1654867 a x)). Qed.
Lemma lem1654870 : term8 = term8.
Proof. exact (eq_refl term8). Qed.
Lemma lem1654871 (a : real) (x : real) : (term305 a x) = (term62 a x).
Proof. exact (MK_COMB (@lem1654869 a x) (@lem1654870)). Qed.
Lemma lem1654872 (a : real) (x : real) (h1 : term210 a x) : term62 a x.
Proof. exact (EQ_MP (@lem1654871 a x) (@lem1654866 a x h1)). Qed.
Lemma lem1654874 (y : real) : term246 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1654875 (a : real) (x : real) : term278 a x.
Proof. exact (@lem1654874 (term57 a x)). Qed.
Lemma lem1654876 (a : real) (x : real) (h1 : term210 a x) : term279 a x.
Proof. exact (@lem1654875 a x (@lem1654849 a x h1)). Qed.
Lemma lem1654877 (a : real) (x : real) (h1 : term210 a x) : term307 a x.
Proof. exact (@lem1654876 a x h1 term22). Qed.
Lemma lem1654878 (a : real) (x : real) : (term307 a x) = ((term308 a x) = term8).
Proof. exact (eq_refl (term307 a x)). Qed.
Lemma lem1654879 (a : real) (x : real) (h1 : term210 a x) : (term308 a x) = term8.
Proof. exact (EQ_MP (@lem1654878 a x) (@lem1654877 a x h1)). Qed.
Lemma lem1654880 (a : real) (x : real) : (term308 a x) = (term309 a x).
Proof. exact (@lem1483508 (term11 a) term22 (term11 x)). Qed.
Lemma lem1654881 (x : real) : (term23 x) = (term24 x).
Proof. exact (@lem1483476 term22 term22 x). Qed.
Lemma lem1654883 (m : nat) (n : nat) : (term25 m n) = (term26 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1654884 : term27 = term28.
Proof. exact (@lem1654883 term29 term29). Qed.
Lemma lem1654885 : (term30 = (BIT1 0)) = (term31 = term29).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1654886 : term31 = term29.
Proof. exact (EQ_MP (@lem1654885) (@lem940073)). Qed.
Lemma lem1654887 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1654888 : term28 = term32.
Proof. exact (MK_COMB (@lem1654887) (@lem1654886)). Qed.
Lemma lem1654889 : term27 = term32.
Proof. exact (TRANS (@lem1654884) (@lem1654888)). Qed.
Lemma lem1654890 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1654891 : term33 = term34.
Proof. exact (MK_COMB (@lem1654890) (@lem1654889)). Qed.
Lemma lem1654892 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1654893 (x : real) : (term24 x) = (term35 x).
Proof. exact (MK_COMB (@lem1654891) (@lem1654892 x)). Qed.
Lemma lem1654894 (x : real) : (term23 x) = (term35 x).
Proof. exact (TRANS (@lem1654881 x) (@lem1654893 x)). Qed.
Lemma lem1654895 (x : real) : (term35 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1654896 (x : real) : (term23 x) = x.
Proof. exact (TRANS (@lem1654894 x) (@lem1654895 x)). Qed.
Lemma lem1654897 (a : real) : (term23 a) = (term24 a).
Proof. exact (@lem1483476 term22 term22 a). Qed.
Lemma lem1654899 (m : nat) (n : nat) : (term25 m n) = (term26 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1654900 : term27 = term28.
Proof. exact (@lem1654899 term29 term29). Qed.
Lemma lem1654901 : (term30 = (BIT1 0)) = (term31 = term29).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1654902 : term31 = term29.
Proof. exact (EQ_MP (@lem1654901) (@lem940073)). Qed.
Lemma lem1654903 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1654904 : term28 = term32.
Proof. exact (MK_COMB (@lem1654903) (@lem1654902)). Qed.
Lemma lem1654905 : term27 = term32.
Proof. exact (TRANS (@lem1654900) (@lem1654904)). Qed.
Lemma lem1654906 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1654907 : term33 = term34.
Proof. exact (MK_COMB (@lem1654906) (@lem1654905)). Qed.
Lemma lem1654908 (a : real) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1654909 (a : real) : (term24 a) = (term35 a).
Proof. exact (MK_COMB (@lem1654907) (@lem1654908 a)). Qed.
Lemma lem1654910 (a : real) : (term23 a) = (term35 a).
Proof. exact (TRANS (@lem1654897 a) (@lem1654909 a)). Qed.
Lemma lem1654911 (a : real) : (term35 a) = a.
Proof. exact (@lem1483436 a). Qed.
Lemma lem1654912 (a : real) : (term23 a) = a.
Proof. exact (TRANS (@lem1654910 a) (@lem1654911 a)). Qed.
Lemma lem1654913 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1654914 (a : real) : (term36 a) = (real_add a).
Proof. exact (MK_COMB (@lem1654913) (@lem1654912 a)). Qed.
Lemma lem1654915 (a : real) (x : real) : (term309 a x) = (real_add a x).
Proof. exact (MK_COMB (@lem1654914 a) (@lem1654896 x)). Qed.
Lemma lem1654916 (a : real) (x : real) : (term308 a x) = (real_add a x).
Proof. exact (TRANS (@lem1654880 a x) (@lem1654915 a x)). Qed.
Lemma lem1654917 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1654918 (a : real) (x : real) : (term310 a x) = (term311 a x).
Proof. exact (MK_COMB (@lem1654917) (@lem1654916 a x)). Qed.
Lemma lem1654919 : term8 = term8.
Proof. exact (eq_refl term8). Qed.
Lemma lem1654920 (a : real) (x : real) : ((term308 a x) = term8) = ((real_add a x) = term8).
Proof. exact (MK_COMB (@lem1654918 a x) (@lem1654919)). Qed.
Lemma lem1654921 (a : real) (x : real) (h1 : term210 a x) : (real_add a x) = term8.
Proof. exact (EQ_MP (@lem1654920 a x) (@lem1654879 a x h1)). Qed.
Lemma lem1654922 (a : real) (x : real) (h1 : term210 a x) : term312 a x.
Proof. exact (conj (@lem1654921 a x h1) (@lem1654872 a x h1)). Qed.
Lemma lem1654924 (x : real) (y : real) : term253 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1654925 (a : real) (x : real) : term313 a x.
Proof. exact (@lem1654924 (real_add a x) (term57 a x)). Qed.
Lemma lem1654926 (a : real) (x : real) (h1 : term210 a x) : term314 a x.
Proof. exact (@lem1654925 a x (@lem1654922 a x h1)). Qed.
Lemma lem1654927 (a : real) (x : real) : (term315 a x) = (term316 a x).
Proof. exact (@lem1483480 a (term11 a) x (term11 x)). Qed.
Lemma lem1654928 (a : real) : (term258 a) = (term259 a).
Proof. exact (@lem1483442 term22 a). Qed.
Lemma lem1654930 (m : nat) : (term260 m) = term8.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1654931 : term261 = term8.
Proof. exact (@lem1654930 term29). Qed.
Lemma lem1654932 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1654933 : term262 = term263.
Proof. exact (MK_COMB (@lem1654932) (@lem1654931)). Qed.
Lemma lem1654934 (a : real) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1654935 (a : real) : (term259 a) = (term264 a).
Proof. exact (MK_COMB (@lem1654933) (@lem1654934 a)). Qed.
Lemma lem1654936 (a : real) : (term258 a) = (term264 a).
Proof. exact (TRANS (@lem1654928 a) (@lem1654935 a)). Qed.
Lemma lem1654937 (a : real) : (term264 a) = term8.
Proof. exact (@lem1483446 a). Qed.
Lemma lem1654938 (a : real) : (term258 a) = term8.
Proof. exact (TRANS (@lem1654936 a) (@lem1654937 a)). Qed.
Lemma lem1654939 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1654940 (a : real) : (term265 a) = term266.
Proof. exact (MK_COMB (@lem1654939) (@lem1654938 a)). Qed.
Lemma lem1654941 (x : real) : (term258 x) = (term259 x).
Proof. exact (@lem1483442 term22 x). Qed.
Lemma lem1654943 (m : nat) : (term260 m) = term8.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1654944 : term261 = term8.
Proof. exact (@lem1654943 term29). Qed.
Lemma lem1654945 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1654946 : term262 = term263.
Proof. exact (MK_COMB (@lem1654945) (@lem1654944)). Qed.
Lemma lem1654947 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1654948 (x : real) : (term259 x) = (term264 x).
Proof. exact (MK_COMB (@lem1654946) (@lem1654947 x)). Qed.
Lemma lem1654949 (x : real) : (term258 x) = (term264 x).
Proof. exact (TRANS (@lem1654941 x) (@lem1654948 x)). Qed.
Lemma lem1654950 (x : real) : (term264 x) = term8.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1654951 (x : real) : (term258 x) = term8.
Proof. exact (TRANS (@lem1654949 x) (@lem1654950 x)). Qed.
Lemma lem1654952 (a : real) (x : real) : (term316 a x) = term268.
Proof. exact (MK_COMB (@lem1654940 a) (@lem1654951 x)). Qed.
Lemma lem1654953 (a : real) (x : real) : (term315 a x) = term268.
Proof. exact (TRANS (@lem1654927 a x) (@lem1654952 a x)). Qed.
Lemma lem1654954 : term268 = term8.
Proof. exact (@lem1483448 term8). Qed.
Lemma lem1654955 (a : real) (x : real) : (term315 a x) = term8.
Proof. exact (TRANS (@lem1654953 a x) (@lem1654954)). Qed.
Lemma lem1654956 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1654957 (a : real) (x : real) : (term317 a x) = term270.
Proof. exact (MK_COMB (@lem1654956) (@lem1654955 a x)). Qed.
Lemma lem1654958 : term8 = term8.
Proof. exact (eq_refl term8). Qed.
Lemma lem1654959 (a : real) (x : real) : (term314 a x) = term271.
Proof. exact (MK_COMB (@lem1654957 a x) (@lem1654958)). Qed.
Lemma lem1654960 (a : real) (x : real) (h1 : term210 a x) : term271.
Proof. exact (EQ_MP (@lem1654959 a x) (@lem1654926 a x h1)). Qed.
Lemma lem1654962 (n : nat) (m : nat) : (term236 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1654963 : term271 = term272.
Proof. exact (@lem1654962 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1654964 : term272 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1654965 : term271 = False.
Proof. exact (TRANS (@lem1654963) (@lem1654964)). Qed.
Lemma lem1654966 (a : real) (x : real) (h1 : term210 a x) : False.
Proof. exact (EQ_MP (@lem1654965) (@lem1654960 a x h1)). Qed.
Lemma lem1654967 (a : real) (x : real) (h1 : term211 a x) : False.
Proof. exact (or_elim (@lem1654737 a x h1) (fun h0 : term202 a x => @lem1654844 a x h0) (fun h0 : term210 a x => @lem1654966 a x h0)). Qed.
Lemma lem1654968 (a : real) (x : real) (h1 : term230 a x) : term230 a x.
Proof. exact (h1). Qed.
Lemma lem1654969 (a : real) (x : real) (h1 : term223 a x) : term223 a x.
Proof. exact (h1). Qed.
Lemma lem1654970 (a : real) (x : real) (h1 : term223 a x) : term221 a x.
Proof. exact (proj2 (@lem1654969 a x h1)). Qed.
Lemma lem1654972 (a : real) (x : real) (h1 : term223 a x) : term88 a x.
Proof. exact (proj2 (@lem1654970 a x h1)). Qed.
Lemma lem1654973 (a : real) (x : real) (h1 : term223 a x) : (term17 a x) = term8.
Proof. exact (proj1 (@lem1654970 a x h1)). Qed.
Lemma lem1654975 (a : real) (x : real) (h1 : term223 a x) : term41 a x.
Proof. exact (proj1 (@lem1654972 a x h1)). Qed.
Lemma lem1654977 (n : nat) (m : nat) : (term236 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1654978 : term237 = term238.
Proof. exact (@lem1654977 (NUMERAL 0) term29). Qed.
Lemma lem1654979 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1654980 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1654981 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem1654980 h1) (fun h1 : term238 = True => @lem1654979)). Qed.
Lemma lem1654982 : term238 = True.
Proof. exact (EQ_MP (@lem1654981) (@lem1654979)). Qed.
Lemma lem1654983 : term237 = True.
Proof. exact (TRANS (@lem1654978) (@lem1654982)). Qed.
Lemma lem1654984 : True = term237.
Proof. exact (SYM (@lem1654983)). Qed.
Lemma lem1654985 : term237.
Proof. exact (EQ_MP (@lem1654984) (@lem0)). Qed.
Lemma lem1654986 (a : real) (x : real) (h1 : term223 a x) : term290 a x.
Proof. exact (conj (@lem1654985) (@lem1654975 a x h1)). Qed.
Lemma lem1654988 (x : real) (y : real) : term241 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1654989 (a : real) (x : real) : term291 a x.
Proof. exact (@lem1654988 term32 (term16 a x)). Qed.
Lemma lem1654990 (a : real) (x : real) (h1 : term223 a x) : term292 a x.
Proof. exact (@lem1654989 a x (@lem1654986 a x h1)). Qed.
Lemma lem1654991 (a : real) (x : real) : (term293 a x) = (term16 a x).
Proof. exact (@lem1483460 (term16 a x)). Qed.
Lemma lem1654992 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1654993 (a : real) (x : real) : (term294 a x) = (term39 a x).
Proof. exact (MK_COMB (@lem1654992) (@lem1654991 a x)). Qed.
Lemma lem1654994 : term8 = term8.
Proof. exact (eq_refl term8). Qed.
Lemma lem1654995 (a : real) (x : real) : (term292 a x) = (term41 a x).
Proof. exact (MK_COMB (@lem1654993 a x) (@lem1654994)). Qed.
Lemma lem1654996 (a : real) (x : real) (h1 : term223 a x) : term41 a x.
Proof. exact (EQ_MP (@lem1654995 a x) (@lem1654990 a x h1)). Qed.
Lemma lem1654998 (y : real) : term246 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1654999 (a : real) (x : real) : term247 a x.
Proof. exact (@lem1654998 (term17 a x)). Qed.
Lemma lem1655000 (a : real) (x : real) (h1 : term223 a x) : term248 a x.
Proof. exact (@lem1654999 a x (@lem1654973 a x h1)). Qed.
Lemma lem1655001 (a : real) (x : real) (h1 : term223 a x) : term295 a x.
Proof. exact (@lem1655000 a x h1 term32). Qed.
Lemma lem1655002 (a : real) (x : real) : (term295 a x) = ((term244 a x) = term8).
Proof. exact (eq_refl (term295 a x)). Qed.
Lemma lem1655003 (a : real) (x : real) (h1 : term223 a x) : (term244 a x) = term8.
Proof. exact (EQ_MP (@lem1655002 a x) (@lem1655001 a x h1)). Qed.
Lemma lem1655004 (a : real) (x : real) : (term244 a x) = (term17 a x).
Proof. exact (@lem1483460 (term17 a x)). Qed.
Lemma lem1655005 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1655006 (a : real) (x : real) : (term296 a x) = (term127 a x).
Proof. exact (MK_COMB (@lem1655005) (@lem1655004 a x)). Qed.
Lemma lem1655007 : term8 = term8.
Proof. exact (eq_refl term8). Qed.
Lemma lem1655008 (a : real) (x : real) : ((term244 a x) = term8) = ((term17 a x) = term8).
Proof. exact (MK_COMB (@lem1655006 a x) (@lem1655007)). Qed.
Lemma lem1655009 (a : real) (x : real) (h1 : term223 a x) : (term17 a x) = term8.
Proof. exact (EQ_MP (@lem1655008 a x) (@lem1655003 a x h1)). Qed.
Lemma lem1655010 (a : real) (x : real) (h1 : term223 a x) : term297 a x.
Proof. exact (conj (@lem1655009 a x h1) (@lem1654996 a x h1)). Qed.
Lemma lem1655012 (x : real) (y : real) : term253 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1655013 (a : real) (x : real) : term298 a x.
Proof. exact (@lem1655012 (term17 a x) (term16 a x)). Qed.
Lemma lem1655014 (a : real) (x : real) (h1 : term223 a x) : term299 a x.
Proof. exact (@lem1655013 a x (@lem1655010 a x h1)). Qed.
Lemma lem1655015 (a : real) (x : real) : (term300 a x) = (term301 a x).
Proof. exact (@lem1483480 (term11 a) a x (term11 x)). Qed.
Lemma lem1655016 (a : real) : (term267 a) = (term259 a).
Proof. exact (@lem1483440 term22 a). Qed.
Lemma lem1655018 (m : nat) : (term260 m) = term8.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1655019 : term261 = term8.
Proof. exact (@lem1655018 term29). Qed.
Lemma lem1655020 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1655021 : term262 = term263.
Proof. exact (MK_COMB (@lem1655020) (@lem1655019)). Qed.
Lemma lem1655022 (a : real) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1655023 (a : real) : (term259 a) = (term264 a).
Proof. exact (MK_COMB (@lem1655021) (@lem1655022 a)). Qed.
Lemma lem1655024 (a : real) : (term267 a) = (term264 a).
Proof. exact (TRANS (@lem1655016 a) (@lem1655023 a)). Qed.
Lemma lem1655025 (a : real) : (term264 a) = term8.
Proof. exact (@lem1483446 a). Qed.
Lemma lem1655026 (a : real) : (term267 a) = term8.
Proof. exact (TRANS (@lem1655024 a) (@lem1655025 a)). Qed.
Lemma lem1655027 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1655028 (a : real) : (term288 a) = term266.
Proof. exact (MK_COMB (@lem1655027) (@lem1655026 a)). Qed.
Lemma lem1655029 (x : real) : (term258 x) = (term259 x).
Proof. exact (@lem1483442 term22 x). Qed.
Lemma lem1655031 (m : nat) : (term260 m) = term8.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1655032 : term261 = term8.
Proof. exact (@lem1655031 term29). Qed.
Lemma lem1655033 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1655034 : term262 = term263.
Proof. exact (MK_COMB (@lem1655033) (@lem1655032)). Qed.
Lemma lem1655035 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1655036 (x : real) : (term259 x) = (term264 x).
Proof. exact (MK_COMB (@lem1655034) (@lem1655035 x)). Qed.
Lemma lem1655037 (x : real) : (term258 x) = (term264 x).
Proof. exact (TRANS (@lem1655029 x) (@lem1655036 x)). Qed.
Lemma lem1655038 (x : real) : (term264 x) = term8.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1655039 (x : real) : (term258 x) = term8.
Proof. exact (TRANS (@lem1655037 x) (@lem1655038 x)). Qed.
Lemma lem1655040 (a : real) (x : real) : (term301 a x) = term268.
Proof. exact (MK_COMB (@lem1655028 a) (@lem1655039 x)). Qed.
Lemma lem1655041 (a : real) (x : real) : (term300 a x) = term268.
Proof. exact (TRANS (@lem1655015 a x) (@lem1655040 a x)). Qed.
Lemma lem1655042 : term268 = term8.
Proof. exact (@lem1483448 term8). Qed.
Lemma lem1655043 (a : real) (x : real) : (term300 a x) = term8.
Proof. exact (TRANS (@lem1655041 a x) (@lem1655042)). Qed.
Lemma lem1655044 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1655045 (a : real) (x : real) : (term302 a x) = term270.
Proof. exact (MK_COMB (@lem1655044) (@lem1655043 a x)). Qed.
Lemma lem1655046 : term8 = term8.
Proof. exact (eq_refl term8). Qed.
Lemma lem1655047 (a : real) (x : real) : (term299 a x) = term271.
Proof. exact (MK_COMB (@lem1655045 a x) (@lem1655046)). Qed.
Lemma lem1655048 (a : real) (x : real) (h1 : term223 a x) : term271.
Proof. exact (EQ_MP (@lem1655047 a x) (@lem1655014 a x h1)). Qed.
Lemma lem1655050 (n : nat) (m : nat) : (term236 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1655051 : term271 = term272.
Proof. exact (@lem1655050 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1655052 : term272 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1655053 : term271 = False.
Proof. exact (TRANS (@lem1655051) (@lem1655052)). Qed.
Lemma lem1655054 (a : real) (x : real) (h1 : term223 a x) : False.
Proof. exact (EQ_MP (@lem1655053) (@lem1655048 a x h1)). Qed.
Lemma lem1655055 (a : real) (x : real) (h1 : term229 a x) : term229 a x.
Proof. exact (h1). Qed.
Lemma lem1655056 (a : real) (x : real) (h1 : term229 a x) : term228 a x.
Proof. exact (proj2 (@lem1655055 a x h1)). Qed.
Lemma lem1655058 (a : real) (x : real) (h1 : term229 a x) : term88 a x.
Proof. exact (proj2 (@lem1655056 a x h1)). Qed.
Lemma lem1655059 (a : real) (x : real) (h1 : term229 a x) : (term57 a x) = term8.
Proof. exact (proj1 (@lem1655056 a x h1)). Qed.
Lemma lem1655060 (a : real) (x : real) (h1 : term229 a x) : term62 a x.
Proof. exact (proj2 (@lem1655058 a x h1)). Qed.
Lemma lem1655063 (n : nat) (m : nat) : (term236 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1655064 : term237 = term238.
Proof. exact (@lem1655063 (NUMERAL 0) term29). Qed.
Lemma lem1655065 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1655066 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1655067 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem1655066 h1) (fun h1 : term238 = True => @lem1655065)). Qed.
Lemma lem1655068 : term238 = True.
Proof. exact (EQ_MP (@lem1655067) (@lem1655065)). Qed.
Lemma lem1655069 : term237 = True.
Proof. exact (TRANS (@lem1655064) (@lem1655068)). Qed.
Lemma lem1655070 : True = term237.
Proof. exact (SYM (@lem1655069)). Qed.
Lemma lem1655071 : term237.
Proof. exact (EQ_MP (@lem1655070) (@lem0)). Qed.
Lemma lem1655072 (a : real) (x : real) (h1 : term229 a x) : term303 a x.
Proof. exact (conj (@lem1655071) (@lem1655060 a x h1)). Qed.
Lemma lem1655074 (x : real) (y : real) : term241 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1655075 (a : real) (x : real) : term304 a x.
Proof. exact (@lem1655074 term32 (term57 a x)). Qed.
Lemma lem1655076 (a : real) (x : real) (h1 : term229 a x) : term305 a x.
Proof. exact (@lem1655075 a x (@lem1655072 a x h1)). Qed.
Lemma lem1655077 (a : real) (x : real) : (term281 a x) = (term57 a x).
Proof. exact (@lem1483460 (term57 a x)). Qed.
Lemma lem1655078 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1655079 (a : real) (x : real) : (term306 a x) = (term60 a x).
Proof. exact (MK_COMB (@lem1655078) (@lem1655077 a x)). Qed.
Lemma lem1655080 : term8 = term8.
Proof. exact (eq_refl term8). Qed.
Lemma lem1655081 (a : real) (x : real) : (term305 a x) = (term62 a x).
Proof. exact (MK_COMB (@lem1655079 a x) (@lem1655080)). Qed.
Lemma lem1655082 (a : real) (x : real) (h1 : term229 a x) : term62 a x.
Proof. exact (EQ_MP (@lem1655081 a x) (@lem1655076 a x h1)). Qed.
Lemma lem1655084 (y : real) : term246 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1655085 (a : real) (x : real) : term278 a x.
Proof. exact (@lem1655084 (term57 a x)). Qed.
Lemma lem1655086 (a : real) (x : real) (h1 : term229 a x) : term279 a x.
Proof. exact (@lem1655085 a x (@lem1655059 a x h1)). Qed.
Lemma lem1655087 (a : real) (x : real) (h1 : term229 a x) : term307 a x.
Proof. exact (@lem1655086 a x h1 term22). Qed.
Lemma lem1655088 (a : real) (x : real) : (term307 a x) = ((term308 a x) = term8).
Proof. exact (eq_refl (term307 a x)). Qed.
Lemma lem1655089 (a : real) (x : real) (h1 : term229 a x) : (term308 a x) = term8.
Proof. exact (EQ_MP (@lem1655088 a x) (@lem1655087 a x h1)). Qed.
Lemma lem1655090 (a : real) (x : real) : (term308 a x) = (term309 a x).
Proof. exact (@lem1483508 (term11 a) term22 (term11 x)). Qed.
Lemma lem1655091 (x : real) : (term23 x) = (term24 x).
Proof. exact (@lem1483476 term22 term22 x). Qed.
Lemma lem1655093 (m : nat) (n : nat) : (term25 m n) = (term26 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1655094 : term27 = term28.
Proof. exact (@lem1655093 term29 term29). Qed.
Lemma lem1655095 : (term30 = (BIT1 0)) = (term31 = term29).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1655096 : term31 = term29.
Proof. exact (EQ_MP (@lem1655095) (@lem940073)). Qed.
Lemma lem1655097 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1655098 : term28 = term32.
Proof. exact (MK_COMB (@lem1655097) (@lem1655096)). Qed.
Lemma lem1655099 : term27 = term32.
Proof. exact (TRANS (@lem1655094) (@lem1655098)). Qed.
Lemma lem1655100 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1655101 : term33 = term34.
Proof. exact (MK_COMB (@lem1655100) (@lem1655099)). Qed.
Lemma lem1655102 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1655103 (x : real) : (term24 x) = (term35 x).
Proof. exact (MK_COMB (@lem1655101) (@lem1655102 x)). Qed.
Lemma lem1655104 (x : real) : (term23 x) = (term35 x).
Proof. exact (TRANS (@lem1655091 x) (@lem1655103 x)). Qed.
Lemma lem1655105 (x : real) : (term35 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1655106 (x : real) : (term23 x) = x.
Proof. exact (TRANS (@lem1655104 x) (@lem1655105 x)). Qed.
Lemma lem1655107 (a : real) : (term23 a) = (term24 a).
Proof. exact (@lem1483476 term22 term22 a). Qed.
Lemma lem1655109 (m : nat) (n : nat) : (term25 m n) = (term26 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1655110 : term27 = term28.
Proof. exact (@lem1655109 term29 term29). Qed.
Lemma lem1655111 : (term30 = (BIT1 0)) = (term31 = term29).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1655112 : term31 = term29.
Proof. exact (EQ_MP (@lem1655111) (@lem940073)). Qed.
Lemma lem1655113 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1655114 : term28 = term32.
Proof. exact (MK_COMB (@lem1655113) (@lem1655112)). Qed.
Lemma lem1655115 : term27 = term32.
Proof. exact (TRANS (@lem1655110) (@lem1655114)). Qed.
Lemma lem1655116 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1655117 : term33 = term34.
Proof. exact (MK_COMB (@lem1655116) (@lem1655115)). Qed.
Lemma lem1655118 (a : real) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1655119 (a : real) : (term24 a) = (term35 a).
Proof. exact (MK_COMB (@lem1655117) (@lem1655118 a)). Qed.
Lemma lem1655120 (a : real) : (term23 a) = (term35 a).
Proof. exact (TRANS (@lem1655107 a) (@lem1655119 a)). Qed.
Lemma lem1655121 (a : real) : (term35 a) = a.
Proof. exact (@lem1483436 a). Qed.
Lemma lem1655122 (a : real) : (term23 a) = a.
Proof. exact (TRANS (@lem1655120 a) (@lem1655121 a)). Qed.
Lemma lem1655123 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1655124 (a : real) : (term36 a) = (real_add a).
Proof. exact (MK_COMB (@lem1655123) (@lem1655122 a)). Qed.
Lemma lem1655125 (a : real) (x : real) : (term309 a x) = (real_add a x).
Proof. exact (MK_COMB (@lem1655124 a) (@lem1655106 x)). Qed.
Lemma lem1655126 (a : real) (x : real) : (term308 a x) = (real_add a x).
Proof. exact (TRANS (@lem1655090 a x) (@lem1655125 a x)). Qed.
Lemma lem1655127 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1655128 (a : real) (x : real) : (term310 a x) = (term311 a x).
Proof. exact (MK_COMB (@lem1655127) (@lem1655126 a x)). Qed.
Lemma lem1655129 : term8 = term8.
Proof. exact (eq_refl term8). Qed.
Lemma lem1655130 (a : real) (x : real) : ((term308 a x) = term8) = ((real_add a x) = term8).
Proof. exact (MK_COMB (@lem1655128 a x) (@lem1655129)). Qed.
Lemma lem1655131 (a : real) (x : real) (h1 : term229 a x) : (real_add a x) = term8.
Proof. exact (EQ_MP (@lem1655130 a x) (@lem1655089 a x h1)). Qed.
Lemma lem1655132 (a : real) (x : real) (h1 : term229 a x) : term312 a x.
Proof. exact (conj (@lem1655131 a x h1) (@lem1655082 a x h1)). Qed.
Lemma lem1655134 (x : real) (y : real) : term253 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1655135 (a : real) (x : real) : term313 a x.
Proof. exact (@lem1655134 (real_add a x) (term57 a x)). Qed.
Lemma lem1655136 (a : real) (x : real) (h1 : term229 a x) : term314 a x.
Proof. exact (@lem1655135 a x (@lem1655132 a x h1)). Qed.
Lemma lem1655137 (a : real) (x : real) : (term315 a x) = (term316 a x).
Proof. exact (@lem1483480 a (term11 a) x (term11 x)). Qed.
Lemma lem1655138 (a : real) : (term258 a) = (term259 a).
Proof. exact (@lem1483442 term22 a). Qed.
Lemma lem1655140 (m : nat) : (term260 m) = term8.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1655141 : term261 = term8.
Proof. exact (@lem1655140 term29). Qed.
Lemma lem1655142 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1655143 : term262 = term263.
Proof. exact (MK_COMB (@lem1655142) (@lem1655141)). Qed.
Lemma lem1655144 (a : real) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1655145 (a : real) : (term259 a) = (term264 a).
Proof. exact (MK_COMB (@lem1655143) (@lem1655144 a)). Qed.
Lemma lem1655146 (a : real) : (term258 a) = (term264 a).
Proof. exact (TRANS (@lem1655138 a) (@lem1655145 a)). Qed.
Lemma lem1655147 (a : real) : (term264 a) = term8.
Proof. exact (@lem1483446 a). Qed.
Lemma lem1655148 (a : real) : (term258 a) = term8.
Proof. exact (TRANS (@lem1655146 a) (@lem1655147 a)). Qed.
Lemma lem1655149 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1655150 (a : real) : (term265 a) = term266.
Proof. exact (MK_COMB (@lem1655149) (@lem1655148 a)). Qed.
Lemma lem1655151 (x : real) : (term258 x) = (term259 x).
Proof. exact (@lem1483442 term22 x). Qed.
Lemma lem1655153 (m : nat) : (term260 m) = term8.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1655154 : term261 = term8.
Proof. exact (@lem1655153 term29). Qed.
Lemma lem1655155 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1655156 : term262 = term263.
Proof. exact (MK_COMB (@lem1655155) (@lem1655154)). Qed.
Lemma lem1655157 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1655158 (x : real) : (term259 x) = (term264 x).
Proof. exact (MK_COMB (@lem1655156) (@lem1655157 x)). Qed.
Lemma lem1655159 (x : real) : (term258 x) = (term264 x).
Proof. exact (TRANS (@lem1655151 x) (@lem1655158 x)). Qed.
Lemma lem1655160 (x : real) : (term264 x) = term8.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1655161 (x : real) : (term258 x) = term8.
Proof. exact (TRANS (@lem1655159 x) (@lem1655160 x)). Qed.
Lemma lem1655162 (a : real) (x : real) : (term316 a x) = term268.
Proof. exact (MK_COMB (@lem1655150 a) (@lem1655161 x)). Qed.
Lemma lem1655163 (a : real) (x : real) : (term315 a x) = term268.
Proof. exact (TRANS (@lem1655137 a x) (@lem1655162 a x)). Qed.
Lemma lem1655164 : term268 = term8.
Proof. exact (@lem1483448 term8). Qed.
Lemma lem1655165 (a : real) (x : real) : (term315 a x) = term8.
Proof. exact (TRANS (@lem1655163 a x) (@lem1655164)). Qed.
Lemma lem1655166 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1655167 (a : real) (x : real) : (term317 a x) = term270.
Proof. exact (MK_COMB (@lem1655166) (@lem1655165 a x)). Qed.
Lemma lem1655168 : term8 = term8.
Proof. exact (eq_refl term8). Qed.
Lemma lem1655169 (a : real) (x : real) : (term314 a x) = term271.
Proof. exact (MK_COMB (@lem1655167 a x) (@lem1655168)). Qed.
Lemma lem1655170 (a : real) (x : real) (h1 : term229 a x) : term271.
Proof. exact (EQ_MP (@lem1655169 a x) (@lem1655136 a x h1)). Qed.
Lemma lem1655172 (n : nat) (m : nat) : (term236 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1655173 : term271 = term272.
Proof. exact (@lem1655172 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1655174 : term272 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1655175 : term271 = False.
Proof. exact (TRANS (@lem1655173) (@lem1655174)). Qed.
Lemma lem1655176 (a : real) (x : real) (h1 : term229 a x) : False.
Proof. exact (EQ_MP (@lem1655175) (@lem1655170 a x h1)). Qed.
Lemma lem1655177 (a : real) (x : real) (h1 : term230 a x) : False.
Proof. exact (or_elim (@lem1654968 a x h1) (fun h0 : term223 a x => @lem1655054 a x h0) (fun h0 : term229 a x => @lem1655176 a x h0)). Qed.
Lemma lem1655178 (a : real) (x : real) (h1 : term233 a x) : False.
Proof. exact (or_elim (@lem1654736 a x h1) (fun h0 : term211 a x => @lem1654967 a x h0) (fun h0 : term230 a x => @lem1655177 a x h0)). Qed.
Lemma lem1655179 (a : real) (x : real) (h1 : term235 a x) : False.
Proof. exact (or_elim (@lem1654364 a x h1) (fun h0 : term190 a x => @lem1654735 a x h0) (fun h0 : term233 a x => @lem1655178 a x h0)). Qed.
Lemma lem1655180 (a : real) (x : real) (h1 : term95 a x) : term95 a x.
Proof. exact (h1). Qed.
Lemma lem1655181 (a : real) (x : real) (h1 : term95 a x) : term235 a x.
Proof. exact (EQ_MP (@lem1654363 a x) (@lem1655180 a x h1)). Qed.
Lemma lem1655182 (a : real) (x : real) (h1 : term95 a x) : (term235 a x) = False.
Proof. exact (prop_ext (fun h2 : term235 a x => @lem1655179 a x h2) (fun h2 : False => @lem1655181 a x h1)). Qed.
Lemma lem1655183 (a : real) (x : real) (h1 : term95 a x) : False.
Proof. exact (EQ_MP (@lem1655182 a x h1) (@lem1655181 a x h1)). Qed.
Lemma lem1655184 (x : real) (a : real) (h1 : term5 x a) : term5 x a.
Proof. exact (h1). Qed.
Lemma lem1655185 (x : real) (a : real) (h1 : term5 x a) : term95 a x.
Proof. exact (EQ_MP (@lem1653910 a x) (@lem1655184 x a h1)). Qed.
Lemma lem1655186 (x : real) (a : real) (h1 : term5 x a) : (term95 a x) = False.
Proof. exact (prop_ext (fun h2 : term95 a x => @lem1655183 a x h2) (fun h2 : False => @lem1655185 x a h1)). Qed.
Lemma lem1655187 (x : real) (a : real) (h1 : term5 x a) : False.
Proof. exact (EQ_MP (@lem1655186 x a h1) (@lem1655185 x a h1)). Qed.
Lemma lem1655188 (x : real) (a : real) : term318 x a.
Proof. exact (fun h0 : term5 x a => @lem1655187 x a h0). Qed.
Lemma lem1655189 (x : real) (a : real) : term319 x a.
Proof. exact (@lem1386578 (term320 x a)). Qed.
Lemma lem1655191 (t1 : Prop) : term321 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem1655192 (t1 : Prop) : (term321 t1) = (term322 t1).
Proof. exact (eq_refl (term321 t1)). Qed.
Lemma lem1655193 (t1 : Prop) : term322 t1.
Proof. exact (EQ_MP (@lem1655192 t1) (@lem1655191 t1)). Qed.
Lemma lem1655194 (t1 : Prop) (t2 : Prop) : term323 t1 t2.
Proof. exact (@lem1655193 t1 t2). Qed.
Lemma lem1655195 (t1 : Prop) (t2 : Prop) : (term323 t1 t2) = (term324 t1 t2).
Proof. exact (eq_refl (term323 t1 t2)). Qed.
Lemma lem1655196 (t1 : Prop) (t2 : Prop) : term324 t1 t2.
Proof. exact (EQ_MP (@lem1655195 t1 t2) (@lem1655194 t1 t2)). Qed.
Lemma lem1655197 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term325 t1 t2 t3.
Proof. exact (@lem1655196 t1 t2 t3). Qed.
Lemma lem1655198 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term325 t1 t2 t3) = ((term326 t1 t2 t3) = (term327 t1 t2 t3)).
Proof. exact (eq_refl (term325 t1 t2 t3)). Qed.
Lemma lem1655199 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term326 t1 t2 t3) = (term327 t1 t2 t3).
Proof. exact (EQ_MP (@lem1655198 t1 t2 t3) (@lem1655197 t1 t2 t3)). Qed.
Lemma lem1655200 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term327 t1 t2 t3) = (term326 t1 t2 t3).
Proof. exact (SYM (@lem1655199 t1 t2 t3)). Qed.
Lemma lem1655201 (x : real) : term328 x.
Proof. exact (@lem9784 ((real_abs x) = term32)). Qed.
Lemma lem1655202 (x : real) : (term328 x) = (term329 x).
Proof. exact (eq_refl (term328 x)). Qed.
Lemma lem1655203 (x : real) : term329 x.
Proof. exact (EQ_MP (@lem1655202 x) (@lem1655201 x)). Qed.
Lemma lem1655204 (x : real) (h1 : (real_abs x) = term32) : (real_abs x) = term32.
Proof. exact (h1). Qed.
Lemma lem1655205 (x : real) (h1 : term330 x) : term330 x.
Proof. exact (h1). Qed.
Lemma lem1655206 (n : nat) : term331 n.
Proof. exact (@lem9784 (n = (NUMERAL 0))). Qed.
Lemma lem1655207 (n : nat) : (term331 n) = (term332 n).
Proof. exact (eq_refl (term331 n)). Qed.
Lemma lem1655208 (n : nat) : term332 n.
Proof. exact (EQ_MP (@lem1655207 n) (@lem1655206 n)). Qed.
Lemma lem1655210 (n : nat) (h1 : term333 n) : term333 n.
Proof. exact (h1). Qed.
Lemma lem1655221 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1655222 (x : real) : (real_pow x) = (real_pow x).
Proof. exact (eq_refl (real_pow x)). Qed.
Lemma lem1655223 (x : real) (n : nat) (h1 : n = (NUMERAL 0)) : (real_pow x n) = (term334 x).
Proof. exact (MK_COMB (@lem1655222 x) (@lem1655221 n h1)). Qed.
Lemma lem1655225 (x : real) : (term334 x) = term32.
Proof. exact (EQ_MP (@lem1344311 x) (@lem1344310 x)). Qed.
Lemma lem1655226 (x : real) (n : nat) (h1 : n = (NUMERAL 0)) : (real_pow x n) = term32.
Proof. exact (TRANS (@lem1655223 x n h1) (@lem1655225 x)). Qed.
Lemma lem1655227 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1655228 (x : real) (n : nat) (h1 : n = (NUMERAL 0)) : (term335 x n) = term336.
Proof. exact (MK_COMB (@lem1655227) (@lem1655226 x n h1)). Qed.
Lemma lem1655229 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1655230 (x : real) (n : nat) (h1 : n = (NUMERAL 0)) : ((real_pow x n) = term32) = (term32 = term32).
Proof. exact (MK_COMB (@lem1655228 x n h1) (@lem1655229)). Qed.
Lemma lem1655232 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1655233 (x : real) : (x = x) = True.
Proof. exact (@lem1655232 real x). Qed.
Lemma lem1655234 : (term32 = term32) = True.
Proof. exact (@lem1655233 term32). Qed.
Lemma lem1655235 (x : real) (n : nat) (h1 : n = (NUMERAL 0)) : ((real_pow x n) = term32) = True.
Proof. exact (TRANS (@lem1655230 x n h1) (@lem1655234)). Qed.
Lemma lem1655236 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1655237 (x : real) (n : nat) (h1 : n = (NUMERAL 0)) : (term337 x n) = (@eq Prop True).
Proof. exact (MK_COMB (@lem1655236) (@lem1655235 x n h1)). Qed.
Lemma lem1655247 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1655248 : Coq.Arith.PeanoNat.Nat.Even = Coq.Arith.PeanoNat.Nat.Even.
Proof. exact (eq_refl Coq.Arith.PeanoNat.Nat.Even). Qed.
Lemma lem1655249 (n : nat) (h1 : n = (NUMERAL 0)) : (Coq.Arith.PeanoNat.Nat.Even n) = term338.
Proof. exact (MK_COMB (@lem1655248) (@lem1655247 n h1)). Qed.
Lemma lem1655250 (x : real) : (term339 x) = (term339 x).
Proof. exact (eq_refl (term339 x)). Qed.
Lemma lem1655251 (x : real) (n : nat) (h1 : n = (NUMERAL 0)) : (term340 x n) = (term341 x).
Proof. exact (MK_COMB (@lem1655250 x) (@lem1655249 n h1)). Qed.
Lemma lem1655254 (x : real) : (term342 x) = (term342 x).
Proof. exact (eq_refl (term342 x)). Qed.
Lemma lem1655255 (x : real) (n : nat) (h1 : n = (NUMERAL 0)) : (term343 x n) = (term344 x).
Proof. exact (MK_COMB (@lem1655254 x) (@lem1655251 x n h1)). Qed.
Lemma lem1655258 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1655259 (x : real) (n : nat) (h1 : n = (NUMERAL 0)) : (term345 x n) = (term346 x).
Proof. exact (MK_COMB (@lem1655258) (@lem1655255 x n h1)). Qed.
Lemma lem1655263 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1655264 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1655265 (n : nat) (h1 : n = (NUMERAL 0)) : (@eq nat n) = term347.
Proof. exact (MK_COMB (@lem1655264) (@lem1655263 n h1)). Qed.
Lemma lem1655266 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem1655267 (n : nat) (h1 : n = (NUMERAL 0)) : (n = (NUMERAL 0)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem1655265 n h1) (@lem1655266)). Qed.
Lemma lem1655269 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1655270 (x : nat) : (x = x) = True.
Proof. exact (@lem1655269 nat x). Qed.
Lemma lem1655271 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1655270 (NUMERAL 0)). Qed.
Lemma lem1655272 (n : nat) (h1 : n = (NUMERAL 0)) : (n = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem1655267 n h1) (@lem1655271)). Qed.
Lemma lem1655273 (x : real) (n : nat) (h1 : n = (NUMERAL 0)) : (term348 x n) = (term349 x).
Proof. exact (MK_COMB (@lem1655259 x n h1) (@lem1655272 n h1)). Qed.
Lemma lem1655275 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem1655276 (x : real) : (term349 x) = True.
Proof. exact (@lem1655275 (term344 x)). Qed.
Lemma lem1655277 (x : real) (n : nat) (h1 : n = (NUMERAL 0)) : (term348 x n) = True.
Proof. exact (TRANS (@lem1655273 x n h1) (@lem1655276 x)). Qed.
Lemma lem1655278 (x : real) (n : nat) (h1 : n = (NUMERAL 0)) : (((real_pow x n) = term32) = (term348 x n)) = (True = True).
Proof. exact (MK_COMB (@lem1655237 x n h1) (@lem1655277 x n h1)). Qed.
Lemma lem1655280 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem1655281 : (True = True) = True.
Proof. exact (@lem1655280 True). Qed.
Lemma lem1655282 (x : real) (n : nat) (h1 : n = (NUMERAL 0)) : (((real_pow x n) = term32) = (term348 x n)) = True.
Proof. exact (TRANS (@lem1655278 x n h1) (@lem1655281)). Qed.
Lemma lem1655283 (x : real) (n : nat) (h1 : n = (NUMERAL 0)) : True = (((real_pow x n) = term32) = (term348 x n)).
Proof. exact (SYM (@lem1655282 x n h1)). Qed.
Lemma lem1655284 (x : real) (n : nat) (h1 : n = (NUMERAL 0)) : ((real_pow x n) = term32) = (term348 x n).
Proof. exact (EQ_MP (@lem1655283 x n h1) (@lem0)). Qed.
Lemma lem1655290 (n : nat) : term350 n.
Proof. exact (@lem82 (n = (NUMERAL 0))). Qed.
Lemma lem1655316 (n : nat) (h1 : term333 n) : (n = (NUMERAL 0)) = False.
Proof. exact (@lem1655290 n (@lem1655210 n h1)). Qed.
Lemma lem1655317 (x : real) (n : nat) : (term345 x n) = (term345 x n).
Proof. exact (eq_refl (term345 x n)). Qed.
Lemma lem1655318 (x : real) (n : nat) (h1 : term333 n) : (term348 x n) = (term351 x n).
Proof. exact (MK_COMB (@lem1655317 x n) (@lem1655316 n h1)). Qed.
Lemma lem1655320 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem1655321 (x : real) (n : nat) : (term351 x n) = (term343 x n).
Proof. exact (@lem1655320 (term343 x n)). Qed.
Lemma lem1655328 (x : real) (n : nat) (h1 : term333 n) : (term348 x n) = (term343 x n).
Proof. exact (TRANS (@lem1655318 x n h1) (@lem1655321 x n)). Qed.
Lemma lem1655329 (x : real) (n : nat) : (term337 x n) = (term337 x n).
Proof. exact (eq_refl (term337 x n)). Qed.
Lemma lem1655330 (x : real) (n : nat) (h1 : term333 n) : (((real_pow x n) = term32) = (term348 x n)) = (((real_pow x n) = term32) = (term343 x n)).
Proof. exact (MK_COMB (@lem1655329 x n) (@lem1655328 x n h1)). Qed.
Lemma lem1655333 (x : real) (n : nat) (h1 : term333 n) : (((real_pow x n) = term32) = (term343 x n)) = (((real_pow x n) = term32) = (term348 x n)).
Proof. exact (SYM (@lem1655330 x n h1)). Qed.
Lemma lem1655335 (p : Prop) : p = (term352 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1655336 (x : real) (n : nat) : (((real_pow x n) = term32) = (term343 x n)) = (term353 x n).
Proof. exact (@lem1655335 (((real_pow x n) = term32) = (term343 x n))). Qed.
Lemma lem1655337 (x : real) (n : nat) : (term353 x n) = (((real_pow x n) = term32) = (term343 x n)).
Proof. exact (SYM (@lem1655336 x n)). Qed.
Lemma lem1655338 (x : real) (n : nat) (h1 : term354 x n) : term354 x n.
Proof. exact (h1). Qed.
Lemma lem1655341 (x : real) (n : nat) (h1 : term355 x n) : term355 x n.
Proof. exact (h1). Qed.
Lemma lem1655342 (x : real) (n : nat) : term356 x n.
Proof. exact (fun h0 : term355 x n => @lem1655341 x n h0). Qed.
Lemma lem1655343 (x : real) (n : nat) (h1 : term356 x n) : term356 x n.
Proof. exact (h1). Qed.
Lemma lem1655344 (x : real) (n : nat) (h1 : term355 x n) : term355 x n.
Proof. exact (h1). Qed.
Lemma lem1655345 (x : real) (n : nat) (h1 : term355 x n) (h2 : term356 x n) : term355 x n.
Proof. exact (@lem1655343 x n h2 (@lem1655344 x n h1)). Qed.
Lemma lem1655346 (x : real) (n : nat) (h1 : term355 x n) : term357 x n.
Proof. exact (fun h0 : term356 x n => @lem1655345 x n h1 h0). Qed.
Lemma lem1655347 (x : real) (n : nat) (h1 : term356 x n) : term356 x n.
Proof. exact (h1). Qed.
Lemma lem1655348 (x : real) (n : nat) (h1 : term355 x n) (h2 : term356 x n) : term355 x n.
Proof. exact (@lem1655346 x n h1 (@lem1655347 x n h2)). Qed.
Lemma lem1655349 (x : real) (n : nat) (h1 : term356 x n) : term356 x n.
Proof. exact (fun h0 : term355 x n => @lem1655348 x n h0 h1). Qed.
Lemma lem1655350 (x : real) (n : nat) : term358 x n.
Proof. exact (fun h0 : term356 x n => @lem1655349 x n h0). Qed.
Lemma lem1655353 (x : real) (n : nat) : term356 x n.
Proof. exact (@lem1655350 x n (@lem1655342 x n)). Qed.
Lemma lem1655373 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1655374 : term359 = term360.
Proof. exact (@lem1655373 term361). Qed.
Lemma lem1655387 (x : real) (n : nat) : (term362 x n) = (term362 x n).
Proof. exact (eq_refl (term362 x n)). Qed.
Lemma lem1655388 (x : real) (n : nat) : (term363 x n) = (term364 x n).
Proof. exact (MK_COMB (@lem1655387 x n) (@lem1655374)). Qed.
Lemma lem1655391 (x : real) : (term365 x) = (term365 x).
Proof. exact (eq_refl (term365 x)). Qed.
Lemma lem1655392 (x : real) (n : nat) : (term366 x n) = (term367 x n).
Proof. exact (MK_COMB (@lem1655391 x) (@lem1655388 x n)). Qed.
Lemma lem1655395 (n : nat) : (term368 n) = (term368 n).
Proof. exact (eq_refl (term368 n)). Qed.
Lemma lem1655396 (x : real) (n : nat) : (term355 x n) = (term369 x n).
Proof. exact (MK_COMB (@lem1655395 n) (@lem1655392 x n)). Qed.
Lemma lem1655399 (n : nat) : (term370 n) = (term371 n).
Proof. exact (fun_ext (fun x : real => @lem1655396 x n)). Qed.
Lemma lem1655400 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1655401 (n : nat) : (term372 n) = (term373 n).
Proof. exact (MK_COMB (@lem1655400) (@lem1655399 n)). Qed.
Lemma lem1655406 : term374 = term375.
Proof. exact (fun_ext (fun n : nat => @lem1655401 n)). Qed.
Lemma lem1655407 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1655416 : term376 = term377.
Proof. exact (MK_COMB (@lem1655407) (@lem1655406)). Qed.
Lemma lem1655427 (n : nat) (x : real) : (term378 n x) = (term378 n x).
Proof. exact (eq_refl (term378 n x)). Qed.
Lemma lem1655428 (x : real) : (term379 x) = (term379 x).
Proof. exact (fun_ext (fun n : nat => @lem1655427 n x)). Qed.
Lemma lem1655429 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1655430 (x : real) : (term380 x) = (term380 x).
Proof. exact (MK_COMB (@lem1655429) (@lem1655428 x)). Qed.
Lemma lem1655431 : term381 = term381.
Proof. exact (fun_ext (fun x : real => @lem1655430 x)). Qed.
Lemma lem1655432 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1655433 : term361 = term361.
Proof. exact (MK_COMB (@lem1655432) (@lem1655431)). Qed.
Lemma lem1655434 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1655435 : term360 = term360.
Proof. exact (MK_COMB (@lem1655434) (@lem1655433)). Qed.
Lemma lem1655452 (x : real) (n : nat) : (term362 x n) = (term362 x n).
Proof. exact (eq_refl (term362 x n)). Qed.
Lemma lem1655453 (x : real) (n : nat) : (term364 x n) = (term364 x n).
Proof. exact (MK_COMB (@lem1655452 x n) (@lem1655435)). Qed.
Lemma lem1655458 (x : real) : (term365 x) = (term365 x).
Proof. exact (eq_refl (term365 x)). Qed.
Lemma lem1655459 (x : real) (n : nat) : (term367 x n) = (term367 x n).
Proof. exact (MK_COMB (@lem1655458 x) (@lem1655453 x n)). Qed.
Lemma lem1655464 (n : nat) : (term368 n) = (term368 n).
Proof. exact (eq_refl (term368 n)). Qed.
Lemma lem1655465 (x : real) (n : nat) : (term369 x n) = (term369 x n).
Proof. exact (MK_COMB (@lem1655464 n) (@lem1655459 x n)). Qed.
Lemma lem1655466 (n : nat) : (term371 n) = (term371 n).
Proof. exact (fun_ext (fun x : real => @lem1655465 x n)). Qed.
Lemma lem1655467 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1655468 (n : nat) : (term373 n) = (term373 n).
Proof. exact (MK_COMB (@lem1655467) (@lem1655466 n)). Qed.
Lemma lem1655469 : term375 = term375.
Proof. exact (fun_ext (fun n : nat => @lem1655468 n)). Qed.
Lemma lem1655470 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1655471 : term377 = term377.
Proof. exact (MK_COMB (@lem1655470) (@lem1655469)). Qed.
Lemma lem1655512 : term376 = term377.
Proof. exact (TRANS (@lem1655416) (@lem1655471)). Qed.
Lemma lem1655513 : term377 = term376.
Proof. exact (SYM (@lem1655512)). Qed.
Lemma lem1655516 (x : real) (n : nat) (h1 : term354 x n) : term354 x n.
Proof. exact (h1). Qed.
Lemma lem1655517 (h1 : term361) : term361.
Proof. exact (h1). Qed.
Lemma lem1655523 (n : nat) (h1 : term333 n) : term333 n.
Proof. exact (h1). Qed.
Lemma lem1655529 (x : real) (h1 : term330 x) : term330 x.
Proof. exact (h1). Qed.
Lemma lem1655542 (x : real) (n : nat) : (term382 x n) = (term383 x n).
Proof. exact (@lem17362 (term384 x) (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem1655547 (x : real) (n : nat) : (term340 x n) = (term385 x n).
Proof. exact (@lem17265 (term384 x) (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem1655549 (x : real) : (term386 x) = (term386 x).
Proof. exact (eq_refl (term386 x)). Qed.
Lemma lem1655550 (x : real) (n : nat) : (term387 x n) = (term388 x n).
Proof. exact (MK_COMB (@lem1655549 x) (@lem1655542 x n)). Qed.
Lemma lem1655551 (x : real) (n : nat) : (term389 x n) = (term387 x n).
Proof. exact (@lem17045 ((real_abs x) = term32) (term340 x n)). Qed.
Lemma lem1655552 (x : real) (n : nat) : (term389 x n) = (term388 x n).
Proof. exact (TRANS (@lem1655551 x n) (@lem1655550 x n)). Qed.
Lemma lem1655554 (x : real) : (term342 x) = (term342 x).
Proof. exact (eq_refl (term342 x)). Qed.
Lemma lem1655555 (x : real) (n : nat) : (term343 x n) = (term390 x n).
Proof. exact (MK_COMB (@lem1655554 x) (@lem1655547 x n)). Qed.
Lemma lem1655557 (x : real) (n : nat) : (term391 x n) = (term391 x n).
Proof. exact (eq_refl (term391 x n)). Qed.
Lemma lem1655558 (x : real) (n : nat) : (term392 x n) = (term393 x n).
Proof. exact (MK_COMB (@lem1655557 x n) (@lem1655555 x n)). Qed.
Lemma lem1655560 (x : real) (n : nat) : (term394 x n) = (term394 x n).
Proof. exact (eq_refl (term394 x n)). Qed.
Lemma lem1655561 (x : real) (n : nat) : (term395 x n) = (term396 x n).
Proof. exact (MK_COMB (@lem1655560 x n) (@lem1655552 x n)). Qed.
Lemma lem1655562 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1655563 (x : real) (n : nat) : (term397 x n) = (term398 x n).
Proof. exact (MK_COMB (@lem1655562) (@lem1655561 x n)). Qed.
Lemma lem1655564 (x : real) (n : nat) : (term399 x n) = (term400 x n).
Proof. exact (MK_COMB (@lem1655563 x n) (@lem1655558 x n)). Qed.
Lemma lem1655565 (x : real) (n : nat) : (term354 x n) = (term399 x n).
Proof. exact (@lem17646 ((real_pow x n) = term32) (term343 x n)). Qed.
Lemma lem1655570 (x : real) (n : nat) : (term354 x n) = (term400 x n).
Proof. exact (TRANS (@lem1655565 x n) (@lem1655564 x n)). Qed.
Lemma lem1655574 (n : nat) : (term401 n) = (n = (NUMERAL 0)).
Proof. exact (@lem16933 (n = (NUMERAL 0))). Qed.
Lemma lem1655575 (x : real) (n : nat) : (term402 x n) = (term402 x n).
Proof. exact (eq_refl (term402 x n)). Qed.
Lemma lem1655576 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1655577 (n : nat) : (term403 n) = (term404 n).
Proof. exact (MK_COMB (@lem1655576) (@lem1655574 n)). Qed.
Lemma lem1655578 (x : real) (n : nat) : (term405 x n) = (term406 x n).
Proof. exact (MK_COMB (@lem1655577 n) (@lem1655575 x n)). Qed.
Lemma lem1655579 (x : real) (n : nat) : (term407 x n) = (term405 x n).
Proof. exact (@lem17045 (term333 n) ((real_pow x n) = term32)). Qed.
Lemma lem1655580 (x : real) (n : nat) : (term407 x n) = (term406 x n).
Proof. exact (TRANS (@lem1655579 x n) (@lem1655578 x n)). Qed.
Lemma lem1655581 (x : real) : ((real_abs x) = term32) = ((real_abs x) = term32).
Proof. exact (eq_refl ((real_abs x) = term32)). Qed.
Lemma lem1655582 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1655583 (x : real) (n : nat) : (term408 x n) = (term409 x n).
Proof. exact (MK_COMB (@lem1655582) (@lem1655580 x n)). Qed.
Lemma lem1655584 (n : nat) (x : real) : (term410 n x) = (term411 n x).
Proof. exact (MK_COMB (@lem1655583 x n) (@lem1655581 x)). Qed.
Lemma lem1655585 (n : nat) (x : real) : (term378 n x) = (term410 n x).
Proof. exact (@lem17265 (term412 x n) ((real_abs x) = term32)). Qed.
Lemma lem1655586 (n : nat) (x : real) : (term378 n x) = (term411 n x).
Proof. exact (TRANS (@lem1655585 n x) (@lem1655584 n x)). Qed.
Lemma lem1655587 (x : real) : (term379 x) = (term413 x).
Proof. exact (fun_ext (fun n : nat => @lem1655586 n x)). Qed.
Lemma lem1655588 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1655589 (x : real) : (term380 x) = (term414 x).
Proof. exact (MK_COMB (@lem1655588) (@lem1655587 x)). Qed.
Lemma lem1655590 : term381 = term415.
Proof. exact (fun_ext (fun x : real => @lem1655589 x)). Qed.
Lemma lem1655591 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1655592 : term361 = term416.
Proof. exact (MK_COMB (@lem1655591) (@lem1655590)). Qed.
Lemma lem1655618 {A : Type'} (P : A -> Prop) (Q : Prop) : (term417 A P Q) = (term418 A P Q).
Proof. exact (EQ_MP (@lem18947 A P Q) (@lem18946 A P Q)). Qed.
Lemma lem1655619 (P : nat -> Prop) (Q : Prop) : (term419 P Q) = (term420 P Q).
Proof. exact (@lem1655618 nat P Q). Qed.
Lemma lem1655620 (x : real) : (term421 x) = (term422 x).
Proof. exact (@lem1655619 (term423 x) ((real_abs x) = term32)). Qed.
Lemma lem1655621 (x : real) (n : nat) : (term424 x n) = (term406 x n).
Proof. exact (eq_refl (term424 x n)). Qed.
Lemma lem1655622 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1655623 (x : real) (n : nat) : (term425 x n) = (term409 x n).
Proof. exact (MK_COMB (@lem1655622) (@lem1655621 x n)). Qed.
Lemma lem1655624 (x : real) : ((real_abs x) = term32) = ((real_abs x) = term32).
Proof. exact (eq_refl ((real_abs x) = term32)). Qed.
Lemma lem1655625 (n : nat) (x : real) : (term426 n x) = (term411 n x).
Proof. exact (MK_COMB (@lem1655623 x n) (@lem1655624 x)). Qed.
Lemma lem1655626 (x : real) : (term427 x) = (term413 x).
Proof. exact (fun_ext (fun n : nat => @lem1655625 n x)). Qed.
Lemma lem1655627 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1655628 (x : real) : (term421 x) = (term414 x).
Proof. exact (MK_COMB (@lem1655627) (@lem1655626 x)). Qed.
Lemma lem1655629 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1655630 (x : real) : (term428 x) = (term429 x).
Proof. exact (MK_COMB (@lem1655629) (@lem1655628 x)). Qed.
Lemma lem1655631 (x : real) (n : nat) : (term424 x n) = (term406 x n).
Proof. exact (eq_refl (term424 x n)). Qed.
Lemma lem1655632 (x : real) : (term430 x) = (term423 x).
Proof. exact (fun_ext (fun n : nat => @lem1655631 x n)). Qed.
Lemma lem1655633 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1655634 (x : real) : (term431 x) = (term432 x).
Proof. exact (MK_COMB (@lem1655633) (@lem1655632 x)). Qed.
Lemma lem1655635 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1655636 (x : real) : (term433 x) = (term434 x).
Proof. exact (MK_COMB (@lem1655635) (@lem1655634 x)). Qed.
Lemma lem1655637 (x : real) : ((real_abs x) = term32) = ((real_abs x) = term32).
Proof. exact (eq_refl ((real_abs x) = term32)). Qed.
Lemma lem1655638 (x : real) : (term422 x) = (term435 x).
Proof. exact (MK_COMB (@lem1655636 x) (@lem1655637 x)). Qed.
Lemma lem1655639 (x : real) : ((term421 x) = (term422 x)) = ((term414 x) = (term435 x)).
Proof. exact (MK_COMB (@lem1655630 x) (@lem1655638 x)). Qed.
Lemma lem1655640 (x : real) : (term414 x) = (term435 x).
Proof. exact (EQ_MP (@lem1655639 x) (@lem1655620 x)). Qed.
Lemma lem1655689 : term415 = term436.
Proof. exact (fun_ext (fun x : real => @lem1655640 x)). Qed.
Lemma lem1655690 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1655741 : term416 = term437.
Proof. exact (MK_COMB (@lem1655690) (@lem1655689)). Qed.
Lemma lem1655742 : term361 = term437.
Proof. exact (TRANS (@lem1655592) (@lem1655741)). Qed.
Lemma lem1655743 (h1 : term361) : term437.
Proof. exact (EQ_MP (@lem1655742) (@lem1655517 h1)). Qed.
Lemma lem1655753 (n : nat) (h1 : term333 n) : term333 n.
Proof. exact (h1). Qed.
Lemma lem1655769 (x : real) (h1 : term330 x) : term330 x.
Proof. exact (h1). Qed.
Lemma lem1655879 (x : real) (n : nat) (h1 : term354 x n) : term400 x n.
Proof. exact (EQ_MP (@lem1655570 x n) (@lem1655516 x n h1)). Qed.
Lemma lem1655892 (x : real) : ((real_abs x) = term32) = ((real_abs x) = term32).
Proof. exact (eq_refl ((real_abs x) = term32)). Qed.
Lemma lem1655919 (x : real) (n : nat) : (term406 x n) = (term406 x n).
Proof. exact (eq_refl (term406 x n)). Qed.
Lemma lem1655920 (x : real) : (term423 x) = (term423 x).
Proof. exact (fun_ext (fun n : nat => @lem1655919 x n)). Qed.
Lemma lem1655921 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1655922 (x : real) : (term432 x) = (term432 x).
Proof. exact (MK_COMB (@lem1655921) (@lem1655920 x)). Qed.
Lemma lem1655923 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1655924 (x : real) : (term434 x) = (term434 x).
Proof. exact (MK_COMB (@lem1655923) (@lem1655922 x)). Qed.
Lemma lem1655925 (x : real) : (term435 x) = (term435 x).
Proof. exact (MK_COMB (@lem1655924 x) (@lem1655892 x)). Qed.
Lemma lem1655926 : term436 = term436.
Proof. exact (fun_ext (fun x : real => @lem1655925 x)). Qed.
Lemma lem1655927 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1655928 : term437 = term437.
Proof. exact (MK_COMB (@lem1655927) (@lem1655926)). Qed.
Lemma lem1655929 (h1 : term361) : term437.
Proof. exact (EQ_MP (@lem1655928) (@lem1655743 h1)). Qed.
Lemma lem1655930 (x : real) (n : nat) (h1 : term396 x n) : term396 x n.
Proof. exact (h1). Qed.
Lemma lem1655931 (x : real) (n : nat) (h1 : term393 x n) : term393 x n.
Proof. exact (h1). Qed.
Lemma lem1655932 (x : real) (n : nat) (h1 : term396 x n) : term388 x n.
Proof. exact (proj2 (@lem1655930 x n h1)). Qed.
Lemma lem1655938 (x : real) (n : nat) (h1 : term393 x n) : term390 x n.
Proof. exact (proj2 (@lem1655931 x n h1)). Qed.
Lemma lem1655940 (x : real) (n : nat) (h1 : term393 x n) : term385 x n.
Proof. exact (proj2 (@lem1655938 x n h1)). Qed.
Lemma lem1655947 (n : nat) (h1 : term333 n) : term333 n.
Proof. exact (h1). Qed.
Lemma lem1655951 (x : real) (h1 : term330 x) : term330 x.
Proof. exact (h1). Qed.
Lemma lem1655953 {A : Type'} (P : A -> Prop) (Q : Prop) : (term418 A P Q) = (term417 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem1655954 (P : nat -> Prop) (Q : Prop) : (term420 P Q) = (term419 P Q).
Proof. exact (@lem1655953 nat P Q). Qed.
Lemma lem1655955 (x : real) : (term422 x) = (term421 x).
Proof. exact (@lem1655954 (term423 x) ((real_abs x) = term32)). Qed.
Lemma lem1655956 (x : real) (n : nat) : (term424 x n) = (term406 x n).
Proof. exact (eq_refl (term424 x n)). Qed.
Lemma lem1655957 (x : real) : (term430 x) = (term423 x).
Proof. exact (fun_ext (fun n : nat => @lem1655956 x n)). Qed.
Lemma lem1655958 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1655959 (x : real) : (term431 x) = (term432 x).
Proof. exact (MK_COMB (@lem1655958) (@lem1655957 x)). Qed.
Lemma lem1655960 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1655961 (x : real) : (term433 x) = (term434 x).
Proof. exact (MK_COMB (@lem1655960) (@lem1655959 x)). Qed.
Lemma lem1655962 (x : real) : ((real_abs x) = term32) = ((real_abs x) = term32).
Proof. exact (eq_refl ((real_abs x) = term32)). Qed.
Lemma lem1655963 (x : real) : (term422 x) = (term435 x).
Proof. exact (MK_COMB (@lem1655961 x) (@lem1655962 x)). Qed.
Lemma lem1655964 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1655965 (x : real) : (term438 x) = (term439 x).
Proof. exact (MK_COMB (@lem1655964) (@lem1655963 x)). Qed.
Lemma lem1655966 (x : real) (n : nat) : (term424 x n) = (term406 x n).
Proof. exact (eq_refl (term424 x n)). Qed.
Lemma lem1655967 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1655968 (x : real) (n : nat) : (term425 x n) = (term409 x n).
Proof. exact (MK_COMB (@lem1655967) (@lem1655966 x n)). Qed.
Lemma lem1655969 (x : real) : ((real_abs x) = term32) = ((real_abs x) = term32).
Proof. exact (eq_refl ((real_abs x) = term32)). Qed.
Lemma lem1655970 (n : nat) (x : real) : (term426 n x) = (term411 n x).
Proof. exact (MK_COMB (@lem1655968 x n) (@lem1655969 x)). Qed.
Lemma lem1655971 (x : real) : (term427 x) = (term413 x).
Proof. exact (fun_ext (fun n : nat => @lem1655970 n x)). Qed.
Lemma lem1655972 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1655973 (x : real) : (term421 x) = (term414 x).
Proof. exact (MK_COMB (@lem1655972) (@lem1655971 x)). Qed.
Lemma lem1655974 (x : real) : ((term422 x) = (term421 x)) = ((term435 x) = (term414 x)).
Proof. exact (MK_COMB (@lem1655965 x) (@lem1655973 x)). Qed.
Lemma lem1655975 (x : real) : (term435 x) = (term414 x).
Proof. exact (EQ_MP (@lem1655974 x) (@lem1655955 x)). Qed.
Lemma lem1655976 : term436 = term415.
Proof. exact (fun_ext (fun x : real => @lem1655975 x)). Qed.
Lemma lem1655977 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1655978 : term437 = term416.
Proof. exact (MK_COMB (@lem1655977) (@lem1655976)). Qed.
Lemma lem1655991 (n : nat) (x : real) : (term411 n x) = (term411 n x).
Proof. exact (eq_refl (term411 n x)). Qed.
Lemma lem1655992 (x : real) : (term413 x) = (term413 x).
Proof. exact (fun_ext (fun n : nat => @lem1655991 n x)). Qed.
Lemma lem1655993 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1655994 (x : real) : (term414 x) = (term414 x).
Proof. exact (MK_COMB (@lem1655993) (@lem1655992 x)). Qed.
Lemma lem1655995 : term415 = term415.
Proof. exact (fun_ext (fun x : real => @lem1655994 x)). Qed.
Lemma lem1655996 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1655997 : term416 = term416.
Proof. exact (MK_COMB (@lem1655996) (@lem1655995)). Qed.
Lemma lem1655998 : term437 = term416.
Proof. exact (TRANS (@lem1655978) (@lem1655997)). Qed.
Lemma lem1655999 (h1 : term361) : term416.
Proof. exact (EQ_MP (@lem1655998) (@lem1655929 h1)). Qed.
Lemma lem1656007 (x : real) (h1 : term330 x) : term330 x.
Proof. exact (h1). Qed.
Lemma lem1656011 (n : nat) (h1 : term333 n) : term333 n.
Proof. exact (h1). Qed.
Lemma lem1656015 (x : real) (h1 : term330 x) : term330 x.
Proof. exact (h1). Qed.
Lemma lem1656017 {A : Type'} (P : A -> Prop) (Q : Prop) : (term418 A P Q) = (term417 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem1656018 (P : nat -> Prop) (Q : Prop) : (term420 P Q) = (term419 P Q).
Proof. exact (@lem1656017 nat P Q). Qed.
Lemma lem1656019 (x : real) : (term422 x) = (term421 x).
Proof. exact (@lem1656018 (term423 x) ((real_abs x) = term32)). Qed.
Lemma lem1656020 (x : real) (n : nat) : (term424 x n) = (term406 x n).
Proof. exact (eq_refl (term424 x n)). Qed.
Lemma lem1656021 (x : real) : (term430 x) = (term423 x).
Proof. exact (fun_ext (fun n : nat => @lem1656020 x n)). Qed.
Lemma lem1656022 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1656023 (x : real) : (term431 x) = (term432 x).
Proof. exact (MK_COMB (@lem1656022) (@lem1656021 x)). Qed.
Lemma lem1656024 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1656025 (x : real) : (term433 x) = (term434 x).
Proof. exact (MK_COMB (@lem1656024) (@lem1656023 x)). Qed.
Lemma lem1656026 (x : real) : ((real_abs x) = term32) = ((real_abs x) = term32).
Proof. exact (eq_refl ((real_abs x) = term32)). Qed.
Lemma lem1656027 (x : real) : (term422 x) = (term435 x).
Proof. exact (MK_COMB (@lem1656025 x) (@lem1656026 x)). Qed.
Lemma lem1656028 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1656029 (x : real) : (term438 x) = (term439 x).
Proof. exact (MK_COMB (@lem1656028) (@lem1656027 x)). Qed.
Lemma lem1656030 (x : real) (n : nat) : (term424 x n) = (term406 x n).
Proof. exact (eq_refl (term424 x n)). Qed.
Lemma lem1656031 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1656032 (x : real) (n : nat) : (term425 x n) = (term409 x n).
Proof. exact (MK_COMB (@lem1656031) (@lem1656030 x n)). Qed.
Lemma lem1656033 (x : real) : ((real_abs x) = term32) = ((real_abs x) = term32).
Proof. exact (eq_refl ((real_abs x) = term32)). Qed.
Lemma lem1656034 (n : nat) (x : real) : (term426 n x) = (term411 n x).
Proof. exact (MK_COMB (@lem1656032 x n) (@lem1656033 x)). Qed.
Lemma lem1656035 (x : real) : (term427 x) = (term413 x).
Proof. exact (fun_ext (fun n : nat => @lem1656034 n x)). Qed.
Lemma lem1656036 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1656037 (x : real) : (term421 x) = (term414 x).
Proof. exact (MK_COMB (@lem1656036) (@lem1656035 x)). Qed.
Lemma lem1656038 (x : real) : ((term422 x) = (term421 x)) = ((term435 x) = (term414 x)).
Proof. exact (MK_COMB (@lem1656029 x) (@lem1656037 x)). Qed.
Lemma lem1656039 (x : real) : (term435 x) = (term414 x).
Proof. exact (EQ_MP (@lem1656038 x) (@lem1656019 x)). Qed.
Lemma lem1656040 : term436 = term415.
Proof. exact (fun_ext (fun x : real => @lem1656039 x)). Qed.
Lemma lem1656041 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1656042 : term437 = term416.
Proof. exact (MK_COMB (@lem1656041) (@lem1656040)). Qed.
Lemma lem1656055 (n : nat) (x : real) : (term411 n x) = (term411 n x).
Proof. exact (eq_refl (term411 n x)). Qed.
Lemma lem1656056 (x : real) : (term413 x) = (term413 x).
Proof. exact (fun_ext (fun n : nat => @lem1656055 n x)). Qed.
Lemma lem1656057 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1656058 (x : real) : (term414 x) = (term414 x).
Proof. exact (MK_COMB (@lem1656057) (@lem1656056 x)). Qed.
Lemma lem1656059 : term415 = term415.
Proof. exact (fun_ext (fun x : real => @lem1656058 x)). Qed.
Lemma lem1656060 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1656061 : term416 = term416.
Proof. exact (MK_COMB (@lem1656060) (@lem1656059)). Qed.
Lemma lem1656062 : term437 = term416.
Proof. exact (TRANS (@lem1656042) (@lem1656061)). Qed.
Lemma lem1656063 (h1 : term361) : term416.
Proof. exact (EQ_MP (@lem1656062) (@lem1655929 h1)). Qed.
Lemma lem1656083 (x : real) (h1 : term330 x) : term330 x.
Proof. exact (h1). Qed.
Lemma lem1656151 (x : real) (h1 : term330 x) : term330 x.
Proof. exact (h1). Qed.
Lemma lem1656212 (_25647 : real) (h1 : term361) : term440 _25647.
Proof. exact (@lem1655999 h1 _25647). Qed.
Lemma lem1656213 (_25647 : real) : (term440 _25647) = (term414 _25647).
Proof. exact (eq_refl (term440 _25647)). Qed.
Lemma lem1656214 (_25647 : real) (h1 : term361) : term414 _25647.
Proof. exact (EQ_MP (@lem1656213 _25647) (@lem1656212 _25647 h1)). Qed.
Lemma lem1656215 (_25647 : real) (_25648 : nat) (h1 : term361) : term441 _25647 _25648.
Proof. exact (@lem1656214 _25647 h1 _25648). Qed.
Lemma lem1656216 (_25648 : nat) (_25647 : real) : (term441 _25647 _25648) = (term411 _25648 _25647).
Proof. exact (eq_refl (term441 _25647 _25648)). Qed.
Lemma lem1656217 (_25648 : nat) (_25647 : real) (h1 : term361) : term411 _25648 _25647.
Proof. exact (EQ_MP (@lem1656216 _25648 _25647) (@lem1656215 _25647 _25648 h1)). Qed.
Lemma lem1656218 (_25649 : real) (h1 : term361) : term440 _25649.
Proof. exact (@lem1656063 h1 _25649). Qed.
Lemma lem1656219 (_25649 : real) : (term440 _25649) = (term414 _25649).
Proof. exact (eq_refl (term440 _25649)). Qed.
Lemma lem1656220 (_25649 : real) (h1 : term361) : term414 _25649.
Proof. exact (EQ_MP (@lem1656219 _25649) (@lem1656218 _25649 h1)). Qed.
Lemma lem1656221 (_25649 : real) (_25650 : nat) (h1 : term361) : term441 _25649 _25650.
Proof. exact (@lem1656220 _25649 h1 _25650). Qed.
Lemma lem1656222 (_25650 : nat) (_25649 : real) : (term441 _25649 _25650) = (term411 _25650 _25649).
Proof. exact (eq_refl (term441 _25649 _25650)). Qed.
Lemma lem1656223 (_25650 : nat) (_25649 : real) (h1 : term361) : term411 _25650 _25649.
Proof. exact (EQ_MP (@lem1656222 _25650 _25649) (@lem1656221 _25649 _25650 h1)). Qed.
Lemma lem1656237 (n : nat) (h1 : term333 n) : term333 n.
Proof. exact (h1). Qed.
Lemma lem1656239 (x : real) (h1 : term330 x) : term330 x.
Proof. exact (h1). Qed.
Lemma lem1656250 (_25648 : nat) (_25647 : real) : (term411 _25648 _25647) = (term442 _25648 _25647).
Proof. exact (@lem1655200 (_25648 = (NUMERAL 0)) (term402 _25647 _25648) ((real_abs _25647) = term32)). Qed.
Lemma lem1656251 (_25648 : nat) (_25647 : real) (h1 : term361) : term442 _25648 _25647.
Proof. exact (EQ_MP (@lem1656250 _25648 _25647) (@lem1656217 _25648 _25647 h1)). Qed.
Lemma lem1656255 (x : real) (h1 : term330 x) : term330 x.
Proof. exact (h1). Qed.
Lemma lem1656257 (n : nat) (h1 : term333 n) : term333 n.
Proof. exact (h1). Qed.
Lemma lem1656259 (x : real) (h1 : term330 x) : term330 x.
Proof. exact (h1). Qed.
Lemma lem1656270 (_25650 : nat) (_25649 : real) : (term411 _25650 _25649) = (term442 _25650 _25649).
Proof. exact (@lem1655200 (_25650 = (NUMERAL 0)) (term402 _25649 _25650) ((real_abs _25649) = term32)). Qed.
Lemma lem1656271 (_25650 : nat) (_25649 : real) (h1 : term361) : term442 _25650 _25649.
Proof. exact (EQ_MP (@lem1656270 _25650 _25649) (@lem1656223 _25650 _25649 h1)). Qed.
Lemma lem1656281 (x : real) (h1 : term330 x) : term330 x.
Proof. exact (h1). Qed.
Lemma lem1656303 (x : real) (h1 : term330 x) : term330 x.
Proof. exact (h1). Qed.
Lemma lem1656374 (n : nat) (h1 : term333 n) : term333 n.
Proof. exact (h1). Qed.
Lemma lem1656375 (n : nat) (h1 : term333 n) : term443 n.
Proof. exact (fun h0 : n = (NUMERAL 0) => @lem1656374 n h1). Qed.
Lemma lem1656377 (p : Prop) : (term444 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1656378 (n : nat) : (term443 n) = (term333 n).
Proof. exact (@lem1656377 (n = (NUMERAL 0))). Qed.
Lemma lem1656379 (n : nat) (h1 : term333 n) : term333 n.
Proof. exact (EQ_MP (@lem1656378 n) (@lem1656375 n h1)). Qed.
Lemma lem1656381 (x : real) (n : nat) (h1 : term396 x n) : (real_pow x n) = term32.
Proof. exact (proj1 (@lem1655930 x n h1)). Qed.
Lemma lem1656382 (x : real) (n : nat) (h1 : term396 x n) : term445 x n.
Proof. exact (fun h0 : term402 x n => @lem1656381 x n h1). Qed.
Lemma lem1656384 (p : Prop) : (term446 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1656385 (x : real) (n : nat) : (term445 x n) = ((real_pow x n) = term32).
Proof. exact (@lem1656384 ((real_pow x n) = term32)). Qed.
Lemma lem1656386 (x : real) (n : nat) (h1 : term396 x n) : (real_pow x n) = term32.
Proof. exact (EQ_MP (@lem1656385 x n) (@lem1656382 x n h1)). Qed.
Lemma lem1656404 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1656405 (_25647 : real) (_25648 : nat) : (term447 _25648 _25647) = (term448 _25647 _25648).
Proof. exact (@lem1656404 ((real_abs _25647) = term32) (term402 _25647 _25648)). Qed.
Lemma lem1656415 (_25648 : nat) : (term404 _25648) = (term404 _25648).
Proof. exact (eq_refl (term404 _25648)). Qed.
Lemma lem1656416 (_25647 : real) (_25648 : nat) : (term442 _25648 _25647) = (term449 _25647 _25648).
Proof. exact (MK_COMB (@lem1656415 _25648) (@lem1656405 _25647 _25648)). Qed.
Lemma lem1656427 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1656428 (_25647 : real) (_25648 : nat) : (term450 _25648 _25647) = (term451 _25647 _25648).
Proof. exact (MK_COMB (@lem1656427) (@lem1656416 _25647 _25648)). Qed.
Lemma lem1656432 (q : Prop) (p : Prop) (r : Prop) : (term326 p q r) = (term326 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1656433 (_25647 : real) (_25648 : nat) : (term452 _25647 _25648) = (term449 _25647 _25648).
Proof. exact (@lem1656432 (_25648 = (NUMERAL 0)) ((real_abs _25647) = term32) (term402 _25647 _25648)). Qed.
Lemma lem1656455 (_25647 : real) (_25648 : nat) : ((term442 _25648 _25647) = (term452 _25647 _25648)) = ((term449 _25647 _25648) = (term449 _25647 _25648)).
Proof. exact (MK_COMB (@lem1656428 _25647 _25648) (@lem1656433 _25647 _25648)). Qed.
Lemma lem1656457 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1656458 (x : Prop) : (x = x) = True.
Proof. exact (@lem1656457 Prop x). Qed.
Lemma lem1656459 (_25647 : real) (_25648 : nat) : ((term449 _25647 _25648) = (term449 _25647 _25648)) = True.
Proof. exact (@lem1656458 (term449 _25647 _25648)). Qed.
Lemma lem1656460 (_25647 : real) (_25648 : nat) : ((term442 _25648 _25647) = (term452 _25647 _25648)) = True.
Proof. exact (TRANS (@lem1656455 _25647 _25648) (@lem1656459 _25647 _25648)). Qed.
Lemma lem1656461 (_25647 : real) (_25648 : nat) : True = ((term442 _25648 _25647) = (term452 _25647 _25648)).
Proof. exact (SYM (@lem1656460 _25647 _25648)). Qed.
Lemma lem1656462 (_25647 : real) (_25648 : nat) : (term442 _25648 _25647) = (term452 _25647 _25648).
Proof. exact (EQ_MP (@lem1656461 _25647 _25648) (@lem0)). Qed.
Lemma lem1656463 (_25647 : real) (_25648 : nat) (h1 : term361) : term452 _25647 _25648.
Proof. exact (EQ_MP (@lem1656462 _25647 _25648) (@lem1656251 _25648 _25647 h1)). Qed.
Lemma lem1656465 (b : Prop) (a : Prop) : (a \/ b) = (term453 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1656466 (_25648 : nat) (_25647 : real) : (term452 _25647 _25648) = (term454 _25648 _25647).
Proof. exact (@lem1656465 (term406 _25647 _25648) ((real_abs _25647) = term32)). Qed.
Lemma lem1656468 (a : Prop) (b : Prop) : (term455 a b) = (term456 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1656469 (_25647 : real) (_25648 : nat) : (term457 _25647 _25648) = (term458 _25647 _25648).
Proof. exact (@lem1656468 (_25648 = (NUMERAL 0)) (term402 _25647 _25648)). Qed.
Lemma lem1656471 (a : Prop) : (term459 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1656472 (_25647 : real) (_25648 : nat) : (term460 _25647 _25648) = ((real_pow _25647 _25648) = term32).
Proof. exact (@lem1656471 ((real_pow _25647 _25648) = term32)). Qed.
Lemma lem1656473 (_25648 : nat) : (term461 _25648) = (term461 _25648).
Proof. exact (eq_refl (term461 _25648)). Qed.
Lemma lem1656474 (_25647 : real) (_25648 : nat) : (term458 _25647 _25648) = (term412 _25647 _25648).
Proof. exact (MK_COMB (@lem1656473 _25648) (@lem1656472 _25647 _25648)). Qed.
Lemma lem1656475 (_25647 : real) (_25648 : nat) : (term457 _25647 _25648) = (term412 _25647 _25648).
Proof. exact (TRANS (@lem1656469 _25647 _25648) (@lem1656474 _25647 _25648)). Qed.
Lemma lem1656476 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1656477 (_25647 : real) (_25648 : nat) : (term462 _25647 _25648) = (term463 _25647 _25648).
Proof. exact (MK_COMB (@lem1656476) (@lem1656475 _25647 _25648)). Qed.
Lemma lem1656478 (_25647 : real) : ((real_abs _25647) = term32) = ((real_abs _25647) = term32).
Proof. exact (eq_refl ((real_abs _25647) = term32)). Qed.
Lemma lem1656479 (_25648 : nat) (_25647 : real) : (term454 _25648 _25647) = (term378 _25648 _25647).
Proof. exact (MK_COMB (@lem1656477 _25647 _25648) (@lem1656478 _25647)). Qed.
Lemma lem1656480 (_25648 : nat) (_25647 : real) : (term452 _25647 _25648) = (term378 _25648 _25647).
Proof. exact (TRANS (@lem1656466 _25648 _25647) (@lem1656479 _25648 _25647)). Qed.
Lemma lem1656482 (x : real) (n : nat) (h1 : term333 n) (h2 : term396 x n) : term412 x n.
Proof. exact (conj (@lem1656379 n h1) (@lem1656386 x n h2)). Qed.
Lemma lem1656484 (_25648 : nat) (_25647 : real) (h1 : term361) : term378 _25648 _25647.
Proof. exact (EQ_MP (@lem1656480 _25648 _25647) (@lem1656463 _25647 _25648 h1)). Qed.
Lemma lem1656485 (n : nat) (x : real) (h1 : term361) : term378 n x.
Proof. exact (@lem1656484 n x h1). Qed.
Lemma lem1656488 (x : real) (n : nat) (h1 : term361) (h2 : term333 n) (h3 : term396 x n) : (real_abs x) = term32.
Proof. exact (@lem1656485 n x h1 (@lem1656482 x n h2 h3)). Qed.
Lemma lem1656489 (x : real) (n : nat) (h1 : term361) (h2 : term333 n) (h3 : term396 x n) : term464 x.
Proof. exact (fun h0 : term330 x => @lem1656488 x n h1 h2 h3). Qed.
Lemma lem1656491 (p : Prop) : (term446 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1656492 (x : real) : (term464 x) = ((real_abs x) = term32).
Proof. exact (@lem1656491 ((real_abs x) = term32)). Qed.
Lemma lem1656493 (x : real) (n : nat) (h1 : term361) (h2 : term333 n) (h3 : term396 x n) : (real_abs x) = term32.
Proof. exact (EQ_MP (@lem1656492 x) (@lem1656489 x n h1 h2 h3)). Qed.
Lemma lem1656496 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1656498 (x : real) : (term330 x) = (term465 x).
Proof. exact (@lem1656496 ((real_abs x) = term32)). Qed.
Lemma lem1656501 (x : real) (h1 : term330 x) : term465 x.
Proof. exact (EQ_MP (@lem1656498 x) (@lem1656239 x h1)). Qed.
Lemma lem1656504 (x : real) (n : nat) (h1 : term361) (h2 : term333 n) (h3 : term330 x) (h4 : term396 x n) : False.
Proof. exact (@lem1656501 x h3 (@lem1656493 x n h1 h2 h4)). Qed.
Lemma lem1656505 (x : real) (n : nat) (h1 : term361) (h2 : term333 n) (h3 : term330 x) (h4 : term396 x n) : term466.
Proof. exact (fun h0 : ~ False => @lem1656504 x n h1 h2 h3 h4). Qed.
Lemma lem1656507 (p : Prop) : (term446 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1656508 : term466 = False.
Proof. exact (@lem1656507 False). Qed.
Lemma lem1656509 (x : real) (n : nat) (h1 : term361) (h2 : term333 n) (h3 : term330 x) (h4 : term396 x n) : False.
Proof. exact (EQ_MP (@lem1656508) (@lem1656505 x n h1 h2 h3 h4)). Qed.
Lemma lem1656593 (n : nat) (h1 : term333 n) : term333 n.
Proof. exact (h1). Qed.
Lemma lem1656594 (n : nat) (h1 : term333 n) : term443 n.
Proof. exact (fun h0 : n = (NUMERAL 0) => @lem1656593 n h1). Qed.
Lemma lem1656596 (p : Prop) : (term444 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1656597 (n : nat) : (term443 n) = (term333 n).
Proof. exact (@lem1656596 (n = (NUMERAL 0))). Qed.
Lemma lem1656598 (n : nat) (h1 : term333 n) : term333 n.
Proof. exact (EQ_MP (@lem1656597 n) (@lem1656594 n h1)). Qed.
Lemma lem1656600 (x : real) (n : nat) (h1 : term396 x n) : (real_pow x n) = term32.
Proof. exact (proj1 (@lem1655930 x n h1)). Qed.
Lemma lem1656601 (x : real) (n : nat) (h1 : term396 x n) : term445 x n.
Proof. exact (fun h0 : term402 x n => @lem1656600 x n h1). Qed.
Lemma lem1656603 (p : Prop) : (term446 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1656604 (x : real) (n : nat) : (term445 x n) = ((real_pow x n) = term32).
Proof. exact (@lem1656603 ((real_pow x n) = term32)). Qed.
Lemma lem1656605 (x : real) (n : nat) (h1 : term396 x n) : (real_pow x n) = term32.
Proof. exact (EQ_MP (@lem1656604 x n) (@lem1656601 x n h1)). Qed.
Lemma lem1656623 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1656624 (_25649 : real) (_25650 : nat) : (term447 _25650 _25649) = (term448 _25649 _25650).
Proof. exact (@lem1656623 ((real_abs _25649) = term32) (term402 _25649 _25650)). Qed.
Lemma lem1656634 (_25650 : nat) : (term404 _25650) = (term404 _25650).
Proof. exact (eq_refl (term404 _25650)). Qed.
Lemma lem1656635 (_25649 : real) (_25650 : nat) : (term442 _25650 _25649) = (term449 _25649 _25650).
Proof. exact (MK_COMB (@lem1656634 _25650) (@lem1656624 _25649 _25650)). Qed.
Lemma lem1656646 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1656647 (_25649 : real) (_25650 : nat) : (term450 _25650 _25649) = (term451 _25649 _25650).
Proof. exact (MK_COMB (@lem1656646) (@lem1656635 _25649 _25650)). Qed.
Lemma lem1656651 (q : Prop) (p : Prop) (r : Prop) : (term326 p q r) = (term326 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1656652 (_25649 : real) (_25650 : nat) : (term452 _25649 _25650) = (term449 _25649 _25650).
Proof. exact (@lem1656651 (_25650 = (NUMERAL 0)) ((real_abs _25649) = term32) (term402 _25649 _25650)). Qed.
Lemma lem1656674 (_25649 : real) (_25650 : nat) : ((term442 _25650 _25649) = (term452 _25649 _25650)) = ((term449 _25649 _25650) = (term449 _25649 _25650)).
Proof. exact (MK_COMB (@lem1656647 _25649 _25650) (@lem1656652 _25649 _25650)). Qed.
Lemma lem1656676 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1656677 (x : Prop) : (x = x) = True.
Proof. exact (@lem1656676 Prop x). Qed.
Lemma lem1656678 (_25649 : real) (_25650 : nat) : ((term449 _25649 _25650) = (term449 _25649 _25650)) = True.
Proof. exact (@lem1656677 (term449 _25649 _25650)). Qed.
Lemma lem1656679 (_25649 : real) (_25650 : nat) : ((term442 _25650 _25649) = (term452 _25649 _25650)) = True.
Proof. exact (TRANS (@lem1656674 _25649 _25650) (@lem1656678 _25649 _25650)). Qed.
Lemma lem1656680 (_25649 : real) (_25650 : nat) : True = ((term442 _25650 _25649) = (term452 _25649 _25650)).
Proof. exact (SYM (@lem1656679 _25649 _25650)). Qed.
Lemma lem1656681 (_25649 : real) (_25650 : nat) : (term442 _25650 _25649) = (term452 _25649 _25650).
Proof. exact (EQ_MP (@lem1656680 _25649 _25650) (@lem0)). Qed.
Lemma lem1656682 (_25649 : real) (_25650 : nat) (h1 : term361) : term452 _25649 _25650.
Proof. exact (EQ_MP (@lem1656681 _25649 _25650) (@lem1656271 _25650 _25649 h1)). Qed.
Lemma lem1656684 (b : Prop) (a : Prop) : (a \/ b) = (term453 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1656685 (_25650 : nat) (_25649 : real) : (term452 _25649 _25650) = (term454 _25650 _25649).
Proof. exact (@lem1656684 (term406 _25649 _25650) ((real_abs _25649) = term32)). Qed.
Lemma lem1656687 (a : Prop) (b : Prop) : (term455 a b) = (term456 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1656688 (_25649 : real) (_25650 : nat) : (term457 _25649 _25650) = (term458 _25649 _25650).
Proof. exact (@lem1656687 (_25650 = (NUMERAL 0)) (term402 _25649 _25650)). Qed.
Lemma lem1656690 (a : Prop) : (term459 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1656691 (_25649 : real) (_25650 : nat) : (term460 _25649 _25650) = ((real_pow _25649 _25650) = term32).
Proof. exact (@lem1656690 ((real_pow _25649 _25650) = term32)). Qed.
Lemma lem1656692 (_25650 : nat) : (term461 _25650) = (term461 _25650).
Proof. exact (eq_refl (term461 _25650)). Qed.
Lemma lem1656693 (_25649 : real) (_25650 : nat) : (term458 _25649 _25650) = (term412 _25649 _25650).
Proof. exact (MK_COMB (@lem1656692 _25650) (@lem1656691 _25649 _25650)). Qed.
Lemma lem1656694 (_25649 : real) (_25650 : nat) : (term457 _25649 _25650) = (term412 _25649 _25650).
Proof. exact (TRANS (@lem1656688 _25649 _25650) (@lem1656693 _25649 _25650)). Qed.
Lemma lem1656695 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1656696 (_25649 : real) (_25650 : nat) : (term462 _25649 _25650) = (term463 _25649 _25650).
Proof. exact (MK_COMB (@lem1656695) (@lem1656694 _25649 _25650)). Qed.
Lemma lem1656697 (_25649 : real) : ((real_abs _25649) = term32) = ((real_abs _25649) = term32).
Proof. exact (eq_refl ((real_abs _25649) = term32)). Qed.
Lemma lem1656698 (_25650 : nat) (_25649 : real) : (term454 _25650 _25649) = (term378 _25650 _25649).
Proof. exact (MK_COMB (@lem1656696 _25649 _25650) (@lem1656697 _25649)). Qed.
Lemma lem1656699 (_25650 : nat) (_25649 : real) : (term452 _25649 _25650) = (term378 _25650 _25649).
Proof. exact (TRANS (@lem1656685 _25650 _25649) (@lem1656698 _25650 _25649)). Qed.
Lemma lem1656701 (x : real) (n : nat) (h1 : term333 n) (h2 : term396 x n) : term412 x n.
Proof. exact (conj (@lem1656598 n h1) (@lem1656605 x n h2)). Qed.
Lemma lem1656703 (_25650 : nat) (_25649 : real) (h1 : term361) : term378 _25650 _25649.
Proof. exact (EQ_MP (@lem1656699 _25650 _25649) (@lem1656682 _25649 _25650 h1)). Qed.
Lemma lem1656704 (n : nat) (x : real) (h1 : term361) : term378 n x.
Proof. exact (@lem1656703 n x h1). Qed.
Lemma lem1656707 (x : real) (n : nat) (h1 : term361) (h2 : term333 n) (h3 : term396 x n) : (real_abs x) = term32.
Proof. exact (@lem1656704 n x h1 (@lem1656701 x n h2 h3)). Qed.
Lemma lem1656708 (x : real) (n : nat) (h1 : term361) (h2 : term333 n) (h3 : term396 x n) : term464 x.
Proof. exact (fun h0 : term330 x => @lem1656707 x n h1 h2 h3). Qed.
Lemma lem1656710 (p : Prop) : (term446 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1656711 (x : real) : (term464 x) = ((real_abs x) = term32).
Proof. exact (@lem1656710 ((real_abs x) = term32)). Qed.
Lemma lem1656712 (x : real) (n : nat) (h1 : term361) (h2 : term333 n) (h3 : term396 x n) : (real_abs x) = term32.
Proof. exact (EQ_MP (@lem1656711 x) (@lem1656708 x n h1 h2 h3)). Qed.
Lemma lem1656715 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1656717 (x : real) : (term330 x) = (term465 x).
Proof. exact (@lem1656715 ((real_abs x) = term32)). Qed.
Lemma lem1656720 (x : real) (h1 : term330 x) : term465 x.
Proof. exact (EQ_MP (@lem1656717 x) (@lem1656259 x h1)). Qed.
Lemma lem1656723 (x : real) (n : nat) (h1 : term361) (h2 : term333 n) (h3 : term330 x) (h4 : term396 x n) : False.
Proof. exact (@lem1656720 x h3 (@lem1656712 x n h1 h2 h4)). Qed.
Lemma lem1656724 (x : real) (n : nat) (h1 : term361) (h2 : term333 n) (h3 : term330 x) (h4 : term396 x n) : term466.
Proof. exact (fun h0 : ~ False => @lem1656723 x n h1 h2 h3 h4). Qed.
Lemma lem1656726 (p : Prop) : (term446 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1656727 : term466 = False.
Proof. exact (@lem1656726 False). Qed.
Lemma lem1656728 (x : real) (n : nat) (h1 : term361) (h2 : term333 n) (h3 : term330 x) (h4 : term396 x n) : False.
Proof. exact (EQ_MP (@lem1656727) (@lem1656724 x n h1 h2 h3 h4)). Qed.
Lemma lem1656800 (x : real) (n : nat) (h1 : term393 x n) : (real_abs x) = term32.
Proof. exact (proj1 (@lem1655938 x n h1)). Qed.
Lemma lem1656801 (x : real) (n : nat) (h1 : term393 x n) : term464 x.
Proof. exact (fun h0 : term330 x => @lem1656800 x n h1). Qed.
Lemma lem1656803 (p : Prop) : (term446 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1656804 (x : real) : (term464 x) = ((real_abs x) = term32).
Proof. exact (@lem1656803 ((real_abs x) = term32)). Qed.
Lemma lem1656805 (x : real) (n : nat) (h1 : term393 x n) : (real_abs x) = term32.
Proof. exact (EQ_MP (@lem1656804 x) (@lem1656801 x n h1)). Qed.
Lemma lem1656808 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1656810 (x : real) : (term330 x) = (term465 x).
Proof. exact (@lem1656808 ((real_abs x) = term32)). Qed.
Lemma lem1656813 (x : real) (h1 : term330 x) : term465 x.
Proof. exact (EQ_MP (@lem1656810 x) (@lem1656281 x h1)). Qed.
Lemma lem1656816 (x : real) (n : nat) (h1 : term330 x) (h2 : term393 x n) : False.
Proof. exact (@lem1656813 x h1 (@lem1656805 x n h2)). Qed.
Lemma lem1656817 (x : real) (n : nat) (h1 : term330 x) (h2 : term393 x n) : term466.
Proof. exact (fun h0 : ~ False => @lem1656816 x n h1 h2). Qed.
Lemma lem1656819 (p : Prop) : (term446 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1656820 : term466 = False.
Proof. exact (@lem1656819 False). Qed.
Lemma lem1656821 (x : real) (n : nat) (h1 : term330 x) (h2 : term393 x n) : False.
Proof. exact (EQ_MP (@lem1656820) (@lem1656817 x n h1 h2)). Qed.
Lemma lem1656886 (x : real) (n : nat) (h1 : term393 x n) : (real_abs x) = term32.
Proof. exact (proj1 (@lem1655938 x n h1)). Qed.
Lemma lem1656887 (x : real) (n : nat) (h1 : term393 x n) : term464 x.
Proof. exact (fun h0 : term330 x => @lem1656886 x n h1). Qed.
Lemma lem1656889 (p : Prop) : (term446 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1656890 (x : real) : (term464 x) = ((real_abs x) = term32).
Proof. exact (@lem1656889 ((real_abs x) = term32)). Qed.
Lemma lem1656891 (x : real) (n : nat) (h1 : term393 x n) : (real_abs x) = term32.
Proof. exact (EQ_MP (@lem1656890 x) (@lem1656887 x n h1)). Qed.
Lemma lem1656894 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1656896 (x : real) : (term330 x) = (term465 x).
Proof. exact (@lem1656894 ((real_abs x) = term32)). Qed.
Lemma lem1656899 (x : real) (h1 : term330 x) : term465 x.
Proof. exact (EQ_MP (@lem1656896 x) (@lem1656303 x h1)). Qed.
Lemma lem1656902 (x : real) (n : nat) (h1 : term330 x) (h2 : term393 x n) : False.
Proof. exact (@lem1656899 x h1 (@lem1656891 x n h2)). Qed.
Lemma lem1656903 (x : real) (n : nat) (h1 : term330 x) (h2 : term393 x n) : term466.
Proof. exact (fun h0 : ~ False => @lem1656902 x n h1 h2). Qed.
Lemma lem1656905 (p : Prop) : (term446 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1656906 : term466 = False.
Proof. exact (@lem1656905 False). Qed.
Lemma lem1656907 (x : real) (n : nat) (h1 : term330 x) (h2 : term393 x n) : False.
Proof. exact (EQ_MP (@lem1656906) (@lem1656903 x n h1 h2)). Qed.
Lemma lem1656908 (x : real) (n : nat) (h1 : term330 x) (h2 : term393 x n) : (term330 x) = False.
Proof. exact (prop_ext (fun h3 : term330 x => @lem1656907 x n h1 h2) (fun h3 : False => @lem1656303 x h1)). Qed.
Lemma lem1656909 (x : real) (n : nat) (h1 : term330 x) (h2 : term393 x n) : False.
Proof. exact (EQ_MP (@lem1656908 x n h1 h2) (@lem1656303 x h1)). Qed.
Lemma lem1656910 (x : real) (n : nat) (h1 : term330 x) (h2 : term393 x n) : (term330 x) = False.
Proof. exact (prop_ext (fun h3 : term330 x => @lem1656821 x n h1 h2) (fun h3 : False => @lem1656281 x h1)). Qed.
Lemma lem1656911 (x : real) (n : nat) (h1 : term330 x) (h2 : term393 x n) : False.
Proof. exact (EQ_MP (@lem1656910 x n h1 h2) (@lem1656281 x h1)). Qed.
Lemma lem1656912 (x : real) (n : nat) (h1 : term361) (h2 : term333 n) (h3 : term330 x) (h4 : term396 x n) : (term330 x) = False.
Proof. exact (prop_ext (fun h5 : term330 x => @lem1656728 x n h1 h2 h3 h4) (fun h5 : False => @lem1656259 x h3)). Qed.
Lemma lem1656913 (x : real) (n : nat) (h1 : term361) (h2 : term333 n) (h3 : term330 x) (h4 : term396 x n) : False.
Proof. exact (EQ_MP (@lem1656912 x n h1 h2 h3 h4) (@lem1656259 x h3)). Qed.
Lemma lem1656914 (x : real) (n : nat) (h1 : term361) (h2 : term333 n) (h3 : term330 x) (h4 : term396 x n) : (term333 n) = False.
Proof. exact (prop_ext (fun h5 : term333 n => @lem1656913 x n h1 h2 h3 h4) (fun h5 : False => @lem1656257 n h2)). Qed.
Lemma lem1656915 (x : real) (n : nat) (h1 : term361) (h2 : term333 n) (h3 : term330 x) (h4 : term396 x n) : False.
Proof. exact (EQ_MP (@lem1656914 x n h1 h2 h3 h4) (@lem1656257 n h2)). Qed.
Lemma lem1656916 (x : real) (n : nat) (h1 : term361) (h2 : term333 n) (h3 : term330 x) (h4 : term396 x n) : (term330 x) = False.
Proof. exact (prop_ext (fun h5 : term330 x => @lem1656509 x n h1 h2 h3 h4) (fun h5 : False => @lem1656255 x h3)). Qed.
Lemma lem1656917 (x : real) (n : nat) (h1 : term361) (h2 : term333 n) (h3 : term330 x) (h4 : term396 x n) : False.
Proof. exact (EQ_MP (@lem1656916 x n h1 h2 h3 h4) (@lem1656255 x h3)). Qed.
Lemma lem1656918 (x : real) (n : nat) (h1 : term361) (h2 : term333 n) (h3 : term330 x) (h4 : term396 x n) : (term330 x) = False.
Proof. exact (prop_ext (fun h5 : term330 x => @lem1656917 x n h1 h2 h3 h4) (fun h5 : False => @lem1656239 x h3)). Qed.
Lemma lem1656919 (x : real) (n : nat) (h1 : term361) (h2 : term333 n) (h3 : term330 x) (h4 : term396 x n) : False.
Proof. exact (EQ_MP (@lem1656918 x n h1 h2 h3 h4) (@lem1656239 x h3)). Qed.
Lemma lem1656920 (x : real) (n : nat) (h1 : term361) (h2 : term333 n) (h3 : term330 x) (h4 : term396 x n) : (term333 n) = False.
Proof. exact (prop_ext (fun h5 : term333 n => @lem1656919 x n h1 h2 h3 h4) (fun h5 : False => @lem1656237 n h2)). Qed.
Lemma lem1656921 (x : real) (n : nat) (h1 : term361) (h2 : term333 n) (h3 : term330 x) (h4 : term396 x n) : False.
Proof. exact (EQ_MP (@lem1656920 x n h1 h2 h3 h4) (@lem1656237 n h2)). Qed.
Lemma lem1656922 (x : real) (n : nat) (h1 : term330 x) (h2 : term393 x n) : (term330 x) = False.
Proof. exact (prop_ext (fun h3 : term330 x => @lem1656909 x n h1 h2) (fun h3 : False => @lem1656151 x h1)). Qed.
Lemma lem1656923 (x : real) (n : nat) (h1 : term330 x) (h2 : term393 x n) : False.
Proof. exact (EQ_MP (@lem1656922 x n h1 h2) (@lem1656151 x h1)). Qed.
Lemma lem1656924 (x : real) (n : nat) (h1 : term330 x) (h2 : term393 x n) : (term330 x) = False.
Proof. exact (prop_ext (fun h3 : term330 x => @lem1656911 x n h1 h2) (fun h3 : False => @lem1656083 x h1)). Qed.
Lemma lem1656925 (x : real) (n : nat) (h1 : term330 x) (h2 : term393 x n) : False.
Proof. exact (EQ_MP (@lem1656924 x n h1 h2) (@lem1656083 x h1)). Qed.
Lemma lem1656926 (x : real) (n : nat) (h1 : term361) (h2 : term333 n) (h3 : term330 x) (h4 : term396 x n) : (term330 x) = False.
Proof. exact (prop_ext (fun h5 : term330 x => @lem1656915 x n h1 h2 h3 h4) (fun h5 : False => @lem1656015 x h3)). Qed.
Lemma lem1656927 (x : real) (n : nat) (h1 : term361) (h2 : term333 n) (h3 : term330 x) (h4 : term396 x n) : False.
Proof. exact (EQ_MP (@lem1656926 x n h1 h2 h3 h4) (@lem1656015 x h3)). Qed.
Lemma lem1656928 (x : real) (n : nat) (h1 : term361) (h2 : term333 n) (h3 : term330 x) (h4 : term396 x n) : (term333 n) = False.
Proof. exact (prop_ext (fun h5 : term333 n => @lem1656927 x n h1 h2 h3 h4) (fun h5 : False => @lem1656011 n h2)). Qed.
Lemma lem1656929 (x : real) (n : nat) (h1 : term361) (h2 : term333 n) (h3 : term330 x) (h4 : term396 x n) : False.
Proof. exact (EQ_MP (@lem1656928 x n h1 h2 h3 h4) (@lem1656011 n h2)). Qed.
Lemma lem1656930 (x : real) (n : nat) (h1 : term361) (h2 : term333 n) (h3 : term330 x) (h4 : term396 x n) : (term330 x) = False.
Proof. exact (prop_ext (fun h5 : term330 x => @lem1656921 x n h1 h2 h3 h4) (fun h5 : False => @lem1656007 x h3)). Qed.
Lemma lem1656931 (x : real) (n : nat) (h1 : term361) (h2 : term333 n) (h3 : term330 x) (h4 : term396 x n) : False.
Proof. exact (EQ_MP (@lem1656930 x n h1 h2 h3 h4) (@lem1656007 x h3)). Qed.
Lemma lem1656932 (x : real) (n : nat) (h1 : term361) (h2 : term333 n) (h3 : term330 x) (h4 : term396 x n) : (term330 x) = False.
Proof. exact (prop_ext (fun h5 : term330 x => @lem1656931 x n h1 h2 h3 h4) (fun h5 : False => @lem1655951 x h3)). Qed.
Lemma lem1656933 (x : real) (n : nat) (h1 : term361) (h2 : term333 n) (h3 : term330 x) (h4 : term396 x n) : False.
Proof. exact (EQ_MP (@lem1656932 x n h1 h2 h3 h4) (@lem1655951 x h3)). Qed.
Lemma lem1656934 (x : real) (n : nat) (h1 : term361) (h2 : term333 n) (h3 : term330 x) (h4 : term396 x n) : (term333 n) = False.
Proof. exact (prop_ext (fun h5 : term333 n => @lem1656933 x n h1 h2 h3 h4) (fun h5 : False => @lem1655947 n h2)). Qed.
Lemma lem1656935 (x : real) (n : nat) (h1 : term361) (h2 : term333 n) (h3 : term330 x) (h4 : term396 x n) : False.
Proof. exact (EQ_MP (@lem1656934 x n h1 h2 h3 h4) (@lem1655947 n h2)). Qed.
Lemma lem1656936 (x : real) (n : nat) (h1 : term330 x) (h2 : term393 x n) : (term330 x) = False.
Proof. exact (prop_ext (fun h3 : term330 x => @lem1656923 x n h1 h2) (fun h3 : False => @lem1656151 x h1)). Qed.
Lemma lem1656937 (x : real) (n : nat) (h1 : term330 x) (h2 : term393 x n) : False.
Proof. exact (EQ_MP (@lem1656936 x n h1 h2) (@lem1656151 x h1)). Qed.
Lemma lem1656938 (x : real) (n : nat) (h1 : term330 x) (h2 : term393 x n) : (term330 x) = False.
Proof. exact (prop_ext (fun h3 : term330 x => @lem1656925 x n h1 h2) (fun h3 : False => @lem1656083 x h1)). Qed.
Lemma lem1656939 (x : real) (n : nat) (h1 : term330 x) (h2 : term393 x n) : False.
Proof. exact (EQ_MP (@lem1656938 x n h1 h2) (@lem1656083 x h1)). Qed.
Lemma lem1656940 (x : real) (n : nat) (h1 : term361) (h2 : term333 n) (h3 : term330 x) (h4 : term396 x n) : (term330 x) = False.
Proof. exact (prop_ext (fun h5 : term330 x => @lem1656929 x n h1 h2 h3 h4) (fun h5 : False => @lem1656015 x h3)). Qed.
Lemma lem1656941 (x : real) (n : nat) (h1 : term361) (h2 : term333 n) (h3 : term330 x) (h4 : term396 x n) : False.
Proof. exact (EQ_MP (@lem1656940 x n h1 h2 h3 h4) (@lem1656015 x h3)). Qed.
Lemma lem1656942 (x : real) (n : nat) (h1 : term361) (h2 : term333 n) (h3 : term330 x) (h4 : term396 x n) : (term333 n) = False.
Proof. exact (prop_ext (fun h5 : term333 n => @lem1656941 x n h1 h2 h3 h4) (fun h5 : False => @lem1656011 n h2)). Qed.
Lemma lem1656943 (x : real) (n : nat) (h1 : term361) (h2 : term333 n) (h3 : term330 x) (h4 : term396 x n) : False.
Proof. exact (EQ_MP (@lem1656942 x n h1 h2 h3 h4) (@lem1656011 n h2)). Qed.
Lemma lem1656944 (x : real) (n : nat) (h1 : term361) (h2 : term333 n) (h3 : term330 x) (h4 : term396 x n) : (term330 x) = False.
Proof. exact (prop_ext (fun h5 : term330 x => @lem1656935 x n h1 h2 h3 h4) (fun h5 : False => @lem1656007 x h3)). Qed.
Lemma lem1656945 (x : real) (n : nat) (h1 : term361) (h2 : term333 n) (h3 : term330 x) (h4 : term396 x n) : False.
Proof. exact (EQ_MP (@lem1656944 x n h1 h2 h3 h4) (@lem1656007 x h3)). Qed.
Lemma lem1656946 (x : real) (n : nat) (h1 : term361) (h2 : term333 n) (h3 : term330 x) (h4 : term396 x n) : (term330 x) = False.
Proof. exact (prop_ext (fun h5 : term330 x => @lem1656945 x n h1 h2 h3 h4) (fun h5 : False => @lem1655951 x h3)). Qed.
Lemma lem1656947 (x : real) (n : nat) (h1 : term361) (h2 : term333 n) (h3 : term330 x) (h4 : term396 x n) : False.
Proof. exact (EQ_MP (@lem1656946 x n h1 h2 h3 h4) (@lem1655951 x h3)). Qed.
Lemma lem1656948 (x : real) (n : nat) (h1 : term361) (h2 : term333 n) (h3 : term330 x) (h4 : term396 x n) : (term333 n) = False.
Proof. exact (prop_ext (fun h5 : term333 n => @lem1656947 x n h1 h2 h3 h4) (fun h5 : False => @lem1655947 n h2)). Qed.
Lemma lem1656949 (x : real) (n : nat) (h1 : term361) (h2 : term333 n) (h3 : term330 x) (h4 : term396 x n) : False.
Proof. exact (EQ_MP (@lem1656948 x n h1 h2 h3 h4) (@lem1655947 n h2)). Qed.
Lemma lem1656950 (x : real) (n : nat) (h1 : term330 x) (h2 : term393 x n) : False.
Proof. exact (or_elim (@lem1655940 x n h2) (fun h0 : term467 x => @lem1656939 x n h1 h2) (fun h0 : Coq.Arith.PeanoNat.Nat.Even n => @lem1656937 x n h1 h2)). Qed.
Lemma lem1656951 (x : real) (n : nat) (h1 : term361) (h2 : term333 n) (h3 : term330 x) (h4 : term396 x n) : False.
Proof. exact (or_elim (@lem1655932 x n h4) (fun h0 : term330 x => @lem1656949 x n h1 h2 h3 h4) (fun h0 : term383 x n => @lem1656943 x n h1 h2 h3 h4)). Qed.
Lemma lem1656952 (n : nat) (x : real) (h1 : term361) (h2 : term354 x n) (h3 : term333 n) (h4 : term330 x) : False.
Proof. exact (or_elim (@lem1655879 x n h2) (fun h0 : term396 x n => @lem1656951 x n h1 h3 h4 h0) (fun h0 : term393 x n => @lem1656950 x n h4 h0)). Qed.
Lemma lem1656953 (n : nat) (x : real) (h1 : term361) (h2 : term354 x n) (h3 : term333 n) (h4 : term330 x) : (term330 x) = False.
Proof. exact (prop_ext (fun h5 : term330 x => @lem1656952 n x h1 h2 h3 h4) (fun h5 : False => @lem1655769 x h4)). Qed.
Lemma lem1656954 (n : nat) (x : real) (h1 : term361) (h2 : term354 x n) (h3 : term333 n) (h4 : term330 x) : False.
Proof. exact (EQ_MP (@lem1656953 n x h1 h2 h3 h4) (@lem1655769 x h4)). Qed.
Lemma lem1656955 (n : nat) (x : real) (h1 : term361) (h2 : term354 x n) (h3 : term333 n) (h4 : term330 x) : (term333 n) = False.
Proof. exact (prop_ext (fun h5 : term333 n => @lem1656954 n x h1 h2 h3 h4) (fun h5 : False => @lem1655753 n h3)). Qed.
Lemma lem1656956 (n : nat) (x : real) (h1 : term361) (h2 : term354 x n) (h3 : term333 n) (h4 : term330 x) : False.
Proof. exact (EQ_MP (@lem1656955 n x h1 h2 h3 h4) (@lem1655753 n h3)). Qed.
Lemma lem1656957 (n : nat) (x : real) (h1 : term361) (h2 : term354 x n) (h3 : term333 n) (h4 : term330 x) : (term330 x) = False.
Proof. exact (prop_ext (fun h5 : term330 x => @lem1656956 n x h1 h2 h3 h4) (fun h5 : False => @lem1655529 x h4)). Qed.
Lemma lem1656958 (n : nat) (x : real) (h1 : term361) (h2 : term354 x n) (h3 : term333 n) (h4 : term330 x) : False.
Proof. exact (EQ_MP (@lem1656957 n x h1 h2 h3 h4) (@lem1655529 x h4)). Qed.
Lemma lem1656959 (n : nat) (x : real) (h1 : term361) (h2 : term354 x n) (h3 : term333 n) (h4 : term330 x) : (term333 n) = False.
Proof. exact (prop_ext (fun h5 : term333 n => @lem1656958 n x h1 h2 h3 h4) (fun h5 : False => @lem1655523 n h3)). Qed.
Lemma lem1656960 (n : nat) (x : real) (h1 : term361) (h2 : term354 x n) (h3 : term333 n) (h4 : term330 x) : False.
Proof. exact (EQ_MP (@lem1656959 n x h1 h2 h3 h4) (@lem1655523 n h3)). Qed.
Lemma lem1656961 (n : nat) (x : real) (h1 : term354 x n) (h2 : term333 n) (h3 : term330 x) : term359.
Proof. exact (fun h0 : term361 => @lem1656960 n x h0 h1 h2 h3). Qed.
Lemma lem1656962 : term359 = term360.
Proof. exact (@lem69 term361). Qed.
Lemma lem1656963 (n : nat) (x : real) (h1 : term354 x n) (h2 : term333 n) (h3 : term330 x) : term360.
Proof. exact (EQ_MP (@lem1656962) (@lem1656961 n x h1 h2 h3)). Qed.
Lemma lem1656964 (n : nat) (x : real) (h1 : term333 n) (h2 : term330 x) : term364 x n.
Proof. exact (fun h0 : term354 x n => @lem1656963 n x h0 h1 h2). Qed.
Lemma lem1656965 (x : real) (n : nat) (h1 : term333 n) : term367 x n.
Proof. exact (fun h0 : term330 x => @lem1656964 n x h1 h0). Qed.
Lemma lem1656966 (x : real) (n : nat) : term369 x n.
Proof. exact (fun h0 : term333 n => @lem1656965 x n h0). Qed.
Lemma lem1656971 (n : nat) : term373 n.
Proof. exact (fun x : real => @lem1656966 x n). Qed.
Lemma lem1656976 : term377.
Proof. exact (fun n : nat => @lem1656971 n). Qed.
Lemma lem1656977 : term376.
Proof. exact (EQ_MP (@lem1655513) (@lem1656976)). Qed.
Lemma lem1656978 (n : nat) : term468 n.
Proof. exact (@lem1656977 n). Qed.
Lemma lem1656979 (n : nat) : (term468 n) = (term372 n).
Proof. exact (eq_refl (term468 n)). Qed.
Lemma lem1656980 (n : nat) : term372 n.
Proof. exact (EQ_MP (@lem1656979 n) (@lem1656978 n)). Qed.
Lemma lem1656981 (n : nat) (x : real) : term469 n x.
Proof. exact (@lem1656980 n x). Qed.
Lemma lem1656982 (x : real) (n : nat) : (term469 n x) = (term355 x n).
Proof. exact (eq_refl (term469 n x)). Qed.
Lemma lem1656983 (x : real) (n : nat) : term355 x n.
Proof. exact (EQ_MP (@lem1656982 x n) (@lem1656981 n x)). Qed.
Lemma lem1656985 (x : real) (n : nat) : term355 x n.
Proof. exact (@lem1655353 x n (@lem1656983 x n)). Qed.
Lemma lem1656986 (x : real) (n : nat) (h1 : term333 n) : term366 x n.
Proof. exact (@lem1656985 x n (@lem1655210 n h1)). Qed.
Lemma lem1656987 (n : nat) (x : real) (h1 : term333 n) (h2 : term330 x) : term363 x n.
Proof. exact (@lem1656986 x n h1 (@lem1655205 x h2)). Qed.
Lemma lem1656988 (n : nat) (x : real) (h1 : term354 x n) (h2 : term333 n) (h3 : term330 x) : term359.
Proof. exact (@lem1656987 n x h2 h3 (@lem1655338 x n h1)). Qed.
Lemma lem1656989 (n : nat) (x : real) (h1 : term354 x n) (h2 : term333 n) (h3 : term330 x) : False.
Proof. exact (@lem1656988 n x h1 h2 h3 (@lem1653669)). Qed.
Lemma lem1656990 (n : nat) (x : real) (h1 : term354 x n) (h2 : term333 n) (h3 : term330 x) : (term354 x n) = False.
Proof. exact (prop_ext (fun h4 : term354 x n => @lem1656989 n x h1 h2 h3) (fun h4 : False => @lem1655338 x n h1)). Qed.
Lemma lem1656991 (n : nat) (x : real) (h1 : term354 x n) (h2 : term333 n) (h3 : term330 x) : False.
Proof. exact (EQ_MP (@lem1656990 n x h1 h2 h3) (@lem1655338 x n h1)). Qed.
Lemma lem1656992 (n : nat) (x : real) (h1 : term333 n) (h2 : term330 x) : term353 x n.
Proof. exact (fun h0 : term354 x n => @lem1656991 n x h0 h1 h2). Qed.
Lemma lem1656993 (n : nat) (x : real) (h1 : term333 n) (h2 : term330 x) : ((real_pow x n) = term32) = (term343 x n).
Proof. exact (EQ_MP (@lem1655337 x n) (@lem1656992 n x h1 h2)). Qed.
Lemma lem1657016 (x : real) (h1 : (real_abs x) = term32) : (real_abs x) = term32.
Proof. exact (h1). Qed.
Lemma lem1657017 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1657018 (x : real) (h1 : (real_abs x) = term32) : (term470 x) = term336.
Proof. exact (MK_COMB (@lem1657017) (@lem1657016 x h1)). Qed.
Lemma lem1657019 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1657020 (x : real) (h1 : (real_abs x) = term32) : ((real_abs x) = term32) = (term32 = term32).
Proof. exact (MK_COMB (@lem1657018 x h1) (@lem1657019)). Qed.
Lemma lem1657022 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1657023 (x : real) : (x = x) = True.
Proof. exact (@lem1657022 real x). Qed.
Lemma lem1657024 : (term32 = term32) = True.
Proof. exact (@lem1657023 term32). Qed.
Lemma lem1657025 (x : real) (h1 : (real_abs x) = term32) : ((real_abs x) = term32) = True.
Proof. exact (TRANS (@lem1657020 x h1) (@lem1657024)). Qed.
Lemma lem1657026 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1657027 (x : real) (h1 : (real_abs x) = term32) : (term342 x) = (and True).
Proof. exact (MK_COMB (@lem1657026) (@lem1657025 x h1)). Qed.
Lemma lem1657030 (x : real) (n : nat) : (term340 x n) = (term340 x n).
Proof. exact (eq_refl (term340 x n)). Qed.
Lemma lem1657031 (n : nat) (x : real) (h1 : (real_abs x) = term32) : (term343 x n) = (term471 x n).
Proof. exact (MK_COMB (@lem1657027 x h1) (@lem1657030 x n)). Qed.
Lemma lem1657033 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1657034 (x : real) (n : nat) : (term471 x n) = (term340 x n).
Proof. exact (@lem1657033 (term340 x n)). Qed.
Lemma lem1657037 (n : nat) (x : real) (h1 : (real_abs x) = term32) : (term343 x n) = (term340 x n).
Proof. exact (TRANS (@lem1657031 n x h1) (@lem1657034 x n)). Qed.
Lemma lem1657038 (x : real) (n : nat) : (term337 x n) = (term337 x n).
Proof. exact (eq_refl (term337 x n)). Qed.
Lemma lem1657039 (n : nat) (x : real) (h1 : (real_abs x) = term32) : (((real_pow x n) = term32) = (term343 x n)) = (((real_pow x n) = term32) = (term340 x n)).
Proof. exact (MK_COMB (@lem1657038 x n) (@lem1657037 n x h1)). Qed.
Lemma lem1657042 (n : nat) (x : real) (h1 : (real_abs x) = term32) : (((real_pow x n) = term32) = (term340 x n)) = (((real_pow x n) = term32) = (term343 x n)).
Proof. exact (SYM (@lem1657039 n x h1)). Qed.
Lemma lem1657044 (x : real) (a : real) : term320 x a.
Proof. exact (@lem1655189 x a (@lem1655188 x a)). Qed.
Lemma lem1657045 (x : real) : term472 x.
Proof. exact (@lem1657044 x term32). Qed.
Lemma lem1657046 (x : real) (h1 : (real_abs x) = term32) : term473 x.
Proof. exact (@lem1657045 x (@lem1655204 x h1)). Qed.
Lemma lem1657047 (x : real) (h1 : x = term32) : x = term32.
Proof. exact (h1). Qed.
Lemma lem1657048 (x : real) (h1 : x = term22) : x = term22.
Proof. exact (h1). Qed.
Lemma lem1657049 (n : nat) : (term474 n) = (term474 n).
Proof. exact (eq_refl (term474 n)). Qed.
Lemma lem1657050 (n : nat) (x : real) (h1 : x = term32) : (term475 n x) = (term476 n).
Proof. exact (MK_COMB (@lem1657049 n) (@lem1657047 x h1)). Qed.
Lemma lem1657051 (n : nat) : (term476 n) = (((term477 n) = term32) = (term478 n)).
Proof. exact (eq_refl (term476 n)). Qed.
Lemma lem1657052 (n : nat) (x : real) : (term479 n x) = (term479 n x).
Proof. exact (eq_refl (term479 n x)). Qed.
Lemma lem1657053 (x : real) (n : nat) : ((term475 n x) = (term476 n)) = ((term475 n x) = (((term477 n) = term32) = (term478 n))).
Proof. exact (MK_COMB (@lem1657052 n x) (@lem1657051 n)). Qed.
Lemma lem1657054 (x : real) (n : nat) : (term475 n x) = (((real_pow x n) = term32) = (term340 x n)).
Proof. exact (eq_refl (term475 n x)). Qed.
Lemma lem1657055 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1657056 (x : real) (n : nat) : (term479 n x) = (term480 x n).
Proof. exact (MK_COMB (@lem1657055) (@lem1657054 x n)). Qed.
Lemma lem1657057 (n : nat) : (((term477 n) = term32) = (term478 n)) = (((term477 n) = term32) = (term478 n)).
Proof. exact (eq_refl (((term477 n) = term32) = (term478 n))). Qed.
Lemma lem1657058 (x : real) (n : nat) : ((term475 n x) = (((term477 n) = term32) = (term478 n))) = ((((real_pow x n) = term32) = (term340 x n)) = (((term477 n) = term32) = (term478 n))).
Proof. exact (MK_COMB (@lem1657056 x n) (@lem1657057 n)). Qed.
Lemma lem1657059 (x : real) (n : nat) : ((term475 n x) = (term476 n)) = ((((real_pow x n) = term32) = (term340 x n)) = (((term477 n) = term32) = (term478 n))).
Proof. exact (TRANS (@lem1657053 x n) (@lem1657058 x n)). Qed.
Lemma lem1657060 (n : nat) (x : real) (h1 : x = term32) : (((real_pow x n) = term32) = (term340 x n)) = (((term477 n) = term32) = (term478 n)).
Proof. exact (EQ_MP (@lem1657059 x n) (@lem1657050 n x h1)). Qed.
Lemma lem1657061 (n : nat) (x : real) (h1 : x = term32) : (((term477 n) = term32) = (term478 n)) = (((real_pow x n) = term32) = (term340 x n)).
Proof. exact (SYM (@lem1657060 n x h1)). Qed.
Lemma lem1657062 (n : nat) : (term474 n) = (term474 n).
Proof. exact (eq_refl (term474 n)). Qed.
Lemma lem1657063 (n : nat) (x : real) (h1 : x = term22) : (term475 n x) = (term481 n).
Proof. exact (MK_COMB (@lem1657062 n) (@lem1657048 x h1)). Qed.
Lemma lem1657064 (n : nat) : (term481 n) = (((term482 n) = term32) = (term483 n)).
Proof. exact (eq_refl (term481 n)). Qed.
Lemma lem1657065 (n : nat) (x : real) : (term479 n x) = (term479 n x).
Proof. exact (eq_refl (term479 n x)). Qed.
Lemma lem1657066 (x : real) (n : nat) : ((term475 n x) = (term481 n)) = ((term475 n x) = (((term482 n) = term32) = (term483 n))).
Proof. exact (MK_COMB (@lem1657065 n x) (@lem1657064 n)). Qed.
Lemma lem1657067 (x : real) (n : nat) : (term475 n x) = (((real_pow x n) = term32) = (term340 x n)).
Proof. exact (eq_refl (term475 n x)). Qed.
Lemma lem1657068 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1657069 (x : real) (n : nat) : (term479 n x) = (term480 x n).
Proof. exact (MK_COMB (@lem1657068) (@lem1657067 x n)). Qed.
Lemma lem1657070 (n : nat) : (((term482 n) = term32) = (term483 n)) = (((term482 n) = term32) = (term483 n)).
Proof. exact (eq_refl (((term482 n) = term32) = (term483 n))). Qed.
Lemma lem1657071 (x : real) (n : nat) : ((term475 n x) = (((term482 n) = term32) = (term483 n))) = ((((real_pow x n) = term32) = (term340 x n)) = (((term482 n) = term32) = (term483 n))).
Proof. exact (MK_COMB (@lem1657069 x n) (@lem1657070 n)). Qed.
Lemma lem1657072 (x : real) (n : nat) : ((term475 n x) = (term481 n)) = ((((real_pow x n) = term32) = (term340 x n)) = (((term482 n) = term32) = (term483 n))).
Proof. exact (TRANS (@lem1657066 x n) (@lem1657071 x n)). Qed.
Lemma lem1657073 (n : nat) (x : real) (h1 : x = term22) : (((real_pow x n) = term32) = (term340 x n)) = (((term482 n) = term32) = (term483 n)).
Proof. exact (EQ_MP (@lem1657072 x n) (@lem1657063 n x h1)). Qed.
Lemma lem1657074 (n : nat) (x : real) (h1 : x = term22) : (((term482 n) = term32) = (term483 n)) = (((real_pow x n) = term32) = (term340 x n)).
Proof. exact (SYM (@lem1657073 n x h1)). Qed.
Lemma lem1657075 (n : nat) : term484 n.
Proof. exact (@lem1631092 n). Qed.
Lemma lem1657076 (n : nat) : (term484 n) = ((term477 n) = term32).
Proof. exact (eq_refl (term484 n)). Qed.
Lemma lem1657102 (n : nat) : (term477 n) = term32.
Proof. exact (EQ_MP (@lem1657076 n) (@lem1657075 n)). Qed.
Lemma lem1657103 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1657104 (n : nat) : (term485 n) = term336.
Proof. exact (MK_COMB (@lem1657103) (@lem1657102 n)). Qed.
Lemma lem1657105 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1657106 (n : nat) : ((term477 n) = term32) = (term32 = term32).
Proof. exact (MK_COMB (@lem1657104 n) (@lem1657105)). Qed.
Lemma lem1657108 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1657109 (x : real) : (x = x) = True.
Proof. exact (@lem1657108 real x). Qed.
Lemma lem1657110 : (term32 = term32) = True.
Proof. exact (@lem1657109 term32). Qed.
Lemma lem1657111 (n : nat) : ((term477 n) = term32) = True.
Proof. exact (TRANS (@lem1657106 n) (@lem1657110)). Qed.
Lemma lem1657112 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1657113 (n : nat) : (term486 n) = (@eq Prop True).
Proof. exact (MK_COMB (@lem1657112) (@lem1657111 n)). Qed.
Lemma lem1657116 (n : nat) : (term478 n) = (term478 n).
Proof. exact (eq_refl (term478 n)). Qed.
Lemma lem1657117 (n : nat) : (((term477 n) = term32) = (term478 n)) = (True = (term478 n)).
Proof. exact (MK_COMB (@lem1657113 n) (@lem1657116 n)). Qed.
Lemma lem1657119 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem1657120 (n : nat) : (True = (term478 n)) = (term478 n).
Proof. exact (@lem1657119 (term478 n)). Qed.
Lemma lem1657123 (n : nat) : (((term477 n) = term32) = (term478 n)) = (term478 n).
Proof. exact (TRANS (@lem1657117 n) (@lem1657120 n)). Qed.
Lemma lem1657124 (n : nat) : (term478 n) = (((term477 n) = term32) = (term478 n)).
Proof. exact (SYM (@lem1657123 n)). Qed.
Lemma lem1657125 (n : nat) : term484 n.
Proof. exact (@lem1631092 n). Qed.
Lemma lem1657126 (n : nat) : (term484 n) = ((term477 n) = term32).
Proof. exact (eq_refl (term484 n)). Qed.
Lemma lem1657128 (x : real) : term487 x.
Proof. exact (@lem1362863 x). Qed.
Lemma lem1657129 (x : real) : (term487 x) = (term488 x).
Proof. exact (eq_refl (term487 x)). Qed.
Lemma lem1657130 (x : real) : term488 x.
Proof. exact (EQ_MP (@lem1657129 x) (@lem1657128 x)). Qed.
Lemma lem1657131 (x : real) (n : nat) : term489 x n.
Proof. exact (@lem1657130 x n). Qed.
Lemma lem1657132 (x : real) (n : nat) : (term489 x n) = ((term490 x n) = (term491 x n)).
Proof. exact (eq_refl (term489 x n)). Qed.
Lemma lem1657152 (x : real) (n : nat) : (term490 x n) = (term491 x n).
Proof. exact (EQ_MP (@lem1657132 x n) (@lem1657131 x n)). Qed.
Lemma lem1657153 (n : nat) : (term482 n) = (term492 n).
Proof. exact (@lem1657152 term32 n). Qed.
Lemma lem1657155 (n : nat) : (term477 n) = term32.
Proof. exact (EQ_MP (@lem1657126 n) (@lem1657125 n)). Qed.
Lemma lem1657156 (n : nat) : (term493 n) = (term493 n).
Proof. exact (eq_refl (term493 n)). Qed.
Lemma lem1657157 (n : nat) : (term494 n) = (term495 n).
Proof. exact (MK_COMB (@lem1657156 n) (@lem1657155 n)). Qed.
Lemma lem1657159 (n : nat) : (term477 n) = term32.
Proof. exact (EQ_MP (@lem1657126 n) (@lem1657125 n)). Qed.
Lemma lem1657160 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1657161 (n : nat) : (term496 n) = term22.
Proof. exact (MK_COMB (@lem1657160) (@lem1657159 n)). Qed.
Lemma lem1657162 (n : nat) : (term492 n) = (term497 n).
Proof. exact (MK_COMB (@lem1657157 n) (@lem1657161 n)). Qed.
Lemma lem1657163 (n : nat) : (term482 n) = (term497 n).
Proof. exact (TRANS (@lem1657153 n) (@lem1657162 n)). Qed.
Lemma lem1657164 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1657165 (n : nat) : (term498 n) = (term499 n).
Proof. exact (MK_COMB (@lem1657164) (@lem1657163 n)). Qed.
Lemma lem1657166 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1657167 (n : nat) : ((term482 n) = term32) = ((term497 n) = term32).
Proof. exact (MK_COMB (@lem1657165 n) (@lem1657166)). Qed.
Lemma lem1657170 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1657171 (n : nat) : (term500 n) = (term501 n).
Proof. exact (MK_COMB (@lem1657170) (@lem1657167 n)). Qed.
Lemma lem1657174 (n : nat) : (term483 n) = (term483 n).
Proof. exact (eq_refl (term483 n)). Qed.
Lemma lem1657175 (n : nat) : (((term482 n) = term32) = (term483 n)) = (((term497 n) = term32) = (term483 n)).
Proof. exact (MK_COMB (@lem1657171 n) (@lem1657174 n)). Qed.
Lemma lem1657178 (n : nat) : (((term497 n) = term32) = (term483 n)) = (((term482 n) = term32) = (term483 n)).
Proof. exact (SYM (@lem1657175 n)). Qed.
Lemma lem1657179 (_474 : real) (_475 : Prop) (_476 : real -> Prop) (_477 : real) : (term502 _476 _475 _474 _477) = (term503 _474 _475 _476 _477).
Proof. exact (@lem13473 real _474 _475 _476 _477). Qed.
Lemma lem1657180 (_474 : real) (_475 : Prop) (n : nat) (_477 : real) : (term504 n _475 _474 _477) = (term505 _474 _475 n _477).
Proof. exact (@lem1657179 _474 _475 (term506 n) _477). Qed.
Lemma lem1657181 (n : nat) : (term507 n) = (term508 n).
Proof. exact (@lem1657180 term32 (Coq.Arith.PeanoNat.Nat.Even n) n term22). Qed.
Lemma lem1657182 (n : nat) : (term509 n) = ((term22 = term32) = (term483 n)).
Proof. exact (eq_refl (term509 n)). Qed.
Lemma lem1657183 (n : nat) : (term510 n) = (term510 n).
Proof. exact (eq_refl (term510 n)). Qed.
Lemma lem1657184 (n : nat) : (term511 n) = (term512 n).
Proof. exact (MK_COMB (@lem1657183 n) (@lem1657182 n)). Qed.
Lemma lem1657185 (n : nat) : (term513 n) = ((term32 = term32) = (term483 n)).
Proof. exact (eq_refl (term513 n)). Qed.
Lemma lem1657186 (n : nat) : (term514 n) = (term514 n).
Proof. exact (eq_refl (term514 n)). Qed.
Lemma lem1657187 (n : nat) : (term515 n) = (term516 n).
Proof. exact (MK_COMB (@lem1657186 n) (@lem1657185 n)). Qed.
Lemma lem1657188 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1657189 (n : nat) : (term517 n) = (term518 n).
Proof. exact (MK_COMB (@lem1657188) (@lem1657187 n)). Qed.
Lemma lem1657190 (n : nat) : (term508 n) = (term519 n).
Proof. exact (MK_COMB (@lem1657189 n) (@lem1657184 n)). Qed.
Lemma lem1657191 (n : nat) : (term507 n) = (((term497 n) = term32) = (term483 n)).
Proof. exact (eq_refl (term507 n)). Qed.
Lemma lem1657192 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1657193 (n : nat) : (term520 n) = (term521 n).
Proof. exact (MK_COMB (@lem1657192) (@lem1657191 n)). Qed.
Lemma lem1657194 (n : nat) : ((term507 n) = (term508 n)) = ((((term497 n) = term32) = (term483 n)) = (term519 n)).
Proof. exact (MK_COMB (@lem1657193 n) (@lem1657190 n)). Qed.
Lemma lem1657195 (n : nat) : (((term497 n) = term32) = (term483 n)) = (term519 n).
Proof. exact (EQ_MP (@lem1657194 n) (@lem1657181 n)). Qed.
Lemma lem1657196 (n : nat) : (term519 n) = (((term497 n) = term32) = (term483 n)).
Proof. exact (SYM (@lem1657195 n)). Qed.
Lemma lem1657197 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : Coq.Arith.PeanoNat.Nat.Even n.
Proof. exact (h1). Qed.
Lemma lem1657198 (n : nat) : (Coq.Arith.PeanoNat.Nat.Even n) = ((Coq.Arith.PeanoNat.Nat.Even n) = True).
Proof. exact (@lem7 (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem1657199 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : (Coq.Arith.PeanoNat.Nat.Even n) = True.
Proof. exact (EQ_MP (@lem1657198 n) (@lem1657197 n h1)). Qed.
Lemma lem1657200 : term522 = term522.
Proof. exact (eq_refl term522). Qed.
Lemma lem1657201 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : (term523 n) = term524.
Proof. exact (MK_COMB (@lem1657200) (@lem1657199 n h1)). Qed.
Lemma lem1657202 : term524 = ((term32 = term32) = term525).
Proof. exact (eq_refl term524). Qed.
Lemma lem1657203 (n : nat) : (term526 n) = (term526 n).
Proof. exact (eq_refl (term526 n)). Qed.
Lemma lem1657204 (n : nat) : ((term523 n) = term524) = ((term523 n) = ((term32 = term32) = term525)).
Proof. exact (MK_COMB (@lem1657203 n) (@lem1657202)). Qed.
Lemma lem1657205 (n : nat) : (term523 n) = ((term32 = term32) = (term483 n)).
Proof. exact (eq_refl (term523 n)). Qed.
Lemma lem1657206 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1657207 (n : nat) : (term526 n) = (term527 n).
Proof. exact (MK_COMB (@lem1657206) (@lem1657205 n)). Qed.
Lemma lem1657208 : ((term32 = term32) = term525) = ((term32 = term32) = term525).
Proof. exact (eq_refl ((term32 = term32) = term525)). Qed.
Lemma lem1657209 (n : nat) : ((term523 n) = ((term32 = term32) = term525)) = (((term32 = term32) = (term483 n)) = ((term32 = term32) = term525)).
Proof. exact (MK_COMB (@lem1657207 n) (@lem1657208)). Qed.
Lemma lem1657210 (n : nat) : ((term523 n) = term524) = (((term32 = term32) = (term483 n)) = ((term32 = term32) = term525)).
Proof. exact (TRANS (@lem1657204 n) (@lem1657209 n)). Qed.
Lemma lem1657211 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : ((term32 = term32) = (term483 n)) = ((term32 = term32) = term525).
Proof. exact (EQ_MP (@lem1657210 n) (@lem1657201 n h1)). Qed.
Lemma lem1657212 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : ((term32 = term32) = term525) = ((term32 = term32) = (term483 n)).
Proof. exact (SYM (@lem1657211 n h1)). Qed.
Lemma lem1657213 (n : nat) (h1 : term528 n) : term528 n.
Proof. exact (h1). Qed.
Lemma lem1657214 (n : nat) : term529 n.
Proof. exact (@lem82 (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem1657215 (n : nat) (h1 : term528 n) : (Coq.Arith.PeanoNat.Nat.Even n) = False.
Proof. exact (@lem1657214 n (@lem1657213 n h1)). Qed.
Lemma lem1657216 : term530 = term530.
Proof. exact (eq_refl term530). Qed.
Lemma lem1657217 (n : nat) (h1 : term528 n) : (term531 n) = term532.
Proof. exact (MK_COMB (@lem1657216) (@lem1657215 n h1)). Qed.
Lemma lem1657218 : term532 = ((term22 = term32) = term533).
Proof. exact (eq_refl term532). Qed.
Lemma lem1657219 (n : nat) : (term534 n) = (term534 n).
Proof. exact (eq_refl (term534 n)). Qed.
Lemma lem1657220 (n : nat) : ((term531 n) = term532) = ((term531 n) = ((term22 = term32) = term533)).
Proof. exact (MK_COMB (@lem1657219 n) (@lem1657218)). Qed.
Lemma lem1657221 (n : nat) : (term531 n) = ((term22 = term32) = (term483 n)).
Proof. exact (eq_refl (term531 n)). Qed.
Lemma lem1657222 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1657223 (n : nat) : (term534 n) = (term535 n).
Proof. exact (MK_COMB (@lem1657222) (@lem1657221 n)). Qed.
Lemma lem1657224 : ((term22 = term32) = term533) = ((term22 = term32) = term533).
Proof. exact (eq_refl ((term22 = term32) = term533)). Qed.
Lemma lem1657225 (n : nat) : ((term531 n) = ((term22 = term32) = term533)) = (((term22 = term32) = (term483 n)) = ((term22 = term32) = term533)).
Proof. exact (MK_COMB (@lem1657223 n) (@lem1657224)). Qed.
Lemma lem1657226 (n : nat) : ((term531 n) = term532) = (((term22 = term32) = (term483 n)) = ((term22 = term32) = term533)).
Proof. exact (TRANS (@lem1657220 n) (@lem1657225 n)). Qed.
Lemma lem1657227 (n : nat) (h1 : term528 n) : ((term22 = term32) = (term483 n)) = ((term22 = term32) = term533).
Proof. exact (EQ_MP (@lem1657226 n) (@lem1657217 n h1)). Qed.
Lemma lem1657228 (n : nat) (h1 : term528 n) : ((term22 = term32) = term533) = ((term22 = term32) = (term483 n)).
Proof. exact (SYM (@lem1657227 n h1)). Qed.
Lemma lem1657264 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1657265 (x : real) : (x = x) = True.
Proof. exact (@lem1657264 real x). Qed.
Lemma lem1657266 : (term32 = term32) = True.
Proof. exact (@lem1657265 term32). Qed.
Lemma lem1657267 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1657268 : term536 = (@eq Prop True).
Proof. exact (MK_COMB (@lem1657267) (@lem1657266)). Qed.
Lemma lem1657270 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1657271 : term525 = True.
Proof. exact (@lem1657270 term537). Qed.
Lemma lem1657272 : ((term32 = term32) = term525) = (True = True).
Proof. exact (MK_COMB (@lem1657268) (@lem1657271)). Qed.
Lemma lem1657274 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem1657275 : (True = True) = True.
Proof. exact (@lem1657274 True). Qed.
Lemma lem1657276 : ((term32 = term32) = term525) = True.
Proof. exact (TRANS (@lem1657272) (@lem1657275)). Qed.
Lemma lem1657277 : True = ((term32 = term32) = term525).
Proof. exact (SYM (@lem1657276)). Qed.
Lemma lem1657278 : (term32 = term32) = term525.
Proof. exact (EQ_MP (@lem1657277) (@lem0)). Qed.
Lemma lem1657299 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem1657300 : term533 = term538.
Proof. exact (@lem1657299 term537). Qed.
Lemma lem1657301 : term539 = term539.
Proof. exact (eq_refl term539). Qed.
Lemma lem1657302 : ((term22 = term32) = term533) = ((term22 = term32) = term538).
Proof. exact (MK_COMB (@lem1657301) (@lem1657300)). Qed.
Lemma lem1657305 : ((term22 = term32) = term538) = ((term22 = term32) = term533).
Proof. exact (SYM (@lem1657302)). Qed.
Lemma lem1657326 (n : nat) : (term540 n) = (term541 n).
Proof. exact (@lem17362 term542 (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem1657327 : term542 = term543.
Proof. exact (@lem1483521 term8 term32). Qed.
Lemma lem1657333 : term544 = term545.
Proof. exact (@lem1483519 term8 term32). Qed.
Lemma lem1657335 (m : nat) (n : nat) : (term546 m n) = (term547 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1657336 : term548 = term549.
Proof. exact (@lem1657335 term29 term29). Qed.
Lemma lem1657337 : (term30 = (BIT1 0)) = (term31 = term29).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1657338 : term31 = term29.
Proof. exact (EQ_MP (@lem1657337) (@lem940073)). Qed.
Lemma lem1657339 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1657340 : term28 = term32.
Proof. exact (MK_COMB (@lem1657339) (@lem1657338)). Qed.
Lemma lem1657341 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1657342 : term549 = term22.
Proof. exact (MK_COMB (@lem1657341) (@lem1657340)). Qed.
Lemma lem1657343 : term548 = term22.
Proof. exact (TRANS (@lem1657336) (@lem1657342)). Qed.
Lemma lem1657344 : term266 = term266.
Proof. exact (eq_refl term266). Qed.
Lemma lem1657345 : term545 = term550.
Proof. exact (MK_COMB (@lem1657344) (@lem1657343)). Qed.
Lemma lem1657346 : term550 = term22.
Proof. exact (@lem1483448 term22). Qed.
Lemma lem1657347 : term545 = term22.
Proof. exact (TRANS (@lem1657345) (@lem1657346)). Qed.
Lemma lem1657349 : term544 = term22.
Proof. exact (TRANS (@lem1657333) (@lem1657347)). Qed.
Lemma lem1657350 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1657351 : term551 = term552.
Proof. exact (MK_COMB (@lem1657350) (@lem1657349)). Qed.
Lemma lem1657352 : term8 = term8.
Proof. exact (eq_refl term8). Qed.
Lemma lem1657353 : term543 = term553.
Proof. exact (MK_COMB (@lem1657351) (@lem1657352)). Qed.
Lemma lem1657354 : term542 = term553.
Proof. exact (TRANS (@lem1657327) (@lem1657353)). Qed.
Lemma lem1657355 (n : nat) : (term528 n) = (term528 n).
Proof. exact (eq_refl (term528 n)). Qed.
Lemma lem1657356 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1657357 : term554 = term555.
Proof. exact (MK_COMB (@lem1657356) (@lem1657354)). Qed.
Lemma lem1657358 (n : nat) : (term541 n) = (term556 n).
Proof. exact (MK_COMB (@lem1657357) (@lem1657355 n)). Qed.
Lemma lem1657373 (n : nat) : (term540 n) = (term556 n).
Proof. exact (TRANS (@lem1657326 n) (@lem1657358 n)). Qed.
Lemma lem1657377 (n : nat) (h1 : term556 n) : term556 n.
Proof. exact (h1). Qed.
Lemma lem1657379 (n : nat) (h1 : term556 n) : term553.
Proof. exact (proj1 (@lem1657377 n h1)). Qed.
Lemma lem1657381 (m : nat) (n : nat) : (term557 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1657382 : term553 = False.
Proof. exact (@lem1657381 term29 (NUMERAL 0)). Qed.
Lemma lem1657383 (n : nat) (h1 : term556 n) : False.
Proof. exact (EQ_MP (@lem1657382) (@lem1657379 n h1)). Qed.
Lemma lem1657385 (n : nat) (h1 : term556 n) : term556 n.
Proof. exact (h1). Qed.
Lemma lem1657386 (n : nat) (h1 : term556 n) : (term556 n) = False.
Proof. exact (prop_ext (fun h2 : term556 n => @lem1657383 n h1) (fun h2 : False => @lem1657385 n h1)). Qed.
Lemma lem1657387 (n : nat) (h1 : term556 n) : False.
Proof. exact (EQ_MP (@lem1657386 n h1) (@lem1657385 n h1)). Qed.
Lemma lem1657388 (n : nat) (h1 : term540 n) : term540 n.
Proof. exact (h1). Qed.
Lemma lem1657389 (n : nat) (h1 : term540 n) : term556 n.
Proof. exact (EQ_MP (@lem1657373 n) (@lem1657388 n h1)). Qed.
Lemma lem1657390 (n : nat) (h1 : term540 n) : (term556 n) = False.
Proof. exact (prop_ext (fun h2 : term556 n => @lem1657387 n h2) (fun h2 : False => @lem1657389 n h1)). Qed.
Lemma lem1657391 (n : nat) (h1 : term540 n) : False.
Proof. exact (EQ_MP (@lem1657390 n h1) (@lem1657389 n h1)). Qed.
Lemma lem1657392 (n : nat) : term558 n.
Proof. exact (fun h0 : term540 n => @lem1657391 n h0). Qed.
Lemma lem1657393 (n : nat) : term559 n.
Proof. exact (@lem1386578 (term478 n)). Qed.
Lemma lem1657403 : term560 = term537.
Proof. exact (@lem16933 term537). Qed.
Lemma lem1657406 : term561 = term561.
Proof. exact (eq_refl term561). Qed.
Lemma lem1657408 : term562 = term562.
Proof. exact (eq_refl term562). Qed.
Lemma lem1657409 : term563 = term564.
Proof. exact (MK_COMB (@lem1657408) (@lem1657403)). Qed.
Lemma lem1657410 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1657411 : term565 = term566.
Proof. exact (MK_COMB (@lem1657410) (@lem1657409)). Qed.
Lemma lem1657412 : term567 = term568.
Proof. exact (MK_COMB (@lem1657411) (@lem1657406)). Qed.
Lemma lem1657413 : term569 = term567.
Proof. exact (@lem17646 (term22 = term32) term538). Qed.
Lemma lem1657433 : term569 = term568.
Proof. exact (TRANS (@lem1657413) (@lem1657412)). Qed.
Lemma lem1657434 : (term22 = term32) = (term570 = term8).
Proof. exact (@lem1483529 term22 term32). Qed.
Lemma lem1657440 : term570 = term571.
Proof. exact (@lem1483519 term22 term32). Qed.
Lemma lem1657442 (m : nat) (n : nat) : (term546 m n) = (term547 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1657443 : term548 = term549.
Proof. exact (@lem1657442 term29 term29). Qed.
Lemma lem1657444 : (term30 = (BIT1 0)) = (term31 = term29).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1657445 : term31 = term29.
Proof. exact (EQ_MP (@lem1657444) (@lem940073)). Qed.
Lemma lem1657446 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1657447 : term28 = term32.
Proof. exact (MK_COMB (@lem1657446) (@lem1657445)). Qed.
Lemma lem1657448 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1657449 : term549 = term22.
Proof. exact (MK_COMB (@lem1657448) (@lem1657447)). Qed.
Lemma lem1657450 : term548 = term22.
Proof. exact (TRANS (@lem1657443) (@lem1657449)). Qed.
Lemma lem1657451 : term572 = term572.
Proof. exact (eq_refl term572). Qed.
Lemma lem1657452 : term571 = term573.
Proof. exact (MK_COMB (@lem1657451) (@lem1657450)). Qed.
Lemma lem1657453 : term573 = term574.
Proof. exact (@lem1367763 term29 term29). Qed.
Lemma lem1657454 : term575 = term576.
Proof. exact (@lem706885). Qed.
Lemma lem1657455 : (term575 = term576) = (term577 = term578).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term576). Qed.
Lemma lem1657456 : term577 = term578.
Proof. exact (EQ_MP (@lem1657455) (@lem1657454)). Qed.
Lemma lem1657457 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1657458 : term579 = term580.
Proof. exact (MK_COMB (@lem1657457) (@lem1657456)). Qed.
Lemma lem1657459 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1657460 : term574 = term581.
Proof. exact (MK_COMB (@lem1657459) (@lem1657458)). Qed.
Lemma lem1657461 : term573 = term581.
Proof. exact (TRANS (@lem1657453) (@lem1657460)). Qed.
Lemma lem1657462 : term571 = term581.
Proof. exact (TRANS (@lem1657452) (@lem1657461)). Qed.
Lemma lem1657464 : term570 = term581.
Proof. exact (TRANS (@lem1657440) (@lem1657462)). Qed.
Lemma lem1657465 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1657466 : term582 = term583.
Proof. exact (MK_COMB (@lem1657465) (@lem1657464)). Qed.
Lemma lem1657467 : term8 = term8.
Proof. exact (eq_refl term8). Qed.
Lemma lem1657468 : (term570 = term8) = (term581 = term8).
Proof. exact (MK_COMB (@lem1657466) (@lem1657467)). Qed.
Lemma lem1657469 : (term22 = term32) = (term581 = term8).
Proof. exact (TRANS (@lem1657434) (@lem1657468)). Qed.
Lemma lem1657470 : term537 = term584.
Proof. exact (@lem1483521 term8 term22). Qed.
Lemma lem1657476 : term585 = term586.
Proof. exact (@lem1483519 term8 term22). Qed.
Lemma lem1657478 (m : nat) (n : nat) : (term25 m n) = (term26 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1657479 : term27 = term28.
Proof. exact (@lem1657478 term29 term29). Qed.
Lemma lem1657480 : (term30 = (BIT1 0)) = (term31 = term29).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1657481 : term31 = term29.
Proof. exact (EQ_MP (@lem1657480) (@lem940073)). Qed.
Lemma lem1657482 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1657483 : term28 = term32.
Proof. exact (MK_COMB (@lem1657482) (@lem1657481)). Qed.
Lemma lem1657484 : term27 = term32.
Proof. exact (TRANS (@lem1657479) (@lem1657483)). Qed.
Lemma lem1657485 : term266 = term266.
Proof. exact (eq_refl term266). Qed.
Lemma lem1657486 : term586 = term587.
Proof. exact (MK_COMB (@lem1657485) (@lem1657484)). Qed.
Lemma lem1657487 : term587 = term32.
Proof. exact (@lem1483448 term32). Qed.
Lemma lem1657488 : term586 = term32.
Proof. exact (TRANS (@lem1657486) (@lem1657487)). Qed.
Lemma lem1657490 : term585 = term32.
Proof. exact (TRANS (@lem1657476) (@lem1657488)). Qed.
Lemma lem1657491 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1657492 : term588 = term589.
Proof. exact (MK_COMB (@lem1657491) (@lem1657490)). Qed.
Lemma lem1657493 : term8 = term8.
Proof. exact (eq_refl term8). Qed.
Lemma lem1657494 : term584 = term237.
Proof. exact (MK_COMB (@lem1657492) (@lem1657493)). Qed.
Lemma lem1657495 : term537 = term237.
Proof. exact (TRANS (@lem1657470) (@lem1657494)). Qed.
Lemma lem1657496 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1657497 : term562 = term590.
Proof. exact (MK_COMB (@lem1657496) (@lem1657469)). Qed.
Lemma lem1657498 : term564 = term591.
Proof. exact (MK_COMB (@lem1657497) (@lem1657495)). Qed.
Lemma lem1657499 : term592 = term593.
Proof. exact (@lem1483554 term22 term32). Qed.
Lemma lem1657505 : term570 = term571.
Proof. exact (@lem1483519 term22 term32). Qed.
Lemma lem1657507 (m : nat) (n : nat) : (term546 m n) = (term547 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1657508 : term548 = term549.
Proof. exact (@lem1657507 term29 term29). Qed.
Lemma lem1657509 : (term30 = (BIT1 0)) = (term31 = term29).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1657510 : term31 = term29.
Proof. exact (EQ_MP (@lem1657509) (@lem940073)). Qed.
Lemma lem1657511 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1657512 : term28 = term32.
Proof. exact (MK_COMB (@lem1657511) (@lem1657510)). Qed.
Lemma lem1657513 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1657514 : term549 = term22.
Proof. exact (MK_COMB (@lem1657513) (@lem1657512)). Qed.
Lemma lem1657515 : term548 = term22.
Proof. exact (TRANS (@lem1657508) (@lem1657514)). Qed.
Lemma lem1657516 : term572 = term572.
Proof. exact (eq_refl term572). Qed.
Lemma lem1657517 : term571 = term573.
Proof. exact (MK_COMB (@lem1657516) (@lem1657515)). Qed.
Lemma lem1657518 : term573 = term574.
Proof. exact (@lem1367763 term29 term29). Qed.
Lemma lem1657519 : term575 = term576.
Proof. exact (@lem706885). Qed.
Lemma lem1657520 : (term575 = term576) = (term577 = term578).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term576). Qed.
Lemma lem1657521 : term577 = term578.
Proof. exact (EQ_MP (@lem1657520) (@lem1657519)). Qed.
Lemma lem1657522 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1657523 : term579 = term580.
Proof. exact (MK_COMB (@lem1657522) (@lem1657521)). Qed.
Lemma lem1657524 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1657525 : term574 = term581.
Proof. exact (MK_COMB (@lem1657524) (@lem1657523)). Qed.
Lemma lem1657526 : term573 = term581.
Proof. exact (TRANS (@lem1657518) (@lem1657525)). Qed.
Lemma lem1657527 : term571 = term581.
Proof. exact (TRANS (@lem1657517) (@lem1657526)). Qed.
Lemma lem1657529 : term570 = term581.
Proof. exact (TRANS (@lem1657505) (@lem1657527)). Qed.
Lemma lem1657530 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1657531 : term594 = term595.
Proof. exact (MK_COMB (@lem1657530) (@lem1657529)). Qed.
Lemma lem1657532 : term595 = term596.
Proof. exact (@lem1483512 term581). Qed.
Lemma lem1657534 (m : nat) (n : nat) : (term25 m n) = (term26 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1657535 : term596 = term597.
Proof. exact (@lem1657534 term29 term578). Qed.
Lemma lem1657536 : term598 = term576.
Proof. exact (@lem996238 term576). Qed.
Lemma lem1657537 : (term598 = term576) = (term599 = term578).
Proof. exact (@lem1007663 (BIT1 0) term576 term576). Qed.
Lemma lem1657538 : term599 = term578.
Proof. exact (EQ_MP (@lem1657537) (@lem1657536)). Qed.
Lemma lem1657539 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1657540 : term597 = term580.
Proof. exact (MK_COMB (@lem1657539) (@lem1657538)). Qed.
Lemma lem1657541 : term596 = term580.
Proof. exact (TRANS (@lem1657535) (@lem1657540)). Qed.
Lemma lem1657542 : term595 = term580.
Proof. exact (TRANS (@lem1657532) (@lem1657541)). Qed.
Lemma lem1657543 : term600 = term600.
Proof. exact (eq_refl term600). Qed.
Lemma lem1657544 : (term594 = term595) = (term594 = term580).
Proof. exact (MK_COMB (@lem1657543) (@lem1657542)). Qed.
Lemma lem1657545 : term594 = term580.
Proof. exact (EQ_MP (@lem1657544) (@lem1657531)). Qed.
Lemma lem1657546 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1657547 : term601 = term602.
Proof. exact (MK_COMB (@lem1657546) (@lem1657545)). Qed.
Lemma lem1657548 : term8 = term8.
Proof. exact (eq_refl term8). Qed.
Lemma lem1657549 : term603 = term604.
Proof. exact (MK_COMB (@lem1657547) (@lem1657548)). Qed.
Lemma lem1657550 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1657551 : term605 = term606.
Proof. exact (MK_COMB (@lem1657550) (@lem1657529)). Qed.
Lemma lem1657552 : term8 = term8.
Proof. exact (eq_refl term8). Qed.
Lemma lem1657553 : term607 = term608.
Proof. exact (MK_COMB (@lem1657551) (@lem1657552)). Qed.
Lemma lem1657554 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1657555 : term609 = term610.
Proof. exact (MK_COMB (@lem1657554) (@lem1657553)). Qed.
Lemma lem1657556 : term593 = term611.
Proof. exact (MK_COMB (@lem1657555) (@lem1657549)). Qed.
Lemma lem1657557 : term592 = term611.
Proof. exact (TRANS (@lem1657499) (@lem1657556)). Qed.
Lemma lem1657558 : term538 = term612.
Proof. exact (@lem1483531 term22 term8). Qed.
Lemma lem1657564 : term613 = term614.
Proof. exact (@lem1483519 term22 term8). Qed.
Lemma lem1657566 (x : nat) : (term118 x) = term8.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1657567 : term119 = term8.
Proof. exact (@lem1657566 term29). Qed.
Lemma lem1657568 : term572 = term572.
Proof. exact (eq_refl term572). Qed.
Lemma lem1657569 : term614 = term615.
Proof. exact (MK_COMB (@lem1657568) (@lem1657567)). Qed.
Lemma lem1657570 : term615 = term22.
Proof. exact (@lem1483450 term22). Qed.
Lemma lem1657571 : term614 = term22.
Proof. exact (TRANS (@lem1657569) (@lem1657570)). Qed.
Lemma lem1657573 : term613 = term22.
Proof. exact (TRANS (@lem1657564) (@lem1657571)). Qed.
Lemma lem1657574 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1657575 : term616 = term617.
Proof. exact (MK_COMB (@lem1657574) (@lem1657573)). Qed.
Lemma lem1657576 : term8 = term8.
Proof. exact (eq_refl term8). Qed.
Lemma lem1657577 : term612 = term618.
Proof. exact (MK_COMB (@lem1657575) (@lem1657576)). Qed.
Lemma lem1657578 : term538 = term618.
Proof. exact (TRANS (@lem1657558) (@lem1657577)). Qed.
Lemma lem1657579 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1657580 : term619 = term620.
Proof. exact (MK_COMB (@lem1657579) (@lem1657557)). Qed.
Lemma lem1657581 : term561 = term621.
Proof. exact (MK_COMB (@lem1657580) (@lem1657578)). Qed.
Lemma lem1657582 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1657583 : term566 = term622.
Proof. exact (MK_COMB (@lem1657582) (@lem1657498)). Qed.
Lemma lem1657584 : term568 = term623.
Proof. exact (MK_COMB (@lem1657583) (@lem1657581)). Qed.
Lemma lem1657591 : term569 = term623.
Proof. exact (TRANS (@lem1657433) (@lem1657584)). Qed.
Lemma lem1657608 : term621 = term624.
Proof. exact (@lem19367 term608 term604 term618). Qed.
Lemma lem1657617 : term622 = term622.
Proof. exact (eq_refl term622). Qed.
Lemma lem1657618 : term623 = term625.
Proof. exact (MK_COMB (@lem1657617) (@lem1657608)). Qed.
Lemma lem1657619 : term569 = term625.
Proof. exact (TRANS (@lem1657591) (@lem1657618)). Qed.
Lemma lem1657635 (h1 : term625) : term625.
Proof. exact (h1). Qed.
Lemma lem1657636 (h1 : term591) : term591.
Proof. exact (h1). Qed.
Lemma lem1657638 (h1 : term591) : term581 = term8.
Proof. exact (proj1 (@lem1657636 h1)). Qed.
Lemma lem1657640 (m : nat) (n : nat) : ((term626 m) = (real_of_num n)) = (term627 m n).
Proof. exact (proj1 (@lem1366974 m n)). Qed.
Lemma lem1657641 : (term581 = term8) = term628.
Proof. exact (@lem1657640 term578 (NUMERAL 0)). Qed.
Lemma lem1657642 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem1657643 : term629 = term576.
Proof. exact (@lem912803). Qed.
Lemma lem1657644 (h1 : term629 = term576) : (term578 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 (BIT1 0) 0 term576 h1). Qed.
Lemma lem1657645 : (term629 = term576) = ((term578 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term629 = term576 => @lem1657644 h1) (fun h1 : (term578 = (NUMERAL 0)) = False => @lem1657643)). Qed.
Lemma lem1657646 : (term578 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem1657645) (@lem1657643)). Qed.
Lemma lem1657647 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1657648 : term630 = (and False).
Proof. exact (MK_COMB (@lem1657647) (@lem1657646)). Qed.
Lemma lem1657649 : term628 = (False /\ True).
Proof. exact (MK_COMB (@lem1657648) (@lem1657642)). Qed.
Lemma lem1657651 : (False /\ True) = False.
Proof. exact (proj1 (@lem1365105)). Qed.
Lemma lem1657652 : term628 = False.
Proof. exact (TRANS (@lem1657649) (@lem1657651)). Qed.
Lemma lem1657653 : (term581 = term8) = False.
Proof. exact (TRANS (@lem1657641) (@lem1657652)). Qed.
Lemma lem1657654 (h1 : term591) : False.
Proof. exact (EQ_MP (@lem1657653) (@lem1657638 h1)). Qed.
Lemma lem1657655 (h1 : term624) : term624.
Proof. exact (h1). Qed.
Lemma lem1657656 (h1 : term631) : term631.
Proof. exact (h1). Qed.
Lemma lem1657658 (h1 : term631) : term608.
Proof. exact (proj1 (@lem1657656 h1)). Qed.
Lemma lem1657660 (m : nat) (n : nat) : (term557 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1657661 : term608 = False.
Proof. exact (@lem1657660 term578 (NUMERAL 0)). Qed.
Lemma lem1657662 (h1 : term631) : False.
Proof. exact (EQ_MP (@lem1657661) (@lem1657658 h1)). Qed.
Lemma lem1657663 (h1 : term632) : term632.
Proof. exact (h1). Qed.
Lemma lem1657664 (h1 : term632) : term618.
Proof. exact (proj2 (@lem1657663 h1)). Qed.
Lemma lem1657667 (m : nat) (n : nat) : (term633 m n) = (term627 m n).
Proof. exact (proj2 (@lem1365990 m n)). Qed.
Lemma lem1657668 : term618 = term634.
Proof. exact (@lem1657667 term29 (NUMERAL 0)). Qed.
Lemma lem1657669 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem1657670 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1657671 (h1 : term239 = (BIT1 0)) : (term29 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem1657672 : (term239 = (BIT1 0)) = ((term29 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem1657671 h1) (fun h1 : (term29 = (NUMERAL 0)) = False => @lem1657670)). Qed.
Lemma lem1657673 : (term29 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem1657672) (@lem1657670)). Qed.
Lemma lem1657674 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1657675 : term635 = (and False).
Proof. exact (MK_COMB (@lem1657674) (@lem1657673)). Qed.
Lemma lem1657676 : term634 = (False /\ True).
Proof. exact (MK_COMB (@lem1657675) (@lem1657669)). Qed.
Lemma lem1657678 : (False /\ True) = False.
Proof. exact (proj1 (@lem1365105)). Qed.
Lemma lem1657679 : term634 = False.
Proof. exact (TRANS (@lem1657676) (@lem1657678)). Qed.
Lemma lem1657680 : term618 = False.
Proof. exact (TRANS (@lem1657668) (@lem1657679)). Qed.
Lemma lem1657681 (h1 : term632) : False.
Proof. exact (EQ_MP (@lem1657680) (@lem1657664 h1)). Qed.
Lemma lem1657682 (h1 : term624) : False.
Proof. exact (or_elim (@lem1657655 h1) (fun h0 : term631 => @lem1657662 h0) (fun h0 : term632 => @lem1657681 h0)). Qed.
Lemma lem1657683 (h1 : term625) : False.
Proof. exact (or_elim (@lem1657635 h1) (fun h0 : term591 => @lem1657654 h0) (fun h0 : term624 => @lem1657682 h0)). Qed.
Lemma lem1657685 (h1 : term625) : term625.
Proof. exact (h1). Qed.
Lemma lem1657686 (h1 : term625) : term625 = False.
Proof. exact (prop_ext (fun h2 : term625 => @lem1657683 h1) (fun h2 : False => @lem1657685 h1)). Qed.
Lemma lem1657687 (h1 : term625) : False.
Proof. exact (EQ_MP (@lem1657686 h1) (@lem1657685 h1)). Qed.
Lemma lem1657688 (h1 : term569) : term569.
Proof. exact (h1). Qed.
Lemma lem1657689 (h1 : term569) : term625.
Proof. exact (EQ_MP (@lem1657619) (@lem1657688 h1)). Qed.
Lemma lem1657690 (h1 : term569) : term625 = False.
Proof. exact (prop_ext (fun h2 : term625 => @lem1657687 h2) (fun h2 : False => @lem1657689 h1)). Qed.
Lemma lem1657691 (h1 : term569) : False.
Proof. exact (EQ_MP (@lem1657690 h1) (@lem1657689 h1)). Qed.
Lemma lem1657692 : term636.
Proof. exact (fun h0 : term569 => @lem1657691 h0). Qed.
Lemma lem1657693 : term637.
Proof. exact (@lem1386578 ((term22 = term32) = term538)). Qed.
Lemma lem1657694 : (term22 = term32) = term538.
Proof. exact (@lem1657693 (@lem1657692)). Qed.
Lemma lem1657695 : (term22 = term32) = term533.
Proof. exact (EQ_MP (@lem1657305) (@lem1657694)). Qed.
Lemma lem1657696 (n : nat) : term478 n.
Proof. exact (@lem1657393 n (@lem1657392 n)). Qed.
Lemma lem1657697 (n : nat) (h1 : term528 n) : (term22 = term32) = (term483 n).
Proof. exact (EQ_MP (@lem1657228 n h1) (@lem1657695)). Qed.
Lemma lem1657698 (n : nat) (h1 : term528 n) : (term528 n) = ((term22 = term32) = (term483 n)).
Proof. exact (prop_ext (fun h2 : term528 n => @lem1657697 n h1) (fun h2 : (term22 = term32) = (term483 n) => @lem1657213 n h1)). Qed.
Lemma lem1657699 (n : nat) (h1 : term528 n) : (term22 = term32) = (term483 n).
Proof. exact (EQ_MP (@lem1657698 n h1) (@lem1657213 n h1)). Qed.
Lemma lem1657700 (n : nat) : term512 n.
Proof. exact (fun h0 : term528 n => @lem1657699 n h0). Qed.
Lemma lem1657701 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : (term32 = term32) = (term483 n).
Proof. exact (EQ_MP (@lem1657212 n h1) (@lem1657278)). Qed.
Lemma lem1657702 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : (Coq.Arith.PeanoNat.Nat.Even n) = ((term32 = term32) = (term483 n)).
Proof. exact (prop_ext (fun h2 : Coq.Arith.PeanoNat.Nat.Even n => @lem1657701 n h1) (fun h2 : (term32 = term32) = (term483 n) => @lem1657197 n h1)). Qed.
Lemma lem1657703 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : (term32 = term32) = (term483 n).
Proof. exact (EQ_MP (@lem1657702 n h1) (@lem1657197 n h1)). Qed.
Lemma lem1657704 (n : nat) : term516 n.
Proof. exact (fun h0 : Coq.Arith.PeanoNat.Nat.Even n => @lem1657703 n h0). Qed.
Lemma lem1657705 (n : nat) : term519 n.
Proof. exact (conj (@lem1657704 n) (@lem1657700 n)). Qed.
Lemma lem1657706 (n : nat) : ((term497 n) = term32) = (term483 n).
Proof. exact (EQ_MP (@lem1657196 n) (@lem1657705 n)). Qed.
Lemma lem1657707 (n : nat) : ((term482 n) = term32) = (term483 n).
Proof. exact (EQ_MP (@lem1657178 n) (@lem1657706 n)). Qed.
Lemma lem1657708 (n : nat) : ((term477 n) = term32) = (term478 n).
Proof. exact (EQ_MP (@lem1657124 n) (@lem1657696 n)). Qed.
Lemma lem1657709 (n : nat) (x : real) (h1 : x = term22) : ((real_pow x n) = term32) = (term340 x n).
Proof. exact (EQ_MP (@lem1657074 n x h1) (@lem1657707 n)). Qed.
Lemma lem1657710 (n : nat) (x : real) (h1 : x = term32) : ((real_pow x n) = term32) = (term340 x n).
Proof. exact (EQ_MP (@lem1657061 n x h1) (@lem1657708 n)). Qed.
Lemma lem1657711 (n : nat) (x : real) (h1 : (real_abs x) = term32) : ((real_pow x n) = term32) = (term340 x n).
Proof. exact (or_elim (@lem1657046 x h1) (fun h0 : x = term32 => @lem1657710 n x h0) (fun h0 : x = term22 => @lem1657709 n x h0)). Qed.
Lemma lem1657712 (n : nat) (x : real) (h1 : (real_abs x) = term32) : ((real_pow x n) = term32) = (term343 x n).
Proof. exact (EQ_MP (@lem1657042 n x h1) (@lem1657711 n x h1)). Qed.
Lemma lem1657713 (x : real) (n : nat) (h1 : term333 n) : ((real_pow x n) = term32) = (term343 x n).
Proof. exact (or_elim (@lem1655203 x) (fun h0 : (real_abs x) = term32 => @lem1657712 n x h0) (fun h0 : term330 x => @lem1656993 n x h1 h0)). Qed.
Lemma lem1657714 (x : real) (n : nat) (h1 : term333 n) : ((real_pow x n) = term32) = (term348 x n).
Proof. exact (EQ_MP (@lem1655333 x n h1) (@lem1657713 x n h1)). Qed.
Lemma lem1657715 (x : real) (n : nat) : ((real_pow x n) = term32) = (term348 x n).
Proof. exact (or_elim (@lem1655208 n) (fun h0 : n = (NUMERAL 0) => @lem1655284 x n h0) (fun h0 : term333 n => @lem1657714 x n h0)). Qed.
Lemma lem1657720 (x : real) : term638 x.
Proof. exact (fun n : nat => @lem1657715 x n). Qed.
Lemma lem1657725 : term639.
Proof. exact (fun x : real => @lem1657720 x). Qed.
