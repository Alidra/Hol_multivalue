Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_EQ_MUL_LCANCEL_term_abbrevs.
Require Import REAL_ENTIRE_spec.
Require Import REAL_SUB_LDISTRIB_spec.
Require Import REAL_SUB_RZERO_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1396750_spec.
Require Import thm1483436_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483450_spec.
Require Import thm1483460_spec.
Require Import thm1483476_spec.
Require Import thm1483480_spec.
Require Import thm1483508_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483529_spec.
Require Import thm1483554_spec.
Require Import thm1483568_spec.
Require Import thm1483574_spec.
Require Import thm17646_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm19158_spec.
Require Import thm19367_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem1585789 (y : real) (x : real) (z : real) (h1 : (term0 x y z) = (term1 y x z)) : (term0 x y z) = (term1 y x z).
Proof. exact (h1). Qed.
Lemma lem1585790 (y : real) (x : real) (z : real) (h1 : (term0 x y z) = (term1 y x z)) : (term1 y x z) = (term0 x y z).
Proof. exact (SYM (@lem1585789 y x z h1)). Qed.
Lemma lem1585791 (x : real) (y : real) (z : real) (h1 : (term1 y x z) = (term0 x y z)) : (term1 y x z) = (term0 x y z).
Proof. exact (h1). Qed.
Lemma lem1585792 (x : real) (y : real) (z : real) (h1 : (term1 y x z) = (term0 x y z)) : (term0 x y z) = (term1 y x z).
Proof. exact (SYM (@lem1585791 x y z h1)). Qed.
Lemma lem1585793 (x : real) (y : real) (z : real) : ((term0 x y z) = (term1 y x z)) = ((term1 y x z) = (term0 x y z)).
Proof. exact (prop_ext (fun h1 : (term0 x y z) = (term1 y x z) => @lem1585790 y x z h1) (fun h1 : (term1 y x z) = (term0 x y z) => @lem1585792 x y z h1)). Qed.
Lemma lem1585794 (x : real) (y : real) : (term2 y x) = (term3 x y).
Proof. exact (fun_ext (fun z : real => @lem1585793 x y z)). Qed.
Lemma lem1585795 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1585796 (x : real) (y : real) : (term4 y x) = (term5 x y).
Proof. exact (MK_COMB (@lem1585795) (@lem1585794 x y)). Qed.
Lemma lem1585797 (x : real) : (term6 x) = (term7 x).
Proof. exact (fun_ext (fun y : real => @lem1585796 x y)). Qed.
Lemma lem1585798 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1585799 (x : real) : (term8 x) = (term9 x).
Proof. exact (MK_COMB (@lem1585798) (@lem1585797 x)). Qed.
Lemma lem1585800 : term10 = term11.
Proof. exact (fun_ext (fun x : real => @lem1585799 x)). Qed.
Lemma lem1585801 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1585802 : term12 = term13.
Proof. exact (MK_COMB (@lem1585801) (@lem1585800)). Qed.
Lemma lem1585803 : term13.
Proof. exact (EQ_MP (@lem1585802) (@lem1526444)). Qed.
Lemma lem1585804 (x : real) : term14 x.
Proof. exact (@lem1518006 x). Qed.
Lemma lem1585805 (x : real) : (term14 x) = ((term15 x) = x).
Proof. exact (eq_refl (term14 x)). Qed.
Lemma lem1585807 (x : real) : term16 x.
Proof. exact (@lem1382769 x). Qed.
Lemma lem1585808 (x : real) : (term16 x) = (term17 x).
Proof. exact (eq_refl (term16 x)). Qed.
Lemma lem1585809 (x : real) : term17 x.
Proof. exact (EQ_MP (@lem1585808 x) (@lem1585807 x)). Qed.
Lemma lem1585810 (x : real) (y : real) : term18 x y.
Proof. exact (@lem1585809 x y). Qed.
Lemma lem1585811 (x : real) (y : real) : (term18 x y) = (((real_mul x y) = term19) = (term20 x y)).
Proof. exact (eq_refl (term18 x y)). Qed.
Lemma lem1585813 (x : real) : term21 x.
Proof. exact (@lem1585803 x). Qed.
Lemma lem1585814 (x : real) : (term21 x) = (term9 x).
Proof. exact (eq_refl (term21 x)). Qed.
Lemma lem1585815 (x : real) : term9 x.
Proof. exact (EQ_MP (@lem1585814 x) (@lem1585813 x)). Qed.
Lemma lem1585816 (x : real) (y : real) : term22 x y.
Proof. exact (@lem1585815 x y). Qed.
Lemma lem1585817 (x : real) (y : real) : (term22 x y) = (term5 x y).
Proof. exact (eq_refl (term22 x y)). Qed.
Lemma lem1585818 (x : real) (y : real) : term5 x y.
Proof. exact (EQ_MP (@lem1585817 x y) (@lem1585816 x y)). Qed.
Lemma lem1585819 (x : real) (y : real) (z : real) : term23 x y z.
Proof. exact (@lem1585818 x y z). Qed.
Lemma lem1585820 (x : real) (y : real) (z : real) : (term23 x y z) = ((term1 y x z) = (term0 x y z)).
Proof. exact (eq_refl (term23 x y z)). Qed.
Lemma lem1585858 (x : real) (y : real) : (term24 x y) = (term25 x y).
Proof. exact (@lem17646 (x = y) ((real_sub x y) = term19)). Qed.
Lemma lem1585859 (x : real) (y : real) : (x = y) = ((real_sub x y) = term19).
Proof. exact (@lem1483529 x y). Qed.
Lemma lem1585872 (x : real) (y : real) : (real_sub x y) = (term26 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1585873 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1585874 (x : real) (y : real) : (term27 x y) = (term28 x y).
Proof. exact (MK_COMB (@lem1585873) (@lem1585872 x y)). Qed.
Lemma lem1585875 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem1585876 (x : real) (y : real) : ((real_sub x y) = term19) = ((term26 x y) = term19).
Proof. exact (MK_COMB (@lem1585874 x y) (@lem1585875)). Qed.
Lemma lem1585877 (x : real) (y : real) : (x = y) = ((term26 x y) = term19).
Proof. exact (TRANS (@lem1585859 x y) (@lem1585876 x y)). Qed.
Lemma lem1585878 (x : real) (y : real) : (term29 x y) = (term30 x y).
Proof. exact (@lem1483554 (real_sub x y) term19). Qed.
Lemma lem1585879 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem1585892 (x : real) (y : real) : (real_sub x y) = (term26 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1585893 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1585894 (x : real) (y : real) : (term31 x y) = (term32 x y).
Proof. exact (MK_COMB (@lem1585893) (@lem1585892 x y)). Qed.
Lemma lem1585895 (x : real) (y : real) : (term33 x y) = (term34 x y).
Proof. exact (MK_COMB (@lem1585894 x y) (@lem1585879)). Qed.
Lemma lem1585896 (x : real) (y : real) : (term34 x y) = (term35 x y).
Proof. exact (@lem1483519 (term26 x y) term19). Qed.
Lemma lem1585898 (x : nat) : (term36 x) = term19.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1585899 : term37 = term19.
Proof. exact (@lem1585898 term38). Qed.
Lemma lem1585900 (x : real) (y : real) : (term39 x y) = (term39 x y).
Proof. exact (eq_refl (term39 x y)). Qed.
Lemma lem1585901 (x : real) (y : real) : (term35 x y) = (term40 x y).
Proof. exact (MK_COMB (@lem1585900 x y) (@lem1585899)). Qed.
Lemma lem1585902 (x : real) (y : real) : (term40 x y) = (term26 x y).
Proof. exact (@lem1483450 (term26 x y)). Qed.
Lemma lem1585903 (x : real) (y : real) : (term35 x y) = (term26 x y).
Proof. exact (TRANS (@lem1585901 x y) (@lem1585902 x y)). Qed.
Lemma lem1585904 (x : real) (y : real) : (term34 x y) = (term26 x y).
Proof. exact (TRANS (@lem1585896 x y) (@lem1585903 x y)). Qed.
Lemma lem1585905 (x : real) (y : real) : (term33 x y) = (term26 x y).
Proof. exact (TRANS (@lem1585895 x y) (@lem1585904 x y)). Qed.
Lemma lem1585906 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1585907 (x : real) (y : real) : (term41 x y) = (term42 x y).
Proof. exact (MK_COMB (@lem1585906) (@lem1585905 x y)). Qed.
Lemma lem1585908 (x : real) (y : real) : (term42 x y) = (term43 x y).
Proof. exact (@lem1483512 (term26 x y)). Qed.
Lemma lem1585909 (x : real) (y : real) : (term43 x y) = (term44 x y).
Proof. exact (@lem1483508 x term45 (term46 y)). Qed.
Lemma lem1585910 (y : real) : (term47 y) = (term48 y).
Proof. exact (@lem1483476 term45 term45 y). Qed.
Lemma lem1585912 (m : nat) (n : nat) : (term49 m n) = (term50 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1585913 : term51 = term52.
Proof. exact (@lem1585912 term38 term38). Qed.
Lemma lem1585914 : (term53 = (BIT1 0)) = (term54 = term38).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1585915 : term54 = term38.
Proof. exact (EQ_MP (@lem1585914) (@lem940073)). Qed.
Lemma lem1585916 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1585917 : term52 = term55.
Proof. exact (MK_COMB (@lem1585916) (@lem1585915)). Qed.
Lemma lem1585918 : term51 = term55.
Proof. exact (TRANS (@lem1585913) (@lem1585917)). Qed.
Lemma lem1585919 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1585920 : term56 = term57.
Proof. exact (MK_COMB (@lem1585919) (@lem1585918)). Qed.
Lemma lem1585921 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1585922 (y : real) : (term48 y) = (term58 y).
Proof. exact (MK_COMB (@lem1585920) (@lem1585921 y)). Qed.
Lemma lem1585923 (y : real) : (term47 y) = (term58 y).
Proof. exact (TRANS (@lem1585910 y) (@lem1585922 y)). Qed.
Lemma lem1585924 (y : real) : (term58 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1585925 (y : real) : (term47 y) = y.
Proof. exact (TRANS (@lem1585923 y) (@lem1585924 y)). Qed.
Lemma lem1585928 (x : real) : (term59 x) = (term59 x).
Proof. exact (eq_refl (term59 x)). Qed.
Lemma lem1585929 (x : real) (y : real) : (term44 x y) = (term60 x y).
Proof. exact (MK_COMB (@lem1585928 x) (@lem1585925 y)). Qed.
Lemma lem1585930 (x : real) (y : real) : (term43 x y) = (term60 x y).
Proof. exact (TRANS (@lem1585909 x y) (@lem1585929 x y)). Qed.
Lemma lem1585931 (x : real) (y : real) : (term42 x y) = (term60 x y).
Proof. exact (TRANS (@lem1585908 x y) (@lem1585930 x y)). Qed.
Lemma lem1585932 (x : real) (y : real) : (term61 x y) = (term61 x y).
Proof. exact (eq_refl (term61 x y)). Qed.
Lemma lem1585933 (x : real) (y : real) : ((term41 x y) = (term42 x y)) = ((term41 x y) = (term60 x y)).
Proof. exact (MK_COMB (@lem1585932 x y) (@lem1585931 x y)). Qed.
Lemma lem1585934 (x : real) (y : real) : (term41 x y) = (term60 x y).
Proof. exact (EQ_MP (@lem1585933 x y) (@lem1585907 x y)). Qed.
Lemma lem1585935 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1585936 (x : real) (y : real) : (term62 x y) = (term63 x y).
Proof. exact (MK_COMB (@lem1585935) (@lem1585934 x y)). Qed.
Lemma lem1585937 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem1585938 (x : real) (y : real) : (term64 x y) = (term65 x y).
Proof. exact (MK_COMB (@lem1585936 x y) (@lem1585937)). Qed.
Lemma lem1585939 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1585940 (x : real) (y : real) : (term66 x y) = (term67 x y).
Proof. exact (MK_COMB (@lem1585939) (@lem1585905 x y)). Qed.
Lemma lem1585941 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem1585942 (x : real) (y : real) : (term68 x y) = (term69 x y).
Proof. exact (MK_COMB (@lem1585940 x y) (@lem1585941)). Qed.
Lemma lem1585943 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1585944 (x : real) (y : real) : (term70 x y) = (term71 x y).
Proof. exact (MK_COMB (@lem1585943) (@lem1585942 x y)). Qed.
Lemma lem1585945 (x : real) (y : real) : (term30 x y) = (term72 x y).
Proof. exact (MK_COMB (@lem1585944 x y) (@lem1585938 x y)). Qed.
Lemma lem1585946 (x : real) (y : real) : (term29 x y) = (term72 x y).
Proof. exact (TRANS (@lem1585878 x y) (@lem1585945 x y)). Qed.
Lemma lem1585947 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1585948 (x : real) (y : real) : (term73 x y) = (term74 x y).
Proof. exact (MK_COMB (@lem1585947) (@lem1585877 x y)). Qed.
Lemma lem1585949 (x : real) (y : real) : (term75 x y) = (term76 x y).
Proof. exact (MK_COMB (@lem1585948 x y) (@lem1585946 x y)). Qed.
Lemma lem1585950 (x : real) (y : real) : (term77 x y) = (term78 x y).
Proof. exact (@lem1483554 x y). Qed.
Lemma lem1585963 (x : real) (y : real) : (real_sub x y) = (term26 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1585964 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1585965 (x : real) (y : real) : (term79 x y) = (term42 x y).
Proof. exact (MK_COMB (@lem1585964) (@lem1585963 x y)). Qed.
Lemma lem1585966 (x : real) (y : real) : (term42 x y) = (term43 x y).
Proof. exact (@lem1483512 (term26 x y)). Qed.
Lemma lem1585967 (x : real) (y : real) : (term43 x y) = (term44 x y).
Proof. exact (@lem1483508 x term45 (term46 y)). Qed.
Lemma lem1585968 (y : real) : (term47 y) = (term48 y).
Proof. exact (@lem1483476 term45 term45 y). Qed.
Lemma lem1585970 (m : nat) (n : nat) : (term49 m n) = (term50 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1585971 : term51 = term52.
Proof. exact (@lem1585970 term38 term38). Qed.
Lemma lem1585972 : (term53 = (BIT1 0)) = (term54 = term38).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1585973 : term54 = term38.
Proof. exact (EQ_MP (@lem1585972) (@lem940073)). Qed.
Lemma lem1585974 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1585975 : term52 = term55.
Proof. exact (MK_COMB (@lem1585974) (@lem1585973)). Qed.
Lemma lem1585976 : term51 = term55.
Proof. exact (TRANS (@lem1585971) (@lem1585975)). Qed.
Lemma lem1585977 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1585978 : term56 = term57.
Proof. exact (MK_COMB (@lem1585977) (@lem1585976)). Qed.
Lemma lem1585979 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1585980 (y : real) : (term48 y) = (term58 y).
Proof. exact (MK_COMB (@lem1585978) (@lem1585979 y)). Qed.
Lemma lem1585981 (y : real) : (term47 y) = (term58 y).
Proof. exact (TRANS (@lem1585968 y) (@lem1585980 y)). Qed.
Lemma lem1585982 (y : real) : (term58 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1585983 (y : real) : (term47 y) = y.
Proof. exact (TRANS (@lem1585981 y) (@lem1585982 y)). Qed.
Lemma lem1585986 (x : real) : (term59 x) = (term59 x).
Proof. exact (eq_refl (term59 x)). Qed.
Lemma lem1585987 (x : real) (y : real) : (term44 x y) = (term60 x y).
Proof. exact (MK_COMB (@lem1585986 x) (@lem1585983 y)). Qed.
Lemma lem1585988 (x : real) (y : real) : (term43 x y) = (term60 x y).
Proof. exact (TRANS (@lem1585967 x y) (@lem1585987 x y)). Qed.
Lemma lem1585989 (x : real) (y : real) : (term42 x y) = (term60 x y).
Proof. exact (TRANS (@lem1585966 x y) (@lem1585988 x y)). Qed.
Lemma lem1585990 (x : real) (y : real) : (term80 x y) = (term80 x y).
Proof. exact (eq_refl (term80 x y)). Qed.
Lemma lem1585991 (x : real) (y : real) : ((term79 x y) = (term42 x y)) = ((term79 x y) = (term60 x y)).
Proof. exact (MK_COMB (@lem1585990 x y) (@lem1585989 x y)). Qed.
Lemma lem1585992 (x : real) (y : real) : (term79 x y) = (term60 x y).
Proof. exact (EQ_MP (@lem1585991 x y) (@lem1585965 x y)). Qed.
Lemma lem1585993 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1585994 (x : real) (y : real) : (term81 x y) = (term63 x y).
Proof. exact (MK_COMB (@lem1585993) (@lem1585992 x y)). Qed.
Lemma lem1585995 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem1585996 (x : real) (y : real) : (term82 x y) = (term65 x y).
Proof. exact (MK_COMB (@lem1585994 x y) (@lem1585995)). Qed.
Lemma lem1585997 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1585998 (x : real) (y : real) : (term83 x y) = (term67 x y).
Proof. exact (MK_COMB (@lem1585997) (@lem1585963 x y)). Qed.
Lemma lem1585999 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem1586000 (x : real) (y : real) : (term84 x y) = (term69 x y).
Proof. exact (MK_COMB (@lem1585998 x y) (@lem1585999)). Qed.
Lemma lem1586001 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1586002 (x : real) (y : real) : (term85 x y) = (term71 x y).
Proof. exact (MK_COMB (@lem1586001) (@lem1586000 x y)). Qed.
Lemma lem1586003 (x : real) (y : real) : (term78 x y) = (term72 x y).
Proof. exact (MK_COMB (@lem1586002 x y) (@lem1585996 x y)). Qed.
Lemma lem1586004 (x : real) (y : real) : (term77 x y) = (term72 x y).
Proof. exact (TRANS (@lem1585950 x y) (@lem1586003 x y)). Qed.
Lemma lem1586005 (x : real) (y : real) : ((real_sub x y) = term19) = ((term33 x y) = term19).
Proof. exact (@lem1483529 (real_sub x y) term19). Qed.
Lemma lem1586006 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem1586019 (x : real) (y : real) : (real_sub x y) = (term26 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1586020 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1586021 (x : real) (y : real) : (term31 x y) = (term32 x y).
Proof. exact (MK_COMB (@lem1586020) (@lem1586019 x y)). Qed.
Lemma lem1586022 (x : real) (y : real) : (term33 x y) = (term34 x y).
Proof. exact (MK_COMB (@lem1586021 x y) (@lem1586006)). Qed.
Lemma lem1586023 (x : real) (y : real) : (term34 x y) = (term35 x y).
Proof. exact (@lem1483519 (term26 x y) term19). Qed.
Lemma lem1586025 (x : nat) : (term36 x) = term19.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1586026 : term37 = term19.
Proof. exact (@lem1586025 term38). Qed.
Lemma lem1586027 (x : real) (y : real) : (term39 x y) = (term39 x y).
Proof. exact (eq_refl (term39 x y)). Qed.
Lemma lem1586028 (x : real) (y : real) : (term35 x y) = (term40 x y).
Proof. exact (MK_COMB (@lem1586027 x y) (@lem1586026)). Qed.
Lemma lem1586029 (x : real) (y : real) : (term40 x y) = (term26 x y).
Proof. exact (@lem1483450 (term26 x y)). Qed.
Lemma lem1586030 (x : real) (y : real) : (term35 x y) = (term26 x y).
Proof. exact (TRANS (@lem1586028 x y) (@lem1586029 x y)). Qed.
Lemma lem1586031 (x : real) (y : real) : (term34 x y) = (term26 x y).
Proof. exact (TRANS (@lem1586023 x y) (@lem1586030 x y)). Qed.
Lemma lem1586032 (x : real) (y : real) : (term33 x y) = (term26 x y).
Proof. exact (TRANS (@lem1586022 x y) (@lem1586031 x y)). Qed.
Lemma lem1586033 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1586034 (x : real) (y : real) : (term86 x y) = (term28 x y).
Proof. exact (MK_COMB (@lem1586033) (@lem1586032 x y)). Qed.
Lemma lem1586035 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem1586036 (x : real) (y : real) : ((term33 x y) = term19) = ((term26 x y) = term19).
Proof. exact (MK_COMB (@lem1586034 x y) (@lem1586035)). Qed.
Lemma lem1586037 (x : real) (y : real) : ((real_sub x y) = term19) = ((term26 x y) = term19).
Proof. exact (TRANS (@lem1586005 x y) (@lem1586036 x y)). Qed.
Lemma lem1586038 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1586039 (x : real) (y : real) : (term87 x y) = (term88 x y).
Proof. exact (MK_COMB (@lem1586038) (@lem1586004 x y)). Qed.
Lemma lem1586040 (x : real) (y : real) : (term89 x y) = (term90 x y).
Proof. exact (MK_COMB (@lem1586039 x y) (@lem1586037 x y)). Qed.
Lemma lem1586041 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1586042 (x : real) (y : real) : (term91 x y) = (term92 x y).
Proof. exact (MK_COMB (@lem1586041) (@lem1585949 x y)). Qed.
Lemma lem1586043 (x : real) (y : real) : (term25 x y) = (term93 x y).
Proof. exact (MK_COMB (@lem1586042 x y) (@lem1586040 x y)). Qed.
Lemma lem1586050 (x : real) (y : real) : (term24 x y) = (term93 x y).
Proof. exact (TRANS (@lem1585858 x y) (@lem1586043 x y)). Qed.
Lemma lem1586067 (x : real) (y : real) : (term90 x y) = (term94 x y).
Proof. exact (@lem19367 (term69 x y) (term65 x y) ((term26 x y) = term19)). Qed.
Lemma lem1586084 (x : real) (y : real) : (term76 x y) = (term95 x y).
Proof. exact (@lem19158 (term69 x y) ((term26 x y) = term19) (term65 x y)). Qed.
Lemma lem1586085 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1586086 (x : real) (y : real) : (term92 x y) = (term96 x y).
Proof. exact (MK_COMB (@lem1586085) (@lem1586084 x y)). Qed.
Lemma lem1586087 (x : real) (y : real) : (term93 x y) = (term97 x y).
Proof. exact (MK_COMB (@lem1586086 x y) (@lem1586067 x y)). Qed.
Lemma lem1586088 (x : real) (y : real) : (term24 x y) = (term97 x y).
Proof. exact (TRANS (@lem1586050 x y) (@lem1586087 x y)). Qed.
Lemma lem1586110 (x : real) (y : real) (h1 : term97 x y) : term97 x y.
Proof. exact (h1). Qed.
Lemma lem1586111 (x : real) (y : real) (h1 : term95 x y) : term95 x y.
Proof. exact (h1). Qed.
Lemma lem1586112 (x : real) (y : real) (h1 : term98 x y) : term98 x y.
Proof. exact (h1). Qed.
Lemma lem1586113 (x : real) (y : real) (h1 : term98 x y) : term69 x y.
Proof. exact (proj2 (@lem1586112 x y h1)). Qed.
Lemma lem1586114 (x : real) (y : real) (h1 : term98 x y) : (term26 x y) = term19.
Proof. exact (proj1 (@lem1586112 x y h1)). Qed.
Lemma lem1586116 (n : nat) (m : nat) : (term99 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1586117 : term100 = term101.
Proof. exact (@lem1586116 (NUMERAL 0) term38). Qed.
Lemma lem1586118 : term102 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1586119 (h1 : term102 = (BIT1 0)) : term101 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1586120 : (term102 = (BIT1 0)) = (term101 = True).
Proof. exact (prop_ext (fun h1 : term102 = (BIT1 0) => @lem1586119 h1) (fun h1 : term101 = True => @lem1586118)). Qed.
Lemma lem1586121 : term101 = True.
Proof. exact (EQ_MP (@lem1586120) (@lem1586118)). Qed.
Lemma lem1586122 : term100 = True.
Proof. exact (TRANS (@lem1586117) (@lem1586121)). Qed.
Lemma lem1586123 : True = term100.
Proof. exact (SYM (@lem1586122)). Qed.
Lemma lem1586124 : term100.
Proof. exact (EQ_MP (@lem1586123) (@lem0)). Qed.
Lemma lem1586125 (x : real) (y : real) (h1 : term98 x y) : term103 x y.
Proof. exact (conj (@lem1586124) (@lem1586113 x y h1)). Qed.
Lemma lem1586127 (x : real) (y : real) : term104 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1586128 (x : real) (y : real) : term105 x y.
Proof. exact (@lem1586127 term55 (term26 x y)). Qed.
Lemma lem1586129 (x : real) (y : real) (h1 : term98 x y) : term106 x y.
Proof. exact (@lem1586128 x y (@lem1586125 x y h1)). Qed.
Lemma lem1586130 (x : real) (y : real) : (term107 x y) = (term26 x y).
Proof. exact (@lem1483460 (term26 x y)). Qed.
Lemma lem1586131 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1586132 (x : real) (y : real) : (term108 x y) = (term67 x y).
Proof. exact (MK_COMB (@lem1586131) (@lem1586130 x y)). Qed.
Lemma lem1586133 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem1586134 (x : real) (y : real) : (term106 x y) = (term69 x y).
Proof. exact (MK_COMB (@lem1586132 x y) (@lem1586133)). Qed.
Lemma lem1586135 (x : real) (y : real) (h1 : term98 x y) : term69 x y.
Proof. exact (EQ_MP (@lem1586134 x y) (@lem1586129 x y h1)). Qed.
Lemma lem1586137 (y : real) : term109 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1586138 (x : real) (y : real) : term110 x y.
Proof. exact (@lem1586137 (term26 x y)). Qed.
Lemma lem1586139 (x : real) (y : real) (h1 : term98 x y) : term111 x y.
Proof. exact (@lem1586138 x y (@lem1586114 x y h1)). Qed.
Lemma lem1586140 (x : real) (y : real) (h1 : term98 x y) : term112 x y.
Proof. exact (@lem1586139 x y h1 term45). Qed.
Lemma lem1586141 (x : real) (y : real) : (term112 x y) = ((term43 x y) = term19).
Proof. exact (eq_refl (term112 x y)). Qed.
Lemma lem1586142 (x : real) (y : real) (h1 : term98 x y) : (term43 x y) = term19.
Proof. exact (EQ_MP (@lem1586141 x y) (@lem1586140 x y h1)). Qed.
Lemma lem1586143 (x : real) (y : real) : (term43 x y) = (term44 x y).
Proof. exact (@lem1483508 x term45 (term46 y)). Qed.
Lemma lem1586144 (y : real) : (term47 y) = (term48 y).
Proof. exact (@lem1483476 term45 term45 y). Qed.
Lemma lem1586146 (m : nat) (n : nat) : (term49 m n) = (term50 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1586147 : term51 = term52.
Proof. exact (@lem1586146 term38 term38). Qed.
Lemma lem1586148 : (term53 = (BIT1 0)) = (term54 = term38).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1586149 : term54 = term38.
Proof. exact (EQ_MP (@lem1586148) (@lem940073)). Qed.
Lemma lem1586150 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1586151 : term52 = term55.
Proof. exact (MK_COMB (@lem1586150) (@lem1586149)). Qed.
Lemma lem1586152 : term51 = term55.
Proof. exact (TRANS (@lem1586147) (@lem1586151)). Qed.
Lemma lem1586153 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1586154 : term56 = term57.
Proof. exact (MK_COMB (@lem1586153) (@lem1586152)). Qed.
Lemma lem1586155 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1586156 (y : real) : (term48 y) = (term58 y).
Proof. exact (MK_COMB (@lem1586154) (@lem1586155 y)). Qed.
Lemma lem1586157 (y : real) : (term47 y) = (term58 y).
Proof. exact (TRANS (@lem1586144 y) (@lem1586156 y)). Qed.
Lemma lem1586158 (y : real) : (term58 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1586159 (y : real) : (term47 y) = y.
Proof. exact (TRANS (@lem1586157 y) (@lem1586158 y)). Qed.
Lemma lem1586162 (x : real) : (term59 x) = (term59 x).
Proof. exact (eq_refl (term59 x)). Qed.
Lemma lem1586163 (x : real) (y : real) : (term44 x y) = (term60 x y).
Proof. exact (MK_COMB (@lem1586162 x) (@lem1586159 y)). Qed.
Lemma lem1586164 (x : real) (y : real) : (term43 x y) = (term60 x y).
Proof. exact (TRANS (@lem1586143 x y) (@lem1586163 x y)). Qed.
Lemma lem1586165 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1586166 (x : real) (y : real) : (term113 x y) = (term114 x y).
Proof. exact (MK_COMB (@lem1586165) (@lem1586164 x y)). Qed.
Lemma lem1586167 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem1586168 (x : real) (y : real) : ((term43 x y) = term19) = ((term60 x y) = term19).
Proof. exact (MK_COMB (@lem1586166 x y) (@lem1586167)). Qed.
Lemma lem1586169 (x : real) (y : real) (h1 : term98 x y) : (term60 x y) = term19.
Proof. exact (EQ_MP (@lem1586168 x y) (@lem1586142 x y h1)). Qed.
Lemma lem1586170 (x : real) (y : real) (h1 : term98 x y) : term115 x y.
Proof. exact (conj (@lem1586169 x y h1) (@lem1586135 x y h1)). Qed.
Lemma lem1586172 (x : real) (y : real) : term116 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1586173 (x : real) (y : real) : term117 x y.
Proof. exact (@lem1586172 (term60 x y) (term26 x y)). Qed.
Lemma lem1586174 (x : real) (y : real) (h1 : term98 x y) : term118 x y.
Proof. exact (@lem1586173 x y (@lem1586170 x y h1)). Qed.
Lemma lem1586175 (x : real) (y : real) : (term119 x y) = (term120 x y).
Proof. exact (@lem1483480 (term46 x) x y (term46 y)). Qed.
Lemma lem1586176 (x : real) : (term121 x) = (term122 x).
Proof. exact (@lem1483440 term45 x). Qed.
Lemma lem1586178 (m : nat) : (term123 m) = term19.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1586179 : term124 = term19.
Proof. exact (@lem1586178 term38). Qed.
Lemma lem1586180 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1586181 : term125 = term126.
Proof. exact (MK_COMB (@lem1586180) (@lem1586179)). Qed.
Lemma lem1586182 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1586183 (x : real) : (term122 x) = (term127 x).
Proof. exact (MK_COMB (@lem1586181) (@lem1586182 x)). Qed.
Lemma lem1586184 (x : real) : (term121 x) = (term127 x).
Proof. exact (TRANS (@lem1586176 x) (@lem1586183 x)). Qed.
Lemma lem1586185 (x : real) : (term127 x) = term19.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1586186 (x : real) : (term121 x) = term19.
Proof. exact (TRANS (@lem1586184 x) (@lem1586185 x)). Qed.
Lemma lem1586187 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1586188 (x : real) : (term128 x) = term129.
Proof. exact (MK_COMB (@lem1586187) (@lem1586186 x)). Qed.
Lemma lem1586189 (y : real) : (term130 y) = (term122 y).
Proof. exact (@lem1483442 term45 y). Qed.
Lemma lem1586191 (m : nat) : (term123 m) = term19.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1586192 : term124 = term19.
Proof. exact (@lem1586191 term38). Qed.
Lemma lem1586193 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1586194 : term125 = term126.
Proof. exact (MK_COMB (@lem1586193) (@lem1586192)). Qed.
Lemma lem1586195 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1586196 (y : real) : (term122 y) = (term127 y).
Proof. exact (MK_COMB (@lem1586194) (@lem1586195 y)). Qed.
Lemma lem1586197 (y : real) : (term130 y) = (term127 y).
Proof. exact (TRANS (@lem1586189 y) (@lem1586196 y)). Qed.
Lemma lem1586198 (y : real) : (term127 y) = term19.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1586199 (y : real) : (term130 y) = term19.
Proof. exact (TRANS (@lem1586197 y) (@lem1586198 y)). Qed.
Lemma lem1586200 (x : real) (y : real) : (term120 x y) = term131.
Proof. exact (MK_COMB (@lem1586188 x) (@lem1586199 y)). Qed.
Lemma lem1586201 (x : real) (y : real) : (term119 x y) = term131.
Proof. exact (TRANS (@lem1586175 x y) (@lem1586200 x y)). Qed.
Lemma lem1586202 : term131 = term19.
Proof. exact (@lem1483448 term19). Qed.
Lemma lem1586203 (x : real) (y : real) : (term119 x y) = term19.
Proof. exact (TRANS (@lem1586201 x y) (@lem1586202)). Qed.
Lemma lem1586204 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1586205 (x : real) (y : real) : (term132 x y) = term133.
Proof. exact (MK_COMB (@lem1586204) (@lem1586203 x y)). Qed.
Lemma lem1586206 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem1586207 (x : real) (y : real) : (term118 x y) = term134.
Proof. exact (MK_COMB (@lem1586205 x y) (@lem1586206)). Qed.
Lemma lem1586208 (x : real) (y : real) (h1 : term98 x y) : term134.
Proof. exact (EQ_MP (@lem1586207 x y) (@lem1586174 x y h1)). Qed.
Lemma lem1586210 (n : nat) (m : nat) : (term99 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1586211 : term134 = term135.
Proof. exact (@lem1586210 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1586212 : term135 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1586213 : term134 = False.
Proof. exact (TRANS (@lem1586211) (@lem1586212)). Qed.
Lemma lem1586214 (x : real) (y : real) (h1 : term98 x y) : False.
Proof. exact (EQ_MP (@lem1586213) (@lem1586208 x y h1)). Qed.
Lemma lem1586215 (x : real) (y : real) (h1 : term136 x y) : term136 x y.
Proof. exact (h1). Qed.
Lemma lem1586216 (x : real) (y : real) (h1 : term136 x y) : term65 x y.
Proof. exact (proj2 (@lem1586215 x y h1)). Qed.
Lemma lem1586217 (x : real) (y : real) (h1 : term136 x y) : (term26 x y) = term19.
Proof. exact (proj1 (@lem1586215 x y h1)). Qed.
Lemma lem1586219 (n : nat) (m : nat) : (term99 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1586220 : term100 = term101.
Proof. exact (@lem1586219 (NUMERAL 0) term38). Qed.
Lemma lem1586221 : term102 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1586222 (h1 : term102 = (BIT1 0)) : term101 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1586223 : (term102 = (BIT1 0)) = (term101 = True).
Proof. exact (prop_ext (fun h1 : term102 = (BIT1 0) => @lem1586222 h1) (fun h1 : term101 = True => @lem1586221)). Qed.
Lemma lem1586224 : term101 = True.
Proof. exact (EQ_MP (@lem1586223) (@lem1586221)). Qed.
Lemma lem1586225 : term100 = True.
Proof. exact (TRANS (@lem1586220) (@lem1586224)). Qed.
Lemma lem1586226 : True = term100.
Proof. exact (SYM (@lem1586225)). Qed.
Lemma lem1586227 : term100.
Proof. exact (EQ_MP (@lem1586226) (@lem0)). Qed.
Lemma lem1586228 (x : real) (y : real) (h1 : term136 x y) : term137 x y.
Proof. exact (conj (@lem1586227) (@lem1586216 x y h1)). Qed.
Lemma lem1586230 (x : real) (y : real) : term104 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1586231 (x : real) (y : real) : term138 x y.
Proof. exact (@lem1586230 term55 (term60 x y)). Qed.
Lemma lem1586232 (x : real) (y : real) (h1 : term136 x y) : term139 x y.
Proof. exact (@lem1586231 x y (@lem1586228 x y h1)). Qed.
Lemma lem1586233 (x : real) (y : real) : (term140 x y) = (term60 x y).
Proof. exact (@lem1483460 (term60 x y)). Qed.
Lemma lem1586234 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1586235 (x : real) (y : real) : (term141 x y) = (term63 x y).
Proof. exact (MK_COMB (@lem1586234) (@lem1586233 x y)). Qed.
Lemma lem1586236 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem1586237 (x : real) (y : real) : (term139 x y) = (term65 x y).
Proof. exact (MK_COMB (@lem1586235 x y) (@lem1586236)). Qed.
Lemma lem1586238 (x : real) (y : real) (h1 : term136 x y) : term65 x y.
Proof. exact (EQ_MP (@lem1586237 x y) (@lem1586232 x y h1)). Qed.
Lemma lem1586240 (y : real) : term109 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1586241 (x : real) (y : real) : term110 x y.
Proof. exact (@lem1586240 (term26 x y)). Qed.
Lemma lem1586242 (x : real) (y : real) (h1 : term136 x y) : term111 x y.
Proof. exact (@lem1586241 x y (@lem1586217 x y h1)). Qed.
Lemma lem1586243 (x : real) (y : real) (h1 : term136 x y) : term142 x y.
Proof. exact (@lem1586242 x y h1 term55). Qed.
Lemma lem1586244 (x : real) (y : real) : (term142 x y) = ((term107 x y) = term19).
Proof. exact (eq_refl (term142 x y)). Qed.
Lemma lem1586245 (x : real) (y : real) (h1 : term136 x y) : (term107 x y) = term19.
Proof. exact (EQ_MP (@lem1586244 x y) (@lem1586243 x y h1)). Qed.
Lemma lem1586246 (x : real) (y : real) : (term107 x y) = (term26 x y).
Proof. exact (@lem1483460 (term26 x y)). Qed.
Lemma lem1586247 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1586248 (x : real) (y : real) : (term143 x y) = (term28 x y).
Proof. exact (MK_COMB (@lem1586247) (@lem1586246 x y)). Qed.
Lemma lem1586249 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem1586250 (x : real) (y : real) : ((term107 x y) = term19) = ((term26 x y) = term19).
Proof. exact (MK_COMB (@lem1586248 x y) (@lem1586249)). Qed.
Lemma lem1586251 (x : real) (y : real) (h1 : term136 x y) : (term26 x y) = term19.
Proof. exact (EQ_MP (@lem1586250 x y) (@lem1586245 x y h1)). Qed.
Lemma lem1586252 (x : real) (y : real) (h1 : term136 x y) : term136 x y.
Proof. exact (conj (@lem1586251 x y h1) (@lem1586238 x y h1)). Qed.
Lemma lem1586254 (x : real) (y : real) : term116 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1586255 (x : real) (y : real) : term144 x y.
Proof. exact (@lem1586254 (term26 x y) (term60 x y)). Qed.
Lemma lem1586256 (x : real) (y : real) (h1 : term136 x y) : term145 x y.
Proof. exact (@lem1586255 x y (@lem1586252 x y h1)). Qed.
Lemma lem1586257 (x : real) (y : real) : (term146 x y) = (term147 x y).
Proof. exact (@lem1483480 x (term46 x) (term46 y) y). Qed.
Lemma lem1586258 (x : real) : (term130 x) = (term122 x).
Proof. exact (@lem1483442 term45 x). Qed.
Lemma lem1586260 (m : nat) : (term123 m) = term19.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1586261 : term124 = term19.
Proof. exact (@lem1586260 term38). Qed.
Lemma lem1586262 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1586263 : term125 = term126.
Proof. exact (MK_COMB (@lem1586262) (@lem1586261)). Qed.
Lemma lem1586264 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1586265 (x : real) : (term122 x) = (term127 x).
Proof. exact (MK_COMB (@lem1586263) (@lem1586264 x)). Qed.
Lemma lem1586266 (x : real) : (term130 x) = (term127 x).
Proof. exact (TRANS (@lem1586258 x) (@lem1586265 x)). Qed.
Lemma lem1586267 (x : real) : (term127 x) = term19.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1586268 (x : real) : (term130 x) = term19.
Proof. exact (TRANS (@lem1586266 x) (@lem1586267 x)). Qed.
Lemma lem1586269 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1586270 (x : real) : (term148 x) = term129.
Proof. exact (MK_COMB (@lem1586269) (@lem1586268 x)). Qed.
Lemma lem1586271 (y : real) : (term121 y) = (term122 y).
Proof. exact (@lem1483440 term45 y). Qed.
Lemma lem1586273 (m : nat) : (term123 m) = term19.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1586274 : term124 = term19.
Proof. exact (@lem1586273 term38). Qed.
Lemma lem1586275 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1586276 : term125 = term126.
Proof. exact (MK_COMB (@lem1586275) (@lem1586274)). Qed.
Lemma lem1586277 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1586278 (y : real) : (term122 y) = (term127 y).
Proof. exact (MK_COMB (@lem1586276) (@lem1586277 y)). Qed.
Lemma lem1586279 (y : real) : (term121 y) = (term127 y).
Proof. exact (TRANS (@lem1586271 y) (@lem1586278 y)). Qed.
Lemma lem1586280 (y : real) : (term127 y) = term19.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1586281 (y : real) : (term121 y) = term19.
Proof. exact (TRANS (@lem1586279 y) (@lem1586280 y)). Qed.
Lemma lem1586282 (x : real) (y : real) : (term147 x y) = term131.
Proof. exact (MK_COMB (@lem1586270 x) (@lem1586281 y)). Qed.
Lemma lem1586283 (x : real) (y : real) : (term146 x y) = term131.
Proof. exact (TRANS (@lem1586257 x y) (@lem1586282 x y)). Qed.
Lemma lem1586284 : term131 = term19.
Proof. exact (@lem1483448 term19). Qed.
Lemma lem1586285 (x : real) (y : real) : (term146 x y) = term19.
Proof. exact (TRANS (@lem1586283 x y) (@lem1586284)). Qed.
Lemma lem1586286 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1586287 (x : real) (y : real) : (term149 x y) = term133.
Proof. exact (MK_COMB (@lem1586286) (@lem1586285 x y)). Qed.
Lemma lem1586288 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem1586289 (x : real) (y : real) : (term145 x y) = term134.
Proof. exact (MK_COMB (@lem1586287 x y) (@lem1586288)). Qed.
Lemma lem1586290 (x : real) (y : real) (h1 : term136 x y) : term134.
Proof. exact (EQ_MP (@lem1586289 x y) (@lem1586256 x y h1)). Qed.
Lemma lem1586292 (n : nat) (m : nat) : (term99 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1586293 : term134 = term135.
Proof. exact (@lem1586292 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1586294 : term135 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1586295 : term134 = False.
Proof. exact (TRANS (@lem1586293) (@lem1586294)). Qed.
Lemma lem1586296 (x : real) (y : real) (h1 : term136 x y) : False.
Proof. exact (EQ_MP (@lem1586295) (@lem1586290 x y h1)). Qed.
Lemma lem1586297 (x : real) (y : real) (h1 : term95 x y) : False.
Proof. exact (or_elim (@lem1586111 x y h1) (fun h0 : term98 x y => @lem1586214 x y h0) (fun h0 : term136 x y => @lem1586296 x y h0)). Qed.
Lemma lem1586298 (x : real) (y : real) (h1 : term94 x y) : term94 x y.
Proof. exact (h1). Qed.
Lemma lem1586299 (x : real) (y : real) (h1 : term150 x y) : term150 x y.
Proof. exact (h1). Qed.
Lemma lem1586300 (x : real) (y : real) (h1 : term150 x y) : (term26 x y) = term19.
Proof. exact (proj2 (@lem1586299 x y h1)). Qed.
Lemma lem1586301 (x : real) (y : real) (h1 : term150 x y) : term69 x y.
Proof. exact (proj1 (@lem1586299 x y h1)). Qed.
Lemma lem1586303 (n : nat) (m : nat) : (term99 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1586304 : term100 = term101.
Proof. exact (@lem1586303 (NUMERAL 0) term38). Qed.
Lemma lem1586305 : term102 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1586306 (h1 : term102 = (BIT1 0)) : term101 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1586307 : (term102 = (BIT1 0)) = (term101 = True).
Proof. exact (prop_ext (fun h1 : term102 = (BIT1 0) => @lem1586306 h1) (fun h1 : term101 = True => @lem1586305)). Qed.
Lemma lem1586308 : term101 = True.
Proof. exact (EQ_MP (@lem1586307) (@lem1586305)). Qed.
Lemma lem1586309 : term100 = True.
Proof. exact (TRANS (@lem1586304) (@lem1586308)). Qed.
Lemma lem1586310 : True = term100.
Proof. exact (SYM (@lem1586309)). Qed.
Lemma lem1586311 : term100.
Proof. exact (EQ_MP (@lem1586310) (@lem0)). Qed.
Lemma lem1586312 (x : real) (y : real) (h1 : term150 x y) : term103 x y.
Proof. exact (conj (@lem1586311) (@lem1586301 x y h1)). Qed.
Lemma lem1586314 (x : real) (y : real) : term104 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1586315 (x : real) (y : real) : term105 x y.
Proof. exact (@lem1586314 term55 (term26 x y)). Qed.
Lemma lem1586316 (x : real) (y : real) (h1 : term150 x y) : term106 x y.
Proof. exact (@lem1586315 x y (@lem1586312 x y h1)). Qed.
Lemma lem1586317 (x : real) (y : real) : (term107 x y) = (term26 x y).
Proof. exact (@lem1483460 (term26 x y)). Qed.
Lemma lem1586318 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1586319 (x : real) (y : real) : (term108 x y) = (term67 x y).
Proof. exact (MK_COMB (@lem1586318) (@lem1586317 x y)). Qed.
Lemma lem1586320 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem1586321 (x : real) (y : real) : (term106 x y) = (term69 x y).
Proof. exact (MK_COMB (@lem1586319 x y) (@lem1586320)). Qed.
Lemma lem1586322 (x : real) (y : real) (h1 : term150 x y) : term69 x y.
Proof. exact (EQ_MP (@lem1586321 x y) (@lem1586316 x y h1)). Qed.
Lemma lem1586324 (y : real) : term109 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1586325 (x : real) (y : real) : term110 x y.
Proof. exact (@lem1586324 (term26 x y)). Qed.
Lemma lem1586326 (x : real) (y : real) (h1 : term150 x y) : term111 x y.
Proof. exact (@lem1586325 x y (@lem1586300 x y h1)). Qed.
Lemma lem1586327 (x : real) (y : real) (h1 : term150 x y) : term112 x y.
Proof. exact (@lem1586326 x y h1 term45). Qed.
Lemma lem1586328 (x : real) (y : real) : (term112 x y) = ((term43 x y) = term19).
Proof. exact (eq_refl (term112 x y)). Qed.
Lemma lem1586329 (x : real) (y : real) (h1 : term150 x y) : (term43 x y) = term19.
Proof. exact (EQ_MP (@lem1586328 x y) (@lem1586327 x y h1)). Qed.
Lemma lem1586330 (x : real) (y : real) : (term43 x y) = (term44 x y).
Proof. exact (@lem1483508 x term45 (term46 y)). Qed.
Lemma lem1586331 (y : real) : (term47 y) = (term48 y).
Proof. exact (@lem1483476 term45 term45 y). Qed.
Lemma lem1586333 (m : nat) (n : nat) : (term49 m n) = (term50 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1586334 : term51 = term52.
Proof. exact (@lem1586333 term38 term38). Qed.
Lemma lem1586335 : (term53 = (BIT1 0)) = (term54 = term38).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1586336 : term54 = term38.
Proof. exact (EQ_MP (@lem1586335) (@lem940073)). Qed.
Lemma lem1586337 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1586338 : term52 = term55.
Proof. exact (MK_COMB (@lem1586337) (@lem1586336)). Qed.
Lemma lem1586339 : term51 = term55.
Proof. exact (TRANS (@lem1586334) (@lem1586338)). Qed.
Lemma lem1586340 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1586341 : term56 = term57.
Proof. exact (MK_COMB (@lem1586340) (@lem1586339)). Qed.
Lemma lem1586342 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1586343 (y : real) : (term48 y) = (term58 y).
Proof. exact (MK_COMB (@lem1586341) (@lem1586342 y)). Qed.
Lemma lem1586344 (y : real) : (term47 y) = (term58 y).
Proof. exact (TRANS (@lem1586331 y) (@lem1586343 y)). Qed.
Lemma lem1586345 (y : real) : (term58 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1586346 (y : real) : (term47 y) = y.
Proof. exact (TRANS (@lem1586344 y) (@lem1586345 y)). Qed.
Lemma lem1586349 (x : real) : (term59 x) = (term59 x).
Proof. exact (eq_refl (term59 x)). Qed.
Lemma lem1586350 (x : real) (y : real) : (term44 x y) = (term60 x y).
Proof. exact (MK_COMB (@lem1586349 x) (@lem1586346 y)). Qed.
Lemma lem1586351 (x : real) (y : real) : (term43 x y) = (term60 x y).
Proof. exact (TRANS (@lem1586330 x y) (@lem1586350 x y)). Qed.
Lemma lem1586352 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1586353 (x : real) (y : real) : (term113 x y) = (term114 x y).
Proof. exact (MK_COMB (@lem1586352) (@lem1586351 x y)). Qed.
Lemma lem1586354 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem1586355 (x : real) (y : real) : ((term43 x y) = term19) = ((term60 x y) = term19).
Proof. exact (MK_COMB (@lem1586353 x y) (@lem1586354)). Qed.
Lemma lem1586356 (x : real) (y : real) (h1 : term150 x y) : (term60 x y) = term19.
Proof. exact (EQ_MP (@lem1586355 x y) (@lem1586329 x y h1)). Qed.
Lemma lem1586357 (x : real) (y : real) (h1 : term150 x y) : term115 x y.
Proof. exact (conj (@lem1586356 x y h1) (@lem1586322 x y h1)). Qed.
Lemma lem1586359 (x : real) (y : real) : term116 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1586360 (x : real) (y : real) : term117 x y.
Proof. exact (@lem1586359 (term60 x y) (term26 x y)). Qed.
Lemma lem1586361 (x : real) (y : real) (h1 : term150 x y) : term118 x y.
Proof. exact (@lem1586360 x y (@lem1586357 x y h1)). Qed.
Lemma lem1586362 (x : real) (y : real) : (term119 x y) = (term120 x y).
Proof. exact (@lem1483480 (term46 x) x y (term46 y)). Qed.
Lemma lem1586363 (x : real) : (term121 x) = (term122 x).
Proof. exact (@lem1483440 term45 x). Qed.
Lemma lem1586365 (m : nat) : (term123 m) = term19.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1586366 : term124 = term19.
Proof. exact (@lem1586365 term38). Qed.
Lemma lem1586367 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1586368 : term125 = term126.
Proof. exact (MK_COMB (@lem1586367) (@lem1586366)). Qed.
Lemma lem1586369 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1586370 (x : real) : (term122 x) = (term127 x).
Proof. exact (MK_COMB (@lem1586368) (@lem1586369 x)). Qed.
Lemma lem1586371 (x : real) : (term121 x) = (term127 x).
Proof. exact (TRANS (@lem1586363 x) (@lem1586370 x)). Qed.
Lemma lem1586372 (x : real) : (term127 x) = term19.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1586373 (x : real) : (term121 x) = term19.
Proof. exact (TRANS (@lem1586371 x) (@lem1586372 x)). Qed.
Lemma lem1586374 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1586375 (x : real) : (term128 x) = term129.
Proof. exact (MK_COMB (@lem1586374) (@lem1586373 x)). Qed.
Lemma lem1586376 (y : real) : (term130 y) = (term122 y).
Proof. exact (@lem1483442 term45 y). Qed.
Lemma lem1586378 (m : nat) : (term123 m) = term19.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1586379 : term124 = term19.
Proof. exact (@lem1586378 term38). Qed.
Lemma lem1586380 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1586381 : term125 = term126.
Proof. exact (MK_COMB (@lem1586380) (@lem1586379)). Qed.
Lemma lem1586382 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1586383 (y : real) : (term122 y) = (term127 y).
Proof. exact (MK_COMB (@lem1586381) (@lem1586382 y)). Qed.
Lemma lem1586384 (y : real) : (term130 y) = (term127 y).
Proof. exact (TRANS (@lem1586376 y) (@lem1586383 y)). Qed.
Lemma lem1586385 (y : real) : (term127 y) = term19.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1586386 (y : real) : (term130 y) = term19.
Proof. exact (TRANS (@lem1586384 y) (@lem1586385 y)). Qed.
Lemma lem1586387 (x : real) (y : real) : (term120 x y) = term131.
Proof. exact (MK_COMB (@lem1586375 x) (@lem1586386 y)). Qed.
Lemma lem1586388 (x : real) (y : real) : (term119 x y) = term131.
Proof. exact (TRANS (@lem1586362 x y) (@lem1586387 x y)). Qed.
Lemma lem1586389 : term131 = term19.
Proof. exact (@lem1483448 term19). Qed.
Lemma lem1586390 (x : real) (y : real) : (term119 x y) = term19.
Proof. exact (TRANS (@lem1586388 x y) (@lem1586389)). Qed.
Lemma lem1586391 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1586392 (x : real) (y : real) : (term132 x y) = term133.
Proof. exact (MK_COMB (@lem1586391) (@lem1586390 x y)). Qed.
Lemma lem1586393 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem1586394 (x : real) (y : real) : (term118 x y) = term134.
Proof. exact (MK_COMB (@lem1586392 x y) (@lem1586393)). Qed.
Lemma lem1586395 (x : real) (y : real) (h1 : term150 x y) : term134.
Proof. exact (EQ_MP (@lem1586394 x y) (@lem1586361 x y h1)). Qed.
Lemma lem1586397 (n : nat) (m : nat) : (term99 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1586398 : term134 = term135.
Proof. exact (@lem1586397 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1586399 : term135 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1586400 : term134 = False.
Proof. exact (TRANS (@lem1586398) (@lem1586399)). Qed.
Lemma lem1586401 (x : real) (y : real) (h1 : term150 x y) : False.
Proof. exact (EQ_MP (@lem1586400) (@lem1586395 x y h1)). Qed.
Lemma lem1586402 (x : real) (y : real) (h1 : term151 x y) : term151 x y.
Proof. exact (h1). Qed.
Lemma lem1586403 (x : real) (y : real) (h1 : term151 x y) : (term26 x y) = term19.
Proof. exact (proj2 (@lem1586402 x y h1)). Qed.
Lemma lem1586404 (x : real) (y : real) (h1 : term151 x y) : term65 x y.
Proof. exact (proj1 (@lem1586402 x y h1)). Qed.
Lemma lem1586406 (n : nat) (m : nat) : (term99 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1586407 : term100 = term101.
Proof. exact (@lem1586406 (NUMERAL 0) term38). Qed.
Lemma lem1586408 : term102 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1586409 (h1 : term102 = (BIT1 0)) : term101 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1586410 : (term102 = (BIT1 0)) = (term101 = True).
Proof. exact (prop_ext (fun h1 : term102 = (BIT1 0) => @lem1586409 h1) (fun h1 : term101 = True => @lem1586408)). Qed.
Lemma lem1586411 : term101 = True.
Proof. exact (EQ_MP (@lem1586410) (@lem1586408)). Qed.
Lemma lem1586412 : term100 = True.
Proof. exact (TRANS (@lem1586407) (@lem1586411)). Qed.
Lemma lem1586413 : True = term100.
Proof. exact (SYM (@lem1586412)). Qed.
Lemma lem1586414 : term100.
Proof. exact (EQ_MP (@lem1586413) (@lem0)). Qed.
Lemma lem1586415 (x : real) (y : real) (h1 : term151 x y) : term137 x y.
Proof. exact (conj (@lem1586414) (@lem1586404 x y h1)). Qed.
Lemma lem1586417 (x : real) (y : real) : term104 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1586418 (x : real) (y : real) : term138 x y.
Proof. exact (@lem1586417 term55 (term60 x y)). Qed.
Lemma lem1586419 (x : real) (y : real) (h1 : term151 x y) : term139 x y.
Proof. exact (@lem1586418 x y (@lem1586415 x y h1)). Qed.
Lemma lem1586420 (x : real) (y : real) : (term140 x y) = (term60 x y).
Proof. exact (@lem1483460 (term60 x y)). Qed.
Lemma lem1586421 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1586422 (x : real) (y : real) : (term141 x y) = (term63 x y).
Proof. exact (MK_COMB (@lem1586421) (@lem1586420 x y)). Qed.
Lemma lem1586423 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem1586424 (x : real) (y : real) : (term139 x y) = (term65 x y).
Proof. exact (MK_COMB (@lem1586422 x y) (@lem1586423)). Qed.
Lemma lem1586425 (x : real) (y : real) (h1 : term151 x y) : term65 x y.
Proof. exact (EQ_MP (@lem1586424 x y) (@lem1586419 x y h1)). Qed.
Lemma lem1586427 (y : real) : term109 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1586428 (x : real) (y : real) : term110 x y.
Proof. exact (@lem1586427 (term26 x y)). Qed.
Lemma lem1586429 (x : real) (y : real) (h1 : term151 x y) : term111 x y.
Proof. exact (@lem1586428 x y (@lem1586403 x y h1)). Qed.
Lemma lem1586430 (x : real) (y : real) (h1 : term151 x y) : term142 x y.
Proof. exact (@lem1586429 x y h1 term55). Qed.
Lemma lem1586431 (x : real) (y : real) : (term142 x y) = ((term107 x y) = term19).
Proof. exact (eq_refl (term142 x y)). Qed.
Lemma lem1586432 (x : real) (y : real) (h1 : term151 x y) : (term107 x y) = term19.
Proof. exact (EQ_MP (@lem1586431 x y) (@lem1586430 x y h1)). Qed.
Lemma lem1586433 (x : real) (y : real) : (term107 x y) = (term26 x y).
Proof. exact (@lem1483460 (term26 x y)). Qed.
Lemma lem1586434 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1586435 (x : real) (y : real) : (term143 x y) = (term28 x y).
Proof. exact (MK_COMB (@lem1586434) (@lem1586433 x y)). Qed.
Lemma lem1586436 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem1586437 (x : real) (y : real) : ((term107 x y) = term19) = ((term26 x y) = term19).
Proof. exact (MK_COMB (@lem1586435 x y) (@lem1586436)). Qed.
Lemma lem1586438 (x : real) (y : real) (h1 : term151 x y) : (term26 x y) = term19.
Proof. exact (EQ_MP (@lem1586437 x y) (@lem1586432 x y h1)). Qed.
Lemma lem1586439 (x : real) (y : real) (h1 : term151 x y) : term136 x y.
Proof. exact (conj (@lem1586438 x y h1) (@lem1586425 x y h1)). Qed.
Lemma lem1586441 (x : real) (y : real) : term116 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1586442 (x : real) (y : real) : term144 x y.
Proof. exact (@lem1586441 (term26 x y) (term60 x y)). Qed.
Lemma lem1586443 (x : real) (y : real) (h1 : term151 x y) : term145 x y.
Proof. exact (@lem1586442 x y (@lem1586439 x y h1)). Qed.
Lemma lem1586444 (x : real) (y : real) : (term146 x y) = (term147 x y).
Proof. exact (@lem1483480 x (term46 x) (term46 y) y). Qed.
Lemma lem1586445 (x : real) : (term130 x) = (term122 x).
Proof. exact (@lem1483442 term45 x). Qed.
Lemma lem1586447 (m : nat) : (term123 m) = term19.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1586448 : term124 = term19.
Proof. exact (@lem1586447 term38). Qed.
Lemma lem1586449 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1586450 : term125 = term126.
Proof. exact (MK_COMB (@lem1586449) (@lem1586448)). Qed.
Lemma lem1586451 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1586452 (x : real) : (term122 x) = (term127 x).
Proof. exact (MK_COMB (@lem1586450) (@lem1586451 x)). Qed.
Lemma lem1586453 (x : real) : (term130 x) = (term127 x).
Proof. exact (TRANS (@lem1586445 x) (@lem1586452 x)). Qed.
Lemma lem1586454 (x : real) : (term127 x) = term19.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1586455 (x : real) : (term130 x) = term19.
Proof. exact (TRANS (@lem1586453 x) (@lem1586454 x)). Qed.
Lemma lem1586456 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1586457 (x : real) : (term148 x) = term129.
Proof. exact (MK_COMB (@lem1586456) (@lem1586455 x)). Qed.
Lemma lem1586458 (y : real) : (term121 y) = (term122 y).
Proof. exact (@lem1483440 term45 y). Qed.
Lemma lem1586460 (m : nat) : (term123 m) = term19.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1586461 : term124 = term19.
Proof. exact (@lem1586460 term38). Qed.
Lemma lem1586462 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1586463 : term125 = term126.
Proof. exact (MK_COMB (@lem1586462) (@lem1586461)). Qed.
Lemma lem1586464 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1586465 (y : real) : (term122 y) = (term127 y).
Proof. exact (MK_COMB (@lem1586463) (@lem1586464 y)). Qed.
Lemma lem1586466 (y : real) : (term121 y) = (term127 y).
Proof. exact (TRANS (@lem1586458 y) (@lem1586465 y)). Qed.
Lemma lem1586467 (y : real) : (term127 y) = term19.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1586468 (y : real) : (term121 y) = term19.
Proof. exact (TRANS (@lem1586466 y) (@lem1586467 y)). Qed.
Lemma lem1586469 (x : real) (y : real) : (term147 x y) = term131.
Proof. exact (MK_COMB (@lem1586457 x) (@lem1586468 y)). Qed.
Lemma lem1586470 (x : real) (y : real) : (term146 x y) = term131.
Proof. exact (TRANS (@lem1586444 x y) (@lem1586469 x y)). Qed.
Lemma lem1586471 : term131 = term19.
Proof. exact (@lem1483448 term19). Qed.
Lemma lem1586472 (x : real) (y : real) : (term146 x y) = term19.
Proof. exact (TRANS (@lem1586470 x y) (@lem1586471)). Qed.
Lemma lem1586473 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1586474 (x : real) (y : real) : (term149 x y) = term133.
Proof. exact (MK_COMB (@lem1586473) (@lem1586472 x y)). Qed.
Lemma lem1586475 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem1586476 (x : real) (y : real) : (term145 x y) = term134.
Proof. exact (MK_COMB (@lem1586474 x y) (@lem1586475)). Qed.
Lemma lem1586477 (x : real) (y : real) (h1 : term151 x y) : term134.
Proof. exact (EQ_MP (@lem1586476 x y) (@lem1586443 x y h1)). Qed.
Lemma lem1586479 (n : nat) (m : nat) : (term99 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1586480 : term134 = term135.
Proof. exact (@lem1586479 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1586481 : term135 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1586482 : term134 = False.
Proof. exact (TRANS (@lem1586480) (@lem1586481)). Qed.
Lemma lem1586483 (x : real) (y : real) (h1 : term151 x y) : False.
Proof. exact (EQ_MP (@lem1586482) (@lem1586477 x y h1)). Qed.
Lemma lem1586484 (x : real) (y : real) (h1 : term94 x y) : False.
Proof. exact (or_elim (@lem1586298 x y h1) (fun h0 : term150 x y => @lem1586401 x y h0) (fun h0 : term151 x y => @lem1586483 x y h0)). Qed.
Lemma lem1586485 (x : real) (y : real) (h1 : term97 x y) : False.
Proof. exact (or_elim (@lem1586110 x y h1) (fun h0 : term95 x y => @lem1586297 x y h0) (fun h0 : term94 x y => @lem1586484 x y h0)). Qed.
Lemma lem1586487 (x : real) (y : real) (h1 : term97 x y) : term97 x y.
Proof. exact (h1). Qed.
Lemma lem1586488 (x : real) (y : real) (h1 : term97 x y) : (term97 x y) = False.
Proof. exact (prop_ext (fun h2 : term97 x y => @lem1586485 x y h1) (fun h2 : False => @lem1586487 x y h1)). Qed.
Lemma lem1586489 (x : real) (y : real) (h1 : term97 x y) : False.
Proof. exact (EQ_MP (@lem1586488 x y h1) (@lem1586487 x y h1)). Qed.
Lemma lem1586490 (x : real) (y : real) (h1 : term24 x y) : term24 x y.
Proof. exact (h1). Qed.
Lemma lem1586491 (x : real) (y : real) (h1 : term24 x y) : term97 x y.
Proof. exact (EQ_MP (@lem1586088 x y) (@lem1586490 x y h1)). Qed.
Lemma lem1586492 (x : real) (y : real) (h1 : term24 x y) : (term97 x y) = False.
Proof. exact (prop_ext (fun h2 : term97 x y => @lem1586489 x y h2) (fun h2 : False => @lem1586491 x y h1)). Qed.
Lemma lem1586493 (x : real) (y : real) (h1 : term24 x y) : False.
Proof. exact (EQ_MP (@lem1586492 x y h1) (@lem1586491 x y h1)). Qed.
Lemma lem1586494 (x : real) (y : real) : term152 x y.
Proof. exact (fun h0 : term24 x y => @lem1586493 x y h0). Qed.
Lemma lem1586495 (x : real) (y : real) : term153 x y.
Proof. exact (@lem1386578 ((x = y) = ((real_sub x y) = term19))). Qed.
Lemma lem1586504 (x : real) (y : real) : (x = y) = ((real_sub x y) = term19).
Proof. exact (@lem1586495 x y (@lem1586494 x y)). Qed.
Lemma lem1586505 (y : real) (x : real) (z : real) : ((real_mul x y) = (real_mul x z)) = ((term1 y x z) = term19).
Proof. exact (@lem1586504 (real_mul x y) (real_mul x z)). Qed.
Lemma lem1586506 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1586507 (y : real) (x : real) (z : real) : (term154 y x z) = (term155 y x z).
Proof. exact (MK_COMB (@lem1586506) (@lem1586505 y x z)). Qed.
Lemma lem1586513 (x : real) (y : real) : (x = y) = ((real_sub x y) = term19).
Proof. exact (@lem1586495 x y (@lem1586494 x y)). Qed.
Lemma lem1586514 (x : real) : (x = term19) = ((term15 x) = term19).
Proof. exact (@lem1586513 x term19). Qed.
Lemma lem1586515 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1586516 (x : real) : (term156 x) = (term157 x).
Proof. exact (MK_COMB (@lem1586515) (@lem1586514 x)). Qed.
Lemma lem1586520 (x : real) (y : real) : (x = y) = ((real_sub x y) = term19).
Proof. exact (@lem1586495 x y (@lem1586494 x y)). Qed.
Lemma lem1586521 (y : real) (z : real) : (y = z) = ((real_sub y z) = term19).
Proof. exact (@lem1586520 y z). Qed.
Lemma lem1586522 (x : real) (y : real) (z : real) : (term158 x y z) = (term159 x y z).
Proof. exact (MK_COMB (@lem1586516 x) (@lem1586521 y z)). Qed.
Lemma lem1586523 (x : real) (y : real) (z : real) : (((real_mul x y) = (real_mul x z)) = (term158 x y z)) = (((term1 y x z) = term19) = (term159 x y z)).
Proof. exact (MK_COMB (@lem1586507 y x z) (@lem1586522 x y z)). Qed.
Lemma lem1586524 (x : real) (y : real) (z : real) : (((term1 y x z) = term19) = (term159 x y z)) = (((real_mul x y) = (real_mul x z)) = (term158 x y z)).
Proof. exact (SYM (@lem1586523 x y z)). Qed.
Lemma lem1586530 (x : real) (y : real) (z : real) : (term1 y x z) = (term0 x y z).
Proof. exact (EQ_MP (@lem1585820 x y z) (@lem1585819 x y z)). Qed.
Lemma lem1586531 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1586532 (x : real) (y : real) (z : real) : (term160 y x z) = (term161 x y z).
Proof. exact (MK_COMB (@lem1586531) (@lem1586530 x y z)). Qed.
Lemma lem1586533 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem1586534 (x : real) (y : real) (z : real) : ((term1 y x z) = term19) = ((term0 x y z) = term19).
Proof. exact (MK_COMB (@lem1586532 x y z) (@lem1586533)). Qed.
Lemma lem1586536 (x : real) (y : real) : ((real_mul x y) = term19) = (term20 x y).
Proof. exact (EQ_MP (@lem1585811 x y) (@lem1585810 x y)). Qed.
Lemma lem1586537 (x : real) (y : real) (z : real) : ((term0 x y z) = term19) = (term162 x y z).
Proof. exact (@lem1586536 x (real_sub y z)). Qed.
Lemma lem1586544 (x : real) (y : real) (z : real) : ((term1 y x z) = term19) = (term162 x y z).
Proof. exact (TRANS (@lem1586534 x y z) (@lem1586537 x y z)). Qed.
Lemma lem1586545 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1586546 (x : real) (y : real) (z : real) : (term155 y x z) = (term163 x y z).
Proof. exact (MK_COMB (@lem1586545) (@lem1586544 x y z)). Qed.
Lemma lem1586552 (x : real) : (term15 x) = x.
Proof. exact (EQ_MP (@lem1585805 x) (@lem1585804 x)). Qed.
Lemma lem1586553 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1586554 (x : real) : (term164 x) = (@eq real x).
Proof. exact (MK_COMB (@lem1586553) (@lem1586552 x)). Qed.
Lemma lem1586555 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem1586556 (x : real) : ((term15 x) = term19) = (x = term19).
Proof. exact (MK_COMB (@lem1586554 x) (@lem1586555)). Qed.
Lemma lem1586559 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1586560 (x : real) : (term157 x) = (term156 x).
Proof. exact (MK_COMB (@lem1586559) (@lem1586556 x)). Qed.
Lemma lem1586563 (y : real) (z : real) : ((real_sub y z) = term19) = ((real_sub y z) = term19).
Proof. exact (eq_refl ((real_sub y z) = term19)). Qed.
Lemma lem1586564 (x : real) (y : real) (z : real) : (term159 x y z) = (term162 x y z).
Proof. exact (MK_COMB (@lem1586560 x) (@lem1586563 y z)). Qed.
Lemma lem1586567 (x : real) (y : real) (z : real) : (((term1 y x z) = term19) = (term159 x y z)) = ((term162 x y z) = (term162 x y z)).
Proof. exact (MK_COMB (@lem1586546 x y z) (@lem1586564 x y z)). Qed.
Lemma lem1586569 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1586570 (x : Prop) : (x = x) = True.
Proof. exact (@lem1586569 Prop x). Qed.
Lemma lem1586571 (x : real) (y : real) (z : real) : ((term162 x y z) = (term162 x y z)) = True.
Proof. exact (@lem1586570 (term162 x y z)). Qed.
Lemma lem1586572 (x : real) (y : real) (z : real) : (((term1 y x z) = term19) = (term159 x y z)) = True.
Proof. exact (TRANS (@lem1586567 x y z) (@lem1586571 x y z)). Qed.
Lemma lem1586573 (x : real) (y : real) (z : real) : True = (((term1 y x z) = term19) = (term159 x y z)).
Proof. exact (SYM (@lem1586572 x y z)). Qed.
Lemma lem1586574 (x : real) (y : real) (z : real) : ((term1 y x z) = term19) = (term159 x y z).
Proof. exact (EQ_MP (@lem1586573 x y z) (@lem0)). Qed.
Lemma lem1586575 (x : real) (y : real) (z : real) : ((real_mul x y) = (real_mul x z)) = (term158 x y z).
Proof. exact (EQ_MP (@lem1586524 x y z) (@lem1586574 x y z)). Qed.
Lemma lem1586580 (x : real) (y : real) : term165 x y.
Proof. exact (fun z : real => @lem1586575 x y z). Qed.
Lemma lem1586585 (x : real) : term166 x.
Proof. exact (fun y : real => @lem1586580 x y). Qed.
Lemma lem1586590 : term167.
Proof. exact (fun x : real => @lem1586585 x). Qed.
