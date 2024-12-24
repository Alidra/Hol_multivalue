Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_SUB_TRIANGLE_term_abbrevs.
Require Import thm1008952_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1483436_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483476_spec.
Require Import thm1483480_spec.
Require Import thm1483482_spec.
Require Import thm1483490_spec.
Require Import thm1483508_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483554_spec.
Require Import thm18392_spec.
Require Import thm18931_spec.
Require Import thm18932_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm940073_spec.
Lemma lem1519821 (P : real -> Prop) : (term0 P) = (term1 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1519822 (b : real) (a : real) : (term2 b a) = (term3 b a).
Proof. exact (@lem1519821 (term4 b a)). Qed.
Lemma lem1519823 (b : real) (a : real) (c : real) : (term5 b a c) = ((term6 a b c) = (real_sub a c)).
Proof. exact (eq_refl (term5 b a c)). Qed.
Lemma lem1519824 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1519826 (b : real) (a : real) (c : real) : (term7 b a c) = (term8 b a c).
Proof. exact (MK_COMB (@lem1519824) (@lem1519823 b a c)). Qed.
Lemma lem1519827 (b : real) (a : real) : (term9 b a) = (term10 b a).
Proof. exact (fun_ext (fun c : real => @lem1519826 b a c)). Qed.
Lemma lem1519828 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1519829 (b : real) (a : real) : (term3 b a) = (term11 b a).
Proof. exact (MK_COMB (@lem1519828) (@lem1519827 b a)). Qed.
Lemma lem1519830 (b : real) (a : real) : (term2 b a) = (term11 b a).
Proof. exact (TRANS (@lem1519822 b a) (@lem1519829 b a)). Qed.
Lemma lem1519831 (P : real -> Prop) : (term0 P) = (term1 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1519832 (a : real) : (term12 a) = (term13 a).
Proof. exact (@lem1519831 (term14 a)). Qed.
Lemma lem1519833 (b : real) (a : real) : (term15 a b) = (term16 b a).
Proof. exact (eq_refl (term15 a b)). Qed.
Lemma lem1519834 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1519835 (b : real) (a : real) : (term17 a b) = (term2 b a).
Proof. exact (MK_COMB (@lem1519834) (@lem1519833 b a)). Qed.
Lemma lem1519836 (b : real) (a : real) : (term17 a b) = (term11 b a).
Proof. exact (TRANS (@lem1519835 b a) (@lem1519830 b a)). Qed.
Lemma lem1519837 (a : real) : (term18 a) = (term19 a).
Proof. exact (fun_ext (fun b : real => @lem1519836 b a)). Qed.
Lemma lem1519838 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1519839 (a : real) : (term13 a) = (term20 a).
Proof. exact (MK_COMB (@lem1519838) (@lem1519837 a)). Qed.
Lemma lem1519840 (a : real) : (term12 a) = (term20 a).
Proof. exact (TRANS (@lem1519832 a) (@lem1519839 a)). Qed.
Lemma lem1519841 (P : real -> Prop) : (term0 P) = (term1 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1519842 : term21 = term22.
Proof. exact (@lem1519841 term23). Qed.
Lemma lem1519843 (a : real) : (term24 a) = (term25 a).
Proof. exact (eq_refl (term24 a)). Qed.
Lemma lem1519844 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1519845 (a : real) : (term26 a) = (term12 a).
Proof. exact (MK_COMB (@lem1519844) (@lem1519843 a)). Qed.
Lemma lem1519846 (a : real) : (term26 a) = (term20 a).
Proof. exact (TRANS (@lem1519845 a) (@lem1519840 a)). Qed.
Lemma lem1519847 : term27 = term28.
Proof. exact (fun_ext (fun a : real => @lem1519846 a)). Qed.
Lemma lem1519848 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1519849 : term22 = term29.
Proof. exact (MK_COMB (@lem1519848) (@lem1519847)). Qed.
Lemma lem1519851 : term21 = term29.
Proof. exact (TRANS (@lem1519842) (@lem1519849)). Qed.
Lemma lem1519854 (b : real) (a : real) (c : real) : (term8 b a c) = (term8 b a c).
Proof. exact (eq_refl (term8 b a c)). Qed.
Lemma lem1519855 (b : real) (a : real) : (term10 b a) = (term10 b a).
Proof. exact (fun_ext (fun c : real => @lem1519854 b a c)). Qed.
Lemma lem1519856 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1519857 (b : real) (a : real) : (term11 b a) = (term11 b a).
Proof. exact (MK_COMB (@lem1519856) (@lem1519855 b a)). Qed.
Lemma lem1519858 (a : real) : (term19 a) = (term19 a).
Proof. exact (fun_ext (fun b : real => @lem1519857 b a)). Qed.
Lemma lem1519859 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1519860 (a : real) : (term20 a) = (term20 a).
Proof. exact (MK_COMB (@lem1519859) (@lem1519858 a)). Qed.
Lemma lem1519861 : term28 = term28.
Proof. exact (fun_ext (fun a : real => @lem1519860 a)). Qed.
Lemma lem1519862 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1519863 : term29 = term29.
Proof. exact (MK_COMB (@lem1519862) (@lem1519861)). Qed.
Lemma lem1519864 : term21 = term29.
Proof. exact (TRANS (@lem1519851) (@lem1519863)). Qed.
Lemma lem1519865 (b : real) (a : real) (c : real) : (term8 b a c) = (term30 b a c).
Proof. exact (@lem1483554 (term6 a b c) (real_sub a c)). Qed.
Lemma lem1519878 (a : real) (c : real) : (real_sub a c) = (term31 a c).
Proof. exact (@lem1483519 a c). Qed.
Lemma lem1519891 (b : real) (c : real) : (real_sub b c) = (term31 b c).
Proof. exact (@lem1483519 b c). Qed.
Lemma lem1519904 (a : real) (b : real) : (real_sub a b) = (term31 a b).
Proof. exact (@lem1483519 a b). Qed.
Lemma lem1519905 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1519906 (a : real) (b : real) : (term32 a b) = (term33 a b).
Proof. exact (MK_COMB (@lem1519905) (@lem1519904 a b)). Qed.
Lemma lem1519907 (a : real) (b : real) (c : real) : (term6 a b c) = (term34 a b c).
Proof. exact (MK_COMB (@lem1519906 a b) (@lem1519891 b c)). Qed.
Lemma lem1519908 (a : real) (b : real) (c : real) : (term34 a b c) = (term35 a b c).
Proof. exact (@lem1483482 a (term36 b) (term31 b c)). Qed.
Lemma lem1519909 (b : real) (c : real) : (term37 b c) = (term38 b c).
Proof. exact (@lem1483490 (term36 b) b (term36 c)). Qed.
Lemma lem1519910 (b : real) : (term39 b) = (term40 b).
Proof. exact (@lem1483440 term41 b). Qed.
Lemma lem1519912 (m : nat) : (term42 m) = term43.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1519913 : term44 = term43.
Proof. exact (@lem1519912 term45). Qed.
Lemma lem1519914 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1519915 : term46 = term47.
Proof. exact (MK_COMB (@lem1519914) (@lem1519913)). Qed.
Lemma lem1519916 (b : real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem1519917 (b : real) : (term40 b) = (term48 b).
Proof. exact (MK_COMB (@lem1519915) (@lem1519916 b)). Qed.
Lemma lem1519918 (b : real) : (term39 b) = (term48 b).
Proof. exact (TRANS (@lem1519910 b) (@lem1519917 b)). Qed.
Lemma lem1519919 (b : real) : (term48 b) = term43.
Proof. exact (@lem1483446 b). Qed.
Lemma lem1519920 (b : real) : (term39 b) = term43.
Proof. exact (TRANS (@lem1519918 b) (@lem1519919 b)). Qed.
Lemma lem1519921 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1519922 (b : real) : (term49 b) = term50.
Proof. exact (MK_COMB (@lem1519921) (@lem1519920 b)). Qed.
Lemma lem1519923 (c : real) : (term36 c) = (term36 c).
Proof. exact (eq_refl (term36 c)). Qed.
Lemma lem1519924 (b : real) (c : real) : (term38 b c) = (term51 c).
Proof. exact (MK_COMB (@lem1519922 b) (@lem1519923 c)). Qed.
Lemma lem1519925 (b : real) (c : real) : (term37 b c) = (term51 c).
Proof. exact (TRANS (@lem1519909 b c) (@lem1519924 b c)). Qed.
Lemma lem1519926 (c : real) : (term51 c) = (term36 c).
Proof. exact (@lem1483448 (term36 c)). Qed.
Lemma lem1519927 (b : real) (c : real) : (term37 b c) = (term36 c).
Proof. exact (TRANS (@lem1519925 b c) (@lem1519926 c)). Qed.
Lemma lem1519928 (a : real) : (real_add a) = (real_add a).
Proof. exact (eq_refl (real_add a)). Qed.
Lemma lem1519929 (b : real) (a : real) (c : real) : (term35 a b c) = (term31 a c).
Proof. exact (MK_COMB (@lem1519928 a) (@lem1519927 b c)). Qed.
Lemma lem1519930 (b : real) (a : real) (c : real) : (term34 a b c) = (term31 a c).
Proof. exact (TRANS (@lem1519908 a b c) (@lem1519929 b a c)). Qed.
Lemma lem1519931 (b : real) (a : real) (c : real) : (term6 a b c) = (term31 a c).
Proof. exact (TRANS (@lem1519907 a b c) (@lem1519930 b a c)). Qed.
Lemma lem1519932 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1519933 (b : real) (a : real) (c : real) : (term52 a b c) = (term53 a c).
Proof. exact (MK_COMB (@lem1519932) (@lem1519931 b a c)). Qed.
Lemma lem1519934 (b : real) (a : real) (c : real) : (term54 b a c) = (term55 a c).
Proof. exact (MK_COMB (@lem1519933 b a c) (@lem1519878 a c)). Qed.
Lemma lem1519935 (a : real) (c : real) : (term55 a c) = (term56 a c).
Proof. exact (@lem1483519 (term31 a c) (term31 a c)). Qed.
Lemma lem1519936 (a : real) (c : real) : (term57 a c) = (term58 a c).
Proof. exact (@lem1483508 a term41 (term36 c)). Qed.
Lemma lem1519937 (c : real) : (term59 c) = (term60 c).
Proof. exact (@lem1483476 term41 term41 c). Qed.
Lemma lem1519939 (m : nat) (n : nat) : (term61 m n) = (term62 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1519940 : term63 = term64.
Proof. exact (@lem1519939 term45 term45). Qed.
Lemma lem1519941 : (term65 = (BIT1 0)) = (term66 = term45).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1519942 : term66 = term45.
Proof. exact (EQ_MP (@lem1519941) (@lem940073)). Qed.
Lemma lem1519943 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1519944 : term64 = term67.
Proof. exact (MK_COMB (@lem1519943) (@lem1519942)). Qed.
Lemma lem1519945 : term63 = term67.
Proof. exact (TRANS (@lem1519940) (@lem1519944)). Qed.
Lemma lem1519946 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1519947 : term68 = term69.
Proof. exact (MK_COMB (@lem1519946) (@lem1519945)). Qed.
Lemma lem1519948 (c : real) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem1519949 (c : real) : (term60 c) = (term70 c).
Proof. exact (MK_COMB (@lem1519947) (@lem1519948 c)). Qed.
Lemma lem1519950 (c : real) : (term59 c) = (term70 c).
Proof. exact (TRANS (@lem1519937 c) (@lem1519949 c)). Qed.
Lemma lem1519951 (c : real) : (term70 c) = c.
Proof. exact (@lem1483436 c). Qed.
Lemma lem1519952 (c : real) : (term59 c) = c.
Proof. exact (TRANS (@lem1519950 c) (@lem1519951 c)). Qed.
Lemma lem1519955 (a : real) : (term71 a) = (term71 a).
Proof. exact (eq_refl (term71 a)). Qed.
Lemma lem1519956 (a : real) (c : real) : (term58 a c) = (term72 a c).
Proof. exact (MK_COMB (@lem1519955 a) (@lem1519952 c)). Qed.
Lemma lem1519957 (a : real) (c : real) : (term57 a c) = (term72 a c).
Proof. exact (TRANS (@lem1519936 a c) (@lem1519956 a c)). Qed.
Lemma lem1519958 (a : real) (c : real) : (term33 a c) = (term33 a c).
Proof. exact (eq_refl (term33 a c)). Qed.
Lemma lem1519959 (a : real) (c : real) : (term56 a c) = (term73 a c).
Proof. exact (MK_COMB (@lem1519958 a c) (@lem1519957 a c)). Qed.
Lemma lem1519960 (a : real) (c : real) : (term73 a c) = (term74 a c).
Proof. exact (@lem1483480 a (term36 a) (term36 c) c). Qed.
Lemma lem1519961 (a : real) : (term75 a) = (term40 a).
Proof. exact (@lem1483442 term41 a). Qed.
Lemma lem1519963 (m : nat) : (term42 m) = term43.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1519964 : term44 = term43.
Proof. exact (@lem1519963 term45). Qed.
Lemma lem1519965 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1519966 : term46 = term47.
Proof. exact (MK_COMB (@lem1519965) (@lem1519964)). Qed.
Lemma lem1519967 (a : real) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1519968 (a : real) : (term40 a) = (term48 a).
Proof. exact (MK_COMB (@lem1519966) (@lem1519967 a)). Qed.
Lemma lem1519969 (a : real) : (term75 a) = (term48 a).
Proof. exact (TRANS (@lem1519961 a) (@lem1519968 a)). Qed.
Lemma lem1519970 (a : real) : (term48 a) = term43.
Proof. exact (@lem1483446 a). Qed.
Lemma lem1519971 (a : real) : (term75 a) = term43.
Proof. exact (TRANS (@lem1519969 a) (@lem1519970 a)). Qed.
Lemma lem1519972 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1519973 (a : real) : (term76 a) = term50.
Proof. exact (MK_COMB (@lem1519972) (@lem1519971 a)). Qed.
Lemma lem1519974 (c : real) : (term39 c) = (term40 c).
Proof. exact (@lem1483440 term41 c). Qed.
Lemma lem1519976 (m : nat) : (term42 m) = term43.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1519977 : term44 = term43.
Proof. exact (@lem1519976 term45). Qed.
Lemma lem1519978 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1519979 : term46 = term47.
Proof. exact (MK_COMB (@lem1519978) (@lem1519977)). Qed.
Lemma lem1519980 (c : real) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem1519981 (c : real) : (term40 c) = (term48 c).
Proof. exact (MK_COMB (@lem1519979) (@lem1519980 c)). Qed.
Lemma lem1519982 (c : real) : (term39 c) = (term48 c).
Proof. exact (TRANS (@lem1519974 c) (@lem1519981 c)). Qed.
Lemma lem1519983 (c : real) : (term48 c) = term43.
Proof. exact (@lem1483446 c). Qed.
Lemma lem1519984 (c : real) : (term39 c) = term43.
Proof. exact (TRANS (@lem1519982 c) (@lem1519983 c)). Qed.
Lemma lem1519985 (a : real) (c : real) : (term74 a c) = term77.
Proof. exact (MK_COMB (@lem1519973 a) (@lem1519984 c)). Qed.
Lemma lem1519986 (a : real) (c : real) : (term73 a c) = term77.
Proof. exact (TRANS (@lem1519960 a c) (@lem1519985 a c)). Qed.
Lemma lem1519987 : term77 = term43.
Proof. exact (@lem1483448 term43). Qed.
Lemma lem1519988 (a : real) (c : real) : (term73 a c) = term43.
Proof. exact (TRANS (@lem1519986 a c) (@lem1519987)). Qed.
Lemma lem1519989 (a : real) (c : real) : (term56 a c) = term43.
Proof. exact (TRANS (@lem1519959 a c) (@lem1519988 a c)). Qed.
Lemma lem1519990 (a : real) (c : real) : (term55 a c) = term43.
Proof. exact (TRANS (@lem1519935 a c) (@lem1519989 a c)). Qed.
Lemma lem1519991 (b : real) (a : real) (c : real) : (term54 b a c) = term43.
Proof. exact (TRANS (@lem1519934 b a c) (@lem1519990 a c)). Qed.
Lemma lem1519992 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1519993 (b : real) (a : real) (c : real) : (term78 b a c) = term79.
Proof. exact (MK_COMB (@lem1519992) (@lem1519991 b a c)). Qed.
Lemma lem1519994 : term79 = term80.
Proof. exact (@lem1483512 term43). Qed.
Lemma lem1519996 (x : nat) : (term81 x) = term43.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1519997 : term80 = term43.
Proof. exact (@lem1519996 term45). Qed.
Lemma lem1519998 : term79 = term43.
Proof. exact (TRANS (@lem1519994) (@lem1519997)). Qed.
Lemma lem1519999 (b : real) (a : real) (c : real) : (term82 b a c) = (term82 b a c).
Proof. exact (eq_refl (term82 b a c)). Qed.
Lemma lem1520000 (b : real) (a : real) (c : real) : ((term78 b a c) = term79) = ((term78 b a c) = term43).
Proof. exact (MK_COMB (@lem1519999 b a c) (@lem1519998)). Qed.
Lemma lem1520001 (b : real) (a : real) (c : real) : (term78 b a c) = term43.
Proof. exact (EQ_MP (@lem1520000 b a c) (@lem1519993 b a c)). Qed.
Lemma lem1520002 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1520003 (b : real) (a : real) (c : real) : (term83 b a c) = term84.
Proof. exact (MK_COMB (@lem1520002) (@lem1520001 b a c)). Qed.
Lemma lem1520004 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem1520005 (b : real) (a : real) (c : real) : (term85 b a c) = term86.
Proof. exact (MK_COMB (@lem1520003 b a c) (@lem1520004)). Qed.
Lemma lem1520006 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1520007 (b : real) (a : real) (c : real) : (term87 b a c) = term84.
Proof. exact (MK_COMB (@lem1520006) (@lem1519991 b a c)). Qed.
Lemma lem1520008 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem1520009 (b : real) (a : real) (c : real) : (term88 b a c) = term86.
Proof. exact (MK_COMB (@lem1520007 b a c) (@lem1520008)). Qed.
Lemma lem1520010 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1520011 (b : real) (a : real) (c : real) : (term89 b a c) = term90.
Proof. exact (MK_COMB (@lem1520010) (@lem1520009 b a c)). Qed.
Lemma lem1520012 (b : real) (a : real) (c : real) : (term30 b a c) = term91.
Proof. exact (MK_COMB (@lem1520011 b a c) (@lem1520005 b a c)). Qed.
Lemma lem1520013 (b : real) (a : real) (c : real) : (term8 b a c) = term91.
Proof. exact (TRANS (@lem1519865 b a c) (@lem1520012 b a c)). Qed.
Lemma lem1520014 (b : real) (a : real) : (term10 b a) = term92.
Proof. exact (fun_ext (fun c : real => @lem1520013 b a c)). Qed.
Lemma lem1520015 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1520016 (b : real) (a : real) : (term11 b a) = term93.
Proof. exact (MK_COMB (@lem1520015) (@lem1520014 b a)). Qed.
Lemma lem1520017 (a : real) : (term19 a) = term94.
Proof. exact (fun_ext (fun b : real => @lem1520016 b a)). Qed.
Lemma lem1520018 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1520019 (a : real) : (term20 a) = term95.
Proof. exact (MK_COMB (@lem1520018) (@lem1520017 a)). Qed.
Lemma lem1520020 : term28 = term96.
Proof. exact (fun_ext (fun a : real => @lem1520019 a)). Qed.
Lemma lem1520021 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1520022 : term29 = term97.
Proof. exact (MK_COMB (@lem1520021) (@lem1520020)). Qed.
Lemma lem1520023 : term21 = term97.
Proof. exact (TRANS (@lem1519864) (@lem1520022)). Qed.
Lemma lem1520025 {A : Type'} (t : Prop) : (term98 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1520026 (t : Prop) : (term99 t) = t.
Proof. exact (@lem1520025 real t). Qed.
Lemma lem1520027 : term97 = term95.
Proof. exact (@lem1520026 term95). Qed.
Lemma lem1520029 {A : Type'} (t : Prop) : (term98 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1520030 (t : Prop) : (term99 t) = t.
Proof. exact (@lem1520029 real t). Qed.
Lemma lem1520031 : term95 = term93.
Proof. exact (@lem1520030 term93). Qed.
Lemma lem1520033 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term100 A P Q) = (term101 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1520034 (P : real -> Prop) (Q : real -> Prop) : (term102 P Q) = (term103 P Q).
Proof. exact (@lem1520033 real P Q). Qed.
Lemma lem1520035 : term104 = term105.
Proof. exact (@lem1520034 term106 term106). Qed.
Lemma lem1520036 (c : real) : (term107 c) = term86.
Proof. exact (eq_refl (term107 c)). Qed.
Lemma lem1520037 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1520038 (c : real) : (term108 c) = term90.
Proof. exact (MK_COMB (@lem1520037) (@lem1520036 c)). Qed.
Lemma lem1520039 (c : real) : (term107 c) = term86.
Proof. exact (eq_refl (term107 c)). Qed.
Lemma lem1520040 (c : real) : (term109 c) = term91.
Proof. exact (MK_COMB (@lem1520038 c) (@lem1520039 c)). Qed.
Lemma lem1520041 : term110 = term92.
Proof. exact (fun_ext (fun c : real => @lem1520040 c)). Qed.
Lemma lem1520042 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1520043 : term104 = term93.
Proof. exact (MK_COMB (@lem1520042) (@lem1520041)). Qed.
Lemma lem1520044 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1520045 : term111 = term112.
Proof. exact (MK_COMB (@lem1520044) (@lem1520043)). Qed.
Lemma lem1520046 (c : real) : (term107 c) = term86.
Proof. exact (eq_refl (term107 c)). Qed.
Lemma lem1520047 : term113 = term106.
Proof. exact (fun_ext (fun c : real => @lem1520046 c)). Qed.
Lemma lem1520048 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1520049 : term114 = term115.
Proof. exact (MK_COMB (@lem1520048) (@lem1520047)). Qed.
Lemma lem1520050 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1520051 : term116 = term117.
Proof. exact (MK_COMB (@lem1520050) (@lem1520049)). Qed.
Lemma lem1520052 (c : real) : (term107 c) = term86.
Proof. exact (eq_refl (term107 c)). Qed.
Lemma lem1520053 : term113 = term106.
Proof. exact (fun_ext (fun c : real => @lem1520052 c)). Qed.
Lemma lem1520054 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1520055 : term114 = term115.
Proof. exact (MK_COMB (@lem1520054) (@lem1520053)). Qed.
Lemma lem1520056 : term105 = term118.
Proof. exact (MK_COMB (@lem1520051) (@lem1520055)). Qed.
Lemma lem1520057 : (term104 = term105) = (term93 = term118).
Proof. exact (MK_COMB (@lem1520045) (@lem1520056)). Qed.
Lemma lem1520058 : term93 = term118.
Proof. exact (EQ_MP (@lem1520057) (@lem1520035)). Qed.
Lemma lem1520059 : term95 = term118.
Proof. exact (TRANS (@lem1520031) (@lem1520058)). Qed.
Lemma lem1520060 : term97 = term118.
Proof. exact (TRANS (@lem1520027) (@lem1520059)). Qed.
Lemma lem1520062 {A : Type'} (t : Prop) : (term98 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1520063 (t : Prop) : (term99 t) = t.
Proof. exact (@lem1520062 real t). Qed.
Lemma lem1520064 : term115 = term86.
Proof. exact (@lem1520063 term86). Qed.
Lemma lem1520065 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1520066 : term117 = term90.
Proof. exact (MK_COMB (@lem1520065) (@lem1520064)). Qed.
Lemma lem1520068 {A : Type'} (t : Prop) : (term98 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1520069 (t : Prop) : (term99 t) = t.
Proof. exact (@lem1520068 real t). Qed.
Lemma lem1520070 : term115 = term86.
Proof. exact (@lem1520069 term86). Qed.
Lemma lem1520071 : term118 = term91.
Proof. exact (MK_COMB (@lem1520066) (@lem1520070)). Qed.
Lemma lem1520074 : term97 = term91.
Proof. exact (TRANS (@lem1520060) (@lem1520071)). Qed.
Lemma lem1520083 : term21 = term91.
Proof. exact (TRANS (@lem1520023) (@lem1520074)). Qed.
Lemma lem1520093 (h1 : term91) : term91.
Proof. exact (h1). Qed.
Lemma lem1520094 (h1 : term86) : term86.
Proof. exact (h1). Qed.
Lemma lem1520096 (n : nat) (m : nat) : (term119 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1520097 : term86 = term120.
Proof. exact (@lem1520096 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1520098 : term120 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1520099 : term86 = False.
Proof. exact (TRANS (@lem1520097) (@lem1520098)). Qed.
Lemma lem1520100 (h1 : term86) : False.
Proof. exact (EQ_MP (@lem1520099) (@lem1520094 h1)). Qed.
Lemma lem1520101 (h1 : term86) : term86.
Proof. exact (h1). Qed.
Lemma lem1520103 (n : nat) (m : nat) : (term119 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1520104 : term86 = term120.
Proof. exact (@lem1520103 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1520105 : term120 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1520106 : term86 = False.
Proof. exact (TRANS (@lem1520104) (@lem1520105)). Qed.
Lemma lem1520107 (h1 : term86) : False.
Proof. exact (EQ_MP (@lem1520106) (@lem1520101 h1)). Qed.
Lemma lem1520108 (h1 : term91) : False.
Proof. exact (or_elim (@lem1520093 h1) (fun h0 : term86 => @lem1520100 h0) (fun h0 : term86 => @lem1520107 h0)). Qed.
Lemma lem1520110 (h1 : term91) : term91.
Proof. exact (h1). Qed.
Lemma lem1520111 (h1 : term91) : term91 = False.
Proof. exact (prop_ext (fun h2 : term91 => @lem1520108 h1) (fun h2 : False => @lem1520110 h1)). Qed.
Lemma lem1520112 (h1 : term91) : False.
Proof. exact (EQ_MP (@lem1520111 h1) (@lem1520110 h1)). Qed.
Lemma lem1520113 (h1 : term21) : term21.
Proof. exact (h1). Qed.
Lemma lem1520114 (h1 : term21) : term91.
Proof. exact (EQ_MP (@lem1520083) (@lem1520113 h1)). Qed.
Lemma lem1520115 (h1 : term21) : term91 = False.
Proof. exact (prop_ext (fun h2 : term91 => @lem1520112 h2) (fun h2 : False => @lem1520114 h1)). Qed.
Lemma lem1520116 (h1 : term21) : False.
Proof. exact (EQ_MP (@lem1520115 h1) (@lem1520114 h1)). Qed.
Lemma lem1520117 : term121.
Proof. exact (fun h0 : term21 => @lem1520116 h0). Qed.
Lemma lem1520118 : term122.
Proof. exact (@lem1386578 term123). Qed.
Lemma lem1520119 : term123.
Proof. exact (@lem1520118 (@lem1520117)). Qed.
