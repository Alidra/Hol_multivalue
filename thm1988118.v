Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1988118_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import REAL_MUL_LZERO_spec.
Require Import REAL_MUL_RINV_spec.
Require Import REAL_SUB_0_spec.
Require Import thm0_spec.
Require Import thm1013352_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1366971_spec.
Require Import thm1367254_spec.
Require Import thm1386578_spec.
Require Import thm1483450_spec.
Require Import thm1483519_spec.
Require Import thm1483529_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17265_spec.
Require Import thm17646_spec.
Require Import thm18394_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
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
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm69_spec.
Require Import thm912739_spec.
Lemma lem1986829 (t : Prop) : (term0 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem1986835 : term1 = (term2 = term3).
Proof. exact (@lem1986829 (term2 = term3)). Qed.
Lemma lem1986836 : (term2 = term3) = (term4 = term3).
Proof. exact (@lem1483529 term2 term3). Qed.
Lemma lem1986842 : term4 = term5.
Proof. exact (@lem1483519 term2 term3). Qed.
Lemma lem1986844 (x : nat) : (term6 x) = term3.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1986845 : term7 = term3.
Proof. exact (@lem1986844 term8). Qed.
Lemma lem1986846 : term9 = term9.
Proof. exact (eq_refl term9). Qed.
Lemma lem1986847 : term5 = term10.
Proof. exact (MK_COMB (@lem1986846) (@lem1986845)). Qed.
Lemma lem1986848 : term10 = term2.
Proof. exact (@lem1483450 term2). Qed.
Lemma lem1986849 : term5 = term2.
Proof. exact (TRANS (@lem1986847) (@lem1986848)). Qed.
Lemma lem1986851 : term4 = term2.
Proof. exact (TRANS (@lem1986842) (@lem1986849)). Qed.
Lemma lem1986852 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1986853 : term11 = term12.
Proof. exact (MK_COMB (@lem1986852) (@lem1986851)). Qed.
Lemma lem1986854 : term3 = term3.
Proof. exact (eq_refl term3). Qed.
Lemma lem1986855 : (term4 = term3) = (term2 = term3).
Proof. exact (MK_COMB (@lem1986853) (@lem1986854)). Qed.
Lemma lem1986856 : (term2 = term3) = (term2 = term3).
Proof. exact (TRANS (@lem1986836) (@lem1986855)). Qed.
Lemma lem1986865 : term1 = (term2 = term3).
Proof. exact (TRANS (@lem1986835) (@lem1986856)). Qed.
Lemma lem1986869 (h1 : term2 = term3) : term2 = term3.
Proof. exact (h1). Qed.
Lemma lem1986871 (m : nat) (n : nat) : ((real_of_num m) = (real_of_num n)) = (m = n).
Proof. exact (proj1 (@lem1366971 m n)). Qed.
Lemma lem1986872 : (term2 = term3) = (term8 = (NUMERAL 0)).
Proof. exact (@lem1986871 term8 (NUMERAL 0)). Qed.
Lemma lem1986873 : term13 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1986874 (h1 : term13 = (BIT1 0)) : (term8 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem1986875 : (term13 = (BIT1 0)) = ((term8 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term13 = (BIT1 0) => @lem1986874 h1) (fun h1 : (term8 = (NUMERAL 0)) = False => @lem1986873)). Qed.
Lemma lem1986876 : (term8 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem1986875) (@lem1986873)). Qed.
Lemma lem1986877 : (term2 = term3) = False.
Proof. exact (TRANS (@lem1986872) (@lem1986876)). Qed.
Lemma lem1986878 (h1 : term2 = term3) : False.
Proof. exact (EQ_MP (@lem1986877) (@lem1986869 h1)). Qed.
Lemma lem1986880 (h1 : term2 = term3) : term2 = term3.
Proof. exact (h1). Qed.
Lemma lem1986881 (h1 : term2 = term3) : (term2 = term3) = False.
Proof. exact (prop_ext (fun h2 : term2 = term3 => @lem1986878 h1) (fun h2 : False => @lem1986880 h1)). Qed.
Lemma lem1986882 (h1 : term2 = term3) : False.
Proof. exact (EQ_MP (@lem1986881 h1) (@lem1986880 h1)). Qed.
Lemma lem1986883 (h1 : term1) : term1.
Proof. exact (h1). Qed.
Lemma lem1986884 (h1 : term1) : term2 = term3.
Proof. exact (EQ_MP (@lem1986865) (@lem1986883 h1)). Qed.
Lemma lem1986885 (h1 : term1) : (term2 = term3) = False.
Proof. exact (prop_ext (fun h2 : term2 = term3 => @lem1986882 h2) (fun h2 : False => @lem1986884 h1)). Qed.
Lemma lem1986886 (h1 : term1) : False.
Proof. exact (EQ_MP (@lem1986885 h1) (@lem1986884 h1)). Qed.
Lemma lem1986887 : term14.
Proof. exact (fun h0 : term1 => @lem1986886 h0). Qed.
Lemma lem1986888 : term15.
Proof. exact (@lem1386578 term16). Qed.
Lemma lem1986889 : term16.
Proof. exact (@lem1986888 (@lem1986887)). Qed.
Lemma lem1986902 (x : real) (y : real) (h1 : ((real_sub x y) = term3) = (x = y)) : ((real_sub x y) = term3) = (x = y).
Proof. exact (h1). Qed.
Lemma lem1986903 (x : real) (y : real) (h1 : ((real_sub x y) = term3) = (x = y)) : (x = y) = ((real_sub x y) = term3).
Proof. exact (SYM (@lem1986902 x y h1)). Qed.
Lemma lem1986904 (x : real) (y : real) (h1 : (x = y) = ((real_sub x y) = term3)) : (x = y) = ((real_sub x y) = term3).
Proof. exact (h1). Qed.
Lemma lem1986905 (x : real) (y : real) (h1 : (x = y) = ((real_sub x y) = term3)) : ((real_sub x y) = term3) = (x = y).
Proof. exact (SYM (@lem1986904 x y h1)). Qed.
Lemma lem1986906 (x : real) (y : real) : (((real_sub x y) = term3) = (x = y)) = ((x = y) = ((real_sub x y) = term3)).
Proof. exact (prop_ext (fun h1 : ((real_sub x y) = term3) = (x = y) => @lem1986903 x y h1) (fun h1 : (x = y) = ((real_sub x y) = term3) => @lem1986905 x y h1)). Qed.
Lemma lem1986907 (x : real) : (term17 x) = (term18 x).
Proof. exact (fun_ext (fun y : real => @lem1986906 x y)). Qed.
Lemma lem1986908 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1986909 (x : real) : (term19 x) = (term20 x).
Proof. exact (MK_COMB (@lem1986908) (@lem1986907 x)). Qed.
Lemma lem1986910 : term21 = term22.
Proof. exact (fun_ext (fun x : real => @lem1986909 x)). Qed.
Lemma lem1986911 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1986912 : term23 = term24.
Proof. exact (MK_COMB (@lem1986911) (@lem1986910)). Qed.
Lemma lem1986913 : term24.
Proof. exact (EQ_MP (@lem1986912) (@lem1376695)). Qed.
Lemma lem1986914 (x : real) : term25 x.
Proof. exact (@lem1986913 x). Qed.
Lemma lem1986915 (x : real) : (term25 x) = (term20 x).
Proof. exact (eq_refl (term25 x)). Qed.
Lemma lem1986916 (x : real) : term20 x.
Proof. exact (EQ_MP (@lem1986915 x) (@lem1986914 x)). Qed.
Lemma lem1986917 (x : real) (y : real) : term26 x y.
Proof. exact (@lem1986916 x y). Qed.
Lemma lem1986918 (x : real) (y : real) : (term26 x y) = ((x = y) = ((real_sub x y) = term3)).
Proof. exact (eq_refl (term26 x y)). Qed.
Lemma lem1986921 (x : real) (y : real) : (x = y) = ((real_sub x y) = term3).
Proof. exact (EQ_MP (@lem1986918 x y) (@lem1986917 x y)). Qed.
Lemma lem1986922 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1986923 (x : real) (y : real) : (term27 x y) = (term28 x y).
Proof. exact (MK_COMB (@lem1986922) (@lem1986921 x y)). Qed.
Lemma lem1986924 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1986925 (x : real) (y : real) : (term29 x y) = (term30 x y).
Proof. exact (MK_COMB (@lem1986924) (@lem1986923 x y)). Qed.
Lemma lem1986926 (x : real) (y : real) : (term31 x y) = (term31 x y).
Proof. exact (eq_refl (term31 x y)). Qed.
Lemma lem1986927 (x : real) (y : real) : ((term27 x y) = (term31 x y)) = ((term28 x y) = (term31 x y)).
Proof. exact (MK_COMB (@lem1986925 x y) (@lem1986926 x y)). Qed.
Lemma lem1986928 (x : real) (y : real) : ((term28 x y) = (term31 x y)) = ((term27 x y) = (term31 x y)).
Proof. exact (SYM (@lem1986927 x y)). Qed.
Lemma lem1986930 (p : Prop) : p = (term32 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1986931 (x : real) (y : real) : ((term28 x y) = (term31 x y)) = (term33 x y).
Proof. exact (@lem1986930 ((term28 x y) = (term31 x y))). Qed.
Lemma lem1986932 (x : real) (y : real) : (term33 x y) = ((term28 x y) = (term31 x y)).
Proof. exact (SYM (@lem1986931 x y)). Qed.
Lemma lem1986933 (x : real) (y : real) (h1 : term34 x y) : term34 x y.
Proof. exact (h1). Qed.
Lemma lem1986936 (x : real) (y : real) (h1 : term35 x y) : term35 x y.
Proof. exact (h1). Qed.
Lemma lem1986937 (x : real) (y : real) : term36 x y.
Proof. exact (fun h0 : term35 x y => @lem1986936 x y h0). Qed.
Lemma lem1986938 (x : real) (y : real) (h1 : term36 x y) : term36 x y.
Proof. exact (h1). Qed.
Lemma lem1986939 (x : real) (y : real) (h1 : term35 x y) : term35 x y.
Proof. exact (h1). Qed.
Lemma lem1986940 (x : real) (y : real) (h1 : term35 x y) (h2 : term36 x y) : term35 x y.
Proof. exact (@lem1986938 x y h2 (@lem1986939 x y h1)). Qed.
Lemma lem1986941 (x : real) (y : real) (h1 : term35 x y) : term37 x y.
Proof. exact (fun h0 : term36 x y => @lem1986940 x y h1 h0). Qed.
Lemma lem1986942 (x : real) (y : real) (h1 : term36 x y) : term36 x y.
Proof. exact (h1). Qed.
Lemma lem1986943 (x : real) (y : real) (h1 : term35 x y) (h2 : term36 x y) : term35 x y.
Proof. exact (@lem1986941 x y h1 (@lem1986942 x y h2)). Qed.
Lemma lem1986944 (x : real) (y : real) (h1 : term36 x y) : term36 x y.
Proof. exact (fun h0 : term35 x y => @lem1986943 x y h0 h1). Qed.
Lemma lem1986945 (x : real) (y : real) : term38 x y.
Proof. exact (fun h0 : term36 x y => @lem1986944 x y h0). Qed.
Lemma lem1986948 (x : real) (y : real) : term36 x y.
Proof. exact (@lem1986945 x y (@lem1986937 x y)). Qed.
Lemma lem1986972 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1986973 : term39 = term40.
Proof. exact (@lem1986972 term41). Qed.
Lemma lem1986980 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem1986981 : term43 = term44.
Proof. exact (MK_COMB (@lem1986980) (@lem1986973)). Qed.
Lemma lem1986984 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem1986985 : term46 = term47.
Proof. exact (MK_COMB (@lem1986984) (@lem1986981)). Qed.
Lemma lem1986988 (x : real) (y : real) : (term48 x y) = (term48 x y).
Proof. exact (eq_refl (term48 x y)). Qed.
Lemma lem1986989 (x : real) (y : real) : (term35 x y) = (term49 x y).
Proof. exact (MK_COMB (@lem1986988 x y) (@lem1986985)). Qed.
Lemma lem1986992 (y : real) : (term50 y) = (term51 y).
Proof. exact (fun_ext (fun x : real => @lem1986989 x y)). Qed.
Lemma lem1986993 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1986994 (y : real) : (term52 y) = (term53 y).
Proof. exact (MK_COMB (@lem1986993) (@lem1986992 y)). Qed.
Lemma lem1986999 : term54 = term55.
Proof. exact (fun_ext (fun y : real => @lem1986994 y)). Qed.
Lemma lem1987000 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1987009 : term56 = term57.
Proof. exact (MK_COMB (@lem1987000) (@lem1986999)). Qed.
Lemma lem1987016 (x : real) : (term58 x) = (term58 x).
Proof. exact (eq_refl (term58 x)). Qed.
Lemma lem1987017 : term59 = term59.
Proof. exact (fun_ext (fun x : real => @lem1987016 x)). Qed.
Lemma lem1987018 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1987019 : term41 = term41.
Proof. exact (MK_COMB (@lem1987018) (@lem1987017)). Qed.
Lemma lem1987020 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1987021 : term40 = term40.
Proof. exact (MK_COMB (@lem1987020) (@lem1987019)). Qed.
Lemma lem1987022 (x : real) : ((term60 x) = term3) = ((term60 x) = term3).
Proof. exact (eq_refl ((term60 x) = term3)). Qed.
Lemma lem1987023 : term61 = term61.
Proof. exact (fun_ext (fun x : real => @lem1987022 x)). Qed.
Lemma lem1987024 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1987025 : term62 = term62.
Proof. exact (MK_COMB (@lem1987024) (@lem1987023)). Qed.
Lemma lem1987026 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1987027 : term42 = term42.
Proof. exact (MK_COMB (@lem1987026) (@lem1987025)). Qed.
Lemma lem1987028 : term44 = term44.
Proof. exact (MK_COMB (@lem1987027) (@lem1987021)). Qed.
Lemma lem1987033 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem1987034 : term47 = term47.
Proof. exact (MK_COMB (@lem1987033) (@lem1987028)). Qed.
Lemma lem1987035 (x : real) (y : real) (z : real) : ((term63 x y z) = term2) = ((term63 x y z) = term2).
Proof. exact (eq_refl ((term63 x y z) = term2)). Qed.
Lemma lem1987036 (x : real) (y : real) : (term64 x y) = (term64 x y).
Proof. exact (fun_ext (fun z : real => @lem1987035 x y z)). Qed.
Lemma lem1987037 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1987038 (x : real) (y : real) : (term31 x y) = (term31 x y).
Proof. exact (MK_COMB (@lem1987037) (@lem1987036 x y)). Qed.
Lemma lem1987043 (x : real) (y : real) : (term30 x y) = (term30 x y).
Proof. exact (eq_refl (term30 x y)). Qed.
Lemma lem1987044 (x : real) (y : real) : ((term28 x y) = (term31 x y)) = ((term28 x y) = (term31 x y)).
Proof. exact (MK_COMB (@lem1987043 x y) (@lem1987038 x y)). Qed.
Lemma lem1987045 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1987046 (x : real) (y : real) : (term34 x y) = (term34 x y).
Proof. exact (MK_COMB (@lem1987045) (@lem1987044 x y)). Qed.
Lemma lem1987047 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1987048 (x : real) (y : real) : (term48 x y) = (term48 x y).
Proof. exact (MK_COMB (@lem1987047) (@lem1987046 x y)). Qed.
Lemma lem1987049 (x : real) (y : real) : (term49 x y) = (term49 x y).
Proof. exact (MK_COMB (@lem1987048 x y) (@lem1987034)). Qed.
Lemma lem1987050 (y : real) : (term51 y) = (term51 y).
Proof. exact (fun_ext (fun x : real => @lem1987049 x y)). Qed.
Lemma lem1987051 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1987052 (y : real) : (term53 y) = (term53 y).
Proof. exact (MK_COMB (@lem1987051) (@lem1987050 y)). Qed.
Lemma lem1987053 : term55 = term55.
Proof. exact (fun_ext (fun y : real => @lem1987052 y)). Qed.
Lemma lem1987054 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1987055 : term57 = term57.
Proof. exact (MK_COMB (@lem1987054) (@lem1987053)). Qed.
Lemma lem1987096 : term56 = term57.
Proof. exact (TRANS (@lem1987009) (@lem1987055)). Qed.
Lemma lem1987097 : term57 = term56.
Proof. exact (SYM (@lem1987096)). Qed.
Lemma lem1987098 (x : real) (y : real) (h1 : term34 x y) : term34 x y.
Proof. exact (h1). Qed.
Lemma lem1987100 (h1 : term62) : term62.
Proof. exact (h1). Qed.
Lemma lem1987101 (h1 : term41) : term41.
Proof. exact (h1). Qed.
Lemma lem1987105 (x : real) (y : real) : (term65 x y) = ((real_sub x y) = term3).
Proof. exact (@lem16933 ((real_sub x y) = term3)). Qed.
Lemma lem1987107 (x : real) (y : real) (z : real) : ((term63 x y z) = term2) = ((term63 x y z) = term2).
Proof. exact (eq_refl ((term63 x y z) = term2)). Qed.
Lemma lem1987108 (P : real -> Prop) : (term66 P) = (term67 P).
Proof. exact (@lem18394 real P). Qed.
Lemma lem1987109 (x : real) (y : real) : (term68 x y) = (term69 x y).
Proof. exact (@lem1987108 (term64 x y)). Qed.
Lemma lem1987110 (x : real) (y : real) (z : real) : (term70 x y z) = ((term63 x y z) = term2).
Proof. exact (eq_refl (term70 x y z)). Qed.
Lemma lem1987111 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1987113 (x : real) (y : real) (z : real) : (term71 x y z) = (term72 x y z).
Proof. exact (MK_COMB (@lem1987111) (@lem1987110 x y z)). Qed.
Lemma lem1987114 (x : real) (y : real) : (term73 x y) = (term74 x y).
Proof. exact (fun_ext (fun z : real => @lem1987113 x y z)). Qed.
Lemma lem1987115 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1987116 (x : real) (y : real) : (term69 x y) = (term75 x y).
Proof. exact (MK_COMB (@lem1987115) (@lem1987114 x y)). Qed.
Lemma lem1987117 (x : real) (y : real) : (term68 x y) = (term75 x y).
Proof. exact (TRANS (@lem1987109 x y) (@lem1987116 x y)). Qed.
Lemma lem1987118 (x : real) (y : real) : (term64 x y) = (term64 x y).
Proof. exact (fun_ext (fun z : real => @lem1987107 x y z)). Qed.
Lemma lem1987119 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1987120 (x : real) (y : real) : (term31 x y) = (term31 x y).
Proof. exact (MK_COMB (@lem1987119) (@lem1987118 x y)). Qed.
Lemma lem1987121 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1987122 (x : real) (y : real) : (term76 x y) = (term77 x y).
Proof. exact (MK_COMB (@lem1987121) (@lem1987105 x y)). Qed.
Lemma lem1987123 (x : real) (y : real) : (term78 x y) = (term79 x y).
Proof. exact (MK_COMB (@lem1987122 x y) (@lem1987120 x y)). Qed.
Lemma lem1987125 (x : real) (y : real) : (term80 x y) = (term80 x y).
Proof. exact (eq_refl (term80 x y)). Qed.
Lemma lem1987126 (x : real) (y : real) : (term81 x y) = (term82 x y).
Proof. exact (MK_COMB (@lem1987125 x y) (@lem1987117 x y)). Qed.
Lemma lem1987127 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1987128 (x : real) (y : real) : (term83 x y) = (term84 x y).
Proof. exact (MK_COMB (@lem1987127) (@lem1987126 x y)). Qed.
Lemma lem1987129 (x : real) (y : real) : (term85 x y) = (term86 x y).
Proof. exact (MK_COMB (@lem1987128 x y) (@lem1987123 x y)). Qed.
Lemma lem1987130 (x : real) (y : real) : (term34 x y) = (term85 x y).
Proof. exact (@lem17646 (term28 x y) (term31 x y)). Qed.
Lemma lem1987131 (x : real) (y : real) : (term34 x y) = (term86 x y).
Proof. exact (TRANS (@lem1987130 x y) (@lem1987129 x y)). Qed.
Lemma lem1987142 {A : Type'} (P : Prop) (Q : A -> Prop) : (term87 A P Q) = (term88 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem1987143 (P : Prop) (Q : real -> Prop) : (term89 P Q) = (term90 P Q).
Proof. exact (@lem1987142 real P Q). Qed.
Lemma lem1987144 (x : real) (y : real) : (term91 x y) = (term92 x y).
Proof. exact (@lem1987143 ((real_sub x y) = term3) (term64 x y)). Qed.
Lemma lem1987145 (x : real) (y : real) (z : real) : (term70 x y z) = ((term63 x y z) = term2).
Proof. exact (eq_refl (term70 x y z)). Qed.
Lemma lem1987146 (x : real) (y : real) : (term93 x y) = (term64 x y).
Proof. exact (fun_ext (fun z : real => @lem1987145 x y z)). Qed.
Lemma lem1987147 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1987148 (x : real) (y : real) : (term94 x y) = (term31 x y).
Proof. exact (MK_COMB (@lem1987147) (@lem1987146 x y)). Qed.
Lemma lem1987149 (x : real) (y : real) : (term77 x y) = (term77 x y).
Proof. exact (eq_refl (term77 x y)). Qed.
Lemma lem1987150 (x : real) (y : real) : (term91 x y) = (term79 x y).
Proof. exact (MK_COMB (@lem1987149 x y) (@lem1987148 x y)). Qed.
Lemma lem1987151 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1987152 (x : real) (y : real) : (term95 x y) = (term96 x y).
Proof. exact (MK_COMB (@lem1987151) (@lem1987150 x y)). Qed.
Lemma lem1987153 (x : real) (y : real) (z : real) : (term70 x y z) = ((term63 x y z) = term2).
Proof. exact (eq_refl (term70 x y z)). Qed.
Lemma lem1987154 (x : real) (y : real) : (term77 x y) = (term77 x y).
Proof. exact (eq_refl (term77 x y)). Qed.
Lemma lem1987155 (x : real) (y : real) (z : real) : (term97 x y z) = (term98 x y z).
Proof. exact (MK_COMB (@lem1987154 x y) (@lem1987153 x y z)). Qed.
Lemma lem1987156 (x : real) (y : real) : (term99 x y) = (term100 x y).
Proof. exact (fun_ext (fun z : real => @lem1987155 x y z)). Qed.
Lemma lem1987157 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1987158 (x : real) (y : real) : (term92 x y) = (term101 x y).
Proof. exact (MK_COMB (@lem1987157) (@lem1987156 x y)). Qed.
Lemma lem1987159 (x : real) (y : real) : ((term91 x y) = (term92 x y)) = ((term79 x y) = (term101 x y)).
Proof. exact (MK_COMB (@lem1987152 x y) (@lem1987158 x y)). Qed.
Lemma lem1987160 (x : real) (y : real) : (term79 x y) = (term101 x y).
Proof. exact (EQ_MP (@lem1987159 x y) (@lem1987144 x y)). Qed.
Lemma lem1987161 (x : real) (y : real) : (term84 x y) = (term84 x y).
Proof. exact (eq_refl (term84 x y)). Qed.
Lemma lem1987162 (x : real) (y : real) : (term86 x y) = (term102 x y).
Proof. exact (MK_COMB (@lem1987161 x y) (@lem1987160 x y)). Qed.
Lemma lem1987164 {A : Type'} (P : Prop) (Q : A -> Prop) : (term103 A P Q) = (term104 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem1987165 (P : Prop) (Q : real -> Prop) : (term105 P Q) = (term106 P Q).
Proof. exact (@lem1987164 real P Q). Qed.
Lemma lem1987166 (x : real) (y : real) : (term107 x y) = (term108 x y).
Proof. exact (@lem1987165 (term82 x y) (term100 x y)). Qed.
Lemma lem1987167 (x : real) (y : real) (z : real) : (term109 x y z) = (term98 x y z).
Proof. exact (eq_refl (term109 x y z)). Qed.
Lemma lem1987168 (x : real) (y : real) : (term110 x y) = (term100 x y).
Proof. exact (fun_ext (fun z : real => @lem1987167 x y z)). Qed.
Lemma lem1987169 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1987170 (x : real) (y : real) : (term111 x y) = (term101 x y).
Proof. exact (MK_COMB (@lem1987169) (@lem1987168 x y)). Qed.
Lemma lem1987171 (x : real) (y : real) : (term84 x y) = (term84 x y).
Proof. exact (eq_refl (term84 x y)). Qed.
Lemma lem1987172 (x : real) (y : real) : (term107 x y) = (term102 x y).
Proof. exact (MK_COMB (@lem1987171 x y) (@lem1987170 x y)). Qed.
Lemma lem1987173 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1987174 (x : real) (y : real) : (term112 x y) = (term113 x y).
Proof. exact (MK_COMB (@lem1987173) (@lem1987172 x y)). Qed.
Lemma lem1987175 (x : real) (y : real) (z : real) : (term109 x y z) = (term98 x y z).
Proof. exact (eq_refl (term109 x y z)). Qed.
Lemma lem1987176 (x : real) (y : real) : (term84 x y) = (term84 x y).
Proof. exact (eq_refl (term84 x y)). Qed.
Lemma lem1987177 (x : real) (y : real) (z : real) : (term114 x y z) = (term115 x y z).
Proof. exact (MK_COMB (@lem1987176 x y) (@lem1987175 x y z)). Qed.
Lemma lem1987178 (x : real) (y : real) : (term116 x y) = (term117 x y).
Proof. exact (fun_ext (fun z : real => @lem1987177 x y z)). Qed.
Lemma lem1987179 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1987180 (x : real) (y : real) : (term108 x y) = (term118 x y).
Proof. exact (MK_COMB (@lem1987179) (@lem1987178 x y)). Qed.
Lemma lem1987181 (x : real) (y : real) : ((term107 x y) = (term108 x y)) = ((term102 x y) = (term118 x y)).
Proof. exact (MK_COMB (@lem1987174 x y) (@lem1987180 x y)). Qed.
Lemma lem1987182 (x : real) (y : real) : (term102 x y) = (term118 x y).
Proof. exact (EQ_MP (@lem1987181 x y) (@lem1987166 x y)). Qed.
Lemma lem1987184 (x : real) (y : real) : (term86 x y) = (term118 x y).
Proof. exact (TRANS (@lem1987162 x y) (@lem1987182 x y)). Qed.
Lemma lem1987185 (x : real) (y : real) : (term34 x y) = (term118 x y).
Proof. exact (TRANS (@lem1987131 x y) (@lem1987184 x y)). Qed.
Lemma lem1987186 (x : real) (y : real) (h1 : term34 x y) : term118 x y.
Proof. exact (EQ_MP (@lem1987185 x y) (@lem1987098 x y h1)). Qed.
Lemma lem1987192 (h1 : term16) : term16.
Proof. exact (h1). Qed.
Lemma lem1987193 (x : real) : ((term60 x) = term3) = ((term60 x) = term3).
Proof. exact (eq_refl ((term60 x) = term3)). Qed.
Lemma lem1987194 : term61 = term61.
Proof. exact (fun_ext (fun x : real => @lem1987193 x)). Qed.
Lemma lem1987195 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1987204 : term62 = term62.
Proof. exact (MK_COMB (@lem1987195) (@lem1987194)). Qed.
Lemma lem1987205 (h1 : term62) : term62.
Proof. exact (EQ_MP (@lem1987204) (@lem1987100 h1)). Qed.
Lemma lem1987208 (x : real) : (term119 x) = (x = term3).
Proof. exact (@lem16933 (x = term3)). Qed.
Lemma lem1987209 (x : real) : ((term120 x) = term2) = ((term120 x) = term2).
Proof. exact (eq_refl ((term120 x) = term2)). Qed.
Lemma lem1987210 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1987211 (x : real) : (term121 x) = (term122 x).
Proof. exact (MK_COMB (@lem1987210) (@lem1987208 x)). Qed.
Lemma lem1987212 (x : real) : (term123 x) = (term124 x).
Proof. exact (MK_COMB (@lem1987211 x) (@lem1987209 x)). Qed.
Lemma lem1987213 (x : real) : (term58 x) = (term123 x).
Proof. exact (@lem17265 (term125 x) ((term120 x) = term2)). Qed.
Lemma lem1987214 (x : real) : (term58 x) = (term124 x).
Proof. exact (TRANS (@lem1987213 x) (@lem1987212 x)). Qed.
Lemma lem1987215 : term59 = term126.
Proof. exact (fun_ext (fun x : real => @lem1987214 x)). Qed.
Lemma lem1987216 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1987269 : term41 = term127.
Proof. exact (MK_COMB (@lem1987216) (@lem1987215)). Qed.
Lemma lem1987270 (h1 : term41) : term127.
Proof. exact (EQ_MP (@lem1987269) (@lem1987101 h1)). Qed.
Lemma lem1987271 (x : real) (y : real) (z : real) (h1 : term115 x y z) : term115 x y z.
Proof. exact (h1). Qed.
Lemma lem1987289 (h1 : term16) : term16.
Proof. exact (h1). Qed.
Lemma lem1987306 (x : real) : ((term60 x) = term3) = ((term60 x) = term3).
Proof. exact (eq_refl ((term60 x) = term3)). Qed.
Lemma lem1987307 : term61 = term61.
Proof. exact (fun_ext (fun x : real => @lem1987306 x)). Qed.
Lemma lem1987308 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1987309 : term62 = term62.
Proof. exact (MK_COMB (@lem1987308) (@lem1987307)). Qed.
Lemma lem1987310 (h1 : term62) : term62.
Proof. exact (EQ_MP (@lem1987309) (@lem1987205 h1)). Qed.
Lemma lem1987339 (x : real) : (term124 x) = (term124 x).
Proof. exact (eq_refl (term124 x)). Qed.
Lemma lem1987340 : term126 = term126.
Proof. exact (fun_ext (fun x : real => @lem1987339 x)). Qed.
Lemma lem1987341 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1987342 : term127 = term127.
Proof. exact (MK_COMB (@lem1987341) (@lem1987340)). Qed.
Lemma lem1987343 (h1 : term41) : term127.
Proof. exact (EQ_MP (@lem1987342) (@lem1987270 h1)). Qed.
Lemma lem1987378 (x : real) (y : real) (z : real) : (term98 x y z) = (term98 x y z).
Proof. exact (eq_refl (term98 x y z)). Qed.
Lemma lem1987399 (x : real) (y : real) (z : real) : (term72 x y z) = (term72 x y z).
Proof. exact (eq_refl (term72 x y z)). Qed.
Lemma lem1987400 (x : real) (y : real) : (term74 x y) = (term74 x y).
Proof. exact (fun_ext (fun z : real => @lem1987399 x y z)). Qed.
Lemma lem1987401 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1987402 (x : real) (y : real) : (term75 x y) = (term75 x y).
Proof. exact (MK_COMB (@lem1987401) (@lem1987400 x y)). Qed.
Lemma lem1987419 (x : real) (y : real) : (term80 x y) = (term80 x y).
Proof. exact (eq_refl (term80 x y)). Qed.
Lemma lem1987420 (x : real) (y : real) : (term82 x y) = (term82 x y).
Proof. exact (MK_COMB (@lem1987419 x y) (@lem1987402 x y)). Qed.
Lemma lem1987421 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1987422 (x : real) (y : real) : (term84 x y) = (term84 x y).
Proof. exact (MK_COMB (@lem1987421) (@lem1987420 x y)). Qed.
Lemma lem1987423 (x : real) (y : real) (z : real) : (term115 x y z) = (term115 x y z).
Proof. exact (MK_COMB (@lem1987422 x y) (@lem1987378 x y z)). Qed.
Lemma lem1987424 (x : real) (y : real) (z : real) (h1 : term115 x y z) : term115 x y z.
Proof. exact (EQ_MP (@lem1987423 x y z) (@lem1987271 x y z h1)). Qed.
Lemma lem1987425 (x : real) (y : real) (h1 : term82 x y) : term82 x y.
Proof. exact (h1). Qed.
Lemma lem1987426 (x : real) (y : real) (z : real) (h1 : term98 x y z) : term98 x y z.
Proof. exact (h1). Qed.
Lemma lem1987427 (x : real) (y : real) (h1 : term82 x y) : term75 x y.
Proof. exact (proj2 (@lem1987425 x y h1)). Qed.
Lemma lem1987449 (x : real) : (term124 x) = (term124 x).
Proof. exact (eq_refl (term124 x)). Qed.
Lemma lem1987450 : term126 = term126.
Proof. exact (fun_ext (fun x : real => @lem1987449 x)). Qed.
Lemma lem1987451 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1987453 : term127 = term127.
Proof. exact (MK_COMB (@lem1987451) (@lem1987450)). Qed.
Lemma lem1987454 (h1 : term41) : term127.
Proof. exact (EQ_MP (@lem1987453) (@lem1987343 h1)). Qed.
Lemma lem1987460 (x : real) (y : real) (z : real) : (term72 x y z) = (term72 x y z).
Proof. exact (eq_refl (term72 x y z)). Qed.
Lemma lem1987461 (x : real) (y : real) : (term74 x y) = (term74 x y).
Proof. exact (fun_ext (fun z : real => @lem1987460 x y z)). Qed.
Lemma lem1987462 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1987464 (x : real) (y : real) : (term75 x y) = (term75 x y).
Proof. exact (MK_COMB (@lem1987462) (@lem1987461 x y)). Qed.
Lemma lem1987465 (x : real) (y : real) (h1 : term82 x y) : term75 x y.
Proof. exact (EQ_MP (@lem1987464 x y) (@lem1987427 x y h1)). Qed.
Lemma lem1987469 (h1 : term16) : term16.
Proof. exact (h1). Qed.
Lemma lem1987471 (x : real) : ((term60 x) = term3) = ((term60 x) = term3).
Proof. exact (eq_refl ((term60 x) = term3)). Qed.
Lemma lem1987472 : term61 = term61.
Proof. exact (fun_ext (fun x : real => @lem1987471 x)). Qed.
Lemma lem1987473 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1987475 : term62 = term62.
Proof. exact (MK_COMB (@lem1987473) (@lem1987472)). Qed.
Lemma lem1987476 (h1 : term62) : term62.
Proof. exact (EQ_MP (@lem1987475) (@lem1987310 h1)). Qed.
Lemma lem1987501 (_27744 : real) (h1 : term41) : term128 _27744.
Proof. exact (@lem1987454 h1 _27744). Qed.
Lemma lem1987502 (_27744 : real) : (term128 _27744) = (term124 _27744).
Proof. exact (eq_refl (term128 _27744)). Qed.
Lemma lem1987504 (_27745 : real) (x : real) (y : real) (h1 : term82 x y) : term129 x y _27745.
Proof. exact (@lem1987465 x y h1 _27745). Qed.
Lemma lem1987505 (x : real) (y : real) (_27745 : real) : (term129 x y _27745) = (term72 x y _27745).
Proof. exact (eq_refl (term129 x y _27745)). Qed.
Lemma lem1987507 (_27746 : real) (h1 : term62) : term130 _27746.
Proof. exact (@lem1987476 h1 _27746). Qed.
Lemma lem1987508 (_27746 : real) : (term130 _27746) = ((term60 _27746) = term3).
Proof. exact (eq_refl (term130 _27746)). Qed.
Lemma lem1987522 (_27744 : real) (h1 : term41) : term124 _27744.
Proof. exact (EQ_MP (@lem1987502 _27744) (@lem1987501 _27744 h1)). Qed.
Lemma lem1987526 (_27745 : real) (x : real) (y : real) (h1 : term82 x y) : term72 x y _27745.
Proof. exact (EQ_MP (@lem1987505 x y _27745) (@lem1987504 _27745 x y h1)). Qed.
Lemma lem1987528 (h1 : term16) : term16.
Proof. exact (h1). Qed.
Lemma lem1987608 (x : real) (y : real) (h1 : term82 x y) : term28 x y.
Proof. exact (proj1 (@lem1987425 x y h1)). Qed.
Lemma lem1987609 (x : real) (y : real) (h1 : term82 x y) : term131 x y.
Proof. exact (fun h0 : (real_sub x y) = term3 => @lem1987608 x y h1). Qed.
Lemma lem1987611 (p : Prop) : (term132 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1987612 (x : real) (y : real) : (term131 x y) = (term28 x y).
Proof. exact (@lem1987611 ((real_sub x y) = term3)). Qed.
Lemma lem1987613 (x : real) (y : real) (h1 : term82 x y) : term28 x y.
Proof. exact (EQ_MP (@lem1987612 x y) (@lem1987609 x y h1)). Qed.
Lemma lem1987628 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1987629 (_27744 : real) : (term133 _27744) = (term124 _27744).
Proof. exact (@lem1987628 (_27744 = term3) ((term120 _27744) = term2)). Qed.
Lemma lem1987639 (_27744 : real) : (term134 _27744) = (term134 _27744).
Proof. exact (eq_refl (term134 _27744)). Qed.
Lemma lem1987640 (_27744 : real) : ((term124 _27744) = (term133 _27744)) = ((term124 _27744) = (term124 _27744)).
Proof. exact (MK_COMB (@lem1987639 _27744) (@lem1987629 _27744)). Qed.
Lemma lem1987642 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1987643 (x : Prop) : (x = x) = True.
Proof. exact (@lem1987642 Prop x). Qed.
Lemma lem1987644 (_27744 : real) : ((term124 _27744) = (term124 _27744)) = True.
Proof. exact (@lem1987643 (term124 _27744)). Qed.
Lemma lem1987645 (_27744 : real) : ((term124 _27744) = (term133 _27744)) = True.
Proof. exact (TRANS (@lem1987640 _27744) (@lem1987644 _27744)). Qed.
Lemma lem1987646 (_27744 : real) : True = ((term124 _27744) = (term133 _27744)).
Proof. exact (SYM (@lem1987645 _27744)). Qed.
Lemma lem1987647 (_27744 : real) : (term124 _27744) = (term133 _27744).
Proof. exact (EQ_MP (@lem1987646 _27744) (@lem0)). Qed.
Lemma lem1987648 (_27744 : real) (h1 : term41) : term133 _27744.
Proof. exact (EQ_MP (@lem1987647 _27744) (@lem1987522 _27744 h1)). Qed.
Lemma lem1987650 (b : Prop) (a : Prop) : (a \/ b) = (term135 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1987653 (_27744 : real) : (term133 _27744) = (term58 _27744).
Proof. exact (@lem1987650 (_27744 = term3) ((term120 _27744) = term2)). Qed.
Lemma lem1987656 (_27744 : real) (h1 : term41) : term58 _27744.
Proof. exact (EQ_MP (@lem1987653 _27744) (@lem1987648 _27744 h1)). Qed.
Lemma lem1987657 (x : real) (y : real) (h1 : term41) : term136 x y.
Proof. exact (@lem1987656 (real_sub x y) h1). Qed.
Lemma lem1987660 (x : real) (y : real) (h1 : term41) (h2 : term82 x y) : (term137 x y) = term2.
Proof. exact (@lem1987657 x y h1 (@lem1987613 x y h2)). Qed.
Lemma lem1987661 (x : real) (y : real) (h1 : term41) (h2 : term82 x y) : term138 x y.
Proof. exact (fun h0 : term139 x y => @lem1987660 x y h1 h2). Qed.
Lemma lem1987663 (p : Prop) : (term140 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1987664 (x : real) (y : real) : (term138 x y) = ((term137 x y) = term2).
Proof. exact (@lem1987663 ((term137 x y) = term2)). Qed.
Lemma lem1987665 (x : real) (y : real) (h1 : term41) (h2 : term82 x y) : (term137 x y) = term2.
Proof. exact (EQ_MP (@lem1987664 x y) (@lem1987661 x y h1 h2)). Qed.
Lemma lem1987668 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1987670 (x : real) (y : real) (_27745 : real) : (term72 x y _27745) = (term141 x y _27745).
Proof. exact (@lem1987668 ((term63 x y _27745) = term2)). Qed.
Lemma lem1987673 (_27745 : real) (x : real) (y : real) (h1 : term82 x y) : term141 x y _27745.
Proof. exact (EQ_MP (@lem1987670 x y _27745) (@lem1987526 _27745 x y h1)). Qed.
Lemma lem1987674 (x : real) (y : real) (h1 : term82 x y) : term142 x y.
Proof. exact (@lem1987673 (term143 x y) x y h1). Qed.
Lemma lem1987677 (x : real) (y : real) (h1 : term41) (h2 : term82 x y) : False.
Proof. exact (@lem1987674 x y h2 (@lem1987665 x y h1 h2)). Qed.
Lemma lem1987678 (x : real) (y : real) (h1 : term41) (h2 : term82 x y) : term144.
Proof. exact (fun h0 : ~ False => @lem1987677 x y h1 h2). Qed.
Lemma lem1987680 (p : Prop) : (term140 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1987681 : term144 = False.
Proof. exact (@lem1987680 False). Qed.
Lemma lem1987682 (x : real) (y : real) (h1 : term41) (h2 : term82 x y) : False.
Proof. exact (EQ_MP (@lem1987681) (@lem1987678 x y h1 h2)). Qed.
Lemma lem1987706 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1987707 (_27770 : real) (_27772 : real) (h1 : _27770 = _27772) : _27770 = _27772.
Proof. exact (h1). Qed.
Lemma lem1987708 (_27771 : real) (_27773 : real) (h1 : _27771 = _27773) : _27771 = _27773.
Proof. exact (h1). Qed.
Lemma lem1987709 (_27770 : real) (_27772 : real) (h1 : _27770 = _27772) : (real_mul _27770) = (real_mul _27772).
Proof. exact (MK_COMB (@lem1987706) (@lem1987707 _27770 _27772 h1)). Qed.
Lemma lem1987710 (_27770 : real) (_27772 : real) (_27771 : real) (_27773 : real) (h1 : _27770 = _27772) (h2 : _27771 = _27773) : (real_mul _27770 _27771) = (real_mul _27772 _27773).
Proof. exact (MK_COMB (@lem1987709 _27770 _27772 h1) (@lem1987708 _27771 _27773 h2)). Qed.
Lemma lem1987711 (_27771 : real) (_27773 : real) (_27770 : real) (_27772 : real) (h1 : _27770 = _27772) : term145 _27770 _27771 _27772 _27773.
Proof. exact (fun h0 : _27771 = _27773 => @lem1987710 _27770 _27772 _27771 _27773 h1 h0). Qed.
Lemma lem1987713 (a : Prop) (b : Prop) : (a -> b) = (term146 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1987714 (_27770 : real) (_27771 : real) (_27772 : real) (_27773 : real) : (term145 _27770 _27771 _27772 _27773) = (term147 _27770 _27771 _27772 _27773).
Proof. exact (@lem1987713 (_27771 = _27773) ((real_mul _27770 _27771) = (real_mul _27772 _27773))). Qed.
Lemma lem1987715 (_27771 : real) (_27773 : real) (_27770 : real) (_27772 : real) (h1 : _27770 = _27772) : term147 _27770 _27771 _27772 _27773.
Proof. exact (EQ_MP (@lem1987714 _27770 _27771 _27772 _27773) (@lem1987711 _27771 _27773 _27770 _27772 h1)). Qed.
Lemma lem1987716 (_27770 : real) (_27771 : real) (_27772 : real) (_27773 : real) : term148 _27770 _27771 _27772 _27773.
Proof. exact (fun h0 : _27770 = _27772 => @lem1987715 _27771 _27773 _27770 _27772 h0). Qed.
Lemma lem1987718 (a : Prop) (b : Prop) : (a -> b) = (term146 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1987719 (_27770 : real) (_27771 : real) (_27772 : real) (_27773 : real) : (term148 _27770 _27771 _27772 _27773) = (term149 _27770 _27771 _27772 _27773).
Proof. exact (@lem1987718 (_27770 = _27772) (term147 _27770 _27771 _27772 _27773)). Qed.
Lemma lem1987720 (_27770 : real) (_27771 : real) (_27772 : real) (_27773 : real) : term149 _27770 _27771 _27772 _27773.
Proof. exact (EQ_MP (@lem1987719 _27770 _27771 _27772 _27773) (@lem1987716 _27770 _27771 _27772 _27773)). Qed.
Lemma lem1987746 (x : real) (y : real) (z : real) : term150 x y z.
Proof. exact (@lem21385 real x y z). Qed.
Lemma lem1987750 (x : real) (y : real) (z : real) (h1 : term98 x y z) : (real_sub x y) = term3.
Proof. exact (proj1 (@lem1987426 x y z h1)). Qed.
Lemma lem1987751 (x : real) (y : real) (z : real) (h1 : term98 x y z) : term151 x y.
Proof. exact (fun h0 : term28 x y => @lem1987750 x y z h1). Qed.
Lemma lem1987753 (p : Prop) : (term140 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1987754 (x : real) (y : real) : (term151 x y) = ((real_sub x y) = term3).
Proof. exact (@lem1987753 ((real_sub x y) = term3)). Qed.
Lemma lem1987755 (x : real) (y : real) (z : real) (h1 : term98 x y z) : (real_sub x y) = term3.
Proof. exact (EQ_MP (@lem1987754 x y) (@lem1987751 x y z h1)). Qed.
Lemma lem1987757 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1987758 (z : real) : z = z.
Proof. exact (@lem1987757 z). Qed.
Lemma lem1987759 (z : real) : term152 z.
Proof. exact (fun h0 : term153 z => @lem1987758 z). Qed.
Lemma lem1987761 (p : Prop) : (term140 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1987762 (z : real) : (term152 z) = (z = z).
Proof. exact (@lem1987761 (z = z)). Qed.
Lemma lem1987763 (z : real) : z = z.
Proof. exact (EQ_MP (@lem1987762 z) (@lem1987759 z)). Qed.
Lemma lem1987781 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1987782 (_27770 : real) (_27772 : real) (_27771 : real) (_27773 : real) : (term147 _27770 _27771 _27772 _27773) = (term154 _27770 _27772 _27771 _27773).
Proof. exact (@lem1987781 ((real_mul _27770 _27771) = (real_mul _27772 _27773)) (term27 _27771 _27773)). Qed.
Lemma lem1987792 (_27770 : real) (_27772 : real) : (term155 _27770 _27772) = (term155 _27770 _27772).
Proof. exact (eq_refl (term155 _27770 _27772)). Qed.
Lemma lem1987793 (_27770 : real) (_27772 : real) (_27771 : real) (_27773 : real) : (term149 _27770 _27771 _27772 _27773) = (term156 _27770 _27772 _27771 _27773).
Proof. exact (MK_COMB (@lem1987792 _27770 _27772) (@lem1987782 _27770 _27772 _27771 _27773)). Qed.
Lemma lem1987797 (q : Prop) (p : Prop) (r : Prop) : (term157 p q r) = (term157 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1987798 (_27770 : real) (_27772 : real) (_27771 : real) (_27773 : real) : (term156 _27770 _27772 _27771 _27773) = (term158 _27770 _27772 _27771 _27773).
Proof. exact (@lem1987797 ((real_mul _27770 _27771) = (real_mul _27772 _27773)) (term27 _27770 _27772) (term27 _27771 _27773)). Qed.
Lemma lem1987820 (_27770 : real) (_27772 : real) (_27771 : real) (_27773 : real) : (term149 _27770 _27771 _27772 _27773) = (term158 _27770 _27772 _27771 _27773).
Proof. exact (TRANS (@lem1987793 _27770 _27772 _27771 _27773) (@lem1987798 _27770 _27772 _27771 _27773)). Qed.
Lemma lem1987821 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1987822 (_27770 : real) (_27772 : real) (_27771 : real) (_27773 : real) : (term159 _27770 _27771 _27772 _27773) = (term160 _27770 _27772 _27771 _27773).
Proof. exact (MK_COMB (@lem1987821) (@lem1987820 _27770 _27772 _27771 _27773)). Qed.
Lemma lem1987844 (_27770 : real) (_27772 : real) (_27771 : real) (_27773 : real) : (term158 _27770 _27772 _27771 _27773) = (term158 _27770 _27772 _27771 _27773).
Proof. exact (eq_refl (term158 _27770 _27772 _27771 _27773)). Qed.
Lemma lem1987845 (_27770 : real) (_27772 : real) (_27771 : real) (_27773 : real) : ((term149 _27770 _27771 _27772 _27773) = (term158 _27770 _27772 _27771 _27773)) = ((term158 _27770 _27772 _27771 _27773) = (term158 _27770 _27772 _27771 _27773)).
Proof. exact (MK_COMB (@lem1987822 _27770 _27772 _27771 _27773) (@lem1987844 _27770 _27772 _27771 _27773)). Qed.
Lemma lem1987847 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1987848 (x : Prop) : (x = x) = True.
Proof. exact (@lem1987847 Prop x). Qed.
Lemma lem1987849 (_27770 : real) (_27772 : real) (_27771 : real) (_27773 : real) : ((term158 _27770 _27772 _27771 _27773) = (term158 _27770 _27772 _27771 _27773)) = True.
Proof. exact (@lem1987848 (term158 _27770 _27772 _27771 _27773)). Qed.
Lemma lem1987850 (_27770 : real) (_27772 : real) (_27771 : real) (_27773 : real) : ((term149 _27770 _27771 _27772 _27773) = (term158 _27770 _27772 _27771 _27773)) = True.
Proof. exact (TRANS (@lem1987845 _27770 _27772 _27771 _27773) (@lem1987849 _27770 _27772 _27771 _27773)). Qed.
Lemma lem1987851 (_27770 : real) (_27772 : real) (_27771 : real) (_27773 : real) : True = ((term149 _27770 _27771 _27772 _27773) = (term158 _27770 _27772 _27771 _27773)).
Proof. exact (SYM (@lem1987850 _27770 _27772 _27771 _27773)). Qed.
Lemma lem1987852 (_27770 : real) (_27772 : real) (_27771 : real) (_27773 : real) : (term149 _27770 _27771 _27772 _27773) = (term158 _27770 _27772 _27771 _27773).
Proof. exact (EQ_MP (@lem1987851 _27770 _27772 _27771 _27773) (@lem0)). Qed.
Lemma lem1987853 (_27770 : real) (_27772 : real) (_27771 : real) (_27773 : real) : term158 _27770 _27772 _27771 _27773.
Proof. exact (EQ_MP (@lem1987852 _27770 _27772 _27771 _27773) (@lem1987720 _27770 _27771 _27772 _27773)). Qed.
Lemma lem1987855 (b : Prop) (a : Prop) : (a \/ b) = (term135 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1987856 (_27770 : real) (_27771 : real) (_27772 : real) (_27773 : real) : (term158 _27770 _27772 _27771 _27773) = (term161 _27770 _27771 _27772 _27773).
Proof. exact (@lem1987855 (term162 _27770 _27772 _27771 _27773) ((real_mul _27770 _27771) = (real_mul _27772 _27773))). Qed.
Lemma lem1987858 (a : Prop) (b : Prop) : (term163 a b) = (term164 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1987859 (_27770 : real) (_27772 : real) (_27771 : real) (_27773 : real) : (term165 _27770 _27772 _27771 _27773) = (term166 _27770 _27772 _27771 _27773).
Proof. exact (@lem1987858 (term27 _27770 _27772) (term27 _27771 _27773)). Qed.
Lemma lem1987861 (a : Prop) : (term0 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1987862 (_27770 : real) (_27772 : real) : (term167 _27770 _27772) = (_27770 = _27772).
Proof. exact (@lem1987861 (_27770 = _27772)). Qed.
Lemma lem1987863 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1987864 (_27770 : real) (_27772 : real) : (term168 _27770 _27772) = (term169 _27770 _27772).
Proof. exact (MK_COMB (@lem1987863) (@lem1987862 _27770 _27772)). Qed.
Lemma lem1987866 (a : Prop) : (term0 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1987867 (_27771 : real) (_27773 : real) : (term167 _27771 _27773) = (_27771 = _27773).
Proof. exact (@lem1987866 (_27771 = _27773)). Qed.
Lemma lem1987868 (_27770 : real) (_27772 : real) (_27771 : real) (_27773 : real) : (term166 _27770 _27772 _27771 _27773) = (term170 _27770 _27772 _27771 _27773).
Proof. exact (MK_COMB (@lem1987864 _27770 _27772) (@lem1987867 _27771 _27773)). Qed.
Lemma lem1987869 (_27770 : real) (_27772 : real) (_27771 : real) (_27773 : real) : (term165 _27770 _27772 _27771 _27773) = (term170 _27770 _27772 _27771 _27773).
Proof. exact (TRANS (@lem1987859 _27770 _27772 _27771 _27773) (@lem1987868 _27770 _27772 _27771 _27773)). Qed.
Lemma lem1987870 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1987871 (_27770 : real) (_27772 : real) (_27771 : real) (_27773 : real) : (term171 _27770 _27772 _27771 _27773) = (term172 _27770 _27772 _27771 _27773).
Proof. exact (MK_COMB (@lem1987870) (@lem1987869 _27770 _27772 _27771 _27773)). Qed.
Lemma lem1987872 (_27770 : real) (_27771 : real) (_27772 : real) (_27773 : real) : ((real_mul _27770 _27771) = (real_mul _27772 _27773)) = ((real_mul _27770 _27771) = (real_mul _27772 _27773)).
Proof. exact (eq_refl ((real_mul _27770 _27771) = (real_mul _27772 _27773))). Qed.
Lemma lem1987873 (_27770 : real) (_27771 : real) (_27772 : real) (_27773 : real) : (term161 _27770 _27771 _27772 _27773) = (term173 _27770 _27771 _27772 _27773).
Proof. exact (MK_COMB (@lem1987871 _27770 _27772 _27771 _27773) (@lem1987872 _27770 _27771 _27772 _27773)). Qed.
Lemma lem1987874 (_27770 : real) (_27771 : real) (_27772 : real) (_27773 : real) : (term158 _27770 _27772 _27771 _27773) = (term173 _27770 _27771 _27772 _27773).
Proof. exact (TRANS (@lem1987856 _27770 _27771 _27772 _27773) (@lem1987873 _27770 _27771 _27772 _27773)). Qed.
Lemma lem1987876 (x : real) (y : real) (z : real) (h1 : term98 x y z) : term174 x y z.
Proof. exact (conj (@lem1987755 x y z h1) (@lem1987763 z)). Qed.
Lemma lem1987878 (_27770 : real) (_27771 : real) (_27772 : real) (_27773 : real) : term173 _27770 _27771 _27772 _27773.
Proof. exact (EQ_MP (@lem1987874 _27770 _27771 _27772 _27773) (@lem1987853 _27770 _27772 _27771 _27773)). Qed.
Lemma lem1987879 (x : real) (y : real) (z : real) : term175 x y z.
Proof. exact (@lem1987878 (real_sub x y) z term3 z). Qed.
Lemma lem1987882 (x : real) (y : real) (z : real) (h1 : term98 x y z) : (term63 x y z) = (term60 z).
Proof. exact (@lem1987879 x y z (@lem1987876 x y z h1)). Qed.
Lemma lem1987883 (x : real) (y : real) (z : real) (h1 : term98 x y z) : term176 x y z.
Proof. exact (fun h0 : term177 x y z => @lem1987882 x y z h1). Qed.
Lemma lem1987885 (p : Prop) : (term140 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1987886 (x : real) (y : real) (z : real) : (term176 x y z) = ((term63 x y z) = (term60 z)).
Proof. exact (@lem1987885 ((term63 x y z) = (term60 z))). Qed.
Lemma lem1987887 (x : real) (y : real) (z : real) (h1 : term98 x y z) : (term63 x y z) = (term60 z).
Proof. exact (EQ_MP (@lem1987886 x y z) (@lem1987883 x y z h1)). Qed.
Lemma lem1987889 (x : real) (y : real) (z : real) (h1 : term98 x y z) : (term63 x y z) = term2.
Proof. exact (proj2 (@lem1987426 x y z h1)). Qed.
Lemma lem1987890 (x : real) (y : real) (z : real) (h1 : term98 x y z) : term178 x y z.
Proof. exact (fun h0 : term72 x y z => @lem1987889 x y z h1). Qed.
Lemma lem1987892 (p : Prop) : (term140 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1987893 (x : real) (y : real) (z : real) : (term178 x y z) = ((term63 x y z) = term2).
Proof. exact (@lem1987892 ((term63 x y z) = term2)). Qed.
Lemma lem1987894 (x : real) (y : real) (z : real) (h1 : term98 x y z) : (term63 x y z) = term2.
Proof. exact (EQ_MP (@lem1987893 x y z) (@lem1987890 x y z h1)). Qed.
Lemma lem1987912 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1987913 (y : real) (x : real) (z : real) : (term179 x y z) = (term180 y x z).
Proof. exact (@lem1987912 (y = z) (term27 x z)). Qed.
Lemma lem1987923 (x : real) (y : real) : (term155 x y) = (term155 x y).
Proof. exact (eq_refl (term155 x y)). Qed.
Lemma lem1987924 (y : real) (x : real) (z : real) : (term150 x y z) = (term181 y x z).
Proof. exact (MK_COMB (@lem1987923 x y) (@lem1987913 y x z)). Qed.
Lemma lem1987928 (q : Prop) (p : Prop) (r : Prop) : (term157 p q r) = (term157 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1987929 (y : real) (x : real) (z : real) : (term181 y x z) = (term182 y x z).
Proof. exact (@lem1987928 (y = z) (term27 x y) (term27 x z)). Qed.
Lemma lem1987951 (y : real) (x : real) (z : real) : (term150 x y z) = (term182 y x z).
Proof. exact (TRANS (@lem1987924 y x z) (@lem1987929 y x z)). Qed.
Lemma lem1987952 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1987953 (y : real) (x : real) (z : real) : (term183 x y z) = (term184 y x z).
Proof. exact (MK_COMB (@lem1987952) (@lem1987951 y x z)). Qed.
Lemma lem1987975 (y : real) (x : real) (z : real) : (term182 y x z) = (term182 y x z).
Proof. exact (eq_refl (term182 y x z)). Qed.
Lemma lem1987976 (y : real) (x : real) (z : real) : ((term150 x y z) = (term182 y x z)) = ((term182 y x z) = (term182 y x z)).
Proof. exact (MK_COMB (@lem1987953 y x z) (@lem1987975 y x z)). Qed.
Lemma lem1987978 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1987979 (x : Prop) : (x = x) = True.
Proof. exact (@lem1987978 Prop x). Qed.
Lemma lem1987980 (y : real) (x : real) (z : real) : ((term182 y x z) = (term182 y x z)) = True.
Proof. exact (@lem1987979 (term182 y x z)). Qed.
Lemma lem1987981 (y : real) (x : real) (z : real) : ((term150 x y z) = (term182 y x z)) = True.
Proof. exact (TRANS (@lem1987976 y x z) (@lem1987980 y x z)). Qed.
Lemma lem1987982 (y : real) (x : real) (z : real) : True = ((term150 x y z) = (term182 y x z)).
Proof. exact (SYM (@lem1987981 y x z)). Qed.
Lemma lem1987983 (y : real) (x : real) (z : real) : (term150 x y z) = (term182 y x z).
Proof. exact (EQ_MP (@lem1987982 y x z) (@lem0)). Qed.
Lemma lem1987984 (y : real) (x : real) (z : real) : term182 y x z.
Proof. exact (EQ_MP (@lem1987983 y x z) (@lem1987746 x y z)). Qed.
Lemma lem1987986 (b : Prop) (a : Prop) : (a \/ b) = (term135 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1987987 (x : real) (y : real) (z : real) : (term182 y x z) = (term185 x y z).
Proof. exact (@lem1987986 (term186 y x z) (y = z)). Qed.
Lemma lem1987989 (a : Prop) (b : Prop) : (term163 a b) = (term164 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1987990 (y : real) (x : real) (z : real) : (term187 y x z) = (term188 y x z).
Proof. exact (@lem1987989 (term27 x y) (term27 x z)). Qed.
Lemma lem1987992 (a : Prop) : (term0 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1987993 (x : real) (y : real) : (term167 x y) = (x = y).
Proof. exact (@lem1987992 (x = y)). Qed.
Lemma lem1987994 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1987995 (x : real) (y : real) : (term168 x y) = (term169 x y).
Proof. exact (MK_COMB (@lem1987994) (@lem1987993 x y)). Qed.
Lemma lem1987997 (a : Prop) : (term0 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1987998 (x : real) (z : real) : (term167 x z) = (x = z).
Proof. exact (@lem1987997 (x = z)). Qed.
Lemma lem1987999 (y : real) (x : real) (z : real) : (term188 y x z) = (term189 y x z).
Proof. exact (MK_COMB (@lem1987995 x y) (@lem1987998 x z)). Qed.
Lemma lem1988000 (y : real) (x : real) (z : real) : (term187 y x z) = (term189 y x z).
Proof. exact (TRANS (@lem1987990 y x z) (@lem1987999 y x z)). Qed.
Lemma lem1988001 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1988002 (y : real) (x : real) (z : real) : (term190 y x z) = (term191 y x z).
Proof. exact (MK_COMB (@lem1988001) (@lem1988000 y x z)). Qed.
Lemma lem1988003 (y : real) (z : real) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1988004 (x : real) (y : real) (z : real) : (term185 x y z) = (term192 x y z).
Proof. exact (MK_COMB (@lem1988002 y x z) (@lem1988003 y z)). Qed.
Lemma lem1988005 (x : real) (y : real) (z : real) : (term182 y x z) = (term192 x y z).
Proof. exact (TRANS (@lem1987987 x y z) (@lem1988004 x y z)). Qed.
Lemma lem1988007 (x : real) (y : real) (z : real) (h1 : term98 x y z) : term193 x y z.
Proof. exact (conj (@lem1987887 x y z h1) (@lem1987894 x y z h1)). Qed.
Lemma lem1988009 (x : real) (y : real) (z : real) : term192 x y z.
Proof. exact (EQ_MP (@lem1988005 x y z) (@lem1987984 y x z)). Qed.
Lemma lem1988010 (x : real) (y : real) (z : real) : term194 x y z.
Proof. exact (@lem1988009 (term63 x y z) (term60 z) term2). Qed.
Lemma lem1988013 (x : real) (y : real) (z : real) (h1 : term98 x y z) : (term60 z) = term2.
Proof. exact (@lem1988010 x y z (@lem1988007 x y z h1)). Qed.
Lemma lem1988014 (x : real) (y : real) (z : real) (h1 : term98 x y z) : term195 z.
Proof. exact (fun h0 : term196 z => @lem1988013 x y z h1). Qed.
Lemma lem1988016 (p : Prop) : (term140 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1988017 (z : real) : (term195 z) = ((term60 z) = term2).
Proof. exact (@lem1988016 ((term60 z) = term2)). Qed.
Lemma lem1988018 (x : real) (y : real) (z : real) (h1 : term98 x y z) : (term60 z) = term2.
Proof. exact (EQ_MP (@lem1988017 z) (@lem1988014 x y z h1)). Qed.
Lemma lem1988020 (_27746 : real) (h1 : term62) : (term60 _27746) = term3.
Proof. exact (EQ_MP (@lem1987508 _27746) (@lem1987507 _27746 h1)). Qed.
Lemma lem1988021 (z : real) (h1 : term62) : (term60 z) = term3.
Proof. exact (@lem1988020 z h1). Qed.
Lemma lem1988022 (z : real) (h1 : term62) : term197 z.
Proof. exact (fun h0 : term198 z => @lem1988021 z h1). Qed.
Lemma lem1988024 (p : Prop) : (term140 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1988025 (z : real) : (term197 z) = ((term60 z) = term3).
Proof. exact (@lem1988024 ((term60 z) = term3)). Qed.
Lemma lem1988026 (z : real) (h1 : term62) : (term60 z) = term3.
Proof. exact (EQ_MP (@lem1988025 z) (@lem1988022 z h1)). Qed.
Lemma lem1988027 (x : real) (y : real) (z : real) (h1 : term62) (h2 : term98 x y z) : term199 z.
Proof. exact (conj (@lem1988018 x y z h2) (@lem1988026 z h1)). Qed.
Lemma lem1988029 (x : real) (y : real) (z : real) : term192 x y z.
Proof. exact (EQ_MP (@lem1988005 x y z) (@lem1987984 y x z)). Qed.
Lemma lem1988030 (z : real) : term200 z.
Proof. exact (@lem1988029 (term60 z) term2 term3). Qed.
Lemma lem1988033 (x : real) (y : real) (z : real) (h1 : term62) (h2 : term98 x y z) : term2 = term3.
Proof. exact (@lem1988030 z (@lem1988027 x y z h1 h2)). Qed.
Lemma lem1988034 (x : real) (y : real) (z : real) (h1 : term62) (h2 : term98 x y z) : term201.
Proof. exact (fun h0 : term16 => @lem1988033 x y z h1 h2). Qed.
Lemma lem1988036 (p : Prop) : (term140 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1988037 : term201 = (term2 = term3).
Proof. exact (@lem1988036 (term2 = term3)). Qed.
Lemma lem1988038 (x : real) (y : real) (z : real) (h1 : term62) (h2 : term98 x y z) : term2 = term3.
Proof. exact (EQ_MP (@lem1988037) (@lem1988034 x y z h1 h2)). Qed.
Lemma lem1988041 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1988043 : term16 = term202.
Proof. exact (@lem1988041 (term2 = term3)). Qed.
Lemma lem1988046 (h1 : term16) : term202.
Proof. exact (EQ_MP (@lem1988043) (@lem1987528 h1)). Qed.
Lemma lem1988049 (x : real) (y : real) (z : real) (h1 : term62) (h2 : term16) (h3 : term98 x y z) : False.
Proof. exact (@lem1988046 h2 (@lem1988038 x y z h1 h3)). Qed.
Lemma lem1988050 (x : real) (y : real) (z : real) (h1 : term62) (h2 : term16) (h3 : term98 x y z) : term144.
Proof. exact (fun h0 : ~ False => @lem1988049 x y z h1 h2 h3). Qed.
Lemma lem1988052 (p : Prop) : (term140 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1988053 : term144 = False.
Proof. exact (@lem1988052 False). Qed.
Lemma lem1988054 (x : real) (y : real) (z : real) (h1 : term62) (h2 : term16) (h3 : term98 x y z) : False.
Proof. exact (EQ_MP (@lem1988053) (@lem1988050 x y z h1 h2 h3)). Qed.
Lemma lem1988055 (x : real) (y : real) (z : real) (h1 : term62) (h2 : term16) (h3 : term98 x y z) : term16 = False.
Proof. exact (prop_ext (fun h4 : term16 => @lem1988054 x y z h1 h2 h3) (fun h4 : False => @lem1987528 h2)). Qed.
Lemma lem1988056 (x : real) (y : real) (z : real) (h1 : term62) (h2 : term16) (h3 : term98 x y z) : False.
Proof. exact (EQ_MP (@lem1988055 x y z h1 h2 h3) (@lem1987528 h2)). Qed.
Lemma lem1988057 (x : real) (y : real) (z : real) (h1 : term62) (h2 : term16) (h3 : term98 x y z) : term16 = False.
Proof. exact (prop_ext (fun h4 : term16 => @lem1988056 x y z h1 h2 h3) (fun h4 : False => @lem1987469 h2)). Qed.
Lemma lem1988058 (x : real) (y : real) (z : real) (h1 : term62) (h2 : term16) (h3 : term98 x y z) : False.
Proof. exact (EQ_MP (@lem1988057 x y z h1 h2 h3) (@lem1987469 h2)). Qed.
Lemma lem1988059 (x : real) (y : real) (z : real) (h1 : term62) (h2 : term16) (h3 : term98 x y z) : term62 = False.
Proof. exact (prop_ext (fun h4 : term62 => @lem1988058 x y z h1 h2 h3) (fun h4 : False => @lem1987476 h1)). Qed.
Lemma lem1988060 (x : real) (y : real) (z : real) (h1 : term62) (h2 : term16) (h3 : term98 x y z) : False.
Proof. exact (EQ_MP (@lem1988059 x y z h1 h2 h3) (@lem1987476 h1)). Qed.
Lemma lem1988061 (x : real) (y : real) (z : real) (h1 : term62) (h2 : term16) (h3 : term98 x y z) : term16 = False.
Proof. exact (prop_ext (fun h4 : term16 => @lem1988060 x y z h1 h2 h3) (fun h4 : False => @lem1987469 h2)). Qed.
Lemma lem1988062 (x : real) (y : real) (z : real) (h1 : term62) (h2 : term16) (h3 : term98 x y z) : False.
Proof. exact (EQ_MP (@lem1988061 x y z h1 h2 h3) (@lem1987469 h2)). Qed.
Lemma lem1988063 (x : real) (y : real) (z : real) (h1 : term62) (h2 : term41) (h3 : term16) (h4 : term115 x y z) : False.
Proof. exact (or_elim (@lem1987424 x y z h4) (fun h0 : term82 x y => @lem1987682 x y h2 h0) (fun h0 : term98 x y z => @lem1988062 x y z h1 h3 h0)). Qed.
Lemma lem1988064 (x : real) (y : real) (z : real) (h1 : term62) (h2 : term41) (h3 : term16) (h4 : term115 x y z) : (term115 x y z) = False.
Proof. exact (prop_ext (fun h5 : term115 x y z => @lem1988063 x y z h1 h2 h3 h4) (fun h5 : False => @lem1987424 x y z h4)). Qed.
Lemma lem1988065 (x : real) (y : real) (z : real) (h1 : term62) (h2 : term41) (h3 : term16) (h4 : term115 x y z) : False.
Proof. exact (EQ_MP (@lem1988064 x y z h1 h2 h3 h4) (@lem1987424 x y z h4)). Qed.
Lemma lem1988066 (x : real) (y : real) (z : real) (h1 : term62) (h2 : term41) (h3 : term16) (h4 : term115 x y z) : term62 = False.
Proof. exact (prop_ext (fun h5 : term62 => @lem1988065 x y z h1 h2 h3 h4) (fun h5 : False => @lem1987310 h1)). Qed.
Lemma lem1988067 (x : real) (y : real) (z : real) (h1 : term62) (h2 : term41) (h3 : term16) (h4 : term115 x y z) : False.
Proof. exact (EQ_MP (@lem1988066 x y z h1 h2 h3 h4) (@lem1987310 h1)). Qed.
Lemma lem1988068 (x : real) (y : real) (z : real) (h1 : term62) (h2 : term41) (h3 : term16) (h4 : term115 x y z) : term16 = False.
Proof. exact (prop_ext (fun h5 : term16 => @lem1988067 x y z h1 h2 h3 h4) (fun h5 : False => @lem1987289 h3)). Qed.
Lemma lem1988069 (x : real) (y : real) (z : real) (h1 : term62) (h2 : term41) (h3 : term16) (h4 : term115 x y z) : False.
Proof. exact (EQ_MP (@lem1988068 x y z h1 h2 h3 h4) (@lem1987289 h3)). Qed.
Lemma lem1988070 (x : real) (y : real) (h1 : term62) (h2 : term41) (h3 : term34 x y) (h4 : term16) : False.
Proof. exact (ex_elim (@lem1987186 x y h3) (fun z : real => fun h0 : term117 x y z => @lem1988069 x y z h1 h2 h4 h0)). Qed.
Lemma lem1988071 (x : real) (y : real) (h1 : term62) (h2 : term41) (h3 : term34 x y) (h4 : term16) : term62 = False.
Proof. exact (prop_ext (fun h5 : term62 => @lem1988070 x y h1 h2 h3 h4) (fun h5 : False => @lem1987205 h1)). Qed.
Lemma lem1988072 (x : real) (y : real) (h1 : term62) (h2 : term41) (h3 : term34 x y) (h4 : term16) : False.
Proof. exact (EQ_MP (@lem1988071 x y h1 h2 h3 h4) (@lem1987205 h1)). Qed.
Lemma lem1988073 (x : real) (y : real) (h1 : term62) (h2 : term41) (h3 : term34 x y) (h4 : term16) : term16 = False.
Proof. exact (prop_ext (fun h5 : term16 => @lem1988072 x y h1 h2 h3 h4) (fun h5 : False => @lem1987192 h4)). Qed.
Lemma lem1988074 (x : real) (y : real) (h1 : term62) (h2 : term41) (h3 : term34 x y) (h4 : term16) : False.
Proof. exact (EQ_MP (@lem1988073 x y h1 h2 h3 h4) (@lem1987192 h4)). Qed.
Lemma lem1988075 (x : real) (y : real) (h1 : term62) (h2 : term34 x y) (h3 : term16) : term39.
Proof. exact (fun h0 : term41 => @lem1988074 x y h1 h0 h2 h3). Qed.
Lemma lem1988076 : term39 = term40.
Proof. exact (@lem69 term41). Qed.
Lemma lem1988077 (x : real) (y : real) (h1 : term62) (h2 : term34 x y) (h3 : term16) : term40.
Proof. exact (EQ_MP (@lem1988076) (@lem1988075 x y h1 h2 h3)). Qed.
Lemma lem1988078 (x : real) (y : real) (h1 : term34 x y) (h2 : term16) : term44.
Proof. exact (fun h0 : term62 => @lem1988077 x y h0 h1 h2). Qed.
Lemma lem1988079 (x : real) (y : real) (h1 : term34 x y) : term47.
Proof. exact (fun h0 : term16 => @lem1988078 x y h1 h0). Qed.
Lemma lem1988080 (x : real) (y : real) : term49 x y.
Proof. exact (fun h0 : term34 x y => @lem1988079 x y h0). Qed.
Lemma lem1988085 (y : real) : term53 y.
Proof. exact (fun x : real => @lem1988080 x y). Qed.
Lemma lem1988090 : term57.
Proof. exact (fun y : real => @lem1988085 y). Qed.
Lemma lem1988091 : term56.
Proof. exact (EQ_MP (@lem1987097) (@lem1988090)). Qed.
Lemma lem1988092 (y : real) : term203 y.
Proof. exact (@lem1988091 y). Qed.
Lemma lem1988093 (y : real) : (term203 y) = (term52 y).
Proof. exact (eq_refl (term203 y)). Qed.
Lemma lem1988094 (y : real) : term52 y.
Proof. exact (EQ_MP (@lem1988093 y) (@lem1988092 y)). Qed.
Lemma lem1988095 (y : real) (x : real) : term204 y x.
Proof. exact (@lem1988094 y x). Qed.
Lemma lem1988096 (x : real) (y : real) : (term204 y x) = (term35 x y).
Proof. exact (eq_refl (term204 y x)). Qed.
Lemma lem1988097 (x : real) (y : real) : term35 x y.
Proof. exact (EQ_MP (@lem1988096 x y) (@lem1988095 y x)). Qed.
Lemma lem1988099 (x : real) (y : real) : term35 x y.
Proof. exact (@lem1986948 x y (@lem1988097 x y)). Qed.
Lemma lem1988100 (x : real) (y : real) (h1 : term34 x y) : term46.
Proof. exact (@lem1988099 x y (@lem1986933 x y h1)). Qed.
Lemma lem1988101 (x : real) (y : real) (h1 : term34 x y) : term43.
Proof. exact (@lem1988100 x y h1 (@lem1986889)). Qed.
Lemma lem1988102 (x : real) (y : real) (h1 : term34 x y) : term39.
Proof. exact (@lem1988101 x y h1 (@lem1357243)). Qed.
Lemma lem1988103 (x : real) (y : real) (h1 : term34 x y) : False.
Proof. exact (@lem1988102 x y h1 (@lem1591985)). Qed.
Lemma lem1988104 (x : real) (y : real) (h1 : term34 x y) : (term34 x y) = False.
Proof. exact (prop_ext (fun h2 : term34 x y => @lem1988103 x y h1) (fun h2 : False => @lem1986933 x y h1)). Qed.
Lemma lem1988105 (x : real) (y : real) (h1 : term34 x y) : False.
Proof. exact (EQ_MP (@lem1988104 x y h1) (@lem1986933 x y h1)). Qed.
Lemma lem1988106 (x : real) (y : real) : term33 x y.
Proof. exact (fun h0 : term34 x y => @lem1988105 x y h0). Qed.
Lemma lem1988107 (x : real) (y : real) : (term28 x y) = (term31 x y).
Proof. exact (EQ_MP (@lem1986932 x y) (@lem1988106 x y)). Qed.
Lemma lem1988108 (x : real) (y : real) : (term27 x y) = (term31 x y).
Proof. exact (EQ_MP (@lem1986928 x y) (@lem1988107 x y)). Qed.
Lemma lem1988113 (x : real) : term205 x.
Proof. exact (fun y : real => @lem1988108 x y). Qed.
Lemma lem1988118 : term206.
Proof. exact (fun x : real => @lem1988113 x). Qed.
