Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_ABS_POS_term_abbrevs.
Require Import thm0_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1482702_spec.
Require Import thm1483440_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483460_spec.
Require Import thm1483519_spec.
Require Import thm1483533_spec.
Require Import thm1483568_spec.
Require Import thm1483584_spec.
Require Import thm18392_spec.
Require Import thm912739_spec.
Lemma lem1531905 (P : real -> Prop) : (term0 P) = (term1 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1531906 : term2 = term3.
Proof. exact (@lem1531905 term4). Qed.
Lemma lem1531907 (x : real) : (term5 x) = (term6 x).
Proof. exact (eq_refl (term5 x)). Qed.
Lemma lem1531908 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1531910 (x : real) : (term7 x) = (term8 x).
Proof. exact (MK_COMB (@lem1531908) (@lem1531907 x)). Qed.
Lemma lem1531911 : term9 = term10.
Proof. exact (fun_ext (fun x : real => @lem1531910 x)). Qed.
Lemma lem1531912 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1531913 : term3 = term11.
Proof. exact (MK_COMB (@lem1531912) (@lem1531911)). Qed.
Lemma lem1531915 : term2 = term11.
Proof. exact (TRANS (@lem1531906) (@lem1531913)). Qed.
Lemma lem1531918 (x : real) : (term8 x) = (term8 x).
Proof. exact (eq_refl (term8 x)). Qed.
Lemma lem1531919 : term10 = term10.
Proof. exact (fun_ext (fun x : real => @lem1531918 x)). Qed.
Lemma lem1531920 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1531921 : term11 = term11.
Proof. exact (MK_COMB (@lem1531920) (@lem1531919)). Qed.
Lemma lem1531922 : term2 = term11.
Proof. exact (TRANS (@lem1531915) (@lem1531921)). Qed.
Lemma lem1531923 (x : real) : (term8 x) = (term12 x).
Proof. exact (@lem1483533 term13 (real_abs x)). Qed.
Lemma lem1531929 (x : real) : (term14 x) = (term15 x).
Proof. exact (@lem1483519 term13 (real_abs x)). Qed.
Lemma lem1531934 (x : real) : (term15 x) = (term16 x).
Proof. exact (@lem1483448 (term16 x)). Qed.
Lemma lem1531936 (x : real) : (term14 x) = (term16 x).
Proof. exact (TRANS (@lem1531929 x) (@lem1531934 x)). Qed.
Lemma lem1531937 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1531938 (x : real) : (term17 x) = (term18 x).
Proof. exact (MK_COMB (@lem1531937) (@lem1531936 x)). Qed.
Lemma lem1531939 : term13 = term13.
Proof. exact (eq_refl term13). Qed.
Lemma lem1531940 (x : real) : (term12 x) = (term19 x).
Proof. exact (MK_COMB (@lem1531938 x) (@lem1531939)). Qed.
Lemma lem1531941 (x : real) : (term8 x) = (term19 x).
Proof. exact (TRANS (@lem1531923 x) (@lem1531940 x)). Qed.
Lemma lem1531942 : term10 = term20.
Proof. exact (fun_ext (fun x : real => @lem1531941 x)). Qed.
Lemma lem1531943 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1531944 : term11 = term21.
Proof. exact (MK_COMB (@lem1531943) (@lem1531942)). Qed.
Lemma lem1531955 : term2 = term21.
Proof. exact (TRANS (@lem1531922) (@lem1531944)). Qed.
Lemma lem1531956 (x : real) : (term19 x) = (term19 x).
Proof. exact (eq_refl (term19 x)). Qed.
Lemma lem1531957 : term20 = term20.
Proof. exact (fun_ext (fun x : real => @lem1531956 x)). Qed.
Lemma lem1531958 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1531959 : term21 = term21.
Proof. exact (MK_COMB (@lem1531958) (@lem1531957)). Qed.
Lemma lem1531960 : term2 = term21.
Proof. exact (TRANS (@lem1531955) (@lem1531959)). Qed.
Lemma lem1531962 (x : real) (r : real) : (term22 x r) = (term23 x r).
Proof. exact (proj1 (@lem1482702 x (@el real) (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1531963 (x : real) : (term19 x) = (term24 x).
Proof. exact (@lem1531962 x term13). Qed.
Lemma lem1531970 (x : real) : (term25 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1531971 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1531972 (x : real) : (term26 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1531971) (@lem1531970 x)). Qed.
Lemma lem1531973 : term13 = term13.
Proof. exact (eq_refl term13). Qed.
Lemma lem1531974 (x : real) : (term27 x) = (term28 x).
Proof. exact (MK_COMB (@lem1531972 x) (@lem1531973)). Qed.
Lemma lem1531987 (x : real) : (term29 x) = (term29 x).
Proof. exact (eq_refl (term29 x)). Qed.
Lemma lem1531988 (x : real) : (term24 x) = (term30 x).
Proof. exact (MK_COMB (@lem1531987 x) (@lem1531974 x)). Qed.
Lemma lem1531991 (x : real) : (term19 x) = (term30 x).
Proof. exact (TRANS (@lem1531963 x) (@lem1531988 x)). Qed.
Lemma lem1531992 (x : real) (h1 : term30 x) : term30 x.
Proof. exact (h1). Qed.
Lemma lem1531993 (x : real) (h1 : term30 x) : term28 x.
Proof. exact (proj2 (@lem1531992 x h1)). Qed.
Lemma lem1531994 (x : real) (h1 : term30 x) : term31 x.
Proof. exact (proj1 (@lem1531992 x h1)). Qed.
Lemma lem1531996 (n : nat) (m : nat) : (term32 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1531997 : term33 = term34.
Proof. exact (@lem1531996 (NUMERAL 0) term35). Qed.
Lemma lem1531998 : term36 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1531999 (h1 : term36 = (BIT1 0)) : term34 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1532000 : (term36 = (BIT1 0)) = (term34 = True).
Proof. exact (prop_ext (fun h1 : term36 = (BIT1 0) => @lem1531999 h1) (fun h1 : term34 = True => @lem1531998)). Qed.
Lemma lem1532001 : term34 = True.
Proof. exact (EQ_MP (@lem1532000) (@lem1531998)). Qed.
Lemma lem1532002 : term33 = True.
Proof. exact (TRANS (@lem1531997) (@lem1532001)). Qed.
Lemma lem1532003 : True = term33.
Proof. exact (SYM (@lem1532002)). Qed.
Lemma lem1532004 : term33.
Proof. exact (EQ_MP (@lem1532003) (@lem0)). Qed.
Lemma lem1532005 (x : real) (h1 : term30 x) : term37 x.
Proof. exact (conj (@lem1532004) (@lem1531993 x h1)). Qed.
Lemma lem1532007 (x : real) (y : real) : term38 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1532008 (x : real) : term39 x.
Proof. exact (@lem1532007 term40 x). Qed.
Lemma lem1532009 (x : real) (h1 : term30 x) : term27 x.
Proof. exact (@lem1532008 x (@lem1532005 x h1)). Qed.
Lemma lem1532010 (x : real) : (term25 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1532011 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1532012 (x : real) : (term26 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1532011) (@lem1532010 x)). Qed.
Lemma lem1532013 : term13 = term13.
Proof. exact (eq_refl term13). Qed.
Lemma lem1532014 (x : real) : (term27 x) = (term28 x).
Proof. exact (MK_COMB (@lem1532012 x) (@lem1532013)). Qed.
Lemma lem1532015 (x : real) (h1 : term30 x) : term28 x.
Proof. exact (EQ_MP (@lem1532014 x) (@lem1532009 x h1)). Qed.
Lemma lem1532017 (n : nat) (m : nat) : (term32 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1532018 : term33 = term34.
Proof. exact (@lem1532017 (NUMERAL 0) term35). Qed.
Lemma lem1532019 : term36 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1532020 (h1 : term36 = (BIT1 0)) : term34 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1532021 : (term36 = (BIT1 0)) = (term34 = True).
Proof. exact (prop_ext (fun h1 : term36 = (BIT1 0) => @lem1532020 h1) (fun h1 : term34 = True => @lem1532019)). Qed.
Lemma lem1532022 : term34 = True.
Proof. exact (EQ_MP (@lem1532021) (@lem1532019)). Qed.
Lemma lem1532023 : term33 = True.
Proof. exact (TRANS (@lem1532018) (@lem1532022)). Qed.
Lemma lem1532024 : True = term33.
Proof. exact (SYM (@lem1532023)). Qed.
Lemma lem1532025 : term33.
Proof. exact (EQ_MP (@lem1532024) (@lem0)). Qed.
Lemma lem1532026 (x : real) (h1 : term30 x) : term41 x.
Proof. exact (conj (@lem1532025) (@lem1531994 x h1)). Qed.
Lemma lem1532028 (x : real) (y : real) : term38 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1532029 (x : real) : term42 x.
Proof. exact (@lem1532028 term40 (term43 x)). Qed.
Lemma lem1532030 (x : real) (h1 : term30 x) : term44 x.
Proof. exact (@lem1532029 x (@lem1532026 x h1)). Qed.
Lemma lem1532031 (x : real) : (term45 x) = (term43 x).
Proof. exact (@lem1483460 (term43 x)). Qed.
Lemma lem1532032 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1532033 (x : real) : (term46 x) = (term47 x).
Proof. exact (MK_COMB (@lem1532032) (@lem1532031 x)). Qed.
Lemma lem1532034 : term13 = term13.
Proof. exact (eq_refl term13). Qed.
Lemma lem1532035 (x : real) : (term44 x) = (term31 x).
Proof. exact (MK_COMB (@lem1532033 x) (@lem1532034)). Qed.
Lemma lem1532036 (x : real) (h1 : term30 x) : term31 x.
Proof. exact (EQ_MP (@lem1532035 x) (@lem1532030 x h1)). Qed.
Lemma lem1532037 (x : real) (h1 : term30 x) : term30 x.
Proof. exact (conj (@lem1532036 x h1) (@lem1532015 x h1)). Qed.
Lemma lem1532039 (x : real) (y : real) : term48 x y.
Proof. exact (proj2 (@lem1483584 x y)). Qed.
Lemma lem1532040 (x : real) : term49 x.
Proof. exact (@lem1532039 (term43 x) x). Qed.
Lemma lem1532041 (x : real) (h1 : term30 x) : term50 x.
Proof. exact (@lem1532040 x (@lem1532037 x h1)). Qed.
Lemma lem1532042 (x : real) : (term51 x) = (term52 x).
Proof. exact (@lem1483440 term53 x). Qed.
Lemma lem1532044 (m : nat) : (term54 m) = term13.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1532045 : term55 = term13.
Proof. exact (@lem1532044 term35). Qed.
Lemma lem1532046 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1532047 : term56 = term57.
Proof. exact (MK_COMB (@lem1532046) (@lem1532045)). Qed.
Lemma lem1532048 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1532049 (x : real) : (term52 x) = (term58 x).
Proof. exact (MK_COMB (@lem1532047) (@lem1532048 x)). Qed.
Lemma lem1532050 (x : real) : (term51 x) = (term58 x).
Proof. exact (TRANS (@lem1532042 x) (@lem1532049 x)). Qed.
Lemma lem1532051 (x : real) : (term58 x) = term13.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1532052 (x : real) : (term51 x) = term13.
Proof. exact (TRANS (@lem1532050 x) (@lem1532051 x)). Qed.
Lemma lem1532053 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1532054 (x : real) : (term59 x) = term60.
Proof. exact (MK_COMB (@lem1532053) (@lem1532052 x)). Qed.
Lemma lem1532055 : term13 = term13.
Proof. exact (eq_refl term13). Qed.
Lemma lem1532056 (x : real) : (term50 x) = term61.
Proof. exact (MK_COMB (@lem1532054 x) (@lem1532055)). Qed.
Lemma lem1532057 (x : real) (h1 : term30 x) : term61.
Proof. exact (EQ_MP (@lem1532056 x) (@lem1532041 x h1)). Qed.
Lemma lem1532059 (n : nat) (m : nat) : (term32 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1532060 : term61 = term62.
Proof. exact (@lem1532059 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1532061 : term62 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1532062 : term61 = False.
Proof. exact (TRANS (@lem1532060) (@lem1532061)). Qed.
Lemma lem1532063 (x : real) (h1 : term30 x) : False.
Proof. exact (EQ_MP (@lem1532062) (@lem1532057 x h1)). Qed.
Lemma lem1532064 (x : real) (h1 : term19 x) : term19 x.
Proof. exact (h1). Qed.
Lemma lem1532065 (x : real) (h1 : term19 x) : term30 x.
Proof. exact (EQ_MP (@lem1531991 x) (@lem1532064 x h1)). Qed.
Lemma lem1532066 (x : real) (h1 : term19 x) : (term30 x) = False.
Proof. exact (prop_ext (fun h2 : term30 x => @lem1532063 x h2) (fun h2 : False => @lem1532065 x h1)). Qed.
Lemma lem1532067 (x : real) (h1 : term19 x) : False.
Proof. exact (EQ_MP (@lem1532066 x h1) (@lem1532065 x h1)). Qed.
Lemma lem1532068 (h1 : term21) : term21.
Proof. exact (h1). Qed.
Lemma lem1532069 (h1 : term21) : False.
Proof. exact (ex_elim (@lem1532068 h1) (fun x : real => fun h0 : term20 x => @lem1532067 x h0)). Qed.
Lemma lem1532070 (h1 : term2) : term2.
Proof. exact (h1). Qed.
Lemma lem1532071 (h1 : term2) : term21.
Proof. exact (EQ_MP (@lem1531960) (@lem1532070 h1)). Qed.
Lemma lem1532072 (h1 : term2) : term21 = False.
Proof. exact (prop_ext (fun h2 : term21 => @lem1532069 h2) (fun h2 : False => @lem1532071 h1)). Qed.
Lemma lem1532073 (h1 : term2) : False.
Proof. exact (EQ_MP (@lem1532072 h1) (@lem1532071 h1)). Qed.
Lemma lem1532074 : term63.
Proof. exact (fun h0 : term2 => @lem1532073 h0). Qed.
Lemma lem1532075 : term64.
Proof. exact (@lem1386578 term65). Qed.
Lemma lem1532076 : term65.
Proof. exact (@lem1532075 (@lem1532074)). Qed.
