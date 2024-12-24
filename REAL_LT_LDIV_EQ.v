Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LT_LDIV_EQ_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import REAL_LE_RDIV_EQ_spec.
Require Import REAL_NOT_LE_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm82_spec.
Lemma lem1628916 (y : real) (x : real) (h1 : (term0 x y) = (real_lt y x)) : (term0 x y) = (real_lt y x).
Proof. exact (h1). Qed.
Lemma lem1628917 (y : real) (x : real) (h1 : (term0 x y) = (real_lt y x)) : (real_lt y x) = (term0 x y).
Proof. exact (SYM (@lem1628916 y x h1)). Qed.
Lemma lem1628918 (x : real) (y : real) (h1 : (real_lt y x) = (term0 x y)) : (real_lt y x) = (term0 x y).
Proof. exact (h1). Qed.
Lemma lem1628919 (x : real) (y : real) (h1 : (real_lt y x) = (term0 x y)) : (term0 x y) = (real_lt y x).
Proof. exact (SYM (@lem1628918 x y h1)). Qed.
Lemma lem1628920 (x : real) (y : real) : ((term0 x y) = (real_lt y x)) = ((real_lt y x) = (term0 x y)).
Proof. exact (prop_ext (fun h1 : (term0 x y) = (real_lt y x) => @lem1628917 y x h1) (fun h1 : (real_lt y x) = (term0 x y) => @lem1628919 x y h1)). Qed.
Lemma lem1628921 (x : real) : (term1 x) = (term2 x).
Proof. exact (fun_ext (fun y : real => @lem1628920 x y)). Qed.
Lemma lem1628922 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1628923 (x : real) : (term3 x) = (term4 x).
Proof. exact (MK_COMB (@lem1628922) (@lem1628921 x)). Qed.
Lemma lem1628924 : term5 = term6.
Proof. exact (fun_ext (fun x : real => @lem1628923 x)). Qed.
Lemma lem1628925 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1628926 : term7 = term8.
Proof. exact (MK_COMB (@lem1628925) (@lem1628924)). Qed.
Lemma lem1628927 : term8.
Proof. exact (EQ_MP (@lem1628926) (@lem1495933)). Qed.
Lemma lem1628928 (x : real) : term9 x.
Proof. exact (@lem1628574 x). Qed.
Lemma lem1628929 (x : real) : (term9 x) = (term10 x).
Proof. exact (eq_refl (term9 x)). Qed.
Lemma lem1628930 (x : real) : term10 x.
Proof. exact (EQ_MP (@lem1628929 x) (@lem1628928 x)). Qed.
Lemma lem1628931 (x : real) (y : real) : term11 x y.
Proof. exact (@lem1628930 x y). Qed.
Lemma lem1628932 (x : real) (y : real) : (term11 x y) = (term12 x y).
Proof. exact (eq_refl (term11 x y)). Qed.
Lemma lem1628933 (x : real) (y : real) : term12 x y.
Proof. exact (EQ_MP (@lem1628932 x y) (@lem1628931 x y)). Qed.
Lemma lem1628934 (x : real) (y : real) (z : real) : term13 x y z.
Proof. exact (@lem1628933 x y z). Qed.
Lemma lem1628935 (x : real) (z : real) (y : real) : (term13 x y z) = (term14 x z y).
Proof. exact (eq_refl (term13 x y z)). Qed.
Lemma lem1628936 (x : real) (z : real) (y : real) : term14 x z y.
Proof. exact (EQ_MP (@lem1628935 x z y) (@lem1628934 x y z)). Qed.
Lemma lem1628937 (z : real) (h1 : term15 z) : term15 z.
Proof. exact (h1). Qed.
Lemma lem1628938 (x : real) (y : real) (z : real) (h1 : term15 z) : (term16 x y z) = (term17 x z y).
Proof. exact (@lem1628936 x z y (@lem1628937 z h1)). Qed.
Lemma lem1628944 (x : real) : term18 x.
Proof. exact (@lem1628927 x). Qed.
Lemma lem1628945 (x : real) : (term18 x) = (term4 x).
Proof. exact (eq_refl (term18 x)). Qed.
Lemma lem1628946 (x : real) : term4 x.
Proof. exact (EQ_MP (@lem1628945 x) (@lem1628944 x)). Qed.
Lemma lem1628947 (x : real) (y : real) : term19 x y.
Proof. exact (@lem1628946 x y). Qed.
Lemma lem1628948 (x : real) (y : real) : (term19 x y) = ((real_lt y x) = (term0 x y)).
Proof. exact (eq_refl (term19 x y)). Qed.
Lemma lem1628965 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term20 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1628966 (p : Prop) (q : Prop) (p' : Prop) : term21 p q p'.
Proof. exact (fun q' : Prop => @lem1628965 p q p' q'). Qed.
Lemma lem1628967 (p : Prop) (q : Prop) : term22 p q.
Proof. exact (fun p' : Prop => @lem1628966 p q p'). Qed.
Lemma lem1628968 (x : real) (y : real) (z : real) : term23 x y z.
Proof. exact (@lem1628967 (term15 z) ((term24 x z y) = (term25 x y z))). Qed.
Lemma lem1628969 (x : real) (y : real) (z : real) (p' : Prop) : term26 x y z p'.
Proof. exact (@lem1628968 x y z p'). Qed.
Lemma lem1628970 (x : real) (y : real) (z : real) (p' : Prop) : (term26 x y z p') = (term27 x y z p').
Proof. exact (eq_refl (term26 x y z p')). Qed.
Lemma lem1628971 (x : real) (y : real) (z : real) (p' : Prop) : term27 x y z p'.
Proof. exact (EQ_MP (@lem1628970 x y z p') (@lem1628969 x y z p')). Qed.
Lemma lem1628972 (x : real) (y : real) (z : real) (p' : Prop) (q' : Prop) : term28 x y z p' q'.
Proof. exact (@lem1628971 x y z p' q'). Qed.
Lemma lem1628973 (x : real) (y : real) (z : real) (p' : Prop) (q' : Prop) : (term28 x y z p' q') = (term29 x y z p' q').
Proof. exact (eq_refl (term28 x y z p' q')). Qed.
Lemma lem1628974 (x : real) (y : real) (z : real) (p' : Prop) (q' : Prop) : term29 x y z p' q'.
Proof. exact (EQ_MP (@lem1628973 x y z p' q') (@lem1628972 x y z p' q')). Qed.
Lemma lem1628976 (x : real) (y : real) : (real_lt y x) = (term0 x y).
Proof. exact (EQ_MP (@lem1628948 x y) (@lem1628947 x y)). Qed.
Lemma lem1628977 (z : real) : (term15 z) = (term30 z).
Proof. exact (@lem1628976 z term31). Qed.
Lemma lem1628978 (x : real) (y : real) (z : real) (q' : Prop) : term32 x y z q'.
Proof. exact (@lem1628974 x y z (term30 z) q'). Qed.
Lemma lem1628979 (x : real) (y : real) (z : real) (q' : Prop) : term33 x y z q'.
Proof. exact (@lem1628978 x y z q' (@lem1628977 z)). Qed.
Lemma lem1628980 (z : real) (h1 : term30 z) : term30 z.
Proof. exact (h1). Qed.
Lemma lem1628981 (z : real) : term34 z.
Proof. exact (@lem82 (term35 z)). Qed.
Lemma lem1628986 (x : real) (y : real) : (real_lt y x) = (term0 x y).
Proof. exact (EQ_MP (@lem1628948 x y) (@lem1628947 x y)). Qed.
Lemma lem1628987 (y : real) (x : real) (z : real) : (term24 x z y) = (term36 y x z).
Proof. exact (@lem1628986 y (real_div x z)). Qed.
Lemma lem1628989 (x : real) (z : real) (y : real) : term14 x z y.
Proof. exact (fun h0 : term15 z => @lem1628938 x y z h0). Qed.
Lemma lem1628990 (y : real) (z : real) (x : real) : term14 y z x.
Proof. exact (@lem1628989 y z x). Qed.
Lemma lem1628992 (x : real) (y : real) : (real_lt y x) = (term0 x y).
Proof. exact (EQ_MP (@lem1628948 x y) (@lem1628947 x y)). Qed.
Lemma lem1628993 (z : real) : (term15 z) = (term30 z).
Proof. exact (@lem1628992 z term31). Qed.
Lemma lem1628995 (z : real) (h1 : term30 z) : (term35 z) = False.
Proof. exact (@lem1628981 z (@lem1628980 z h1)). Qed.
Lemma lem1628996 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1628997 (z : real) (h1 : term30 z) : (term30 z) = (~ False).
Proof. exact (MK_COMB (@lem1628996) (@lem1628995 z h1)). Qed.
Lemma lem1628999 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1629000 (z : real) (h1 : term30 z) : (term30 z) = True.
Proof. exact (TRANS (@lem1628997 z h1) (@lem1628999)). Qed.
Lemma lem1629001 (z : real) (h1 : term30 z) : (term15 z) = True.
Proof. exact (TRANS (@lem1628993 z) (@lem1629000 z h1)). Qed.
Lemma lem1629002 (z : real) (h1 : term30 z) : True = (term15 z).
Proof. exact (SYM (@lem1629001 z h1)). Qed.
Lemma lem1629003 (z : real) (h1 : term30 z) : term15 z.
Proof. exact (EQ_MP (@lem1629002 z h1) (@lem0)). Qed.
Lemma lem1629004 (y : real) (x : real) (z : real) (h1 : term30 z) : (term16 y x z) = (term17 y z x).
Proof. exact (@lem1628990 y z x (@lem1629003 z h1)). Qed.
Lemma lem1629005 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1629006 (y : real) (x : real) (z : real) (h1 : term30 z) : (term36 y x z) = (term37 y z x).
Proof. exact (MK_COMB (@lem1629005) (@lem1629004 y x z h1)). Qed.
Lemma lem1629007 (y : real) (x : real) (z : real) (h1 : term30 z) : (term24 x z y) = (term37 y z x).
Proof. exact (TRANS (@lem1628987 y x z) (@lem1629006 y x z h1)). Qed.
Lemma lem1629008 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1629009 (y : real) (x : real) (z : real) (h1 : term30 z) : (term38 x z y) = (term39 y z x).
Proof. exact (MK_COMB (@lem1629008) (@lem1629007 y x z h1)). Qed.
Lemma lem1629011 (x : real) (y : real) : (real_lt y x) = (term0 x y).
Proof. exact (EQ_MP (@lem1628948 x y) (@lem1628947 x y)). Qed.
Lemma lem1629012 (y : real) (z : real) (x : real) : (term25 x y z) = (term37 y z x).
Proof. exact (@lem1629011 (real_mul y z) x). Qed.
Lemma lem1629013 (y : real) (x : real) (z : real) (h1 : term30 z) : ((term24 x z y) = (term25 x y z)) = ((term37 y z x) = (term37 y z x)).
Proof. exact (MK_COMB (@lem1629009 y x z h1) (@lem1629012 y z x)). Qed.
Lemma lem1629015 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1629016 (x : Prop) : (x = x) = True.
Proof. exact (@lem1629015 Prop x). Qed.
Lemma lem1629017 (y : real) (z : real) (x : real) : ((term37 y z x) = (term37 y z x)) = True.
Proof. exact (@lem1629016 (term37 y z x)). Qed.
Lemma lem1629018 (x : real) (y : real) (z : real) (h1 : term30 z) : ((term24 x z y) = (term25 x y z)) = True.
Proof. exact (TRANS (@lem1629013 y x z h1) (@lem1629017 y z x)). Qed.
Lemma lem1629019 (x : real) (y : real) (z : real) : term40 x y z.
Proof. exact (fun h0 : term30 z => @lem1629018 x y z h0). Qed.
Lemma lem1629020 (x : real) (y : real) (z : real) : term41 x y z.
Proof. exact (@lem1628979 x y z True). Qed.
Lemma lem1629021 (x : real) (y : real) (z : real) : (term42 x y z) = (term43 z).
Proof. exact (@lem1629020 x y z (@lem1629019 x y z)). Qed.
Lemma lem1629023 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1629024 (z : real) : (term43 z) = True.
Proof. exact (@lem1629023 (term30 z)). Qed.
Lemma lem1629025 (x : real) (y : real) (z : real) : (term42 x y z) = True.
Proof. exact (TRANS (@lem1629021 x y z) (@lem1629024 z)). Qed.
Lemma lem1629026 (x : real) (y : real) : (term44 x y) = term45.
Proof. exact (fun_ext (fun z : real => @lem1629025 x y z)). Qed.
Lemma lem1629027 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1629028 (x : real) (y : real) : (term46 x y) = term47.
Proof. exact (MK_COMB (@lem1629027) (@lem1629026 x y)). Qed.
Lemma lem1629030 {A : Type'} (t : Prop) : (term48 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1629031 (t : Prop) : (term49 t) = t.
Proof. exact (@lem1629030 real t). Qed.
Lemma lem1629032 : term47 = True.
Proof. exact (@lem1629031 True). Qed.
Lemma lem1629033 (x : real) (y : real) : (term46 x y) = True.
Proof. exact (TRANS (@lem1629028 x y) (@lem1629032)). Qed.
Lemma lem1629034 (x : real) : (term50 x) = term45.
Proof. exact (fun_ext (fun y : real => @lem1629033 x y)). Qed.
Lemma lem1629035 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1629036 (x : real) : (term51 x) = term47.
Proof. exact (MK_COMB (@lem1629035) (@lem1629034 x)). Qed.
Lemma lem1629038 {A : Type'} (t : Prop) : (term48 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1629039 (t : Prop) : (term49 t) = t.
Proof. exact (@lem1629038 real t). Qed.
Lemma lem1629040 : term47 = True.
Proof. exact (@lem1629039 True). Qed.
Lemma lem1629041 (x : real) : (term51 x) = True.
Proof. exact (TRANS (@lem1629036 x) (@lem1629040)). Qed.
Lemma lem1629042 : term52 = term45.
Proof. exact (fun_ext (fun x : real => @lem1629041 x)). Qed.
Lemma lem1629043 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1629044 : term53 = term47.
Proof. exact (MK_COMB (@lem1629043) (@lem1629042)). Qed.
Lemma lem1629046 {A : Type'} (t : Prop) : (term48 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1629047 (t : Prop) : (term49 t) = t.
Proof. exact (@lem1629046 real t). Qed.
Lemma lem1629048 : term47 = True.
Proof. exact (@lem1629047 True). Qed.
Lemma lem1629049 : term53 = True.
Proof. exact (TRANS (@lem1629044) (@lem1629048)). Qed.
Lemma lem1629050 : True = term53.
Proof. exact (SYM (@lem1629049)). Qed.
Lemma lem1629051 : term53.
Proof. exact (EQ_MP (@lem1629050) (@lem0)). Qed.
