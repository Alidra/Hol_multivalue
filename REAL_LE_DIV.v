Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LE_DIV_term_abbrevs.
Require Import REAL_LE_INV_EQ_spec.
Require Import real_div_spec.
Require Import thm0_spec.
Require Import thm1340049_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem1640962 (x : real) : term0 x.
Proof. exact (@lem1344936 x). Qed.
Lemma lem1640963 (x : real) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1640964 (x : real) : term1 x.
Proof. exact (EQ_MP (@lem1640963 x) (@lem1640962 x)). Qed.
Lemma lem1640965 (x : real) (y : real) : term2 x y.
Proof. exact (@lem1640964 x y). Qed.
Lemma lem1640966 (x : real) (y : real) : (term2 x y) = ((real_div x y) = (term3 x y)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem1640968 (x : real) : term4 x.
Proof. exact (@lem1591907 x). Qed.
Lemma lem1640969 (x : real) : (term4 x) = ((term5 x) = (term6 x)).
Proof. exact (eq_refl (term4 x)). Qed.
Lemma lem1640971 (x : real) : term7 x.
Proof. exact (@lem1340049 x). Qed.
Lemma lem1640972 (x : real) : (term7 x) = (term8 x).
Proof. exact (eq_refl (term7 x)). Qed.
Lemma lem1640973 (x : real) : term8 x.
Proof. exact (EQ_MP (@lem1640972 x) (@lem1640971 x)). Qed.
Lemma lem1640974 (x : real) (y : real) : term9 x y.
Proof. exact (@lem1640973 x y). Qed.
Lemma lem1640975 (x : real) (y : real) : (term9 x y) = (term10 x y).
Proof. exact (eq_refl (term9 x y)). Qed.
Lemma lem1640976 (x : real) (y : real) : term10 x y.
Proof. exact (EQ_MP (@lem1640975 x y) (@lem1640974 x y)). Qed.
Lemma lem1640977 (x : real) (y : real) (h1 : term11 x y) : term11 x y.
Proof. exact (h1). Qed.
Lemma lem1640978 (x : real) (y : real) (h1 : term11 x y) : term12 x y.
Proof. exact (@lem1640976 x y (@lem1640977 x y h1)). Qed.
Lemma lem1640979 (x : real) (y : real) : (term12 x y) = ((term12 x y) = True).
Proof. exact (@lem7 (term12 x y)). Qed.
Lemma lem1640980 (x : real) (y : real) (h1 : term11 x y) : (term12 x y) = True.
Proof. exact (EQ_MP (@lem1640979 x y) (@lem1640978 x y h1)). Qed.
Lemma lem1640997 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term13 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1640998 (p : Prop) (q : Prop) (p' : Prop) : term14 p q p'.
Proof. exact (fun q' : Prop => @lem1640997 p q p' q'). Qed.
Lemma lem1640999 (p : Prop) (q : Prop) : term15 p q.
Proof. exact (fun p' : Prop => @lem1640998 p q p'). Qed.
Lemma lem1641000 (x : real) (y : real) : term16 x y.
Proof. exact (@lem1640999 (term11 x y) (term17 x y)). Qed.
Lemma lem1641001 (x : real) (y : real) (p' : Prop) : term18 x y p'.
Proof. exact (@lem1641000 x y p'). Qed.
Lemma lem1641002 (x : real) (y : real) (p' : Prop) : (term18 x y p') = (term19 x y p').
Proof. exact (eq_refl (term18 x y p')). Qed.
Lemma lem1641003 (x : real) (y : real) (p' : Prop) : term19 x y p'.
Proof. exact (EQ_MP (@lem1641002 x y p') (@lem1641001 x y p')). Qed.
Lemma lem1641004 (x : real) (y : real) (p' : Prop) (q' : Prop) : term20 x y p' q'.
Proof. exact (@lem1641003 x y p' q'). Qed.
Lemma lem1641005 (x : real) (y : real) (p' : Prop) (q' : Prop) : (term20 x y p' q') = (term21 x y p' q').
Proof. exact (eq_refl (term20 x y p' q')). Qed.
Lemma lem1641006 (x : real) (y : real) (p' : Prop) (q' : Prop) : term21 x y p' q'.
Proof. exact (EQ_MP (@lem1641005 x y p' q') (@lem1641004 x y p' q')). Qed.
Lemma lem1641009 (x : real) (y : real) : (term11 x y) = (term11 x y).
Proof. exact (eq_refl (term11 x y)). Qed.
Lemma lem1641010 (x : real) (y : real) (q' : Prop) : term22 x y q'.
Proof. exact (@lem1641006 x y (term11 x y) q'). Qed.
Lemma lem1641011 (x : real) (y : real) (q' : Prop) : term23 x y q'.
Proof. exact (@lem1641010 x y q' (@lem1641009 x y)). Qed.
Lemma lem1641012 (x : real) (y : real) (h1 : term11 x y) : term11 x y.
Proof. exact (h1). Qed.
Lemma lem1641013 (x : real) (y : real) (h1 : term11 x y) : term6 y.
Proof. exact (proj2 (@lem1641012 x y h1)). Qed.
Lemma lem1641014 (y : real) : (term6 y) = ((term6 y) = True).
Proof. exact (@lem7 (term6 y)). Qed.
Lemma lem1641016 (x : real) (y : real) (h1 : term11 x y) : term6 x.
Proof. exact (proj1 (@lem1641012 x y h1)). Qed.
Lemma lem1641017 (x : real) : (term6 x) = ((term6 x) = True).
Proof. exact (@lem7 (term6 x)). Qed.
Lemma lem1641020 (x : real) (y : real) : (real_div x y) = (term3 x y).
Proof. exact (EQ_MP (@lem1640966 x y) (@lem1640965 x y)). Qed.
Lemma lem1641021 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1641022 (x : real) (y : real) : (term17 x y) = (term25 x y).
Proof. exact (MK_COMB (@lem1641021) (@lem1641020 x y)). Qed.
Lemma lem1641024 (x : real) (y : real) : term26 x y.
Proof. exact (fun h0 : term11 x y => @lem1640980 x y h0). Qed.
Lemma lem1641025 (x : real) (y : real) : term27 x y.
Proof. exact (@lem1641024 x (real_inv y)). Qed.
Lemma lem1641029 (x : real) (y : real) (h1 : term11 x y) : (term6 x) = True.
Proof. exact (EQ_MP (@lem1641017 x) (@lem1641016 x y h1)). Qed.
Lemma lem1641030 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1641031 (x : real) (y : real) (h1 : term11 x y) : (term28 x) = (and True).
Proof. exact (MK_COMB (@lem1641030) (@lem1641029 x y h1)). Qed.
Lemma lem1641033 (x : real) : (term5 x) = (term6 x).
Proof. exact (EQ_MP (@lem1640969 x) (@lem1640968 x)). Qed.
Lemma lem1641034 (y : real) : (term5 y) = (term6 y).
Proof. exact (@lem1641033 y). Qed.
Lemma lem1641036 (x : real) (y : real) (h1 : term11 x y) : (term6 y) = True.
Proof. exact (EQ_MP (@lem1641014 y) (@lem1641013 x y h1)). Qed.
Lemma lem1641037 (x : real) (y : real) (h1 : term11 x y) : (term5 y) = True.
Proof. exact (TRANS (@lem1641034 y) (@lem1641036 x y h1)). Qed.
Lemma lem1641038 (x : real) (y : real) (h1 : term11 x y) : (term29 x y) = (True /\ True).
Proof. exact (MK_COMB (@lem1641031 x y h1) (@lem1641037 x y h1)). Qed.
Lemma lem1641040 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1641041 : (True /\ True) = True.
Proof. exact (@lem1641040 True). Qed.
Lemma lem1641042 (x : real) (y : real) (h1 : term11 x y) : (term29 x y) = True.
Proof. exact (TRANS (@lem1641038 x y h1) (@lem1641041)). Qed.
Lemma lem1641043 (x : real) (y : real) (h1 : term11 x y) : True = (term29 x y).
Proof. exact (SYM (@lem1641042 x y h1)). Qed.
Lemma lem1641044 (x : real) (y : real) (h1 : term11 x y) : term29 x y.
Proof. exact (EQ_MP (@lem1641043 x y h1) (@lem0)). Qed.
Lemma lem1641045 (x : real) (y : real) (h1 : term11 x y) : (term25 x y) = True.
Proof. exact (@lem1641025 x y (@lem1641044 x y h1)). Qed.
Lemma lem1641046 (x : real) (y : real) (h1 : term11 x y) : (term17 x y) = True.
Proof. exact (TRANS (@lem1641022 x y) (@lem1641045 x y h1)). Qed.
Lemma lem1641047 (x : real) (y : real) : term30 x y.
Proof. exact (fun h0 : term11 x y => @lem1641046 x y h0). Qed.
Lemma lem1641048 (x : real) (y : real) : term31 x y.
Proof. exact (@lem1641011 x y True). Qed.
Lemma lem1641049 (x : real) (y : real) : (term32 x y) = (term33 x y).
Proof. exact (@lem1641048 x y (@lem1641047 x y)). Qed.
Lemma lem1641051 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1641052 (x : real) (y : real) : (term33 x y) = True.
Proof. exact (@lem1641051 (term11 x y)). Qed.
Lemma lem1641053 (x : real) (y : real) : (term32 x y) = True.
Proof. exact (TRANS (@lem1641049 x y) (@lem1641052 x y)). Qed.
Lemma lem1641054 (x : real) : (term34 x) = term35.
Proof. exact (fun_ext (fun y : real => @lem1641053 x y)). Qed.
Lemma lem1641055 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1641056 (x : real) : (term36 x) = term37.
Proof. exact (MK_COMB (@lem1641055) (@lem1641054 x)). Qed.
Lemma lem1641058 {A : Type'} (t : Prop) : (term38 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1641059 (t : Prop) : (term39 t) = t.
Proof. exact (@lem1641058 real t). Qed.
Lemma lem1641060 : term37 = True.
Proof. exact (@lem1641059 True). Qed.
Lemma lem1641061 (x : real) : (term36 x) = True.
Proof. exact (TRANS (@lem1641056 x) (@lem1641060)). Qed.
Lemma lem1641062 : term40 = term35.
Proof. exact (fun_ext (fun x : real => @lem1641061 x)). Qed.
Lemma lem1641063 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1641064 : term41 = term37.
Proof. exact (MK_COMB (@lem1641063) (@lem1641062)). Qed.
Lemma lem1641066 {A : Type'} (t : Prop) : (term38 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1641067 (t : Prop) : (term39 t) = t.
Proof. exact (@lem1641066 real t). Qed.
Lemma lem1641068 : term37 = True.
Proof. exact (@lem1641067 True). Qed.
Lemma lem1641069 : term41 = True.
Proof. exact (TRANS (@lem1641064) (@lem1641068)). Qed.
Lemma lem1641070 : True = term41.
Proof. exact (SYM (@lem1641069)). Qed.
Lemma lem1641071 : term41.
Proof. exact (EQ_MP (@lem1641070) (@lem0)). Qed.
