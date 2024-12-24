Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LT_SUB_LADD_term_abbrevs.
Require Import REAL_LT_SUB_LADD_spec.
Require Import thm2299897_spec.
Require Import thm2299898_spec.
Require Import thm2299912_spec.
Require Import thm2299913_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Lemma lem2304971 (x : int) : term0 x.
Proof. exact (@lem1515170 (real_of_int x)). Qed.
Lemma lem2304972 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2304973 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2304972 x) (@lem2304971 x)). Qed.
Lemma lem2304974 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2304973 x (real_of_int y)). Qed.
Lemma lem2304975 (x : int) (y : int) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2304976 (x : int) (y : int) : term3 x y.
Proof. exact (EQ_MP (@lem2304975 x y) (@lem2304974 x y)). Qed.
Lemma lem2304977 (x : int) (y : int) (z : int) : term4 x y z.
Proof. exact (@lem2304976 x y (real_of_int z)). Qed.
Lemma lem2304978 (x : int) (z : int) (y : int) : (term4 x y z) = ((term5 x y z) = (term6 x z y)).
Proof. exact (eq_refl (term4 x y z)). Qed.
Lemma lem2304979 (x : int) (z : int) (y : int) : (term5 x y z) = (term6 x z y).
Proof. exact (EQ_MP (@lem2304978 x z y) (@lem2304977 x y z)). Qed.
Lemma lem2304981 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (EQ_MP (@lem2299898 x y) (@lem2299897 x y)). Qed.
Lemma lem2304982 (y : int) (z : int) : (term7 y z) = (term8 y z).
Proof. exact (@lem2304981 y z). Qed.
Lemma lem2304983 (x : int) : (term9 x) = (term9 x).
Proof. exact (eq_refl (term9 x)). Qed.
Lemma lem2304984 (x : int) (y : int) (z : int) : (term5 x y z) = (term10 x y z).
Proof. exact (MK_COMB (@lem2304983 x) (@lem2304982 y z)). Qed.
Lemma lem2304986 (x : int) (y : int) : (term11 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2304987 (x : int) (y : int) (z : int) : (term10 x y z) = (term12 x y z).
Proof. exact (@lem2304986 x (int_sub y z)). Qed.
Lemma lem2304988 (x : int) (y : int) (z : int) : (term5 x y z) = (term12 x y z).
Proof. exact (TRANS (@lem2304984 x y z) (@lem2304987 x y z)). Qed.
Lemma lem2304989 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2304990 (x : int) (y : int) (z : int) : (term13 x y z) = (term14 x y z).
Proof. exact (MK_COMB (@lem2304989) (@lem2304988 x y z)). Qed.
Lemma lem2304992 (x : int) (y : int) : (term15 x y) = (term16 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2304993 (x : int) (z : int) : (term15 x z) = (term16 x z).
Proof. exact (@lem2304992 x z). Qed.
Lemma lem2304994 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2304995 (x : int) (z : int) : (term17 x z) = (term18 x z).
Proof. exact (MK_COMB (@lem2304994) (@lem2304993 x z)). Qed.
Lemma lem2304996 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2304997 (x : int) (z : int) (y : int) : (term6 x z y) = (term19 x z y).
Proof. exact (MK_COMB (@lem2304995 x z) (@lem2304996 y)). Qed.
Lemma lem2304999 (x : int) (y : int) : (term11 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2305000 (x : int) (z : int) (y : int) : (term19 x z y) = (term20 x z y).
Proof. exact (@lem2304999 (int_add x z) y). Qed.
Lemma lem2305001 (x : int) (z : int) (y : int) : (term6 x z y) = (term20 x z y).
Proof. exact (TRANS (@lem2304997 x z y) (@lem2305000 x z y)). Qed.
Lemma lem2305002 (x : int) (z : int) (y : int) : ((term5 x y z) = (term6 x z y)) = ((term12 x y z) = (term20 x z y)).
Proof. exact (MK_COMB (@lem2304990 x y z) (@lem2305001 x z y)). Qed.
Lemma lem2305003 (x : int) (z : int) (y : int) : (term12 x y z) = (term20 x z y).
Proof. exact (EQ_MP (@lem2305002 x z y) (@lem2304979 x z y)). Qed.
Lemma lem2305004 (x : int) (y : int) : term21 x y.
Proof. exact (fun z : int => @lem2305003 x z y). Qed.
Lemma lem2305005 (x : int) : term22 x.
Proof. exact (fun y : int => @lem2305004 x y). Qed.
Lemma lem2305006 : term23.
Proof. exact (fun x : int => @lem2305005 x). Qed.
