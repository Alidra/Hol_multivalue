Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_EQ_SUB_RADD_term_abbrevs.
Require Import REAL_EQ_SUB_RADD_spec.
Require Import thm2299897_spec.
Require Import thm2299898_spec.
Require Import thm2299912_spec.
Require Import thm2299913_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2301940 (x : int) : term0 x.
Proof. exact (@lem1522949 (real_of_int x)). Qed.
Lemma lem2301941 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2301942 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2301941 x) (@lem2301940 x)). Qed.
Lemma lem2301943 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2301942 x (real_of_int y)). Qed.
Lemma lem2301944 (x : int) (y : int) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2301945 (x : int) (y : int) : term3 x y.
Proof. exact (EQ_MP (@lem2301944 x y) (@lem2301943 x y)). Qed.
Lemma lem2301946 (x : int) (y : int) (z : int) : term4 x y z.
Proof. exact (@lem2301945 x y (real_of_int z)). Qed.
Lemma lem2301947 (x : int) (z : int) (y : int) : (term4 x y z) = (((term5 x y) = (real_of_int z)) = ((real_of_int x) = (term6 z y))).
Proof. exact (eq_refl (term4 x y z)). Qed.
Lemma lem2301948 (x : int) (z : int) (y : int) : ((term5 x y) = (real_of_int z)) = ((real_of_int x) = (term6 z y)).
Proof. exact (EQ_MP (@lem2301947 x z y) (@lem2301946 x y z)). Qed.
Lemma lem2301950 (x : int) (y : int) : (term5 x y) = (term7 x y).
Proof. exact (EQ_MP (@lem2299898 x y) (@lem2299897 x y)). Qed.
Lemma lem2301951 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2301952 (x : int) (y : int) : (term8 x y) = (term9 x y).
Proof. exact (MK_COMB (@lem2301951) (@lem2301950 x y)). Qed.
Lemma lem2301953 (z : int) : (real_of_int z) = (real_of_int z).
Proof. exact (eq_refl (real_of_int z)). Qed.
Lemma lem2301954 (x : int) (y : int) (z : int) : ((term5 x y) = (real_of_int z)) = ((term7 x y) = (real_of_int z)).
Proof. exact (MK_COMB (@lem2301952 x y) (@lem2301953 z)). Qed.
Lemma lem2301956 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2301957 (x : int) (y : int) (z : int) : ((term7 x y) = (real_of_int z)) = ((int_sub x y) = z).
Proof. exact (@lem2301956 (int_sub x y) z). Qed.
Lemma lem2301958 (x : int) (y : int) (z : int) : ((term5 x y) = (real_of_int z)) = ((int_sub x y) = z).
Proof. exact (TRANS (@lem2301954 x y z) (@lem2301957 x y z)). Qed.
Lemma lem2301959 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2301960 (x : int) (y : int) (z : int) : (term10 x y z) = (term11 x y z).
Proof. exact (MK_COMB (@lem2301959) (@lem2301958 x y z)). Qed.
Lemma lem2301962 (x : int) (y : int) : (term6 x y) = (term12 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2301963 (z : int) (y : int) : (term6 z y) = (term12 z y).
Proof. exact (@lem2301962 z y). Qed.
Lemma lem2301964 (x : int) : (term13 x) = (term13 x).
Proof. exact (eq_refl (term13 x)). Qed.
Lemma lem2301965 (x : int) (z : int) (y : int) : ((real_of_int x) = (term6 z y)) = ((real_of_int x) = (term12 z y)).
Proof. exact (MK_COMB (@lem2301964 x) (@lem2301963 z y)). Qed.
Lemma lem2301967 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2301968 (x : int) (z : int) (y : int) : ((real_of_int x) = (term12 z y)) = (x = (int_add z y)).
Proof. exact (@lem2301967 x (int_add z y)). Qed.
Lemma lem2301969 (x : int) (z : int) (y : int) : ((real_of_int x) = (term6 z y)) = (x = (int_add z y)).
Proof. exact (TRANS (@lem2301965 x z y) (@lem2301968 x z y)). Qed.
Lemma lem2301970 (x : int) (z : int) (y : int) : (((term5 x y) = (real_of_int z)) = ((real_of_int x) = (term6 z y))) = (((int_sub x y) = z) = (x = (int_add z y))).
Proof. exact (MK_COMB (@lem2301960 x y z) (@lem2301969 x z y)). Qed.
Lemma lem2301971 (x : int) (z : int) (y : int) : ((int_sub x y) = z) = (x = (int_add z y)).
Proof. exact (EQ_MP (@lem2301970 x z y) (@lem2301948 x z y)). Qed.
Lemma lem2301972 (x : int) (y : int) : term14 x y.
Proof. exact (fun z : int => @lem2301971 x z y). Qed.
Lemma lem2301973 (x : int) : term15 x.
Proof. exact (fun y : int => @lem2301972 x y). Qed.
Lemma lem2301974 : term16.
Proof. exact (fun x : int => @lem2301973 x). Qed.
