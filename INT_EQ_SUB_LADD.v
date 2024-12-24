Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_EQ_SUB_LADD_term_abbrevs.
Require Import REAL_EQ_SUB_LADD_spec.
Require Import thm2299897_spec.
Require Import thm2299898_spec.
Require Import thm2299912_spec.
Require Import thm2299913_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2301904 (x : int) : term0 x.
Proof. exact (@lem1521519 (real_of_int x)). Qed.
Lemma lem2301905 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2301906 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2301905 x) (@lem2301904 x)). Qed.
Lemma lem2301907 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2301906 x (real_of_int y)). Qed.
Lemma lem2301908 (x : int) (y : int) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2301909 (x : int) (y : int) : term3 x y.
Proof. exact (EQ_MP (@lem2301908 x y) (@lem2301907 x y)). Qed.
Lemma lem2301910 (x : int) (y : int) (z : int) : term4 x y z.
Proof. exact (@lem2301909 x y (real_of_int z)). Qed.
Lemma lem2301911 (x : int) (z : int) (y : int) : (term4 x y z) = (((real_of_int x) = (term5 y z)) = ((term6 x z) = (real_of_int y))).
Proof. exact (eq_refl (term4 x y z)). Qed.
Lemma lem2301912 (x : int) (z : int) (y : int) : ((real_of_int x) = (term5 y z)) = ((term6 x z) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2301911 x z y) (@lem2301910 x y z)). Qed.
Lemma lem2301914 (x : int) (y : int) : (term5 x y) = (term7 x y).
Proof. exact (EQ_MP (@lem2299898 x y) (@lem2299897 x y)). Qed.
Lemma lem2301915 (y : int) (z : int) : (term5 y z) = (term7 y z).
Proof. exact (@lem2301914 y z). Qed.
Lemma lem2301916 (x : int) : (term8 x) = (term8 x).
Proof. exact (eq_refl (term8 x)). Qed.
Lemma lem2301917 (x : int) (y : int) (z : int) : ((real_of_int x) = (term5 y z)) = ((real_of_int x) = (term7 y z)).
Proof. exact (MK_COMB (@lem2301916 x) (@lem2301915 y z)). Qed.
Lemma lem2301919 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2301920 (x : int) (y : int) (z : int) : ((real_of_int x) = (term7 y z)) = (x = (int_sub y z)).
Proof. exact (@lem2301919 x (int_sub y z)). Qed.
Lemma lem2301921 (x : int) (y : int) (z : int) : ((real_of_int x) = (term5 y z)) = (x = (int_sub y z)).
Proof. exact (TRANS (@lem2301917 x y z) (@lem2301920 x y z)). Qed.
Lemma lem2301922 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2301923 (x : int) (y : int) (z : int) : (term9 x y z) = (term10 x y z).
Proof. exact (MK_COMB (@lem2301922) (@lem2301921 x y z)). Qed.
Lemma lem2301925 (x : int) (y : int) : (term6 x y) = (term11 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2301926 (x : int) (z : int) : (term6 x z) = (term11 x z).
Proof. exact (@lem2301925 x z). Qed.
Lemma lem2301927 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2301928 (x : int) (z : int) : (term12 x z) = (term13 x z).
Proof. exact (MK_COMB (@lem2301927) (@lem2301926 x z)). Qed.
Lemma lem2301929 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2301930 (x : int) (z : int) (y : int) : ((term6 x z) = (real_of_int y)) = ((term11 x z) = (real_of_int y)).
Proof. exact (MK_COMB (@lem2301928 x z) (@lem2301929 y)). Qed.
Lemma lem2301932 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2301933 (x : int) (z : int) (y : int) : ((term11 x z) = (real_of_int y)) = ((int_add x z) = y).
Proof. exact (@lem2301932 (int_add x z) y). Qed.
Lemma lem2301934 (x : int) (z : int) (y : int) : ((term6 x z) = (real_of_int y)) = ((int_add x z) = y).
Proof. exact (TRANS (@lem2301930 x z y) (@lem2301933 x z y)). Qed.
Lemma lem2301935 (x : int) (z : int) (y : int) : (((real_of_int x) = (term5 y z)) = ((term6 x z) = (real_of_int y))) = ((x = (int_sub y z)) = ((int_add x z) = y)).
Proof. exact (MK_COMB (@lem2301923 x y z) (@lem2301934 x z y)). Qed.
Lemma lem2301936 (x : int) (z : int) (y : int) : (x = (int_sub y z)) = ((int_add x z) = y).
Proof. exact (EQ_MP (@lem2301935 x z y) (@lem2301912 x z y)). Qed.
Lemma lem2301937 (x : int) (y : int) : term14 x y.
Proof. exact (fun z : int => @lem2301936 x z y). Qed.
Lemma lem2301938 (x : int) : term15 x.
Proof. exact (fun y : int => @lem2301937 x y). Qed.
Lemma lem2301939 : term16.
Proof. exact (fun x : int => @lem2301938 x). Qed.
