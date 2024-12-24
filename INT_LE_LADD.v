Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LE_LADD_term_abbrevs.
Require Import REAL_LE_LADD_spec.
Require Import thm2299912_spec.
Require Import thm2299913_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2302380 (x : int) : term0 x.
Proof. exact (@lem1500213 (real_of_int x)). Qed.
Lemma lem2302381 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2302382 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2302381 x) (@lem2302380 x)). Qed.
Lemma lem2302383 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2302382 x (real_of_int y)). Qed.
Lemma lem2302384 (x : int) (y : int) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2302385 (x : int) (y : int) : term3 x y.
Proof. exact (EQ_MP (@lem2302384 x y) (@lem2302383 x y)). Qed.
Lemma lem2302386 (x : int) (y : int) (z : int) : term4 x y z.
Proof. exact (@lem2302385 x y (real_of_int z)). Qed.
Lemma lem2302387 (x : int) (y : int) (z : int) : (term4 x y z) = ((term5 y x z) = (term6 y z)).
Proof. exact (eq_refl (term4 x y z)). Qed.
Lemma lem2302388 (x : int) (y : int) (z : int) : (term5 y x z) = (term6 y z).
Proof. exact (EQ_MP (@lem2302387 x y z) (@lem2302386 x y z)). Qed.
Lemma lem2302390 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2302391 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2302392 (x : int) (y : int) : (term9 x y) = (term10 x y).
Proof. exact (MK_COMB (@lem2302391) (@lem2302390 x y)). Qed.
Lemma lem2302394 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2302395 (x : int) (z : int) : (term7 x z) = (term8 x z).
Proof. exact (@lem2302394 x z). Qed.
Lemma lem2302396 (y : int) (x : int) (z : int) : (term5 y x z) = (term11 y x z).
Proof. exact (MK_COMB (@lem2302392 x y) (@lem2302395 x z)). Qed.
Lemma lem2302398 (x : int) (y : int) : (term6 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2302399 (y : int) (x : int) (z : int) : (term11 y x z) = (term12 y x z).
Proof. exact (@lem2302398 (int_add x y) (int_add x z)). Qed.
Lemma lem2302400 (y : int) (x : int) (z : int) : (term5 y x z) = (term12 y x z).
Proof. exact (TRANS (@lem2302396 y x z) (@lem2302399 y x z)). Qed.
Lemma lem2302401 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2302402 (y : int) (x : int) (z : int) : (term13 y x z) = (term14 y x z).
Proof. exact (MK_COMB (@lem2302401) (@lem2302400 y x z)). Qed.
Lemma lem2302404 (x : int) (y : int) : (term6 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2302405 (y : int) (z : int) : (term6 y z) = (int_le y z).
Proof. exact (@lem2302404 y z). Qed.
Lemma lem2302406 (x : int) (y : int) (z : int) : ((term5 y x z) = (term6 y z)) = ((term12 y x z) = (int_le y z)).
Proof. exact (MK_COMB (@lem2302402 y x z) (@lem2302405 y z)). Qed.
Lemma lem2302407 (x : int) (y : int) (z : int) : (term12 y x z) = (int_le y z).
Proof. exact (EQ_MP (@lem2302406 x y z) (@lem2302388 x y z)). Qed.
Lemma lem2302408 (x : int) (y : int) : term15 x y.
Proof. exact (fun z : int => @lem2302407 x y z). Qed.
Lemma lem2302409 (x : int) : term16 x.
Proof. exact (fun y : int => @lem2302408 x y). Qed.
Lemma lem2302410 : term17.
Proof. exact (fun x : int => @lem2302409 x). Qed.
