Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_MAX_MAX_term_abbrevs.
Require Import REAL_MAX_MAX_spec.
Require Import thm2299888_spec.
Require Import thm2299889_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2305352 (x : int) : term0 x.
Proof. exact (@lem1557480 (real_of_int x)). Qed.
Lemma lem2305353 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2305354 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2305353 x) (@lem2305352 x)). Qed.
Lemma lem2305355 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2305354 x (real_of_int y)). Qed.
Lemma lem2305356 (x : int) (y : int) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2305357 (x : int) (y : int) : term3 x y.
Proof. exact (EQ_MP (@lem2305356 x y) (@lem2305355 x y)). Qed.
Lemma lem2305359 (x : int) (y : int) : (term4 x y) = (term5 x y).
Proof. exact (EQ_MP (@lem2299889 x y) (@lem2299888 x y)). Qed.
Lemma lem2305360 (x : int) : (term6 x) = (term6 x).
Proof. exact (eq_refl (term6 x)). Qed.
Lemma lem2305361 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (MK_COMB (@lem2305360 x) (@lem2305359 x y)). Qed.
Lemma lem2305363 (x : int) (y : int) : (term9 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2305364 (x : int) (y : int) : (term8 x y) = (term10 x y).
Proof. exact (@lem2305363 x (int_max x y)). Qed.
Lemma lem2305365 (x : int) (y : int) : (term7 x y) = (term10 x y).
Proof. exact (TRANS (@lem2305361 x y) (@lem2305364 x y)). Qed.
Lemma lem2305366 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2305367 (x : int) (y : int) : (term11 x y) = (term12 x y).
Proof. exact (MK_COMB (@lem2305366) (@lem2305365 x y)). Qed.
Lemma lem2305369 (x : int) (y : int) : (term4 x y) = (term5 x y).
Proof. exact (EQ_MP (@lem2299889 x y) (@lem2299888 x y)). Qed.
Lemma lem2305370 (y : int) : (term6 y) = (term6 y).
Proof. exact (eq_refl (term6 y)). Qed.
Lemma lem2305371 (x : int) (y : int) : (term13 x y) = (term14 x y).
Proof. exact (MK_COMB (@lem2305370 y) (@lem2305369 x y)). Qed.
Lemma lem2305373 (x : int) (y : int) : (term9 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2305374 (x : int) (y : int) : (term14 x y) = (term15 x y).
Proof. exact (@lem2305373 y (int_max x y)). Qed.
Lemma lem2305375 (x : int) (y : int) : (term13 x y) = (term15 x y).
Proof. exact (TRANS (@lem2305371 x y) (@lem2305374 x y)). Qed.
Lemma lem2305376 (x : int) (y : int) : (term3 x y) = (term16 x y).
Proof. exact (MK_COMB (@lem2305367 x y) (@lem2305375 x y)). Qed.
Lemma lem2305377 (x : int) (y : int) : term16 x y.
Proof. exact (EQ_MP (@lem2305376 x y) (@lem2305357 x y)). Qed.
Lemma lem2305378 (x : int) : term17 x.
Proof. exact (fun y : int => @lem2305377 x y). Qed.
Lemma lem2305379 : term18.
Proof. exact (fun x : int => @lem2305378 x). Qed.
