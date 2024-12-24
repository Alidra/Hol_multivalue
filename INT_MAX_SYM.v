Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_MAX_SYM_term_abbrevs.
Require Import REAL_MAX_SYM_spec.
Require Import thm2299888_spec.
Require Import thm2299889_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2305416 (x : int) : term0 x.
Proof. exact (@lem1558662 (real_of_int x)). Qed.
Lemma lem2305417 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2305418 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2305417 x) (@lem2305416 x)). Qed.
Lemma lem2305419 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2305418 x (real_of_int y)). Qed.
Lemma lem2305420 (y : int) (x : int) : (term2 x y) = ((term3 x y) = (term3 y x)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2305421 (y : int) (x : int) : (term3 x y) = (term3 y x).
Proof. exact (EQ_MP (@lem2305420 y x) (@lem2305419 x y)). Qed.
Lemma lem2305423 (x : int) (y : int) : (term3 x y) = (term4 x y).
Proof. exact (EQ_MP (@lem2299889 x y) (@lem2299888 x y)). Qed.
Lemma lem2305424 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2305425 (x : int) (y : int) : (term5 x y) = (term6 x y).
Proof. exact (MK_COMB (@lem2305424) (@lem2305423 x y)). Qed.
Lemma lem2305427 (x : int) (y : int) : (term3 x y) = (term4 x y).
Proof. exact (EQ_MP (@lem2299889 x y) (@lem2299888 x y)). Qed.
Lemma lem2305428 (y : int) (x : int) : (term3 y x) = (term4 y x).
Proof. exact (@lem2305427 y x). Qed.
Lemma lem2305429 (y : int) (x : int) : ((term3 x y) = (term3 y x)) = ((term4 x y) = (term4 y x)).
Proof. exact (MK_COMB (@lem2305425 x y) (@lem2305428 y x)). Qed.
Lemma lem2305431 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2305432 (y : int) (x : int) : ((term4 x y) = (term4 y x)) = ((int_max x y) = (int_max y x)).
Proof. exact (@lem2305431 (int_max x y) (int_max y x)). Qed.
Lemma lem2305433 (y : int) (x : int) : ((term3 x y) = (term3 y x)) = ((int_max x y) = (int_max y x)).
Proof. exact (TRANS (@lem2305429 y x) (@lem2305432 y x)). Qed.
Lemma lem2305434 (y : int) (x : int) : (int_max x y) = (int_max y x).
Proof. exact (EQ_MP (@lem2305433 y x) (@lem2305421 y x)). Qed.
Lemma lem2305435 (x : int) : term7 x.
Proof. exact (fun y : int => @lem2305434 y x). Qed.
Lemma lem2305436 : term8.
Proof. exact (fun x : int => @lem2305435 x). Qed.
