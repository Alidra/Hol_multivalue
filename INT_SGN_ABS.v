Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_SGN_ABS_term_abbrevs.
Require Import REAL_SGN_ABS_spec.
Require Import thm2299891_spec.
Require Import thm2299892_spec.
Require Import thm2299900_spec.
Require Import thm2299901_spec.
Require Import thm2299906_spec.
Require Import thm2299907_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2309250 (x : int) : term0 x.
Proof. exact (@lem1717545 (real_of_int x)). Qed.
Lemma lem2309251 (x : int) : (term0 x) = ((term1 x) = (real_of_int x)).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2309252 (x : int) : (term1 x) = (real_of_int x).
Proof. exact (EQ_MP (@lem2309251 x) (@lem2309250 x)). Qed.
Lemma lem2309254 (x : int) : (term2 x) = (term3 x).
Proof. exact (EQ_MP (@lem2299901 x) (@lem2299900 x)). Qed.
Lemma lem2309255 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2309256 (x : int) : (term4 x) = (term5 x).
Proof. exact (MK_COMB (@lem2309255) (@lem2309254 x)). Qed.
Lemma lem2309258 (x : int) : (term6 x) = (term7 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2309259 (x : int) : (term1 x) = (term8 x).
Proof. exact (MK_COMB (@lem2309256 x) (@lem2309258 x)). Qed.
Lemma lem2309261 (x : int) (y : int) : (term9 x y) = (term10 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2309262 (x : int) : (term8 x) = (term11 x).
Proof. exact (@lem2309261 (int_sgn x) (int_abs x)). Qed.
Lemma lem2309263 (x : int) : (term1 x) = (term11 x).
Proof. exact (TRANS (@lem2309259 x) (@lem2309262 x)). Qed.
Lemma lem2309264 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2309265 (x : int) : (term12 x) = (term13 x).
Proof. exact (MK_COMB (@lem2309264) (@lem2309263 x)). Qed.
Lemma lem2309266 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2309267 (x : int) : ((term1 x) = (real_of_int x)) = ((term11 x) = (real_of_int x)).
Proof. exact (MK_COMB (@lem2309265 x) (@lem2309266 x)). Qed.
Lemma lem2309269 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2309270 (x : int) : ((term11 x) = (real_of_int x)) = ((term14 x) = x).
Proof. exact (@lem2309269 (term14 x) x). Qed.
Lemma lem2309271 (x : int) : ((term1 x) = (real_of_int x)) = ((term14 x) = x).
Proof. exact (TRANS (@lem2309267 x) (@lem2309270 x)). Qed.
Lemma lem2309272 (x : int) : (term14 x) = x.
Proof. exact (EQ_MP (@lem2309271 x) (@lem2309252 x)). Qed.
Lemma lem2309273 : term15.
Proof. exact (fun x : int => @lem2309272 x). Qed.
