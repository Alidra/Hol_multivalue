Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_SGN_ABS_ALT_term_abbrevs.
Require Import REAL_SGN_ABS_ALT_spec.
Require Import thm2299891_spec.
Require Import thm2299892_spec.
Require Import thm2299900_spec.
Require Import thm2299901_spec.
Require Import thm2299906_spec.
Require Import thm2299907_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2309274 (x : int) : term0 x.
Proof. exact (@lem1719699 (real_of_int x)). Qed.
Lemma lem2309275 (x : int) : (term0 x) = ((term1 x) = (term2 x)).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2309276 (x : int) : (term1 x) = (term2 x).
Proof. exact (EQ_MP (@lem2309275 x) (@lem2309274 x)). Qed.
Lemma lem2309278 (x : int) : (term3 x) = (term4 x).
Proof. exact (EQ_MP (@lem2299901 x) (@lem2299900 x)). Qed.
Lemma lem2309279 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2309280 (x : int) : (term5 x) = (term6 x).
Proof. exact (MK_COMB (@lem2309279) (@lem2309278 x)). Qed.
Lemma lem2309281 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2309282 (x : int) : (term1 x) = (term7 x).
Proof. exact (MK_COMB (@lem2309280 x) (@lem2309281 x)). Qed.
Lemma lem2309284 (x : int) (y : int) : (term8 x y) = (term9 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2309285 (x : int) : (term7 x) = (term10 x).
Proof. exact (@lem2309284 (int_sgn x) x). Qed.
Lemma lem2309286 (x : int) : (term1 x) = (term10 x).
Proof. exact (TRANS (@lem2309282 x) (@lem2309285 x)). Qed.
Lemma lem2309287 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2309288 (x : int) : (term11 x) = (term12 x).
Proof. exact (MK_COMB (@lem2309287) (@lem2309286 x)). Qed.
Lemma lem2309290 (x : int) : (term2 x) = (term13 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2309291 (x : int) : ((term1 x) = (term2 x)) = ((term10 x) = (term13 x)).
Proof. exact (MK_COMB (@lem2309288 x) (@lem2309290 x)). Qed.
Lemma lem2309293 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2309294 (x : int) : ((term10 x) = (term13 x)) = ((term14 x) = (int_abs x)).
Proof. exact (@lem2309293 (term14 x) (int_abs x)). Qed.
Lemma lem2309295 (x : int) : ((term1 x) = (term2 x)) = ((term14 x) = (int_abs x)).
Proof. exact (TRANS (@lem2309291 x) (@lem2309294 x)). Qed.
Lemma lem2309296 (x : int) : (term14 x) = (int_abs x).
Proof. exact (EQ_MP (@lem2309295 x) (@lem2309276 x)). Qed.
Lemma lem2309297 : term15.
Proof. exact (fun x : int => @lem2309296 x). Qed.
