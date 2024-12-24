Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_NEG_MUL2_term_abbrevs.
Require Import REAL_NEG_MUL2_spec.
Require Import thm2299906_spec.
Require Import thm2299907_spec.
Require Import thm2299915_spec.
Require Import thm2299916_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2306613 (x : int) : term0 x.
Proof. exact (@lem1491878 (real_of_int x)). Qed.
Lemma lem2306614 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2306615 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2306614 x) (@lem2306613 x)). Qed.
Lemma lem2306616 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2306615 x (real_of_int y)). Qed.
Lemma lem2306617 (x : int) (y : int) : (term2 x y) = ((term3 x y) = (term4 x y)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2306618 (x : int) (y : int) : (term3 x y) = (term4 x y).
Proof. exact (EQ_MP (@lem2306617 x y) (@lem2306616 x y)). Qed.
Lemma lem2306620 (x : int) : (term5 x) = (term6 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2306621 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2306622 (x : int) : (term7 x) = (term8 x).
Proof. exact (MK_COMB (@lem2306621) (@lem2306620 x)). Qed.
Lemma lem2306624 (x : int) : (term5 x) = (term6 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2306625 (y : int) : (term5 y) = (term6 y).
Proof. exact (@lem2306624 y). Qed.
Lemma lem2306626 (x : int) (y : int) : (term3 x y) = (term9 x y).
Proof. exact (MK_COMB (@lem2306622 x) (@lem2306625 y)). Qed.
Lemma lem2306628 (x : int) (y : int) : (term4 x y) = (term10 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2306629 (x : int) (y : int) : (term9 x y) = (term11 x y).
Proof. exact (@lem2306628 (int_neg x) (int_neg y)). Qed.
Lemma lem2306630 (x : int) (y : int) : (term3 x y) = (term11 x y).
Proof. exact (TRANS (@lem2306626 x y) (@lem2306629 x y)). Qed.
Lemma lem2306631 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2306632 (x : int) (y : int) : (term12 x y) = (term13 x y).
Proof. exact (MK_COMB (@lem2306631) (@lem2306630 x y)). Qed.
Lemma lem2306634 (x : int) (y : int) : (term4 x y) = (term10 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2306635 (x : int) (y : int) : ((term3 x y) = (term4 x y)) = ((term11 x y) = (term10 x y)).
Proof. exact (MK_COMB (@lem2306632 x y) (@lem2306634 x y)). Qed.
Lemma lem2306637 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2306638 (x : int) (y : int) : ((term11 x y) = (term10 x y)) = ((term14 x y) = (int_mul x y)).
Proof. exact (@lem2306637 (term14 x y) (int_mul x y)). Qed.
Lemma lem2306639 (x : int) (y : int) : ((term3 x y) = (term4 x y)) = ((term14 x y) = (int_mul x y)).
Proof. exact (TRANS (@lem2306635 x y) (@lem2306638 x y)). Qed.
Lemma lem2306640 (x : int) (y : int) : (term14 x y) = (int_mul x y).
Proof. exact (EQ_MP (@lem2306639 x y) (@lem2306618 x y)). Qed.
Lemma lem2306641 (x : int) : term15 x.
Proof. exact (fun y : int => @lem2306640 x y). Qed.
Lemma lem2306642 : term16.
Proof. exact (fun x : int => @lem2306641 x). Qed.
