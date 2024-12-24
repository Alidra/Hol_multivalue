Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_NEG_RMUL_term_abbrevs.
Require Import REAL_NEG_RMUL_spec.
Require Import thm2299906_spec.
Require Import thm2299907_spec.
Require Import thm2299915_spec.
Require Import thm2299916_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2306664 (x : int) : term0 x.
Proof. exact (@lem1491648 (real_of_int x)). Qed.
Lemma lem2306665 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2306666 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2306665 x) (@lem2306664 x)). Qed.
Lemma lem2306667 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2306666 x (real_of_int y)). Qed.
Lemma lem2306668 (x : int) (y : int) : (term2 x y) = ((term3 x y) = (term4 x y)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2306669 (x : int) (y : int) : (term3 x y) = (term4 x y).
Proof. exact (EQ_MP (@lem2306668 x y) (@lem2306667 x y)). Qed.
Lemma lem2306671 (x : int) (y : int) : (term5 x y) = (term6 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2306672 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2306673 (x : int) (y : int) : (term3 x y) = (term7 x y).
Proof. exact (MK_COMB (@lem2306672) (@lem2306671 x y)). Qed.
Lemma lem2306675 (x : int) : (term8 x) = (term9 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2306676 (x : int) (y : int) : (term7 x y) = (term10 x y).
Proof. exact (@lem2306675 (int_mul x y)). Qed.
Lemma lem2306677 (x : int) (y : int) : (term3 x y) = (term10 x y).
Proof. exact (TRANS (@lem2306673 x y) (@lem2306676 x y)). Qed.
Lemma lem2306678 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2306679 (x : int) (y : int) : (term11 x y) = (term12 x y).
Proof. exact (MK_COMB (@lem2306678) (@lem2306677 x y)). Qed.
Lemma lem2306681 (x : int) : (term8 x) = (term9 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2306682 (y : int) : (term8 y) = (term9 y).
Proof. exact (@lem2306681 y). Qed.
Lemma lem2306683 (x : int) : (term13 x) = (term13 x).
Proof. exact (eq_refl (term13 x)). Qed.
Lemma lem2306684 (x : int) (y : int) : (term4 x y) = (term14 x y).
Proof. exact (MK_COMB (@lem2306683 x) (@lem2306682 y)). Qed.
Lemma lem2306686 (x : int) (y : int) : (term5 x y) = (term6 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2306687 (x : int) (y : int) : (term14 x y) = (term15 x y).
Proof. exact (@lem2306686 x (int_neg y)). Qed.
Lemma lem2306688 (x : int) (y : int) : (term4 x y) = (term15 x y).
Proof. exact (TRANS (@lem2306684 x y) (@lem2306687 x y)). Qed.
Lemma lem2306689 (x : int) (y : int) : ((term3 x y) = (term4 x y)) = ((term10 x y) = (term15 x y)).
Proof. exact (MK_COMB (@lem2306679 x y) (@lem2306688 x y)). Qed.
Lemma lem2306691 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2306692 (x : int) (y : int) : ((term10 x y) = (term15 x y)) = ((term16 x y) = (term17 x y)).
Proof. exact (@lem2306691 (term16 x y) (term17 x y)). Qed.
Lemma lem2306693 (x : int) (y : int) : ((term3 x y) = (term4 x y)) = ((term16 x y) = (term17 x y)).
Proof. exact (TRANS (@lem2306689 x y) (@lem2306692 x y)). Qed.
Lemma lem2306694 (x : int) (y : int) : (term16 x y) = (term17 x y).
Proof. exact (EQ_MP (@lem2306693 x y) (@lem2306669 x y)). Qed.
Lemma lem2306695 (x : int) : term18 x.
Proof. exact (fun y : int => @lem2306694 x y). Qed.
Lemma lem2306696 : term19.
Proof. exact (fun x : int => @lem2306695 x). Qed.
