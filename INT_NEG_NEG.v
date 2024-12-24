Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_NEG_NEG_term_abbrevs.
Require Import REAL_NEG_NEG_spec.
Require Import thm2299915_spec.
Require Import thm2299916_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2306643 (x : int) : term0 x.
Proof. exact (@lem1358662 (real_of_int x)). Qed.
Lemma lem2306644 (x : int) : (term0 x) = ((term1 x) = (real_of_int x)).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2306645 (x : int) : (term1 x) = (real_of_int x).
Proof. exact (EQ_MP (@lem2306644 x) (@lem2306643 x)). Qed.
Lemma lem2306647 (x : int) : (term2 x) = (term3 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2306648 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2306649 (x : int) : (term1 x) = (term4 x).
Proof. exact (MK_COMB (@lem2306648) (@lem2306647 x)). Qed.
Lemma lem2306651 (x : int) : (term2 x) = (term3 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2306652 (x : int) : (term4 x) = (term5 x).
Proof. exact (@lem2306651 (int_neg x)). Qed.
Lemma lem2306653 (x : int) : (term1 x) = (term5 x).
Proof. exact (TRANS (@lem2306649 x) (@lem2306652 x)). Qed.
Lemma lem2306654 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2306655 (x : int) : (term6 x) = (term7 x).
Proof. exact (MK_COMB (@lem2306654) (@lem2306653 x)). Qed.
Lemma lem2306656 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2306657 (x : int) : ((term1 x) = (real_of_int x)) = ((term5 x) = (real_of_int x)).
Proof. exact (MK_COMB (@lem2306655 x) (@lem2306656 x)). Qed.
Lemma lem2306659 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2306660 (x : int) : ((term5 x) = (real_of_int x)) = ((term8 x) = x).
Proof. exact (@lem2306659 (term8 x) x). Qed.
Lemma lem2306661 (x : int) : ((term1 x) = (real_of_int x)) = ((term8 x) = x).
Proof. exact (TRANS (@lem2306657 x) (@lem2306660 x)). Qed.
Lemma lem2306662 (x : int) : (term8 x) = x.
Proof. exact (EQ_MP (@lem2306661 x) (@lem2306645 x)). Qed.
Lemma lem2306663 : term9.
Proof. exact (fun x : int => @lem2306662 x). Qed.
