Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_ABS_SGN_term_abbrevs.
Require Import REAL_ABS_SGN_spec.
Require Import thm2299891_spec.
Require Import thm2299892_spec.
Require Import thm2299900_spec.
Require Import thm2299901_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2300586 (x : int) : term0 x.
Proof. exact (@lem1733749 (real_of_int x)). Qed.
Lemma lem2300587 (x : int) : (term0 x) = ((term1 x) = (term2 x)).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2300588 (x : int) : (term1 x) = (term2 x).
Proof. exact (EQ_MP (@lem2300587 x) (@lem2300586 x)). Qed.
Lemma lem2300590 (x : int) : (term3 x) = (term4 x).
Proof. exact (EQ_MP (@lem2299901 x) (@lem2299900 x)). Qed.
Lemma lem2300591 : real_abs = real_abs.
Proof. exact (eq_refl real_abs). Qed.
Lemma lem2300592 (x : int) : (term1 x) = (term5 x).
Proof. exact (MK_COMB (@lem2300591) (@lem2300590 x)). Qed.
Lemma lem2300594 (x : int) : (term6 x) = (term7 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2300595 (x : int) : (term5 x) = (term8 x).
Proof. exact (@lem2300594 (int_sgn x)). Qed.
Lemma lem2300596 (x : int) : (term1 x) = (term8 x).
Proof. exact (TRANS (@lem2300592 x) (@lem2300595 x)). Qed.
Lemma lem2300597 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2300598 (x : int) : (term9 x) = (term10 x).
Proof. exact (MK_COMB (@lem2300597) (@lem2300596 x)). Qed.
Lemma lem2300600 (x : int) : (term6 x) = (term7 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2300601 : real_sgn = real_sgn.
Proof. exact (eq_refl real_sgn). Qed.
Lemma lem2300602 (x : int) : (term2 x) = (term11 x).
Proof. exact (MK_COMB (@lem2300601) (@lem2300600 x)). Qed.
Lemma lem2300604 (x : int) : (term3 x) = (term4 x).
Proof. exact (EQ_MP (@lem2299901 x) (@lem2299900 x)). Qed.
Lemma lem2300605 (x : int) : (term11 x) = (term12 x).
Proof. exact (@lem2300604 (int_abs x)). Qed.
Lemma lem2300606 (x : int) : (term2 x) = (term12 x).
Proof. exact (TRANS (@lem2300602 x) (@lem2300605 x)). Qed.
Lemma lem2300607 (x : int) : ((term1 x) = (term2 x)) = ((term8 x) = (term12 x)).
Proof. exact (MK_COMB (@lem2300598 x) (@lem2300606 x)). Qed.
Lemma lem2300609 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2300610 (x : int) : ((term8 x) = (term12 x)) = ((term13 x) = (term14 x)).
Proof. exact (@lem2300609 (term13 x) (term14 x)). Qed.
Lemma lem2300611 (x : int) : ((term1 x) = (term2 x)) = ((term13 x) = (term14 x)).
Proof. exact (TRANS (@lem2300607 x) (@lem2300610 x)). Qed.
Lemma lem2300612 (x : int) : (term13 x) = (term14 x).
Proof. exact (EQ_MP (@lem2300611 x) (@lem2300588 x)). Qed.
Lemma lem2300613 : term15.
Proof. exact (fun x : int => @lem2300612 x). Qed.
