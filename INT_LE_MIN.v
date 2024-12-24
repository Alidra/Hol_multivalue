Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LE_MIN_term_abbrevs.
Require Import REAL_LE_MIN_spec.
Require Import thm2299882_spec.
Require Import thm2299883_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2302665 (x : int) : term0 x.
Proof. exact (@lem1562409 (real_of_int x)). Qed.
Lemma lem2302666 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2302667 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2302666 x) (@lem2302665 x)). Qed.
Lemma lem2302668 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2302667 x (real_of_int y)). Qed.
Lemma lem2302669 (x : int) (y : int) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2302670 (x : int) (y : int) : term3 x y.
Proof. exact (EQ_MP (@lem2302669 x y) (@lem2302668 x y)). Qed.
Lemma lem2302671 (x : int) (y : int) (z : int) : term4 x y z.
Proof. exact (@lem2302670 x y (real_of_int z)). Qed.
Lemma lem2302672 (x : int) (z : int) (y : int) : (term4 x y z) = ((term5 z x y) = (term6 x z y)).
Proof. exact (eq_refl (term4 x y z)). Qed.
Lemma lem2302673 (x : int) (z : int) (y : int) : (term5 z x y) = (term6 x z y).
Proof. exact (EQ_MP (@lem2302672 x z y) (@lem2302671 x y z)). Qed.
Lemma lem2302675 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (EQ_MP (@lem2299883 x y) (@lem2299882 x y)). Qed.
Lemma lem2302676 (z : int) : (term9 z) = (term9 z).
Proof. exact (eq_refl (term9 z)). Qed.
Lemma lem2302677 (z : int) (x : int) (y : int) : (term5 z x y) = (term10 z x y).
Proof. exact (MK_COMB (@lem2302676 z) (@lem2302675 x y)). Qed.
Lemma lem2302679 (x : int) (y : int) : (term11 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2302680 (z : int) (x : int) (y : int) : (term10 z x y) = (term12 z x y).
Proof. exact (@lem2302679 z (int_min x y)). Qed.
Lemma lem2302681 (z : int) (x : int) (y : int) : (term5 z x y) = (term12 z x y).
Proof. exact (TRANS (@lem2302677 z x y) (@lem2302680 z x y)). Qed.
Lemma lem2302682 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2302683 (z : int) (x : int) (y : int) : (term13 z x y) = (term14 z x y).
Proof. exact (MK_COMB (@lem2302682) (@lem2302681 z x y)). Qed.
Lemma lem2302685 (x : int) (y : int) : (term11 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2302686 (z : int) (x : int) : (term11 z x) = (int_le z x).
Proof. exact (@lem2302685 z x). Qed.
Lemma lem2302687 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2302688 (z : int) (x : int) : (term15 z x) = (term16 z x).
Proof. exact (MK_COMB (@lem2302687) (@lem2302686 z x)). Qed.
Lemma lem2302690 (x : int) (y : int) : (term11 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2302691 (z : int) (y : int) : (term11 z y) = (int_le z y).
Proof. exact (@lem2302690 z y). Qed.
Lemma lem2302692 (x : int) (z : int) (y : int) : (term6 x z y) = (term17 x z y).
Proof. exact (MK_COMB (@lem2302688 z x) (@lem2302691 z y)). Qed.
Lemma lem2302693 (x : int) (z : int) (y : int) : ((term5 z x y) = (term6 x z y)) = ((term12 z x y) = (term17 x z y)).
Proof. exact (MK_COMB (@lem2302683 z x y) (@lem2302692 x z y)). Qed.
Lemma lem2302694 (x : int) (z : int) (y : int) : (term12 z x y) = (term17 x z y).
Proof. exact (EQ_MP (@lem2302693 x z y) (@lem2302673 x z y)). Qed.
Lemma lem2302695 (x : int) (y : int) : term18 x y.
Proof. exact (fun z : int => @lem2302694 x z y). Qed.
Lemma lem2302696 (x : int) : term19 x.
Proof. exact (fun y : int => @lem2302695 x y). Qed.
Lemma lem2302697 : term20.
Proof. exact (fun x : int => @lem2302696 x). Qed.
