Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_MIN_LE_term_abbrevs.
Require Import REAL_MIN_LE_spec.
Require Import thm2299882_spec.
Require Import thm2299883_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2305628 (x : int) : term0 x.
Proof. exact (@lem1568445 (real_of_int x)). Qed.
Lemma lem2305629 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2305630 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2305629 x) (@lem2305628 x)). Qed.
Lemma lem2305631 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2305630 x (real_of_int y)). Qed.
Lemma lem2305632 (x : int) (y : int) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2305633 (x : int) (y : int) : term3 x y.
Proof. exact (EQ_MP (@lem2305632 x y) (@lem2305631 x y)). Qed.
Lemma lem2305634 (x : int) (y : int) (z : int) : term4 x y z.
Proof. exact (@lem2305633 x y (real_of_int z)). Qed.
Lemma lem2305635 (x : int) (y : int) (z : int) : (term4 x y z) = ((term5 x y z) = (term6 x y z)).
Proof. exact (eq_refl (term4 x y z)). Qed.
Lemma lem2305636 (x : int) (y : int) (z : int) : (term5 x y z) = (term6 x y z).
Proof. exact (EQ_MP (@lem2305635 x y z) (@lem2305634 x y z)). Qed.
Lemma lem2305638 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (EQ_MP (@lem2299883 x y) (@lem2299882 x y)). Qed.
Lemma lem2305639 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2305640 (x : int) (y : int) : (term9 x y) = (term10 x y).
Proof. exact (MK_COMB (@lem2305639) (@lem2305638 x y)). Qed.
Lemma lem2305641 (z : int) : (real_of_int z) = (real_of_int z).
Proof. exact (eq_refl (real_of_int z)). Qed.
Lemma lem2305642 (x : int) (y : int) (z : int) : (term5 x y z) = (term11 x y z).
Proof. exact (MK_COMB (@lem2305640 x y) (@lem2305641 z)). Qed.
Lemma lem2305644 (x : int) (y : int) : (term12 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2305645 (x : int) (y : int) (z : int) : (term11 x y z) = (term13 x y z).
Proof. exact (@lem2305644 (int_min x y) z). Qed.
Lemma lem2305646 (x : int) (y : int) (z : int) : (term5 x y z) = (term13 x y z).
Proof. exact (TRANS (@lem2305642 x y z) (@lem2305645 x y z)). Qed.
Lemma lem2305647 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2305648 (x : int) (y : int) (z : int) : (term14 x y z) = (term15 x y z).
Proof. exact (MK_COMB (@lem2305647) (@lem2305646 x y z)). Qed.
Lemma lem2305650 (x : int) (y : int) : (term12 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2305651 (x : int) (z : int) : (term12 x z) = (int_le x z).
Proof. exact (@lem2305650 x z). Qed.
Lemma lem2305652 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2305653 (x : int) (z : int) : (term16 x z) = (term17 x z).
Proof. exact (MK_COMB (@lem2305652) (@lem2305651 x z)). Qed.
Lemma lem2305655 (x : int) (y : int) : (term12 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2305656 (y : int) (z : int) : (term12 y z) = (int_le y z).
Proof. exact (@lem2305655 y z). Qed.
Lemma lem2305657 (x : int) (y : int) (z : int) : (term6 x y z) = (term18 x y z).
Proof. exact (MK_COMB (@lem2305653 x z) (@lem2305656 y z)). Qed.
Lemma lem2305658 (x : int) (y : int) (z : int) : ((term5 x y z) = (term6 x y z)) = ((term13 x y z) = (term18 x y z)).
Proof. exact (MK_COMB (@lem2305648 x y z) (@lem2305657 x y z)). Qed.
Lemma lem2305659 (x : int) (y : int) (z : int) : (term13 x y z) = (term18 x y z).
Proof. exact (EQ_MP (@lem2305658 x y z) (@lem2305636 x y z)). Qed.
Lemma lem2305660 (x : int) (y : int) : term19 x y.
Proof. exact (fun z : int => @lem2305659 x y z). Qed.
Lemma lem2305661 (x : int) : term20 x.
Proof. exact (fun y : int => @lem2305660 x y). Qed.
Lemma lem2305662 : term21.
Proof. exact (fun x : int => @lem2305661 x). Qed.
