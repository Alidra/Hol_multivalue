Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LE_MAX_term_abbrevs.
Require Import REAL_LE_MAX_spec.
Require Import thm2299888_spec.
Require Import thm2299889_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2302632 (x : int) : term0 x.
Proof. exact (@lem1560900 (real_of_int x)). Qed.
Lemma lem2302633 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2302634 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2302633 x) (@lem2302632 x)). Qed.
Lemma lem2302635 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2302634 x (real_of_int y)). Qed.
Lemma lem2302636 (x : int) (y : int) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2302637 (x : int) (y : int) : term3 x y.
Proof. exact (EQ_MP (@lem2302636 x y) (@lem2302635 x y)). Qed.
Lemma lem2302638 (x : int) (y : int) (z : int) : term4 x y z.
Proof. exact (@lem2302637 x y (real_of_int z)). Qed.
Lemma lem2302639 (x : int) (z : int) (y : int) : (term4 x y z) = ((term5 z x y) = (term6 x z y)).
Proof. exact (eq_refl (term4 x y z)). Qed.
Lemma lem2302640 (x : int) (z : int) (y : int) : (term5 z x y) = (term6 x z y).
Proof. exact (EQ_MP (@lem2302639 x z y) (@lem2302638 x y z)). Qed.
Lemma lem2302642 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (EQ_MP (@lem2299889 x y) (@lem2299888 x y)). Qed.
Lemma lem2302643 (z : int) : (term9 z) = (term9 z).
Proof. exact (eq_refl (term9 z)). Qed.
Lemma lem2302644 (z : int) (x : int) (y : int) : (term5 z x y) = (term10 z x y).
Proof. exact (MK_COMB (@lem2302643 z) (@lem2302642 x y)). Qed.
Lemma lem2302646 (x : int) (y : int) : (term11 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2302647 (z : int) (x : int) (y : int) : (term10 z x y) = (term12 z x y).
Proof. exact (@lem2302646 z (int_max x y)). Qed.
Lemma lem2302648 (z : int) (x : int) (y : int) : (term5 z x y) = (term12 z x y).
Proof. exact (TRANS (@lem2302644 z x y) (@lem2302647 z x y)). Qed.
Lemma lem2302649 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2302650 (z : int) (x : int) (y : int) : (term13 z x y) = (term14 z x y).
Proof. exact (MK_COMB (@lem2302649) (@lem2302648 z x y)). Qed.
Lemma lem2302652 (x : int) (y : int) : (term11 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2302653 (z : int) (x : int) : (term11 z x) = (int_le z x).
Proof. exact (@lem2302652 z x). Qed.
Lemma lem2302654 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2302655 (z : int) (x : int) : (term15 z x) = (term16 z x).
Proof. exact (MK_COMB (@lem2302654) (@lem2302653 z x)). Qed.
Lemma lem2302657 (x : int) (y : int) : (term11 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2302658 (z : int) (y : int) : (term11 z y) = (int_le z y).
Proof. exact (@lem2302657 z y). Qed.
Lemma lem2302659 (x : int) (z : int) (y : int) : (term6 x z y) = (term17 x z y).
Proof. exact (MK_COMB (@lem2302655 z x) (@lem2302658 z y)). Qed.
Lemma lem2302660 (x : int) (z : int) (y : int) : ((term5 z x y) = (term6 x z y)) = ((term12 z x y) = (term17 x z y)).
Proof. exact (MK_COMB (@lem2302650 z x y) (@lem2302659 x z y)). Qed.
Lemma lem2302661 (x : int) (z : int) (y : int) : (term12 z x y) = (term17 x z y).
Proof. exact (EQ_MP (@lem2302660 x z y) (@lem2302640 x z y)). Qed.
Lemma lem2302662 (x : int) (y : int) : term18 x y.
Proof. exact (fun z : int => @lem2302661 x z y). Qed.
Lemma lem2302663 (x : int) : term19 x.
Proof. exact (fun y : int => @lem2302662 x y). Qed.
Lemma lem2302664 : term20.
Proof. exact (fun x : int => @lem2302663 x). Qed.
