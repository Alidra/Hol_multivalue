Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_MIN_LT_term_abbrevs.
Require Import REAL_MIN_LT_spec.
Require Import thm2299882_spec.
Require Import thm2299883_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Lemma lem2305663 (x : int) : term0 x.
Proof. exact (@lem1571463 (real_of_int x)). Qed.
Lemma lem2305664 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2305665 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2305664 x) (@lem2305663 x)). Qed.
Lemma lem2305666 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2305665 x (real_of_int y)). Qed.
Lemma lem2305667 (x : int) (y : int) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2305668 (x : int) (y : int) : term3 x y.
Proof. exact (EQ_MP (@lem2305667 x y) (@lem2305666 x y)). Qed.
Lemma lem2305669 (x : int) (y : int) (z : int) : term4 x y z.
Proof. exact (@lem2305668 x y (real_of_int z)). Qed.
Lemma lem2305670 (x : int) (y : int) (z : int) : (term4 x y z) = ((term5 x y z) = (term6 x y z)).
Proof. exact (eq_refl (term4 x y z)). Qed.
Lemma lem2305671 (x : int) (y : int) (z : int) : (term5 x y z) = (term6 x y z).
Proof. exact (EQ_MP (@lem2305670 x y z) (@lem2305669 x y z)). Qed.
Lemma lem2305673 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (EQ_MP (@lem2299883 x y) (@lem2299882 x y)). Qed.
Lemma lem2305674 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2305675 (x : int) (y : int) : (term9 x y) = (term10 x y).
Proof. exact (MK_COMB (@lem2305674) (@lem2305673 x y)). Qed.
Lemma lem2305676 (z : int) : (real_of_int z) = (real_of_int z).
Proof. exact (eq_refl (real_of_int z)). Qed.
Lemma lem2305677 (x : int) (y : int) (z : int) : (term5 x y z) = (term11 x y z).
Proof. exact (MK_COMB (@lem2305675 x y) (@lem2305676 z)). Qed.
Lemma lem2305679 (x : int) (y : int) : (term12 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2305680 (x : int) (y : int) (z : int) : (term11 x y z) = (term13 x y z).
Proof. exact (@lem2305679 (int_min x y) z). Qed.
Lemma lem2305681 (x : int) (y : int) (z : int) : (term5 x y z) = (term13 x y z).
Proof. exact (TRANS (@lem2305677 x y z) (@lem2305680 x y z)). Qed.
Lemma lem2305682 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2305683 (x : int) (y : int) (z : int) : (term14 x y z) = (term15 x y z).
Proof. exact (MK_COMB (@lem2305682) (@lem2305681 x y z)). Qed.
Lemma lem2305685 (x : int) (y : int) : (term12 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2305686 (x : int) (z : int) : (term12 x z) = (int_lt x z).
Proof. exact (@lem2305685 x z). Qed.
Lemma lem2305687 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2305688 (x : int) (z : int) : (term16 x z) = (term17 x z).
Proof. exact (MK_COMB (@lem2305687) (@lem2305686 x z)). Qed.
Lemma lem2305690 (x : int) (y : int) : (term12 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2305691 (y : int) (z : int) : (term12 y z) = (int_lt y z).
Proof. exact (@lem2305690 y z). Qed.
Lemma lem2305692 (x : int) (y : int) (z : int) : (term6 x y z) = (term18 x y z).
Proof. exact (MK_COMB (@lem2305688 x z) (@lem2305691 y z)). Qed.
Lemma lem2305693 (x : int) (y : int) (z : int) : ((term5 x y z) = (term6 x y z)) = ((term13 x y z) = (term18 x y z)).
Proof. exact (MK_COMB (@lem2305683 x y z) (@lem2305692 x y z)). Qed.
Lemma lem2305694 (x : int) (y : int) (z : int) : (term13 x y z) = (term18 x y z).
Proof. exact (EQ_MP (@lem2305693 x y z) (@lem2305671 x y z)). Qed.
Lemma lem2305695 (x : int) (y : int) : term19 x y.
Proof. exact (fun z : int => @lem2305694 x y z). Qed.
Lemma lem2305696 (x : int) : term20 x.
Proof. exact (fun y : int => @lem2305695 x y). Qed.
Lemma lem2305697 : term21.
Proof. exact (fun x : int => @lem2305696 x). Qed.
