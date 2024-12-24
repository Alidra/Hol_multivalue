Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LTE_TRANS_term_abbrevs.
Require Import REAL_LTE_TRANS_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2303611 (x : int) : term0 x.
Proof. exact (@lem1370312 (real_of_int x)). Qed.
Lemma lem2303612 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2303613 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2303612 x) (@lem2303611 x)). Qed.
Lemma lem2303614 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2303613 x (real_of_int y)). Qed.
Lemma lem2303615 (y : int) (x : int) : (term2 x y) = (term3 y x).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2303616 (y : int) (x : int) : term3 y x.
Proof. exact (EQ_MP (@lem2303615 y x) (@lem2303614 x y)). Qed.
Lemma lem2303617 (y : int) (x : int) (z : int) : term4 y x z.
Proof. exact (@lem2303616 y x (real_of_int z)). Qed.
Lemma lem2303618 (y : int) (x : int) (z : int) : (term4 y x z) = (term5 y x z).
Proof. exact (eq_refl (term4 y x z)). Qed.
Lemma lem2303619 (y : int) (x : int) (z : int) : term5 y x z.
Proof. exact (EQ_MP (@lem2303618 y x z) (@lem2303617 y x z)). Qed.
Lemma lem2303621 (x : int) (y : int) : (term6 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2303622 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2303623 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (MK_COMB (@lem2303622) (@lem2303621 x y)). Qed.
Lemma lem2303625 (x : int) (y : int) : (term9 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2303626 (y : int) (z : int) : (term9 y z) = (int_le y z).
Proof. exact (@lem2303625 y z). Qed.
Lemma lem2303627 (x : int) (y : int) (z : int) : (term10 x y z) = (term11 x y z).
Proof. exact (MK_COMB (@lem2303623 x y) (@lem2303626 y z)). Qed.
Lemma lem2303628 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2303629 (x : int) (y : int) (z : int) : (term12 x y z) = (term13 x y z).
Proof. exact (MK_COMB (@lem2303628) (@lem2303627 x y z)). Qed.
Lemma lem2303631 (x : int) (y : int) : (term6 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2303632 (x : int) (z : int) : (term6 x z) = (int_lt x z).
Proof. exact (@lem2303631 x z). Qed.
Lemma lem2303633 (y : int) (x : int) (z : int) : (term5 y x z) = (term14 y x z).
Proof. exact (MK_COMB (@lem2303629 x y z) (@lem2303632 x z)). Qed.
Lemma lem2303634 (y : int) (x : int) (z : int) : term14 y x z.
Proof. exact (EQ_MP (@lem2303633 y x z) (@lem2303619 y x z)). Qed.
Lemma lem2303635 (y : int) (x : int) : term15 y x.
Proof. exact (fun z : int => @lem2303634 y x z). Qed.
Lemma lem2303636 (x : int) : term16 x.
Proof. exact (fun y : int => @lem2303635 y x). Qed.
Lemma lem2303637 : term17.
Proof. exact (fun x : int => @lem2303636 x). Qed.
