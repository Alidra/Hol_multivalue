Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_MIN_MIN_term_abbrevs.
Require Import REAL_MIN_MIN_spec.
Require Import thm2299882_spec.
Require Import thm2299883_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2305734 (x : int) : term0 x.
Proof. exact (@lem1557933 (real_of_int x)). Qed.
Lemma lem2305735 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2305736 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2305735 x) (@lem2305734 x)). Qed.
Lemma lem2305737 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2305736 x (real_of_int y)). Qed.
Lemma lem2305738 (x : int) (y : int) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2305739 (x : int) (y : int) : term3 x y.
Proof. exact (EQ_MP (@lem2305738 x y) (@lem2305737 x y)). Qed.
Lemma lem2305741 (x : int) (y : int) : (term4 x y) = (term5 x y).
Proof. exact (EQ_MP (@lem2299883 x y) (@lem2299882 x y)). Qed.
Lemma lem2305742 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2305743 (x : int) (y : int) : (term6 x y) = (term7 x y).
Proof. exact (MK_COMB (@lem2305742) (@lem2305741 x y)). Qed.
Lemma lem2305744 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2305745 (y : int) (x : int) : (term8 y x) = (term9 y x).
Proof. exact (MK_COMB (@lem2305743 x y) (@lem2305744 x)). Qed.
Lemma lem2305747 (x : int) (y : int) : (term10 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2305748 (y : int) (x : int) : (term9 y x) = (term11 y x).
Proof. exact (@lem2305747 (int_min x y) x). Qed.
Lemma lem2305749 (y : int) (x : int) : (term8 y x) = (term11 y x).
Proof. exact (TRANS (@lem2305745 y x) (@lem2305748 y x)). Qed.
Lemma lem2305750 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2305751 (y : int) (x : int) : (term12 y x) = (term13 y x).
Proof. exact (MK_COMB (@lem2305750) (@lem2305749 y x)). Qed.
Lemma lem2305753 (x : int) (y : int) : (term4 x y) = (term5 x y).
Proof. exact (EQ_MP (@lem2299883 x y) (@lem2299882 x y)). Qed.
Lemma lem2305754 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2305755 (x : int) (y : int) : (term6 x y) = (term7 x y).
Proof. exact (MK_COMB (@lem2305754) (@lem2305753 x y)). Qed.
Lemma lem2305756 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2305757 (x : int) (y : int) : (term14 x y) = (term15 x y).
Proof. exact (MK_COMB (@lem2305755 x y) (@lem2305756 y)). Qed.
Lemma lem2305759 (x : int) (y : int) : (term10 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2305760 (x : int) (y : int) : (term15 x y) = (term16 x y).
Proof. exact (@lem2305759 (int_min x y) y). Qed.
Lemma lem2305761 (x : int) (y : int) : (term14 x y) = (term16 x y).
Proof. exact (TRANS (@lem2305757 x y) (@lem2305760 x y)). Qed.
Lemma lem2305762 (x : int) (y : int) : (term3 x y) = (term17 x y).
Proof. exact (MK_COMB (@lem2305751 y x) (@lem2305761 x y)). Qed.
Lemma lem2305763 (x : int) (y : int) : term17 x y.
Proof. exact (EQ_MP (@lem2305762 x y) (@lem2305739 x y)). Qed.
Lemma lem2305764 (x : int) : term18 x.
Proof. exact (fun y : int => @lem2305763 x y). Qed.
Lemma lem2305765 : term19.
Proof. exact (fun x : int => @lem2305764 x). Qed.
