Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_NOT_LE_term_abbrevs.
Require Import REAL_NOT_LE_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2306748 (x : int) : term0 x.
Proof. exact (@lem1495933 (real_of_int x)). Qed.
Lemma lem2306749 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2306750 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2306749 x) (@lem2306748 x)). Qed.
Lemma lem2306751 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2306750 x (real_of_int y)). Qed.
Lemma lem2306752 (y : int) (x : int) : (term2 x y) = ((term3 x y) = (term4 y x)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2306753 (y : int) (x : int) : (term3 x y) = (term4 y x).
Proof. exact (EQ_MP (@lem2306752 y x) (@lem2306751 x y)). Qed.
Lemma lem2306755 (x : int) (y : int) : (term5 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2306756 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2306757 (x : int) (y : int) : (term3 x y) = (term6 x y).
Proof. exact (MK_COMB (@lem2306756) (@lem2306755 x y)). Qed.
Lemma lem2306758 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2306759 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (MK_COMB (@lem2306758) (@lem2306757 x y)). Qed.
Lemma lem2306761 (x : int) (y : int) : (term4 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2306762 (y : int) (x : int) : (term4 y x) = (int_lt y x).
Proof. exact (@lem2306761 y x). Qed.
Lemma lem2306763 (y : int) (x : int) : ((term3 x y) = (term4 y x)) = ((term6 x y) = (int_lt y x)).
Proof. exact (MK_COMB (@lem2306759 x y) (@lem2306762 y x)). Qed.
Lemma lem2306764 (y : int) (x : int) : (term6 x y) = (int_lt y x).
Proof. exact (EQ_MP (@lem2306763 y x) (@lem2306753 y x)). Qed.
Lemma lem2306765 (x : int) : term9 x.
Proof. exact (fun y : int => @lem2306764 y x). Qed.
Lemma lem2306766 : term10.
Proof. exact (fun x : int => @lem2306765 x). Qed.
