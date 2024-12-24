Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LE_LT_term_abbrevs.
Require Import REAL_LE_LT_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2302611 (x : int) : term0 x.
Proof. exact (@lem1376325 (real_of_int x)). Qed.
Lemma lem2302612 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2302613 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2302612 x) (@lem2302611 x)). Qed.
Lemma lem2302614 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2302613 x (real_of_int y)). Qed.
Lemma lem2302615 (x : int) (y : int) : (term2 x y) = ((term3 x y) = (term4 x y)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2302616 (x : int) (y : int) : (term3 x y) = (term4 x y).
Proof. exact (EQ_MP (@lem2302615 x y) (@lem2302614 x y)). Qed.
Lemma lem2302618 (x : int) (y : int) : (term3 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2302619 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2302620 (x : int) (y : int) : (term5 x y) = (term6 x y).
Proof. exact (MK_COMB (@lem2302619) (@lem2302618 x y)). Qed.
Lemma lem2302622 (x : int) (y : int) : (term7 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2302623 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2302624 (x : int) (y : int) : (term8 x y) = (term9 x y).
Proof. exact (MK_COMB (@lem2302623) (@lem2302622 x y)). Qed.
Lemma lem2302626 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2302627 (x : int) (y : int) : (term4 x y) = (term10 x y).
Proof. exact (MK_COMB (@lem2302624 x y) (@lem2302626 x y)). Qed.
Lemma lem2302628 (x : int) (y : int) : ((term3 x y) = (term4 x y)) = ((int_le x y) = (term10 x y)).
Proof. exact (MK_COMB (@lem2302620 x y) (@lem2302627 x y)). Qed.
Lemma lem2302629 (x : int) (y : int) : (int_le x y) = (term10 x y).
Proof. exact (EQ_MP (@lem2302628 x y) (@lem2302616 x y)). Qed.
Lemma lem2302630 (x : int) : term11 x.
Proof. exact (fun y : int => @lem2302629 x y). Qed.
Lemma lem2302631 : term12.
Proof. exact (fun x : int => @lem2302630 x). Qed.
