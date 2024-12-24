Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LTE_ANTISYM_term_abbrevs.
Require Import REAL_LTE_ANTISYM_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2303575 (x : int) : term0 x.
Proof. exact (@lem1374144 (real_of_int x)). Qed.
Lemma lem2303576 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2303577 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2303576 x) (@lem2303575 x)). Qed.
Lemma lem2303578 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2303577 x (real_of_int y)). Qed.
Lemma lem2303579 (y : int) (x : int) : (term2 x y) = (term3 y x).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2303580 (y : int) (x : int) : term3 y x.
Proof. exact (EQ_MP (@lem2303579 y x) (@lem2303578 x y)). Qed.
Lemma lem2303582 (x : int) (y : int) : (term4 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2303583 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2303584 (x : int) (y : int) : (term5 x y) = (term6 x y).
Proof. exact (MK_COMB (@lem2303583) (@lem2303582 x y)). Qed.
Lemma lem2303586 (x : int) (y : int) : (term7 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2303587 (y : int) (x : int) : (term7 y x) = (int_le y x).
Proof. exact (@lem2303586 y x). Qed.
Lemma lem2303588 (y : int) (x : int) : (term8 y x) = (term9 y x).
Proof. exact (MK_COMB (@lem2303584 x y) (@lem2303587 y x)). Qed.
Lemma lem2303589 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2303590 (y : int) (x : int) : (term3 y x) = (term10 y x).
Proof. exact (MK_COMB (@lem2303589) (@lem2303588 y x)). Qed.
Lemma lem2303591 (y : int) (x : int) : term10 y x.
Proof. exact (EQ_MP (@lem2303590 y x) (@lem2303580 y x)). Qed.
Lemma lem2303592 (x : int) : term11 x.
Proof. exact (fun y : int => @lem2303591 y x). Qed.
Lemma lem2303593 : term12.
Proof. exact (fun x : int => @lem2303592 x). Qed.
