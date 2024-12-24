Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2841573_term_abbrevs.
Require Import int_sub_th_spec.
Lemma lem2841570 (x : int) : term0 x.
Proof. exact (@lem2285582 x). Qed.
Lemma lem2841571 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2841572 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2841571 x) (@lem2841570 x)). Qed.
Lemma lem2841573 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2841572 x y). Qed.
