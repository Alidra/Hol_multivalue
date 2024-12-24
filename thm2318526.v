Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2318526_term_abbrevs.
Require Import int_sub_th_spec.
Lemma lem2318523 (x : int) : term0 x.
Proof. exact (@lem2285582 x). Qed.
Lemma lem2318524 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2318525 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2318524 x) (@lem2318523 x)). Qed.
Lemma lem2318526 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2318525 x y). Qed.
