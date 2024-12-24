Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2318568_term_abbrevs.
Require Import int_le_spec.
Lemma lem2318565 (x : int) : term0 x.
Proof. exact (@lem2269094 x). Qed.
Lemma lem2318566 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2318567 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2318566 x) (@lem2318565 x)). Qed.
Lemma lem2318568 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2318567 x y). Qed.
