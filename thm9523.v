Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm9523_term_abbrevs.
Require Import SELECT_REFL_spec.
Lemma lem9523 {A : Type'} (x : A) : term0 A x.
Proof. exact (@lem9442 A x). Qed.
