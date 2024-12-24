Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7927968_spec.
Lemma lem7927969 {A : Type'} : (@_103783 A) = (@mktybit0 A).
Proof. exact (SYM (@lem7927968 A)). Qed.
