Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm4785464_spec.
Lemma lem4785466 {A : Type'} : (@set_of_list A (@nil A)) = (@EMPTY A).
Proof. exact (proj1 (@lem4785464 A)). Qed.
