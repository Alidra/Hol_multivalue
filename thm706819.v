Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm525380_spec.
Lemma lem706819 : (Nat.add 0 0) = 0.
Proof. exact (proj1 (@lem525380)). Qed.
