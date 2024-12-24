Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm21773_term_abbrevs.
Require Import thm21772_spec.
Lemma lem21773 (t : Prop) : term0 t.
Proof. exact (proj2 (@lem21772 t)). Qed.
