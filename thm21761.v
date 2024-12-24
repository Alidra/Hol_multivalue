Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm21761_term_abbrevs.
Require Import thm21760_spec.
Lemma lem21761 (t : Prop) : term0 t.
Proof. exact (proj2 (@lem21760 t)). Qed.
