Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm21751_term_abbrevs.
Require Import thm21750_spec.
Lemma lem21751 (t : Prop) : term0 t.
Proof. exact (proj2 (@lem21750 t)). Qed.
