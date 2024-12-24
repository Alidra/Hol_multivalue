Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1834_term_abbrevs.
Require Import thm1833_spec.
Lemma lem1834 (t : Prop) : term0 t.
Proof. exact (proj2 (@lem1833 t)). Qed.
