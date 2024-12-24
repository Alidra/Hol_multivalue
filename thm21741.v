Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm21741_term_abbrevs.
Require Import thm21740_spec.
Lemma lem21741 (t : Prop) : term0 t.
Proof. exact (proj2 (@lem21740 t)). Qed.
