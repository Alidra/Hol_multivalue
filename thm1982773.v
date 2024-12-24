Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1982773_term_abbrevs.
Require Import thm1982770_spec.
Lemma lem1982773 (x : real) (y : real) (q : nat) : (term0 x y q) = (term1 x y q).
Proof. exact (proj1 (@lem1982770 (@el nat) y (@el real) x q)). Qed.
