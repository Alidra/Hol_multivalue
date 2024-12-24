Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1483507_term_abbrevs.
Require Import thm1483505_spec.
Lemma lem1483507 (x : real) (q : nat) : (term0 x q) = (term1 x q).
Proof. exact (proj2 (@lem1483505 (@el real) (@el real) x q)). Qed.
