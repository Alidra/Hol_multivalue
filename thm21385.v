Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm21385_term_abbrevs.
Require Import thm21384_spec.
Lemma lem21385 {A : Type'} (x : A) (y : A) (z : A) : term0 A x y z.
Proof. exact (proj2 (@lem21384 A x y z)). Qed.
