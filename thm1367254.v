Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1367254_term_abbrevs.
Require Import thm1367253_spec.
Lemma lem1367254 (x : nat) : term0 x.
Proof. exact (proj2 (@lem1367253 x)). Qed.
