Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2300923_term_abbrevs.
Require Import REAL_ADD_AC_spec.
Lemma lem2300923 (n : real) (m : real) (p : real) : term0 n m p.
Proof. exact (proj2 (@lem1352530 n m p)). Qed.
