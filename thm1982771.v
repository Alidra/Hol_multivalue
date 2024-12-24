Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1982771_term_abbrevs.
Require Import thm1982768_spec.
Lemma lem1982771 (x : real) : (real_mul x x) = (term0 x).
Proof. exact (proj1 (@lem1982768 (@el nat) (@el real) (@el real) x (@el nat))). Qed.
