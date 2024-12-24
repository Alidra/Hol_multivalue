Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ONE_term_abbrevs.
Require Import thm0_spec.
Require Import thm80360_spec.
Lemma lem80361 : term0 = term1.
Proof. exact (EQ_MP (@lem80360) (@lem0)). Qed.
