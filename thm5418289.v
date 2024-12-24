Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm5418289_term_abbrevs.
Require Import thm5400988_spec.
Require Import thm5418285_spec.
Lemma lem5418289 (m : nat) (h1 : term0 m) : term1 m.
Proof. exact (EQ_MP (@lem5400988 m) (@lem5418285 m h1)). Qed.
