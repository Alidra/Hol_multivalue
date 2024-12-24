Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm5418285_term_abbrevs.
Require Import thm5400825_spec.
Require Import thm5405853_spec.
Lemma lem5418285 (m : nat) (h1 : term0 m) : term1 m.
Proof. exact (@lem5405853 m (@lem5400825 m h1)). Qed.
