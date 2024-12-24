Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm5418286_term_abbrevs.
Require Import thm5400808_spec.
Require Import thm5404127_spec.
Lemma lem5418286 (m : nat) (h1 : m = (NUMERAL 0)) : term0 m.
Proof. exact (@lem5404127 m (@lem5400808 m h1)). Qed.
