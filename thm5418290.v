Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm5418290_term_abbrevs.
Require Import thm5400957_spec.
Require Import thm5418286_spec.
Lemma lem5418290 (m : nat) (h1 : m = (NUMERAL 0)) : term0 m.
Proof. exact (EQ_MP (@lem5400957 m) (@lem5418286 m h1)). Qed.
