Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm5418288_term_abbrevs.
Require Import thm5401030_spec.
Require Import thm5418284_spec.
Lemma lem5418288 (m : nat) (n : nat) (h1 : term0 m n) : term1 m n.
Proof. exact (EQ_MP (@lem5401030 m n) (@lem5418284 m n h1)). Qed.
