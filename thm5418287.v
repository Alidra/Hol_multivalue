Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm5418287_term_abbrevs.
Require Import thm5401059_spec.
Require Import thm5418283_spec.
Lemma lem5418287 (m : nat) (n : nat) (h1 : term0 m n) : term1 m n.
Proof. exact (EQ_MP (@lem5401059 m n) (@lem5418283 m n h1)). Qed.
