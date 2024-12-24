Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm534523_term_abbrevs.
Require Import thm534473_spec.
Require Import thm534474_spec.
Lemma lem534522 (m : nat) (n : nat) : (term0 m n) = (term1 m n).
Proof. exact (EQ_MP (@lem534474 m n) (@lem534473 m n)). Qed.
Lemma lem534523 : term2 = term3.
Proof. exact (@lem534522 (BIT1 0) 0). Qed.
