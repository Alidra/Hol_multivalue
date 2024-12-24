Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm531147_term_abbrevs.
Require Import thm531111_spec.
Require Import thm531112_spec.
Lemma lem531146 (m : nat) (n : nat) : (term0 m n) = (term1 m n).
Proof. exact (EQ_MP (@lem531112 m n) (@lem531111 m n)). Qed.
Lemma lem531147 : term2 = term3.
Proof. exact (@lem531146 (BIT1 0) 0). Qed.
