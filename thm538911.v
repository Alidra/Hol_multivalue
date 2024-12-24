Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm538911_term_abbrevs.
Require Import thm538882_spec.
Require Import thm538883_spec.
Lemma lem538910 (m : nat) (n : nat) : (term0 m n) = (term1 m n).
Proof. exact (EQ_MP (@lem538883 m n) (@lem538882 m n)). Qed.
Lemma lem538911 : term2 = term3.
Proof. exact (@lem538910 term4 term5). Qed.
