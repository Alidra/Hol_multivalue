Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm302784_term_abbrevs.
Require Import thm302628_spec.
Require Import thm302782_spec.
Lemma lem302784 (m : nat) (n : nat) : (m = n) = ((Nat.add m m) = (term0 n)).
Proof. exact (EQ_MP (@lem302628 m n) (@lem302782 m n)). Qed.
