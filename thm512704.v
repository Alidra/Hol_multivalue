Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm512704_term_abbrevs.
Require Import thm75543_spec.
Lemma lem512704 (n : nat) : term0 n.
Proof. exact (@lem75543 n). Qed.
