Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm528183_term_abbrevs.
Require Import thm528181_spec.
Lemma lem528182 : term0.
Proof. exact (proj2 (@lem528181)). Qed.
Lemma lem528183 (n : nat) : term1 n.
Proof. exact (@lem528182 n). Qed.
