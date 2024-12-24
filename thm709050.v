Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm709050_term_abbrevs.
Require Import thm709043_spec.
Lemma lem709044 : term0.
Proof. exact (proj2 (@lem709043)). Qed.
Lemma lem709049 : term1.
Proof. exact (proj1 (@lem709044)). Qed.
Lemma lem709050 (n : nat) : term2 n.
Proof. exact (@lem709049 n). Qed.
