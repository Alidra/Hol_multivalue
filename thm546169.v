Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm546169_term_abbrevs.
Require Import thm546167_spec.
Lemma lem546168 : term0.
Proof. exact (proj2 (@lem546167)). Qed.
Lemma lem546169 (n : nat) : term1 n.
Proof. exact (@lem546168 n). Qed.
