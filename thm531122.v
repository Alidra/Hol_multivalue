Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm531122_term_abbrevs.
Require Import thm531089_spec.
Lemma lem531121 : term0.
Proof. exact (proj1 (@lem531089)). Qed.
Lemma lem531122 (n : nat) : term1 n.
Proof. exact (@lem531121 n). Qed.
