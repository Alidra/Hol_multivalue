Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm513185_term_abbrevs.
Require Import thm513141_spec.
Lemma lem513184 : term0.
Proof. exact (proj2 (@lem513141)). Qed.
Lemma lem513185 (n : nat) : term1 n.
Proof. exact (@lem513184 n). Qed.
