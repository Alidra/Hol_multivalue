Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EL_term_abbrevs.
Require Import thm1105743_spec.
Require Import thm1105747_spec.
Require Import thm1105748_spec.
Lemma lem1105749 {_25569 : Type'} (n : nat) (l : list _25569) : (term0 _25569 n l) = (term1 _25569 n l).
Proof. exact (EQ_MP (@lem1105748 _25569 n l) (@lem1105747 _25569 n l)). Qed.
Lemma lem1105750 {_25569 : Type'} (n : nat) (l : list _25569) : term2 _25569 n l.
Proof. exact (conj (@lem1105743 _25569 l) (@lem1105749 _25569 n l)). Qed.
