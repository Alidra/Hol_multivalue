Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1105747_term_abbrevs.
Require Import thm1105739_spec.
Lemma lem1105744 {_25569 : Type'} (n : nat) : term0 _25569 n.
Proof. exact (@lem1105739 _25569 n). Qed.
Lemma lem1105745 {_25569 : Type'} (n : nat) : (term0 _25569 n) = (term1 _25569 n).
Proof. exact (eq_refl (term0 _25569 n)). Qed.
Lemma lem1105746 {_25569 : Type'} (n : nat) : term1 _25569 n.
Proof. exact (EQ_MP (@lem1105745 _25569 n) (@lem1105744 _25569 n)). Qed.
Lemma lem1105747 {_25569 : Type'} (n : nat) (l : list _25569) : term2 _25569 n l.
Proof. exact (@lem1105746 _25569 n l). Qed.
