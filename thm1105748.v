Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1105748_term_abbrevs.
Lemma lem1105748 {_25569 : Type'} (n : nat) (l : list _25569) : (term0 _25569 n l) = ((term1 _25569 n l) = (term2 _25569 n l)).
Proof. exact (eq_refl (term0 _25569 n l)). Qed.
