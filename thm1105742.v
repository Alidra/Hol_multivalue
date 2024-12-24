Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1105742_term_abbrevs.
Lemma lem1105742 {_25569 : Type'} (l : list _25569) : (term0 _25569 l) = ((term1 _25569 l) = (@hd _25569 l)).
Proof. exact (eq_refl (term0 _25569 l)). Qed.
