Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1106563_term_abbrevs.
Lemma lem1106563 {_25594 : Type'} (P : _25594 -> Prop) : (term0 _25594 P) = ((@FILTER _25594 P (@nil _25594)) = (@nil _25594)).
Proof. exact (eq_refl (term0 _25594 P)). Qed.
