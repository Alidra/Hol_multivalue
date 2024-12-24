Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1101588_term_abbrevs.
Lemma lem1101588 {_25328 : Type'} (P : _25328 -> Prop) : (term0 _25328 P) = ((@EX _25328 P (@nil _25328)) = False).
Proof. exact (eq_refl (term0 _25328 P)). Qed.
