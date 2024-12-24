Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1101597_term_abbrevs.
Lemma lem1101597 {_25328 : Type'} (h : _25328) (P : _25328 -> Prop) (t : list _25328) : (term0 _25328 h P t) = ((term1 _25328 P h t) = (term2 _25328 h P t)).
Proof. exact (eq_refl (term0 _25328 h P t)). Qed.
