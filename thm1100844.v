Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1100844_term_abbrevs.
Lemma lem1100844 {_25307 : Type'} (h : _25307) (P : _25307 -> Prop) (t : list _25307) : (term0 _25307 h P t) = ((term1 _25307 P h t) = (term2 _25307 h P t)).
Proof. exact (eq_refl (term0 _25307 h P t)). Qed.
