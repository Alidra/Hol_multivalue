Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1107273_term_abbrevs.
Lemma lem1107273 {_25617 _25623 : Type'} (h : prod _25623 _25617) (a : _25623) (t : type1641 _25617 _25623) : (term0 _25617 _25623 h a t) = ((term1 _25617 _25623 a h t) = (term2 _25617 _25623 h a t)).
Proof. exact (eq_refl (term0 _25617 _25623 h a t)). Qed.
