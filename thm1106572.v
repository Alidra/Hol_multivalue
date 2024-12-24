Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1106572_term_abbrevs.
Lemma lem1106572 {_25594 : Type'} (h : _25594) (P : _25594 -> Prop) (t : list _25594) : (term0 _25594 h P t) = ((term1 _25594 P h t) = (term2 _25594 h P t)).
Proof. exact (eq_refl (term0 _25594 h P t)). Qed.
