Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FILTER_term_abbrevs.
Require Import thm1106564_spec.
Require Import thm1106571_spec.
Require Import thm1106572_spec.
Lemma lem1106573 {_25594 : Type'} (h : _25594) (P : _25594 -> Prop) (t : list _25594) : (term0 _25594 P h t) = (term1 _25594 h P t).
Proof. exact (EQ_MP (@lem1106572 _25594 h P t) (@lem1106571 _25594 h P t)). Qed.
Lemma lem1106574 {_25594 : Type'} (h : _25594) (P : _25594 -> Prop) (t : list _25594) : term2 _25594 h P t.
Proof. exact (conj (@lem1106564 _25594 P) (@lem1106573 _25594 h P t)). Qed.
