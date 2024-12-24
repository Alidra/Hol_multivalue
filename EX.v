Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EX_term_abbrevs.
Require Import thm1101589_spec.
Require Import thm1101596_spec.
Require Import thm1101597_spec.
Lemma lem1101598 {_25328 : Type'} (h : _25328) (P : _25328 -> Prop) (t : list _25328) : (term0 _25328 P h t) = (term1 _25328 h P t).
Proof. exact (EQ_MP (@lem1101597 _25328 h P t) (@lem1101596 _25328 h P t)). Qed.
Lemma lem1101599 {_25328 : Type'} (h : _25328) (P : _25328 -> Prop) (t : list _25328) : term2 _25328 h P t.
Proof. exact (conj (@lem1101589 _25328 P) (@lem1101598 _25328 h P t)). Qed.
