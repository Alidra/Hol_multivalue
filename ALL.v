Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ALL_term_abbrevs.
Require Import thm1100836_spec.
Require Import thm1100843_spec.
Require Import thm1100844_spec.
Lemma lem1100845 {_25307 : Type'} (h : _25307) (P : _25307 -> Prop) (t : list _25307) : (term0 _25307 P h t) = (term1 _25307 h P t).
Proof. exact (EQ_MP (@lem1100844 _25307 h P t) (@lem1100843 _25307 h P t)). Qed.
Lemma lem1100846 {_25307 : Type'} (h : _25307) (P : _25307 -> Prop) (t : list _25307) : term2 _25307 h P t.
Proof. exact (conj (@lem1100836 _25307 P) (@lem1100845 _25307 h P t)). Qed.
