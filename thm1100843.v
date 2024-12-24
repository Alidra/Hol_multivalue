Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1100843_term_abbrevs.
Require Import thm1100832_spec.
Lemma lem1100837 {_25307 : Type'} (h : _25307) : term0 _25307 h.
Proof. exact (@lem1100832 _25307 h). Qed.
Lemma lem1100838 {_25307 : Type'} (h : _25307) : (term0 _25307 h) = (term1 _25307 h).
Proof. exact (eq_refl (term0 _25307 h)). Qed.
Lemma lem1100839 {_25307 : Type'} (h : _25307) : term1 _25307 h.
Proof. exact (EQ_MP (@lem1100838 _25307 h) (@lem1100837 _25307 h)). Qed.
Lemma lem1100840 {_25307 : Type'} (h : _25307) (P : _25307 -> Prop) : term2 _25307 h P.
Proof. exact (@lem1100839 _25307 h P). Qed.
Lemma lem1100841 {_25307 : Type'} (h : _25307) (P : _25307 -> Prop) : (term2 _25307 h P) = (term3 _25307 h P).
Proof. exact (eq_refl (term2 _25307 h P)). Qed.
Lemma lem1100842 {_25307 : Type'} (h : _25307) (P : _25307 -> Prop) : term3 _25307 h P.
Proof. exact (EQ_MP (@lem1100841 _25307 h P) (@lem1100840 _25307 h P)). Qed.
Lemma lem1100843 {_25307 : Type'} (h : _25307) (P : _25307 -> Prop) (t : list _25307) : term4 _25307 h P t.
Proof. exact (@lem1100842 _25307 h P t). Qed.
