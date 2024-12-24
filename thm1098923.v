Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1098923_term_abbrevs.
Require Import thm1098918_spec.
Lemma lem1098920 {_25251 : Type'} (h : _25251) : term0 _25251 h.
Proof. exact (@lem1098918 _25251 h). Qed.
Lemma lem1098921 {_25251 : Type'} (h : _25251) : (term0 _25251 h) = (term1 _25251 h).
Proof. exact (eq_refl (term0 _25251 h)). Qed.
Lemma lem1098922 {_25251 : Type'} (h : _25251) : term1 _25251 h.
Proof. exact (EQ_MP (@lem1098921 _25251 h) (@lem1098920 _25251 h)). Qed.
Lemma lem1098923 {_25251 : Type'} (h : _25251) (t : list _25251) : term2 _25251 h t.
Proof. exact (@lem1098922 _25251 h t). Qed.
