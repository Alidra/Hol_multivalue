Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import BUTLAST_term_abbrevs.
Require Import thm1098919_spec.
Require Import thm1098923_spec.
Require Import thm1098924_spec.
Lemma lem1098925 {_25251 : Type'} (h : _25251) (t : list _25251) : (term0 _25251 h t) = (term1 _25251 h t).
Proof. exact (EQ_MP (@lem1098924 _25251 h t) (@lem1098923 _25251 h t)). Qed.
Lemma lem1098926 {_25251 : Type'} (h : _25251) (t : list _25251) : term2 _25251 h t.
Proof. exact (conj (@lem1098919 _25251) (@lem1098925 _25251 h t)). Qed.
