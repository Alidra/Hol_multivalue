Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MEM_term_abbrevs.
Require Import thm1103193_spec.
Require Import thm1103200_spec.
Require Import thm1103201_spec.
Lemma lem1103202 {_25376 : Type'} (h : _25376) (x : _25376) (t : list _25376) : (term0 _25376 x h t) = (term1 _25376 h x t).
Proof. exact (EQ_MP (@lem1103201 _25376 h x t) (@lem1103200 _25376 h x t)). Qed.
Lemma lem1103203 {_25376 : Type'} (h : _25376) (x : _25376) (t : list _25376) : term2 _25376 h x t.
Proof. exact (conj (@lem1103193 _25376 x) (@lem1103202 _25376 h x t)). Qed.
