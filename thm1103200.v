Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1103200_term_abbrevs.
Require Import thm1103189_spec.
Lemma lem1103194 {_25376 : Type'} (h : _25376) : term0 _25376 h.
Proof. exact (@lem1103189 _25376 h). Qed.
Lemma lem1103195 {_25376 : Type'} (h : _25376) : (term0 _25376 h) = (term1 _25376 h).
Proof. exact (eq_refl (term0 _25376 h)). Qed.
Lemma lem1103196 {_25376 : Type'} (h : _25376) : term1 _25376 h.
Proof. exact (EQ_MP (@lem1103195 _25376 h) (@lem1103194 _25376 h)). Qed.
Lemma lem1103197 {_25376 : Type'} (h : _25376) (x : _25376) : term2 _25376 h x.
Proof. exact (@lem1103196 _25376 h x). Qed.
Lemma lem1103198 {_25376 : Type'} (h : _25376) (x : _25376) : (term2 _25376 h x) = (term3 _25376 h x).
Proof. exact (eq_refl (term2 _25376 h x)). Qed.
Lemma lem1103199 {_25376 : Type'} (h : _25376) (x : _25376) : term3 _25376 h x.
Proof. exact (EQ_MP (@lem1103198 _25376 h x) (@lem1103197 _25376 h x)). Qed.
Lemma lem1103200 {_25376 : Type'} (h : _25376) (x : _25376) (t : list _25376) : term4 _25376 h x t.
Proof. exact (@lem1103199 _25376 h x t). Qed.
