Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ITLIST_term_abbrevs.
Require Import thm1102429_spec.
Require Import thm1102439_spec.
Require Import thm1102440_spec.
Lemma lem1102441 {_25350 _25351 : Type'} (h : _25351) (f : type1467 _25350 _25351) (t : list _25351) (b : _25350) : (term0 _25350 _25351 f h t b) = (term1 _25350 _25351 h f t b).
Proof. exact (EQ_MP (@lem1102440 _25350 _25351 h f t b) (@lem1102439 _25350 _25351 h f t b)). Qed.
Lemma lem1102442 {_25350 _25351 : Type'} (h : _25351) (f : type1467 _25350 _25351) (t : list _25351) (b : _25350) : term2 _25350 _25351 h f t b.
Proof. exact (conj (@lem1102429 _25350 _25351 f b) (@lem1102441 _25350 _25351 h f t b)). Qed.
