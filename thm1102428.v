Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1102428_term_abbrevs.
Lemma lem1102428 {_25350 _25351 : Type'} (f : type1467 _25350 _25351) (b : _25350) : (term0 _25350 _25351 f b) = ((@ITLIST _25350 _25351 f (@nil _25351) b) = b).
Proof. exact (eq_refl (term0 _25350 _25351 f b)). Qed.
