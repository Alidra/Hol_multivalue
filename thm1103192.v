Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1103192_term_abbrevs.
Lemma lem1103192 {_25376 : Type'} (x : _25376) : (term0 _25376 x) = ((@List.In _25376 x (@nil _25376)) = False).
Proof. exact (eq_refl (term0 _25376 x)). Qed.
