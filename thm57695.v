Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm57695_term_abbrevs.
Lemma lem57695 {A : Type'} (t : A) : (term0 A t) = ((@LET_END A t) = t).
Proof. exact (eq_refl (term0 A t)). Qed.
