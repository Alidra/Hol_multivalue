Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm5400788_term_abbrevs.
Lemma lem5400788 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term0 A s t) = ((s = t) = (term1 A s t)).
Proof. exact (eq_refl (term0 A s t)). Qed.
