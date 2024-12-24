Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3211711_term_abbrevs.
Lemma lem3211711 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term0 A s t x) = ((term1 A x s t) = (term2 A s x t)).
Proof. exact (eq_refl (term0 A s t x)). Qed.
