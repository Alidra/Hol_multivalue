Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3211657_term_abbrevs.
Lemma lem3211657 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term0 A B y s f) = ((term1 A B y f s) = (term2 A B y f s)).
Proof. exact (eq_refl (term0 A B y s f)). Qed.
