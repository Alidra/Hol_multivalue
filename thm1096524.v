Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1096524_term_abbrevs.
Lemma lem1096524 {A : Type'} (l : list A) (x : A) : (term0 A l x) = ((term1 A x l) = (term2 A l x)).
Proof. exact (eq_refl (term0 A l x)). Qed.
