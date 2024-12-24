Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm17944_term_abbrevs.
Lemma lem17944 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term0 t1 t2 t3) = ((term1 t1 t2 t3) = (term2 t1 t2 t3)).
Proof. exact (eq_refl (term0 t1 t2 t3)). Qed.
