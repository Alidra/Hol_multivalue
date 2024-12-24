Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2338244_term_abbrevs.
Lemma lem2338244 (t2 : Prop) (t1 : Prop) : (term0 t1 t2) = ((term1 t1 t2) = (t2 -> t1)).
Proof. exact (eq_refl (term0 t1 t2)). Qed.
