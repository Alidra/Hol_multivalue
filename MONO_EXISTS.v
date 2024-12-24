Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MONO_EXISTS_term_abbrevs.
Require Import thm7400_spec.
Lemma lem7401 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term0 A P Q.
Proof. exact (fun h0 : term1 A P Q => @lem7400 A P Q h0). Qed.
