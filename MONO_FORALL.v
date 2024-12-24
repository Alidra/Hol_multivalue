Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MONO_FORALL_term_abbrevs.
Require Import thm7362_spec.
Lemma lem7363 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term0 A P Q.
Proof. exact (fun h0 : term1 A P Q => @lem7362 A P Q h0). Qed.
