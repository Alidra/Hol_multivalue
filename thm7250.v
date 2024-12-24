Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7250_term_abbrevs.
Require Import thm7249_spec.
Lemma lem7250 (A : Prop) (C : Prop) (B : Prop) (D : Prop) : term0 A C B D.
Proof. exact (fun h0 : term1 B A C D => @lem7249 B A C D h0). Qed.
