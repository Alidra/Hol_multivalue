Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7059_term_abbrevs.
Require Import thm7058_spec.
Lemma lem7059 (A : Prop) (C : Prop) (B : Prop) (D : Prop) : term0 A C B D.
Proof. exact (fun h0 : term1 A B C D => @lem7058 A B C D h0). Qed.
