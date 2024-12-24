Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm21490_term_abbrevs.
Require Import thm21397_spec.
Require Import thm21487_spec.
Require Import thm21488_spec.
Lemma lem21490 (a : Prop) (b : Prop) : (a -> b) = (term0 a b).
Proof. exact (or_elim (@lem21397 a) (fun h0 : a = True => @lem21488 b a h0) (fun h0 : a = False => @lem21487 b a h0)). Qed.
