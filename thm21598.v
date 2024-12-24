Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm21598_term_abbrevs.
Require Import thm21504_spec.
Require Import thm21595_spec.
Require Import thm21596_spec.
Lemma lem21598 (b : Prop) (a : Prop) : term0 b a.
Proof. exact (or_elim (@lem21504 a) (fun h0 : a = True => @lem21596 b a h0) (fun h0 : a = False => @lem21595 b a h0)). Qed.
