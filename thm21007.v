Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm21007_term_abbrevs.
Require Import thm20907_spec.
Require Import thm21004_spec.
Require Import thm21005_spec.
Lemma lem21007 (a : Prop) (b : Prop) : (term0 a b) = (term1 a b).
Proof. exact (or_elim (@lem20907 a) (fun h0 : a = True => @lem21005 b a h0) (fun h0 : a = False => @lem21004 b a h0)). Qed.
