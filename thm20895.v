Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm20895_term_abbrevs.
Require Import thm20792_spec.
Require Import thm20892_spec.
Require Import thm20893_spec.
Lemma lem20895 (a : Prop) (b : Prop) : (term0 a b) = (term1 a b).
Proof. exact (or_elim (@lem20792 a) (fun h0 : a = True => @lem20893 b a h0) (fun h0 : a = False => @lem20892 b a h0)). Qed.
