Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm20764_term_abbrevs.
Require Import thm20685_spec.
Require Import thm20761_spec.
Require Import thm20762_spec.
Lemma lem20764 (b : Prop) (a : Prop) : (a \/ b) = (term0 b a).
Proof. exact (or_elim (@lem20685 a) (fun h0 : a = True => @lem20762 b a h0) (fun h0 : a = False => @lem20761 b a h0)). Qed.
