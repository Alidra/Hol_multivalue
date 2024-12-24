Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm21182_term_abbrevs.
Require Import thm21117_spec.
Require Import thm21179_spec.
Require Import thm21180_spec.
Lemma lem21182 (p : Prop) : (term0 p) = p.
Proof. exact (or_elim (@lem21117 p) (fun h0 : p = True => @lem21180 p h0) (fun h0 : p = False => @lem21179 p h0)). Qed.
