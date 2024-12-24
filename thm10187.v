Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm10187_term_abbrevs.
Require Import thm10164_spec.
Lemma lem10187 : term0.
Proof. exact (fun t : Prop => @lem10164 t). Qed.
