Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3184729_term_abbrevs.
Require Import thm3184696_spec.
Lemma lem3184724 {_83123 : Type'} (P : type919 _83123) : term0 _83123 P.
Proof. exact (fun x : _83123 => @lem3184696 _83123 P x). Qed.
Lemma lem3184729 {_83123 : Type'} : term1 _83123.
Proof. exact (fun P : type919 _83123 => @lem3184724 _83123 P). Qed.
