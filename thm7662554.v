Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7662554_term_abbrevs.
Require Import thm10578_spec.
Require Import thm10597_spec.
Lemma lem7662552 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7662553 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : ((term1 _140476 _140477 _140478 P) = (term2 _140476 _140477 _140478 P)) = (term3 _140476 _140477 _140478 P).
Proof. exact (@lem7662552 ((term1 _140476 _140477 _140478 P) = (term2 _140476 _140477 _140478 P))). Qed.
Lemma lem7662554 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term3 _140476 _140477 _140478 P) = ((term1 _140476 _140477 _140478 P) = (term2 _140476 _140477 _140478 P)).
Proof. exact (SYM (@lem7662553 _140476 _140477 _140478 P)). Qed.
