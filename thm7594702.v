Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7594702_term_abbrevs.
Require Import thm10578_spec.
Require Import thm10597_spec.
Lemma lem7594700 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7594701 {A : Type'} (n : nat) : (term1 A n) = (term2 A n).
Proof. exact (@lem7594700 (term1 A n)). Qed.
Lemma lem7594702 {A : Type'} (n : nat) : (term2 A n) = (term1 A n).
Proof. exact (SYM (@lem7594701 A n)). Qed.
