Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm20612_term_abbrevs.
Require Import thm20440_spec.
Require Import thm20530_spec.
Lemma lem20612 (x : Prop) (x1 : Prop) (x0 : Prop) (b : Prop) (h1 : b = True) : term0 x x1 b x0.
Proof. exact (EQ_MP (@lem20440 x x1 x0 b h1) (@lem20530 x x1 x0)). Qed.
