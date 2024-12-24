Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_RULES_spec.
Require Import thm0_spec.
Require Import thm7_spec.
Lemma lem3596278 {A : Type'} : @FINITE A (@EMPTY A).
Proof. exact (proj1 (@lem3197565 A)). Qed.
Lemma lem3596279 {A : Type'} : (@FINITE A (@EMPTY A)) = ((@FINITE A (@EMPTY A)) = True).
Proof. exact (@lem7 (@FINITE A (@EMPTY A))). Qed.
Lemma lem3596282 {A : Type'} : (@FINITE A (@EMPTY A)) = True.
Proof. exact (EQ_MP (@lem3596279 A) (@lem3596278 A)). Qed.
Lemma lem3596283 {_92140 : Type'} : (@FINITE _92140 (@EMPTY _92140)) = True.
Proof. exact (@lem3596282 _92140). Qed.
Lemma lem3596284 {_92140 : Type'} : True = (@FINITE _92140 (@EMPTY _92140)).
Proof. exact (SYM (@lem3596283 _92140)). Qed.
Lemma lem3596285 {_92140 : Type'} : @FINITE _92140 (@EMPTY _92140).
Proof. exact (EQ_MP (@lem3596284 _92140) (@lem0)). Qed.
