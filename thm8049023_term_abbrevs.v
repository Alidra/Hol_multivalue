Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (a1 : Type') (x0 : type56 a0 a1) := ~ (x0 = (@EMPTY ((cart a0 a1) -> Prop))).
