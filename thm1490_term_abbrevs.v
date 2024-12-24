Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term3 := False -> ~ True.
Definition term4 := ((~ True) -> False) /\ (False -> ~ True).
Definition term1 := @eq Prop (~ True).
Definition term2 := (~ True) -> False.
Definition term0 := (fun y0 : Prop => y0 -> False) True.
