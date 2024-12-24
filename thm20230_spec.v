Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem20230 : forall {_3603 : Type'} (P : Prop) (c : _3603) (Q : _3603 -> Prop), True = ((forall a : _3603, (a = c) -> P = (Q a)) -> P = (forall a : _3603, (a = c) -> Q a)).
