Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term8 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term7 (a0 : Type') := forall y0 : a0, True.
Definition term6 (a0 : Type') := forall y0 : a0, ~ ((@Some a0 y0) = (@None a0)).
Definition term0 (a0 : Type') (x0 : a0) := (fun y0 : a0 => ~ ((@None a0) = (@Some a0 y0))) x0.
Definition term5 (a0 : Type') := fun y0 : a0 => True.
Definition term4 (a0 : Type') := fun y0 : a0 => ~ ((@Some a0 y0) = (@None a0)).
Definition term3 (a0 : Type') (x0 : a0) := (~ ((@Some a0 x0) = (@None a0))) -> ((@Some a0 x0) = (@None a0)) = False.
Definition term2 (a0 : Type') (x0 : a0) := ~ ((@Some a0 x0) = (@None a0)).
Definition term1 (a0 : Type') (x0 : a0) := ~ ((@None a0) = (@Some a0 x0)).
