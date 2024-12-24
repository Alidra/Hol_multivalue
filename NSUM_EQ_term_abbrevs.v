Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term23 (a0 : Type') (x0 : type1606) := (@monoidal nat x0) -> forall y0 : a0 -> nat, forall y1 : a0 -> nat, forall y2 : a0 -> Prop, (forall y3 : a0, (@IN a0 y3 y2) -> (y0 y3) = (y1 y3)) -> (@iterate nat a0 x0 y2 y0) = (@iterate nat a0 x0 y2 y1).
Definition term2 (a0 : Type') (a1 : Type') (x0 : type1400 a1) := (@monoidal a1 x0) -> forall y0 : a0 -> a1, forall y1 : a0 -> a1, forall y2 : a0 -> Prop, (forall y3 : a0, (@IN a0 y3 y2) -> (y0 y3) = (y1 y3)) -> (@iterate a1 a0 x0 y2 y0) = (@iterate a1 a0 x0 y2 y1).
Definition term22 (a0 : Type') := forall y0 : a0 -> nat, forall y1 : a0 -> nat, forall y2 : a0 -> Prop, (forall y3 : a0, (@IN a0 y3 y2) -> (y0 y3) = (y1 y3)) -> (@iterate nat a0 Nat.add y2 y0) = (@iterate nat a0 Nat.add y2 y1).
Definition term21 (a0 : Type') := forall y0 : a0 -> nat, forall y1 : a0 -> nat, forall y2 : a0 -> Prop, (forall y3 : a0, (@IN a0 y3 y2) -> (y0 y3) = (y1 y3)) -> (@nsum a0 y2 y0) = (@nsum a0 y2 y1).
Definition term3 (a0 : Type') (a1 : Type') (x0 : type1400 a1) := forall y0 : a0 -> a1, forall y1 : a0 -> a1, forall y2 : a0 -> Prop, (forall y3 : a0, (@IN a0 y3 y2) -> (y0 y3) = (y1 y3)) -> (@iterate a1 a0 x0 y2 y0) = (@iterate a1 a0 x0 y2 y1).
Definition term8 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0 -> nat) := imp (forall y0 : a0, (@IN a0 y0 x0) -> (x1 y0) = (x2 y0)).
Definition term0 (a0 : Type') (a1 : Type') := forall y0 : type1400 a1, (@monoidal a1 y0) -> forall y1 : a0 -> a1, forall y2 : a0 -> a1, forall y3 : a0 -> Prop, (forall y4 : a0, (@IN a0 y4 y3) -> (y1 y4) = (y2 y4)) -> (@iterate a1 a0 y0 y3 y1) = (@iterate a1 a0 y0 y3 y2).
Definition term4 (a0 : Type') (a1 : Type') (x0 : type1400 a1) := (forall y0 : type1400 a1, (@monoidal a1 y0) -> forall y1 : a0 -> a1, forall y2 : a0 -> a1, forall y3 : a0 -> Prop, (forall y4 : a0, (@IN a0 y4 y3) -> (y1 y4) = (y2 y4)) -> (@iterate a1 a0 y0 y3 y1) = (@iterate a1 a0 y0 y3 y2)) -> forall y0 : a0 -> a1, forall y1 : a0 -> a1, forall y2 : a0 -> Prop, (forall y3 : a0, (@IN a0 y3 y2) -> (y0 y3) = (y1 y3)) -> (@iterate a1 a0 x0 y2 y0) = (@iterate a1 a0 x0 y2 y1).
Definition term9 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) (x2 : a0 -> nat) := (forall y0 : a0, (@IN a0 y0 x1) -> (x0 y0) = (x2 y0)) -> (@nsum a0 x1 x0) = (@nsum a0 x1 x2).
Definition term12 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> nat) := fun y0 : a0 -> Prop => (forall y1 : a0, (@IN a0 y1 y0) -> (x0 y1) = (x1 y1)) -> (@iterate nat a0 Nat.add y0 x0) = (@iterate nat a0 Nat.add y0 x1).
Definition term10 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) (x2 : a0 -> nat) := (forall y0 : a0, (@IN a0 y0 x1) -> (x0 y0) = (x2 y0)) -> (@iterate nat a0 Nat.add x1 x0) = (@iterate nat a0 Nat.add x1 x2).
Definition term16 (a0 : Type') (x0 : a0 -> nat) := fun y0 : a0 -> nat => forall y1 : a0 -> Prop, (forall y2 : a0, (@IN a0 y2 y1) -> (x0 y2) = (y0 y2)) -> (@iterate nat a0 Nat.add y1 x0) = (@iterate nat a0 Nat.add y1 y0).
Definition term15 (a0 : Type') (x0 : a0 -> nat) := fun y0 : a0 -> nat => forall y1 : a0 -> Prop, (forall y2 : a0, (@IN a0 y2 y1) -> (x0 y2) = (y0 y2)) -> (@nsum a0 y1 x0) = (@nsum a0 y1 y0).
Definition term18 (a0 : Type') (x0 : a0 -> nat) := forall y0 : a0 -> nat, forall y1 : a0 -> Prop, (forall y2 : a0, (@IN a0 y2 y1) -> (x0 y2) = (y0 y2)) -> (@iterate nat a0 Nat.add y1 x0) = (@iterate nat a0 Nat.add y1 y0).
Definition term17 (a0 : Type') (x0 : a0 -> nat) := forall y0 : a0 -> nat, forall y1 : a0 -> Prop, (forall y2 : a0, (@IN a0 y2 y1) -> (x0 y2) = (y0 y2)) -> (@nsum a0 y1 x0) = (@nsum a0 y1 y0).
Definition term11 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> nat) := fun y0 : a0 -> Prop => (forall y1 : a0, (@IN a0 y1 y0) -> (x0 y1) = (x1 y1)) -> (@nsum a0 y0 x0) = (@nsum a0 y0 x1).
Definition term6 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := @eq nat (@nsum a0 x0 x1).
Definition term7 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := @eq nat (@iterate nat a0 Nat.add x0 x1).
Definition term24 (a0 : Type') := (@monoidal nat Nat.add) -> forall y0 : a0 -> nat, forall y1 : a0 -> nat, forall y2 : a0 -> Prop, (forall y3 : a0, (@IN a0 y3 y2) -> (y0 y3) = (y1 y3)) -> (@iterate nat a0 Nat.add y2 y0) = (@iterate nat a0 Nat.add y2 y1).
Definition term1 (a0 : Type') (a1 : Type') (x0 : type1400 a1) := (fun y0 : type1400 a1 => (@monoidal a1 y0) -> forall y1 : a0 -> a1, forall y2 : a0 -> a1, forall y3 : a0 -> Prop, (forall y4 : a0, (@IN a0 y4 y3) -> (y1 y4) = (y2 y4)) -> (@iterate a1 a0 y0 y3 y1) = (@iterate a1 a0 y0 y3 y2)) x0.
Definition term5 (a0 : Type') (a1 : Type') := (forall y0 : type1400 a1, (@monoidal a1 y0) -> forall y1 : a0 -> a1, forall y2 : a0 -> a1, forall y3 : a0 -> Prop, (forall y4 : a0, (@IN a0 y4 y3) -> (y1 y4) = (y2 y4)) -> (@iterate a1 a0 y0 y3 y1) = (@iterate a1 a0 y0 y3 y2)) -> forall y0 : type1400 a1, (@monoidal a1 y0) -> forall y1 : a0 -> a1, forall y2 : a0 -> a1, forall y3 : a0 -> Prop, (forall y4 : a0, (@IN a0 y4 y3) -> (y1 y4) = (y2 y4)) -> (@iterate a1 a0 y0 y3 y1) = (@iterate a1 a0 y0 y3 y2).
Definition term20 (a0 : Type') := fun y0 : a0 -> nat => forall y1 : a0 -> nat, forall y2 : a0 -> Prop, (forall y3 : a0, (@IN a0 y3 y2) -> (y0 y3) = (y1 y3)) -> (@iterate nat a0 Nat.add y2 y0) = (@iterate nat a0 Nat.add y2 y1).
Definition term19 (a0 : Type') := fun y0 : a0 -> nat => forall y1 : a0 -> nat, forall y2 : a0 -> Prop, (forall y3 : a0, (@IN a0 y3 y2) -> (y0 y3) = (y1 y3)) -> (@nsum a0 y2 y0) = (@nsum a0 y2 y1).
Definition term14 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> nat) := forall y0 : a0 -> Prop, (forall y1 : a0, (@IN a0 y1 y0) -> (x0 y1) = (x1 y1)) -> (@iterate nat a0 Nat.add y0 x0) = (@iterate nat a0 Nat.add y0 x1).
Definition term13 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> nat) := forall y0 : a0 -> Prop, (forall y1 : a0, (@IN a0 y1 y0) -> (x0 y1) = (x1 y1)) -> (@nsum a0 y0 x0) = (@nsum a0 y0 x1).
