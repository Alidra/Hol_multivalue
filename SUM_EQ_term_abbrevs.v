Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term23 (a0 : Type') (x0 : type1627) := (@monoidal real x0) -> forall y0 : a0 -> real, forall y1 : a0 -> real, forall y2 : a0 -> Prop, (forall y3 : a0, (@IN a0 y3 y2) -> (y0 y3) = (y1 y3)) -> (@iterate real a0 x0 y2 y0) = (@iterate real a0 x0 y2 y1).
Definition term2 (a0 : Type') (a1 : Type') (x0 : type1400 a1) := (@monoidal a1 x0) -> forall y0 : a0 -> a1, forall y1 : a0 -> a1, forall y2 : a0 -> Prop, (forall y3 : a0, (@IN a0 y3 y2) -> (y0 y3) = (y1 y3)) -> (@iterate a1 a0 x0 y2 y0) = (@iterate a1 a0 x0 y2 y1).
Definition term22 (a0 : Type') := forall y0 : a0 -> real, forall y1 : a0 -> real, forall y2 : a0 -> Prop, (forall y3 : a0, (@IN a0 y3 y2) -> (y0 y3) = (y1 y3)) -> (@iterate real a0 real_add y2 y0) = (@iterate real a0 real_add y2 y1).
Definition term21 (a0 : Type') := forall y0 : a0 -> real, forall y1 : a0 -> real, forall y2 : a0 -> Prop, (forall y3 : a0, (@IN a0 y3 y2) -> (y0 y3) = (y1 y3)) -> (@sum a0 y2 y0) = (@sum a0 y2 y1).
Definition term3 (a0 : Type') (a1 : Type') (x0 : type1400 a1) := forall y0 : a0 -> a1, forall y1 : a0 -> a1, forall y2 : a0 -> Prop, (forall y3 : a0, (@IN a0 y3 y2) -> (y0 y3) = (y1 y3)) -> (@iterate a1 a0 x0 y2 y0) = (@iterate a1 a0 x0 y2 y1).
Definition term8 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0 -> real) := imp (forall y0 : a0, (@IN a0 y0 x0) -> (x1 y0) = (x2 y0)).
Definition term0 (a0 : Type') (a1 : Type') := forall y0 : type1400 a1, (@monoidal a1 y0) -> forall y1 : a0 -> a1, forall y2 : a0 -> a1, forall y3 : a0 -> Prop, (forall y4 : a0, (@IN a0 y4 y3) -> (y1 y4) = (y2 y4)) -> (@iterate a1 a0 y0 y3 y1) = (@iterate a1 a0 y0 y3 y2).
Definition term24 (a0 : Type') := (@monoidal real real_add) -> forall y0 : a0 -> real, forall y1 : a0 -> real, forall y2 : a0 -> Prop, (forall y3 : a0, (@IN a0 y3 y2) -> (y0 y3) = (y1 y3)) -> (@iterate real a0 real_add y2 y0) = (@iterate real a0 real_add y2 y1).
Definition term9 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : a0 -> real) := (forall y0 : a0, (@IN a0 y0 x1) -> (x0 y0) = (x2 y0)) -> (@sum a0 x1 x0) = (@sum a0 x1 x2).
Definition term4 (a0 : Type') (a1 : Type') (x0 : type1400 a1) := (forall y0 : type1400 a1, (@monoidal a1 y0) -> forall y1 : a0 -> a1, forall y2 : a0 -> a1, forall y3 : a0 -> Prop, (forall y4 : a0, (@IN a0 y4 y3) -> (y1 y4) = (y2 y4)) -> (@iterate a1 a0 y0 y3 y1) = (@iterate a1 a0 y0 y3 y2)) -> forall y0 : a0 -> a1, forall y1 : a0 -> a1, forall y2 : a0 -> Prop, (forall y3 : a0, (@IN a0 y3 y2) -> (y0 y3) = (y1 y3)) -> (@iterate a1 a0 x0 y2 y0) = (@iterate a1 a0 x0 y2 y1).
Definition term16 (a0 : Type') (x0 : a0 -> real) := fun y0 : a0 -> real => forall y1 : a0 -> Prop, (forall y2 : a0, (@IN a0 y2 y1) -> (x0 y2) = (y0 y2)) -> (@iterate real a0 real_add y1 x0) = (@iterate real a0 real_add y1 y0).
Definition term15 (a0 : Type') (x0 : a0 -> real) := fun y0 : a0 -> real => forall y1 : a0 -> Prop, (forall y2 : a0, (@IN a0 y2 y1) -> (x0 y2) = (y0 y2)) -> (@sum a0 y1 x0) = (@sum a0 y1 y0).
Definition term12 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> real) := fun y0 : a0 -> Prop => (forall y1 : a0, (@IN a0 y1 y0) -> (x0 y1) = (x1 y1)) -> (@iterate real a0 real_add y0 x0) = (@iterate real a0 real_add y0 x1).
Definition term10 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : a0 -> real) := (forall y0 : a0, (@IN a0 y0 x1) -> (x0 y0) = (x2 y0)) -> (@iterate real a0 real_add x1 x0) = (@iterate real a0 real_add x1 x2).
Definition term6 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := @eq real (@sum a0 x0 x1).
Definition term20 (a0 : Type') := fun y0 : a0 -> real => forall y1 : a0 -> real, forall y2 : a0 -> Prop, (forall y3 : a0, (@IN a0 y3 y2) -> (y0 y3) = (y1 y3)) -> (@iterate real a0 real_add y2 y0) = (@iterate real a0 real_add y2 y1).
Definition term19 (a0 : Type') := fun y0 : a0 -> real => forall y1 : a0 -> real, forall y2 : a0 -> Prop, (forall y3 : a0, (@IN a0 y3 y2) -> (y0 y3) = (y1 y3)) -> (@sum a0 y2 y0) = (@sum a0 y2 y1).
Definition term18 (a0 : Type') (x0 : a0 -> real) := forall y0 : a0 -> real, forall y1 : a0 -> Prop, (forall y2 : a0, (@IN a0 y2 y1) -> (x0 y2) = (y0 y2)) -> (@iterate real a0 real_add y1 x0) = (@iterate real a0 real_add y1 y0).
Definition term17 (a0 : Type') (x0 : a0 -> real) := forall y0 : a0 -> real, forall y1 : a0 -> Prop, (forall y2 : a0, (@IN a0 y2 y1) -> (x0 y2) = (y0 y2)) -> (@sum a0 y1 x0) = (@sum a0 y1 y0).
Definition term11 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> real) := fun y0 : a0 -> Prop => (forall y1 : a0, (@IN a0 y1 y0) -> (x0 y1) = (x1 y1)) -> (@sum a0 y0 x0) = (@sum a0 y0 x1).
Definition term7 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := @eq real (@iterate real a0 real_add x0 x1).
Definition term1 (a0 : Type') (a1 : Type') (x0 : type1400 a1) := (fun y0 : type1400 a1 => (@monoidal a1 y0) -> forall y1 : a0 -> a1, forall y2 : a0 -> a1, forall y3 : a0 -> Prop, (forall y4 : a0, (@IN a0 y4 y3) -> (y1 y4) = (y2 y4)) -> (@iterate a1 a0 y0 y3 y1) = (@iterate a1 a0 y0 y3 y2)) x0.
Definition term5 (a0 : Type') (a1 : Type') := (forall y0 : type1400 a1, (@monoidal a1 y0) -> forall y1 : a0 -> a1, forall y2 : a0 -> a1, forall y3 : a0 -> Prop, (forall y4 : a0, (@IN a0 y4 y3) -> (y1 y4) = (y2 y4)) -> (@iterate a1 a0 y0 y3 y1) = (@iterate a1 a0 y0 y3 y2)) -> forall y0 : type1400 a1, (@monoidal a1 y0) -> forall y1 : a0 -> a1, forall y2 : a0 -> a1, forall y3 : a0 -> Prop, (forall y4 : a0, (@IN a0 y4 y3) -> (y1 y4) = (y2 y4)) -> (@iterate a1 a0 y0 y3 y1) = (@iterate a1 a0 y0 y3 y2).
Definition term14 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> real) := forall y0 : a0 -> Prop, (forall y1 : a0, (@IN a0 y1 y0) -> (x0 y1) = (x1 y1)) -> (@iterate real a0 real_add y0 x0) = (@iterate real a0 real_add y0 x1).
Definition term13 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> real) := forall y0 : a0 -> Prop, (forall y1 : a0, (@IN a0 y1 y0) -> (x0 y1) = (x1 y1)) -> (@sum a0 y0 x0) = (@sum a0 y0 x1).
