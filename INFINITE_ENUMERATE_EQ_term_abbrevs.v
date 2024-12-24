Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term374 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := (~ ((@I (nat -> nat) x1 x0) = (@I (nat -> nat) x1 x2))) -> (@I (nat -> nat) x1 x0) = (@I (nat -> nat) x1 x2).
Definition term335 (x0 : nat) (x1 : nat) := ~ (x0 = x1).
Definition term91 (x0 : nat -> nat) := ((forall y0 : nat, ((x0 y0) = (x0 y0)) -> y0 = y0) /\ ((forall y0 : nat, forall y1 : nat, (((x0 y0) = (x0 y1)) -> y0 = y1) = (((x0 y1) = (x0 y0)) -> y1 = y0)) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> ((x0 y0) = (x0 y1)) -> y0 = y1))) -> forall y0 : nat, forall y1 : nat, ((x0 y0) = (x0 y1)) -> y0 = y1.
Definition term44 (x0 : nat -> nat) := ((forall y0 : nat, (fun y1 : nat => fun y2 : nat => ((x0 y1) = (x0 y2)) -> y1 = y2) y0 y0) /\ ((forall y0 : nat, forall y1 : nat, ((fun y2 : nat => fun y3 : nat => ((x0 y2) = (x0 y3)) -> y2 = y3) y0 y1) = ((fun y2 : nat => fun y3 : nat => ((x0 y2) = (x0 y3)) -> y2 = y3) y1 y0)) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> (fun y2 : nat => fun y3 : nat => ((x0 y2) = (x0 y3)) -> y2 = y3) y0 y1))) -> forall y0 : nat, forall y1 : nat, (fun y2 : nat => fun y3 : nat => ((x0 y2) = (x0 y3)) -> y2 = y3) y0 y1.
Definition term0 (x0 : type1605) := ((forall y0 : nat, x0 y0 y0) /\ ((forall y0 : nat, forall y1 : nat, (x0 y0 y1) = (x0 y1 y0)) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x0 y0 y1))) -> forall y0 : nat, forall y1 : nat, x0 y0 y1.
Definition term443 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := imp (~ ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (Peano.lt x2 x3))))).
Definition term132 (x0 : nat -> Prop) := ~ (all x0).
Definition term372 := (~ False) -> False.
Definition term46 (x0 : nat -> nat) (x1 : nat) := (fun y0 : nat => fun y1 : nat => ((x0 y0) = (x0 y1)) -> y0 = y1) x1.
Definition term343 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := ~ ((@I (nat -> nat) x1 x0) = (@I (nat -> nat) x1 x2)).
Definition term386 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((~ (x0 = x1)) \/ (~ (x0 = x2)))) -> x1 = x2.
Definition term30 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := imp ((@IN nat x0 (@UNIV nat)) /\ ((@IN nat x2 (@UNIV nat)) /\ ((x1 x0) = (x1 x2)))).
Definition term100 := ~ (forall y0 : nat, ~ (Peano.lt y0 y0)).
Definition term458 (x0 : nat -> Prop) := ((@INFINITE nat x0) -> exists y0 : nat -> nat, (forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> Peano.lt (y0 y1) (y0 y2)) /\ ((@IMAGE nat nat y0 (@UNIV nat)) = x0)) /\ ((exists y0 : nat -> nat, (forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> Peano.lt (y0 y1) (y0 y2)) /\ ((@IMAGE nat nat y0 (@UNIV nat)) = x0)) -> @INFINITE nat x0).
Definition term457 (x0 : nat -> Prop) := (exists y0 : nat -> nat, (forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> Peano.lt (y0 y1) (y0 y2)) /\ ((@IMAGE nat nat y0 (@UNIV nat)) = x0)) -> @INFINITE nat x0.
Definition term301 (x0 : nat -> nat) (x1 : nat) := or ((fun y0 : nat => ((x0 y0) = (x0 y0)) /\ (~ (y0 = y0))) x1).
Definition term356 (x0 : nat -> nat) (x1 : nat) := and ((x0 x1) = (x0 x1)).
Definition term362 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := (fun y0 : nat => (~ (Peano.lt x0 y0)) \/ (Peano.lt (@I (nat -> nat) x1 x0) (@I (nat -> nat) x1 y0))) x2.
Definition term16 (x0 : nat -> Prop) := (@INFINITE nat x0) -> exists y0 : nat -> nat, (forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> Peano.lt (y0 y1) (y0 y2)) /\ ((@IMAGE nat nat y0 (@UNIV nat)) = x0).
Definition term445 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((x0 = x2) /\ ((x1 = x3) /\ (Peano.lt x0 x1))) -> Peano.lt x2 x3.
Definition term392 (x0 : Prop) := ~ (~ x0).
Definition term413 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := (Peano.lt (@I (nat -> nat) x0 x1) (@I (nat -> nat) x0 x2)) \/ (~ (Peano.lt x1 x2)).
Definition term422 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.lt x0 x1) \/ ((~ (x3 = x1)) \/ (~ (Peano.lt x2 x3))).
Definition term341 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := (Peano.lt x1 x2) /\ (((@I (nat -> nat) x0 x1) = (@I (nat -> nat) x0 x2)) /\ (~ (x1 = x2))).
Definition term173 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := (Peano.lt x1 x2) /\ (((x0 x1) = (x0 x2)) /\ (~ (x1 = x2))).
Definition term282 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := ((fun y0 : nat => (((~ ((x0 x1) = (x0 y0))) \/ (x1 = y0)) /\ (((x0 y0) = (x0 x1)) /\ (~ (y0 = x1)))) \/ ((((x0 x1) = (x0 y0)) /\ (~ (x1 = y0))) /\ ((~ ((x0 y0) = (x0 x1))) \/ (y0 = x1)))) x2) \/ ((fun y0 : nat => (Peano.lt x1 y0) /\ (((x0 x1) = (x0 y0)) /\ (~ (x1 = y0)))) x2).
Definition term209 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := ((fun y0 : nat => ((~ ((x0 x1) = (x0 y0))) \/ (x1 = y0)) /\ (((x0 y0) = (x0 x1)) /\ (~ (y0 = x1)))) x2) \/ ((fun y0 : nat => (((x0 x1) = (x0 y0)) /\ (~ (x1 = y0))) /\ ((~ ((x0 y0) = (x0 x1))) \/ (y0 = x1))) x2).
Definition term113 (x0 : nat -> nat) := forall y0 : nat -> Prop, (forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> Peano.lt (x0 y1) (x0 y2)) -> (y0 = (@IMAGE nat nat x0 (@UNIV nat))) -> (~ ((forall y1 : nat, ((x0 y1) = (x0 y1)) -> y1 = y1) /\ ((forall y1 : nat, forall y2 : nat, (((x0 y1) = (x0 y2)) -> y1 = y2) = (((x0 y2) = (x0 y1)) -> y2 = y1)) /\ (forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> ((x0 y1) = (x0 y2)) -> y1 = y2)))) -> ~ (forall y1 : nat, ~ (Peano.lt y1 y1)).
Definition term112 (x0 : nat -> nat) := forall y0 : nat -> Prop, (forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> Peano.lt (x0 y1) (x0 y2)) -> (y0 = (@IMAGE nat nat x0 (@UNIV nat))) -> (~ ((forall y1 : nat, ((x0 y1) = (x0 y1)) -> y1 = y1) /\ ((forall y1 : nat, forall y2 : nat, (((x0 y1) = (x0 y2)) -> y1 = y2) = (((x0 y2) = (x0 y1)) -> y2 = y1)) /\ (forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> ((x0 y1) = (x0 y2)) -> y1 = y2)))) -> (forall y1 : nat, ~ (Peano.lt y1 y1)) -> False.
Definition term329 (x0 : nat) (x1 : nat) := or (~ (Peano.lt x0 x1)).
Definition term42 (x0 : nat -> nat) := (@INFINITE nat (@UNIV nat)) /\ (forall y0 : nat, forall y1 : nat, ((@IN nat y0 (@UNIV nat)) /\ ((@IN nat y1 (@UNIV nat)) /\ ((x0 y0) = (x0 y1)))) -> y0 = y1).
Definition term324 (x0 : nat -> nat) := fun y0 : nat => exists y1 : nat, (((x0 y0) = (x0 y0)) /\ (~ (y0 = y0))) \/ (((((~ ((x0 y0) = (x0 y1))) \/ (y0 = y1)) /\ (((x0 y1) = (x0 y0)) /\ (~ (y1 = y0)))) \/ ((((x0 y0) = (x0 y1)) /\ (~ (y0 = y1))) /\ ((~ ((x0 y1) = (x0 y0))) \/ (y1 = y0)))) \/ ((Peano.lt y0 y1) /\ (((x0 y0) = (x0 y1)) /\ (~ (y0 = y1))))).
Definition term287 (x0 : nat -> nat) := fun y0 : nat => exists y1 : nat, ((((~ ((x0 y0) = (x0 y1))) \/ (y0 = y1)) /\ (((x0 y1) = (x0 y0)) /\ (~ (y1 = y0)))) \/ ((((x0 y0) = (x0 y1)) /\ (~ (y0 = y1))) /\ ((~ ((x0 y1) = (x0 y0))) \/ (y1 = y0)))) \/ ((Peano.lt y0 y1) /\ (((x0 y0) = (x0 y1)) /\ (~ (y0 = y1)))).
Definition term227 (x0 : nat -> nat) := fun y0 : nat => exists y1 : nat, (((x0 y0) = (x0 y1)) /\ (~ (y0 = y1))) /\ ((~ ((x0 y1) = (x0 y0))) \/ (y1 = y0)).
Definition term226 (x0 : nat -> nat) := fun y0 : nat => exists y1 : nat, ((~ ((x0 y0) = (x0 y1))) \/ (y0 = y1)) /\ (((x0 y1) = (x0 y0)) /\ (~ (y1 = y0))).
Definition term187 (x0 : nat -> nat) := fun y0 : nat => exists y1 : nat, (Peano.lt y0 y1) /\ (((x0 y0) = (x0 y1)) /\ (~ (y0 = y1))).
Definition term169 (x0 : nat -> nat) := fun y0 : nat => exists y1 : nat, (((~ ((x0 y0) = (x0 y1))) \/ (y0 = y1)) /\ (((x0 y1) = (x0 y0)) /\ (~ (y1 = y0)))) \/ ((((x0 y0) = (x0 y1)) /\ (~ (y0 = y1))) /\ ((~ ((x0 y1) = (x0 y0))) \/ (y1 = y0))).
Definition term400 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := ((@I (nat -> nat) x1 x2) = (@I (nat -> nat) x1 x0)) /\ ((@I (nat -> nat) x1 x2) = (@I (nat -> nat) x1 x2)).
Definition term263 (x0 : nat -> nat) (x1 : nat) := or (exists y0 : nat, (((~ ((x0 x1) = (x0 y0))) \/ (x1 = y0)) /\ (((x0 y0) = (x0 x1)) /\ (~ (y0 = x1)))) \/ ((((x0 x1) = (x0 y0)) /\ (~ (x1 = y0))) /\ ((~ ((x0 y0) = (x0 x1))) \/ (y0 = x1)))).
Definition term217 (x0 : nat -> nat) (x1 : nat) := or (exists y0 : nat, ((~ ((x0 x1) = (x0 y0))) \/ (x1 = y0)) /\ (((x0 y0) = (x0 x1)) /\ (~ (y0 = x1)))).
Definition term195 (x0 : nat -> nat) := or (exists y0 : nat, ((x0 y0) = (x0 y0)) /\ (~ (y0 = y0))).
Definition term452 (x0 : nat) := (Peano.lt x0 x0) -> False.
Definition term29 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := (@IN nat x0 (@UNIV nat)) /\ ((@IN nat x2 (@UNIV nat)) /\ ((x1 x0) = (x1 x2))).
Definition term440 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (~ (x2 = x0))) /\ (~ (~ (Peano.lt x1 x2))).
Definition term391 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (~ (x1 = x0))) /\ (~ (~ (x1 = x2))).
Definition term265 (x0 : nat -> nat) (x1 : nat) := (exists y0 : nat, (((~ ((x0 x1) = (x0 y0))) \/ (x1 = y0)) /\ (((x0 y0) = (x0 x1)) /\ (~ (y0 = x1)))) \/ ((((x0 x1) = (x0 y0)) /\ (~ (x1 = y0))) /\ ((~ ((x0 y0) = (x0 x1))) \/ (y0 = x1)))) \/ (exists y0 : nat, (Peano.lt x1 y0) /\ (((x0 x1) = (x0 y0)) /\ (~ (x1 = y0)))).
Definition term221 (x0 : nat -> nat) (x1 : nat) := (exists y0 : nat, ((~ ((x0 x1) = (x0 y0))) \/ (x1 = y0)) /\ (((x0 y0) = (x0 x1)) /\ (~ (y0 = x1)))) \/ (exists y0 : nat, (((x0 x1) = (x0 y0)) /\ (~ (x1 = y0))) /\ ((~ ((x0 y0) = (x0 x1))) \/ (y0 = x1))).
Definition term199 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term420 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := (~ (Peano.lt (@I (nat -> nat) x1 x0) (@I (nat -> nat) x1 x2))) -> Peano.lt (@I (nat -> nat) x1 x0) (@I (nat -> nat) x1 x2).
Definition term244 (x0 : nat -> nat) := or ((exists y0 : nat, exists y1 : nat, ((~ ((x0 y0) = (x0 y1))) \/ (y0 = y1)) /\ (((x0 y1) = (x0 y0)) /\ (~ (y1 = y0)))) \/ (exists y0 : nat, exists y1 : nat, (((x0 y0) = (x0 y1)) /\ (~ (y0 = y1))) /\ ((~ ((x0 y1) = (x0 y0))) \/ (y1 = y0)))).
Definition term364 (x0 : nat) := fun y0 : nat => ~ (x0 = y0).
Definition term304 (x0 : nat -> nat) (x1 : nat) := (((x0 x1) = (x0 x1)) /\ (~ (x1 = x1))) \/ (exists y0 : nat, ((((~ ((x0 x1) = (x0 y0))) \/ (x1 = y0)) /\ (((x0 y0) = (x0 x1)) /\ (~ (y0 = x1)))) \/ ((((x0 x1) = (x0 y0)) /\ (~ (x1 = y0))) /\ ((~ ((x0 y0) = (x0 x1))) \/ (y0 = x1)))) \/ ((Peano.lt x1 y0) /\ (((x0 x1) = (x0 y0)) /\ (~ (x1 = y0))))).
Definition term326 (x0 : nat -> nat) (x1 : nat) := Peano.lt (x0 x1).
Definition term292 (x0 : nat -> nat) (x1 : nat) := (fun y0 : nat => ((x0 y0) = (x0 y0)) /\ (~ (y0 = y0))) x1.
Definition term355 (x0 : nat) := ~ (x0 = x0).
Definition term177 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.lt x1 y0) -> ((x0 x1) = (x0 y0)) -> x1 = y0) x2.
Definition term455 (x0 : nat -> nat) (x1 : nat -> Prop) := (fun y0 : nat -> Prop => (forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> Peano.lt (x0 y1) (x0 y2)) -> (y0 = (@IMAGE nat nat x0 (@UNIV nat))) -> (~ ((forall y1 : nat, ((x0 y1) = (x0 y1)) -> y1 = y1) /\ ((forall y1 : nat, forall y2 : nat, (((x0 y1) = (x0 y2)) -> y1 = y2) = (((x0 y2) = (x0 y1)) -> y2 = y1)) /\ (forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> ((x0 y1) = (x0 y2)) -> y1 = y2)))) -> (forall y1 : nat, ~ (Peano.lt y1 y1)) -> False) x1.
Definition term92 (x0 : Prop) := (~ x0) -> False.
Definition term82 (x0 : nat -> nat) := (forall y0 : nat, forall y1 : nat, (((x0 y0) = (x0 y1)) -> y0 = y1) = (((x0 y1) = (x0 y0)) -> y1 = y0)) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> ((x0 y0) = (x0 y1)) -> y0 = y1).
Definition term81 (x0 : nat -> nat) := (forall y0 : nat, forall y1 : nat, ((fun y2 : nat => fun y3 : nat => ((x0 y2) = (x0 y3)) -> y2 = y3) y0 y1) = ((fun y2 : nat => fun y3 : nat => ((x0 y2) = (x0 y3)) -> y2 = y3) y1 y0)) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> (fun y2 : nat => fun y3 : nat => ((x0 y2) = (x0 y3)) -> y2 = y3) y0 y1).
Definition term397 (x0 : nat) (x1 : nat) (x2 : nat) := imp (~ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term428 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.lt x0 x3) \/ ((~ (x1 = x0)) \/ ((~ (Peano.lt x1 x2)) \/ (~ (x2 = x3)))).
Definition term185 (x0 : nat -> nat) (x1 : nat) := ~ ((fun y0 : nat => forall y1 : nat, (Peano.lt y0 y1) -> ((x0 y0) = (x0 y1)) -> y0 = y1) x1).
Definition term167 (x0 : nat -> nat) (x1 : nat) := ~ ((fun y0 : nat => forall y1 : nat, (((x0 y0) = (x0 y1)) -> y0 = y1) = (((x0 y1) = (x0 y0)) -> y1 = y0)) x1).
Definition term451 (x0 : nat -> nat) (x1 : nat) := ~ (Peano.lt (@I (nat -> nat) x0 x1) (@I (nat -> nat) x0 x1)).
Definition term93 (x0 : nat -> nat) := (~ ((forall y0 : nat, ((x0 y0) = (x0 y0)) -> y0 = y0) /\ ((forall y0 : nat, forall y1 : nat, (((x0 y0) = (x0 y1)) -> y0 = y1) = (((x0 y1) = (x0 y0)) -> y1 = y0)) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> ((x0 y0) = (x0 y1)) -> y0 = y1)))) -> False.
Definition term453 (x0 : nat -> nat) (x1 : nat) := (Peano.lt (@I (nat -> nat) x0 x1) (@I (nat -> nat) x0 x1)) -> False.
Definition term424 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.lt x0 x1)) \/ (~ (x1 = x2)).
Definition term24 (x0 : nat -> nat) := ((@INFINITE nat (@UNIV nat)) /\ (forall y0 : nat, forall y1 : nat, ((@IN nat y0 (@UNIV nat)) /\ ((@IN nat y1 (@UNIV nat)) /\ ((x0 y0) = (x0 y1)))) -> y0 = y1)) -> @INFINITE nat (@IMAGE nat nat x0 (@UNIV nat)).
Definition term115 := fun y0 : nat -> nat => forall y1 : nat -> Prop, (forall y2 : nat, forall y3 : nat, (Peano.lt y2 y3) -> Peano.lt (y0 y2) (y0 y3)) -> (y1 = (@IMAGE nat nat y0 (@UNIV nat))) -> (~ ((forall y2 : nat, ((y0 y2) = (y0 y2)) -> y2 = y2) /\ ((forall y2 : nat, forall y3 : nat, (((y0 y2) = (y0 y3)) -> y2 = y3) = (((y0 y3) = (y0 y2)) -> y3 = y2)) /\ (forall y2 : nat, forall y3 : nat, (Peano.lt y2 y3) -> ((y0 y2) = (y0 y3)) -> y2 = y3)))) -> ~ (forall y2 : nat, ~ (Peano.lt y2 y2)).
Definition term114 := fun y0 : nat -> nat => forall y1 : nat -> Prop, (forall y2 : nat, forall y3 : nat, (Peano.lt y2 y3) -> Peano.lt (y0 y2) (y0 y3)) -> (y1 = (@IMAGE nat nat y0 (@UNIV nat))) -> (~ ((forall y2 : nat, ((y0 y2) = (y0 y2)) -> y2 = y2) /\ ((forall y2 : nat, forall y3 : nat, (((y0 y2) = (y0 y3)) -> y2 = y3) = (((y0 y3) = (y0 y2)) -> y3 = y2)) /\ (forall y2 : nat, forall y3 : nat, (Peano.lt y2 y3) -> ((y0 y2) = (y0 y3)) -> y2 = y3)))) -> (forall y2 : nat, ~ (Peano.lt y2 y2)) -> False.
Definition term172 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := (Peano.lt x1 x2) /\ (~ (((x0 x1) = (x0 x2)) -> x1 = x2)).
Definition term340 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := ((@I (nat -> nat) x0 x1) = (@I (nat -> nat) x0 x2)) /\ (~ (x1 = x2)).
Definition term319 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := (((x0 x1) = (x0 x1)) /\ (~ (x1 = x1))) \/ ((fun y0 : nat => ((((~ ((x0 x1) = (x0 y0))) \/ (x1 = y0)) /\ (((x0 y0) = (x0 x1)) /\ (~ (y0 = x1)))) \/ ((((x0 x1) = (x0 y0)) /\ (~ (x1 = y0))) /\ ((~ ((x0 y0) = (x0 x1))) \/ (y0 = x1)))) \/ ((Peano.lt x1 y0) /\ (((x0 x1) = (x0 y0)) /\ (~ (x1 = y0))))) x2).
Definition term159 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (((x0 x1) = (x0 y0)) -> x1 = y0) = (((x0 y0) = (x0 x1)) -> y0 = x1)) x2.
Definition term402 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := ((@I (nat -> nat) x1 x0) = (@I (nat -> nat) x1 x2)) -> False.
Definition term311 (x0 : Prop) (x1 : nat -> Prop) := exists y0 : nat, x0 \/ (x1 y0).
Definition term427 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x1 = x0)) \/ ((Peano.lt x0 x3) \/ ((~ (Peano.lt x1 x2)) \/ (~ (x2 = x3)))).
Definition term56 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => fun y1 : nat => ((x0 y0) = (x0 y1)) -> y0 = y1) x1 x2.
Definition term323 (x0 : nat -> nat) (x1 : nat) := exists y0 : nat, (((x0 x1) = (x0 x1)) /\ (~ (x1 = x1))) \/ (((((~ ((x0 x1) = (x0 y0))) \/ (x1 = y0)) /\ (((x0 y0) = (x0 x1)) /\ (~ (y0 = x1)))) \/ ((((x0 x1) = (x0 y0)) /\ (~ (x1 = y0))) /\ ((~ ((x0 y0) = (x0 x1))) \/ (y0 = x1)))) \/ ((Peano.lt x1 y0) /\ (((x0 x1) = (x0 y0)) /\ (~ (x1 = y0))))).
Definition term286 (x0 : nat -> nat) (x1 : nat) := exists y0 : nat, ((((~ ((x0 x1) = (x0 y0))) \/ (x1 = y0)) /\ (((x0 y0) = (x0 x1)) /\ (~ (y0 = x1)))) \/ ((((x0 x1) = (x0 y0)) /\ (~ (x1 = y0))) /\ ((~ ((x0 y0) = (x0 x1))) \/ (y0 = x1)))) \/ ((Peano.lt x1 y0) /\ (((x0 x1) = (x0 y0)) /\ (~ (x1 = y0)))).
Definition term163 (x0 : nat -> nat) (x1 : nat) := exists y0 : nat, (((~ ((x0 x1) = (x0 y0))) \/ (x1 = y0)) /\ (((x0 y0) = (x0 x1)) /\ (~ (y0 = x1)))) \/ ((((x0 x1) = (x0 y0)) /\ (~ (x1 = y0))) /\ ((~ ((x0 y0) = (x0 x1))) \/ (y0 = x1))).
Definition term49 (x0 : nat -> nat) (x1 : nat) := ((x0 x1) = (x0 x1)) -> x1 = x1.
Definition term385 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term206 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((~ ((x0 x1) = (x0 y0))) \/ (x1 = y0)) /\ (((x0 y0) = (x0 x1)) /\ (~ (y0 = x1)))) x2.
Definition term395 (x0 : nat) (x1 : nat) := and (x0 = x1).
Definition term145 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := and (((x0 x1) = (x0 x2)) /\ (~ (x1 = x2))).
Definition term196 (x0 : nat -> nat) := (~ (forall y0 : nat, ((x0 y0) = (x0 y0)) -> y0 = y0)) \/ (~ ((forall y0 : nat, forall y1 : nat, (((x0 y0) = (x0 y1)) -> y0 = y1) = (((x0 y1) = (x0 y0)) -> y1 = y0)) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> ((x0 y0) = (x0 y1)) -> y0 = y1))).
Definition term318 (x0 : nat -> nat) (x1 : nat) := @eq Prop ((((x0 x1) = (x0 x1)) /\ (~ (x1 = x1))) \/ (exists y0 : nat, ((((~ ((x0 x1) = (x0 y0))) \/ (x1 = y0)) /\ (((x0 y0) = (x0 x1)) /\ (~ (y0 = x1)))) \/ ((((x0 x1) = (x0 y0)) /\ (~ (x1 = y0))) /\ ((~ ((x0 y0) = (x0 x1))) \/ (y0 = x1)))) \/ ((Peano.lt x1 y0) /\ (((x0 x1) = (x0 y0)) /\ (~ (x1 = y0)))))).
Definition term317 (x0 : nat -> nat) (x1 : nat) := @eq Prop ((((x0 x1) = (x0 x1)) /\ (~ (x1 = x1))) \/ (exists y0 : nat, (fun y1 : nat => ((((~ ((x0 x1) = (x0 y1))) \/ (x1 = y1)) /\ (((x0 y1) = (x0 x1)) /\ (~ (y1 = x1)))) \/ ((((x0 x1) = (x0 y1)) /\ (~ (x1 = y1))) /\ ((~ ((x0 y1) = (x0 x1))) \/ (y1 = x1)))) \/ ((Peano.lt x1 y1) /\ (((x0 x1) = (x0 y1)) /\ (~ (x1 = y1))))) y0)).
Definition term33 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := ((x0 x1) = (x0 x2)) -> x1 = x2.
Definition term175 (x0 : nat -> nat) (x1 : nat) := ~ (forall y0 : nat, (Peano.lt x1 y0) -> ((x0 x1) = (x0 y0)) -> x1 = y0).
Definition term157 (x0 : nat -> nat) (x1 : nat) := ~ (forall y0 : nat, (((x0 x1) = (x0 y0)) -> x1 = y0) = (((x0 y0) = (x0 x1)) -> y0 = x1)).
Definition term134 (x0 : nat -> nat) := ~ (forall y0 : nat, ((x0 y0) = (x0 y0)) -> y0 = y0).
Definition term182 (x0 : nat -> nat) := ~ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> ((x0 y0) = (x0 y1)) -> y0 = y1).
Definition term164 (x0 : nat -> nat) := ~ (forall y0 : nat, forall y1 : nat, (((x0 y0) = (x0 y1)) -> y0 = y1) = (((x0 y1) = (x0 y0)) -> y1 = y0)).
Definition term14 (a0 : Type') (a1 : Type') := (forall y0 : a0 -> a1, forall y1 : a0 -> Prop, ((@INFINITE a0 y1) /\ (forall y2 : a0, forall y3 : a0, ((@IN a0 y2 y1) /\ ((@IN a0 y3 y1) /\ ((y0 y2) = (y0 y3)))) -> y2 = y3)) -> @INFINITE a1 (@IMAGE a0 a1 y0 y1)) -> forall y0 : a0 -> a1, forall y1 : a0 -> Prop, ((@INFINITE a0 y1) /\ (forall y2 : a0, forall y3 : a0, ((@IN a0 y2 y1) /\ ((@IN a0 y3 y1) /\ ((y0 y2) = (y0 y3)))) -> y2 = y3)) -> @INFINITE a1 (@IMAGE a0 a1 y0 y1).
Definition term208 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (((x0 x1) = (x0 y0)) /\ (~ (x1 = y0))) /\ ((~ ((x0 y0) = (x0 x1))) \/ (y0 = x1))) x2.
Definition term351 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := or (((~ ((@I (nat -> nat) x0 x2) = (@I (nat -> nat) x0 x1))) \/ (x2 = x1)) /\ (((@I (nat -> nat) x0 x1) = (@I (nat -> nat) x0 x2)) /\ (~ (x1 = x2)))).
Definition term153 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := or (((~ ((x0 x2) = (x0 x1))) \/ (x2 = x1)) /\ (((x0 x1) = (x0 x2)) /\ (~ (x1 = x2)))).
Definition term441 (x0 : nat) (x1 : nat) (x2 : nat) := (x2 = x0) /\ (Peano.lt x1 x2).
Definition term370 (x0 : Prop) := (~ x0) -> x0.
Definition term396 (x0 : nat) (x1 : nat) (x2 : nat) := (x1 = x0) /\ (x1 = x2).
Definition term306 (x0 : nat -> nat) := fun y0 : nat => (((x0 y0) = (x0 y0)) /\ (~ (y0 = y0))) \/ (exists y1 : nat, ((((~ ((x0 y0) = (x0 y1))) \/ (y0 = y1)) /\ (((x0 y1) = (x0 y0)) /\ (~ (y1 = y0)))) \/ ((((x0 y0) = (x0 y1)) /\ (~ (y0 = y1))) /\ ((~ ((x0 y1) = (x0 y0))) \/ (y1 = y0)))) \/ ((Peano.lt y0 y1) /\ (((x0 y0) = (x0 y1)) /\ (~ (y0 = y1))))).
Definition term139 (x0 : nat -> nat) := fun y0 : nat => ((x0 y0) = (x0 y0)) /\ (~ (y0 = y0)).
Definition term12 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := @INFINITE a1 (@IMAGE a0 a1 x0 x1).
Definition term174 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := ~ ((Peano.lt x1 x2) -> ((x0 x1) = (x0 x2)) -> x1 = x2).
Definition term449 (x0 : nat -> nat) (x1 : nat) := Peano.lt (@I (nat -> nat) x0 x1) (@I (nat -> nat) x0 x1).
Definition term45 (x0 : nat -> nat) := fun y0 : nat => fun y1 : nat => ((x0 y0) = (x0 y1)) -> y0 = y1.
Definition term387 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x1 = x0)) \/ (~ (x1 = x2)).
Definition term26 (x0 : nat) := and (@IN nat x0 (@UNIV nat)).
Definition term336 (x0 : nat -> nat) (x1 : nat) := @eq nat (x0 x1).
Definition term389 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term375 (x0 : nat -> nat) (x1 : nat) := (~ ((@I (nat -> nat) x0 x1) = (@I (nat -> nat) x0 x1))) -> (@I (nat -> nat) x0 x1) = (@I (nat -> nat) x0 x1).
Definition term369 (x0 : nat) := (~ (x0 = x0)) -> x0 = x0.
Definition term130 (x0 : nat -> nat) (x1 : nat) := ~ (((x0 x1) = (x0 x1)) -> x1 = x1).
Definition term431 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.lt x1 x3) \/ ((~ (Peano.lt x0 x2)) \/ ((~ (x0 = x1)) \/ (~ (x2 = x3)))).
Definition term383 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2))).
Definition term331 (x0 : nat) (x1 : nat -> nat) := fun y0 : nat => (~ (Peano.lt x0 y0)) \/ (Peano.lt (@I (nat -> nat) x1 x0) (@I (nat -> nat) x1 y0)).
Definition term194 (x0 : nat -> nat) := or (~ (forall y0 : nat, ((x0 y0) = (x0 y0)) -> y0 = y0)).
Definition term189 (x0 : nat -> nat) := or (~ (forall y0 : nat, forall y1 : nat, (((x0 y0) = (x0 y1)) -> y0 = y1) = (((x0 y1) = (x0 y0)) -> y1 = y0))).
Definition term384 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term314 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((((~ ((x0 x1) = (x0 y0))) \/ (x1 = y0)) /\ (((x0 y0) = (x0 x1)) /\ (~ (y0 = x1)))) \/ ((((x0 x1) = (x0 y0)) /\ (~ (x1 = y0))) /\ ((~ ((x0 y0) = (x0 x1))) \/ (y0 = x1)))) \/ ((Peano.lt x1 y0) /\ (((x0 x1) = (x0 y0)) /\ (~ (x1 = y0))))) x2.
Definition term345 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := or (~ ((@I (nat -> nat) x1 x0) = (@I (nat -> nat) x1 x2))).
Definition term125 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := Peano.lt (x1 x0) (x1 x2).
Definition term297 (x0 : nat -> nat) := fun y0 : nat => (fun y1 : nat => exists y2 : nat, ((((~ ((x0 y1) = (x0 y2))) \/ (y1 = y2)) /\ (((x0 y2) = (x0 y1)) /\ (~ (y2 = y1)))) \/ ((((x0 y1) = (x0 y2)) /\ (~ (y1 = y2))) /\ ((~ ((x0 y2) = (x0 y1))) \/ (y2 = y1)))) \/ ((Peano.lt y1 y2) /\ (((x0 y1) = (x0 y2)) /\ (~ (y1 = y2))))) y0.
Definition term258 (x0 : nat -> nat) := fun y0 : nat => (fun y1 : nat => exists y2 : nat, (Peano.lt y1 y2) /\ (((x0 y1) = (x0 y2)) /\ (~ (y1 = y2)))) y0.
Definition term254 (x0 : nat -> nat) := fun y0 : nat => (fun y1 : nat => exists y2 : nat, (((~ ((x0 y1) = (x0 y2))) \/ (y1 = y2)) /\ (((x0 y2) = (x0 y1)) /\ (~ (y2 = y1)))) \/ ((((x0 y1) = (x0 y2)) /\ (~ (y1 = y2))) /\ ((~ ((x0 y2) = (x0 y1))) \/ (y2 = y1)))) y0.
Definition term240 (x0 : nat -> nat) := fun y0 : nat => (fun y1 : nat => exists y2 : nat, (((x0 y1) = (x0 y2)) /\ (~ (y1 = y2))) /\ ((~ ((x0 y2) = (x0 y1))) \/ (y2 = y1))) y0.
Definition term235 (x0 : nat -> nat) := fun y0 : nat => (fun y1 : nat => exists y2 : nat, ((~ ((x0 y1) = (x0 y2))) \/ (y1 = y2)) /\ (((x0 y2) = (x0 y1)) /\ (~ (y2 = y1)))) y0.
Definition term347 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := and (((@I (nat -> nat) x0 x1) = (@I (nat -> nat) x0 x2)) /\ (~ (x1 = x2))).
Definition term381 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term361 (x0 : nat -> nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (~ (Peano.lt y0 y1)) \/ (Peano.lt (@I (nat -> nat) x0 y0) (@I (nat -> nat) x0 y1))) x1.
Definition term184 (x0 : nat -> nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y0 y1) -> ((x0 y0) = (x0 y1)) -> y0 = y1) x1.
Definition term166 (x0 : nat -> nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (((x0 y0) = (x0 y1)) -> y0 = y1) = (((x0 y1) = (x0 y0)) -> y1 = y0)) x1.
Definition term433 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop ((Peano.lt x1 x3) \/ ((~ (Peano.lt x0 x2)) \/ ((~ (x0 = x1)) \/ (~ (x2 = x3))))).
Definition term197 (x0 : nat -> nat) := (exists y0 : nat, ((x0 y0) = (x0 y0)) /\ (~ (y0 = y0))) \/ ((exists y0 : nat, exists y1 : nat, (((~ ((x0 y0) = (x0 y1))) \/ (y0 = y1)) /\ (((x0 y1) = (x0 y0)) /\ (~ (y1 = y0)))) \/ ((((x0 y0) = (x0 y1)) /\ (~ (y0 = y1))) /\ ((~ ((x0 y1) = (x0 y0))) \/ (y1 = y0)))) \/ (exists y0 : nat, exists y1 : nat, (Peano.lt y0 y1) /\ (((x0 y0) = (x0 y1)) /\ (~ (y0 = y1))))).
Definition term59 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := @eq Prop (((x0 x1) = (x0 x2)) -> x1 = x2).
Definition term423 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x2 = x0)) \/ (~ (Peano.lt x1 x2)).
Definition term71 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := (Peano.lt x1 x2) -> (fun y0 : nat => fun y1 : nat => ((x0 y0) = (x0 y1)) -> y0 = y1) x1 x2.
Definition term141 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := ~ (((x0 x1) = (x0 x2)) -> x1 = x2).
Definition term31 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := imp ((x1 x0) = (x1 x2)).
Definition term77 (x0 : nat -> nat) := fun y0 : nat => forall y1 : nat, (Peano.lt y0 y1) -> (fun y2 : nat => fun y3 : nat => ((x0 y2) = (x0 y3)) -> y2 = y3) y0 y1.
Definition term64 (x0 : nat -> nat) := fun y0 : nat => forall y1 : nat, ((fun y2 : nat => fun y3 : nat => ((x0 y2) = (x0 y3)) -> y2 = y3) y0 y1) = ((fun y2 : nat => fun y3 : nat => ((x0 y2) = (x0 y3)) -> y2 = y3) y1 y0).
Definition term39 (x0 : nat -> nat) := fun y0 : nat => forall y1 : nat, ((x0 y0) = (x0 y1)) -> y0 = y1.
Definition term38 (x0 : nat -> nat) := fun y0 : nat => forall y1 : nat, ((@IN nat y0 (@UNIV nat)) /\ ((@IN nat y1 (@UNIV nat)) /\ ((x0 y0) = (x0 y1)))) -> y0 = y1.
Definition term417 (x0 : nat) (x1 : nat) := ~ (~ (Peano.lt x0 x1)).
Definition term456 (x0 : nat -> Prop) := fun y0 : nat -> nat => (forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> Peano.lt (y0 y1) (y0 y2)) /\ ((@IMAGE nat nat y0 (@UNIV nat)) = x0).
Definition term444 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := imp ((x2 = x0) /\ ((x3 = x1) /\ (Peano.lt x2 x3))).
Definition term338 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := and ((x1 x0) = (x1 x2)).
Definition term360 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := (((@I (nat -> nat) x0 x1) = (@I (nat -> nat) x0 x1)) /\ (~ (x1 = x1))) \/ (((((~ ((@I (nat -> nat) x0 x1) = (@I (nat -> nat) x0 x2))) \/ (x1 = x2)) /\ (((@I (nat -> nat) x0 x2) = (@I (nat -> nat) x0 x1)) /\ (~ (x2 = x1)))) \/ ((((@I (nat -> nat) x0 x1) = (@I (nat -> nat) x0 x2)) /\ (~ (x1 = x2))) /\ ((~ ((@I (nat -> nat) x0 x2) = (@I (nat -> nat) x0 x1))) \/ (x2 = x1)))) \/ ((Peano.lt x1 x2) /\ (((@I (nat -> nat) x0 x1) = (@I (nat -> nat) x0 x2)) /\ (~ (x1 = x2))))).
Definition term320 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := (((x0 x1) = (x0 x1)) /\ (~ (x1 = x1))) \/ (((((~ ((x0 x1) = (x0 x2))) \/ (x1 = x2)) /\ (((x0 x2) = (x0 x1)) /\ (~ (x2 = x1)))) \/ ((((x0 x1) = (x0 x2)) /\ (~ (x1 = x2))) /\ ((~ ((x0 x2) = (x0 x1))) \/ (x2 = x1)))) \/ ((Peano.lt x1 x2) /\ (((x0 x1) = (x0 x2)) /\ (~ (x1 = x2))))).
Definition term9 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => ((@INFINITE a0 y0) /\ (forall y1 : a0, forall y2 : a0, ((@IN a0 y1 y0) /\ ((@IN a0 y2 y0) /\ ((x0 y1) = (x0 y2)))) -> y1 = y2)) -> @INFINITE a1 (@IMAGE a0 a1 x0 y0)) x1.
Definition term405 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.lt x0 x1) \/ (~ (Peano.lt x2 x3)).
Definition term234 (x0 : nat -> nat) := @eq Prop (exists y0 : nat, (exists y1 : nat, ((~ ((x0 y0) = (x0 y1))) \/ (y0 = y1)) /\ (((x0 y1) = (x0 y0)) /\ (~ (y1 = y0)))) \/ (exists y1 : nat, (((x0 y0) = (x0 y1)) /\ (~ (y0 = y1))) /\ ((~ ((x0 y1) = (x0 y0))) \/ (y1 = y0)))).
Definition term233 (x0 : nat -> nat) := @eq Prop (exists y0 : nat, ((fun y1 : nat => exists y2 : nat, ((~ ((x0 y1) = (x0 y2))) \/ (y1 = y2)) /\ (((x0 y2) = (x0 y1)) /\ (~ (y2 = y1)))) y0) \/ ((fun y1 : nat => exists y2 : nat, (((x0 y1) = (x0 y2)) /\ (~ (y1 = y2))) /\ ((~ ((x0 y2) = (x0 y1))) \/ (y2 = y1))) y0)).
Definition term212 (x0 : nat -> nat) (x1 : nat) := @eq Prop (exists y0 : nat, (((~ ((x0 x1) = (x0 y0))) \/ (x1 = y0)) /\ (((x0 y0) = (x0 x1)) /\ (~ (y0 = x1)))) \/ ((((x0 x1) = (x0 y0)) /\ (~ (x1 = y0))) /\ ((~ ((x0 y0) = (x0 x1))) \/ (y0 = x1)))).
Definition term211 (x0 : nat -> nat) (x1 : nat) := @eq Prop (exists y0 : nat, ((fun y1 : nat => ((~ ((x0 x1) = (x0 y1))) \/ (x1 = y1)) /\ (((x0 y1) = (x0 x1)) /\ (~ (y1 = x1)))) y0) \/ ((fun y1 : nat => (((x0 x1) = (x0 y1)) /\ (~ (x1 = y1))) /\ ((~ ((x0 y1) = (x0 x1))) \/ (y1 = x1))) y0)).
Definition term103 (x0 : nat -> nat) := (~ ((forall y0 : nat, ((x0 y0) = (x0 y0)) -> y0 = y0) /\ ((forall y0 : nat, forall y1 : nat, (((x0 y0) = (x0 y1)) -> y0 = y1) = (((x0 y1) = (x0 y0)) -> y1 = y0)) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> ((x0 y0) = (x0 y1)) -> y0 = y1)))) -> (forall y0 : nat, ~ (Peano.lt y0 y0)) -> False.
Definition term97 (x0 : nat -> Prop) (x1 : nat -> nat) := (((forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.lt (x1 y0) (x1 y1)) -> (x0 = (@IMAGE nat nat x1 (@UNIV nat))) -> (~ ((forall y0 : nat, ((x1 y0) = (x1 y0)) -> y0 = y0) /\ ((forall y0 : nat, forall y1 : nat, (((x1 y0) = (x1 y1)) -> y0 = y1) = (((x1 y1) = (x1 y0)) -> y1 = y0)) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> ((x1 y0) = (x1 y1)) -> y0 = y1)))) -> (forall y0 : nat, ~ (Peano.lt y0 y0)) -> False) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.lt (x1 y0) (x1 y1)) -> (x0 = (@IMAGE nat nat x1 (@UNIV nat))) -> (~ ((forall y0 : nat, ((x1 y0) = (x1 y0)) -> y0 = y0) /\ ((forall y0 : nat, forall y1 : nat, (((x1 y0) = (x1 y1)) -> y0 = y1) = (((x1 y1) = (x1 y0)) -> y1 = y0)) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> ((x1 y0) = (x1 y1)) -> y0 = y1)))) -> (forall y0 : nat, ~ (Peano.lt y0 y0)) -> False) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.lt (x1 y0) (x1 y1)) -> (x0 = (@IMAGE nat nat x1 (@UNIV nat))) -> (~ ((forall y0 : nat, ((x1 y0) = (x1 y0)) -> y0 = y0) /\ ((forall y0 : nat, forall y1 : nat, (((x1 y0) = (x1 y1)) -> y0 = y1) = (((x1 y1) = (x1 y0)) -> y1 = y0)) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> ((x1 y0) = (x1 y1)) -> y0 = y1)))) -> (forall y0 : nat, ~ (Peano.lt y0 y0)) -> False.
Definition term61 (x0 : nat -> nat) (x1 : nat) := fun y0 : nat => (((x0 x1) = (x0 y0)) -> x1 = y0) = (((x0 y0) = (x0 x1)) -> y0 = x1).
Definition term373 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2)).
Definition term330 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := (~ (Peano.lt x0 x2)) \/ (Peano.lt (@I (nat -> nat) x1 x0) (@I (nat -> nat) x1 x2)).
Definition term96 (x0 : nat -> Prop) (x1 : nat -> nat) := ((forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.lt (x1 y0) (x1 y1)) -> (x0 = (@IMAGE nat nat x1 (@UNIV nat))) -> (~ ((forall y0 : nat, ((x1 y0) = (x1 y0)) -> y0 = y0) /\ ((forall y0 : nat, forall y1 : nat, (((x1 y0) = (x1 y1)) -> y0 = y1) = (((x1 y1) = (x1 y0)) -> y1 = y0)) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> ((x1 y0) = (x1 y1)) -> y0 = y1)))) -> (forall y0 : nat, ~ (Peano.lt y0 y0)) -> False) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.lt (x1 y0) (x1 y1)) -> (x0 = (@IMAGE nat nat x1 (@UNIV nat))) -> (~ ((forall y0 : nat, ((x1 y0) = (x1 y0)) -> y0 = y0) /\ ((forall y0 : nat, forall y1 : nat, (((x1 y0) = (x1 y1)) -> y0 = y1) = (((x1 y1) = (x1 y0)) -> y1 = y0)) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> ((x1 y0) = (x1 y1)) -> y0 = y1)))) -> (forall y0 : nat, ~ (Peano.lt y0 y0)) -> False.
Definition term87 (x0 : nat -> nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => fun y2 : nat => ((x0 y1) = (x0 y2)) -> y1 = y2) x1 y0.
Definition term109 (x0 : nat -> Prop) (x1 : nat -> nat) := (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.lt (x1 y0) (x1 y1)) -> (x0 = (@IMAGE nat nat x1 (@UNIV nat))) -> (~ ((forall y0 : nat, ((x1 y0) = (x1 y0)) -> y0 = y0) /\ ((forall y0 : nat, forall y1 : nat, (((x1 y0) = (x1 y1)) -> y0 = y1) = (((x1 y1) = (x1 y0)) -> y1 = y0)) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> ((x1 y0) = (x1 y1)) -> y0 = y1)))) -> ~ (forall y0 : nat, ~ (Peano.lt y0 y0)).
Definition term13 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := (forall y0 : a0 -> a1, forall y1 : a0 -> Prop, ((@INFINITE a0 y1) /\ (forall y2 : a0, forall y3 : a0, ((@IN a0 y2 y1) /\ ((@IN a0 y3 y1) /\ ((y0 y2) = (y0 y3)))) -> y2 = y3)) -> @INFINITE a1 (@IMAGE a0 a1 y0 y1)) -> @INFINITE a1 (@IMAGE a0 a1 x0 x1).
Definition term425 (x0 : nat) (x1 : nat) := or (Peano.lt x0 x1).
Definition term106 (x0 : nat -> Prop) (x1 : nat -> nat) := (x0 = (@IMAGE nat nat x1 (@UNIV nat))) -> (~ ((forall y0 : nat, ((x1 y0) = (x1 y0)) -> y0 = y0) /\ ((forall y0 : nat, forall y1 : nat, (((x1 y0) = (x1 y1)) -> y0 = y1) = (((x1 y1) = (x1 y0)) -> y1 = y0)) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> ((x1 y0) = (x1 y1)) -> y0 = y1)))) -> (forall y0 : nat, ~ (Peano.lt y0 y0)) -> False.
Definition term220 (x0 : nat -> nat) (x1 : nat) := exists y0 : nat, (((x0 x1) = (x0 y0)) /\ (~ (x1 = y0))) /\ ((~ ((x0 y0) = (x0 x1))) \/ (y0 = x1)).
Definition term382 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term348 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := (((@I (nat -> nat) x0 x2) = (@I (nat -> nat) x0 x1)) /\ (~ (x2 = x1))) /\ ((~ ((@I (nat -> nat) x0 x1) = (@I (nat -> nat) x0 x2))) \/ (x1 = x2)).
Definition term147 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := (((x0 x2) = (x0 x1)) /\ (~ (x2 = x1))) /\ ((~ ((x0 x1) = (x0 x2))) \/ (x1 = x2)).
Definition term76 (x0 : nat -> nat) (x1 : nat) := forall y0 : nat, (Peano.lt x1 y0) -> ((x0 x1) = (x0 y0)) -> x1 = y0.
Definition term290 (x0 : nat -> nat) := (exists y0 : nat, (fun y1 : nat => ((x0 y1) = (x0 y1)) /\ (~ (y1 = y1))) y0) \/ (exists y0 : nat, (fun y1 : nat => exists y2 : nat, ((((~ ((x0 y1) = (x0 y2))) \/ (y1 = y2)) /\ (((x0 y2) = (x0 y1)) /\ (~ (y2 = y1)))) \/ ((((x0 y1) = (x0 y2)) /\ (~ (y1 = y2))) /\ ((~ ((x0 y2) = (x0 y1))) \/ (y2 = y1)))) \/ ((Peano.lt y1 y2) /\ (((x0 y1) = (x0 y2)) /\ (~ (y1 = y2))))) y0).
Definition term269 (x0 : nat -> nat) (x1 : nat) := (exists y0 : nat, (fun y1 : nat => (((~ ((x0 x1) = (x0 y1))) \/ (x1 = y1)) /\ (((x0 y1) = (x0 x1)) /\ (~ (y1 = x1)))) \/ ((((x0 x1) = (x0 y1)) /\ (~ (x1 = y1))) /\ ((~ ((x0 y1) = (x0 x1))) \/ (y1 = x1)))) y0) \/ (exists y0 : nat, (fun y1 : nat => (Peano.lt x1 y1) /\ (((x0 x1) = (x0 y1)) /\ (~ (x1 = y1)))) y0).
Definition term251 (x0 : nat -> nat) := (exists y0 : nat, (fun y1 : nat => exists y2 : nat, (((~ ((x0 y1) = (x0 y2))) \/ (y1 = y2)) /\ (((x0 y2) = (x0 y1)) /\ (~ (y2 = y1)))) \/ ((((x0 y1) = (x0 y2)) /\ (~ (y1 = y2))) /\ ((~ ((x0 y2) = (x0 y1))) \/ (y2 = y1)))) y0) \/ (exists y0 : nat, (fun y1 : nat => exists y2 : nat, (Peano.lt y1 y2) /\ (((x0 y1) = (x0 y2)) /\ (~ (y1 = y2)))) y0).
Definition term225 (x0 : nat -> nat) := (exists y0 : nat, (fun y1 : nat => exists y2 : nat, ((~ ((x0 y1) = (x0 y2))) \/ (y1 = y2)) /\ (((x0 y2) = (x0 y1)) /\ (~ (y2 = y1)))) y0) \/ (exists y0 : nat, (fun y1 : nat => exists y2 : nat, (((x0 y1) = (x0 y2)) /\ (~ (y1 = y2))) /\ ((~ ((x0 y2) = (x0 y1))) \/ (y2 = y1))) y0).
Definition term203 (x0 : nat -> nat) (x1 : nat) := (exists y0 : nat, (fun y1 : nat => ((~ ((x0 x1) = (x0 y1))) \/ (x1 = y1)) /\ (((x0 y1) = (x0 x1)) /\ (~ (y1 = x1)))) y0) \/ (exists y0 : nat, (fun y1 : nat => (((x0 x1) = (x0 y1)) /\ (~ (x1 = y1))) /\ ((~ ((x0 y1) = (x0 x1))) \/ (y1 = x1))) y0).
Definition term58 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := @eq Prop ((fun y0 : nat => fun y1 : nat => ((x0 y0) = (x0 y1)) -> y0 = y1) x1 x2).
Definition term302 (x0 : nat -> nat) (x1 : nat) := or (((x0 x1) = (x0 x1)) /\ (~ (x1 = x1))).
Definition term312 (x0 : nat -> nat) (x1 : nat) := (((x0 x1) = (x0 x1)) /\ (~ (x1 = x1))) \/ (exists y0 : nat, (fun y1 : nat => ((((~ ((x0 x1) = (x0 y1))) \/ (x1 = y1)) /\ (((x0 y1) = (x0 x1)) /\ (~ (y1 = x1)))) \/ ((((x0 x1) = (x0 y1)) /\ (~ (x1 = y1))) /\ ((~ ((x0 y1) = (x0 x1))) \/ (y1 = x1)))) \/ ((Peano.lt x1 y1) /\ (((x0 x1) = (x0 y1)) /\ (~ (x1 = y1))))) y0).
Definition term293 (x0 : nat -> nat) := fun y0 : nat => (fun y1 : nat => ((x0 y1) = (x0 y1)) /\ (~ (y1 = y1))) y0.
Definition term72 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := (Peano.lt x1 x2) -> ((x0 x1) = (x0 x2)) -> x1 = x2.
Definition term156 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := ~ ((((x0 x2) = (x0 x1)) -> x2 = x1) = (((x0 x1) = (x0 x2)) -> x1 = x2)).
Definition term419 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := (Peano.lt x0 x2) -> Peano.lt (@I (nat -> nat) x1 x0) (@I (nat -> nat) x1 x2).
Definition term107 (x0 : nat -> Prop) (x1 : nat -> nat) := (x0 = (@IMAGE nat nat x1 (@UNIV nat))) -> (~ ((forall y0 : nat, ((x1 y0) = (x1 y0)) -> y0 = y0) /\ ((forall y0 : nat, forall y1 : nat, (((x1 y0) = (x1 y1)) -> y0 = y1) = (((x1 y1) = (x1 y0)) -> y1 = y0)) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> ((x1 y0) = (x1 y1)) -> y0 = y1)))) -> ~ (forall y0 : nat, ~ (Peano.lt y0 y0)).
Definition term55 (x0 : nat -> nat) := and (forall y0 : nat, ((x0 y0) = (x0 y0)) -> y0 = y0).
Definition term74 (x0 : nat -> nat) (x1 : nat) := fun y0 : nat => (Peano.lt x1 y0) -> ((x0 x1) = (x0 y0)) -> x1 = y0.
Definition term43 (x0 : nat -> nat) := True /\ (forall y0 : nat, forall y1 : nat, ((x0 y0) = (x0 y1)) -> y0 = y1).
Definition term358 (x0 : nat -> nat) (x1 : nat) := ((@I (nat -> nat) x0 x1) = (@I (nat -> nat) x0 x1)) /\ (~ (x1 = x1)).
Definition term459 := forall y0 : nat -> Prop, (@INFINITE nat y0) = (exists y1 : nat -> nat, (forall y2 : nat, forall y3 : nat, (Peano.lt y2 y3) -> Peano.lt (y1 y2) (y1 y3)) /\ ((@IMAGE nat nat y1 (@UNIV nat)) = y0)).
Definition term339 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := and ((@I (nat -> nat) x1 x0) = (@I (nat -> nat) x1 x2)).
Definition term408 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x3 = x1)) \/ ((Peano.lt x0 x1) \/ (~ (Peano.lt x2 x3))).
Definition term84 (x0 : nat -> nat) := (forall y0 : nat, ((x0 y0) = (x0 y0)) -> y0 = y0) /\ ((forall y0 : nat, forall y1 : nat, (((x0 y0) = (x0 y1)) -> y0 = y1) = (((x0 y1) = (x0 y0)) -> y1 = y0)) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> ((x0 y0) = (x0 y1)) -> y0 = y1)).
Definition term5 (a0 : Type') (x0 : a0) := (fun y0 : a0 => @IN a0 y0 (@UNIV a0)) x0.
Definition term404 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Peano.lt x2 x3) = (Peano.lt x0 x1)) -> (Peano.lt x0 x1) \/ (~ (Peano.lt x2 x3)).
Definition term86 (x0 : nat -> nat) := imp ((forall y0 : nat, ((x0 y0) = (x0 y0)) -> y0 = y0) /\ ((forall y0 : nat, forall y1 : nat, (((x0 y0) = (x0 y1)) -> y0 = y1) = (((x0 y1) = (x0 y0)) -> y1 = y0)) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> ((x0 y0) = (x0 y1)) -> y0 = y1))).
Definition term85 (x0 : nat -> nat) := imp ((forall y0 : nat, (fun y1 : nat => fun y2 : nat => ((x0 y1) = (x0 y2)) -> y1 = y2) y0 y0) /\ ((forall y0 : nat, forall y1 : nat, ((fun y2 : nat => fun y3 : nat => ((x0 y2) = (x0 y3)) -> y2 = y3) y0 y1) = ((fun y2 : nat => fun y3 : nat => ((x0 y2) = (x0 y3)) -> y2 = y3) y1 y0)) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> (fun y2 : nat => fun y3 : nat => ((x0 y2) = (x0 y3)) -> y2 = y3) y0 y1))).
Definition term436 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ ((~ (x0 = x2)) \/ ((~ (x1 = x3)) \/ (~ (Peano.lt x0 x1))))) -> Peano.lt x2 x3.
Definition term271 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (((~ ((x0 x1) = (x0 y0))) \/ (x1 = y0)) /\ (((x0 y0) = (x0 x1)) /\ (~ (y0 = x1)))) \/ ((((x0 x1) = (x0 y0)) /\ (~ (x1 = y0))) /\ ((~ ((x0 y0) = (x0 x1))) \/ (y0 = x1)))) x2.
Definition term322 (x0 : nat -> nat) (x1 : nat) := fun y0 : nat => (((x0 x1) = (x0 x1)) /\ (~ (x1 = x1))) \/ (((((~ ((x0 x1) = (x0 y0))) \/ (x1 = y0)) /\ (((x0 y0) = (x0 x1)) /\ (~ (y0 = x1)))) \/ ((((x0 x1) = (x0 y0)) /\ (~ (x1 = y0))) /\ ((~ ((x0 y0) = (x0 x1))) \/ (y0 = x1)))) \/ ((Peano.lt x1 y0) /\ (((x0 x1) = (x0 y0)) /\ (~ (x1 = y0))))).
Definition term376 (x0 : nat -> nat) (x1 : nat) := ~ ((@I (nat -> nat) x0 x1) = (@I (nat -> nat) x0 x1)).
Definition term309 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 \/ (x1 y0).
Definition term126 (x0 : nat) (x1 : nat -> nat) := fun y0 : nat => (~ (Peano.lt x0 y0)) \/ (Peano.lt (x1 x0) (x1 y0)).
Definition term315 (x0 : nat -> nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => ((((~ ((x0 x1) = (x0 y1))) \/ (x1 = y1)) /\ (((x0 y1) = (x0 x1)) /\ (~ (y1 = x1)))) \/ ((((x0 x1) = (x0 y1)) /\ (~ (x1 = y1))) /\ ((~ ((x0 y1) = (x0 x1))) \/ (y1 = x1)))) \/ ((Peano.lt x1 y1) /\ (((x0 x1) = (x0 y1)) /\ (~ (x1 = y1))))) y0.
Definition term272 (x0 : nat -> nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => (((~ ((x0 x1) = (x0 y1))) \/ (x1 = y1)) /\ (((x0 y1) = (x0 x1)) /\ (~ (y1 = x1)))) \/ ((((x0 x1) = (x0 y1)) /\ (~ (x1 = y1))) /\ ((~ ((x0 y1) = (x0 x1))) \/ (y1 = x1)))) y0.
Definition term262 (x0 : nat -> nat) (x1 : nat) := or ((fun y0 : nat => exists y1 : nat, (((~ ((x0 y0) = (x0 y1))) \/ (y0 = y1)) /\ (((x0 y1) = (x0 y0)) /\ (~ (y1 = y0)))) \/ ((((x0 y0) = (x0 y1)) /\ (~ (y0 = y1))) /\ ((~ ((x0 y1) = (x0 y0))) \/ (y1 = y0)))) x1).
Definition term229 (x0 : nat -> nat) (x1 : nat) := or ((fun y0 : nat => exists y1 : nat, ((~ ((x0 y0) = (x0 y1))) \/ (y0 = y1)) /\ (((x0 y1) = (x0 y0)) /\ (~ (y1 = y0)))) x1).
Definition term450 (x0 : nat -> nat) (x1 : nat) := (~ (Peano.lt (@I (nat -> nat) x0 x1) (@I (nat -> nat) x0 x1))) -> Peano.lt (@I (nat -> nat) x0 x1) (@I (nat -> nat) x0 x1).
Definition term54 (x0 : nat -> nat) := and (forall y0 : nat, (fun y1 : nat => fun y2 : nat => ((x0 y1) = (x0 y2)) -> y1 = y2) y0 y0).
Definition term388 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term122 (x0 : nat) (x1 : nat -> nat) := forall y0 : nat, (Peano.lt x0 y0) -> Peano.lt (x1 x0) (x1 y0).
Definition term296 (x0 : nat -> nat) (x1 : nat) := (fun y0 : nat => exists y1 : nat, ((((~ ((x0 y0) = (x0 y1))) \/ (y0 = y1)) /\ (((x0 y1) = (x0 y0)) /\ (~ (y1 = y0)))) \/ ((((x0 y0) = (x0 y1)) /\ (~ (y0 = y1))) /\ ((~ ((x0 y1) = (x0 y0))) \/ (y1 = y0)))) \/ ((Peano.lt y0 y1) /\ (((x0 y0) = (x0 y1)) /\ (~ (y0 = y1))))) x1.
Definition term257 (x0 : nat -> nat) (x1 : nat) := (fun y0 : nat => exists y1 : nat, (Peano.lt y0 y1) /\ (((x0 y0) = (x0 y1)) /\ (~ (y0 = y1)))) x1.
Definition term253 (x0 : nat -> nat) (x1 : nat) := (fun y0 : nat => exists y1 : nat, (((~ ((x0 y0) = (x0 y1))) \/ (y0 = y1)) /\ (((x0 y1) = (x0 y0)) /\ (~ (y1 = y0)))) \/ ((((x0 y0) = (x0 y1)) /\ (~ (y0 = y1))) /\ ((~ ((x0 y1) = (x0 y0))) \/ (y1 = y0)))) x1.
Definition term230 (x0 : nat -> nat) (x1 : nat) := (fun y0 : nat => exists y1 : nat, (((x0 y0) = (x0 y1)) /\ (~ (y0 = y1))) /\ ((~ ((x0 y1) = (x0 y0))) \/ (y1 = y0))) x1.
Definition term228 (x0 : nat -> nat) (x1 : nat) := (fun y0 : nat => exists y1 : nat, ((~ ((x0 y0) = (x0 y1))) \/ (y0 = y1)) /\ (((x0 y1) = (x0 y0)) /\ (~ (y1 = y0)))) x1.
Definition term334 (x0 : nat -> nat) := forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) \/ (Peano.lt (@I (nat -> nat) x0 y0) (@I (nat -> nat) x0 y1)).
Definition term129 (x0 : nat -> nat) := forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) \/ (Peano.lt (x0 y0) (x0 y1)).
Definition term90 (x0 : nat -> nat) := forall y0 : nat, forall y1 : nat, (fun y2 : nat => fun y3 : nat => ((x0 y2) = (x0 y3)) -> y2 = y3) y0 y1.
Definition term80 (x0 : nat -> nat) := forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> ((x0 y0) = (x0 y1)) -> y0 = y1.
Definition term79 (x0 : nat -> nat) := forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> (fun y2 : nat => fun y3 : nat => ((x0 y2) = (x0 y3)) -> y2 = y3) y0 y1.
Definition term67 (x0 : nat -> nat) := forall y0 : nat, forall y1 : nat, (((x0 y0) = (x0 y1)) -> y0 = y1) = (((x0 y1) = (x0 y0)) -> y1 = y0).
Definition term66 (x0 : nat -> nat) := forall y0 : nat, forall y1 : nat, ((fun y2 : nat => fun y3 : nat => ((x0 y2) = (x0 y3)) -> y2 = y3) y0 y1) = ((fun y2 : nat => fun y3 : nat => ((x0 y2) = (x0 y3)) -> y2 = y3) y1 y0).
Definition term41 (x0 : nat -> nat) := forall y0 : nat, forall y1 : nat, ((x0 y0) = (x0 y1)) -> y0 = y1.
Definition term40 (x0 : nat -> nat) := forall y0 : nat, forall y1 : nat, ((@IN nat y0 (@UNIV nat)) /\ ((@IN nat y1 (@UNIV nat)) /\ ((x0 y0) = (x0 y1)))) -> y0 = y1.
Definition term21 (x0 : nat -> nat) := forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.lt (x0 y0) (x0 y1).
Definition term2 (x0 : type1605) := forall y0 : nat, forall y1 : nat, x0 y0 y1.
Definition term150 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := (((x0 x2) = (x0 x1)) -> x2 = x1) /\ (~ (((x0 x1) = (x0 x2)) -> x1 = x2)).
Definition term111 (x0 : nat -> nat) := fun y0 : nat -> Prop => (forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> Peano.lt (x0 y1) (x0 y2)) -> (y0 = (@IMAGE nat nat x0 (@UNIV nat))) -> (~ ((forall y1 : nat, ((x0 y1) = (x0 y1)) -> y1 = y1) /\ ((forall y1 : nat, forall y2 : nat, (((x0 y1) = (x0 y2)) -> y1 = y2) = (((x0 y2) = (x0 y1)) -> y2 = y1)) /\ (forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> ((x0 y1) = (x0 y2)) -> y1 = y2)))) -> ~ (forall y1 : nat, ~ (Peano.lt y1 y1)).
Definition term308 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 \/ (exists y0 : a0, x1 y0).
Definition term121 (x0 : nat) (x1 : nat -> nat) := fun y0 : nat => (Peano.lt x0 y0) -> Peano.lt (x1 x0) (x1 y0).
Definition term178 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := ~ ((fun y0 : nat => (Peano.lt x1 y0) -> ((x0 x1) = (x0 y0)) -> x1 = y0) x2).
Definition term160 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := ~ ((fun y0 : nat => (((x0 x1) = (x0 y0)) -> x1 = y0) = (((x0 y0) = (x0 x1)) -> y0 = x1)) x2).
Definition term313 (x0 : nat -> nat) (x1 : nat) := exists y0 : nat, (((x0 x1) = (x0 x1)) /\ (~ (x1 = x1))) \/ ((fun y1 : nat => ((((~ ((x0 x1) = (x0 y1))) \/ (x1 = y1)) /\ (((x0 y1) = (x0 x1)) /\ (~ (y1 = x1)))) \/ ((((x0 x1) = (x0 y1)) /\ (~ (x1 = y1))) /\ ((~ ((x0 y1) = (x0 x1))) \/ (y1 = x1)))) \/ ((Peano.lt x1 y1) /\ (((x0 x1) = (x0 y1)) /\ (~ (x1 = y1))))) y0).
Definition term268 (x0 : nat -> nat) := exists y0 : nat, (exists y1 : nat, (((~ ((x0 y0) = (x0 y1))) \/ (y0 = y1)) /\ (((x0 y1) = (x0 y0)) /\ (~ (y1 = y0)))) \/ ((((x0 y0) = (x0 y1)) /\ (~ (y0 = y1))) /\ ((~ ((x0 y1) = (x0 y0))) \/ (y1 = y0)))) \/ (exists y1 : nat, (Peano.lt y0 y1) /\ (((x0 y0) = (x0 y1)) /\ (~ (y0 = y1)))).
Definition term223 (x0 : nat -> nat) := exists y0 : nat, (exists y1 : nat, ((~ ((x0 y0) = (x0 y1))) \/ (y0 = y1)) /\ (((x0 y1) = (x0 y0)) /\ (~ (y1 = y0)))) \/ (exists y1 : nat, (((x0 y0) = (x0 y1)) /\ (~ (y0 = y1))) /\ ((~ ((x0 y1) = (x0 y0))) \/ (y1 = y0))).
Definition term289 (x0 : nat -> nat) := (exists y0 : nat, ((x0 y0) = (x0 y0)) /\ (~ (y0 = y0))) \/ (exists y0 : nat, exists y1 : nat, ((((~ ((x0 y0) = (x0 y1))) \/ (y0 = y1)) /\ (((x0 y1) = (x0 y0)) /\ (~ (y1 = y0)))) \/ ((((x0 y0) = (x0 y1)) /\ (~ (y0 = y1))) /\ ((~ ((x0 y1) = (x0 y0))) \/ (y1 = y0)))) \/ ((Peano.lt y0 y1) /\ (((x0 y0) = (x0 y1)) /\ (~ (y0 = y1))))).
Definition term291 (x0 : nat -> nat) := exists y0 : nat, ((fun y1 : nat => ((x0 y1) = (x0 y1)) /\ (~ (y1 = y1))) y0) \/ ((fun y1 : nat => exists y2 : nat, ((((~ ((x0 y1) = (x0 y2))) \/ (y1 = y2)) /\ (((x0 y2) = (x0 y1)) /\ (~ (y2 = y1)))) \/ ((((x0 y1) = (x0 y2)) /\ (~ (y1 = y2))) /\ ((~ ((x0 y2) = (x0 y1))) \/ (y2 = y1)))) \/ ((Peano.lt y1 y2) /\ (((x0 y1) = (x0 y2)) /\ (~ (y1 = y2))))) y0).
Definition term270 (x0 : nat -> nat) (x1 : nat) := exists y0 : nat, ((fun y1 : nat => (((~ ((x0 x1) = (x0 y1))) \/ (x1 = y1)) /\ (((x0 y1) = (x0 x1)) /\ (~ (y1 = x1)))) \/ ((((x0 x1) = (x0 y1)) /\ (~ (x1 = y1))) /\ ((~ ((x0 y1) = (x0 x1))) \/ (y1 = x1)))) y0) \/ ((fun y1 : nat => (Peano.lt x1 y1) /\ (((x0 x1) = (x0 y1)) /\ (~ (x1 = y1)))) y0).
Definition term252 (x0 : nat -> nat) := exists y0 : nat, ((fun y1 : nat => exists y2 : nat, (((~ ((x0 y1) = (x0 y2))) \/ (y1 = y2)) /\ (((x0 y2) = (x0 y1)) /\ (~ (y2 = y1)))) \/ ((((x0 y1) = (x0 y2)) /\ (~ (y1 = y2))) /\ ((~ ((x0 y2) = (x0 y1))) \/ (y2 = y1)))) y0) \/ ((fun y1 : nat => exists y2 : nat, (Peano.lt y1 y2) /\ (((x0 y1) = (x0 y2)) /\ (~ (y1 = y2)))) y0).
Definition term224 (x0 : nat -> nat) := exists y0 : nat, ((fun y1 : nat => exists y2 : nat, ((~ ((x0 y1) = (x0 y2))) \/ (y1 = y2)) /\ (((x0 y2) = (x0 y1)) /\ (~ (y2 = y1)))) y0) \/ ((fun y1 : nat => exists y2 : nat, (((x0 y1) = (x0 y2)) /\ (~ (y1 = y2))) /\ ((~ ((x0 y2) = (x0 y1))) \/ (y2 = y1))) y0).
Definition term202 (x0 : nat -> nat) (x1 : nat) := exists y0 : nat, ((fun y1 : nat => ((~ ((x0 x1) = (x0 y1))) \/ (x1 = y1)) /\ (((x0 y1) = (x0 x1)) /\ (~ (y1 = x1)))) y0) \/ ((fun y1 : nat => (((x0 x1) = (x0 y1)) /\ (~ (x1 = y1))) /\ ((~ ((x0 y1) = (x0 x1))) \/ (y1 = x1))) y0).
Definition term20 (x0 : nat -> Prop) (x1 : nat -> nat) := (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.lt (x1 y0) (x1 y1)) /\ (x0 = (@IMAGE nat nat x1 (@UNIV nat))).
Definition term414 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := @eq Prop ((~ (Peano.lt x0 x2)) \/ (Peano.lt (@I (nat -> nat) x1 x0) (@I (nat -> nat) x1 x2))).
Definition term50 (x0 : nat -> nat) := fun y0 : nat => (fun y1 : nat => fun y2 : nat => ((x0 y1) = (x0 y2)) -> y1 = y2) y0 y0.
Definition term25 := and (@INFINITE nat (@UNIV nat)).
Definition term143 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := (~ ((x0 x1) = (x0 x2))) \/ (x1 = x2).
Definition term102 (x0 : nat -> nat) := imp (~ ((forall y0 : nat, ((x0 y0) = (x0 y0)) -> y0 = y0) /\ ((forall y0 : nat, forall y1 : nat, (((x0 y0) = (x0 y1)) -> y0 = y1) = (((x0 y1) = (x0 y0)) -> y1 = y0)) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> ((x0 y0) = (x0 y1)) -> y0 = y1)))).
Definition term448 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := (((@I (nat -> nat) x1 x0) = (@I (nat -> nat) x1 x2)) /\ (((@I (nat -> nat) x1 x2) = (@I (nat -> nat) x1 x2)) /\ (Peano.lt (@I (nat -> nat) x1 x0) (@I (nat -> nat) x1 x2)))) -> Peano.lt (@I (nat -> nat) x1 x2) (@I (nat -> nat) x1 x2).
Definition term110 (x0 : nat -> nat) := fun y0 : nat -> Prop => (forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> Peano.lt (x0 y1) (x0 y2)) -> (y0 = (@IMAGE nat nat x0 (@UNIV nat))) -> (~ ((forall y1 : nat, ((x0 y1) = (x0 y1)) -> y1 = y1) /\ ((forall y1 : nat, forall y2 : nat, (((x0 y1) = (x0 y2)) -> y1 = y2) = (((x0 y2) = (x0 y1)) -> y2 = y1)) /\ (forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> ((x0 y1) = (x0 y2)) -> y1 = y2)))) -> (forall y1 : nat, ~ (Peano.lt y1 y1)) -> False.
Definition term245 (x0 : nat -> nat) := ((exists y0 : nat, exists y1 : nat, ((~ ((x0 y0) = (x0 y1))) \/ (y0 = y1)) /\ (((x0 y1) = (x0 y0)) /\ (~ (y1 = y0)))) \/ (exists y0 : nat, exists y1 : nat, (((x0 y0) = (x0 y1)) /\ (~ (y0 = y1))) /\ ((~ ((x0 y1) = (x0 y0))) \/ (y1 = y0)))) \/ (exists y0 : nat, exists y1 : nat, (Peano.lt y0 y1) /\ (((x0 y0) = (x0 y1)) /\ (~ (y0 = y1)))).
Definition term23 (x0 : nat -> nat) (x1 : nat -> Prop) := ((@INFINITE nat x1) /\ (forall y0 : nat, forall y1 : nat, ((@IN nat y0 x1) /\ ((@IN nat y1 x1) /\ ((x0 y0) = (x0 y1)))) -> y0 = y1)) -> @INFINITE nat (@IMAGE nat nat x0 x1).
Definition term10 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := ((@INFINITE a0 x1) /\ (forall y0 : a0, forall y1 : a0, ((@IN a0 y0 x1) /\ ((@IN a0 y1 x1) /\ ((x0 y0) = (x0 y1)))) -> y0 = y1)) -> @INFINITE a1 (@IMAGE a0 a1 x0 x1).
Definition term409 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x2 = x0) -> (~ (x3 = x1)) \/ ((Peano.lt x0 x1) \/ (~ (Peano.lt x2 x3))).
Definition term378 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = x2) \/ (~ (x1 = x2)).
Definition term32 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := ((@IN nat x1 (@UNIV nat)) /\ ((@IN nat x2 (@UNIV nat)) /\ ((x0 x1) = (x0 x2)))) -> x1 = x2.
Definition term437 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ~ ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (Peano.lt x2 x3)))).
Definition term118 (x0 : nat) := ~ (Peano.lt x0 x0).
Definition term264 (x0 : nat -> nat) (x1 : nat) := ((fun y0 : nat => exists y1 : nat, (((~ ((x0 y0) = (x0 y1))) \/ (y0 = y1)) /\ (((x0 y1) = (x0 y0)) /\ (~ (y1 = y0)))) \/ ((((x0 y0) = (x0 y1)) /\ (~ (y0 = y1))) /\ ((~ ((x0 y1) = (x0 y0))) \/ (y1 = y0)))) x1) \/ ((fun y0 : nat => exists y1 : nat, (Peano.lt y0 y1) /\ (((x0 y0) = (x0 y1)) /\ (~ (y0 = y1)))) x1).
Definition term231 (x0 : nat -> nat) (x1 : nat) := ((fun y0 : nat => exists y1 : nat, ((~ ((x0 y0) = (x0 y1))) \/ (y0 = y1)) /\ (((x0 y1) = (x0 y0)) /\ (~ (y1 = y0)))) x1) \/ ((fun y0 : nat => exists y1 : nat, (((x0 y0) = (x0 y1)) /\ (~ (y0 = y1))) /\ ((~ ((x0 y1) = (x0 y0))) \/ (y1 = y0))) x1).
Definition term350 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := ((~ ((@I (nat -> nat) x0 x2) = (@I (nat -> nat) x0 x1))) \/ (x2 = x1)) /\ (((@I (nat -> nat) x0 x1) = (@I (nat -> nat) x0 x2)) /\ (~ (x1 = x2))).
Definition term63 (x0 : nat -> nat) (x1 : nat) := forall y0 : nat, (((x0 x1) = (x0 y0)) -> x1 = y0) = (((x0 y0) = (x0 x1)) -> y0 = x1).
Definition term352 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := (((~ ((@I (nat -> nat) x0 x2) = (@I (nat -> nat) x0 x1))) \/ (x2 = x1)) /\ (((@I (nat -> nat) x0 x1) = (@I (nat -> nat) x0 x2)) /\ (~ (x1 = x2)))) \/ ((((@I (nat -> nat) x0 x2) = (@I (nat -> nat) x0 x1)) /\ (~ (x2 = x1))) /\ ((~ ((@I (nat -> nat) x0 x1) = (@I (nat -> nat) x0 x2))) \/ (x1 = x2))).
Definition term155 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := (((~ ((x0 x2) = (x0 x1))) \/ (x2 = x1)) /\ (((x0 x1) = (x0 x2)) /\ (~ (x1 = x2)))) \/ ((((x0 x2) = (x0 x1)) /\ (~ (x2 = x1))) /\ ((~ ((x0 x1) = (x0 x2))) \/ (x1 = x2))).
Definition term426 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.lt x0 x3) \/ ((~ (Peano.lt x1 x2)) \/ (~ (x2 = x3))).
Definition term239 (x0 : nat -> nat) := or (exists y0 : nat, exists y1 : nat, ((~ ((x0 y0) = (x0 y1))) \/ (y0 = y1)) /\ (((x0 y1) = (x0 y0)) /\ (~ (y1 = y0)))).
Definition term190 (x0 : nat -> nat) := or (exists y0 : nat, exists y1 : nat, (((~ ((x0 y0) = (x0 y1))) \/ (y0 = y1)) /\ (((x0 y1) = (x0 y0)) /\ (~ (y1 = y0)))) \/ ((((x0 y0) = (x0 y1)) /\ (~ (y0 = y1))) /\ ((~ ((x0 y1) = (x0 y0))) \/ (y1 = y0)))).
Definition term94 (x0 : nat -> nat) := ~ ((forall y0 : nat, ((x0 y0) = (x0 y0)) -> y0 = y0) /\ ((forall y0 : nat, forall y1 : nat, (((x0 y0) = (x0 y1)) -> y0 = y1) = (((x0 y1) = (x0 y0)) -> y1 = y0)) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> ((x0 y0) = (x0 y1)) -> y0 = y1))).
Definition term101 := forall y0 : nat, ~ (Peano.lt y0 y0).
Definition term186 (x0 : nat -> nat) := fun y0 : nat => ~ ((fun y1 : nat => forall y2 : nat, (Peano.lt y1 y2) -> ((x0 y1) = (x0 y2)) -> y1 = y2) y0).
Definition term168 (x0 : nat -> nat) := fun y0 : nat => ~ ((fun y1 : nat => forall y2 : nat, (((x0 y1) = (x0 y2)) -> y1 = y2) = (((x0 y2) = (x0 y1)) -> y2 = y1)) y0).
Definition term406 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x3 = x1) -> (Peano.lt x0 x1) \/ (~ (Peano.lt x2 x3)).
Definition term144 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := and (~ (((x0 x1) = (x0 x2)) -> x1 = x2)).
Definition term152 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := or ((((x0 x2) = (x0 x1)) -> x2 = x1) /\ (~ (((x0 x1) = (x0 x2)) -> x1 = x2))).
Definition term154 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := ((((x0 x2) = (x0 x1)) -> x2 = x1) /\ (~ (((x0 x1) = (x0 x2)) -> x1 = x2))) \/ ((~ (((x0 x2) = (x0 x1)) -> x2 = x1)) /\ (((x0 x1) = (x0 x2)) -> x1 = x2)).
Definition term88 (x0 : nat -> nat) (x1 : nat) := forall y0 : nat, (fun y1 : nat => fun y2 : nat => ((x0 y1) = (x0 y2)) -> y1 = y2) x1 y0.
Definition term380 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x1 = x0)) \/ ((x0 = x2) \/ (~ (x1 = x2))).
Definition term316 (x0 : nat -> nat) (x1 : nat) := exists y0 : nat, (fun y1 : nat => ((((~ ((x0 x1) = (x0 y1))) \/ (x1 = y1)) /\ (((x0 y1) = (x0 x1)) /\ (~ (y1 = x1)))) \/ ((((x0 x1) = (x0 y1)) /\ (~ (x1 = y1))) /\ ((~ ((x0 y1) = (x0 x1))) \/ (y1 = x1)))) \/ ((Peano.lt x1 y1) /\ (((x0 x1) = (x0 y1)) /\ (~ (x1 = y1))))) y0.
Definition term294 (x0 : nat -> nat) := exists y0 : nat, (fun y1 : nat => ((x0 y1) = (x0 y1)) /\ (~ (y1 = y1))) y0.
Definition term277 (x0 : nat -> nat) (x1 : nat) := exists y0 : nat, (fun y1 : nat => (Peano.lt x1 y1) /\ (((x0 x1) = (x0 y1)) /\ (~ (x1 = y1)))) y0.
Definition term273 (x0 : nat -> nat) (x1 : nat) := exists y0 : nat, (fun y1 : nat => (((~ ((x0 x1) = (x0 y1))) \/ (x1 = y1)) /\ (((x0 y1) = (x0 x1)) /\ (~ (y1 = x1)))) \/ ((((x0 x1) = (x0 y1)) /\ (~ (x1 = y1))) /\ ((~ ((x0 y1) = (x0 x1))) \/ (y1 = x1)))) y0.
Definition term219 (x0 : nat -> nat) (x1 : nat) := exists y0 : nat, (fun y1 : nat => (((x0 x1) = (x0 y1)) /\ (~ (x1 = y1))) /\ ((~ ((x0 y1) = (x0 x1))) \/ (y1 = x1))) y0.
Definition term214 (x0 : nat -> nat) (x1 : nat) := exists y0 : nat, (fun y1 : nat => ((~ ((x0 x1) = (x0 y1))) \/ (x1 = y1)) /\ (((x0 y1) = (x0 x1)) /\ (~ (y1 = x1)))) y0.
Definition term89 (x0 : nat -> nat) := fun y0 : nat => forall y1 : nat, (fun y2 : nat => fun y3 : nat => ((x0 y2) = (x0 y3)) -> y2 = y3) y0 y1.
Definition term70 (x0 : nat) (x1 : nat) := imp (Peano.lt x0 x1).
Definition term303 (x0 : nat -> nat) (x1 : nat) := ((fun y0 : nat => ((x0 y0) = (x0 y0)) /\ (~ (y0 = y0))) x1) \/ ((fun y0 : nat => exists y1 : nat, ((((~ ((x0 y0) = (x0 y1))) \/ (y0 = y1)) /\ (((x0 y1) = (x0 y0)) /\ (~ (y1 = y0)))) \/ ((((x0 y0) = (x0 y1)) /\ (~ (y0 = y1))) /\ ((~ ((x0 y1) = (x0 y0))) \/ (y1 = y0)))) \/ ((Peano.lt y0 y1) /\ (((x0 y0) = (x0 y1)) /\ (~ (y0 = y1))))) x1).
Definition term99 := (forall y0 : nat, ~ (Peano.lt y0 y0)) -> False.
Definition term119 := fun y0 : nat => ~ (Peano.lt y0 y0).
Definition term193 (x0 : nat -> nat) := ~ ((forall y0 : nat, forall y1 : nat, (((x0 y0) = (x0 y1)) -> y0 = y1) = (((x0 y1) = (x0 y0)) -> y1 = y0)) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> ((x0 y0) = (x0 y1)) -> y0 = y1)).
Definition term4 (x0 : type1605) := (((forall y0 : nat, x0 y0 y0) /\ ((forall y0 : nat, forall y1 : nat, (x0 y0 y1) = (x0 y1 y0)) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x0 y0 y1))) -> forall y0 : nat, forall y1 : nat, x0 y0 y1) -> ((forall y0 : nat, x0 y0 y0) /\ ((forall y0 : nat, forall y1 : nat, (x0 y0 y1) = (x0 y1 y0)) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x0 y0 y1))) -> forall y0 : nat, forall y1 : nat, x0 y0 y1.
Definition term171 (x0 : nat) (x1 : nat) := and (Peano.lt x0 x1).
Definition term394 (x0 : nat) (x1 : nat) := and (~ (~ (x0 = x1))).
Definition term83 (x0 : nat -> nat) := (forall y0 : nat, (fun y1 : nat => fun y2 : nat => ((x0 y1) = (x0 y2)) -> y1 = y2) y0 y0) /\ ((forall y0 : nat, forall y1 : nat, ((fun y2 : nat => fun y3 : nat => ((x0 y2) = (x0 y3)) -> y2 = y3) y0 y1) = ((fun y2 : nat => fun y3 : nat => ((x0 y2) = (x0 y3)) -> y2 = y3) y1 y0)) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> (fun y2 : nat => fun y3 : nat => ((x0 y2) = (x0 y3)) -> y2 = y3) y0 y1)).
Definition term1 (x0 : type1605) := (forall y0 : nat, x0 y0 y0) /\ ((forall y0 : nat, forall y1 : nat, (x0 y0 y1) = (x0 y1 y0)) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x0 y0 y1)).
Definition term415 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := @eq Prop ((Peano.lt (@I (nat -> nat) x0 x1) (@I (nat -> nat) x0 x2)) \/ (~ (Peano.lt x1 x2))).
Definition term53 (x0 : nat -> nat) := forall y0 : nat, ((x0 y0) = (x0 y0)) -> y0 = y0.
Definition term37 (x0 : nat -> nat) (x1 : nat) := forall y0 : nat, ((x0 x1) = (x0 y0)) -> x1 = y0.
Definition term36 (x0 : nat -> nat) (x1 : nat) := forall y0 : nat, ((@IN nat x1 (@UNIV nat)) /\ ((@IN nat y0 (@UNIV nat)) /\ ((x0 x1) = (x0 y0)))) -> x1 = y0.
Definition term47 (x0 : nat -> nat) (x1 : nat) := (fun y0 : nat => fun y1 : nat => ((x0 y0) = (x0 y1)) -> y0 = y1) x1 x1.
Definition term6 (a0 : Type') (a1 : Type') := forall y0 : a0 -> a1, forall y1 : a0 -> Prop, ((@INFINITE a0 y1) /\ (forall y2 : a0, forall y3 : a0, ((@IN a0 y2 y1) /\ ((@IN a0 y3 y1) /\ ((y0 y2) = (y0 y3)))) -> y2 = y3)) -> @INFINITE a1 (@IMAGE a0 a1 y0 y1).
Definition term98 (x0 : nat -> Prop) (x1 : nat -> nat) := (((forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.lt (x1 y0) (x1 y1)) -> (x0 = (@IMAGE nat nat x1 (@UNIV nat))) -> (~ ((forall y0 : nat, ((x1 y0) = (x1 y0)) -> y0 = y0) /\ ((forall y0 : nat, forall y1 : nat, (((x1 y0) = (x1 y1)) -> y0 = y1) = (((x1 y1) = (x1 y0)) -> y1 = y0)) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> ((x1 y0) = (x1 y1)) -> y0 = y1)))) -> (forall y0 : nat, ~ (Peano.lt y0 y0)) -> False) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.lt (x1 y0) (x1 y1)) -> (x0 = (@IMAGE nat nat x1 (@UNIV nat))) -> (~ ((forall y0 : nat, ((x1 y0) = (x1 y0)) -> y0 = y0) /\ ((forall y0 : nat, forall y1 : nat, (((x1 y0) = (x1 y1)) -> y0 = y1) = (((x1 y1) = (x1 y0)) -> y1 = y0)) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> ((x1 y0) = (x1 y1)) -> y0 = y1)))) -> (forall y0 : nat, ~ (Peano.lt y0 y0)) -> False) -> ((forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.lt (x1 y0) (x1 y1)) -> (x0 = (@IMAGE nat nat x1 (@UNIV nat))) -> (~ ((forall y0 : nat, ((x1 y0) = (x1 y0)) -> y0 = y0) /\ ((forall y0 : nat, forall y1 : nat, (((x1 y0) = (x1 y1)) -> y0 = y1) = (((x1 y1) = (x1 y0)) -> y1 = y0)) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> ((x1 y0) = (x1 y1)) -> y0 = y1)))) -> (forall y0 : nat, ~ (Peano.lt y0 y0)) -> False) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.lt (x1 y0) (x1 y1)) -> (x0 = (@IMAGE nat nat x1 (@UNIV nat))) -> (~ ((forall y0 : nat, ((x1 y0) = (x1 y0)) -> y0 = y0) /\ ((forall y0 : nat, forall y1 : nat, (((x1 y0) = (x1 y1)) -> y0 = y1) = (((x1 y1) = (x1 y0)) -> y1 = y0)) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> ((x1 y0) = (x1 y1)) -> y0 = y1)))) -> (forall y0 : nat, ~ (Peano.lt y0 y0)) -> False.
Definition term28 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := True /\ ((x1 x0) = (x1 x2)).
Definition term435 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.lt x0 x1) \/ ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (Peano.lt x2 x3)))).
Definition term27 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := (@IN nat x2 (@UNIV nat)) /\ ((x1 x0) = (x1 x2)).
Definition term22 (x0 : nat -> nat) := @INFINITE nat (@IMAGE nat nat x0 (@UNIV nat)).
Definition term267 (x0 : nat -> nat) := fun y0 : nat => (exists y1 : nat, (((~ ((x0 y0) = (x0 y1))) \/ (y0 = y1)) /\ (((x0 y1) = (x0 y0)) /\ (~ (y1 = y0)))) \/ ((((x0 y0) = (x0 y1)) /\ (~ (y0 = y1))) /\ ((~ ((x0 y1) = (x0 y0))) \/ (y1 = y0)))) \/ (exists y1 : nat, (Peano.lt y0 y1) /\ (((x0 y0) = (x0 y1)) /\ (~ (y0 = y1)))).
Definition term222 (x0 : nat -> nat) := fun y0 : nat => (exists y1 : nat, ((~ ((x0 y0) = (x0 y1))) \/ (y0 = y1)) /\ (((x0 y1) = (x0 y0)) /\ (~ (y1 = y0)))) \/ (exists y1 : nat, (((x0 y0) = (x0 y1)) /\ (~ (y0 = y1))) /\ ((~ ((x0 y1) = (x0 y0))) \/ (y1 = y0))).
Definition term403 (x0 : Prop) (x1 : Prop) := (x1 = x0) -> x0 \/ (~ x1).
Definition term416 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := (~ (~ (Peano.lt x0 x2))) -> Peano.lt (@I (nat -> nat) x1 x0) (@I (nat -> nat) x1 x2).
Definition term204 (x0 : nat -> nat) (x1 : nat) := fun y0 : nat => ((~ ((x0 x1) = (x0 y0))) \/ (x1 = y0)) /\ (((x0 y0) = (x0 x1)) /\ (~ (y0 = x1))).
Definition term367 (x0 : nat) (x1 : nat) := @eq Prop ((fun y0 : nat => ~ (x0 = y0)) x1).
Definition term69 (x0 : nat -> nat) := and (forall y0 : nat, forall y1 : nat, (((x0 y0) = (x0 y1)) -> y0 = y1) = (((x0 y1) = (x0 y0)) -> y1 = y0)).
Definition term68 (x0 : nat -> nat) := and (forall y0 : nat, forall y1 : nat, ((fun y2 : nat => fun y3 : nat => ((x0 y2) = (x0 y3)) -> y2 = y3) y0 y1) = ((fun y2 : nat => fun y3 : nat => ((x0 y2) = (x0 y3)) -> y2 = y3) y1 y0)).
Definition term19 (x0 : nat -> nat) := and (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.lt (x0 y0) (x0 y1)).
Definition term305 (x0 : nat -> nat) := fun y0 : nat => ((fun y1 : nat => ((x0 y1) = (x0 y1)) /\ (~ (y1 = y1))) y0) \/ ((fun y1 : nat => exists y2 : nat, ((((~ ((x0 y1) = (x0 y2))) \/ (y1 = y2)) /\ (((x0 y2) = (x0 y1)) /\ (~ (y2 = y1)))) \/ ((((x0 y1) = (x0 y2)) /\ (~ (y1 = y2))) /\ ((~ ((x0 y2) = (x0 y1))) \/ (y2 = y1)))) \/ ((Peano.lt y1 y2) /\ (((x0 y1) = (x0 y2)) /\ (~ (y1 = y2))))) y0).
Definition term266 (x0 : nat -> nat) := fun y0 : nat => ((fun y1 : nat => exists y2 : nat, (((~ ((x0 y1) = (x0 y2))) \/ (y1 = y2)) /\ (((x0 y2) = (x0 y1)) /\ (~ (y2 = y1)))) \/ ((((x0 y1) = (x0 y2)) /\ (~ (y1 = y2))) /\ ((~ ((x0 y2) = (x0 y1))) \/ (y2 = y1)))) y0) \/ ((fun y1 : nat => exists y2 : nat, (Peano.lt y1 y2) /\ (((x0 y1) = (x0 y2)) /\ (~ (y1 = y2)))) y0).
Definition term232 (x0 : nat -> nat) := fun y0 : nat => ((fun y1 : nat => exists y2 : nat, ((~ ((x0 y1) = (x0 y2))) \/ (y1 = y2)) /\ (((x0 y2) = (x0 y1)) /\ (~ (y2 = y1)))) y0) \/ ((fun y1 : nat => exists y2 : nat, (((x0 y1) = (x0 y2)) /\ (~ (y1 = y2))) /\ ((~ ((x0 y2) = (x0 y1))) \/ (y2 = y1))) y0).
Definition term421 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := ~ (Peano.lt (@I (nat -> nat) x1 x0) (@I (nat -> nat) x1 x2)).
Definition term412 (x0 : nat) (x1 : nat) := ~ (Peano.lt x0 x1).
Definition term357 (x0 : nat -> nat) (x1 : nat) := and ((@I (nat -> nat) x0 x1) = (@I (nat -> nat) x0 x1)).
Definition term117 := forall y0 : nat -> nat, forall y1 : nat -> Prop, (forall y2 : nat, forall y3 : nat, (Peano.lt y2 y3) -> Peano.lt (y0 y2) (y0 y3)) -> (y1 = (@IMAGE nat nat y0 (@UNIV nat))) -> (~ ((forall y2 : nat, ((y0 y2) = (y0 y2)) -> y2 = y2) /\ ((forall y2 : nat, forall y3 : nat, (((y0 y2) = (y0 y3)) -> y2 = y3) = (((y0 y3) = (y0 y2)) -> y3 = y2)) /\ (forall y2 : nat, forall y3 : nat, (Peano.lt y2 y3) -> ((y0 y2) = (y0 y3)) -> y2 = y3)))) -> ~ (forall y2 : nat, ~ (Peano.lt y2 y2)).
Definition term116 := forall y0 : nat -> nat, forall y1 : nat -> Prop, (forall y2 : nat, forall y3 : nat, (Peano.lt y2 y3) -> Peano.lt (y0 y2) (y0 y3)) -> (y1 = (@IMAGE nat nat y0 (@UNIV nat))) -> (~ ((forall y2 : nat, ((y0 y2) = (y0 y2)) -> y2 = y2) /\ ((forall y2 : nat, forall y3 : nat, (((y0 y2) = (y0 y3)) -> y2 = y3) = (((y0 y3) = (y0 y2)) -> y3 = y2)) /\ (forall y2 : nat, forall y3 : nat, (Peano.lt y2 y3) -> ((y0 y2) = (y0 y3)) -> y2 = y3)))) -> (forall y2 : nat, ~ (Peano.lt y2 y2)) -> False.
Definition term120 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := (Peano.lt x0 x2) -> Peano.lt (x1 x0) (x1 x2).
Definition term215 (x0 : nat -> nat) (x1 : nat) := exists y0 : nat, ((~ ((x0 x1) = (x0 y0))) \/ (x1 = y0)) /\ (((x0 y0) = (x0 x1)) /\ (~ (y0 = x1))).
Definition term328 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := Peano.lt (@I (nat -> nat) x1 x0) (@I (nat -> nat) x1 x2).
Definition term148 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := and (((x0 x1) = (x0 x2)) -> x1 = x2).
Definition term275 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.lt x1 y0) /\ (((x0 x1) = (x0 y0)) /\ (~ (x1 = y0)))) x2.
Definition term307 (x0 : nat -> nat) := exists y0 : nat, (((x0 y0) = (x0 y0)) /\ (~ (y0 = y0))) \/ (exists y1 : nat, ((((~ ((x0 y0) = (x0 y1))) \/ (y0 = y1)) /\ (((x0 y1) = (x0 y0)) /\ (~ (y1 = y0)))) \/ ((((x0 y0) = (x0 y1)) /\ (~ (y0 = y1))) /\ ((~ ((x0 y1) = (x0 y0))) \/ (y1 = y0)))) \/ ((Peano.lt y0 y1) /\ (((x0 y0) = (x0 y1)) /\ (~ (y0 = y1))))).
Definition term332 (x0 : nat) (x1 : nat -> nat) := forall y0 : nat, (~ (Peano.lt x0 y0)) \/ (Peano.lt (@I (nat -> nat) x1 x0) (@I (nat -> nat) x1 y0)).
Definition term11 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) := (@INFINITE a0 x0) /\ (forall y0 : a0, forall y1 : a0, ((@IN a0 y0 x0) /\ ((@IN a0 y1 x0) /\ ((x1 y0) = (x1 y1)))) -> y0 = y1).
Definition term136 (x0 : nat -> nat) (x1 : nat) := (fun y0 : nat => ((x0 y0) = (x0 y0)) -> y0 = y0) x1.
Definition term48 (x0 : nat -> nat) (x1 : nat) := (fun y0 : nat => ((x0 x1) = (x0 y0)) -> x1 = y0) x1.
Definition term442 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x2 = x0) /\ ((x3 = x1) /\ (Peano.lt x2 x3)).
Definition term18 (x0 : nat -> nat) (x1 : nat -> Prop) := (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.lt (x0 y0) (x0 y1)) /\ ((@IMAGE nat nat x0 (@UNIV nat)) = x1).
Definition term327 (x0 : nat -> nat) (x1 : nat) := Peano.lt (@I (nat -> nat) x0 x1).
Definition term321 (x0 : nat -> nat) (x1 : nat) := fun y0 : nat => (((x0 x1) = (x0 x1)) /\ (~ (x1 = x1))) \/ ((fun y1 : nat => ((((~ ((x0 x1) = (x0 y1))) \/ (x1 = y1)) /\ (((x0 y1) = (x0 x1)) /\ (~ (y1 = x1)))) \/ ((((x0 x1) = (x0 y1)) /\ (~ (x1 = y1))) /\ ((~ ((x0 y1) = (x0 x1))) \/ (y1 = x1)))) \/ ((Peano.lt x1 y1) /\ (((x0 x1) = (x0 y1)) /\ (~ (x1 = y1))))) y0).
Definition term3 (x0 : type1605) := (((forall y0 : nat, x0 y0 y0) /\ ((forall y0 : nat, forall y1 : nat, (x0 y0 y1) = (x0 y1 y0)) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x0 y0 y1))) -> forall y0 : nat, forall y1 : nat, x0 y0 y1) -> forall y0 : nat, forall y1 : nat, x0 y0 y1.
Definition term359 (x0 : nat -> nat) (x1 : nat) := or (((@I (nat -> nat) x0 x1) = (@I (nat -> nat) x0 x1)) /\ (~ (x1 = x1))).
Definition term124 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := (~ (Peano.lt x0 x2)) \/ (Peano.lt (x1 x0) (x1 x2)).
Definition term363 (x0 : nat) := (fun y0 : nat => ~ (Peano.lt y0 y0)) x0.
Definition term434 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (Peano.lt x2 x3))).
Definition term429 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x1 = x0)) \/ ((~ (Peano.lt x1 x2)) \/ (~ (x2 = x3))).
Definition term439 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((~ (x2 = x0)) \/ (~ (Peano.lt x1 x2))).
Definition term390 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term432 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ ((Peano.lt x0 x1) \/ (~ (Peano.lt x2 x3))))).
Definition term183 (x0 : nat -> nat) := exists y0 : nat, ~ ((fun y1 : nat => forall y2 : nat, (Peano.lt y1 y2) -> ((x0 y1) = (x0 y2)) -> y1 = y2) y0).
Definition term176 (x0 : nat -> nat) (x1 : nat) := exists y0 : nat, ~ ((fun y1 : nat => (Peano.lt x1 y1) -> ((x0 x1) = (x0 y1)) -> x1 = y1) y0).
Definition term165 (x0 : nat -> nat) := exists y0 : nat, ~ ((fun y1 : nat => forall y2 : nat, (((x0 y1) = (x0 y2)) -> y1 = y2) = (((x0 y2) = (x0 y1)) -> y2 = y1)) y0).
Definition term158 (x0 : nat -> nat) (x1 : nat) := exists y0 : nat, ~ ((fun y1 : nat => (((x0 x1) = (x0 y1)) -> x1 = y1) = (((x0 y1) = (x0 x1)) -> y1 = x1)) y0).
Definition term135 (x0 : nat -> nat) := exists y0 : nat, ~ ((fun y1 : nat => ((x0 y1) = (x0 y1)) -> y1 = y1) y0).
Definition term411 (x0 : nat) (x1 : nat) := (~ (Peano.lt x0 x1)) -> Peano.lt x0 x1.
Definition term280 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := or ((fun y0 : nat => (((~ ((x0 x1) = (x0 y0))) \/ (x1 = y0)) /\ (((x0 y0) = (x0 x1)) /\ (~ (y0 = x1)))) \/ ((((x0 x1) = (x0 y0)) /\ (~ (x1 = y0))) /\ ((~ ((x0 y0) = (x0 x1))) \/ (y0 = x1)))) x2).
Definition term207 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := or ((fun y0 : nat => ((~ ((x0 x1) = (x0 y0))) \/ (x1 = y0)) /\ (((x0 y0) = (x0 x1)) /\ (~ (y0 = x1)))) x2).
Definition term447 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := ((@I (nat -> nat) x1 x0) = (@I (nat -> nat) x1 x2)) /\ (((@I (nat -> nat) x1 x2) = (@I (nat -> nat) x1 x2)) /\ (Peano.lt (@I (nat -> nat) x1 x0) (@I (nat -> nat) x1 x2))).
Definition term243 (x0 : nat -> nat) := (exists y0 : nat, exists y1 : nat, ((~ ((x0 y0) = (x0 y1))) \/ (y0 = y1)) /\ (((x0 y1) = (x0 y0)) /\ (~ (y1 = y0)))) \/ (exists y0 : nat, exists y1 : nat, (((x0 y0) = (x0 y1)) /\ (~ (y0 = y1))) /\ ((~ ((x0 y1) = (x0 y0))) \/ (y1 = y0))).
Definition term192 (x0 : nat -> nat) := (exists y0 : nat, exists y1 : nat, (((~ ((x0 y0) = (x0 y1))) \/ (y0 = y1)) /\ (((x0 y1) = (x0 y0)) /\ (~ (y1 = y0)))) \/ ((((x0 y0) = (x0 y1)) /\ (~ (y0 = y1))) /\ ((~ ((x0 y1) = (x0 y0))) \/ (y1 = y0)))) \/ (exists y0 : nat, exists y1 : nat, (Peano.lt y0 y1) /\ (((x0 y0) = (x0 y1)) /\ (~ (y0 = y1)))).
Definition term401 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := (((@I (nat -> nat) x1 x2) = (@I (nat -> nat) x1 x0)) /\ ((@I (nat -> nat) x1 x2) = (@I (nat -> nat) x1 x2))) -> (@I (nat -> nat) x1 x0) = (@I (nat -> nat) x1 x2).
Definition term276 (x0 : nat -> nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => (Peano.lt x1 y1) /\ (((x0 x1) = (x0 y1)) /\ (~ (x1 = y1)))) y0.
Definition term218 (x0 : nat -> nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => (((x0 x1) = (x0 y1)) /\ (~ (x1 = y1))) /\ ((~ ((x0 y1) = (x0 x1))) \/ (y1 = x1))) y0.
Definition term213 (x0 : nat -> nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => ((~ ((x0 x1) = (x0 y1))) \/ (x1 = y1)) /\ (((x0 y1) = (x0 x1)) /\ (~ (y1 = x1)))) y0.
Definition term285 (x0 : nat -> nat) (x1 : nat) := fun y0 : nat => ((((~ ((x0 x1) = (x0 y0))) \/ (x1 = y0)) /\ (((x0 y0) = (x0 x1)) /\ (~ (y0 = x1)))) \/ ((((x0 x1) = (x0 y0)) /\ (~ (x1 = y0))) /\ ((~ ((x0 y0) = (x0 x1))) \/ (y0 = x1)))) \/ ((Peano.lt x1 y0) /\ (((x0 x1) = (x0 y0)) /\ (~ (x1 = y0)))).
Definition term407 (x0 : Prop) (x1 : Prop) := (~ x0) \/ x1.
Definition term438 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (~ (x2 = x0))) /\ (~ ((~ (x3 = x1)) \/ (~ (Peano.lt x2 x3)))).
Definition term105 (x0 : nat -> Prop) (x1 : nat -> nat) := imp (x0 = (@IMAGE nat nat x1 (@UNIV nat))).
Definition term191 (x0 : nat -> nat) := (~ (forall y0 : nat, forall y1 : nat, (((x0 y0) = (x0 y1)) -> y0 = y1) = (((x0 y1) = (x0 y0)) -> y1 = y0))) \/ (~ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> ((x0 y0) = (x0 y1)) -> y0 = y1)).
Definition term146 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := (~ (((x0 x2) = (x0 x1)) -> x2 = x1)) /\ (((x0 x1) = (x0 x2)) -> x1 = x2).
Definition term17 (x0 : nat -> Prop) := exists y0 : nat -> nat, (forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> Peano.lt (y0 y1) (y0 y2)) /\ ((@IMAGE nat nat y0 (@UNIV nat)) = x0).
Definition term342 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := ~ ((x1 x0) = (x1 x2)).
Definition term15 (x0 : nat -> Prop) := (fun y0 : nat -> Prop => (@INFINITE nat y0) -> exists y1 : nat -> nat, (forall y2 : nat, forall y3 : nat, (Peano.lt y2 y3) -> Peano.lt (y1 y2) (y1 y3)) /\ ((@IMAGE nat nat y1 (@UNIV nat)) = y0)) x0.
Definition term430 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (Peano.lt x0 x2)) \/ ((~ (x0 = x1)) \/ (~ (x2 = x3))).
Definition term398 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((x1 = x0) /\ (x1 = x2)).
Definition term73 (x0 : nat -> nat) (x1 : nat) := fun y0 : nat => (Peano.lt x1 y0) -> (fun y1 : nat => fun y2 : nat => ((x0 y1) = (x0 y2)) -> y1 = y2) x1 y0.
Definition term298 (x0 : nat -> nat) := exists y0 : nat, (fun y1 : nat => exists y2 : nat, ((((~ ((x0 y1) = (x0 y2))) \/ (y1 = y2)) /\ (((x0 y2) = (x0 y1)) /\ (~ (y2 = y1)))) \/ ((((x0 y1) = (x0 y2)) /\ (~ (y1 = y2))) /\ ((~ ((x0 y2) = (x0 y1))) \/ (y2 = y1)))) \/ ((Peano.lt y1 y2) /\ (((x0 y1) = (x0 y2)) /\ (~ (y1 = y2))))) y0.
Definition term259 (x0 : nat -> nat) := exists y0 : nat, (fun y1 : nat => exists y2 : nat, (Peano.lt y1 y2) /\ (((x0 y1) = (x0 y2)) /\ (~ (y1 = y2)))) y0.
Definition term255 (x0 : nat -> nat) := exists y0 : nat, (fun y1 : nat => exists y2 : nat, (((~ ((x0 y1) = (x0 y2))) \/ (y1 = y2)) /\ (((x0 y2) = (x0 y1)) /\ (~ (y2 = y1)))) \/ ((((x0 y1) = (x0 y2)) /\ (~ (y1 = y2))) /\ ((~ ((x0 y2) = (x0 y1))) \/ (y2 = y1)))) y0.
Definition term241 (x0 : nat -> nat) := exists y0 : nat, (fun y1 : nat => exists y2 : nat, (((x0 y1) = (x0 y2)) /\ (~ (y1 = y2))) /\ ((~ ((x0 y2) = (x0 y1))) \/ (y2 = y1))) y0.
Definition term236 (x0 : nat -> nat) := exists y0 : nat, (fun y1 : nat => exists y2 : nat, ((~ ((x0 y1) = (x0 y2))) \/ (y1 = y2)) /\ (((x0 y2) = (x0 y1)) /\ (~ (y2 = y1)))) y0.
Definition term8 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := forall y0 : a0 -> Prop, ((@INFINITE a0 y0) /\ (forall y1 : a0, forall y2 : a0, ((@IN a0 y1 y0) /\ ((@IN a0 y2 y0) /\ ((x0 y1) = (x0 y2)))) -> y1 = y2)) -> @INFINITE a1 (@IMAGE a0 a1 x0 y0).
Definition term325 (x0 : nat -> nat) := exists y0 : nat, exists y1 : nat, (((x0 y0) = (x0 y0)) /\ (~ (y0 = y0))) \/ (((((~ ((x0 y0) = (x0 y1))) \/ (y0 = y1)) /\ (((x0 y1) = (x0 y0)) /\ (~ (y1 = y0)))) \/ ((((x0 y0) = (x0 y1)) /\ (~ (y0 = y1))) /\ ((~ ((x0 y1) = (x0 y0))) \/ (y1 = y0)))) \/ ((Peano.lt y0 y1) /\ (((x0 y0) = (x0 y1)) /\ (~ (y0 = y1))))).
Definition term288 (x0 : nat -> nat) := exists y0 : nat, exists y1 : nat, ((((~ ((x0 y0) = (x0 y1))) \/ (y0 = y1)) /\ (((x0 y1) = (x0 y0)) /\ (~ (y1 = y0)))) \/ ((((x0 y0) = (x0 y1)) /\ (~ (y0 = y1))) /\ ((~ ((x0 y1) = (x0 y0))) \/ (y1 = y0)))) \/ ((Peano.lt y0 y1) /\ (((x0 y0) = (x0 y1)) /\ (~ (y0 = y1)))).
Definition term242 (x0 : nat -> nat) := exists y0 : nat, exists y1 : nat, (((x0 y0) = (x0 y1)) /\ (~ (y0 = y1))) /\ ((~ ((x0 y1) = (x0 y0))) \/ (y1 = y0)).
Definition term237 (x0 : nat -> nat) := exists y0 : nat, exists y1 : nat, ((~ ((x0 y0) = (x0 y1))) \/ (y0 = y1)) /\ (((x0 y1) = (x0 y0)) /\ (~ (y1 = y0))).
Definition term188 (x0 : nat -> nat) := exists y0 : nat, exists y1 : nat, (Peano.lt y0 y1) /\ (((x0 y0) = (x0 y1)) /\ (~ (y0 = y1))).
Definition term170 (x0 : nat -> nat) := exists y0 : nat, exists y1 : nat, (((~ ((x0 y0) = (x0 y1))) \/ (y0 = y1)) /\ (((x0 y1) = (x0 y0)) /\ (~ (y1 = y0)))) \/ ((((x0 y0) = (x0 y1)) /\ (~ (y0 = y1))) /\ ((~ ((x0 y1) = (x0 y0))) \/ (y1 = y0))).
Definition term62 (x0 : nat -> nat) (x1 : nat) := forall y0 : nat, ((fun y1 : nat => fun y2 : nat => ((x0 y1) = (x0 y2)) -> y1 = y2) x1 y0) = ((fun y1 : nat => fun y2 : nat => ((x0 y1) = (x0 y2)) -> y1 = y2) y0 x1).
Definition term142 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := ((x0 x1) = (x0 x2)) /\ (~ (x1 = x2)).
Definition term454 (x0 : nat -> nat) := (fun y0 : nat -> nat => forall y1 : nat -> Prop, (forall y2 : nat, forall y3 : nat, (Peano.lt y2 y3) -> Peano.lt (y0 y2) (y0 y3)) -> (y1 = (@IMAGE nat nat y0 (@UNIV nat))) -> (~ ((forall y2 : nat, ((y0 y2) = (y0 y2)) -> y2 = y2) /\ ((forall y2 : nat, forall y3 : nat, (((y0 y2) = (y0 y3)) -> y2 = y3) = (((y0 y3) = (y0 y2)) -> y3 = y2)) /\ (forall y2 : nat, forall y3 : nat, (Peano.lt y2 y3) -> ((y0 y2) = (y0 y3)) -> y2 = y3)))) -> (forall y2 : nat, ~ (Peano.lt y2 y2)) -> False) x0.
Definition term200 (x0 : nat -> Prop) (x1 : nat -> Prop) := exists y0 : nat, (x0 y0) \/ (x1 y0).
Definition term179 (x0 : nat -> nat) (x1 : nat) := fun y0 : nat => ~ ((fun y1 : nat => (Peano.lt x1 y1) -> ((x0 x1) = (x0 y1)) -> x1 = y1) y0).
Definition term161 (x0 : nat -> nat) (x1 : nat) := fun y0 : nat => ~ ((fun y1 : nat => (((x0 x1) = (x0 y1)) -> x1 = y1) = (((x0 y1) = (x0 x1)) -> y1 = x1)) y0).
Definition term138 (x0 : nat -> nat) := fun y0 : nat => ~ ((fun y1 : nat => ((x0 y1) = (x0 y1)) -> y1 = y1) y0).
Definition term137 (x0 : nat -> nat) (x1 : nat) := ~ ((fun y0 : nat => ((x0 y0) = (x0 y0)) -> y0 = y0) x1).
Definition term205 (x0 : nat -> nat) (x1 : nat) := fun y0 : nat => (((x0 x1) = (x0 y0)) /\ (~ (x1 = y0))) /\ ((~ ((x0 y0) = (x0 x1))) \/ (y0 = x1)).
Definition term57 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((x0 x1) = (x0 y0)) -> x1 = y0) x2.
Definition term75 (x0 : nat -> nat) (x1 : nat) := forall y0 : nat, (Peano.lt x1 y0) -> (fun y1 : nat => fun y2 : nat => ((x0 y1) = (x0 y2)) -> y1 = y2) x1 y0.
Definition term35 (x0 : nat -> nat) (x1 : nat) := fun y0 : nat => ((x0 x1) = (x0 y0)) -> x1 = y0.
Definition term51 (x0 : nat -> nat) := fun y0 : nat => ((x0 y0) = (x0 y0)) -> y0 = y0.
Definition term181 (x0 : nat -> nat) (x1 : nat) := exists y0 : nat, (Peano.lt x1 y0) /\ (((x0 x1) = (x0 y0)) /\ (~ (x1 = y0))).
Definition term337 (x0 : nat -> nat) (x1 : nat) := @eq nat (@I (nat -> nat) x0 x1).
Definition term377 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = x2)) \/ (x1 = x2).
Definition term284 (x0 : nat -> nat) (x1 : nat) := fun y0 : nat => ((fun y1 : nat => (((~ ((x0 x1) = (x0 y1))) \/ (x1 = y1)) /\ (((x0 y1) = (x0 x1)) /\ (~ (y1 = x1)))) \/ ((((x0 x1) = (x0 y1)) /\ (~ (x1 = y1))) /\ ((~ ((x0 y1) = (x0 x1))) \/ (y1 = x1)))) y0) \/ ((fun y1 : nat => (Peano.lt x1 y1) /\ (((x0 x1) = (x0 y1)) /\ (~ (x1 = y1)))) y0).
Definition term210 (x0 : nat -> nat) (x1 : nat) := fun y0 : nat => ((fun y1 : nat => ((~ ((x0 x1) = (x0 y1))) \/ (x1 = y1)) /\ (((x0 y1) = (x0 x1)) /\ (~ (y1 = x1)))) y0) \/ ((fun y1 : nat => (((x0 x1) = (x0 y1)) /\ (~ (x1 = y1))) /\ ((~ ((x0 y1) = (x0 x1))) \/ (y1 = x1))) y0).
Definition term295 (x0 : nat -> nat) := or (exists y0 : nat, (fun y1 : nat => ((x0 y1) = (x0 y1)) /\ (~ (y1 = y1))) y0).
Definition term274 (x0 : nat -> nat) (x1 : nat) := or (exists y0 : nat, (fun y1 : nat => (((~ ((x0 x1) = (x0 y1))) \/ (x1 = y1)) /\ (((x0 y1) = (x0 x1)) /\ (~ (y1 = x1)))) \/ ((((x0 x1) = (x0 y1)) /\ (~ (x1 = y1))) /\ ((~ ((x0 y1) = (x0 x1))) \/ (y1 = x1)))) y0).
Definition term256 (x0 : nat -> nat) := or (exists y0 : nat, (fun y1 : nat => exists y2 : nat, (((~ ((x0 y1) = (x0 y2))) \/ (y1 = y2)) /\ (((x0 y2) = (x0 y1)) /\ (~ (y2 = y1)))) \/ ((((x0 y1) = (x0 y2)) /\ (~ (y1 = y2))) /\ ((~ ((x0 y2) = (x0 y1))) \/ (y2 = y1)))) y0).
Definition term238 (x0 : nat -> nat) := or (exists y0 : nat, (fun y1 : nat => exists y2 : nat, ((~ ((x0 y1) = (x0 y2))) \/ (y1 = y2)) /\ (((x0 y2) = (x0 y1)) /\ (~ (y2 = y1)))) y0).
Definition term216 (x0 : nat -> nat) (x1 : nat) := or (exists y0 : nat, (fun y1 : nat => ((~ ((x0 x1) = (x0 y1))) \/ (x1 = y1)) /\ (((x0 y1) = (x0 x1)) /\ (~ (y1 = x1)))) y0).
Definition term346 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := (~ ((@I (nat -> nat) x0 x1) = (@I (nat -> nat) x0 x2))) \/ (x1 = x2).
Definition term162 (x0 : nat -> nat) (x1 : nat) := fun y0 : nat => (((~ ((x0 x1) = (x0 y0))) \/ (x1 = y0)) /\ (((x0 y0) = (x0 x1)) /\ (~ (y0 = x1)))) \/ ((((x0 x1) = (x0 y0)) /\ (~ (x1 = y0))) /\ ((~ ((x0 y0) = (x0 x1))) \/ (y0 = x1))).
Definition term127 (x0 : nat) (x1 : nat -> nat) := forall y0 : nat, (~ (Peano.lt x0 y0)) \/ (Peano.lt (x1 x0) (x1 y0)).
Definition term366 (x0 : nat) := (fun y0 : nat => ~ (x0 = y0)) x0.
Definition term95 (x0 : nat -> Prop) (x1 : nat -> nat) := (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.lt (x1 y0) (x1 y1)) -> (x0 = (@IMAGE nat nat x1 (@UNIV nat))) -> (~ ((forall y0 : nat, ((x1 y0) = (x1 y0)) -> y0 = y0) /\ ((forall y0 : nat, forall y1 : nat, (((x1 y0) = (x1 y1)) -> y0 = y1) = (((x1 y1) = (x1 y0)) -> y1 = y0)) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> ((x1 y0) = (x1 y1)) -> y0 = y1)))) -> (forall y0 : nat, ~ (Peano.lt y0 y0)) -> False.
Definition term393 (x0 : nat) (x1 : nat) := ~ (~ (x0 = x1)).
Definition term7 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := (fun y0 : a0 -> a1 => forall y1 : a0 -> Prop, ((@INFINITE a0 y1) /\ (forall y2 : a0, forall y3 : a0, ((@IN a0 y2 y1) /\ ((@IN a0 y3 y1) /\ ((y0 y2) = (y0 y3)))) -> y2 = y3)) -> @INFINITE a1 (@IMAGE a0 a1 y0 y1)) x0.
Definition term353 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := or ((((~ ((@I (nat -> nat) x0 x2) = (@I (nat -> nat) x0 x1))) \/ (x2 = x1)) /\ (((@I (nat -> nat) x0 x1) = (@I (nat -> nat) x0 x2)) /\ (~ (x1 = x2)))) \/ ((((@I (nat -> nat) x0 x2) = (@I (nat -> nat) x0 x1)) /\ (~ (x2 = x1))) /\ ((~ ((@I (nat -> nat) x0 x1) = (@I (nat -> nat) x0 x2))) \/ (x1 = x2)))).
Definition term281 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := or ((((~ ((x0 x2) = (x0 x1))) \/ (x2 = x1)) /\ (((x0 x1) = (x0 x2)) /\ (~ (x1 = x2)))) \/ ((((x0 x2) = (x0 x1)) /\ (~ (x2 = x1))) /\ ((~ ((x0 x1) = (x0 x2))) \/ (x1 = x2)))).
Definition term379 (x0 : nat) (x1 : nat) := or (~ (x0 = x1)).
Definition term365 (x0 : nat) (x1 : nat) := (fun y0 : nat => ~ (x0 = y0)) x1.
Definition term131 (x0 : nat -> nat) (x1 : nat) := ((x0 x1) = (x0 x1)) /\ (~ (x1 = x1)).
Definition term108 (x0 : nat -> nat) := imp (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.lt (x0 y0) (x0 y1)).
Definition term151 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := ((~ ((x0 x2) = (x0 x1))) \/ (x2 = x1)) /\ (((x0 x1) = (x0 x2)) /\ (~ (x1 = x2))).
Definition term52 (x0 : nat -> nat) := forall y0 : nat, (fun y1 : nat => fun y2 : nat => ((x0 y1) = (x0 y2)) -> y1 = y2) y0 y0.
Definition term344 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := or (~ ((x1 x0) = (x1 x2))).
Definition term349 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := and ((~ ((@I (nat -> nat) x0 x1) = (@I (nat -> nat) x0 x2))) \/ (x1 = x2)).
Definition term149 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := and ((~ ((x0 x1) = (x0 x2))) \/ (x1 = x2)).
Definition term198 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term399 (x0 : nat) (x1 : nat) (x2 : nat) := ((x0 = x1) /\ (x0 = x2)) -> x1 = x2.
Definition term410 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ ((Peano.lt x0 x1) \/ (~ (Peano.lt x2 x3)))).
Definition term60 (x0 : nat -> nat) (x1 : nat) := fun y0 : nat => ((fun y1 : nat => fun y2 : nat => ((x0 y1) = (x0 y2)) -> y1 = y2) x1 y0) = ((fun y1 : nat => fun y2 : nat => ((x0 y1) = (x0 y2)) -> y1 = y2) y0 x1).
Definition term133 (x0 : nat -> Prop) := exists y0 : nat, ~ (x0 y0).
Definition term368 (x0 : nat) (x1 : nat) := @eq Prop (~ (x0 = x1)).
Definition term310 (x0 : Prop) (x1 : nat -> Prop) := x0 \/ (exists y0 : nat, x1 y0).
Definition term180 (x0 : nat -> nat) (x1 : nat) := fun y0 : nat => (Peano.lt x1 y0) /\ (((x0 x1) = (x0 y0)) /\ (~ (x1 = y0))).
Definition term354 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := ((((~ ((@I (nat -> nat) x0 x1) = (@I (nat -> nat) x0 x2))) \/ (x1 = x2)) /\ (((@I (nat -> nat) x0 x2) = (@I (nat -> nat) x0 x1)) /\ (~ (x2 = x1)))) \/ ((((@I (nat -> nat) x0 x1) = (@I (nat -> nat) x0 x2)) /\ (~ (x1 = x2))) /\ ((~ ((@I (nat -> nat) x0 x2) = (@I (nat -> nat) x0 x1))) \/ (x2 = x1)))) \/ ((Peano.lt x1 x2) /\ (((@I (nat -> nat) x0 x1) = (@I (nat -> nat) x0 x2)) /\ (~ (x1 = x2)))).
Definition term283 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := ((((~ ((x0 x1) = (x0 x2))) \/ (x1 = x2)) /\ (((x0 x2) = (x0 x1)) /\ (~ (x2 = x1)))) \/ ((((x0 x1) = (x0 x2)) /\ (~ (x1 = x2))) /\ ((~ ((x0 x2) = (x0 x1))) \/ (x2 = x1)))) \/ ((Peano.lt x1 x2) /\ (((x0 x1) = (x0 x2)) /\ (~ (x1 = x2)))).
Definition term333 (x0 : nat -> nat) := fun y0 : nat => forall y1 : nat, (~ (Peano.lt y0 y1)) \/ (Peano.lt (@I (nat -> nat) x0 y0) (@I (nat -> nat) x0 y1)).
Definition term128 (x0 : nat -> nat) := fun y0 : nat => forall y1 : nat, (~ (Peano.lt y0 y1)) \/ (Peano.lt (x0 y0) (x0 y1)).
Definition term123 (x0 : nat -> nat) := fun y0 : nat => forall y1 : nat, (Peano.lt y0 y1) -> Peano.lt (x0 y0) (x0 y1).
Definition term78 (x0 : nat -> nat) := fun y0 : nat => forall y1 : nat, (Peano.lt y0 y1) -> ((x0 y0) = (x0 y1)) -> y0 = y1.
Definition term65 (x0 : nat -> nat) := fun y0 : nat => forall y1 : nat, (((x0 y0) = (x0 y1)) -> y0 = y1) = (((x0 y1) = (x0 y0)) -> y1 = y0).
Definition term201 (x0 : nat -> Prop) (x1 : nat -> Prop) := (exists y0 : nat, x0 y0) \/ (exists y0 : nat, x1 y0).
Definition term446 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := ((@I (nat -> nat) x1 x2) = (@I (nat -> nat) x1 x2)) /\ (Peano.lt (@I (nat -> nat) x1 x0) (@I (nat -> nat) x1 x2)).
Definition term371 (x0 : nat) := (x0 = x0) -> False.
Definition term140 (x0 : nat -> nat) := exists y0 : nat, ((x0 y0) = (x0 y0)) /\ (~ (y0 = y0)).
Definition term418 (x0 : nat) (x1 : nat) := imp (~ (~ (Peano.lt x0 x1))).
Definition term246 (x0 : nat -> nat) := (exists y0 : nat, ((x0 y0) = (x0 y0)) /\ (~ (y0 = y0))) \/ (((exists y0 : nat, exists y1 : nat, ((~ ((x0 y0) = (x0 y1))) \/ (y0 = y1)) /\ (((x0 y1) = (x0 y0)) /\ (~ (y1 = y0)))) \/ (exists y0 : nat, exists y1 : nat, (((x0 y0) = (x0 y1)) /\ (~ (y0 = y1))) /\ ((~ ((x0 y1) = (x0 y0))) \/ (y1 = y0)))) \/ (exists y0 : nat, exists y1 : nat, (Peano.lt y0 y1) /\ (((x0 y0) = (x0 y1)) /\ (~ (y0 = y1))))).
Definition term104 (x0 : nat -> nat) := (~ ((forall y0 : nat, ((x0 y0) = (x0 y0)) -> y0 = y0) /\ ((forall y0 : nat, forall y1 : nat, (((x0 y0) = (x0 y1)) -> y0 = y1) = (((x0 y1) = (x0 y0)) -> y1 = y0)) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> ((x0 y0) = (x0 y1)) -> y0 = y1)))) -> ~ (forall y0 : nat, ~ (Peano.lt y0 y0)).
Definition term34 (x0 : nat -> nat) (x1 : nat) := fun y0 : nat => ((@IN nat x1 (@UNIV nat)) /\ ((@IN nat y0 (@UNIV nat)) /\ ((x0 x1) = (x0 y0)))) -> x1 = y0.
Definition term300 (x0 : nat -> nat) := @eq Prop ((exists y0 : nat, ((x0 y0) = (x0 y0)) /\ (~ (y0 = y0))) \/ (exists y0 : nat, exists y1 : nat, ((((~ ((x0 y0) = (x0 y1))) \/ (y0 = y1)) /\ (((x0 y1) = (x0 y0)) /\ (~ (y1 = y0)))) \/ ((((x0 y0) = (x0 y1)) /\ (~ (y0 = y1))) /\ ((~ ((x0 y1) = (x0 y0))) \/ (y1 = y0)))) \/ ((Peano.lt y0 y1) /\ (((x0 y0) = (x0 y1)) /\ (~ (y0 = y1)))))).
Definition term299 (x0 : nat -> nat) := @eq Prop ((exists y0 : nat, (fun y1 : nat => ((x0 y1) = (x0 y1)) /\ (~ (y1 = y1))) y0) \/ (exists y0 : nat, (fun y1 : nat => exists y2 : nat, ((((~ ((x0 y1) = (x0 y2))) \/ (y1 = y2)) /\ (((x0 y2) = (x0 y1)) /\ (~ (y2 = y1)))) \/ ((((x0 y1) = (x0 y2)) /\ (~ (y1 = y2))) /\ ((~ ((x0 y2) = (x0 y1))) \/ (y2 = y1)))) \/ ((Peano.lt y1 y2) /\ (((x0 y1) = (x0 y2)) /\ (~ (y1 = y2))))) y0)).
Definition term279 (x0 : nat -> nat) (x1 : nat) := @eq Prop ((exists y0 : nat, (((~ ((x0 x1) = (x0 y0))) \/ (x1 = y0)) /\ (((x0 y0) = (x0 x1)) /\ (~ (y0 = x1)))) \/ ((((x0 x1) = (x0 y0)) /\ (~ (x1 = y0))) /\ ((~ ((x0 y0) = (x0 x1))) \/ (y0 = x1)))) \/ (exists y0 : nat, (Peano.lt x1 y0) /\ (((x0 x1) = (x0 y0)) /\ (~ (x1 = y0))))).
Definition term278 (x0 : nat -> nat) (x1 : nat) := @eq Prop ((exists y0 : nat, (fun y1 : nat => (((~ ((x0 x1) = (x0 y1))) \/ (x1 = y1)) /\ (((x0 y1) = (x0 x1)) /\ (~ (y1 = x1)))) \/ ((((x0 x1) = (x0 y1)) /\ (~ (x1 = y1))) /\ ((~ ((x0 y1) = (x0 x1))) \/ (y1 = x1)))) y0) \/ (exists y0 : nat, (fun y1 : nat => (Peano.lt x1 y1) /\ (((x0 x1) = (x0 y1)) /\ (~ (x1 = y1)))) y0)).
Definition term261 (x0 : nat -> nat) := @eq Prop ((exists y0 : nat, exists y1 : nat, (((~ ((x0 y0) = (x0 y1))) \/ (y0 = y1)) /\ (((x0 y1) = (x0 y0)) /\ (~ (y1 = y0)))) \/ ((((x0 y0) = (x0 y1)) /\ (~ (y0 = y1))) /\ ((~ ((x0 y1) = (x0 y0))) \/ (y1 = y0)))) \/ (exists y0 : nat, exists y1 : nat, (Peano.lt y0 y1) /\ (((x0 y0) = (x0 y1)) /\ (~ (y0 = y1))))).
Definition term260 (x0 : nat -> nat) := @eq Prop ((exists y0 : nat, (fun y1 : nat => exists y2 : nat, (((~ ((x0 y1) = (x0 y2))) \/ (y1 = y2)) /\ (((x0 y2) = (x0 y1)) /\ (~ (y2 = y1)))) \/ ((((x0 y1) = (x0 y2)) /\ (~ (y1 = y2))) /\ ((~ ((x0 y2) = (x0 y1))) \/ (y2 = y1)))) y0) \/ (exists y0 : nat, (fun y1 : nat => exists y2 : nat, (Peano.lt y1 y2) /\ (((x0 y1) = (x0 y2)) /\ (~ (y1 = y2)))) y0)).
Definition term250 (x0 : nat -> nat) (x1 : nat) := @eq Prop ((exists y0 : nat, ((~ ((x0 x1) = (x0 y0))) \/ (x1 = y0)) /\ (((x0 y0) = (x0 x1)) /\ (~ (y0 = x1)))) \/ (exists y0 : nat, (((x0 x1) = (x0 y0)) /\ (~ (x1 = y0))) /\ ((~ ((x0 y0) = (x0 x1))) \/ (y0 = x1)))).
Definition term249 (x0 : nat -> nat) (x1 : nat) := @eq Prop ((exists y0 : nat, (fun y1 : nat => ((~ ((x0 x1) = (x0 y1))) \/ (x1 = y1)) /\ (((x0 y1) = (x0 x1)) /\ (~ (y1 = x1)))) y0) \/ (exists y0 : nat, (fun y1 : nat => (((x0 x1) = (x0 y1)) /\ (~ (x1 = y1))) /\ ((~ ((x0 y1) = (x0 x1))) \/ (y1 = x1))) y0)).
Definition term248 (x0 : nat -> nat) := @eq Prop ((exists y0 : nat, exists y1 : nat, ((~ ((x0 y0) = (x0 y1))) \/ (y0 = y1)) /\ (((x0 y1) = (x0 y0)) /\ (~ (y1 = y0)))) \/ (exists y0 : nat, exists y1 : nat, (((x0 y0) = (x0 y1)) /\ (~ (y0 = y1))) /\ ((~ ((x0 y1) = (x0 y0))) \/ (y1 = y0)))).
Definition term247 (x0 : nat -> nat) := @eq Prop ((exists y0 : nat, (fun y1 : nat => exists y2 : nat, ((~ ((x0 y1) = (x0 y2))) \/ (y1 = y2)) /\ (((x0 y2) = (x0 y1)) /\ (~ (y2 = y1)))) y0) \/ (exists y0 : nat, (fun y1 : nat => exists y2 : nat, (((x0 y1) = (x0 y2)) /\ (~ (y1 = y2))) /\ ((~ ((x0 y2) = (x0 y1))) \/ (y2 = y1))) y0)).
