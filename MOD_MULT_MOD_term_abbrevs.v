Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term619 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul (Nat.div (Nat.div x0 x1) x2) x2).
Definition term516 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)) = x0) \/ (x1 = x2).
Definition term604 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul (Nat.div x0 (Nat.mul x1 x2)) (Nat.mul x1 x2)).
Definition term359 (x0 : nat) (x1 : nat) := (~ ((NUMERAL 0) = x1)) \/ (x0 = x1).
Definition term9 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1).
Definition term528 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : Prop => (((Nat.add (Nat.mul x2 (Nat.div x1 x2)) (Nat.modulo x1 x2)) = x1) \/ (x2 = x0)) -> ((~ ((Nat.add (Nat.mul x2 (Nat.div x1 x2)) (Nat.modulo x1 x2)) = x1)) \/ y0) -> (x2 = x0) \/ y0) ((~ (x1 = x1)) \/ (x1 = (Nat.add (Nat.mul x2 (Nat.div x1 x2)) (Nat.modulo x1 x2)))).
Definition term564 (x0 : nat) (x1 : nat) := (~ ((NUMERAL 0) = x1)) \/ ((x0 = (NUMERAL 0)) \/ (~ (x0 = x1))).
Definition term87 (x0 : nat) (x1 : nat) := ~ (x0 = x1).
Definition term349 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) -> (x0 = x1) \/ (~ ((NUMERAL 0) = x1)).
Definition term238 (x0 : nat) (x1 : nat) := (~ (x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))) -> False.
Definition term423 (x0 : nat) (x1 : nat) := (fun y0 : Prop => forall y1 : Prop, y0 -> ((~ y0) \/ y1) -> y1) ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))).
Definition term400 (x0 : nat) (x1 : nat) := (fun y0 : Prop => forall y1 : Prop, (y0 -> y1) = ((~ y0) \/ y1)) ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))).
Definition term471 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : Prop => ((x1 = (Nat.add (Nat.mul (Nat.div x1 x2) x2) (Nat.modulo x1 x2))) \/ (x2 = x0)) -> ((~ (x1 = (Nat.add (Nat.mul (Nat.div x1 x2) x2) (Nat.modulo x1 x2)))) \/ y0) -> (x2 = x0) \/ y0) (x1 = (Nat.add (Nat.mul x2 (Nat.div x1 x2)) (Nat.modulo x1 x2))).
Definition term598 (x0 : nat) (x1 : nat) (x2 : nat) := (exists y0 : nat, (Nat.add y0 (Nat.modulo x1 (Nat.mul x2 x0))) = (Nat.add y0 (Nat.add (Nat.mul x2 (Nat.modulo (Nat.div x1 x2) x0)) (Nat.modulo x1 x2)))) -> (Nat.modulo x1 (Nat.mul x2 x0)) = (Nat.add (Nat.mul x2 (Nat.modulo (Nat.div x1 x2) x0)) (Nat.modulo x1 x2)).
Definition term175 := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, forall y3 : nat, ((Nat.add y1 y2) = (Nat.add y1 y3)) \/ (~ (y2 = y3))) y0) /\ ((fun y1 : nat => forall y2 : nat, forall y3 : nat, (~ ((Nat.add y1 y2) = (Nat.add y1 y3))) \/ (y2 = y3)) y0).
Definition term153 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, ((Nat.add x0 y1) = (Nat.add x0 y2)) \/ (~ (y1 = y2))) y0) /\ ((fun y1 : nat => forall y2 : nat, (~ ((Nat.add x0 y1) = (Nat.add x0 y2))) \/ (y1 = y2)) y0).
Definition term202 := (~ False) -> False.
Definition term89 (x0 : nat) (x1 : nat) := (exists y0 : nat, (Nat.add y0 x0) = (Nat.add y0 x1)) /\ (~ (x0 = x1)).
Definition term461 (x0 : nat) (x1 : nat) := (fun y0 : Prop => forall y1 : Prop, y0 -> ((~ y0) \/ y1) -> y1) ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))).
Definition term126 (x0 : nat) (x1 : nat) (x2 : nat) := and ((fun y0 : nat => ((Nat.add x0 x1) = (Nat.add x0 y0)) \/ (~ (x1 = y0))) x2).
Definition term102 (x0 : nat) (x1 : nat) (x2 : nat) := and ((fun y0 : nat => (Nat.add y0 x0) = (Nat.add y0 x1)) x2).
Definition term426 (x0 : nat) (x1 : nat) := ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) -> ((~ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) \/ ((~ ((Nat.mul (Nat.div x0 x1) x1) = (Nat.mul x1 (Nat.div x0 x1)))) \/ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))))) -> (~ ((Nat.mul (Nat.div x0 x1) x1) = (Nat.mul x1 (Nat.div x0 x1)))) \/ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))).
Definition term199 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.add x0 x1) = (Nat.add x0 x2)) -> x1 = x2.
Definition term605 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul (Nat.div (Nat.div x0 x1) x2) (Nat.mul x1 x2)) (Nat.modulo x0 (Nat.mul x1 x2)).
Definition term222 (x0 : nat) (x1 : nat) := Nat.modulo (Nat.div x0 x1).
Definition term588 (x0 : nat) := (fun y0 : Prop => forall y1 : Prop, (y0 \/ y1) -> (~ y0) -> y1) (x0 = (NUMERAL 0)).
Definition term556 (x0 : nat) := (fun y0 : Prop => forall y1 : Prop, ((~ y0) -> y1) = (y0 \/ y1)) (x0 = (NUMERAL 0)).
Definition term376 (x0 : nat) := (fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, (y0 \/ y1) -> ((~ y0) \/ y2) -> y1 \/ y2) (x0 = (NUMERAL 0)).
Definition term350 (x0 : nat) := (fun y0 : Prop => forall y1 : Prop, (y0 -> y1) = ((~ y0) \/ y1)) (x0 = (NUMERAL 0)).
Definition term337 (x0 : nat) := (fun y0 : Prop => forall y1 : Prop, y0 -> ((~ y0) \/ y1) -> y1) (x0 = (NUMERAL 0)).
Definition term103 (x0 : nat) (x1 : nat) (x2 : nat) := and ((Nat.add x1 x0) = (Nat.add x1 x2)).
Definition term475 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((x2 = x0) \/ (x1 = (Nat.add (Nat.mul x2 (Nat.div x1 x2)) (Nat.modulo x1 x2)))).
Definition term385 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((x2 = x0) \/ (x1 = (Nat.add (Nat.mul (Nat.div x1 x2) x2) (Nat.modulo x1 x2)))).
Definition term167 := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, forall y3 : nat, ((Nat.add y1 y2) = (Nat.add y1 y3)) \/ (~ (y2 = y3))) y0) /\ ((fun y1 : nat => forall y2 : nat, forall y3 : nat, (~ ((Nat.add y1 y2) = (Nat.add y1 y3))) \/ (y2 = y3)) y0).
Definition term145 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Nat.add x0 y1) = (Nat.add x0 y2)) \/ (~ (y1 = y2))) y0) /\ ((fun y1 : nat => forall y2 : nat, (~ ((Nat.add x0 y1) = (Nat.add x0 y2))) \/ (y1 = y2)) y0).
Definition term120 (x0 : nat) (x1 : nat) := forall y0 : nat, ((fun y1 : nat => ((Nat.add x0 x1) = (Nat.add x0 y1)) \/ (~ (x1 = y1))) y0) /\ ((fun y1 : nat => (~ ((Nat.add x0 x1) = (Nat.add x0 y1))) \/ (x1 = y1)) y0).
Definition term510 (x0 : nat) (x1 : nat) := (~ (x0 = x0)) \/ ((~ ((Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)) = x0)) \/ (x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))).
Definition term342 := @eq nat (NUMERAL 0).
Definition term366 (x0 : nat) (x1 : nat) := (~ (x0 = (NUMERAL 0))) \/ (x0 = x1).
Definition term487 (x0 : nat) (x1 : nat) (x2 : nat) := ((x2 = (Nat.add (Nat.mul x1 (Nat.div x2 x1)) (Nat.modulo x2 x1))) \/ (x1 = x0)) -> ((~ (x2 = (Nat.add (Nat.mul x1 (Nat.div x2 x1)) (Nat.modulo x2 x1)))) \/ ((Nat.add (Nat.mul x1 (Nat.div x2 x1)) (Nat.modulo x2 x1)) = x2)) -> (x1 = x0) \/ ((Nat.add (Nat.mul x1 (Nat.div x2 x1)) (Nat.modulo x2 x1)) = x2).
Definition term27 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.add (Nat.mul x0 x1) (Nat.mul x0 y0)) = (Nat.mul x0 (Nat.add x1 y0)).
Definition term443 (x0 : nat) (x1 : nat) := ~ ((~ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) \/ ((x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))) \/ (~ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))))).
Definition term104 (x0 : nat) (x1 : nat) (x2 : nat) := ((fun y0 : nat => (Nat.add y0 x1) = (Nat.add y0 x2)) x0) /\ (~ (x1 = x2)).
Definition term215 := forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0).
Definition term195 (x0 : Prop) := ~ (~ x0).
Definition term595 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (~ (y0 = (NUMERAL 0))) -> (y2 = (NUMERAL 0)) -> (~ (y1 = (Nat.add (Nat.mul y0 (Nat.div y1 y0)) (Nat.modulo y1 y0)))) -> (forall y3 : nat, forall y4 : nat, (Nat.mul y3 y4) = (Nat.mul y4 y3)) -> (forall y3 : nat, forall y4 : nat, (~ (y4 = (NUMERAL 0))) -> (y3 = (Nat.add (Nat.mul (Nat.div y3 y4) y4) (Nat.modulo y3 y4))) /\ (Peano.lt (Nat.modulo y3 y4) y4)) -> False) x0.
Definition term173 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (~ ((Nat.add y0 y1) = (Nat.add y0 y2))) \/ (y1 = y2)) x0.
Definition term171 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Nat.add y0 y1) = (Nat.add y0 y2)) \/ (~ (y1 = y2))) x0.
Definition term55 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.div (Nat.div y0 y1) y2) = (Nat.div y0 (Nat.mul y1 y2))) x0.
Definition term48 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y2)) = (Nat.mul y0 (Nat.add y1 y2))) x0.
Definition term41 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.add y0 (Nat.add y1 y2)) = (Nat.add (Nat.add y0 y1) y2)) x0.
Definition term38 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.div y0 (Nat.mul y1 y2)) = (Nat.div (Nat.div y0 y1) y2)) x0.
Definition term413 (x0 : nat) (x1 : nat) := ~ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))).
Definition term255 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = (NUMERAL 0)) -> (~ (x1 = (Nat.add (Nat.mul x2 (Nat.div x1 x2)) (Nat.modulo x1 x2)))) -> (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> ~ (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term257 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x2 = (NUMERAL 0))) -> (x0 = (NUMERAL 0)) -> (~ (x1 = (Nat.add (Nat.mul x2 (Nat.div x1 x2)) (Nat.modulo x1 x2)))) -> (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> ~ (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term303 (x0 : nat) (x1 : nat) := (~ ((x1 = (NUMERAL 0)) \/ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))))) -> ~ ((x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) \/ (x1 = (NUMERAL 0))).
Definition term511 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((x1 = x0) \/ ((Nat.add (Nat.mul x1 (Nat.div x2 x1)) (Nat.modulo x2 x1)) = x2)).
Definition term453 (x0 : nat) (x1 : nat) := (~ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) \/ ((~ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))) \/ (x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))).
Definition term285 (x0 : nat) := forall y0 : nat, (y0 = (NUMERAL 0)) \/ ((x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0)).
Definition term622 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x1 (Nat.add (Nat.mul (Nat.div (Nat.div x0 x1) x2) x2) (Nat.modulo (Nat.div x0 x1) x2)).
Definition term615 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x1 (Nat.add (Nat.mul (Nat.div x0 (Nat.mul x1 x2)) x2) (Nat.modulo (Nat.div x0 x1) x2)).
Definition term131 (x0 : nat) (x1 : nat) := fun y0 : nat => ((fun y1 : nat => ((Nat.add x0 x1) = (Nat.add x0 y1)) \/ (~ (x1 = y1))) y0) /\ ((fun y1 : nat => (~ ((Nat.add x0 x1) = (Nat.add x0 y1))) \/ (x1 = y1)) y0).
Definition term428 (x0 : nat) (x1 : nat) := (fun y0 : Prop => forall y1 : Prop, y0 -> ((~ y0) \/ y1) -> y1) ((Nat.mul (Nat.div x0 x1) x1) = (Nat.mul x1 (Nat.div x0 x1))).
Definition term405 (x0 : nat) (x1 : nat) := (fun y0 : Prop => forall y1 : Prop, (y0 -> y1) = ((~ y0) \/ y1)) ((Nat.mul (Nat.div x0 x1) x1) = (Nat.mul x1 (Nat.div x0 x1))).
Definition term492 (x0 : nat) (x1 : nat) := (fun y0 : Prop => ((~ (x1 = (Nat.add (Nat.mul x0 (Nat.div x1 x0)) (Nat.modulo x1 x0)))) -> y0) = ((x1 = (Nat.add (Nat.mul x0 (Nat.div x1 x0)) (Nat.modulo x1 x0))) \/ y0)) (~ (x1 = x1)).
Definition term554 (x0 : nat) (x1 : nat) (x2 : nat) := ((~ (x0 = x0)) \/ (x1 = x2)) -> x1 = x2.
Definition term503 (x0 : nat) := ~ (~ (x0 = x0)).
Definition term79 (x0 : nat) (x1 : nat) := fun y0 : nat => ((Nat.add x0 x1) = (Nat.add x0 y0)) = (x1 = y0).
Definition term549 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))) -> (~ (x0 = x0)) \/ (x1 = x2).
Definition term617 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.div (Nat.div x0 x1) x2) x2.
Definition term391 (x0 : nat) (x1 : nat) := (fun y0 : Prop => forall y1 : Prop, y0 -> ((~ y0) \/ y1) -> y1) ((Nat.mul x1 x0) = (Nat.mul x0 x1)).
Definition term62 (x0 : nat) (x1 : nat) := (~ ((exists y0 : nat, (Nat.add y0 x0) = (Nat.add y0 x1)) -> x0 = x1)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Nat.add y0 y1) = (Nat.add y0 y2)) = (y1 = y2)) -> False.
Definition term214 (x0 : nat) := Nat.modulo x0 (NUMERAL 0).
Definition term352 (x0 : nat) (x1 : nat) := (fun y0 : Prop => ((x0 = (NUMERAL 0)) -> y0) = ((~ (x0 = (NUMERAL 0))) \/ y0)) ((x0 = x1) \/ (~ ((NUMERAL 0) = x1))).
Definition term290 (x0 : nat) := fun y0 : nat => ((y0 = (NUMERAL 0)) \/ (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0)))) /\ ((y0 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo x0 y0) y0)).
Definition term614 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x1 (Nat.mul (Nat.div x0 (Nat.mul x1 x2)) x2)) (Nat.mul x1 (Nat.modulo (Nat.div x0 x1) x2)).
Definition term7 (x0 : nat) := forall y0 : nat, (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0)) = x0.
Definition term2 (x0 : nat) := forall y0 : nat, (Nat.add (Nat.mul y0 (Nat.div x0 y0)) (Nat.modulo x0 y0)) = x0.
Definition term219 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.modulo x0 (Nat.mul x1 x2).
Definition term61 (x0 : nat) (x1 : nat) := ~ ((exists y0 : nat, (Nat.add y0 x0) = (Nat.add y0 x1)) -> x0 = x1).
Definition term64 (x0 : nat) (x1 : nat) := (((~ ((exists y0 : nat, (Nat.add y0 x0) = (Nat.add y0 x1)) -> x0 = x1)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Nat.add y0 y1) = (Nat.add y0 y2)) = (y1 = y2)) -> False) -> (~ ((exists y0 : nat, (Nat.add y0 x0) = (Nat.add y0 x1)) -> x0 = x1)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Nat.add y0 y1) = (Nat.add y0 y2)) = (y1 = y2)) -> False) -> (~ ((exists y0 : nat, (Nat.add y0 x0) = (Nat.add y0 x1)) -> x0 = x1)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Nat.add y0 y1) = (Nat.add y0 y2)) = (y1 = y2)) -> False.
Definition term11 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.div x0 (Nat.mul x1 x2).
Definition term370 (x0 : nat) (x1 : nat) := (~ ((NUMERAL 0) = x1)) \/ ((~ (x0 = (NUMERAL 0))) \/ (x0 = x1)).
Definition term299 (x0 : nat) (x1 : nat) := ~ ((x1 = (NUMERAL 0)) \/ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))).
Definition term624 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x1 (Nat.add (Nat.mul (Nat.div (Nat.div x0 x1) x2) x2) (Nat.modulo (Nat.div x0 x1) x2))).
Definition term374 (x0 : nat) (x1 : nat) := ((NUMERAL 0) = x1) -> ((~ ((NUMERAL 0) = x1)) \/ ((~ (x0 = (NUMERAL 0))) \/ (x0 = x1))) -> (~ (x0 = (NUMERAL 0))) \/ (x0 = x1).
Definition term545 (x0 : nat) (x1 : nat) := (fun y0 : Prop => forall y1 : Prop, (y0 \/ y1) -> (~ y0) -> y1) (x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))).
Definition term439 (x0 : nat) (x1 : nat) := (fun y0 : Prop => forall y1 : Prop, (y0 -> y1) = ((~ y0) \/ y1)) (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))).
Definition term434 (x0 : nat) (x1 : nat) := (fun y0 : Prop => forall y1 : Prop, ((~ y0) -> y1) = (y0 \/ y1)) (x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))).
Definition term378 (x0 : nat) (x1 : nat) := (fun y0 : Prop => forall y1 : Prop, ((x1 = (NUMERAL 0)) \/ y0) -> ((~ (x1 = (NUMERAL 0))) \/ y1) -> y0 \/ y1) (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))).
Definition term621 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul (Nat.div (Nat.div x0 x1) x2) x2) (Nat.modulo (Nat.div x0 x1) x2).
Definition term490 (x0 : nat) := ~ (x0 = x0).
Definition term343 (x0 : nat) := ~ ((NUMERAL 0) = x0).
Definition term29 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.add (Nat.mul x0 x1) (Nat.mul x0 y0)) = (Nat.mul x0 (Nat.add x1 y0)).
Definition term590 (x0 : nat) (x1 : nat) := (fun y0 : Prop => ((x0 = (NUMERAL 0)) \/ y0) -> (~ (x0 = (NUMERAL 0))) -> y0) (~ (x0 = x1)).
Definition term58 (x0 : Prop) := (~ x0) -> False.
Definition term168 := (forall y0 : nat, (fun y1 : nat => forall y2 : nat, forall y3 : nat, ((Nat.add y1 y2) = (Nat.add y1 y3)) \/ (~ (y2 = y3))) y0) /\ (forall y0 : nat, (fun y1 : nat => forall y2 : nat, forall y3 : nat, (~ ((Nat.add y1 y2) = (Nat.add y1 y3))) \/ (y2 = y3)) y0).
Definition term146 (x0 : nat) := (forall y0 : nat, (fun y1 : nat => forall y2 : nat, ((Nat.add x0 y1) = (Nat.add x0 y2)) \/ (~ (y1 = y2))) y0) /\ (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ ((Nat.add x0 y1) = (Nat.add x0 y2))) \/ (y1 = y2)) y0).
Definition term121 (x0 : nat) (x1 : nat) := (forall y0 : nat, (fun y1 : nat => ((Nat.add x0 x1) = (Nat.add x0 y1)) \/ (~ (x1 = y1))) y0) /\ (forall y0 : nat, (fun y1 : nat => (~ ((Nat.add x0 x1) = (Nat.add x0 y1))) \/ (x1 = y1)) y0).
Definition term577 (x0 : nat) (x1 : nat) := (~ (x1 = x0)) \/ (x1 = (NUMERAL 0)).
Definition term298 (x0 : nat) (x1 : nat) := (x1 = (NUMERAL 0)) \/ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))).
Definition term186 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Nat.add y0 y1) = (Nat.add y0 y2)) \/ (~ (y1 = y2))) /\ (forall y0 : nat, forall y1 : nat, forall y2 : nat, (~ ((Nat.add y0 y1) = (Nat.add y0 y2))) \/ (y1 = y2)).
Definition term164 (x0 : nat) := (forall y0 : nat, forall y1 : nat, ((Nat.add x0 y0) = (Nat.add x0 y1)) \/ (~ (y0 = y1))) /\ (forall y0 : nat, forall y1 : nat, (~ ((Nat.add x0 y0) = (Nat.add x0 y1))) \/ (y0 = y1)).
Definition term539 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))) \/ ((~ (x0 = x0)) \/ (x1 = x2))).
Definition term291 (x0 : nat) := forall y0 : nat, ((y0 = (NUMERAL 0)) \/ (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0)))) /\ ((y0 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo x0 y0) y0)).
Definition term111 (x0 : nat) (x1 : nat) := forall y0 : nat, (((Nat.add x0 x1) = (Nat.add x0 y0)) \/ (~ (x1 = y0))) /\ ((~ ((Nat.add x0 x1) = (Nat.add x0 y0))) \/ (x1 = y0)).
Definition term481 (x0 : nat) (x1 : nat) := (~ (x1 = (Nat.add (Nat.mul x0 (Nat.div x1 x0)) (Nat.modulo x1 x0)))) \/ ((Nat.add (Nat.mul x0 (Nat.div x1 x0)) (Nat.modulo x1 x0)) = x1).
Definition term313 (a0 : Type') (x0 : a0) (x1 : a0) := (fun y0 : Prop => forall y1 : Prop, (y0 -> y1) = ((~ y0) \/ y1)) (x0 = x1).
Definition term597 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (~ (x1 = (NUMERAL 0))) -> (y0 = (NUMERAL 0)) -> (~ (x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))) -> (forall y1 : nat, forall y2 : nat, (Nat.mul y1 y2) = (Nat.mul y2 y1)) -> (forall y1 : nat, forall y2 : nat, (~ (y2 = (NUMERAL 0))) -> (y1 = (Nat.add (Nat.mul (Nat.div y1 y2) y2) (Nat.modulo y1 y2))) /\ (Peano.lt (Nat.modulo y1 y2) y2)) -> False) x2.
Definition term300 (x0 : nat) (x1 : nat) := ~ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))).
Definition term239 (x0 : nat) (x1 : nat) := ~ (x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))).
Definition term216 (x0 : nat) := (fun y0 : nat => (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) x0.
Definition term165 := fun y0 : nat => (forall y1 : nat, forall y2 : nat, ((Nat.add y0 y1) = (Nat.add y0 y2)) \/ (~ (y1 = y2))) /\ (forall y1 : nat, forall y2 : nat, (~ ((Nat.add y0 y1) = (Nat.add y0 y2))) \/ (y1 = y2)).
Definition term80 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Nat.add x0 x1) = (Nat.add x0 y0)) = (x1 = y0).
Definition term105 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.add x0 x1) = (Nat.add x0 x2)) /\ (~ (x1 = x2)).
Definition term140 (x0 : nat) (x1 : nat) := forall y0 : nat, (fun y1 : nat => (~ ((Nat.add x0 x1) = (Nat.add x0 y1))) \/ (x1 = y1)) y0.
Definition term135 (x0 : nat) (x1 : nat) := forall y0 : nat, (fun y1 : nat => ((Nat.add x0 x1) = (Nat.add x0 y1)) \/ (~ (x1 = y1))) y0.
Definition term530 (x0 : nat) (x1 : nat) (x2 : nat) := ((~ ((Nat.add (Nat.mul x2 (Nat.div x1 x2)) (Nat.modulo x1 x2)) = x1)) \/ ((~ (x1 = x1)) \/ (x1 = (Nat.add (Nat.mul x2 (Nat.div x1 x2)) (Nat.modulo x1 x2))))) -> (x2 = x0) \/ ((~ (x1 = x1)) \/ (x1 = (Nat.add (Nat.mul x2 (Nat.div x1 x2)) (Nat.modulo x1 x2)))).
Definition term609 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul (Nat.div x1 (Nat.mul x2 x0)) (Nat.mul x2 x0)) (Nat.add (Nat.mul x2 (Nat.modulo (Nat.div x1 x2) x0)) (Nat.modulo x1 x2)).
Definition term411 (x0 : nat) (x1 : nat) := ~ ((Nat.mul (Nat.div x0 x1) x1) = (Nat.mul x1 (Nat.div x0 x1))).
Definition term380 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : Prop => ((x1 = (NUMERAL 0)) \/ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) -> ((~ (x1 = (NUMERAL 0))) \/ y0) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) \/ y0) (x1 = x2).
Definition term515 (x0 : nat) (x1 : nat) (x2 : nat) := ((~ ((x1 = x0) \/ ((Nat.add (Nat.mul x1 (Nat.div x2 x1)) (Nat.modulo x2 x1)) = x2))) -> ~ (((Nat.add (Nat.mul x1 (Nat.div x2 x1)) (Nat.modulo x2 x1)) = x2) \/ (x1 = x0))) /\ ((~ (((Nat.add (Nat.mul x1 (Nat.div x2 x1)) (Nat.modulo x2 x1)) = x2) \/ (x1 = x0))) -> ~ ((x1 = x0) \/ ((Nat.add (Nat.mul x1 (Nat.div x2 x1)) (Nat.modulo x2 x1)) = x2))).
Definition term388 (x0 : nat) (x1 : nat) (x2 : nat) := ((~ ((x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) \/ (x1 = x2))) -> ~ ((x1 = x2) \/ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))))) /\ ((~ ((x1 = x2) \/ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))))) -> ~ ((x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) \/ (x1 = x2))).
Definition term10 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.div (Nat.div x0 x1) x2.
Definition term193 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term118 (x0 : nat -> Prop) (x1 : nat -> Prop) := forall y0 : nat, (x0 y0) /\ (x1 y0).
Definition term478 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((x1 = x2) \/ (x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))))) -> ~ ((x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))) \/ (x1 = x2)).
Definition term386 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((x1 = x2) \/ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))))) -> ~ ((x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) \/ (x1 = x2)).
Definition term241 (x0 : nat) (x1 : nat) (x2 : nat) := ((~ (x2 = (NUMERAL 0))) -> (x0 = (NUMERAL 0)) -> (~ (x1 = (Nat.add (Nat.mul x2 (Nat.div x1 x2)) (Nat.modulo x1 x2)))) -> (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False) -> (~ (x2 = (NUMERAL 0))) -> (x0 = (NUMERAL 0)) -> (~ (x1 = (Nat.add (Nat.mul x2 (Nat.div x1 x2)) (Nat.modulo x1 x2)))) -> (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False.
Definition term446 (x0 : nat) (x1 : nat) := ~ (~ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))).
Definition term415 (x0 : nat) (x1 : nat) := ~ (~ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))).
Definition term40 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.div x0 (Nat.mul x1 y0)) = (Nat.div (Nat.div x0 x1) y0)) x2.
Definition term532 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((x2 = x0) \/ ((~ (x1 = x1)) \/ (x1 = (Nat.add (Nat.mul x2 (Nat.div x1 x2)) (Nat.modulo x1 x2))))).
Definition term230 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x2 (Nat.modulo (Nat.div x1 x2) x0)) (Nat.modulo x1 x2).
Definition term537 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = x0)) \/ ((x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))) \/ (x1 = x2)).
Definition term143 (x0 : nat) := fun y0 : nat => (forall y1 : nat, ((Nat.add x0 y0) = (Nat.add x0 y1)) \/ (~ (y0 = y1))) /\ (forall y1 : nat, (~ ((Nat.add x0 y0) = (Nat.add x0 y1))) \/ (y0 = y1)).
Definition term245 := ~ (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term67 := ~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Nat.add y0 y1) = (Nat.add y0 y2)) = (y1 = y2)).
Definition term213 (x0 : nat) := (fun y0 : nat => (Nat.modulo y0 (NUMERAL 0)) = y0) x0.
Definition term47 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.add x0 x1) x2.
Definition term279 (x0 : nat) (x1 : nat) := (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1).
Definition term465 (x0 : nat) (x1 : nat) := ((~ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))) \/ ((~ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) \/ (x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))))) -> (~ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) \/ (x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))).
Definition term345 (x0 : nat) (x1 : nat) := (fun y0 : Prop => forall y1 : Prop, ((~ y0) -> y1) = (y0 \/ y1)) (x0 = x1).
Definition term235 (x0 : nat) (x1 : nat) := Nat.modulo (Nat.div x0 x1) (NUMERAL 0).
Definition term96 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.add y0 x0) = (Nat.add y0 x1)) x2.
Definition term570 (x0 : nat) (x1 : nat) := (~ ((NUMERAL 0) = x0)) \/ (x1 = (NUMERAL 0)).
Definition term473 (x0 : nat) (x1 : nat) (x2 : nat) := ((~ (x1 = (Nat.add (Nat.mul (Nat.div x1 x2) x2) (Nat.modulo x1 x2)))) \/ (x1 = (Nat.add (Nat.mul x2 (Nat.div x1 x2)) (Nat.modulo x1 x2)))) -> (x2 = x0) \/ (x1 = (Nat.add (Nat.mul x2 (Nat.div x1 x2)) (Nat.modulo x1 x2))).
Definition term50 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.add (Nat.mul x0 x1) (Nat.mul x0 y0)) = (Nat.mul x0 (Nat.add x1 y0))) x2.
Definition term201 (x0 : nat) (x1 : nat) := (x0 = x1) -> False.
Definition term237 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x1 (Nat.div x0 x1)).
Definition term432 (x0 : nat) (x1 : nat) := ((~ ((Nat.mul (Nat.div x0 x1) x1) = (Nat.mul x1 (Nat.div x0 x1)))) \/ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))) -> (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)).
Definition term200 (x0 : nat) (x1 : nat) := (~ (x0 = x1)) -> x0 = x1.
Definition term189 (x0 : Prop) := (~ x0) -> x0.
Definition term576 (x0 : nat) (x1 : nat) := ~ ((~ ((NUMERAL 0) = x0)) \/ ((~ (x1 = x0)) \/ (x1 = (NUMERAL 0)))).
Definition term569 (x0 : nat) (x1 : nat) := ~ ((~ (x1 = x0)) \/ ((~ ((NUMERAL 0) = x0)) \/ (x1 = (NUMERAL 0)))).
Definition term297 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((y0 = (NUMERAL 0)) \/ (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0)))) /\ ((y0 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo x0 y0) y0))) x1.
Definition term284 (x0 : nat) := fun y0 : nat => (y0 = (NUMERAL 0)) \/ ((x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0)).
Definition term540 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = x0)) \/ (x1 = x2).
Definition term256 (x0 : nat) := imp (~ (x0 = (NUMERAL 0))).
Definition term240 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x2 = (NUMERAL 0))) -> (x0 = (NUMERAL 0)) -> (~ (x1 = (Nat.add (Nat.mul x2 (Nat.div x1 x2)) (Nat.modulo x1 x2)))) -> (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False.
Definition term259 (x0 : nat) (x1 : nat) := fun y0 : nat => (~ (x1 = (NUMERAL 0))) -> (y0 = (NUMERAL 0)) -> (~ (x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))) -> (forall y1 : nat, forall y2 : nat, (Nat.mul y1 y2) = (Nat.mul y2 y1)) -> ~ (forall y1 : nat, forall y2 : nat, (~ (y2 = (NUMERAL 0))) -> (y1 = (Nat.add (Nat.mul (Nat.div y1 y2) y2) (Nat.modulo y1 y2))) /\ (Peano.lt (Nat.modulo y1 y2) y2)).
Definition term258 (x0 : nat) (x1 : nat) := fun y0 : nat => (~ (x1 = (NUMERAL 0))) -> (y0 = (NUMERAL 0)) -> (~ (x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))) -> (forall y1 : nat, forall y2 : nat, (Nat.mul y1 y2) = (Nat.mul y2 y1)) -> (forall y1 : nat, forall y2 : nat, (~ (y2 = (NUMERAL 0))) -> (y1 = (Nat.add (Nat.mul (Nat.div y1 y2) y2) (Nat.modulo y1 y2))) /\ (Peano.lt (Nat.modulo y1 y2) y2)) -> False.
Definition term130 (x0 : nat) (x1 : nat) (x2 : nat) := ((fun y0 : nat => ((Nat.add x0 x1) = (Nat.add x0 y0)) \/ (~ (x1 = y0))) x2) /\ ((fun y0 : nat => (~ ((Nat.add x0 x1) = (Nat.add x0 y0))) \/ (x1 = y0)) x2).
Definition term12 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.div (Nat.div x0 x1) y0) = (Nat.div x0 (Nat.mul x1 y0)).
Definition term547 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : Prop => ((x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))) \/ y0) -> (~ (x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))) -> y0) ((~ (x0 = x0)) \/ (x1 = x2)).
Definition term404 (x0 : nat) (x1 : nat) := ((Nat.mul (Nat.div x0 x1) x1) = (Nat.mul x1 (Nat.div x0 x1))) -> (~ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) \/ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))).
Definition term589 (x0 : nat) := forall y0 : Prop, ((x0 = (NUMERAL 0)) \/ y0) -> (~ (x0 = (NUMERAL 0))) -> y0.
Definition term551 (x0 : nat) := forall y0 : Prop, (x0 = x0) -> ((~ (x0 = x0)) \/ y0) -> y0.
Definition term546 (x0 : nat) (x1 : nat) := forall y0 : Prop, ((x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))) \/ y0) -> (~ (x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))) -> y0.
Definition term372 (x0 : nat) := forall y0 : Prop, ((NUMERAL 0) = x0) -> ((~ ((NUMERAL 0) = x0)) \/ y0) -> y0.
Definition term331 (a0 : Type') (x0 : a0) := forall y0 : Prop, (x0 = x0) -> ((~ (x0 = x0)) \/ y0) -> y0.
Definition term305 (x0 : nat) (x1 : nat) := (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) \/ (x1 = (NUMERAL 0)).
Definition term6 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)) = y0) x0.
Definition term1 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add (Nat.mul y1 (Nat.div y0 y1)) (Nat.modulo y0 y1)) = y0) x0.
Definition term444 (x0 : nat) (x1 : nat) := ~ ((x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))) \/ (~ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))))).
Definition term533 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((~ (x0 = x0)) \/ ((x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))) \/ (x1 = x2))).
Definition term455 (x0 : nat) (x1 : nat) := ~ ((~ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))) \/ ((~ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) \/ (x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))))).
Definition term448 (x0 : nat) (x1 : nat) := ~ ((~ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) \/ ((~ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))) \/ (x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))))).
Definition term99 (x0 : nat) (x1 : nat) := and (exists y0 : nat, (fun y1 : nat => (Nat.add y1 x0) = (Nat.add y1 x1)) y0).
Definition term274 (x0 : nat) := fun y0 : nat => (Nat.mul x0 y0) = (Nat.mul y0 x0).
Definition term397 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul (Nat.div x0 x1) x1).
Definition term86 (x0 : nat) (x1 : nat) := imp (exists y0 : nat, (Nat.add y0 x0) = (Nat.add y0 x1)).
Definition term177 := @eq Prop (forall y0 : nat, (forall y1 : nat, forall y2 : nat, ((Nat.add y0 y1) = (Nat.add y0 y2)) \/ (~ (y1 = y2))) /\ (forall y1 : nat, forall y2 : nat, (~ ((Nat.add y0 y1) = (Nat.add y0 y2))) \/ (y1 = y2))).
Definition term176 := @eq Prop (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, forall y3 : nat, ((Nat.add y1 y2) = (Nat.add y1 y3)) \/ (~ (y2 = y3))) y0) /\ ((fun y1 : nat => forall y2 : nat, forall y3 : nat, (~ ((Nat.add y1 y2) = (Nat.add y1 y3))) \/ (y2 = y3)) y0)).
Definition term155 (x0 : nat) := @eq Prop (forall y0 : nat, (forall y1 : nat, ((Nat.add x0 y0) = (Nat.add x0 y1)) \/ (~ (y0 = y1))) /\ (forall y1 : nat, (~ ((Nat.add x0 y0) = (Nat.add x0 y1))) \/ (y0 = y1))).
Definition term154 (x0 : nat) := @eq Prop (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Nat.add x0 y1) = (Nat.add x0 y2)) \/ (~ (y1 = y2))) y0) /\ ((fun y1 : nat => forall y2 : nat, (~ ((Nat.add x0 y1) = (Nat.add x0 y2))) \/ (y1 = y2)) y0)).
Definition term133 (x0 : nat) (x1 : nat) := @eq Prop (forall y0 : nat, (((Nat.add x0 x1) = (Nat.add x0 y0)) \/ (~ (x1 = y0))) /\ ((~ ((Nat.add x0 x1) = (Nat.add x0 y0))) \/ (x1 = y0))).
Definition term132 (x0 : nat) (x1 : nat) := @eq Prop (forall y0 : nat, ((fun y1 : nat => ((Nat.add x0 x1) = (Nat.add x0 y1)) \/ (~ (x1 = y1))) y0) /\ ((fun y1 : nat => (~ ((Nat.add x0 x1) = (Nat.add x0 y1))) \/ (x1 = y1)) y0)).
Definition term44 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.add x0 (Nat.add x1 y0)) = (Nat.add (Nat.add x0 x1) y0).
Definition term15 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.div x0 (Nat.mul x1 y0)) = (Nat.div (Nat.div x0 x1) y0).
Definition term506 (x0 : nat) (x1 : nat) := (~ ((Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)) = x0)) \/ (x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))).
Definition term498 (x0 : nat) (x1 : nat) := (~ ((Nat.add (Nat.mul x0 (Nat.div x1 x0)) (Nat.modulo x1 x0)) = x1)) \/ ((x1 = (Nat.add (Nat.mul x0 (Nat.div x1 x0)) (Nat.modulo x1 x0))) \/ (~ (x1 = x1))).
Definition term187 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((Nat.add x1 x0) = (Nat.add x1 x2))) -> (Nat.add x1 x0) = (Nat.add x1 x2).
Definition term117 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term248 := (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False.
Definition term431 (x0 : nat) (x1 : nat) := ((Nat.mul (Nat.div x0 x1) x1) = (Nat.mul x1 (Nat.div x0 x1))) -> ((~ ((Nat.mul (Nat.div x0 x1) x1) = (Nat.mul x1 (Nat.div x0 x1)))) \/ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))) -> (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)).
Definition term418 (x0 : nat) (x1 : nat) := (~ ((Nat.mul (Nat.div x0 x1) x1) = (Nat.mul x1 (Nat.div x0 x1)))) \/ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))).
Definition term403 (x0 : nat) (x1 : nat) := (~ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) \/ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))).
Definition term596 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (~ (x0 = (NUMERAL 0))) -> (y1 = (NUMERAL 0)) -> (~ (y0 = (Nat.add (Nat.mul x0 (Nat.div y0 x0)) (Nat.modulo y0 x0)))) -> (forall y2 : nat, forall y3 : nat, (Nat.mul y2 y3) = (Nat.mul y3 y2)) -> (forall y2 : nat, forall y3 : nat, (~ (y3 = (NUMERAL 0))) -> (y2 = (Nat.add (Nat.mul (Nat.div y2 y3) y3) (Nat.modulo y2 y3))) /\ (Peano.lt (Nat.modulo y2 y3) y3)) -> False) x1.
Definition term151 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (~ ((Nat.add x0 y0) = (Nat.add x0 y1))) \/ (y0 = y1)) x1.
Definition term149 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.add x0 y0) = (Nat.add x0 y1)) \/ (~ (y0 = y1))) x1.
Definition term56 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.div (Nat.div x0 y0) y1) = (Nat.div x0 (Nat.mul y0 y1))) x1.
Definition term49 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y1)) = (Nat.mul x0 (Nat.add y0 y1))) x1.
Definition term43 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add x0 (Nat.add y0 y1)) = (Nat.add (Nat.add x0 y0) y1)) x1.
Definition term39 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.div x0 (Nat.mul y0 y1)) = (Nat.div (Nat.div x0 y0) y1)) x1.
Definition term13 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.div x0 (Nat.mul x1 y0)) = (Nat.div (Nat.div x0 x1) y0).
Definition term106 (x0 : nat) (x1 : nat) := fun y0 : nat => ((fun y1 : nat => (Nat.add y1 x0) = (Nat.add y1 x1)) y0) /\ (~ (x0 = x1)).
Definition term398 (x0 : nat) (x1 : nat) := @eq nat (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)).
Definition term375 (x0 : nat) (x1 : nat) := ((~ ((NUMERAL 0) = x1)) \/ ((~ (x0 = (NUMERAL 0))) \/ (x0 = x1))) -> (~ (x0 = (NUMERAL 0))) \/ (x0 = x1).
Definition term512 (x0 : nat) (x1 : nat) (x2 : nat) := ~ (((Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)) = x0) \/ (x1 = x2)).
Definition term581 (x0 : nat) (x1 : nat) := (~ ((NUMERAL 0) = x0)) \/ ((~ (x1 = x0)) \/ (x1 = (NUMERAL 0))).
Definition term476 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))) \/ (x1 = x2)).
Definition term384 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) \/ (x1 = x2)).
Definition term402 (x0 : nat) (x1 : nat) := (fun y0 : Prop => (((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) -> y0) = ((~ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) \/ y0)) ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))).
Definition term209 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term341 (x0 : nat) := ((~ (x0 = (NUMERAL 0))) \/ ((NUMERAL 0) = x0)) -> (NUMERAL 0) = x0.
Definition term276 := fun y0 : nat => forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0).
Definition term148 (x0 : nat) := fun y0 : nat => forall y1 : nat, (~ ((Nat.add x0 y0) = (Nat.add x0 y1))) \/ (y0 = y1).
Definition term81 (x0 : nat) := fun y0 : nat => forall y1 : nat, ((Nat.add x0 y0) = (Nat.add x0 y1)) = (y0 = y1).
Definition term17 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Nat.div x0 (Nat.mul y0 y1)) = (Nat.div (Nat.div x0 y0) y1).
Definition term355 (x0 : nat) (x1 : nat) := ~ ((x0 = x1) \/ (~ ((NUMERAL 0) = x1))).
Definition term282 (x0 : nat) (x1 : nat) := (~ (~ (x1 = (NUMERAL 0)))) \/ ((x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1)).
Definition term72 (x0 : nat) := fun y0 : nat => (~ ((exists y1 : nat, (Nat.add y1 y0) = (Nat.add y1 x0)) -> y0 = x0)) -> ~ (forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Nat.add y1 y2) = (Nat.add y1 y3)) = (y2 = y3)).
Definition term486 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : Prop => ((x2 = (Nat.add (Nat.mul x1 (Nat.div x2 x1)) (Nat.modulo x2 x1))) \/ (x1 = x0)) -> ((~ (x2 = (Nat.add (Nat.mul x1 (Nat.div x2 x1)) (Nat.modulo x2 x1)))) \/ y0) -> (x1 = x0) \/ y0) ((Nat.add (Nat.mul x1 (Nat.div x2 x1)) (Nat.modulo x2 x1)) = x2).
Definition term4 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1).
Definition term101 (x0 : nat) (x1 : nat) := @eq Prop ((exists y0 : nat, (Nat.add y0 x0) = (Nat.add y0 x1)) /\ (~ (x0 = x1))).
Definition term100 (x0 : nat) (x1 : nat) := @eq Prop ((exists y0 : nat, (fun y1 : nat => (Nat.add y1 x0) = (Nat.add y1 x1)) y0) /\ (~ (x0 = x1))).
Definition term364 (x0 : nat) (x1 : nat) := ~ ((~ (x0 = (NUMERAL 0))) \/ (x0 = x1)).
Definition term436 (x0 : nat) (x1 : nat) := (fun y0 : Prop => ((~ (x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))) -> y0) = ((x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))) \/ y0)) (~ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))).
Definition term586 (x0 : nat) (x1 : nat) := (~ ((~ (x0 = x1)) \/ (x0 = (NUMERAL 0)))) -> ~ ((x0 = (NUMERAL 0)) \/ (~ (x0 = x1))).
Definition term491 (x0 : nat) (x1 : nat) := (~ (x1 = (Nat.add (Nat.mul x0 (Nat.div x1 x0)) (Nat.modulo x1 x0)))) -> ~ (x1 = x1).
Definition term396 (x0 : nat) (x1 : nat) := Nat.mul (Nat.div x0 x1) x1.
Definition term417 (x0 : nat) (x1 : nat) := ~ ((~ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) \/ ((~ ((Nat.mul (Nat.div x0 x1) x1) = (Nat.mul x1 (Nat.div x0 x1)))) \/ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))))).
Definition term409 (x0 : nat) (x1 : nat) := ~ ((~ ((Nat.mul (Nat.div x0 x1) x1) = (Nat.mul x1 (Nat.div x0 x1)))) \/ ((~ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) \/ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))))).
Definition term593 (x0 : nat) (x1 : nat) := (x0 = x1) -> (~ (x0 = x1)) -> False.
Definition term253 (x0 : nat) := imp (x0 = (NUMERAL 0)).
Definition term562 (x0 : nat) := forall y0 : Prop, (((NUMERAL 0) = x0) -> y0) = ((~ ((NUMERAL 0) = x0)) \/ y0).
Definition term557 (x0 : nat) := forall y0 : Prop, ((~ (x0 = (NUMERAL 0))) -> y0) = ((x0 = (NUMERAL 0)) \/ y0).
Definition term496 (x0 : nat) (x1 : nat) := forall y0 : Prop, (((Nat.add (Nat.mul x0 (Nat.div x1 x0)) (Nat.modulo x1 x0)) = x1) -> y0) = ((~ ((Nat.add (Nat.mul x0 (Nat.div x1 x0)) (Nat.modulo x1 x0)) = x1)) \/ y0).
Definition term440 (x0 : nat) (x1 : nat) := forall y0 : Prop, ((x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) -> y0) = ((~ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) \/ y0).
Definition term435 (x0 : nat) (x1 : nat) := forall y0 : Prop, ((~ (x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))) -> y0) = ((x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))) \/ y0).
Definition term406 (x0 : nat) (x1 : nat) := forall y0 : Prop, (((Nat.mul (Nat.div x0 x1) x1) = (Nat.mul x1 (Nat.div x0 x1))) -> y0) = ((~ ((Nat.mul (Nat.div x0 x1) x1) = (Nat.mul x1 (Nat.div x0 x1)))) \/ y0).
Definition term401 (x0 : nat) (x1 : nat) := forall y0 : Prop, (((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) -> y0) = ((~ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) \/ y0).
Definition term351 (x0 : nat) := forall y0 : Prop, ((x0 = (NUMERAL 0)) -> y0) = ((~ (x0 = (NUMERAL 0))) \/ y0).
Definition term346 (x0 : nat) (x1 : nat) := forall y0 : Prop, ((~ (x0 = x1)) -> y0) = ((x0 = x1) \/ y0).
Definition term314 (a0 : Type') (x0 : a0) (x1 : a0) := forall y0 : Prop, ((x0 = x1) -> y0) = ((~ (x0 = x1)) \/ y0).
Definition term309 (a0 : Type') (x0 : a0) := forall y0 : Prop, ((x0 = x0) -> y0) = ((~ (x0 = x0)) \/ y0).
Definition term565 (x0 : nat) (x1 : nat) := ~ ((~ ((NUMERAL 0) = x1)) \/ ((x0 = (NUMERAL 0)) \/ (~ (x0 = x1)))).
Definition term499 (x0 : nat) (x1 : nat) := ~ ((~ ((Nat.add (Nat.mul x0 (Nat.div x1 x0)) (Nat.modulo x1 x0)) = x1)) \/ ((x1 = (Nat.add (Nat.mul x0 (Nat.div x1 x0)) (Nat.modulo x1 x0))) \/ (~ (x1 = x1)))).
Definition term226 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x1 (Nat.modulo (Nat.div x0 x1) x2).
Definition term301 (x0 : nat) (x1 : nat) := ~ ((x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) \/ (x1 = (NUMERAL 0))).
Definition term518 (x0 : nat) (x1 : nat) := ~ ((~ ((Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)) = x0)) \/ ((~ (x0 = x0)) \/ (x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))))).
Definition term505 (x0 : nat) (x1 : nat) := ~ ((~ (x0 = x0)) \/ ((~ ((Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)) = x0)) \/ (x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))))).
Definition term513 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (((Nat.add (Nat.mul x1 (Nat.div x2 x1)) (Nat.modulo x2 x1)) = x2) \/ (x1 = x0))) -> ~ ((x1 = x0) \/ ((Nat.add (Nat.mul x1 (Nat.div x2 x1)) (Nat.modulo x2 x1)) = x2)).
Definition term587 (x0 : nat) (x1 : nat) := ((~ ((~ (x1 = x0)) \/ (x1 = (NUMERAL 0)))) -> ~ ((x1 = (NUMERAL 0)) \/ (~ (x1 = x0)))) /\ ((~ ((x1 = (NUMERAL 0)) \/ (~ (x1 = x0)))) -> ~ ((~ (x1 = x0)) \/ (x1 = (NUMERAL 0)))).
Definition term580 (x0 : nat) (x1 : nat) := ((~ ((~ (x1 = x0)) \/ ((~ ((NUMERAL 0) = x0)) \/ (x1 = (NUMERAL 0))))) -> ~ ((~ ((NUMERAL 0) = x0)) \/ ((~ (x1 = x0)) \/ (x1 = (NUMERAL 0))))) /\ ((~ ((~ ((NUMERAL 0) = x0)) \/ ((~ (x1 = x0)) \/ (x1 = (NUMERAL 0))))) -> ~ ((~ (x1 = x0)) \/ ((~ ((NUMERAL 0) = x0)) \/ (x1 = (NUMERAL 0))))).
Definition term573 (x0 : nat) (x1 : nat) := ((~ ((~ ((NUMERAL 0) = x1)) \/ ((x0 = (NUMERAL 0)) \/ (~ (x0 = x1))))) -> ~ ((~ (x0 = x1)) \/ ((~ ((NUMERAL 0) = x1)) \/ (x0 = (NUMERAL 0))))) /\ ((~ ((~ (x0 = x1)) \/ ((~ ((NUMERAL 0) = x1)) \/ (x0 = (NUMERAL 0))))) -> ~ ((~ ((NUMERAL 0) = x1)) \/ ((x0 = (NUMERAL 0)) \/ (~ (x0 = x1))))).
Definition term543 (x0 : nat) (x1 : nat) (x2 : nat) := ((~ ((~ (x0 = x0)) \/ ((x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))) \/ (x1 = x2)))) -> ~ ((x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))) \/ ((~ (x0 = x0)) \/ (x1 = x2)))) /\ ((~ ((x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))) \/ ((~ (x0 = x0)) \/ (x1 = x2)))) -> ~ ((~ (x0 = x0)) \/ ((x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))) \/ (x1 = x2)))).
Definition term536 (x0 : nat) (x1 : nat) (x2 : nat) := ((~ ((x2 = x0) \/ ((~ (x1 = x1)) \/ (x1 = (Nat.add (Nat.mul x2 (Nat.div x1 x2)) (Nat.modulo x1 x2)))))) -> ~ ((~ (x1 = x1)) \/ ((x1 = (Nat.add (Nat.mul x2 (Nat.div x1 x2)) (Nat.modulo x1 x2))) \/ (x2 = x0)))) /\ ((~ ((~ (x1 = x1)) \/ ((x1 = (Nat.add (Nat.mul x2 (Nat.div x1 x2)) (Nat.modulo x1 x2))) \/ (x2 = x0)))) -> ~ ((x2 = x0) \/ ((~ (x1 = x1)) \/ (x1 = (Nat.add (Nat.mul x2 (Nat.div x1 x2)) (Nat.modulo x1 x2)))))).
Definition term522 (x0 : nat) (x1 : nat) := ((~ ((~ (x0 = x0)) \/ ((~ ((Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)) = x0)) \/ (x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))))) -> ~ ((~ ((Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)) = x0)) \/ ((~ (x0 = x0)) \/ (x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))))) /\ ((~ ((~ ((Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)) = x0)) \/ ((~ (x0 = x0)) \/ (x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))))) -> ~ ((~ (x0 = x0)) \/ ((~ ((Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)) = x0)) \/ (x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))))).
Definition term509 (x0 : nat) (x1 : nat) := ((~ ((~ ((Nat.add (Nat.mul x0 (Nat.div x1 x0)) (Nat.modulo x1 x0)) = x1)) \/ ((x1 = (Nat.add (Nat.mul x0 (Nat.div x1 x0)) (Nat.modulo x1 x0))) \/ (~ (x1 = x1))))) -> ~ ((~ (x1 = x1)) \/ ((~ ((Nat.add (Nat.mul x0 (Nat.div x1 x0)) (Nat.modulo x1 x0)) = x1)) \/ (x1 = (Nat.add (Nat.mul x0 (Nat.div x1 x0)) (Nat.modulo x1 x0)))))) /\ ((~ ((~ (x1 = x1)) \/ ((~ ((Nat.add (Nat.mul x0 (Nat.div x1 x0)) (Nat.modulo x1 x0)) = x1)) \/ (x1 = (Nat.add (Nat.mul x0 (Nat.div x1 x0)) (Nat.modulo x1 x0)))))) -> ~ ((~ ((Nat.add (Nat.mul x0 (Nat.div x1 x0)) (Nat.modulo x1 x0)) = x1)) \/ ((x1 = (Nat.add (Nat.mul x0 (Nat.div x1 x0)) (Nat.modulo x1 x0))) \/ (~ (x1 = x1))))).
Definition term479 (x0 : nat) (x1 : nat) (x2 : nat) := ((~ ((x2 = x0) \/ (x1 = (Nat.add (Nat.mul x2 (Nat.div x1 x2)) (Nat.modulo x1 x2))))) -> ~ ((x1 = (Nat.add (Nat.mul x2 (Nat.div x1 x2)) (Nat.modulo x1 x2))) \/ (x2 = x0))) /\ ((~ ((x1 = (Nat.add (Nat.mul x2 (Nat.div x1 x2)) (Nat.modulo x1 x2))) \/ (x2 = x0))) -> ~ ((x2 = x0) \/ (x1 = (Nat.add (Nat.mul x2 (Nat.div x1 x2)) (Nat.modulo x1 x2))))).
Definition term466 (x0 : nat) (x1 : nat) (x2 : nat) := ((~ ((x2 = x0) \/ (x1 = (Nat.add (Nat.mul (Nat.div x1 x2) x2) (Nat.modulo x1 x2))))) -> ~ ((x1 = (Nat.add (Nat.mul (Nat.div x1 x2) x2) (Nat.modulo x1 x2))) \/ (x2 = x0))) /\ ((~ ((x1 = (Nat.add (Nat.mul (Nat.div x1 x2) x2) (Nat.modulo x1 x2))) \/ (x2 = x0))) -> ~ ((x2 = x0) \/ (x1 = (Nat.add (Nat.mul (Nat.div x1 x2) x2) (Nat.modulo x1 x2))))).
Definition term459 (x0 : nat) (x1 : nat) := ((~ ((~ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) \/ ((~ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))) \/ (x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))))) -> ~ ((~ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))) \/ ((~ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) \/ (x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))))) /\ ((~ ((~ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))) \/ ((~ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) \/ (x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))))) -> ~ ((~ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) \/ ((~ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))) \/ (x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))))).
Definition term452 (x0 : nat) (x1 : nat) := ((~ ((~ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) \/ ((x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))) \/ (~ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))))))) -> ~ ((~ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) \/ ((~ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))) \/ (x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))))) /\ ((~ ((~ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) \/ ((~ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))) \/ (x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))))) -> ~ ((~ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) \/ ((x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))) \/ (~ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))))))).
Definition term421 (x0 : nat) (x1 : nat) := ((~ ((~ ((Nat.mul (Nat.div x0 x1) x1) = (Nat.mul x1 (Nat.div x0 x1)))) \/ ((~ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) \/ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))))) -> ~ ((~ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) \/ ((~ ((Nat.mul (Nat.div x0 x1) x1) = (Nat.mul x1 (Nat.div x0 x1)))) \/ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))))) /\ ((~ ((~ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) \/ ((~ ((Nat.mul (Nat.div x0 x1) x1) = (Nat.mul x1 (Nat.div x0 x1)))) \/ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))))) -> ~ ((~ ((Nat.mul (Nat.div x0 x1) x1) = (Nat.mul x1 (Nat.div x0 x1)))) \/ ((~ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) \/ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))))).
Definition term369 (x0 : nat) (x1 : nat) := ((~ ((~ (x0 = (NUMERAL 0))) \/ ((~ ((NUMERAL 0) = x1)) \/ (x0 = x1)))) -> ~ ((~ ((NUMERAL 0) = x1)) \/ ((~ (x0 = (NUMERAL 0))) \/ (x0 = x1)))) /\ ((~ ((~ ((NUMERAL 0) = x1)) \/ ((~ (x0 = (NUMERAL 0))) \/ (x0 = x1)))) -> ~ ((~ (x0 = (NUMERAL 0))) \/ ((~ ((NUMERAL 0) = x1)) \/ (x0 = x1)))).
Definition term362 (x0 : nat) (x1 : nat) := ((~ ((~ (x0 = (NUMERAL 0))) \/ ((x0 = x1) \/ (~ ((NUMERAL 0) = x1))))) -> ~ ((~ (x0 = (NUMERAL 0))) \/ ((~ ((NUMERAL 0) = x1)) \/ (x0 = x1)))) /\ ((~ ((~ (x0 = (NUMERAL 0))) \/ ((~ ((NUMERAL 0) = x1)) \/ (x0 = x1)))) -> ~ ((~ (x0 = (NUMERAL 0))) \/ ((x0 = x1) \/ (~ ((NUMERAL 0) = x1))))).
Definition term328 (a0 : Type') (x0 : a0) (x1 : a0) := ((~ ((~ (x1 = x0)) \/ ((~ (x1 = x1)) \/ (x0 = x1)))) -> ~ ((~ (x1 = x1)) \/ ((~ (x1 = x0)) \/ (x0 = x1)))) /\ ((~ ((~ (x1 = x1)) \/ ((~ (x1 = x0)) \/ (x0 = x1)))) -> ~ ((~ (x1 = x0)) \/ ((~ (x1 = x1)) \/ (x0 = x1)))).
Definition term306 (x0 : nat) (x1 : nat) := ((~ ((x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) \/ (x1 = (NUMERAL 0)))) -> ~ ((x1 = (NUMERAL 0)) \/ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))))) /\ ((~ ((x1 = (NUMERAL 0)) \/ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))))) -> ~ ((x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) \/ (x1 = (NUMERAL 0)))).
Definition term304 (x0 : nat) (x1 : nat) := ((~ ((x1 = (NUMERAL 0)) \/ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))))) -> ~ ((x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) \/ (x1 = (NUMERAL 0)))) /\ ((~ ((x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) \/ (x1 = (NUMERAL 0)))) -> ~ ((x1 = (NUMERAL 0)) \/ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))))).
Definition term542 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((~ (x0 = x0)) \/ ((x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))) \/ (x1 = x2)))) -> ~ ((x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))) \/ ((~ (x0 = x0)) \/ (x1 = x2))).
Definition term224 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.modulo (Nat.div x0 x1) x2.
Definition term134 (x0 : nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => ((Nat.add x0 x1) = (Nat.add x0 y1)) \/ (~ (x1 = y1))) y0.
Definition term582 (x0 : nat) (x1 : nat) := (fun y0 : Prop => ((NUMERAL 0) = x0) -> ((~ ((NUMERAL 0) = x0)) \/ y0) -> y0) ((~ (x1 = x0)) \/ (x1 = (NUMERAL 0))).
Definition term330 (a0 : Type') (x0 : a0) := (fun y0 : Prop => forall y1 : Prop, y0 -> ((~ y0) \/ y1) -> y1) (x0 = x0).
Definition term308 (a0 : Type') (x0 : a0) := (fun y0 : Prop => forall y1 : Prop, (y0 -> y1) = ((~ y0) \/ y1)) (x0 = x0).
Definition term407 (x0 : nat) (x1 : nat) := (fun y0 : Prop => (((Nat.mul (Nat.div x0 x1) x1) = (Nat.mul x1 (Nat.div x0 x1))) -> y0) = ((~ ((Nat.mul (Nat.div x0 x1) x1) = (Nat.mul x1 (Nat.div x0 x1)))) \/ y0)) ((~ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) \/ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))).
Definition term321 (a0 : Type') (x0 : a0) := ~ (x0 = x0).
Definition term611 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x1 (Nat.mul (Nat.div x0 (Nat.mul x1 x2)) x2)).
Definition term228 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x1 (Nat.modulo (Nat.div x0 x1) x2)).
Definition term233 (x0 : nat) := (fun y0 : nat => (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) x0.
Definition term244 := (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False.
Definition term66 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Nat.add y0 y1) = (Nat.add y0 y2)) = (y1 = y2)) -> False.
Definition term437 (x0 : nat) (x1 : nat) := (x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))) \/ (~ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))).
Definition term480 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))) \/ (x1 = x2).
Definition term383 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) \/ (x1 = x2).
Definition term441 (x0 : nat) (x1 : nat) := (fun y0 : Prop => ((x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) -> y0) = ((~ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) \/ y0)) ((x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))) \/ (~ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))))).
Definition term497 (x0 : nat) (x1 : nat) := (fun y0 : Prop => (((Nat.add (Nat.mul x0 (Nat.div x1 x0)) (Nat.modulo x1 x0)) = x1) -> y0) = ((~ ((Nat.add (Nat.mul x0 (Nat.div x1 x0)) (Nat.modulo x1 x0)) = x1)) \/ y0)) ((x1 = (Nat.add (Nat.mul x0 (Nat.div x1 x0)) (Nat.modulo x1 x0))) \/ (~ (x1 = x1))).
Definition term606 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul (Nat.div x0 (Nat.mul x1 x2)) (Nat.mul x1 x2)) (Nat.modulo x0 (Nat.mul x1 x2)).
Definition term261 (x0 : nat) (x1 : nat) := forall y0 : nat, (~ (x1 = (NUMERAL 0))) -> (y0 = (NUMERAL 0)) -> (~ (x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))) -> (forall y1 : nat, forall y2 : nat, (Nat.mul y1 y2) = (Nat.mul y2 y1)) -> ~ (forall y1 : nat, forall y2 : nat, (~ (y2 = (NUMERAL 0))) -> (y1 = (Nat.add (Nat.mul (Nat.div y1 y2) y2) (Nat.modulo y1 y2))) /\ (Peano.lt (Nat.modulo y1 y2) y2)).
Definition term260 (x0 : nat) (x1 : nat) := forall y0 : nat, (~ (x1 = (NUMERAL 0))) -> (y0 = (NUMERAL 0)) -> (~ (x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))) -> (forall y1 : nat, forall y2 : nat, (Nat.mul y1 y2) = (Nat.mul y2 y1)) -> (forall y1 : nat, forall y2 : nat, (~ (y2 = (NUMERAL 0))) -> (y1 = (Nat.add (Nat.mul (Nat.div y1 y2) y2) (Nat.modulo y1 y2))) /\ (Peano.lt (Nat.modulo y1 y2) y2)) -> False.
Definition term192 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((x0 = x2) \/ (~ ((Nat.add x1 x0) = (Nat.add x1 x2)))).
Definition term188 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((Nat.add x1 x0) = (Nat.add x1 x2)).
Definition term414 (x0 : nat) (x1 : nat) := ~ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))).
Definition term307 (a0 : Type') (x0 : a0) (x1 : a0) := (x1 = x1) -> x0 = x1.
Definition term442 (x0 : nat) (x1 : nat) := (~ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) \/ ((x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))) \/ (~ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))))).
Definition term243 (x0 : nat) (x1 : nat) (x2 : nat) := (((~ (x2 = (NUMERAL 0))) -> (x0 = (NUMERAL 0)) -> (~ (x1 = (Nat.add (Nat.mul x2 (Nat.div x1 x2)) (Nat.modulo x1 x2)))) -> (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False) -> (~ (x2 = (NUMERAL 0))) -> (x0 = (NUMERAL 0)) -> (~ (x1 = (Nat.add (Nat.mul x2 (Nat.div x1 x2)) (Nat.modulo x1 x2)))) -> (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False) -> ((~ (x2 = (NUMERAL 0))) -> (x0 = (NUMERAL 0)) -> (~ (x1 = (Nat.add (Nat.mul x2 (Nat.div x1 x2)) (Nat.modulo x1 x2)))) -> (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False) -> (~ (x2 = (NUMERAL 0))) -> (x0 = (NUMERAL 0)) -> (~ (x1 = (Nat.add (Nat.mul x2 (Nat.div x1 x2)) (Nat.modulo x1 x2)))) -> (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False.
Definition term585 (x0 : nat) (x1 : nat) := (~ ((x1 = (NUMERAL 0)) \/ (~ (x1 = x0)))) -> ~ ((~ (x1 = x0)) \/ (x1 = (NUMERAL 0))).
Definition term138 (x0 : nat) (x1 : nat) := and (forall y0 : nat, ((Nat.add x0 x1) = (Nat.add x0 y0)) \/ (~ (x1 = y0))).
Definition term25 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x1 x0) (Nat.mul x1 x2).
Definition term127 (x0 : nat) (x1 : nat) (x2 : nat) := and (((Nat.add x0 x1) = (Nat.add x0 x2)) \/ (~ (x1 = x2))).
Definition term427 (x0 : nat) (x1 : nat) := ((~ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) \/ ((~ ((Nat.mul (Nat.div x0 x1) x1) = (Nat.mul x1 (Nat.div x0 x1)))) \/ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))))) -> (~ ((Nat.mul (Nat.div x0 x1) x1) = (Nat.mul x1 (Nat.div x0 x1)))) \/ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))).
Definition term197 (x0 : nat) (x1 : nat) (x2 : nat) := imp (~ (~ ((Nat.add x1 x0) = (Nat.add x1 x2)))).
Definition term399 (x0 : nat) (x1 : nat) := ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) -> (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)).
Definition term315 (a0 : Type') (x0 : a0) (x1 : a0) := (fun y0 : Prop => ((x1 = x0) -> y0) = ((~ (x1 = x0)) \/ y0)) ((~ (x1 = x1)) \/ (x0 = x1)).
Definition term212 (x0 : nat) := Nat.add (NUMERAL 0) x0.
Definition term280 (x0 : nat) := or (~ (~ (x0 = (NUMERAL 0)))).
Definition term541 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))) \/ ((~ (x0 = x0)) \/ (x1 = x2)))) -> ~ ((~ (x0 = x0)) \/ ((x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))) \/ (x1 = x2))).
Definition term535 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((x1 = x2) \/ ((~ (x0 = x0)) \/ (x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))))) -> ~ ((~ (x0 = x0)) \/ ((x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))) \/ (x1 = x2))).
Definition term368 (x0 : nat) (x1 : nat) := (~ ((~ (x0 = (NUMERAL 0))) \/ ((~ ((NUMERAL 0) = x1)) \/ (x0 = x1)))) -> ~ ((~ ((NUMERAL 0) = x1)) \/ ((~ (x0 = (NUMERAL 0))) \/ (x0 = x1))).
Definition term367 (x0 : nat) (x1 : nat) := (~ ((~ ((NUMERAL 0) = x1)) \/ ((~ (x0 = (NUMERAL 0))) \/ (x0 = x1)))) -> ~ ((~ (x0 = (NUMERAL 0))) \/ ((~ ((NUMERAL 0) = x1)) \/ (x0 = x1))).
Definition term361 (x0 : nat) (x1 : nat) := (~ ((~ (x0 = (NUMERAL 0))) \/ ((x0 = x1) \/ (~ ((NUMERAL 0) = x1))))) -> ~ ((~ (x0 = (NUMERAL 0))) \/ ((~ ((NUMERAL 0) = x1)) \/ (x0 = x1))).
Definition term327 (a0 : Type') (x0 : a0) (x1 : a0) := (~ ((~ (x1 = x0)) \/ ((~ (x1 = x1)) \/ (x0 = x1)))) -> ~ ((~ (x1 = x1)) \/ ((~ (x1 = x0)) \/ (x0 = x1))).
Definition term326 (a0 : Type') (x0 : a0) (x1 : a0) := (~ ((~ (x1 = x1)) \/ ((~ (x1 = x0)) \/ (x0 = x1)))) -> ~ ((~ (x1 = x0)) \/ ((~ (x1 = x1)) \/ (x0 = x1))).
Definition term95 (x0 : nat) (x1 : nat) := exists y0 : nat, ((fun y1 : nat => (Nat.add y1 x0) = (Nat.add y1 x1)) y0) /\ (~ (x0 = x1)).
Definition term395 (x0 : nat) (x1 : nat) := ((~ ((Nat.mul x0 x1) = (Nat.mul x1 x0))) \/ ((Nat.mul x1 x0) = (Nat.mul x0 x1))) -> (Nat.mul x1 x0) = (Nat.mul x0 x1).
Definition term579 (x0 : nat) (x1 : nat) := (~ ((~ (x1 = x0)) \/ ((~ ((NUMERAL 0) = x0)) \/ (x1 = (NUMERAL 0))))) -> ~ ((~ ((NUMERAL 0) = x0)) \/ ((~ (x1 = x0)) \/ (x1 = (NUMERAL 0)))).
Definition term578 (x0 : nat) (x1 : nat) := (~ ((~ ((NUMERAL 0) = x0)) \/ ((~ (x1 = x0)) \/ (x1 = (NUMERAL 0))))) -> ~ ((~ (x1 = x0)) \/ ((~ ((NUMERAL 0) = x0)) \/ (x1 = (NUMERAL 0)))).
Definition term572 (x0 : nat) (x1 : nat) := (~ ((~ ((NUMERAL 0) = x0)) \/ ((x1 = (NUMERAL 0)) \/ (~ (x1 = x0))))) -> ~ ((~ (x1 = x0)) \/ ((~ ((NUMERAL 0) = x0)) \/ (x1 = (NUMERAL 0)))).
Definition term521 (x0 : nat) (x1 : nat) := (~ ((~ (x0 = x0)) \/ ((~ ((Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)) = x0)) \/ (x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))))) -> ~ ((~ ((Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)) = x0)) \/ ((~ (x0 = x0)) \/ (x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))))).
Definition term520 (x0 : nat) (x1 : nat) := (~ ((~ ((Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)) = x0)) \/ ((~ (x0 = x0)) \/ (x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))))) -> ~ ((~ (x0 = x0)) \/ ((~ ((Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)) = x0)) \/ (x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))))).
Definition term508 (x0 : nat) (x1 : nat) := (~ ((~ ((Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)) = x0)) \/ ((x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))) \/ (~ (x0 = x0))))) -> ~ ((~ (x0 = x0)) \/ ((~ ((Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)) = x0)) \/ (x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))))).
Definition term458 (x0 : nat) (x1 : nat) := (~ ((~ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) \/ ((~ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))) \/ (x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))))) -> ~ ((~ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))) \/ ((~ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) \/ (x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))))).
Definition term457 (x0 : nat) (x1 : nat) := (~ ((~ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))) \/ ((~ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) \/ (x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))))) -> ~ ((~ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) \/ ((~ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))) \/ (x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))))).
Definition term451 (x0 : nat) (x1 : nat) := (~ ((~ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) \/ ((x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))) \/ (~ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))))))) -> ~ ((~ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) \/ ((~ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))) \/ (x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))))).
Definition term420 (x0 : nat) (x1 : nat) := (~ ((~ ((Nat.mul (Nat.div x0 x1) x1) = (Nat.mul x1 (Nat.div x0 x1)))) \/ ((~ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) \/ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))))) -> ~ ((~ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) \/ ((~ ((Nat.mul (Nat.div x0 x1) x1) = (Nat.mul x1 (Nat.div x0 x1)))) \/ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))))).
Definition term419 (x0 : nat) (x1 : nat) := (~ ((~ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) \/ ((~ ((Nat.mul (Nat.div x0 x1) x1) = (Nat.mul x1 (Nat.div x0 x1)))) \/ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))))) -> ~ ((~ ((Nat.mul (Nat.div x0 x1) x1) = (Nat.mul x1 (Nat.div x0 x1)))) \/ ((~ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) \/ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))))).
Definition term271 (x0 : nat) := fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0).
Definition term281 (x0 : nat) := or (x0 = (NUMERAL 0)).
Definition term251 (x0 : nat) (x1 : nat) := (~ (x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))) -> (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False.
Definition term630 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo y0 (Nat.mul y1 y2)) = (Nat.add (Nat.mul y1 (Nat.modulo (Nat.div y0 y1) y2)) (Nat.modulo y0 y1)).
Definition term629 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.modulo x0 (Nat.mul y0 y1)) = (Nat.add (Nat.mul y0 (Nat.modulo (Nat.div x0 y0) y1)) (Nat.modulo x0 y0)).
Definition term293 := forall y0 : nat, forall y1 : nat, ((y1 = (NUMERAL 0)) \/ (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)))) /\ ((y1 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term287 := forall y0 : nat, forall y1 : nat, (y1 = (NUMERAL 0)) \/ ((y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term277 := forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0).
Definition term269 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (~ (y0 = (NUMERAL 0))) -> (y2 = (NUMERAL 0)) -> (~ (y1 = (Nat.add (Nat.mul y0 (Nat.div y1 y0)) (Nat.modulo y1 y0)))) -> (forall y3 : nat, forall y4 : nat, (Nat.mul y3 y4) = (Nat.mul y4 y3)) -> ~ (forall y3 : nat, forall y4 : nat, (~ (y4 = (NUMERAL 0))) -> (y3 = (Nat.add (Nat.mul (Nat.div y3 y4) y4) (Nat.modulo y3 y4))) /\ (Peano.lt (Nat.modulo y3 y4) y4)).
Definition term268 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (~ (y0 = (NUMERAL 0))) -> (y2 = (NUMERAL 0)) -> (~ (y1 = (Nat.add (Nat.mul y0 (Nat.div y1 y0)) (Nat.modulo y1 y0)))) -> (forall y3 : nat, forall y4 : nat, (Nat.mul y3 y4) = (Nat.mul y4 y3)) -> (forall y3 : nat, forall y4 : nat, (~ (y4 = (NUMERAL 0))) -> (y3 = (Nat.add (Nat.mul (Nat.div y3 y4) y4) (Nat.modulo y3 y4))) /\ (Peano.lt (Nat.modulo y3 y4) y4)) -> False.
Definition term265 (x0 : nat) := forall y0 : nat, forall y1 : nat, (~ (x0 = (NUMERAL 0))) -> (y1 = (NUMERAL 0)) -> (~ (y0 = (Nat.add (Nat.mul x0 (Nat.div y0 x0)) (Nat.modulo y0 x0)))) -> (forall y2 : nat, forall y3 : nat, (Nat.mul y2 y3) = (Nat.mul y3 y2)) -> ~ (forall y2 : nat, forall y3 : nat, (~ (y3 = (NUMERAL 0))) -> (y2 = (Nat.add (Nat.mul (Nat.div y2 y3) y3) (Nat.modulo y2 y3))) /\ (Peano.lt (Nat.modulo y2 y3) y3)).
Definition term264 (x0 : nat) := forall y0 : nat, forall y1 : nat, (~ (x0 = (NUMERAL 0))) -> (y1 = (NUMERAL 0)) -> (~ (y0 = (Nat.add (Nat.mul x0 (Nat.div y0 x0)) (Nat.modulo y0 x0)))) -> (forall y2 : nat, forall y3 : nat, (Nat.mul y2 y3) = (Nat.mul y3 y2)) -> (forall y2 : nat, forall y3 : nat, (~ (y3 = (NUMERAL 0))) -> (y2 = (Nat.add (Nat.mul (Nat.div y2 y3) y3) (Nat.modulo y2 y3))) /\ (Peano.lt (Nat.modulo y2 y3) y3)) -> False.
Definition term246 := forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1).
Definition term185 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (~ ((Nat.add y0 y1) = (Nat.add y0 y2))) \/ (y1 = y2).
Definition term180 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Nat.add y0 y1) = (Nat.add y0 y2)) \/ (~ (y1 = y2)).
Definition term163 (x0 : nat) := forall y0 : nat, forall y1 : nat, (~ ((Nat.add x0 y0) = (Nat.add x0 y1))) \/ (y0 = y1).
Definition term158 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Nat.add x0 y0) = (Nat.add x0 y1)) \/ (~ (y0 = y1)).
Definition term115 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (((Nat.add y0 y1) = (Nat.add y0 y2)) \/ (~ (y1 = y2))) /\ ((~ ((Nat.add y0 y1) = (Nat.add y0 y2))) \/ (y1 = y2)).
Definition term113 (x0 : nat) := forall y0 : nat, forall y1 : nat, (((Nat.add x0 y0) = (Nat.add x0 y1)) \/ (~ (y0 = y1))) /\ ((~ ((Nat.add x0 y0) = (Nat.add x0 y1))) \/ (y0 = y1)).
Definition term82 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Nat.add x0 y0) = (Nat.add x0 y1)) = (y0 = y1).
Definition term78 := forall y0 : nat, forall y1 : nat, (~ ((exists y2 : nat, (Nat.add y2 y1) = (Nat.add y2 y0)) -> y1 = y0)) -> ~ (forall y2 : nat, forall y3 : nat, forall y4 : nat, ((Nat.add y2 y3) = (Nat.add y2 y4)) = (y3 = y4)).
Definition term77 := forall y0 : nat, forall y1 : nat, (~ ((exists y2 : nat, (Nat.add y2 y1) = (Nat.add y2 y0)) -> y1 = y0)) -> (forall y2 : nat, forall y3 : nat, forall y4 : nat, ((Nat.add y2 y3) = (Nat.add y2 y4)) = (y3 = y4)) -> False.
Definition term68 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Nat.add y0 y1) = (Nat.add y0 y2)) = (y1 = y2).
Definition term42 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.add x0 (Nat.add y0 y1)) = (Nat.add (Nat.add x0 y0) y1).
Definition term37 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y2)) = (Nat.mul y0 (Nat.add y1 y2)).
Definition term36 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.mul y0 (Nat.add y1 y2)) = (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y2)).
Definition term33 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y1)) = (Nat.mul x0 (Nat.add y0 y1)).
Definition term32 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.mul x0 (Nat.add y0 y1)) = (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y1)).
Definition term23 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.div y0 (Nat.mul y1 y2)) = (Nat.div (Nat.div y0 y1) y2).
Definition term22 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.div (Nat.div y0 y1) y2) = (Nat.div y0 (Nat.mul y1 y2)).
Definition term19 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.div x0 (Nat.mul y0 y1)) = (Nat.div (Nat.div x0 y0) y1).
Definition term18 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.div (Nat.div x0 y0) y1) = (Nat.div x0 (Nat.mul y0 y1)).
Definition term5 := forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)) = y0.
Definition term0 := forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul y1 (Nat.div y0 y1)) (Nat.modulo y0 y1)) = y0.
Definition term583 (x0 : nat) (x1 : nat) := ((NUMERAL 0) = x0) -> ((~ ((NUMERAL 0) = x0)) \/ ((~ (x1 = x0)) \/ (x1 = (NUMERAL 0)))) -> (~ (x1 = x0)) \/ (x1 = (NUMERAL 0)).
Definition term363 (x0 : nat) (x1 : nat) := (~ (x0 = (NUMERAL 0))) \/ ((~ ((NUMERAL 0) = x1)) \/ (x0 = x1)).
Definition term174 (x0 : nat) := ((fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Nat.add y0 y1) = (Nat.add y0 y2)) \/ (~ (y1 = y2))) x0) /\ ((fun y0 : nat => forall y1 : nat, forall y2 : nat, (~ ((Nat.add y0 y1) = (Nat.add y0 y2))) \/ (y1 = y2)) x0).
Definition term91 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) /\ x1.
Definition term208 (x0 : nat) := (x0 = (NUMERAL 0)) \/ (~ (x0 = (NUMERAL 0))).
Definition term493 (x0 : nat) (x1 : nat) := (x1 = (Nat.add (Nat.mul x0 (Nat.div x1 x0)) (Nat.modulo x1 x0))) \/ (~ (x1 = x1)).
Definition term584 (x0 : nat) (x1 : nat) := ((~ ((NUMERAL 0) = x0)) \/ ((~ (x1 = x0)) \/ (x1 = (NUMERAL 0)))) -> (~ (x1 = x0)) \/ (x1 = (NUMERAL 0)).
Definition term553 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = x0) -> ((~ (x0 = x0)) \/ (x1 = x2)) -> x1 = x2.
Definition term242 (x0 : nat) (x1 : nat) (x2 : nat) := (((~ (x2 = (NUMERAL 0))) -> (x0 = (NUMERAL 0)) -> (~ (x1 = (Nat.add (Nat.mul x2 (Nat.div x1 x2)) (Nat.modulo x1 x2)))) -> (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False) -> (~ (x2 = (NUMERAL 0))) -> (x0 = (NUMERAL 0)) -> (~ (x1 = (Nat.add (Nat.mul x2 (Nat.div x1 x2)) (Nat.modulo x1 x2)))) -> (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False) -> (~ (x2 = (NUMERAL 0))) -> (x0 = (NUMERAL 0)) -> (~ (x1 = (Nat.add (Nat.mul x2 (Nat.div x1 x2)) (Nat.modulo x1 x2)))) -> (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False.
Definition term626 (x0 : nat) (x1 : nat) (x2 : nat) := exists y0 : nat, (Nat.add y0 (Nat.modulo x1 (Nat.mul x2 x0))) = (Nat.add y0 (Nat.add (Nat.mul x2 (Nat.modulo (Nat.div x1 x2) x0)) (Nat.modulo x1 x2))).
Definition term122 (x0 : nat) (x1 : nat) := fun y0 : nat => ((Nat.add x0 x1) = (Nat.add x0 y0)) \/ (~ (x1 = y0)).
Definition term463 (x0 : nat) (x1 : nat) := (fun y0 : Prop => ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))) -> ((~ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))) \/ y0) -> y0) ((~ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) \/ (x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))).
Definition term323 (a0 : Type') (x0 : a0) (x1 : a0) := ~ ((~ (x1 = x0)) \/ (x0 = x1)).
Definition term318 (a0 : Type') (x0 : a0) (x1 : a0) := ~ ((~ (x1 = x1)) \/ (x0 = x1)).
Definition term548 (x0 : nat) (x1 : nat) (x2 : nat) := ((x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))) \/ ((~ (x0 = x0)) \/ (x1 = x2))) -> (~ (x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))) -> (~ (x0 = x0)) \/ (x1 = x2).
Definition term270 (x0 : nat) (x1 : nat) := (~ (x1 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1).
Definition term136 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Nat.add x0 x1) = (Nat.add x0 y0)) \/ (~ (x1 = y0)).
Definition term312 (a0 : Type') (x0 : a0) (x1 : a0) := (x1 = x0) -> (~ (x1 = x1)) \/ (x0 = x1).
Definition term336 (x0 : nat) := (~ (x0 = (NUMERAL 0))) \/ ((NUMERAL 0) = x0).
Definition term128 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (~ ((Nat.add x0 x1) = (Nat.add x0 y0))) \/ (x1 = y0)) x2.
Definition term210 := forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0.
Definition term502 (x0 : nat) (x1 : nat) := ~ (~ ((Nat.add (Nat.mul x0 (Nat.div x1 x0)) (Nat.modulo x1 x0)) = x1)).
Definition term211 (x0 : nat) := (fun y0 : nat => (Nat.add (NUMERAL 0) y0) = y0) x0.
Definition term316 (a0 : Type') (x0 : a0) (x1 : a0) := (~ (x1 = x0)) \/ ((~ (x1 = x1)) \/ (x0 = x1)).
Definition term356 (x0 : nat) := ~ (~ ((NUMERAL 0) = x0)).
Definition term393 (x0 : nat) (x1 : nat) := (fun y0 : Prop => ((Nat.mul x0 x1) = (Nat.mul x1 x0)) -> ((~ ((Nat.mul x0 x1) = (Nat.mul x1 x0))) \/ y0) -> y0) ((Nat.mul x1 x0) = (Nat.mul x0 x1)).
Definition term302 (x0 : nat) (x1 : nat) := (~ ((x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) \/ (x1 = (NUMERAL 0)))) -> ~ ((x1 = (NUMERAL 0)) \/ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))).
Definition term628 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.modulo x0 (Nat.mul x1 y0)) = (Nat.add (Nat.mul x1 (Nat.modulo (Nat.div x0 x1) y0)) (Nat.modulo x0 x1)).
Definition term28 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.mul x1 (Nat.add x0 y0)) = (Nat.add (Nat.mul x1 x0) (Nat.mul x1 y0)).
Definition term620 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul (Nat.div x0 (Nat.mul x1 x2)) x2) (Nat.modulo (Nat.div x0 x1) x2).
Definition term552 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : Prop => (x0 = x0) -> ((~ (x0 = x0)) \/ y0) -> y0) (x1 = x2).
Definition term93 (x0 : nat -> Prop) (x1 : Prop) := exists y0 : nat, (x0 y0) /\ x1.
Definition term558 (x0 : nat) (x1 : nat) := (fun y0 : Prop => ((~ (x0 = (NUMERAL 0))) -> y0) = ((x0 = (NUMERAL 0)) \/ y0)) (~ (x0 = x1)).
Definition term124 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Nat.add x0 x1) = (Nat.add x0 y0)) \/ (~ (x1 = y0))) x2.
Definition term571 (x0 : nat) (x1 : nat) := (~ ((~ (x0 = x1)) \/ ((~ ((NUMERAL 0) = x1)) \/ (x0 = (NUMERAL 0))))) -> ~ ((~ ((NUMERAL 0) = x1)) \/ ((x0 = (NUMERAL 0)) \/ (~ (x0 = x1)))).
Definition term507 (x0 : nat) (x1 : nat) := (~ ((~ (x1 = x1)) \/ ((~ ((Nat.add (Nat.mul x0 (Nat.div x1 x0)) (Nat.modulo x1 x0)) = x1)) \/ (x1 = (Nat.add (Nat.mul x0 (Nat.div x1 x0)) (Nat.modulo x1 x0)))))) -> ~ ((~ ((Nat.add (Nat.mul x0 (Nat.div x1 x0)) (Nat.modulo x1 x0)) = x1)) \/ ((x1 = (Nat.add (Nat.mul x0 (Nat.div x1 x0)) (Nat.modulo x1 x0))) \/ (~ (x1 = x1)))).
Definition term450 (x0 : nat) (x1 : nat) := (~ ((~ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) \/ ((~ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))) \/ (x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))))) -> ~ ((~ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) \/ ((x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))) \/ (~ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))))).
Definition term360 (x0 : nat) (x1 : nat) := (~ ((~ (x0 = (NUMERAL 0))) \/ ((~ ((NUMERAL 0) = x1)) \/ (x0 = x1)))) -> ~ ((~ (x0 = (NUMERAL 0))) \/ ((x0 = x1) \/ (~ ((NUMERAL 0) = x1)))).
Definition term348 (x0 : nat) (x1 : nat) := (x0 = x1) \/ (~ ((NUMERAL 0) = x1)).
Definition term204 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ ((exists y1 : nat, (Nat.add y1 y0) = (Nat.add y1 x0)) -> y0 = x0)) -> (forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Nat.add y1 y2) = (Nat.add y1 y3)) = (y2 = y3)) -> False) x1.
Definition term559 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) \/ (~ (x0 = x1)).
Definition term206 (x0 : nat) (x1 : nat) := ((exists y0 : nat, (Nat.add y0 x0) = (Nat.add y0 x1)) -> x0 = x1) -> (exists y0 : nat, (Nat.add y0 x0) = (Nat.add y0 x1)) -> x0 = x1.
Definition term205 (x0 : nat) (x1 : nat) := ((exists y0 : nat, (Nat.add y0 x0) = (Nat.add y0 x1)) -> x0 = x1) -> x0 = x1.
Definition term236 (x0 : nat) (x1 : nat) := Nat.mul x1 (Nat.div x0 x1).
Definition term275 (x0 : nat) := forall y0 : nat, (Nat.mul x0 y0) = (Nat.mul y0 x0).
Definition term550 (x0 : nat) := (fun y0 : Prop => forall y1 : Prop, y0 -> ((~ y0) \/ y1) -> y1) (x0 = x0).
Definition term464 (x0 : nat) (x1 : nat) := ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))) -> ((~ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))) \/ ((~ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) \/ (x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))))) -> (~ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) \/ (x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))).
Definition term488 (x0 : nat) (x1 : nat) (x2 : nat) := ((~ (x2 = (Nat.add (Nat.mul x1 (Nat.div x2 x1)) (Nat.modulo x2 x1)))) \/ ((Nat.add (Nat.mul x1 (Nat.div x2 x1)) (Nat.modulo x2 x1)) = x2)) -> (x1 = x0) \/ ((Nat.add (Nat.mul x1 (Nat.div x2 x1)) (Nat.modulo x2 x1)) = x2).
Definition term119 (x0 : nat -> Prop) (x1 : nat -> Prop) := (forall y0 : nat, x0 y0) /\ (forall y0 : nat, x1 y0).
Definition term610 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x1 (Nat.mul (Nat.div x0 (Nat.mul x1 x2)) x2).
Definition term310 (a0 : Type') (x0 : a0) (x1 : a0) := (fun y0 : Prop => ((x1 = x1) -> y0) = ((~ (x1 = x1)) \/ y0)) (x0 = x1).
Definition term517 (x0 : nat) (x1 : nat) := ~ ((~ (x0 = x0)) \/ (x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))).
Definition term504 (x0 : nat) (x1 : nat) := ~ ((~ ((Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)) = x0)) \/ (x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))).
Definition term73 (x0 : nat) := forall y0 : nat, (~ ((exists y1 : nat, (Nat.add y1 y0) = (Nat.add y1 x0)) -> y0 = x0)) -> (forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Nat.add y1 y2) = (Nat.add y1 y3)) = (y2 = y3)) -> False.
Definition term603 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul (Nat.div (Nat.div x0 x1) x2) (Nat.mul x1 x2)).
Definition term59 (x0 : nat) (x1 : nat) := (exists y0 : nat, (Nat.add y0 x0) = (Nat.add y0 x1)) -> x0 = x1.
Definition term335 (x0 : nat) (x1 : nat) := (~ (x1 = x0)) \/ (x0 = x1).
Definition term98 (x0 : nat) (x1 : nat) := exists y0 : nat, (fun y1 : nat => (Nat.add y1 x0) = (Nat.add y1 x1)) y0.
Definition term390 (x0 : nat) (x1 : nat) := (~ ((Nat.mul x0 x1) = (Nat.mul x1 x0))) \/ ((Nat.mul x1 x0) = (Nat.mul x0 x1)).
Definition term525 (x0 : nat) (x1 : nat) := forall y0 : Prop, forall y1 : Prop, (((Nat.add (Nat.mul x0 (Nat.div x1 x0)) (Nat.modulo x1 x0)) = x1) \/ y0) -> ((~ ((Nat.add (Nat.mul x0 (Nat.div x1 x0)) (Nat.modulo x1 x0)) = x1)) \/ y1) -> y0 \/ y1.
Definition term483 (x0 : nat) (x1 : nat) := forall y0 : Prop, forall y1 : Prop, ((x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))) \/ y0) -> ((~ (x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))) \/ y1) -> y0 \/ y1.
Definition term468 (x0 : nat) (x1 : nat) := forall y0 : Prop, forall y1 : Prop, ((x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) \/ y0) -> ((~ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) \/ y1) -> y0 \/ y1.
Definition term377 (x0 : nat) := forall y0 : Prop, forall y1 : Prop, ((x0 = (NUMERAL 0)) \/ y0) -> ((~ (x0 = (NUMERAL 0))) \/ y1) -> y0 \/ y1.
Definition term295 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.mul x0 y0) = (Nat.mul y0 x0)) x1.
Definition term599 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.div (Nat.div x0 x1) x2).
Definition term150 (x0 : nat) (x1 : nat) := and ((fun y0 : nat => forall y1 : nat, ((Nat.add x0 y0) = (Nat.add x0 y1)) \/ (~ (y0 = y1))) x1).
Definition term319 (a0 : Type') (x0 : a0) (x1 : a0) := ~ (x0 = x1).
Definition term563 (x0 : nat) (x1 : nat) := (fun y0 : Prop => (((NUMERAL 0) = x1) -> y0) = ((~ ((NUMERAL 0) = x1)) \/ y0)) ((x0 = (NUMERAL 0)) \/ (~ (x0 = x1))).
Definition term252 (x0 : nat) (x1 : nat) := (~ (x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))) -> (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> ~ (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term529 (x0 : nat) (x1 : nat) (x2 : nat) := (((Nat.add (Nat.mul x2 (Nat.div x1 x2)) (Nat.modulo x1 x2)) = x1) \/ (x2 = x0)) -> ((~ ((Nat.add (Nat.mul x2 (Nat.div x1 x2)) (Nat.modulo x1 x2)) = x1)) \/ ((~ (x1 = x1)) \/ (x1 = (Nat.add (Nat.mul x2 (Nat.div x1 x2)) (Nat.modulo x1 x2))))) -> (x2 = x0) \/ ((~ (x1 = x1)) \/ (x1 = (Nat.add (Nat.mul x2 (Nat.div x1 x2)) (Nat.modulo x1 x2)))).
Definition term69 (x0 : nat) (x1 : nat) := imp (~ ((exists y0 : nat, (Nat.add y0 x0) = (Nat.add y0 x1)) -> x0 = x1)).
Definition term353 (x0 : nat) (x1 : nat) := (~ (x0 = (NUMERAL 0))) \/ ((x0 = x1) \/ (~ ((NUMERAL 0) = x1))).
Definition term57 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.div (Nat.div x0 x1) y0) = (Nat.div x0 (Nat.mul x1 y0))) x2.
Definition term46 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add x0 (Nat.add x1 x2).
Definition term527 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : Prop, (((Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)) = x0) \/ (x1 = x2)) -> ((~ ((Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)) = x0)) \/ y0) -> (x1 = x2) \/ y0.
Definition term485 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : Prop, ((x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))) \/ (x1 = x2)) -> ((~ (x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))) \/ y0) -> (x1 = x2) \/ y0.
Definition term470 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : Prop, ((x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) \/ (x1 = x2)) -> ((~ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) \/ y0) -> (x1 = x2) \/ y0.
Definition term379 (x0 : nat) (x1 : nat) := forall y0 : Prop, ((x1 = (NUMERAL 0)) \/ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) -> ((~ (x1 = (NUMERAL 0))) \/ y0) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) \/ y0.
Definition term472 (x0 : nat) (x1 : nat) (x2 : nat) := ((x1 = (Nat.add (Nat.mul (Nat.div x1 x2) x2) (Nat.modulo x1 x2))) \/ (x2 = x0)) -> ((~ (x1 = (Nat.add (Nat.mul (Nat.div x1 x2) x2) (Nat.modulo x1 x2)))) \/ (x1 = (Nat.add (Nat.mul x2 (Nat.div x1 x2)) (Nat.modulo x1 x2)))) -> (x2 = x0) \/ (x1 = (Nat.add (Nat.mul x2 (Nat.div x1 x2)) (Nat.modulo x1 x2))).
Definition term613 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.add (Nat.mul x2 (Nat.mul (Nat.div x1 (Nat.mul x2 x0)) x0)) (Nat.mul x2 (Nat.modulo (Nat.div x1 x2) x0))) (Nat.modulo x1 x2).
Definition term152 (x0 : nat) (x1 : nat) := ((fun y0 : nat => forall y1 : nat, ((Nat.add x0 y0) = (Nat.add x0 y1)) \/ (~ (y0 = y1))) x1) /\ ((fun y0 : nat => forall y1 : nat, (~ ((Nat.add x0 y0) = (Nat.add x0 y1))) \/ (y0 = y1)) x1).
Definition term608 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul (Nat.div (Nat.div x1 x2) x0) (Nat.mul x2 x0)) (Nat.add (Nat.mul x2 (Nat.modulo (Nat.div x1 x2) x0)) (Nat.modulo x1 x2)).
Definition term142 (x0 : nat) (x1 : nat) := (forall y0 : nat, ((Nat.add x0 x1) = (Nat.add x0 y0)) \/ (~ (x1 = y0))) /\ (forall y0 : nat, (~ ((Nat.add x0 x1) = (Nat.add x0 y0))) \/ (x1 = y0)).
Definition term422 (x0 : nat) (x1 : nat) := (~ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) \/ ((~ ((Nat.mul (Nat.div x0 x1) x1) = (Nat.mul x1 (Nat.div x0 x1)))) \/ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))).
Definition term408 (x0 : nat) (x1 : nat) := (~ ((Nat.mul (Nat.div x0 x1) x1) = (Nat.mul x1 (Nat.div x0 x1)))) \/ ((~ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) \/ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))).
Definition term229 := Nat.add (NUMERAL 0).
Definition term94 (x0 : nat) (x1 : nat) := (exists y0 : nat, (fun y1 : nat => (Nat.add y1 x0) = (Nat.add y1 x1)) y0) /\ (~ (x0 = x1)).
Definition term594 (x0 : nat) (x1 : nat) := (~ (x0 = x1)) -> False.
Definition term182 := and (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Nat.add y0 y1) = (Nat.add y0 y2)) \/ (~ (y1 = y2))).
Definition term160 (x0 : nat) := and (forall y0 : nat, forall y1 : nat, ((Nat.add x0 y0) = (Nat.add x0 y1)) \/ (~ (y0 = y1))).
Definition term523 (x0 : nat) (x1 : nat) := (~ ((Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)) = x0)) \/ ((~ (x0 = x0)) \/ (x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))).
Definition term524 (x0 : nat) (x1 : nat) := (fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, (y0 \/ y1) -> ((~ y0) \/ y2) -> y1 \/ y2) ((Nat.add (Nat.mul x0 (Nat.div x1 x0)) (Nat.modulo x1 x0)) = x1).
Definition term495 (x0 : nat) (x1 : nat) := (fun y0 : Prop => forall y1 : Prop, (y0 -> y1) = ((~ y0) \/ y1)) ((Nat.add (Nat.mul x0 (Nat.div x1 x0)) (Nat.modulo x1 x0)) = x1).
Definition term607 (x0 : nat) (x1 : nat) (x2 : nat) := @eq nat (Nat.add (Nat.mul (Nat.div (Nat.div x0 x1) x2) (Nat.mul x1 x2)) (Nat.modulo x0 (Nat.mul x1 x2))).
Definition term92 (x0 : nat -> Prop) (x1 : Prop) := (exists y0 : nat, x0 y0) /\ x1.
Definition term109 (x0 : nat) (x1 : nat) (x2 : nat) := (((Nat.add x0 x1) = (Nat.add x0 x2)) \/ (~ (x1 = x2))) /\ ((~ ((Nat.add x0 x1) = (Nat.add x0 x2))) \/ (x1 = x2)).
Definition term566 (x0 : nat) (x1 : nat) := ~ ((x0 = (NUMERAL 0)) \/ (~ (x0 = x1))).
Definition term592 (x0 : nat) (x1 : nat) := (fun y0 : Prop => y0 -> (~ y0) -> False) (x0 = x1).
Definition term625 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x2 (Nat.add (Nat.mul (Nat.div (Nat.div x1 x2) x0) x0) (Nat.modulo (Nat.div x1 x2) x0))) (Nat.modulo x1 x2).
Definition term333 (a0 : Type') (x0 : a0) (x1 : a0) := (x1 = x1) -> ((~ (x1 = x1)) \/ ((~ (x1 = x0)) \/ (x0 = x1))) -> (~ (x1 = x0)) \/ (x0 = x1).
Definition term183 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, forall y3 : nat, (~ ((Nat.add y1 y2) = (Nat.add y1 y3))) \/ (y2 = y3)) y0.
Definition term178 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, forall y3 : nat, ((Nat.add y1 y2) = (Nat.add y1 y3)) \/ (~ (y2 = y3))) y0.
Definition term161 (x0 : nat) := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (~ ((Nat.add x0 y1) = (Nat.add x0 y2))) \/ (y1 = y2)) y0.
Definition term156 (x0 : nat) := fun y0 : nat => (fun y1 : nat => forall y2 : nat, ((Nat.add x0 y1) = (Nat.add x0 y2)) \/ (~ (y1 = y2))) y0.
Definition term191 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((~ ((Nat.add x0 x1) = (Nat.add x0 x2))) \/ (x1 = x2)).
Definition term340 (x0 : nat) := (x0 = (NUMERAL 0)) -> ((~ (x0 = (NUMERAL 0))) \/ ((NUMERAL 0) = x0)) -> (NUMERAL 0) = x0.
Definition term627 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nat => (Nat.add y0 (Nat.modulo x1 (Nat.mul x2 x0))) = (Nat.add y0 (Nat.add (Nat.mul x2 (Nat.modulo (Nat.div x1 x2) x0)) (Nat.modulo x1 x2))).
Definition term296 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((y1 = (NUMERAL 0)) \/ (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)))) /\ ((y1 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo y0 y1) y1))) x0.
Definition term294 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) x0.
Definition term203 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ ((exists y2 : nat, (Nat.add y2 y1) = (Nat.add y2 y0)) -> y1 = y0)) -> (forall y2 : nat, forall y3 : nat, forall y4 : nat, ((Nat.add y2 y3) = (Nat.add y2 y4)) = (y3 = y4)) -> False) x0.
Definition term456 (x0 : nat) (x1 : nat) := (~ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) \/ (x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))).
Definition term474 (x0 : nat) (x1 : nat) (x2 : nat) := (x2 = x0) \/ (x1 = (Nat.add (Nat.mul x2 (Nat.div x1 x2)) (Nat.modulo x1 x2))).
Definition term389 (x0 : nat) (x1 : nat) (x2 : nat) := (x2 = x0) \/ (x1 = (Nat.add (Nat.mul (Nat.div x1 x2) x2) (Nat.modulo x1 x2))).
Definition term322 (a0 : Type') (x0 : a0) := ~ (~ (x0 = x0)).
Definition term514 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((x1 = x2) \/ ((Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)) = x0))) -> ~ (((Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)) = x0) \/ (x1 = x2)).
Definition term232 := forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0).
Definition term63 (x0 : nat) (x1 : nat) := ((~ ((exists y0 : nat, (Nat.add y0 x0) = (Nat.add y0 x1)) -> x0 = x1)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Nat.add y0 y1) = (Nat.add y0 y2)) = (y1 = y2)) -> False) -> (~ ((exists y0 : nat, (Nat.add y0 x0) = (Nat.add y0 x1)) -> x0 = x1)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Nat.add y0 y1) = (Nat.add y0 y2)) = (y1 = y2)) -> False.
Definition term575 (x0 : nat) (x1 : nat) := ~ ((~ (x1 = x0)) \/ (x1 = (NUMERAL 0))).
Definition term568 (x0 : nat) (x1 : nat) := ~ ((~ ((NUMERAL 0) = x0)) \/ (x1 = (NUMERAL 0))).
Definition term26 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.mul x1 (Nat.add x0 y0)) = (Nat.add (Nat.mul x1 x0) (Nat.mul x1 y0)).
Definition term347 (x0 : nat) (x1 : nat) := (fun y0 : Prop => ((~ (x0 = x1)) -> y0) = ((x0 = x1) \/ y0)) (~ ((NUMERAL 0) = x1)).
Definition term53 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (Nat.mul x1 x2).
Definition term88 (x0 : nat) (x1 : nat) := and (exists y0 : nat, (Nat.add y0 x0) = (Nat.add y0 x1)).
Definition term616 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.div x0 (Nat.mul x1 x2)) x2.
Definition term190 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = x2) \/ (~ ((Nat.add x1 x0) = (Nat.add x1 x2))).
Definition term382 (x0 : nat) (x1 : nat) (x2 : nat) := ((~ (x1 = (NUMERAL 0))) \/ (x1 = x2)) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) \/ (x1 = x2).
Definition term45 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.add x0 (Nat.add x1 y0)) = (Nat.add (Nat.add x0 x1) y0)) x2.
Definition term234 (x0 : nat) := Nat.mul x0 (NUMERAL 0).
Definition term477 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((x1 = (Nat.add (Nat.mul x2 (Nat.div x1 x2)) (Nat.modulo x1 x2))) \/ (x2 = x0))) -> ~ ((x2 = x0) \/ (x1 = (Nat.add (Nat.mul x2 (Nat.div x1 x2)) (Nat.modulo x1 x2)))).
Definition term387 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((x1 = (Nat.add (Nat.mul (Nat.div x1 x2) x2) (Nat.modulo x1 x2))) \/ (x2 = x0))) -> ~ ((x2 = x0) \/ (x1 = (Nat.add (Nat.mul (Nat.div x1 x2) x2) (Nat.modulo x1 x2)))).
Definition term194 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (~ ((Nat.add x0 x1) = (Nat.add x0 x2)))) -> x1 = x2.
Definition term612 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x2 (Nat.mul (Nat.div x1 (Nat.mul x2 x0)) x0)) (Nat.add (Nat.mul x2 (Nat.modulo (Nat.div x1 x2) x0)) (Nat.modulo x1 x2)).
Definition term357 (x0 : nat) (x1 : nat) := ~ ((~ ((NUMERAL 0) = x1)) \/ (x0 = x1)).
Definition term225 (x0 : nat) (x1 : nat) := Nat.modulo (Nat.div x0 (NUMERAL 0)) x1.
Definition term220 (x0 : nat) (x1 : nat) (x2 : nat) := @eq nat (Nat.modulo x0 (Nat.mul x1 x2)).
Definition term288 (x0 : nat) (x1 : nat) := ((x1 = (NUMERAL 0)) \/ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) /\ ((x1 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo x0 x1) x1)).
Definition term85 (x0 : nat) (x1 : nat) := exists y0 : nat, (Nat.add y0 x0) = (Nat.add y0 x1).
Definition term110 (x0 : nat) (x1 : nat) := fun y0 : nat => (((Nat.add x0 x1) = (Nat.add x0 y0)) \/ (~ (x1 = y0))) /\ ((~ ((Nat.add x0 x1) = (Nat.add x0 y0))) \/ (x1 = y0)).
Definition term139 (x0 : nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => (~ ((Nat.add x0 x1) = (Nat.add x0 y1))) \/ (x1 = y1)) y0.
Definition term249 := (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> ~ (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term181 := and (forall y0 : nat, (fun y1 : nat => forall y2 : nat, forall y3 : nat, ((Nat.add y1 y2) = (Nat.add y1 y3)) \/ (~ (y2 = y3))) y0).
Definition term159 (x0 : nat) := and (forall y0 : nat, (fun y1 : nat => forall y2 : nat, ((Nat.add x0 y1) = (Nat.add x0 y2)) \/ (~ (y1 = y2))) y0).
Definition term137 (x0 : nat) (x1 : nat) := and (forall y0 : nat, (fun y1 : nat => ((Nat.add x0 x1) = (Nat.add x0 y1)) \/ (~ (x1 = y1))) y0).
Definition term482 (x0 : nat) (x1 : nat) := (fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, (y0 \/ y1) -> ((~ y0) \/ y2) -> y1 \/ y2) (x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))).
Definition term467 (x0 : nat) (x1 : nat) := (fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, (y0 \/ y1) -> ((~ y0) \/ y2) -> y1 \/ y2) (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))).
Definition term172 (x0 : nat) := and ((fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Nat.add y0 y1) = (Nat.add y0 y2)) \/ (~ (y1 = y2))) x0).
Definition term289 (x0 : nat) (x1 : nat) := Peano.lt (Nat.modulo x0 x1) x1.
Definition term52 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.mul (Nat.mul x1 x0) x2) = (Nat.mul x1 (Nat.mul x0 x2))) /\ ((Nat.mul x1 (Nat.mul x0 x2)) = (Nat.mul x0 (Nat.mul x1 x2))).
Definition term462 (x0 : nat) (x1 : nat) := forall y0 : Prop, ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))) -> ((~ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))) \/ y0) -> y0.
Definition term429 (x0 : nat) (x1 : nat) := forall y0 : Prop, ((Nat.mul (Nat.div x0 x1) x1) = (Nat.mul x1 (Nat.div x0 x1))) -> ((~ ((Nat.mul (Nat.div x0 x1) x1) = (Nat.mul x1 (Nat.div x0 x1)))) \/ y0) -> y0.
Definition term424 (x0 : nat) (x1 : nat) := forall y0 : Prop, ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) -> ((~ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) \/ y0) -> y0.
Definition term392 (x0 : nat) (x1 : nat) := forall y0 : Prop, ((Nat.mul x1 x0) = (Nat.mul x0 x1)) -> ((~ ((Nat.mul x1 x0) = (Nat.mul x0 x1))) \/ y0) -> y0.
Definition term338 (x0 : nat) := forall y0 : Prop, (x0 = (NUMERAL 0)) -> ((~ (x0 = (NUMERAL 0))) \/ y0) -> y0.
Definition term70 (x0 : nat) (x1 : nat) := (~ ((exists y0 : nat, (Nat.add y0 x0) = (Nat.add y0 x1)) -> x0 = x1)) -> ~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Nat.add y0 y1) = (Nat.add y0 y2)) = (y1 = y2)).
Definition term107 (x0 : nat) (x1 : nat) := fun y0 : nat => ((Nat.add y0 x0) = (Nat.add y0 x1)) /\ (~ (x0 = x1)).
Definition term500 (x0 : nat) (x1 : nat) := ~ ((x1 = (Nat.add (Nat.mul x0 (Nat.div x1 x0)) (Nat.modulo x1 x0))) \/ (~ (x1 = x1))).
Definition term254 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = (NUMERAL 0)) -> (~ (x1 = (Nat.add (Nat.mul x2 (Nat.div x1 x2)) (Nat.modulo x1 x2)))) -> (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False.
Definition term97 (x0 : nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => (Nat.add y1 x0) = (Nat.add y1 x1)) y0.
Definition term534 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((~ (x1 = x1)) \/ ((x1 = (Nat.add (Nat.mul x2 (Nat.div x1 x2)) (Nat.modulo x1 x2))) \/ (x2 = x0)))) -> ~ ((x2 = x0) \/ ((~ (x1 = x1)) \/ (x1 = (Nat.add (Nat.mul x2 (Nat.div x1 x2)) (Nat.modulo x1 x2))))).
Definition term24 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (Nat.add x1 x2).
Definition term14 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.div (Nat.div x0 x1) y0) = (Nat.div x0 (Nat.mul x1 y0)).
Definition term147 (x0 : nat) := fun y0 : nat => forall y1 : nat, ((Nat.add x0 y0) = (Nat.add x0 y1)) \/ (~ (y0 = y1)).
Definition term76 := fun y0 : nat => forall y1 : nat, (~ ((exists y2 : nat, (Nat.add y2 y1) = (Nat.add y2 y0)) -> y1 = y0)) -> ~ (forall y2 : nat, forall y3 : nat, forall y4 : nat, ((Nat.add y2 y3) = (Nat.add y2 y4)) = (y3 = y4)).
Definition term560 (x0 : nat) (x1 : nat) := ((NUMERAL 0) = x1) -> (x0 = (NUMERAL 0)) \/ (~ (x0 = x1)).
Definition term116 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term618 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul (Nat.div x0 (Nat.mul x1 x2)) x2).
Definition term166 := forall y0 : nat, (forall y1 : nat, forall y2 : nat, ((Nat.add y0 y1) = (Nat.add y0 y2)) \/ (~ (y1 = y2))) /\ (forall y1 : nat, forall y2 : nat, (~ ((Nat.add y0 y1) = (Nat.add y0 y2))) \/ (y1 = y2)).
Definition term144 (x0 : nat) := forall y0 : nat, (forall y1 : nat, ((Nat.add x0 y0) = (Nat.add x0 y1)) \/ (~ (y0 = y1))) /\ (forall y1 : nat, (~ ((Nat.add x0 y0) = (Nat.add x0 y1))) \/ (y0 = y1)).
Definition term416 (x0 : nat) (x1 : nat) := ~ ((~ ((Nat.mul (Nat.div x0 x1) x1) = (Nat.mul x1 (Nat.div x0 x1)))) \/ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))).
Definition term410 (x0 : nat) (x1 : nat) := ~ ((~ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) \/ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))).
Definition term218 := Nat.mul (NUMERAL 0).
Definition term60 (x0 : nat) (x1 : nat) := (~ ((exists y0 : nat, (Nat.add y0 x0) = (Nat.add y0 x1)) -> x0 = x1)) -> False.
Definition term489 (x0 : nat) (x1 : nat) (x2 : nat) := (x1 = x0) \/ ((Nat.add (Nat.mul x1 (Nat.div x2 x1)) (Nat.modulo x2 x1)) = x2).
Definition term217 (x0 : nat) := Nat.mul (NUMERAL 0) x0.
Definition term544 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))) \/ ((~ (x0 = x0)) \/ (x1 = x2)).
Definition term430 (x0 : nat) (x1 : nat) := (fun y0 : Prop => ((Nat.mul (Nat.div x0 x1) x1) = (Nat.mul x1 (Nat.div x0 x1))) -> ((~ ((Nat.mul (Nat.div x0 x1) x1) = (Nat.mul x1 (Nat.div x0 x1)))) \/ y0) -> y0) ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))).
Definition term454 (x0 : nat) (x1 : nat) := ~ ((~ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) \/ (x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))).
Definition term447 (x0 : nat) (x1 : nat) := ~ ((~ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))) \/ (x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))).
Definition term283 (x0 : nat) (x1 : nat) := (x1 = (NUMERAL 0)) \/ ((x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1)).
Definition term460 (x0 : nat) (x1 : nat) := (~ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))) \/ ((~ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) \/ (x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))).
Definition term445 (x0 : nat) (x1 : nat) := ~ (~ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))).
Definition term90 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) /\ x1.
Definition term325 (a0 : Type') (x0 : a0) (x1 : a0) := (~ (x1 = x0)) \/ (x0 = x1).
Definition term373 (x0 : nat) (x1 : nat) := (fun y0 : Prop => ((NUMERAL 0) = x1) -> ((~ ((NUMERAL 0) = x1)) \/ y0) -> y0) ((~ (x0 = (NUMERAL 0))) \/ (x0 = x1)).
Definition term412 (x0 : nat) (x1 : nat) := ~ (~ ((Nat.mul (Nat.div x0 x1) x1) = (Nat.mul x1 (Nat.div x0 x1)))).
Definition term227 (x0 : nat) (x1 : nat) := Nat.mul (NUMERAL 0) (Nat.modulo (Nat.div x0 (NUMERAL 0)) x1).
Definition term129 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((Nat.add x0 x1) = (Nat.add x0 x2))) \/ (x1 = x2).
Definition term74 (x0 : nat) := forall y0 : nat, (~ ((exists y1 : nat, (Nat.add y1 y0) = (Nat.add y1 x0)) -> y0 = x0)) -> ~ (forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Nat.add y1 y2) = (Nat.add y1 y3)) = (y2 = y3)).
Definition term51 (a0 : Type') (x0 : a0) := (fun y0 : a0 => (y0 = y0) = True) x0.
Definition term278 (x0 : nat) := ~ (~ (x0 = (NUMERAL 0))).
Definition term332 (a0 : Type') (x0 : a0) (x1 : a0) := (fun y0 : Prop => (x1 = x1) -> ((~ (x1 = x1)) \/ y0) -> y0) ((~ (x1 = x0)) \/ (x0 = x1)).
Definition term531 (x0 : nat) (x1 : nat) (x2 : nat) := (x2 = x0) \/ ((~ (x1 = x1)) \/ (x1 = (Nat.add (Nat.mul x2 (Nat.div x1 x2)) (Nat.modulo x1 x2)))).
Definition term344 (x0 : nat) (x1 : nat) := (~ (x0 = x1)) -> ~ ((NUMERAL 0) = x1).
Definition term141 (x0 : nat) (x1 : nat) := forall y0 : nat, (~ ((Nat.add x0 x1) = (Nat.add x0 y0))) \/ (x1 = y0).
Definition term84 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.add y0 x0) = (Nat.add y0 x1).
Definition term567 (x0 : nat) (x1 : nat) := ~ (~ (x0 = x1)).
Definition term65 (x0 : nat) (x1 : nat) := (((~ ((exists y0 : nat, (Nat.add y0 x0) = (Nat.add y0 x1)) -> x0 = x1)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Nat.add y0 y1) = (Nat.add y0 y2)) = (y1 = y2)) -> False) -> (~ ((exists y0 : nat, (Nat.add y0 x0) = (Nat.add y0 x1)) -> x0 = x1)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Nat.add y0 y1) = (Nat.add y0 y2)) = (y1 = y2)) -> False) -> ((~ ((exists y0 : nat, (Nat.add y0 x0) = (Nat.add y0 x1)) -> x0 = x1)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Nat.add y0 y1) = (Nat.add y0 y2)) = (y1 = y2)) -> False) -> (~ ((exists y0 : nat, (Nat.add y0 x0) = (Nat.add y0 x1)) -> x0 = x1)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Nat.add y0 y1) = (Nat.add y0 y2)) = (y1 = y2)) -> False.
Definition term602 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.div x0 (Nat.mul x1 x2)) (Nat.mul x1 x2).
Definition term272 (x0 : nat) := forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0).
Definition term311 (a0 : Type') (x0 : a0) (x1 : a0) := (~ (x1 = x1)) \/ (x0 = x1).
Definition term221 (x0 : nat) := Nat.div x0 (NUMERAL 0).
Definition term519 (x0 : nat) (x1 : nat) := (~ (x0 = x0)) \/ (x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))).
Definition term8 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0)) = x0) x1.
Definition term3 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add (Nat.mul y0 (Nat.div x0 y0)) (Nat.modulo x0 y0)) = x0) x1.
Definition term561 (x0 : nat) := (fun y0 : Prop => forall y1 : Prop, (y0 -> y1) = ((~ y0) \/ y1)) ((NUMERAL 0) = x0).
Definition term371 (x0 : nat) := (fun y0 : Prop => forall y1 : Prop, y0 -> ((~ y0) \/ y1) -> y1) ((NUMERAL 0) = x0).
Definition term433 (x0 : nat) (x1 : nat) := (~ (x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))) -> ~ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))).
Definition term591 (x0 : nat) (x1 : nat) := ((x0 = (NUMERAL 0)) \/ (~ (x0 = x1))) -> (~ (x0 = (NUMERAL 0))) -> ~ (x0 = x1).
Definition term184 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, forall y3 : nat, (~ ((Nat.add y1 y2) = (Nat.add y1 y3))) \/ (y2 = y3)) y0.
Definition term179 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, forall y3 : nat, ((Nat.add y1 y2) = (Nat.add y1 y3)) \/ (~ (y2 = y3))) y0.
Definition term162 (x0 : nat) := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ ((Nat.add x0 y1) = (Nat.add x0 y2))) \/ (y1 = y2)) y0.
Definition term157 (x0 : nat) := forall y0 : nat, (fun y1 : nat => forall y2 : nat, ((Nat.add x0 y1) = (Nat.add x0 y2)) \/ (~ (y1 = y2))) y0.
Definition term247 := imp (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)).
Definition term334 (a0 : Type') (x0 : a0) (x1 : a0) := ((~ (x1 = x1)) \/ ((~ (x1 = x0)) \/ (x0 = x1))) -> (~ (x1 = x0)) \/ (x0 = x1).
Definition term231 := (forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))).
Definition term438 (x0 : nat) (x1 : nat) := (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) -> (x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))) \/ (~ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))).
Definition term75 := fun y0 : nat => forall y1 : nat, (~ ((exists y2 : nat, (Nat.add y2 y1) = (Nat.add y2 y0)) -> y1 = y0)) -> (forall y2 : nat, forall y3 : nat, forall y4 : nat, ((Nat.add y2 y3) = (Nat.add y2 y4)) = (y3 = y4)) -> False.
Definition term223 (x0 : nat) := Nat.modulo (Nat.div x0 (NUMERAL 0)).
Definition term329 (a0 : Type') (x0 : a0) (x1 : a0) := (~ (x1 = x1)) \/ ((~ (x1 = x0)) \/ (x0 = x1)).
Definition term354 (x0 : nat) (x1 : nat) := ~ ((~ (x0 = (NUMERAL 0))) \/ ((x0 = x1) \/ (~ ((NUMERAL 0) = x1)))).
Definition term555 (x0 : nat) (x1 : nat) := (~ (x0 = (NUMERAL 0))) -> ~ (x0 = x1).
Definition term494 (x0 : nat) (x1 : nat) := ((Nat.add (Nat.mul x0 (Nat.div x1 x0)) (Nat.modulo x1 x0)) = x1) -> (x1 = (Nat.add (Nat.mul x0 (Nat.div x1 x0)) (Nat.modulo x1 x0))) \/ (~ (x1 = x1)).
Definition term600 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.div x0 (Nat.mul x1 x2)).
Definition term54 (x0 : nat) (x1 : nat) (x2 : nat) := @eq nat (Nat.mul x0 (Nat.mul x1 x2)).
Definition term601 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.div (Nat.div x0 x1) x2) (Nat.mul x1 x2).
Definition term574 (x0 : nat) (x1 : nat) := (~ (x1 = x0)) \/ ((~ ((NUMERAL 0) = x0)) \/ (x1 = (NUMERAL 0))).
Definition term207 (x0 : nat) := (fun y0 : Prop => y0 \/ (~ y0)) (x0 = (NUMERAL 0)).
Definition term538 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((~ (x0 = x0)) \/ (x1 = x2)).
Definition term250 (x0 : nat) (x1 : nat) := imp (~ (x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))).
Definition term320 (a0 : Type') (x0 : a0) (x1 : a0) := ~ (~ (x0 = x1)).
Definition term339 (x0 : nat) := (fun y0 : Prop => (x0 = (NUMERAL 0)) -> ((~ (x0 = (NUMERAL 0))) \/ y0) -> y0) ((NUMERAL 0) = x0).
Definition term292 := fun y0 : nat => forall y1 : nat, ((y1 = (NUMERAL 0)) \/ (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)))) /\ ((y1 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term286 := fun y0 : nat => forall y1 : nat, (y1 = (NUMERAL 0)) \/ ((y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term273 := fun y0 : nat => forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1).
Definition term263 (x0 : nat) := fun y0 : nat => forall y1 : nat, (~ (x0 = (NUMERAL 0))) -> (y1 = (NUMERAL 0)) -> (~ (y0 = (Nat.add (Nat.mul x0 (Nat.div y0 x0)) (Nat.modulo y0 x0)))) -> (forall y2 : nat, forall y3 : nat, (Nat.mul y2 y3) = (Nat.mul y3 y2)) -> ~ (forall y2 : nat, forall y3 : nat, (~ (y3 = (NUMERAL 0))) -> (y2 = (Nat.add (Nat.mul (Nat.div y2 y3) y3) (Nat.modulo y2 y3))) /\ (Peano.lt (Nat.modulo y2 y3) y3)).
Definition term262 (x0 : nat) := fun y0 : nat => forall y1 : nat, (~ (x0 = (NUMERAL 0))) -> (y1 = (NUMERAL 0)) -> (~ (y0 = (Nat.add (Nat.mul x0 (Nat.div y0 x0)) (Nat.modulo y0 x0)))) -> (forall y2 : nat, forall y3 : nat, (Nat.mul y2 y3) = (Nat.mul y3 y2)) -> (forall y2 : nat, forall y3 : nat, (~ (y3 = (NUMERAL 0))) -> (y2 = (Nat.add (Nat.mul (Nat.div y2 y3) y3) (Nat.modulo y2 y3))) /\ (Peano.lt (Nat.modulo y2 y3) y3)) -> False.
Definition term112 (x0 : nat) := fun y0 : nat => forall y1 : nat, (((Nat.add x0 y0) = (Nat.add x0 y1)) \/ (~ (y0 = y1))) /\ ((~ ((Nat.add x0 y0) = (Nat.add x0 y1))) \/ (y0 = y1)).
Definition term31 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y1)) = (Nat.mul x0 (Nat.add y0 y1)).
Definition term30 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Nat.mul x0 (Nat.add y0 y1)) = (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y1)).
Definition term16 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Nat.div (Nat.div x0 y0) y1) = (Nat.div x0 (Nat.mul y0 y1)).
Definition term123 (x0 : nat) (x1 : nat) := fun y0 : nat => (~ ((Nat.add x0 x1) = (Nat.add x0 y0))) \/ (x1 = y0).
Definition term526 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : Prop => forall y1 : Prop, (((Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)) = x0) \/ y0) -> ((~ ((Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)) = x0)) \/ y1) -> y0 \/ y1) (x1 = x2).
Definition term484 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : Prop => forall y1 : Prop, ((x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))) \/ y0) -> ((~ (x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))) \/ y1) -> y0 \/ y1) (x1 = x2).
Definition term469 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : Prop => forall y1 : Prop, ((x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) \/ y0) -> ((~ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) \/ y1) -> y0 \/ y1) (x1 = x2).
Definition term449 (x0 : nat) (x1 : nat) := (~ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))) \/ (x0 = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))).
Definition term125 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.add x0 x1) = (Nat.add x0 x2)) \/ (~ (x1 = x2)).
Definition term71 (x0 : nat) := fun y0 : nat => (~ ((exists y1 : nat, (Nat.add y1 y0) = (Nat.add y1 x0)) -> y0 = x0)) -> (forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Nat.add y1 y2) = (Nat.add y1 y3)) = (y2 = y3)) -> False.
Definition term267 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (~ (y0 = (NUMERAL 0))) -> (y2 = (NUMERAL 0)) -> (~ (y1 = (Nat.add (Nat.mul y0 (Nat.div y1 y0)) (Nat.modulo y1 y0)))) -> (forall y3 : nat, forall y4 : nat, (Nat.mul y3 y4) = (Nat.mul y4 y3)) -> ~ (forall y3 : nat, forall y4 : nat, (~ (y4 = (NUMERAL 0))) -> (y3 = (Nat.add (Nat.mul (Nat.div y3 y4) y4) (Nat.modulo y3 y4))) /\ (Peano.lt (Nat.modulo y3 y4) y4)).
Definition term266 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (~ (y0 = (NUMERAL 0))) -> (y2 = (NUMERAL 0)) -> (~ (y1 = (Nat.add (Nat.mul y0 (Nat.div y1 y0)) (Nat.modulo y1 y0)))) -> (forall y3 : nat, forall y4 : nat, (Nat.mul y3 y4) = (Nat.mul y4 y3)) -> (forall y3 : nat, forall y4 : nat, (~ (y4 = (NUMERAL 0))) -> (y3 = (Nat.add (Nat.mul (Nat.div y3 y4) y4) (Nat.modulo y3 y4))) /\ (Peano.lt (Nat.modulo y3 y4) y4)) -> False.
Definition term170 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (~ ((Nat.add y0 y1) = (Nat.add y0 y2))) \/ (y1 = y2).
Definition term169 := fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Nat.add y0 y1) = (Nat.add y0 y2)) \/ (~ (y1 = y2)).
Definition term114 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (((Nat.add y0 y1) = (Nat.add y0 y2)) \/ (~ (y1 = y2))) /\ ((~ ((Nat.add y0 y1) = (Nat.add y0 y2))) \/ (y1 = y2)).
Definition term83 := fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Nat.add y0 y1) = (Nat.add y0 y2)) = (y1 = y2).
Definition term35 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y2)) = (Nat.mul y0 (Nat.add y1 y2)).
Definition term34 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.mul y0 (Nat.add y1 y2)) = (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y2)).
Definition term21 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.div y0 (Nat.mul y1 y2)) = (Nat.div (Nat.div y0 y1) y2).
Definition term20 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.div (Nat.div y0 y1) y2) = (Nat.div y0 (Nat.mul y1 y2)).
Definition term198 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((Nat.add x1 x0) = (Nat.add x1 x2)).
Definition term394 (x0 : nat) (x1 : nat) := ((Nat.mul x0 x1) = (Nat.mul x1 x0)) -> ((~ ((Nat.mul x0 x1) = (Nat.mul x1 x0))) \/ ((Nat.mul x1 x0) = (Nat.mul x0 x1))) -> (Nat.mul x1 x0) = (Nat.mul x0 x1).
Definition term501 (x0 : nat) (x1 : nat) := ~ ((Nat.add (Nat.mul x0 (Nat.div x1 x0)) (Nat.modulo x1 x0)) = x1).
Definition term358 (x0 : nat) (x1 : nat) := ~ ((~ (x0 = (NUMERAL 0))) \/ ((~ ((NUMERAL 0) = x1)) \/ (x0 = x1))).
Definition term108 (x0 : nat) (x1 : nat) := exists y0 : nat, ((Nat.add y0 x0) = (Nat.add y0 x1)) /\ (~ (x0 = x1)).
Definition term623 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.add (Nat.mul x1 (Nat.mul (Nat.div x0 (Nat.mul x1 x2)) x2)) (Nat.mul x1 (Nat.modulo (Nat.div x0 x1) x2))).
Definition term365 (x0 : nat) (x1 : nat) := ~ ((~ ((NUMERAL 0) = x1)) \/ ((~ (x0 = (NUMERAL 0))) \/ (x0 = x1))).
Definition term324 (a0 : Type') (x0 : a0) (x1 : a0) := ~ ((~ (x1 = x1)) \/ ((~ (x1 = x0)) \/ (x0 = x1))).
Definition term317 (a0 : Type') (x0 : a0) (x1 : a0) := ~ ((~ (x1 = x0)) \/ ((~ (x1 = x1)) \/ (x0 = x1))).
Definition term425 (x0 : nat) (x1 : nat) := (fun y0 : Prop => ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) -> ((~ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) \/ y0) -> y0) ((~ ((Nat.mul (Nat.div x0 x1) x1) = (Nat.mul x1 (Nat.div x0 x1)))) \/ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))).
Definition term196 (x0 : nat) (x1 : nat) (x2 : nat) := ~ (~ ((Nat.add x1 x0) = (Nat.add x1 x2))).
Definition term381 (x0 : nat) (x1 : nat) (x2 : nat) := ((x1 = (NUMERAL 0)) \/ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) -> ((~ (x1 = (NUMERAL 0))) \/ (x1 = x2)) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) \/ (x1 = x2).
