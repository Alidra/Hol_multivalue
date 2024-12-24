Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term52 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1).
Definition term119 (x0 : nat) (x1 : nat) := exists y0 : nat, ((Nat.mul x1 x0) = (Nat.mul x1 y0)) /\ (Peano.lt (NUMERAL 0) x1).
Definition term118 (x0 : nat) (x1 : nat) := exists y0 : nat, (x0 = (Nat.add (Nat.mul y0 x1) (NUMERAL 0))) /\ (Peano.lt (NUMERAL 0) x1).
Definition term154 (x0 : nat) (x1 : nat) := (~ (exists y0 : nat, ((Nat.mul x1 x0) = (Nat.mul x1 y0)) /\ (Peano.lt (NUMERAL 0) x1))) -> (forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False.
Definition term285 (x0 : nat) := ~ (Peano.le x0 (NUMERAL 0)).
Definition term84 := fun y0 : nat => forall y1 : nat, exists y2 : nat, (Nat.mul (Nat.div y1 y0) y0) = (Nat.mul y2 y0).
Definition term264 := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 y2)) \/ (~ (Peano.lt y2 y1))) y0) /\ ((fun y1 : nat => forall y2 : nat, (Peano.le y1 y2) \/ (Peano.lt y2 y1)) y0).
Definition term108 (x0 : nat) (x1 : nat) (x2 : nat) := and (x0 = (Nat.add (Nat.mul x1 x2) (NUMERAL 0))).
Definition term102 := (~ False) -> False.
Definition term134 (x0 : nat) (x1 : nat) (x2 : nat) := and ((fun y0 : nat => (Nat.mul x1 x0) = (Nat.mul x1 y0)) x2).
Definition term69 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.mul (Nat.div x0 x1) x1) = (Nat.mul y0 x1).
Definition term203 (x0 : nat) := (Peano.le x0 (NUMERAL 0)) \/ (~ (x0 = (NUMERAL 0))).
Definition term144 (x0 : nat) (x1 : nat) := (exists y0 : nat, (Nat.mul x1 x0) = (Nat.mul x1 y0)) /\ (Peano.lt (NUMERAL 0) x1).
Definition term256 := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 y2)) \/ (~ (Peano.lt y2 y1))) y0) /\ ((fun y1 : nat => forall y2 : nat, (Peano.le y1 y2) \/ (Peano.lt y2 y1)) y0).
Definition term233 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => (~ (Peano.le x0 y1)) \/ (~ (Peano.lt y1 x0))) y0) /\ ((fun y1 : nat => (Peano.le x0 y1) \/ (Peano.lt y1 x0)) y0).
Definition term198 := forall y0 : nat, ((fun y1 : nat => (Peano.le y1 (NUMERAL 0)) \/ (~ (y1 = (NUMERAL 0)))) y0) /\ ((fun y1 : nat => (~ (Peano.le y1 (NUMERAL 0))) \/ (y1 = (NUMERAL 0))) y0).
Definition term78 (x0 : Prop) := ~ (~ x0).
Definition term294 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (~ (y0 = (NUMERAL 0))) -> (y2 = (Nat.mul y1 y0)) -> (~ (exists y3 : nat, ((Nat.mul y0 y1) = (Nat.mul y0 y3)) /\ (Peano.lt (NUMERAL 0) y0))) -> (forall y3 : nat, (Peano.le y3 (NUMERAL 0)) = (y3 = (NUMERAL 0))) -> (forall y3 : nat, forall y4 : nat, (~ (Peano.le y3 y4)) = (Peano.lt y4 y3)) -> False) x0.
Definition term19 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (exists y3 : nat, (y0 = (Nat.add (Nat.mul y3 y1) y2)) /\ (Peano.lt y2 y1)) -> (Nat.modulo y0 y1) = y2) x0.
Definition term2 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y0 = (Nat.add (Nat.mul y2 y1) y3)) /\ (Peano.lt y3 y1)) -> (Nat.modulo y0 y1) = y3) x0.
Definition term135 (x0 : nat) (x1 : nat) (x2 : nat) := ((fun y0 : nat => (Nat.mul x2 x0) = (Nat.mul x2 y0)) x1) /\ (Peano.lt (NUMERAL 0) x2).
Definition term136 (x0 : nat) (x1 : nat) := fun y0 : nat => ((fun y1 : nat => (Nat.mul x1 x0) = (Nat.mul x1 y1)) y0) /\ (Peano.lt (NUMERAL 0) x1).
Definition term82 (x0 : nat) := forall y0 : nat, exists y1 : nat, (Nat.mul (Nat.div y0 x0) x0) = (Nat.mul y1 x0).
Definition term242 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => (~ (Peano.le x0 y1)) \/ (~ (Peano.lt y1 x0))) y0) /\ ((fun y1 : nat => (Peano.le x0 y1) \/ (Peano.lt y1 x0)) y0).
Definition term209 := fun y0 : nat => ((fun y1 : nat => (Peano.le y1 (NUMERAL 0)) \/ (~ (y1 = (NUMERAL 0)))) y0) /\ ((fun y1 : nat => (~ (Peano.le y1 (NUMERAL 0))) \/ (y1 = (NUMERAL 0))) y0).
Definition term174 (x0 : nat) := fun y0 : nat => (~ (Peano.le x0 y0)) = (Peano.lt y0 x0).
Definition term206 (x0 : nat) := (fun y0 : nat => (~ (Peano.le y0 (NUMERAL 0))) \/ (y0 = (NUMERAL 0))) x0.
Definition term33 (x0 : nat) := (fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> forall y1 : nat, (y1 = (Nat.add (Nat.mul (Nat.div y1 y0) y0) (Nat.modulo y1 y0))) /\ (Peano.lt (Nat.modulo y1 y0) y0)) x0.
Definition term13 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nat => (x0 = (Nat.add (Nat.mul y0 x2) x1)) /\ (Peano.lt x1 x2).
Definition term37 (x0 : nat) := Nat.modulo x0 (NUMERAL 0).
Definition term18 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y0 = (Nat.add (Nat.mul y2 y1) y3)) /\ (Peano.lt y3 y1)) -> (Nat.modulo y0 y1) = y3) -> forall y0 : nat, forall y1 : nat, forall y2 : nat, (exists y3 : nat, (y0 = (Nat.add (Nat.mul y3 y1) y2)) /\ (Peano.lt y2 y1)) -> (Nat.modulo y0 y1) = y2.
Definition term14 (x0 : nat) (x1 : nat) (x2 : nat) := (exists y0 : nat, (x0 = (Nat.add (Nat.mul y0 x1) x2)) /\ (Peano.lt x2 x1)) -> (Nat.modulo x0 x1) = x2.
Definition term191 (x0 : nat) := ((Peano.le x0 (NUMERAL 0)) \/ (~ (x0 = (NUMERAL 0)))) /\ ((~ (Peano.le x0 (NUMERAL 0))) \/ (x0 = (NUMERAL 0))).
Definition term152 := (forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False.
Definition term71 (x0 : Prop) := (~ x0) -> False.
Definition term257 := (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 y2)) \/ (~ (Peano.lt y2 y1))) y0) /\ (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Peano.le y1 y2) \/ (Peano.lt y2 y1)) y0).
Definition term234 (x0 : nat) := (forall y0 : nat, (fun y1 : nat => (~ (Peano.le x0 y1)) \/ (~ (Peano.lt y1 x0))) y0) /\ (forall y0 : nat, (fun y1 : nat => (Peano.le x0 y1) \/ (Peano.lt y1 x0)) y0).
Definition term199 := (forall y0 : nat, (fun y1 : nat => (Peano.le y1 (NUMERAL 0)) \/ (~ (y1 = (NUMERAL 0)))) y0) /\ (forall y0 : nat, (fun y1 : nat => (~ (Peano.le y1 (NUMERAL 0))) \/ (y1 = (NUMERAL 0))) y0).
Definition term275 := (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0))) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.lt y1 y0)).
Definition term230 (x0 : nat) := forall y0 : nat, ((~ (Peano.le x0 y0)) \/ (~ (Peano.lt y0 x0))) /\ ((Peano.le x0 y0) \/ (Peano.lt y0 x0)).
Definition term296 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (~ (x1 = (NUMERAL 0))) -> (y0 = (Nat.mul x0 x1)) -> (~ (exists y1 : nat, ((Nat.mul x1 x0) = (Nat.mul x1 y1)) /\ (Peano.lt (NUMERAL 0) x1))) -> (forall y1 : nat, (Peano.le y1 (NUMERAL 0)) = (y1 = (NUMERAL 0))) -> (forall y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) = (Peano.lt y2 y1)) -> False) x2.
Definition term293 (x0 : nat) := (Peano.lt (NUMERAL 0) x0) -> False.
Definition term156 (x0 : nat) (x1 : nat) (x2 : nat) := imp (x0 = (Nat.mul x1 x2)).
Definition term7 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, ((x1 = (Nat.add (Nat.mul x0 x2) y0)) /\ (Peano.lt y0 x2)) -> (Nat.modulo x1 x2) = y0.
Definition term182 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((Nat.mul x1 x0) = (Nat.mul x1 x2)).
Definition term158 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = (Nat.mul x1 x2)) -> (~ ((exists y0 : nat, (Nat.mul x2 x1) = (Nat.mul x2 y0)) /\ (Peano.lt (NUMERAL 0) x2))) -> (forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) -> ~ (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)).
Definition term251 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (Peano.le x0 y1) \/ (Peano.lt y1 x0)) y0.
Definition term246 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (~ (Peano.le x0 y1)) \/ (~ (Peano.lt y1 x0))) y0.
Definition term218 := forall y0 : nat, (fun y1 : nat => (~ (Peano.le y1 (NUMERAL 0))) \/ (y1 = (NUMERAL 0))) y0.
Definition term213 := forall y0 : nat, (fun y1 : nat => (Peano.le y1 (NUMERAL 0)) \/ (~ (y1 = (NUMERAL 0)))) y0.
Definition term238 (x0 : nat) (x1 : nat) := (~ (Peano.le x1 x0)) \/ (~ (Peano.lt x0 x1)).
Definition term279 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.mul x1 x0) = (Nat.mul x1 x2)) -> False.
Definition term100 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.mul (Nat.div x0 x2) x2) = (Nat.mul x1 x2)) -> False.
Definition term240 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le x0 y0) \/ (Peano.lt y0 x0)) x1.
Definition term21 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (exists y1 : nat, (x0 = (Nat.add (Nat.mul y1 x1) y0)) /\ (Peano.lt y0 x1)) -> (Nat.modulo x0 x1) = y0) x2.
Definition term283 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term196 (x0 : nat -> Prop) (x1 : nat -> Prop) := forall y0 : nat, (x0 y0) /\ (x1 y0).
Definition term123 (x0 : nat) (x1 : nat) (x2 : nat) := ((~ (x2 = (NUMERAL 0))) -> (x0 = (Nat.mul x1 x2)) -> (~ (exists y0 : nat, ((Nat.mul x2 x1) = (Nat.mul x2 y0)) /\ (Peano.lt (NUMERAL 0) x2))) -> (forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False) -> (~ (x2 = (NUMERAL 0))) -> (x0 = (Nat.mul x1 x2)) -> (~ (exists y0 : nat, ((Nat.mul x2 x1) = (Nat.mul x2 y0)) /\ (Peano.lt (NUMERAL 0) x2))) -> (forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False.
Definition term254 := fun y0 : nat => (forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0))) /\ (forall y1 : nat, (Peano.le y0 y1) \/ (Peano.lt y1 y0)).
Definition term149 := ~ (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)).
Definition term61 (x0 : nat) := (fun y0 : nat => (Nat.add y0 (NUMERAL 0)) = y0) x0.
Definition term36 (x0 : nat) := (fun y0 : nat => (Nat.modulo y0 (NUMERAL 0)) = y0) x0.
Definition term28 (x0 : nat) (x1 : nat) := (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1).
Definition term201 := fun y0 : nat => (~ (Peano.le y0 (NUMERAL 0))) \/ (y0 = (NUMERAL 0)).
Definition term12 (x0 : nat) (x1 : nat) (x2 : nat) := exists y0 : nat, (x0 = (Nat.add (Nat.mul y0 x2) x1)) /\ (Peano.lt x1 x2).
Definition term147 (x0 : nat) (x1 : nat) := imp (~ ((exists y0 : nat, (Nat.mul x1 x0) = (Nat.mul x1 y0)) /\ (Peano.lt (NUMERAL 0) x1))).
Definition term112 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.mul x2 x0) = (Nat.mul x1 x2)) /\ (Peano.lt (NUMERAL 0) x2).
Definition term99 (x0 : Prop) := (~ x0) -> x0.
Definition term32 := (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> forall y1 : nat, (y1 = (Nat.add (Nat.mul (Nat.div y1 y0) y0) (Nat.modulo y1 y0))) /\ (Peano.lt (Nat.modulo y1 y0) y0).
Definition term184 (x0 : nat) (x1 : nat) := fun y0 : nat => ~ ((Nat.mul x1 x0) = (Nat.mul x1 y0)).
Definition term159 (x0 : nat) := imp (~ (x0 = (NUMERAL 0))).
Definition term122 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x2 = (NUMERAL 0))) -> (x0 = (Nat.mul x1 x2)) -> (~ (exists y0 : nat, ((Nat.mul x2 x1) = (Nat.mul x2 y0)) /\ (Peano.lt (NUMERAL 0) x2))) -> (forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False.
Definition term104 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (exists y1 : nat, (Nat.mul (Nat.div y0 x0) x0) = (Nat.mul y1 x0))) -> False) x1.
Definition term10 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x0 = (Nat.add (Nat.mul x1 x3) x2)) /\ (Peano.lt x2 x3).
Definition term142 (x0 : nat) (x1 : nat) := and (exists y0 : nat, (fun y1 : nat => (Nat.mul x1 x0) = (Nat.mul x1 y1)) y0).
Definition term235 (x0 : nat) := fun y0 : nat => (~ (Peano.le x0 y0)) \/ (~ (Peano.lt y0 x0)).
Definition term229 (x0 : nat) := fun y0 : nat => ((~ (Peano.le x0 y0)) \/ (~ (Peano.lt y0 x0))) /\ ((Peano.le x0 y0) \/ (Peano.lt y0 x0)).
Definition term120 (x0 : nat) (x1 : nat) := (~ (exists y0 : nat, ((Nat.mul x1 x0) = (Nat.mul x1 y0)) /\ (Peano.lt (NUMERAL 0) x1))) -> False.
Definition term72 (x0 : nat) (x1 : nat) := (~ (exists y0 : nat, (Nat.mul (Nat.div x0 x1) x1) = (Nat.mul y0 x1))) -> False.
Definition term207 (x0 : nat) := (~ (Peano.le x0 (NUMERAL 0))) \/ (x0 = (NUMERAL 0)).
Definition term63 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul (Nat.div x0 x1) x1).
Definition term266 := @eq Prop (forall y0 : nat, (forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0))) /\ (forall y1 : nat, (Peano.le y0 y1) \/ (Peano.lt y1 y0))).
Definition term265 := @eq Prop (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 y2)) \/ (~ (Peano.lt y2 y1))) y0) /\ ((fun y1 : nat => forall y2 : nat, (Peano.le y1 y2) \/ (Peano.lt y2 y1)) y0)).
Definition term244 (x0 : nat) := @eq Prop (forall y0 : nat, ((~ (Peano.le x0 y0)) \/ (~ (Peano.lt y0 x0))) /\ ((Peano.le x0 y0) \/ (Peano.lt y0 x0))).
Definition term243 (x0 : nat) := @eq Prop (forall y0 : nat, ((fun y1 : nat => (~ (Peano.le x0 y1)) \/ (~ (Peano.lt y1 x0))) y0) /\ ((fun y1 : nat => (Peano.le x0 y1) \/ (Peano.lt y1 x0)) y0)).
Definition term211 := @eq Prop (forall y0 : nat, ((Peano.le y0 (NUMERAL 0)) \/ (~ (y0 = (NUMERAL 0)))) /\ ((~ (Peano.le y0 (NUMERAL 0))) \/ (y0 = (NUMERAL 0)))).
Definition term210 := @eq Prop (forall y0 : nat, ((fun y1 : nat => (Peano.le y1 (NUMERAL 0)) \/ (~ (y1 = (NUMERAL 0)))) y0) /\ ((fun y1 : nat => (~ (Peano.le y1 (NUMERAL 0))) \/ (y1 = (NUMERAL 0))) y0)).
Definition term51 (x0 : nat) (x1 : nat) := (fun y0 : nat => (y0 = (Nat.add (Nat.mul (Nat.div y0 x0) x0) (Nat.modulo y0 x0))) /\ (Peano.lt (Nat.modulo y0 x0) x0)) x1.
Definition term80 (x0 : nat) := fun y0 : nat => exists y1 : nat, (Nat.mul (Nat.div y0 x0) x0) = (Nat.mul y1 x0).
Definition term42 (x0 : nat) (x1 : nat) := @eq nat (Nat.modulo x0 x1).
Definition term195 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term62 (x0 : nat) := Nat.add x0 (NUMERAL 0).
Definition term103 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (exists y2 : nat, (Nat.mul (Nat.div y1 y0) y0) = (Nat.mul y2 y0))) -> False) x0.
Definition term297 (x0 : nat) (x1 : nat) := (exists y0 : nat, x0 = (Nat.mul y0 x1)) -> (Nat.modulo x0 x1) = (NUMERAL 0).
Definition term105 (x0 : nat) (x1 : nat) := (exists y0 : nat, (x0 = (Nat.add (Nat.mul y0 x1) (NUMERAL 0))) /\ (Peano.lt (NUMERAL 0) x1)) -> (Nat.modulo x0 x1) = (NUMERAL 0).
Definition term56 (x0 : nat) (x1 : nat) := exists y0 : nat, (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.mul y0 x1).
Definition term295 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (~ (x0 = (NUMERAL 0))) -> (y1 = (Nat.mul y0 x0)) -> (~ (exists y2 : nat, ((Nat.mul x0 y0) = (Nat.mul x0 y2)) /\ (Peano.lt (NUMERAL 0) x0))) -> (forall y2 : nat, (Peano.le y2 (NUMERAL 0)) = (y2 = (NUMERAL 0))) -> (forall y2 : nat, forall y3 : nat, (~ (Peano.le y2 y3)) = (Peano.lt y3 y2)) -> False) x1.
Definition term20 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (exists y2 : nat, (x0 = (Nat.add (Nat.mul y2 y0) y1)) /\ (Peano.lt y1 y0)) -> (Nat.modulo x0 y0) = y1) x1.
Definition term284 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> ~ (Peano.le x0 (NUMERAL 0)).
Definition term66 (x0 : nat) (x1 : nat) := @eq nat (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)).
Definition term146 (x0 : nat) (x1 : nat) := imp (~ (exists y0 : nat, ((Nat.mul x1 x0) = (Nat.mul x1 y0)) /\ (Peano.lt (NUMERAL 0) x1))).
Definition term227 (x0 : nat) (x1 : nat) := ((~ (Peano.le x1 x0)) \/ (~ (Peano.lt x0 x1))) /\ ((~ (~ (Peano.le x1 x0))) \/ (Peano.lt x0 x1)).
Definition term27 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term259 := fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) \/ (Peano.lt y1 y0).
Definition term176 := fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0).
Definition term252 (x0 : nat) := forall y0 : nat, (Peano.le x0 y0) \/ (Peano.lt y0 x0).
Definition term45 (x0 : nat) (x1 : nat) := fun y0 : nat => x0 = (Nat.mul y0 x1).
Definition term65 (x0 : nat) (x1 : nat) := Nat.mul (Nat.div x0 x1) x1.
Definition term138 (x0 : nat) (x1 : nat) := @eq Prop (exists y0 : nat, ((Nat.mul x1 x0) = (Nat.mul x1 y0)) /\ (Peano.lt (NUMERAL 0) x1)).
Definition term137 (x0 : nat) (x1 : nat) := @eq Prop (exists y0 : nat, ((fun y1 : nat => (Nat.mul x1 x0) = (Nat.mul x1 y1)) y0) /\ (Peano.lt (NUMERAL 0) x1)).
Definition term58 (x0 : nat) (x1 : nat) := @eq Prop (exists y0 : nat, x0 = (Nat.mul y0 x1)).
Definition term204 (x0 : nat) := and ((fun y0 : nat => (Peano.le y0 (NUMERAL 0)) \/ (~ (y0 = (NUMERAL 0)))) x0).
Definition term57 (x0 : nat) (x1 : nat) := @eq Prop ((fun y0 : nat => exists y1 : nat, y0 = (Nat.mul y1 x0)) x1).
Definition term60 := forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0.
Definition term208 (x0 : nat) := ((fun y0 : nat => (Peano.le y0 (NUMERAL 0)) \/ (~ (y0 = (NUMERAL 0)))) x0) /\ ((fun y0 : nat => (~ (Peano.le y0 (NUMERAL 0))) \/ (y0 = (NUMERAL 0))) x0).
Definition term224 (x0 : nat) (x1 : nat) := (~ (~ (Peano.le x1 x0))) \/ (Peano.lt x0 x1).
Definition term101 (x0 : nat) (x1 : nat) := ((Nat.mul (Nat.div x0 x1) x1) = (Nat.mul (Nat.div x0 x1) x1)) -> False.
Definition term131 (x0 : nat) (x1 : nat) := (exists y0 : nat, (fun y1 : nat => (Nat.mul x1 x0) = (Nat.mul x1 y1)) y0) /\ (Peano.lt (NUMERAL 0) x1).
Definition term43 (x0 : nat) (x1 : nat) := @eq Prop ((Nat.modulo x0 x1) = (NUMERAL 0)).
Definition term97 (x0 : nat) (x1 : nat) := (~ ((Nat.mul (Nat.div x0 x1) x1) = (Nat.mul (Nat.div x0 x1) x1))) -> (Nat.mul (Nat.div x0 x1) x1) = (Nat.mul (Nat.div x0 x1) x1).
Definition term173 (x0 : nat) (x1 : nat) := ~ (Peano.le x0 x1).
Definition term245 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (~ (Peano.le x0 y1)) \/ (~ (Peano.lt y1 x0))) y0.
Definition term212 := fun y0 : nat => (fun y1 : nat => (Peano.le y1 (NUMERAL 0)) \/ (~ (y1 = (NUMERAL 0)))) y0.
Definition term223 (x0 : nat) (x1 : nat) := or (Peano.le x0 x1).
Definition term40 (x0 : nat) := (fun y0 : nat => (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) x0.
Definition term148 := (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False.
Definition term113 (x0 : nat) (x1 : nat) := fun y0 : nat => (x0 = (Nat.add (Nat.mul y0 x1) (NUMERAL 0))) /\ (Peano.lt (NUMERAL 0) x1).
Definition term190 (x0 : nat) (x1 : nat) := (forall y0 : nat, ~ ((Nat.mul x1 x0) = (Nat.mul x1 y0))) \/ (~ (Peano.lt (NUMERAL 0) x1)).
Definition term164 (x0 : nat) (x1 : nat) := forall y0 : nat, (~ (x1 = (NUMERAL 0))) -> (y0 = (Nat.mul x0 x1)) -> (~ ((exists y1 : nat, (Nat.mul x1 x0) = (Nat.mul x1 y1)) /\ (Peano.lt (NUMERAL 0) x1))) -> (forall y1 : nat, (Peano.le y1 (NUMERAL 0)) = (y1 = (NUMERAL 0))) -> ~ (forall y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) = (Peano.lt y2 y1)).
Definition term163 (x0 : nat) (x1 : nat) := forall y0 : nat, (~ (x1 = (NUMERAL 0))) -> (y0 = (Nat.mul x0 x1)) -> (~ (exists y1 : nat, ((Nat.mul x1 x0) = (Nat.mul x1 y1)) /\ (Peano.lt (NUMERAL 0) x1))) -> (forall y1 : nat, (Peano.le y1 (NUMERAL 0)) = (y1 = (NUMERAL 0))) -> (forall y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) = (Peano.lt y2 y1)) -> False.
Definition term125 (x0 : nat) (x1 : nat) (x2 : nat) := (((~ (x2 = (NUMERAL 0))) -> (x0 = (Nat.mul x1 x2)) -> (~ (exists y0 : nat, ((Nat.mul x2 x1) = (Nat.mul x2 y0)) /\ (Peano.lt (NUMERAL 0) x2))) -> (forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False) -> (~ (x2 = (NUMERAL 0))) -> (x0 = (Nat.mul x1 x2)) -> (~ (exists y0 : nat, ((Nat.mul x2 x1) = (Nat.mul x2 y0)) /\ (Peano.lt (NUMERAL 0) x2))) -> (forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False) -> ((~ (x2 = (NUMERAL 0))) -> (x0 = (Nat.mul x1 x2)) -> (~ (exists y0 : nat, ((Nat.mul x2 x1) = (Nat.mul x2 y0)) /\ (Peano.lt (NUMERAL 0) x2))) -> (forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False) -> (~ (x2 = (NUMERAL 0))) -> (x0 = (Nat.mul x1 x2)) -> (~ (exists y0 : nat, ((Nat.mul x2 x1) = (Nat.mul x2 y0)) /\ (Peano.lt (NUMERAL 0) x2))) -> (forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False.
Definition term151 := imp (forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))).
Definition term31 := forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> forall y1 : nat, (y1 = (Nat.add (Nat.mul (Nat.div y1 y0) y0) (Nat.modulo y1 y0))) /\ (Peano.lt (Nat.modulo y1 y0) y0).
Definition term249 (x0 : nat) := and (forall y0 : nat, (~ (Peano.le x0 y0)) \/ (~ (Peano.lt y0 x0))).
Definition term216 := and (forall y0 : nat, (Peano.le y0 (NUMERAL 0)) \/ (~ (y0 = (NUMERAL 0)))).
Definition term185 (x0 : nat) (x1 : nat) := forall y0 : nat, ~ ((Nat.mul x1 x0) = (Nat.mul x1 y0)).
Definition term95 (x0 : nat) (x1 : nat) := forall y0 : nat, ~ ((Nat.mul (Nat.div x0 x1) x1) = (Nat.mul y0 x1)).
Definition term50 (x0 : Prop) := exists y0 : nat, x0.
Definition term55 (x0 : nat) (x1 : nat) := (fun y0 : nat => exists y1 : nat, y0 = (Nat.mul y1 x1)) (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)).
Definition term92 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((Nat.mul (Nat.div x0 x2) x2) = (Nat.mul x1 x2)).
Definition term9 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((x1 = (Nat.add (Nat.mul x0 x2) x3)) /\ (Peano.lt x3 x2)) -> (Nat.modulo x1 x2) = x3.
Definition term74 (x0 : nat) (x1 : nat) := ((~ (exists y0 : nat, (Nat.mul (Nat.div x0 x1) x1) = (Nat.mul y0 x1))) -> False) -> (~ (exists y0 : nat, (Nat.mul (Nat.div x0 x1) x1) = (Nat.mul y0 x1))) -> False.
Definition term133 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.mul x1 x0) = (Nat.mul x1 y0)) x2.
Definition term288 (x0 : nat) (x1 : nat) := @eq Prop ((Peano.le x1 x0) \/ (Peano.lt x0 x1)).
Definition term115 (x0 : nat) (x1 : nat) (x2 : nat) := and ((Nat.mul x1 x0) = (Nat.mul x1 x2)).
Definition term109 (x0 : nat) (x1 : nat) (x2 : nat) := and ((Nat.mul x2 x0) = (Nat.mul x1 x2)).
Definition term276 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ~ ((Nat.mul x1 x0) = (Nat.mul x1 y0))) x2.
Definition term153 := (forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) -> ~ (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)).
Definition term8 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => ((x1 = (Nat.add (Nat.mul x0 x2) y0)) /\ (Peano.lt y0 x2)) -> (Nat.modulo x1 x2) = y0) x3.
Definition term217 := fun y0 : nat => (fun y1 : nat => (~ (Peano.le y1 (NUMERAL 0))) \/ (y1 = (NUMERAL 0))) y0.
Definition term98 (x0 : nat) (x1 : nat) := ~ ((Nat.mul (Nat.div x0 x1) x1) = (Nat.mul (Nat.div x0 x1) x1)).
Definition term54 (x0 : nat) (x1 : nat) := (fun y0 : nat => exists y1 : nat, y0 = (Nat.mul y1 x0)) x1.
Definition term301 := forall y0 : nat, forall y1 : nat, ((Nat.modulo y0 y1) = (NUMERAL 0)) = (exists y2 : nat, y0 = (Nat.mul y2 y1)).
Definition term274 := forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.lt y1 y0).
Definition term269 := forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0)).
Definition term232 := forall y0 : nat, forall y1 : nat, ((~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0))) /\ ((Peano.le y0 y1) \/ (Peano.lt y1 y0)).
Definition term172 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (~ (y0 = (NUMERAL 0))) -> (y2 = (Nat.mul y1 y0)) -> (~ ((exists y3 : nat, (Nat.mul y0 y1) = (Nat.mul y0 y3)) /\ (Peano.lt (NUMERAL 0) y0))) -> (forall y3 : nat, (Peano.le y3 (NUMERAL 0)) = (y3 = (NUMERAL 0))) -> ~ (forall y3 : nat, forall y4 : nat, (~ (Peano.le y3 y4)) = (Peano.lt y4 y3)).
Definition term171 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (~ (y0 = (NUMERAL 0))) -> (y2 = (Nat.mul y1 y0)) -> (~ (exists y3 : nat, ((Nat.mul y0 y1) = (Nat.mul y0 y3)) /\ (Peano.lt (NUMERAL 0) y0))) -> (forall y3 : nat, (Peano.le y3 (NUMERAL 0)) = (y3 = (NUMERAL 0))) -> (forall y3 : nat, forall y4 : nat, (~ (Peano.le y3 y4)) = (Peano.lt y4 y3)) -> False.
Definition term168 (x0 : nat) := forall y0 : nat, forall y1 : nat, (~ (x0 = (NUMERAL 0))) -> (y1 = (Nat.mul y0 x0)) -> (~ ((exists y2 : nat, (Nat.mul x0 y0) = (Nat.mul x0 y2)) /\ (Peano.lt (NUMERAL 0) x0))) -> (forall y2 : nat, (Peano.le y2 (NUMERAL 0)) = (y2 = (NUMERAL 0))) -> ~ (forall y2 : nat, forall y3 : nat, (~ (Peano.le y2 y3)) = (Peano.lt y3 y2)).
Definition term167 (x0 : nat) := forall y0 : nat, forall y1 : nat, (~ (x0 = (NUMERAL 0))) -> (y1 = (Nat.mul y0 x0)) -> (~ (exists y2 : nat, ((Nat.mul x0 y0) = (Nat.mul x0 y2)) /\ (Peano.lt (NUMERAL 0) x0))) -> (forall y2 : nat, (Peano.le y2 (NUMERAL 0)) = (y2 = (NUMERAL 0))) -> (forall y2 : nat, forall y3 : nat, (~ (Peano.le y2 y3)) = (Peano.lt y3 y2)) -> False.
Definition term150 := forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0).
Definition term86 := forall y0 : nat, forall y1 : nat, exists y2 : nat, (Nat.mul (Nat.div y1 y0) y0) = (Nat.mul y2 y0).
Definition term85 := forall y0 : nat, forall y1 : nat, (~ (exists y2 : nat, (Nat.mul (Nat.div y1 y0) y0) = (Nat.mul y2 y0))) -> False.
Definition term22 := forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1).
Definition term17 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (exists y3 : nat, (y0 = (Nat.add (Nat.mul y3 y1) y2)) /\ (Peano.lt y2 y1)) -> (Nat.modulo y0 y1) = y2.
Definition term16 (x0 : nat) := forall y0 : nat, forall y1 : nat, (exists y2 : nat, (x0 = (Nat.add (Nat.mul y2 y0) y1)) /\ (Peano.lt y1 y0)) -> (Nat.modulo x0 y0) = y1.
Definition term5 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, ((x0 = (Nat.add (Nat.mul y0 x1) y1)) /\ (Peano.lt y1 x1)) -> (Nat.modulo x0 x1) = y1.
Definition term3 (x0 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((x0 = (Nat.add (Nat.mul y1 y0) y2)) /\ (Peano.lt y2 y0)) -> (Nat.modulo x0 y0) = y2.
Definition term1 := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y0 = (Nat.add (Nat.mul y2 y1) y3)) /\ (Peano.lt y3 y1)) -> (Nat.modulo y0 y1) = y3.
Definition term94 (x0 : nat) (x1 : nat) := fun y0 : nat => ~ ((Nat.mul (Nat.div x0 x1) x1) = (Nat.mul y0 x1)).
Definition term181 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((fun y0 : nat => (Nat.mul x1 x0) = (Nat.mul x1 y0)) x2).
Definition term91 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((fun y0 : nat => (Nat.mul (Nat.div x0 x1) x1) = (Nat.mul y0 x1)) x2).
Definition term263 (x0 : nat) := ((fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0))) x0) /\ ((fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) \/ (Peano.lt y1 y0)) x0).
Definition term126 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) /\ x1.
Definition term35 (x0 : nat) := (x0 = (NUMERAL 0)) \/ (~ (x0 = (NUMERAL 0))).
Definition term87 (x0 : nat -> Prop) := ~ (ex x0).
Definition term6 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => forall y1 : nat, ((x0 = (Nat.add (Nat.mul y0 x1) y1)) /\ (Peano.lt y1 x1)) -> (Nat.modulo x0 x1) = y1) x2.
Definition term175 (x0 : nat) := forall y0 : nat, (~ (Peano.le x0 y0)) = (Peano.lt y0 x0).
Definition term4 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((x0 = (Nat.add (Nat.mul y1 y0) y2)) /\ (Peano.lt y2 y0)) -> (Nat.modulo x0 y0) = y2) x1.
Definition term226 (x0 : nat) (x1 : nat) := and ((~ (Peano.le x1 x0)) \/ (~ (Peano.lt x0 x1))).
Definition term79 (x0 : nat) := fun y0 : nat => (~ (exists y1 : nat, (Nat.mul (Nat.div y0 x0) x0) = (Nat.mul y1 x0))) -> False.
Definition term202 (x0 : nat) := (fun y0 : nat => (Peano.le y0 (NUMERAL 0)) \/ (~ (y0 = (NUMERAL 0)))) x0.
Definition term124 (x0 : nat) (x1 : nat) (x2 : nat) := (((~ (x2 = (NUMERAL 0))) -> (x0 = (Nat.mul x1 x2)) -> (~ (exists y0 : nat, ((Nat.mul x2 x1) = (Nat.mul x2 y0)) /\ (Peano.lt (NUMERAL 0) x2))) -> (forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False) -> (~ (x2 = (NUMERAL 0))) -> (x0 = (Nat.mul x1 x2)) -> (~ (exists y0 : nat, ((Nat.mul x2 x1) = (Nat.mul x2 y0)) /\ (Peano.lt (NUMERAL 0) x2))) -> (forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False) -> (~ (x2 = (NUMERAL 0))) -> (x0 = (Nat.mul x1 x2)) -> (~ (exists y0 : nat, ((Nat.mul x2 x1) = (Nat.mul x2 y0)) /\ (Peano.lt (NUMERAL 0) x2))) -> (forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False.
Definition term286 (x0 : nat) := (Peano.le x0 (NUMERAL 0)) -> ~ (Peano.le x0 (NUMERAL 0)).
Definition term130 (x0 : nat) (x1 : nat) := exists y0 : nat, ((fun y1 : nat => (Nat.mul x1 x0) = (Nat.mul x1 y1)) y0) /\ (Peano.lt (NUMERAL 0) x1).
Definition term26 (x0 : nat) (x1 : nat) := (~ (x1 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1).
Definition term155 (x0 : nat) (x1 : nat) := (~ ((exists y0 : nat, (Nat.mul x1 x0) = (Nat.mul x1 y0)) /\ (Peano.lt (NUMERAL 0) x1))) -> (forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) -> ~ (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)).
Definition term88 (x0 : nat -> Prop) := forall y0 : nat, ~ (x0 y0).
Definition term11 (x0 : nat) (x1 : nat) (x2 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y0 = (Nat.add (Nat.mul y2 y1) y3)) /\ (Peano.lt y3 y1)) -> (Nat.modulo y0 y1) = y3) -> (Nat.modulo x0 x1) = x2.
Definition term278 (x0 : nat) (x1 : nat) := ~ ((Nat.mul x0 x1) = (Nat.mul x0 x1)).
Definition term178 := fun y0 : nat => (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0)).
Definition term128 (x0 : nat -> Prop) (x1 : Prop) := exists y0 : nat, (x0 y0) /\ x1.
Definition term225 (x0 : nat) (x1 : nat) := (Peano.le x1 x0) \/ (Peano.lt x0 x1).
Definition term291 (x0 : nat) := (~ (Peano.le x0 (NUMERAL 0))) -> Peano.lt (NUMERAL 0) x0.
Definition term162 (x0 : nat) (x1 : nat) := fun y0 : nat => (~ (x1 = (NUMERAL 0))) -> (y0 = (Nat.mul x0 x1)) -> (~ ((exists y1 : nat, (Nat.mul x1 x0) = (Nat.mul x1 y1)) /\ (Peano.lt (NUMERAL 0) x1))) -> (forall y1 : nat, (Peano.le y1 (NUMERAL 0)) = (y1 = (NUMERAL 0))) -> ~ (forall y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) = (Peano.lt y2 y1)).
Definition term161 (x0 : nat) (x1 : nat) := fun y0 : nat => (~ (x1 = (NUMERAL 0))) -> (y0 = (Nat.mul x0 x1)) -> (~ (exists y1 : nat, ((Nat.mul x1 x0) = (Nat.mul x1 y1)) /\ (Peano.lt (NUMERAL 0) x1))) -> (forall y1 : nat, (Peano.le y1 (NUMERAL 0)) = (y1 = (NUMERAL 0))) -> (forall y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) = (Peano.lt y2 y1)) -> False.
Definition term188 (x0 : nat) (x1 : nat) := or (forall y0 : nat, ~ ((Nat.mul x1 x0) = (Nat.mul x1 y0))).
Definition term205 (x0 : nat) := and ((Peano.le x0 (NUMERAL 0)) \/ (~ (x0 = (NUMERAL 0)))).
Definition term241 (x0 : nat) (x1 : nat) := ((fun y0 : nat => (~ (Peano.le x0 y0)) \/ (~ (Peano.lt y0 x0))) x1) /\ ((fun y0 : nat => (Peano.le x0 y0) \/ (Peano.lt y0 x0)) x1).
Definition term197 (x0 : nat -> Prop) (x1 : nat -> Prop) := (forall y0 : nat, x0 y0) /\ (forall y0 : nat, x1 y0).
Definition term47 (x0 : nat) (x1 : nat) := exists y0 : nat, x0 = (Nat.mul y0 x1).
Definition term81 (x0 : nat) := forall y0 : nat, (~ (exists y1 : nat, (Nat.mul (Nat.div y0 x0) x0) = (Nat.mul y1 x0))) -> False.
Definition term281 (x0 : nat) := (x0 = (NUMERAL 0)) -> ~ (x0 = (NUMERAL 0)).
Definition term292 (x0 : nat) := (~ (Peano.lt (NUMERAL 0) x0)) -> Peano.lt (NUMERAL 0) x0.
Definition term90 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.mul (Nat.div x0 x1) x1) = (Nat.mul y0 x1)) x2.
Definition term290 (x0 : nat) (x1 : nat) := (~ (Peano.le x1 x0)) -> Peano.lt x0 x1.
Definition term140 (x0 : nat) (x1 : nat) := exists y0 : nat, (fun y1 : nat => (Nat.mul x1 x0) = (Nat.mul x1 y1)) y0.
Definition term75 (x0 : nat) (x1 : nat) := (((~ (exists y0 : nat, (Nat.mul (Nat.div x0 x1) x1) = (Nat.mul y0 x1))) -> False) -> (~ (exists y0 : nat, (Nat.mul (Nat.div x0 x1) x1) = (Nat.mul y0 x1))) -> False) -> (~ (exists y0 : nat, (Nat.mul (Nat.div x0 x1) x1) = (Nat.mul y0 x1))) -> False.
Definition term214 := forall y0 : nat, (Peano.le y0 (NUMERAL 0)) \/ (~ (y0 = (NUMERAL 0))).
Definition term49 (a0 : Type') (x0 : Prop) := exists y0 : a0, x0.
Definition term59 := (forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))).
Definition term277 (x0 : nat) (x1 : nat) := (~ ((Nat.mul x0 x1) = (Nat.mul x0 x1))) -> (Nat.mul x0 x1) = (Nat.mul x0 x1).
Definition term83 := fun y0 : nat => forall y1 : nat, (~ (exists y2 : nat, (Nat.mul (Nat.div y1 y0) y0) = (Nat.mul y2 y0))) -> False.
Definition term200 := fun y0 : nat => (Peano.le y0 (NUMERAL 0)) \/ (~ (y0 = (NUMERAL 0))).
Definition term117 (x0 : nat) (x1 : nat) := fun y0 : nat => ((Nat.mul x1 x0) = (Nat.mul x1 y0)) /\ (Peano.lt (NUMERAL 0) x1).
Definition term114 (x0 : nat) (x1 : nat) := fun y0 : nat => ((Nat.mul x1 x0) = (Nat.mul y0 x1)) /\ (Peano.lt (NUMERAL 0) x1).
Definition term219 := forall y0 : nat, (~ (Peano.le y0 (NUMERAL 0))) \/ (y0 = (NUMERAL 0)).
Definition term157 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = (Nat.mul x1 x2)) -> (~ (exists y0 : nat, ((Nat.mul x2 x1) = (Nat.mul x2 y0)) /\ (Peano.lt (NUMERAL 0) x2))) -> (forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False.
Definition term29 (x0 : nat) := forall y0 : nat, (y0 = (Nat.add (Nat.mul (Nat.div y0 x0) x0) (Nat.modulo y0 x0))) /\ (Peano.lt (Nat.modulo y0 x0) x0).
Definition term298 (x0 : nat) (x1 : nat) := ((Nat.modulo x0 x1) = (NUMERAL 0)) -> exists y0 : nat, x0 = (Nat.mul y0 x1).
Definition term111 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = (Nat.add (Nat.mul x1 x2) (NUMERAL 0))) /\ (Peano.lt (NUMERAL 0) x2).
Definition term68 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.mul y0 x1).
Definition term253 (x0 : nat) := (forall y0 : nat, (~ (Peano.le x0 y0)) \/ (~ (Peano.lt y0 x0))) /\ (forall y0 : nat, (Peano.le x0 y0) \/ (Peano.lt y0 x0)).
Definition term220 := (forall y0 : nat, (Peano.le y0 (NUMERAL 0)) \/ (~ (y0 = (NUMERAL 0)))) /\ (forall y0 : nat, (~ (Peano.le y0 (NUMERAL 0))) \/ (y0 = (NUMERAL 0))).
Definition term15 (x0 : nat) (x1 : nat) := forall y0 : nat, (exists y1 : nat, (x0 = (Nat.add (Nat.mul y1 x1) y0)) /\ (Peano.lt y0 x1)) -> (Nat.modulo x0 x1) = y0.
Definition term280 (x0 : nat) (x1 : nat) := ((Nat.mul x0 x1) = (Nat.mul x0 x1)) -> False.
Definition term64 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul (Nat.div x0 x1) x1) (NUMERAL 0).
Definition term271 := and (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0))).
Definition term129 (x0 : nat -> Prop) (x1 : Prop) := (exists y0 : nat, x0 y0) /\ x1.
Definition term180 (x0 : nat) (x1 : nat) := forall y0 : nat, ~ ((fun y1 : nat => (Nat.mul x1 x0) = (Nat.mul x1 y1)) y0).
Definition term89 (x0 : nat) (x1 : nat) := forall y0 : nat, ~ ((fun y1 : nat => (Nat.mul (Nat.div x0 x1) x1) = (Nat.mul y1 x1)) y0).
Definition term272 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (Peano.le y1 y2) \/ (Peano.lt y2 y1)) y0.
Definition term267 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 y2)) \/ (~ (Peano.lt y2 y1))) y0.
Definition term262 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) \/ (Peano.lt y1 y0)) x0.
Definition term260 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0))) x0.
Definition term23 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) x0.
Definition term39 := forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0).
Definition term221 (x0 : nat) (x1 : nat) := ~ (~ (Peano.le x0 x1)).
Definition term143 (x0 : nat) (x1 : nat) := and (exists y0 : nat, (Nat.mul x1 x0) = (Nat.mul x1 y0)).
Definition term41 (x0 : nat) := Nat.mul x0 (NUMERAL 0).
Definition term67 (x0 : nat) (x1 : nat) := @eq nat (Nat.mul (Nat.div x0 x1) x1).
Definition term141 (x0 : nat) (x1 : nat) := exists y0 : nat, (Nat.mul x1 x0) = (Nat.mul x1 y0).
Definition term236 (x0 : nat) := fun y0 : nat => (Peano.le x0 y0) \/ (Peano.lt y0 x0).
Definition term247 (x0 : nat) := forall y0 : nat, (~ (Peano.le x0 y0)) \/ (~ (Peano.lt y0 x0)).
Definition term70 (x0 : nat) (x1 : nat) := exists y0 : nat, (Nat.mul (Nat.div x0 x1) x1) = (Nat.mul y0 x1).
Definition term0 := forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0)).
Definition term289 (x0 : nat) (x1 : nat) := @eq Prop ((Peano.lt x1 x0) \/ (Peano.le x0 x1)).
Definition term250 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (Peano.le x0 y1) \/ (Peano.lt y1 x0)) y0.
Definition term270 := and (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 y2)) \/ (~ (Peano.lt y2 y1))) y0).
Definition term248 (x0 : nat) := and (forall y0 : nat, (fun y1 : nat => (~ (Peano.le x0 y1)) \/ (~ (Peano.lt y1 x0))) y0).
Definition term215 := and (forall y0 : nat, (fun y1 : nat => (Peano.le y1 (NUMERAL 0)) \/ (~ (y1 = (NUMERAL 0)))) y0).
Definition term261 (x0 : nat) := and ((fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0))) x0).
Definition term46 (x0 : nat) := fun y0 : nat => x0 = (NUMERAL 0).
Definition term25 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0)) x1.
Definition term116 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.mul x2 x0) = (Nat.mul x2 x1)) /\ (Peano.lt (NUMERAL 0) x2).
Definition term106 (x0 : nat) (x1 : nat) := @eq nat (Nat.mul x0 x1).
Definition term30 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> forall y0 : nat, (y0 = (Nat.add (Nat.mul (Nat.div y0 x0) x0) (Nat.modulo y0 x0))) /\ (Peano.lt (Nat.modulo y0 x0) x0).
Definition term53 (x0 : nat) := fun y0 : nat => exists y1 : nat, y0 = (Nat.mul y1 x0).
Definition term139 (x0 : nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => (Nat.mul x1 x0) = (Nat.mul x1 y1)) y0.
Definition term222 (x0 : nat) (x1 : nat) := or (~ (~ (Peano.le x0 x1))).
Definition term186 (x0 : nat) := ~ (Peano.lt (NUMERAL 0) x0).
Definition term189 (x0 : nat) (x1 : nat) := (~ (exists y0 : nat, (Nat.mul x1 x0) = (Nat.mul x1 y0))) \/ (~ (Peano.lt (NUMERAL 0) x1)).
Definition term160 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x2 = (NUMERAL 0))) -> (x0 = (Nat.mul x1 x2)) -> (~ ((exists y0 : nat, (Nat.mul x2 x1) = (Nat.mul x2 y0)) /\ (Peano.lt (NUMERAL 0) x2))) -> (forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) -> ~ (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)).
Definition term258 := fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0)).
Definition term300 (x0 : nat) := forall y0 : nat, ((Nat.modulo x0 y0) = (NUMERAL 0)) = (exists y1 : nat, x0 = (Nat.mul y1 y0)).
Definition term194 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term255 := forall y0 : nat, (forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0))) /\ (forall y1 : nat, (Peano.le y0 y1) \/ (Peano.lt y1 y0)).
Definition term239 (x0 : nat) (x1 : nat) := and ((fun y0 : nat => (~ (Peano.le x0 y0)) \/ (~ (Peano.lt y0 x0))) x1).
Definition term183 (x0 : nat) (x1 : nat) := fun y0 : nat => ~ ((fun y1 : nat => (Nat.mul x1 x0) = (Nat.mul x1 y1)) y0).
Definition term93 (x0 : nat) (x1 : nat) := fun y0 : nat => ~ ((fun y1 : nat => (Nat.mul (Nat.div x0 x1) x1) = (Nat.mul y1 x1)) y0).
Definition term76 (x0 : nat) (x1 : nat) := (((~ (exists y0 : nat, (Nat.mul (Nat.div x0 x1) x1) = (Nat.mul y0 x1))) -> False) -> (~ (exists y0 : nat, (Nat.mul (Nat.div x0 x1) x1) = (Nat.mul y0 x1))) -> False) -> ((~ (exists y0 : nat, (Nat.mul (Nat.div x0 x1) x1) = (Nat.mul y0 x1))) -> False) -> (~ (exists y0 : nat, (Nat.mul (Nat.div x0 x1) x1) = (Nat.mul y0 x1))) -> False.
Definition term228 (x0 : nat) (x1 : nat) := ((~ (Peano.le x1 x0)) \/ (~ (Peano.lt x0 x1))) /\ ((Peano.le x1 x0) \/ (Peano.lt x0 x1)).
Definition term187 (x0 : nat) (x1 : nat) := or (~ (exists y0 : nat, (Nat.mul x1 x0) = (Nat.mul x1 y0))).
Definition term127 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) /\ x1.
Definition term107 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x0 x1) (NUMERAL 0).
Definition term96 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ~ ((Nat.mul (Nat.div x0 x1) x1) = (Nat.mul y0 x1))) x2.
Definition term24 (x0 : nat) := forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0).
Definition term77 (x0 : nat) (x1 : nat) := ~ (~ (exists y0 : nat, (Nat.mul (Nat.div x0 x1) x1) = (Nat.mul y0 x1))).
Definition term273 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Peano.le y1 y2) \/ (Peano.lt y2 y1)) y0.
Definition term268 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 y2)) \/ (~ (Peano.lt y2 y1))) y0.
Definition term177 (x0 : nat) := Peano.le x0 (NUMERAL 0).
Definition term38 := (forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))).
Definition term110 (x0 : nat) := Peano.lt (NUMERAL 0) x0.
Definition term34 (x0 : nat) := (fun y0 : Prop => y0 \/ (~ y0)) (x0 = (NUMERAL 0)).
Definition term44 (x0 : nat) := @eq Prop (x0 = (NUMERAL 0)).
Definition term179 (x0 : nat) (x1 : nat) := ~ (exists y0 : nat, (Nat.mul x1 x0) = (Nat.mul x1 y0)).
Definition term121 (x0 : nat) (x1 : nat) := ~ (exists y0 : nat, ((Nat.mul x1 x0) = (Nat.mul x1 y0)) /\ (Peano.lt (NUMERAL 0) x1)).
Definition term73 (x0 : nat) (x1 : nat) := ~ (exists y0 : nat, (Nat.mul (Nat.div x0 x1) x1) = (Nat.mul y0 x1)).
Definition term237 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (Peano.le x0 y0)) \/ (~ (Peano.lt y0 x0))) x1.
Definition term231 := fun y0 : nat => forall y1 : nat, ((~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0))) /\ ((Peano.le y0 y1) \/ (Peano.lt y1 y0)).
Definition term166 (x0 : nat) := fun y0 : nat => forall y1 : nat, (~ (x0 = (NUMERAL 0))) -> (y1 = (Nat.mul y0 x0)) -> (~ ((exists y2 : nat, (Nat.mul x0 y0) = (Nat.mul x0 y2)) /\ (Peano.lt (NUMERAL 0) x0))) -> (forall y2 : nat, (Peano.le y2 (NUMERAL 0)) = (y2 = (NUMERAL 0))) -> ~ (forall y2 : nat, forall y3 : nat, (~ (Peano.le y2 y3)) = (Peano.lt y3 y2)).
Definition term165 (x0 : nat) := fun y0 : nat => forall y1 : nat, (~ (x0 = (NUMERAL 0))) -> (y1 = (Nat.mul y0 x0)) -> (~ (exists y2 : nat, ((Nat.mul x0 y0) = (Nat.mul x0 y2)) /\ (Peano.lt (NUMERAL 0) x0))) -> (forall y2 : nat, (Peano.le y2 (NUMERAL 0)) = (y2 = (NUMERAL 0))) -> (forall y2 : nat, forall y3 : nat, (~ (Peano.le y2 y3)) = (Peano.lt y3 y2)) -> False.
Definition term145 (x0 : nat) (x1 : nat) := ~ ((exists y0 : nat, (Nat.mul x1 x0) = (Nat.mul x1 y0)) /\ (Peano.lt (NUMERAL 0) x1)).
Definition term299 (x0 : nat) (x1 : nat) := (((Nat.modulo x0 x1) = (NUMERAL 0)) -> exists y0 : nat, x0 = (Nat.mul y0 x1)) /\ ((exists y0 : nat, x0 = (Nat.mul y0 x1)) -> (Nat.modulo x0 x1) = (NUMERAL 0)).
Definition term193 := forall y0 : nat, ((Peano.le y0 (NUMERAL 0)) \/ (~ (y0 = (NUMERAL 0)))) /\ ((~ (Peano.le y0 (NUMERAL 0))) \/ (y0 = (NUMERAL 0))).
Definition term48 (x0 : nat) := exists y0 : nat, x0 = (NUMERAL 0).
Definition term282 (x0 : Prop) := x0 -> ~ x0.
Definition term170 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (~ (y0 = (NUMERAL 0))) -> (y2 = (Nat.mul y1 y0)) -> (~ ((exists y3 : nat, (Nat.mul y0 y1) = (Nat.mul y0 y3)) /\ (Peano.lt (NUMERAL 0) y0))) -> (forall y3 : nat, (Peano.le y3 (NUMERAL 0)) = (y3 = (NUMERAL 0))) -> ~ (forall y3 : nat, forall y4 : nat, (~ (Peano.le y3 y4)) = (Peano.lt y4 y3)).
Definition term169 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (~ (y0 = (NUMERAL 0))) -> (y2 = (Nat.mul y1 y0)) -> (~ (exists y3 : nat, ((Nat.mul y0 y1) = (Nat.mul y0 y3)) /\ (Peano.lt (NUMERAL 0) y0))) -> (forall y3 : nat, (Peano.le y3 (NUMERAL 0)) = (y3 = (NUMERAL 0))) -> (forall y3 : nat, forall y4 : nat, (~ (Peano.le y3 y4)) = (Peano.lt y4 y3)) -> False.
Definition term192 := fun y0 : nat => ((Peano.le y0 (NUMERAL 0)) \/ (~ (y0 = (NUMERAL 0)))) /\ ((~ (Peano.le y0 (NUMERAL 0))) \/ (y0 = (NUMERAL 0))).
Definition term287 (x0 : nat) (x1 : nat) := (Peano.lt x1 x0) \/ (Peano.le x0 x1).
Definition term132 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.mul x1 x0) = (Nat.mul x1 y0).
