Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term74 (x0 : nat) (x1 : nat) := (((Nat.modulo x0 x1) = x0) /\ (~ ((x1 = (NUMERAL 0)) \/ (Peano.lt x0 x1)))) \/ ((~ ((Nat.modulo x0 x1) = x0)) /\ ((x1 = (NUMERAL 0)) \/ (Peano.lt x0 x1))).
Definition term159 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1).
Definition term202 (x0 : nat) (x1 : nat) := ~ (x0 = x1).
Definition term195 (x0 : nat) (x1 : nat) := @eq Prop ((Peano.lt (Nat.modulo x0 x1) x1) \/ (x1 = (NUMERAL 0))).
Definition term231 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := imp (~ ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (Peano.lt x2 x3))))).
Definition term171 (x0 : nat) (x1 : nat) := (x1 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo x0 x1) x1).
Definition term77 (x0 : nat -> Prop) := ~ (all x0).
Definition term239 := (~ False) -> False.
Definition term187 (x0 : nat) (x1 : nat) := (~ ((Nat.modulo x1 x0) = x1)) -> (Nat.modulo x1 x0) = x1.
Definition term101 (x0 : nat) (x1 : nat) := or ((fun y0 : nat => ((Nat.modulo x0 y0) = x0) /\ ((~ (y0 = (NUMERAL 0))) /\ (~ (Peano.lt x0 y0)))) x1).
Definition term233 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((x0 = x2) /\ ((x1 = x3) /\ (Peano.lt x0 x1))) -> Peano.lt x2 x3.
Definition term222 (x0 : Prop) := ~ (~ x0).
Definition term201 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.lt x0 x1) \/ ((~ (x3 = x1)) \/ (~ (Peano.lt x2 x3))).
Definition term150 (x0 : nat) := forall y0 : nat, (y0 = (NUMERAL 0)) \/ ((x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0)).
Definition term61 := (forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0))))))).
Definition term121 := fun y0 : nat => exists y1 : nat, (~ ((Nat.modulo y0 y1) = y0)) /\ ((y1 = (NUMERAL 0)) \/ (Peano.lt y0 y1)).
Definition term120 := fun y0 : nat => exists y1 : nat, ((Nat.modulo y0 y1) = y0) /\ ((~ (y1 = (NUMERAL 0))) /\ (~ (Peano.lt y0 y1))).
Definition term90 := fun y0 : nat => exists y1 : nat, (((Nat.modulo y0 y1) = y0) /\ ((~ (y1 = (NUMERAL 0))) /\ (~ (Peano.lt y0 y1)))) \/ ((~ ((Nat.modulo y0 y1) = y0)) /\ ((y1 = (NUMERAL 0)) \/ (Peano.lt y0 y1))).
Definition term111 (x0 : nat) := or (exists y0 : nat, ((Nat.modulo x0 y0) = x0) /\ ((~ (y0 = (NUMERAL 0))) /\ (~ (Peano.lt x0 y0)))).
Definition term234 (x0 : nat) (x1 : nat) := (x1 = x1) /\ (Peano.lt (Nat.modulo x0 x1) x1).
Definition term227 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (~ (x2 = x0))) /\ (~ (~ (Peano.lt x1 x2))).
Definition term22 (x0 : nat) := Nat.modulo x0 (NUMERAL 0).
Definition term161 (x0 : nat) := fun y0 : nat => ((y0 = (NUMERAL 0)) \/ (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0)))) /\ ((y0 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo x0 y0) y0)).
Definition term115 (x0 : nat) := (exists y0 : nat, ((Nat.modulo x0 y0) = x0) /\ ((~ (y0 = (NUMERAL 0))) /\ (~ (Peano.lt x0 y0)))) \/ (exists y0 : nat, (~ ((Nat.modulo x0 y0) = x0)) /\ ((y0 = (NUMERAL 0)) \/ (Peano.lt x0 y0))).
Definition term93 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term16 := (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> (Nat.modulo y0 y1) = y0) -> ~ (forall y0 : nat, (Nat.modulo y0 (NUMERAL 0)) = y0).
Definition term8 := (forall y0 : nat, (Nat.modulo y0 (NUMERAL 0)) = y0) -> False.
Definition term190 (x0 : nat) := ~ (x0 = x0).
Definition term0 (x0 : Prop) := (~ x0) -> False.
Definition term162 (x0 : nat) := forall y0 : nat, ((y0 = (NUMERAL 0)) \/ (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0)))) /\ ((y0 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo x0 y0) y0)).
Definition term209 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.lt x0 x3) \/ ((~ (x1 = x0)) \/ ((~ (Peano.lt x1 x2)) \/ (~ (x2 = x3)))).
Definition term204 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.lt x0 x1)) \/ (~ (x1 = x2)).
Definition term100 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Nat.modulo x0 y0) = x0) /\ ((~ (y0 = (NUMERAL 0))) /\ (~ (Peano.lt x0 y0)))) x1.
Definition term17 := imp ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))).
Definition term199 (x0 : nat) (x1 : nat) := ~ (Peano.lt (Nat.modulo x0 x1) x1).
Definition term242 (x0 : nat) (x1 : nat) := ((Nat.modulo x0 x1) = x0) \/ (~ (Peano.lt x0 x1)).
Definition term5 := ((~ (forall y0 : nat, forall y1 : nat, ((Nat.modulo y0 y1) = y0) = ((y1 = (NUMERAL 0)) \/ (Peano.lt y0 y1)))) -> ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> (Nat.modulo y0 y1) = y0) -> (forall y0 : nat, (Nat.modulo y0 (NUMERAL 0)) = y0) -> False) -> (~ (forall y0 : nat, forall y1 : nat, ((Nat.modulo y0 y1) = y0) = ((y1 = (NUMERAL 0)) \/ (Peano.lt y0 y1)))) -> ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> (Nat.modulo y0 y1) = y0) -> (forall y0 : nat, (Nat.modulo y0 (NUMERAL 0)) = y0) -> False.
Definition term208 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x1 = x0)) \/ ((Peano.lt x0 x3) \/ ((~ (Peano.lt x1 x2)) \/ (~ (x2 = x3)))).
Definition term85 (x0 : nat) := exists y0 : nat, (((Nat.modulo x0 y0) = x0) /\ ((~ (y0 = (NUMERAL 0))) /\ (~ (Peano.lt x0 y0)))) \/ ((~ ((Nat.modulo x0 y0) = x0)) /\ ((y0 = (NUMERAL 0)) \/ (Peano.lt x0 y0))).
Definition term197 (x0 : nat) (x1 : nat) := (~ (x1 = (NUMERAL 0))) -> Peano.lt (Nat.modulo x0 x1) x1.
Definition term196 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term225 (x0 : nat) (x1 : nat) := and (x0 = x1).
Definition term194 (x0 : nat) (x1 : nat) := @eq Prop ((x1 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo x0 x1) x1)).
Definition term79 (x0 : nat) := ~ (forall y0 : nat, ((Nat.modulo x0 y0) = x0) = ((y0 = (NUMERAL 0)) \/ (Peano.lt x0 y0))).
Definition term3 := ~ (forall y0 : nat, forall y1 : nat, ((Nat.modulo y0 y1) = y0) = ((y1 = (NUMERAL 0)) \/ (Peano.lt y0 y1))).
Definition term167 (x0 : nat) := (fun y0 : nat => (Nat.modulo y0 (NUMERAL 0)) = y0) x0.
Definition term143 (x0 : nat) (x1 : nat) := (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1).
Definition term70 (x0 : nat) (x1 : nat) := ((Nat.modulo x0 x1) = x0) /\ (~ ((x1 = (NUMERAL 0)) \/ (Peano.lt x0 x1))).
Definition term229 (x0 : nat) (x1 : nat) (x2 : nat) := (x2 = x0) /\ (Peano.lt x1 x2).
Definition term59 := forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0.
Definition term54 := forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0.
Definition term178 (x0 : nat) (x1 : nat) := @eq Prop (~ ((Nat.modulo x1 x0) = x1)).
Definition term188 (x0 : Prop) := (~ x0) -> x0.
Definition term166 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((y0 = (NUMERAL 0)) \/ (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0)))) /\ ((y0 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo x0 y0) y0))) x1.
Definition term149 (x0 : nat) := fun y0 : nat => (y0 = (NUMERAL 0)) \/ ((x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0)).
Definition term4 := (~ (forall y0 : nat, forall y1 : nat, ((Nat.modulo y0 y1) = y0) = ((y1 = (NUMERAL 0)) \/ (Peano.lt y0 y1)))) -> ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> (Nat.modulo y0 y1) = y0) -> (forall y0 : nat, (Nat.modulo y0 (NUMERAL 0)) = y0) -> False.
Definition term125 (x0 : nat) := ((fun y0 : nat => exists y1 : nat, ((Nat.modulo y0 y1) = y0) /\ ((~ (y1 = (NUMERAL 0))) /\ (~ (Peano.lt y0 y1)))) x0) \/ ((fun y0 : nat => exists y1 : nat, (~ ((Nat.modulo y0 y1) = y0)) /\ ((y1 = (NUMERAL 0)) \/ (Peano.lt y0 y1))) x0).
Definition term38 := fun y0 : nat => (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0.
Definition term219 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term189 (x0 : nat) := (~ (x0 = x0)) -> x0 = x0.
Definition term212 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.lt x1 x3) \/ ((~ (Peano.lt x0 x2)) \/ ((~ (x0 = x1)) \/ (~ (x2 = x3)))).
Definition term67 (x0 : nat) (x1 : nat) := (~ (x1 = (NUMERAL 0))) /\ (~ (Peano.lt x0 x1)).
Definition term124 (x0 : nat) := (fun y0 : nat => exists y1 : nat, (~ ((Nat.modulo y0 y1) = y0)) /\ ((y1 = (NUMERAL 0)) \/ (Peano.lt y0 y1))) x0.
Definition term122 (x0 : nat) := (fun y0 : nat => exists y1 : nat, ((Nat.modulo y0 y1) = y0) /\ ((~ (y1 = (NUMERAL 0))) /\ (~ (Peano.lt y0 y1)))) x0.
Definition term15 := (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> (Nat.modulo y0 y1) = y0) -> (forall y0 : nat, (Nat.modulo y0 (NUMERAL 0)) = y0) -> False.
Definition term18 := ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> (Nat.modulo y0 y1) = y0) -> (forall y0 : nat, (Nat.modulo y0 (NUMERAL 0)) = y0) -> False.
Definition term12 := (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> (Nat.modulo y0 y1) = y0) -> (forall y0 : nat, (Nat.modulo y0 (NUMERAL 0)) = y0) -> False.
Definition term58 := fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0.
Definition term134 := fun y0 : nat => (fun y1 : nat => exists y2 : nat, (~ ((Nat.modulo y1 y2) = y1)) /\ ((y2 = (NUMERAL 0)) \/ (Peano.lt y1 y2))) y0.
Definition term129 := fun y0 : nat => (fun y1 : nat => exists y2 : nat, ((Nat.modulo y1 y2) = y1) /\ ((~ (y2 = (NUMERAL 0))) /\ (~ (Peano.lt y1 y2)))) y0.
Definition term200 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term214 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop ((Peano.lt x1 x3) \/ ((~ (Peano.lt x0 x2)) \/ ((~ (x0 = x1)) \/ (~ (x2 = x3))))).
Definition term203 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x2 = x0)) \/ (~ (Peano.lt x1 x2)).
Definition term66 (x0 : nat) (x1 : nat) := ~ ((x1 = (NUMERAL 0)) \/ (Peano.lt x0 x1)).
Definition term148 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term98 (x0 : nat) := fun y0 : nat => ((Nat.modulo x0 y0) = x0) /\ ((~ (y0 = (NUMERAL 0))) /\ (~ (Peano.lt x0 y0))).
Definition term156 := fun y0 : nat => forall y1 : nat, (~ (Peano.lt y0 y1)) \/ ((Nat.modulo y0 y1) = y0).
Definition term27 := fun y0 : nat => forall y1 : nat, (Peano.lt y0 y1) -> (Nat.modulo y0 y1) = y0.
Definition term146 (x0 : nat) (x1 : nat) := (~ (~ (x1 = (NUMERAL 0)))) \/ ((x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1)).
Definition term228 (x0 : nat) (x1 : nat) := ~ (~ (Peano.lt x0 x1)).
Definition term232 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := imp ((x2 = x0) /\ ((x3 = x1) /\ (Peano.lt x2 x3))).
Definition term69 (x0 : nat) (x1 : nat) := and ((Nat.modulo x1 x0) = x1).
Definition term62 (x0 : nat) (x1 : nat) := (x1 = (NUMERAL 0)) \/ (Peano.lt x0 x1).
Definition term19 := ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> (Nat.modulo y0 y1) = y0) -> ~ (forall y0 : nat, (Nat.modulo y0 (NUMERAL 0)) = y0).
Definition term181 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.lt x0 x1) \/ (~ (Peano.lt x2 x3)).
Definition term128 := @eq Prop (exists y0 : nat, (exists y1 : nat, ((Nat.modulo y0 y1) = y0) /\ ((~ (y1 = (NUMERAL 0))) /\ (~ (Peano.lt y0 y1)))) \/ (exists y1 : nat, (~ ((Nat.modulo y0 y1) = y0)) /\ ((y1 = (NUMERAL 0)) \/ (Peano.lt y0 y1)))).
Definition term127 := @eq Prop (exists y0 : nat, ((fun y1 : nat => exists y2 : nat, ((Nat.modulo y1 y2) = y1) /\ ((~ (y2 = (NUMERAL 0))) /\ (~ (Peano.lt y1 y2)))) y0) \/ ((fun y1 : nat => exists y2 : nat, (~ ((Nat.modulo y1 y2) = y1)) /\ ((y2 = (NUMERAL 0)) \/ (Peano.lt y1 y2))) y0)).
Definition term106 (x0 : nat) := @eq Prop (exists y0 : nat, (((Nat.modulo x0 y0) = x0) /\ ((~ (y0 = (NUMERAL 0))) /\ (~ (Peano.lt x0 y0)))) \/ ((~ ((Nat.modulo x0 y0) = x0)) /\ ((y0 = (NUMERAL 0)) \/ (Peano.lt x0 y0)))).
Definition term105 (x0 : nat) := @eq Prop (exists y0 : nat, ((fun y1 : nat => ((Nat.modulo x0 y1) = x0) /\ ((~ (y1 = (NUMERAL 0))) /\ (~ (Peano.lt x0 y1)))) y0) \/ ((fun y1 : nat => (~ ((Nat.modulo x0 y1) = x0)) /\ ((y1 = (NUMERAL 0)) \/ (Peano.lt x0 y1))) y0)).
Definition term10 := forall y0 : nat, (Nat.modulo y0 (NUMERAL 0)) = y0.
Definition term84 (x0 : nat) := fun y0 : nat => (((Nat.modulo x0 y0) = x0) /\ ((~ (y0 = (NUMERAL 0))) /\ (~ (Peano.lt x0 y0)))) \/ ((~ ((Nat.modulo x0 y0) = x0)) /\ ((y0 = (NUMERAL 0)) \/ (Peano.lt x0 y0))).
Definition term114 (x0 : nat) := exists y0 : nat, (~ ((Nat.modulo x0 y0) = x0)) /\ ((y0 = (NUMERAL 0)) \/ (Peano.lt x0 y0)).
Definition term205 (x0 : nat) (x1 : nat) := or (Peano.lt x0 x1).
Definition term119 := (exists y0 : nat, (fun y1 : nat => exists y2 : nat, ((Nat.modulo y1 y2) = y1) /\ ((~ (y2 = (NUMERAL 0))) /\ (~ (Peano.lt y1 y2)))) y0) \/ (exists y0 : nat, (fun y1 : nat => exists y2 : nat, (~ ((Nat.modulo y1 y2) = y1)) /\ ((y2 = (NUMERAL 0)) \/ (Peano.lt y1 y2))) y0).
Definition term97 (x0 : nat) := (exists y0 : nat, (fun y1 : nat => ((Nat.modulo x0 y1) = x0) /\ ((~ (y1 = (NUMERAL 0))) /\ (~ (Peano.lt x0 y1)))) y0) \/ (exists y0 : nat, (fun y1 : nat => (~ ((Nat.modulo x0 y1) = x0)) /\ ((y1 = (NUMERAL 0)) \/ (Peano.lt x0 y1))) y0).
Definition term76 (x0 : nat) (x1 : nat) := ~ (((Nat.modulo x0 x1) = x0) = ((x1 = (NUMERAL 0)) \/ (Peano.lt x0 x1))).
Definition term73 (x0 : nat) (x1 : nat) := or (((Nat.modulo x0 x1) = x0) /\ ((~ (x1 = (NUMERAL 0))) /\ (~ (Peano.lt x0 x1)))).
Definition term63 (x0 : nat) := fun y0 : nat => ((Nat.modulo x0 y0) = x0) = ((y0 = (NUMERAL 0)) \/ (Peano.lt x0 y0)).
Definition term7 := (((~ (forall y0 : nat, forall y1 : nat, ((Nat.modulo y0 y1) = y0) = ((y1 = (NUMERAL 0)) \/ (Peano.lt y0 y1)))) -> ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> (Nat.modulo y0 y1) = y0) -> (forall y0 : nat, (Nat.modulo y0 (NUMERAL 0)) = y0) -> False) -> (~ (forall y0 : nat, forall y1 : nat, ((Nat.modulo y0 y1) = y0) = ((y1 = (NUMERAL 0)) \/ (Peano.lt y0 y1)))) -> ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> (Nat.modulo y0 y1) = y0) -> (forall y0 : nat, (Nat.modulo y0 (NUMERAL 0)) = y0) -> False) -> ((~ (forall y0 : nat, forall y1 : nat, ((Nat.modulo y0 y1) = y0) = ((y1 = (NUMERAL 0)) \/ (Peano.lt y0 y1)))) -> ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> (Nat.modulo y0 y1) = y0) -> (forall y0 : nat, (Nat.modulo y0 (NUMERAL 0)) = y0) -> False) -> (~ (forall y0 : nat, forall y1 : nat, ((Nat.modulo y0 y1) = y0) = ((y1 = (NUMERAL 0)) \/ (Peano.lt y0 y1)))) -> ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> (Nat.modulo y0 y1) = y0) -> (forall y0 : nat, (Nat.modulo y0 (NUMERAL 0)) = y0) -> False.
Definition term60 := and (forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0).
Definition term55 := and (forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0).
Definition term50 := and (forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))).
Definition term45 := and (forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0).
Definition term40 := and (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0).
Definition term184 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x3 = x1)) \/ ((Peano.lt x0 x1) \/ (~ (Peano.lt x2 x3))).
Definition term46 := (forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))).
Definition term180 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Peano.lt x2 x3) = (Peano.lt x0 x1)) -> (Peano.lt x0 x1) \/ (~ (Peano.lt x2 x3)).
Definition term53 := fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0.
Definition term169 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (Peano.lt x0 y0)) \/ ((Nat.modulo x0 y0) = x0)) x1.
Definition term144 (x0 : nat) := or (~ (~ (x0 = (NUMERAL 0)))).
Definition term217 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ ((~ (x0 = x2)) \/ ((~ (x1 = x3)) \/ (~ (Peano.lt x0 x1))))) -> Peano.lt x2 x3.
Definition term30 (x0 : nat) := fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0).
Definition term235 (x0 : nat) (x1 : nat) := ((Nat.modulo x0 x1) = x0) /\ ((x1 = x1) /\ (Peano.lt (Nat.modulo x0 x1) x1)).
Definition term145 (x0 : nat) := or (x0 = (NUMERAL 0)).
Definition term218 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term164 := forall y0 : nat, forall y1 : nat, ((y1 = (NUMERAL 0)) \/ (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)))) /\ ((y1 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term157 := forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) \/ ((Nat.modulo y0 y1) = y0).
Definition term152 := forall y0 : nat, forall y1 : nat, (y1 = (NUMERAL 0)) \/ ((y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term33 := forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1).
Definition term28 := forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> (Nat.modulo y0 y1) = y0.
Definition term1 := forall y0 : nat, forall y1 : nat, ((Nat.modulo y0 y1) = y0) = ((y1 = (NUMERAL 0)) \/ (Peano.lt y0 y1)).
Definition term68 (x0 : nat) (x1 : nat) := (~ ((Nat.modulo x0 x1) = x0)) /\ ((x1 = (NUMERAL 0)) \/ (Peano.lt x0 x1)).
Definition term238 (x0 : nat) (x1 : nat) := (Peano.lt x0 x1) -> False.
Definition term117 := exists y0 : nat, (exists y1 : nat, ((Nat.modulo y0 y1) = y0) /\ ((~ (y1 = (NUMERAL 0))) /\ (~ (Peano.lt y0 y1)))) \/ (exists y1 : nat, (~ ((Nat.modulo y0 y1) = y0)) /\ ((y1 = (NUMERAL 0)) \/ (Peano.lt y0 y1))).
Definition term118 := exists y0 : nat, ((fun y1 : nat => exists y2 : nat, ((Nat.modulo y1 y2) = y1) /\ ((~ (y2 = (NUMERAL 0))) /\ (~ (Peano.lt y1 y2)))) y0) \/ ((fun y1 : nat => exists y2 : nat, (~ ((Nat.modulo y1 y2) = y1)) /\ ((y2 = (NUMERAL 0)) \/ (Peano.lt y1 y2))) y0).
Definition term96 (x0 : nat) := exists y0 : nat, ((fun y1 : nat => ((Nat.modulo x0 y1) = x0) /\ ((~ (y1 = (NUMERAL 0))) /\ (~ (Peano.lt x0 y1)))) y0) \/ ((fun y1 : nat => (~ ((Nat.modulo x0 y1) = x0)) /\ ((y1 = (NUMERAL 0)) \/ (Peano.lt x0 y1))) y0).
Definition term193 (x0 : nat) (x1 : nat) := (Peano.lt (Nat.modulo x0 x1) x1) \/ (x1 = (NUMERAL 0)).
Definition term29 (x0 : nat) (x1 : nat) := (~ (x1 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1).
Definition term21 := (~ (forall y0 : nat, forall y1 : nat, ((Nat.modulo y0 y1) = y0) = ((y1 = (NUMERAL 0)) \/ (Peano.lt y0 y1)))) -> ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> (Nat.modulo y0 y1) = y0) -> ~ (forall y0 : nat, (Nat.modulo y0 (NUMERAL 0)) = y0).
Definition term185 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x2 = x0) -> (~ (x3 = x1)) \/ ((Peano.lt x0 x1) \/ (~ (Peano.lt x2 x3))).
Definition term48 := fun y0 : nat => (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0)).
Definition term220 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ~ ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (Peano.lt x2 x3)))).
Definition term25 (x0 : nat) := fun y0 : nat => (Peano.lt x0 y0) -> (Nat.modulo x0 y0) = x0.
Definition term206 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.lt x0 x3) \/ ((~ (Peano.lt x1 x2)) \/ (~ (x2 = x3))).
Definition term133 := or (exists y0 : nat, exists y1 : nat, ((Nat.modulo y0 y1) = y0) /\ ((~ (y1 = (NUMERAL 0))) /\ (~ (Peano.lt y0 y1)))).
Definition term72 (x0 : nat) (x1 : nat) := or (((Nat.modulo x0 x1) = x0) /\ (~ ((x1 = (NUMERAL 0)) \/ (Peano.lt x0 x1)))).
Definition term2 := (~ (forall y0 : nat, forall y1 : nat, ((Nat.modulo y0 y1) = y0) = ((y1 = (NUMERAL 0)) \/ (Peano.lt y0 y1)))) -> False.
Definition term89 := fun y0 : nat => ~ ((fun y1 : nat => forall y2 : nat, ((Nat.modulo y1 y2) = y1) = ((y2 = (NUMERAL 0)) \/ (Peano.lt y1 y2))) y0).
Definition term57 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) x0.
Definition term236 (x0 : nat) (x1 : nat) := (((Nat.modulo x0 x1) = x0) /\ ((x1 = x1) /\ (Peano.lt (Nat.modulo x0 x1) x1))) -> Peano.lt x0 x1.
Definition term182 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x3 = x1) -> (Peano.lt x0 x1) \/ (~ (Peano.lt x2 x3)).
Definition term43 := fun y0 : nat => (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0.
Definition term176 (x0 : nat) := ~ ((Nat.modulo x0 (NUMERAL 0)) = x0).
Definition term191 (x0 : nat) := (x0 = (NUMERAL 0)) -> ~ (x0 = (NUMERAL 0)).
Definition term113 (x0 : nat) := exists y0 : nat, (fun y1 : nat => (~ ((Nat.modulo x0 y1) = x0)) /\ ((y1 = (NUMERAL 0)) \/ (Peano.lt x0 y1))) y0.
Definition term108 (x0 : nat) := exists y0 : nat, (fun y1 : nat => ((Nat.modulo x0 y1) = x0) /\ ((~ (y1 = (NUMERAL 0))) /\ (~ (Peano.lt x0 y1)))) y0.
Definition term247 (x0 : nat) (x1 : nat) := imp (Peano.lt x0 x1).
Definition term24 (x0 : nat) (x1 : nat) := (Peano.lt x1 x0) -> (Nat.modulo x1 x0) = x1.
Definition term224 (x0 : nat) (x1 : nat) := and (~ (~ (x0 = x1))).
Definition term216 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.lt x0 x1) \/ ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (Peano.lt x2 x3)))).
Definition term241 (x0 : nat) := ((Nat.modulo x0 (NUMERAL 0)) = x0) -> False.
Definition term116 := fun y0 : nat => (exists y1 : nat, ((Nat.modulo y0 y1) = y0) /\ ((~ (y1 = (NUMERAL 0))) /\ (~ (Peano.lt y0 y1)))) \/ (exists y1 : nat, (~ ((Nat.modulo y0 y1) = y0)) /\ ((y1 = (NUMERAL 0)) \/ (Peano.lt y0 y1))).
Definition term179 (x0 : Prop) (x1 : Prop) := (x1 = x0) -> x0 \/ (~ x1).
Definition term41 := (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0))).
Definition term49 := forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0)).
Definition term36 := forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)).
Definition term177 (x0 : nat) (x1 : nat) := @eq Prop ((fun y0 : nat => ~ ((Nat.modulo x0 y0) = x0)) x1).
Definition term126 := fun y0 : nat => ((fun y1 : nat => exists y2 : nat, ((Nat.modulo y1 y2) = y1) /\ ((~ (y2 = (NUMERAL 0))) /\ (~ (Peano.lt y1 y2)))) y0) \/ ((fun y1 : nat => exists y2 : nat, (~ ((Nat.modulo y1 y2) = y1)) /\ ((y2 = (NUMERAL 0)) \/ (Peano.lt y1 y2))) y0).
Definition term88 (x0 : nat) := ~ ((fun y0 : nat => forall y1 : nat, ((Nat.modulo y0 y1) = y0) = ((y1 = (NUMERAL 0)) \/ (Peano.lt y0 y1))) x0).
Definition term240 (x0 : nat) := (~ ((Nat.modulo x0 (NUMERAL 0)) = x0)) -> (Nat.modulo x0 (NUMERAL 0)) = x0.
Definition term170 (x0 : nat) (x1 : nat) := ~ (Peano.lt x0 x1).
Definition term123 (x0 : nat) := or ((fun y0 : nat => exists y1 : nat, ((Nat.modulo y0 y1) = y0) /\ ((~ (y1 = (NUMERAL 0))) /\ (~ (Peano.lt y0 y1)))) x0).
Definition term75 (x0 : nat) (x1 : nat) := (((Nat.modulo x0 x1) = x0) /\ ((~ (x1 = (NUMERAL 0))) /\ (~ (Peano.lt x0 x1)))) \/ ((~ ((Nat.modulo x0 x1) = x0)) /\ ((x1 = (NUMERAL 0)) \/ (Peano.lt x0 x1))).
Definition term173 (x0 : nat) := fun y0 : nat => ~ ((Nat.modulo x0 y0) = x0).
Definition term168 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (Peano.lt y0 y1)) \/ ((Nat.modulo y0 y1) = y0)) x0.
Definition term165 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((y1 = (NUMERAL 0)) \/ (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)))) /\ ((y1 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo y0 y1) y1))) x0.
Definition term87 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.modulo y0 y1) = y0) = ((y1 = (NUMERAL 0)) \/ (Peano.lt y0 y1))) x0.
Definition term230 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x2 = x0) /\ ((x3 = x1) /\ (Peano.lt x2 x3)).
Definition term243 (x0 : nat) (x1 : nat) := @eq Prop ((~ (Peano.lt x1 x0)) \/ ((Nat.modulo x1 x0) = x1)).
Definition term154 (x0 : nat) := fun y0 : nat => (~ (Peano.lt x0 y0)) \/ ((Nat.modulo x0 y0) = x0).
Definition term51 := (forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0))))).
Definition term44 := forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0.
Definition term39 := forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0.
Definition term155 (x0 : nat) := forall y0 : nat, (~ (Peano.lt x0 y0)) \/ ((Nat.modulo x0 y0) = x0).
Definition term71 (x0 : nat) (x1 : nat) := ((Nat.modulo x0 x1) = x0) /\ ((~ (x1 = (NUMERAL 0))) /\ (~ (Peano.lt x0 x1))).
Definition term215 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (Peano.lt x2 x3))).
Definition term210 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x1 = x0)) \/ ((~ (Peano.lt x1 x2)) \/ (~ (x2 = x3))).
Definition term64 (x0 : nat) := forall y0 : nat, ((Nat.modulo x0 y0) = x0) = ((y0 = (NUMERAL 0)) \/ (Peano.lt x0 y0)).
Definition term158 (x0 : nat) (x1 : nat) := ((x1 = (NUMERAL 0)) \/ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) /\ ((x1 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo x0 x1) x1)).
Definition term226 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((~ (x2 = x0)) \/ (~ (Peano.lt x1 x2))).
Definition term81 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Nat.modulo x0 y0) = x0) = ((y0 = (NUMERAL 0)) \/ (Peano.lt x0 y0))) x1.
Definition term213 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ ((Peano.lt x0 x1) \/ (~ (Peano.lt x2 x3))))).
Definition term86 := exists y0 : nat, ~ ((fun y1 : nat => forall y2 : nat, ((Nat.modulo y1 y2) = y1) = ((y2 = (NUMERAL 0)) \/ (Peano.lt y1 y2))) y0).
Definition term80 (x0 : nat) := exists y0 : nat, ~ ((fun y1 : nat => ((Nat.modulo x0 y1) = x0) = ((y1 = (NUMERAL 0)) \/ (Peano.lt x0 y1))) y0).
Definition term237 (x0 : nat) (x1 : nat) := (~ (Peano.lt x0 x1)) -> Peano.lt x0 x1.
Definition term137 := (exists y0 : nat, exists y1 : nat, ((Nat.modulo y0 y1) = y0) /\ ((~ (y1 = (NUMERAL 0))) /\ (~ (Peano.lt y0 y1)))) \/ (exists y0 : nat, exists y1 : nat, (~ ((Nat.modulo y0 y1) = y0)) /\ ((y1 = (NUMERAL 0)) \/ (Peano.lt y0 y1))).
Definition term244 (x0 : nat) (x1 : nat) := @eq Prop (((Nat.modulo x0 x1) = x0) \/ (~ (Peano.lt x0 x1))).
Definition term174 (x0 : nat) (x1 : nat) := (fun y0 : nat => ~ ((Nat.modulo x0 y0) = x0)) x1.
Definition term13 := (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> (Nat.modulo y0 y1) = y0) -> ~ (forall y0 : nat, (Nat.modulo y0 (NUMERAL 0)) = y0).
Definition term112 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (~ ((Nat.modulo x0 y1) = x0)) /\ ((y1 = (NUMERAL 0)) \/ (Peano.lt x0 y1))) y0.
Definition term107 (x0 : nat) := fun y0 : nat => (fun y1 : nat => ((Nat.modulo x0 y1) = x0) /\ ((~ (y1 = (NUMERAL 0))) /\ (~ (Peano.lt x0 y1)))) y0.
Definition term245 (x0 : nat) (x1 : nat) := (~ (~ (Peano.lt x1 x0))) -> (Nat.modulo x1 x0) = x1.
Definition term183 (x0 : Prop) (x1 : Prop) := (~ x0) \/ x1.
Definition term221 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (~ (x2 = x0))) /\ (~ ((~ (x3 = x1)) \/ (~ (Peano.lt x2 x3)))).
Definition term160 (x0 : nat) (x1 : nat) := Peano.lt (Nat.modulo x0 x1) x1.
Definition term37 (x0 : nat) := (Peano.le (NUMERAL (BIT1 0)) x0) -> Peano.lt (NUMERAL 0) x0.
Definition term6 := (((~ (forall y0 : nat, forall y1 : nat, ((Nat.modulo y0 y1) = y0) = ((y1 = (NUMERAL 0)) \/ (Peano.lt y0 y1)))) -> ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> (Nat.modulo y0 y1) = y0) -> (forall y0 : nat, (Nat.modulo y0 (NUMERAL 0)) = y0) -> False) -> (~ (forall y0 : nat, forall y1 : nat, ((Nat.modulo y0 y1) = y0) = ((y1 = (NUMERAL 0)) \/ (Peano.lt y0 y1)))) -> ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> (Nat.modulo y0 y1) = y0) -> (forall y0 : nat, (Nat.modulo y0 (NUMERAL 0)) = y0) -> False) -> (~ (forall y0 : nat, forall y1 : nat, ((Nat.modulo y0 y1) = y0) = ((y1 = (NUMERAL 0)) \/ (Peano.lt y0 y1)))) -> ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> (Nat.modulo y0 y1) = y0) -> (forall y0 : nat, (Nat.modulo y0 (NUMERAL 0)) = y0) -> False.
Definition term23 := fun y0 : nat => (Nat.modulo y0 (NUMERAL 0)) = y0.
Definition term211 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (Peano.lt x0 x2)) \/ ((~ (x0 = x1)) \/ (~ (x2 = x3))).
Definition term135 := exists y0 : nat, (fun y1 : nat => exists y2 : nat, (~ ((Nat.modulo y1 y2) = y1)) /\ ((y2 = (NUMERAL 0)) \/ (Peano.lt y1 y2))) y0.
Definition term130 := exists y0 : nat, (fun y1 : nat => exists y2 : nat, ((Nat.modulo y1 y2) = y1) /\ ((~ (y2 = (NUMERAL 0))) /\ (~ (Peano.lt y1 y2)))) y0.
Definition term42 (x0 : nat) := (Peano.lt (NUMERAL 0) x0) -> Peano.le (NUMERAL (BIT1 0)) x0.
Definition term136 := exists y0 : nat, exists y1 : nat, (~ ((Nat.modulo y0 y1) = y0)) /\ ((y1 = (NUMERAL 0)) \/ (Peano.lt y0 y1)).
Definition term131 := exists y0 : nat, exists y1 : nat, ((Nat.modulo y0 y1) = y0) /\ ((~ (y1 = (NUMERAL 0))) /\ (~ (Peano.lt y0 y1))).
Definition term91 := exists y0 : nat, exists y1 : nat, (((Nat.modulo y0 y1) = y0) /\ ((~ (y1 = (NUMERAL 0))) /\ (~ (Peano.lt y0 y1)))) \/ ((~ ((Nat.modulo y0 y1) = y0)) /\ ((y1 = (NUMERAL 0)) \/ (Peano.lt y0 y1))).
Definition term102 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ ((Nat.modulo x0 y0) = x0)) /\ ((y0 = (NUMERAL 0)) \/ (Peano.lt x0 y0))) x1.
Definition term94 (x0 : nat -> Prop) (x1 : nat -> Prop) := exists y0 : nat, (x0 y0) \/ (x1 y0).
Definition term83 (x0 : nat) := fun y0 : nat => ~ ((fun y1 : nat => ((Nat.modulo x0 y1) = x0) = ((y1 = (NUMERAL 0)) \/ (Peano.lt x0 y1))) y0).
Definition term82 (x0 : nat) (x1 : nat) := ~ ((fun y0 : nat => ((Nat.modulo x0 y0) = x0) = ((y0 = (NUMERAL 0)) \/ (Peano.lt x0 y0))) x1).
Definition term34 (x0 : nat) := (Peano.le (NUMERAL (BIT1 0)) x0) -> ~ (x0 = (NUMERAL 0)).
Definition term52 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) x0.
Definition term248 (x0 : nat) (x1 : nat) := ((Nat.modulo x1 x0) = x1) -> False.
Definition term109 (x0 : nat) := exists y0 : nat, ((Nat.modulo x0 y0) = x0) /\ ((~ (y0 = (NUMERAL 0))) /\ (~ (Peano.lt x0 y0))).
Definition term147 (x0 : nat) (x1 : nat) := (x1 = (NUMERAL 0)) \/ ((x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1)).
Definition term99 (x0 : nat) := fun y0 : nat => (~ ((Nat.modulo x0 y0) = x0)) /\ ((y0 = (NUMERAL 0)) \/ (Peano.lt x0 y0)).
Definition term104 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => ((Nat.modulo x0 y1) = x0) /\ ((~ (y1 = (NUMERAL 0))) /\ (~ (Peano.lt x0 y1)))) y0) \/ ((fun y1 : nat => (~ ((Nat.modulo x0 y1) = x0)) /\ ((y1 = (NUMERAL 0)) \/ (Peano.lt x0 y1))) y0).
Definition term132 := or (exists y0 : nat, (fun y1 : nat => exists y2 : nat, ((Nat.modulo y1 y2) = y1) /\ ((~ (y2 = (NUMERAL 0))) /\ (~ (Peano.lt y1 y2)))) y0).
Definition term110 (x0 : nat) := or (exists y0 : nat, (fun y1 : nat => ((Nat.modulo x0 y1) = x0) /\ ((~ (y1 = (NUMERAL 0))) /\ (~ (Peano.lt x0 y1)))) y0).
Definition term9 := ~ (forall y0 : nat, (Nat.modulo y0 (NUMERAL 0)) = y0).
Definition term142 (x0 : nat) := ~ (~ (x0 = (NUMERAL 0))).
Definition term223 (x0 : nat) (x1 : nat) := ~ (~ (x0 = x1)).
Definition term103 (x0 : nat) (x1 : nat) := ((fun y0 : nat => ((Nat.modulo x0 y0) = x0) /\ ((~ (y0 = (NUMERAL 0))) /\ (~ (Peano.lt x0 y0)))) x1) \/ ((fun y0 : nat => (~ ((Nat.modulo x0 y0) = x0)) /\ ((y0 = (NUMERAL 0)) \/ (Peano.lt x0 y0))) x1).
Definition term31 (x0 : nat) := forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0).
Definition term207 (x0 : nat) (x1 : nat) := or (~ (x0 = x1)).
Definition term172 (x0 : nat) (x1 : nat) := ~ ((Nat.modulo x1 x0) = x1).
Definition term14 := imp (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term11 := imp (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> (Nat.modulo y0 y1) = y0).
Definition term56 := (forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))).
Definition term35 := fun y0 : nat => (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)).
Definition term153 (x0 : nat) (x1 : nat) := (~ (Peano.lt x1 x0)) \/ ((Nat.modulo x1 x0) = x1).
Definition term92 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term186 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ ((Peano.lt x0 x1) \/ (~ (Peano.lt x2 x3)))).
Definition term78 (x0 : nat -> Prop) := exists y0 : nat, ~ (x0 y0).
Definition term175 (x0 : nat) := (fun y0 : nat => ~ ((Nat.modulo x0 y0) = x0)) (NUMERAL 0).
Definition term163 := fun y0 : nat => forall y1 : nat, ((y1 = (NUMERAL 0)) \/ (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)))) /\ ((y1 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term151 := fun y0 : nat => forall y1 : nat, (y1 = (NUMERAL 0)) \/ ((y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term65 := fun y0 : nat => forall y1 : nat, ((Nat.modulo y0 y1) = y0) = ((y1 = (NUMERAL 0)) \/ (Peano.lt y0 y1)).
Definition term32 := fun y0 : nat => forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1).
Definition term47 (x0 : nat) := (Peano.lt (NUMERAL 0) x0) -> ~ (x0 = (NUMERAL 0)).
Definition term95 (x0 : nat -> Prop) (x1 : nat -> Prop) := (exists y0 : nat, x0 y0) \/ (exists y0 : nat, x1 y0).
Definition term20 := imp (~ (forall y0 : nat, forall y1 : nat, ((Nat.modulo y0 y1) = y0) = ((y1 = (NUMERAL 0)) \/ (Peano.lt y0 y1)))).
Definition term192 (x0 : Prop) := x0 -> ~ x0.
Definition term198 (x0 : nat) (x1 : nat) := (~ (Peano.lt (Nat.modulo x0 x1) x1)) -> Peano.lt (Nat.modulo x0 x1) x1.
Definition term26 (x0 : nat) := forall y0 : nat, (Peano.lt x0 y0) -> (Nat.modulo x0 y0) = x0.
Definition term246 (x0 : nat) (x1 : nat) := imp (~ (~ (Peano.lt x0 x1))).
Definition term141 (x0 : nat) := @eq Prop ((exists y0 : nat, ((Nat.modulo x0 y0) = x0) /\ ((~ (y0 = (NUMERAL 0))) /\ (~ (Peano.lt x0 y0)))) \/ (exists y0 : nat, (~ ((Nat.modulo x0 y0) = x0)) /\ ((y0 = (NUMERAL 0)) \/ (Peano.lt x0 y0)))).
Definition term140 (x0 : nat) := @eq Prop ((exists y0 : nat, (fun y1 : nat => ((Nat.modulo x0 y1) = x0) /\ ((~ (y1 = (NUMERAL 0))) /\ (~ (Peano.lt x0 y1)))) y0) \/ (exists y0 : nat, (fun y1 : nat => (~ ((Nat.modulo x0 y1) = x0)) /\ ((y1 = (NUMERAL 0)) \/ (Peano.lt x0 y1))) y0)).
Definition term139 := @eq Prop ((exists y0 : nat, exists y1 : nat, ((Nat.modulo y0 y1) = y0) /\ ((~ (y1 = (NUMERAL 0))) /\ (~ (Peano.lt y0 y1)))) \/ (exists y0 : nat, exists y1 : nat, (~ ((Nat.modulo y0 y1) = y0)) /\ ((y1 = (NUMERAL 0)) \/ (Peano.lt y0 y1)))).
Definition term138 := @eq Prop ((exists y0 : nat, (fun y1 : nat => exists y2 : nat, ((Nat.modulo y1 y2) = y1) /\ ((~ (y2 = (NUMERAL 0))) /\ (~ (Peano.lt y1 y2)))) y0) \/ (exists y0 : nat, (fun y1 : nat => exists y2 : nat, (~ ((Nat.modulo y1 y2) = y1)) /\ ((y2 = (NUMERAL 0)) \/ (Peano.lt y1 y2))) y0)).
