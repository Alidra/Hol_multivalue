Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term280 (x0 : nat) := fun y0 : nat => (forall y1 : nat, Peano.lt (Nat.add x0 y1) (Nat.add y0 y1)) \/ (~ (Peano.lt x0 y0)).
Definition term392 (x0 : nat) (x1 : nat) := exists y0 : nat, (x0 = (Nat.add (Nat.mul y0 x1) (Nat.sub x0 x1))) /\ (Peano.lt (Nat.sub x0 x1) x1).
Definition term125 (x0 : nat) (x1 : nat) := ~ (x0 = x1).
Definition term369 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := imp (~ ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (Peano.lt x2 x3))))).
Definition term61 (x0 : nat) (x1 : nat) := (~ (x0 = (Nat.add x1 (Nat.sub x0 x1)))) -> False.
Definition term342 (x0 : nat) (x1 : nat) := ~ (x0 = (Nat.add (Nat.sub x0 x1) x1)).
Definition term172 (x0 : nat) (x1 : nat) := (~ (Peano.lt (Nat.sub x0 x1) x1)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.lt y0 y2) /\ (Peano.lt y1 y3)) -> Peano.lt (Nat.add y0 y1) (Nat.add y2 y3)) -> (forall y0 : nat, (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (Nat.add y0 y0)) -> (forall y0 : nat, forall y1 : nat, (Peano.le y1 y0) -> (Nat.add (Nat.sub y0 y1) y1) = y0) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.lt (Nat.add y0 y2) (Nat.add y1 y2)) = (Peano.lt y0 y1)) -> False.
Definition term308 := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, (forall y3 : nat, Peano.lt (Nat.add y1 y3) (Nat.add y2 y3)) \/ (~ (Peano.lt y1 y2))) y0) /\ ((fun y1 : nat => forall y2 : nat, (forall y3 : nat, ~ (Peano.lt (Nat.add y1 y3) (Nat.add y2 y3))) \/ (Peano.lt y1 y2)) y0).
Definition term149 := (~ False) -> False.
Definition term119 (x0 : nat) (x1 : nat) := (~ ((Nat.add (Nat.sub x1 x0) x0) = x1)) -> (Nat.add (Nat.sub x1 x0) x0) = x1.
Definition term195 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nat => ((Peano.lt x0 x2) /\ (Peano.lt x1 y0)) -> Peano.lt (Nat.add x0 x1) (Nat.add x2 y0).
Definition term261 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ~ (Peano.lt (Nat.add x0 y0) (Nat.add x1 y0))) x2.
Definition term187 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.lt (Nat.add x0 y0) (Nat.add x1 y0)) = (Peano.lt x0 x1).
Definition term220 (x0 : nat) (x1 : nat) (x2 : nat) := and ((fun y0 : nat => (Peano.lt (Nat.add x0 y0) (Nat.add x1 y0)) \/ (~ (Peano.lt x0 x1))) x2).
Definition term132 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((~ (x0 = x1)) \/ (~ (x0 = x2)))) -> x1 = x2.
Definition term93 (x0 : nat) := fun y0 : nat => (Nat.add x0 y0) = (Nat.add y0 x0).
Definition term345 (x0 : nat) (x1 : nat) := (~ (Peano.lt x0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1))) -> Peano.lt x0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1).
Definition term300 := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (forall y3 : nat, Peano.lt (Nat.add y1 y3) (Nat.add y2 y3)) \/ (~ (Peano.lt y1 y2))) y0) /\ ((fun y1 : nat => forall y2 : nat, (forall y3 : nat, ~ (Peano.lt (Nat.add y1 y3) (Nat.add y2 y3))) \/ (Peano.lt y1 y2)) y0).
Definition term278 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => (forall y2 : nat, Peano.lt (Nat.add x0 y2) (Nat.add y1 y2)) \/ (~ (Peano.lt x0 y1))) y0) /\ ((fun y1 : nat => (forall y2 : nat, ~ (Peano.lt (Nat.add x0 y2) (Nat.add y1 y2))) \/ (Peano.lt x0 y1)) y0).
Definition term214 (x0 : nat) (x1 : nat) := forall y0 : nat, ((fun y1 : nat => (Peano.lt (Nat.add x0 y1) (Nat.add x1 y1)) \/ (~ (Peano.lt x0 x1))) y0) /\ ((fun y1 : nat => (~ (Peano.lt (Nat.add x0 y1) (Nat.add x1 y1))) \/ (Peano.lt x0 x1)) y0).
Definition term270 (x0 : nat) (x1 : nat) := forall y0 : nat, (fun y1 : nat => ~ (Peano.lt (Nat.add x0 y1) (Nat.add x1 y1))) y0.
Definition term1 := (forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))))).
Definition term371 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((x0 = x2) /\ ((x1 = x3) /\ (Peano.lt x0 x1))) -> Peano.lt x2 x3.
Definition term116 (x0 : Prop) := ~ (~ x0).
Definition term327 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (~ (Peano.lt (Nat.add y0 y2) (Nat.add y1 y2))) \/ (Peano.lt y0 y1)) x0.
Definition term27 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (exists y3 : nat, (y0 = (Nat.add (Nat.mul y3 y1) y2)) /\ (Peano.lt y2 y1)) -> (Nat.modulo y0 y1) = y2) x0.
Definition term10 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y0 = (Nat.add (Nat.mul y2 y1) y3)) /\ (Peano.lt y3 y1)) -> (Nat.modulo y0 y1) = y3) x0.
Definition term376 (x0 : nat) (x1 : nat) := (~ (Peano.lt (Nat.add (Nat.sub x0 x1) x1) (Nat.add x1 x1))) -> Peano.lt (Nat.add (Nat.sub x0 x1) x1) (Nat.add x1 x1).
Definition term343 (x0 : nat) := (~ ((Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) = (Nat.add x0 x0))) -> (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) = (Nat.add x0 x0).
Definition term347 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.lt x0 x1) \/ ((~ (x3 = x1)) \/ (~ (Peano.lt x2 x3))).
Definition term286 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => (forall y2 : nat, Peano.lt (Nat.add x0 y2) (Nat.add y1 y2)) \/ (~ (Peano.lt x0 y1))) y0) /\ ((fun y1 : nat => (forall y2 : nat, ~ (Peano.lt (Nat.add x0 y2) (Nat.add y1 y2))) \/ (Peano.lt x0 y1)) y0).
Definition term225 (x0 : nat) (x1 : nat) := fun y0 : nat => ((fun y1 : nat => (Peano.lt (Nat.add x0 y1) (Nat.add x1 y1)) \/ (~ (Peano.lt x0 x1))) y0) /\ ((fun y1 : nat => (~ (Peano.lt (Nat.add x0 y1) (Nat.add x1 y1))) \/ (Peano.lt x0 x1)) y0).
Definition term21 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nat => (x0 = (Nat.add (Nat.mul y0 x2) x1)) /\ (Peano.lt x1 x2).
Definition term339 (x0 : nat) (x1 : nat) := ((Nat.add (Nat.sub x0 x1) x1) = x0) /\ ((Nat.add (Nat.sub x0 x1) x1) = (Nat.add (Nat.sub x0 x1) x1)).
Definition term272 (x0 : nat) (x1 : nat) := or (forall y0 : nat, (fun y1 : nat => ~ (Peano.lt (Nat.add x0 y1) (Nat.add x1 y1))) y0).
Definition term254 (x0 : nat) (x1 : nat) := or (forall y0 : nat, (fun y1 : nat => Peano.lt (Nat.add x0 y1) (Nat.add x1 y1)) y0).
Definition term274 (x0 : nat) (x1 : nat) := (forall y0 : nat, ~ (Peano.lt (Nat.add x0 y0) (Nat.add x1 y0))) \/ (Peano.lt x0 x1).
Definition term259 (x0 : nat) (x1 : nat) := (forall y0 : nat, (fun y1 : nat => ~ (Peano.lt (Nat.add x0 y1) (Nat.add x1 y1))) y0) \/ (Peano.lt x0 x1).
Definition term365 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (~ (x2 = x0))) /\ (~ (~ (Peano.lt x1 x2))).
Definition term137 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (~ (x1 = x0))) /\ (~ (~ (x1 = x2))).
Definition term97 (x0 : nat) (x1 : nat) := (~ (Peano.le x0 x1)) \/ ((Nat.add (Nat.sub x1 x0) x0) = x1).
Definition term26 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y0 = (Nat.add (Nat.mul y2 y1) y3)) /\ (Peano.lt y3 y1)) -> (Nat.modulo y0 y1) = y3) -> forall y0 : nat, forall y1 : nat, forall y2 : nat, (exists y3 : nat, (y0 = (Nat.add (Nat.mul y3 y1) y2)) /\ (Peano.lt y2 y1)) -> (Nat.modulo y0 y1) = y2.
Definition term54 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt x0 y0) -> (Nat.modulo x0 y0) = x0) x1.
Definition term41 (x0 : nat) (x1 : nat) := (~ (Peano.lt x0 x1)) -> (Nat.modulo x0 x1) = (Nat.sub x0 x1).
Definition term22 (x0 : nat) (x1 : nat) (x2 : nat) := (exists y0 : nat, (x0 = (Nat.add (Nat.mul y0 x1) x2)) /\ (Peano.lt x2 x1)) -> (Nat.modulo x0 x1) = x2.
Definition term265 (x0 : nat) (x1 : nat) (x2 : nat) := ((fun y0 : nat => ~ (Peano.lt (Nat.add x1 y0) (Nat.add x2 y0))) x0) \/ (Peano.lt x1 x2).
Definition term121 (x0 : nat) (x1 : nat) := (~ ((Nat.add (Nat.sub x0 x1) x1) = (Nat.add x1 (Nat.sub x0 x1)))) -> (Nat.add (Nat.sub x0 x1) x1) = (Nat.add x1 (Nat.sub x0 x1)).
Definition term60 (x0 : Prop) := (~ x0) -> False.
Definition term301 := (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (forall y3 : nat, Peano.lt (Nat.add y1 y3) (Nat.add y2 y3)) \/ (~ (Peano.lt y1 y2))) y0) /\ (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (forall y3 : nat, ~ (Peano.lt (Nat.add y1 y3) (Nat.add y2 y3))) \/ (Peano.lt y1 y2)) y0).
Definition term279 (x0 : nat) := (forall y0 : nat, (fun y1 : nat => (forall y2 : nat, Peano.lt (Nat.add x0 y2) (Nat.add y1 y2)) \/ (~ (Peano.lt x0 y1))) y0) /\ (forall y0 : nat, (fun y1 : nat => (forall y2 : nat, ~ (Peano.lt (Nat.add x0 y2) (Nat.add y1 y2))) \/ (Peano.lt x0 y1)) y0).
Definition term215 (x0 : nat) (x1 : nat) := (forall y0 : nat, (fun y1 : nat => (Peano.lt (Nat.add x0 y1) (Nat.add x1 y1)) \/ (~ (Peano.lt x0 x1))) y0) /\ (forall y0 : nat, (fun y1 : nat => (~ (Peano.lt (Nat.add x0 y1) (Nat.add x1 y1))) \/ (Peano.lt x0 x1)) y0).
Definition term319 := (forall y0 : nat, forall y1 : nat, (forall y2 : nat, Peano.lt (Nat.add y0 y2) (Nat.add y1 y2)) \/ (~ (Peano.lt y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (forall y2 : nat, ~ (Peano.lt (Nat.add y0 y2) (Nat.add y1 y2))) \/ (Peano.lt y0 y1)).
Definition term277 (x0 : nat) := forall y0 : nat, ((forall y1 : nat, Peano.lt (Nat.add x0 y1) (Nat.add y0 y1)) \/ (~ (Peano.lt x0 y0))) /\ ((forall y1 : nat, ~ (Peano.lt (Nat.add x0 y1) (Nat.add y0 y1))) \/ (Peano.lt x0 y0)).
Definition term205 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Peano.lt (Nat.add x0 y0) (Nat.add x1 y0)) \/ (~ (Peano.lt x0 x1))) /\ ((~ (Peano.lt (Nat.add x0 y0) (Nat.add x1 y0))) \/ (Peano.lt x0 x1)).
Definition term142 (x0 : nat) (x1 : nat) (x2 : nat) := imp (~ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term353 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.lt x0 x3) \/ ((~ (x1 = x0)) \/ ((~ (Peano.lt x1 x2)) \/ (~ (x2 = x3)))).
Definition term349 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.lt x0 x1)) \/ (~ (x1 = x2)).
Definition term219 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.lt (Nat.add x1 x0) (Nat.add x2 x0)) \/ (~ (Peano.lt x1 x2)).
Definition term15 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, ((x1 = (Nat.add (Nat.mul x0 x2) y0)) /\ (Peano.lt y0 x2)) -> (Nat.modulo x1 x2) = y0.
Definition term154 (x0 : nat) (x1 : nat) := ~ (Peano.lt (Nat.sub x0 x1) x1).
Definition term281 (x0 : nat) := fun y0 : nat => (forall y1 : nat, ~ (Peano.lt (Nat.add x0 y1) (Nat.add y0 y1))) \/ (Peano.lt x0 y0).
Definition term385 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.lt (Nat.add x1 x0) (Nat.add x2 x0)) -> Peano.lt x1 x2.
Definition term295 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (forall y2 : nat, ~ (Peano.lt (Nat.add x0 y2) (Nat.add y1 y2))) \/ (Peano.lt x0 y1)) y0.
Definition term290 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (forall y2 : nat, Peano.lt (Nat.add x0 y2) (Nat.add y1 y2)) \/ (~ (Peano.lt x0 y1))) y0.
Definition term252 (x0 : nat) (x1 : nat) := forall y0 : nat, (fun y1 : nat => Peano.lt (Nat.add x0 y1) (Nat.add x1 y1)) y0.
Definition term234 (x0 : nat) (x1 : nat) := forall y0 : nat, (fun y1 : nat => (~ (Peano.lt (Nat.add x0 y1) (Nat.add x1 y1))) \/ (Peano.lt x0 x1)) y0.
Definition term229 (x0 : nat) (x1 : nat) := forall y0 : nat, (fun y1 : nat => (Peano.lt (Nat.add x0 y1) (Nat.add x1 y1)) \/ (~ (Peano.lt x0 x1))) y0.
Definition term157 (x0 : nat) (x1 : nat) := (((Peano.lt x0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) -> (Peano.le x1 x0) -> (~ (Peano.lt (Nat.sub x0 x1) x1)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.lt y0 y2) /\ (Peano.lt y1 y3)) -> Peano.lt (Nat.add y0 y1) (Nat.add y2 y3)) -> (forall y0 : nat, (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (Nat.add y0 y0)) -> (forall y0 : nat, forall y1 : nat, (Peano.le y1 y0) -> (Nat.add (Nat.sub y0 y1) y1) = y0) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.lt (Nat.add y0 y2) (Nat.add y1 y2)) = (Peano.lt y0 y1)) -> False) -> (Peano.lt x0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) -> (Peano.le x1 x0) -> (~ (Peano.lt (Nat.sub x0 x1) x1)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.lt y0 y2) /\ (Peano.lt y1 y3)) -> Peano.lt (Nat.add y0 y1) (Nat.add y2 y3)) -> (forall y0 : nat, (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (Nat.add y0 y0)) -> (forall y0 : nat, forall y1 : nat, (Peano.le y1 y0) -> (Nat.add (Nat.sub y0 y1) y1) = y0) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.lt (Nat.add y0 y2) (Nat.add y1 y2)) = (Peano.lt y0 y1)) -> False) -> (Peano.lt x0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) -> (Peano.le x1 x0) -> (~ (Peano.lt (Nat.sub x0 x1) x1)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.lt y0 y2) /\ (Peano.lt y1 y3)) -> Peano.lt (Nat.add y0 y1) (Nat.add y2 y3)) -> (forall y0 : nat, (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (Nat.add y0 y0)) -> (forall y0 : nat, forall y1 : nat, (Peano.le y1 y0) -> (Nat.add (Nat.sub y0 y1) y1) = y0) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.lt (Nat.add y0 y2) (Nat.add y1 y2)) = (Peano.lt y0 y1)) -> False.
Definition term156 (x0 : nat) (x1 : nat) := ((Peano.lt x0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) -> (Peano.le x1 x0) -> (~ (Peano.lt (Nat.sub x0 x1) x1)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.lt y0 y2) /\ (Peano.lt y1 y3)) -> Peano.lt (Nat.add y0 y1) (Nat.add y2 y3)) -> (forall y0 : nat, (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (Nat.add y0 y0)) -> (forall y0 : nat, forall y1 : nat, (Peano.le y1 y0) -> (Nat.add (Nat.sub y0 y1) y1) = y0) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.lt (Nat.add y0 y2) (Nat.add y1 y2)) = (Peano.lt y0 y1)) -> False) -> (Peano.lt x0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) -> (Peano.le x1 x0) -> (~ (Peano.lt (Nat.sub x0 x1) x1)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.lt y0 y2) /\ (Peano.lt y1 y3)) -> Peano.lt (Nat.add y0 y1) (Nat.add y2 y3)) -> (forall y0 : nat, (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (Nat.add y0 y0)) -> (forall y0 : nat, forall y1 : nat, (Peano.le y1 y0) -> (Nat.add (Nat.sub y0 y1) y1) = y0) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.lt (Nat.add y0 y2) (Nat.add y1 y2)) = (Peano.lt y0 y1)) -> False.
Definition term65 (x0 : nat) (x1 : nat) := (((Peano.lt x0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) -> (Peano.le x1 x0) -> (~ (x0 = (Nat.add x1 (Nat.sub x0 x1)))) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> (forall y0 : nat, forall y1 : nat, (Peano.le y1 y0) -> (Nat.add (Nat.sub y0 y1) y1) = y0) -> False) -> (Peano.lt x0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) -> (Peano.le x1 x0) -> (~ (x0 = (Nat.add x1 (Nat.sub x0 x1)))) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> (forall y0 : nat, forall y1 : nat, (Peano.le y1 y0) -> (Nat.add (Nat.sub y0 y1) y1) = y0) -> False) -> (Peano.lt x0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) -> (Peano.le x1 x0) -> (~ (x0 = (Nat.add x1 (Nat.sub x0 x1)))) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> (forall y0 : nat, forall y1 : nat, (Peano.le y1 y0) -> (Nat.add (Nat.sub y0 y1) y1) = y0) -> False.
Definition term64 (x0 : nat) (x1 : nat) := ((Peano.lt x0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) -> (Peano.le x1 x0) -> (~ (x0 = (Nat.add x1 (Nat.sub x0 x1)))) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> (forall y0 : nat, forall y1 : nat, (Peano.le y1 y0) -> (Nat.add (Nat.sub y0 y1) y1) = y0) -> False) -> (Peano.lt x0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) -> (Peano.le x1 x0) -> (~ (x0 = (Nat.add x1 (Nat.sub x0 x1)))) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> (forall y0 : nat, forall y1 : nat, (Peano.le y1 y0) -> (Nat.add (Nat.sub y0 y1) y1) = y0) -> False.
Definition term352 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x1 = x0)) \/ ((Peano.lt x0 x3) \/ ((~ (Peano.lt x1 x2)) \/ (~ (x2 = x3)))).
Definition term29 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (exists y1 : nat, (x0 = (Nat.add (Nat.mul y1 x1) y0)) /\ (Peano.lt y0 x1)) -> (Nat.modulo x0 x1) = y0) x2.
Definition term390 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt y0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) -> (Peano.le x0 y0) -> (~ (Peano.lt (Nat.sub y0 x0) x0)) -> (forall y1 : nat, forall y2 : nat, forall y3 : nat, forall y4 : nat, ((Peano.lt y1 y3) /\ (Peano.lt y2 y4)) -> Peano.lt (Nat.add y1 y2) (Nat.add y3 y4)) -> (forall y1 : nat, (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1) = (Nat.add y1 y1)) -> (forall y1 : nat, forall y2 : nat, (Peano.le y2 y1) -> (Nat.add (Nat.sub y1 y2) y2) = y1) -> (forall y1 : nat, forall y2 : nat, forall y3 : nat, (Peano.lt (Nat.add y1 y3) (Nat.add y2 y3)) = (Peano.lt y1 y2)) -> False) x1.
Definition term151 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt y0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) -> (Peano.le x0 y0) -> (~ (y0 = (Nat.add x0 (Nat.sub y0 x0)))) -> (forall y1 : nat, forall y2 : nat, (Nat.add y1 y2) = (Nat.add y2 y1)) -> (forall y1 : nat, forall y2 : nat, (Peano.le y2 y1) -> (Nat.add (Nat.sub y1 y2) y2) = y1) -> False) x1.
Definition term266 (x0 : nat) (x1 : nat) := fun y0 : nat => ((fun y1 : nat => ~ (Peano.lt (Nat.add x0 y1) (Nat.add x1 y1))) y0) \/ (Peano.lt x0 x1).
Definition term114 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term212 (x0 : nat -> Prop) (x1 : nat -> Prop) := forall y0 : nat, (x0 y0) /\ (x1 y0).
Definition term140 (x0 : nat) (x1 : nat) := and (x0 = x1).
Definition term372 (x0 : nat) (x1 : nat) := ((Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1) = (Nat.add x1 x1)) /\ (Peano.lt x0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)).
Definition term298 := fun y0 : nat => (forall y1 : nat, (forall y2 : nat, Peano.lt (Nat.add y0 y2) (Nat.add y1 y2)) \/ (~ (Peano.lt y0 y1))) /\ (forall y1 : nat, (forall y2 : nat, ~ (Peano.lt (Nat.add y0 y2) (Nat.add y1 y2))) \/ (Peano.lt y0 y1)).
Definition term160 := ~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.lt (Nat.add y0 y2) (Nat.add y1 y2)) = (Peano.lt y0 y1)).
Definition term68 := ~ (forall y0 : nat, forall y1 : nat, (Peano.le y1 y0) -> (Nat.add (Nat.sub y0 y1) y1) = y0).
Definition term243 (x0 : nat) (x1 : nat) := fun y0 : nat => Peano.lt (Nat.add x0 y0) (Nat.add x1 y0).
Definition term381 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (~ (Peano.lt (Nat.add x1 x0) (Nat.add x2 x0)))) -> Peano.lt x1 x2.
Definition term171 (x0 : nat) (x1 : nat) := imp (~ (Peano.lt (Nat.sub x0 x1) x1)).
Definition term391 (x0 : nat) (x1 : nat) := (x0 = (Nat.add (Nat.mul (NUMERAL (BIT1 0)) x1) (Nat.sub x0 x1))) /\ (Peano.lt (Nat.sub x0 x1) x1).
Definition term31 (x0 : nat -> Prop) (x1 : Prop) (x2 : nat) (x3 : nat) := x0 (@COND nat x1 x2 x3).
Definition term20 (x0 : nat) (x1 : nat) (x2 : nat) := exists y0 : nat, (x0 = (Nat.add (Nat.mul y0 x2) x1)) /\ (Peano.lt x1 x2).
Definition term367 (x0 : nat) (x1 : nat) (x2 : nat) := (x2 = x0) /\ (Peano.lt x1 x2).
Definition term222 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (~ (Peano.lt (Nat.add x0 y0) (Nat.add x1 y0))) \/ (Peano.lt x0 x1)) x2.
Definition term76 (x0 : nat) (x1 : nat) := imp (Peano.le x0 x1).
Definition term110 (x0 : Prop) := (~ x0) -> x0.
Definition term141 (x0 : nat) (x1 : nat) (x2 : nat) := (x1 = x0) /\ (x1 = x2).
Definition term382 (x0 : nat) (x1 : nat) (x2 : nat) := ~ (~ (Peano.lt (Nat.add x0 x2) (Nat.add x1 x2))).
Definition term122 (x0 : nat) (x1 : nat) := ~ ((Nat.add (Nat.sub x0 x1) x1) = (Nat.add x1 (Nat.sub x0 x1))).
Definition term148 (x0 : nat) (x1 : nat) := (x0 = (Nat.add x1 (Nat.sub x0 x1))) -> False.
Definition term39 (x0 : nat) (x1 : nat) := imp (~ (Peano.lt x0 x1)).
Definition term341 (x0 : nat) (x1 : nat) := (~ (x0 = (Nat.add (Nat.sub x0 x1) x1))) -> x0 = (Nat.add (Nat.sub x0 x1) x1).
Definition term133 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x1 = x0)) \/ (~ (x1 = x2)).
Definition term170 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.lt y0 y2) /\ (Peano.lt y1 y3)) -> Peano.lt (Nat.add y0 y1) (Nat.add y2 y3)) -> (forall y0 : nat, (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (Nat.add y0 y0)) -> (forall y0 : nat, forall y1 : nat, (Peano.le y1 y0) -> (Nat.add (Nat.sub y0 y1) y1) = y0) -> ~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.lt (Nat.add y0 y2) (Nat.add y1 y2)) = (Peano.lt y0 y1)).
Definition term224 (x0 : nat) (x1 : nat) (x2 : nat) := ((fun y0 : nat => (Peano.lt (Nat.add x0 y0) (Nat.add x1 y0)) \/ (~ (Peano.lt x0 x1))) x2) /\ ((fun y0 : nat => (~ (Peano.lt (Nat.add x0 y0) (Nat.add x1 y0))) \/ (Peano.lt x0 x1)) x2).
Definition term135 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term257 (x0 : nat) (x1 : nat) := and ((forall y0 : nat, Peano.lt (Nat.add x0 y0) (Nat.add x1 y0)) \/ (~ (Peano.lt x0 x1))).
Definition term276 (x0 : nat) := fun y0 : nat => ((forall y1 : nat, Peano.lt (Nat.add x0 y1) (Nat.add y0 y1)) \/ (~ (Peano.lt x0 y0))) /\ ((forall y1 : nat, ~ (Peano.lt (Nat.add x0 y1) (Nat.add y0 y1))) \/ (Peano.lt x0 y0)).
Definition term59 (x0 : nat) (x1 : nat) := Nat.add x1 (Nat.sub x0 x1).
Definition term356 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.lt x1 x3) \/ ((~ (Peano.lt x0 x2)) \/ ((~ (x0 = x1)) \/ (~ (x2 = x3)))).
Definition term246 (x0 : nat) (x1 : nat) (x2 : nat) := or (Peano.lt (Nat.add x0 x2) (Nat.add x1 x2)).
Definition term130 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2))).
Definition term18 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x0 = (Nat.add (Nat.mul x1 x3) x2)) /\ (Peano.lt x2 x3).
Definition term108 (x0 : nat) (x1 : nat) := (~ (Peano.le x0 x1)) -> Peano.le x0 x1.
Definition term310 := @eq Prop (forall y0 : nat, (forall y1 : nat, (forall y2 : nat, Peano.lt (Nat.add y0 y2) (Nat.add y1 y2)) \/ (~ (Peano.lt y0 y1))) /\ (forall y1 : nat, (forall y2 : nat, ~ (Peano.lt (Nat.add y0 y2) (Nat.add y1 y2))) \/ (Peano.lt y0 y1))).
Definition term309 := @eq Prop (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (forall y3 : nat, Peano.lt (Nat.add y1 y3) (Nat.add y2 y3)) \/ (~ (Peano.lt y1 y2))) y0) /\ ((fun y1 : nat => forall y2 : nat, (forall y3 : nat, ~ (Peano.lt (Nat.add y1 y3) (Nat.add y2 y3))) \/ (Peano.lt y1 y2)) y0)).
Definition term288 (x0 : nat) := @eq Prop (forall y0 : nat, ((forall y1 : nat, Peano.lt (Nat.add x0 y1) (Nat.add y0 y1)) \/ (~ (Peano.lt x0 y0))) /\ ((forall y1 : nat, ~ (Peano.lt (Nat.add x0 y1) (Nat.add y0 y1))) \/ (Peano.lt x0 y0))).
Definition term287 (x0 : nat) := @eq Prop (forall y0 : nat, ((fun y1 : nat => (forall y2 : nat, Peano.lt (Nat.add x0 y2) (Nat.add y1 y2)) \/ (~ (Peano.lt x0 y1))) y0) /\ ((fun y1 : nat => (forall y2 : nat, ~ (Peano.lt (Nat.add x0 y2) (Nat.add y1 y2))) \/ (Peano.lt x0 y1)) y0)).
Definition term268 (x0 : nat) (x1 : nat) := @eq Prop (forall y0 : nat, (~ (Peano.lt (Nat.add x0 y0) (Nat.add x1 y0))) \/ (Peano.lt x0 x1)).
Definition term267 (x0 : nat) (x1 : nat) := @eq Prop (forall y0 : nat, ((fun y1 : nat => ~ (Peano.lt (Nat.add x0 y1) (Nat.add x1 y1))) y0) \/ (Peano.lt x0 x1)).
Definition term250 (x0 : nat) (x1 : nat) := @eq Prop (forall y0 : nat, (Peano.lt (Nat.add x0 y0) (Nat.add x1 y0)) \/ (~ (Peano.lt x0 x1))).
Definition term249 (x0 : nat) (x1 : nat) := @eq Prop (forall y0 : nat, ((fun y1 : nat => Peano.lt (Nat.add x0 y1) (Nat.add x1 y1)) y0) \/ (~ (Peano.lt x0 x1))).
Definition term227 (x0 : nat) (x1 : nat) := @eq Prop (forall y0 : nat, ((Peano.lt (Nat.add x0 y0) (Nat.add x1 y0)) \/ (~ (Peano.lt x0 x1))) /\ ((~ (Peano.lt (Nat.add x0 y0) (Nat.add x1 y0))) \/ (Peano.lt x0 x1))).
Definition term226 (x0 : nat) (x1 : nat) := @eq Prop (forall y0 : nat, ((fun y1 : nat => (Peano.lt (Nat.add x0 y1) (Nat.add x1 y1)) \/ (~ (Peano.lt x0 x1))) y0) /\ ((fun y1 : nat => (~ (Peano.lt (Nat.add x0 y1) (Nat.add x1 y1))) \/ (Peano.lt x0 x1)) y0)).
Definition term48 (x0 : nat) (x1 : nat) := ((Peano.lt x0 x1) -> (Nat.modulo x0 x1) = x0) /\ ((~ (Peano.lt x0 x1)) -> (Nat.modulo x0 x1) = (Nat.sub x0 x1)).
Definition term131 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term55 (x0 : nat) (x1 : nat) := @eq nat (Nat.modulo x0 x1).
Definition term211 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term57 (x0 : nat) := Nat.add (Nat.mul (NUMERAL (BIT1 0)) x0).
Definition term163 := (forall y0 : nat, forall y1 : nat, (Peano.le y1 y0) -> (Nat.add (Nat.sub y0 y1) y1) = y0) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.lt (Nat.add y0 y2) (Nat.add y1 y2)) = (Peano.lt y0 y1)) -> False.
Definition term71 := (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> (forall y0 : nat, forall y1 : nat, (Peano.le y1 y0) -> (Nat.add (Nat.sub y0 y1) y1) = y0) -> False.
Definition term239 (x0 : nat -> Prop) (x1 : Prop) := forall y0 : nat, (x0 y0) \/ x1.
Definition term238 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (forall y0 : a0, x0 y0) \/ x1.
Definition term186 (x0 : nat) (x1 : nat) := fun y0 : nat => (Peano.lt (Nat.add x0 y0) (Nat.add x1 y0)) = (Peano.lt x0 x1).
Definition term128 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term328 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (~ (Peano.lt (Nat.add x0 y1) (Nat.add y0 y1))) \/ (Peano.lt x0 y0)) x1.
Definition term28 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (exists y2 : nat, (x0 = (Nat.add (Nat.mul y2 y0) y1)) /\ (Peano.lt y1 y0)) -> (Nat.modulo x0 y0) = y1) x1.
Definition term358 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop ((Peano.lt x1 x3) \/ ((~ (Peano.lt x0 x2)) \/ ((~ (x0 = x1)) \/ (~ (x2 = x3))))).
Definition term321 (x0 : nat) (x1 : nat) := @eq Prop ((forall y0 : nat, ~ (Peano.lt (Nat.add x0 y0) (Nat.add x1 y0))) \/ (Peano.lt x0 x1)).
Definition term320 (x0 : nat) (x1 : nat) := @eq Prop ((forall y0 : nat, (fun y1 : nat => ~ (Peano.lt (Nat.add x0 y1) (Nat.add x1 y1))) y0) \/ (Peano.lt x0 x1)).
Definition term348 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x2 = x0)) \/ (~ (Peano.lt x1 x2)).
Definition term344 (x0 : nat) := ~ ((Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) = (Nat.add x0 x0)).
Definition term260 (x0 : nat) (x1 : nat) := fun y0 : nat => ~ (Peano.lt (Nat.add x0 y0) (Nat.add x1 y0)).
Definition term322 (x0 : nat) := fun y0 : nat => forall y1 : nat, (~ (Peano.lt (Nat.add x0 y1) (Nat.add y0 y1))) \/ (Peano.lt x0 y0).
Definition term303 := fun y0 : nat => forall y1 : nat, (forall y2 : nat, ~ (Peano.lt (Nat.add y0 y2) (Nat.add y1 y2))) \/ (Peano.lt y0 y1).
Definition term188 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Peano.lt (Nat.add x0 y1) (Nat.add y0 y1)) = (Peano.lt x0 y0).
Definition term101 := fun y0 : nat => forall y1 : nat, (~ (Peano.le y1 y0)) \/ ((Nat.add (Nat.sub y0 y1) y1) = y0).
Definition term95 := fun y0 : nat => forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0).
Definition term92 := fun y0 : nat => forall y1 : nat, (Peano.le y1 y0) -> (Nat.add (Nat.sub y0 y1) y1) = y0.
Definition term366 (x0 : nat) (x1 : nat) := ~ (~ (Peano.lt x0 x1)).
Definition term203 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.lt (Nat.add x1 x0) (Nat.add x2 x0)) \/ (~ (Peano.lt x1 x2))) /\ ((~ (Peano.lt (Nat.add x1 x0) (Nat.add x2 x0))) \/ (Peano.lt x1 x2)).
Definition term35 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.modulo x0 x1) = y0.
Definition term370 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := imp ((x2 = x0) /\ ((x3 = x1) /\ (Peano.lt x2 x3))).
Definition term32 (x0 : nat) (x1 : Prop) (x2 : nat -> Prop) (x3 : nat) := (x1 -> x2 x0) /\ ((~ x1) -> x2 x3).
Definition term337 (x0 : nat) (x1 : nat) := (~ ((Nat.add (Nat.sub x0 x1) x1) = (Nat.add (Nat.sub x0 x1) x1))) -> (Nat.add (Nat.sub x0 x1) x1) = (Nat.add (Nat.sub x0 x1) x1).
Definition term331 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.lt x0 x1) \/ (~ (Peano.lt x2 x3)).
Definition term204 (x0 : nat) (x1 : nat) := fun y0 : nat => ((Peano.lt (Nat.add x0 y0) (Nat.add x1 y0)) \/ (~ (Peano.lt x0 x1))) /\ ((~ (Peano.lt (Nat.add x0 y0) (Nat.add x1 y0))) \/ (Peano.lt x0 x1)).
Definition term192 := fun y0 : nat => (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (Nat.add y0 y0).
Definition term107 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2)).
Definition term62 (x0 : nat) (x1 : nat) := ~ (x0 = (Nat.add x1 (Nat.sub x0 x1))).
Definition term109 (x0 : nat) (x1 : nat) := ~ (Peano.le x0 x1).
Definition term289 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (forall y2 : nat, Peano.lt (Nat.add x0 y2) (Nat.add y1 y2)) \/ (~ (Peano.lt x0 y1))) y0.
Definition term228 (x0 : nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => (Peano.lt (Nat.add x0 y1) (Nat.add x1 y1)) \/ (~ (Peano.lt x0 x1))) y0.
Definition term350 (x0 : nat) (x1 : nat) := or (Peano.lt x0 x1).
Definition term129 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term44 (x0 : nat) (x1 : nat) := (Peano.lt x1 x0) -> (fun y0 : nat => (Nat.modulo x1 x0) = y0) x1.
Definition term153 (x0 : nat) (x1 : nat) := (~ (Peano.lt (Nat.sub x0 x1) x1)) -> False.
Definition term191 (x0 : nat) := Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0.
Definition term159 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.lt (Nat.add y0 y2) (Nat.add y1 y2)) = (Peano.lt y0 y1)) -> False.
Definition term67 := (forall y0 : nat, forall y1 : nat, (Peano.le y1 y0) -> (Nat.add (Nat.sub y0 y1) y1) = y0) -> False.
Definition term158 (x0 : nat) (x1 : nat) := (((Peano.lt x0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) -> (Peano.le x1 x0) -> (~ (Peano.lt (Nat.sub x0 x1) x1)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.lt y0 y2) /\ (Peano.lt y1 y3)) -> Peano.lt (Nat.add y0 y1) (Nat.add y2 y3)) -> (forall y0 : nat, (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (Nat.add y0 y0)) -> (forall y0 : nat, forall y1 : nat, (Peano.le y1 y0) -> (Nat.add (Nat.sub y0 y1) y1) = y0) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.lt (Nat.add y0 y2) (Nat.add y1 y2)) = (Peano.lt y0 y1)) -> False) -> (Peano.lt x0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) -> (Peano.le x1 x0) -> (~ (Peano.lt (Nat.sub x0 x1) x1)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.lt y0 y2) /\ (Peano.lt y1 y3)) -> Peano.lt (Nat.add y0 y1) (Nat.add y2 y3)) -> (forall y0 : nat, (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (Nat.add y0 y0)) -> (forall y0 : nat, forall y1 : nat, (Peano.le y1 y0) -> (Nat.add (Nat.sub y0 y1) y1) = y0) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.lt (Nat.add y0 y2) (Nat.add y1 y2)) = (Peano.lt y0 y1)) -> False) -> ((Peano.lt x0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) -> (Peano.le x1 x0) -> (~ (Peano.lt (Nat.sub x0 x1) x1)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.lt y0 y2) /\ (Peano.lt y1 y3)) -> Peano.lt (Nat.add y0 y1) (Nat.add y2 y3)) -> (forall y0 : nat, (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (Nat.add y0 y0)) -> (forall y0 : nat, forall y1 : nat, (Peano.le y1 y0) -> (Nat.add (Nat.sub y0 y1) y1) = y0) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.lt (Nat.add y0 y2) (Nat.add y1 y2)) = (Peano.lt y0 y1)) -> False) -> (Peano.lt x0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) -> (Peano.le x1 x0) -> (~ (Peano.lt (Nat.sub x0 x1) x1)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.lt y0 y2) /\ (Peano.lt y1 y3)) -> Peano.lt (Nat.add y0 y1) (Nat.add y2 y3)) -> (forall y0 : nat, (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (Nat.add y0 y0)) -> (forall y0 : nat, forall y1 : nat, (Peano.le y1 y0) -> (Nat.add (Nat.sub y0 y1) y1) = y0) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.lt (Nat.add y0 y2) (Nat.add y1 y2)) = (Peano.lt y0 y1)) -> False.
Definition term66 (x0 : nat) (x1 : nat) := (((Peano.lt x0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) -> (Peano.le x1 x0) -> (~ (x0 = (Nat.add x1 (Nat.sub x0 x1)))) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> (forall y0 : nat, forall y1 : nat, (Peano.le y1 y0) -> (Nat.add (Nat.sub y0 y1) y1) = y0) -> False) -> (Peano.lt x0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) -> (Peano.le x1 x0) -> (~ (x0 = (Nat.add x1 (Nat.sub x0 x1)))) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> (forall y0 : nat, forall y1 : nat, (Peano.le y1 y0) -> (Nat.add (Nat.sub y0 y1) y1) = y0) -> False) -> ((Peano.lt x0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) -> (Peano.le x1 x0) -> (~ (x0 = (Nat.add x1 (Nat.sub x0 x1)))) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> (forall y0 : nat, forall y1 : nat, (Peano.le y1 y0) -> (Nat.add (Nat.sub y0 y1) y1) = y0) -> False) -> (Peano.lt x0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) -> (Peano.le x1 x0) -> (~ (x0 = (Nat.add x1 (Nat.sub x0 x1)))) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> (forall y0 : nat, forall y1 : nat, (Peano.le y1 y0) -> (Nat.add (Nat.sub y0 y1) y1) = y0) -> False.
Definition term235 (x0 : nat) (x1 : nat) := forall y0 : nat, (~ (Peano.lt (Nat.add x0 y0) (Nat.add x1 y0))) \/ (Peano.lt x0 x1).
Definition term165 := imp (forall y0 : nat, (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (Nat.add y0 y0)).
Definition term90 (x0 : nat) := fun y0 : nat => (Peano.le y0 x0) -> (Nat.add (Nat.sub x0 y0) y0) = x0.
Definition term293 (x0 : nat) := and (forall y0 : nat, (forall y1 : nat, Peano.lt (Nat.add x0 y1) (Nat.add y0 y1)) \/ (~ (Peano.lt x0 y0))).
Definition term232 (x0 : nat) (x1 : nat) := and (forall y0 : nat, (Peano.lt (Nat.add x0 y0) (Nat.add x1 y0)) \/ (~ (Peano.lt x0 x1))).
Definition term271 (x0 : nat) (x1 : nat) := forall y0 : nat, ~ (Peano.lt (Nat.add x0 y0) (Nat.add x1 y0)).
Definition term193 := forall y0 : nat, (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (Nat.add y0 y0).
Definition term40 (x0 : nat) (x1 : nat) := (~ (Peano.lt x0 x1)) -> (fun y0 : nat => (Nat.modulo x0 x1) = y0) (Nat.sub x0 x1).
Definition term221 (x0 : nat) (x1 : nat) (x2 : nat) := and ((Peano.lt (Nat.add x1 x0) (Nat.add x2 x0)) \/ (~ (Peano.lt x1 x2))).
Definition term383 (x0 : nat) (x1 : nat) (x2 : nat) := imp (~ (~ (Peano.lt (Nat.add x0 x2) (Nat.add x1 x2)))).
Definition term17 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((x1 = (Nat.add (Nat.mul x0 x2) x3)) /\ (Peano.lt x3 x2)) -> (Nat.modulo x1 x2) = x3.
Definition term334 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x3 = x1)) \/ ((Peano.lt x0 x1) \/ (~ (Peano.lt x2 x3))).
Definition term326 (x0 : nat) := (fun y0 : nat => (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (Nat.add y0 y0)) x0.
Definition term330 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Peano.lt x2 x3) = (Peano.lt x0 x1)) -> (Peano.lt x0 x1) \/ (~ (Peano.lt x2 x3)).
Definition term106 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (Peano.le y0 x0)) \/ ((Nat.add (Nat.sub x0 y0) y0) = x0)) x1.
Definition term361 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ ((~ (x0 = x2)) \/ ((~ (x1 = x3)) \/ (~ (Peano.lt x0 x1))))) -> Peano.lt x2 x3.
Definition term16 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => ((x1 = (Nat.add (Nat.mul x0 x2) y0)) /\ (Peano.lt y0 x2)) -> (Nat.modulo x1 x2) = y0) x3.
Definition term147 (x0 : nat) (x1 : nat) := (~ (x0 = (Nat.add x1 (Nat.sub x0 x1)))) -> x0 = (Nat.add x1 (Nat.sub x0 x1)).
Definition term134 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term74 (x0 : nat) (x1 : nat) := (~ (x0 = (Nat.add x1 (Nat.sub x0 x1)))) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> (forall y0 : nat, forall y1 : nat, (Peano.le y1 y0) -> (Nat.add (Nat.sub y0 y1) y1) = y0) -> False.
Definition term397 := forall y0 : nat, forall y1 : nat, (Peano.lt y0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) -> (Nat.modulo y0 y1) = (@COND nat (Peano.lt y0 y1) y0 (Nat.sub y0 y1)).
Definition term325 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (~ (Peano.lt (Nat.add y0 y2) (Nat.add y1 y2))) \/ (Peano.lt y0 y1).
Definition term323 (x0 : nat) := forall y0 : nat, forall y1 : nat, (~ (Peano.lt (Nat.add x0 y1) (Nat.add y0 y1))) \/ (Peano.lt x0 y0).
Definition term318 := forall y0 : nat, forall y1 : nat, (forall y2 : nat, ~ (Peano.lt (Nat.add y0 y2) (Nat.add y1 y2))) \/ (Peano.lt y0 y1).
Definition term313 := forall y0 : nat, forall y1 : nat, (forall y2 : nat, Peano.lt (Nat.add y0 y2) (Nat.add y1 y2)) \/ (~ (Peano.lt y0 y1)).
Definition term209 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt (Nat.add y0 y2) (Nat.add y1 y2)) \/ (~ (Peano.lt y0 y1))) /\ ((~ (Peano.lt (Nat.add y0 y2) (Nat.add y1 y2))) \/ (Peano.lt y0 y1)).
Definition term207 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.lt (Nat.add x0 y1) (Nat.add y0 y1)) \/ (~ (Peano.lt x0 y0))) /\ ((~ (Peano.lt (Nat.add x0 y1) (Nat.add y0 y1))) \/ (Peano.lt x0 y0)).
Definition term202 := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.lt y0 y2) /\ (Peano.lt y1 y3)) -> Peano.lt (Nat.add y0 y1) (Nat.add y2 y3).
Definition term200 (x0 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt x0 y1) /\ (Peano.lt y0 y2)) -> Peano.lt (Nat.add x0 y0) (Nat.add y1 y2).
Definition term198 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.lt x0 y0) /\ (Peano.lt x1 y1)) -> Peano.lt (Nat.add x0 x1) (Nat.add y0 y1).
Definition term189 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.lt (Nat.add x0 y1) (Nat.add y0 y1)) = (Peano.lt x0 y0).
Definition term184 := forall y0 : nat, forall y1 : nat, (Peano.lt y1 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) -> (Peano.le y0 y1) -> (~ (Peano.lt (Nat.sub y1 y0) y0)) -> (forall y2 : nat, forall y3 : nat, forall y4 : nat, forall y5 : nat, ((Peano.lt y2 y4) /\ (Peano.lt y3 y5)) -> Peano.lt (Nat.add y2 y3) (Nat.add y4 y5)) -> (forall y2 : nat, (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y2) = (Nat.add y2 y2)) -> (forall y2 : nat, forall y3 : nat, (Peano.le y3 y2) -> (Nat.add (Nat.sub y2 y3) y3) = y2) -> ~ (forall y2 : nat, forall y3 : nat, forall y4 : nat, (Peano.lt (Nat.add y2 y4) (Nat.add y3 y4)) = (Peano.lt y2 y3)).
Definition term183 := forall y0 : nat, forall y1 : nat, (Peano.lt y1 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) -> (Peano.le y0 y1) -> (~ (Peano.lt (Nat.sub y1 y0) y0)) -> (forall y2 : nat, forall y3 : nat, forall y4 : nat, forall y5 : nat, ((Peano.lt y2 y4) /\ (Peano.lt y3 y5)) -> Peano.lt (Nat.add y2 y3) (Nat.add y4 y5)) -> (forall y2 : nat, (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y2) = (Nat.add y2 y2)) -> (forall y2 : nat, forall y3 : nat, (Peano.le y3 y2) -> (Nat.add (Nat.sub y2 y3) y3) = y2) -> (forall y2 : nat, forall y3 : nat, forall y4 : nat, (Peano.lt (Nat.add y2 y4) (Nat.add y3 y4)) = (Peano.lt y2 y3)) -> False.
Definition term161 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.lt (Nat.add y0 y2) (Nat.add y1 y2)) = (Peano.lt y0 y1).
Definition term102 := forall y0 : nat, forall y1 : nat, (~ (Peano.le y1 y0)) \/ ((Nat.add (Nat.sub y0 y1) y1) = y0).
Definition term96 := forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0).
Definition term88 := forall y0 : nat, forall y1 : nat, (Peano.lt y1 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) -> (Peano.le y0 y1) -> (~ (y1 = (Nat.add y0 (Nat.sub y1 y0)))) -> (forall y2 : nat, forall y3 : nat, (Nat.add y2 y3) = (Nat.add y3 y2)) -> ~ (forall y2 : nat, forall y3 : nat, (Peano.le y3 y2) -> (Nat.add (Nat.sub y2 y3) y3) = y2).
Definition term87 := forall y0 : nat, forall y1 : nat, (Peano.lt y1 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) -> (Peano.le y0 y1) -> (~ (y1 = (Nat.add y0 (Nat.sub y1 y0)))) -> (forall y2 : nat, forall y3 : nat, (Nat.add y2 y3) = (Nat.add y3 y2)) -> (forall y2 : nat, forall y3 : nat, (Peano.le y3 y2) -> (Nat.add (Nat.sub y2 y3) y3) = y2) -> False.
Definition term69 := forall y0 : nat, forall y1 : nat, (Peano.le y1 y0) -> (Nat.add (Nat.sub y0 y1) y1) = y0.
Definition term25 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (exists y3 : nat, (y0 = (Nat.add (Nat.mul y3 y1) y2)) /\ (Peano.lt y2 y1)) -> (Nat.modulo y0 y1) = y2.
Definition term24 (x0 : nat) := forall y0 : nat, forall y1 : nat, (exists y2 : nat, (x0 = (Nat.add (Nat.mul y2 y0) y1)) /\ (Peano.lt y1 y0)) -> (Nat.modulo x0 y0) = y1.
Definition term13 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, ((x0 = (Nat.add (Nat.mul y0 x1) y1)) /\ (Peano.lt y1 x1)) -> (Nat.modulo x0 x1) = y1.
Definition term11 (x0 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((x0 = (Nat.add (Nat.mul y1 y0) y2)) /\ (Peano.lt y2 y0)) -> (Nat.modulo x0 y0) = y2.
Definition term9 := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y0 = (Nat.add (Nat.mul y2 y1) y3)) /\ (Peano.lt y3 y1)) -> (Nat.modulo y0 y1) = y3.
Definition term80 (x0 : nat) (x1 : nat) := (Peano.lt x0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) -> (Peano.le x1 x0) -> (~ (x0 = (Nat.add x1 (Nat.sub x0 x1)))) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> ~ (forall y0 : nat, forall y1 : nat, (Peano.le y1 y0) -> (Nat.add (Nat.sub y0 y1) y1) = y0).
Definition term30 (x0 : nat) (x1 : nat) := Peano.lt x0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1).
Definition term307 (x0 : nat) := ((fun y0 : nat => forall y1 : nat, (forall y2 : nat, Peano.lt (Nat.add y0 y2) (Nat.add y1 y2)) \/ (~ (Peano.lt y0 y1))) x0) /\ ((fun y0 : nat => forall y1 : nat, (forall y2 : nat, ~ (Peano.lt (Nat.add y0 y2) (Nat.add y1 y2))) \/ (Peano.lt y0 y1)) x0).
Definition term37 (x0 : nat) (x1 : nat) := ((Peano.lt x0 x1) -> (fun y0 : nat => (Nat.modulo x0 x1) = y0) x0) /\ ((~ (Peano.lt x0 x1)) -> (fun y0 : nat => (Nat.modulo x0 x1) = y0) (Nat.sub x0 x1)).
Definition term173 (x0 : nat) (x1 : nat) := (~ (Peano.lt (Nat.sub x0 x1) x1)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.lt y0 y2) /\ (Peano.lt y1 y3)) -> Peano.lt (Nat.add y0 y1) (Nat.add y2 y3)) -> (forall y0 : nat, (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (Nat.add y0 y0)) -> (forall y0 : nat, forall y1 : nat, (Peano.le y1 y0) -> (Nat.add (Nat.sub y0 y1) y1) = y0) -> ~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.lt (Nat.add y0 y2) (Nat.add y1 y2)) = (Peano.lt y0 y1)).
Definition term240 (x0 : nat -> Prop) (x1 : Prop) := (forall y0 : nat, x0 y0) \/ x1.
Definition term14 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => forall y1 : nat, ((x0 = (Nat.add (Nat.mul y0 x1) y1)) /\ (Peano.lt y1 x1)) -> (Nat.modulo x0 x1) = y1) x2.
Definition term6 (x0 : nat) := forall y0 : nat, (~ (Peano.lt x0 y0)) = (Peano.le y0 x0).
Definition term12 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((x0 = (Nat.add (Nat.mul y1 y0) y2)) /\ (Peano.lt y2 y0)) -> (Nat.modulo x0 y0) = y2) x1.
Definition term63 (x0 : nat) (x1 : nat) := (Peano.lt x0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) -> (Peano.le x1 x0) -> (~ (x0 = (Nat.add x1 (Nat.sub x0 x1)))) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> (forall y0 : nat, forall y1 : nat, (Peano.le y1 y0) -> (Nat.add (Nat.sub y0 y1) y1) = y0) -> False.
Definition term256 (x0 : nat) (x1 : nat) := (forall y0 : nat, Peano.lt (Nat.add x0 y0) (Nat.add x1 y0)) \/ (~ (Peano.lt x0 x1)).
Definition term263 (x0 : nat) (x1 : nat) (x2 : nat) := or ((fun y0 : nat => ~ (Peano.lt (Nat.add x0 y0) (Nat.add x1 y0))) x2).
Definition term111 (x0 : nat) (x1 : nat) := ((Nat.add (Nat.sub x1 x0) x0) = x1) \/ (~ (Peano.le x0 x1)).
Definition term380 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((Peano.lt x0 x1) \/ (~ (Peano.lt (Nat.add x0 x2) (Nat.add x1 x2)))).
Definition term145 (x0 : nat) (x1 : nat) := ((Nat.add (Nat.sub x0 x1) x1) = x0) /\ ((Nat.add (Nat.sub x0 x1) x1) = (Nat.add x1 (Nat.sub x0 x1))).
Definition term275 (x0 : nat) (x1 : nat) := ((forall y0 : nat, Peano.lt (Nat.add x0 y0) (Nat.add x1 y0)) \/ (~ (Peano.lt x0 x1))) /\ ((forall y0 : nat, ~ (Peano.lt (Nat.add x0 y0) (Nat.add x1 y0))) \/ (Peano.lt x0 x1)).
Definition term230 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.lt (Nat.add x0 y0) (Nat.add x1 y0)) \/ (~ (Peano.lt x0 x1)).
Definition term386 (x0 : nat) (x1 : nat) := (Peano.lt (Nat.add (Nat.sub x0 x1) x1) (Nat.add x1 x1)) -> Peano.lt (Nat.sub x0 x1) x1.
Definition term194 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Peano.lt x0 x2) /\ (Peano.lt x1 x3)) -> Peano.lt (Nat.add x0 x1) (Nat.add x2 x3).
Definition term2 := forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0.
Definition term3 (x0 : nat) := (fun y0 : nat => (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) x0.
Definition term19 (x0 : nat) (x1 : nat) (x2 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y0 = (Nat.add (Nat.mul y2 y1) y3)) /\ (Peano.lt y3 y1)) -> (Nat.modulo y0 y1) = y3) -> (Nat.modulo x0 x1) = x2.
Definition term335 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x2 = x0) -> (~ (x3 = x1)) \/ ((Peano.lt x0 x1) \/ (~ (Peano.lt x2 x3))).
Definition term34 (x0 : nat) (x1 : Prop) (x2 : nat) (x3 : nat) (x4 : nat) := (x1 -> (fun y0 : nat => (Nat.modulo x2 x3) = y0) x0) /\ ((~ x1) -> (fun y0 : nat => (Nat.modulo x2 x3) = y0) x4).
Definition term284 (x0 : nat) (x1 : nat) := (fun y0 : nat => (forall y1 : nat, ~ (Peano.lt (Nat.add x0 y1) (Nat.add y0 y1))) \/ (Peano.lt x0 y0)) x1.
Definition term124 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = x2) \/ (~ (x1 = x2)).
Definition term362 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ~ ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (Peano.lt x2 x3)))).
Definition term351 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.lt x0 x3) \/ ((~ (Peano.lt x1 x2)) \/ (~ (x2 = x3))).
Definition term169 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.lt y0 y2) /\ (Peano.lt y1 y3)) -> Peano.lt (Nat.add y0 y1) (Nat.add y2 y3)) -> (forall y0 : nat, (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (Nat.add y0 y0)) -> (forall y0 : nat, forall y1 : nat, (Peano.le y1 y0) -> (Nat.add (Nat.sub y0 y1) y1) = y0) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.lt (Nat.add y0 y2) (Nat.add y1 y2)) = (Peano.lt y0 y1)) -> False.
Definition term218 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.lt (Nat.add x0 y0) (Nat.add x1 y0)) \/ (~ (Peano.lt x0 x1))) x2.
Definition term332 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x3 = x1) -> (Peano.lt x0 x1) \/ (~ (Peano.lt x2 x3)).
Definition term273 (x0 : nat) (x1 : nat) := or (forall y0 : nat, ~ (Peano.lt (Nat.add x0 y0) (Nat.add x1 y0))).
Definition term51 (x0 : nat) (x1 : nat) := @eq Prop ((Nat.modulo x0 x1) = (@COND nat (Peano.lt x0 x1) x0 (Nat.sub x0 x1))).
Definition term94 (x0 : nat) := forall y0 : nat, (Nat.add x0 y0) = (Nat.add y0 x0).
Definition term285 (x0 : nat) (x1 : nat) := ((fun y0 : nat => (forall y1 : nat, Peano.lt (Nat.add x0 y1) (Nat.add y0 y1)) \/ (~ (Peano.lt x0 y0))) x1) /\ ((fun y0 : nat => (forall y1 : nat, ~ (Peano.lt (Nat.add x0 y1) (Nat.add y0 y1))) \/ (Peano.lt x0 y0)) x1).
Definition term213 (x0 : nat -> Prop) (x1 : nat -> Prop) := (forall y0 : nat, x0 y0) /\ (forall y0 : nat, x1 y0).
Definition term346 (x0 : nat) (x1 : nat) := ~ (Peano.lt x0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)).
Definition term237 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := forall y0 : a0, (x0 y0) \/ x1.
Definition term178 (x0 : nat) := fun y0 : nat => (Peano.lt y0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) -> (Peano.le x0 y0) -> (~ (Peano.lt (Nat.sub y0 x0) x0)) -> (forall y1 : nat, forall y2 : nat, forall y3 : nat, forall y4 : nat, ((Peano.lt y1 y3) /\ (Peano.lt y2 y4)) -> Peano.lt (Nat.add y1 y2) (Nat.add y3 y4)) -> (forall y1 : nat, (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1) = (Nat.add y1 y1)) -> (forall y1 : nat, forall y2 : nat, (Peano.le y2 y1) -> (Nat.add (Nat.sub y1 y2) y2) = y1) -> ~ (forall y1 : nat, forall y2 : nat, forall y3 : nat, (Peano.lt (Nat.add y1 y3) (Nat.add y2 y3)) = (Peano.lt y1 y2)).
Definition term177 (x0 : nat) := fun y0 : nat => (Peano.lt y0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) -> (Peano.le x0 y0) -> (~ (Peano.lt (Nat.sub y0 x0) x0)) -> (forall y1 : nat, forall y2 : nat, forall y3 : nat, forall y4 : nat, ((Peano.lt y1 y3) /\ (Peano.lt y2 y4)) -> Peano.lt (Nat.add y1 y2) (Nat.add y3 y4)) -> (forall y1 : nat, (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1) = (Nat.add y1 y1)) -> (forall y1 : nat, forall y2 : nat, (Peano.le y2 y1) -> (Nat.add (Nat.sub y1 y2) y2) = y1) -> (forall y1 : nat, forall y2 : nat, forall y3 : nat, (Peano.lt (Nat.add y1 y3) (Nat.add y2 y3)) = (Peano.lt y1 y2)) -> False.
Definition term82 (x0 : nat) := fun y0 : nat => (Peano.lt y0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) -> (Peano.le x0 y0) -> (~ (y0 = (Nat.add x0 (Nat.sub y0 x0)))) -> (forall y1 : nat, forall y2 : nat, (Nat.add y1 y2) = (Nat.add y2 y1)) -> ~ (forall y1 : nat, forall y2 : nat, (Peano.le y2 y1) -> (Nat.add (Nat.sub y1 y2) y2) = y1).
Definition term81 (x0 : nat) := fun y0 : nat => (Peano.lt y0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) -> (Peano.le x0 y0) -> (~ (y0 = (Nat.add x0 (Nat.sub y0 x0)))) -> (forall y1 : nat, forall y2 : nat, (Nat.add y1 y2) = (Nat.add y2 y1)) -> (forall y1 : nat, forall y2 : nat, (Peano.le y2 y1) -> (Nat.add (Nat.sub y1 y2) y2) = y1) -> False.
Definition term127 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x1 = x0)) \/ ((x0 = x2) \/ (~ (x1 = x2))).
Definition term373 (x0 : nat) (x1 : nat) := (x0 = (Nat.add (Nat.sub x0 x1) x1)) /\ (((Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1) = (Nat.add x1 x1)) /\ (Peano.lt x0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1))).
Definition term393 (x0 : nat) (x1 : nat) := fun y0 : nat => (x0 = (Nat.add (Nat.mul y0 x1) (Nat.sub x0 x1))) /\ (Peano.lt (Nat.sub x0 x1) x1).
Definition term43 (x0 : nat) (x1 : nat) := imp (Peano.lt x0 x1).
Definition term33 (x0 : nat) (x1 : nat) (x2 : Prop) (x3 : nat) (x4 : nat) := (fun y0 : nat => (Nat.modulo x0 x1) = y0) (@COND nat x2 x3 x4).
Definition term45 (x0 : nat) (x1 : nat) := (Peano.lt x1 x0) -> (Nat.modulo x1 x0) = x1.
Definition term104 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add x0 y0) = (Nat.add y0 x0)) x1.
Definition term262 (x0 : nat) (x1 : nat) (x2 : nat) := ~ (Peano.lt (Nat.add x0 x2) (Nat.add x1 x2)).
Definition term139 (x0 : nat) (x1 : nat) := and (~ (~ (x0 = x1))).
Definition term384 (x0 : nat) (x1 : nat) (x2 : nat) := imp (Peano.lt (Nat.add x0 x2) (Nat.add x1 x2)).
Definition term75 (x0 : nat) (x1 : nat) := (~ (x0 = (Nat.add x1 (Nat.sub x0 x1)))) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> ~ (forall y0 : nat, forall y1 : nat, (Peano.le y1 y0) -> (Nat.add (Nat.sub y0 y1) y1) = y0).
Definition term146 (x0 : nat) (x1 : nat) := (((Nat.add (Nat.sub x0 x1) x1) = x0) /\ ((Nat.add (Nat.sub x0 x1) x1) = (Nat.add x1 (Nat.sub x0 x1)))) -> x0 = (Nat.add x1 (Nat.sub x0 x1)).
Definition term360 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.lt x0 x1) \/ ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (Peano.lt x2 x3)))).
Definition term340 (x0 : nat) (x1 : nat) := (((Nat.add (Nat.sub x0 x1) x1) = x0) /\ ((Nat.add (Nat.sub x0 x1) x1) = (Nat.add (Nat.sub x0 x1) x1))) -> x0 = (Nat.add (Nat.sub x0 x1) x1).
Definition term247 (x0 : nat) (x1 : nat) (x2 : nat) := ((fun y0 : nat => Peano.lt (Nat.add x1 y0) (Nat.add x2 y0)) x0) \/ (~ (Peano.lt x1 x2)).
Definition term329 (x0 : Prop) (x1 : Prop) := (x1 = x0) -> x0 \/ (~ x1).
Definition term297 (x0 : nat) := (forall y0 : nat, (forall y1 : nat, Peano.lt (Nat.add x0 y1) (Nat.add y0 y1)) \/ (~ (Peano.lt x0 y0))) /\ (forall y0 : nat, (forall y1 : nat, ~ (Peano.lt (Nat.add x0 y1) (Nat.add y0 y1))) \/ (Peano.lt x0 y0)).
Definition term236 (x0 : nat) (x1 : nat) := (forall y0 : nat, (Peano.lt (Nat.add x0 y0) (Nat.add x1 y0)) \/ (~ (Peano.lt x0 x1))) /\ (forall y0 : nat, (~ (Peano.lt (Nat.add x0 y0) (Nat.add x1 y0))) \/ (Peano.lt x0 x1)).
Definition term46 (x0 : nat) (x1 : nat) := and ((Peano.lt x1 x0) -> (fun y0 : nat => (Nat.modulo x1 x0) = y0) x1).
Definition term23 (x0 : nat) (x1 : nat) := forall y0 : nat, (exists y1 : nat, (x0 = (Nat.add (Nat.mul y1 x1) y0)) /\ (Peano.lt y0 x1)) -> (Nat.modulo x0 x1) = y0.
Definition term251 (x0 : nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => Peano.lt (Nat.add x0 y1) (Nat.add x1 y1)) y0.
Definition term315 := and (forall y0 : nat, forall y1 : nat, (forall y2 : nat, Peano.lt (Nat.add y0 y2) (Nat.add y1 y2)) \/ (~ (Peano.lt y0 y1))).
Definition term374 (x0 : nat) (x1 : nat) := ((x0 = (Nat.add (Nat.sub x0 x1) x1)) /\ (((Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1) = (Nat.add x1 x1)) /\ (Peano.lt x0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)))) -> Peano.lt (Nat.add (Nat.sub x0 x1) x1) (Nat.add x1 x1).
Definition term8 (x0 : nat) (x1 : nat) := ~ (Peano.lt x0 x1).
Definition term77 (x0 : nat) (x1 : nat) := (Peano.le x1 x0) -> (~ (x0 = (Nat.add x1 (Nat.sub x0 x1)))) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> (forall y0 : nat, forall y1 : nat, (Peano.le y1 y0) -> (Nat.add (Nat.sub y0 y1) y1) = y0) -> False.
Definition term167 := (forall y0 : nat, (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (Nat.add y0 y0)) -> (forall y0 : nat, forall y1 : nat, (Peano.le y1 y0) -> (Nat.add (Nat.sub y0 y1) y1) = y0) -> ~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.lt (Nat.add y0 y2) (Nat.add y1 y2)) = (Peano.lt y0 y1)).
Definition term241 (x0 : nat) (x1 : nat) := forall y0 : nat, ((fun y1 : nat => Peano.lt (Nat.add x0 y1) (Nat.add x1 y1)) y0) \/ (~ (Peano.lt x0 x1)).
Definition term316 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (forall y3 : nat, ~ (Peano.lt (Nat.add y1 y3) (Nat.add y2 y3))) \/ (Peano.lt y1 y2)) y0.
Definition term311 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (forall y3 : nat, Peano.lt (Nat.add y1 y3) (Nat.add y2 y3)) \/ (~ (Peano.lt y1 y2))) y0.
Definition term47 (x0 : nat) (x1 : nat) := and ((Peano.lt x1 x0) -> (Nat.modulo x1 x0) = x1).
Definition term79 (x0 : nat) (x1 : nat) := imp (Peano.lt x0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)).
Definition term389 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y1 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) -> (Peano.le y0 y1) -> (~ (Peano.lt (Nat.sub y1 y0) y0)) -> (forall y2 : nat, forall y3 : nat, forall y4 : nat, forall y5 : nat, ((Peano.lt y2 y4) /\ (Peano.lt y3 y5)) -> Peano.lt (Nat.add y2 y3) (Nat.add y4 y5)) -> (forall y2 : nat, (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y2) = (Nat.add y2 y2)) -> (forall y2 : nat, forall y3 : nat, (Peano.le y3 y2) -> (Nat.add (Nat.sub y2 y3) y3) = y2) -> (forall y2 : nat, forall y3 : nat, forall y4 : nat, (Peano.lt (Nat.add y2 y4) (Nat.add y3 y4)) = (Peano.lt y2 y3)) -> False) x0.
Definition term306 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (forall y2 : nat, ~ (Peano.lt (Nat.add y0 y2) (Nat.add y1 y2))) \/ (Peano.lt y0 y1)) x0.
Definition term304 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (forall y2 : nat, Peano.lt (Nat.add y0 y2) (Nat.add y1 y2)) \/ (~ (Peano.lt y0 y1))) x0.
Definition term150 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y1 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) -> (Peano.le y0 y1) -> (~ (y1 = (Nat.add y0 (Nat.sub y1 y0)))) -> (forall y2 : nat, forall y3 : nat, (Nat.add y2 y3) = (Nat.add y3 y2)) -> (forall y2 : nat, forall y3 : nat, (Peano.le y3 y2) -> (Nat.add (Nat.sub y2 y3) y3) = y2) -> False) x0.
Definition term105 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (Peano.le y1 y0)) \/ ((Nat.add (Nat.sub y0 y1) y1) = y0)) x0.
Definition term103 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) x0.
Definition term52 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y0 y1) -> (Nat.modulo y0 y1) = y0) x0.
Definition term5 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)) x0.
Definition term368 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x2 = x0) /\ ((x3 = x1) /\ (Peano.lt x2 x3)).
Definition term112 (x0 : nat) (x1 : nat) := @eq Prop ((~ (Peano.le x0 x1)) \/ ((Nat.add (Nat.sub x1 x0) x0) = x1)).
Definition term99 (x0 : nat) := fun y0 : nat => (~ (Peano.le y0 x0)) \/ ((Nat.add (Nat.sub x0 y0) y0) = x0).
Definition term117 (x0 : nat) (x1 : nat) := ~ (~ (Peano.le x0 x1)).
Definition term38 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.modulo x0 x1) = y0) (Nat.sub x0 x1).
Definition term196 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, ((Peano.lt x0 x2) /\ (Peano.lt x1 y0)) -> Peano.lt (Nat.add x0 x1) (Nat.add x2 y0).
Definition term375 (x0 : nat) (x1 : nat) := Peano.lt (Nat.add (Nat.sub x0 x1) x1) (Nat.add x1 x1).
Definition term100 (x0 : nat) := forall y0 : nat, (~ (Peano.le y0 x0)) \/ ((Nat.add (Nat.sub x0 y0) y0) = x0).
Definition term338 (x0 : nat) (x1 : nat) := ~ ((Nat.add (Nat.sub x0 x1) x1) = (Nat.add (Nat.sub x0 x1) x1)).
Definition term359 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (Peano.lt x2 x3))).
Definition term354 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x1 = x0)) \/ ((~ (Peano.lt x1 x2)) \/ (~ (x2 = x3))).
Definition term379 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((~ (Peano.lt (Nat.add x1 x0) (Nat.add x2 x0))) \/ (Peano.lt x1 x2)).
Definition term364 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((~ (x2 = x0)) \/ (~ (Peano.lt x1 x2))).
Definition term136 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term264 (x0 : nat) (x1 : nat) (x2 : nat) := or (~ (Peano.lt (Nat.add x0 x2) (Nat.add x1 x2))).
Definition term73 (x0 : nat) (x1 : nat) := imp (~ (x0 = (Nat.add x1 (Nat.sub x0 x1)))).
Definition term357 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ ((Peano.lt x0 x1) \/ (~ (Peano.lt x2 x3))))).
Definition term245 (x0 : nat) (x1 : nat) (x2 : nat) := or ((fun y0 : nat => Peano.lt (Nat.add x0 y0) (Nat.add x1 y0)) x2).
Definition term152 (x0 : nat) (x1 : nat) := Peano.lt (Nat.sub x0 x1) x1.
Definition term294 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (forall y2 : nat, ~ (Peano.lt (Nat.add x0 y2) (Nat.add y1 y2))) \/ (Peano.lt x0 y1)) y0.
Definition term233 (x0 : nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => (~ (Peano.lt (Nat.add x0 y1) (Nat.add x1 y1))) \/ (Peano.lt x0 x1)) y0.
Definition term42 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.modulo x1 x0) = y0) x1.
Definition term164 := (forall y0 : nat, forall y1 : nat, (Peano.le y1 y0) -> (Nat.add (Nat.sub y0 y1) y1) = y0) -> ~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.lt (Nat.add y0 y2) (Nat.add y1 y2)) = (Peano.lt y0 y1)).
Definition term72 := (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> ~ (forall y0 : nat, forall y1 : nat, (Peano.le y1 y0) -> (Nat.add (Nat.sub y0 y1) y1) = y0).
Definition term242 (x0 : nat) (x1 : nat) := (forall y0 : nat, (fun y1 : nat => Peano.lt (Nat.add x0 y1) (Nat.add x1 y1)) y0) \/ (~ (Peano.lt x0 x1)).
Definition term314 := and (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (forall y3 : nat, Peano.lt (Nat.add y1 y3) (Nat.add y2 y3)) \/ (~ (Peano.lt y1 y2))) y0).
Definition term292 (x0 : nat) := and (forall y0 : nat, (fun y1 : nat => (forall y2 : nat, Peano.lt (Nat.add x0 y2) (Nat.add y1 y2)) \/ (~ (Peano.lt x0 y1))) y0).
Definition term231 (x0 : nat) (x1 : nat) := and (forall y0 : nat, (fun y1 : nat => (Peano.lt (Nat.add x0 y1) (Nat.add x1 y1)) \/ (~ (Peano.lt x0 x1))) y0).
Definition term115 (x0 : nat) (x1 : nat) := (~ (~ (Peano.le x0 x1))) -> (Nat.add (Nat.sub x1 x0) x0) = x1.
Definition term333 (x0 : Prop) (x1 : Prop) := (~ x0) \/ x1.
Definition term363 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (~ (x2 = x0))) /\ (~ ((~ (x3 = x1)) \/ (~ (Peano.lt x2 x3)))).
Definition term305 (x0 : nat) := and ((fun y0 : nat => forall y1 : nat, (forall y2 : nat, Peano.lt (Nat.add y0 y2) (Nat.add y1 y2)) \/ (~ (Peano.lt y0 y1))) x0).
Definition term269 (x0 : nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => ~ (Peano.lt (Nat.add x0 y1) (Nat.add x1 y1))) y0.
Definition term216 (x0 : nat) (x1 : nat) := fun y0 : nat => (Peano.lt (Nat.add x0 y0) (Nat.add x1 y0)) \/ (~ (Peano.lt x0 x1)).
Definition term176 (x0 : nat) (x1 : nat) := (Peano.lt x0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) -> (Peano.le x1 x0) -> (~ (Peano.lt (Nat.sub x0 x1) x1)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.lt y0 y2) /\ (Peano.lt y1 y3)) -> Peano.lt (Nat.add y0 y1) (Nat.add y2 y3)) -> (forall y0 : nat, (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (Nat.add y0 y0)) -> (forall y0 : nat, forall y1 : nat, (Peano.le y1 y0) -> (Nat.add (Nat.sub y0 y1) y1) = y0) -> ~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.lt (Nat.add y0 y2) (Nat.add y1 y2)) = (Peano.lt y0 y1)).
Definition term155 (x0 : nat) (x1 : nat) := (Peano.lt x0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) -> (Peano.le x1 x0) -> (~ (Peano.lt (Nat.sub x0 x1) x1)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.lt y0 y2) /\ (Peano.lt y1 y3)) -> Peano.lt (Nat.add y0 y1) (Nat.add y2 y3)) -> (forall y0 : nat, (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (Nat.add y0 y0)) -> (forall y0 : nat, forall y1 : nat, (Peano.le y1 y0) -> (Nat.add (Nat.sub y0 y1) y1) = y0) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.lt (Nat.add y0 y2) (Nat.add y1 y2)) = (Peano.lt y0 y1)) -> False.
Definition term355 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (Peano.lt x0 x2)) \/ ((~ (x0 = x1)) \/ (~ (x2 = x3))).
Definition term302 := fun y0 : nat => forall y1 : nat, (forall y2 : nat, Peano.lt (Nat.add y0 y2) (Nat.add y1 y2)) \/ (~ (Peano.lt y0 y1)).
Definition term143 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((x1 = x0) /\ (x1 = x2)).
Definition term210 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term377 (x0 : nat) (x1 : nat) := ~ (Peano.lt (Nat.add (Nat.sub x0 x1) x1) (Nat.add x1 x1)).
Definition term299 := forall y0 : nat, (forall y1 : nat, (forall y2 : nat, Peano.lt (Nat.add y0 y2) (Nat.add y1 y2)) \/ (~ (Peano.lt y0 y1))) /\ (forall y1 : nat, (forall y2 : nat, ~ (Peano.lt (Nat.add y0 y2) (Nat.add y1 y2))) \/ (Peano.lt y0 y1)).
Definition term98 (x0 : nat) (x1 : nat) := Nat.add (Nat.sub x0 x1) x1.
Definition term175 (x0 : nat) (x1 : nat) := (Peano.le x1 x0) -> (~ (Peano.lt (Nat.sub x0 x1) x1)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.lt y0 y2) /\ (Peano.lt y1 y3)) -> Peano.lt (Nat.add y0 y1) (Nat.add y2 y3)) -> (forall y0 : nat, (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (Nat.add y0 y0)) -> (forall y0 : nat, forall y1 : nat, (Peano.le y1 y0) -> (Nat.add (Nat.sub y0 y1) y1) = y0) -> ~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.lt (Nat.add y0 y2) (Nat.add y1 y2)) = (Peano.lt y0 y1)).
Definition term174 (x0 : nat) (x1 : nat) := (Peano.le x1 x0) -> (~ (Peano.lt (Nat.sub x0 x1) x1)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.lt y0 y2) /\ (Peano.lt y1 y3)) -> Peano.lt (Nat.add y0 y1) (Nat.add y2 y3)) -> (forall y0 : nat, (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (Nat.add y0 y0)) -> (forall y0 : nat, forall y1 : nat, (Peano.le y1 y0) -> (Nat.add (Nat.sub y0 y1) y1) = y0) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.lt (Nat.add y0 y2) (Nat.add y1 y2)) = (Peano.lt y0 y1)) -> False.
Definition term36 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.modulo x0 x1) = y0) (@COND nat (Peano.lt x0 x1) x0 (Nat.sub x0 x1)).
Definition term396 (x0 : nat) := forall y0 : nat, (Peano.lt x0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) -> (Nat.modulo x0 y0) = (@COND nat (Peano.lt x0 y0) x0 (Nat.sub x0 y0)).
Definition term180 (x0 : nat) := forall y0 : nat, (Peano.lt y0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) -> (Peano.le x0 y0) -> (~ (Peano.lt (Nat.sub y0 x0) x0)) -> (forall y1 : nat, forall y2 : nat, forall y3 : nat, forall y4 : nat, ((Peano.lt y1 y3) /\ (Peano.lt y2 y4)) -> Peano.lt (Nat.add y1 y2) (Nat.add y3 y4)) -> (forall y1 : nat, (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1) = (Nat.add y1 y1)) -> (forall y1 : nat, forall y2 : nat, (Peano.le y2 y1) -> (Nat.add (Nat.sub y1 y2) y2) = y1) -> ~ (forall y1 : nat, forall y2 : nat, forall y3 : nat, (Peano.lt (Nat.add y1 y3) (Nat.add y2 y3)) = (Peano.lt y1 y2)).
Definition term179 (x0 : nat) := forall y0 : nat, (Peano.lt y0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) -> (Peano.le x0 y0) -> (~ (Peano.lt (Nat.sub y0 x0) x0)) -> (forall y1 : nat, forall y2 : nat, forall y3 : nat, forall y4 : nat, ((Peano.lt y1 y3) /\ (Peano.lt y2 y4)) -> Peano.lt (Nat.add y1 y2) (Nat.add y3 y4)) -> (forall y1 : nat, (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1) = (Nat.add y1 y1)) -> (forall y1 : nat, forall y2 : nat, (Peano.le y2 y1) -> (Nat.add (Nat.sub y1 y2) y2) = y1) -> (forall y1 : nat, forall y2 : nat, forall y3 : nat, (Peano.lt (Nat.add y1 y3) (Nat.add y2 y3)) = (Peano.lt y1 y2)) -> False.
Definition term84 (x0 : nat) := forall y0 : nat, (Peano.lt y0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) -> (Peano.le x0 y0) -> (~ (y0 = (Nat.add x0 (Nat.sub y0 x0)))) -> (forall y1 : nat, forall y2 : nat, (Nat.add y1 y2) = (Nat.add y2 y1)) -> ~ (forall y1 : nat, forall y2 : nat, (Peano.le y2 y1) -> (Nat.add (Nat.sub y1 y2) y2) = y1).
Definition term83 (x0 : nat) := forall y0 : nat, (Peano.lt y0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) -> (Peano.le x0 y0) -> (~ (y0 = (Nat.add x0 (Nat.sub y0 x0)))) -> (forall y1 : nat, forall y2 : nat, (Nat.add y1 y2) = (Nat.add y2 y1)) -> (forall y1 : nat, forall y2 : nat, (Peano.le y2 y1) -> (Nat.add (Nat.sub y1 y2) y2) = y1) -> False.
Definition term283 (x0 : nat) (x1 : nat) := and ((fun y0 : nat => (forall y1 : nat, Peano.lt (Nat.add x0 y1) (Nat.add y0 y1)) \/ (~ (Peano.lt x0 y0))) x1).
Definition term217 (x0 : nat) (x1 : nat) := fun y0 : nat => (~ (Peano.lt (Nat.add x0 y0) (Nat.add x1 y0))) \/ (Peano.lt x0 x1).
Definition term113 (x0 : nat) (x1 : nat) := @eq Prop (((Nat.add (Nat.sub x1 x0) x0) = x1) \/ (~ (Peano.le x0 x1))).
Definition term291 (x0 : nat) := forall y0 : nat, (forall y1 : nat, Peano.lt (Nat.add x0 y1) (Nat.add y0 y1)) \/ (~ (Peano.lt x0 y0)).
Definition term388 (x0 : nat) (x1 : nat) := (Peano.lt (Nat.sub x0 x1) x1) -> False.
Definition term123 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = x2)) \/ (x1 = x2).
Definition term7 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (Peano.lt x0 y0)) = (Peano.le y0 x0)) x1.
Definition term78 (x0 : nat) (x1 : nat) := (Peano.le x1 x0) -> (~ (x0 = (Nat.add x1 (Nat.sub x0 x1)))) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> ~ (forall y0 : nat, forall y1 : nat, (Peano.le y1 y0) -> (Nat.add (Nat.sub y0 y1) y1) = y0).
Definition term244 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => Peano.lt (Nat.add x0 y0) (Nat.add x1 y0)) x2.
Definition term138 (x0 : nat) (x1 : nat) := ~ (~ (x0 = x1)).
Definition term89 (x0 : nat) (x1 : nat) := (Peano.le x0 x1) -> (Nat.add (Nat.sub x1 x0) x0) = x1.
Definition term258 (x0 : nat) (x1 : nat) := forall y0 : nat, ((fun y1 : nat => ~ (Peano.lt (Nat.add x0 y1) (Nat.add x1 y1))) y0) \/ (Peano.lt x0 x1).
Definition term49 (x0 : nat) (x1 : nat) := @COND nat (Peano.lt x0 x1) x0 (Nat.sub x0 x1).
Definition term50 (x0 : nat) (x1 : nat) := @eq Prop ((fun y0 : nat => (Nat.modulo x0 x1) = y0) (@COND nat (Peano.lt x0 x1) x0 (Nat.sub x0 x1))).
Definition term126 (x0 : nat) (x1 : nat) := or (~ (x0 = x1)).
Definition term120 (x0 : nat) (x1 : nat) := ~ ((Nat.add (Nat.sub x1 x0) x0) = x1).
Definition term317 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (forall y3 : nat, ~ (Peano.lt (Nat.add y1 y3) (Nat.add y2 y3))) \/ (Peano.lt y1 y2)) y0.
Definition term312 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (forall y3 : nat, Peano.lt (Nat.add y1 y3) (Nat.add y2 y3)) \/ (~ (Peano.lt y1 y2))) y0.
Definition term58 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul (NUMERAL (BIT1 0)) x1) (Nat.sub x0 x1).
Definition term168 := imp (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.lt y0 y2) /\ (Peano.lt y1 y3)) -> Peano.lt (Nat.add y0 y1) (Nat.add y2 y3)).
Definition term162 := imp (forall y0 : nat, forall y1 : nat, (Peano.le y1 y0) -> (Nat.add (Nat.sub y0 y1) y1) = y0).
Definition term70 := imp (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)).
Definition term0 := (forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))).
Definition term185 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.lt (Nat.add x0 x2) (Nat.add x1 x2).
Definition term395 (x0 : nat) (x1 : nat) := (Peano.lt x0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) -> (Nat.modulo x0 x1) = (@COND nat (Peano.lt x0 x1) x0 (Nat.sub x0 x1)).
Definition term144 (x0 : nat) (x1 : nat) (x2 : nat) := ((x0 = x1) /\ (x0 = x2)) -> x1 = x2.
Definition term166 := (forall y0 : nat, (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (Nat.add y0 y0)) -> (forall y0 : nat, forall y1 : nat, (Peano.le y1 y0) -> (Nat.add (Nat.sub y0 y1) y1) = y0) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.lt (Nat.add y0 y2) (Nat.add y1 y2)) = (Peano.lt y0 y1)) -> False.
Definition term336 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ ((Peano.lt x0 x1) \/ (~ (Peano.lt x2 x3)))).
Definition term282 (x0 : nat) (x1 : nat) := (fun y0 : nat => (forall y1 : nat, Peano.lt (Nat.add x0 y1) (Nat.add y0 y1)) \/ (~ (Peano.lt x0 y0))) x1.
Definition term378 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.lt x0 x1) \/ (~ (Peano.lt (Nat.add x0 x2) (Nat.add x1 x2))).
Definition term206 (x0 : nat) := fun y0 : nat => forall y1 : nat, ((Peano.lt (Nat.add x0 y1) (Nat.add y0 y1)) \/ (~ (Peano.lt x0 y0))) /\ ((~ (Peano.lt (Nat.add x0 y1) (Nat.add y0 y1))) \/ (Peano.lt x0 y0)).
Definition term197 (x0 : nat) (x1 : nat) := fun y0 : nat => forall y1 : nat, ((Peano.lt x0 y0) /\ (Peano.lt x1 y1)) -> Peano.lt (Nat.add x0 x1) (Nat.add y0 y1).
Definition term182 := fun y0 : nat => forall y1 : nat, (Peano.lt y1 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) -> (Peano.le y0 y1) -> (~ (Peano.lt (Nat.sub y1 y0) y0)) -> (forall y2 : nat, forall y3 : nat, forall y4 : nat, forall y5 : nat, ((Peano.lt y2 y4) /\ (Peano.lt y3 y5)) -> Peano.lt (Nat.add y2 y3) (Nat.add y4 y5)) -> (forall y2 : nat, (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y2) = (Nat.add y2 y2)) -> (forall y2 : nat, forall y3 : nat, (Peano.le y3 y2) -> (Nat.add (Nat.sub y2 y3) y3) = y2) -> ~ (forall y2 : nat, forall y3 : nat, forall y4 : nat, (Peano.lt (Nat.add y2 y4) (Nat.add y3 y4)) = (Peano.lt y2 y3)).
Definition term181 := fun y0 : nat => forall y1 : nat, (Peano.lt y1 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) -> (Peano.le y0 y1) -> (~ (Peano.lt (Nat.sub y1 y0) y0)) -> (forall y2 : nat, forall y3 : nat, forall y4 : nat, forall y5 : nat, ((Peano.lt y2 y4) /\ (Peano.lt y3 y5)) -> Peano.lt (Nat.add y2 y3) (Nat.add y4 y5)) -> (forall y2 : nat, (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y2) = (Nat.add y2 y2)) -> (forall y2 : nat, forall y3 : nat, (Peano.le y3 y2) -> (Nat.add (Nat.sub y2 y3) y3) = y2) -> (forall y2 : nat, forall y3 : nat, forall y4 : nat, (Peano.lt (Nat.add y2 y4) (Nat.add y3 y4)) = (Peano.lt y2 y3)) -> False.
Definition term86 := fun y0 : nat => forall y1 : nat, (Peano.lt y1 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) -> (Peano.le y0 y1) -> (~ (y1 = (Nat.add y0 (Nat.sub y1 y0)))) -> (forall y2 : nat, forall y3 : nat, (Nat.add y2 y3) = (Nat.add y3 y2)) -> ~ (forall y2 : nat, forall y3 : nat, (Peano.le y3 y2) -> (Nat.add (Nat.sub y2 y3) y3) = y2).
Definition term85 := fun y0 : nat => forall y1 : nat, (Peano.lt y1 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) -> (Peano.le y0 y1) -> (~ (y1 = (Nat.add y0 (Nat.sub y1 y0)))) -> (forall y2 : nat, forall y3 : nat, (Nat.add y2 y3) = (Nat.add y3 y2)) -> (forall y2 : nat, forall y3 : nat, (Peano.le y3 y2) -> (Nat.add (Nat.sub y2 y3) y3) = y2) -> False.
Definition term394 := NUMERAL (BIT1 0).
Definition term4 (x0 : nat) := Nat.mul (NUMERAL (BIT1 0)) x0.
Definition term223 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.lt (Nat.add x1 x0) (Nat.add x2 x0))) \/ (Peano.lt x1 x2).
Definition term255 (x0 : nat) (x1 : nat) := or (forall y0 : nat, Peano.lt (Nat.add x0 y0) (Nat.add x1 y0)).
Definition term296 (x0 : nat) := forall y0 : nat, (forall y1 : nat, ~ (Peano.lt (Nat.add x0 y1) (Nat.add y0 y1))) \/ (Peano.lt x0 y0).
Definition term324 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (~ (Peano.lt (Nat.add y0 y2) (Nat.add y1 y2))) \/ (Peano.lt y0 y1).
Definition term208 := fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.lt (Nat.add y0 y2) (Nat.add y1 y2)) \/ (~ (Peano.lt y0 y1))) /\ ((~ (Peano.lt (Nat.add y0 y2) (Nat.add y1 y2))) \/ (Peano.lt y0 y1)).
Definition term201 := fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.lt y0 y2) /\ (Peano.lt y1 y3)) -> Peano.lt (Nat.add y0 y1) (Nat.add y2 y3).
Definition term199 (x0 : nat) := fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.lt x0 y1) /\ (Peano.lt y0 y2)) -> Peano.lt (Nat.add x0 y0) (Nat.add y1 y2).
Definition term190 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.lt (Nat.add y0 y2) (Nat.add y1 y2)) = (Peano.lt y0 y1).
Definition term248 (x0 : nat) (x1 : nat) := fun y0 : nat => ((fun y1 : nat => Peano.lt (Nat.add x0 y1) (Nat.add x1 y1)) y0) \/ (~ (Peano.lt x0 x1)).
Definition term253 (x0 : nat) (x1 : nat) := forall y0 : nat, Peano.lt (Nat.add x0 y0) (Nat.add x1 y0).
Definition term387 (x0 : nat) (x1 : nat) := (~ (Peano.lt (Nat.sub x0 x1) x1)) -> Peano.lt (Nat.sub x0 x1) x1.
Definition term91 (x0 : nat) := forall y0 : nat, (Peano.le y0 x0) -> (Nat.add (Nat.sub x0 y0) y0) = x0.
Definition term53 (x0 : nat) := forall y0 : nat, (Peano.lt x0 y0) -> (Nat.modulo x0 y0) = x0.
Definition term56 (x0 : nat) (x1 : nat) := (exists y0 : nat, (x0 = (Nat.add (Nat.mul y0 x1) (Nat.sub x0 x1))) /\ (Peano.lt (Nat.sub x0 x1) x1)) -> (Nat.modulo x0 x1) = (Nat.sub x0 x1).
Definition term118 (x0 : nat) (x1 : nat) := imp (~ (~ (Peano.le x0 x1))).
