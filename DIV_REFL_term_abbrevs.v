Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term53 (x0 : nat) := ((fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) x0) -> (fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) (S x0).
Definition term71 (x0 : nat) := imp (~ ((S x0) = (NUMERAL 0))).
Definition term36 (x0 : nat) := and (x0 = (Nat.add (Nat.mul (NUMERAL (BIT1 0)) x0) (NUMERAL 0))).
Definition term76 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> (Nat.div x0 x0) = (NUMERAL (BIT1 0)).
Definition term1 (x0 : nat) := Peano.lt (NUMERAL 0) (S x0).
Definition term63 := fun y0 : nat => (fun y1 : nat => (~ (y1 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y1) y0.
Definition term70 := False -> Peano.lt (NUMERAL 0) (NUMERAL 0).
Definition term38 (x0 : nat) := (x0 = (Nat.add (Nat.mul (NUMERAL (BIT1 0)) x0) (NUMERAL 0))) /\ (Peano.lt (NUMERAL 0) x0).
Definition term3 := (forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))))).
Definition term29 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (exists y3 : nat, (y0 = (Nat.add (Nat.mul y2 y1) y3)) /\ (Peano.lt y3 y1)) -> (Nat.div y0 y1) = y2) x0.
Definition term12 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y0 = (Nat.add (Nat.mul y2 y1) y3)) /\ (Peano.lt y3 y1)) -> (Nat.div y0 y1) = y2) x0.
Definition term28 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y0 = (Nat.add (Nat.mul y2 y1) y3)) /\ (Peano.lt y3 y1)) -> (Nat.div y0 y1) = y2) -> forall y0 : nat, forall y1 : nat, forall y2 : nat, (exists y3 : nat, (y0 = (Nat.add (Nat.mul y2 y1) y3)) /\ (Peano.lt y3 y1)) -> (Nat.div y0 y1) = y2.
Definition term24 (x0 : nat) (x1 : nat) (x2 : nat) := (exists y0 : nat, (x0 = (Nat.add (Nat.mul x2 x1) y0)) /\ (Peano.lt y0 x1)) -> (Nat.div x0 x1) = x2.
Definition term50 (x0 : nat) := imp ((~ (x0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) x0).
Definition term64 := forall y0 : nat, (fun y1 : nat => (~ (y1 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y1) y0.
Definition term44 := (~ ((NUMERAL 0) = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) (NUMERAL 0).
Definition term31 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (exists y1 : nat, (x0 = (Nat.add (Nat.mul y0 x1) y1)) /\ (Peano.lt y1 x1)) -> (Nat.div x0 x1) = y0) x2.
Definition term59 := ((fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (~ (y1 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y1) y0) -> (fun y1 : nat => (~ (y1 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y1) (S y0)).
Definition term54 (x0 : nat) := ((~ (x0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) x0) -> (~ ((S x0) = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) (S x0).
Definition term9 (x0 : nat) := (fun y0 : nat => (Nat.add y0 (NUMERAL 0)) = y0) x0.
Definition term22 (x0 : nat) (x1 : nat) (x2 : nat) := exists y0 : nat, (x0 = (Nat.add (Nat.mul x1 x2) y0)) /\ (Peano.lt y0 x2).
Definition term65 := forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0.
Definition term41 := (((fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (~ (y1 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y1) y0) -> (fun y1 : nat => (~ (y1 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y1) (S y0))) -> forall y0 : nat, (fun y1 : nat => (~ (y1 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y1) y0.
Definition term51 (x0 : nat) := (fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) (S x0).
Definition term40 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term20 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x0 = (Nat.add (Nat.mul x1 x3) x2)) /\ (Peano.lt x2 x3).
Definition term18 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => ((x0 = (Nat.add (Nat.mul x2 x1) y0)) /\ (Peano.lt y0 x1)) -> (Nat.div x0 x1) = x2) x3.
Definition term61 := imp (((fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (~ (y1 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y1) y0) -> (fun y1 : nat => (~ (y1 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y1) (S y0))).
Definition term10 (x0 : nat) := Nat.add x0 (NUMERAL 0).
Definition term42 := fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0.
Definition term72 (x0 : nat) := (~ ((S x0) = (NUMERAL 0))) -> True.
Definition term67 := ~ ((NUMERAL 0) = (NUMERAL 0)).
Definition term30 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (exists y2 : nat, (x0 = (Nat.add (Nat.mul y1 y0) y2)) /\ (Peano.lt y2 y0)) -> (Nat.div x0 y0) = y1) x1.
Definition term33 (x0 : nat) := (exists y0 : nat, (x0 = (Nat.add (Nat.mul (NUMERAL (BIT1 0)) x0) y0)) /\ (Peano.lt y0 x0)) -> (Nat.div x0 x0) = (NUMERAL (BIT1 0)).
Definition term57 := forall y0 : nat, ((fun y1 : nat => (~ (y1 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y1) y0) -> (fun y1 : nat => (~ (y1 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y1) (S y0).
Definition term56 := fun y0 : nat => ((~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) -> (~ ((S y0) = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) (S y0).
Definition term32 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term77 := forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> (Nat.div y0 y0) = (NUMERAL (BIT1 0)).
Definition term8 := forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0.
Definition term45 := and ((fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) (NUMERAL 0)).
Definition term69 := Peano.lt (NUMERAL 0) (NUMERAL 0).
Definition term55 := fun y0 : nat => ((fun y1 : nat => (~ (y1 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y1) y0) -> (fun y1 : nat => (~ (y1 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y1) (S y0).
Definition term19 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((x1 = (Nat.add (Nat.mul x3 x2) x0)) /\ (Peano.lt x0 x2)) -> (Nat.div x1 x2) = x3.
Definition term46 := and ((~ ((NUMERAL 0) = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) (NUMERAL 0)).
Definition term17 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, ((x0 = (Nat.add (Nat.mul x2 x1) y0)) /\ (Peano.lt y0 x1)) -> (Nat.div x0 x1) = x2.
Definition term27 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (exists y3 : nat, (y0 = (Nat.add (Nat.mul y2 y1) y3)) /\ (Peano.lt y3 y1)) -> (Nat.div y0 y1) = y2.
Definition term26 (x0 : nat) := forall y0 : nat, forall y1 : nat, (exists y2 : nat, (x0 = (Nat.add (Nat.mul y1 y0) y2)) /\ (Peano.lt y2 y0)) -> (Nat.div x0 y0) = y1.
Definition term15 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, ((x0 = (Nat.add (Nat.mul y0 x1) y1)) /\ (Peano.lt y1 x1)) -> (Nat.div x0 x1) = y0.
Definition term13 (x0 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((x0 = (Nat.add (Nat.mul y1 y0) y2)) /\ (Peano.lt y2 y0)) -> (Nat.div x0 y0) = y1.
Definition term11 := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y0 = (Nat.add (Nat.mul y2 y1) y3)) /\ (Peano.lt y3 y1)) -> (Nat.div y0 y1) = y2.
Definition term47 (x0 : nat) := (fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) x0.
Definition term75 (x0 : nat) := fun y0 : nat => (x0 = (Nat.add (Nat.mul (NUMERAL (BIT1 0)) x0) y0)) /\ (Peano.lt y0 x0).
Definition term39 (x0 : nat) := True /\ (Peano.lt (NUMERAL 0) x0).
Definition term16 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => forall y1 : nat, ((x0 = (Nat.add (Nat.mul y0 x1) y1)) /\ (Peano.lt y1 x1)) -> (Nat.div x0 x1) = y0) x2.
Definition term14 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((x0 = (Nat.add (Nat.mul y1 y0) y2)) /\ (Peano.lt y2 y0)) -> (Nat.div x0 y0) = y1) x1.
Definition term4 := forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0.
Definition term5 (x0 : nat) := (fun y0 : nat => (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) x0.
Definition term21 (x0 : nat) (x1 : nat) (x2 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y0 = (Nat.add (Nat.mul y2 y1) y3)) /\ (Peano.lt y3 y1)) -> (Nat.div y0 y1) = y2) -> (Nat.div x0 x1) = x2.
Definition term66 := (((~ ((NUMERAL 0) = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (forall y0 : nat, ((~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) -> (~ ((S y0) = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) (S y0))) -> forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0.
Definition term73 (x0 : nat) := ~ ((S x0) = (NUMERAL 0)).
Definition term48 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) x0.
Definition term23 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nat => (x0 = (Nat.add (Nat.mul x1 x2) y0)) /\ (Peano.lt y0 x2).
Definition term35 (x0 : nat) := Nat.add (Nat.mul (NUMERAL (BIT1 0)) x0) (NUMERAL 0).
Definition term7 := (forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))).
Definition term25 (x0 : nat) (x1 : nat) := forall y0 : nat, (exists y1 : nat, (x0 = (Nat.add (Nat.mul y0 x1) y1)) /\ (Peano.lt y1 x1)) -> (Nat.div x0 x1) = y0.
Definition term68 := imp (~ ((NUMERAL 0) = (NUMERAL 0))).
Definition term52 (x0 : nat) := (~ ((S x0) = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) (S x0).
Definition term74 (x0 : nat) := exists y0 : nat, (x0 = (Nat.add (Nat.mul (NUMERAL (BIT1 0)) x0) y0)) /\ (Peano.lt y0 x0).
Definition term62 := imp (((~ ((NUMERAL 0) = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (forall y0 : nat, ((~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) -> (~ ((S y0) = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) (S y0))).
Definition term60 := ((~ ((NUMERAL 0) = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (forall y0 : nat, ((~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) -> (~ ((S y0) = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) (S y0)).
Definition term58 := forall y0 : nat, ((~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) -> (~ ((S y0) = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) (S y0).
Definition term49 (x0 : nat) := imp ((fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) x0).
Definition term43 := (fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) (NUMERAL 0).
Definition term2 := (forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))).
Definition term37 (x0 : nat) := Peano.lt (NUMERAL 0) x0.
Definition term34 := NUMERAL (BIT1 0).
Definition term6 (x0 : nat) := Nat.mul (NUMERAL (BIT1 0)) x0.
Definition term0 (x0 : nat) := (fun y0 : nat => Peano.lt (NUMERAL 0) (S y0)) x0.
