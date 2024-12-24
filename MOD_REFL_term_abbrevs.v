Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term83 (x0 : nat) (x1 : nat) := ~ (x0 = x1).
Definition term65 (x0 : nat -> Prop) := ~ (all x0).
Definition term112 := (~ False) -> False.
Definition term54 (x0 : nat) := fun y0 : nat => x0 = (Nat.mul y0 x0).
Definition term91 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((~ (x0 = x1)) \/ (~ (x0 = x2)))) -> x1 = x2.
Definition term72 := exists y0 : nat, forall y1 : nat, ~ (y0 = (Nat.mul y1 y0)).
Definition term44 := (forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))))).
Definition term52 := forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0).
Definition term7 := forall y0 : nat, (Nat.modulo y0 y0) = (NUMERAL 0).
Definition term97 (x0 : Prop) := ~ (~ x0).
Definition term8 := forall y0 : nat, exists y1 : nat, y0 = (Nat.mul y1 y0).
Definition term79 (x0 : nat) := (~ ((Nat.mul (NUMERAL (BIT1 0)) x0) = (Nat.mul (NUMERAL (BIT1 0)) x0))) -> (Nat.mul (NUMERAL (BIT1 0)) x0) = (Nat.mul (NUMERAL (BIT1 0)) x0).
Definition term18 := (forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))))))).
Definition term5 := fun y0 : nat => (Nat.modulo y0 y0) = (NUMERAL 0).
Definition term96 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (~ (x1 = x0))) /\ (~ (~ (x1 = x2))).
Definition term77 (x0 : nat) := ~ ((Nat.mul (NUMERAL (BIT1 0)) x0) = x0).
Definition term17 := ~ ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))))).
Definition term24 (x0 : nat) := forall y0 : nat, (Nat.mul x0 (S y0)) = (Nat.add x0 (Nat.mul x0 y0)).
Definition term9 (x0 : Prop) := (~ x0) -> False.
Definition term34 := (forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))).
Definition term102 (x0 : nat) (x1 : nat) (x2 : nat) := imp (~ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term41 := fun y0 : nat => (Nat.mul (NUMERAL (BIT1 0)) y0) = y0.
Definition term12 := (~ (forall y0 : nat, exists y1 : nat, y0 = (Nat.mul y1 y0))) -> ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))))) -> False.
Definition term110 (x0 : nat) := (x0 = (Nat.mul (NUMERAL (BIT1 0)) x0)) -> False.
Definition term90 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term100 (x0 : nat) (x1 : nat) := and (x0 = x1).
Definition term11 := ~ (forall y0 : nat, exists y1 : nat, y0 = (Nat.mul y1 y0)).
Definition term78 (x0 : Prop) := (~ x0) -> x0.
Definition term101 (x0 : nat) (x1 : nat) (x2 : nat) := (x1 = x0) /\ (x1 = x2).
Definition term92 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x1 = x0)) \/ (~ (x1 = x2)).
Definition term94 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term88 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2))).
Definition term68 (x0 : nat) := (fun y0 : nat => exists y1 : nat, y0 = (Nat.mul y1 y0)) x0.
Definition term89 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term36 := fun y0 : nat => (Nat.mul y0 (NUMERAL (BIT1 0))) = y0.
Definition term86 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term27 (x0 : nat) (x1 : nat) := Nat.mul (S x0) x1.
Definition term109 (x0 : nat) (x1 : nat) := (x1 = (Nat.mul x0 x1)) -> False.
Definition term31 := fun y0 : nat => forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1).
Definition term21 (x0 : nat) (x1 : nat) := Nat.mul x0 (S x1).
Definition term80 (x0 : nat) := ~ ((Nat.mul (NUMERAL (BIT1 0)) x0) = (Nat.mul (NUMERAL (BIT1 0)) x0)).
Definition term37 := forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0.
Definition term75 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2)).
Definition term87 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term4 (x0 : nat) := exists y0 : nat, x0 = (Nat.mul y0 x0).
Definition term53 := and (forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)).
Definition term48 := and (forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)).
Definition term20 := (~ (forall y0 : nat, exists y1 : nat, y0 = (Nat.mul y1 y0))) -> ~ ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))))).
Definition term73 (x0 : nat) (x1 : nat) := (fun y0 : nat => ~ (x0 = (Nat.mul y0 x0))) x1.
Definition term43 := and (forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0).
Definition term38 := and (forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0).
Definition term93 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term32 := forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1).
Definition term26 := forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)).
Definition term55 (x0 : nat -> Prop) := ~ (ex x0).
Definition term63 (x0 : nat) := fun y0 : nat => ~ (x0 = (Nat.mul y0 x0)).
Definition term107 (x0 : nat) := (~ (x0 = (Nat.mul (NUMERAL (BIT1 0)) x0))) -> x0 = (Nat.mul (NUMERAL (BIT1 0)) x0).
Definition term105 (x0 : nat) := ((Nat.mul (NUMERAL (BIT1 0)) x0) = x0) /\ ((Nat.mul (NUMERAL (BIT1 0)) x0) = (Nat.mul (NUMERAL (BIT1 0)) x0)).
Definition term56 (x0 : nat -> Prop) := forall y0 : nat, ~ (x0 y0).
Definition term42 := forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0.
Definition term74 (x0 : nat) := (fun y0 : nat => (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) x0.
Definition term82 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = x2) \/ (~ (x1 = x2)).
Definition term30 (x0 : nat) := forall y0 : nat, (Nat.mul (S x0) y0) = (Nat.add (Nat.mul x0 y0) y0).
Definition term10 := (~ (forall y0 : nat, exists y1 : nat, y0 = (Nat.mul y1 y0))) -> False.
Definition term70 := fun y0 : nat => ~ ((fun y1 : nat => exists y2 : nat, y1 = (Nat.mul y2 y1)) y0).
Definition term3 (x0 : nat) (x1 : nat) := exists y0 : nat, x0 = (Nat.mul y0 x1).
Definition term85 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x1 = x0)) \/ ((x0 = x2) \/ (~ (x1 = x2))).
Definition term46 := fun y0 : nat => (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0).
Definition term99 (x0 : nat) (x1 : nat) := and (~ (~ (x0 = x1))).
Definition term39 := (forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))).
Definition term64 (x0 : nat) := forall y0 : nat, ~ (x0 = (Nat.mul y0 x0)).
Definition term29 (x0 : nat) := fun y0 : nat => (Nat.mul (S x0) y0) = (Nat.add (Nat.mul x0 y0) y0).
Definition term108 (x0 : nat) := ~ (x0 = (Nat.mul (NUMERAL (BIT1 0)) x0)).
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Nat.modulo x0 y0) = (NUMERAL 0)) = (exists y1 : nat, x0 = (Nat.mul y1 y0))) x1.
Definition term33 := and (forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)).
Definition term69 (x0 : nat) := ~ ((fun y0 : nat => exists y1 : nat, y0 = (Nat.mul y1 y0)) x0).
Definition term16 := ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))))) -> False.
Definition term35 (x0 : nat) := Nat.mul x0 (NUMERAL (BIT1 0)).
Definition term58 (x0 : nat) := forall y0 : nat, ~ ((fun y1 : nat => x0 = (Nat.mul y1 x0)) y0).
Definition term76 (x0 : nat) := (~ ((Nat.mul (NUMERAL (BIT1 0)) x0) = x0)) -> (Nat.mul (NUMERAL (BIT1 0)) x0) = x0.
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.modulo y0 y1) = (NUMERAL 0)) = (exists y2 : nat, y0 = (Nat.mul y2 y1))) x0.
Definition term47 := forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0).
Definition term59 (x0 : nat) (x1 : nat) := (fun y0 : nat => x0 = (Nat.mul y0 x0)) x1.
Definition term28 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x0 x1) x1.
Definition term106 (x0 : nat) := (((Nat.mul (NUMERAL (BIT1 0)) x0) = x0) /\ ((Nat.mul (NUMERAL (BIT1 0)) x0) = (Nat.mul (NUMERAL (BIT1 0)) x0))) -> x0 = (Nat.mul (NUMERAL (BIT1 0)) x0).
Definition term22 (x0 : nat) (x1 : nat) := Nat.add x0 (Nat.mul x0 x1).
Definition term61 (x0 : nat) (x1 : nat) := ~ (x1 = (Nat.mul x0 x1)).
Definition term45 (x0 : nat) := Nat.mul x0 (NUMERAL 0).
Definition term95 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term67 := exists y0 : nat, ~ ((fun y1 : nat => exists y2 : nat, y1 = (Nat.mul y2 y1)) y0).
Definition term71 := fun y0 : nat => forall y1 : nat, ~ (y0 = (Nat.mul y1 y0)).
Definition term6 := fun y0 : nat => exists y1 : nat, y0 = (Nat.mul y1 y0).
Definition term1 (x0 : nat) := forall y0 : nat, ((Nat.modulo x0 y0) = (NUMERAL 0)) = (exists y1 : nat, x0 = (Nat.mul y1 y0)).
Definition term103 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((x1 = x0) /\ (x1 = x2)).
Definition term14 := (((~ (forall y0 : nat, exists y1 : nat, y0 = (Nat.mul y1 y0))) -> ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))))) -> False) -> (~ (forall y0 : nat, exists y1 : nat, y0 = (Nat.mul y1 y0))) -> ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))))) -> False) -> (~ (forall y0 : nat, exists y1 : nat, y0 = (Nat.mul y1 y0))) -> ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))))) -> False.
Definition term50 (x0 : nat) := Nat.mul (NUMERAL 0) x0.
Definition term62 (x0 : nat) := fun y0 : nat => ~ ((fun y1 : nat => x0 = (Nat.mul y1 x0)) y0).
Definition term60 (x0 : nat) (x1 : nat) := ~ ((fun y0 : nat => x0 = (Nat.mul y0 x0)) x1).
Definition term81 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = x2)) \/ (x1 = x2).
Definition term23 (x0 : nat) := fun y0 : nat => (Nat.mul x0 (S y0)) = (Nat.add x0 (Nat.mul x0 y0)).
Definition term98 (x0 : nat) (x1 : nat) := ~ (~ (x0 = x1)).
Definition term15 := (((~ (forall y0 : nat, exists y1 : nat, y0 = (Nat.mul y1 y0))) -> ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))))) -> False) -> (~ (forall y0 : nat, exists y1 : nat, y0 = (Nat.mul y1 y0))) -> ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))))) -> False) -> ((~ (forall y0 : nat, exists y1 : nat, y0 = (Nat.mul y1 y0))) -> ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))))) -> False) -> (~ (forall y0 : nat, exists y1 : nat, y0 = (Nat.mul y1 y0))) -> ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))))) -> False.
Definition term84 (x0 : nat) (x1 : nat) := or (~ (x0 = x1)).
Definition term49 := (forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))).
Definition term104 (x0 : nat) (x1 : nat) (x2 : nat) := ((x0 = x1) /\ (x0 = x2)) -> x1 = x2.
Definition term66 (x0 : nat -> Prop) := exists y0 : nat, ~ (x0 y0).
Definition term57 (x0 : nat) := ~ (exists y0 : nat, x0 = (Nat.mul y0 x0)).
Definition term25 := fun y0 : nat => forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)).
Definition term111 := NUMERAL (BIT1 0).
Definition term40 (x0 : nat) := Nat.mul (NUMERAL (BIT1 0)) x0.
Definition term19 := imp (~ (forall y0 : nat, exists y1 : nat, y0 = (Nat.mul y1 y0))).
Definition term51 := fun y0 : nat => (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0).
Definition term13 := ((~ (forall y0 : nat, exists y1 : nat, y0 = (Nat.mul y1 y0))) -> ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))))) -> False) -> (~ (forall y0 : nat, exists y1 : nat, y0 = (Nat.mul y1 y0))) -> ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))))) -> False.
