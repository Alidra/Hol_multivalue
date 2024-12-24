Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term20 (x0 : nat) := (fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even (S y0)) = (~ (Coq.Arith.PeanoNat.Nat.Even y0))) x0.
Definition term30 (x0 : nat) := (fun y0 : nat => ((Coq.Arith.PeanoNat.Nat.Even y0) -> exists y1 : nat, y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) /\ ((~ (Coq.Arith.PeanoNat.Nat.Even y0)) -> exists y1 : nat, y0 = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)))) x0.
Definition term36 (x0 : nat) := ((fun y0 : nat => ((Coq.Arith.PeanoNat.Nat.Even y0) -> exists y1 : nat, y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) /\ ((~ (Coq.Arith.PeanoNat.Nat.Even y0)) -> exists y1 : nat, y0 = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)))) x0) -> (fun y0 : nat => ((Coq.Arith.PeanoNat.Nat.Even y0) -> exists y1 : nat, y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) /\ ((~ (Coq.Arith.PeanoNat.Nat.Even y0)) -> exists y1 : nat, y0 = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)))) (S x0).
Definition term48 := forall y0 : nat, ((Coq.Arith.PeanoNat.Nat.Even y0) -> exists y1 : nat, y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) /\ ((~ (Coq.Arith.PeanoNat.Nat.Even y0)) -> exists y1 : nat, y0 = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))).
Definition term54 := True -> exists y0 : nat, (NUMERAL 0) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0).
Definition term78 (x0 : nat) := ((~ (Coq.Arith.PeanoNat.Nat.Even x0)) -> exists y0 : nat, (S x0) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) /\ ((Coq.Arith.PeanoNat.Nat.Even x0) -> exists y0 : nat, (S x0) = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0))).
Definition term31 (x0 : nat) := ((Coq.Arith.PeanoNat.Nat.Even x0) -> exists y0 : nat, x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) /\ ((~ (Coq.Arith.PeanoNat.Nat.Even x0)) -> exists y0 : nat, x0 = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0))).
Definition term85 (x0 : nat) := exists y0 : nat, x0 = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)).
Definition term52 := exists y0 : nat, (NUMERAL 0) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0).
Definition term81 := @eq nat (NUMERAL 0).
Definition term66 (x0 : nat) := (Coq.Arith.PeanoNat.Nat.Even (S x0)) -> exists y0 : nat, (S x0) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0).
Definition term72 (x0 : Prop) := ~ (~ x0).
Definition term1 := (forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))).
Definition term22 (x0 : nat) := ~ (Coq.Arith.PeanoNat.Nat.Even x0).
Definition term47 := forall y0 : nat, (fun y1 : nat => ((Coq.Arith.PeanoNat.Nat.Even y1) -> exists y2 : nat, y1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y2)) /\ ((~ (Coq.Arith.PeanoNat.Nat.Even y1)) -> exists y2 : nat, y1 = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y2)))) y0.
Definition term50 := Coq.Arith.PeanoNat.Nat.Even (NUMERAL 0).
Definition term42 := ((fun y0 : nat => ((Coq.Arith.PeanoNat.Nat.Even y0) -> exists y1 : nat, y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) /\ ((~ (Coq.Arith.PeanoNat.Nat.Even y0)) -> exists y1 : nat, y0 = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Coq.Arith.PeanoNat.Nat.Even y1) -> exists y2 : nat, y1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y2)) /\ ((~ (Coq.Arith.PeanoNat.Nat.Even y1)) -> exists y2 : nat, y1 = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y2)))) y0) -> (fun y1 : nat => ((Coq.Arith.PeanoNat.Nat.Even y1) -> exists y2 : nat, y1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y2)) /\ ((~ (Coq.Arith.PeanoNat.Nat.Even y1)) -> exists y2 : nat, y1 = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y2)))) (S y0)).
Definition term33 (x0 : nat) := imp (((Coq.Arith.PeanoNat.Nat.Even x0) -> exists y0 : nat, x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) /\ ((~ (Coq.Arith.PeanoNat.Nat.Even x0)) -> exists y0 : nat, x0 = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)))).
Definition term55 := and ((Coq.Arith.PeanoNat.Nat.Even (NUMERAL 0)) -> exists y0 : nat, (NUMERAL 0) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)).
Definition term71 (x0 : nat) := ~ (~ (Coq.Arith.PeanoNat.Nat.Even x0)).
Definition term70 (x0 : nat) := ~ (Coq.Arith.PeanoNat.Nat.Even (S x0)).
Definition term73 (x0 : nat) := imp (~ (Coq.Arith.PeanoNat.Nat.Even (S x0))).
Definition term24 := (((fun y0 : nat => ((Coq.Arith.PeanoNat.Nat.Even y0) -> exists y1 : nat, y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) /\ ((~ (Coq.Arith.PeanoNat.Nat.Even y0)) -> exists y1 : nat, y0 = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Coq.Arith.PeanoNat.Nat.Even y1) -> exists y2 : nat, y1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y2)) /\ ((~ (Coq.Arith.PeanoNat.Nat.Even y1)) -> exists y2 : nat, y1 = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y2)))) y0) -> (fun y1 : nat => ((Coq.Arith.PeanoNat.Nat.Even y1) -> exists y2 : nat, y1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y2)) /\ ((~ (Coq.Arith.PeanoNat.Nat.Even y1)) -> exists y2 : nat, y1 = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y2)))) (S y0))) -> forall y0 : nat, (fun y1 : nat => ((Coq.Arith.PeanoNat.Nat.Even y1) -> exists y2 : nat, y1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y2)) /\ ((~ (Coq.Arith.PeanoNat.Nat.Even y1)) -> exists y2 : nat, y1 = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y2)))) y0.
Definition term79 := Nat.mul (NUMERAL (BIT0 (BIT1 0))) (NUMERAL 0).
Definition term23 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term10 (x0 : nat) := forall y0 : nat, (Nat.add (S x0) y0) = (S (Nat.add x0 y0)).
Definition term74 (x0 : nat) := imp (Coq.Arith.PeanoNat.Nat.Even x0).
Definition term97 (x0 : nat) := Nat.add x0 (S x0).
Definition term44 := imp (((fun y0 : nat => ((Coq.Arith.PeanoNat.Nat.Even y0) -> exists y1 : nat, y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) /\ ((~ (Coq.Arith.PeanoNat.Nat.Even y0)) -> exists y1 : nat, y0 = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Coq.Arith.PeanoNat.Nat.Even y1) -> exists y2 : nat, y1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y2)) /\ ((~ (Coq.Arith.PeanoNat.Nat.Even y1)) -> exists y2 : nat, y1 = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y2)))) y0) -> (fun y1 : nat => ((Coq.Arith.PeanoNat.Nat.Even y1) -> exists y2 : nat, y1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y2)) /\ ((~ (Coq.Arith.PeanoNat.Nat.Even y1)) -> exists y2 : nat, y1 = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y2)))) (S y0))).
Definition term58 := imp (~ (Coq.Arith.PeanoNat.Nat.Even (NUMERAL 0))).
Definition term25 := fun y0 : nat => ((Coq.Arith.PeanoNat.Nat.Even y0) -> exists y1 : nat, y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) /\ ((~ (Coq.Arith.PeanoNat.Nat.Even y0)) -> exists y1 : nat, y0 = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))).
Definition term40 := forall y0 : nat, ((fun y1 : nat => ((Coq.Arith.PeanoNat.Nat.Even y1) -> exists y2 : nat, y1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y2)) /\ ((~ (Coq.Arith.PeanoNat.Nat.Even y1)) -> exists y2 : nat, y1 = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y2)))) y0) -> (fun y1 : nat => ((Coq.Arith.PeanoNat.Nat.Even y1) -> exists y2 : nat, y1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y2)) /\ ((~ (Coq.Arith.PeanoNat.Nat.Even y1)) -> exists y2 : nat, y1 = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y2)))) (S y0).
Definition term94 (x0 : nat) := @eq nat (S (S (Nat.add x0 x0))).
Definition term92 (x0 : nat) := S (Nat.add x0 x0).
Definition term29 := and (((Coq.Arith.PeanoNat.Nat.Even (NUMERAL 0)) -> exists y0 : nat, (NUMERAL 0) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) /\ ((~ (Coq.Arith.PeanoNat.Nat.Even (NUMERAL 0))) -> exists y0 : nat, (NUMERAL 0) = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)))).
Definition term76 (x0 : nat) := (~ (Coq.Arith.PeanoNat.Nat.Even (S x0))) -> exists y0 : nat, (S x0) = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)).
Definition term87 (x0 : nat) := S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0).
Definition term83 (x0 : nat) := (~ (Coq.Arith.PeanoNat.Nat.Even x0)) -> exists y0 : nat, x0 = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)).
Definition term67 (x0 : nat) := (~ (Coq.Arith.PeanoNat.Nat.Even x0)) -> exists y0 : nat, (S x0) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0).
Definition term59 := exists y0 : nat, (NUMERAL 0) = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)).
Definition term28 := and ((fun y0 : nat => ((Coq.Arith.PeanoNat.Nat.Even y0) -> exists y1 : nat, y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) /\ ((~ (Coq.Arith.PeanoNat.Nat.Even y0)) -> exists y1 : nat, y0 = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)))) (NUMERAL 0)).
Definition term19 := forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even (S y0)) = (~ (Coq.Arith.PeanoNat.Nat.Even y0)).
Definition term14 (x0 : nat) := Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0.
Definition term17 (x0 : nat) := (fun y0 : nat => (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) x0.
Definition term35 (x0 : nat) := ((Coq.Arith.PeanoNat.Nat.Even (S x0)) -> exists y0 : nat, (S x0) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) /\ ((~ (Coq.Arith.PeanoNat.Nat.Even (S x0))) -> exists y0 : nat, (S x0) = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0))).
Definition term27 := ((Coq.Arith.PeanoNat.Nat.Even (NUMERAL 0)) -> exists y0 : nat, (NUMERAL 0) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) /\ ((~ (Coq.Arith.PeanoNat.Nat.Even (NUMERAL 0))) -> exists y0 : nat, (NUMERAL 0) = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0))).
Definition term11 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add (S x0) y0) = (S (Nat.add x0 y0))) x1.
Definition term95 (x0 : nat) := Nat.add (S x0) (S x0).
Definition term38 := fun y0 : nat => ((fun y1 : nat => ((Coq.Arith.PeanoNat.Nat.Even y1) -> exists y2 : nat, y1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y2)) /\ ((~ (Coq.Arith.PeanoNat.Nat.Even y1)) -> exists y2 : nat, y1 = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y2)))) y0) -> (fun y1 : nat => ((Coq.Arith.PeanoNat.Nat.Even y1) -> exists y2 : nat, y1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y2)) /\ ((~ (Coq.Arith.PeanoNat.Nat.Even y1)) -> exists y2 : nat, y1 = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y2)))) (S y0).
Definition term13 (x0 : nat) := (fun y0 : nat => (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (Nat.add y0 y0)) x0.
Definition term7 (x0 : nat) (x1 : nat) := S (Nat.add x0 x1).
Definition term82 := fun y0 : nat => (NUMERAL 0) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0).
Definition term21 (x0 : nat) := Coq.Arith.PeanoNat.Nat.Even (S x0).
Definition term8 := forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1)).
Definition term2 := forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)).
Definition term26 := (fun y0 : nat => ((Coq.Arith.PeanoNat.Nat.Even y0) -> exists y1 : nat, y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) /\ ((~ (Coq.Arith.PeanoNat.Nat.Even y0)) -> exists y1 : nat, y0 = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)))) (NUMERAL 0).
Definition term49 := ((((Coq.Arith.PeanoNat.Nat.Even (NUMERAL 0)) -> exists y0 : nat, (NUMERAL 0) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) /\ ((~ (Coq.Arith.PeanoNat.Nat.Even (NUMERAL 0))) -> exists y0 : nat, (NUMERAL 0) = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)))) /\ (forall y0 : nat, (((Coq.Arith.PeanoNat.Nat.Even y0) -> exists y1 : nat, y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) /\ ((~ (Coq.Arith.PeanoNat.Nat.Even y0)) -> exists y1 : nat, y0 = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)))) -> ((Coq.Arith.PeanoNat.Nat.Even (S y0)) -> exists y1 : nat, (S y0) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) /\ ((~ (Coq.Arith.PeanoNat.Nat.Even (S y0))) -> exists y1 : nat, (S y0) = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))))) -> forall y0 : nat, ((Coq.Arith.PeanoNat.Nat.Even y0) -> exists y1 : nat, y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) /\ ((~ (Coq.Arith.PeanoNat.Nat.Even y0)) -> exists y1 : nat, y0 = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))).
Definition term84 (x0 : nat) := (Coq.Arith.PeanoNat.Nat.Even x0) -> exists y0 : nat, x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0).
Definition term77 (x0 : nat) := (Coq.Arith.PeanoNat.Nat.Even x0) -> exists y0 : nat, (S x0) = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)).
Definition term43 := (((Coq.Arith.PeanoNat.Nat.Even (NUMERAL 0)) -> exists y0 : nat, (NUMERAL 0) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) /\ ((~ (Coq.Arith.PeanoNat.Nat.Even (NUMERAL 0))) -> exists y0 : nat, (NUMERAL 0) = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)))) /\ (forall y0 : nat, (((Coq.Arith.PeanoNat.Nat.Even y0) -> exists y1 : nat, y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) /\ ((~ (Coq.Arith.PeanoNat.Nat.Even y0)) -> exists y1 : nat, y0 = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)))) -> ((Coq.Arith.PeanoNat.Nat.Even (S y0)) -> exists y1 : nat, (S y0) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) /\ ((~ (Coq.Arith.PeanoNat.Nat.Even (S y0))) -> exists y1 : nat, (S y0) = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)))).
Definition term86 (x0 : nat) := exists y0 : nat, x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0).
Definition term100 (x0 : nat) := fun y0 : nat => (S x0) = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)).
Definition term51 := imp (Coq.Arith.PeanoNat.Nat.Even (NUMERAL 0)).
Definition term90 (x0 : nat) := @eq nat (S (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0))).
Definition term65 (x0 : nat) := exists y0 : nat, (S x0) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0).
Definition term61 := False -> exists y0 : nat, (NUMERAL 0) = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)).
Definition term5 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add x0 (S y0)) = (S (Nat.add x0 y0))) x1.
Definition term75 (x0 : nat) := exists y0 : nat, (S x0) = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)).
Definition term0 := (forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))).
Definition term80 := NUMERAL (BIT0 (BIT1 0)).
Definition term53 := (Coq.Arith.PeanoNat.Nat.Even (NUMERAL 0)) -> exists y0 : nat, (NUMERAL 0) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0).
Definition term99 (x0 : nat) := @eq nat (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)).
Definition term89 (x0 : nat) := @eq nat (S x0).
Definition term98 (x0 : nat) := fun y0 : nat => (S x0) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0).
Definition term62 := (exists y0 : nat, (NUMERAL 0) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) /\ True.
Definition term9 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) x0.
Definition term3 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))) x0.
Definition term16 := forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0).
Definition term56 := and (exists y0 : nat, (NUMERAL 0) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)).
Definition term91 (x0 : nat) := Nat.mul (NUMERAL (BIT0 (BIT1 0))) (S x0).
Definition term64 (x0 : nat) := imp (~ (Coq.Arith.PeanoNat.Nat.Even x0)).
Definition term18 (x0 : nat) := Nat.mul x0 (NUMERAL 0).
Definition term6 (x0 : nat) (x1 : nat) := Nat.add x0 (S x1).
Definition term101 (x0 : nat) := fun y0 : nat => x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0).
Definition term102 (x0 : nat) := fun y0 : nat => x0 = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)).
Definition term46 := fun y0 : nat => (fun y1 : nat => ((Coq.Arith.PeanoNat.Nat.Even y1) -> exists y2 : nat, y1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y2)) /\ ((~ (Coq.Arith.PeanoNat.Nat.Even y1)) -> exists y2 : nat, y1 = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y2)))) y0.
Definition term57 := ~ (Coq.Arith.PeanoNat.Nat.Even (NUMERAL 0)).
Definition term45 := imp ((((Coq.Arith.PeanoNat.Nat.Even (NUMERAL 0)) -> exists y0 : nat, (NUMERAL 0) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) /\ ((~ (Coq.Arith.PeanoNat.Nat.Even (NUMERAL 0))) -> exists y0 : nat, (NUMERAL 0) = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)))) /\ (forall y0 : nat, (((Coq.Arith.PeanoNat.Nat.Even y0) -> exists y1 : nat, y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) /\ ((~ (Coq.Arith.PeanoNat.Nat.Even y0)) -> exists y1 : nat, y0 = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)))) -> ((Coq.Arith.PeanoNat.Nat.Even (S y0)) -> exists y1 : nat, (S y0) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) /\ ((~ (Coq.Arith.PeanoNat.Nat.Even (S y0))) -> exists y1 : nat, (S y0) = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))))).
Definition term63 (x0 : nat) := imp (Coq.Arith.PeanoNat.Nat.Even (S x0)).
Definition term69 (x0 : nat) := and ((~ (Coq.Arith.PeanoNat.Nat.Even x0)) -> exists y0 : nat, (S x0) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)).
Definition term37 (x0 : nat) := (((Coq.Arith.PeanoNat.Nat.Even x0) -> exists y0 : nat, x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) /\ ((~ (Coq.Arith.PeanoNat.Nat.Even x0)) -> exists y0 : nat, x0 = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)))) -> ((Coq.Arith.PeanoNat.Nat.Even (S x0)) -> exists y0 : nat, (S x0) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) /\ ((~ (Coq.Arith.PeanoNat.Nat.Even (S x0))) -> exists y0 : nat, (S x0) = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0))).
Definition term68 (x0 : nat) := and ((Coq.Arith.PeanoNat.Nat.Even (S x0)) -> exists y0 : nat, (S x0) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)).
Definition term34 (x0 : nat) := (fun y0 : nat => ((Coq.Arith.PeanoNat.Nat.Even y0) -> exists y1 : nat, y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) /\ ((~ (Coq.Arith.PeanoNat.Nat.Even y0)) -> exists y1 : nat, y0 = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)))) (S x0).
Definition term41 := forall y0 : nat, (((Coq.Arith.PeanoNat.Nat.Even y0) -> exists y1 : nat, y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) /\ ((~ (Coq.Arith.PeanoNat.Nat.Even y0)) -> exists y1 : nat, y0 = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)))) -> ((Coq.Arith.PeanoNat.Nat.Even (S y0)) -> exists y1 : nat, (S y0) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) /\ ((~ (Coq.Arith.PeanoNat.Nat.Even (S y0))) -> exists y1 : nat, (S y0) = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))).
Definition term96 (x0 : nat) := S (Nat.add x0 (S x0)).
Definition term39 := fun y0 : nat => (((Coq.Arith.PeanoNat.Nat.Even y0) -> exists y1 : nat, y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) /\ ((~ (Coq.Arith.PeanoNat.Nat.Even y0)) -> exists y1 : nat, y0 = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)))) -> ((Coq.Arith.PeanoNat.Nat.Even (S y0)) -> exists y1 : nat, (S y0) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) /\ ((~ (Coq.Arith.PeanoNat.Nat.Even (S y0))) -> exists y1 : nat, (S y0) = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))).
Definition term32 (x0 : nat) := imp ((fun y0 : nat => ((Coq.Arith.PeanoNat.Nat.Even y0) -> exists y1 : nat, y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) /\ ((~ (Coq.Arith.PeanoNat.Nat.Even y0)) -> exists y1 : nat, y0 = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)))) x0).
Definition term15 := (forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))).
Definition term60 := (~ (Coq.Arith.PeanoNat.Nat.Even (NUMERAL 0))) -> exists y0 : nat, (NUMERAL 0) = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)).
Definition term12 (x0 : nat) (x1 : nat) := Nat.add (S x0) x1.
Definition term93 (x0 : nat) := S (S (Nat.add x0 x0)).
Definition term88 (x0 : nat) := S (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)).
Definition term4 (x0 : nat) := forall y0 : nat, (Nat.add x0 (S y0)) = (S (Nat.add x0 y0)).
