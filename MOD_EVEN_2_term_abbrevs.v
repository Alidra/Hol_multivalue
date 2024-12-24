Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term38 (x0 : nat) := imp (exists y0 : nat, (fun y1 : nat => x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) y0).
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.modulo y0 (Nat.mul y1 y2)) y1) = (Nat.modulo y0 y1)) x0.
Definition term65 (x0 : nat) (x1 : nat) := (x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) -> True.
Definition term10 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := forall y0 : a0, (x0 y0) -> x1.
Definition term36 (x0 : nat) := fun y0 : nat => (fun y1 : nat => x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) y0.
Definition term28 (x0 : nat) (x1 : nat) := (exists y0 : nat, x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) -> (Nat.modulo (Nat.modulo x1 x0) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.modulo x1 (NUMERAL (BIT0 (BIT1 0)))).
Definition term61 (x0 : nat) (x1 : nat) := @eq nat (Nat.modulo (Nat.modulo x0 x1) (NUMERAL (BIT0 (BIT1 0)))).
Definition term68 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term31 (x0 : nat) (x1 : nat) := (exists y0 : nat, (fun y1 : nat => x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) y0) -> (Nat.modulo (Nat.modulo x1 x0) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.modulo x1 (NUMERAL (BIT0 (BIT1 0)))).
Definition term26 (x0 : nat) (x1 : nat) := ((exists y0 : nat, x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) -> ((Nat.modulo (Nat.modulo x1 x0) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.modulo x1 (NUMERAL (BIT0 (BIT1 0))))) = ((Nat.modulo (Nat.modulo x1 x0) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.modulo x1 (NUMERAL (BIT0 (BIT1 0)))))) -> ((Coq.Arith.PeanoNat.Nat.Even x0) -> (Nat.modulo (Nat.modulo x1 x0) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.modulo x1 (NUMERAL (BIT0 (BIT1 0))))) = ((exists y0 : nat, x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) -> (Nat.modulo (Nat.modulo x1 x0) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.modulo x1 (NUMERAL (BIT0 (BIT1 0))))).
Definition term18 (x0 : nat) := Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0))).
Definition term32 (x0 : nat) (x1 : nat) := forall y0 : nat, ((fun y1 : nat => x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) y0) -> (Nat.modulo (Nat.modulo x1 x0) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.modulo x1 (NUMERAL (BIT0 (BIT1 0)))).
Definition term63 (x0 : nat) (x1 : nat) (x2 : nat) := (x1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) -> ((Nat.modulo (Nat.modulo x2 x1) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.modulo x2 (NUMERAL (BIT0 (BIT1 0))))) = True.
Definition term55 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : Prop) := ((x1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x2)) -> ((Nat.modulo (Nat.modulo x0 x1) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0))))) = x3) -> ((x1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x2)) -> (Nat.modulo (Nat.modulo x0 x1) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0))))) = ((x1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x2)) -> x3).
Definition term58 (x0 : nat) (x1 : nat) := Nat.modulo (Nat.modulo x0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)).
Definition term3 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.modulo (Nat.modulo x0 (Nat.mul x1 y0)) x1) = (Nat.modulo x0 x1).
Definition term11 (x0 : nat) := (fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even y0) = (exists y1 : nat, y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) x0.
Definition term23 (x0 : nat) (x1 : nat) (x2 : Prop) := ((Coq.Arith.PeanoNat.Nat.Even x1) = (exists y0 : nat, x1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0))) -> ((exists y0 : nat, x1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) -> ((Nat.modulo (Nat.modulo x0 x1) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0))))) = x2) -> ((Coq.Arith.PeanoNat.Nat.Even x1) -> (Nat.modulo (Nat.modulo x0 x1) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0))))) = ((exists y0 : nat, x1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) -> x2).
Definition term39 (x0 : nat) := imp (exists y0 : nat, x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)).
Definition term57 (x0 : nat) (x1 : nat) := Nat.modulo (Nat.modulo x0 x1).
Definition term50 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((x1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) = y0) -> (y0 -> ((Nat.modulo (Nat.modulo x2 x1) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.modulo x2 (NUMERAL (BIT0 (BIT1 0))))) = y1) -> ((x1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) -> (Nat.modulo (Nat.modulo x2 x1) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.modulo x2 (NUMERAL (BIT0 (BIT1 0))))) = (y0 -> y1)) x3.
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.modulo (Nat.modulo x0 (Nat.mul y0 y1)) y0) = (Nat.modulo x0 y0)) x1.
Definition term13 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term22 (x0 : nat) (x1 : nat) (x2 : Prop) (x3 : Prop) := ((Coq.Arith.PeanoNat.Nat.Even x0) = x2) -> (x2 -> ((Nat.modulo (Nat.modulo x1 x0) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.modulo x1 (NUMERAL (BIT0 (BIT1 0))))) = x3) -> ((Coq.Arith.PeanoNat.Nat.Even x0) -> (Nat.modulo (Nat.modulo x1 x0) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.modulo x1 (NUMERAL (BIT0 (BIT1 0))))) = (x2 -> x3).
Definition term5 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.modulo (Nat.modulo x0 (Nat.mul x2 x1)) x2.
Definition term35 (x0 : nat) := Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0.
Definition term8 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (fun y0 : Prop => ((exists y1 : a0, x0 y1) -> y0) = (forall y1 : a0, (x0 y1) -> y0)) x1.
Definition term53 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : Prop) (x4 : Prop) := ((x1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) = x3) -> (x3 -> ((Nat.modulo (Nat.modulo x2 x1) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.modulo x2 (NUMERAL (BIT0 (BIT1 0))))) = x4) -> ((x1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) -> (Nat.modulo (Nat.modulo x2 x1) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.modulo x2 (NUMERAL (BIT0 (BIT1 0))))) = (x3 -> x4).
Definition term71 (x0 : nat) := forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even y0) -> (Nat.modulo (Nat.modulo x0 y0) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term64 (x0 : nat) (x1 : nat) (x2 : nat) := ((x1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x2)) -> ((Nat.modulo (Nat.modulo x0 x1) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0))))) = True) -> ((x1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x2)) -> (Nat.modulo (Nat.modulo x0 x1) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0))))) = ((x1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x2)) -> True).
Definition term73 := forall y0 : nat, forall y1 : nat, (Coq.Arith.PeanoNat.Nat.Even y1) -> (Nat.modulo (Nat.modulo y0 y1) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term1 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.modulo (Nat.modulo x0 (Nat.mul y0 y1)) y0) = (Nat.modulo x0 y0).
Definition term60 (x0 : nat) (x1 : nat) := Nat.modulo (Nat.modulo x0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) (NUMERAL (BIT0 (BIT1 0))).
Definition term17 (x0 : nat) (x1 : nat) := Nat.modulo (Nat.modulo x0 x1) (NUMERAL (BIT0 (BIT1 0))).
Definition term21 (x0 : nat) (x1 : nat) (x2 : Prop) (x3 : Prop) := (fun y0 : Prop => ((Coq.Arith.PeanoNat.Nat.Even x0) = x2) -> (x2 -> ((Nat.modulo (Nat.modulo x1 x0) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.modulo x1 (NUMERAL (BIT0 (BIT1 0))))) = y0) -> ((Coq.Arith.PeanoNat.Nat.Even x0) -> (Nat.modulo (Nat.modulo x1 x0) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.modulo x1 (NUMERAL (BIT0 (BIT1 0))))) = (x2 -> y0)) x3.
Definition term67 := forall y0 : nat, True.
Definition term44 (x0 : nat) (x1 : nat) (x2 : nat) := ((fun y0 : nat => x1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) x0) -> (Nat.modulo (Nat.modulo x2 x1) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.modulo x2 (NUMERAL (BIT0 (BIT1 0)))).
Definition term29 (x0 : nat -> Prop) (x1 : Prop) := (exists y0 : nat, x0 y0) -> x1.
Definition term12 (x0 : nat) := exists y0 : nat, x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0).
Definition term42 (x0 : nat) (x1 : nat) := imp ((fun y0 : nat => x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) x1).
Definition term6 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : Prop, ((exists y2 : a0, y0 y2) -> y1) = (forall y2 : a0, (y0 y2) -> y1)) x0.
Definition term66 := fun y0 : nat => True.
Definition term30 (x0 : nat -> Prop) (x1 : Prop) := forall y0 : nat, (x0 y0) -> x1.
Definition term51 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : Prop) := forall y0 : Prop, ((x1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) = x3) -> (x3 -> ((Nat.modulo (Nat.modulo x2 x1) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.modulo x2 (NUMERAL (BIT0 (BIT1 0))))) = y0) -> ((x1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) -> (Nat.modulo (Nat.modulo x2 x1) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.modulo x2 (NUMERAL (BIT0 (BIT1 0))))) = (x3 -> y0).
Definition term20 (x0 : nat) (x1 : nat) (x2 : Prop) := forall y0 : Prop, ((Coq.Arith.PeanoNat.Nat.Even x0) = x2) -> (x2 -> ((Nat.modulo (Nat.modulo x1 x0) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.modulo x1 (NUMERAL (BIT0 (BIT1 0))))) = y0) -> ((Coq.Arith.PeanoNat.Nat.Even x0) -> (Nat.modulo (Nat.modulo x1 x0) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.modulo x1 (NUMERAL (BIT0 (BIT1 0))))) = (x2 -> y0).
Definition term14 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term4 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.modulo (Nat.modulo x0 (Nat.mul x1 y0)) x1) = (Nat.modulo x0 x1)) x2.
Definition term34 (x0 : nat) (x1 : nat) := (fun y0 : nat => x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) x1.
Definition term37 (x0 : nat) := exists y0 : nat, (fun y1 : nat => x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) y0.
Definition term49 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : Prop, forall y1 : Prop, ((x1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) = y0) -> (y0 -> ((Nat.modulo (Nat.modulo x2 x1) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.modulo x2 (NUMERAL (BIT0 (BIT1 0))))) = y1) -> ((x1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) -> (Nat.modulo (Nat.modulo x2 x1) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.modulo x2 (NUMERAL (BIT0 (BIT1 0))))) = (y0 -> y1).
Definition term16 (x0 : nat) (x1 : nat) := forall y0 : Prop, forall y1 : Prop, ((Coq.Arith.PeanoNat.Nat.Even x0) = y0) -> (y0 -> ((Nat.modulo (Nat.modulo x1 x0) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.modulo x1 (NUMERAL (BIT0 (BIT1 0))))) = y1) -> ((Coq.Arith.PeanoNat.Nat.Even x0) -> (Nat.modulo (Nat.modulo x1 x0) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.modulo x1 (NUMERAL (BIT0 (BIT1 0))))) = (y0 -> y1).
Definition term15 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term59 := NUMERAL (BIT0 (BIT1 0)).
Definition term52 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : Prop) (x4 : Prop) := (fun y0 : Prop => ((x1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) = x3) -> (x3 -> ((Nat.modulo (Nat.modulo x2 x1) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.modulo x2 (NUMERAL (BIT0 (BIT1 0))))) = y0) -> ((x1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) -> (Nat.modulo (Nat.modulo x2 x1) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.modulo x2 (NUMERAL (BIT0 (BIT1 0))))) = (x3 -> y0)) x4.
Definition term7 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : Prop, ((exists y1 : a0, x0 y1) -> y0) = (forall y1 : a0, (x0 y1) -> y0).
Definition term45 (x0 : nat) (x1 : nat) (x2 : nat) := (x1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) -> (Nat.modulo (Nat.modulo x2 x1) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.modulo x2 (NUMERAL (BIT0 (BIT1 0)))).
Definition term41 (x0 : nat) (x1 : nat) := @eq Prop ((exists y0 : nat, x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) -> (Nat.modulo (Nat.modulo x1 x0) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.modulo x1 (NUMERAL (BIT0 (BIT1 0))))).
Definition term40 (x0 : nat) (x1 : nat) := @eq Prop ((exists y0 : nat, (fun y1 : nat => x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) y0) -> (Nat.modulo (Nat.modulo x1 x0) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.modulo x1 (NUMERAL (BIT0 (BIT1 0))))).
Definition term25 (x0 : nat) (x1 : nat) := (exists y0 : nat, x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) -> ((Nat.modulo (Nat.modulo x1 x0) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.modulo x1 (NUMERAL (BIT0 (BIT1 0))))) = ((Nat.modulo (Nat.modulo x1 x0) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.modulo x1 (NUMERAL (BIT0 (BIT1 0))))).
Definition term24 (x0 : nat) (x1 : nat) (x2 : Prop) := ((exists y0 : nat, x1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) -> ((Nat.modulo (Nat.modulo x0 x1) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0))))) = x2) -> ((Coq.Arith.PeanoNat.Nat.Even x1) -> (Nat.modulo (Nat.modulo x0 x1) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0))))) = ((exists y0 : nat, x1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) -> x2).
Definition term9 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) -> x1.
Definition term43 (x0 : nat) (x1 : nat) := imp (x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)).
Definition term33 (x0 : nat) := fun y0 : nat => x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0).
Definition term56 (x0 : nat) (x1 : nat) := Nat.modulo x0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1).
Definition term62 (x0 : nat) := @eq nat (Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term54 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : Prop) := ((x1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x2)) = (x1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x2))) -> ((x1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x2)) -> ((Nat.modulo (Nat.modulo x0 x1) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0))))) = x3) -> ((x1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x2)) -> (Nat.modulo (Nat.modulo x0 x1) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0))))) = ((x1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x2)) -> x3).
Definition term47 (x0 : nat) (x1 : nat) := fun y0 : nat => (x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) -> (Nat.modulo (Nat.modulo x1 x0) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.modulo x1 (NUMERAL (BIT0 (BIT1 0)))).
Definition term70 (x0 : nat) := fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even y0) -> (Nat.modulo (Nat.modulo x0 y0) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term69 (x0 : Prop) := forall y0 : nat, x0.
Definition term48 (x0 : nat) (x1 : nat) := forall y0 : nat, (x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) -> (Nat.modulo (Nat.modulo x1 x0) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.modulo x1 (NUMERAL (BIT0 (BIT1 0)))).
Definition term19 (x0 : nat) (x1 : nat) (x2 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((Coq.Arith.PeanoNat.Nat.Even x0) = y0) -> (y0 -> ((Nat.modulo (Nat.modulo x1 x0) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.modulo x1 (NUMERAL (BIT0 (BIT1 0))))) = y1) -> ((Coq.Arith.PeanoNat.Nat.Even x0) -> (Nat.modulo (Nat.modulo x1 x0) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.modulo x1 (NUMERAL (BIT0 (BIT1 0))))) = (y0 -> y1)) x2.
Definition term46 (x0 : nat) (x1 : nat) := fun y0 : nat => ((fun y1 : nat => x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) y0) -> (Nat.modulo (Nat.modulo x1 x0) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.modulo x1 (NUMERAL (BIT0 (BIT1 0)))).
Definition term27 (x0 : nat) (x1 : nat) := (Coq.Arith.PeanoNat.Nat.Even x0) -> (Nat.modulo (Nat.modulo x1 x0) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.modulo x1 (NUMERAL (BIT0 (BIT1 0)))).
Definition term72 := fun y0 : nat => forall y1 : nat, (Coq.Arith.PeanoNat.Nat.Even y1) -> (Nat.modulo (Nat.modulo y0 y1) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))).
