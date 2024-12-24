Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term7 (x0 : nat) := forall y0 : nat, (Peano.le x0 y0) -> (dotdot x0 y0) = (@INSERT nat y0 (dotdot x0 (Nat.sub y0 (NUMERAL (BIT1 0))))).
Definition term39 (x0 : nat) := fun y0 : nat => (Peano.le x0 (S y0)) -> (dotdot x0 (S y0)) = (@INSERT nat (S y0) (dotdot x0 y0)).
Definition term4 (x0 : nat) := fun y0 : nat => (Peano.le x0 y0) -> (@INSERT nat y0 (dotdot x0 (Nat.sub y0 (NUMERAL (BIT1 0))))) = (dotdot x0 y0).
Definition term43 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term15 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le x0 y0) -> (dotdot x0 y0) = (@INSERT nat y0 (dotdot x0 (Nat.sub y0 (NUMERAL (BIT1 0)))))) x1.
Definition term3 (x0 : nat) (x1 : nat) := (Peano.le x0 x1) -> (dotdot x0 x1) = (@INSERT nat x1 (dotdot x0 (Nat.sub x1 (NUMERAL (BIT1 0))))).
Definition term22 (x0 : nat) (x1 : nat) := @INSERT nat (S x1) (dotdot x0 x1).
Definition term12 (x0 : nat) := (fun y0 : nat => (Nat.sub (S y0) (NUMERAL (BIT1 0))) = y0) x0.
Definition term1 (x0 : nat) (x1 : nat) := imp (Peano.le x0 x1).
Definition term13 (x0 : nat) := Nat.sub (S x0) (NUMERAL (BIT1 0)).
Definition term21 (x0 : nat) (x1 : nat) := dotdot x0 (S x1).
Definition term2 (x0 : nat) (x1 : nat) := (Peano.le x0 x1) -> (@INSERT nat x1 (dotdot x0 (Nat.sub x1 (NUMERAL (BIT1 0))))) = (dotdot x0 x1).
Definition term27 (x0 : nat) (x1 : nat) (x2 : Prop) := ((Peano.le x0 (S x1)) = (Peano.le x0 (S x1))) -> ((Peano.le x0 (S x1)) -> ((dotdot x0 (S x1)) = (@INSERT nat (S x1) (dotdot x0 x1))) = x2) -> ((Peano.le x0 (S x1)) -> (dotdot x0 (S x1)) = (@INSERT nat (S x1) (dotdot x0 x1))) = ((Peano.le x0 (S x1)) -> x2).
Definition term16 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term34 (x0 : nat) (x1 : nat) := @eq (nat -> Prop) (@INSERT nat (S x1) (dotdot x0 x1)).
Definition term6 (x0 : nat) := forall y0 : nat, (Peano.le x0 y0) -> (@INSERT nat y0 (dotdot x0 (Nat.sub y0 (NUMERAL (BIT1 0))))) = (dotdot x0 y0).
Definition term30 (x0 : nat) (x1 : nat) := @INSERT nat (S x1) (dotdot x0 (Nat.sub (S x1) (NUMERAL (BIT1 0)))).
Definition term29 (x0 : nat) (x1 : nat) := (Peano.le x0 (S x1)) -> (dotdot x0 (S x1)) = (@INSERT nat (S x1) (dotdot x0 (Nat.sub (S x1) (NUMERAL (BIT1 0))))).
Definition term32 (x0 : nat) := @INSERT nat (S x0).
Definition term36 (x0 : nat) (x1 : nat) := ((Peano.le x0 (S x1)) -> ((dotdot x0 (S x1)) = (@INSERT nat (S x1) (dotdot x0 x1))) = True) -> ((Peano.le x0 (S x1)) -> (dotdot x0 (S x1)) = (@INSERT nat (S x1) (dotdot x0 x1))) = ((Peano.le x0 (S x1)) -> True).
Definition term35 (x0 : nat) (x1 : nat) := (Peano.le x0 (S x1)) -> ((dotdot x0 (S x1)) = (@INSERT nat (S x1) (dotdot x0 x1))) = True.
Definition term46 := forall y0 : nat, forall y1 : nat, (Peano.le y0 (S y1)) -> (dotdot y0 (S y1)) = (@INSERT nat (S y1) (dotdot y0 y1)).
Definition term11 := forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> (dotdot y0 y1) = (@INSERT nat y1 (dotdot y0 (Nat.sub y1 (NUMERAL (BIT1 0))))).
Definition term10 := forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> (@INSERT nat y1 (dotdot y0 (Nat.sub y1 (NUMERAL (BIT1 0))))) = (dotdot y0 y1).
Definition term25 (x0 : nat) (x1 : nat) (x2 : Prop) (x3 : Prop) := (fun y0 : Prop => ((Peano.le x0 (S x1)) = x2) -> (x2 -> ((dotdot x0 (S x1)) = (@INSERT nat (S x1) (dotdot x0 x1))) = y0) -> ((Peano.le x0 (S x1)) -> (dotdot x0 (S x1)) = (@INSERT nat (S x1) (dotdot x0 x1))) = (x2 -> y0)) x3.
Definition term42 := forall y0 : nat, True.
Definition term38 (x0 : nat) (x1 : nat) := (Peano.le x0 (S x1)) -> True.
Definition term40 := fun y0 : nat => True.
Definition term24 (x0 : nat) (x1 : nat) (x2 : Prop) := forall y0 : Prop, ((Peano.le x0 (S x1)) = x2) -> (x2 -> ((dotdot x0 (S x1)) = (@INSERT nat (S x1) (dotdot x0 x1))) = y0) -> ((Peano.le x0 (S x1)) -> (dotdot x0 (S x1)) = (@INSERT nat (S x1) (dotdot x0 x1))) = (x2 -> y0).
Definition term17 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term31 (x0 : nat) (x1 : nat) := dotdot x0 (Nat.sub (S x1) (NUMERAL (BIT1 0))).
Definition term19 (x0 : nat) (x1 : nat) := forall y0 : Prop, forall y1 : Prop, ((Peano.le x0 (S x1)) = y0) -> (y0 -> ((dotdot x0 (S x1)) = (@INSERT nat (S x1) (dotdot x0 x1))) = y1) -> ((Peano.le x0 (S x1)) -> (dotdot x0 (S x1)) = (@INSERT nat (S x1) (dotdot x0 x1))) = (y0 -> y1).
Definition term18 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term28 (x0 : nat) (x1 : nat) (x2 : Prop) := ((Peano.le x0 (S x1)) -> ((dotdot x0 (S x1)) = (@INSERT nat (S x1) (dotdot x0 x1))) = x2) -> ((Peano.le x0 (S x1)) -> (dotdot x0 (S x1)) = (@INSERT nat (S x1) (dotdot x0 x1))) = ((Peano.le x0 (S x1)) -> x2).
Definition term14 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) -> (dotdot y0 y1) = (@INSERT nat y1 (dotdot y0 (Nat.sub y1 (NUMERAL (BIT1 0)))))) x0.
Definition term26 (x0 : nat) (x1 : nat) (x2 : Prop) (x3 : Prop) := ((Peano.le x0 (S x1)) = x2) -> (x2 -> ((dotdot x0 (S x1)) = (@INSERT nat (S x1) (dotdot x0 x1))) = x3) -> ((Peano.le x0 (S x1)) -> (dotdot x0 (S x1)) = (@INSERT nat (S x1) (dotdot x0 x1))) = (x2 -> x3).
Definition term0 (x0 : nat) (x1 : nat) := @INSERT nat x1 (dotdot x0 (Nat.sub x1 (NUMERAL (BIT1 0)))).
Definition term44 (x0 : Prop) := forall y0 : nat, x0.
Definition term41 (x0 : nat) := forall y0 : nat, (Peano.le x0 (S y0)) -> (dotdot x0 (S y0)) = (@INSERT nat (S y0) (dotdot x0 y0)).
Definition term33 (x0 : nat) (x1 : nat) := @eq (nat -> Prop) (dotdot x0 (S x1)).
Definition term37 (x0 : nat) (x1 : nat) := (Peano.le x0 (S x1)) -> (dotdot x0 (S x1)) = (@INSERT nat (S x1) (dotdot x0 x1)).
Definition term23 (x0 : nat) (x1 : nat) (x2 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((Peano.le x0 (S x1)) = y0) -> (y0 -> ((dotdot x0 (S x1)) = (@INSERT nat (S x1) (dotdot x0 x1))) = y1) -> ((Peano.le x0 (S x1)) -> (dotdot x0 (S x1)) = (@INSERT nat (S x1) (dotdot x0 x1))) = (y0 -> y1)) x2.
Definition term20 (x0 : nat) (x1 : nat) := Peano.le x0 (S x1).
Definition term45 := fun y0 : nat => forall y1 : nat, (Peano.le y0 (S y1)) -> (dotdot y0 (S y1)) = (@INSERT nat (S y1) (dotdot y0 y1)).
Definition term9 := fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) -> (dotdot y0 y1) = (@INSERT nat y1 (dotdot y0 (Nat.sub y1 (NUMERAL (BIT1 0))))).
Definition term8 := fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) -> (@INSERT nat y1 (dotdot y0 (Nat.sub y1 (NUMERAL (BIT1 0))))) = (dotdot y0 y1).
Definition term5 (x0 : nat) := fun y0 : nat => (Peano.le x0 y0) -> (dotdot x0 y0) = (@INSERT nat y0 (dotdot x0 (Nat.sub y0 (NUMERAL (BIT1 0))))).
