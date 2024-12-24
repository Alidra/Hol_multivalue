Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, ((~ (y0 = y1)) /\ (~ (y2 = y3))) = (~ ((Nat.add (Nat.mul y0 y2) (Nat.mul y1 y3)) = (Nat.add (Nat.mul y0 y3) (Nat.mul y1 y2))))) x0.
Definition term7 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => ((~ (x0 = x1)) /\ (~ (x2 = y0))) = (~ ((Nat.add (Nat.mul x0 x2) (Nat.mul x1 y0)) = (Nat.add (Nat.mul x0 y0) (Nat.mul x1 x2))))) x3.
Definition term6 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, ((~ (x0 = x1)) /\ (~ (x2 = y0))) = (~ ((Nat.add (Nat.mul x0 x2) (Nat.mul x1 y0)) = (Nat.add (Nat.mul x0 y0) (Nat.mul x1 x2)))).
Definition term4 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, ((~ (x0 = x1)) /\ (~ (y0 = y1))) = (~ ((Nat.add (Nat.mul x0 y0) (Nat.mul x1 y1)) = (Nat.add (Nat.mul x0 y1) (Nat.mul x1 y0)))).
Definition term2 (x0 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((~ (x0 = y0)) /\ (~ (y1 = y2))) = (~ ((Nat.add (Nat.mul x0 y1) (Nat.mul y0 y2)) = (Nat.add (Nat.mul x0 y2) (Nat.mul y0 y1)))).
Definition term0 := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((~ (y0 = y1)) /\ (~ (y2 = y3))) = (~ ((Nat.add (Nat.mul y0 y2) (Nat.mul y1 y3)) = (Nat.add (Nat.mul y0 y3) (Nat.mul y1 y2)))).
Definition term5 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => forall y1 : nat, ((~ (x0 = x1)) /\ (~ (y0 = y1))) = (~ ((Nat.add (Nat.mul x0 y0) (Nat.mul x1 y1)) = (Nat.add (Nat.mul x0 y1) (Nat.mul x1 y0))))) x2.
Definition term3 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((~ (x0 = y0)) /\ (~ (y1 = y2))) = (~ ((Nat.add (Nat.mul x0 y1) (Nat.mul y0 y2)) = (Nat.add (Nat.mul x0 y2) (Nat.mul y0 y1))))) x1.
