Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term8 (x0 : nat) := fun y0 : nat => (Peano.lt x0 y0) = (Peano.le (S x0) y0).
Definition term51 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.lt x0 (Nat.mul x1 (S x2)).
Definition term21 (x0 : nat) := forall y0 : nat, (Peano.le y0 x0) = (~ (Peano.lt x0 y0)).
Definition term38 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (~ (y0 = (NUMERAL 0))) -> (Peano.le y2 (Nat.div y1 y0)) = (Peano.le (Nat.mul y0 y2) y1)) x0.
Definition term31 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop (Peano.le (Nat.div x0 x1) x2).
Definition term34 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.lt x0 (Nat.div x1 x2).
Definition term0 (x0 : nat) := (fun y0 : nat => (S y0) = (Nat.add y0 (NUMERAL (BIT1 0)))) x0.
Definition term49 (x0 : nat) (x1 : nat) (x2 : nat) := ~ (Peano.le (Nat.mul x0 (S x1)) x2).
Definition term40 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (~ (x0 = (NUMERAL 0))) -> (Peano.le y1 (Nat.div y0 x0)) = (Peano.le (Nat.mul x0 y1) y0)) x1.
Definition term28 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term22 := fun y0 : nat => forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0).
Definition term12 := fun y0 : nat => forall y1 : nat, (Peano.lt y0 y1) = (Peano.le (S y0) y1).
Definition term11 := fun y0 : nat => forall y1 : nat, (Peano.le (S y0) y1) = (Peano.lt y0 y1).
Definition term52 (x0 : nat) (x1 : nat) := Nat.mul x0 (S x1).
Definition term5 (x0 : nat) (x1 : nat) := ~ (Peano.le x0 x1).
Definition term56 (x0 : nat) (x1 : nat) := forall y0 : nat, (~ (x1 = (NUMERAL 0))) -> (Peano.le (Nat.div x0 x1) y0) = (Peano.lt x0 (Nat.mul x1 (Nat.add y0 (NUMERAL (BIT1 0))))).
Definition term18 (x0 : nat) := fun y0 : nat => (~ (Peano.lt x0 y0)) = (Peano.le y0 x0).
Definition term48 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul x0 (S x1)) x2.
Definition term9 (x0 : nat) := forall y0 : nat, (Peano.le (S x0) y0) = (Peano.lt x0 y0).
Definition term50 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop (~ (Peano.le (Nat.mul x0 (S x1)) x2)).
Definition term58 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (~ (y0 = (NUMERAL 0))) -> (Peano.le (Nat.div y1 y0) y2) = (Peano.lt y1 (Nat.mul y0 (Nat.add y2 (NUMERAL (BIT1 0))))).
Definition term57 (x0 : nat) := forall y0 : nat, forall y1 : nat, (~ (x0 = (NUMERAL 0))) -> (Peano.le (Nat.div y0 x0) y1) = (Peano.lt y0 (Nat.mul x0 (Nat.add y1 (NUMERAL (BIT1 0))))).
Definition term39 (x0 : nat) := forall y0 : nat, forall y1 : nat, (~ (x0 = (NUMERAL 0))) -> (Peano.le y1 (Nat.div y0 x0)) = (Peano.le (Nat.mul x0 y1) y0).
Definition term25 := forall y0 : nat, forall y1 : nat, (Peano.le y1 y0) = (~ (Peano.lt y0 y1)).
Definition term24 := forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0).
Definition term14 := forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) = (Peano.le (S y0) y1).
Definition term13 := forall y0 : nat, forall y1 : nat, (Peano.le (S y0) y1) = (Peano.lt y0 y1).
Definition term20 (x0 : nat) := forall y0 : nat, (~ (Peano.lt x0 y0)) = (Peano.le y0 x0).
Definition term3 (x0 : nat) := forall y0 : nat, (~ (Peano.le x0 y0)) = (Peano.lt y0 x0).
Definition term16 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt x0 y0) = (Peano.le (S x0) y0)) x1.
Definition term19 (x0 : nat) := fun y0 : nat => (Peano.le y0 x0) = (~ (Peano.lt x0 y0)).
Definition term1 (x0 : nat) := Nat.add x0 (NUMERAL (BIT1 0)).
Definition term36 (x0 : nat) (x1 : nat) (x2 : nat) := ~ (Peano.le (S x0) (Nat.div x1 x2)).
Definition term42 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (~ (x0 = (NUMERAL 0))) -> (Peano.le y0 (Nat.div x1 x0)) = (Peano.le (Nat.mul x0 y0) x1)) x2.
Definition term45 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul x0 x1) x2.
Definition term10 (x0 : nat) := forall y0 : nat, (Peano.lt x0 y0) = (Peano.le (S x0) y0).
Definition term33 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.lt x0 (Nat.mul x1 (Nat.add x2 (NUMERAL (BIT1 0)))).
Definition term47 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = (NUMERAL 0))) -> (Peano.le (S x1) (Nat.div x2 x0)) = (Peano.le (Nat.mul x0 (S x1)) x2).
Definition term54 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop (Peano.lt x0 (Nat.mul x1 (Nat.add x2 (NUMERAL (BIT1 0))))).
Definition term37 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop (~ (Peano.le (S x0) (Nat.div x1 x2))).
Definition term35 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (S x0) (Nat.div x1 x2).
Definition term17 (x0 : nat) (x1 : nat) := ~ (Peano.lt x0 x1).
Definition term26 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y1 y0) = (~ (Peano.lt y0 y1))) x0.
Definition term15 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y0 y1) = (Peano.le (S y0) y1)) x0.
Definition term2 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) x0.
Definition term43 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = (NUMERAL 0))) -> (Peano.le x1 (Nat.div x2 x0)) = (Peano.le (Nat.mul x0 x1) x2).
Definition term44 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le x0 (Nat.div x1 x2).
Definition term29 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.div x0 x1) x2.
Definition term6 (x0 : nat) (x1 : nat) := Peano.le (S x0) x1.
Definition term27 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le y0 x0) = (~ (Peano.lt x0 y0))) x1.
Definition term30 (x0 : nat) (x1 : nat) (x2 : nat) := ~ (Peano.lt x0 (Nat.div x1 x2)).
Definition term55 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x1 = (NUMERAL 0))) -> (Peano.le (Nat.div x0 x1) x2) = (Peano.lt x0 (Nat.mul x1 (Nat.add x2 (NUMERAL (BIT1 0))))).
Definition term46 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> (x0 = (NUMERAL 0)) = False.
Definition term23 := fun y0 : nat => forall y1 : nat, (Peano.le y1 y0) = (~ (Peano.lt y0 y1)).
Definition term32 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop (~ (Peano.lt x0 (Nat.div x1 x2))).
Definition term7 (x0 : nat) := fun y0 : nat => (Peano.le (S x0) y0) = (Peano.lt x0 y0).
Definition term4 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (Peano.le x0 y0)) = (Peano.lt y0 x0)) x1.
Definition term41 (x0 : nat) (x1 : nat) := forall y0 : nat, (~ (x0 = (NUMERAL 0))) -> (Peano.le y0 (Nat.div x1 x0)) = (Peano.le (Nat.mul x0 y0) x1).
Definition term53 (x0 : nat) (x1 : nat) := Nat.mul x0 (Nat.add x1 (NUMERAL (BIT1 0))).
