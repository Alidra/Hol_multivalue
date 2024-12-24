Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term49 (x0 : nat -> real) (x1 : nat) (x2 : nat) := ((Peano.le x1 x2) -> ((@sum nat (dotdot x1 x2) x0) = (@sum nat (dotdot (NUMERAL 0) (Nat.sub x2 x1)) (fun y0 : nat => x0 (Nat.add y0 x1)))) = True) -> ((Peano.le x1 x2) -> (@sum nat (dotdot x1 x2) x0) = (@sum nat (dotdot (NUMERAL 0) (Nat.sub x2 x1)) (fun y0 : nat => x0 (Nat.add y0 x1)))) = ((Peano.le x1 x2) -> True).
Definition term20 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le y0 x0) -> (Nat.add (Nat.sub x0 y0) y0) = x0) x1.
Definition term56 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term46 (x0 : nat) (x1 : nat) := @sum nat (dotdot x0 x1).
Definition term40 (x0 : nat -> real) (x1 : nat) (x2 : nat) (x3 : Prop) := ((Peano.le x1 x2) = (Peano.le x1 x2)) -> ((Peano.le x1 x2) -> ((@sum nat (dotdot x1 x2) x0) = (@sum nat (dotdot (NUMERAL 0) (Nat.sub x2 x1)) (fun y0 : nat => x0 (Nat.add y0 x1)))) = x3) -> ((Peano.le x1 x2) -> (@sum nat (dotdot x1 x2) x0) = (@sum nat (dotdot (NUMERAL 0) (Nat.sub x2 x1)) (fun y0 : nat => x0 (Nat.add y0 x1)))) = ((Peano.le x1 x2) -> x3).
Definition term60 := fun y0 : nat -> real => forall y1 : nat, forall y2 : nat, (Peano.le y1 y2) -> (@sum nat (dotdot y1 y2) y0) = (@sum nat (dotdot (NUMERAL 0) (Nat.sub y2 y1)) (fun y3 : nat => y0 (Nat.add y3 y1))).
Definition term11 (x0 : nat) := fun y0 : nat -> real => forall y1 : nat, forall y2 : nat, (@sum nat (dotdot y1 y2) (fun y3 : nat => y0 (Nat.add y3 x0))) = (@sum nat (dotdot (Nat.add y1 x0) (Nat.add y2 x0)) y0).
Definition term10 (x0 : nat) := fun y0 : nat -> real => forall y1 : nat, forall y2 : nat, (@sum nat (dotdot (Nat.add y1 x0) (Nat.add y2 x0)) y0) = (@sum nat (dotdot y1 y2) (fun y3 : nat => y0 (Nat.add y3 x0))).
Definition term6 (x0 : nat -> real) (x1 : nat) := fun y0 : nat => forall y1 : nat, (@sum nat (dotdot (Nat.add y0 x1) (Nat.add y1 x1)) x0) = (@sum nat (dotdot y0 y1) (fun y2 : nat => x0 (Nat.add y2 x1))).
Definition term48 (x0 : nat) (x1 : nat -> real) (x2 : nat) := (Peano.le x2 x0) -> ((@sum nat (dotdot x2 x0) x1) = (@sum nat (dotdot (NUMERAL 0) (Nat.sub x0 x2)) (fun y0 : nat => x1 (Nat.add y0 x2)))) = True.
Definition term62 := forall y0 : nat -> real, forall y1 : nat, forall y2 : nat, (Peano.le y1 y2) -> (@sum nat (dotdot y1 y2) y0) = (@sum nat (dotdot (NUMERAL 0) (Nat.sub y2 y1)) (fun y3 : nat => y0 (Nat.add y3 y1))).
Definition term13 (x0 : nat) := forall y0 : nat -> real, forall y1 : nat, forall y2 : nat, (@sum nat (dotdot y1 y2) (fun y3 : nat => y0 (Nat.add y3 x0))) = (@sum nat (dotdot (Nat.add y1 x0) (Nat.add y2 x0)) y0).
Definition term12 (x0 : nat) := forall y0 : nat -> real, forall y1 : nat, forall y2 : nat, (@sum nat (dotdot (Nat.add y1 x0) (Nat.add y2 x0)) y0) = (@sum nat (dotdot y1 y2) (fun y3 : nat => y0 (Nat.add y3 x0))).
Definition term52 (x0 : nat -> real) (x1 : nat) := fun y0 : nat => (Peano.le x1 y0) -> (@sum nat (dotdot x1 y0) x0) = (@sum nat (dotdot (NUMERAL 0) (Nat.sub y0 x1)) (fun y1 : nat => x0 (Nat.add y1 x1))).
Definition term45 (x0 : nat) (x1 : nat) := @sum nat (dotdot (Nat.add (NUMERAL 0) x1) (Nat.add (Nat.sub x0 x1) x1)).
Definition term36 (x0 : nat) (x1 : nat -> real) (x2 : nat) (x3 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((Peano.le x2 x0) = y0) -> (y0 -> ((@sum nat (dotdot x2 x0) x1) = (@sum nat (dotdot (NUMERAL 0) (Nat.sub x0 x2)) (fun y2 : nat => x1 (Nat.add y2 x2)))) = y1) -> ((Peano.le x2 x0) -> (@sum nat (dotdot x2 x0) x1) = (@sum nat (dotdot (NUMERAL 0) (Nat.sub x0 x2)) (fun y2 : nat => x1 (Nat.add y2 x2)))) = (y0 -> y1)) x3.
Definition term7 (x0 : nat) (x1 : nat -> real) := fun y0 : nat => forall y1 : nat, (@sum nat (dotdot y0 y1) (fun y2 : nat => x1 (Nat.add y2 x0))) = (@sum nat (dotdot (Nat.add y0 x0) (Nat.add y1 x0)) x1).
Definition term1 (x0 : nat) (x1 : nat) (x2 : nat -> real) (x3 : nat) := @sum nat (dotdot x0 x1) (fun y0 : nat => x2 (Nat.add y0 x3)).
Definition term15 := fun y0 : nat => forall y1 : nat -> real, forall y2 : nat, forall y3 : nat, (@sum nat (dotdot y2 y3) (fun y4 : nat => y1 (Nat.add y4 y0))) = (@sum nat (dotdot (Nat.add y2 y0) (Nat.add y3 y0)) y1).
Definition term14 := fun y0 : nat => forall y1 : nat -> real, forall y2 : nat, forall y3 : nat, (@sum nat (dotdot (Nat.add y2 y0) (Nat.add y3 y0)) y1) = (@sum nat (dotdot y2 y3) (fun y4 : nat => y1 (Nat.add y4 y0))).
Definition term0 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat -> real) := @sum nat (dotdot (Nat.add x0 x2) (Nat.add x1 x2)) x3.
Definition term30 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term42 (x0 : nat) (x1 : nat) (x2 : nat -> real) := @sum nat (dotdot (Nat.add (NUMERAL 0) x1) (Nat.add (Nat.sub x0 x1) x1)) x2.
Definition term39 (x0 : nat) (x1 : nat -> real) (x2 : nat) (x3 : Prop) (x4 : Prop) := ((Peano.le x2 x0) = x3) -> (x3 -> ((@sum nat (dotdot x2 x0) x1) = (@sum nat (dotdot (NUMERAL 0) (Nat.sub x0 x2)) (fun y0 : nat => x1 (Nat.add y0 x2)))) = x4) -> ((Peano.le x2 x0) -> (@sum nat (dotdot x2 x0) x1) = (@sum nat (dotdot (NUMERAL 0) (Nat.sub x0 x2)) (fun y0 : nat => x1 (Nat.add y0 x2)))) = (x3 -> x4).
Definition term29 (x0 : nat) (x1 : nat) (x2 : nat -> real) (x3 : nat) := (fun y0 : nat => (@sum nat (dotdot x0 y0) (fun y1 : nat => x2 (Nat.add y1 x1))) = (@sum nat (dotdot (Nat.add x0 x1) (Nat.add y0 x1)) x2)) x3.
Definition term25 (x0 : nat) := Nat.add (NUMERAL 0) x0.
Definition term63 := forall y0 : nat -> real, True.
Definition term59 (x0 : nat -> real) := forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> (@sum nat (dotdot y0 y1) x0) = (@sum nat (dotdot (NUMERAL 0) (Nat.sub y1 y0)) (fun y2 : nat => x0 (Nat.add y2 y0))).
Definition term17 := forall y0 : nat, forall y1 : nat -> real, forall y2 : nat, forall y3 : nat, (@sum nat (dotdot y2 y3) (fun y4 : nat => y1 (Nat.add y4 y0))) = (@sum nat (dotdot (Nat.add y2 y0) (Nat.add y3 y0)) y1).
Definition term16 := forall y0 : nat, forall y1 : nat -> real, forall y2 : nat, forall y3 : nat, (@sum nat (dotdot (Nat.add y2 y0) (Nat.add y3 y0)) y1) = (@sum nat (dotdot y2 y3) (fun y4 : nat => y1 (Nat.add y4 y0))).
Definition term9 (x0 : nat) (x1 : nat -> real) := forall y0 : nat, forall y1 : nat, (@sum nat (dotdot y0 y1) (fun y2 : nat => x1 (Nat.add y2 x0))) = (@sum nat (dotdot (Nat.add y0 x0) (Nat.add y1 x0)) x1).
Definition term8 (x0 : nat -> real) (x1 : nat) := forall y0 : nat, forall y1 : nat, (@sum nat (dotdot (Nat.add y0 x1) (Nat.add y1 x1)) x0) = (@sum nat (dotdot y0 y1) (fun y2 : nat => x0 (Nat.add y2 x1))).
Definition term28 (x0 : nat) (x1 : nat -> real) (x2 : nat) := (fun y0 : nat => forall y1 : nat, (@sum nat (dotdot y0 y1) (fun y2 : nat => x1 (Nat.add y2 x0))) = (@sum nat (dotdot (Nat.add y0 x0) (Nat.add y1 x0)) x1)) x2.
Definition term55 := forall y0 : nat, True.
Definition term23 := forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0.
Definition term24 (x0 : nat) := (fun y0 : nat => (Nat.add (NUMERAL 0) y0) = y0) x0.
Definition term53 := fun y0 : nat => True.
Definition term26 (x0 : nat) := (fun y0 : nat => forall y1 : nat -> real, forall y2 : nat, forall y3 : nat, (@sum nat (dotdot y2 y3) (fun y4 : nat => y1 (Nat.add y4 y0))) = (@sum nat (dotdot (Nat.add y2 y0) (Nat.add y3 y0)) y1)) x0.
Definition term50 (x0 : nat) (x1 : nat -> real) (x2 : nat) := (Peano.le x2 x0) -> (@sum nat (dotdot x2 x0) x1) = (@sum nat (dotdot (NUMERAL 0) (Nat.sub x0 x2)) (fun y0 : nat => x1 (Nat.add y0 x2))).
Definition term4 (x0 : nat) (x1 : nat -> real) (x2 : nat) := forall y0 : nat, (@sum nat (dotdot (Nat.add x0 x2) (Nat.add y0 x2)) x1) = (@sum nat (dotdot x0 y0) (fun y1 : nat => x1 (Nat.add y1 x2))).
Definition term43 (x0 : nat) := dotdot (Nat.add (NUMERAL 0) x0).
Definition term37 (x0 : nat) (x1 : nat -> real) (x2 : nat) (x3 : Prop) := forall y0 : Prop, ((Peano.le x2 x0) = x3) -> (x3 -> ((@sum nat (dotdot x2 x0) x1) = (@sum nat (dotdot (NUMERAL 0) (Nat.sub x0 x2)) (fun y1 : nat => x1 (Nat.add y1 x2)))) = y0) -> ((Peano.le x2 x0) -> (@sum nat (dotdot x2 x0) x1) = (@sum nat (dotdot (NUMERAL 0) (Nat.sub x0 x2)) (fun y1 : nat => x1 (Nat.add y1 x2)))) = (x3 -> y0).
Definition term31 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term54 (x0 : nat -> real) (x1 : nat) := forall y0 : nat, (Peano.le x1 y0) -> (@sum nat (dotdot x1 y0) x0) = (@sum nat (dotdot (NUMERAL 0) (Nat.sub y0 x1)) (fun y1 : nat => x0 (Nat.add y1 x1))).
Definition term33 (x0 : nat) (x1 : nat -> real) (x2 : nat) := forall y0 : Prop, forall y1 : Prop, ((Peano.le x2 x0) = y0) -> (y0 -> ((@sum nat (dotdot x2 x0) x1) = (@sum nat (dotdot (NUMERAL 0) (Nat.sub x0 x2)) (fun y2 : nat => x1 (Nat.add y2 x2)))) = y1) -> ((Peano.le x2 x0) -> (@sum nat (dotdot x2 x0) x1) = (@sum nat (dotdot (NUMERAL 0) (Nat.sub x0 x2)) (fun y2 : nat => x1 (Nat.add y2 x2)))) = (y0 -> y1).
Definition term32 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term51 (x0 : nat) (x1 : nat) := (Peano.le x0 x1) -> True.
Definition term41 (x0 : nat -> real) (x1 : nat) (x2 : nat) (x3 : Prop) := ((Peano.le x1 x2) -> ((@sum nat (dotdot x1 x2) x0) = (@sum nat (dotdot (NUMERAL 0) (Nat.sub x2 x1)) (fun y0 : nat => x0 (Nat.add y0 x1)))) = x3) -> ((Peano.le x1 x2) -> (@sum nat (dotdot x1 x2) x0) = (@sum nat (dotdot (NUMERAL 0) (Nat.sub x2 x1)) (fun y0 : nat => x0 (Nat.add y0 x1)))) = ((Peano.le x1 x2) -> x3).
Definition term35 (x0 : nat) (x1 : nat -> real) (x2 : nat) := @sum nat (dotdot (NUMERAL 0) (Nat.sub x0 x2)) (fun y0 : nat => x1 (Nat.add y0 x2)).
Definition term38 (x0 : nat) (x1 : nat -> real) (x2 : nat) (x3 : Prop) (x4 : Prop) := (fun y0 : Prop => ((Peano.le x2 x0) = x3) -> (x3 -> ((@sum nat (dotdot x2 x0) x1) = (@sum nat (dotdot (NUMERAL 0) (Nat.sub x0 x2)) (fun y1 : nat => x1 (Nat.add y1 x2)))) = y0) -> ((Peano.le x2 x0) -> (@sum nat (dotdot x2 x0) x1) = (@sum nat (dotdot (NUMERAL 0) (Nat.sub x0 x2)) (fun y1 : nat => x1 (Nat.add y1 x2)))) = (x3 -> y0)) x4.
Definition term27 (x0 : nat) (x1 : nat -> real) := (fun y0 : nat -> real => forall y1 : nat, forall y2 : nat, (@sum nat (dotdot y1 y2) (fun y3 : nat => y0 (Nat.add y3 x0))) = (@sum nat (dotdot (Nat.add y1 x0) (Nat.add y2 x0)) y0)) x1.
Definition term34 (x0 : nat) (x1 : nat) (x2 : nat -> real) := @sum nat (dotdot x0 x1) x2.
Definition term61 := fun y0 : nat -> real => True.
Definition term18 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y1 y0) -> (Nat.add (Nat.sub y0 y1) y1) = y0) x0.
Definition term44 (x0 : nat) (x1 : nat) := dotdot (Nat.add (NUMERAL 0) x1) (Nat.add (Nat.sub x0 x1) x1).
Definition term64 (x0 : Prop) := forall y0 : nat -> real, x0.
Definition term5 (x0 : nat) (x1 : nat) (x2 : nat -> real) := forall y0 : nat, (@sum nat (dotdot x0 y0) (fun y1 : nat => x2 (Nat.add y1 x1))) = (@sum nat (dotdot (Nat.add x0 x1) (Nat.add y0 x1)) x2).
Definition term57 (x0 : Prop) := forall y0 : nat, x0.
Definition term47 (x0 : nat) (x1 : nat) (x2 : nat -> real) := @eq real (@sum nat (dotdot x0 x1) x2).
Definition term22 (x0 : nat) (x1 : nat) := Nat.add (Nat.sub x0 x1) x1.
Definition term2 (x0 : nat) (x1 : nat -> real) (x2 : nat) := fun y0 : nat => (@sum nat (dotdot (Nat.add x0 x2) (Nat.add y0 x2)) x1) = (@sum nat (dotdot x0 y0) (fun y1 : nat => x1 (Nat.add y1 x2))).
Definition term21 (x0 : nat) (x1 : nat) := (Peano.le x0 x1) -> (Nat.add (Nat.sub x1 x0) x0) = x1.
Definition term3 (x0 : nat) (x1 : nat) (x2 : nat -> real) := fun y0 : nat => (@sum nat (dotdot x0 y0) (fun y1 : nat => x2 (Nat.add y1 x1))) = (@sum nat (dotdot (Nat.add x0 x1) (Nat.add y0 x1)) x2).
Definition term58 (x0 : nat -> real) := fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) -> (@sum nat (dotdot y0 y1) x0) = (@sum nat (dotdot (NUMERAL 0) (Nat.sub y1 y0)) (fun y2 : nat => x0 (Nat.add y2 y0))).
Definition term19 (x0 : nat) := forall y0 : nat, (Peano.le y0 x0) -> (Nat.add (Nat.sub x0 y0) y0) = x0.
