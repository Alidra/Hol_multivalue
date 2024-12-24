Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term34 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x0 (NUMERAL 0)) x1.
Definition term70 (x0 : nat) (x1 : nat) := (~ (x1 = (NUMERAL 0))) -> exists y0 : nat, exists y1 : nat, (x0 = (Nat.add (Nat.mul y0 x1) y1)) /\ (Peano.lt y1 x1).
Definition term66 := exists y0 : nat, y0 = (NUMERAL 0).
Definition term52 (x0 : nat) (x1 : nat) := (fun y0 : nat => y0 = x0) x1.
Definition term22 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : Prop) (x5 : Prop) (x6 : Prop) := (fun y0 : Prop => ((x3 = (NUMERAL 0)) = x4) -> (x4 -> ((x1 = (NUMERAL 0)) /\ (x2 = x0)) = x5) -> ((~ x4) -> ((x0 = (Nat.add (Nat.mul x1 x3) x2)) /\ (Peano.lt x2 x3)) = y0) -> (@COND Prop (x3 = (NUMERAL 0)) ((x1 = (NUMERAL 0)) /\ (x2 = x0)) ((x0 = (Nat.add (Nat.mul x1 x3) x2)) /\ (Peano.lt x2 x3))) = (@COND Prop x4 x5 y0)) x6.
Definition term39 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ True) -> ((x1 = (Nat.add (Nat.mul x2 x0) x3)) /\ (Peano.lt x3 x0)) = ((x1 = (Nat.add (Nat.mul x2 (NUMERAL 0)) x3)) /\ (Peano.lt x3 (NUMERAL 0))).
Definition term24 := @eq nat (NUMERAL 0).
Definition term85 (x0 : nat) := forall y0 : nat, exists y1 : nat, exists y2 : nat, @COND Prop (y0 = (NUMERAL 0)) ((y1 = (NUMERAL 0)) /\ (y2 = x0)) ((x0 = (Nat.add (Nat.mul y1 y0) y2)) /\ (Peano.lt y2 y0)).
Definition term68 (x0 : nat) := forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> exists y1 : nat, exists y2 : nat, (x0 = (Nat.add (Nat.mul y1 y0) y2)) /\ (Peano.lt y2 y0).
Definition term41 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @COND Prop (x3 = (NUMERAL 0)) ((x1 = (NUMERAL 0)) /\ (x2 = x0)) ((x0 = (Nat.add (Nat.mul x1 x3) x2)) /\ (Peano.lt x2 x3)).
Definition term18 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : Prop) := (fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, ((x3 = (NUMERAL 0)) = y0) -> (y0 -> ((x1 = (NUMERAL 0)) /\ (x2 = x0)) = y1) -> ((~ y0) -> ((x0 = (Nat.add (Nat.mul x1 x3) x2)) /\ (Peano.lt x2 x3)) = y2) -> (@COND Prop (x3 = (NUMERAL 0)) ((x1 = (NUMERAL 0)) /\ (x2 = x0)) ((x0 = (Nat.add (Nat.mul x1 x3) x2)) /\ (Peano.lt x2 x3))) = (@COND Prop y0 y1 y2)) x4.
Definition term46 (x0 : nat) (x1 : nat) := exists y0 : nat, (x0 = (NUMERAL 0)) /\ (y0 = x1).
Definition term55 (x0 : nat) (x1 : nat) := fun y0 : nat => (x0 = (NUMERAL 0)) /\ ((fun y1 : nat => y1 = x1) y0).
Definition term31 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x0 x1).
Definition term8 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 /\ (x1 y0).
Definition term32 (x0 : nat) := Nat.add (Nat.mul x0 (NUMERAL 0)).
Definition term49 (x0 : nat) (x1 : nat) := exists y0 : nat, (x0 = (NUMERAL 0)) /\ ((fun y1 : nat => y1 = x1) y0).
Definition term78 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ False) -> ((x0 = (Nat.add (Nat.mul x1 x3) x2)) /\ (Peano.lt x2 x3)) = ((x0 = (Nat.add (Nat.mul x1 x3) x2)) /\ (Peano.lt x2 x3)).
Definition term77 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : Prop) := ((~ False) -> ((x3 = (Nat.add (Nat.mul x1 x0) x2)) /\ (Peano.lt x2 x0)) = x4) -> (@COND Prop (x0 = (NUMERAL 0)) ((x1 = (NUMERAL 0)) /\ (x2 = x3)) ((x3 = (Nat.add (Nat.mul x1 x0) x2)) /\ (Peano.lt x2 x0))) = (@COND Prop False ((x1 = (NUMERAL 0)) /\ (x2 = x3)) x4).
Definition term29 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : Prop) := ((~ True) -> ((x3 = (Nat.add (Nat.mul x1 x0) x2)) /\ (Peano.lt x2 x0)) = x4) -> (@COND Prop (x0 = (NUMERAL 0)) ((x1 = (NUMERAL 0)) /\ (x2 = x3)) ((x3 = (Nat.add (Nat.mul x1 x0) x2)) /\ (Peano.lt x2 x0))) = (@COND Prop True ((x1 = (NUMERAL 0)) /\ (x2 = x3)) x4).
Definition term11 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) (x3 : Prop) (x4 : a0) := forall y0 : a0, (x0 = x3) -> (x3 -> x1 = x4) -> ((~ x3) -> x2 = y0) -> (@COND a0 x0 x1 x2) = (@COND a0 x3 x4 y0).
Definition term9 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 /\ (exists y0 : a0, x1 y0).
Definition term7 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (exists y1 : a0, x0 /\ (y0 y1)) = (x0 /\ (exists y1 : a0, y0 y1))) x1.
Definition term25 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : Prop) (x5 : Prop) := ((x3 = (NUMERAL 0)) = True) -> (True -> ((x1 = (NUMERAL 0)) /\ (x2 = x0)) = x4) -> ((~ True) -> ((x0 = (Nat.add (Nat.mul x1 x3) x2)) /\ (Peano.lt x2 x3)) = x5) -> (@COND Prop (x3 = (NUMERAL 0)) ((x1 = (NUMERAL 0)) /\ (x2 = x0)) ((x0 = (Nat.add (Nat.mul x1 x3) x2)) /\ (Peano.lt x2 x3))) = (@COND Prop True x4 x5).
Definition term82 (x0 : nat) (x1 : nat) (x2 : nat) := exists y0 : nat, (x0 = (Nat.add (Nat.mul x1 x2) y0)) /\ (Peano.lt y0 x2).
Definition term53 (x0 : nat) := and (x0 = (NUMERAL 0)).
Definition term3 (a0 : Type') (x0 : a0) := (fun y0 : a0 => exists y1 : a0, y1 = y0) x0.
Definition term40 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((~ True) -> ((x1 = (Nat.add (Nat.mul x2 x0) x3)) /\ (Peano.lt x3 x0)) = ((x1 = (Nat.add (Nat.mul x2 (NUMERAL 0)) x3)) /\ (Peano.lt x3 (NUMERAL 0)))) -> (@COND Prop (x0 = (NUMERAL 0)) ((x2 = (NUMERAL 0)) /\ (x3 = x1)) ((x1 = (Nat.add (Nat.mul x2 x0) x3)) /\ (Peano.lt x3 x0))) = (@COND Prop True ((x2 = (NUMERAL 0)) /\ (x3 = x1)) ((x1 = (Nat.add (Nat.mul x2 (NUMERAL 0)) x3)) /\ (Peano.lt x3 (NUMERAL 0)))).
Definition term17 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x0 = (Nat.add (Nat.mul x1 x3) x2)) /\ (Peano.lt x2 x3).
Definition term83 (x0 : nat) (x1 : nat) := fun y0 : nat => exists y1 : nat, (x0 = (Nat.add (Nat.mul y0 x1) y1)) /\ (Peano.lt y1 x1).
Definition term44 (x0 : nat) (x1 : nat) := fun y0 : nat => (x0 = (NUMERAL 0)) /\ (y0 = x1).
Definition term2 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term5 (a0 : Type') (x0 : Prop) := (fun y0 : Prop => forall y1 : a0 -> Prop, (exists y2 : a0, y0 /\ (y1 y2)) = (y0 /\ (exists y2 : a0, y1 y2))) x0.
Definition term6 (a0 : Type') (x0 : Prop) := forall y0 : a0 -> Prop, (exists y1 : a0, x0 /\ (y0 y1)) = (x0 /\ (exists y1 : a0, y0 y1)).
Definition term57 (x0 : nat) (x1 : nat) := @eq Prop (exists y0 : nat, (x0 = (NUMERAL 0)) /\ (y0 = x1)).
Definition term56 (x0 : nat) (x1 : nat) := @eq Prop (exists y0 : nat, (x0 = (NUMERAL 0)) /\ ((fun y1 : nat => y1 = x1) y0)).
Definition term47 (x0 : Prop) (x1 : nat -> Prop) := exists y0 : nat, x0 /\ (x1 y0).
Definition term74 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : Prop) (x5 : Prop) := (False -> ((x1 = (NUMERAL 0)) /\ (x2 = x0)) = x4) -> ((~ False) -> ((x0 = (Nat.add (Nat.mul x1 x3) x2)) /\ (Peano.lt x2 x3)) = x5) -> (@COND Prop (x3 = (NUMERAL 0)) ((x1 = (NUMERAL 0)) /\ (x2 = x0)) ((x0 = (Nat.add (Nat.mul x1 x3) x2)) /\ (Peano.lt x2 x3))) = (@COND Prop False x4 x5).
Definition term16 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = (NUMERAL 0)) /\ (x1 = x2).
Definition term42 (x0 : nat) (x1 : nat) (x2 : nat) := @COND Prop True ((x1 = (NUMERAL 0)) /\ (x2 = x0)) ((x0 = (Nat.add (Nat.mul x1 (NUMERAL 0)) x2)) /\ (Peano.lt x2 (NUMERAL 0))).
Definition term48 (x0 : Prop) (x1 : nat -> Prop) := x0 /\ (exists y0 : nat, x1 y0).
Definition term80 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @COND Prop False ((x1 = (NUMERAL 0)) /\ (x2 = x0)) ((x0 = (Nat.add (Nat.mul x1 x3) x2)) /\ (Peano.lt x2 x3)).
Definition term43 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nat => @COND Prop (x2 = (NUMERAL 0)) ((x1 = (NUMERAL 0)) /\ (y0 = x0)) ((x0 = (Nat.add (Nat.mul x1 x2) y0)) /\ (Peano.lt y0 x2)).
Definition term62 (x0 : nat) := (x0 = (NUMERAL 0)) /\ True.
Definition term50 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) /\ (exists y0 : nat, (fun y1 : nat => y1 = x1) y0).
Definition term20 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : Prop) (x5 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((x3 = (NUMERAL 0)) = x4) -> (x4 -> ((x1 = (NUMERAL 0)) /\ (x2 = x0)) = y0) -> ((~ x4) -> ((x0 = (Nat.add (Nat.mul x1 x3) x2)) /\ (Peano.lt x2 x3)) = y1) -> (@COND Prop (x3 = (NUMERAL 0)) ((x1 = (NUMERAL 0)) /\ (x2 = x0)) ((x0 = (Nat.add (Nat.mul x1 x3) x2)) /\ (Peano.lt x2 x3))) = (@COND Prop x4 y0 y1)) x5.
Definition term59 (x0 : nat) := exists y0 : nat, (fun y1 : nat => y1 = x0) y0.
Definition term35 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := and (x0 = (Nat.add (Nat.mul x1 x2) x3)).
Definition term86 := forall y0 : nat, forall y1 : nat, exists y2 : nat, exists y3 : nat, @COND Prop (y1 = (NUMERAL 0)) ((y2 = (NUMERAL 0)) /\ (y3 = y0)) ((y0 = (Nat.add (Nat.mul y2 y1) y3)) /\ (Peano.lt y3 y1)).
Definition term23 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : Prop) (x5 : Prop) (x6 : Prop) := ((x3 = (NUMERAL 0)) = x4) -> (x4 -> ((x1 = (NUMERAL 0)) /\ (x2 = x0)) = x5) -> ((~ x4) -> ((x0 = (Nat.add (Nat.mul x1 x3) x2)) /\ (Peano.lt x2 x3)) = x6) -> (@COND Prop (x3 = (NUMERAL 0)) ((x1 = (NUMERAL 0)) /\ (x2 = x0)) ((x0 = (Nat.add (Nat.mul x1 x3) x2)) /\ (Peano.lt x2 x3))) = (@COND Prop x4 x5 x6).
Definition term45 (x0 : nat) (x1 : nat) (x2 : nat) := exists y0 : nat, @COND Prop (x2 = (NUMERAL 0)) ((x1 = (NUMERAL 0)) /\ (y0 = x0)) ((x0 = (Nat.add (Nat.mul x1 x2) y0)) /\ (Peano.lt y0 x2)).
Definition term1 (x0 : nat) := (x0 = (NUMERAL 0)) \/ (~ (x0 = (NUMERAL 0))).
Definition term36 (x0 : nat) (x1 : nat) (x2 : nat) := and (x0 = (Nat.add (Nat.mul x1 (NUMERAL 0)) x2)).
Definition term26 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : Prop) (x5 : Prop) := (True -> ((x1 = (NUMERAL 0)) /\ (x2 = x0)) = x4) -> ((~ True) -> ((x0 = (Nat.add (Nat.mul x1 x3) x2)) /\ (Peano.lt x2 x3)) = x5) -> (@COND Prop (x3 = (NUMERAL 0)) ((x1 = (NUMERAL 0)) /\ (x2 = x0)) ((x0 = (Nat.add (Nat.mul x1 x3) x2)) /\ (Peano.lt x2 x3))) = (@COND Prop True x4 x5).
Definition term63 (x0 : nat) (x1 : nat) := fun y0 : nat => exists y1 : nat, @COND Prop (x1 = (NUMERAL 0)) ((y0 = (NUMERAL 0)) /\ (y1 = x0)) ((x0 = (Nat.add (Nat.mul y0 x1) y1)) /\ (Peano.lt y1 x1)).
Definition term27 (x0 : nat) (x1 : nat) (x2 : nat) := True -> ((x0 = (NUMERAL 0)) /\ (x1 = x2)) = ((x0 = (NUMERAL 0)) /\ (x1 = x2)).
Definition term54 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = (NUMERAL 0)) /\ ((fun y0 : nat => y0 = x1) x2).
Definition term75 (x0 : nat) (x1 : nat) (x2 : nat) := False -> ((x0 = (NUMERAL 0)) /\ (x1 = x2)) = ((x0 = (NUMERAL 0)) /\ (x1 = x2)).
Definition term60 (x0 : nat) := exists y0 : nat, y0 = x0.
Definition term21 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : Prop) (x5 : Prop) := forall y0 : Prop, ((x3 = (NUMERAL 0)) = x4) -> (x4 -> ((x1 = (NUMERAL 0)) /\ (x2 = x0)) = x5) -> ((~ x4) -> ((x0 = (Nat.add (Nat.mul x1 x3) x2)) /\ (Peano.lt x2 x3)) = y0) -> (@COND Prop (x3 = (NUMERAL 0)) ((x1 = (NUMERAL 0)) /\ (x2 = x0)) ((x0 = (Nat.add (Nat.mul x1 x3) x2)) /\ (Peano.lt x2 x3))) = (@COND Prop x4 x5 y0).
Definition term4 (a0 : Type') (x0 : a0) := exists y0 : a0, y0 = x0.
Definition term81 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nat => (x0 = (Nat.add (Nat.mul x1 x2) y0)) /\ (Peano.lt y0 x2).
Definition term69 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> exists y1 : nat, exists y2 : nat, (x0 = (Nat.add (Nat.mul y1 y0) y2)) /\ (Peano.lt y2 y0)) x1.
Definition term19 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : Prop) := forall y0 : Prop, forall y1 : Prop, ((x3 = (NUMERAL 0)) = x4) -> (x4 -> ((x1 = (NUMERAL 0)) /\ (x2 = x0)) = y0) -> ((~ x4) -> ((x0 = (Nat.add (Nat.mul x1 x3) x2)) /\ (Peano.lt x2 x3)) = y1) -> (@COND Prop (x3 = (NUMERAL 0)) ((x1 = (NUMERAL 0)) /\ (x2 = x0)) ((x0 = (Nat.add (Nat.mul x1 x3) x2)) /\ (Peano.lt x2 x3))) = (@COND Prop x4 y0 y1).
Definition term15 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := forall y0 : Prop, forall y1 : Prop, forall y2 : Prop, ((x3 = (NUMERAL 0)) = y0) -> (y0 -> ((x1 = (NUMERAL 0)) /\ (x2 = x0)) = y1) -> ((~ y0) -> ((x0 = (Nat.add (Nat.mul x1 x3) x2)) /\ (Peano.lt x2 x3)) = y2) -> (@COND Prop (x3 = (NUMERAL 0)) ((x1 = (NUMERAL 0)) /\ (x2 = x0)) ((x0 = (Nat.add (Nat.mul x1 x3) x2)) /\ (Peano.lt x2 x3))) = (@COND Prop y0 y1 y2).
Definition term14 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, forall y1 : Prop, forall y2 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> ((~ y0) -> x2 = y2) -> (@COND Prop x0 x1 x2) = (@COND Prop y0 y1 y2).
Definition term13 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) := forall y0 : Prop, forall y1 : a0, forall y2 : a0, (x0 = y0) -> (y0 -> x1 = y1) -> ((~ y0) -> x2 = y2) -> (@COND a0 x0 x1 x2) = (@COND a0 y0 y1 y2).
Definition term76 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : Prop) := (False -> ((x1 = (NUMERAL 0)) /\ (x2 = x3)) = ((x1 = (NUMERAL 0)) /\ (x2 = x3))) -> ((~ False) -> ((x3 = (Nat.add (Nat.mul x1 x0) x2)) /\ (Peano.lt x2 x0)) = x4) -> (@COND Prop (x0 = (NUMERAL 0)) ((x1 = (NUMERAL 0)) /\ (x2 = x3)) ((x3 = (Nat.add (Nat.mul x1 x0) x2)) /\ (Peano.lt x2 x0))) = (@COND Prop False ((x1 = (NUMERAL 0)) /\ (x2 = x3)) x4).
Definition term37 (x0 : nat) := Peano.lt x0 (NUMERAL 0).
Definition term51 (x0 : nat) := fun y0 : nat => y0 = x0.
Definition term67 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> exists y2 : nat, exists y3 : nat, (y0 = (Nat.add (Nat.mul y2 y1) y3)) /\ (Peano.lt y3 y1)) x0.
Definition term28 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : Prop) := (True -> ((x1 = (NUMERAL 0)) /\ (x2 = x3)) = ((x1 = (NUMERAL 0)) /\ (x2 = x3))) -> ((~ True) -> ((x3 = (Nat.add (Nat.mul x1 x0) x2)) /\ (Peano.lt x2 x0)) = x4) -> (@COND Prop (x0 = (NUMERAL 0)) ((x1 = (NUMERAL 0)) /\ (x2 = x3)) ((x3 = (Nat.add (Nat.mul x1 x0) x2)) /\ (Peano.lt x2 x0))) = (@COND Prop True ((x1 = (NUMERAL 0)) /\ (x2 = x3)) x4).
Definition term79 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((~ False) -> ((x0 = (Nat.add (Nat.mul x1 x3) x2)) /\ (Peano.lt x2 x3)) = ((x0 = (Nat.add (Nat.mul x1 x3) x2)) /\ (Peano.lt x2 x3))) -> (@COND Prop (x3 = (NUMERAL 0)) ((x1 = (NUMERAL 0)) /\ (x2 = x0)) ((x0 = (Nat.add (Nat.mul x1 x3) x2)) /\ (Peano.lt x2 x3))) = (@COND Prop False ((x1 = (NUMERAL 0)) /\ (x2 = x0)) ((x0 = (Nat.add (Nat.mul x1 x3) x2)) /\ (Peano.lt x2 x3))).
Definition term61 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) /\ (exists y0 : nat, y0 = x1).
Definition term12 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) (x3 : Prop) := forall y0 : a0, forall y1 : a0, (x0 = x3) -> (x3 -> x1 = y0) -> ((~ x3) -> x2 = y1) -> (@COND a0 x0 x1 x2) = (@COND a0 x3 y0 y1).
Definition term30 (x0 : nat) := Nat.mul x0 (NUMERAL 0).
Definition term38 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = (Nat.add (Nat.mul x1 (NUMERAL 0)) x2)) /\ (Peano.lt x2 (NUMERAL 0)).
Definition term84 (x0 : nat) (x1 : nat) := (~ (x1 = (NUMERAL 0))) -> (exists y0 : nat, exists y1 : nat, (x0 = (Nat.add (Nat.mul y0 x1) y1)) /\ (Peano.lt y1 x1)) = True.
Definition term72 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> (x0 = (NUMERAL 0)) = False.
Definition term73 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : Prop) (x5 : Prop) := ((x3 = (NUMERAL 0)) = False) -> (False -> ((x1 = (NUMERAL 0)) /\ (x2 = x0)) = x4) -> ((~ False) -> ((x0 = (Nat.add (Nat.mul x1 x3) x2)) /\ (Peano.lt x2 x3)) = x5) -> (@COND Prop (x3 = (NUMERAL 0)) ((x1 = (NUMERAL 0)) /\ (x2 = x0)) ((x0 = (Nat.add (Nat.mul x1 x3) x2)) /\ (Peano.lt x2 x3))) = (@COND Prop False x4 x5).
Definition term58 (x0 : nat) := fun y0 : nat => (fun y1 : nat => y1 = x0) y0.
Definition term71 (x0 : nat) (x1 : nat) := exists y0 : nat, exists y1 : nat, (x0 = (Nat.add (Nat.mul y0 x1) y1)) /\ (Peano.lt y1 x1).
Definition term65 (x0 : nat) (x1 : nat) := exists y0 : nat, exists y1 : nat, @COND Prop (x1 = (NUMERAL 0)) ((y0 = (NUMERAL 0)) /\ (y1 = x0)) ((x0 = (Nat.add (Nat.mul y0 x1) y1)) /\ (Peano.lt y1 x1)).
Definition term64 := fun y0 : nat => y0 = (NUMERAL 0).
Definition term33 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x0 x1) x2.
Definition term10 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) (x3 : Prop) (x4 : a0) (x5 : a0) := (x0 = x3) -> (x3 -> x1 = x4) -> ((~ x3) -> x2 = x5) -> (@COND a0 x0 x1 x2) = (@COND a0 x3 x4 x5).
Definition term0 (x0 : nat) := (fun y0 : Prop => y0 \/ (~ y0)) (x0 = (NUMERAL 0)).
