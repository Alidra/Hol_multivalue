Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term33 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := real_of_num (@nsum a0 (@support a0 nat Nat.add x1 x0) x1).
Definition term31 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := @FINITE a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ ((x1 y1) = (NUMERAL 0)))) y1)).
Definition term75 := real_of_num (NUMERAL 0).
Definition term15 (a0 : Type') := fun y0 : a0 -> nat => forall y1 : a0 -> Prop, (@nsum a0 y1 y0) = (@nsum a0 (@support a0 nat Nat.add y0 y1) y0).
Definition term14 (a0 : Type') := fun y0 : a0 -> nat => forall y1 : a0 -> Prop, (@nsum a0 (@support a0 nat Nat.add y0 y1) y0) = (@nsum a0 y1 y0).
Definition term5 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) := (fun y0 : a0 -> a1 => forall y1 : type1400 a1, (@support a0 a1 y1 y0 x0) = (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 ((@IN a0 y3 x0) /\ (~ ((y0 y3) = (@neutral a1 y1)))) y3))) x1.
Definition term72 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) := @eq real ((fun y0 : a0 => (fun y1 : a0 => real_of_num (x0 y1)) y0) x1).
Definition term80 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> nat) := fun y0 : a0 => @SETSPEC a0 x0 ((@IN a0 y0 x1) /\ (~ (((fun y1 : a0 => real_of_num (x2 y1)) y0) = (@neutral real real_add)))) y0.
Definition term52 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> nat) := fun y0 : a0 => @SETSPEC a0 x0 ((@IN a0 y0 x1) /\ (~ ((x2 y0) = (NUMERAL 0)))) y0.
Definition term51 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> nat) := fun y0 : a0 => @SETSPEC a0 x0 ((@IN a0 y0 x1) /\ (~ ((x2 y0) = (@neutral nat Nat.add)))) y0.
Definition term1 (x0 : nat) := forall y0 : nat, ((real_of_num x0) = (real_of_num y0)) = (x0 = y0).
Definition term3 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> a1, forall y2 : type1400 a1, (@support a0 a1 y2 y1 y0) = (@GSPEC a0 (fun y3 : a0 => exists y4 : a0, @SETSPEC a0 y3 ((@IN a0 y4 y0) /\ (~ ((y1 y4) = (@neutral a1 y2)))) y4))) x0.
Definition term10 (a0 : Type') (x0 : a0 -> nat) := fun y0 : a0 -> Prop => (@nsum a0 (@support a0 nat Nat.add x0 y0) x0) = (@nsum a0 y0 x0).
Definition term84 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := @sum a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ ((x1 y1) = (NUMERAL 0)))) y1)).
Definition term87 (a0 : Type') (x0 : a0 -> nat) := forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (real_of_num (@nsum a0 y0 x0)) = (@sum a0 y0 (fun y1 : a0 => real_of_num (x0 y1))).
Definition term79 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> nat) (x3 : a0) := @SETSPEC a0 x0 ((@IN a0 x3 x1) /\ (~ (((fun y0 : a0 => real_of_num (x2 y0)) x3) = (@neutral real real_add)))) x3.
Definition term50 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> nat) (x3 : a0) := @SETSPEC a0 x0 ((@IN a0 x3 x1) /\ (~ ((x2 x3) = (NUMERAL 0)))) x3.
Definition term49 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> nat) (x3 : a0) := @SETSPEC a0 x0 ((@IN a0 x3 x1) /\ (~ ((x2 x3) = (@neutral nat Nat.add)))) x3.
Definition term30 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@sum a0 y0 x0) = (@sum a0 (@support a0 real real_add x0 y0) x0)) x1.
Definition term28 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@nsum a0 y0 x0) = (@nsum a0 (@support a0 nat Nat.add x0 y0) x0)) x1.
Definition term35 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := @eq real (real_of_num (@nsum a0 (@support a0 nat Nat.add x1 x0) x1)).
Definition term37 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := @sum a0 (@support a0 real real_add (fun y0 : a0 => real_of_num (x1 y0)) x0) (fun y0 : a0 => real_of_num (x1 y0)).
Definition term18 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := @sum a0 (@support a0 real real_add x1 x0) x1.
Definition term68 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) := (fun y0 : a0 => (fun y1 : a0 => real_of_num (x0 y1)) y0) x1.
Definition term77 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0) := (@IN a0 x2 x0) /\ (~ (((fun y0 : a0 => real_of_num (x1 y0)) x2) = (@neutral real real_add))).
Definition term41 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) := @eq nat (x0 x1).
Definition term58 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) := @nsum a0 (@support a0 nat Nat.add x0 x1).
Definition term62 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := @eq real (real_of_num (@nsum a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ ((x1 y1) = (NUMERAL 0)))) y1)) x1)).
Definition term74 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) := @eq real (real_of_num (x0 x1)).
Definition term7 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : type1400 a1) := (fun y0 : type1400 a1 => (@support a0 a1 y0 x1 x0) = (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 x0) /\ (~ ((x1 y2) = (@neutral a1 y0)))) y2))) x2.
Definition term22 (a0 : Type') (x0 : a0 -> real) := forall y0 : a0 -> Prop, (@sum a0 y0 x0) = (@sum a0 (@support a0 real real_add x0 y0) x0).
Definition term13 (a0 : Type') (x0 : a0 -> nat) := forall y0 : a0 -> Prop, (@nsum a0 y0 x0) = (@nsum a0 (@support a0 nat Nat.add x0 y0) x0).
Definition term45 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0) := (@IN a0 x2 x0) /\ (~ ((x1 x2) = (@neutral nat Nat.add))).
Definition term44 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := and (@IN a0 x0 x1).
Definition term19 (a0 : Type') (x0 : a0 -> real) := fun y0 : a0 -> Prop => (@sum a0 (@support a0 real real_add x0 y0) x0) = (@sum a0 y0 x0).
Definition term42 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) := ~ ((x0 x1) = (@neutral nat Nat.add)).
Definition term76 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) := ~ (((fun y0 : a0 => real_of_num (x0 y0)) x1) = (@neutral real real_add)).
Definition term21 (a0 : Type') (x0 : a0 -> real) := forall y0 : a0 -> Prop, (@sum a0 (@support a0 real real_add x0 y0) x0) = (@sum a0 y0 x0).
Definition term12 (a0 : Type') (x0 : a0 -> nat) := forall y0 : a0 -> Prop, (@nsum a0 (@support a0 nat Nat.add x0 y0) x0) = (@nsum a0 y0 x0).
Definition term61 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := real_of_num (@nsum a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ ((x1 y1) = (NUMERAL 0)))) y1)) x1).
Definition term66 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term65 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := @GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ (((fun y2 : a0 => real_of_num (x1 y2)) y1) = (@neutral real real_add)))) y1).
Definition term63 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : type1627) := @GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ ((x1 y1) = (@neutral real x2)))) y1).
Definition term57 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := @GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ ((x1 y1) = (NUMERAL 0)))) y1).
Definition term40 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := @GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ ((x1 y1) = (@neutral nat Nat.add)))) y1).
Definition term39 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : type1606) := @GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ ((x1 y1) = (@neutral nat x2)))) y1).
Definition term8 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : type1400 a1) := @GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ ((x1 y1) = (@neutral a1 x2)))) y1).
Definition term67 (a0 : Type') (x0 : a0 -> real) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term78 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> nat) (x3 : a0) := @SETSPEC a0 x0 ((@IN a0 x3 x1) /\ (~ (((fun y0 : a0 => real_of_num (x2 y0)) x3) = (@neutral real real_add)))).
Definition term48 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> nat) (x3 : a0) := @SETSPEC a0 x0 ((@IN a0 x3 x1) /\ (~ ((x2 x3) = (NUMERAL 0)))).
Definition term47 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> nat) (x3 : a0) := @SETSPEC a0 x0 ((@IN a0 x3 x1) /\ (~ ((x2 x3) = (@neutral nat Nat.add)))).
Definition term32 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := real_of_num (@nsum a0 x0 x1).
Definition term73 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) := @eq real ((fun y0 : a0 => real_of_num (x0 y0)) x1).
Definition term81 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> nat) := exists y0 : a0, @SETSPEC a0 x0 ((@IN a0 y0 x1) /\ (~ (((fun y1 : a0 => real_of_num (x2 y1)) y0) = (@neutral real real_add)))) y0.
Definition term54 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> nat) := exists y0 : a0, @SETSPEC a0 x0 ((@IN a0 y0 x1) /\ (~ ((x2 y0) = (NUMERAL 0)))) y0.
Definition term53 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> nat) := exists y0 : a0, @SETSPEC a0 x0 ((@IN a0 y0 x1) /\ (~ ((x2 y0) = (@neutral nat Nat.add)))) y0.
Definition term89 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := (@FINITE a0 x0) -> (real_of_num (@nsum a0 x0 x1)) = (@sum a0 x0 (fun y0 : a0 => real_of_num (x1 y0))).
Definition term11 (a0 : Type') (x0 : a0 -> nat) := fun y0 : a0 -> Prop => (@nsum a0 y0 x0) = (@nsum a0 (@support a0 nat Nat.add x0 y0) x0).
Definition term86 (a0 : Type') (x0 : a0 -> nat) := (fun y0 : a0 -> nat => forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (real_of_num (@nsum a0 y1 y0)) = (@sum a0 y1 (fun y2 : a0 => real_of_num (y0 y2)))) x0.
Definition term29 (a0 : Type') (x0 : a0 -> real) := (fun y0 : a0 -> real => forall y1 : a0 -> Prop, (@sum a0 y1 y0) = (@sum a0 (@support a0 real real_add y0 y1) y0)) x0.
Definition term27 (a0 : Type') (x0 : a0 -> nat) := (fun y0 : a0 -> nat => forall y1 : a0 -> Prop, (@nsum a0 y1 y0) = (@nsum a0 (@support a0 nat Nat.add y0 y1) y0)) x0.
Definition term83 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) := @sum a0 (@support a0 real real_add (fun y0 : a0 => real_of_num (x0 y0)) x1).
Definition term88 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@FINITE a0 y0) -> (real_of_num (@nsum a0 y0 x0)) = (@sum a0 y0 (fun y1 : a0 => real_of_num (x0 y1)))) x1.
Definition term36 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := @sum a0 x0 (fun y0 : a0 => real_of_num (x1 y0)).
Definition term69 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) := (fun y0 : a0 => real_of_num (x0 y0)) x1.
Definition term82 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ (((fun y2 : a0 => real_of_num (x1 y2)) y1) = (@neutral real real_add)))) y1.
Definition term56 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ ((x1 y1) = (NUMERAL 0)))) y1.
Definition term55 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ ((x1 y1) = (@neutral nat Nat.add)))) y1.
Definition term38 (a0 : Type') (x0 : a0 -> nat) := fun y0 : a0 => real_of_num (x0 y0).
Definition term94 (a0 : Type') := forall y0 : a0 -> nat, forall y1 : a0 -> Prop, (@FINITE a0 (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 ((@IN a0 y3 y1) /\ (~ ((y0 y3) = (NUMERAL 0)))) y3))) -> (real_of_num (@nsum a0 y1 y0)) = (@sum a0 y1 (fun y2 : a0 => real_of_num (y0 y2))).
Definition term26 (a0 : Type') := forall y0 : a0 -> real, forall y1 : a0 -> Prop, (@sum a0 y1 y0) = (@sum a0 (@support a0 real real_add y0 y1) y0).
Definition term25 (a0 : Type') := forall y0 : a0 -> real, forall y1 : a0 -> Prop, (@sum a0 (@support a0 real real_add y0 y1) y0) = (@sum a0 y1 y0).
Definition term17 (a0 : Type') := forall y0 : a0 -> nat, forall y1 : a0 -> Prop, (@nsum a0 y1 y0) = (@nsum a0 (@support a0 nat Nat.add y0 y1) y0).
Definition term16 (a0 : Type') := forall y0 : a0 -> nat, forall y1 : a0 -> Prop, (@nsum a0 (@support a0 nat Nat.add y0 y1) y0) = (@nsum a0 y1 y0).
Definition term4 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> a1, forall y1 : type1400 a1, (@support a0 a1 y1 y0 x0) = (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 ((@IN a0 y3 x0) /\ (~ ((y0 y3) = (@neutral a1 y1)))) y3)).
Definition term60 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := @nsum a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ ((x1 y1) = (NUMERAL 0)))) y1)) x1.
Definition term9 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := @nsum a0 (@support a0 nat Nat.add x1 x0) x1.
Definition term6 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) := forall y0 : type1400 a1, (@support a0 a1 y0 x1 x0) = (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 x0) /\ (~ ((x1 y2) = (@neutral a1 y0)))) y2)).
Definition term46 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0) := (@IN a0 x2 x0) /\ (~ ((x1 x2) = (NUMERAL 0))).
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((real_of_num y0) = (real_of_num y1)) = (y0 = y1)) x0.
Definition term24 (a0 : Type') := fun y0 : a0 -> real => forall y1 : a0 -> Prop, (@sum a0 y1 y0) = (@sum a0 (@support a0 real real_add y0 y1) y0).
Definition term23 (a0 : Type') := fun y0 : a0 -> real => forall y1 : a0 -> Prop, (@sum a0 (@support a0 real real_add y0 y1) y0) = (@sum a0 y1 y0).
Definition term91 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := @eq real (@sum a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ ((x1 y1) = (NUMERAL 0)))) y1)) (fun y0 : a0 => real_of_num (x1 y0))).
Definition term92 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := (@FINITE a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ ((x1 y1) = (NUMERAL 0)))) y1))) -> (real_of_num (@nsum a0 x0 x1)) = (@sum a0 x0 (fun y0 : a0 => real_of_num (x1 y0))).
Definition term90 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := (@FINITE a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ ((x1 y1) = (NUMERAL 0)))) y1))) -> (real_of_num (@nsum a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ ((x1 y1) = (NUMERAL 0)))) y1)) x1)) = (@sum a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ ((x1 y1) = (NUMERAL 0)))) y1)) (fun y0 : a0 => real_of_num (x1 y0))).
Definition term59 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := @nsum a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ ((x1 y1) = (NUMERAL 0)))) y1)).
Definition term64 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) := @support a0 real real_add (fun y0 : a0 => real_of_num (x0 y0)) x1.
Definition term93 (a0 : Type') (x0 : a0 -> nat) := forall y0 : a0 -> Prop, (@FINITE a0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 y0) /\ (~ ((x0 y2) = (NUMERAL 0)))) y2))) -> (real_of_num (@nsum a0 y0 x0)) = (@sum a0 y0 (fun y1 : a0 => real_of_num (x0 y1))).
Definition term20 (a0 : Type') (x0 : a0 -> real) := fun y0 : a0 -> Prop => (@sum a0 y0 x0) = (@sum a0 (@support a0 real real_add x0 y0) x0).
Definition term71 (a0 : Type') (x0 : a0 -> nat) := fun y0 : a0 => (fun y1 : a0 => real_of_num (x0 y1)) y0.
Definition term34 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := @eq real (real_of_num (@nsum a0 x0 x1)).
Definition term85 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := @sum a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ ((x1 y1) = (NUMERAL 0)))) y1)) (fun y0 : a0 => real_of_num (x1 y0)).
Definition term70 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) := real_of_num (x0 x1).
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((real_of_num x0) = (real_of_num y0)) = (x0 = y0)) x1.
Definition term43 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) := ~ ((x0 x1) = (NUMERAL 0)).
