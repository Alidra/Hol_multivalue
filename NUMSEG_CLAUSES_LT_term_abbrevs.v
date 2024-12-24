Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term57 (x0 : nat) (x1 : nat) := @SETSPEC nat x0 ((fun y0 : nat => False) x1).
Definition term43 := ((@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 False y1)) = (@EMPTY nat)) /\ (forall y0 : nat, (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 ((y2 = y0) \/ (Peano.lt y2 y0)) y2)) = (@INSERT nat y0 (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 (Peano.lt y2 y0) y2)))).
Definition term42 := ((@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.lt y1 (NUMERAL 0)) y1)) = (@EMPTY nat)) /\ (forall y0 : nat, (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 (Peano.lt y2 (S y0)) y2)) = (@INSERT nat y0 (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 (Peano.lt y2 y0) y2)))).
Definition term37 (x0 : nat) := @INSERT nat x0 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.lt y1 x0) y1)).
Definition term59 (x0 : nat) := fun y0 : nat => @SETSPEC nat x0 ((fun y1 : nat => False) y0) y0.
Definition term16 := fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 False y1.
Definition term11 (x0 : nat) := fun y0 : nat => @SETSPEC nat x0 (Peano.lt y0 (NUMERAL 0)) y0.
Definition term83 (x0 : nat) (x1 : nat) := @eq Prop ((x0 = x1) \/ (Peano.lt x0 x1)).
Definition term85 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := (x1 = x0) \/ (@IN a0 x1 x2).
Definition term69 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term24 (x0 : nat) (x1 : nat) (x2 : nat) := @SETSPEC nat x0 ((x1 = x2) \/ (Peano.lt x1 x2)).
Definition term30 (x0 : nat) (x1 : nat) := exists y0 : nat, @SETSPEC nat x0 ((y0 = x1) \/ (Peano.lt y0 x1)) y0.
Definition term29 (x0 : nat) (x1 : nat) := exists y0 : nat, @SETSPEC nat x0 (Peano.lt y0 (S x1)) y0.
Definition term13 (x0 : nat) := exists y0 : nat, @SETSPEC nat x0 (Peano.lt y0 (NUMERAL 0)) y0.
Definition term84 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := @IN a0 x0 (@INSERT a0 x1 x2).
Definition term103 (x0 : nat) := fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.lt y1 x0) y1.
Definition term102 (x0 : nat) := fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 ((fun y2 : nat => Peano.lt y2 x0) y1) y1.
Definition term78 (x0 : nat) := fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 ((fun y2 : nat => (y2 = x0) \/ (Peano.lt y2 x0)) y1) y1.
Definition term61 := fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 ((fun y2 : nat => False) y1) y1.
Definition term32 (x0 : nat) := fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 ((y1 = x0) \/ (Peano.lt y1 x0)) y1.
Definition term31 (x0 : nat) := fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.lt y1 (S x0)) y1.
Definition term15 := fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.lt y1 (NUMERAL 0)) y1.
Definition term72 (x0 : nat) (x1 : nat) := (fun y0 : nat => (y0 = x0) \/ (Peano.lt y0 x0)) x1.
Definition term44 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) = (@IN a0 y0 x1).
Definition term25 (x0 : nat) (x1 : nat) (x2 : nat) := @SETSPEC nat x0 (Peano.lt x2 (S x1)) x2.
Definition term45 (x0 : nat -> Prop) (x1 : nat -> Prop) := forall y0 : nat, (@IN nat y0 x0) = (@IN nat y0 x1).
Definition term6 := forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False.
Definition term10 (x0 : nat) (x1 : nat) := @SETSPEC nat x0 (Peano.lt x1 (NUMERAL 0)) x1.
Definition term107 (x0 : nat) (x1 : nat) := @eq Prop (@IN nat x0 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.lt y1 x1) y1))).
Definition term106 (x0 : nat) (x1 : nat) := @eq Prop (@IN nat x0 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 ((fun y2 : nat => Peano.lt y2 x1) y1) y1))).
Definition term82 (x0 : nat) (x1 : nat) := @eq Prop (@IN nat x0 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 ((y1 = x1) \/ (Peano.lt y1 x1)) y1))).
Definition term81 (x0 : nat) (x1 : nat) := @eq Prop (@IN nat x0 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 ((fun y2 : nat => (y2 = x1) \/ (Peano.lt y2 x1)) y1) y1))).
Definition term65 (x0 : nat) := @eq Prop (@IN nat x0 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 False y1))).
Definition term64 (x0 : nat) := @eq Prop (@IN nat x0 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 ((fun y2 : nat => False) y1) y1))).
Definition term39 := fun y0 : nat => (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 ((y2 = y0) \/ (Peano.lt y2 y0)) y2)) = (@INSERT nat y0 (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 (Peano.lt y2 y0) y2))).
Definition term38 := fun y0 : nat => (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 (Peano.lt y2 (S y0)) y2)) = (@INSERT nat y0 (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 (Peano.lt y2 y0) y2))).
Definition term87 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := (x1 = x0) \/ (@IN nat x1 x2).
Definition term5 (x0 : nat) (x1 : nat) := (x0 = x1) \/ (Peano.lt x0 x1).
Definition term23 (x0 : nat) (x1 : nat) (x2 : nat) := @SETSPEC nat x0 (Peano.lt x1 (S x2)).
Definition term96 (x0 : nat) (x1 : nat) (x2 : nat) := @SETSPEC nat x0 ((fun y0 : nat => Peano.lt y0 x1) x2) x2.
Definition term75 (x0 : nat) (x1 : nat) (x2 : nat) := @SETSPEC nat x0 ((fun y0 : nat => (y0 = x1) \/ (Peano.lt y0 x1)) x2) x2.
Definition term97 (x0 : nat) (x1 : nat) (x2 : nat) := @SETSPEC nat x0 (Peano.lt x2 x1) x2.
Definition term52 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 (x1 y1) y1)).
Definition term36 (x0 : nat) := @eq (nat -> Prop) (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 ((y1 = x0) \/ (Peano.lt y1 x0)) y1)).
Definition term35 (x0 : nat) := @eq (nat -> Prop) (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.lt y1 (S x0)) y1)).
Definition term20 := @eq (nat -> Prop) (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 False y1)).
Definition term19 := @eq (nat -> Prop) (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.lt y1 (NUMERAL 0)) y1)).
Definition term94 (x0 : nat) (x1 : nat) (x2 : nat) := @SETSPEC nat x0 ((fun y0 : nat => Peano.lt y0 x1) x2).
Definition term7 (x0 : nat) := (fun y0 : nat => (Peano.lt y0 (NUMERAL 0)) = False) x0.
Definition term47 := and (forall y0 : nat, (@IN nat y0 (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 False y2))) = (@IN nat y0 (@EMPTY nat))).
Definition term93 (x0 : nat) := fun y0 : nat => Peano.lt y0 x0.
Definition term109 (x0 : nat) := fun y0 : nat => (@IN nat y0 (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 ((y2 = x0) \/ (Peano.lt y2 x0)) y2))) = (@IN nat y0 (@INSERT nat x0 (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 (Peano.lt y2 x0) y2)))).
Definition term12 (x0 : nat) := fun y0 : nat => @SETSPEC nat x0 False y0.
Definition term22 := and ((@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 False y1)) = (@EMPTY nat)).
Definition term21 := and ((@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.lt y1 (NUMERAL 0)) y1)) = (@EMPTY nat)).
Definition term50 := forall y0 : nat, forall y1 : nat, (@IN nat y1 (@GSPEC nat (fun y2 : nat => exists y3 : nat, @SETSPEC nat y2 ((y3 = y0) \/ (Peano.lt y3 y0)) y3))) = (@IN nat y1 (@INSERT nat y0 (@GSPEC nat (fun y2 : nat => exists y3 : nat, @SETSPEC nat y2 (Peano.lt y3 y0) y3)))).
Definition term0 := forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)).
Definition term26 (x0 : nat) (x1 : nat) (x2 : nat) := @SETSPEC nat x0 ((x2 = x1) \/ (Peano.lt x2 x1)) x2.
Definition term58 (x0 : nat) (x1 : nat) := @SETSPEC nat x0 ((fun y0 : nat => False) x1) x1.
Definition term86 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := @IN nat x0 (@INSERT nat x1 x2).
Definition term4 (x0 : nat) (x1 : nat) := Peano.lt x0 (S x1).
Definition term68 := forall y0 : nat, True.
Definition term92 (x0 : nat) (x1 : nat) := (fun y0 : nat => Peano.lt y0 x0) x1.
Definition term89 (x0 : nat) (x1 : nat) := (x0 = x1) \/ (@IN nat x0 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.lt y1 x1) y1))).
Definition term74 (x0 : nat) (x1 : nat) (x2 : nat) := @SETSPEC nat x0 ((fun y0 : nat => (y0 = x1) \/ (Peano.lt y0 x1)) x2).
Definition term67 := fun y0 : nat => True.
Definition term2 (x0 : nat) := forall y0 : nat, (Peano.lt x0 (S y0)) = ((x0 = y0) \/ (Peano.lt x0 y0)).
Definition term101 (x0 : nat) (x1 : nat) := exists y0 : nat, @SETSPEC nat x0 (Peano.lt y0 x1) y0.
Definition term14 (x0 : nat) := exists y0 : nat, @SETSPEC nat x0 False y0.
Definition term66 := fun y0 : nat => (@IN nat y0 (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 False y2))) = (@IN nat y0 (@EMPTY nat)).
Definition term56 := fun y0 : nat => False.
Definition term51 := (forall y0 : nat, (@IN nat y0 (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 False y2))) = (@IN nat y0 (@EMPTY nat))) /\ (forall y0 : nat, forall y1 : nat, (@IN nat y1 (@GSPEC nat (fun y2 : nat => exists y3 : nat, @SETSPEC nat y2 ((y3 = y0) \/ (Peano.lt y3 y0)) y3))) = (@IN nat y1 (@INSERT nat y0 (@GSPEC nat (fun y2 : nat => exists y3 : nat, @SETSPEC nat y2 (Peano.lt y3 y0) y3))))).
Definition term3 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt x0 (S y0)) = ((x0 = y0) \/ (Peano.lt x0 y0))) x1.
Definition term95 (x0 : nat) (x1 : nat) (x2 : nat) := @SETSPEC nat x0 (Peano.lt x1 x2).
Definition term8 (x0 : nat) := Peano.lt x0 (NUMERAL 0).
Definition term28 (x0 : nat) (x1 : nat) := fun y0 : nat => @SETSPEC nat x0 ((y0 = x1) \/ (Peano.lt y0 x1)) y0.
Definition term1 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1))) x0.
Definition term55 (x0 : nat) := (fun y0 : nat => False) x0.
Definition term99 (x0 : nat) (x1 : nat) := fun y0 : nat => @SETSPEC nat x0 (Peano.lt y0 x1) y0.
Definition term9 (x0 : nat) (x1 : nat) := @SETSPEC nat x0 (Peano.lt x1 (NUMERAL 0)).
Definition term48 (x0 : nat) := forall y0 : nat, (@IN nat y0 (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 ((y2 = x0) \/ (Peano.lt y2 x0)) y2))) = (@IN nat y0 (@INSERT nat x0 (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 (Peano.lt y2 x0) y2)))).
Definition term27 (x0 : nat) (x1 : nat) := fun y0 : nat => @SETSPEC nat x0 (Peano.lt y0 (S x1)) y0.
Definition term73 (x0 : nat) := fun y0 : nat => (y0 = x0) \/ (Peano.lt y0 x0).
Definition term105 (x0 : nat) (x1 : nat) := @IN nat x0 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.lt y1 x1) y1)).
Definition term91 (x0 : nat) (x1 : nat) := @IN nat x0 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 ((fun y2 : nat => Peano.lt y2 x1) y1) y1)).
Definition term80 (x0 : nat) (x1 : nat) := @IN nat x0 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 ((y1 = x1) \/ (Peano.lt y1 x1)) y1)).
Definition term71 (x0 : nat) (x1 : nat) := @IN nat x0 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 ((fun y2 : nat => (y2 = x1) \/ (Peano.lt y2 x1)) y1) y1)).
Definition term63 (x0 : nat) := @IN nat x0 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 False y1)).
Definition term54 (x0 : nat) := @IN nat x0 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 ((fun y2 : nat => False) y1) y1)).
Definition term53 (x0 : nat) (x1 : nat -> Prop) := @IN nat x0 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (x1 y1) y1)).
Definition term70 (x0 : Prop) := forall y0 : nat, x0.
Definition term88 (x0 : nat) (x1 : nat) := @IN nat x0 (@INSERT nat x1 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.lt y1 x1) y1))).
Definition term100 (x0 : nat) (x1 : nat) := exists y0 : nat, @SETSPEC nat x0 ((fun y1 : nat => Peano.lt y1 x1) y0) y0.
Definition term77 (x0 : nat) (x1 : nat) := exists y0 : nat, @SETSPEC nat x0 ((fun y1 : nat => (y1 = x1) \/ (Peano.lt y1 x1)) y0) y0.
Definition term60 (x0 : nat) := exists y0 : nat, @SETSPEC nat x0 ((fun y1 : nat => False) y0) y0.
Definition term46 := forall y0 : nat, (@IN nat y0 (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 False y2))) = (@IN nat y0 (@EMPTY nat)).
Definition term98 (x0 : nat) (x1 : nat) := fun y0 : nat => @SETSPEC nat x0 ((fun y1 : nat => Peano.lt y1 x1) y0) y0.
Definition term76 (x0 : nat) (x1 : nat) := fun y0 : nat => @SETSPEC nat x0 ((fun y1 : nat => (y1 = x1) \/ (Peano.lt y1 x1)) y0) y0.
Definition term108 (x0 : nat) (x1 : nat) := or (x0 = x1).
Definition term49 := fun y0 : nat => forall y1 : nat, (@IN nat y1 (@GSPEC nat (fun y2 : nat => exists y3 : nat, @SETSPEC nat y2 ((y3 = y0) \/ (Peano.lt y3 y0)) y3))) = (@IN nat y1 (@INSERT nat y0 (@GSPEC nat (fun y2 : nat => exists y3 : nat, @SETSPEC nat y2 (Peano.lt y3 y0) y3)))).
Definition term104 (x0 : nat) := @GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 ((fun y2 : nat => Peano.lt y2 x0) y1) y1).
Definition term90 (x0 : nat) := @GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.lt y1 x0) y1).
Definition term79 (x0 : nat) := @GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 ((fun y2 : nat => (y2 = x0) \/ (Peano.lt y2 x0)) y1) y1).
Definition term62 := @GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 ((fun y2 : nat => False) y1) y1).
Definition term34 (x0 : nat) := @GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 ((y1 = x0) \/ (Peano.lt y1 x0)) y1).
Definition term33 (x0 : nat) := @GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.lt y1 (S x0)) y1).
Definition term18 := @GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 False y1).
Definition term17 := @GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.lt y1 (NUMERAL 0)) y1).
Definition term41 := forall y0 : nat, (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 ((y2 = y0) \/ (Peano.lt y2 y0)) y2)) = (@INSERT nat y0 (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 (Peano.lt y2 y0) y2))).
Definition term40 := forall y0 : nat, (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 (Peano.lt y2 (S y0)) y2)) = (@INSERT nat y0 (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 (Peano.lt y2 y0) y2))).
