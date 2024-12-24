Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term95 (x0 : nat) (x1 : nat) := @eq Prop ((x0 = (S x1)) \/ (Peano.le x0 x1)).
Definition term103 (x0 : nat) (x1 : nat) (x2 : nat) := @SETSPEC nat x0 (Peano.le x1 x2).
Definition term14 (x0 : nat) := fun y0 : nat => @SETSPEC nat x0 (y0 = (NUMERAL 0)) y0.
Definition term13 (x0 : nat) := fun y0 : nat => @SETSPEC nat x0 (Peano.le y0 (NUMERAL 0)) y0.
Definition term7 (x0 : nat) := (fun y0 : nat => (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) x0.
Definition term71 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := (x1 = x0) \/ (@IN a0 x1 x2).
Definition term81 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term33 (x0 : nat) (x1 : nat) := exists y0 : nat, @SETSPEC nat x0 ((y0 = (S x1)) \/ (Peano.le y0 x1)) y0.
Definition term32 (x0 : nat) (x1 : nat) := exists y0 : nat, @SETSPEC nat x0 (Peano.le y0 (S x1)) y0.
Definition term16 (x0 : nat) := exists y0 : nat, @SETSPEC nat x0 (y0 = (NUMERAL 0)) y0.
Definition term15 (x0 : nat) := exists y0 : nat, @SETSPEC nat x0 (Peano.le y0 (NUMERAL 0)) y0.
Definition term116 (x0 : nat) (x1 : nat) := or (x0 = (S x1)).
Definition term70 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := @IN a0 x0 (@INSERT a0 x1 x2).
Definition term111 (x0 : nat) := fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.le y1 x0) y1.
Definition term110 (x0 : nat) := fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 ((fun y2 : nat => Peano.le y2 x0) y1) y1.
Definition term90 (x0 : nat) := fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 ((fun y2 : nat => (y2 = (S x0)) \/ (Peano.le y2 x0)) y1) y1.
Definition term64 := fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 ((fun y2 : nat => y2 = (NUMERAL 0)) y1) y1.
Definition term35 (x0 : nat) := fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 ((y1 = (S x0)) \/ (Peano.le y1 x0)) y1.
Definition term34 (x0 : nat) := fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.le y1 (S x0)) y1.
Definition term18 := fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (y1 = (NUMERAL 0)) y1.
Definition term17 := fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.le y1 (NUMERAL 0)) y1.
Definition term84 (x0 : nat) (x1 : nat) := (fun y0 : nat => (y0 = (S x0)) \/ (Peano.le y0 x0)) x1.
Definition term100 (x0 : nat) (x1 : nat) := (fun y0 : nat => Peano.le y0 x0) x1.
Definition term97 (x0 : nat) (x1 : nat) := (x0 = (S x1)) \/ (@IN nat x0 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.le y1 x1) y1))).
Definition term47 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) = (@IN a0 y0 x1).
Definition term48 (x0 : nat -> Prop) (x1 : nat -> Prop) := forall y0 : nat, (@IN nat y0 x0) = (@IN nat y0 x1).
Definition term96 (x0 : nat) (x1 : nat) := @IN nat x0 (@INSERT nat (S x1) (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.le y1 x1) y1))).
Definition term115 (x0 : nat) (x1 : nat) := @eq Prop (@IN nat x0 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.le y1 x1) y1))).
Definition term114 (x0 : nat) (x1 : nat) := @eq Prop (@IN nat x0 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 ((fun y2 : nat => Peano.le y2 x1) y1) y1))).
Definition term94 (x0 : nat) (x1 : nat) := @eq Prop (@IN nat x0 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 ((y1 = (S x1)) \/ (Peano.le y1 x1)) y1))).
Definition term93 (x0 : nat) (x1 : nat) := @eq Prop (@IN nat x0 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 ((fun y2 : nat => (y2 = (S x1)) \/ (Peano.le y2 x1)) y1) y1))).
Definition term68 (x0 : nat) := @eq Prop (@IN nat x0 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (y1 = (NUMERAL 0)) y1))).
Definition term67 (x0 : nat) := @eq Prop (@IN nat x0 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 ((fun y2 : nat => y2 = (NUMERAL 0)) y1) y1))).
Definition term29 (x0 : nat) (x1 : nat) (x2 : nat) := @SETSPEC nat x0 ((x2 = (S x1)) \/ (Peano.le x2 x1)) x2.
Definition term27 (x0 : nat) (x1 : nat) (x2 : nat) := @SETSPEC nat x0 ((x1 = (S x2)) \/ (Peano.le x1 x2)).
Definition term73 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := (x1 = x0) \/ (@IN nat x1 x2).
Definition term12 (x0 : nat) (x1 : nat) := @SETSPEC nat x0 (x1 = (NUMERAL 0)) x1.
Definition term46 := ((@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (y1 = (NUMERAL 0)) y1)) = (@INSERT nat (NUMERAL 0) (@EMPTY nat))) /\ (forall y0 : nat, (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 ((y2 = (S y0)) \/ (Peano.le y2 y0)) y2)) = (@INSERT nat (S y0) (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 (Peano.le y2 y0) y2)))).
Definition term45 := ((@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.le y1 (NUMERAL 0)) y1)) = (@INSERT nat (NUMERAL 0) (@EMPTY nat))) /\ (forall y0 : nat, (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 (Peano.le y2 (S y0)) y2)) = (@INSERT nat (S y0) (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 (Peano.le y2 y0) y2)))).
Definition term104 (x0 : nat) (x1 : nat) (x2 : nat) := @SETSPEC nat x0 ((fun y0 : nat => Peano.le y0 x1) x2) x2.
Definition term87 (x0 : nat) (x1 : nat) (x2 : nat) := @SETSPEC nat x0 ((fun y0 : nat => (y0 = (S x1)) \/ (Peano.le y0 x1)) x2) x2.
Definition term55 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 (x1 y1) y1)).
Definition term39 (x0 : nat) := @eq (nat -> Prop) (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 ((y1 = (S x0)) \/ (Peano.le y1 x0)) y1)).
Definition term38 (x0 : nat) := @eq (nat -> Prop) (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.le y1 (S x0)) y1)).
Definition term22 := @eq (nat -> Prop) (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (y1 = (NUMERAL 0)) y1)).
Definition term21 := @eq (nat -> Prop) (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.le y1 (NUMERAL 0)) y1)).
Definition term102 (x0 : nat) (x1 : nat) (x2 : nat) := @SETSPEC nat x0 ((fun y0 : nat => Peano.le y0 x1) x2).
Definition term50 := and (forall y0 : nat, (@IN nat y0 (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 (y2 = (NUMERAL 0)) y2))) = (@IN nat y0 (@INSERT nat (NUMERAL 0) (@EMPTY nat)))).
Definition term26 (x0 : nat) (x1 : nat) (x2 : nat) := @SETSPEC nat x0 (Peano.le x1 (S x2)).
Definition term85 (x0 : nat) := fun y0 : nat => (y0 = (S x0)) \/ (Peano.le y0 x0).
Definition term76 (x0 : nat) := or (x0 = (NUMERAL 0)).
Definition term11 (x0 : nat) (x1 : nat) := @SETSPEC nat x0 (Peano.le x1 (NUMERAL 0)) x1.
Definition term53 := forall y0 : nat, forall y1 : nat, (@IN nat y1 (@GSPEC nat (fun y2 : nat => exists y3 : nat, @SETSPEC nat y2 ((y3 = (S y0)) \/ (Peano.le y3 y0)) y3))) = (@IN nat y1 (@INSERT nat (S y0) (@GSPEC nat (fun y2 : nat => exists y3 : nat, @SETSPEC nat y2 (Peano.le y3 y0) y3)))).
Definition term0 := forall y0 : nat, forall y1 : nat, (Peano.le y0 (S y1)) = ((y0 = (S y1)) \/ (Peano.le y0 y1)).
Definition term72 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := @IN nat x0 (@INSERT nat x1 x2).
Definition term80 := forall y0 : nat, True.
Definition term42 := fun y0 : nat => (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 ((y2 = (S y0)) \/ (Peano.le y2 y0)) y2)) = (@INSERT nat (S y0) (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 (Peano.le y2 y0) y2))).
Definition term41 := fun y0 : nat => (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 (Peano.le y2 (S y0)) y2)) = (@INSERT nat (S y0) (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 (Peano.le y2 y0) y2))).
Definition term105 (x0 : nat) (x1 : nat) (x2 : nat) := @SETSPEC nat x0 (Peano.le x2 x1) x2.
Definition term86 (x0 : nat) (x1 : nat) (x2 : nat) := @SETSPEC nat x0 ((fun y0 : nat => (y0 = (S x1)) \/ (Peano.le y0 x1)) x2).
Definition term79 := fun y0 : nat => True.
Definition term2 (x0 : nat) := forall y0 : nat, (Peano.le x0 (S y0)) = ((x0 = (S y0)) \/ (Peano.le x0 y0)).
Definition term109 (x0 : nat) (x1 : nat) := exists y0 : nat, @SETSPEC nat x0 (Peano.le y0 x1) y0.
Definition term101 (x0 : nat) := fun y0 : nat => Peano.le y0 x0.
Definition term44 := forall y0 : nat, (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 ((y2 = (S y0)) \/ (Peano.le y2 y0)) y2)) = (@INSERT nat (S y0) (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 (Peano.le y2 y0) y2))).
Definition term43 := forall y0 : nat, (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 (Peano.le y2 (S y0)) y2)) = (@INSERT nat (S y0) (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 (Peano.le y2 y0) y2))).
Definition term78 := fun y0 : nat => (@IN nat y0 (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 (y2 = (NUMERAL 0)) y2))) = (@IN nat y0 (@INSERT nat (NUMERAL 0) (@EMPTY nat))).
Definition term54 := (forall y0 : nat, (@IN nat y0 (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 (y2 = (NUMERAL 0)) y2))) = (@IN nat y0 (@INSERT nat (NUMERAL 0) (@EMPTY nat)))) /\ (forall y0 : nat, forall y1 : nat, (@IN nat y1 (@GSPEC nat (fun y2 : nat => exists y3 : nat, @SETSPEC nat y2 ((y3 = (S y0)) \/ (Peano.le y3 y0)) y3))) = (@IN nat y1 (@INSERT nat (S y0) (@GSPEC nat (fun y2 : nat => exists y3 : nat, @SETSPEC nat y2 (Peano.le y3 y0) y3))))).
Definition term58 (x0 : nat) := (fun y0 : nat => y0 = (NUMERAL 0)) x0.
Definition term117 (x0 : nat) := fun y0 : nat => (@IN nat y0 (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 ((y2 = (S x0)) \/ (Peano.le y2 x0)) y2))) = (@IN nat y0 (@INSERT nat (S x0) (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 (Peano.le y2 x0) y2)))).
Definition term28 (x0 : nat) (x1 : nat) (x2 : nat) := @SETSPEC nat x0 (Peano.le x2 (S x1)) x2.
Definition term31 (x0 : nat) (x1 : nat) := fun y0 : nat => @SETSPEC nat x0 ((y0 = (S x1)) \/ (Peano.le y0 x1)) y0.
Definition term23 := @INSERT nat (NUMERAL 0) (@EMPTY nat).
Definition term5 (x0 : nat) (x1 : nat) := (x0 = (S x1)) \/ (Peano.le x0 x1).
Definition term1 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y0 (S y1)) = ((y0 = (S y1)) \/ (Peano.le y0 y1))) x0.
Definition term107 (x0 : nat) (x1 : nat) := fun y0 : nat => @SETSPEC nat x0 (Peano.le y0 x1) y0.
Definition term10 (x0 : nat) (x1 : nat) := @SETSPEC nat x0 (x1 = (NUMERAL 0)).
Definition term51 (x0 : nat) := forall y0 : nat, (@IN nat y0 (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 ((y2 = (S x0)) \/ (Peano.le y2 x0)) y2))) = (@IN nat y0 (@INSERT nat (S x0) (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 (Peano.le y2 x0) y2)))).
Definition term30 (x0 : nat) (x1 : nat) := fun y0 : nat => @SETSPEC nat x0 (Peano.le y0 (S x1)) y0.
Definition term77 (x0 : nat) := (x0 = (NUMERAL 0)) \/ False.
Definition term6 := forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0)).
Definition term75 (x0 : nat) := (x0 = (NUMERAL 0)) \/ (@IN nat x0 (@EMPTY nat)).
Definition term113 (x0 : nat) (x1 : nat) := @IN nat x0 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.le y1 x1) y1)).
Definition term99 (x0 : nat) (x1 : nat) := @IN nat x0 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 ((fun y2 : nat => Peano.le y2 x1) y1) y1)).
Definition term92 (x0 : nat) (x1 : nat) := @IN nat x0 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 ((y1 = (S x1)) \/ (Peano.le y1 x1)) y1)).
Definition term83 (x0 : nat) (x1 : nat) := @IN nat x0 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 ((fun y2 : nat => (y2 = (S x1)) \/ (Peano.le y2 x1)) y1) y1)).
Definition term66 (x0 : nat) := @IN nat x0 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (y1 = (NUMERAL 0)) y1)).
Definition term57 (x0 : nat) := @IN nat x0 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 ((fun y2 : nat => y2 = (NUMERAL 0)) y1) y1)).
Definition term56 (x0 : nat) (x1 : nat -> Prop) := @IN nat x0 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (x1 y1) y1)).
Definition term82 (x0 : Prop) := forall y0 : nat, x0.
Definition term59 := fun y0 : nat => y0 = (NUMERAL 0).
Definition term40 (x0 : nat) := @INSERT nat (S x0) (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.le y1 x0) y1)).
Definition term108 (x0 : nat) (x1 : nat) := exists y0 : nat, @SETSPEC nat x0 ((fun y1 : nat => Peano.le y1 x1) y0) y0.
Definition term89 (x0 : nat) (x1 : nat) := exists y0 : nat, @SETSPEC nat x0 ((fun y1 : nat => (y1 = (S x1)) \/ (Peano.le y1 x1)) y0) y0.
Definition term63 (x0 : nat) := exists y0 : nat, @SETSPEC nat x0 ((fun y1 : nat => y1 = (NUMERAL 0)) y0) y0.
Definition term9 (x0 : nat) (x1 : nat) := @SETSPEC nat x0 (Peano.le x1 (NUMERAL 0)).
Definition term49 := forall y0 : nat, (@IN nat y0 (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 (y2 = (NUMERAL 0)) y2))) = (@IN nat y0 (@INSERT nat (NUMERAL 0) (@EMPTY nat))).
Definition term106 (x0 : nat) (x1 : nat) := fun y0 : nat => @SETSPEC nat x0 ((fun y1 : nat => Peano.le y1 x1) y0) y0.
Definition term88 (x0 : nat) (x1 : nat) := fun y0 : nat => @SETSPEC nat x0 ((fun y1 : nat => (y1 = (S x1)) \/ (Peano.le y1 x1)) y0) y0.
Definition term62 (x0 : nat) := fun y0 : nat => @SETSPEC nat x0 ((fun y1 : nat => y1 = (NUMERAL 0)) y0) y0.
Definition term60 (x0 : nat) (x1 : nat) := @SETSPEC nat x0 ((fun y0 : nat => y0 = (NUMERAL 0)) x1).
Definition term8 (x0 : nat) := Peano.le x0 (NUMERAL 0).
Definition term3 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le x0 (S y0)) = ((x0 = (S y0)) \/ (Peano.le x0 y0))) x1.
Definition term4 (x0 : nat) (x1 : nat) := Peano.le x0 (S x1).
Definition term74 (x0 : nat) := @IN nat x0 (@INSERT nat (NUMERAL 0) (@EMPTY nat)).
Definition term69 (x0 : nat) := @eq Prop (x0 = (NUMERAL 0)).
Definition term25 := and ((@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (y1 = (NUMERAL 0)) y1)) = (@INSERT nat (NUMERAL 0) (@EMPTY nat))).
Definition term24 := and ((@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.le y1 (NUMERAL 0)) y1)) = (@INSERT nat (NUMERAL 0) (@EMPTY nat))).
Definition term52 := fun y0 : nat => forall y1 : nat, (@IN nat y1 (@GSPEC nat (fun y2 : nat => exists y3 : nat, @SETSPEC nat y2 ((y3 = (S y0)) \/ (Peano.le y3 y0)) y3))) = (@IN nat y1 (@INSERT nat (S y0) (@GSPEC nat (fun y2 : nat => exists y3 : nat, @SETSPEC nat y2 (Peano.le y3 y0) y3)))).
Definition term112 (x0 : nat) := @GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 ((fun y2 : nat => Peano.le y2 x0) y1) y1).
Definition term98 (x0 : nat) := @GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.le y1 x0) y1).
Definition term91 (x0 : nat) := @GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 ((fun y2 : nat => (y2 = (S x0)) \/ (Peano.le y2 x0)) y1) y1).
Definition term65 := @GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 ((fun y2 : nat => y2 = (NUMERAL 0)) y1) y1).
Definition term37 (x0 : nat) := @GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 ((y1 = (S x0)) \/ (Peano.le y1 x0)) y1).
Definition term36 (x0 : nat) := @GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.le y1 (S x0)) y1).
Definition term20 := @GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (y1 = (NUMERAL 0)) y1).
Definition term19 := @GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.le y1 (NUMERAL 0)) y1).
Definition term61 (x0 : nat) (x1 : nat) := @SETSPEC nat x0 ((fun y0 : nat => y0 = (NUMERAL 0)) x1) x1.
