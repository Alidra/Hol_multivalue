Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term48 (x0 : nat) (x1 : nat) (x2 : nat -> nat) := @COND nat (Peano.le x0 (S x1)) (Nat.add (@iterate nat nat Nat.add (dotdot x0 x1) x2) (x2 (S x1))) (@iterate nat nat Nat.add (dotdot x0 x1) x2).
Definition term49 (x0 : nat) (x1 : nat -> nat) := fun y0 : nat => (@nsum nat (dotdot x0 (S y0)) x1) = (@COND nat (Peano.le x0 (S y0)) (Nat.add (@nsum nat (dotdot x0 y0) x1) (x1 (S y0))) (@nsum nat (dotdot x0 y0) x1)).
Definition term44 (x0 : nat) (x1 : nat) := @COND nat (Peano.le x0 (S x1)).
Definition term10 (x0 : nat -> nat) := fun y0 : nat => (@iterate nat nat Nat.add (dotdot y0 (NUMERAL 0)) x0) = (@COND nat (y0 = (NUMERAL 0)) (x0 (NUMERAL 0)) (@neutral nat Nat.add)).
Definition term38 (x0 : nat) (x1 : nat) (x2 : nat -> nat) := @iterate nat nat Nat.add (dotdot x0 x1) x2.
Definition term11 (x0 : nat -> nat) := fun y0 : nat => (@iterate nat nat Nat.add (dotdot y0 (NUMERAL 0)) x0) = (@COND nat (y0 = (NUMERAL 0)) (x0 (NUMERAL 0)) (NUMERAL 0)).
Definition term35 (x0 : nat) (x1 : nat) := @nsum nat (dotdot x0 x1).
Definition term42 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := Nat.add (@nsum nat (dotdot x0 x2) x1) (x1 (S x2)).
Definition term52 (x0 : nat) (x1 : nat -> nat) := forall y0 : nat, (@iterate nat nat Nat.add (dotdot x0 (S y0)) x1) = (@COND nat (Peano.le x0 (S y0)) (Nat.add (@iterate nat nat Nat.add (dotdot x0 y0) x1) (x1 (S y0))) (@iterate nat nat Nat.add (dotdot x0 y0) x1)).
Definition term51 (x0 : nat) (x1 : nat -> nat) := forall y0 : nat, (@nsum nat (dotdot x0 (S y0)) x1) = (@COND nat (Peano.le x0 (S y0)) (Nat.add (@nsum nat (dotdot x0 y0) x1) (x1 (S y0))) (@nsum nat (dotdot x0 y0) x1)).
Definition term6 (x0 : nat) (x1 : nat -> nat) := @COND nat (x0 = (NUMERAL 0)) (x1 (NUMERAL 0)) (@neutral nat Nat.add).
Definition term58 (x0 : nat -> nat) := ((forall y0 : nat, (@iterate nat nat Nat.add (dotdot y0 (NUMERAL 0)) x0) = (@COND nat (y0 = (NUMERAL 0)) (x0 (NUMERAL 0)) (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, (@iterate nat nat Nat.add (dotdot y0 (S y1)) x0) = (@COND nat (Peano.le y0 (S y1)) (Nat.add (@iterate nat nat Nat.add (dotdot y0 y1) x0) (x0 (S y1))) (@iterate nat nat Nat.add (dotdot y0 y1) x0)))) -> (forall y0 : nat, (@iterate nat nat Nat.add (dotdot y0 (NUMERAL 0)) x0) = (@COND nat (y0 = (NUMERAL 0)) (x0 (NUMERAL 0)) (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, (@iterate nat nat Nat.add (dotdot y0 (S y1)) x0) = (@COND nat (Peano.le y0 (S y1)) (Nat.add (@iterate nat nat Nat.add (dotdot y0 y1) x0) (x0 (S y1))) (@iterate nat nat Nat.add (dotdot y0 y1) x0))).
Definition term57 (x0 : nat -> nat) := ((forall y0 : nat, (@iterate nat nat Nat.add (dotdot y0 (NUMERAL 0)) x0) = (@COND nat (y0 = (NUMERAL 0)) (x0 (NUMERAL 0)) (@neutral nat Nat.add))) /\ (forall y0 : nat, forall y1 : nat, (@iterate nat nat Nat.add (dotdot y0 (S y1)) x0) = (@COND nat (Peano.le y0 (S y1)) (Nat.add (@iterate nat nat Nat.add (dotdot y0 y1) x0) (x0 (S y1))) (@iterate nat nat Nat.add (dotdot y0 y1) x0)))) -> (forall y0 : nat, (@nsum nat (dotdot y0 (NUMERAL 0)) x0) = (@COND nat (y0 = (NUMERAL 0)) (x0 (NUMERAL 0)) (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, (@nsum nat (dotdot y0 (S y1)) x0) = (@COND nat (Peano.le y0 (S y1)) (Nat.add (@nsum nat (dotdot y0 y1) x0) (x0 (S y1))) (@nsum nat (dotdot y0 y1) x0))).
Definition term24 (x0 : nat) (x1 : nat -> nat) := @eq nat (@nsum nat (dotdot x0 (NUMERAL 0)) x1).
Definition term29 (x0 : nat) (x1 : nat) := @nsum nat (dotdot x0 (S x1)).
Definition term21 (x0 : nat) := @nsum nat (dotdot x0 (NUMERAL 0)).
Definition term26 (x0 : nat -> nat) := forall y0 : nat, (@nsum nat (dotdot y0 (NUMERAL 0)) x0) = (@COND nat (y0 = (NUMERAL 0)) (x0 (NUMERAL 0)) (NUMERAL 0)).
Definition term13 (x0 : nat -> nat) := forall y0 : nat, (@iterate nat nat Nat.add (dotdot y0 (NUMERAL 0)) x0) = (@COND nat (y0 = (NUMERAL 0)) (x0 (NUMERAL 0)) (NUMERAL 0)).
Definition term12 (x0 : nat -> nat) := forall y0 : nat, (@iterate nat nat Nat.add (dotdot y0 (NUMERAL 0)) x0) = (@COND nat (y0 = (NUMERAL 0)) (x0 (NUMERAL 0)) (@neutral nat Nat.add)).
Definition term22 (x0 : nat) := @iterate nat nat Nat.add (dotdot x0 (NUMERAL 0)).
Definition term28 (x0 : nat) (x1 : nat) := dotdot x0 (S x1).
Definition term40 (x0 : nat) (x1 : nat) (x2 : nat -> nat) := Nat.add (@iterate nat nat Nat.add (dotdot x0 x1) x2).
Definition term3 (x0 : nat -> nat) := (@monoidal nat Nat.add) -> (forall y0 : nat, (@iterate nat nat Nat.add (dotdot y0 (NUMERAL 0)) x0) = (@COND nat (y0 = (NUMERAL 0)) (x0 (NUMERAL 0)) (@neutral nat Nat.add))) /\ (forall y0 : nat, forall y1 : nat, (@iterate nat nat Nat.add (dotdot y0 (S y1)) x0) = (@COND nat (Peano.le y0 (S y1)) (Nat.add (@iterate nat nat Nat.add (dotdot y0 y1) x0) (x0 (S y1))) (@iterate nat nat Nat.add (dotdot y0 y1) x0))).
Definition term46 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := @COND nat (Peano.le x0 (S x2)) (Nat.add (@iterate nat nat Nat.add (dotdot x0 x2) x1) (x1 (S x2))).
Definition term9 (x0 : nat) (x1 : nat -> nat) := @iterate nat nat Nat.add (dotdot x0 (NUMERAL 0)) x1.
Definition term43 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := Nat.add (@iterate nat nat Nat.add (dotdot x0 x2) x1) (x1 (S x2)).
Definition term39 (x0 : nat) (x1 : nat) (x2 : nat -> nat) := Nat.add (@nsum nat (dotdot x0 x1) x2).
Definition term45 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := @COND nat (Peano.le x0 (S x2)) (Nat.add (@nsum nat (dotdot x0 x2) x1) (x1 (S x2))).
Definition term27 (x0 : nat -> nat) := and (forall y0 : nat, (@nsum nat (dotdot y0 (NUMERAL 0)) x0) = (@COND nat (y0 = (NUMERAL 0)) (x0 (NUMERAL 0)) (NUMERAL 0))).
Definition term15 (x0 : nat -> nat) := and (forall y0 : nat, (@iterate nat nat Nat.add (dotdot y0 (NUMERAL 0)) x0) = (@COND nat (y0 = (NUMERAL 0)) (x0 (NUMERAL 0)) (NUMERAL 0))).
Definition term14 (x0 : nat -> nat) := and (forall y0 : nat, (@iterate nat nat Nat.add (dotdot y0 (NUMERAL 0)) x0) = (@COND nat (y0 = (NUMERAL 0)) (x0 (NUMERAL 0)) (@neutral nat Nat.add))).
Definition term32 (x0 : nat) (x1 : nat) (x2 : nat -> nat) := @iterate nat nat Nat.add (dotdot x0 (S x1)) x2.
Definition term19 (x0 : nat -> nat) := imp ((forall y0 : nat, (@iterate nat nat Nat.add (dotdot y0 (NUMERAL 0)) x0) = (@COND nat (y0 = (NUMERAL 0)) (x0 (NUMERAL 0)) (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, (@iterate nat nat Nat.add (dotdot y0 (S y1)) x0) = (@COND nat (Peano.le y0 (S y1)) (Nat.add (@iterate nat nat Nat.add (dotdot y0 y1) x0) (x0 (S y1))) (@iterate nat nat Nat.add (dotdot y0 y1) x0)))).
Definition term18 (x0 : nat -> nat) := imp ((forall y0 : nat, (@iterate nat nat Nat.add (dotdot y0 (NUMERAL 0)) x0) = (@COND nat (y0 = (NUMERAL 0)) (x0 (NUMERAL 0)) (@neutral nat Nat.add))) /\ (forall y0 : nat, forall y1 : nat, (@iterate nat nat Nat.add (dotdot y0 (S y1)) x0) = (@COND nat (Peano.le y0 (S y1)) (Nat.add (@iterate nat nat Nat.add (dotdot y0 y1) x0) (x0 (S y1))) (@iterate nat nat Nat.add (dotdot y0 y1) x0)))).
Definition term55 (x0 : nat -> nat) := forall y0 : nat, forall y1 : nat, (@nsum nat (dotdot y0 (S y1)) x0) = (@COND nat (Peano.le y0 (S y1)) (Nat.add (@nsum nat (dotdot y0 y1) x0) (x0 (S y1))) (@nsum nat (dotdot y0 y1) x0)).
Definition term16 (x0 : nat -> nat) := forall y0 : nat, forall y1 : nat, (@iterate nat nat Nat.add (dotdot y0 (S y1)) x0) = (@COND nat (Peano.le y0 (S y1)) (Nat.add (@iterate nat nat Nat.add (dotdot y0 y1) x0) (x0 (S y1))) (@iterate nat nat Nat.add (dotdot y0 y1) x0)).
Definition term30 (x0 : nat) (x1 : nat) := @iterate nat nat Nat.add (dotdot x0 (S x1)).
Definition term7 (x0 : nat) (x1 : nat -> nat) := @COND nat (x0 = (NUMERAL 0)) (x1 (NUMERAL 0)) (NUMERAL 0).
Definition term8 (x0 : nat) (x1 : nat -> nat) := @eq nat (@iterate nat nat Nat.add (dotdot x0 (NUMERAL 0)) x1).
Definition term56 (x0 : nat -> nat) := (forall y0 : nat, (@nsum nat (dotdot y0 (NUMERAL 0)) x0) = (@COND nat (y0 = (NUMERAL 0)) (x0 (NUMERAL 0)) (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, (@nsum nat (dotdot y0 (S y1)) x0) = (@COND nat (Peano.le y0 (S y1)) (Nat.add (@nsum nat (dotdot y0 y1) x0) (x0 (S y1))) (@nsum nat (dotdot y0 y1) x0))).
Definition term17 (x0 : nat -> nat) := (forall y0 : nat, (@iterate nat nat Nat.add (dotdot y0 (NUMERAL 0)) x0) = (@COND nat (y0 = (NUMERAL 0)) (x0 (NUMERAL 0)) (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, (@iterate nat nat Nat.add (dotdot y0 (S y1)) x0) = (@COND nat (Peano.le y0 (S y1)) (Nat.add (@iterate nat nat Nat.add (dotdot y0 y1) x0) (x0 (S y1))) (@iterate nat nat Nat.add (dotdot y0 y1) x0))).
Definition term4 (x0 : nat -> nat) := (forall y0 : nat, (@iterate nat nat Nat.add (dotdot y0 (NUMERAL 0)) x0) = (@COND nat (y0 = (NUMERAL 0)) (x0 (NUMERAL 0)) (@neutral nat Nat.add))) /\ (forall y0 : nat, forall y1 : nat, (@iterate nat nat Nat.add (dotdot y0 (S y1)) x0) = (@COND nat (Peano.le y0 (S y1)) (Nat.add (@iterate nat nat Nat.add (dotdot y0 y1) x0) (x0 (S y1))) (@iterate nat nat Nat.add (dotdot y0 y1) x0))).
Definition term0 (a0 : Type') (x0 : nat -> a0) (x1 : type1400 a0) := (fun y0 : type1400 a0 => (@monoidal a0 y0) -> (forall y1 : nat, (@iterate a0 nat y0 (dotdot y1 (NUMERAL 0)) x0) = (@COND a0 (y1 = (NUMERAL 0)) (x0 (NUMERAL 0)) (@neutral a0 y0))) /\ (forall y1 : nat, forall y2 : nat, (@iterate a0 nat y0 (dotdot y1 (S y2)) x0) = (@COND a0 (Peano.le y1 (S y2)) (y0 (@iterate a0 nat y0 (dotdot y1 y2) x0) (x0 (S y2))) (@iterate a0 nat y0 (dotdot y1 y2) x0)))) x1.
Definition term34 (x0 : nat) (x1 : nat) (x2 : nat -> nat) := @eq nat (@iterate nat nat Nat.add (dotdot x0 (S x1)) x2).
Definition term2 (x0 : type1606) (x1 : nat -> nat) := (@monoidal nat x0) -> (forall y0 : nat, (@iterate nat nat x0 (dotdot y0 (NUMERAL 0)) x1) = (@COND nat (y0 = (NUMERAL 0)) (x1 (NUMERAL 0)) (@neutral nat x0))) /\ (forall y0 : nat, forall y1 : nat, (@iterate nat nat x0 (dotdot y0 (S y1)) x1) = (@COND nat (Peano.le y0 (S y1)) (x0 (@iterate nat nat x0 (dotdot y0 y1) x1) (x1 (S y1))) (@iterate nat nat x0 (dotdot y0 y1) x1))).
Definition term1 (a0 : Type') (x0 : type1400 a0) (x1 : nat -> a0) := (@monoidal a0 x0) -> (forall y0 : nat, (@iterate a0 nat x0 (dotdot y0 (NUMERAL 0)) x1) = (@COND a0 (y0 = (NUMERAL 0)) (x1 (NUMERAL 0)) (@neutral a0 x0))) /\ (forall y0 : nat, forall y1 : nat, (@iterate a0 nat x0 (dotdot y0 (S y1)) x1) = (@COND a0 (Peano.le y0 (S y1)) (x0 (@iterate a0 nat x0 (dotdot y0 y1) x1) (x1 (S y1))) (@iterate a0 nat x0 (dotdot y0 y1) x1))).
Definition term5 (x0 : nat) (x1 : nat -> nat) := @COND nat (x0 = (NUMERAL 0)) (x1 (NUMERAL 0)).
Definition term33 (x0 : nat) (x1 : nat) (x2 : nat -> nat) := @eq nat (@nsum nat (dotdot x0 (S x1)) x2).
Definition term47 (x0 : nat) (x1 : nat) (x2 : nat -> nat) := @COND nat (Peano.le x0 (S x1)) (Nat.add (@nsum nat (dotdot x0 x1) x2) (x2 (S x1))) (@nsum nat (dotdot x0 x1) x2).
Definition term31 (x0 : nat) (x1 : nat) (x2 : nat -> nat) := @nsum nat (dotdot x0 (S x1)) x2.
Definition term25 (x0 : nat -> nat) := fun y0 : nat => (@nsum nat (dotdot y0 (NUMERAL 0)) x0) = (@COND nat (y0 = (NUMERAL 0)) (x0 (NUMERAL 0)) (NUMERAL 0)).
Definition term50 (x0 : nat) (x1 : nat -> nat) := fun y0 : nat => (@iterate nat nat Nat.add (dotdot x0 (S y0)) x1) = (@COND nat (Peano.le x0 (S y0)) (Nat.add (@iterate nat nat Nat.add (dotdot x0 y0) x1) (x1 (S y0))) (@iterate nat nat Nat.add (dotdot x0 y0) x1)).
Definition term41 (x0 : nat -> nat) (x1 : nat) := x0 (S x1).
Definition term36 (x0 : nat) (x1 : nat) := @iterate nat nat Nat.add (dotdot x0 x1).
Definition term23 (x0 : nat) (x1 : nat -> nat) := @nsum nat (dotdot x0 (NUMERAL 0)) x1.
Definition term20 (x0 : nat) := dotdot x0 (NUMERAL 0).
Definition term37 (x0 : nat) (x1 : nat) (x2 : nat -> nat) := @nsum nat (dotdot x0 x1) x2.
Definition term54 (x0 : nat -> nat) := fun y0 : nat => forall y1 : nat, (@iterate nat nat Nat.add (dotdot y0 (S y1)) x0) = (@COND nat (Peano.le y0 (S y1)) (Nat.add (@iterate nat nat Nat.add (dotdot y0 y1) x0) (x0 (S y1))) (@iterate nat nat Nat.add (dotdot y0 y1) x0)).
Definition term53 (x0 : nat -> nat) := fun y0 : nat => forall y1 : nat, (@nsum nat (dotdot y0 (S y1)) x0) = (@COND nat (Peano.le y0 (S y1)) (Nat.add (@nsum nat (dotdot y0 y1) x0) (x0 (S y1))) (@nsum nat (dotdot y0 y1) x0)).
