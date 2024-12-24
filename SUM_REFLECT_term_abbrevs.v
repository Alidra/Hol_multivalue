Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (x0 : type1627) := (@monoidal real x0) -> forall y0 : nat -> real, forall y1 : nat, forall y2 : nat, (@iterate real nat x0 (dotdot y1 y2) y0) = (@COND real (Peano.lt y2 y1) (@neutral real x0) (@iterate real nat x0 (dotdot (NUMERAL 0) (Nat.sub y2 y1)) (fun y3 : nat => y0 (Nat.sub y2 y3)))).
Definition term1 (a0 : Type') (x0 : type1400 a0) := (@monoidal a0 x0) -> forall y0 : nat -> a0, forall y1 : nat, forall y2 : nat, (@iterate a0 nat x0 (dotdot y1 y2) y0) = (@COND a0 (Peano.lt y2 y1) (@neutral a0 x0) (@iterate a0 nat x0 (dotdot (NUMERAL 0) (Nat.sub y2 y1)) (fun y3 : nat => y0 (Nat.sub y2 y3)))).
Definition term29 (x0 : nat) (x1 : nat) := @COND real (Peano.lt x0 x1) (@neutral real real_add).
Definition term27 := real_of_num (NUMERAL 0).
Definition term22 (x0 : nat) (x1 : nat -> real) (x2 : nat) := @iterate real nat real_add (dotdot (NUMERAL 0) (Nat.sub x2 x0)) (fun y0 : nat => x1 (Nat.sub x2 y0)).
Definition term5 (x0 : nat -> real) := (fun y0 : nat -> real => forall y1 : nat, forall y2 : nat, (@iterate real nat real_add (dotdot y1 y2) y0) = (@COND real (Peano.lt y2 y1) (@neutral real real_add) (@iterate real nat real_add (dotdot (NUMERAL 0) (Nat.sub y2 y1)) (fun y3 : nat => y0 (Nat.sub y2 y3))))) x0.
Definition term12 (x0 : nat) (x1 : nat) := @sum nat (dotdot x0 x1).
Definition term20 (x0 : nat -> real) (x1 : nat) := fun y0 : nat => x0 (Nat.sub x1 y0).
Definition term33 := forall y0 : nat -> real, forall y1 : nat, forall y2 : nat, (@sum nat (dotdot y1 y2) y0) = (@COND real (Peano.lt y2 y1) (real_of_num (NUMERAL 0)) (@sum nat (dotdot (NUMERAL 0) (Nat.sub y2 y1)) (fun y3 : nat => y0 (Nat.sub y2 y3)))).
Definition term4 := forall y0 : nat -> real, forall y1 : nat, forall y2 : nat, (@iterate real nat real_add (dotdot y1 y2) y0) = (@COND real (Peano.lt y2 y1) (@neutral real real_add) (@iterate real nat real_add (dotdot (NUMERAL 0) (Nat.sub y2 y1)) (fun y3 : nat => y0 (Nat.sub y2 y3)))).
Definition term3 := (@monoidal real real_add) -> forall y0 : nat -> real, forall y1 : nat, forall y2 : nat, (@iterate real nat real_add (dotdot y1 y2) y0) = (@COND real (Peano.lt y2 y1) (@neutral real real_add) (@iterate real nat real_add (dotdot (NUMERAL 0) (Nat.sub y2 y1)) (fun y3 : nat => y0 (Nat.sub y2 y3)))).
Definition term19 (x0 : nat) (x1 : nat) := @iterate real nat real_add (dotdot (NUMERAL 0) (Nat.sub x0 x1)).
Definition term9 (x0 : nat) (x1 : nat -> real) (x2 : nat) := (fun y0 : nat => (@iterate real nat real_add (dotdot x0 y0) x1) = (@COND real (Peano.lt y0 x0) (@neutral real real_add) (@iterate real nat real_add (dotdot (NUMERAL 0) (Nat.sub y0 x0)) (fun y1 : nat => x1 (Nat.sub y0 y1))))) x2.
Definition term11 (x0 : nat) (x1 : nat -> real) (x2 : nat) := @COND real (Peano.lt x2 x0) (@neutral real real_add) (@iterate real nat real_add (dotdot (NUMERAL 0) (Nat.sub x2 x0)) (fun y0 : nat => x1 (Nat.sub x2 y0))).
Definition term7 (x0 : nat -> real) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (@iterate real nat real_add (dotdot y0 y1) x0) = (@COND real (Peano.lt y1 y0) (@neutral real real_add) (@iterate real nat real_add (dotdot (NUMERAL 0) (Nat.sub y1 y0)) (fun y2 : nat => x0 (Nat.sub y1 y2))))) x1.
Definition term10 (x0 : nat) (x1 : nat) (x2 : nat -> real) := @iterate real nat real_add (dotdot x0 x1) x2.
Definition term31 (x0 : nat) (x1 : nat -> real) := forall y0 : nat, (@sum nat (dotdot x0 y0) x1) = (@COND real (Peano.lt y0 x0) (real_of_num (NUMERAL 0)) (@sum nat (dotdot (NUMERAL 0) (Nat.sub y0 x0)) (fun y1 : nat => x1 (Nat.sub y0 y1)))).
Definition term8 (x0 : nat) (x1 : nat -> real) := forall y0 : nat, (@iterate real nat real_add (dotdot x0 y0) x1) = (@COND real (Peano.lt y0 x0) (@neutral real real_add) (@iterate real nat real_add (dotdot (NUMERAL 0) (Nat.sub y0 x0)) (fun y1 : nat => x1 (Nat.sub y0 y1)))).
Definition term24 (x0 : nat) (x1 : nat -> real) (x2 : nat) := @COND real (Peano.lt x2 x0) (real_of_num (NUMERAL 0)) (@sum nat (dotdot (NUMERAL 0) (Nat.sub x2 x0)) (fun y0 : nat => x1 (Nat.sub x2 y0))).
Definition term26 (x0 : nat) (x1 : nat -> real) (x2 : nat) := @eq real (@COND real (Peano.lt x2 x0) (@neutral real real_add) (@iterate real nat real_add (dotdot (NUMERAL 0) (Nat.sub x2 x0)) (fun y0 : nat => x1 (Nat.sub x2 y0)))).
Definition term0 (a0 : Type') (x0 : type1400 a0) := (fun y0 : type1400 a0 => (@monoidal a0 y0) -> forall y1 : nat -> a0, forall y2 : nat, forall y3 : nat, (@iterate a0 nat y0 (dotdot y2 y3) y1) = (@COND a0 (Peano.lt y3 y2) (@neutral a0 y0) (@iterate a0 nat y0 (dotdot (NUMERAL 0) (Nat.sub y3 y2)) (fun y4 : nat => y1 (Nat.sub y3 y4))))) x0.
Definition term32 (x0 : nat -> real) := forall y0 : nat, forall y1 : nat, (@sum nat (dotdot y0 y1) x0) = (@COND real (Peano.lt y1 y0) (real_of_num (NUMERAL 0)) (@sum nat (dotdot (NUMERAL 0) (Nat.sub y1 y0)) (fun y2 : nat => x0 (Nat.sub y1 y2)))).
Definition term6 (x0 : nat -> real) := forall y0 : nat, forall y1 : nat, (@iterate real nat real_add (dotdot y0 y1) x0) = (@COND real (Peano.lt y1 y0) (@neutral real real_add) (@iterate real nat real_add (dotdot (NUMERAL 0) (Nat.sub y1 y0)) (fun y2 : nat => x0 (Nat.sub y1 y2)))).
Definition term21 (x0 : nat) (x1 : nat -> real) (x2 : nat) := @sum nat (dotdot (NUMERAL 0) (Nat.sub x2 x0)) (fun y0 : nat => x1 (Nat.sub x2 y0)).
Definition term14 (x0 : nat) (x1 : nat) (x2 : nat -> real) := @sum nat (dotdot x0 x1) x2.
Definition term18 (x0 : nat) (x1 : nat) := @sum nat (dotdot (NUMERAL 0) (Nat.sub x0 x1)).
Definition term25 (x0 : nat) (x1 : nat -> real) (x2 : nat) := @COND real (Peano.lt x2 x0) (real_of_num (NUMERAL 0)) (@iterate real nat real_add (dotdot (NUMERAL 0) (Nat.sub x2 x0)) (fun y0 : nat => x1 (Nat.sub x2 y0))).
Definition term23 (x0 : nat) (x1 : nat) := @COND real (Peano.lt x0 x1) (real_of_num (NUMERAL 0)).
Definition term16 (x0 : nat) (x1 : nat) (x2 : nat -> real) := @eq real (@iterate real nat real_add (dotdot x0 x1) x2).
Definition term15 (x0 : nat) (x1 : nat) (x2 : nat -> real) := @eq real (@sum nat (dotdot x0 x1) x2).
Definition term13 (x0 : nat) (x1 : nat) := @iterate real nat real_add (dotdot x0 x1).
Definition term17 (x0 : nat) (x1 : nat) := dotdot (NUMERAL 0) (Nat.sub x0 x1).
Definition term30 (x0 : nat) (x1 : nat -> real) (x2 : nat) := @eq real (@COND real (Peano.lt x2 x0) (real_of_num (NUMERAL 0)) (@iterate real nat real_add (dotdot (NUMERAL 0) (Nat.sub x2 x0)) (fun y0 : nat => x1 (Nat.sub x2 y0)))).
Definition term28 (x0 : nat) (x1 : nat) := @COND real (Peano.lt x0 x1).
