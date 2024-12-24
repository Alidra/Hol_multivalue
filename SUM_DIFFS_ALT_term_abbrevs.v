Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term46 (x0 : nat -> real) (x1 : nat) := real_neg ((fun y0 : nat => real_sub (x0 y0) (x0 (Nat.add y0 (NUMERAL (BIT1 0))))) x1).
Definition term76 (x0 : nat) (x1 : nat -> real) (x2 : nat) := @COND real True (real_neg (real_sub (x1 x0) (x1 (Nat.add x2 (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term54 (x0 : real) (x1 : Prop) (x2 : nat) (x3 : nat -> real) (x4 : nat) (x5 : real) := (x1 -> (fun y0 : real => (real_neg y0) = (@COND real (Peano.le x2 x4) (real_neg (real_sub (x3 x2) (x3 (Nat.add x4 (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)))) x0) /\ ((~ x1) -> (fun y0 : real => (real_neg y0) = (@COND real (Peano.le x2 x4) (real_neg (real_sub (x3 x2) (x3 (Nat.add x4 (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)))) x5).
Definition term93 (x0 : nat -> real) (x1 : nat) := forall y0 : nat, (@sum nat (dotdot x1 y0) (fun y1 : nat => real_sub (x0 (Nat.add y1 (NUMERAL (BIT1 0)))) (x0 y1))) = (@COND real (Peano.le x1 y0) (real_sub (x0 (Nat.add y0 (NUMERAL (BIT1 0)))) (x0 x1)) (real_of_num (NUMERAL 0))).
Definition term1 (x0 : nat) (x1 : nat -> real) := forall y0 : nat, (@sum nat (dotdot x0 y0) (fun y1 : nat => real_sub (x1 y1) (x1 (Nat.add y1 (NUMERAL (BIT1 0)))))) = (@COND real (Peano.le x0 y0) (real_sub (x1 x0) (x1 (Nat.add y0 (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))).
Definition term83 (x0 : nat) (x1 : nat -> real) (x2 : nat) := (fun y0 : Prop => (real_neg (real_of_num (NUMERAL 0))) = (@COND real y0 (real_neg (real_sub (x1 x0) (x1 (Nat.add x2 (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)))) False.
Definition term37 (x0 : nat) (x1 : nat -> real) (x2 : nat) := @COND real (Peano.le x2 x0) (real_sub (x1 (Nat.add x0 (NUMERAL (BIT1 0)))) (x1 x2)) (real_of_num (NUMERAL 0)).
Definition term24 (x0 : nat -> real) := fun y0 : nat => real_sub (x0 (Nat.add y0 (NUMERAL (BIT1 0)))) (x0 y0).
Definition term36 := real_of_num (NUMERAL 0).
Definition term21 (x0 : nat -> real) (x1 : nat) := real_sub (x0 (Nat.add x1 (NUMERAL (BIT1 0)))) (x0 x1).
Definition term23 (x0 : nat -> real) (x1 : nat) := x0 (Nat.add x1 (NUMERAL (BIT1 0))).
Definition term29 (x0 : nat) (x1 : nat) (x2 : nat -> real) := @eq real (@sum nat (dotdot x0 x1) (fun y0 : nat => real_sub (x2 (Nat.add y0 (NUMERAL (BIT1 0)))) (x2 y0))).
Definition term45 (x0 : nat -> real) (x1 : nat) := real_sub (x0 x1) (x0 (Nat.add x1 (NUMERAL (BIT1 0)))).
Definition term26 (x0 : nat) (x1 : nat) := @sum nat (dotdot x0 x1).
Definition term38 (x0 : nat) (x1 : nat -> real) (x2 : nat) := @COND real (Peano.le x0 x2) (real_neg (real_sub (x1 x0) (x1 (Nat.add x2 (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term56 (x0 : nat) (x1 : nat -> real) (x2 : nat) := (fun y0 : real => (real_neg y0) = (@COND real (Peano.le x0 x2) (real_neg (real_sub (x1 x0) (x1 (Nat.add x2 (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)))) (@COND real (Peano.le x0 x2) (real_sub (x1 x0) (x1 (Nat.add x2 (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))).
Definition term42 (x0 : nat) (x1 : nat) (x2 : nat -> real) := real_neg (@sum nat (dotdot x0 x1) (fun y0 : nat => real_sub (x2 y0) (x2 (Nat.add y0 (NUMERAL (BIT1 0)))))).
Definition term60 := real_neg (real_of_num (NUMERAL 0)).
Definition term69 (x0 : nat) (x1 : nat -> real) (x2 : nat) := and ((Peano.le x0 x2) -> (real_neg (real_sub (x1 x0) (x1 (Nat.add x2 (NUMERAL (BIT1 0)))))) = (@COND real (Peano.le x0 x2) (real_neg (real_sub (x1 x0) (x1 (Nat.add x2 (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)))).
Definition term28 (x0 : nat) (x1 : nat) (x2 : nat -> real) := @sum nat (dotdot x0 x1) (fun y0 : nat => real_neg (real_sub (x2 y0) (x2 (Nat.add y0 (NUMERAL (BIT1 0)))))).
Definition term27 (x0 : nat) (x1 : nat) (x2 : nat -> real) := @sum nat (dotdot x0 x1) (fun y0 : nat => real_sub (x2 (Nat.add y0 (NUMERAL (BIT1 0)))) (x2 y0)).
Definition term85 (x0 : nat -> real) (x1 : nat) (x2 : nat) := @eq Prop ((fun y0 : Prop => (real_neg (real_of_num (NUMERAL 0))) = (@COND real y0 (real_neg (real_sub (x0 x1) (x0 (Nat.add x2 (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)))) (Peano.le x1 x2)).
Definition term77 (x0 : nat -> real) (x1 : nat) (x2 : nat) := @eq Prop ((fun y0 : Prop => (real_neg (real_sub (x0 x1) (x0 (Nat.add x2 (NUMERAL (BIT1 0)))))) = (@COND real y0 (real_neg (real_sub (x0 x1) (x0 (Nat.add x2 (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)))) (Peano.le x1 x2)).
Definition term3 (x0 : nat) (x1 : nat) (x2 : nat -> real) := @sum nat (dotdot x0 x1) (fun y0 : nat => real_sub (x2 y0) (x2 (Nat.add y0 (NUMERAL (BIT1 0))))).
Definition term65 (x0 : nat) (x1 : nat) := imp (Peano.le x0 x1).
Definition term35 (x0 : nat) (x1 : nat -> real) (x2 : nat) := @COND real (Peano.le x0 x2) (real_neg (real_sub (x1 x0) (x1 (Nat.add x2 (NUMERAL (BIT1 0)))))).
Definition term43 (x0 : nat -> real) := fun y0 : nat => real_sub (x0 y0) (x0 (Nat.add y0 (NUMERAL (BIT1 0)))).
Definition term18 := forall y0 : real, forall y1 : real, (real_sub y1 y0) = (real_neg (real_sub y0 y1)).
Definition term17 := forall y0 : real, forall y1 : real, (real_neg (real_sub y0 y1)) = (real_sub y1 y0).
Definition term0 (x0 : nat -> real) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (@sum nat (dotdot y0 y1) (fun y2 : nat => real_sub (x0 y2) (x0 (Nat.add y2 (NUMERAL (BIT1 0)))))) = (@COND real (Peano.le y0 y1) (real_sub (x0 y0) (x0 (Nat.add y1 (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)))) x1.
Definition term20 (x0 : real) (x1 : real) := (fun y0 : real => (real_sub y0 x0) = (real_neg (real_sub x0 y0))) x1.
Definition term52 (x0 : real) (x1 : Prop) (x2 : real -> Prop) (x3 : real) := (x1 -> x2 x0) /\ ((~ x1) -> x2 x3).
Definition term91 := @eq real (real_neg (real_of_num (NUMERAL 0))).
Definition term90 (x0 : nat) (x1 : nat -> real) (x2 : nat) := @eq real (real_sub (x1 (Nat.add x0 (NUMERAL (BIT1 0)))) (x1 x2)).
Definition term31 (x0 : nat) (x1 : nat -> real) (x2 : nat) := real_sub (x1 (Nat.add x0 (NUMERAL (BIT1 0)))) (x1 x2).
Definition term59 (x0 : nat) (x1 : nat -> real) (x2 : nat) := (fun y0 : real => (real_neg y0) = (@COND real (Peano.le x0 x2) (real_neg (real_sub (x1 x0) (x1 (Nat.add x2 (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)))) (real_of_num (NUMERAL 0)).
Definition term62 (x0 : nat) (x1 : nat -> real) (x2 : nat) := (~ (Peano.le x0 x2)) -> (fun y0 : real => (real_neg y0) = (@COND real (Peano.le x0 x2) (real_neg (real_sub (x1 x0) (x1 (Nat.add x2 (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)))) (real_of_num (NUMERAL 0)).
Definition term41 (x0 : nat) (x1 : nat) (x2 : nat -> real) := @sum nat (dotdot x0 x1) (fun y0 : nat => real_neg ((fun y1 : nat => real_sub (x2 y1) (x2 (Nat.add y1 (NUMERAL (BIT1 0))))) y0)).
Definition term79 (x0 : nat) (x1 : nat) := ~ (Peano.le x0 x1).
Definition term84 (x0 : nat) (x1 : nat -> real) (x2 : nat) := @COND real False (real_neg (real_sub (x1 x0) (x1 (Nat.add x2 (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term25 (x0 : nat -> real) := fun y0 : nat => real_neg (real_sub (x0 y0) (x0 (Nat.add y0 (NUMERAL (BIT1 0))))).
Definition term13 (x0 : real) := forall y0 : real, (real_neg (real_sub x0 y0)) = (real_sub y0 x0).
Definition term66 (x0 : nat) (x1 : nat -> real) (x2 : nat) := (Peano.le x0 x2) -> (fun y0 : real => (real_neg y0) = (@COND real (Peano.le x0 x2) (real_neg (real_sub (x1 x0) (x1 (Nat.add x2 (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)))) (real_sub (x1 x0) (x1 (Nat.add x2 (NUMERAL (BIT1 0))))).
Definition term92 := @eq real (real_of_num (NUMERAL 0)).
Definition term7 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@sum a0 y0 (fun y1 : a0 => real_neg (x0 y1))) = (real_neg (@sum a0 y0 x0))) x1.
Definition term11 (x0 : real) := fun y0 : real => (real_neg (real_sub x0 y0)) = (real_sub y0 x0).
Definition term73 (x0 : nat) (x1 : nat -> real) (x2 : nat) := fun y0 : Prop => (real_neg (real_sub (x1 x0) (x1 (Nat.add x2 (NUMERAL (BIT1 0)))))) = (@COND real y0 (real_neg (real_sub (x1 x0) (x1 (Nat.add x2 (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0))).
Definition term80 (x0 : nat) (x1 : nat) := (~ (Peano.le x0 x1)) -> (Peano.le x0 x1) = False.
Definition term39 (x0 : nat -> Prop) (x1 : nat -> real) := @sum nat x0 (fun y0 : nat => real_neg (x1 y0)).
Definition term70 (x0 : nat) (x1 : nat -> real) (x2 : nat) := ((Peano.le x0 x2) -> (real_neg (real_sub (x1 x0) (x1 (Nat.add x2 (NUMERAL (BIT1 0)))))) = (@COND real (Peano.le x0 x2) (real_neg (real_sub (x1 x0) (x1 (Nat.add x2 (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)))) /\ ((~ (Peano.le x0 x2)) -> (real_neg (real_of_num (NUMERAL 0))) = (@COND real (Peano.le x0 x2) (real_neg (real_sub (x1 x0) (x1 (Nat.add x2 (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)))).
Definition term94 (x0 : nat -> real) := forall y0 : nat, forall y1 : nat, (@sum nat (dotdot y0 y1) (fun y2 : nat => real_sub (x0 (Nat.add y2 (NUMERAL (BIT1 0)))) (x0 y2))) = (@COND real (Peano.le y0 y1) (real_sub (x0 (Nat.add y1 (NUMERAL (BIT1 0)))) (x0 y0)) (real_of_num (NUMERAL 0))).
Definition term2 (x0 : nat) (x1 : nat -> real) (x2 : nat) := (fun y0 : nat => (@sum nat (dotdot x0 y0) (fun y1 : nat => real_sub (x1 y1) (x1 (Nat.add y1 (NUMERAL (BIT1 0)))))) = (@COND real (Peano.le x0 y0) (real_sub (x1 x0) (x1 (Nat.add y0 (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)))) x2.
Definition term82 (x0 : nat -> real) (x1 : nat) (x2 : nat) := (fun y0 : Prop => (real_neg (real_of_num (NUMERAL 0))) = (@COND real y0 (real_neg (real_sub (x0 x1) (x0 (Nat.add x2 (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)))) (Peano.le x1 x2).
Definition term74 (x0 : nat -> real) (x1 : nat) (x2 : nat) := (fun y0 : Prop => (real_neg (real_sub (x0 x1) (x0 (Nat.add x2 (NUMERAL (BIT1 0)))))) = (@COND real y0 (real_neg (real_sub (x0 x1) (x0 (Nat.add x2 (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)))) (Peano.le x1 x2).
Definition term88 (x0 : real) (x1 : real) := (fun y0 : real => (real_neg (real_sub x0 y0)) = (real_sub y0 x0)) x1.
Definition term47 (x0 : nat -> real) := fun y0 : nat => real_neg ((fun y1 : nat => real_sub (x0 y1) (x0 (Nat.add y1 (NUMERAL (BIT1 0))))) y0).
Definition term15 := fun y0 : real => forall y1 : real, (real_neg (real_sub y0 y1)) = (real_sub y1 y0).
Definition term68 (x0 : nat) (x1 : nat -> real) (x2 : nat) := and ((Peano.le x0 x2) -> (fun y0 : real => (real_neg y0) = (@COND real (Peano.le x0 x2) (real_neg (real_sub (x1 x0) (x1 (Nat.add x2 (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)))) (real_sub (x1 x0) (x1 (Nat.add x2 (NUMERAL (BIT1 0)))))).
Definition term87 (x0 : real) := (fun y0 : real => forall y1 : real, (real_neg (real_sub y0 y1)) = (real_sub y1 y0)) x0.
Definition term19 (x0 : real) := (fun y0 : real => forall y1 : real, (real_sub y1 y0) = (real_neg (real_sub y0 y1))) x0.
Definition term12 (x0 : real) := fun y0 : real => (real_sub y0 x0) = (real_neg (real_sub x0 y0)).
Definition term22 (x0 : nat -> real) (x1 : nat) := real_neg (real_sub (x0 x1) (x0 (Nat.add x1 (NUMERAL (BIT1 0))))).
Definition term5 (a0 : Type') (x0 : a0 -> real) := (fun y0 : a0 -> real => forall y1 : a0 -> Prop, (@sum a0 y1 (fun y2 : a0 => real_neg (y0 y2))) = (real_neg (@sum a0 y1 y0))) x0.
Definition term81 (x0 : nat) (x1 : nat -> real) (x2 : nat) := fun y0 : Prop => (real_neg (real_of_num (NUMERAL 0))) = (@COND real y0 (real_neg (real_sub (x1 x0) (x1 (Nat.add x2 (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0))).
Definition term86 (x0 : nat) (x1 : nat -> real) (x2 : nat) := @eq Prop ((real_neg (real_of_num (NUMERAL 0))) = (@COND real (Peano.le x0 x2) (real_neg (real_sub (x1 x0) (x1 (Nat.add x2 (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)))).
Definition term75 (x0 : nat) (x1 : nat -> real) (x2 : nat) := (fun y0 : Prop => (real_neg (real_sub (x1 x0) (x1 (Nat.add x2 (NUMERAL (BIT1 0)))))) = (@COND real y0 (real_neg (real_sub (x1 x0) (x1 (Nat.add x2 (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)))) True.
Definition term4 (x0 : nat) (x1 : nat -> real) (x2 : nat) := @COND real (Peano.le x0 x2) (real_sub (x1 x0) (x1 (Nat.add x2 (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term14 (x0 : real) := forall y0 : real, (real_sub y0 x0) = (real_neg (real_sub x0 y0)).
Definition term55 (x0 : nat) (x1 : nat -> real) (x2 : nat) := fun y0 : real => (real_neg y0) = (@COND real (Peano.le x0 x2) (real_neg (real_sub (x1 x0) (x1 (Nat.add x2 (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0))).
Definition term64 (x0 : nat) (x1 : nat -> real) (x2 : nat) := (fun y0 : real => (real_neg y0) = (@COND real (Peano.le x0 x2) (real_neg (real_sub (x1 x0) (x1 (Nat.add x2 (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)))) (real_sub (x1 x0) (x1 (Nat.add x2 (NUMERAL (BIT1 0))))).
Definition term89 (x0 : nat) (x1 : nat -> real) (x2 : nat) := @eq real (real_neg (real_sub (x1 x0) (x1 (Nat.add x2 (NUMERAL (BIT1 0)))))).
Definition term49 (x0 : nat) (x1 : nat -> real) (x2 : nat) := real_neg (@COND real (Peano.le x0 x2) (real_sub (x1 x0) (x1 (Nat.add x2 (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))).
Definition term48 (x0 : nat) (x1 : nat) (x2 : nat -> real) := @eq real (@sum nat (dotdot x0 x1) (fun y0 : nat => real_neg ((fun y1 : nat => real_sub (x2 y1) (x2 (Nat.add y1 (NUMERAL (BIT1 0))))) y0))).
Definition term30 (x0 : nat) (x1 : nat) (x2 : nat -> real) := @eq real (@sum nat (dotdot x0 x1) (fun y0 : nat => real_neg (real_sub (x2 y0) (x2 (Nat.add y0 (NUMERAL (BIT1 0))))))).
Definition term6 (a0 : Type') (x0 : a0 -> real) := forall y0 : a0 -> Prop, (@sum a0 y0 (fun y1 : a0 => real_neg (x0 y1))) = (real_neg (@sum a0 y0 x0)).
Definition term67 (x0 : nat) (x1 : nat -> real) (x2 : nat) := (Peano.le x0 x2) -> (real_neg (real_sub (x1 x0) (x1 (Nat.add x2 (NUMERAL (BIT1 0)))))) = (@COND real (Peano.le x0 x2) (real_neg (real_sub (x1 x0) (x1 (Nat.add x2 (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0))).
Definition term40 (x0 : nat -> Prop) (x1 : nat -> real) := real_neg (@sum nat x0 x1).
Definition term9 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := real_neg (@sum a0 x0 x1).
Definition term71 (x0 : nat) (x1 : nat -> real) (x2 : nat) := @eq Prop ((fun y0 : real => (real_neg y0) = (@COND real (Peano.le x0 x2) (real_neg (real_sub (x1 x0) (x1 (Nat.add x2 (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)))) (@COND real (Peano.le x0 x2) (real_sub (x1 x0) (x1 (Nat.add x2 (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)))).
Definition term61 (x0 : nat) (x1 : nat) := imp (~ (Peano.le x0 x1)).
Definition term51 (x0 : real -> Prop) (x1 : Prop) (x2 : real) (x3 : real) := x0 (@COND real x1 x2 x3).
Definition term50 (x0 : nat) (x1 : nat -> real) (x2 : nat) := @eq real (real_neg (@COND real (Peano.le x0 x2) (real_sub (x1 x0) (x1 (Nat.add x2 (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)))).
Definition term32 (x0 : nat) (x1 : nat -> real) (x2 : nat) := real_neg (real_sub (x1 x0) (x1 (Nat.add x2 (NUMERAL (BIT1 0))))).
Definition term33 (x0 : nat) (x1 : nat) := @COND real (Peano.le x0 x1).
Definition term10 (x0 : real) (x1 : real) := real_neg (real_sub x0 x1).
Definition term63 (x0 : nat) (x1 : nat -> real) (x2 : nat) := (~ (Peano.le x0 x2)) -> (real_neg (real_of_num (NUMERAL 0))) = (@COND real (Peano.le x0 x2) (real_neg (real_sub (x1 x0) (x1 (Nat.add x2 (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0))).
Definition term8 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := @sum a0 x0 (fun y0 : a0 => real_neg (x1 y0)).
Definition term57 (x0 : nat) (x1 : nat -> real) (x2 : nat) := ((Peano.le x0 x2) -> (fun y0 : real => (real_neg y0) = (@COND real (Peano.le x0 x2) (real_neg (real_sub (x1 x0) (x1 (Nat.add x2 (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)))) (real_sub (x1 x0) (x1 (Nat.add x2 (NUMERAL (BIT1 0)))))) /\ ((~ (Peano.le x0 x2)) -> (fun y0 : real => (real_neg y0) = (@COND real (Peano.le x0 x2) (real_neg (real_sub (x1 x0) (x1 (Nat.add x2 (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)))) (real_of_num (NUMERAL 0))).
Definition term58 (x0 : nat) (x1 : nat -> real) (x2 : nat) := real_sub (x1 x0) (x1 (Nat.add x2 (NUMERAL (BIT1 0)))).
Definition term78 (x0 : nat) (x1 : nat -> real) (x2 : nat) := @eq Prop ((real_neg (real_sub (x1 x0) (x1 (Nat.add x2 (NUMERAL (BIT1 0)))))) = (@COND real (Peano.le x0 x2) (real_neg (real_sub (x1 x0) (x1 (Nat.add x2 (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)))).
Definition term72 (x0 : nat) (x1 : nat -> real) (x2 : nat) := @eq Prop ((real_neg (@COND real (Peano.le x0 x2) (real_sub (x1 x0) (x1 (Nat.add x2 (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)))) = (@COND real (Peano.le x0 x2) (real_neg (real_sub (x1 x0) (x1 (Nat.add x2 (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)))).
Definition term53 (x0 : nat) (x1 : nat -> real) (x2 : nat) (x3 : Prop) (x4 : real) (x5 : real) := (fun y0 : real => (real_neg y0) = (@COND real (Peano.le x0 x2) (real_neg (real_sub (x1 x0) (x1 (Nat.add x2 (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)))) (@COND real x3 x4 x5).
Definition term34 (x0 : nat) (x1 : nat -> real) (x2 : nat) := @COND real (Peano.le x2 x0) (real_sub (x1 (Nat.add x0 (NUMERAL (BIT1 0)))) (x1 x2)).
Definition term16 := fun y0 : real => forall y1 : real, (real_sub y1 y0) = (real_neg (real_sub y0 y1)).
Definition term44 (x0 : nat -> real) (x1 : nat) := (fun y0 : nat => real_sub (x0 y0) (x0 (Nat.add y0 (NUMERAL (BIT1 0))))) x1.
