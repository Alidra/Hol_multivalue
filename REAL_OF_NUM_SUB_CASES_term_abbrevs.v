Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term84 := (~ False) -> False.
Definition term71 (x0 : nat) := fun y0 : nat => (Peano.le x0 y0) \/ (Peano.le y0 x0).
Definition term40 (x0 : nat) (x1 : nat) := and ((Peano.le x1 x0) -> (real_sub (real_of_num x0) (real_of_num x1)) = (real_of_num (Nat.sub x0 x1))).
Definition term10 := (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> (real_sub (real_of_num y1) (real_of_num y0)) = (real_of_num (Nat.sub y1 y0))) -> forall y0 : nat, forall y1 : nat, (Peano.le y1 y0) -> (real_sub (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.sub y0 y1)).
Definition term44 (x0 : nat) (x1 : nat) := @eq Prop ((real_sub (real_of_num x1) (real_of_num x0)) = (@COND real (Peano.le x0 x1) (real_of_num (Nat.sub x1 x0)) (real_neg (real_of_num (Nat.sub x0 x1))))).
Definition term6 (x0 : nat) (x1 : nat) := real_of_num (Nat.sub x0 x1).
Definition term50 (x0 : Prop) := (~ x0) -> False.
Definition term3 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le x0 y0) -> (real_sub (real_of_num y0) (real_of_num x0)) = (real_of_num (Nat.sub y0 x0))) x1.
Definition term75 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le x0 y0) \/ (Peano.le y0 x0)) x1.
Definition term64 (x0 : nat) := forall y0 : nat, (~ (Peano.le x0 y0)) -> (~ (Peano.le y0 x0)) -> (forall y1 : nat, forall y2 : nat, (Peano.le y1 y2) \/ (Peano.le y2 y1)) -> False.
Definition term79 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term34 (x0 : nat) (x1 : nat) := (~ (Peano.le x0 x1)) -> (fun y0 : real => (real_sub (real_of_num x1) (real_of_num x0)) = y0) (real_neg (real_of_num (Nat.sub x0 x1))).
Definition term57 := ~ (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)).
Definition term37 (x0 : nat) (x1 : nat) := imp (Peano.le x0 x1).
Definition term82 (x0 : Prop) := (~ x0) -> x0.
Definition term32 (x0 : nat) (x1 : nat) := (fun y0 : real => (real_sub (real_of_num x1) (real_of_num x0)) = y0) (real_neg (real_of_num (Nat.sub x0 x1))).
Definition term48 (x0 : nat) (x1 : nat) := real_neg (real_sub (real_of_num x0) (real_of_num x1)).
Definition term4 (x0 : nat) (x1 : nat) := (Peano.le x1 x0) -> (real_sub (real_of_num x0) (real_of_num x1)) = (real_of_num (Nat.sub x0 x1)).
Definition term81 (x0 : nat) (x1 : nat) := (~ (Peano.le x0 x1)) -> Peano.le x0 x1.
Definition term21 := forall y0 : real, forall y1 : real, (real_sub y1 y0) = (real_neg (real_sub y0 y1)).
Definition term20 := forall y0 : real, forall y1 : real, (real_neg (real_sub y0 y1)) = (real_sub y1 y0).
Definition term23 (x0 : real) (x1 : real) := (fun y0 : real => (real_sub y0 x0) = (real_neg (real_sub x0 y0))) x1.
Definition term80 (x0 : nat) (x1 : nat) := (~ (Peano.le x1 x0)) -> Peano.le x0 x1.
Definition term63 (x0 : nat) := fun y0 : nat => (~ (Peano.le x0 y0)) -> (~ (Peano.le y0 x0)) -> ~ (forall y1 : nat, forall y2 : nat, (Peano.le y1 y2) \/ (Peano.le y2 y1)).
Definition term53 (x0 : nat) (x1 : nat) := ((~ (Peano.le x1 x0)) -> (~ (Peano.le x0 x1)) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) -> False) -> (~ (Peano.le x1 x0)) -> (~ (Peano.le x0 x1)) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) -> False.
Definition term5 (x0 : nat) (x1 : nat) := real_sub (real_of_num x0) (real_of_num x1).
Definition term46 (x0 : nat) (x1 : nat) := @eq real (real_sub (real_of_num x0) (real_of_num x1)).
Definition term73 := fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0).
Definition term61 (x0 : nat) (x1 : nat) := (~ (Peano.le x1 x0)) -> (~ (Peano.le x0 x1)) -> ~ (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)).
Definition term72 (x0 : nat) := forall y0 : nat, (Peano.le x0 y0) \/ (Peano.le y0 x0).
Definition term60 (x0 : nat) (x1 : nat) := (~ (Peano.le x0 x1)) -> ~ (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)).
Definition term25 (x0 : real) (x1 : Prop) (x2 : real -> Prop) (x3 : real) := (x1 -> x2 x0) /\ ((~ x1) -> x2 x3).
Definition term65 (x0 : nat) := forall y0 : nat, (~ (Peano.le x0 y0)) -> (~ (Peano.le y0 x0)) -> ~ (forall y1 : nat, forall y2 : nat, (Peano.le y1 y2) \/ (Peano.le y2 y1)).
Definition term62 (x0 : nat) := fun y0 : nat => (~ (Peano.le x0 y0)) -> (~ (Peano.le y0 x0)) -> (forall y1 : nat, forall y2 : nat, (Peano.le y1 y2) \/ (Peano.le y2 y1)) -> False.
Definition term45 (x0 : nat) (x1 : nat) := ~ (Peano.le x0 x1).
Definition term29 (x0 : nat) (x1 : nat) := (fun y0 : real => (real_sub (real_of_num x1) (real_of_num x0)) = y0) (@COND real (Peano.le x0 x1) (real_of_num (Nat.sub x1 x0)) (real_neg (real_of_num (Nat.sub x0 x1)))).
Definition term56 := (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) -> False.
Definition term87 (x0 : nat) := forall y0 : nat, (real_sub (real_of_num x0) (real_of_num y0)) = (@COND real (Peano.le y0 x0) (real_of_num (Nat.sub x0 y0)) (real_neg (real_of_num (Nat.sub y0 x0)))).
Definition term16 (x0 : real) := forall y0 : real, (real_neg (real_sub x0 y0)) = (real_sub y0 x0).
Definition term39 (x0 : nat) (x1 : nat) := and ((Peano.le x1 x0) -> (fun y0 : real => (real_sub (real_of_num x0) (real_of_num x1)) = y0) (real_of_num (Nat.sub x0 x1))).
Definition term14 (x0 : real) := fun y0 : real => (real_neg (real_sub x0 y0)) = (real_sub y0 x0).
Definition term86 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (Peano.le x0 y0)) -> (~ (Peano.le y0 x0)) -> (forall y1 : nat, forall y2 : nat, (Peano.le y1 y2) \/ (Peano.le y2 y1)) -> False) x1.
Definition term38 (x0 : nat) (x1 : nat) := (Peano.le x1 x0) -> (fun y0 : real => (real_sub (real_of_num x0) (real_of_num x1)) = y0) (real_of_num (Nat.sub x0 x1)).
Definition term88 := forall y0 : nat, forall y1 : nat, (real_sub (real_of_num y0) (real_of_num y1)) = (@COND real (Peano.le y1 y0) (real_of_num (Nat.sub y0 y1)) (real_neg (real_of_num (Nat.sub y1 y0)))).
Definition term69 := forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) -> (~ (Peano.le y1 y0)) -> ~ (forall y2 : nat, forall y3 : nat, (Peano.le y2 y3) \/ (Peano.le y3 y2)).
Definition term68 := forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) -> (~ (Peano.le y1 y0)) -> (forall y2 : nat, forall y3 : nat, (Peano.le y2 y3) \/ (Peano.le y3 y2)) -> False.
Definition term58 := forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0).
Definition term9 := forall y0 : nat, forall y1 : nat, (Peano.le y1 y0) -> (real_sub (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.sub y0 y1)).
Definition term0 := forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> (real_sub (real_of_num y1) (real_of_num y0)) = (real_of_num (Nat.sub y1 y0)).
Definition term35 (x0 : nat) (x1 : nat) := (~ (Peano.le x0 x1)) -> (real_sub (real_of_num x1) (real_of_num x0)) = (real_neg (real_of_num (Nat.sub x0 x1))).
Definition term41 (x0 : nat) (x1 : nat) := ((Peano.le x0 x1) -> (real_sub (real_of_num x1) (real_of_num x0)) = (real_of_num (Nat.sub x1 x0))) /\ ((~ (Peano.le x0 x1)) -> (real_sub (real_of_num x1) (real_of_num x0)) = (real_neg (real_of_num (Nat.sub x0 x1)))).
Definition term54 (x0 : nat) (x1 : nat) := (((~ (Peano.le x1 x0)) -> (~ (Peano.le x0 x1)) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) -> False) -> (~ (Peano.le x1 x0)) -> (~ (Peano.le x0 x1)) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) -> False) -> (~ (Peano.le x1 x0)) -> (~ (Peano.le x0 x1)) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) -> False.
Definition term18 := fun y0 : real => forall y1 : real, (real_neg (real_sub y0 y1)) = (real_sub y1 y0).
Definition term22 (x0 : real) := (fun y0 : real => forall y1 : real, (real_sub y1 y0) = (real_neg (real_sub y0 y1))) x0.
Definition term15 (x0 : real) := fun y0 : real => (real_sub y0 x0) = (real_neg (real_sub x0 y0)).
Definition term27 (x0 : real) (x1 : Prop) (x2 : nat) (x3 : nat) (x4 : real) := (x1 -> (fun y0 : real => (real_sub (real_of_num x2) (real_of_num x3)) = y0) x0) /\ ((~ x1) -> (fun y0 : real => (real_sub (real_of_num x2) (real_of_num x3)) = y0) x4).
Definition term12 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le y0 x0) -> (real_sub (real_of_num x0) (real_of_num y0)) = (real_of_num (Nat.sub x0 y0))) x1.
Definition term26 (x0 : nat) (x1 : nat) (x2 : Prop) (x3 : real) (x4 : real) := (fun y0 : real => (real_sub (real_of_num x0) (real_of_num x1)) = y0) (@COND real x2 x3 x4).
Definition term70 (x0 : nat) (x1 : nat) := (Peano.le x1 x0) \/ (Peano.le x0 x1).
Definition term36 (x0 : nat) (x1 : nat) := (fun y0 : real => (real_sub (real_of_num x0) (real_of_num x1)) = y0) (real_of_num (Nat.sub x0 x1)).
Definition term31 (x0 : nat) (x1 : nat) := real_neg (real_of_num (Nat.sub x0 x1)).
Definition term55 (x0 : nat) (x1 : nat) := (((~ (Peano.le x1 x0)) -> (~ (Peano.le x0 x1)) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) -> False) -> (~ (Peano.le x1 x0)) -> (~ (Peano.le x0 x1)) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) -> False) -> ((~ (Peano.le x1 x0)) -> (~ (Peano.le x0 x1)) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) -> False) -> (~ (Peano.le x1 x0)) -> (~ (Peano.le x0 x1)) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) -> False.
Definition term17 (x0 : real) := forall y0 : real, (real_sub y0 x0) = (real_neg (real_sub x0 y0)).
Definition term76 (x0 : nat) (x1 : nat) := (Peano.le x0 x1) -> ~ (Peano.le x0 x1).
Definition term43 (x0 : nat) (x1 : nat) := @eq Prop ((fun y0 : real => (real_sub (real_of_num x1) (real_of_num x0)) = y0) (@COND real (Peano.le x0 x1) (real_of_num (Nat.sub x1 x0)) (real_neg (real_of_num (Nat.sub x0 x1))))).
Definition term51 (x0 : nat) (x1 : nat) := (~ (Peano.le x0 x1)) -> False.
Definition term52 (x0 : nat) (x1 : nat) := (~ (Peano.le x1 x0)) -> (~ (Peano.le x0 x1)) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) -> False.
Definition term7 (x0 : nat) (x1 : nat) := (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> (real_sub (real_of_num y1) (real_of_num y0)) = (real_of_num (Nat.sub y1 y0))) -> (real_sub (real_of_num x0) (real_of_num x1)) = (real_of_num (Nat.sub x0 x1)).
Definition term42 (x0 : nat) (x1 : nat) := @COND real (Peano.le x0 x1) (real_of_num (Nat.sub x1 x0)) (real_neg (real_of_num (Nat.sub x0 x1))).
Definition term85 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) -> (~ (Peano.le y1 y0)) -> (forall y2 : nat, forall y3 : nat, (Peano.le y2 y3) \/ (Peano.le y3 y2)) -> False) x0.
Definition term74 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) x0.
Definition term11 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y1 y0) -> (real_sub (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.sub y0 y1))) x0.
Definition term1 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) -> (real_sub (real_of_num y1) (real_of_num y0)) = (real_of_num (Nat.sub y1 y0))) x0.
Definition term49 (x0 : nat) (x1 : nat) := @eq real (real_neg (real_sub (real_of_num x0) (real_of_num x1))).
Definition term28 (x0 : nat) (x1 : nat) := fun y0 : real => (real_sub (real_of_num x0) (real_of_num x1)) = y0.
Definition term59 (x0 : nat) (x1 : nat) := (~ (Peano.le x0 x1)) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) -> False.
Definition term33 (x0 : nat) (x1 : nat) := imp (~ (Peano.le x0 x1)).
Definition term24 (x0 : real -> Prop) (x1 : Prop) (x2 : real) (x3 : real) := x0 (@COND real x1 x2 x3).
Definition term78 (x0 : nat) (x1 : nat) := @eq Prop ((Peano.le x1 x0) \/ (Peano.le x0 x1)).
Definition term8 (x0 : nat) := forall y0 : nat, (Peano.le y0 x0) -> (real_sub (real_of_num x0) (real_of_num y0)) = (real_of_num (Nat.sub x0 y0)).
Definition term2 (x0 : nat) := forall y0 : nat, (Peano.le x0 y0) -> (real_sub (real_of_num y0) (real_of_num x0)) = (real_of_num (Nat.sub y0 x0)).
Definition term30 (x0 : nat) (x1 : nat) := ((Peano.le x0 x1) -> (fun y0 : real => (real_sub (real_of_num x1) (real_of_num x0)) = y0) (real_of_num (Nat.sub x1 x0))) /\ ((~ (Peano.le x0 x1)) -> (fun y0 : real => (real_sub (real_of_num x1) (real_of_num x0)) = y0) (real_neg (real_of_num (Nat.sub x0 x1)))).
Definition term13 (x0 : real) (x1 : real) := real_neg (real_sub x0 x1).
Definition term47 (x0 : nat) (x1 : nat) := @eq real (real_of_num (Nat.sub x0 x1)).
Definition term83 (x0 : nat) (x1 : nat) := (Peano.le x0 x1) -> False.
Definition term67 := fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) -> (~ (Peano.le y1 y0)) -> ~ (forall y2 : nat, forall y3 : nat, (Peano.le y2 y3) \/ (Peano.le y3 y2)).
Definition term66 := fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) -> (~ (Peano.le y1 y0)) -> (forall y2 : nat, forall y3 : nat, (Peano.le y2 y3) \/ (Peano.le y3 y2)) -> False.
Definition term77 (x0 : Prop) := x0 -> ~ x0.
Definition term19 := fun y0 : real => forall y1 : real, (real_sub y1 y0) = (real_neg (real_sub y0 y1)).
