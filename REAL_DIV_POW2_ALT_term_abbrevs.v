Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term33 (x0 : real) (x1 : nat) (x2 : nat) := (fun y0 : nat => (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_div (real_pow x0 x1) (real_pow x0 y0)) = (@COND real (Peano.le y0 x1) (real_pow x0 (Nat.sub x1 y0)) (real_inv (real_pow x0 (Nat.sub y0 x1))))) x2.
Definition term4 (x0 : nat) := fun y0 : nat => (Peano.lt y0 x0) = (~ (Peano.le x0 y0)).
Definition term6 (x0 : nat) := forall y0 : nat, (Peano.lt y0 x0) = (~ (Peano.le x0 y0)).
Definition term17 := fun y0 : real => y0 = (real_inv (real_inv y0)).
Definition term54 (x0 : real) (x1 : nat) (x2 : nat) (x3 : Prop) (x4 : real) (x5 : real) := (fun y0 : real => ((Peano.lt x1 x2) = x3) -> (x3 -> (real_pow x0 (Nat.sub x2 x1)) = x4) -> ((~ x3) -> (real_inv (real_pow x0 (Nat.sub x1 x2))) = y0) -> (@COND real (Peano.lt x1 x2) (real_pow x0 (Nat.sub x2 x1)) (real_inv (real_pow x0 (Nat.sub x1 x2)))) = (@COND real x3 x4 y0)) x5.
Definition term39 := real_of_num (NUMERAL 0).
Definition term38 (x0 : real) := (~ (x0 = (real_of_num (NUMERAL 0)))) -> (x0 = (real_of_num (NUMERAL 0))) = False.
Definition term53 (x0 : real) (x1 : nat) (x2 : nat) (x3 : Prop) (x4 : real) := forall y0 : real, ((Peano.lt x1 x2) = x3) -> (x3 -> (real_pow x0 (Nat.sub x2 x1)) = x4) -> ((~ x3) -> (real_inv (real_pow x0 (Nat.sub x1 x2))) = y0) -> (@COND real (Peano.lt x1 x2) (real_pow x0 (Nat.sub x2 x1)) (real_inv (real_pow x0 (Nat.sub x1 x2)))) = (@COND real x3 x4 y0).
Definition term3 (x0 : nat) := fun y0 : nat => (~ (Peano.le x0 y0)) = (Peano.lt y0 x0).
Definition term19 := forall y0 : real, y0 = (real_inv (real_inv y0)).
Definition term0 (x0 : nat) (x1 : nat) := (fun y0 : Prop => y0 \/ (~ y0)) (Peano.le x0 x1).
Definition term43 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) (x3 : Prop) (x4 : a0) := forall y0 : a0, (x0 = x3) -> (x3 -> x1 = x4) -> ((~ x3) -> x2 = y0) -> (@COND a0 x0 x1 x2) = (@COND a0 x3 x4 y0).
Definition term16 := fun y0 : real => (real_inv (real_inv y0)) = y0.
Definition term23 (x0 : nat) (x1 : real) (x2 : nat) := real_inv (real_inv (real_div (real_pow x1 x0) (real_pow x1 x2))).
Definition term71 (x0 : real) (x1 : nat) (x2 : nat) := @COND real (~ (Peano.le x1 x2)) (real_pow x0 (Nat.sub x1 x2)).
Definition term57 (x0 : real) (x1 : nat) (x2 : nat) (x3 : real) (x4 : real) := ((~ (Peano.le x1 x2)) -> (real_pow x0 (Nat.sub x1 x2)) = x3) -> ((~ (~ (Peano.le x1 x2))) -> (real_inv (real_pow x0 (Nat.sub x2 x1))) = x4) -> (@COND real (Peano.lt x2 x1) (real_pow x0 (Nat.sub x1 x2)) (real_inv (real_pow x0 (Nat.sub x2 x1)))) = (@COND real (~ (Peano.le x1 x2)) x3 x4).
Definition term81 := forall y0 : real, forall y1 : nat, forall y2 : nat, (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_div (real_pow y0 y1) (real_pow y0 y2)) = (@COND real (Peano.lt y2 y1) (real_pow y0 (Nat.sub y1 y2)) (real_inv (real_pow y0 (Nat.sub y2 y1)))).
Definition term51 (x0 : real) (x1 : nat) (x2 : nat) (x3 : Prop) := forall y0 : real, forall y1 : real, ((Peano.lt x1 x2) = x3) -> (x3 -> (real_pow x0 (Nat.sub x2 x1)) = y0) -> ((~ x3) -> (real_inv (real_pow x0 (Nat.sub x1 x2))) = y1) -> (@COND real (Peano.lt x1 x2) (real_pow x0 (Nat.sub x2 x1)) (real_inv (real_pow x0 (Nat.sub x1 x2)))) = (@COND real x3 y0 y1).
Definition term20 (x0 : real) := (fun y0 : real => y0 = (real_inv (real_inv y0))) x0.
Definition term28 (x0 : nat) (x1 : real) (x2 : nat) := @eq real (real_inv (real_div (real_pow x1 x0) (real_pow x1 x2))).
Definition term68 (x0 : real) (x1 : nat) (x2 : nat) := @COND real True (real_pow x0 (Nat.sub x2 x1)) (real_inv (real_pow x0 (Nat.sub x1 x2))).
Definition term22 (x0 : nat) (x1 : real) (x2 : nat) := real_div (real_pow x1 x0) (real_pow x1 x2).
Definition term31 (x0 : real) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_div (real_pow x0 y0) (real_pow x0 y1)) = (@COND real (Peano.le y1 y0) (real_pow x0 (Nat.sub y0 y1)) (real_inv (real_pow x0 (Nat.sub y1 y0))))) x1.
Definition term18 := forall y0 : real, (real_inv (real_inv y0)) = y0.
Definition term7 := fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0).
Definition term21 (x0 : real) := ~ (x0 = (real_of_num (NUMERAL 0))).
Definition term1 (x0 : nat) (x1 : nat) := (Peano.le x0 x1) \/ (~ (Peano.le x0 x1)).
Definition term24 (x0 : nat) (x1 : real) (x2 : nat) := @eq real (real_div (real_pow x1 x0) (real_pow x1 x2)).
Definition term2 (x0 : nat) (x1 : nat) := ~ (Peano.le x0 x1).
Definition term64 (x0 : real) (x1 : nat) (x2 : nat) := @COND real (~ (Peano.le x2 x1)) (real_pow x0 (Nat.sub x2 x1)) (real_inv (real_pow x0 (Nat.sub x1 x2))).
Definition term70 (x0 : nat) (x1 : nat) := @COND real (~ (Peano.le x0 x1)).
Definition term79 (x0 : real) (x1 : nat) := forall y0 : nat, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_div (real_pow x0 x1) (real_pow x0 y0)) = (@COND real (Peano.lt y0 x1) (real_pow x0 (Nat.sub x1 y0)) (real_inv (real_pow x0 (Nat.sub y0 x1)))).
Definition term32 (x0 : real) (x1 : nat) := forall y0 : nat, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_div (real_pow x0 x1) (real_pow x0 y0)) = (@COND real (Peano.le y0 x1) (real_pow x0 (Nat.sub x1 y0)) (real_inv (real_pow x0 (Nat.sub y0 x1)))).
Definition term12 (x0 : real) := forall y0 : real, (real_inv (real_div x0 y0)) = (real_div y0 x0).
Definition term52 (x0 : real) (x1 : nat) (x2 : nat) (x3 : Prop) (x4 : real) := (fun y0 : real => forall y1 : real, ((Peano.lt x1 x2) = x3) -> (x3 -> (real_pow x0 (Nat.sub x2 x1)) = y0) -> ((~ x3) -> (real_inv (real_pow x0 (Nat.sub x1 x2))) = y1) -> (@COND real (Peano.lt x1 x2) (real_pow x0 (Nat.sub x2 x1)) (real_inv (real_pow x0 (Nat.sub x1 x2)))) = (@COND real x3 y0 y1)) x4.
Definition term27 (x0 : nat) (x1 : real) (x2 : nat) := real_inv (real_div (real_pow x1 x0) (real_pow x1 x2)).
Definition term50 (x0 : real) (x1 : nat) (x2 : nat) (x3 : Prop) := (fun y0 : Prop => forall y1 : real, forall y2 : real, ((Peano.lt x1 x2) = y0) -> (y0 -> (real_pow x0 (Nat.sub x2 x1)) = y1) -> ((~ y0) -> (real_inv (real_pow x0 (Nat.sub x1 x2))) = y2) -> (@COND real (Peano.lt x1 x2) (real_pow x0 (Nat.sub x2 x1)) (real_inv (real_pow x0 (Nat.sub x1 x2)))) = (@COND real y0 y1 y2)) x3.
Definition term75 (x0 : nat) (x1 : nat) := (~ (Peano.le x0 x1)) -> (Peano.le x0 x1) = False.
Definition term15 (x0 : real) := real_inv (real_inv x0).
Definition term80 (x0 : real) := forall y0 : nat, forall y1 : nat, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_div (real_pow x0 y0) (real_pow x0 y1)) = (@COND real (Peano.lt y1 y0) (real_pow x0 (Nat.sub y0 y1)) (real_inv (real_pow x0 (Nat.sub y1 y0)))).
Definition term30 (x0 : real) := forall y0 : nat, forall y1 : nat, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_div (real_pow x0 y0) (real_pow x0 y1)) = (@COND real (Peano.le y1 y0) (real_pow x0 (Nat.sub y0 y1)) (real_inv (real_pow x0 (Nat.sub y1 y0)))).
Definition term10 := forall y0 : nat, forall y1 : nat, (Peano.lt y1 y0) = (~ (Peano.le y0 y1)).
Definition term9 := forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0).
Definition term5 (x0 : nat) := forall y0 : nat, (~ (Peano.le x0 y0)) = (Peano.lt y0 x0).
Definition term74 (x0 : real) := (fun y0 : real => (real_inv (real_inv y0)) = y0) x0.
Definition term14 (x0 : real) (x1 : real) := real_inv (real_div x0 x1).
Definition term48 (x0 : real) (x1 : nat) (x2 : nat) := real_pow x0 (Nat.sub x1 x2).
Definition term61 (x0 : real) (x1 : nat) (x2 : nat) := (~ (~ (Peano.le x2 x1))) -> (real_inv (real_pow x0 (Nat.sub x1 x2))) = (real_inv (real_pow x0 (Nat.sub x1 x2))).
Definition term11 (x0 : real) := (fun y0 : real => forall y1 : real, (real_inv (real_div y0 y1)) = (real_div y1 y0)) x0.
Definition term73 (x0 : real) (x1 : nat) (x2 : nat) := @COND real False (real_pow x0 (Nat.sub x2 x1)) (real_inv (real_pow x0 (Nat.sub x1 x2))).
Definition term66 (x0 : real) (x1 : nat) (x2 : nat) := @COND real (Peano.le x2 x1) (real_pow x0 (Nat.sub x1 x2)).
Definition term41 (x0 : real) (x1 : nat) (x2 : nat) := @eq real (real_inv (@COND real (Peano.le x1 x2) (real_pow x0 (Nat.sub x2 x1)) (real_inv (real_pow x0 (Nat.sub x1 x2))))).
Definition term78 (x0 : real) (x1 : nat) (x2 : nat) := (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_div (real_pow x0 x2) (real_pow x0 x1)) = (@COND real (Peano.lt x1 x2) (real_pow x0 (Nat.sub x2 x1)) (real_inv (real_pow x0 (Nat.sub x1 x2)))).
Definition term34 (x0 : real) (x1 : nat) (x2 : nat) := (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_div (real_pow x0 x2) (real_pow x0 x1)) = (@COND real (Peano.le x1 x2) (real_pow x0 (Nat.sub x2 x1)) (real_inv (real_pow x0 (Nat.sub x1 x2)))).
Definition term47 (x0 : real) (x1 : nat) (x2 : nat) := forall y0 : Prop, forall y1 : real, forall y2 : real, ((Peano.lt x1 x2) = y0) -> (y0 -> (real_pow x0 (Nat.sub x2 x1)) = y1) -> ((~ y0) -> (real_inv (real_pow x0 (Nat.sub x1 x2))) = y2) -> (@COND real (Peano.lt x1 x2) (real_pow x0 (Nat.sub x2 x1)) (real_inv (real_pow x0 (Nat.sub x1 x2)))) = (@COND real y0 y1 y2).
Definition term46 (x0 : Prop) (x1 : real) (x2 : real) := forall y0 : Prop, forall y1 : real, forall y2 : real, (x0 = y0) -> (y0 -> x1 = y1) -> ((~ y0) -> x2 = y2) -> (@COND real x0 x1 x2) = (@COND real y0 y1 y2).
Definition term45 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) := forall y0 : Prop, forall y1 : a0, forall y2 : a0, (x0 = y0) -> (y0 -> x1 = y1) -> ((~ y0) -> x2 = y2) -> (@COND a0 x0 x1 x2) = (@COND a0 y0 y1 y2).
Definition term77 (x0 : real) (x1 : nat) (x2 : nat) := @eq real (real_pow x0 (Nat.sub x1 x2)).
Definition term25 (x0 : nat) (x1 : real) (x2 : nat) := @eq real (real_inv (real_inv (real_div (real_pow x1 x0) (real_pow x1 x2)))).
Definition term36 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y1 y0) = (~ (Peano.le y0 y1))) x0.
Definition term62 (x0 : nat) (x1 : nat) := ~ (~ (Peano.le x0 x1)).
Definition term55 (x0 : real) (x1 : nat) (x2 : nat) (x3 : Prop) (x4 : real) (x5 : real) := ((Peano.lt x1 x2) = x3) -> (x3 -> (real_pow x0 (Nat.sub x2 x1)) = x4) -> ((~ x3) -> (real_inv (real_pow x0 (Nat.sub x1 x2))) = x5) -> (@COND real (Peano.lt x1 x2) (real_pow x0 (Nat.sub x2 x1)) (real_inv (real_pow x0 (Nat.sub x1 x2)))) = (@COND real x3 x4 x5).
Definition term63 (x0 : real) (x1 : nat) (x2 : nat) := ((~ (~ (Peano.le x2 x1))) -> (real_inv (real_pow x0 (Nat.sub x1 x2))) = (real_inv (real_pow x0 (Nat.sub x1 x2)))) -> (@COND real (Peano.lt x1 x2) (real_pow x0 (Nat.sub x2 x1)) (real_inv (real_pow x0 (Nat.sub x1 x2)))) = (@COND real (~ (Peano.le x2 x1)) (real_pow x0 (Nat.sub x2 x1)) (real_inv (real_pow x0 (Nat.sub x1 x2)))).
Definition term29 (x0 : real) := (fun y0 : real => forall y1 : nat, forall y2 : nat, (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_div (real_pow y0 y1) (real_pow y0 y2)) = (@COND real (Peano.le y2 y1) (real_pow y0 (Nat.sub y1 y2)) (real_inv (real_pow y0 (Nat.sub y2 y1))))) x0.
Definition term35 (x0 : real) (x1 : nat) (x2 : nat) := @COND real (Peano.le x1 x2) (real_pow x0 (Nat.sub x2 x1)) (real_inv (real_pow x0 (Nat.sub x1 x2))).
Definition term26 (x0 : real) (x1 : nat) (x2 : nat) := @COND real (Peano.lt x1 x2) (real_pow x0 (Nat.sub x2 x1)) (real_inv (real_pow x0 (Nat.sub x1 x2))).
Definition term44 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) (x3 : Prop) := forall y0 : a0, forall y1 : a0, (x0 = x3) -> (x3 -> x1 = y0) -> ((~ x3) -> x2 = y1) -> (@COND a0 x0 x1 x2) = (@COND a0 x3 y0 y1).
Definition term13 (x0 : real) (x1 : real) := (fun y0 : real => (real_inv (real_div x0 y0)) = (real_div y0 x0)) x1.
Definition term37 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt y0 x0) = (~ (Peano.le x0 y0))) x1.
Definition term67 (x0 : real) (x1 : nat) (x2 : nat) := @COND real True (real_pow x0 (Nat.sub x1 x2)).
Definition term72 (x0 : real) (x1 : nat) (x2 : nat) := @COND real False (real_pow x0 (Nat.sub x1 x2)).
Definition term65 (x0 : nat) (x1 : nat) := @COND real (Peano.le x0 x1).
Definition term60 (x0 : real) (x1 : nat) (x2 : nat) (x3 : real) := ((~ (~ (Peano.le x1 x2))) -> (real_inv (real_pow x0 (Nat.sub x2 x1))) = x3) -> (@COND real (Peano.lt x2 x1) (real_pow x0 (Nat.sub x1 x2)) (real_inv (real_pow x0 (Nat.sub x2 x1)))) = (@COND real (~ (Peano.le x1 x2)) (real_pow x0 (Nat.sub x1 x2)) x3).
Definition term8 := fun y0 : nat => forall y1 : nat, (Peano.lt y1 y0) = (~ (Peano.le y0 y1)).
Definition term56 (x0 : real) (x1 : nat) (x2 : nat) (x3 : real) (x4 : real) := ((Peano.lt x2 x1) = (~ (Peano.le x1 x2))) -> ((~ (Peano.le x1 x2)) -> (real_pow x0 (Nat.sub x1 x2)) = x3) -> ((~ (~ (Peano.le x1 x2))) -> (real_inv (real_pow x0 (Nat.sub x2 x1))) = x4) -> (@COND real (Peano.lt x2 x1) (real_pow x0 (Nat.sub x1 x2)) (real_inv (real_pow x0 (Nat.sub x2 x1)))) = (@COND real (~ (Peano.le x1 x2)) x3 x4).
Definition term69 (x0 : real) (x1 : nat) (x2 : nat) := @eq real (real_inv (real_pow x0 (Nat.sub x1 x2))).
Definition term49 (x0 : real) (x1 : nat) (x2 : nat) := real_inv (real_pow x0 (Nat.sub x1 x2)).
Definition term40 (x0 : real) (x1 : nat) (x2 : nat) := real_inv (@COND real (Peano.le x1 x2) (real_pow x0 (Nat.sub x2 x1)) (real_inv (real_pow x0 (Nat.sub x1 x2)))).
Definition term76 (x0 : real) (x1 : nat) (x2 : nat) := real_inv (real_inv (real_pow x0 (Nat.sub x1 x2))).
Definition term58 (x0 : real) (x1 : nat) (x2 : nat) := (~ (Peano.le x1 x2)) -> (real_pow x0 (Nat.sub x1 x2)) = (real_pow x0 (Nat.sub x1 x2)).
Definition term59 (x0 : real) (x1 : nat) (x2 : nat) (x3 : real) := ((~ (Peano.le x1 x2)) -> (real_pow x0 (Nat.sub x1 x2)) = (real_pow x0 (Nat.sub x1 x2))) -> ((~ (~ (Peano.le x1 x2))) -> (real_inv (real_pow x0 (Nat.sub x2 x1))) = x3) -> (@COND real (Peano.lt x2 x1) (real_pow x0 (Nat.sub x1 x2)) (real_inv (real_pow x0 (Nat.sub x2 x1)))) = (@COND real (~ (Peano.le x1 x2)) (real_pow x0 (Nat.sub x1 x2)) x3).
Definition term42 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) (x3 : Prop) (x4 : a0) (x5 : a0) := (x0 = x3) -> (x3 -> x1 = x4) -> ((~ x3) -> x2 = x5) -> (@COND a0 x0 x1 x2) = (@COND a0 x3 x4 x5).
