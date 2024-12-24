Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term185 (x0 : nat) (x1 : nat) (x2 : nat) := @COND nat ((Peano.le x0 x1) \/ (x2 = (NUMERAL (BIT1 0)))).
Definition term232 (x0 : nat) := (~ True) -> (@COND nat (x0 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)) = (@COND nat (x0 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)).
Definition term291 (x0 : nat) (x1 : nat) := Peano.lt (@COND nat (x0 = (NUMERAL (BIT1 0))) (NUMERAL 0) (Nat.pow x0 x1)).
Definition term367 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((x0 = (S (NUMERAL 0))) \/ (x0 = (NUMERAL 0)))) /\ (Peano.lt x1 x2).
Definition term197 (x0 : nat) (x1 : nat) (x2 : nat) := (((Nat.pow x1 x2) = (Nat.add (Nat.mul (@COND nat (Peano.le x0 x2) (Nat.pow x1 (Nat.sub x2 x0)) (@COND nat (x1 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0))) (Nat.pow x1 x0)) (@COND nat ((Peano.le x0 x2) \/ (x1 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow x1 x2)))) /\ (Peano.lt (@COND nat ((Peano.le x0 x2) \/ (x1 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow x1 x2)) (Nat.pow x1 x0))) -> ((Nat.div (Nat.pow x1 x2) (Nat.pow x1 x0)) = (@COND nat (Peano.le x0 x2) (Nat.pow x1 (Nat.sub x2 x0)) (@COND nat (x1 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)))) /\ ((Nat.modulo (Nat.pow x1 x2) (Nat.pow x1 x0)) = (@COND nat ((Peano.le x0 x2) \/ (x1 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow x1 x2))).
Definition term196 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.div (Nat.pow x1 x2) (Nat.pow x1 x0)) = (@COND nat (Peano.le x0 x2) (Nat.pow x1 (Nat.sub x2 x0)) (@COND nat (x1 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)))) /\ ((Nat.modulo (Nat.pow x1 x2) (Nat.pow x1 x0)) = (@COND nat ((Peano.le x0 x2) \/ (x1 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow x1 x2))).
Definition term31 (x0 : nat) := (x0 = (NUMERAL (BIT1 0))) \/ (~ (x0 = (NUMERAL (BIT1 0)))).
Definition term328 := @COND nat False (NUMERAL (BIT1 0)).
Definition term161 (x0 : nat) (x1 : nat) := @eq nat (Nat.div (Nat.pow (NUMERAL 0) x0) (Nat.pow (NUMERAL 0) x1)).
Definition term299 (x0 : nat) := (fun y0 : nat => (Nat.pow (NUMERAL (BIT1 0)) y0) = (NUMERAL (BIT1 0))) x0.
Definition term186 (x0 : nat) (x1 : nat) := @COND nat ((Peano.le x0 x1) \/ ((NUMERAL 0) = (NUMERAL (BIT1 0)))).
Definition term123 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, (~ (x0 = (NUMERAL 0))) -> (Nat.div (Nat.pow x0 y1) (Nat.pow x0 y2)) = (@COND nat (Peano.le y2 y1) (Nat.pow x0 (Nat.sub y1 y2)) (@COND nat (x0 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)))) y0) /\ ((fun y1 : nat => forall y2 : nat, (~ (x0 = (NUMERAL 0))) -> (Nat.modulo (Nat.pow x0 y1) (Nat.pow x0 y2)) = (@COND nat ((Peano.le y2 y1) \/ (x0 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow x0 y1))) y0).
Definition term101 := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, forall y3 : nat, (~ (y1 = (NUMERAL 0))) -> (Nat.div (Nat.pow y1 y2) (Nat.pow y1 y3)) = (@COND nat (Peano.le y3 y2) (Nat.pow y1 (Nat.sub y2 y3)) (@COND nat (y1 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)))) y0) /\ ((fun y1 : nat => forall y2 : nat, forall y3 : nat, (~ (y1 = (NUMERAL 0))) -> (Nat.modulo (Nat.pow y1 y2) (Nat.pow y1 y3)) = (@COND nat ((Peano.le y3 y2) \/ (y1 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow y1 y2))) y0).
Definition term141 (x0 : nat) (x1 : nat) (x2 : nat) := and ((fun y0 : nat => (~ (x1 = (NUMERAL 0))) -> (Nat.div (Nat.pow x1 x0) (Nat.pow x1 y0)) = (@COND nat (Peano.le y0 x0) (Nat.pow x1 (Nat.sub x0 y0)) (@COND nat (x1 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)))) x2).
Definition term183 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x1) \/ (x2 = (NUMERAL (BIT1 0))).
Definition term189 (x0 : nat) (x1 : nat) (x2 : nat) := @COND nat ((Peano.le x0 x2) \/ (x1 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow x1 x2).
Definition term135 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (~ (x0 = (NUMERAL 0))) -> (Nat.modulo (Nat.pow x0 x1) (Nat.pow x0 y0)) = (@COND nat ((Peano.le y0 x1) \/ (x0 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow x0 x1))) x2.
Definition term130 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (~ (x1 = (NUMERAL 0))) -> (Nat.div (Nat.pow x1 x0) (Nat.pow x1 y0)) = (@COND nat (Peano.le y0 x0) (Nat.pow x1 (Nat.sub x0 y0)) (@COND nat (x1 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)))) x2.
Definition term2 (x0 : nat) := fun y0 : nat => (Peano.lt y0 x0) = (~ (Peano.le x0 y0)).
Definition term300 (x0 : nat) := Nat.pow (NUMERAL (BIT1 0)) x0.
Definition term140 (x0 : nat) (x1 : nat) := @eq Prop ((forall y0 : nat, (~ (x0 = (NUMERAL 0))) -> (Nat.div (Nat.pow x0 x1) (Nat.pow x0 y0)) = (@COND nat (Peano.le y0 x1) (Nat.pow x0 (Nat.sub x1 y0)) (@COND nat (x0 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)))) /\ (forall y0 : nat, (~ (x0 = (NUMERAL 0))) -> (Nat.modulo (Nat.pow x0 x1) (Nat.pow x0 y0)) = (@COND nat ((Peano.le y0 x1) \/ (x0 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow x0 x1)))).
Definition term139 (x0 : nat) (x1 : nat) := @eq Prop ((forall y0 : nat, (fun y1 : nat => (~ (x0 = (NUMERAL 0))) -> (Nat.div (Nat.pow x0 x1) (Nat.pow x0 y1)) = (@COND nat (Peano.le y1 x1) (Nat.pow x0 (Nat.sub x1 y1)) (@COND nat (x0 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)))) y0) /\ (forall y0 : nat, (fun y1 : nat => (~ (x0 = (NUMERAL 0))) -> (Nat.modulo (Nat.pow x0 x1) (Nat.pow x0 y1)) = (@COND nat ((Peano.le y1 x1) \/ (x0 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow x0 x1))) y0)).
Definition term118 (x0 : nat) := @eq Prop ((forall y0 : nat, forall y1 : nat, (~ (x0 = (NUMERAL 0))) -> (Nat.div (Nat.pow x0 y0) (Nat.pow x0 y1)) = (@COND nat (Peano.le y1 y0) (Nat.pow x0 (Nat.sub y0 y1)) (@COND nat (x0 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)))) /\ (forall y0 : nat, forall y1 : nat, (~ (x0 = (NUMERAL 0))) -> (Nat.modulo (Nat.pow x0 y0) (Nat.pow x0 y1)) = (@COND nat ((Peano.le y1 y0) \/ (x0 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow x0 y0)))).
Definition term117 (x0 : nat) := @eq Prop ((forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (x0 = (NUMERAL 0))) -> (Nat.div (Nat.pow x0 y1) (Nat.pow x0 y2)) = (@COND nat (Peano.le y2 y1) (Nat.pow x0 (Nat.sub y1 y2)) (@COND nat (x0 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)))) y0) /\ (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (x0 = (NUMERAL 0))) -> (Nat.modulo (Nat.pow x0 y1) (Nat.pow x0 y2)) = (@COND nat ((Peano.le y2 y1) \/ (x0 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow x0 y1))) y0)).
Definition term96 := @eq Prop ((forall y0 : nat, forall y1 : nat, forall y2 : nat, (~ (y0 = (NUMERAL 0))) -> (Nat.div (Nat.pow y0 y1) (Nat.pow y0 y2)) = (@COND nat (Peano.le y2 y1) (Nat.pow y0 (Nat.sub y1 y2)) (@COND nat (y0 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)))) /\ (forall y0 : nat, forall y1 : nat, forall y2 : nat, (~ (y0 = (NUMERAL 0))) -> (Nat.modulo (Nat.pow y0 y1) (Nat.pow y0 y2)) = (@COND nat ((Peano.le y2 y1) \/ (y0 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow y0 y1)))).
Definition term95 := @eq Prop ((forall y0 : nat, (fun y1 : nat => forall y2 : nat, forall y3 : nat, (~ (y1 = (NUMERAL 0))) -> (Nat.div (Nat.pow y1 y2) (Nat.pow y1 y3)) = (@COND nat (Peano.le y3 y2) (Nat.pow y1 (Nat.sub y2 y3)) (@COND nat (y1 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)))) y0) /\ (forall y0 : nat, (fun y1 : nat => forall y2 : nat, forall y3 : nat, (~ (y1 = (NUMERAL 0))) -> (Nat.modulo (Nat.pow y1 y2) (Nat.pow y1 y3)) = (@COND nat ((Peano.le y3 y2) \/ (y1 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow y1 y2))) y0)).
Definition term13 (x0 : nat) := forall y0 : nat, (Peano.le y0 x0) = (~ (Peano.lt x0 y0)).
Definition term4 (x0 : nat) := forall y0 : nat, (Peano.lt y0 x0) = (~ (Peano.le x0 y0)).
Definition term166 (x0 : nat) (x1 : nat) := @COND nat (Peano.le x1 x0) (Nat.pow (NUMERAL 0) (Nat.sub x0 x1)).
Definition term245 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : Prop) (x4 : nat) := (fun y0 : nat => forall y1 : nat, (((Peano.le x0 x2) \/ (x1 = (NUMERAL (BIT1 0)))) = x3) -> (x3 -> (NUMERAL 0) = y0) -> ((~ x3) -> (Nat.pow x1 x2) = y1) -> (@COND nat ((Peano.le x0 x2) \/ (x1 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow x1 x2)) = (@COND nat x3 y0 y1)) x4.
Definition term223 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : Prop) (x4 : nat) := (fun y0 : nat => forall y1 : nat, ((Peano.le x1 x0) = x3) -> (x3 -> (Nat.pow x2 (Nat.sub x0 x1)) = y0) -> ((~ x3) -> (@COND nat (x2 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)) = y1) -> (@COND nat (Peano.le x1 x0) (Nat.pow x2 (Nat.sub x0 x1)) (@COND nat (x2 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0))) = (@COND nat x3 y0 y1)) x4.
Definition term127 (x0 : nat) (x1 : nat) := forall y0 : nat, ((fun y1 : nat => (~ (x0 = (NUMERAL 0))) -> (Nat.div (Nat.pow x0 x1) (Nat.pow x0 y1)) = (@COND nat (Peano.le y1 x1) (Nat.pow x0 (Nat.sub x1 y1)) (@COND nat (x0 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)))) y0) /\ ((fun y1 : nat => (~ (x0 = (NUMERAL 0))) -> (Nat.modulo (Nat.pow x0 x1) (Nat.pow x0 y1)) = (@COND nat ((Peano.le y1 x1) \/ (x0 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow x0 x1))) y0).
Definition term105 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (~ (x0 = (NUMERAL 0))) -> (Nat.div (Nat.pow x0 y1) (Nat.pow x0 y2)) = (@COND nat (Peano.le y2 y1) (Nat.pow x0 (Nat.sub y1 y2)) (@COND nat (x0 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)))) y0) /\ ((fun y1 : nat => forall y2 : nat, (~ (x0 = (NUMERAL 0))) -> (Nat.modulo (Nat.pow x0 y1) (Nat.pow x0 y2)) = (@COND nat ((Peano.le y2 y1) \/ (x0 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow x0 y1))) y0).
Definition term79 := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, forall y3 : nat, (~ (y1 = (NUMERAL 0))) -> (Nat.div (Nat.pow y1 y2) (Nat.pow y1 y3)) = (@COND nat (Peano.le y3 y2) (Nat.pow y1 (Nat.sub y2 y3)) (@COND nat (y1 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)))) y0) /\ ((fun y1 : nat => forall y2 : nat, forall y3 : nat, (~ (y1 = (NUMERAL 0))) -> (Nat.modulo (Nat.pow y1 y2) (Nat.pow y1 y3)) = (@COND nat ((Peano.le y3 y2) \/ (y1 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow y1 y2))) y0).
Definition term241 (x0 : nat) (x1 : nat) := Nat.add (Nat.pow x0 x1).
Definition term152 := @eq nat (NUMERAL 0).
Definition term176 (x0 : nat) (x1 : nat) := Nat.modulo (Nat.pow x0 x1).
Definition term246 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : Prop) (x4 : nat) := forall y0 : nat, (((Peano.le x0 x2) \/ (x1 = (NUMERAL (BIT1 0)))) = x3) -> (x3 -> (NUMERAL 0) = x4) -> ((~ x3) -> (Nat.pow x1 x2) = y0) -> (@COND nat ((Peano.le x0 x2) \/ (x1 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow x1 x2)) = (@COND nat x3 x4 y0).
Definition term224 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : Prop) (x4 : nat) := forall y0 : nat, ((Peano.le x1 x0) = x3) -> (x3 -> (Nat.pow x2 (Nat.sub x0 x1)) = x4) -> ((~ x3) -> (@COND nat (x2 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)) = y0) -> (@COND nat (Peano.le x1 x0) (Nat.pow x2 (Nat.sub x0 x1)) (@COND nat (x2 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0))) = (@COND nat x3 x4 y0).
Definition term295 := (forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))))).
Definition term321 := forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0).
Definition term230 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (True -> (Nat.pow x0 (Nat.sub x1 x2)) = (Nat.pow x0 (Nat.sub x1 x2))) -> ((~ True) -> (@COND nat (x0 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)) = x3) -> (@COND nat (Peano.le x2 x1) (Nat.pow x0 (Nat.sub x1 x2)) (@COND nat (x0 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0))) = (@COND nat True (Nat.pow x0 (Nat.sub x1 x2)) x3).
Definition term314 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.lt (Nat.pow y0 y1) (Nat.pow y0 y2)) = (((Peano.le (NUMERAL (BIT0 (BIT1 0))) y0) /\ (Peano.lt y1 y2)) \/ ((y0 = (NUMERAL 0)) /\ ((~ (y1 = (NUMERAL 0))) /\ (y2 = (NUMERAL 0)))))) x0.
Definition term212 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.mul (Nat.pow y0 y1) (Nat.pow y0 y2)) = (Nat.pow y0 (Nat.add y1 y2))) x0.
Definition term89 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (~ (y0 = (NUMERAL 0))) -> (Nat.modulo (Nat.pow y0 y1) (Nat.pow y0 y2)) = (@COND nat ((Peano.le y2 y1) \/ (y0 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow y0 y1))) x0.
Definition term82 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (~ (y0 = (NUMERAL 0))) -> (Nat.div (Nat.pow y0 y1) (Nat.pow y0 y2)) = (@COND nat (Peano.le y2 y1) (Nat.pow y0 (Nat.sub y1 y2)) (@COND nat (y0 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)))) x0.
Definition term65 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y1 = (Nat.add (Nat.mul y0 y2) y3)) /\ (Peano.lt y3 y2)) -> ((Nat.div y1 y2) = y0) /\ ((Nat.modulo y1 y2) = y3)) x0.
Definition term50 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y0 = (Nat.add (Nat.mul y2 y1) y3)) /\ (Peano.lt y3 y1)) -> ((Nat.div y0 y1) = y2) /\ ((Nat.modulo y0 y1) = y3)) x0.
Definition term253 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (True -> (NUMERAL 0) = (NUMERAL 0)) -> ((~ True) -> (Nat.pow x1 x2) = x3) -> (@COND nat ((Peano.le x0 x2) \/ (x1 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow x1 x2)) = (@COND nat True (NUMERAL 0) x3).
Definition term327 (x0 : nat) := (~ (x0 = (NUMERAL (BIT1 0)))) -> (x0 = (NUMERAL (BIT1 0))) = False.
Definition term179 (x0 : nat) (x1 : nat) := Nat.modulo (Nat.pow (NUMERAL 0) x0) (Nat.pow (NUMERAL 0) x1).
Definition term169 (x0 : nat) := @COND nat (x0 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)).
Definition term237 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (@COND nat (Peano.le x2 x0) (Nat.pow x1 (Nat.sub x0 x2)) (@COND nat (x1 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0))) (Nat.pow x1 x2).
Definition term145 (x0 : nat) (x1 : nat) := fun y0 : nat => ((fun y1 : nat => (~ (x0 = (NUMERAL 0))) -> (Nat.div (Nat.pow x0 x1) (Nat.pow x0 y1)) = (@COND nat (Peano.le y1 x1) (Nat.pow x0 (Nat.sub x1 y1)) (@COND nat (x0 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)))) y0) /\ ((fun y1 : nat => (~ (x0 = (NUMERAL 0))) -> (Nat.modulo (Nat.pow x0 x1) (Nat.pow x0 y1)) = (@COND nat ((Peano.le y1 x1) \/ (x0 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow x0 x1))) y0).
Definition term204 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le y0 x0) -> (Nat.add (Nat.sub x0 y0) y0) = x0) x1.
Definition term1 (x0 : nat) := fun y0 : nat => (~ (Peano.le x0 y0)) = (Peano.lt y0 x0).
Definition term32 (x0 : nat) := ~ (x0 = (NUMERAL (BIT1 0))).
Definition term271 (x0 : nat) (x1 : nat) (x2 : nat) := False -> (Nat.pow x0 (Nat.sub x1 x2)) = (Nat.pow x0 (Nat.sub x1 x2)).
Definition term171 (x0 : nat) := @COND nat (x0 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0).
Definition term180 (x0 : nat) (x1 : nat) (x2 : nat) := @eq nat (Nat.modulo (Nat.pow x1 x0) (Nat.pow x1 x2)).
Definition term195 (x0 : nat) (x1 : nat) (x2 : nat) := True -> (Nat.modulo (Nat.pow x1 x2) (Nat.pow x1 x0)) = (@COND nat ((Peano.le x0 x2) \/ (x1 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow x1 x2)).
Definition term64 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y0 = (Nat.add (Nat.mul y2 y1) y3)) /\ (Peano.lt y3 y1)) -> ((Nat.div y0 y1) = y2) /\ ((Nat.modulo y0 y1) = y3)) -> forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y1 = (Nat.add (Nat.mul y0 y2) y3)) /\ (Peano.lt y3 y2)) -> ((Nat.div y1 y2) = y0) /\ ((Nat.modulo y1 y2) = y3).
Definition term47 (x0 : nat) (x1 : nat) := (fun y0 : Prop => y0 \/ (~ y0)) (Peano.le x0 x1).
Definition term331 (x0 : nat) (x1 : nat) := Nat.mul (NUMERAL 0) (Nat.pow x0 x1).
Definition term345 := S (NUMERAL 0).
Definition term252 := True -> (NUMERAL 0) = (NUMERAL 0).
Definition term38 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.mul (Nat.pow x0 x1) (Nat.pow x0 y0)) = (Nat.pow x0 (Nat.add x1 y0)).
Definition term214 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.mul (Nat.pow x0 x1) (Nat.pow x0 y0)) = (Nat.pow x0 (Nat.add x1 y0))) x2.
Definition term126 (x0 : nat) (x1 : nat) := (forall y0 : nat, (fun y1 : nat => (~ (x0 = (NUMERAL 0))) -> (Nat.div (Nat.pow x0 x1) (Nat.pow x0 y1)) = (@COND nat (Peano.le y1 x1) (Nat.pow x0 (Nat.sub x1 y1)) (@COND nat (x0 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)))) y0) /\ (forall y0 : nat, (fun y1 : nat => (~ (x0 = (NUMERAL 0))) -> (Nat.modulo (Nat.pow x0 x1) (Nat.pow x0 y1)) = (@COND nat ((Peano.le y1 x1) \/ (x0 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow x0 x1))) y0).
Definition term104 (x0 : nat) := (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (x0 = (NUMERAL 0))) -> (Nat.div (Nat.pow x0 y1) (Nat.pow x0 y2)) = (@COND nat (Peano.le y2 y1) (Nat.pow x0 (Nat.sub y1 y2)) (@COND nat (x0 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)))) y0) /\ (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (x0 = (NUMERAL 0))) -> (Nat.modulo (Nat.pow x0 y1) (Nat.pow x0 y2)) = (@COND nat ((Peano.le y2 y1) \/ (x0 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow x0 y1))) y0).
Definition term78 := (forall y0 : nat, (fun y1 : nat => forall y2 : nat, forall y3 : nat, (~ (y1 = (NUMERAL 0))) -> (Nat.div (Nat.pow y1 y2) (Nat.pow y1 y3)) = (@COND nat (Peano.le y3 y2) (Nat.pow y1 (Nat.sub y2 y3)) (@COND nat (y1 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)))) y0) /\ (forall y0 : nat, (fun y1 : nat => forall y2 : nat, forall y3 : nat, (~ (y1 = (NUMERAL 0))) -> (Nat.modulo (Nat.pow y1 y2) (Nat.pow y1 y3)) = (@COND nat ((Peano.le y3 y2) \/ (y1 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow y1 y2))) y0).
Definition term336 (x0 : nat) (x1 : nat) := Peano.lt (Nat.pow x0 x1).
Definition term100 (x0 : nat) := (forall y0 : nat, forall y1 : nat, (~ (x0 = (NUMERAL 0))) -> (Nat.div (Nat.pow x0 y0) (Nat.pow x0 y1)) = (@COND nat (Peano.le y1 y0) (Nat.pow x0 (Nat.sub y0 y1)) (@COND nat (x0 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)))) /\ (forall y0 : nat, forall y1 : nat, (~ (x0 = (NUMERAL 0))) -> (Nat.modulo (Nat.pow x0 y0) (Nat.pow x0 y1)) = (@COND nat ((Peano.le y1 y0) \/ (x0 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow x0 y0))).
Definition term94 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, (~ (y0 = (NUMERAL 0))) -> (Nat.div (Nat.pow y0 y1) (Nat.pow y0 y2)) = (@COND nat (Peano.le y2 y1) (Nat.pow y0 (Nat.sub y1 y2)) (@COND nat (y0 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)))) /\ (forall y0 : nat, forall y1 : nat, forall y2 : nat, (~ (y0 = (NUMERAL 0))) -> (Nat.modulo (Nat.pow y0 y1) (Nat.pow y0 y2)) = (@COND nat ((Peano.le y2 y1) \/ (y0 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow y0 y1))).
Definition term159 (x0 : nat) (x1 : nat) := Nat.div (Nat.pow (NUMERAL 0) x0) (Nat.pow (NUMERAL 0) x1).
Definition term322 (x0 : nat) := (fun y0 : nat => (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) x0.
Definition term102 := fun y0 : nat => (forall y1 : nat, forall y2 : nat, (~ (y0 = (NUMERAL 0))) -> (Nat.div (Nat.pow y0 y1) (Nat.pow y0 y2)) = (@COND nat (Peano.le y2 y1) (Nat.pow y0 (Nat.sub y1 y2)) (@COND nat (y0 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)))) /\ (forall y1 : nat, forall y2 : nat, (~ (y0 = (NUMERAL 0))) -> (Nat.modulo (Nat.pow y0 y1) (Nat.pow y0 y2)) = (@COND nat ((Peano.le y2 y1) \/ (y0 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow y0 y1))).
Definition term155 (x0 : nat) := Nat.pow (NUMERAL 0) x0.
Definition term138 (x0 : nat) (x1 : nat) := forall y0 : nat, (fun y1 : nat => (~ (x0 = (NUMERAL 0))) -> (Nat.modulo (Nat.pow x0 x1) (Nat.pow x0 y1)) = (@COND nat ((Peano.le y1 x1) \/ (x0 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow x0 x1))) y0.
Definition term133 (x0 : nat) (x1 : nat) := forall y0 : nat, (fun y1 : nat => (~ (x1 = (NUMERAL 0))) -> (Nat.div (Nat.pow x1 x0) (Nat.pow x1 y1)) = (@COND nat (Peano.le y1 x0) (Nat.pow x1 (Nat.sub x0 y1)) (@COND nat (x1 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)))) y0.
Definition term216 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) (x3 : Prop) (x4 : a0) := forall y0 : a0, (x0 = x3) -> (x3 -> x1 = x4) -> ((~ x3) -> x2 = y0) -> (@COND a0 x0 x1 x2) = (@COND a0 x3 x4 y0).
Definition term354 := S (S (NUMERAL 0)).
Definition term128 (x0 : nat) (x1 : nat) := fun y0 : nat => (~ (x1 = (NUMERAL 0))) -> (Nat.div (Nat.pow x1 x0) (Nat.pow x1 y0)) = (@COND nat (Peano.le y0 x0) (Nat.pow x1 (Nat.sub x0 y0)) (@COND nat (x1 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0))).
Definition term77 (x0 : nat -> Prop) (x1 : nat -> Prop) := forall y0 : nat, (x0 y0) /\ (x1 y0).
Definition term277 (x0 : nat) := Nat.mul (@COND nat (x0 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)).
Definition term359 (x0 : nat) := (x0 = (NUMERAL 0)) \/ (Peano.lt x0 (NUMERAL 0)).
Definition term211 (x0 : nat) (x1 : nat) := (~ (x0 = (NUMERAL 0))) \/ (x1 = (NUMERAL 0)).
Definition term124 (x0 : nat) := fun y0 : nat => (forall y1 : nat, (~ (x0 = (NUMERAL 0))) -> (Nat.div (Nat.pow x0 y0) (Nat.pow x0 y1)) = (@COND nat (Peano.le y1 y0) (Nat.pow x0 (Nat.sub y0 y1)) (@COND nat (x0 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)))) /\ (forall y1 : nat, (~ (x0 = (NUMERAL 0))) -> (Nat.modulo (Nat.pow x0 y0) (Nat.pow x0 y1)) = (@COND nat ((Peano.le y1 y0) \/ (x0 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow x0 y0))).
Definition term73 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => ((forall y1 : a0, x0 y1) /\ (forall y1 : a0, y0 y1)) = (forall y1 : a0, (x0 y1) /\ (y0 y1))) x1.
Definition term156 (x0 : nat) (x1 : nat) := Nat.div (Nat.pow x0 x1).
Definition term200 (x0 : nat) := (fun y0 : nat => (Nat.add y0 (NUMERAL 0)) = y0) x0.
Definition term178 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.modulo (Nat.pow x1 x0) (Nat.pow x1 x2).
Definition term250 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := (((Peano.le x0 x2) \/ (x1 = (NUMERAL (BIT1 0)))) = True) -> (True -> (NUMERAL 0) = x3) -> ((~ True) -> (Nat.pow x1 x2) = x4) -> (@COND nat ((Peano.le x0 x2) \/ (x1 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow x1 x2)) = (@COND nat True x3 x4).
Definition term275 (x0 : nat) (x1 : nat) (x2 : nat) := ((~ False) -> (@COND nat (x2 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)) = (@COND nat (x2 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0))) -> (@COND nat (Peano.le x1 x0) (Nat.pow x2 (Nat.sub x0 x1)) (@COND nat (x2 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0))) = (@COND nat False (Nat.pow x2 (Nat.sub x0 x1)) (@COND nat (x2 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0))).
Definition term233 (x0 : nat) (x1 : nat) (x2 : nat) := ((~ True) -> (@COND nat (x2 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)) = (@COND nat (x2 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0))) -> (@COND nat (Peano.le x1 x0) (Nat.pow x2 (Nat.sub x0 x1)) (@COND nat (x2 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0))) = (@COND nat True (Nat.pow x2 (Nat.sub x0 x1)) (@COND nat (x2 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0))).
Definition term337 (x0 : nat) := and (x0 = (NUMERAL 0)).
Definition term236 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.pow x0 (Nat.sub x1 x2)).
Definition term153 (x0 : nat) := imp (~ (x0 = (NUMERAL 0))).
Definition term26 := forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False.
Definition term158 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.div (Nat.pow x1 x0) (Nat.pow x1 x2).
Definition term273 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((~ False) -> (@COND nat (x0 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)) = x3) -> (@COND nat (Peano.le x2 x1) (Nat.pow x0 (Nat.sub x1 x2)) (@COND nat (x0 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0))) = (@COND nat False (Nat.pow x0 (Nat.sub x1 x2)) x3).
Definition term231 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((~ True) -> (@COND nat (x0 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)) = x3) -> (@COND nat (Peano.le x2 x1) (Nat.pow x0 (Nat.sub x1 x2)) (@COND nat (x0 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0))) = (@COND nat True (Nat.pow x0 (Nat.sub x1 x2)) x3).
Definition term143 (x0 : nat) (x1 : nat) (x2 : nat) := ((fun y0 : nat => (~ (x0 = (NUMERAL 0))) -> (Nat.div (Nat.pow x0 x1) (Nat.pow x0 y0)) = (@COND nat (Peano.le y0 x1) (Nat.pow x0 (Nat.sub x1 y0)) (@COND nat (x0 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)))) x2) /\ ((fun y0 : nat => (~ (x0 = (NUMERAL 0))) -> (Nat.modulo (Nat.pow x0 x1) (Nat.pow x0 y0)) = (@COND nat ((Peano.le y0 x1) \/ (x0 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow x0 x1))) x2).
Definition term319 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.lt (Nat.pow x1 x0) (Nat.pow x1 x2).
Definition term312 := Peano.lt (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term58 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x0 = (Nat.add (Nat.mul x1 x3) x2)) /\ (Peano.lt x2 x3).
Definition term74 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term191 (x0 : nat) (x1 : nat) := False -> (Nat.modulo (Nat.pow (NUMERAL 0) x1) (Nat.pow (NUMERAL 0) x0)) = (@COND nat ((Peano.le x0 x1) \/ ((NUMERAL 0) = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow (NUMERAL 0) x1)).
Definition term201 (x0 : nat) := Nat.add x0 (NUMERAL 0).
Definition term170 := @COND nat ((NUMERAL 0) = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)).
Definition term210 (x0 : nat) (x1 : nat) := Peano.lt (NUMERAL 0) (Nat.pow x0 x1).
Definition term342 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.le (NUMERAL (BIT0 (BIT1 0))) x0) /\ (Peano.lt x1 x2)) \/ False.
Definition term56 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => ((x1 = (Nat.add (Nat.mul x0 x2) y0)) /\ (Peano.lt y0 x2)) -> ((Nat.div x1 x2) = x0) /\ ((Nat.modulo x1 x2) = y0)) x3.
Definition term317 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.lt (Nat.pow x0 x1) (Nat.pow x0 y0)) = (((Peano.le (NUMERAL (BIT0 (BIT1 0))) x0) /\ (Peano.lt x1 y0)) \/ ((x0 = (NUMERAL 0)) /\ ((~ (x1 = (NUMERAL 0))) /\ (y0 = (NUMERAL 0))))).
Definition term208 (x0 : nat) := forall y0 : nat, (Peano.lt (NUMERAL 0) (Nat.pow y0 x0)) = ((~ (y0 = (NUMERAL 0))) \/ (x0 = (NUMERAL 0))).
Definition term316 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt (Nat.pow x0 y0) (Nat.pow x0 y1)) = (((Peano.le (NUMERAL (BIT0 (BIT1 0))) x0) /\ (Peano.lt y0 y1)) \/ ((x0 = (NUMERAL 0)) /\ ((~ (y0 = (NUMERAL 0))) /\ (y1 = (NUMERAL 0)))))) x1.
Definition term213 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul (Nat.pow x0 y0) (Nat.pow x0 y1)) = (Nat.pow x0 (Nat.add y0 y1))) x1.
Definition term113 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (~ (x0 = (NUMERAL 0))) -> (Nat.modulo (Nat.pow x0 y0) (Nat.pow x0 y1)) = (@COND nat ((Peano.le y1 y0) \/ (x0 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow x0 y0))) x1.
Definition term108 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (~ (x0 = (NUMERAL 0))) -> (Nat.div (Nat.pow x0 y0) (Nat.pow x0 y1)) = (@COND nat (Peano.le y1 y0) (Nat.pow x0 (Nat.sub y0 y1)) (@COND nat (x0 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)))) x1.
Definition term272 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (False -> (Nat.pow x0 (Nat.sub x1 x2)) = (Nat.pow x0 (Nat.sub x1 x2))) -> ((~ False) -> (@COND nat (x0 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)) = x3) -> (@COND nat (Peano.le x2 x1) (Nat.pow x0 (Nat.sub x1 x2)) (@COND nat (x0 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0))) = (@COND nat False (Nat.pow x0 (Nat.sub x1 x2)) x3).
Definition term288 (x0 : nat) (x1 : nat) := @COND nat (x0 = (NUMERAL (BIT1 0))) (NUMERAL 0) (Nat.pow x0 x1).
Definition term254 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((~ True) -> (Nat.pow x1 x2) = x3) -> (@COND nat ((Peano.le x0 x2) \/ (x1 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow x1 x2)) = (@COND nat True (NUMERAL 0) x3).
Definition term364 (x0 : nat) := ~ ((x0 = (S (NUMERAL 0))) \/ (x0 = (NUMERAL 0))).
Definition term313 := True /\ (Peano.lt (NUMERAL 0) (NUMERAL (BIT1 0))).
Definition term154 := Nat.pow (NUMERAL 0).
Definition term70 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term177 (x0 : nat) := Nat.modulo (Nat.pow (NUMERAL 0) x0).
Definition term165 (x0 : nat) (x1 : nat) (x2 : nat) := @COND nat (Peano.le x2 x1) (Nat.pow x0 (Nat.sub x1 x2)).
Definition term14 := fun y0 : nat => forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0).
Definition term5 := fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0).
Definition term25 (x0 : nat) (x1 : nat) := (x0 = x1) \/ (Peano.lt x0 x1).
Definition term48 (x0 : nat) (x1 : nat) := (Peano.le x0 x1) \/ (~ (Peano.le x0 x1)).
Definition term188 (x0 : nat) (x1 : nat) := @COND nat ((Peano.le x0 x1) \/ ((NUMERAL 0) = (NUMERAL (BIT1 0)))) (NUMERAL 0).
Definition term136 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x1 = (NUMERAL 0))) -> (Nat.modulo (Nat.pow x1 x2) (Nat.pow x1 x0)) = (@COND nat ((Peano.le x0 x2) \/ (x1 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow x1 x2)).
Definition term343 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le (NUMERAL (BIT0 (BIT1 0))) x0) /\ (Peano.lt x1 x2).
Definition term284 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((x2 = (NUMERAL (BIT1 0))) -> (NUMERAL 0) = (NUMERAL 0)) -> ((~ (x2 = (NUMERAL (BIT1 0)))) -> (Nat.pow x2 x1) = x3) -> (@COND nat ((Peano.le x0 x1) \/ (x2 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow x2 x1)) = (@COND nat (x2 = (NUMERAL (BIT1 0))) (NUMERAL 0) x3).
Definition term199 := forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0.
Definition term33 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.pow x0 (Nat.add x1 x2).
Definition term0 (x0 : nat) (x1 : nat) := ~ (Peano.le x0 x1).
Definition term182 (x0 : nat) (x1 : nat) := or (Peano.le x0 x1).
Definition term193 (x0 : nat) (x1 : nat) (x2 : nat) := True -> (Nat.div (Nat.pow x2 x0) (Nat.pow x2 x1)) = (@COND nat (Peano.le x1 x0) (Nat.pow x2 (Nat.sub x0 x1)) (@COND nat (x2 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0))).
Definition term306 := Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term167 (x0 : nat) := @COND nat (x0 = (NUMERAL (BIT1 0))).
Definition term238 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.pow x1 (Nat.sub x0 x2)) (Nat.pow x1 x2).
Definition term114 (x0 : nat) (x1 : nat) := forall y0 : nat, (~ (x0 = (NUMERAL 0))) -> (Nat.modulo (Nat.pow x0 x1) (Nat.pow x0 y0)) = (@COND nat ((Peano.le y0 x1) \/ (x0 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow x0 x1)).
Definition term109 (x0 : nat) (x1 : nat) := forall y0 : nat, (~ (x1 = (NUMERAL 0))) -> (Nat.div (Nat.pow x1 x0) (Nat.pow x1 y0)) = (@COND nat (Peano.le y0 x0) (Nat.pow x1 (Nat.sub x0 y0)) (@COND nat (x1 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0))).
Definition term27 (x0 : nat) := (fun y0 : nat => (Peano.lt y0 (NUMERAL 0)) = False) x0.
Definition term10 (x0 : nat) := fun y0 : nat => (~ (Peano.lt x0 y0)) = (Peano.le y0 x0).
Definition term209 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt (NUMERAL 0) (Nat.pow y0 x0)) = ((~ (y0 = (NUMERAL 0))) \/ (x0 = (NUMERAL 0)))) x1.
Definition term281 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := (((Peano.le x0 x1) \/ (x2 = (NUMERAL (BIT1 0)))) = (x2 = (NUMERAL (BIT1 0)))) -> ((x2 = (NUMERAL (BIT1 0))) -> (NUMERAL 0) = x3) -> ((~ (x2 = (NUMERAL (BIT1 0)))) -> (Nat.pow x2 x1) = x4) -> (@COND nat ((Peano.le x0 x1) \/ (x2 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow x2 x1)) = (@COND nat (x2 = (NUMERAL (BIT1 0))) x3 x4).
Definition term269 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := ((Peano.le x1 x0) = False) -> (False -> (Nat.pow x2 (Nat.sub x0 x1)) = x3) -> ((~ False) -> (@COND nat (x2 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)) = x4) -> (@COND nat (Peano.le x1 x0) (Nat.pow x2 (Nat.sub x0 x1)) (@COND nat (x2 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0))) = (@COND nat False x3 x4).
Definition term120 (x0 : nat) (x1 : nat) := and (forall y0 : nat, (~ (x1 = (NUMERAL 0))) -> (Nat.div (Nat.pow x1 x0) (Nat.pow x1 y0)) = (@COND nat (Peano.le y0 x0) (Nat.pow x1 (Nat.sub x0 y0)) (@COND nat (x1 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)))).
Definition term160 (x0 : nat) (x1 : nat) (x2 : nat) := @eq nat (Nat.div (Nat.pow x1 x0) (Nat.pow x1 x2)).
Definition term349 := Peano.lt (NUMERAL 0) (NUMERAL 0).
Definition term346 := Peano.lt (NUMERAL 0) (S (NUMERAL 0)).
Definition term366 (x0 : nat) := and (~ ((x0 = (S (NUMERAL 0))) \/ (x0 = (NUMERAL 0)))).
Definition term292 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.lt (@COND nat (x1 = (NUMERAL (BIT1 0))) (NUMERAL 0) (Nat.pow x1 x0)) (Nat.pow x1 x2).
Definition term264 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.lt (@COND nat ((Peano.le x2 x0) \/ (x1 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow x1 x0)) (Nat.pow x1 x2).
Definition term137 (x0 : nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => (~ (x0 = (NUMERAL 0))) -> (Nat.modulo (Nat.pow x0 x1) (Nat.pow x0 y1)) = (@COND nat ((Peano.le y1 x1) \/ (x0 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow x0 x1))) y0.
Definition term132 (x0 : nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => (~ (x1 = (NUMERAL 0))) -> (Nat.div (Nat.pow x1 x0) (Nat.pow x1 y1)) = (@COND nat (Peano.le y1 x0) (Nat.pow x1 (Nat.sub x0 y1)) (@COND nat (x1 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)))) y0.
Definition term326 (x0 : nat) := Nat.add (NUMERAL 0) x0.
Definition term309 := @COND nat True (NUMERAL 0).
Definition term301 := Nat.pow (NUMERAL (BIT1 0)).
Definition term268 (x0 : nat) (x1 : nat) := (~ (Peano.le x0 x1)) -> (Peano.le x0 x1) = False.
Definition term360 (x0 : nat) := or (x0 = (NUMERAL 0)).
Definition term173 (x0 : nat) (x1 : nat) (x2 : nat) := @COND nat (Peano.le x1 x0) (Nat.pow x2 (Nat.sub x0 x1)) (@COND nat (x2 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)).
Definition term339 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = (NUMERAL 0)) /\ ((~ (x1 = (NUMERAL 0))) /\ (x2 = (NUMERAL 0))).
Definition term315 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.lt (Nat.pow x0 y0) (Nat.pow x0 y1)) = (((Peano.le (NUMERAL (BIT0 (BIT1 0))) x0) /\ (Peano.lt y0 y1)) \/ ((x0 = (NUMERAL 0)) /\ ((~ (y0 = (NUMERAL 0))) /\ (y1 = (NUMERAL 0))))).
Definition term244 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : Prop) := forall y0 : nat, forall y1 : nat, (((Peano.le x0 x2) \/ (x1 = (NUMERAL (BIT1 0)))) = x3) -> (x3 -> (NUMERAL 0) = y0) -> ((~ x3) -> (Nat.pow x1 x2) = y1) -> (@COND nat ((Peano.le x0 x2) \/ (x1 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow x1 x2)) = (@COND nat x3 y0 y1).
Definition term222 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : Prop) := forall y0 : nat, forall y1 : nat, ((Peano.le x1 x0) = x3) -> (x3 -> (Nat.pow x2 (Nat.sub x0 x1)) = y0) -> ((~ x3) -> (@COND nat (x2 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)) = y1) -> (@COND nat (Peano.le x1 x0) (Nat.pow x2 (Nat.sub x0 x1)) (@COND nat (x2 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0))) = (@COND nat x3 y0 y1).
Definition term151 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((~ (y0 = (NUMERAL 0))) -> (Nat.div (Nat.pow y0 y1) (Nat.pow y0 y2)) = (@COND nat (Peano.le y2 y1) (Nat.pow y0 (Nat.sub y1 y2)) (@COND nat (y0 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)))) /\ ((~ (y0 = (NUMERAL 0))) -> (Nat.modulo (Nat.pow y0 y1) (Nat.pow y0 y2)) = (@COND nat ((Peano.le y2 y1) \/ (y0 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow y0 y1))).
Definition term149 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((~ (x0 = (NUMERAL 0))) -> (Nat.div (Nat.pow x0 y0) (Nat.pow x0 y1)) = (@COND nat (Peano.le y1 y0) (Nat.pow x0 (Nat.sub y0 y1)) (@COND nat (x0 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)))) /\ ((~ (x0 = (NUMERAL 0))) -> (Nat.modulo (Nat.pow x0 y0) (Nat.pow x0 y1)) = (@COND nat ((Peano.le y1 y0) \/ (x0 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow x0 y0))).
Definition term93 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (~ (y0 = (NUMERAL 0))) -> (Nat.modulo (Nat.pow y0 y1) (Nat.pow y0 y2)) = (@COND nat ((Peano.le y2 y1) \/ (y0 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow y0 y1)).
Definition term90 (x0 : nat) := forall y0 : nat, forall y1 : nat, (~ (x0 = (NUMERAL 0))) -> (Nat.modulo (Nat.pow x0 y0) (Nat.pow x0 y1)) = (@COND nat ((Peano.le y1 y0) \/ (x0 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow x0 y0)).
Definition term86 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (~ (y0 = (NUMERAL 0))) -> (Nat.div (Nat.pow y0 y1) (Nat.pow y0 y2)) = (@COND nat (Peano.le y2 y1) (Nat.pow y0 (Nat.sub y1 y2)) (@COND nat (y0 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0))).
Definition term83 (x0 : nat) := forall y0 : nat, forall y1 : nat, (~ (x0 = (NUMERAL 0))) -> (Nat.div (Nat.pow x0 y0) (Nat.pow x0 y1)) = (@COND nat (Peano.le y1 y0) (Nat.pow x0 (Nat.sub y0 y1)) (@COND nat (x0 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0))).
Definition term63 := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y1 = (Nat.add (Nat.mul y0 y2) y3)) /\ (Peano.lt y3 y2)) -> ((Nat.div y1 y2) = y0) /\ ((Nat.modulo y1 y2) = y3).
Definition term62 (x0 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((y0 = (Nat.add (Nat.mul x0 y1) y2)) /\ (Peano.lt y2 y1)) -> ((Nat.div y0 y1) = x0) /\ ((Nat.modulo y0 y1) = y2).
Definition term61 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, ((x1 = (Nat.add (Nat.mul x0 y0) y1)) /\ (Peano.lt y1 y0)) -> ((Nat.div x1 y0) = x0) /\ ((Nat.modulo x1 y0) = y1).
Definition term53 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, ((x0 = (Nat.add (Nat.mul y0 x1) y1)) /\ (Peano.lt y1 x1)) -> ((Nat.div x0 x1) = y0) /\ ((Nat.modulo x0 x1) = y1).
Definition term51 (x0 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((x0 = (Nat.add (Nat.mul y1 y0) y2)) /\ (Peano.lt y2 y0)) -> ((Nat.div x0 y0) = y1) /\ ((Nat.modulo x0 y0) = y2).
Definition term49 := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y0 = (Nat.add (Nat.mul y2 y1) y3)) /\ (Peano.lt y3 y1)) -> ((Nat.div y0 y1) = y2) /\ ((Nat.modulo y0 y1) = y3).
Definition term46 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.mul (Nat.pow y0 y1) (Nat.pow y0 y2)) = (Nat.pow y0 (Nat.add y1 y2)).
Definition term45 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.pow y0 (Nat.add y1 y2)) = (Nat.mul (Nat.pow y0 y1) (Nat.pow y0 y2)).
Definition term42 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.mul (Nat.pow x0 y0) (Nat.pow x0 y1)) = (Nat.pow x0 (Nat.add y0 y1)).
Definition term41 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.pow x0 (Nat.add y0 y1)) = (Nat.mul (Nat.pow x0 y0) (Nat.pow x0 y1)).
Definition term20 := forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)).
Definition term17 := forall y0 : nat, forall y1 : nat, (Peano.le y1 y0) = (~ (Peano.lt y0 y1)).
Definition term16 := forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0).
Definition term8 := forall y0 : nat, forall y1 : nat, (Peano.lt y1 y0) = (~ (Peano.le y0 y1)).
Definition term7 := forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0).
Definition term356 (x0 : nat) := Peano.lt x0 (S (S (NUMERAL 0))).
Definition term194 (x0 : nat) (x1 : nat) (x2 : nat) := and ((Nat.div (Nat.pow x2 x0) (Nat.pow x2 x1)) = (@COND nat (Peano.le x1 x0) (Nat.pow x2 (Nat.sub x0 x1)) (@COND nat (x2 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)))).
Definition term99 (x0 : nat) := ((fun y0 : nat => forall y1 : nat, forall y2 : nat, (~ (y0 = (NUMERAL 0))) -> (Nat.div (Nat.pow y0 y1) (Nat.pow y0 y2)) = (@COND nat (Peano.le y2 y1) (Nat.pow y0 (Nat.sub y1 y2)) (@COND nat (y0 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)))) x0) /\ ((fun y0 : nat => forall y1 : nat, forall y2 : nat, (~ (y0 = (NUMERAL 0))) -> (Nat.modulo (Nat.pow y0 y1) (Nat.pow y0 y2)) = (@COND nat ((Peano.le y2 y1) \/ (y0 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow y0 y1))) x0).
Definition term69 (x0 : nat) := (x0 = (NUMERAL 0)) \/ (~ (x0 = (NUMERAL 0))).
Definition term67 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => forall y1 : nat, ((x1 = (Nat.add (Nat.mul x0 y0) y1)) /\ (Peano.lt y1 y0)) -> ((Nat.div x1 y0) = x0) /\ ((Nat.modulo x1 y0) = y1)) x2.
Definition term54 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => forall y1 : nat, ((x0 = (Nat.add (Nat.mul y0 x1) y1)) /\ (Peano.lt y1 x1)) -> ((Nat.div x0 x1) = y0) /\ ((Nat.modulo x0 x1) = y1)) x2.
Definition term12 (x0 : nat) := forall y0 : nat, (~ (Peano.lt x0 y0)) = (Peano.le y0 x0).
Definition term3 (x0 : nat) := forall y0 : nat, (~ (Peano.le x0 y0)) = (Peano.lt y0 x0).
Definition term227 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := ((Peano.le x1 x0) = True) -> (True -> (Nat.pow x2 (Nat.sub x0 x1)) = x3) -> ((~ True) -> (@COND nat (x2 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)) = x4) -> (@COND nat (Peano.le x1 x0) (Nat.pow x2 (Nat.sub x0 x1)) (@COND nat (x2 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0))) = (@COND nat True x3 x4).
Definition term66 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((y0 = (Nat.add (Nat.mul x0 y1) y2)) /\ (Peano.lt y2 y1)) -> ((Nat.div y0 y1) = x0) /\ ((Nat.modulo y0 y1) = y2)) x1.
Definition term52 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((x0 = (Nat.add (Nat.mul y1 y0) y2)) /\ (Peano.lt y2 y0)) -> ((Nat.div x0 y0) = y1) /\ ((Nat.modulo x0 y0) = y2)) x1.
Definition term263 := Peano.lt (NUMERAL 0).
Definition term174 (x0 : nat) (x1 : nat) := @COND nat (Peano.le x1 x0) (Nat.pow (NUMERAL 0) (Nat.sub x0 x1)) (@COND nat ((NUMERAL 0) = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)).
Definition term357 (x0 : nat) := (x0 = (S (NUMERAL 0))) \/ (Peano.lt x0 (S (NUMERAL 0))).
Definition term248 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : Prop) (x4 : nat) (x5 : nat) := (((Peano.le x0 x2) \/ (x1 = (NUMERAL (BIT1 0)))) = x3) -> (x3 -> (NUMERAL 0) = x4) -> ((~ x3) -> (Nat.pow x1 x2) = x5) -> (@COND nat ((Peano.le x0 x2) \/ (x1 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow x1 x2)) = (@COND nat x3 x4 x5).
Definition term29 (x0 : nat) := (fun y0 : Prop => y0 \/ (~ y0)) (x0 = (NUMERAL (BIT1 0))).
Definition term24 (x0 : nat) (x1 : nat) := Peano.lt x0 (S x1).
Definition term353 := S (NUMERAL (BIT1 0)).
Definition term72 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, ((forall y1 : a0, x0 y1) /\ (forall y1 : a0, y0 y1)) = (forall y1 : a0, (x0 y1) /\ (y0 y1)).
Definition term278 (x0 : nat) (x1 : nat) := Nat.mul (@COND nat (x0 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)) (Nat.pow x0 x1).
Definition term162 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.pow x0 (Nat.sub x1 x2).
Definition term324 := forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0.
Definition term296 := forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0.
Definition term234 (x0 : nat) (x1 : nat) (x2 : nat) := @COND nat True (Nat.pow x2 (Nat.sub x0 x1)) (@COND nat (x2 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)).
Definition term325 (x0 : nat) := (fun y0 : nat => (Nat.add (NUMERAL 0) y0) = y0) x0.
Definition term297 (x0 : nat) := (fun y0 : nat => (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) x0.
Definition term11 (x0 : nat) := fun y0 : nat => (Peano.le y0 x0) = (~ (Peano.lt x0 y0)).
Definition term144 (x0 : nat) (x1 : nat) (x2 : nat) := ((~ (x1 = (NUMERAL 0))) -> (Nat.div (Nat.pow x1 x2) (Nat.pow x1 x0)) = (@COND nat (Peano.le x0 x2) (Nat.pow x1 (Nat.sub x2 x0)) (@COND nat (x1 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)))) /\ ((~ (x1 = (NUMERAL 0))) -> (Nat.modulo (Nat.pow x1 x2) (Nat.pow x1 x0)) = (@COND nat ((Peano.le x0 x2) \/ (x1 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow x1 x2))).
Definition term239 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.pow x0 (Nat.add (Nat.sub x1 x2) x2).
Definition term344 (x0 : nat) (x1 : nat) (x2 : nat) := True /\ ((Peano.le (NUMERAL (BIT0 (BIT1 0))) x0) /\ (Peano.lt x1 x2)).
Definition term71 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, ((forall y2 : a0, y0 y2) /\ (forall y2 : a0, y1 y2)) = (forall y2 : a0, (y0 y2) /\ (y1 y2))) x0.
Definition term276 (x0 : nat) (x1 : nat) (x2 : nat) := @COND nat False (Nat.pow x2 (Nat.sub x0 x1)) (@COND nat (x2 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)).
Definition term37 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.pow x1 (Nat.add x0 y0)) = (Nat.mul (Nat.pow x1 x0) (Nat.pow x1 y0)).
Definition term22 (x0 : nat) := forall y0 : nat, (Peano.lt x0 (S y0)) = ((x0 = y0) \/ (Peano.lt x0 y0)).
Definition term57 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((x1 = (Nat.add (Nat.mul x0 x2) x3)) /\ (Peano.lt x3 x2)) -> ((Nat.div x1 x2) = x0) /\ ((Nat.modulo x1 x2) = x3).
Definition term255 (x0 : nat) (x1 : nat) := (~ True) -> (Nat.pow x0 x1) = (Nat.pow x0 x1).
Definition term265 (x0 : nat) := or (~ (x0 = (NUMERAL 0))).
Definition term329 := @COND nat False (NUMERAL (BIT1 0)) (NUMERAL 0).
Definition term365 (x0 : nat) := and (Peano.le (NUMERAL (BIT0 (BIT1 0))) x0).
Definition term168 := @COND nat ((NUMERAL 0) = (NUMERAL (BIT1 0))).
Definition term76 (x0 : nat -> Prop) (x1 : nat -> Prop) := (forall y0 : nat, x0 y0) /\ (forall y0 : nat, x1 y0).
Definition term335 (x0 : nat) (x1 : nat) := Nat.add (NUMERAL 0) (Nat.pow x0 x1).
Definition term362 (x0 : nat) := or (x0 = (S (NUMERAL 0))).
Definition term308 (x0 : nat) := @COND nat (x0 = (NUMERAL (BIT1 0))) (NUMERAL 0).
Definition term311 := Nat.add (NUMERAL (BIT1 0)) (NUMERAL 0).
Definition term260 (x0 : nat) (x1 : nat) := @eq nat (Nat.pow x0 x1).
Definition term242 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : Prop, forall y1 : nat, forall y2 : nat, (((Peano.le x0 x2) \/ (x1 = (NUMERAL (BIT1 0)))) = y0) -> (y0 -> (NUMERAL 0) = y1) -> ((~ y0) -> (Nat.pow x1 x2) = y2) -> (@COND nat ((Peano.le x0 x2) \/ (x1 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow x1 x2)) = (@COND nat y0 y1 y2).
Definition term220 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : Prop, forall y1 : nat, forall y2 : nat, ((Peano.le x1 x0) = y0) -> (y0 -> (Nat.pow x2 (Nat.sub x0 x1)) = y1) -> ((~ y0) -> (@COND nat (x2 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)) = y2) -> (@COND nat (Peano.le x1 x0) (Nat.pow x2 (Nat.sub x0 x1)) (@COND nat (x2 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0))) = (@COND nat y0 y1 y2).
Definition term219 (x0 : Prop) (x1 : nat) (x2 : nat) := forall y0 : Prop, forall y1 : nat, forall y2 : nat, (x0 = y0) -> (y0 -> x1 = y1) -> ((~ y0) -> x2 = y2) -> (@COND nat x0 x1 x2) = (@COND nat y0 y1 y2).
Definition term218 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) := forall y0 : Prop, forall y1 : a0, forall y2 : a0, (x0 = y0) -> (y0 -> x1 = y1) -> ((~ y0) -> x2 = y2) -> (@COND a0 x0 x1 x2) = (@COND a0 y0 y1 y2).
Definition term307 := Nat.add (NUMERAL (BIT1 0)).
Definition term119 (x0 : nat) (x1 : nat) := and ((fun y0 : nat => forall y1 : nat, (~ (x0 = (NUMERAL 0))) -> (Nat.div (Nat.pow x0 y0) (Nat.pow x0 y1)) = (@COND nat (Peano.le y1 y0) (Nat.pow x0 (Nat.sub y0 y1)) (@COND nat (x0 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)))) x1).
Definition term198 := (forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))).
Definition term352 := NUMERAL (BIT0 (BIT1 0)).
Definition term304 := @COND nat True (NUMERAL (BIT1 0)) (NUMERAL 0).
Definition term363 (x0 : nat) := (x0 = (S (NUMERAL 0))) \/ (x0 = (NUMERAL 0)).
Definition term36 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.mul (Nat.pow x0 x1) (Nat.pow x0 y0)) = (Nat.pow x0 (Nat.add x1 y0)).
Definition term358 (x0 : nat) := Peano.lt x0 (S (NUMERAL 0)).
Definition term23 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt x0 (S y0)) = ((x0 = y0) \/ (Peano.lt x0 y0))) x1.
Definition term184 (x0 : nat) (x1 : nat) := (Peano.le x0 x1) \/ ((NUMERAL 0) = (NUMERAL (BIT1 0))).
Definition term146 (x0 : nat) (x1 : nat) := fun y0 : nat => ((~ (x0 = (NUMERAL 0))) -> (Nat.div (Nat.pow x0 x1) (Nat.pow x0 y0)) = (@COND nat (Peano.le y0 x1) (Nat.pow x0 (Nat.sub x1 y0)) (@COND nat (x0 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)))) /\ ((~ (x0 = (NUMERAL 0))) -> (Nat.modulo (Nat.pow x0 x1) (Nat.pow x0 y0)) = (@COND nat ((Peano.le y0 x1) \/ (x0 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow x0 x1))).
Definition term285 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((~ (x2 = (NUMERAL (BIT1 0)))) -> (Nat.pow x2 x1) = x3) -> (@COND nat ((Peano.le x0 x1) \/ (x2 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow x2 x1)) = (@COND nat (x2 = (NUMERAL (BIT1 0))) (NUMERAL 0) x3).
Definition term121 (x0 : nat) (x1 : nat) := ((fun y0 : nat => forall y1 : nat, (~ (x0 = (NUMERAL 0))) -> (Nat.div (Nat.pow x0 y0) (Nat.pow x0 y1)) = (@COND nat (Peano.le y1 y0) (Nat.pow x0 (Nat.sub y0 y1)) (@COND nat (x0 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)))) x1) /\ ((fun y0 : nat => forall y1 : nat, (~ (x0 = (NUMERAL 0))) -> (Nat.modulo (Nat.pow x0 y0) (Nat.pow x0 y1)) = (@COND nat ((Peano.le y1 y0) \/ (x0 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow x0 y0))) x1).
Definition term122 (x0 : nat) (x1 : nat) := (forall y0 : nat, (~ (x0 = (NUMERAL 0))) -> (Nat.div (Nat.pow x0 x1) (Nat.pow x0 y0)) = (@COND nat (Peano.le y0 x1) (Nat.pow x0 (Nat.sub x1 y0)) (@COND nat (x0 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)))) /\ (forall y0 : nat, (~ (x0 = (NUMERAL 0))) -> (Nat.modulo (Nat.pow x0 x1) (Nat.pow x0 y0)) = (@COND nat ((Peano.le y0 x1) \/ (x0 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow x0 x1))).
Definition term310 := @COND nat True (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term347 := ((NUMERAL 0) = (NUMERAL 0)) \/ (Peano.lt (NUMERAL 0) (NUMERAL 0)).
Definition term332 := Nat.add (NUMERAL 0).
Definition term28 (x0 : nat) := Peano.lt x0 (NUMERAL 0).
Definition term98 (x0 : nat) := and (forall y0 : nat, forall y1 : nat, (~ (x0 = (NUMERAL 0))) -> (Nat.div (Nat.pow x0 y0) (Nat.pow x0 y1)) = (@COND nat (Peano.le y1 y0) (Nat.pow x0 (Nat.sub y0 y1)) (@COND nat (x0 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)))).
Definition term88 := and (forall y0 : nat, forall y1 : nat, forall y2 : nat, (~ (y0 = (NUMERAL 0))) -> (Nat.div (Nat.pow y0 y1) (Nat.pow y0 y2)) = (@COND nat (Peano.le y2 y1) (Nat.pow y0 (Nat.sub y1 y2)) (@COND nat (y0 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)))).
Definition term289 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul (@COND nat (x1 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)) (Nat.pow x1 x0)) (@COND nat (x1 = (NUMERAL (BIT1 0))) (NUMERAL 0) (Nat.pow x1 x2)).
Definition term258 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul (@COND nat (Peano.le x0 x2) (Nat.pow x1 (Nat.sub x2 x0)) (@COND nat (x1 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0))) (Nat.pow x1 x0)) (@COND nat ((Peano.le x0 x2) \/ (x1 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow x1 x2)).
Definition term129 (x0 : nat) (x1 : nat) := fun y0 : nat => (~ (x0 = (NUMERAL 0))) -> (Nat.modulo (Nat.pow x0 x1) (Nat.pow x0 y0)) = (@COND nat ((Peano.le y0 x1) \/ (x0 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow x0 x1)).
Definition term9 (x0 : nat) (x1 : nat) := ~ (Peano.lt x0 x1).
Definition term282 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := ((x2 = (NUMERAL (BIT1 0))) -> (NUMERAL 0) = x3) -> ((~ (x2 = (NUMERAL (BIT1 0)))) -> (Nat.pow x2 x1) = x4) -> (@COND nat ((Peano.le x0 x1) \/ (x2 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow x2 x1)) = (@COND nat (x2 = (NUMERAL (BIT1 0))) x3 x4).
Definition term290 (x0 : nat) (x1 : nat) (x2 : nat) := and ((Nat.pow x1 x2) = (Nat.add (Nat.mul (@COND nat (x1 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)) (Nat.pow x1 x0)) (@COND nat (x1 = (NUMERAL (BIT1 0))) (NUMERAL 0) (Nat.pow x1 x2)))).
Definition term261 (x0 : nat) (x1 : nat) (x2 : nat) := and ((Nat.pow x1 x2) = (Nat.add (Nat.mul (@COND nat (Peano.le x0 x2) (Nat.pow x1 (Nat.sub x2 x0)) (@COND nat (x1 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0))) (Nat.pow x1 x0)) (@COND nat ((Peano.le x0 x2) \/ (x1 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow x1 x2)))).
Definition term172 := @COND nat ((NUMERAL 0) = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0).
Definition term115 (x0 : nat) := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (~ (x0 = (NUMERAL 0))) -> (Nat.modulo (Nat.pow x0 y1) (Nat.pow x0 y2)) = (@COND nat ((Peano.le y2 y1) \/ (x0 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow x0 y1))) y0.
Definition term110 (x0 : nat) := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (~ (x0 = (NUMERAL 0))) -> (Nat.div (Nat.pow x0 y1) (Nat.pow x0 y2)) = (@COND nat (Peano.le y2 y1) (Nat.pow x0 (Nat.sub y1 y2)) (@COND nat (x0 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)))) y0.
Definition term91 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, forall y3 : nat, (~ (y1 = (NUMERAL 0))) -> (Nat.modulo (Nat.pow y1 y2) (Nat.pow y1 y3)) = (@COND nat ((Peano.le y3 y2) \/ (y1 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow y1 y2))) y0.
Definition term84 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, forall y3 : nat, (~ (y1 = (NUMERAL 0))) -> (Nat.div (Nat.pow y1 y2) (Nat.pow y1 y3)) = (@COND nat (Peano.le y3 y2) (Nat.pow y1 (Nat.sub y2 y3)) (@COND nat (y1 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)))) y0.
Definition term302 := @eq nat (NUMERAL (BIT1 0)).
Definition term287 (x0 : nat) (x1 : nat) (x2 : nat) := ((~ (x1 = (NUMERAL (BIT1 0)))) -> (Nat.pow x1 x2) = (Nat.pow x1 x2)) -> (@COND nat ((Peano.le x0 x2) \/ (x1 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow x1 x2)) = (@COND nat (x1 = (NUMERAL (BIT1 0))) (NUMERAL 0) (Nat.pow x1 x2)).
Definition term368 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y1 y0) = (~ (Peano.le y0 y1))) x0.
Definition term207 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt (NUMERAL 0) (Nat.pow y1 y0)) = ((~ (y1 = (NUMERAL 0))) \/ (y0 = (NUMERAL 0)))) x0.
Definition term202 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y1 y0) -> (Nat.add (Nat.sub y0 y1) y1) = y0) x0.
Definition term21 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1))) x0.
Definition term18 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y1 y0) = (~ (Peano.lt y0 y1))) x0.
Definition term338 (x0 : nat) (x1 : nat) := (~ (x0 = (NUMERAL 0))) /\ (x1 = (NUMERAL 0)).
Definition term266 (x0 : nat) := True \/ (x0 = (NUMERAL 0)).
Definition term226 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : Prop) (x4 : nat) (x5 : nat) := ((Peano.le x1 x0) = x3) -> (x3 -> (Nat.pow x2 (Nat.sub x0 x1)) = x4) -> ((~ x3) -> (@COND nat (x2 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)) = x5) -> (@COND nat (Peano.le x1 x0) (Nat.pow x2 (Nat.sub x0 x1)) (@COND nat (x2 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0))) = (@COND nat x3 x4 x5).
Definition term274 (x0 : nat) := (~ False) -> (@COND nat (x0 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)) = (@COND nat (x0 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)).
Definition term55 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, ((x1 = (Nat.add (Nat.mul x0 x2) y0)) /\ (Peano.lt y0 x2)) -> ((Nat.div x1 x2) = x0) /\ ((Nat.modulo x1 x2) = y0).
Definition term351 (x0 : nat) := ~ (Peano.lt x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term240 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul (@COND nat (Peano.le x2 x0) (Nat.pow x1 (Nat.sub x0 x2)) (@COND nat (x1 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0))) (Nat.pow x1 x2)).
Definition term350 (x0 : nat) := Peano.le (NUMERAL (BIT0 (BIT1 0))) x0.
Definition term217 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) (x3 : Prop) := forall y0 : a0, forall y1 : a0, (x0 = x3) -> (x3 -> x1 = y0) -> ((~ x3) -> x2 = y1) -> (@COND a0 x0 x1 x2) = (@COND a0 x3 y0 y1).
Definition term190 (x0 : nat) (x1 : nat) := @COND nat ((Peano.le x0 x1) \/ ((NUMERAL 0) = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow (NUMERAL 0) x1).
Definition term251 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := (True -> (NUMERAL 0) = x3) -> ((~ True) -> (Nat.pow x1 x2) = x4) -> (@COND nat ((Peano.le x0 x2) \/ (x1 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow x1 x2)) = (@COND nat True x3 x4).
Definition term228 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := (True -> (Nat.pow x2 (Nat.sub x0 x1)) = x3) -> ((~ True) -> (@COND nat (x2 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)) = x4) -> (@COND nat (Peano.le x1 x0) (Nat.pow x2 (Nat.sub x0 x1)) (@COND nat (x2 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0))) = (@COND nat True x3 x4).
Definition term361 (x0 : nat) := (x0 = (NUMERAL 0)) \/ False.
Definition term369 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt y0 x0) = (~ (Peano.le x0 y0))) x1.
Definition term19 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le y0 x0) = (~ (Peano.lt x0 y0))) x1.
Definition term341 (x0 : nat) (x1 : nat) (x2 : nat) := or ((Peano.le (NUMERAL (BIT0 (BIT1 0))) x0) /\ (Peano.lt x1 x2)).
Definition term318 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.lt (Nat.pow x0 x1) (Nat.pow x0 y0)) = (((Peano.le (NUMERAL (BIT0 (BIT1 0))) x0) /\ (Peano.lt x1 y0)) \/ ((x0 = (NUMERAL 0)) /\ ((~ (x1 = (NUMERAL 0))) /\ (y0 = (NUMERAL 0)))))) x2.
Definition term256 (x0 : nat) (x1 : nat) (x2 : nat) := ((~ True) -> (Nat.pow x1 x2) = (Nat.pow x1 x2)) -> (@COND nat ((Peano.le x0 x2) \/ (x1 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow x1 x2)) = (@COND nat True (NUMERAL 0) (Nat.pow x1 x2)).
Definition term134 (x0 : nat) (x1 : nat) := and (forall y0 : nat, (fun y1 : nat => (~ (x1 = (NUMERAL 0))) -> (Nat.div (Nat.pow x1 x0) (Nat.pow x1 y1)) = (@COND nat (Peano.le y1 x0) (Nat.pow x1 (Nat.sub x0 y1)) (@COND nat (x1 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)))) y0).
Definition term112 (x0 : nat) := and (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (x0 = (NUMERAL 0))) -> (Nat.div (Nat.pow x0 y1) (Nat.pow x0 y2)) = (@COND nat (Peano.le y2 y1) (Nat.pow x0 (Nat.sub y1 y2)) (@COND nat (x0 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)))) y0).
Definition term87 := and (forall y0 : nat, (fun y1 : nat => forall y2 : nat, forall y3 : nat, (~ (y1 = (NUMERAL 0))) -> (Nat.div (Nat.pow y1 y2) (Nat.pow y1 y3)) = (@COND nat (Peano.le y3 y2) (Nat.pow y1 (Nat.sub y2 y3)) (@COND nat (y1 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)))) y0).
Definition term97 (x0 : nat) := and ((fun y0 : nat => forall y1 : nat, forall y2 : nat, (~ (y0 = (NUMERAL 0))) -> (Nat.div (Nat.pow y0 y1) (Nat.pow y0 y2)) = (@COND nat (Peano.le y2 y1) (Nat.pow y0 (Nat.sub y1 y2)) (@COND nat (y0 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)))) x0).
Definition term192 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> (x0 = (NUMERAL 0)) = False.
Definition term259 (x0 : nat) (x1 : nat) := Nat.add (Nat.pow x0 x1) (NUMERAL 0).
Definition term34 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.pow x1 x0) (Nat.pow x1 x2).
Definition term60 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y0 = (Nat.add (Nat.mul y2 y1) y3)) /\ (Peano.lt y3 y1)) -> ((Nat.div y0 y1) = y2) /\ ((Nat.modulo y0 y1) = y3)) -> ((Nat.div x1 x2) = x0) /\ ((Nat.modulo x1 x2) = x3).
Definition term164 (x0 : nat) (x1 : nat) := @COND nat (Peano.le x0 x1).
Definition term131 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x2 = (NUMERAL 0))) -> (Nat.div (Nat.pow x2 x0) (Nat.pow x2 x1)) = (@COND nat (Peano.le x1 x0) (Nat.pow x2 (Nat.sub x0 x1)) (@COND nat (x2 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0))).
Definition term283 (x0 : nat) := (x0 = (NUMERAL (BIT1 0))) -> (NUMERAL 0) = (NUMERAL 0).
Definition term303 := @COND nat True (NUMERAL (BIT1 0)).
Definition term15 := fun y0 : nat => forall y1 : nat, (Peano.le y1 y0) = (~ (Peano.lt y0 y1)).
Definition term6 := fun y0 : nat => forall y1 : nat, (Peano.lt y1 y0) = (~ (Peano.le y0 y1)).
Definition term75 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term157 (x0 : nat) := Nat.div (Nat.pow (NUMERAL 0) x0).
Definition term125 (x0 : nat) := forall y0 : nat, (forall y1 : nat, (~ (x0 = (NUMERAL 0))) -> (Nat.div (Nat.pow x0 y0) (Nat.pow x0 y1)) = (@COND nat (Peano.le y1 y0) (Nat.pow x0 (Nat.sub y0 y1)) (@COND nat (x0 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)))) /\ (forall y1 : nat, (~ (x0 = (NUMERAL 0))) -> (Nat.modulo (Nat.pow x0 y0) (Nat.pow x0 y1)) = (@COND nat ((Peano.le y1 y0) \/ (x0 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow x0 y0))).
Definition term103 := forall y0 : nat, (forall y1 : nat, forall y2 : nat, (~ (y0 = (NUMERAL 0))) -> (Nat.div (Nat.pow y0 y1) (Nat.pow y0 y2)) = (@COND nat (Peano.le y2 y1) (Nat.pow y0 (Nat.sub y1 y2)) (@COND nat (y0 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)))) /\ (forall y1 : nat, forall y2 : nat, (~ (y0 = (NUMERAL 0))) -> (Nat.modulo (Nat.pow y0 y1) (Nat.pow y0 y2)) = (@COND nat ((Peano.le y2 y1) \/ (y0 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow y0 y1))).
Definition term330 := Nat.mul (NUMERAL 0).
Definition term206 (x0 : nat) (x1 : nat) := Nat.add (Nat.sub x0 x1) x1.
Definition term340 (x0 : nat) (x1 : nat) := False /\ ((~ (x0 = (NUMERAL 0))) /\ (x1 = (NUMERAL 0))).
Definition term323 (x0 : nat) := Nat.mul (NUMERAL 0) x0.
Definition term142 (x0 : nat) (x1 : nat) (x2 : nat) := and ((~ (x2 = (NUMERAL 0))) -> (Nat.div (Nat.pow x2 x0) (Nat.pow x2 x1)) = (@COND nat (Peano.le x1 x0) (Nat.pow x2 (Nat.sub x0 x1)) (@COND nat (x2 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)))).
Definition term355 (x0 : nat) := Peano.lt x0 (NUMERAL (BIT0 (BIT1 0))).
Definition term257 (x0 : nat) (x1 : nat) := @COND nat True (NUMERAL 0) (Nat.pow x0 x1).
Definition term286 (x0 : nat) (x1 : nat) := (~ (x0 = (NUMERAL (BIT1 0)))) -> (Nat.pow x0 x1) = (Nat.pow x0 x1).
Definition term205 (x0 : nat) (x1 : nat) := (Peano.le x0 x1) -> (Nat.add (Nat.sub x1 x0) x0) = x1.
Definition term348 := or ((NUMERAL 0) = (NUMERAL 0)).
Definition term305 := Nat.mul (NUMERAL (BIT1 0)).
Definition term116 (x0 : nat) := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (x0 = (NUMERAL 0))) -> (Nat.modulo (Nat.pow x0 y1) (Nat.pow x0 y2)) = (@COND nat ((Peano.le y2 y1) \/ (x0 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow x0 y1))) y0.
Definition term111 (x0 : nat) := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (x0 = (NUMERAL 0))) -> (Nat.div (Nat.pow x0 y1) (Nat.pow x0 y2)) = (@COND nat (Peano.le y2 y1) (Nat.pow x0 (Nat.sub y1 y2)) (@COND nat (x0 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)))) y0.
Definition term92 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, forall y3 : nat, (~ (y1 = (NUMERAL 0))) -> (Nat.modulo (Nat.pow y1 y2) (Nat.pow y1 y3)) = (@COND nat ((Peano.le y3 y2) \/ (y1 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow y1 y2))) y0.
Definition term85 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, forall y3 : nat, (~ (y1 = (NUMERAL 0))) -> (Nat.div (Nat.pow y1 y2) (Nat.pow y1 y3)) = (@COND nat (Peano.le y3 y2) (Nat.pow y1 (Nat.sub y2 y3)) (@COND nat (y1 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)))) y0.
Definition term243 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : Prop) := (fun y0 : Prop => forall y1 : nat, forall y2 : nat, (((Peano.le x0 x2) \/ (x1 = (NUMERAL (BIT1 0)))) = y0) -> (y0 -> (NUMERAL 0) = y1) -> ((~ y0) -> (Nat.pow x1 x2) = y2) -> (@COND nat ((Peano.le x0 x2) \/ (x1 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow x1 x2)) = (@COND nat y0 y1 y2)) x3.
Definition term221 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : Prop) := (fun y0 : Prop => forall y1 : nat, forall y2 : nat, ((Peano.le x1 x0) = y0) -> (y0 -> (Nat.pow x2 (Nat.sub x0 x1)) = y1) -> ((~ y0) -> (@COND nat (x2 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)) = y2) -> (@COND nat (Peano.le x1 x0) (Nat.pow x2 (Nat.sub x0 x1)) (@COND nat (x2 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0))) = (@COND nat y0 y1 y2)) x3.
Definition term59 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Nat.div x1 x2) = x0) /\ ((Nat.modulo x1 x2) = x3).
Definition term294 := (forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))).
Definition term235 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (@COND nat (Peano.le x1 x0) (Nat.pow x2 (Nat.sub x0 x1)) (@COND nat (x2 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0))).
Definition term249 (x0 : nat) := True \/ (x0 = (NUMERAL (BIT1 0))).
Definition term215 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) (x3 : Prop) (x4 : a0) (x5 : a0) := (x0 = x3) -> (x3 -> x1 = x4) -> ((~ x3) -> x2 = x5) -> (@COND a0 x0 x1 x2) = (@COND a0 x3 x4 x5).
Definition term270 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := (False -> (Nat.pow x2 (Nat.sub x0 x1)) = x3) -> ((~ False) -> (@COND nat (x2 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)) = x4) -> (@COND nat (Peano.le x1 x0) (Nat.pow x2 (Nat.sub x0 x1)) (@COND nat (x2 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0))) = (@COND nat False x3 x4).
Definition term181 (x0 : nat) (x1 : nat) := @eq nat (Nat.modulo (Nat.pow (NUMERAL 0) x0) (Nat.pow (NUMERAL 0) x1)).
Definition term320 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.le (NUMERAL (BIT0 (BIT1 0))) x0) /\ (Peano.lt x1 x2)) \/ ((x0 = (NUMERAL 0)) /\ ((~ (x1 = (NUMERAL 0))) /\ (x2 = (NUMERAL 0)))).
Definition term293 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.pow x1 x0) = (Nat.add (Nat.mul (@COND nat (x1 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)) (Nat.pow x1 x2)) (@COND nat (x1 = (NUMERAL (BIT1 0))) (NUMERAL 0) (Nat.pow x1 x0)))) /\ (Peano.lt (@COND nat (x1 = (NUMERAL (BIT1 0))) (NUMERAL 0) (Nat.pow x1 x0)) (Nat.pow x1 x2)).
Definition term267 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.pow x1 x0) = (Nat.add (Nat.mul (@COND nat (Peano.le x2 x0) (Nat.pow x1 (Nat.sub x0 x2)) (@COND nat (x1 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0))) (Nat.pow x1 x2)) (@COND nat ((Peano.le x2 x0) \/ (x1 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow x1 x0)))) /\ (Peano.lt (@COND nat ((Peano.le x2 x0) \/ (x1 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow x1 x0)) (Nat.pow x1 x2)).
Definition term247 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : Prop) (x4 : nat) (x5 : nat) := (fun y0 : nat => (((Peano.le x0 x2) \/ (x1 = (NUMERAL (BIT1 0)))) = x3) -> (x3 -> (NUMERAL 0) = x4) -> ((~ x3) -> (Nat.pow x1 x2) = y0) -> (@COND nat ((Peano.le x0 x2) \/ (x1 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow x1 x2)) = (@COND nat x3 x4 y0)) x5.
Definition term225 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : Prop) (x4 : nat) (x5 : nat) := (fun y0 : nat => ((Peano.le x1 x0) = x3) -> (x3 -> (Nat.pow x2 (Nat.sub x0 x1)) = x4) -> ((~ x3) -> (@COND nat (x2 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)) = y0) -> (@COND nat (Peano.le x1 x0) (Nat.pow x2 (Nat.sub x0 x1)) (@COND nat (x2 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0))) = (@COND nat x3 x4 y0)) x5.
Definition term68 (x0 : nat) := (fun y0 : Prop => y0 \/ (~ y0)) (x0 = (NUMERAL 0)).
Definition term175 (x0 : nat) (x1 : nat) := False -> (Nat.div (Nat.pow (NUMERAL 0) x0) (Nat.pow (NUMERAL 0) x1)) = (@COND nat (Peano.le x1 x0) (Nat.pow (NUMERAL 0) (Nat.sub x0 x1)) (@COND nat ((NUMERAL 0) = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0))).
Definition term148 (x0 : nat) := fun y0 : nat => forall y1 : nat, ((~ (x0 = (NUMERAL 0))) -> (Nat.div (Nat.pow x0 y0) (Nat.pow x0 y1)) = (@COND nat (Peano.le y1 y0) (Nat.pow x0 (Nat.sub y0 y1)) (@COND nat (x0 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)))) /\ ((~ (x0 = (NUMERAL 0))) -> (Nat.modulo (Nat.pow x0 y0) (Nat.pow x0 y1)) = (@COND nat ((Peano.le y1 y0) \/ (x0 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow x0 y0))).
Definition term107 (x0 : nat) := fun y0 : nat => forall y1 : nat, (~ (x0 = (NUMERAL 0))) -> (Nat.modulo (Nat.pow x0 y0) (Nat.pow x0 y1)) = (@COND nat ((Peano.le y1 y0) \/ (x0 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow x0 y0)).
Definition term106 (x0 : nat) := fun y0 : nat => forall y1 : nat, (~ (x0 = (NUMERAL 0))) -> (Nat.div (Nat.pow x0 y0) (Nat.pow x0 y1)) = (@COND nat (Peano.le y1 y0) (Nat.pow x0 (Nat.sub y0 y1)) (@COND nat (x0 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0))).
Definition term40 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Nat.mul (Nat.pow x0 y0) (Nat.pow x0 y1)) = (Nat.pow x0 (Nat.add y0 y1)).
Definition term39 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Nat.pow x0 (Nat.add y0 y1)) = (Nat.mul (Nat.pow x0 y0) (Nat.pow x0 y1)).
Definition term280 (x0 : nat) := False \/ (x0 = (NUMERAL (BIT1 0))).
Definition term333 := @COND nat False (NUMERAL 0).
Definition term30 := NUMERAL (BIT1 0).
Definition term298 (x0 : nat) := Nat.mul (NUMERAL (BIT1 0)) x0.
Definition term279 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul (@COND nat (x0 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)) (Nat.pow x0 x1)).
Definition term187 (x0 : nat) (x1 : nat) (x2 : nat) := @COND nat ((Peano.le x0 x1) \/ (x2 = (NUMERAL (BIT1 0)))) (NUMERAL 0).
Definition term147 (x0 : nat) (x1 : nat) := forall y0 : nat, ((~ (x0 = (NUMERAL 0))) -> (Nat.div (Nat.pow x0 x1) (Nat.pow x0 y0)) = (@COND nat (Peano.le y0 x1) (Nat.pow x0 (Nat.sub x1 y0)) (@COND nat (x0 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)))) /\ ((~ (x0 = (NUMERAL 0))) -> (Nat.modulo (Nat.pow x0 x1) (Nat.pow x0 y0)) = (@COND nat ((Peano.le y0 x1) \/ (x0 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow x0 x1))).
Definition term262 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.lt (@COND nat ((Peano.le x0 x2) \/ (x1 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow x1 x2)).
Definition term150 := fun y0 : nat => forall y1 : nat, forall y2 : nat, ((~ (y0 = (NUMERAL 0))) -> (Nat.div (Nat.pow y0 y1) (Nat.pow y0 y2)) = (@COND nat (Peano.le y2 y1) (Nat.pow y0 (Nat.sub y1 y2)) (@COND nat (y0 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0)))) /\ ((~ (y0 = (NUMERAL 0))) -> (Nat.modulo (Nat.pow y0 y1) (Nat.pow y0 y2)) = (@COND nat ((Peano.le y2 y1) \/ (y0 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow y0 y1))).
Definition term81 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (~ (y0 = (NUMERAL 0))) -> (Nat.modulo (Nat.pow y0 y1) (Nat.pow y0 y2)) = (@COND nat ((Peano.le y2 y1) \/ (y0 = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow y0 y1)).
Definition term80 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (~ (y0 = (NUMERAL 0))) -> (Nat.div (Nat.pow y0 y1) (Nat.pow y0 y2)) = (@COND nat (Peano.le y2 y1) (Nat.pow y0 (Nat.sub y1 y2)) (@COND nat (y0 = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0))).
Definition term44 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.mul (Nat.pow y0 y1) (Nat.pow y0 y2)) = (Nat.pow y0 (Nat.add y1 y2)).
Definition term43 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.pow y0 (Nat.add y1 y2)) = (Nat.mul (Nat.pow y0 y1) (Nat.pow y0 y2)).
Definition term229 (x0 : nat) (x1 : nat) (x2 : nat) := True -> (Nat.pow x0 (Nat.sub x1 x2)) = (Nat.pow x0 (Nat.sub x1 x2)).
Definition term203 (x0 : nat) := forall y0 : nat, (Peano.le y0 x0) -> (Nat.add (Nat.sub x0 y0) y0) = x0.
Definition term163 (x0 : nat) (x1 : nat) := Nat.pow (NUMERAL 0) (Nat.sub x0 x1).
Definition term334 (x0 : nat) (x1 : nat) := @COND nat False (NUMERAL 0) (Nat.pow x0 x1).
Definition term35 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.pow x1 (Nat.add x0 y0)) = (Nat.mul (Nat.pow x1 x0) (Nat.pow x1 y0)).
