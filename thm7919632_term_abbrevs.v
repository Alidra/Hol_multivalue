Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term35 (a0 : Type') (a1 : Type') := imp (~ (Peano.le (NUMERAL (BIT1 0)) (Nat.mul (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1))))).
Definition term6 (x0 : nat) (x1 : nat) (x2 : nat) := @IN nat x0 (dotdot x1 x2).
Definition term213 (a0 : Type') (a1 : Type') (x0 : nat) := @dest_finite_prod a0 a1 (@mk_finite_prod a0 a1 x0).
Definition term18 (a0 : Type') (a1 : Type') := ~ (Peano.le (NUMERAL (BIT1 0)) (Nat.mul (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1)))).
Definition term73 (x0 : nat) (x1 : nat) := (~ ((Nat.mul x0 x1) = (NUMERAL 0))) \/ ((x0 = (NUMERAL 0)) \/ (x1 = (NUMERAL 0))).
Definition term140 (x0 : nat) := Peano.le (NUMERAL (BIT1 0)) x0.
Definition term119 := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, ((Nat.mul y1 y2) = (NUMERAL 0)) \/ ((~ (y1 = (NUMERAL 0))) /\ (~ (y2 = (NUMERAL 0))))) y0) /\ ((fun y1 : nat => forall y2 : nat, (~ ((Nat.mul y1 y2) = (NUMERAL 0))) \/ ((y1 = (NUMERAL 0)) \/ (y2 = (NUMERAL 0)))) y0).
Definition term204 := (~ False) -> False.
Definition term208 := fun y0 : nat -> Prop => y0 (@ε nat y0).
Definition term15 (a0 : Type') (a1 : Type') := True /\ (Peano.le (NUMERAL (BIT1 0)) (Nat.mul (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1)))).
Definition term218 (a0 : Type') (a1 : Type') := forall y0 : finite_prod a0 a1, (@mk_finite_prod a0 a1 (@dest_finite_prod a0 a1 y0)) = y0.
Definition term111 := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Nat.mul y1 y2) = (NUMERAL 0)) \/ ((~ (y1 = (NUMERAL 0))) /\ (~ (y2 = (NUMERAL 0))))) y0) /\ ((fun y1 : nat => forall y2 : nat, (~ ((Nat.mul y1 y2) = (NUMERAL 0))) \/ ((y1 = (NUMERAL 0)) \/ (y2 = (NUMERAL 0)))) y0).
Definition term89 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => ((Nat.mul x0 y1) = (NUMERAL 0)) \/ ((~ (x0 = (NUMERAL 0))) /\ (~ (y1 = (NUMERAL 0))))) y0) /\ ((fun y1 : nat => (~ ((Nat.mul x0 y1) = (NUMERAL 0))) \/ ((x0 = (NUMERAL 0)) \/ (y1 = (NUMERAL 0)))) y0).
Definition term143 := fun y0 : nat => (y0 = (NUMERAL 0)) \/ (Peano.le (NUMERAL (BIT1 0)) y0).
Definition term179 (x0 : Prop) := ~ (~ x0).
Definition term1 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (@IN nat y2 (dotdot y0 y1)) = ((Peano.le y0 y2) /\ (Peano.le y2 y1))) x0.
Definition term79 (x0 : nat) (x1 : nat) := (((Nat.mul x0 x1) = (NUMERAL 0)) \/ (~ ((x0 = (NUMERAL 0)) \/ (x1 = (NUMERAL 0))))) /\ ((~ ((Nat.mul x0 x1) = (NUMERAL 0))) \/ ((x0 = (NUMERAL 0)) \/ (x1 = (NUMERAL 0)))).
Definition term192 (x0 : nat) (x1 : nat) := imp ((~ (x0 = (NUMERAL 0))) /\ (~ (x1 = (NUMERAL 0)))).
Definition term97 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => ((Nat.mul x0 y1) = (NUMERAL 0)) \/ ((~ (x0 = (NUMERAL 0))) /\ (~ (y1 = (NUMERAL 0))))) y0) /\ ((fun y1 : nat => (~ ((Nat.mul x0 y1) = (NUMERAL 0))) \/ ((x0 = (NUMERAL 0)) \/ (y1 = (NUMERAL 0)))) y0).
Definition term172 (a0 : Type') := ~ (Peano.le (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0))).
Definition term166 := (forall y0 : nat, (y0 = (NUMERAL 0)) \/ (Peano.lt (NUMERAL 0) y0)) /\ ((forall y0 : nat, (y0 = (NUMERAL 0)) \/ (Peano.le (NUMERAL (BIT1 0)) y0)) /\ ((forall y0 : nat, (~ (Peano.lt (NUMERAL 0) y0)) \/ (~ (y0 = (NUMERAL 0)))) /\ ((forall y0 : nat, (~ (Peano.lt (NUMERAL 0) y0)) \/ (Peano.le (NUMERAL (BIT1 0)) y0)) /\ ((forall y0 : nat, (~ (Peano.le (NUMERAL (BIT1 0)) y0)) \/ (Peano.lt (NUMERAL 0) y0)) /\ (forall y0 : nat, (~ (Peano.le (NUMERAL (BIT1 0)) y0)) \/ (~ (y0 = (NUMERAL 0)))))))).
Definition term26 := (forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0))))))).
Definition term80 (x0 : nat) (x1 : nat) := (((Nat.mul x0 x1) = (NUMERAL 0)) \/ ((~ (x0 = (NUMERAL 0))) /\ (~ (x1 = (NUMERAL 0))))) /\ ((~ ((Nat.mul x0 x1) = (NUMERAL 0))) \/ ((x0 = (NUMERAL 0)) \/ (x1 = (NUMERAL 0)))).
Definition term135 (x0 : nat) := (~ (~ (x0 = (NUMERAL 0)))) \/ (Peano.lt (NUMERAL 0) x0).
Definition term25 := ~ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))).
Definition term76 (x0 : nat) (x1 : nat) := ((Nat.mul x0 x1) = (NUMERAL 0)) \/ ((~ (x0 = (NUMERAL 0))) /\ (~ (x1 = (NUMERAL 0)))).
Definition term72 (x0 : nat) (x1 : nat) := (~ (x0 = (NUMERAL 0))) /\ (~ (x1 = (NUMERAL 0))).
Definition term16 (x0 : Prop) := (~ x0) -> False.
Definition term112 := (forall y0 : nat, (fun y1 : nat => forall y2 : nat, ((Nat.mul y1 y2) = (NUMERAL 0)) \/ ((~ (y1 = (NUMERAL 0))) /\ (~ (y2 = (NUMERAL 0))))) y0) /\ (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ ((Nat.mul y1 y2) = (NUMERAL 0))) \/ ((y1 = (NUMERAL 0)) \/ (y2 = (NUMERAL 0)))) y0).
Definition term90 (x0 : nat) := (forall y0 : nat, (fun y1 : nat => ((Nat.mul x0 y1) = (NUMERAL 0)) \/ ((~ (x0 = (NUMERAL 0))) /\ (~ (y1 = (NUMERAL 0))))) y0) /\ (forall y0 : nat, (fun y1 : nat => (~ ((Nat.mul x0 y1) = (NUMERAL 0))) \/ ((x0 = (NUMERAL 0)) \/ (y1 = (NUMERAL 0)))) y0).
Definition term130 := (forall y0 : nat, forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL 0)) \/ ((~ (y0 = (NUMERAL 0))) /\ (~ (y1 = (NUMERAL 0))))) /\ (forall y0 : nat, forall y1 : nat, (~ ((Nat.mul y0 y1) = (NUMERAL 0))) \/ ((y0 = (NUMERAL 0)) \/ (y1 = (NUMERAL 0)))).
Definition term17 (a0 : Type') (a1 : Type') := (~ (Peano.le (NUMERAL (BIT1 0)) (Nat.mul (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1))))) -> False.
Definition term78 (x0 : nat) (x1 : nat) := and (((Nat.mul x0 x1) = (NUMERAL 0)) \/ ((~ (x0 = (NUMERAL 0))) /\ (~ (x1 = (NUMERAL 0))))).
Definition term106 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (~ ((Nat.mul x0 y1) = (NUMERAL 0))) \/ ((x0 = (NUMERAL 0)) \/ (y1 = (NUMERAL 0)))) y0.
Definition term101 (x0 : nat) := forall y0 : nat, (fun y1 : nat => ((Nat.mul x0 y1) = (NUMERAL 0)) \/ ((~ (x0 = (NUMERAL 0))) /\ (~ (y1 = (NUMERAL 0))))) y0.
Definition term13 := and (Peano.le (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term177 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term87 (x0 : nat -> Prop) (x1 : nat -> Prop) := forall y0 : nat, (x0 y0) /\ (x1 y0).
Definition term203 (a0 : Type') (a1 : Type') := (Peano.le (NUMERAL (BIT1 0)) (Nat.mul (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1)))) -> False.
Definition term9 (a0 : Type') (a1 : Type') := (Peano.le (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))) /\ (Peano.le (NUMERAL (BIT1 0)) (Nat.mul (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1)))).
Definition term175 (x0 : nat) := ~ (Peano.le (NUMERAL (BIT1 0)) x0).
Definition term109 := fun y0 : nat => (forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL 0)) \/ ((~ (y0 = (NUMERAL 0))) /\ (~ (y1 = (NUMERAL 0))))) /\ (forall y1 : nat, (~ ((Nat.mul y0 y1) = (NUMERAL 0))) \/ ((y0 = (NUMERAL 0)) \/ (y1 = (NUMERAL 0)))).
Definition term183 (a0 : Type') := (Peano.le (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0))) -> ~ ((@dimindex a0 (@UNIV a0)) = (NUMERAL 0)).
Definition term93 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Nat.mul x0 y0) = (NUMERAL 0)) \/ ((~ (x0 = (NUMERAL 0))) /\ (~ (y0 = (NUMERAL 0))))) x1.
Definition term182 (x0 : nat) := imp (Peano.le (NUMERAL (BIT1 0)) x0).
Definition term62 := forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0.
Definition term57 := forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0.
Definition term173 (x0 : Prop) := (~ x0) -> x0.
Definition term34 (a0 : Type') (a1 : Type') := (forall y0 : nat, forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) \/ (y1 = (NUMERAL 0)))) -> (forall y0 : a0 -> Prop, Peano.le (NUMERAL (BIT1 0)) (@dimindex a0 y0)) -> (forall y0 : a1 -> Prop, Peano.le (NUMERAL (BIT1 0)) (@dimindex a1 y0)) -> ~ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))).
Definition term41 := fun y0 : nat => (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0.
Definition term77 (x0 : nat) (x1 : nat) := and (((Nat.mul x0 x1) = (NUMERAL 0)) \/ (~ ((x0 = (NUMERAL 0)) \/ (x1 = (NUMERAL 0))))).
Definition term169 (x0 : nat) := (fun y0 : nat => (~ (Peano.le (NUMERAL (BIT1 0)) y0)) \/ (~ (y0 = (NUMERAL 0)))) x0.
Definition term190 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term206 (a0 : Type') (a1 : Type') := fun y0 : nat => @IN nat y0 (dotdot (NUMERAL (BIT1 0)) (Nat.mul (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1)))).
Definition term121 := @eq Prop (forall y0 : nat, (forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL 0)) \/ ((~ (y0 = (NUMERAL 0))) /\ (~ (y1 = (NUMERAL 0))))) /\ (forall y1 : nat, (~ ((Nat.mul y0 y1) = (NUMERAL 0))) \/ ((y0 = (NUMERAL 0)) \/ (y1 = (NUMERAL 0))))).
Definition term120 := @eq Prop (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Nat.mul y1 y2) = (NUMERAL 0)) \/ ((~ (y1 = (NUMERAL 0))) /\ (~ (y2 = (NUMERAL 0))))) y0) /\ ((fun y1 : nat => forall y2 : nat, (~ ((Nat.mul y1 y2) = (NUMERAL 0))) \/ ((y1 = (NUMERAL 0)) \/ (y2 = (NUMERAL 0)))) y0)).
Definition term99 (x0 : nat) := @eq Prop (forall y0 : nat, (((Nat.mul x0 y0) = (NUMERAL 0)) \/ ((~ (x0 = (NUMERAL 0))) /\ (~ (y0 = (NUMERAL 0))))) /\ ((~ ((Nat.mul x0 y0) = (NUMERAL 0))) \/ ((x0 = (NUMERAL 0)) \/ (y0 = (NUMERAL 0))))).
Definition term98 (x0 : nat) := @eq Prop (forall y0 : nat, ((fun y1 : nat => ((Nat.mul x0 y1) = (NUMERAL 0)) \/ ((~ (x0 = (NUMERAL 0))) /\ (~ (y1 = (NUMERAL 0))))) y0) /\ ((fun y1 : nat => (~ ((Nat.mul x0 y1) = (NUMERAL 0))) \/ ((x0 = (NUMERAL 0)) \/ (y1 = (NUMERAL 0)))) y0)).
Definition term217 (a0 : Type') (a1 : Type') := forall y0 : nat, (@IN nat y0 (dotdot (NUMERAL (BIT1 0)) (Nat.mul (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1))))) = ((@dest_finite_prod a0 a1 (@mk_finite_prod a0 a1 y0)) = y0).
Definition term154 (x0 : nat) := (~ (Peano.le (NUMERAL (BIT1 0)) x0)) \/ (~ (x0 = (NUMERAL 0))).
Definition term145 (x0 : nat) := (~ (Peano.lt (NUMERAL 0) x0)) \/ (~ (x0 = (NUMERAL 0))).
Definition term86 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term187 (x0 : nat) (x1 : nat) := (~ ((x0 = (NUMERAL 0)) \/ (x1 = (NUMERAL 0)))) -> ~ ((Nat.mul x0 x1) = (NUMERAL 0)).
Definition term170 (a0 : Type') := Peano.le (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0)).
Definition term61 := fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0.
Definition term202 (a0 : Type') (a1 : Type') := (~ (Peano.le (NUMERAL (BIT1 0)) (Nat.mul (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1))))) -> Peano.le (NUMERAL (BIT1 0)) (Nat.mul (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1))).
Definition term68 (x0 : nat) := forall y0 : nat, ((Nat.mul x0 y0) = (NUMERAL 0)) = ((x0 = (NUMERAL 0)) \/ (y0 = (NUMERAL 0))).
Definition term3 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (@IN nat y1 (dotdot x0 y0)) = ((Peano.le x0 y1) /\ (Peano.le y1 y0))) x1.
Definition term138 := fun y0 : nat => (y0 = (NUMERAL 0)) \/ (Peano.lt (NUMERAL 0) y0).
Definition term137 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term27 (a0 : Type') := imp (forall y0 : a0 -> Prop, Peano.le (NUMERAL (BIT1 0)) (@dimindex a0 y0)).
Definition term167 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => Peano.le (NUMERAL (BIT1 0)) (@dimindex a0 y0)) x0.
Definition term0 (x0 : nat) := (fun y0 : nat => Peano.le y0 y0) x0.
Definition term8 (a0 : Type') (a1 : Type') := @IN nat (NUMERAL (BIT1 0)) (dotdot (NUMERAL (BIT1 0)) (Nat.mul (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1)))).
Definition term178 (x0 : nat) := (~ (~ (Peano.le (NUMERAL (BIT1 0)) x0))) -> ~ (x0 = (NUMERAL 0)).
Definition term193 (x0 : nat) (x1 : nat) := ((~ (x0 = (NUMERAL 0))) /\ (~ (x1 = (NUMERAL 0)))) -> ~ ((Nat.mul x0 x1) = (NUMERAL 0)).
Definition term136 (x0 : nat) := (x0 = (NUMERAL 0)) \/ (Peano.lt (NUMERAL 0) x0).
Definition term23 (a0 : Type') (a1 : Type') := (((~ (Peano.le (NUMERAL (BIT1 0)) (Nat.mul (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1))))) -> (forall y0 : nat, forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) \/ (y1 = (NUMERAL 0)))) -> (forall y0 : a0 -> Prop, Peano.le (NUMERAL (BIT1 0)) (@dimindex a0 y0)) -> (forall y0 : a1 -> Prop, Peano.le (NUMERAL (BIT1 0)) (@dimindex a1 y0)) -> ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> False) -> (~ (Peano.le (NUMERAL (BIT1 0)) (Nat.mul (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1))))) -> (forall y0 : nat, forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) \/ (y1 = (NUMERAL 0)))) -> (forall y0 : a0 -> Prop, Peano.le (NUMERAL (BIT1 0)) (@dimindex a0 y0)) -> (forall y0 : a1 -> Prop, Peano.le (NUMERAL (BIT1 0)) (@dimindex a1 y0)) -> ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> False) -> ((~ (Peano.le (NUMERAL (BIT1 0)) (Nat.mul (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1))))) -> (forall y0 : nat, forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) \/ (y1 = (NUMERAL 0)))) -> (forall y0 : a0 -> Prop, Peano.le (NUMERAL (BIT1 0)) (@dimindex a0 y0)) -> (forall y0 : a1 -> Prop, Peano.le (NUMERAL (BIT1 0)) (@dimindex a1 y0)) -> ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> False) -> (~ (Peano.le (NUMERAL (BIT1 0)) (Nat.mul (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1))))) -> (forall y0 : nat, forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) \/ (y1 = (NUMERAL 0)))) -> (forall y0 : a0 -> Prop, Peano.le (NUMERAL (BIT1 0)) (@dimindex a0 y0)) -> (forall y0 : a1 -> Prop, Peano.le (NUMERAL (BIT1 0)) (@dimindex a1 y0)) -> ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> False.
Definition term165 := and (forall y0 : nat, (y0 = (NUMERAL 0)) \/ (Peano.lt (NUMERAL 0) y0)).
Definition term163 := and (forall y0 : nat, (y0 = (NUMERAL 0)) \/ (Peano.le (NUMERAL (BIT1 0)) y0)).
Definition term161 := and (forall y0 : nat, (~ (Peano.lt (NUMERAL 0) y0)) \/ (~ (y0 = (NUMERAL 0)))).
Definition term159 := and (forall y0 : nat, (~ (Peano.lt (NUMERAL 0) y0)) \/ (Peano.le (NUMERAL (BIT1 0)) y0)).
Definition term157 := and (forall y0 : nat, (~ (Peano.le (NUMERAL (BIT1 0)) y0)) \/ (Peano.lt (NUMERAL 0) y0)).
Definition term104 (x0 : nat) := and (forall y0 : nat, ((Nat.mul x0 y0) = (NUMERAL 0)) \/ ((~ (x0 = (NUMERAL 0))) /\ (~ (y0 = (NUMERAL 0))))).
Definition term63 := and (forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0).
Definition term58 := and (forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0).
Definition term53 := and (forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))).
Definition term48 := and (forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0).
Definition term43 := and (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0).
Definition term81 (x0 : nat) := fun y0 : nat => (((Nat.mul x0 y0) = (NUMERAL 0)) \/ ((~ (x0 = (NUMERAL 0))) /\ (~ (y0 = (NUMERAL 0))))) /\ ((~ ((Nat.mul x0 y0) = (NUMERAL 0))) \/ ((x0 = (NUMERAL 0)) \/ (y0 = (NUMERAL 0)))).
Definition term207 (a0 : Type') := fun y0 : a0 -> Prop => y0 (@ε a0 y0).
Definition term160 := (forall y0 : nat, (~ (Peano.lt (NUMERAL 0) y0)) \/ (Peano.le (NUMERAL (BIT1 0)) y0)) /\ ((forall y0 : nat, (~ (Peano.le (NUMERAL (BIT1 0)) y0)) \/ (Peano.lt (NUMERAL 0) y0)) /\ (forall y0 : nat, (~ (Peano.le (NUMERAL (BIT1 0)) y0)) \/ (~ (y0 = (NUMERAL 0))))).
Definition term49 := (forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))).
Definition term219 (a0 : Type') (a1 : Type') := (forall y0 : finite_prod a0 a1, (@mk_finite_prod a0 a1 (@dest_finite_prod a0 a1 y0)) = y0) /\ (forall y0 : nat, (@IN nat y0 (dotdot (NUMERAL (BIT1 0)) (Nat.mul (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1))))) = ((@dest_finite_prod a0 a1 (@mk_finite_prod a0 a1 y0)) = y0)).
Definition term56 := fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0.
Definition term191 (x0 : nat) (x1 : nat) := imp (~ ((x0 = (NUMERAL 0)) \/ (x1 = (NUMERAL 0)))).
Definition term133 (x0 : nat) := or (~ (~ (x0 = (NUMERAL 0)))).
Definition term210 (a0 : Type') (a1 : Type') := (fun y0 : nat => @IN nat y0 (dotdot (NUMERAL (BIT1 0)) (Nat.mul (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1))))) (@ε nat (fun y0 : nat => @IN nat y0 (dotdot (NUMERAL (BIT1 0)) (Nat.mul (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1)))))).
Definition term19 (a0 : Type') := forall y0 : a0 -> Prop, Peano.le (NUMERAL (BIT1 0)) (@dimindex a0 y0).
Definition term105 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (~ ((Nat.mul x0 y1) = (NUMERAL 0))) \/ ((x0 = (NUMERAL 0)) \/ (y1 = (NUMERAL 0)))) y0.
Definition term100 (x0 : nat) := fun y0 : nat => (fun y1 : nat => ((Nat.mul x0 y1) = (NUMERAL 0)) \/ ((~ (x0 = (NUMERAL 0))) /\ (~ (y1 = (NUMERAL 0))))) y0.
Definition term134 (x0 : nat) := or (x0 = (NUMERAL 0)).
Definition term196 (a0 : Type') (a1 : Type') := ~ ((Nat.mul (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1))) = (NUMERAL 0)).
Definition term107 (x0 : nat) := forall y0 : nat, (~ ((Nat.mul x0 y0) = (NUMERAL 0))) \/ ((x0 = (NUMERAL 0)) \/ (y0 = (NUMERAL 0))).
Definition term189 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term74 (x0 : nat) (x1 : nat) := or ((Nat.mul x0 x1) = (NUMERAL 0)).
Definition term71 (x0 : nat) (x1 : nat) := ~ ((x0 = (NUMERAL 0)) \/ (x1 = (NUMERAL 0))).
Definition term129 := forall y0 : nat, forall y1 : nat, (~ ((Nat.mul y0 y1) = (NUMERAL 0))) \/ ((y0 = (NUMERAL 0)) \/ (y1 = (NUMERAL 0))).
Definition term124 := forall y0 : nat, forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL 0)) \/ ((~ (y0 = (NUMERAL 0))) /\ (~ (y1 = (NUMERAL 0)))).
Definition term84 := forall y0 : nat, forall y1 : nat, (((Nat.mul y0 y1) = (NUMERAL 0)) \/ ((~ (y0 = (NUMERAL 0))) /\ (~ (y1 = (NUMERAL 0))))) /\ ((~ ((Nat.mul y0 y1) = (NUMERAL 0))) \/ ((y0 = (NUMERAL 0)) \/ (y1 = (NUMERAL 0)))).
Definition term70 := forall y0 : nat, forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) \/ (y1 = (NUMERAL 0))).
Definition term2 (x0 : nat) := forall y0 : nat, forall y1 : nat, (@IN nat y1 (dotdot x0 y0)) = ((Peano.le x0 y1) /\ (Peano.le y1 y0)).
Definition term66 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) \/ (x1 = (NUMERAL 0)).
Definition term209 (a0 : Type') (a1 : Type') := (fun y0 : nat -> Prop => y0 (@ε nat y0)) (fun y0 : nat => @IN nat y0 (dotdot (NUMERAL (BIT1 0)) (Nat.mul (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1))))).
Definition term118 (x0 : nat) := ((fun y0 : nat => forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL 0)) \/ ((~ (y0 = (NUMERAL 0))) /\ (~ (y1 = (NUMERAL 0))))) x0) /\ ((fun y0 : nat => forall y1 : nat, (~ ((Nat.mul y0 y1) = (NUMERAL 0))) \/ ((y0 = (NUMERAL 0)) \/ (y1 = (NUMERAL 0)))) x0).
Definition term149 := fun y0 : nat => (~ (Peano.lt (NUMERAL 0) y0)) \/ (Peano.le (NUMERAL (BIT1 0)) y0).
Definition term65 (a0 : Type') := fun y0 : a0 -> Prop => Peano.le (NUMERAL (BIT1 0)) (@dimindex a0 y0).
Definition term180 (x0 : nat) := ~ (~ (Peano.le (NUMERAL (BIT1 0)) x0)).
Definition term142 (x0 : nat) := (x0 = (NUMERAL 0)) \/ (Peano.le (NUMERAL (BIT1 0)) x0).
Definition term51 := fun y0 : nat => (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0)).
Definition term194 (a0 : Type') (a1 : Type') := (~ ((@dimindex a0 (@UNIV a0)) = (NUMERAL 0))) /\ (~ ((@dimindex a1 (@UNIV a1)) = (NUMERAL 0))).
Definition term4 (x0 : nat) (x1 : nat) := forall y0 : nat, (@IN nat y0 (dotdot x0 x1)) = ((Peano.le x0 y0) /\ (Peano.le y0 x1)).
Definition term28 (a0 : Type') := (forall y0 : a0 -> Prop, Peano.le (NUMERAL (BIT1 0)) (@dimindex a0 y0)) -> ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> False.
Definition term20 (a0 : Type') (a1 : Type') := (~ (Peano.le (NUMERAL (BIT1 0)) (Nat.mul (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1))))) -> (forall y0 : nat, forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) \/ (y1 = (NUMERAL 0)))) -> (forall y0 : a0 -> Prop, Peano.le (NUMERAL (BIT1 0)) (@dimindex a0 y0)) -> (forall y0 : a1 -> Prop, Peano.le (NUMERAL (BIT1 0)) (@dimindex a1 y0)) -> ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> False.
Definition term33 (a0 : Type') (a1 : Type') := (forall y0 : nat, forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) \/ (y1 = (NUMERAL 0)))) -> (forall y0 : a0 -> Prop, Peano.le (NUMERAL (BIT1 0)) (@dimindex a0 y0)) -> (forall y0 : a1 -> Prop, Peano.le (NUMERAL (BIT1 0)) (@dimindex a1 y0)) -> ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> False.
Definition term60 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) x0.
Definition term46 := fun y0 : nat => (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0.
Definition term96 (x0 : nat) (x1 : nat) := ((fun y0 : nat => ((Nat.mul x0 y0) = (NUMERAL 0)) \/ ((~ (x0 = (NUMERAL 0))) /\ (~ (y0 = (NUMERAL 0))))) x1) /\ ((fun y0 : nat => (~ ((Nat.mul x0 y0) = (NUMERAL 0))) \/ ((x0 = (NUMERAL 0)) \/ (y0 = (NUMERAL 0)))) x1).
Definition term88 (x0 : nat -> Prop) (x1 : nat -> Prop) := (forall y0 : nat, x0 y0) /\ (forall y0 : nat, x1 y0).
Definition term11 (a0 : Type') (a1 : Type') := Nat.mul (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1)).
Definition term156 := forall y0 : nat, (~ (Peano.le (NUMERAL (BIT1 0)) y0)) \/ (~ (y0 = (NUMERAL 0))).
Definition term147 := forall y0 : nat, (~ (Peano.lt (NUMERAL 0) y0)) \/ (~ (y0 = (NUMERAL 0))).
Definition term144 := forall y0 : nat, (y0 = (NUMERAL 0)) \/ (Peano.le (NUMERAL (BIT1 0)) y0).
Definition term139 := forall y0 : nat, (y0 = (NUMERAL 0)) \/ (Peano.lt (NUMERAL 0) y0).
Definition term184 (a0 : Type') := ~ ((@dimindex a0 (@UNIV a0)) = (NUMERAL 0)).
Definition term91 (x0 : nat) := fun y0 : nat => ((Nat.mul x0 y0) = (NUMERAL 0)) \/ ((~ (x0 = (NUMERAL 0))) /\ (~ (y0 = (NUMERAL 0)))).
Definition term212 (a0 : Type') (a1 : Type') (x0 : nat) := (fun y0 : nat => @IN nat y0 (dotdot (NUMERAL (BIT1 0)) (Nat.mul (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1))))) x0.
Definition term158 := (forall y0 : nat, (~ (Peano.le (NUMERAL (BIT1 0)) y0)) \/ (Peano.lt (NUMERAL 0) y0)) /\ (forall y0 : nat, (~ (Peano.le (NUMERAL (BIT1 0)) y0)) \/ (~ (y0 = (NUMERAL 0)))).
Definition term108 (x0 : nat) := (forall y0 : nat, ((Nat.mul x0 y0) = (NUMERAL 0)) \/ ((~ (x0 = (NUMERAL 0))) /\ (~ (y0 = (NUMERAL 0))))) /\ (forall y0 : nat, (~ ((Nat.mul x0 y0) = (NUMERAL 0))) \/ ((x0 = (NUMERAL 0)) \/ (y0 = (NUMERAL 0)))).
Definition term44 := (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0))).
Definition term52 := forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0)).
Definition term39 := forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)).
Definition term126 := and (forall y0 : nat, forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL 0)) \/ ((~ (y0 = (NUMERAL 0))) /\ (~ (y1 = (NUMERAL 0))))).
Definition term24 := ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> False.
Definition term215 (a0 : Type') (a1 : Type') (x0 : nat) := @eq Prop ((fun y0 : nat => @IN nat y0 (dotdot (NUMERAL (BIT1 0)) (Nat.mul (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1))))) x0).
Definition term22 (a0 : Type') (a1 : Type') := (((~ (Peano.le (NUMERAL (BIT1 0)) (Nat.mul (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1))))) -> (forall y0 : nat, forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) \/ (y1 = (NUMERAL 0)))) -> (forall y0 : a0 -> Prop, Peano.le (NUMERAL (BIT1 0)) (@dimindex a0 y0)) -> (forall y0 : a1 -> Prop, Peano.le (NUMERAL (BIT1 0)) (@dimindex a1 y0)) -> ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> False) -> (~ (Peano.le (NUMERAL (BIT1 0)) (Nat.mul (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1))))) -> (forall y0 : nat, forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) \/ (y1 = (NUMERAL 0)))) -> (forall y0 : a0 -> Prop, Peano.le (NUMERAL (BIT1 0)) (@dimindex a0 y0)) -> (forall y0 : a1 -> Prop, Peano.le (NUMERAL (BIT1 0)) (@dimindex a1 y0)) -> ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> False) -> (~ (Peano.le (NUMERAL (BIT1 0)) (Nat.mul (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1))))) -> (forall y0 : nat, forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) \/ (y1 = (NUMERAL 0)))) -> (forall y0 : a0 -> Prop, Peano.le (NUMERAL (BIT1 0)) (@dimindex a0 y0)) -> (forall y0 : a1 -> Prop, Peano.le (NUMERAL (BIT1 0)) (@dimindex a1 y0)) -> ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> False.
Definition term29 (a0 : Type') := (forall y0 : a0 -> Prop, Peano.le (NUMERAL (BIT1 0)) (@dimindex a0 y0)) -> ~ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))).
Definition term102 (x0 : nat) := forall y0 : nat, ((Nat.mul x0 y0) = (NUMERAL 0)) \/ ((~ (x0 = (NUMERAL 0))) /\ (~ (y0 = (NUMERAL 0)))).
Definition term127 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (~ ((Nat.mul y1 y2) = (NUMERAL 0))) \/ ((y1 = (NUMERAL 0)) \/ (y2 = (NUMERAL 0)))) y0.
Definition term122 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, ((Nat.mul y1 y2) = (NUMERAL 0)) \/ ((~ (y1 = (NUMERAL 0))) /\ (~ (y2 = (NUMERAL 0))))) y0.
Definition term205 (a0 : Type') (a1 : Type') := exists y0 : nat, @IN nat y0 (dotdot (NUMERAL (BIT1 0)) (Nat.mul (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1)))).
Definition term117 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ ((Nat.mul y0 y1) = (NUMERAL 0))) \/ ((y0 = (NUMERAL 0)) \/ (y1 = (NUMERAL 0)))) x0.
Definition term115 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL 0)) \/ ((~ (y0 = (NUMERAL 0))) /\ (~ (y1 = (NUMERAL 0))))) x0.
Definition term21 (a0 : Type') (a1 : Type') := ((~ (Peano.le (NUMERAL (BIT1 0)) (Nat.mul (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1))))) -> (forall y0 : nat, forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) \/ (y1 = (NUMERAL 0)))) -> (forall y0 : a0 -> Prop, Peano.le (NUMERAL (BIT1 0)) (@dimindex a0 y0)) -> (forall y0 : a1 -> Prop, Peano.le (NUMERAL (BIT1 0)) (@dimindex a1 y0)) -> ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> False) -> (~ (Peano.le (NUMERAL (BIT1 0)) (Nat.mul (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1))))) -> (forall y0 : nat, forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) \/ (y1 = (NUMERAL 0)))) -> (forall y0 : a0 -> Prop, Peano.le (NUMERAL (BIT1 0)) (@dimindex a0 y0)) -> (forall y0 : a1 -> Prop, Peano.le (NUMERAL (BIT1 0)) (@dimindex a1 y0)) -> ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> False.
Definition term67 (x0 : nat) := fun y0 : nat => ((Nat.mul x0 y0) = (NUMERAL 0)) = ((x0 = (NUMERAL 0)) \/ (y0 = (NUMERAL 0))).
Definition term162 := (forall y0 : nat, (~ (Peano.lt (NUMERAL 0) y0)) \/ (~ (y0 = (NUMERAL 0)))) /\ ((forall y0 : nat, (~ (Peano.lt (NUMERAL 0) y0)) \/ (Peano.le (NUMERAL (BIT1 0)) y0)) /\ ((forall y0 : nat, (~ (Peano.le (NUMERAL (BIT1 0)) y0)) \/ (Peano.lt (NUMERAL 0) y0)) /\ (forall y0 : nat, (~ (Peano.le (NUMERAL (BIT1 0)) y0)) \/ (~ (y0 = (NUMERAL 0)))))).
Definition term54 := (forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0))))).
Definition term7 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x1) /\ (Peano.le x1 x2).
Definition term198 (x0 : nat) := (Peano.le (NUMERAL (BIT1 0)) x0) \/ (x0 = (NUMERAL 0)).
Definition term47 := forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0.
Definition term42 := forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0.
Definition term216 (a0 : Type') (a1 : Type') (x0 : nat) := @eq Prop (@IN nat x0 (dotdot (NUMERAL (BIT1 0)) (Nat.mul (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1))))).
Definition term5 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (@IN nat y0 (dotdot x0 x1)) = ((Peano.le x0 y0) /\ (Peano.le y0 x1))) x2.
Definition term75 (x0 : nat) (x1 : nat) := ((Nat.mul x0 x1) = (NUMERAL 0)) \/ (~ ((x0 = (NUMERAL 0)) \/ (x1 = (NUMERAL 0)))).
Definition term195 (a0 : Type') (a1 : Type') := ((~ ((@dimindex a0 (@UNIV a0)) = (NUMERAL 0))) /\ (~ ((@dimindex a1 (@UNIV a1)) = (NUMERAL 0)))) -> ~ ((Nat.mul (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1))) = (NUMERAL 0)).
Definition term64 (a0 : Type') (x0 : a0 -> Prop) := Peano.le (NUMERAL (BIT1 0)) (@dimindex a0 x0).
Definition term141 (x0 : nat) := (~ (~ (x0 = (NUMERAL 0)))) \/ (Peano.le (NUMERAL (BIT1 0)) x0).
Definition term211 (a0 : Type') (a1 : Type') (x0 : finite_prod a0 a1) := @mk_finite_prod a0 a1 (@dest_finite_prod a0 a1 x0).
Definition term151 (x0 : nat) := (~ (Peano.le (NUMERAL (BIT1 0)) x0)) \/ (Peano.lt (NUMERAL 0) x0).
Definition term185 (a0 : Type') := ((@dimindex a0 (@UNIV a0)) = (NUMERAL 0)) -> ~ ((@dimindex a0 (@UNIV a0)) = (NUMERAL 0)).
Definition term201 (a0 : Type') (a1 : Type') := (~ ((Nat.mul (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1))) = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) (Nat.mul (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1))).
Definition term214 (a0 : Type') (a1 : Type') (x0 : nat) := @IN nat x0 (dotdot (NUMERAL (BIT1 0)) (Nat.mul (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1)))).
Definition term125 := and (forall y0 : nat, (fun y1 : nat => forall y2 : nat, ((Nat.mul y1 y2) = (NUMERAL 0)) \/ ((~ (y1 = (NUMERAL 0))) /\ (~ (y2 = (NUMERAL 0))))) y0).
Definition term103 (x0 : nat) := and (forall y0 : nat, (fun y1 : nat => ((Nat.mul x0 y1) = (NUMERAL 0)) \/ ((~ (x0 = (NUMERAL 0))) /\ (~ (y1 = (NUMERAL 0))))) y0).
Definition term116 (x0 : nat) := and ((fun y0 : nat => forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL 0)) \/ ((~ (y0 = (NUMERAL 0))) /\ (~ (y1 = (NUMERAL 0))))) x0).
Definition term92 (x0 : nat) := fun y0 : nat => (~ ((Nat.mul x0 y0) = (NUMERAL 0))) \/ ((x0 = (NUMERAL 0)) \/ (y0 = (NUMERAL 0))).
Definition term40 (x0 : nat) := (Peano.le (NUMERAL (BIT1 0)) x0) -> Peano.lt (NUMERAL 0) x0.
Definition term36 (a0 : Type') (a1 : Type') := (~ (Peano.le (NUMERAL (BIT1 0)) (Nat.mul (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1))))) -> (forall y0 : nat, forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) \/ (y1 = (NUMERAL 0)))) -> (forall y0 : a0 -> Prop, Peano.le (NUMERAL (BIT1 0)) (@dimindex a0 y0)) -> (forall y0 : a1 -> Prop, Peano.le (NUMERAL (BIT1 0)) (@dimindex a1 y0)) -> ~ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))).
Definition term148 (x0 : nat) := (~ (Peano.lt (NUMERAL 0) x0)) \/ (Peano.le (NUMERAL (BIT1 0)) x0).
Definition term31 (a0 : Type') (a1 : Type') := (forall y0 : a0 -> Prop, Peano.le (NUMERAL (BIT1 0)) (@dimindex a0 y0)) -> (forall y0 : a1 -> Prop, Peano.le (NUMERAL (BIT1 0)) (@dimindex a1 y0)) -> ~ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))).
Definition term168 (x0 : nat) := (fun y0 : nat => (y0 = (NUMERAL 0)) \/ (Peano.le (NUMERAL (BIT1 0)) y0)) x0.
Definition term85 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term188 (x0 : nat) (x1 : nat) := ~ ((Nat.mul x0 x1) = (NUMERAL 0)).
Definition term45 (x0 : nat) := (Peano.lt (NUMERAL 0) x0) -> Peano.le (NUMERAL (BIT1 0)) x0.
Definition term110 := forall y0 : nat, (forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL 0)) \/ ((~ (y0 = (NUMERAL 0))) /\ (~ (y1 = (NUMERAL 0))))) /\ (forall y1 : nat, (~ ((Nat.mul y0 y1) = (NUMERAL 0))) \/ ((y0 = (NUMERAL 0)) \/ (y1 = (NUMERAL 0)))).
Definition term174 (x0 : nat) := (~ (x0 = (NUMERAL 0))) \/ (~ (Peano.le (NUMERAL (BIT1 0)) x0)).
Definition term14 (a0 : Type') (a1 : Type') := Peano.le (NUMERAL (BIT1 0)) (Nat.mul (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1))).
Definition term94 (x0 : nat) (x1 : nat) := and ((fun y0 : nat => ((Nat.mul x0 y0) = (NUMERAL 0)) \/ ((~ (x0 = (NUMERAL 0))) /\ (~ (y0 = (NUMERAL 0))))) x1).
Definition term37 (x0 : nat) := (Peano.le (NUMERAL (BIT1 0)) x0) -> ~ (x0 = (NUMERAL 0)).
Definition term55 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) x0.
Definition term200 (x0 : nat) := @eq Prop ((Peano.le (NUMERAL (BIT1 0)) x0) \/ (x0 = (NUMERAL 0))).
Definition term131 (x0 : nat) := ~ (~ (x0 = (NUMERAL 0))).
Definition term12 := Peano.le (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term153 := forall y0 : nat, (~ (Peano.le (NUMERAL (BIT1 0)) y0)) \/ (Peano.lt (NUMERAL 0) y0).
Definition term150 := forall y0 : nat, (~ (Peano.lt (NUMERAL 0) y0)) \/ (Peano.le (NUMERAL (BIT1 0)) y0).
Definition term95 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ ((Nat.mul x0 y0) = (NUMERAL 0))) \/ ((x0 = (NUMERAL 0)) \/ (y0 = (NUMERAL 0)))) x1.
Definition term199 (x0 : nat) := @eq Prop ((x0 = (NUMERAL 0)) \/ (Peano.le (NUMERAL (BIT1 0)) x0)).
Definition term197 (a0 : Type') (a1 : Type') := ((Nat.mul (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1))) = (NUMERAL 0)) -> ~ ((Nat.mul (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1))) = (NUMERAL 0)).
Definition term128 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ ((Nat.mul y1 y2) = (NUMERAL 0))) \/ ((y1 = (NUMERAL 0)) \/ (y2 = (NUMERAL 0)))) y0.
Definition term123 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, ((Nat.mul y1 y2) = (NUMERAL 0)) \/ ((~ (y1 = (NUMERAL 0))) /\ (~ (y2 = (NUMERAL 0))))) y0.
Definition term32 := imp (forall y0 : nat, forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) \/ (y1 = (NUMERAL 0)))).
Definition term164 := (forall y0 : nat, (y0 = (NUMERAL 0)) \/ (Peano.le (NUMERAL (BIT1 0)) y0)) /\ ((forall y0 : nat, (~ (Peano.lt (NUMERAL 0) y0)) \/ (~ (y0 = (NUMERAL 0)))) /\ ((forall y0 : nat, (~ (Peano.lt (NUMERAL 0) y0)) \/ (Peano.le (NUMERAL (BIT1 0)) y0)) /\ ((forall y0 : nat, (~ (Peano.le (NUMERAL (BIT1 0)) y0)) \/ (Peano.lt (NUMERAL 0) y0)) /\ (forall y0 : nat, (~ (Peano.le (NUMERAL (BIT1 0)) y0)) \/ (~ (y0 = (NUMERAL 0))))))).
Definition term59 := (forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))).
Definition term38 := fun y0 : nat => (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)).
Definition term132 (x0 : nat) := Peano.lt (NUMERAL 0) x0.
Definition term30 (a0 : Type') (a1 : Type') := (forall y0 : a0 -> Prop, Peano.le (NUMERAL (BIT1 0)) (@dimindex a0 y0)) -> (forall y0 : a1 -> Prop, Peano.le (NUMERAL (BIT1 0)) (@dimindex a1 y0)) -> ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> False.
Definition term155 := fun y0 : nat => (~ (Peano.le (NUMERAL (BIT1 0)) y0)) \/ (~ (y0 = (NUMERAL 0))).
Definition term146 := fun y0 : nat => (~ (Peano.lt (NUMERAL 0) y0)) \/ (~ (y0 = (NUMERAL 0))).
Definition term171 (a0 : Type') := (~ (Peano.le (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0)))) -> Peano.le (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0)).
Definition term176 (x0 : nat) := @eq Prop ((~ (Peano.le (NUMERAL (BIT1 0)) x0)) \/ (~ (x0 = (NUMERAL 0)))).
Definition term114 := fun y0 : nat => forall y1 : nat, (~ ((Nat.mul y0 y1) = (NUMERAL 0))) \/ ((y0 = (NUMERAL 0)) \/ (y1 = (NUMERAL 0))).
Definition term113 := fun y0 : nat => forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL 0)) \/ ((~ (y0 = (NUMERAL 0))) /\ (~ (y1 = (NUMERAL 0)))).
Definition term83 := fun y0 : nat => forall y1 : nat, (((Nat.mul y0 y1) = (NUMERAL 0)) \/ ((~ (y0 = (NUMERAL 0))) /\ (~ (y1 = (NUMERAL 0))))) /\ ((~ ((Nat.mul y0 y1) = (NUMERAL 0))) \/ ((y0 = (NUMERAL 0)) \/ (y1 = (NUMERAL 0)))).
Definition term69 := fun y0 : nat => forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) \/ (y1 = (NUMERAL 0))).
Definition term50 (x0 : nat) := (Peano.lt (NUMERAL 0) x0) -> ~ (x0 = (NUMERAL 0)).
Definition term10 := NUMERAL (BIT1 0).
Definition term82 (x0 : nat) := forall y0 : nat, (((Nat.mul x0 y0) = (NUMERAL 0)) \/ ((~ (x0 = (NUMERAL 0))) /\ (~ (y0 = (NUMERAL 0))))) /\ ((~ ((Nat.mul x0 y0) = (NUMERAL 0))) \/ ((x0 = (NUMERAL 0)) \/ (y0 = (NUMERAL 0)))).
Definition term181 (x0 : nat) := imp (~ (~ (Peano.le (NUMERAL (BIT1 0)) x0))).
Definition term186 (x0 : Prop) := x0 -> ~ x0.
Definition term152 := fun y0 : nat => (~ (Peano.le (NUMERAL (BIT1 0)) y0)) \/ (Peano.lt (NUMERAL 0) y0).
