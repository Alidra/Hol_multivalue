Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term99 (a0 : Type') (a1 : Type') (x0 : type35 a0 a1) (x1 : type35 a0 a1) := (x0 = x1) -> (@mk_cart a0 a1 x0) = (@mk_cart a0 a1 x1).
Definition term82 (a0 : Type') (a1 : Type') := forall y0 : cart a0 a1, (@mk_cart a0 a1 (@dest_cart a0 a1 y0)) = y0.
Definition term119 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) (x2 : cart a0 a1) := (~ (x0 = x2)) \/ (x1 = x2).
Definition term98 := (~ False) -> False.
Definition term4 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := forall y0 : a0 -> a1, (forall y1 : a0, (x0 y1) = (y0 y1)) = (x0 = y0).
Definition term101 (a0 : Type') (a1 : Type') (x0 : type35 a0 a1) (x1 : type35 a0 a1) := (~ (x0 = x1)) \/ ((@mk_cart a0 a1 x0) = (@mk_cart a0 a1 x1)).
Definition term14 (a0 : Type') (x0 : type33 a0) := forall y0 : nat, ((Peano.le (NUMERAL (BIT1 0)) y0) /\ (Peano.le y0 (@dimindex a0 (@UNIV a0)))) -> x0 (@finite_index a0 y0).
Definition term97 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) := ((@dest_cart a0 a1 x0) = (@dest_cart a0 a1 x0)) -> False.
Definition term46 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) := fun y0 : finite_image a1 => ((fun y1 : finite_image a1 => @dest_cart a0 a1 x0 y1) y0) = ((fun y1 : finite_image a1 => @dest_cart a0 a1 x1 y1) y0).
Definition term120 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) (x2 : cart a0 a1) := (x0 = x2) \/ (~ (x1 = x2)).
Definition term110 (x0 : Prop) := ~ (~ x0).
Definition term117 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) := (~ ((@mk_cart a0 a1 (@dest_cart a0 a1 x0)) = x0)) -> (@mk_cart a0 a1 (@dest_cart a0 a1 x0)) = x0.
Definition term91 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) := (fun y0 : cart a0 a1 => ~ ((@dest_cart a0 a1 y0) = (@dest_cart a0 a1 x0))) x0.
Definition term109 (a0 : Type') (a1 : Type') (x0 : type35 a0 a1) (x1 : type35 a0 a1) := (~ (~ (x0 = x1))) -> (@mk_cart a0 a1 x0) = (@mk_cart a0 a1 x1).
Definition term10 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := fun y0 : a0 => x0 y0.
Definition term2 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := fun y0 : a0 -> a1 => (forall y1 : a0, (x0 y1) = (y0 y1)) = (x0 = y0).
Definition term70 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) := imp (~ ((x0 = x1) = ((@dest_cart a0 a1 x0) = (@dest_cart a0 a1 x1)))).
Definition term1 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := fun y0 : a0 -> a1 => (x0 = y0) = (forall y1 : a0, (x0 y1) = (y0 y1)).
Definition term105 (a0 : Type') (a1 : Type') (x0 : type35 a0 a1) (x1 : type35 a0 a1) := ~ (x0 = x1).
Definition term132 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) (x2 : cart a0 a1) := (~ (~ (x1 = x0))) /\ (~ (~ (x1 = x2))).
Definition term50 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) := @eq ((finite_image a1) -> a0) (fun y0 : finite_image a1 => @dest_cart a0 a1 x0 y0).
Definition term25 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) := fun y0 : nat => ((Peano.le (NUMERAL (BIT1 0)) y0) /\ (Peano.le y0 (@dimindex a1 (@UNIV a1)))) -> (@dest_cart a0 a1 x0 (@finite_index a1 y0)) = (@dest_cart a0 a1 x1 (@finite_index a1 y0)).
Definition term56 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) := (~ ((x0 = x1) = ((@dest_cart a0 a1 x0) = (@dest_cart a0 a1 x1)))) -> ((forall y0 : cart a0 a1, (@mk_cart a0 a1 (@dest_cart a0 a1 y0)) = y0) /\ (forall y0 : type35 a0 a1, True = ((@dest_cart a0 a1 (@mk_cart a0 a1 y0)) = y0))) -> False.
Definition term52 (x0 : Prop) := (~ x0) -> False.
Definition term58 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) := (((~ ((x0 = x1) = ((@dest_cart a0 a1 x0) = (@dest_cart a0 a1 x1)))) -> ((forall y0 : cart a0 a1, (@mk_cart a0 a1 (@dest_cart a0 a1 y0)) = y0) /\ (forall y0 : type35 a0 a1, True = ((@dest_cart a0 a1 (@mk_cart a0 a1 y0)) = y0))) -> False) -> (~ ((x0 = x1) = ((@dest_cart a0 a1 x0) = (@dest_cart a0 a1 x1)))) -> ((forall y0 : cart a0 a1, (@mk_cart a0 a1 (@dest_cart a0 a1 y0)) = y0) /\ (forall y0 : type35 a0 a1, True = ((@dest_cart a0 a1 (@mk_cart a0 a1 y0)) = y0))) -> False) -> (~ ((x0 = x1) = ((@dest_cart a0 a1 x0) = (@dest_cart a0 a1 x1)))) -> ((forall y0 : cart a0 a1, (@mk_cart a0 a1 (@dest_cart a0 a1 y0)) = y0) /\ (forall y0 : type35 a0 a1, True = ((@dest_cart a0 a1 (@mk_cart a0 a1 y0)) = y0))) -> False.
Definition term137 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) (x2 : cart a0 a1) := imp (~ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term151 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) := forall y0 : cart a0 a1, (x0 = y0) = (forall y1 : nat, ((Peano.le (NUMERAL (BIT1 0)) y1) /\ (Peano.le y1 (@dimindex a1 (@UNIV a1)))) -> (@dollar a0 a1 x0 y1) = (@dollar a0 a1 y0 y1)).
Definition term53 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) := (~ ((x0 = x1) = ((@dest_cart a0 a1 x0) = (@dest_cart a0 a1 x1)))) -> False.
Definition term63 (a0 : Type') (a1 : Type') := fun y0 : type35 a0 a1 => True = ((@dest_cart a0 a1 (@mk_cart a0 a1 y0)) = y0).
Definition term12 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> a1) := (fun y0 : a0 -> a1 => (forall y1 : a0, (x0 y1) = (y0 y1)) = (x0 = y0)) x1.
Definition term31 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) (x2 : nat) := (fun y0 : finite_image a1 => (@dest_cart a0 a1 x0 y0) = (@dest_cart a0 a1 x1 y0)) (@finite_index a1 x2).
Definition term9 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := (fun y0 : a0 -> a1 => (fun y1 : a0 => y0 y1) = y0) x0.
Definition term108 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term21 (a0 : Type') (x0 : nat) := imp ((Peano.le (NUMERAL (BIT1 0)) x0) /\ (Peano.le x0 (@dimindex a0 (@UNIV a0)))).
Definition term51 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) := @eq ((finite_image a1) -> a0) (@dest_cart a0 a1 x0).
Definition term13 (a0 : Type') (x0 : type33 a0) := forall y0 : finite_image a0, x0 y0.
Definition term96 (x0 : Prop) := (~ x0) -> x0.
Definition term93 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) := @eq Prop ((fun y0 : cart a0 a1 => ~ ((@dest_cart a0 a1 y0) = (@dest_cart a0 a1 x0))) x1).
Definition term84 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) := (x0 = x1) /\ (~ ((@dest_cart a0 a1 x0) = (@dest_cart a0 a1 x1))).
Definition term128 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) (x2 : cart a0 a1) := (~ (x1 = x0)) \/ (~ (x1 = x2)).
Definition term16 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) := forall y0 : nat, (@dollar a0 a1 x0 y0) = (@dest_cart a0 a1 x0 (@finite_index a1 y0)).
Definition term64 (a0 : Type') (a1 : Type') := fun y0 : type35 a0 a1 => (@dest_cart a0 a1 (@mk_cart a0 a1 y0)) = y0.
Definition term130 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term142 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) := (~ ((@mk_cart a0 a1 (@dest_cart a0 a1 x0)) = x1)) -> (@mk_cart a0 a1 (@dest_cart a0 a1 x0)) = x1.
Definition term125 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) (x2 : cart a0 a1) := @eq Prop ((~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2))).
Definition term73 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) := fun y0 : cart a0 a1 => (~ ((y0 = x0) = ((@dest_cart a0 a1 y0) = (@dest_cart a0 a1 x0)))) -> ~ ((forall y1 : cart a0 a1, (@mk_cart a0 a1 (@dest_cart a0 a1 y1)) = y1) /\ (forall y1 : type35 a0 a1, (@dest_cart a0 a1 (@mk_cart a0 a1 y1)) = y1)).
Definition term35 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) := @eq Prop (forall y0 : nat, ((Peano.le (NUMERAL (BIT1 0)) y0) /\ (Peano.le y0 (@dimindex a1 (@UNIV a1)))) -> (@dest_cart a0 a1 x0 (@finite_index a1 y0)) = (@dest_cart a0 a1 x1 (@finite_index a1 y0))).
Definition term34 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) := @eq Prop (forall y0 : nat, ((Peano.le (NUMERAL (BIT1 0)) y0) /\ (Peano.le y0 (@dimindex a1 (@UNIV a1)))) -> (fun y1 : finite_image a1 => (@dest_cart a0 a1 x0 y1) = (@dest_cart a0 a1 x1 y1)) (@finite_index a1 y0)).
Definition term126 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) (x2 : cart a0 a1) := @eq Prop ((x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term23 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) (x2 : nat) := ((Peano.le (NUMERAL (BIT1 0)) x2) /\ (Peano.le x2 (@dimindex a1 (@UNIV a1)))) -> (@dest_cart a0 a1 x0 (@finite_index a1 x2)) = (@dest_cart a0 a1 x1 (@finite_index a1 x2)).
Definition term32 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) (x2 : nat) := ((Peano.le (NUMERAL (BIT1 0)) x2) /\ (Peano.le x2 (@dimindex a1 (@UNIV a1)))) -> (fun y0 : finite_image a1 => (@dest_cart a0 a1 x0 y0) = (@dest_cart a0 a1 x1 y0)) (@finite_index a1 x2).
Definition term152 (a0 : Type') (a1 : Type') := forall y0 : cart a0 a1, forall y1 : cart a0 a1, (y0 = y1) = (forall y2 : nat, ((Peano.le (NUMERAL (BIT1 0)) y2) /\ (Peano.le y2 (@dimindex a1 (@UNIV a1)))) -> (@dollar a0 a1 y0 y2) = (@dollar a0 a1 y1 y2)).
Definition term79 (a0 : Type') (a1 : Type') := forall y0 : cart a0 a1, forall y1 : cart a0 a1, (~ ((y1 = y0) = ((@dest_cart a0 a1 y1) = (@dest_cart a0 a1 y0)))) -> ~ ((forall y2 : cart a0 a1, (@mk_cart a0 a1 (@dest_cart a0 a1 y2)) = y2) /\ (forall y2 : type35 a0 a1, (@dest_cart a0 a1 (@mk_cart a0 a1 y2)) = y2)).
Definition term78 (a0 : Type') (a1 : Type') := forall y0 : cart a0 a1, forall y1 : cart a0 a1, (~ ((y1 = y0) = ((@dest_cart a0 a1 y1) = (@dest_cart a0 a1 y0)))) -> ((forall y2 : cart a0 a1, (@mk_cart a0 a1 (@dest_cart a0 a1 y2)) = y2) /\ (forall y2 : type35 a0 a1, True = ((@dest_cart a0 a1 (@mk_cart a0 a1 y2)) = y2))) -> False.
Definition term71 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) := (~ ((x0 = x1) = ((@dest_cart a0 a1 x0) = (@dest_cart a0 a1 x1)))) -> ~ ((forall y0 : cart a0 a1, (@mk_cart a0 a1 (@dest_cart a0 a1 y0)) = y0) /\ (forall y0 : type35 a0 a1, (@dest_cart a0 a1 (@mk_cart a0 a1 y0)) = y0)).
Definition term88 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) := ~ (x0 = x1).
Definition term123 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term36 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) (x2 : finite_image a1) := (fun y0 : finite_image a1 => (@dest_cart a0 a1 x0 y0) = (@dest_cart a0 a1 x1 y0)) x2.
Definition term107 (a0 : Type') (a1 : Type') (x0 : type35 a0 a1) (x1 : type35 a0 a1) := @eq Prop (((@mk_cart a0 a1 x0) = (@mk_cart a0 a1 x1)) \/ (~ (x0 = x1))).
Definition term94 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) := @eq Prop (~ ((@dest_cart a0 a1 x0) = (@dest_cart a0 a1 x1))).
Definition term20 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : nat) := @eq a0 (@dest_cart a0 a1 x0 (@finite_index a1 x1)).
Definition term90 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) := (fun y0 : cart a0 a1 => ~ ((@dest_cart a0 a1 y0) = (@dest_cart a0 a1 x0))) x1.
Definition term40 (a0 : Type') (a1 : Type') (x0 : type35 a0 a1) (x1 : type35 a0 a1) := forall y0 : finite_image a1, (x0 y0) = (x1 y0).
Definition term102 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) (x2 : cart a0 a1) := (~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2)).
Definition term48 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) := @eq Prop (forall y0 : finite_image a1, (@dest_cart a0 a1 x0 y0) = (@dest_cart a0 a1 x1 y0)).
Definition term28 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) := forall y0 : nat, ((Peano.le (NUMERAL (BIT1 0)) y0) /\ (Peano.le y0 (@dimindex a1 (@UNIV a1)))) -> (fun y1 : finite_image a1 => (@dest_cart a0 a1 x0 y1) = (@dest_cart a0 a1 x1 y1)) (@finite_index a1 y0).
Definition term136 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) (x2 : cart a0 a1) := (x1 = x0) /\ (x1 = x2).
Definition term87 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) := ~ ((@dest_cart a0 a1 x0) = (@dest_cart a0 a1 x1)).
Definition term66 (a0 : Type') (a1 : Type') := forall y0 : type35 a0 a1, (@dest_cart a0 a1 (@mk_cart a0 a1 y0)) = y0.
Definition term113 (a0 : Type') (a1 : Type') (x0 : type35 a0 a1) (x1 : type35 a0 a1) := imp (x0 = x1).
Definition term33 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) := fun y0 : nat => ((Peano.le (NUMERAL (BIT1 0)) y0) /\ (Peano.le y0 (@dimindex a1 (@UNIV a1)))) -> (fun y1 : finite_image a1 => (@dest_cart a0 a1 x0 y1) = (@dest_cart a0 a1 x1 y1)) (@finite_index a1 y0).
Definition term118 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) := ~ ((@mk_cart a0 a1 (@dest_cart a0 a1 x0)) = x0).
Definition term129 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term89 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) := fun y0 : cart a0 a1 => ~ ((@dest_cart a0 a1 y0) = (@dest_cart a0 a1 x0)).
Definition term57 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) := ((~ ((x0 = x1) = ((@dest_cart a0 a1 x0) = (@dest_cart a0 a1 x1)))) -> ((forall y0 : cart a0 a1, (@mk_cart a0 a1 (@dest_cart a0 a1 y0)) = y0) /\ (forall y0 : type35 a0 a1, True = ((@dest_cart a0 a1 (@mk_cart a0 a1 y0)) = y0))) -> False) -> (~ ((x0 = x1) = ((@dest_cart a0 a1 x0) = (@dest_cart a0 a1 x1)))) -> ((forall y0 : cart a0 a1, (@mk_cart a0 a1 (@dest_cart a0 a1 y0)) = y0) /\ (forall y0 : type35 a0 a1, True = ((@dest_cart a0 a1 (@mk_cart a0 a1 y0)) = y0))) -> False.
Definition term141 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) := (((@mk_cart a0 a1 (@dest_cart a0 a1 x1)) = (@mk_cart a0 a1 (@dest_cart a0 a1 x0))) /\ ((@mk_cart a0 a1 (@dest_cart a0 a1 x1)) = x1)) -> (@mk_cart a0 a1 (@dest_cart a0 a1 x0)) = x1.
Definition term140 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) := ((@mk_cart a0 a1 (@dest_cart a0 a1 x1)) = (@mk_cart a0 a1 (@dest_cart a0 a1 x0))) /\ ((@mk_cart a0 a1 (@dest_cart a0 a1 x1)) = x1).
Definition term147 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) := (x0 = x1) -> False.
Definition term92 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) := ~ ((@dest_cart a0 a1 x0) = (@dest_cart a0 a1 x0)).
Definition term43 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : finite_image a1) := (fun y0 : finite_image a1 => @dest_cart a0 a1 x0 y0) x1.
Definition term24 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) := fun y0 : nat => ((Peano.le (NUMERAL (BIT1 0)) y0) /\ (Peano.le y0 (@dimindex a1 (@UNIV a1)))) -> (@dollar a0 a1 x0 y0) = (@dollar a0 a1 x1 y0).
Definition term75 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) := forall y0 : cart a0 a1, (~ ((y0 = x0) = ((@dest_cart a0 a1 y0) = (@dest_cart a0 a1 x0)))) -> ~ ((forall y1 : cart a0 a1, (@mk_cart a0 a1 (@dest_cart a0 a1 y1)) = y1) /\ (forall y1 : type35 a0 a1, (@dest_cart a0 a1 (@mk_cart a0 a1 y1)) = y1)).
Definition term44 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : finite_image a1) := @eq a0 ((fun y0 : finite_image a1 => @dest_cart a0 a1 x0 y0) x1).
Definition term77 (a0 : Type') (a1 : Type') := fun y0 : cart a0 a1 => forall y1 : cart a0 a1, (~ ((y1 = y0) = ((@dest_cart a0 a1 y1) = (@dest_cart a0 a1 y0)))) -> ~ ((forall y2 : cart a0 a1, (@mk_cart a0 a1 (@dest_cart a0 a1 y2)) = y2) /\ (forall y2 : type35 a0 a1, (@dest_cart a0 a1 (@mk_cart a0 a1 y2)) = y2)).
Definition term135 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) := and (x0 = x1).
Definition term80 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) := @mk_cart a0 a1 (@dest_cart a0 a1 x0).
Definition term143 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) := ~ ((@mk_cart a0 a1 (@dest_cart a0 a1 x0)) = x1).
Definition term38 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) := forall y0 : finite_image a1, (@dest_cart a0 a1 x0 y0) = (@dest_cart a0 a1 x1 y0).
Definition term62 (a0 : Type') (a1 : Type') (x0 : type35 a0 a1) := @dest_cart a0 a1 (@mk_cart a0 a1 x0).
Definition term65 (a0 : Type') (a1 : Type') := forall y0 : type35 a0 a1, True = ((@dest_cart a0 a1 (@mk_cart a0 a1 y0)) = y0).
Definition term122 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) (x2 : cart a0 a1) := (~ (x1 = x0)) \/ ((x0 = x2) \/ (~ (x1 = x2))).
Definition term150 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) := (fun y0 : cart a0 a1 => (~ ((y0 = x0) = ((@dest_cart a0 a1 y0) = (@dest_cart a0 a1 x0)))) -> ((forall y1 : cart a0 a1, (@mk_cart a0 a1 (@dest_cart a0 a1 y1)) = y1) /\ (forall y1 : type35 a0 a1, True = ((@dest_cart a0 a1 (@mk_cart a0 a1 y1)) = y1))) -> False) x1.
Definition term81 (a0 : Type') (a1 : Type') := fun y0 : cart a0 a1 => (@mk_cart a0 a1 (@dest_cart a0 a1 y0)) = y0.
Definition term127 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) (x2 : cart a0 a1) := (~ ((~ (x0 = x1)) \/ (~ (x0 = x2)))) -> x1 = x2.
Definition term39 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) := @eq Prop (x0 = x1).
Definition term76 (a0 : Type') (a1 : Type') := fun y0 : cart a0 a1 => forall y1 : cart a0 a1, (~ ((y1 = y0) = ((@dest_cart a0 a1 y1) = (@dest_cart a0 a1 y0)))) -> ((forall y2 : cart a0 a1, (@mk_cart a0 a1 (@dest_cart a0 a1 y2)) = y2) /\ (forall y2 : type35 a0 a1, True = ((@dest_cart a0 a1 (@mk_cart a0 a1 y2)) = y2))) -> False.
Definition term69 (a0 : Type') (a1 : Type') := ~ ((forall y0 : cart a0 a1, (@mk_cart a0 a1 (@dest_cart a0 a1 y0)) = y0) /\ (forall y0 : type35 a0 a1, (@dest_cart a0 a1 (@mk_cart a0 a1 y0)) = y0)).
Definition term61 (a0 : Type') (a1 : Type') := ~ ((forall y0 : cart a0 a1, (@mk_cart a0 a1 (@dest_cart a0 a1 y0)) = y0) /\ (forall y0 : type35 a0 a1, True = ((@dest_cart a0 a1 (@mk_cart a0 a1 y0)) = y0))).
Definition term18 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : nat) := @dest_cart a0 a1 x0 (@finite_index a1 x1).
Definition term134 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) := and (~ (~ (x0 = x1))).
Definition term145 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) := (((@mk_cart a0 a1 (@dest_cart a0 a1 x1)) = x0) /\ ((@mk_cart a0 a1 (@dest_cart a0 a1 x1)) = x1)) -> x0 = x1.
Definition term8 (a0 : Type') (a1 : Type') := forall y0 : a0 -> a1, forall y1 : a0 -> a1, (forall y2 : a0, (y0 y2) = (y1 y2)) = (y0 = y1).
Definition term7 (a0 : Type') (a1 : Type') := forall y0 : a0 -> a1, forall y1 : a0 -> a1, (y0 = y1) = (forall y2 : a0, (y0 y2) = (y1 y2)).
Definition term55 (a0 : Type') (a1 : Type') := (forall y0 : cart a0 a1, (@mk_cart a0 a1 (@dest_cart a0 a1 y0)) = y0) /\ (forall y0 : type35 a0 a1, True = ((@dest_cart a0 a1 (@mk_cart a0 a1 y0)) = y0)).
Definition term149 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) := (fun y0 : cart a0 a1 => forall y1 : cart a0 a1, (~ ((y1 = y0) = ((@dest_cart a0 a1 y1) = (@dest_cart a0 a1 y0)))) -> ((forall y2 : cart a0 a1, (@mk_cart a0 a1 (@dest_cart a0 a1 y2)) = y2) /\ (forall y2 : type35 a0 a1, True = ((@dest_cart a0 a1 (@mk_cart a0 a1 y2)) = y2))) -> False) x0.
Definition term15 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) := (fun y0 : cart a0 a1 => forall y1 : nat, (@dollar a0 a1 y0 y1) = (@dest_cart a0 a1 y0 (@finite_index a1 y1))) x0.
Definition term115 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) := (~ ((@mk_cart a0 a1 (@dest_cart a0 a1 x0)) = (@mk_cart a0 a1 (@dest_cart a0 a1 x1)))) -> (@mk_cart a0 a1 (@dest_cart a0 a1 x0)) = (@mk_cart a0 a1 (@dest_cart a0 a1 x1)).
Definition term37 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) := fun y0 : finite_image a1 => (fun y1 : finite_image a1 => (@dest_cart a0 a1 x0 y1) = (@dest_cart a0 a1 x1 y1)) y0.
Definition term95 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) := (~ ((@dest_cart a0 a1 x0) = (@dest_cart a0 a1 x0))) -> (@dest_cart a0 a1 x0) = (@dest_cart a0 a1 x0).
Definition term124 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) (x2 : cart a0 a1) := (x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term45 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : finite_image a1) := @eq a0 (@dest_cart a0 a1 x0 x1).
Definition term26 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) := forall y0 : nat, ((Peano.le (NUMERAL (BIT1 0)) y0) /\ (Peano.le y0 (@dimindex a1 (@UNIV a1)))) -> (@dollar a0 a1 x0 y0) = (@dollar a0 a1 x1 y0).
Definition term86 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) := (fun y0 : cart a0 a1 => (@mk_cart a0 a1 (@dest_cart a0 a1 y0)) = y0) x0.
Definition term74 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) := forall y0 : cart a0 a1, (~ ((y0 = x0) = ((@dest_cart a0 a1 y0) = (@dest_cart a0 a1 x0)))) -> ((forall y1 : cart a0 a1, (@mk_cart a0 a1 (@dest_cart a0 a1 y1)) = y1) /\ (forall y1 : type35 a0 a1, True = ((@dest_cart a0 a1 (@mk_cart a0 a1 y1)) = y1))) -> False.
Definition term144 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) := ((@mk_cart a0 a1 (@dest_cart a0 a1 x1)) = x0) /\ ((@mk_cart a0 a1 (@dest_cart a0 a1 x1)) = x1).
Definition term146 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) := (~ (x0 = x1)) -> x0 = x1.
Definition term131 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) (x2 : cart a0 a1) := ~ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term106 (a0 : Type') (a1 : Type') (x0 : type35 a0 a1) (x1 : type35 a0 a1) := @eq Prop ((~ (x0 = x1)) \/ ((@mk_cart a0 a1 x0) = (@mk_cart a0 a1 x1))).
Definition term104 (a0 : Type') (a1 : Type') (x0 : type35 a0 a1) (x1 : type35 a0 a1) := ((@mk_cart a0 a1 x0) = (@mk_cart a0 a1 x1)) \/ (~ (x0 = x1)).
Definition term67 (a0 : Type') (a1 : Type') := and (forall y0 : cart a0 a1, (@mk_cart a0 a1 (@dest_cart a0 a1 y0)) = y0).
Definition term100 (x0 : Prop) (x1 : Prop) := (~ x0) \/ x1.
Definition term30 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) := fun y0 : finite_image a1 => (@dest_cart a0 a1 x0 y0) = (@dest_cart a0 a1 x1 y0).
Definition term116 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) := ~ ((@mk_cart a0 a1 (@dest_cart a0 a1 x0)) = (@mk_cart a0 a1 (@dest_cart a0 a1 x1))).
Definition term6 (a0 : Type') (a1 : Type') := fun y0 : a0 -> a1 => forall y1 : a0 -> a1, (forall y2 : a0, (y0 y2) = (y1 y2)) = (y0 = y1).
Definition term85 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) := (~ (x0 = x1)) /\ ((@dest_cart a0 a1 x0) = (@dest_cart a0 a1 x1)).
Definition term148 (a0 : Type') (a1 : Type') := ((forall y0 : cart a0 a1, (@mk_cart a0 a1 (@dest_cart a0 a1 y0)) = y0) /\ (forall y0 : type35 a0 a1, (@dest_cart a0 a1 (@mk_cart a0 a1 y0)) = y0)) -> False.
Definition term60 (a0 : Type') (a1 : Type') := ((forall y0 : cart a0 a1, (@mk_cart a0 a1 (@dest_cart a0 a1 y0)) = y0) /\ (forall y0 : type35 a0 a1, True = ((@dest_cart a0 a1 (@mk_cart a0 a1 y0)) = y0))) -> False.
Definition term42 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) := fun y0 : finite_image a1 => @dest_cart a0 a1 x0 y0.
Definition term138 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) (x2 : cart a0 a1) := imp ((x1 = x0) /\ (x1 = x2)).
Definition term27 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) := forall y0 : nat, ((Peano.le (NUMERAL (BIT1 0)) y0) /\ (Peano.le y0 (@dimindex a1 (@UNIV a1)))) -> (@dest_cart a0 a1 x0 (@finite_index a1 y0)) = (@dest_cart a0 a1 x1 (@finite_index a1 y0)).
Definition term103 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) := (~ ((@dest_cart a0 a1 x0) = (@dest_cart a0 a1 x1))) -> (@dest_cart a0 a1 x0) = (@dest_cart a0 a1 x1).
Definition term72 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) := fun y0 : cart a0 a1 => (~ ((y0 = x0) = ((@dest_cart a0 a1 y0) = (@dest_cart a0 a1 x0)))) -> ((forall y1 : cart a0 a1, (@mk_cart a0 a1 (@dest_cart a0 a1 y1)) = y1) /\ (forall y1 : type35 a0 a1, True = ((@dest_cart a0 a1 (@mk_cart a0 a1 y1)) = y1))) -> False.
Definition term0 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> a1) := forall y0 : a0, (x0 y0) = (x1 y0).
Definition term49 (a0 : Type') (a1 : Type') (x0 : type35 a0 a1) := fun y0 : finite_image a1 => x0 y0.
Definition term133 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) := ~ (~ (x0 = x1)).
Definition term111 (a0 : Type') (a1 : Type') (x0 : type35 a0 a1) (x1 : type35 a0 a1) := ~ (~ (x0 = x1)).
Definition term59 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) := (((~ ((x0 = x1) = ((@dest_cart a0 a1 x0) = (@dest_cart a0 a1 x1)))) -> ((forall y0 : cart a0 a1, (@mk_cart a0 a1 (@dest_cart a0 a1 y0)) = y0) /\ (forall y0 : type35 a0 a1, True = ((@dest_cart a0 a1 (@mk_cart a0 a1 y0)) = y0))) -> False) -> (~ ((x0 = x1) = ((@dest_cart a0 a1 x0) = (@dest_cart a0 a1 x1)))) -> ((forall y0 : cart a0 a1, (@mk_cart a0 a1 (@dest_cart a0 a1 y0)) = y0) /\ (forall y0 : type35 a0 a1, True = ((@dest_cart a0 a1 (@mk_cart a0 a1 y0)) = y0))) -> False) -> ((~ ((x0 = x1) = ((@dest_cart a0 a1 x0) = (@dest_cart a0 a1 x1)))) -> ((forall y0 : cart a0 a1, (@mk_cart a0 a1 (@dest_cart a0 a1 y0)) = y0) /\ (forall y0 : type35 a0 a1, True = ((@dest_cart a0 a1 (@mk_cart a0 a1 y0)) = y0))) -> False) -> (~ ((x0 = x1) = ((@dest_cart a0 a1 x0) = (@dest_cart a0 a1 x1)))) -> ((forall y0 : cart a0 a1, (@mk_cart a0 a1 (@dest_cart a0 a1 y0)) = y0) /\ (forall y0 : type35 a0 a1, True = ((@dest_cart a0 a1 (@mk_cart a0 a1 y0)) = y0))) -> False.
Definition term11 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := (fun y0 : a0 -> a1 => forall y1 : a0 -> a1, (forall y2 : a0, (y0 y2) = (y1 y2)) = (y0 = y1)) x0.
Definition term121 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) := or (~ (x0 = x1)).
Definition term114 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) := ((@dest_cart a0 a1 x0) = (@dest_cart a0 a1 x1)) -> (@mk_cart a0 a1 (@dest_cart a0 a1 x0)) = (@mk_cart a0 a1 (@dest_cart a0 a1 x1)).
Definition term17 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : nat) := (fun y0 : nat => (@dollar a0 a1 x0 y0) = (@dest_cart a0 a1 x0 (@finite_index a1 y0))) x1.
Definition term19 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : nat) := @eq a0 (@dollar a0 a1 x0 x1).
Definition term83 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) := ((x0 = x1) /\ (~ ((@dest_cart a0 a1 x0) = (@dest_cart a0 a1 x1)))) \/ ((~ (x0 = x1)) /\ ((@dest_cart a0 a1 x0) = (@dest_cart a0 a1 x1))).
Definition term5 (a0 : Type') (a1 : Type') := fun y0 : a0 -> a1 => forall y1 : a0 -> a1, (y0 = y1) = (forall y2 : a0, (y0 y2) = (y1 y2)).
Definition term54 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) := ~ ((x0 = x1) = ((@dest_cart a0 a1 x0) = (@dest_cart a0 a1 x1))).
Definition term22 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) (x2 : nat) := ((Peano.le (NUMERAL (BIT1 0)) x2) /\ (Peano.le x2 (@dimindex a1 (@UNIV a1)))) -> (@dollar a0 a1 x0 x2) = (@dollar a0 a1 x1 x2).
Definition term139 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) (x2 : cart a0 a1) := ((x0 = x1) /\ (x0 = x2)) -> x1 = x2.
Definition term3 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := forall y0 : a0 -> a1, (x0 = y0) = (forall y1 : a0, (x0 y1) = (y0 y1)).
Definition term47 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) := @eq Prop (forall y0 : finite_image a1, ((fun y1 : finite_image a1 => @dest_cart a0 a1 x0 y1) y0) = ((fun y1 : finite_image a1 => @dest_cart a0 a1 x1 y1) y0)).
Definition term68 (a0 : Type') (a1 : Type') := (forall y0 : cart a0 a1, (@mk_cart a0 a1 (@dest_cart a0 a1 y0)) = y0) /\ (forall y0 : type35 a0 a1, (@dest_cart a0 a1 (@mk_cart a0 a1 y0)) = y0).
Definition term41 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) := forall y0 : finite_image a1, ((fun y1 : finite_image a1 => @dest_cart a0 a1 x0 y1) y0) = ((fun y1 : finite_image a1 => @dest_cart a0 a1 x1 y1) y0).
Definition term29 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) := forall y0 : finite_image a1, (fun y1 : finite_image a1 => (@dest_cart a0 a1 x0 y1) = (@dest_cart a0 a1 x1 y1)) y0.
Definition term112 (a0 : Type') (a1 : Type') (x0 : type35 a0 a1) (x1 : type35 a0 a1) := imp (~ (~ (x0 = x1))).
