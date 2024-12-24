Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term61 (a0 : Type') (x0 : nat) := (~ (@IN nat x0 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0))))) \/ ((@dest_finite_image a0 (@finite_index a0 x0)) = x0).
Definition term55 (a0 : Type') := fun y0 : nat => (~ (@IN nat y0 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0))))) \/ ((@dest_finite_image a0 (@finite_index a0 y0)) = y0).
Definition term36 (a0 : Type') (x0 : type33 a0) := ~ (all x0).
Definition term140 := (~ False) -> False.
Definition term54 (a0 : Type') := fun y0 : nat => (@IN nat y0 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0)))) \/ (~ ((@dest_finite_image a0 (@finite_index a0 y0)) = y0)).
Definition term52 (a0 : Type') := forall y0 : nat, ((fun y1 : nat => (@IN nat y1 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0)))) \/ (~ ((@dest_finite_image a0 (@finite_index a0 y1)) = y1))) y0) /\ ((fun y1 : nat => (~ (@IN nat y1 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0))))) \/ ((@dest_finite_image a0 (@finite_index a0 y1)) = y1)) y0).
Definition term20 (a0 : Type') := and (forall y0 : finite_image a0, (@finite_index a0 (@dest_finite_image a0 y0)) = y0).
Definition term44 (a0 : Type') (x0 : nat) := ((@IN nat x0 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0)))) \/ (~ ((@dest_finite_image a0 (@finite_index a0 x0)) = x0))) /\ ((~ (@IN nat x0 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0))))) \/ ((@dest_finite_image a0 (@finite_index a0 x0)) = x0)).
Definition term103 (x0 : Prop) := ~ (~ x0).
Definition term137 (a0 : Type') (x0 : finite_image a0) (x1 : nat) := ((x0 = (@finite_index a0 x1)) /\ (@IN nat x1 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0))))) -> False.
Definition term63 (a0 : Type') := fun y0 : nat => ((fun y1 : nat => (@IN nat y1 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0)))) \/ (~ ((@dest_finite_image a0 (@finite_index a0 y1)) = y1))) y0) /\ ((fun y1 : nat => (~ (@IN nat y1 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0))))) \/ ((@dest_finite_image a0 (@finite_index a0 y1)) = y1)) y0).
Definition term102 (a0 : Type') (x0 : finite_image a0) (x1 : finite_image a0) (x2 : finite_image a0) := (~ (~ (x1 = x0))) /\ (~ (~ (x1 = x2))).
Definition term42 (a0 : Type') := fun y0 : finite_image a0 => forall y1 : nat, (~ (y0 = (@finite_index a0 y1))) \/ (~ (@IN nat y1 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0))))).
Definition term115 (a0 : Type') (x0 : finite_image a0) (x1 : finite_image a0) := ((@dest_finite_image a0 x0) = (@dest_finite_image a0 x1)) \/ (~ (x0 = x1)).
Definition term124 (a0 : Type') (x0 : finite_image a0) := ~ ((@dest_finite_image a0 (@finite_index a0 (@dest_finite_image a0 x0))) = (@dest_finite_image a0 x0)).
Definition term3 (a0 : Type') := ~ (forall y0 : finite_image a0, exists y1 : nat, (y0 = (@finite_index a0 y1)) /\ (@IN nat y1 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0))))).
Definition term123 (a0 : Type') (x0 : finite_image a0) := (~ ((@dest_finite_image a0 (@finite_index a0 (@dest_finite_image a0 x0))) = (@dest_finite_image a0 x0))) -> (@dest_finite_image a0 (@finite_index a0 (@dest_finite_image a0 x0))) = (@dest_finite_image a0 x0).
Definition term37 (a0 : Type') (x0 : type33 a0) := exists y0 : finite_image a0, ~ (x0 y0).
Definition term0 (x0 : Prop) := (~ x0) -> False.
Definition term53 (a0 : Type') := (forall y0 : nat, (fun y1 : nat => (@IN nat y1 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0)))) \/ (~ ((@dest_finite_image a0 (@finite_index a0 y1)) = y1))) y0) /\ (forall y0 : nat, (fun y1 : nat => (~ (@IN nat y1 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0))))) \/ ((@dest_finite_image a0 (@finite_index a0 y1)) = y1)) y0).
Definition term93 (a0 : Type') (x0 : finite_image a0) (x1 : finite_image a0) (x2 : finite_image a0) := (x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term46 (a0 : Type') := forall y0 : nat, ((@IN nat y0 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0)))) \/ (~ ((@dest_finite_image a0 (@finite_index a0 y0)) = y0))) /\ ((~ (@IN nat y0 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0))))) \/ ((@dest_finite_image a0 (@finite_index a0 y0)) = y0)).
Definition term108 (a0 : Type') (x0 : finite_image a0) (x1 : finite_image a0) (x2 : finite_image a0) := imp (~ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term41 (a0 : Type') := fun y0 : finite_image a0 => ~ ((fun y1 : finite_image a0 => exists y2 : nat, (y1 = (@finite_index a0 y2)) /\ (@IN nat y2 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0))))) y0).
Definition term132 (a0 : Type') (x0 : finite_image a0) := @IN nat (@dest_finite_image a0 x0) (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0))).
Definition term17 (a0 : Type') (x0 : finite_image a0) := @finite_index a0 (@dest_finite_image a0 x0).
Definition term59 (a0 : Type') (x0 : nat) := and ((@IN nat x0 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0)))) \/ (~ ((@dest_finite_image a0 (@finite_index a0 x0)) = x0))).
Definition term72 (a0 : Type') := forall y0 : nat, (fun y1 : nat => (~ (@IN nat y1 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0))))) \/ ((@dest_finite_image a0 (@finite_index a0 y1)) = y1)) y0.
Definition term67 (a0 : Type') := forall y0 : nat, (fun y1 : nat => (@IN nat y1 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0)))) \/ (~ ((@dest_finite_image a0 (@finite_index a0 y1)) = y1))) y0.
Definition term5 (a0 : Type') := (~ (forall y0 : finite_image a0, exists y1 : nat, (y0 = (@finite_index a0 y1)) /\ (@IN nat y1 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0)))))) -> ((forall y0 : finite_image a0, (@finite_index a0 (@dest_finite_image a0 y0)) = y0) /\ (forall y0 : nat, (@IN nat y0 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0)))) = ((@dest_finite_image a0 (@finite_index a0 y0)) = y0))) -> False.
Definition term83 (a0 : Type') (x0 : finite_image a0) := ~ ((@finite_index a0 (@dest_finite_image a0 x0)) = x0).
Definition term85 (a0 : Type') (x0 : finite_image a0) := (~ ((@finite_index a0 (@dest_finite_image a0 x0)) = (@finite_index a0 (@dest_finite_image a0 x0)))) -> (@finite_index a0 (@dest_finite_image a0 x0)) = (@finite_index a0 (@dest_finite_image a0 x0)).
Definition term126 (a0 : Type') (x0 : nat) := ~ ((@dest_finite_image a0 (@finite_index a0 x0)) = x0).
Definition term96 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term50 (x0 : nat -> Prop) (x1 : nat -> Prop) := forall y0 : nat, (x0 y0) /\ (x1 y0).
Definition term23 (a0 : Type') (x0 : finite_image a0) := exists y0 : nat, (x0 = (@finite_index a0 y0)) /\ (@IN nat y0 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0)))).
Definition term120 (a0 : Type') (x0 : finite_image a0) (x1 : finite_image a0) := imp (x0 = x1).
Definition term122 (a0 : Type') (x0 : finite_image a0) := @dest_finite_image a0 (@finite_index a0 (@dest_finite_image a0 x0)).
Definition term60 (a0 : Type') (x0 : nat) := (fun y0 : nat => (~ (@IN nat y0 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0))))) \/ ((@dest_finite_image a0 (@finite_index a0 y0)) = y0)) x0.
Definition term135 (x0 : Prop) (x1 : Prop) := (~ x0) \/ (~ x1).
Definition term84 (x0 : Prop) := (~ x0) -> x0.
Definition term98 (a0 : Type') (x0 : finite_image a0) (x1 : finite_image a0) (x2 : finite_image a0) := (~ (x1 = x0)) \/ (~ (x1 = x2)).
Definition term100 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term94 (a0 : Type') (x0 : finite_image a0) (x1 : finite_image a0) (x2 : finite_image a0) := @eq Prop ((~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2))).
Definition term136 (x0 : Prop) (x1 : Prop) := ~ (x0 /\ x1).
Definition term65 (a0 : Type') := @eq Prop (forall y0 : nat, ((@IN nat y0 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0)))) \/ (~ ((@dest_finite_image a0 (@finite_index a0 y0)) = y0))) /\ ((~ (@IN nat y0 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0))))) \/ ((@dest_finite_image a0 (@finite_index a0 y0)) = y0))).
Definition term64 (a0 : Type') := @eq Prop (forall y0 : nat, ((fun y1 : nat => (@IN nat y1 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0)))) \/ (~ ((@dest_finite_image a0 (@finite_index a0 y1)) = y1))) y0) /\ ((fun y1 : nat => (~ (@IN nat y1 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0))))) \/ ((@dest_finite_image a0 (@finite_index a0 y1)) = y1)) y0)).
Definition term25 (a0 : Type') (x0 : finite_image a0) (x1 : nat) := ~ ((x0 = (@finite_index a0 x1)) /\ (@IN nat x1 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0))))).
Definition term16 (a0 : Type') := forall y0 : nat, (@IN nat y0 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0)))) = ((@dest_finite_image a0 (@finite_index a0 y0)) = y0).
Definition term95 (a0 : Type') (x0 : finite_image a0) (x1 : finite_image a0) (x2 : finite_image a0) := @eq Prop ((x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term24 (a0 : Type') := fun y0 : finite_image a0 => exists y1 : nat, (y0 = (@finite_index a0 y1)) /\ (@IN nat y1 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0)))).
Definition term49 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term134 (a0 : Type') (x0 : finite_image a0) := ~ (@IN nat (@dest_finite_image a0 x0) (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0)))).
Definition term92 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term117 (a0 : Type') (x0 : finite_image a0) (x1 : finite_image a0) := @eq Prop (((@dest_finite_image a0 x0) = (@dest_finite_image a0 x1)) \/ (~ (x0 = x1))).
Definition term40 (a0 : Type') (x0 : finite_image a0) := ~ ((fun y0 : finite_image a0 => exists y1 : nat, (y0 = (@finite_index a0 y1)) /\ (@IN nat y1 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0))))) x0).
Definition term127 (a0 : Type') (x0 : nat) := ~ (~ ((@dest_finite_image a0 (@finite_index a0 x0)) = x0)).
Definition term106 (a0 : Type') (x0 : finite_image a0) (x1 : finite_image a0) := and (x0 = x1).
Definition term58 (a0 : Type') (x0 : nat) := and ((fun y0 : nat => (@IN nat y0 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0)))) \/ (~ ((@dest_finite_image a0 (@finite_index a0 y0)) = y0))) x0).
Definition term110 (a0 : Type') (x0 : finite_image a0) (x1 : finite_image a0) (x2 : finite_image a0) := ((x0 = x1) /\ (x0 = x2)) -> x1 = x2.
Definition term62 (a0 : Type') (x0 : nat) := ((fun y0 : nat => (@IN nat y0 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0)))) \/ (~ ((@dest_finite_image a0 (@finite_index a0 y0)) = y0))) x0) /\ ((fun y0 : nat => (~ (@IN nat y0 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0))))) \/ ((@dest_finite_image a0 (@finite_index a0 y0)) = y0)) x0).
Definition term81 (a0 : Type') (x0 : finite_image a0) (x1 : finite_image a0) (x2 : finite_image a0) := (~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2)).
Definition term87 (a0 : Type') (x0 : finite_image a0) (x1 : finite_image a0) (x2 : finite_image a0) := (~ (x0 = x2)) \/ (x1 = x2).
Definition term66 (a0 : Type') := fun y0 : nat => (fun y1 : nat => (@IN nat y1 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0)))) \/ (~ ((@dest_finite_image a0 (@finite_index a0 y1)) = y1))) y0.
Definition term57 (a0 : Type') (x0 : nat) := (@IN nat x0 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0)))) \/ (~ ((@dest_finite_image a0 (@finite_index a0 x0)) = x0)).
Definition term70 (a0 : Type') := and (forall y0 : nat, (@IN nat y0 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0)))) \/ (~ ((@dest_finite_image a0 (@finite_index a0 y0)) = y0))).
Definition term82 (a0 : Type') (x0 : finite_image a0) := (~ ((@finite_index a0 (@dest_finite_image a0 x0)) = x0)) -> (@finite_index a0 (@dest_finite_image a0 x0)) = x0.
Definition term47 (a0 : Type') := (forall y0 : finite_image a0, (@finite_index a0 (@dest_finite_image a0 y0)) = y0) /\ (forall y0 : nat, ((@IN nat y0 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0)))) \/ (~ ((@dest_finite_image a0 (@finite_index a0 y0)) = y0))) /\ ((~ (@IN nat y0 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0))))) \/ ((@dest_finite_image a0 (@finite_index a0 y0)) = y0))).
Definition term4 (a0 : Type') := (forall y0 : finite_image a0, (@finite_index a0 (@dest_finite_image a0 y0)) = y0) /\ (forall y0 : nat, (@IN nat y0 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0)))) = ((@dest_finite_image a0 (@finite_index a0 y0)) = y0)).
Definition term38 (a0 : Type') := exists y0 : finite_image a0, ~ ((fun y1 : finite_image a0 => exists y2 : nat, (y1 = (@finite_index a0 y2)) /\ (@IN nat y2 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0))))) y0).
Definition term19 (a0 : Type') := forall y0 : finite_image a0, (@finite_index a0 (@dest_finite_image a0 y0)) = y0.
Definition term113 (a0 : Type') (x0 : finite_image a0) := (~ (x0 = (@finite_index a0 (@dest_finite_image a0 x0)))) -> x0 = (@finite_index a0 (@dest_finite_image a0 x0)).
Definition term99 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term34 (a0 : Type') (x0 : finite_image a0) := fun y0 : nat => (~ (x0 = (@finite_index a0 y0))) \/ (~ (@IN nat y0 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0))))).
Definition term27 (x0 : nat -> Prop) := ~ (ex x0).
Definition term78 (a0 : Type') (x0 : finite_image a0) (x1 : finite_image a0) := (x0 = x1) -> (@dest_finite_image a0 x0) = (@dest_finite_image a0 x1).
Definition term68 (a0 : Type') := forall y0 : nat, (@IN nat y0 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0)))) \/ (~ ((@dest_finite_image a0 (@finite_index a0 y0)) = y0)).
Definition term121 (a0 : Type') (x0 : finite_image a0) := ((@finite_index a0 (@dest_finite_image a0 x0)) = x0) -> (@dest_finite_image a0 (@finite_index a0 (@dest_finite_image a0 x0))) = (@dest_finite_image a0 x0).
Definition term118 (a0 : Type') (x0 : finite_image a0) (x1 : finite_image a0) := (~ (~ (x0 = x1))) -> (@dest_finite_image a0 x0) = (@dest_finite_image a0 x1).
Definition term28 (x0 : nat -> Prop) := forall y0 : nat, ~ (x0 y0).
Definition term88 (a0 : Type') (x0 : finite_image a0) (x1 : finite_image a0) (x2 : finite_image a0) := (x0 = x2) \/ (~ (x1 = x2)).
Definition term114 (a0 : Type') (x0 : finite_image a0) := ~ (x0 = (@finite_index a0 (@dest_finite_image a0 x0))).
Definition term1 (a0 : Type') := forall y0 : finite_image a0, exists y1 : nat, (y0 = (@finite_index a0 y1)) /\ (@IN nat y1 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0)))).
Definition term43 (a0 : Type') := exists y0 : finite_image a0, forall y1 : nat, (~ (y0 = (@finite_index a0 y1))) \/ (~ (@IN nat y1 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0))))).
Definition term2 (a0 : Type') := (~ (forall y0 : finite_image a0, exists y1 : nat, (y0 = (@finite_index a0 y1)) /\ (@IN nat y1 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0)))))) -> False.
Definition term14 (a0 : Type') (x0 : nat) := @dest_finite_image a0 (@finite_index a0 x0).
Definition term138 (a0 : Type') (x0 : finite_image a0) := (x0 = (@finite_index a0 (@dest_finite_image a0 x0))) /\ (@IN nat (@dest_finite_image a0 x0) (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0)))).
Definition term131 (a0 : Type') (x0 : finite_image a0) := ((@dest_finite_image a0 (@finite_index a0 (@dest_finite_image a0 x0))) = (@dest_finite_image a0 x0)) -> @IN nat (@dest_finite_image a0 x0) (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0))).
Definition term51 (x0 : nat -> Prop) (x1 : nat -> Prop) := (forall y0 : nat, x0 y0) /\ (forall y0 : nat, x1 y0).
Definition term35 (a0 : Type') (x0 : finite_image a0) := forall y0 : nat, (~ (x0 = (@finite_index a0 y0))) \/ (~ (@IN nat y0 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0))))).
Definition term18 (a0 : Type') := fun y0 : finite_image a0 => (@finite_index a0 (@dest_finite_image a0 y0)) = y0.
Definition term91 (a0 : Type') (x0 : finite_image a0) (x1 : finite_image a0) (x2 : finite_image a0) := (~ (x1 = x0)) \/ ((x0 = x2) \/ (~ (x1 = x2))).
Definition term97 (a0 : Type') (x0 : finite_image a0) (x1 : finite_image a0) (x2 : finite_image a0) := (~ ((~ (x0 = x1)) \/ (~ (x0 = x2)))) -> x1 = x2.
Definition term111 (a0 : Type') (x0 : finite_image a0) := ((@finite_index a0 (@dest_finite_image a0 x0)) = x0) /\ ((@finite_index a0 (@dest_finite_image a0 x0)) = (@finite_index a0 (@dest_finite_image a0 x0))).
Definition term10 (a0 : Type') := ~ ((forall y0 : finite_image a0, (@finite_index a0 (@dest_finite_image a0 y0)) = y0) /\ (forall y0 : nat, (@IN nat y0 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0)))) = ((@dest_finite_image a0 (@finite_index a0 y0)) = y0))).
Definition term13 (a0 : Type') (x0 : nat) := @IN nat x0 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0))).
Definition term105 (a0 : Type') (x0 : finite_image a0) (x1 : finite_image a0) := and (~ (~ (x0 = x1))).
Definition term75 (a0 : Type') := (forall y0 : finite_image a0, (@finite_index a0 (@dest_finite_image a0 y0)) = y0) /\ ((forall y0 : nat, (@IN nat y0 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0)))) \/ (~ ((@dest_finite_image a0 (@finite_index a0 y0)) = y0))) /\ (forall y0 : nat, (~ (@IN nat y0 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0))))) \/ ((@dest_finite_image a0 (@finite_index a0 y0)) = y0))).
Definition term76 (a0 : Type') (x0 : finite_image a0) (x1 : nat) := (fun y0 : nat => (~ (x0 = (@finite_index a0 y0))) \/ (~ (@IN nat y0 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0)))))) x1.
Definition term21 (a0 : Type') (x0 : finite_image a0) (x1 : nat) := (x0 = (@finite_index a0 x1)) /\ (@IN nat x1 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0)))).
Definition term74 (a0 : Type') := (forall y0 : nat, (@IN nat y0 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0)))) \/ (~ ((@dest_finite_image a0 (@finite_index a0 y0)) = y0))) /\ (forall y0 : nat, (~ (@IN nat y0 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0))))) \/ ((@dest_finite_image a0 (@finite_index a0 y0)) = y0)).
Definition term133 (a0 : Type') (x0 : finite_image a0) := (~ (@IN nat (@dest_finite_image a0 x0) (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0))))) -> @IN nat (@dest_finite_image a0 x0) (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0))).
Definition term30 (a0 : Type') (x0 : finite_image a0) := forall y0 : nat, ~ ((fun y1 : nat => (x0 = (@finite_index a0 y1)) /\ (@IN nat y1 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0))))) y0).
Definition term89 (a0 : Type') (x0 : finite_image a0) (x1 : finite_image a0) := ~ (x0 = x1).
Definition term31 (a0 : Type') (x0 : finite_image a0) (x1 : nat) := (fun y0 : nat => (x0 = (@finite_index a0 y0)) /\ (@IN nat y0 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0))))) x1.
Definition term80 (a0 : Type') (x0 : finite_image a0) (x1 : finite_image a0) := (~ (x0 = x1)) \/ ((@dest_finite_image a0 x0) = (@dest_finite_image a0 x1)).
Definition term101 (a0 : Type') (x0 : finite_image a0) (x1 : finite_image a0) (x2 : finite_image a0) := ~ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term26 (a0 : Type') (x0 : finite_image a0) (x1 : nat) := (~ (x0 = (@finite_index a0 x1))) \/ (~ (@IN nat x1 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0))))).
Definition term116 (a0 : Type') (x0 : finite_image a0) (x1 : finite_image a0) := @eq Prop ((~ (x0 = x1)) \/ ((@dest_finite_image a0 x0) = (@dest_finite_image a0 x1))).
Definition term139 (a0 : Type') (x0 : finite_image a0) := ((x0 = (@finite_index a0 (@dest_finite_image a0 x0))) /\ (@IN nat (@dest_finite_image a0 x0) (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0))))) -> False.
Definition term77 (a0 : Type') (x0 : finite_image a0) := (fun y0 : finite_image a0 => (@finite_index a0 (@dest_finite_image a0 y0)) = y0) x0.
Definition term71 (a0 : Type') := fun y0 : nat => (fun y1 : nat => (~ (@IN nat y1 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0))))) \/ ((@dest_finite_image a0 (@finite_index a0 y1)) = y1)) y0.
Definition term69 (a0 : Type') := and (forall y0 : nat, (fun y1 : nat => (@IN nat y1 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0)))) \/ (~ ((@dest_finite_image a0 (@finite_index a0 y1)) = y1))) y0).
Definition term79 (x0 : Prop) (x1 : Prop) := (~ x0) \/ x1.
Definition term15 (a0 : Type') := fun y0 : nat => (@IN nat y0 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0)))) = ((@dest_finite_image a0 (@finite_index a0 y0)) = y0).
Definition term22 (a0 : Type') (x0 : finite_image a0) := fun y0 : nat => (x0 = (@finite_index a0 y0)) /\ (@IN nat y0 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0)))).
Definition term39 (a0 : Type') (x0 : finite_image a0) := (fun y0 : finite_image a0 => exists y1 : nat, (y0 = (@finite_index a0 y1)) /\ (@IN nat y1 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0))))) x0.
Definition term9 (a0 : Type') := ((forall y0 : finite_image a0, (@finite_index a0 (@dest_finite_image a0 y0)) = y0) /\ (forall y0 : nat, (@IN nat y0 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0)))) = ((@dest_finite_image a0 (@finite_index a0 y0)) = y0))) -> False.
Definition term109 (a0 : Type') (x0 : finite_image a0) (x1 : finite_image a0) (x2 : finite_image a0) := imp ((x1 = x0) /\ (x1 = x2)).
Definition term48 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term7 (a0 : Type') := (((~ (forall y0 : finite_image a0, exists y1 : nat, (y0 = (@finite_index a0 y1)) /\ (@IN nat y1 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0)))))) -> ((forall y0 : finite_image a0, (@finite_index a0 (@dest_finite_image a0 y0)) = y0) /\ (forall y0 : nat, (@IN nat y0 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0)))) = ((@dest_finite_image a0 (@finite_index a0 y0)) = y0))) -> False) -> (~ (forall y0 : finite_image a0, exists y1 : nat, (y0 = (@finite_index a0 y1)) /\ (@IN nat y1 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0)))))) -> ((forall y0 : finite_image a0, (@finite_index a0 (@dest_finite_image a0 y0)) = y0) /\ (forall y0 : nat, (@IN nat y0 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0)))) = ((@dest_finite_image a0 (@finite_index a0 y0)) = y0))) -> False) -> (~ (forall y0 : finite_image a0, exists y1 : nat, (y0 = (@finite_index a0 y1)) /\ (@IN nat y1 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0)))))) -> ((forall y0 : finite_image a0, (@finite_index a0 (@dest_finite_image a0 y0)) = y0) /\ (forall y0 : nat, (@IN nat y0 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0)))) = ((@dest_finite_image a0 (@finite_index a0 y0)) = y0))) -> False.
Definition term33 (a0 : Type') (x0 : finite_image a0) := fun y0 : nat => ~ ((fun y1 : nat => (x0 = (@finite_index a0 y1)) /\ (@IN nat y1 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0))))) y0).
Definition term112 (a0 : Type') (x0 : finite_image a0) := (((@finite_index a0 (@dest_finite_image a0 x0)) = x0) /\ ((@finite_index a0 (@dest_finite_image a0 x0)) = (@finite_index a0 (@dest_finite_image a0 x0)))) -> x0 = (@finite_index a0 (@dest_finite_image a0 x0)).
Definition term32 (a0 : Type') (x0 : finite_image a0) (x1 : nat) := ~ ((fun y0 : nat => (x0 = (@finite_index a0 y0)) /\ (@IN nat y0 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0))))) x1).
Definition term130 (a0 : Type') (x0 : nat) := ((@dest_finite_image a0 (@finite_index a0 x0)) = x0) -> @IN nat x0 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0))).
Definition term107 (a0 : Type') (x0 : finite_image a0) (x1 : finite_image a0) (x2 : finite_image a0) := (x1 = x0) /\ (x1 = x2).
Definition term104 (a0 : Type') (x0 : finite_image a0) (x1 : finite_image a0) := ~ (~ (x0 = x1)).
Definition term8 (a0 : Type') := (((~ (forall y0 : finite_image a0, exists y1 : nat, (y0 = (@finite_index a0 y1)) /\ (@IN nat y1 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0)))))) -> ((forall y0 : finite_image a0, (@finite_index a0 (@dest_finite_image a0 y0)) = y0) /\ (forall y0 : nat, (@IN nat y0 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0)))) = ((@dest_finite_image a0 (@finite_index a0 y0)) = y0))) -> False) -> (~ (forall y0 : finite_image a0, exists y1 : nat, (y0 = (@finite_index a0 y1)) /\ (@IN nat y1 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0)))))) -> ((forall y0 : finite_image a0, (@finite_index a0 (@dest_finite_image a0 y0)) = y0) /\ (forall y0 : nat, (@IN nat y0 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0)))) = ((@dest_finite_image a0 (@finite_index a0 y0)) = y0))) -> False) -> ((~ (forall y0 : finite_image a0, exists y1 : nat, (y0 = (@finite_index a0 y1)) /\ (@IN nat y1 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0)))))) -> ((forall y0 : finite_image a0, (@finite_index a0 (@dest_finite_image a0 y0)) = y0) /\ (forall y0 : nat, (@IN nat y0 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0)))) = ((@dest_finite_image a0 (@finite_index a0 y0)) = y0))) -> False) -> (~ (forall y0 : finite_image a0, exists y1 : nat, (y0 = (@finite_index a0 y1)) /\ (@IN nat y1 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0)))))) -> ((forall y0 : finite_image a0, (@finite_index a0 (@dest_finite_image a0 y0)) = y0) /\ (forall y0 : nat, (@IN nat y0 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0)))) = ((@dest_finite_image a0 (@finite_index a0 y0)) = y0))) -> False.
Definition term90 (a0 : Type') (x0 : finite_image a0) (x1 : finite_image a0) := or (~ (x0 = x1)).
Definition term73 (a0 : Type') := forall y0 : nat, (~ (@IN nat y0 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0))))) \/ ((@dest_finite_image a0 (@finite_index a0 y0)) = y0).
Definition term125 (a0 : Type') (x0 : nat) := (~ (~ ((@dest_finite_image a0 (@finite_index a0 x0)) = x0))) -> @IN nat x0 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0))).
Definition term86 (a0 : Type') (x0 : finite_image a0) := ~ ((@finite_index a0 (@dest_finite_image a0 x0)) = (@finite_index a0 (@dest_finite_image a0 x0))).
Definition term56 (a0 : Type') (x0 : nat) := (fun y0 : nat => (@IN nat y0 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0)))) \/ (~ ((@dest_finite_image a0 (@finite_index a0 y0)) = y0))) x0.
Definition term29 (a0 : Type') (x0 : finite_image a0) := ~ (exists y0 : nat, (x0 = (@finite_index a0 y0)) /\ (@IN nat y0 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0))))).
Definition term45 (a0 : Type') := fun y0 : nat => ((@IN nat y0 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0)))) \/ (~ ((@dest_finite_image a0 (@finite_index a0 y0)) = y0))) /\ ((~ (@IN nat y0 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0))))) \/ ((@dest_finite_image a0 (@finite_index a0 y0)) = y0)).
Definition term11 (a0 : Type') := imp (~ (forall y0 : finite_image a0, exists y1 : nat, (y0 = (@finite_index a0 y1)) /\ (@IN nat y1 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0)))))).
Definition term128 (a0 : Type') (x0 : nat) := imp (~ (~ ((@dest_finite_image a0 (@finite_index a0 x0)) = x0))).
Definition term6 (a0 : Type') := ((~ (forall y0 : finite_image a0, exists y1 : nat, (y0 = (@finite_index a0 y1)) /\ (@IN nat y1 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0)))))) -> ((forall y0 : finite_image a0, (@finite_index a0 (@dest_finite_image a0 y0)) = y0) /\ (forall y0 : nat, (@IN nat y0 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0)))) = ((@dest_finite_image a0 (@finite_index a0 y0)) = y0))) -> False) -> (~ (forall y0 : finite_image a0, exists y1 : nat, (y0 = (@finite_index a0 y1)) /\ (@IN nat y1 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0)))))) -> ((forall y0 : finite_image a0, (@finite_index a0 (@dest_finite_image a0 y0)) = y0) /\ (forall y0 : nat, (@IN nat y0 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0)))) = ((@dest_finite_image a0 (@finite_index a0 y0)) = y0))) -> False.
Definition term12 (a0 : Type') := (~ (forall y0 : finite_image a0, exists y1 : nat, (y0 = (@finite_index a0 y1)) /\ (@IN nat y1 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0)))))) -> ~ ((forall y0 : finite_image a0, (@finite_index a0 (@dest_finite_image a0 y0)) = y0) /\ (forall y0 : nat, (@IN nat y0 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0)))) = ((@dest_finite_image a0 (@finite_index a0 y0)) = y0))).
Definition term119 (a0 : Type') (x0 : finite_image a0) (x1 : finite_image a0) := imp (~ (~ (x0 = x1))).
Definition term129 (a0 : Type') (x0 : nat) := imp ((@dest_finite_image a0 (@finite_index a0 x0)) = x0).
