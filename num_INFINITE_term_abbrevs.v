Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term86 := (~ False) -> False.
Definition term16 := (@FINITE nat (@UNIV nat)) -> (forall y0 : nat, @IN nat y0 (@UNIV nat)) -> ~ (forall y0 : nat -> Prop, (@FINITE nat y0) -> exists y1 : nat, ~ (@IN nat y1 y0)).
Definition term53 (x0 : nat -> Prop) := (fun y0 : nat -> Prop => fun y1 : nat => (~ (@FINITE nat y0)) \/ (~ (@IN nat y1 y0))) x0.
Definition term7 := (((@FINITE nat (@UNIV nat)) -> (forall y0 : nat, @IN nat y0 (@UNIV nat)) -> (forall y0 : nat -> Prop, (@FINITE nat y0) -> exists y1 : nat, ~ (@IN nat y1 y0)) -> False) -> (@FINITE nat (@UNIV nat)) -> (forall y0 : nat, @IN nat y0 (@UNIV nat)) -> (forall y0 : nat -> Prop, (@FINITE nat y0) -> exists y1 : nat, ~ (@IN nat y1 y0)) -> False) -> (@FINITE nat (@UNIV nat)) -> (forall y0 : nat, @IN nat y0 (@UNIV nat)) -> (forall y0 : nat -> Prop, (@FINITE nat y0) -> exists y1 : nat, ~ (@IN nat y1 y0)) -> False.
Definition term61 (x0 : type994) (x1 : nat -> Prop) := (fun y0 : nat -> Prop => fun y1 : nat => (~ (@FINITE nat y0)) \/ (~ (@IN nat y1 y0))) x1 (x0 x1).
Definition term71 (x0 : nat) := (fun y0 : nat => @IN nat y0 (@UNIV nat)) x0.
Definition term57 (x0 : nat -> Prop) := exists y0 : nat, (fun y1 : nat -> Prop => fun y2 : nat => (~ (@FINITE nat y1)) \/ (~ (@IN nat y2 y1))) x0 y0.
Definition term26 := fun y0 : nat -> Prop => (~ (@FINITE nat y0)) \/ (exists y1 : nat, ~ (@IN nat y1 y0)).
Definition term10 := ~ (forall y0 : nat -> Prop, (@FINITE nat y0) -> exists y1 : nat, ~ (@IN nat y1 y0)).
Definition term73 := (~ (@FINITE nat (@UNIV nat))) -> @FINITE nat (@UNIV nat).
Definition term41 (x0 : nat -> Prop) := fun y0 : nat => (~ (@FINITE nat x0)) \/ ((fun y1 : nat => ~ (@IN nat y1 x0)) y0).
Definition term32 (x0 : nat -> Prop) := (~ (@FINITE nat x0)) \/ (exists y0 : nat, (fun y1 : nat => ~ (@IN nat y1 x0)) y0).
Definition term44 := fun y0 : nat -> Prop => exists y1 : nat, (~ (@FINITE nat y0)) \/ (~ (@IN nat y1 y0)).
Definition term31 (x0 : Prop) (x1 : nat -> Prop) := exists y0 : nat, x0 \/ (x1 y0).
Definition term64 (x0 : type994) := fun y0 : nat -> Prop => (fun y1 : nat -> Prop => fun y2 : nat => (~ (@FINITE nat y1)) \/ (~ (@IN nat y2 y1))) y0 (x0 y0).
Definition term8 := (((@FINITE nat (@UNIV nat)) -> (forall y0 : nat, @IN nat y0 (@UNIV nat)) -> (forall y0 : nat -> Prop, (@FINITE nat y0) -> exists y1 : nat, ~ (@IN nat y1 y0)) -> False) -> (@FINITE nat (@UNIV nat)) -> (forall y0 : nat, @IN nat y0 (@UNIV nat)) -> (forall y0 : nat -> Prop, (@FINITE nat y0) -> exists y1 : nat, ~ (@IN nat y1 y0)) -> False) -> ((@FINITE nat (@UNIV nat)) -> (forall y0 : nat, @IN nat y0 (@UNIV nat)) -> (forall y0 : nat -> Prop, (@FINITE nat y0) -> exists y1 : nat, ~ (@IN nat y1 y0)) -> False) -> (@FINITE nat (@UNIV nat)) -> (forall y0 : nat, @IN nat y0 (@UNIV nat)) -> (forall y0 : nat -> Prop, (@FINITE nat y0) -> exists y1 : nat, ~ (@IN nat y1 y0)) -> False.
Definition term13 := (forall y0 : nat, @IN nat y0 (@UNIV nat)) -> (forall y0 : nat -> Prop, (@FINITE nat y0) -> exists y1 : nat, ~ (@IN nat y1 y0)) -> False.
Definition term19 (x0 : nat -> Prop) := exists y0 : nat, ~ (@IN nat y0 x0).
Definition term63 (x0 : type994) (x1 : nat -> Prop) := (~ (@FINITE nat x1)) \/ (~ (@IN nat (x0 x1) x1)).
Definition term78 (x0 : Prop) (x1 : Prop) := (~ x0) \/ (~ x1).
Definition term12 := imp (forall y0 : nat, @IN nat y0 (@UNIV nat)).
Definition term74 (x0 : Prop) := (~ x0) -> x0.
Definition term46 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := forall y0 : a0, exists y1 : a1, x0 y0 y1.
Definition term6 := ((@FINITE nat (@UNIV nat)) -> (forall y0 : nat, @IN nat y0 (@UNIV nat)) -> (forall y0 : nat -> Prop, (@FINITE nat y0) -> exists y1 : nat, ~ (@IN nat y1 y0)) -> False) -> (@FINITE nat (@UNIV nat)) -> (forall y0 : nat, @IN nat y0 (@UNIV nat)) -> (forall y0 : nat -> Prop, (@FINITE nat y0) -> exists y1 : nat, ~ (@IN nat y1 y0)) -> False.
Definition term14 := (forall y0 : nat, @IN nat y0 (@UNIV nat)) -> ~ (forall y0 : nat -> Prop, (@FINITE nat y0) -> exists y1 : nat, ~ (@IN nat y1 y0)).
Definition term79 (x0 : Prop) (x1 : Prop) := ~ (x0 /\ x1).
Definition term70 := exists y0 : type994, forall y1 : nat -> Prop, (~ (@FINITE nat y1)) \/ (~ (@IN nat (y0 y1) y1)).
Definition term51 := exists y0 : type994, forall y1 : nat -> Prop, (fun y2 : nat -> Prop => fun y3 : nat => (~ (@FINITE nat y2)) \/ (~ (@IN nat y3 y2))) y1 (y0 y1).
Definition term49 (x0 : type991) := exists y0 : type994, forall y1 : nat -> Prop, x0 y1 (y0 y1).
Definition term52 := fun y0 : nat -> Prop => fun y1 : nat => (~ (@FINITE nat y0)) \/ (~ (@IN nat y1 y0)).
Definition term27 := forall y0 : nat -> Prop, (~ (@FINITE nat y0)) \/ (exists y1 : nat, ~ (@IN nat y1 y0)).
Definition term2 (x0 : nat -> Prop) := ~ (@FINITE nat x0).
Definition term36 (x0 : nat -> Prop) := exists y0 : nat, (fun y1 : nat => ~ (@IN nat y1 x0)) y0.
Definition term76 (x0 : type994) := (~ (@IN nat (x0 (@UNIV nat)) (@UNIV nat))) -> @IN nat (x0 (@UNIV nat)) (@UNIV nat).
Definition term1 (a0 : Type') (x0 : a0 -> Prop) := ~ (@FINITE a0 x0).
Definition term18 (x0 : nat -> Prop) := fun y0 : nat => ~ (@IN nat y0 x0).
Definition term50 := forall y0 : nat -> Prop, exists y1 : nat, (fun y2 : nat -> Prop => fun y3 : nat => (~ (@FINITE nat y2)) \/ (~ (@IN nat y3 y2))) y0 y1.
Definition term48 (x0 : type991) := forall y0 : nat -> Prop, exists y1 : nat, x0 y0 y1.
Definition term68 := fun y0 : type994 => forall y1 : nat -> Prop, (fun y2 : nat -> Prop => fun y3 : nat => (~ (@FINITE nat y2)) \/ (~ (@IN nat y3 y2))) y1 (y0 y1).
Definition term15 := imp (@FINITE nat (@UNIV nat)).
Definition term11 := forall y0 : nat -> Prop, (@FINITE nat y0) -> exists y1 : nat, ~ (@IN nat y1 y0).
Definition term17 (x0 : nat) (x1 : nat -> Prop) := ~ (@IN nat x0 x1).
Definition term38 (x0 : nat -> Prop) := @eq Prop ((~ (@FINITE nat x0)) \/ (exists y0 : nat, ~ (@IN nat y0 x0))).
Definition term37 (x0 : nat -> Prop) := @eq Prop ((~ (@FINITE nat x0)) \/ (exists y0 : nat, (fun y1 : nat => ~ (@IN nat y1 x0)) y0)).
Definition term60 := @eq Prop (forall y0 : nat -> Prop, exists y1 : nat, (~ (@FINITE nat y0)) \/ (~ (@IN nat y1 y0))).
Definition term59 := @eq Prop (forall y0 : nat -> Prop, exists y1 : nat, (fun y2 : nat -> Prop => fun y3 : nat => (~ (@FINITE nat y2)) \/ (~ (@IN nat y3 y2))) y0 y1).
Definition term40 (x0 : nat) (x1 : nat -> Prop) := (~ (@FINITE nat x1)) \/ (~ (@IN nat x0 x1)).
Definition term29 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 \/ (x1 y0).
Definition term22 := fun y0 : nat -> Prop => (@FINITE nat y0) -> exists y1 : nat, ~ (@IN nat y1 y0).
Definition term69 := fun y0 : type994 => forall y1 : nat -> Prop, (~ (@FINITE nat y1)) \/ (~ (@IN nat (y0 y1) y1)).
Definition term28 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 \/ (exists y0 : a0, x1 y0).
Definition term24 (x0 : nat -> Prop) := or (~ (@FINITE nat x0)).
Definition term33 (x0 : nat -> Prop) := exists y0 : nat, (~ (@FINITE nat x0)) \/ ((fun y1 : nat => ~ (@IN nat y1 x0)) y0).
Definition term65 (x0 : type994) := fun y0 : nat -> Prop => (~ (@FINITE nat y0)) \/ (~ (@IN nat (x0 y0) y0)).
Definition term85 (x0 : type994) := ((@FINITE nat (@UNIV nat)) /\ (@IN nat (x0 (@UNIV nat)) (@UNIV nat))) -> False.
Definition term56 (x0 : nat -> Prop) := fun y0 : nat => (fun y1 : nat -> Prop => fun y2 : nat => (~ (@FINITE nat y1)) \/ (~ (@IN nat y2 y1))) x0 y0.
Definition term9 := (forall y0 : nat -> Prop, (@FINITE nat y0) -> exists y1 : nat, ~ (@IN nat y1 y0)) -> False.
Definition term23 := fun y0 : nat => @IN nat y0 (@UNIV nat).
Definition term80 (x0 : type994) (x1 : nat -> Prop) := ~ ((@FINITE nat x1) /\ (@IN nat (x0 x1) x1)).
Definition term21 (x0 : nat -> Prop) := (@FINITE nat x0) -> exists y0 : nat, ~ (@IN nat y0 x0).
Definition term43 (x0 : nat -> Prop) := exists y0 : nat, (~ (@FINITE nat x0)) \/ (~ (@IN nat y0 x0)).
Definition term72 (x0 : type994) (x1 : nat -> Prop) := (fun y0 : nat -> Prop => (~ (@FINITE nat y0)) \/ (~ (@IN nat (x0 y0) y0))) x1.
Definition term58 := fun y0 : nat -> Prop => exists y1 : nat, (fun y2 : nat -> Prop => fun y3 : nat => (~ (@FINITE nat y2)) \/ (~ (@IN nat y3 y2))) y0 y1.
Definition term4 := forall y0 : nat, @IN nat y0 (@UNIV nat).
Definition term54 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat -> Prop => fun y1 : nat => (~ (@FINITE nat y0)) \/ (~ (@IN nat y1 y0))) x0 x1.
Definition term42 (x0 : nat -> Prop) := fun y0 : nat => (~ (@FINITE nat x0)) \/ (~ (@IN nat y0 x0)).
Definition term82 (x0 : type994) (x1 : nat -> Prop) := ((@FINITE nat x1) /\ (@IN nat (x0 x1) x1)) -> False.
Definition term66 (x0 : type994) := forall y0 : nat -> Prop, (fun y1 : nat -> Prop => fun y2 : nat => (~ (@FINITE nat y1)) \/ (~ (@IN nat y2 y1))) y0 (x0 y0).
Definition term87 := (@FINITE nat (@UNIV nat)) -> False.
Definition term84 (x0 : type994) := (@FINITE nat (@UNIV nat)) /\ (@IN nat (x0 (@UNIV nat)) (@UNIV nat)).
Definition term81 (x0 : type994) (x1 : nat -> Prop) := @IN nat (x0 x1) x1.
Definition term34 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => ~ (@IN nat y0 x0)) x1.
Definition term77 (x0 : type994) := ~ (@IN nat (x0 (@UNIV nat)) (@UNIV nat)).
Definition term62 (x0 : type994) (x1 : nat -> Prop) := (fun y0 : nat => (~ (@FINITE nat x1)) \/ (~ (@IN nat y0 x1))) (x0 x1).
Definition term3 := ~ (@FINITE nat (@UNIV nat)).
Definition term75 (x0 : type994) := @IN nat (x0 (@UNIV nat)) (@UNIV nat).
Definition term35 (x0 : nat -> Prop) := fun y0 : nat => (fun y1 : nat => ~ (@IN nat y1 x0)) y0.
Definition term5 := (@FINITE nat (@UNIV nat)) -> (forall y0 : nat, @IN nat y0 (@UNIV nat)) -> (forall y0 : nat -> Prop, (@FINITE nat y0) -> exists y1 : nat, ~ (@IN nat y1 y0)) -> False.
Definition term20 (x0 : nat -> Prop) := imp (@FINITE nat x0).
Definition term83 (x0 : type994) (x1 : nat -> Prop) := (@FINITE nat x1) /\ (@IN nat (x0 x1) x1).
Definition term67 (x0 : type994) := forall y0 : nat -> Prop, (~ (@FINITE nat y0)) \/ (~ (@IN nat (x0 y0) y0)).
Definition term25 (x0 : nat -> Prop) := (~ (@FINITE nat x0)) \/ (exists y0 : nat, ~ (@IN nat y0 x0)).
Definition term47 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := exists y0 : a0 -> a1, forall y1 : a0, x0 y1 (y0 y1).
Definition term0 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@INFINITE a0 y0) = (~ (@FINITE a0 y0))) x0.
Definition term30 (x0 : Prop) (x1 : nat -> Prop) := x0 \/ (exists y0 : nat, x1 y0).
Definition term45 := forall y0 : nat -> Prop, exists y1 : nat, (~ (@FINITE nat y0)) \/ (~ (@IN nat y1 y0)).
Definition term55 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => (~ (@FINITE nat x0)) \/ (~ (@IN nat y0 x0))) x1.
Definition term39 (x0 : nat -> Prop) (x1 : nat) := (~ (@FINITE nat x0)) \/ ((fun y0 : nat => ~ (@IN nat y0 x0)) x1).
