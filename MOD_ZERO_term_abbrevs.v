Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term85 := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, (~ (y2 = (NUMERAL 0))) \/ (((Nat.div y1 y2) = (NUMERAL 0)) /\ ((Nat.modulo y1 y2) = y1))) y0) /\ ((fun y1 : nat => forall y2 : nat, (y2 = (NUMERAL 0)) \/ ((y1 = (Nat.add (Nat.mul (Nat.div y1 y2) y2) (Nat.modulo y1 y2))) /\ (Peano.lt (Nat.modulo y1 y2) y2))) y0).
Definition term104 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((~ (y0 = (NUMERAL 0))) \/ ((Nat.div x0 y0) = (NUMERAL 0))) /\ ((~ (y0 = (NUMERAL 0))) \/ ((Nat.modulo x0 y0) = x0))) x1.
Definition term39 (x0 : nat -> Prop) := ~ (all x0).
Definition term122 := (~ False) -> False.
Definition term4 := (~ (forall y0 : nat, (Nat.modulo y0 (NUMERAL 0)) = y0)) -> (forall y0 : nat, forall y1 : nat, @COND Prop (y1 = (NUMERAL 0)) (((Nat.div y0 y1) = (NUMERAL 0)) /\ ((Nat.modulo y0 y1) = y0)) ((y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1))) -> False.
Definition term30 (x0 : nat) := forall y0 : nat, @COND Prop (y0 = (NUMERAL 0)) (((Nat.div x0 y0) = (NUMERAL 0)) /\ ((Nat.modulo x0 y0) = x0)) ((x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0)).
Definition term56 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (y0 = (NUMERAL 0))) \/ (((Nat.div x0 y0) = (NUMERAL 0)) /\ ((Nat.modulo x0 y0) = x0))) x1.
Definition term16 (x0 : nat) (x1 : nat) := @COND Prop False (((Nat.div x1 x0) = (NUMERAL 0)) /\ ((Nat.modulo x1 x0) = x1)).
Definition term20 (x0 : nat) (x1 : nat) := ((x1 = (NUMERAL 0)) = False) -> (@COND Prop (x1 = (NUMERAL 0)) (((Nat.div x0 x1) = (NUMERAL 0)) /\ ((Nat.modulo x0 x1) = x0)) ((x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1))) = ((x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1)).
Definition term77 := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (~ (y2 = (NUMERAL 0))) \/ (((Nat.div y1 y2) = (NUMERAL 0)) /\ ((Nat.modulo y1 y2) = y1))) y0) /\ ((fun y1 : nat => forall y2 : nat, (y2 = (NUMERAL 0)) \/ ((y1 = (Nat.add (Nat.mul (Nat.div y1 y2) y2) (Nat.modulo y1 y2))) /\ (Peano.lt (Nat.modulo y1 y2) y2))) y0).
Definition term52 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => (~ (y1 = (NUMERAL 0))) \/ (((Nat.div x0 y1) = (NUMERAL 0)) /\ ((Nat.modulo x0 y1) = x0))) y0) /\ ((fun y1 : nat => (y1 = (NUMERAL 0)) \/ ((x0 = (Nat.add (Nat.mul (Nat.div x0 y1) y1) (Nat.modulo x0 y1))) /\ (Peano.lt (Nat.modulo x0 y1) y1))) y0).
Definition term114 (x0 : Prop) := ~ (~ x0).
Definition term73 (x0 : nat) := forall y0 : nat, (y0 = (NUMERAL 0)) \/ ((x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0)).
Definition term63 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => (~ (y1 = (NUMERAL 0))) \/ (((Nat.div x0 y1) = (NUMERAL 0)) /\ ((Nat.modulo x0 y1) = x0))) y0) /\ ((fun y1 : nat => (y1 = (NUMERAL 0)) \/ ((x0 = (Nat.add (Nat.mul (Nat.div x0 y1) y1) (Nat.modulo x0 y1))) /\ (Peano.lt (Nat.modulo x0 y1) y1))) y0).
Definition term36 (x0 : nat) := Nat.modulo x0 (NUMERAL 0).
Definition term106 := (~ ((NUMERAL 0) = (NUMERAL 0))) -> (NUMERAL 0) = (NUMERAL 0).
Definition term0 (x0 : Prop) := (~ x0) -> False.
Definition term78 := (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (y2 = (NUMERAL 0))) \/ (((Nat.div y1 y2) = (NUMERAL 0)) /\ ((Nat.modulo y1 y2) = y1))) y0) /\ (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (y2 = (NUMERAL 0)) \/ ((y1 = (Nat.add (Nat.mul (Nat.div y1 y2) y2) (Nat.modulo y1 y2))) /\ (Peano.lt (Nat.modulo y1 y2) y2))) y0).
Definition term53 (x0 : nat) := (forall y0 : nat, (fun y1 : nat => (~ (y1 = (NUMERAL 0))) \/ (((Nat.div x0 y1) = (NUMERAL 0)) /\ ((Nat.modulo x0 y1) = x0))) y0) /\ (forall y0 : nat, (fun y1 : nat => (y1 = (NUMERAL 0)) \/ ((x0 = (Nat.add (Nat.mul (Nat.div x0 y1) y1) (Nat.modulo x0 y1))) /\ (Peano.lt (Nat.modulo x0 y1) y1))) y0).
Definition term96 := (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) \/ (((Nat.div y0 y1) = (NUMERAL 0)) /\ ((Nat.modulo y0 y1) = y0))) /\ (forall y0 : nat, forall y1 : nat, (y1 = (NUMERAL 0)) \/ ((y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1))).
Definition term100 (x0 : nat) := forall y0 : nat, ((~ (y0 = (NUMERAL 0))) \/ ((Nat.div x0 y0) = (NUMERAL 0))) /\ ((~ (y0 = (NUMERAL 0))) \/ ((Nat.modulo x0 y0) = x0)).
Definition term23 (x0 : nat) (x1 : nat) := ((x0 = (NUMERAL 0)) = True) -> (@COND Prop (x0 = (NUMERAL 0)) (((Nat.div x1 x0) = (NUMERAL 0)) /\ ((Nat.modulo x1 x0) = x1)) ((x1 = (Nat.add (Nat.mul (Nat.div x1 x0) x0) (Nat.modulo x1 x0))) /\ (Peano.lt (Nat.modulo x1 x0) x0))) = (((Nat.div x1 x0) = (NUMERAL 0)) /\ ((Nat.modulo x1 x0) = x1)).
Definition term72 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (y1 = (NUMERAL 0)) \/ ((x0 = (Nat.add (Nat.mul (Nat.div x0 y1) y1) (Nat.modulo x0 y1))) /\ (Peano.lt (Nat.modulo x0 y1) y1))) y0.
Definition term67 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (~ (y1 = (NUMERAL 0))) \/ (((Nat.div x0 y1) = (NUMERAL 0)) /\ ((Nat.modulo x0 y1) = x0))) y0.
Definition term15 (x0 : nat) (x1 : nat) := @COND Prop (x0 = (NUMERAL 0)) (((Nat.div x1 x0) = (NUMERAL 0)) /\ ((Nat.modulo x1 x0) = x1)).
Definition term112 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term50 (x0 : nat -> Prop) (x1 : nat -> Prop) := forall y0 : nat, (x0 y0) /\ (x1 y0).
Definition term22 (x0 : nat) (x1 : nat) := @COND Prop True (((Nat.div x0 x1) = (NUMERAL 0)) /\ ((Nat.modulo x0 x1) = x0)) ((x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1)).
Definition term75 := fun y0 : nat => (forall y1 : nat, (~ (y1 = (NUMERAL 0))) \/ (((Nat.div y0 y1) = (NUMERAL 0)) /\ ((Nat.modulo y0 y1) = y0))) /\ (forall y1 : nat, (y1 = (NUMERAL 0)) \/ ((y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1))).
Definition term35 := ~ (forall y0 : nat, forall y1 : nat, ((~ (y1 = (NUMERAL 0))) \/ (((Nat.div y0 y1) = (NUMERAL 0)) /\ ((Nat.modulo y0 y1) = y0))) /\ ((y1 = (NUMERAL 0)) \/ ((y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)))).
Definition term9 := ~ (forall y0 : nat, forall y1 : nat, @COND Prop (y1 = (NUMERAL 0)) (((Nat.div y0 y1) = (NUMERAL 0)) /\ ((Nat.modulo y0 y1) = y0)) ((y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1))).
Definition term42 (x0 : nat) := (fun y0 : nat => (Nat.modulo y0 (NUMERAL 0)) = y0) x0.
Definition term17 (x0 : nat) (x1 : nat) := (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1).
Definition term27 (x0 : nat) (x1 : nat) := ((~ (x1 = (NUMERAL 0))) \/ (((Nat.div x0 x1) = (NUMERAL 0)) /\ ((Nat.modulo x0 x1) = x0))) /\ ((x1 = (NUMERAL 0)) \/ ((x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1))).
Definition term108 (x0 : Prop) := (~ x0) -> x0.
Definition term55 (x0 : nat) := fun y0 : nat => (y0 = (NUMERAL 0)) \/ ((x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0)).
Definition term57 (x0 : nat) (x1 : nat) := (~ (x0 = (NUMERAL 0))) \/ (((Nat.div x1 x0) = (NUMERAL 0)) /\ ((Nat.modulo x1 x0) = x1)).
Definition term87 := @eq Prop (forall y0 : nat, (forall y1 : nat, (~ (y1 = (NUMERAL 0))) \/ (((Nat.div y0 y1) = (NUMERAL 0)) /\ ((Nat.modulo y0 y1) = y0))) /\ (forall y1 : nat, (y1 = (NUMERAL 0)) \/ ((y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)))).
Definition term86 := @eq Prop (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (~ (y2 = (NUMERAL 0))) \/ (((Nat.div y1 y2) = (NUMERAL 0)) /\ ((Nat.modulo y1 y2) = y1))) y0) /\ ((fun y1 : nat => forall y2 : nat, (y2 = (NUMERAL 0)) \/ ((y1 = (Nat.add (Nat.mul (Nat.div y1 y2) y2) (Nat.modulo y1 y2))) /\ (Peano.lt (Nat.modulo y1 y2) y2))) y0)).
Definition term65 (x0 : nat) := @eq Prop (forall y0 : nat, ((~ (y0 = (NUMERAL 0))) \/ (((Nat.div x0 y0) = (NUMERAL 0)) /\ ((Nat.modulo x0 y0) = x0))) /\ ((y0 = (NUMERAL 0)) \/ ((x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0)))).
Definition term64 (x0 : nat) := @eq Prop (forall y0 : nat, ((fun y1 : nat => (~ (y1 = (NUMERAL 0))) \/ (((Nat.div x0 y1) = (NUMERAL 0)) /\ ((Nat.modulo x0 y1) = x0))) y0) /\ ((fun y1 : nat => (y1 = (NUMERAL 0)) \/ ((x0 = (Nat.add (Nat.mul (Nat.div x0 y1) y1) (Nat.modulo x0 y1))) /\ (Peano.lt (Nat.modulo x0 y1) y1))) y0)).
Definition term49 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term107 := ~ ((NUMERAL 0) = (NUMERAL 0)).
Definition term13 (x0 : nat) := @COND Prop (x0 = (NUMERAL 0)).
Definition term98 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term117 (x0 : nat) := imp (x0 = (NUMERAL 0)).
Definition term1 := forall y0 : nat, (Nat.modulo y0 (NUMERAL 0)) = y0.
Definition term43 (x0 : nat) := ~ ((fun y0 : nat => (Nat.modulo y0 (NUMERAL 0)) = y0) x0).
Definition term111 (x0 : nat) (x1 : nat) := @eq Prop (((Nat.modulo x0 x1) = x0) \/ (~ (x1 = (NUMERAL 0)))).
Definition term123 := (forall y0 : nat, forall y1 : nat, ((~ (y1 = (NUMERAL 0))) \/ (((Nat.div y0 y1) = (NUMERAL 0)) /\ ((Nat.modulo y0 y1) = y0))) /\ ((y1 = (NUMERAL 0)) \/ ((y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)))) -> False.
Definition term8 := (forall y0 : nat, forall y1 : nat, @COND Prop (y1 = (NUMERAL 0)) (((Nat.div y0 y1) = (NUMERAL 0)) /\ ((Nat.modulo y0 y1) = y0)) ((y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1))) -> False.
Definition term59 (x0 : nat) (x1 : nat) := and ((~ (x0 = (NUMERAL 0))) \/ (((Nat.div x1 x0) = (NUMERAL 0)) /\ ((Nat.modulo x1 x0) = x1))).
Definition term70 (x0 : nat) := and (forall y0 : nat, (~ (y0 = (NUMERAL 0))) \/ (((Nat.div x0 y0) = (NUMERAL 0)) /\ ((Nat.modulo x0 y0) = x0))).
Definition term14 (x0 : nat) (x1 : nat) := ((Nat.div x1 x0) = (NUMERAL 0)) /\ ((Nat.modulo x1 x0) = x1).
Definition term18 (x0 : nat) (x1 : nat) := @COND Prop (x1 = (NUMERAL 0)) (((Nat.div x0 x1) = (NUMERAL 0)) /\ ((Nat.modulo x0 x1) = x0)) ((x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1)).
Definition term6 := (((~ (forall y0 : nat, (Nat.modulo y0 (NUMERAL 0)) = y0)) -> (forall y0 : nat, forall y1 : nat, @COND Prop (y1 = (NUMERAL 0)) (((Nat.div y0 y1) = (NUMERAL 0)) /\ ((Nat.modulo y0 y1) = y0)) ((y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1))) -> False) -> (~ (forall y0 : nat, (Nat.modulo y0 (NUMERAL 0)) = y0)) -> (forall y0 : nat, forall y1 : nat, @COND Prop (y1 = (NUMERAL 0)) (((Nat.div y0 y1) = (NUMERAL 0)) /\ ((Nat.modulo y0 y1) = y0)) ((y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1))) -> False) -> (~ (forall y0 : nat, (Nat.modulo y0 (NUMERAL 0)) = y0)) -> (forall y0 : nat, forall y1 : nat, @COND Prop (y1 = (NUMERAL 0)) (((Nat.div y0 y1) = (NUMERAL 0)) /\ ((Nat.modulo y0 y1) = y0)) ((y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1))) -> False.
Definition term110 (x0 : nat) (x1 : nat) := @eq Prop ((~ (x0 = (NUMERAL 0))) \/ ((Nat.modulo x1 x0) = x1)).
Definition term99 (x0 : nat) := fun y0 : nat => ((~ (y0 = (NUMERAL 0))) \/ ((Nat.div x0 y0) = (NUMERAL 0))) /\ ((~ (y0 = (NUMERAL 0))) \/ ((Nat.modulo x0 y0) = x0)).
Definition term71 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (y1 = (NUMERAL 0)) \/ ((x0 = (Nat.add (Nat.mul (Nat.div x0 y1) y1) (Nat.modulo x0 y1))) /\ (Peano.lt (Nat.modulo x0 y1) y1))) y0.
Definition term66 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (~ (y1 = (NUMERAL 0))) \/ (((Nat.div x0 y1) = (NUMERAL 0)) /\ ((Nat.modulo x0 y1) = x0))) y0.
Definition term102 := forall y0 : nat, forall y1 : nat, ((~ (y1 = (NUMERAL 0))) \/ ((Nat.div y0 y1) = (NUMERAL 0))) /\ ((~ (y1 = (NUMERAL 0))) \/ ((Nat.modulo y0 y1) = y0)).
Definition term95 := forall y0 : nat, forall y1 : nat, (y1 = (NUMERAL 0)) \/ ((y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term90 := forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) \/ (((Nat.div y0 y1) = (NUMERAL 0)) /\ ((Nat.modulo y0 y1) = y0)).
Definition term34 := forall y0 : nat, forall y1 : nat, ((~ (y1 = (NUMERAL 0))) \/ (((Nat.div y0 y1) = (NUMERAL 0)) /\ ((Nat.modulo y0 y1) = y0))) /\ ((y1 = (NUMERAL 0)) \/ ((y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1))).
Definition term10 := forall y0 : nat, forall y1 : nat, @COND Prop (y1 = (NUMERAL 0)) (((Nat.div y0 y1) = (NUMERAL 0)) /\ ((Nat.modulo y0 y1) = y0)) ((y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term46 := fun y0 : nat => ~ ((Nat.modulo y0 (NUMERAL 0)) = y0).
Definition term84 (x0 : nat) := ((fun y0 : nat => forall y1 : nat, (~ (y1 = (NUMERAL 0))) \/ (((Nat.div y0 y1) = (NUMERAL 0)) /\ ((Nat.modulo y0 y1) = y0))) x0) /\ ((fun y0 : nat => forall y1 : nat, (y1 = (NUMERAL 0)) \/ ((y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1))) x0).
Definition term113 (x0 : nat) (x1 : nat) := (~ (~ (x0 = (NUMERAL 0)))) -> (Nat.modulo x1 x0) = x1.
Definition term32 := fun y0 : nat => forall y1 : nat, @COND Prop (y1 = (NUMERAL 0)) (((Nat.div y0 y1) = (NUMERAL 0)) /\ ((Nat.modulo y0 y1) = y0)) ((y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term2 := (~ (forall y0 : nat, (Nat.modulo y0 (NUMERAL 0)) = y0)) -> False.
Definition term62 (x0 : nat) (x1 : nat) := ((fun y0 : nat => (~ (y0 = (NUMERAL 0))) \/ (((Nat.div x0 y0) = (NUMERAL 0)) /\ ((Nat.modulo x0 y0) = x0))) x1) /\ ((fun y0 : nat => (y0 = (NUMERAL 0)) \/ ((x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0))) x1).
Definition term51 (x0 : nat -> Prop) (x1 : nat -> Prop) := (forall y0 : nat, x0 y0) /\ (forall y0 : nat, x1 y0).
Definition term44 (x0 : nat) := ~ ((Nat.modulo x0 (NUMERAL 0)) = x0).
Definition term29 (x0 : nat) := fun y0 : nat => ((~ (y0 = (NUMERAL 0))) \/ (((Nat.div x0 y0) = (NUMERAL 0)) /\ ((Nat.modulo x0 y0) = x0))) /\ ((y0 = (NUMERAL 0)) \/ ((x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0))).
Definition term105 (x0 : nat) (x1 : nat) := (~ (x0 = (NUMERAL 0))) \/ ((Nat.modulo x1 x0) = x1).
Definition term121 (x0 : nat) := ((Nat.modulo x0 (NUMERAL 0)) = x0) -> False.
Definition term74 (x0 : nat) := (forall y0 : nat, (~ (y0 = (NUMERAL 0))) \/ (((Nat.div x0 y0) = (NUMERAL 0)) /\ ((Nat.modulo x0 y0) = x0))) /\ (forall y0 : nat, (y0 = (NUMERAL 0)) \/ ((x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0))).
Definition term60 (x0 : nat) (x1 : nat) := (fun y0 : nat => (y0 = (NUMERAL 0)) \/ ((x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0))) x1.
Definition term92 := and (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) \/ (((Nat.div y0 y1) = (NUMERAL 0)) /\ ((Nat.modulo y0 y1) = y0))).
Definition term120 (x0 : nat) := (~ ((Nat.modulo x0 (NUMERAL 0)) = x0)) -> (Nat.modulo x0 (NUMERAL 0)) = x0.
Definition term25 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (((x2 = False) -> x0 = x3) /\ ((x2 = True) -> x0 = x1)) -> x0 = (((~ x2) \/ x1) /\ (x2 \/ x3)).
Definition term68 (x0 : nat) := forall y0 : nat, (~ (y0 = (NUMERAL 0))) \/ (((Nat.div x0 y0) = (NUMERAL 0)) /\ ((Nat.modulo x0 y0) = x0)).
Definition term93 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (y2 = (NUMERAL 0)) \/ ((y1 = (Nat.add (Nat.mul (Nat.div y1 y2) y2) (Nat.modulo y1 y2))) /\ (Peano.lt (Nat.modulo y1 y2) y2))) y0.
Definition term88 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (~ (y2 = (NUMERAL 0))) \/ (((Nat.div y1 y2) = (NUMERAL 0)) /\ ((Nat.modulo y1 y2) = y1))) y0.
Definition term103 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((~ (y1 = (NUMERAL 0))) \/ ((Nat.div y0 y1) = (NUMERAL 0))) /\ ((~ (y1 = (NUMERAL 0))) \/ ((Nat.modulo y0 y1) = y0))) x0.
Definition term83 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (y1 = (NUMERAL 0)) \/ ((y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1))) x0.
Definition term81 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (y1 = (NUMERAL 0))) \/ (((Nat.div y0 y1) = (NUMERAL 0)) /\ ((Nat.modulo y0 y1) = y0))) x0.
Definition term54 (x0 : nat) := fun y0 : nat => (~ (y0 = (NUMERAL 0))) \/ (((Nat.div x0 y0) = (NUMERAL 0)) /\ ((Nat.modulo x0 y0) = x0)).
Definition term109 (x0 : nat) (x1 : nat) := ((Nat.modulo x0 x1) = x0) \/ (~ (x1 = (NUMERAL 0))).
Definition term119 (x0 : nat) := ((NUMERAL 0) = (NUMERAL 0)) -> (Nat.modulo x0 (NUMERAL 0)) = x0.
Definition term45 := fun y0 : nat => ~ ((fun y1 : nat => (Nat.modulo y1 (NUMERAL 0)) = y1) y0).
Definition term41 := exists y0 : nat, ~ ((fun y1 : nat => (Nat.modulo y1 (NUMERAL 0)) = y1) y0).
Definition term38 := (~ (forall y0 : nat, (Nat.modulo y0 (NUMERAL 0)) = y0)) -> ~ (forall y0 : nat, forall y1 : nat, ((~ (y1 = (NUMERAL 0))) \/ (((Nat.div y0 y1) = (NUMERAL 0)) /\ ((Nat.modulo y0 y1) = y0))) /\ ((y1 = (NUMERAL 0)) \/ ((y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)))).
Definition term12 := (~ (forall y0 : nat, (Nat.modulo y0 (NUMERAL 0)) = y0)) -> ~ (forall y0 : nat, forall y1 : nat, @COND Prop (y1 = (NUMERAL 0)) (((Nat.div y0 y1) = (NUMERAL 0)) /\ ((Nat.modulo y0 y1) = y0)) ((y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1))).
Definition term91 := and (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (y2 = (NUMERAL 0))) \/ (((Nat.div y1 y2) = (NUMERAL 0)) /\ ((Nat.modulo y1 y2) = y1))) y0).
Definition term69 (x0 : nat) := and (forall y0 : nat, (fun y1 : nat => (~ (y1 = (NUMERAL 0))) \/ (((Nat.div x0 y1) = (NUMERAL 0)) /\ ((Nat.modulo x0 y1) = x0))) y0).
Definition term82 (x0 : nat) := and ((fun y0 : nat => forall y1 : nat, (~ (y1 = (NUMERAL 0))) \/ (((Nat.div y0 y1) = (NUMERAL 0)) /\ ((Nat.modulo y0 y1) = y0))) x0).
Definition term47 := exists y0 : nat, ~ ((Nat.modulo y0 (NUMERAL 0)) = y0).
Definition term37 := fun y0 : nat => (Nat.modulo y0 (NUMERAL 0)) = y0.
Definition term21 (x0 : nat) (x1 : nat) := @COND Prop True (((Nat.div x1 x0) = (NUMERAL 0)) /\ ((Nat.modulo x1 x0) = x1)).
Definition term116 (x0 : nat) := imp (~ (~ (x0 = (NUMERAL 0)))).
Definition term48 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term76 := forall y0 : nat, (forall y1 : nat, (~ (y1 = (NUMERAL 0))) \/ (((Nat.div y0 y1) = (NUMERAL 0)) /\ ((Nat.modulo y0 y1) = y0))) /\ (forall y1 : nat, (y1 = (NUMERAL 0)) \/ ((y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1))).
Definition term58 (x0 : nat) (x1 : nat) := and ((fun y0 : nat => (~ (y0 = (NUMERAL 0))) \/ (((Nat.div x0 y0) = (NUMERAL 0)) /\ ((Nat.modulo x0 y0) = x0))) x1).
Definition term61 (x0 : nat) (x1 : nat) := (x1 = (NUMERAL 0)) \/ ((x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1)).
Definition term5 := ((~ (forall y0 : nat, (Nat.modulo y0 (NUMERAL 0)) = y0)) -> (forall y0 : nat, forall y1 : nat, @COND Prop (y1 = (NUMERAL 0)) (((Nat.div y0 y1) = (NUMERAL 0)) /\ ((Nat.modulo y0 y1) = y0)) ((y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1))) -> False) -> (~ (forall y0 : nat, (Nat.modulo y0 (NUMERAL 0)) = y0)) -> (forall y0 : nat, forall y1 : nat, @COND Prop (y1 = (NUMERAL 0)) (((Nat.div y0 y1) = (NUMERAL 0)) /\ ((Nat.modulo y0 y1) = y0)) ((y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1))) -> False.
Definition term3 := ~ (forall y0 : nat, (Nat.modulo y0 (NUMERAL 0)) = y0).
Definition term115 (x0 : nat) := ~ (~ (x0 = (NUMERAL 0))).
Definition term24 (x0 : nat) (x1 : nat) := (((x0 = (NUMERAL 0)) = False) -> (@COND Prop (x0 = (NUMERAL 0)) (((Nat.div x1 x0) = (NUMERAL 0)) /\ ((Nat.modulo x1 x0) = x1)) ((x1 = (Nat.add (Nat.mul (Nat.div x1 x0) x0) (Nat.modulo x1 x0))) /\ (Peano.lt (Nat.modulo x1 x0) x0))) = ((x1 = (Nat.add (Nat.mul (Nat.div x1 x0) x0) (Nat.modulo x1 x0))) /\ (Peano.lt (Nat.modulo x1 x0) x0))) /\ (((x0 = (NUMERAL 0)) = True) -> (@COND Prop (x0 = (NUMERAL 0)) (((Nat.div x1 x0) = (NUMERAL 0)) /\ ((Nat.modulo x1 x0) = x1)) ((x1 = (Nat.add (Nat.mul (Nat.div x1 x0) x0) (Nat.modulo x1 x0))) /\ (Peano.lt (Nat.modulo x1 x0) x0))) = (((Nat.div x1 x0) = (NUMERAL 0)) /\ ((Nat.modulo x1 x0) = x1))).
Definition term7 := (((~ (forall y0 : nat, (Nat.modulo y0 (NUMERAL 0)) = y0)) -> (forall y0 : nat, forall y1 : nat, @COND Prop (y1 = (NUMERAL 0)) (((Nat.div y0 y1) = (NUMERAL 0)) /\ ((Nat.modulo y0 y1) = y0)) ((y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1))) -> False) -> (~ (forall y0 : nat, (Nat.modulo y0 (NUMERAL 0)) = y0)) -> (forall y0 : nat, forall y1 : nat, @COND Prop (y1 = (NUMERAL 0)) (((Nat.div y0 y1) = (NUMERAL 0)) /\ ((Nat.modulo y0 y1) = y0)) ((y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1))) -> False) -> ((~ (forall y0 : nat, (Nat.modulo y0 (NUMERAL 0)) = y0)) -> (forall y0 : nat, forall y1 : nat, @COND Prop (y1 = (NUMERAL 0)) (((Nat.div y0 y1) = (NUMERAL 0)) /\ ((Nat.modulo y0 y1) = y0)) ((y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1))) -> False) -> (~ (forall y0 : nat, (Nat.modulo y0 (NUMERAL 0)) = y0)) -> (forall y0 : nat, forall y1 : nat, @COND Prop (y1 = (NUMERAL 0)) (((Nat.div y0 y1) = (NUMERAL 0)) /\ ((Nat.modulo y0 y1) = y0)) ((y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1))) -> False.
Definition term94 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (y2 = (NUMERAL 0)) \/ ((y1 = (Nat.add (Nat.mul (Nat.div y1 y2) y2) (Nat.modulo y1 y2))) /\ (Peano.lt (Nat.modulo y1 y2) y2))) y0.
Definition term89 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (y2 = (NUMERAL 0))) \/ (((Nat.div y1 y2) = (NUMERAL 0)) /\ ((Nat.modulo y1 y2) = y1))) y0.
Definition term40 (x0 : nat -> Prop) := exists y0 : nat, ~ (x0 y0).
Definition term19 (x0 : nat) (x1 : nat) := @COND Prop False (((Nat.div x0 x1) = (NUMERAL 0)) /\ ((Nat.modulo x0 x1) = x0)) ((x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1)).
Definition term26 (x0 : nat) (x1 : nat) := ((((x1 = (NUMERAL 0)) = False) -> (@COND Prop (x1 = (NUMERAL 0)) (((Nat.div x0 x1) = (NUMERAL 0)) /\ ((Nat.modulo x0 x1) = x0)) ((x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1))) = ((x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1))) /\ (((x1 = (NUMERAL 0)) = True) -> (@COND Prop (x1 = (NUMERAL 0)) (((Nat.div x0 x1) = (NUMERAL 0)) /\ ((Nat.modulo x0 x1) = x0)) ((x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1))) = (((Nat.div x0 x1) = (NUMERAL 0)) /\ ((Nat.modulo x0 x1) = x0)))) -> (@COND Prop (x1 = (NUMERAL 0)) (((Nat.div x0 x1) = (NUMERAL 0)) /\ ((Nat.modulo x0 x1) = x0)) ((x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1))) = (((~ (x1 = (NUMERAL 0))) \/ (((Nat.div x0 x1) = (NUMERAL 0)) /\ ((Nat.modulo x0 x1) = x0))) /\ ((x1 = (NUMERAL 0)) \/ ((x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1)))).
Definition term97 (x0 : nat) (x1 : nat) := ((~ (x0 = (NUMERAL 0))) \/ ((Nat.div x1 x0) = (NUMERAL 0))) /\ ((~ (x0 = (NUMERAL 0))) \/ ((Nat.modulo x1 x0) = x1)).
Definition term101 := fun y0 : nat => forall y1 : nat, ((~ (y1 = (NUMERAL 0))) \/ ((Nat.div y0 y1) = (NUMERAL 0))) /\ ((~ (y1 = (NUMERAL 0))) \/ ((Nat.modulo y0 y1) = y0)).
Definition term80 := fun y0 : nat => forall y1 : nat, (y1 = (NUMERAL 0)) \/ ((y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term79 := fun y0 : nat => forall y1 : nat, (~ (y1 = (NUMERAL 0))) \/ (((Nat.div y0 y1) = (NUMERAL 0)) /\ ((Nat.modulo y0 y1) = y0)).
Definition term33 := fun y0 : nat => forall y1 : nat, ((~ (y1 = (NUMERAL 0))) \/ (((Nat.div y0 y1) = (NUMERAL 0)) /\ ((Nat.modulo y0 y1) = y0))) /\ ((y1 = (NUMERAL 0)) \/ ((y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1))).
Definition term118 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) -> (Nat.modulo x1 x0) = x1.
Definition term31 (x0 : nat) := forall y0 : nat, ((~ (y0 = (NUMERAL 0))) \/ (((Nat.div x0 y0) = (NUMERAL 0)) /\ ((Nat.modulo x0 y0) = x0))) /\ ((y0 = (NUMERAL 0)) \/ ((x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0))).
Definition term11 := imp (~ (forall y0 : nat, (Nat.modulo y0 (NUMERAL 0)) = y0)).
Definition term28 (x0 : nat) := fun y0 : nat => @COND Prop (y0 = (NUMERAL 0)) (((Nat.div x0 y0) = (NUMERAL 0)) /\ ((Nat.modulo x0 y0) = x0)) ((x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0)).
