Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term16 (x0 : nat) := ((fun y0 : nat => (Peano.lt (NUMERAL 0) y0) = (~ (y0 = (NUMERAL 0)))) x0) -> (fun y0 : nat => (Peano.lt (NUMERAL 0) y0) = (~ (y0 = (NUMERAL 0)))) (S x0).
Definition term7 := and ((Peano.lt (NUMERAL 0) (NUMERAL 0)) = (~ ((NUMERAL 0) = (NUMERAL 0)))).
Definition term14 (x0 : nat) := Peano.lt (NUMERAL 0) (S x0).
Definition term56 := True \/ (~ True).
Definition term35 (a0 : Type') (x0 : a0) := forall y0 : a0, (x0 = y0) = (y0 = x0).
Definition term45 (x0 : nat) := ((NUMERAL 0) = x0) \/ (Peano.lt (NUMERAL 0) x0).
Definition term59 := False \/ (~ False).
Definition term23 := ((Peano.lt (NUMERAL 0) (NUMERAL 0)) = (~ ((NUMERAL 0) = (NUMERAL 0)))) /\ (forall y0 : nat, ((Peano.lt (NUMERAL 0) y0) = (~ (y0 = (NUMERAL 0)))) -> (Peano.lt (NUMERAL 0) (S y0)) = (~ ((S y0) = (NUMERAL 0)))).
Definition term26 := fun y0 : nat => (fun y1 : nat => (Peano.lt (NUMERAL 0) y1) = (~ (y1 = (NUMERAL 0)))) y0.
Definition term8 (x0 : nat) := (fun y0 : nat => (Peano.lt (NUMERAL 0) y0) = (~ (y0 = (NUMERAL 0)))) x0.
Definition term27 := forall y0 : nat, (fun y1 : nat => (Peano.lt (NUMERAL 0) y1) = (~ (y1 = (NUMERAL 0)))) y0.
Definition term50 (x0 : nat) := @eq Prop ((x0 = (NUMERAL 0)) \/ (~ (x0 = (NUMERAL 0)))).
Definition term22 := ((fun y0 : nat => (Peano.lt (NUMERAL 0) y0) = (~ (y0 = (NUMERAL 0)))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Peano.lt (NUMERAL 0) y1) = (~ (y1 = (NUMERAL 0)))) y0) -> (fun y1 : nat => (Peano.lt (NUMERAL 0) y1) = (~ (y1 = (NUMERAL 0)))) (S y0)).
Definition term1 := (((fun y0 : nat => (Peano.lt (NUMERAL 0) y0) = (~ (y0 = (NUMERAL 0)))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Peano.lt (NUMERAL 0) y1) = (~ (y1 = (NUMERAL 0)))) y0) -> (fun y1 : nat => (Peano.lt (NUMERAL 0) y1) = (~ (y1 = (NUMERAL 0)))) (S y0))) -> forall y0 : nat, (fun y1 : nat => (Peano.lt (NUMERAL 0) y1) = (~ (y1 = (NUMERAL 0)))) y0.
Definition term30 := forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False.
Definition term0 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term34 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a0, (y0 = y1) = (y1 = y0)) x0.
Definition term24 := imp (((fun y0 : nat => (Peano.lt (NUMERAL 0) y0) = (~ (y0 = (NUMERAL 0)))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Peano.lt (NUMERAL 0) y1) = (~ (y1 = (NUMERAL 0)))) y0) -> (fun y1 : nat => (Peano.lt (NUMERAL 0) y1) = (~ (y1 = (NUMERAL 0)))) (S y0))).
Definition term5 := ~ ((NUMERAL 0) = (NUMERAL 0)).
Definition term20 := forall y0 : nat, ((fun y1 : nat => (Peano.lt (NUMERAL 0) y1) = (~ (y1 = (NUMERAL 0)))) y0) -> (fun y1 : nat => (Peano.lt (NUMERAL 0) y1) = (~ (y1 = (NUMERAL 0)))) (S y0).
Definition term10 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term42 (x0 : nat) (x1 : nat) := (x0 = x1) \/ (Peano.lt x0 x1).
Definition term6 := and ((fun y0 : nat => (Peano.lt (NUMERAL 0) y0) = (~ (y0 = (NUMERAL 0)))) (NUMERAL 0)).
Definition term12 (x0 : nat) := imp ((Peano.lt (NUMERAL 0) x0) = (~ (x0 = (NUMERAL 0)))).
Definition term3 := (fun y0 : nat => (Peano.lt (NUMERAL 0) y0) = (~ (y0 = (NUMERAL 0)))) (NUMERAL 0).
Definition term31 (x0 : nat) := (fun y0 : nat => (Peano.lt y0 (NUMERAL 0)) = False) x0.
Definition term49 (x0 : nat) := @eq Prop (Peano.lt (NUMERAL 0) (S x0)).
Definition term4 := Peano.lt (NUMERAL 0) (NUMERAL 0).
Definition term18 := fun y0 : nat => ((fun y1 : nat => (Peano.lt (NUMERAL 0) y1) = (~ (y1 = (NUMERAL 0)))) y0) -> (fun y1 : nat => (Peano.lt (NUMERAL 0) y1) = (~ (y1 = (NUMERAL 0)))) (S y0).
Definition term33 := @eq Prop (Peano.lt (NUMERAL 0) (NUMERAL 0)).
Definition term46 (x0 : nat) := or ((NUMERAL 0) = x0).
Definition term47 (x0 : nat) := or (x0 = (NUMERAL 0)).
Definition term37 := forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)).
Definition term2 := fun y0 : nat => (Peano.lt (NUMERAL 0) y0) = (~ (y0 = (NUMERAL 0))).
Definition term48 (x0 : nat) := (x0 = (NUMERAL 0)) \/ (~ (x0 = (NUMERAL 0))).
Definition term53 := fun y0 : Prop => y0 \/ (~ y0).
Definition term41 (x0 : nat) (x1 : nat) := Peano.lt x0 (S x1).
Definition term36 (a0 : Type') (x0 : a0) (x1 : a0) := (fun y0 : a0 => (x0 = y0) = (y0 = x0)) x1.
Definition term39 (x0 : nat) := forall y0 : nat, (Peano.lt x0 (S y0)) = ((x0 = y0) \/ (Peano.lt x0 y0)).
Definition term15 (x0 : nat) := ~ ((S x0) = (NUMERAL 0)).
Definition term55 := (fun y0 : Prop => y0 \/ (~ y0)) True.
Definition term19 := fun y0 : nat => ((Peano.lt (NUMERAL 0) y0) = (~ (y0 = (NUMERAL 0)))) -> (Peano.lt (NUMERAL 0) (S y0)) = (~ ((S y0) = (NUMERAL 0))).
Definition term57 (x0 : nat) := @eq Prop ((fun y0 : Prop => y0 \/ (~ y0)) (x0 = (NUMERAL 0))).
Definition term40 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt x0 (S y0)) = ((x0 = y0) \/ (Peano.lt x0 y0))) x1.
Definition term13 (x0 : nat) := (fun y0 : nat => (Peano.lt (NUMERAL 0) y0) = (~ (y0 = (NUMERAL 0)))) (S x0).
Definition term32 (x0 : nat) := Peano.lt x0 (NUMERAL 0).
Definition term28 := forall y0 : nat, (Peano.lt (NUMERAL 0) y0) = (~ (y0 = (NUMERAL 0))).
Definition term38 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1))) x0.
Definition term43 (x0 : nat) := (fun y0 : nat => ~ ((S y0) = (NUMERAL 0))) x0.
Definition term58 := (fun y0 : Prop => y0 \/ (~ y0)) False.
Definition term44 (x0 : nat) := (~ ((S x0) = (NUMERAL 0))) -> ((S x0) = (NUMERAL 0)) = False.
Definition term51 (x0 : nat) := (fun y0 : Prop => (y0 = True) \/ (y0 = False)) (x0 = (NUMERAL 0)).
Definition term17 (x0 : nat) := ((Peano.lt (NUMERAL 0) x0) = (~ (x0 = (NUMERAL 0)))) -> (Peano.lt (NUMERAL 0) (S x0)) = (~ ((S x0) = (NUMERAL 0))).
Definition term11 (x0 : nat) := imp ((fun y0 : nat => (Peano.lt (NUMERAL 0) y0) = (~ (y0 = (NUMERAL 0)))) x0).
Definition term21 := forall y0 : nat, ((Peano.lt (NUMERAL 0) y0) = (~ (y0 = (NUMERAL 0)))) -> (Peano.lt (NUMERAL 0) (S y0)) = (~ ((S y0) = (NUMERAL 0))).
Definition term29 := (((Peano.lt (NUMERAL 0) (NUMERAL 0)) = (~ ((NUMERAL 0) = (NUMERAL 0)))) /\ (forall y0 : nat, ((Peano.lt (NUMERAL 0) y0) = (~ (y0 = (NUMERAL 0)))) -> (Peano.lt (NUMERAL 0) (S y0)) = (~ ((S y0) = (NUMERAL 0))))) -> forall y0 : nat, (Peano.lt (NUMERAL 0) y0) = (~ (y0 = (NUMERAL 0))).
Definition term9 (x0 : nat) := Peano.lt (NUMERAL 0) x0.
Definition term54 (x0 : nat) := (fun y0 : Prop => y0 \/ (~ y0)) (x0 = (NUMERAL 0)).
Definition term52 (x0 : nat) := ((x0 = (NUMERAL 0)) = True) \/ ((x0 = (NUMERAL 0)) = False).
Definition term25 := imp (((Peano.lt (NUMERAL 0) (NUMERAL 0)) = (~ ((NUMERAL 0) = (NUMERAL 0)))) /\ (forall y0 : nat, ((Peano.lt (NUMERAL 0) y0) = (~ (y0 = (NUMERAL 0)))) -> (Peano.lt (NUMERAL 0) (S y0)) = (~ ((S y0) = (NUMERAL 0))))).
