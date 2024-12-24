Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term59 (x0 : nat) := fun y0 : Prop => (y0 /\ (y0 \/ (x0 = (NUMERAL 0)))) = y0.
Definition term17 (x0 : nat) (x1 : nat) := (((Nat.pow x0 x1) = (NUMERAL (BIT1 0))) = ((x0 = (NUMERAL (BIT1 0))) \/ (x1 = (NUMERAL 0)))) -> ((Nat.pow x0 (S x1)) = (NUMERAL (BIT1 0))) = ((x0 = (NUMERAL (BIT1 0))) \/ ((S x1) = (NUMERAL 0))).
Definition term26 (x0 : nat) := fun y0 : nat => (fun y1 : nat => ((Nat.pow x0 y1) = (NUMERAL (BIT1 0))) = ((x0 = (NUMERAL (BIT1 0))) \/ (y1 = (NUMERAL 0)))) y0.
Definition term62 (x0 : nat) := True /\ (True \/ (x0 = (NUMERAL 0))).
Definition term6 (x0 : nat) := (x0 = (NUMERAL (BIT1 0))) \/ ((NUMERAL 0) = (NUMERAL 0)).
Definition term46 (x0 : nat) := forall y0 : nat, (Nat.pow x0 (S y0)) = (Nat.mul x0 (Nat.pow x0 y0)).
Definition term27 (x0 : nat) := forall y0 : nat, (fun y1 : nat => ((Nat.pow x0 y1) = (NUMERAL (BIT1 0))) = ((x0 = (NUMERAL (BIT1 0))) \/ (y1 = (NUMERAL 0)))) y0.
Definition term57 (x0 : nat) := (fun y0 : Prop => (y0 = True) \/ (y0 = False)) (x0 = (NUMERAL (BIT1 0))).
Definition term22 (x0 : nat) := ((fun y0 : nat => ((Nat.pow x0 y0) = (NUMERAL (BIT1 0))) = ((x0 = (NUMERAL (BIT1 0))) \/ (y0 = (NUMERAL 0)))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Nat.pow x0 y1) = (NUMERAL (BIT1 0))) = ((x0 = (NUMERAL (BIT1 0))) \/ (y1 = (NUMERAL 0)))) y0) -> (fun y1 : nat => ((Nat.pow x0 y1) = (NUMERAL (BIT1 0))) = ((x0 = (NUMERAL (BIT1 0))) \/ (y1 = (NUMERAL 0)))) (S y0)).
Definition term13 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Nat.pow x0 y0) = (NUMERAL (BIT1 0))) = ((x0 = (NUMERAL (BIT1 0))) \/ (y0 = (NUMERAL 0)))) (S x1).
Definition term53 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL (BIT1 0))) /\ ((x0 = (NUMERAL (BIT1 0))) \/ (x1 = (NUMERAL 0))).
Definition term14 (x0 : nat) (x1 : nat) := Nat.pow x0 (S x1).
Definition term12 (x0 : nat) (x1 : nat) := imp (((Nat.pow x0 x1) = (NUMERAL (BIT1 0))) = ((x0 = (NUMERAL (BIT1 0))) \/ (x1 = (NUMERAL 0)))).
Definition term16 (x0 : nat) (x1 : nat) := ((fun y0 : nat => ((Nat.pow x0 y0) = (NUMERAL (BIT1 0))) = ((x0 = (NUMERAL (BIT1 0))) \/ (y0 = (NUMERAL 0)))) x1) -> (fun y0 : nat => ((Nat.pow x0 y0) = (NUMERAL (BIT1 0))) = ((x0 = (NUMERAL (BIT1 0))) \/ (y0 = (NUMERAL 0)))) (S x1).
Definition term1 (x0 : nat) := (((fun y0 : nat => ((Nat.pow x0 y0) = (NUMERAL (BIT1 0))) = ((x0 = (NUMERAL (BIT1 0))) \/ (y0 = (NUMERAL 0)))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Nat.pow x0 y1) = (NUMERAL (BIT1 0))) = ((x0 = (NUMERAL (BIT1 0))) \/ (y1 = (NUMERAL 0)))) y0) -> (fun y1 : nat => ((Nat.pow x0 y1) = (NUMERAL (BIT1 0))) = ((x0 = (NUMERAL (BIT1 0))) \/ (y1 = (NUMERAL 0)))) (S y0))) -> forall y0 : nat, (fun y1 : nat => ((Nat.pow x0 y1) = (NUMERAL (BIT1 0))) = ((x0 = (NUMERAL (BIT1 0))) \/ (y1 = (NUMERAL 0)))) y0.
Definition term47 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.pow x0 (S y0)) = (Nat.mul x0 (Nat.pow x0 y0))) x1.
Definition term65 (x0 : nat) := (fun y0 : Prop => (y0 /\ (y0 \/ (x0 = (NUMERAL 0)))) = y0) False.
Definition term4 (x0 : nat) := Nat.pow x0 (NUMERAL 0).
Definition term0 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term42 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Nat.mul x0 y0) = (NUMERAL (BIT1 0))) = ((x0 = (NUMERAL (BIT1 0))) /\ (y0 = (NUMERAL (BIT1 0))))) x1.
Definition term24 (x0 : nat) := imp (((fun y0 : nat => ((Nat.pow x0 y0) = (NUMERAL (BIT1 0))) = ((x0 = (NUMERAL (BIT1 0))) \/ (y0 = (NUMERAL 0)))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Nat.pow x0 y1) = (NUMERAL (BIT1 0))) = ((x0 = (NUMERAL (BIT1 0))) \/ (y1 = (NUMERAL 0)))) y0) -> (fun y1 : nat => ((Nat.pow x0 y1) = (NUMERAL (BIT1 0))) = ((x0 = (NUMERAL (BIT1 0))) \/ (y1 = (NUMERAL 0)))) (S y0))).
Definition term66 (x0 : nat) := False /\ (False \/ (x0 = (NUMERAL 0))).
Definition term54 (x0 : nat) (x1 : nat) := @eq Prop ((Nat.pow x0 (S x1)) = (NUMERAL (BIT1 0))).
Definition term41 (x0 : nat) := forall y0 : nat, ((Nat.mul x0 y0) = (NUMERAL (BIT1 0))) = ((x0 = (NUMERAL (BIT1 0))) /\ (y0 = (NUMERAL (BIT1 0)))).
Definition term28 (x0 : nat) := forall y0 : nat, ((Nat.pow x0 y0) = (NUMERAL (BIT1 0))) = ((x0 = (NUMERAL (BIT1 0))) \/ (y0 = (NUMERAL 0))).
Definition term43 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL (BIT1 0))) /\ (x1 = (NUMERAL (BIT1 0))).
Definition term20 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => ((Nat.pow x0 y1) = (NUMERAL (BIT1 0))) = ((x0 = (NUMERAL (BIT1 0))) \/ (y1 = (NUMERAL 0)))) y0) -> (fun y1 : nat => ((Nat.pow x0 y1) = (NUMERAL (BIT1 0))) = ((x0 = (NUMERAL (BIT1 0))) \/ (y1 = (NUMERAL 0)))) (S y0).
Definition term10 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL (BIT1 0))) \/ (x1 = (NUMERAL 0)).
Definition term51 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL (BIT1 0))) /\ ((Nat.pow x0 x1) = (NUMERAL (BIT1 0))).
Definition term56 (x0 : nat) := (x0 = (NUMERAL (BIT1 0))) \/ False.
Definition term7 (x0 : nat) := and ((fun y0 : nat => ((Nat.pow x0 y0) = (NUMERAL (BIT1 0))) = ((x0 = (NUMERAL (BIT1 0))) \/ (y0 = (NUMERAL 0)))) (NUMERAL 0)).
Definition term35 (x0 : nat) := or (x0 = (NUMERAL (BIT1 0))).
Definition term31 (x0 : nat) := (fun y0 : nat => (Nat.pow y0 (NUMERAL 0)) = (NUMERAL (BIT1 0))) x0.
Definition term18 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => ((Nat.pow x0 y1) = (NUMERAL (BIT1 0))) = ((x0 = (NUMERAL (BIT1 0))) \/ (y1 = (NUMERAL 0)))) y0) -> (fun y1 : nat => ((Nat.pow x0 y1) = (NUMERAL (BIT1 0))) = ((x0 = (NUMERAL (BIT1 0))) \/ (y1 = (NUMERAL 0)))) (S y0).
Definition term19 (x0 : nat) := fun y0 : nat => (((Nat.pow x0 y0) = (NUMERAL (BIT1 0))) = ((x0 = (NUMERAL (BIT1 0))) \/ (y0 = (NUMERAL 0)))) -> ((Nat.pow x0 (S y0)) = (NUMERAL (BIT1 0))) = ((x0 = (NUMERAL (BIT1 0))) \/ ((S y0) = (NUMERAL 0))).
Definition term55 (x0 : nat) (x1 : nat) := @eq Prop ((x0 = (NUMERAL (BIT1 0))) /\ ((x0 = (NUMERAL (BIT1 0))) \/ (x1 = (NUMERAL 0)))).
Definition term64 (x0 : nat) (x1 : nat) := @eq Prop (((x1 = (NUMERAL (BIT1 0))) /\ ((x1 = (NUMERAL (BIT1 0))) \/ (x0 = (NUMERAL 0)))) = (x1 = (NUMERAL (BIT1 0)))).
Definition term70 := forall y0 : nat, forall y1 : nat, ((Nat.pow y0 y1) = (NUMERAL (BIT1 0))) = ((y0 = (NUMERAL (BIT1 0))) \/ (y1 = (NUMERAL 0))).
Definition term44 := forall y0 : nat, forall y1 : nat, (Nat.pow y0 (S y1)) = (Nat.mul y0 (Nat.pow y0 y1)).
Definition term52 (x0 : nat) := and (x0 = (NUMERAL (BIT1 0))).
Definition term49 (x0 : nat) (x1 : nat) := @eq nat (Nat.pow x0 (S x1)).
Definition term60 (x0 : nat) (x1 : nat) := (fun y0 : Prop => (y0 /\ (y0 \/ (x0 = (NUMERAL 0)))) = y0) (x1 = (NUMERAL (BIT1 0))).
Definition term29 (x0 : nat) := ((((Nat.pow x0 (NUMERAL 0)) = (NUMERAL (BIT1 0))) = ((x0 = (NUMERAL (BIT1 0))) \/ ((NUMERAL 0) = (NUMERAL 0)))) /\ (forall y0 : nat, (((Nat.pow x0 y0) = (NUMERAL (BIT1 0))) = ((x0 = (NUMERAL (BIT1 0))) \/ (y0 = (NUMERAL 0)))) -> ((Nat.pow x0 (S y0)) = (NUMERAL (BIT1 0))) = ((x0 = (NUMERAL (BIT1 0))) \/ ((S y0) = (NUMERAL 0))))) -> forall y0 : nat, ((Nat.pow x0 y0) = (NUMERAL (BIT1 0))) = ((x0 = (NUMERAL (BIT1 0))) \/ (y0 = (NUMERAL 0))).
Definition term48 (x0 : nat) (x1 : nat) := Nat.mul x0 (Nat.pow x0 x1).
Definition term11 (x0 : nat) (x1 : nat) := imp ((fun y0 : nat => ((Nat.pow x0 y0) = (NUMERAL (BIT1 0))) = ((x0 = (NUMERAL (BIT1 0))) \/ (y0 = (NUMERAL 0)))) x1).
Definition term38 (x0 : nat) := ~ ((S x0) = (NUMERAL 0)).
Definition term68 (x0 : nat) := ~ (False /\ (False \/ (x0 = (NUMERAL 0)))).
Definition term15 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL (BIT1 0))) \/ ((S x1) = (NUMERAL 0)).
Definition term9 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Nat.pow x0 y0) = (NUMERAL (BIT1 0))) = ((x0 = (NUMERAL (BIT1 0))) \/ (y0 = (NUMERAL 0)))) x1.
Definition term33 := @eq nat (NUMERAL (BIT1 0)).
Definition term69 (x0 : nat) := False \/ (x0 = (NUMERAL 0)).
Definition term45 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.pow y0 (S y1)) = (Nat.mul y0 (Nat.pow y0 y1))) x0.
Definition term40 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) = ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) x0.
Definition term37 (x0 : nat) := (fun y0 : nat => ~ ((S y0) = (NUMERAL 0))) x0.
Definition term30 := forall y0 : nat, (Nat.pow y0 (NUMERAL 0)) = (NUMERAL (BIT1 0)).
Definition term67 (x0 : nat) := True \/ (x0 = (NUMERAL 0)).
Definition term36 (x0 : nat) := (x0 = (NUMERAL (BIT1 0))) \/ True.
Definition term34 (x0 : nat) := @eq Prop ((Nat.pow x0 (NUMERAL 0)) = (NUMERAL (BIT1 0))).
Definition term39 (x0 : nat) := (~ ((S x0) = (NUMERAL 0))) -> ((S x0) = (NUMERAL 0)) = False.
Definition term63 (x0 : nat) (x1 : nat) := @eq Prop ((fun y0 : Prop => (y0 /\ (y0 \/ (x0 = (NUMERAL 0)))) = y0) (x1 = (NUMERAL (BIT1 0)))).
Definition term25 (x0 : nat) := imp ((((Nat.pow x0 (NUMERAL 0)) = (NUMERAL (BIT1 0))) = ((x0 = (NUMERAL (BIT1 0))) \/ ((NUMERAL 0) = (NUMERAL 0)))) /\ (forall y0 : nat, (((Nat.pow x0 y0) = (NUMERAL (BIT1 0))) = ((x0 = (NUMERAL (BIT1 0))) \/ (y0 = (NUMERAL 0)))) -> ((Nat.pow x0 (S y0)) = (NUMERAL (BIT1 0))) = ((x0 = (NUMERAL (BIT1 0))) \/ ((S y0) = (NUMERAL 0))))).
Definition term23 (x0 : nat) := (((Nat.pow x0 (NUMERAL 0)) = (NUMERAL (BIT1 0))) = ((x0 = (NUMERAL (BIT1 0))) \/ ((NUMERAL 0) = (NUMERAL 0)))) /\ (forall y0 : nat, (((Nat.pow x0 y0) = (NUMERAL (BIT1 0))) = ((x0 = (NUMERAL (BIT1 0))) \/ (y0 = (NUMERAL 0)))) -> ((Nat.pow x0 (S y0)) = (NUMERAL (BIT1 0))) = ((x0 = (NUMERAL (BIT1 0))) \/ ((S y0) = (NUMERAL 0)))).
Definition term21 (x0 : nat) := forall y0 : nat, (((Nat.pow x0 y0) = (NUMERAL (BIT1 0))) = ((x0 = (NUMERAL (BIT1 0))) \/ (y0 = (NUMERAL 0)))) -> ((Nat.pow x0 (S y0)) = (NUMERAL (BIT1 0))) = ((x0 = (NUMERAL (BIT1 0))) \/ ((S y0) = (NUMERAL 0))).
Definition term3 (x0 : nat) := (fun y0 : nat => ((Nat.pow x0 y0) = (NUMERAL (BIT1 0))) = ((x0 = (NUMERAL (BIT1 0))) \/ (y0 = (NUMERAL 0)))) (NUMERAL 0).
Definition term32 (x0 : nat) := @eq nat (Nat.pow x0 (NUMERAL 0)).
Definition term61 (x0 : nat) := (fun y0 : Prop => (y0 /\ (y0 \/ (x0 = (NUMERAL 0)))) = y0) True.
Definition term2 (x0 : nat) := fun y0 : nat => ((Nat.pow x0 y0) = (NUMERAL (BIT1 0))) = ((x0 = (NUMERAL (BIT1 0))) \/ (y0 = (NUMERAL 0))).
Definition term58 (x0 : nat) := ((x0 = (NUMERAL (BIT1 0))) = True) \/ ((x0 = (NUMERAL (BIT1 0))) = False).
Definition term5 := NUMERAL (BIT1 0).
Definition term8 (x0 : nat) := and (((Nat.pow x0 (NUMERAL 0)) = (NUMERAL (BIT1 0))) = ((x0 = (NUMERAL (BIT1 0))) \/ ((NUMERAL 0) = (NUMERAL 0)))).
Definition term50 (x0 : nat) (x1 : nat) := @eq nat (Nat.mul x0 (Nat.pow x0 x1)).
