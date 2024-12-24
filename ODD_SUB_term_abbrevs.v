Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term77 := @eq Prop (~ False).
Definition term76 (x0 : nat) := @eq Prop (Coq.Arith.PeanoNat.Nat.Even x0).
Definition term51 (x0 : nat) (x1 : nat) := True /\ (~ ((~ (Coq.Arith.PeanoNat.Nat.Even x0)) = (~ (Coq.Arith.PeanoNat.Nat.Even x1)))).
Definition term29 (x0 : nat) (x1 : nat) := @eq Prop (Coq.Arith.PeanoNat.Nat.Odd (Nat.sub x0 x1)).
Definition term74 (x0 : Prop) := ~ (~ x0).
Definition term56 (x0 : nat) (x1 : nat) := False /\ (~ ((~ (Coq.Arith.PeanoNat.Nat.Even x0)) = (~ (Coq.Arith.PeanoNat.Nat.Even x1)))).
Definition term36 (x0 : nat) (x1 : nat) := (Peano.lt x1 x0) /\ (~ ((~ (Coq.Arith.PeanoNat.Nat.Even x0)) = (~ (Coq.Arith.PeanoNat.Nat.Even x1)))).
Definition term37 (x0 : nat) := fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Odd (Nat.sub x0 y0)) = ((Peano.lt y0 x0) /\ (~ ((Coq.Arith.PeanoNat.Nat.Odd x0) = (Coq.Arith.PeanoNat.Nat.Odd y0)))).
Definition term50 (x0 : nat) (x1 : nat) := True /\ (~ ((Coq.Arith.PeanoNat.Nat.Even x0) = (Coq.Arith.PeanoNat.Nat.Even x1))).
Definition term0 (x0 : nat) := ~ (Coq.Arith.PeanoNat.Nat.Even x0).
Definition term75 (x0 : nat) := @eq Prop (~ (False = (Coq.Arith.PeanoNat.Nat.Even x0))).
Definition term27 (x0 : nat) (x1 : nat) := ~ ((Coq.Arith.PeanoNat.Nat.Even x0) = (Coq.Arith.PeanoNat.Nat.Even x1)).
Definition term39 (x0 : nat) := forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Odd (Nat.sub x0 y0)) = ((Peano.lt y0 x0) /\ (~ ((Coq.Arith.PeanoNat.Nat.Odd x0) = (Coq.Arith.PeanoNat.Nat.Odd y0)))).
Definition term73 (x0 : nat) := ~ (~ (Coq.Arith.PeanoNat.Nat.Even x0)).
Definition term11 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => ((~ (x0 /\ y0)) = ((~ x0) \/ (~ y0))) /\ ((~ (x0 \/ y0)) = ((~ x0) /\ (~ y0)))) x1.
Definition term45 (x0 : nat) (x1 : nat) := (fun y0 : Prop => (y0 = True) \/ (y0 = False)) (Peano.lt x0 x1).
Definition term48 (x0 : nat) (x1 : nat) := (fun y0 : Prop => (y0 /\ (~ ((Coq.Arith.PeanoNat.Nat.Even x1) = (Coq.Arith.PeanoNat.Nat.Even x0)))) = (y0 /\ (~ ((~ (Coq.Arith.PeanoNat.Nat.Even x1)) = (~ (Coq.Arith.PeanoNat.Nat.Even x0)))))) (Peano.lt x0 x1).
Definition term12 (x0 : Prop) (x1 : Prop) := ((~ (x0 /\ x1)) = ((~ x0) \/ (~ x1))) /\ ((~ (x0 \/ x1)) = ((~ x0) /\ (~ x1))).
Definition term61 (x0 : nat) := fun y0 : Prop => (~ (y0 = (Coq.Arith.PeanoNat.Nat.Even x0))) = (~ ((~ y0) = (~ (Coq.Arith.PeanoNat.Nat.Even x0)))).
Definition term23 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term9 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((~ (y0 /\ y1)) = ((~ y0) \/ (~ y1))) /\ ((~ (y0 \/ y1)) = ((~ y0) /\ (~ y1)))) x0.
Definition term34 (x0 : nat) (x1 : nat) := ~ ((~ (Coq.Arith.PeanoNat.Nat.Even x0)) = (~ (Coq.Arith.PeanoNat.Nat.Even x1))).
Definition term10 (x0 : Prop) := forall y0 : Prop, ((~ (x0 /\ y0)) = ((~ x0) \/ (~ y0))) /\ ((~ (x0 \/ y0)) = ((~ x0) /\ (~ y0))).
Definition term58 (x0 : nat) (x1 : nat) := @eq Prop (~ ((Coq.Arith.PeanoNat.Nat.Even x0) = (Coq.Arith.PeanoNat.Nat.Even x1))).
Definition term38 (x0 : nat) := fun y0 : nat => ((Peano.lt y0 x0) /\ (~ ((Coq.Arith.PeanoNat.Nat.Even x0) = (Coq.Arith.PeanoNat.Nat.Even y0)))) = ((Peano.lt y0 x0) /\ (~ ((~ (Coq.Arith.PeanoNat.Nat.Even x0)) = (~ (Coq.Arith.PeanoNat.Nat.Even y0))))).
Definition term8 (x0 : nat) (x1 : nat) := ~ (Peano.le x0 x1).
Definition term78 (x0 : nat) (x1 : nat) := @eq Prop (False /\ (~ ((Coq.Arith.PeanoNat.Nat.Even x0) = (Coq.Arith.PeanoNat.Nat.Even x1)))).
Definition term65 (x0 : nat) := ~ ((~ True) = (~ (Coq.Arith.PeanoNat.Nat.Even x0))).
Definition term4 := forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Odd y0) = (~ (Coq.Arith.PeanoNat.Nat.Even y0)).
Definition term66 (x0 : nat) (x1 : nat) := @eq Prop ((fun y0 : Prop => (~ (y0 = (Coq.Arith.PeanoNat.Nat.Even x0))) = (~ ((~ y0) = (~ (Coq.Arith.PeanoNat.Nat.Even x0))))) (Coq.Arith.PeanoNat.Nat.Even x1)).
Definition term14 (x0 : nat) := forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even (Nat.sub x0 y0)) = ((Peano.le x0 y0) \/ ((Coq.Arith.PeanoNat.Nat.Even x0) = (Coq.Arith.PeanoNat.Nat.Even y0))).
Definition term57 (x0 : nat) (x1 : nat) := @eq Prop (True /\ (~ ((Coq.Arith.PeanoNat.Nat.Even x0) = (Coq.Arith.PeanoNat.Nat.Even x1)))).
Definition term71 (x0 : nat) := @eq Prop (~ (True = (Coq.Arith.PeanoNat.Nat.Even x0))).
Definition term3 := forall y0 : nat, (~ (Coq.Arith.PeanoNat.Nat.Even y0)) = (Coq.Arith.PeanoNat.Nat.Odd y0).
Definition term20 (x0 : nat) (x1 : nat) := ~ (Coq.Arith.PeanoNat.Nat.Even (Nat.sub x0 x1)).
Definition term2 := fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Odd y0) = (~ (Coq.Arith.PeanoNat.Nat.Even y0)).
Definition term22 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term44 := forall y0 : nat, forall y1 : nat, ((Peano.lt y1 y0) /\ (~ ((Coq.Arith.PeanoNat.Nat.Even y0) = (Coq.Arith.PeanoNat.Nat.Even y1)))) = ((Peano.lt y1 y0) /\ (~ ((~ (Coq.Arith.PeanoNat.Nat.Even y0)) = (~ (Coq.Arith.PeanoNat.Nat.Even y1))))).
Definition term43 := forall y0 : nat, forall y1 : nat, (Coq.Arith.PeanoNat.Nat.Odd (Nat.sub y0 y1)) = ((Peano.lt y1 y0) /\ (~ ((Coq.Arith.PeanoNat.Nat.Odd y0) = (Coq.Arith.PeanoNat.Nat.Odd y1)))).
Definition term19 (x0 : nat) (x1 : nat) := Coq.Arith.PeanoNat.Nat.Odd (Nat.sub x0 x1).
Definition term67 (x0 : nat) (x1 : nat) := @eq Prop ((~ ((Coq.Arith.PeanoNat.Nat.Even x0) = (Coq.Arith.PeanoNat.Nat.Even x1))) = (~ ((~ (Coq.Arith.PeanoNat.Nat.Even x0)) = (~ (Coq.Arith.PeanoNat.Nat.Even x1))))).
Definition term6 (x0 : nat) := forall y0 : nat, (~ (Peano.le x0 y0)) = (Peano.lt y0 x0).
Definition term21 (x0 : nat) (x1 : nat) := ~ ((Peano.le x0 x1) \/ ((Coq.Arith.PeanoNat.Nat.Even x0) = (Coq.Arith.PeanoNat.Nat.Even x1))).
Definition term63 (x0 : nat) := (fun y0 : Prop => (~ (y0 = (Coq.Arith.PeanoNat.Nat.Even x0))) = (~ ((~ y0) = (~ (Coq.Arith.PeanoNat.Nat.Even x0))))) True.
Definition term69 (x0 : nat) := ~ (False = (Coq.Arith.PeanoNat.Nat.Even x0)).
Definition term70 (x0 : nat) := ~ ((~ False) = (~ (Coq.Arith.PeanoNat.Nat.Even x0))).
Definition term32 (x0 : nat) := @eq Prop (~ (Coq.Arith.PeanoNat.Nat.Even x0)).
Definition term62 (x0 : nat) (x1 : nat) := (fun y0 : Prop => (~ (y0 = (Coq.Arith.PeanoNat.Nat.Even x0))) = (~ ((~ y0) = (~ (Coq.Arith.PeanoNat.Nat.Even x0))))) (Coq.Arith.PeanoNat.Nat.Even x1).
Definition term30 (x0 : nat) (x1 : nat) := @eq Prop ((Peano.lt x1 x0) /\ (~ ((Coq.Arith.PeanoNat.Nat.Even x0) = (Coq.Arith.PeanoNat.Nat.Even x1)))).
Definition term72 := @eq Prop (~ True).
Definition term17 (x0 : nat) (x1 : nat) := (Peano.le x0 x1) \/ ((Coq.Arith.PeanoNat.Nat.Even x0) = (Coq.Arith.PeanoNat.Nat.Even x1)).
Definition term26 (x0 : nat) (x1 : nat) := and (Peano.lt x0 x1).
Definition term64 (x0 : nat) := ~ (True = (Coq.Arith.PeanoNat.Nat.Even x0)).
Definition term33 (x0 : nat) (x1 : nat) := ~ ((Coq.Arith.PeanoNat.Nat.Odd x0) = (Coq.Arith.PeanoNat.Nat.Odd x1)).
Definition term16 (x0 : nat) (x1 : nat) := Coq.Arith.PeanoNat.Nat.Even (Nat.sub x0 x1).
Definition term59 (x0 : nat) := (fun y0 : Prop => (y0 = True) \/ (y0 = False)) (Coq.Arith.PeanoNat.Nat.Even x0).
Definition term49 (x0 : nat) (x1 : nat) := (fun y0 : Prop => (y0 /\ (~ ((Coq.Arith.PeanoNat.Nat.Even x0) = (Coq.Arith.PeanoNat.Nat.Even x1)))) = (y0 /\ (~ ((~ (Coq.Arith.PeanoNat.Nat.Even x0)) = (~ (Coq.Arith.PeanoNat.Nat.Even x1)))))) True.
Definition term53 (x0 : nat) (x1 : nat) := @eq Prop (((Peano.lt x1 x0) /\ (~ ((Coq.Arith.PeanoNat.Nat.Even x0) = (Coq.Arith.PeanoNat.Nat.Even x1)))) = ((Peano.lt x1 x0) /\ (~ ((~ (Coq.Arith.PeanoNat.Nat.Even x0)) = (~ (Coq.Arith.PeanoNat.Nat.Even x1)))))).
Definition term13 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Coq.Arith.PeanoNat.Nat.Even (Nat.sub y0 y1)) = ((Peano.le y0 y1) \/ ((Coq.Arith.PeanoNat.Nat.Even y0) = (Coq.Arith.PeanoNat.Nat.Even y1)))) x0.
Definition term5 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) x0.
Definition term60 (x0 : nat) := ((Coq.Arith.PeanoNat.Nat.Even x0) = True) \/ ((Coq.Arith.PeanoNat.Nat.Even x0) = False).
Definition term55 (x0 : nat) (x1 : nat) := False /\ (~ ((Coq.Arith.PeanoNat.Nat.Even x0) = (Coq.Arith.PeanoNat.Nat.Even x1))).
Definition term1 := fun y0 : nat => (~ (Coq.Arith.PeanoNat.Nat.Even y0)) = (Coq.Arith.PeanoNat.Nat.Odd y0).
Definition term68 (x0 : nat) := (fun y0 : Prop => (~ (y0 = (Coq.Arith.PeanoNat.Nat.Even x0))) = (~ ((~ y0) = (~ (Coq.Arith.PeanoNat.Nat.Even x0))))) False.
Definition term46 (x0 : nat) (x1 : nat) := ((Peano.lt x0 x1) = True) \/ ((Peano.lt x0 x1) = False).
Definition term52 (x0 : nat) (x1 : nat) := @eq Prop ((fun y0 : Prop => (y0 /\ (~ ((Coq.Arith.PeanoNat.Nat.Even x1) = (Coq.Arith.PeanoNat.Nat.Even x0)))) = (y0 /\ (~ ((~ (Coq.Arith.PeanoNat.Nat.Even x1)) = (~ (Coq.Arith.PeanoNat.Nat.Even x0)))))) (Peano.lt x0 x1)).
Definition term47 (x0 : nat) (x1 : nat) := fun y0 : Prop => (y0 /\ (~ ((Coq.Arith.PeanoNat.Nat.Even x0) = (Coq.Arith.PeanoNat.Nat.Even x1)))) = (y0 /\ (~ ((~ (Coq.Arith.PeanoNat.Nat.Even x0)) = (~ (Coq.Arith.PeanoNat.Nat.Even x1))))).
Definition term24 (x0 : nat) (x1 : nat) := (~ (Peano.le x0 x1)) /\ (~ ((Coq.Arith.PeanoNat.Nat.Even x0) = (Coq.Arith.PeanoNat.Nat.Even x1))).
Definition term35 (x0 : nat) (x1 : nat) := (Peano.lt x1 x0) /\ (~ ((Coq.Arith.PeanoNat.Nat.Odd x0) = (Coq.Arith.PeanoNat.Nat.Odd x1))).
Definition term28 (x0 : nat) (x1 : nat) := (Peano.lt x1 x0) /\ (~ ((Coq.Arith.PeanoNat.Nat.Even x0) = (Coq.Arith.PeanoNat.Nat.Even x1))).
Definition term54 (x0 : nat) (x1 : nat) := (fun y0 : Prop => (y0 /\ (~ ((Coq.Arith.PeanoNat.Nat.Even x0) = (Coq.Arith.PeanoNat.Nat.Even x1)))) = (y0 /\ (~ ((~ (Coq.Arith.PeanoNat.Nat.Even x0)) = (~ (Coq.Arith.PeanoNat.Nat.Even x1)))))) False.
Definition term7 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (Peano.le x0 y0)) = (Peano.lt y0 x0)) x1.
Definition term15 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even (Nat.sub x0 y0)) = ((Peano.le x0 y0) \/ ((Coq.Arith.PeanoNat.Nat.Even x0) = (Coq.Arith.PeanoNat.Nat.Even y0)))) x1.
Definition term31 (x0 : nat) := @eq Prop (Coq.Arith.PeanoNat.Nat.Odd x0).
Definition term25 (x0 : nat) (x1 : nat) := and (~ (Peano.le x0 x1)).
Definition term42 := fun y0 : nat => forall y1 : nat, ((Peano.lt y1 y0) /\ (~ ((Coq.Arith.PeanoNat.Nat.Even y0) = (Coq.Arith.PeanoNat.Nat.Even y1)))) = ((Peano.lt y1 y0) /\ (~ ((~ (Coq.Arith.PeanoNat.Nat.Even y0)) = (~ (Coq.Arith.PeanoNat.Nat.Even y1))))).
Definition term41 := fun y0 : nat => forall y1 : nat, (Coq.Arith.PeanoNat.Nat.Odd (Nat.sub y0 y1)) = ((Peano.lt y1 y0) /\ (~ ((Coq.Arith.PeanoNat.Nat.Odd y0) = (Coq.Arith.PeanoNat.Nat.Odd y1)))).
Definition term40 (x0 : nat) := forall y0 : nat, ((Peano.lt y0 x0) /\ (~ ((Coq.Arith.PeanoNat.Nat.Even x0) = (Coq.Arith.PeanoNat.Nat.Even y0)))) = ((Peano.lt y0 x0) /\ (~ ((~ (Coq.Arith.PeanoNat.Nat.Even x0)) = (~ (Coq.Arith.PeanoNat.Nat.Even y0))))).
Definition term18 (x0 : nat) := (fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Odd y0) = (~ (Coq.Arith.PeanoNat.Nat.Even y0))) x0.
