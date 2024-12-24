Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term35 (x0 : nat) := (fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even (S y0)) = (~ (Coq.Arith.PeanoNat.Nat.Even y0))) x0.
Definition term15 (x0 : nat) (x1 : nat) := (Coq.Arith.PeanoNat.Nat.Even x0) /\ (~ ((S x1) = (NUMERAL 0))).
Definition term5 (x0 : nat) := (Coq.Arith.PeanoNat.Nat.Even x0) /\ (~ ((NUMERAL 0) = (NUMERAL 0))).
Definition term66 (x0 : nat) := (Coq.Arith.PeanoNat.Nat.Even x0) /\ True.
Definition term26 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (Coq.Arith.PeanoNat.Nat.Even (Nat.pow x0 y1)) = ((Coq.Arith.PeanoNat.Nat.Even x0) /\ (~ (y1 = (NUMERAL 0))))) y0.
Definition term65 (x0 : nat) (x1 : nat) := @eq Prop ((Coq.Arith.PeanoNat.Nat.Even x0) \/ ((Coq.Arith.PeanoNat.Nat.Even x0) /\ (~ (x1 = (NUMERAL 0))))).
Definition term63 (x0 : nat) (x1 : nat) := (Coq.Arith.PeanoNat.Nat.Even x0) \/ ((Coq.Arith.PeanoNat.Nat.Even x0) /\ (~ (x1 = (NUMERAL 0)))).
Definition term38 := S (NUMERAL 0).
Definition term56 (x0 : nat) := forall y0 : nat, (Nat.pow x0 (S y0)) = (Nat.mul x0 (Nat.pow x0 y0)).
Definition term37 (x0 : nat) := ~ (Coq.Arith.PeanoNat.Nat.Even x0).
Definition term51 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even (Nat.mul x0 y0)) = ((Coq.Arith.PeanoNat.Nat.Even x0) \/ (Coq.Arith.PeanoNat.Nat.Even y0))) x1.
Definition term3 (x0 : nat) := (fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even (Nat.pow x0 y0)) = ((Coq.Arith.PeanoNat.Nat.Even x0) /\ (~ (y0 = (NUMERAL 0))))) (NUMERAL 0).
Definition term27 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (Coq.Arith.PeanoNat.Nat.Even (Nat.pow x0 y1)) = ((Coq.Arith.PeanoNat.Nat.Even x0) /\ (~ (y1 = (NUMERAL 0))))) y0.
Definition term62 (x0 : nat) := or (Coq.Arith.PeanoNat.Nat.Even x0).
Definition term7 (x0 : nat) := and ((Coq.Arith.PeanoNat.Nat.Even (Nat.pow x0 (NUMERAL 0))) = ((Coq.Arith.PeanoNat.Nat.Even x0) /\ (~ ((NUMERAL 0) = (NUMERAL 0))))).
Definition term41 := Coq.Arith.PeanoNat.Nat.Even (NUMERAL 0).
Definition term2 (x0 : nat) := fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even (Nat.pow x0 y0)) = ((Coq.Arith.PeanoNat.Nat.Even x0) /\ (~ (y0 = (NUMERAL 0)))).
Definition term22 (x0 : nat) := ((fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even (Nat.pow x0 y0)) = ((Coq.Arith.PeanoNat.Nat.Even x0) /\ (~ (y0 = (NUMERAL 0))))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Coq.Arith.PeanoNat.Nat.Even (Nat.pow x0 y1)) = ((Coq.Arith.PeanoNat.Nat.Even x0) /\ (~ (y1 = (NUMERAL 0))))) y0) -> (fun y1 : nat => (Coq.Arith.PeanoNat.Nat.Even (Nat.pow x0 y1)) = ((Coq.Arith.PeanoNat.Nat.Even x0) /\ (~ (y1 = (NUMERAL 0))))) (S y0)).
Definition term12 (x0 : nat) (x1 : nat) := imp ((Coq.Arith.PeanoNat.Nat.Even (Nat.pow x0 x1)) = ((Coq.Arith.PeanoNat.Nat.Even x0) /\ (~ (x1 = (NUMERAL 0))))).
Definition term28 (x0 : nat) := forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even (Nat.pow x0 y0)) = ((Coq.Arith.PeanoNat.Nat.Even x0) /\ (~ (y0 = (NUMERAL 0)))).
Definition term58 (x0 : nat) (x1 : nat) := Nat.pow x0 (S x1).
Definition term16 (x0 : nat) (x1 : nat) := ((fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even (Nat.pow x0 y0)) = ((Coq.Arith.PeanoNat.Nat.Even x0) /\ (~ (y0 = (NUMERAL 0))))) x1) -> (fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even (Nat.pow x0 y0)) = ((Coq.Arith.PeanoNat.Nat.Even x0) /\ (~ (y0 = (NUMERAL 0))))) (S x1).
Definition term1 (x0 : nat) := (((fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even (Nat.pow x0 y0)) = ((Coq.Arith.PeanoNat.Nat.Even x0) /\ (~ (y0 = (NUMERAL 0))))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Coq.Arith.PeanoNat.Nat.Even (Nat.pow x0 y1)) = ((Coq.Arith.PeanoNat.Nat.Even x0) /\ (~ (y1 = (NUMERAL 0))))) y0) -> (fun y1 : nat => (Coq.Arith.PeanoNat.Nat.Even (Nat.pow x0 y1)) = ((Coq.Arith.PeanoNat.Nat.Even x0) /\ (~ (y1 = (NUMERAL 0))))) (S y0))) -> forall y0 : nat, (fun y1 : nat => (Coq.Arith.PeanoNat.Nat.Even (Nat.pow x0 y1)) = ((Coq.Arith.PeanoNat.Nat.Even x0) /\ (~ (y1 = (NUMERAL 0))))) y0.
Definition term57 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.pow x0 (S y0)) = (Nat.mul x0 (Nat.pow x0 y0))) x1.
Definition term32 (x0 : nat) := Nat.pow x0 (NUMERAL 0).
Definition term0 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term24 (x0 : nat) := imp (((fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even (Nat.pow x0 y0)) = ((Coq.Arith.PeanoNat.Nat.Even x0) /\ (~ (y0 = (NUMERAL 0))))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Coq.Arith.PeanoNat.Nat.Even (Nat.pow x0 y1)) = ((Coq.Arith.PeanoNat.Nat.Even x0) /\ (~ (y1 = (NUMERAL 0))))) y0) -> (fun y1 : nat => (Coq.Arith.PeanoNat.Nat.Even (Nat.pow x0 y1)) = ((Coq.Arith.PeanoNat.Nat.Even x0) /\ (~ (y1 = (NUMERAL 0))))) (S y0))).
Definition term43 := ~ ((NUMERAL 0) = (NUMERAL 0)).
Definition term20 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => (Coq.Arith.PeanoNat.Nat.Even (Nat.pow x0 y1)) = ((Coq.Arith.PeanoNat.Nat.Even x0) /\ (~ (y1 = (NUMERAL 0))))) y0) -> (fun y1 : nat => (Coq.Arith.PeanoNat.Nat.Even (Nat.pow x0 y1)) = ((Coq.Arith.PeanoNat.Nat.Even x0) /\ (~ (y1 = (NUMERAL 0))))) (S y0).
Definition term61 (x0 : nat) (x1 : nat) := (Coq.Arith.PeanoNat.Nat.Even x0) \/ (Coq.Arith.PeanoNat.Nat.Even (Nat.pow x0 x1)).
Definition term6 (x0 : nat) := and ((fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even (Nat.pow x0 y0)) = ((Coq.Arith.PeanoNat.Nat.Even x0) /\ (~ (y0 = (NUMERAL 0))))) (NUMERAL 0)).
Definition term34 := forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even (S y0)) = (~ (Coq.Arith.PeanoNat.Nat.Even y0)).
Definition term68 (x0 : nat) (x1 : nat) := (Coq.Arith.PeanoNat.Nat.Even x0) -> (Coq.Arith.PeanoNat.Nat.Even x0) \/ ((Coq.Arith.PeanoNat.Nat.Even x0) /\ (~ (x1 = (NUMERAL 0)))).
Definition term8 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even (Nat.pow x0 y0)) = ((Coq.Arith.PeanoNat.Nat.Even x0) /\ (~ (y0 = (NUMERAL 0))))) x1.
Definition term9 (x0 : nat) (x1 : nat) := Coq.Arith.PeanoNat.Nat.Even (Nat.pow x0 x1).
Definition term31 (x0 : nat) := (fun y0 : nat => (Nat.pow y0 (NUMERAL 0)) = (NUMERAL (BIT1 0))) x0.
Definition term18 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => (Coq.Arith.PeanoNat.Nat.Even (Nat.pow x0 y1)) = ((Coq.Arith.PeanoNat.Nat.Even x0) /\ (~ (y1 = (NUMERAL 0))))) y0) -> (fun y1 : nat => (Coq.Arith.PeanoNat.Nat.Even (Nat.pow x0 y1)) = ((Coq.Arith.PeanoNat.Nat.Even x0) /\ (~ (y1 = (NUMERAL 0))))) (S y0).
Definition term36 (x0 : nat) := Coq.Arith.PeanoNat.Nat.Even (S x0).
Definition term23 (x0 : nat) := ((Coq.Arith.PeanoNat.Nat.Even (Nat.pow x0 (NUMERAL 0))) = ((Coq.Arith.PeanoNat.Nat.Even x0) /\ (~ ((NUMERAL 0) = (NUMERAL 0))))) /\ (forall y0 : nat, ((Coq.Arith.PeanoNat.Nat.Even (Nat.pow x0 y0)) = ((Coq.Arith.PeanoNat.Nat.Even x0) /\ (~ (y0 = (NUMERAL 0))))) -> (Coq.Arith.PeanoNat.Nat.Even (Nat.pow x0 (S y0))) = ((Coq.Arith.PeanoNat.Nat.Even x0) /\ (~ ((S y0) = (NUMERAL 0))))).
Definition term70 := forall y0 : nat, forall y1 : nat, (Coq.Arith.PeanoNat.Nat.Even (Nat.pow y0 y1)) = ((Coq.Arith.PeanoNat.Nat.Even y0) /\ (~ (y1 = (NUMERAL 0)))).
Definition term54 := forall y0 : nat, forall y1 : nat, (Nat.pow y0 (S y1)) = (Nat.mul y0 (Nat.pow y0 y1)).
Definition term39 := Coq.Arith.PeanoNat.Nat.Even (S (NUMERAL 0)).
Definition term64 (x0 : nat) (x1 : nat) := @eq Prop (Coq.Arith.PeanoNat.Nat.Even (Nat.pow x0 (S x1))).
Definition term50 (x0 : nat) := forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even (Nat.mul x0 y0)) = ((Coq.Arith.PeanoNat.Nat.Even x0) \/ (Coq.Arith.PeanoNat.Nat.Even y0)).
Definition term29 (x0 : nat) := (((Coq.Arith.PeanoNat.Nat.Even (Nat.pow x0 (NUMERAL 0))) = ((Coq.Arith.PeanoNat.Nat.Even x0) /\ (~ ((NUMERAL 0) = (NUMERAL 0))))) /\ (forall y0 : nat, ((Coq.Arith.PeanoNat.Nat.Even (Nat.pow x0 y0)) = ((Coq.Arith.PeanoNat.Nat.Even x0) /\ (~ (y0 = (NUMERAL 0))))) -> (Coq.Arith.PeanoNat.Nat.Even (Nat.pow x0 (S y0))) = ((Coq.Arith.PeanoNat.Nat.Even x0) /\ (~ ((S y0) = (NUMERAL 0)))))) -> forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even (Nat.pow x0 y0)) = ((Coq.Arith.PeanoNat.Nat.Even x0) /\ (~ (y0 = (NUMERAL 0)))).
Definition term59 (x0 : nat) (x1 : nat) := Nat.mul x0 (Nat.pow x0 x1).
Definition term60 (x0 : nat) (x1 : nat) := Coq.Arith.PeanoNat.Nat.Even (Nat.mul x0 (Nat.pow x0 x1)).
Definition term11 (x0 : nat) (x1 : nat) := imp ((fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even (Nat.pow x0 y0)) = ((Coq.Arith.PeanoNat.Nat.Even x0) /\ (~ (y0 = (NUMERAL 0))))) x1).
Definition term45 (x0 : nat) := (Coq.Arith.PeanoNat.Nat.Even x0) /\ False.
Definition term67 (x0 : nat) (x1 : nat) := ((Coq.Arith.PeanoNat.Nat.Even x1) \/ ((Coq.Arith.PeanoNat.Nat.Even x1) /\ (~ (x0 = (NUMERAL 0))))) -> Coq.Arith.PeanoNat.Nat.Even x1.
Definition term42 (x0 : nat) := @eq Prop (Coq.Arith.PeanoNat.Nat.Even (Nat.pow x0 (NUMERAL 0))).
Definition term47 (x0 : nat) := ~ ((S x0) = (NUMERAL 0)).
Definition term10 (x0 : nat) (x1 : nat) := (Coq.Arith.PeanoNat.Nat.Even x0) /\ (~ (x1 = (NUMERAL 0))).
Definition term17 (x0 : nat) (x1 : nat) := ((Coq.Arith.PeanoNat.Nat.Even (Nat.pow x0 x1)) = ((Coq.Arith.PeanoNat.Nat.Even x0) /\ (~ (x1 = (NUMERAL 0))))) -> (Coq.Arith.PeanoNat.Nat.Even (Nat.pow x0 (S x1))) = ((Coq.Arith.PeanoNat.Nat.Even x0) /\ (~ ((S x1) = (NUMERAL 0)))).
Definition term19 (x0 : nat) := fun y0 : nat => ((Coq.Arith.PeanoNat.Nat.Even (Nat.pow x0 y0)) = ((Coq.Arith.PeanoNat.Nat.Even x0) /\ (~ (y0 = (NUMERAL 0))))) -> (Coq.Arith.PeanoNat.Nat.Even (Nat.pow x0 (S y0))) = ((Coq.Arith.PeanoNat.Nat.Even x0) /\ (~ ((S y0) = (NUMERAL 0)))).
Definition term55 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.pow y0 (S y1)) = (Nat.mul y0 (Nat.pow y0 y1))) x0.
Definition term49 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Coq.Arith.PeanoNat.Nat.Even (Nat.mul y0 y1)) = ((Coq.Arith.PeanoNat.Nat.Even y0) \/ (Coq.Arith.PeanoNat.Nat.Even y1))) x0.
Definition term46 (x0 : nat) := (fun y0 : nat => ~ ((S y0) = (NUMERAL 0))) x0.
Definition term30 := forall y0 : nat, (Nat.pow y0 (NUMERAL 0)) = (NUMERAL (BIT1 0)).
Definition term53 (x0 : nat) (x1 : nat) := (Coq.Arith.PeanoNat.Nat.Even x0) \/ (Coq.Arith.PeanoNat.Nat.Even x1).
Definition term4 (x0 : nat) := Coq.Arith.PeanoNat.Nat.Even (Nat.pow x0 (NUMERAL 0)).
Definition term48 (x0 : nat) := (~ ((S x0) = (NUMERAL 0))) -> ((S x0) = (NUMERAL 0)) = False.
Definition term44 (x0 : nat) := and (Coq.Arith.PeanoNat.Nat.Even x0).
Definition term40 := ~ (Coq.Arith.PeanoNat.Nat.Even (NUMERAL 0)).
Definition term25 (x0 : nat) := imp (((Coq.Arith.PeanoNat.Nat.Even (Nat.pow x0 (NUMERAL 0))) = ((Coq.Arith.PeanoNat.Nat.Even x0) /\ (~ ((NUMERAL 0) = (NUMERAL 0))))) /\ (forall y0 : nat, ((Coq.Arith.PeanoNat.Nat.Even (Nat.pow x0 y0)) = ((Coq.Arith.PeanoNat.Nat.Even x0) /\ (~ (y0 = (NUMERAL 0))))) -> (Coq.Arith.PeanoNat.Nat.Even (Nat.pow x0 (S y0))) = ((Coq.Arith.PeanoNat.Nat.Even x0) /\ (~ ((S y0) = (NUMERAL 0)))))).
Definition term21 (x0 : nat) := forall y0 : nat, ((Coq.Arith.PeanoNat.Nat.Even (Nat.pow x0 y0)) = ((Coq.Arith.PeanoNat.Nat.Even x0) /\ (~ (y0 = (NUMERAL 0))))) -> (Coq.Arith.PeanoNat.Nat.Even (Nat.pow x0 (S y0))) = ((Coq.Arith.PeanoNat.Nat.Even x0) /\ (~ ((S y0) = (NUMERAL 0)))).
Definition term13 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even (Nat.pow x0 y0)) = ((Coq.Arith.PeanoNat.Nat.Even x0) /\ (~ (y0 = (NUMERAL 0))))) (S x1).
Definition term69 (x0 : nat) (x1 : nat) := (((Coq.Arith.PeanoNat.Nat.Even x0) \/ ((Coq.Arith.PeanoNat.Nat.Even x0) /\ (~ (x1 = (NUMERAL 0))))) -> Coq.Arith.PeanoNat.Nat.Even x0) /\ ((Coq.Arith.PeanoNat.Nat.Even x0) -> (Coq.Arith.PeanoNat.Nat.Even x0) \/ ((Coq.Arith.PeanoNat.Nat.Even x0) /\ (~ (x1 = (NUMERAL 0))))).
Definition term52 (x0 : nat) (x1 : nat) := Coq.Arith.PeanoNat.Nat.Even (Nat.mul x0 x1).
Definition term33 := NUMERAL (BIT1 0).
Definition term14 (x0 : nat) (x1 : nat) := Coq.Arith.PeanoNat.Nat.Even (Nat.pow x0 (S x1)).
