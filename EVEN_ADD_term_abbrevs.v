Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term57 (x0 : nat) := (fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even (S y0)) = (~ (Coq.Arith.PeanoNat.Nat.Even y0))) x0.
Definition term40 (x0 : nat) := @eq Prop (Coq.Arith.PeanoNat.Nat.Even x0).
Definition term62 (x0 : nat) (x1 : nat) := Coq.Arith.PeanoNat.Nat.Even (S (Nat.add x0 x1)).
Definition term87 (x0 : Prop) := ~ (~ x0).
Definition term82 (x0 : nat) (x1 : nat) (x2 : nat) := (Coq.Arith.PeanoNat.Nat.Odd x2) -> (Coq.Arith.PeanoNat.Nat.Odd x0) -> (~ ((Coq.Arith.PeanoNat.Nat.Even x1) = (Coq.Arith.PeanoNat.Nat.Even x2))) = ((~ (Coq.Arith.PeanoNat.Nat.Even x1)) = (Coq.Arith.PeanoNat.Nat.Even x2)).
Definition term46 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term26 := forall y0 : nat, (forall y1 : nat, (Coq.Arith.PeanoNat.Nat.Even (Nat.add y0 y1)) = ((Coq.Arith.PeanoNat.Nat.Even y0) = (Coq.Arith.PeanoNat.Nat.Even y1))) -> forall y1 : nat, (Coq.Arith.PeanoNat.Nat.Even (Nat.add (S y0) y1)) = ((Coq.Arith.PeanoNat.Nat.Even (S y0)) = (Coq.Arith.PeanoNat.Nat.Even y1)).
Definition term6 (x0 : nat) := (fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even y0) \/ (Coq.Arith.PeanoNat.Nat.Odd y0)) x0.
Definition term69 (x0 : nat) := fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even (Nat.add (S x0) y0)) = ((Coq.Arith.PeanoNat.Nat.Even (S x0)) = (Coq.Arith.PeanoNat.Nat.Even y0)).
Definition term43 := fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even (Nat.add (NUMERAL 0) y0)) = ((Coq.Arith.PeanoNat.Nat.Even (NUMERAL 0)) = (Coq.Arith.PeanoNat.Nat.Even y0)).
Definition term49 := (forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))).
Definition term0 (x0 : nat) := ~ (Coq.Arith.PeanoNat.Nat.Even x0).
Definition term72 (x0 : nat) := imp (Coq.Arith.PeanoNat.Nat.Odd x0).
Definition term34 := ((forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even (Nat.add (NUMERAL 0) y0)) = ((Coq.Arith.PeanoNat.Nat.Even (NUMERAL 0)) = (Coq.Arith.PeanoNat.Nat.Even y0))) /\ (forall y0 : nat, (forall y1 : nat, (Coq.Arith.PeanoNat.Nat.Even (Nat.add y0 y1)) = ((Coq.Arith.PeanoNat.Nat.Even y0) = (Coq.Arith.PeanoNat.Nat.Even y1))) -> forall y1 : nat, (Coq.Arith.PeanoNat.Nat.Even (Nat.add (S y0) y1)) = ((Coq.Arith.PeanoNat.Nat.Even (S y0)) = (Coq.Arith.PeanoNat.Nat.Even y1)))) -> forall y0 : nat, forall y1 : nat, (Coq.Arith.PeanoNat.Nat.Even (Nat.add y0 y1)) = ((Coq.Arith.PeanoNat.Nat.Even y0) = (Coq.Arith.PeanoNat.Nat.Even y1)).
Definition term63 (x0 : nat) (x1 : nat) := ~ (Coq.Arith.PeanoNat.Nat.Even (Nat.add x0 x1)).
Definition term41 := Coq.Arith.PeanoNat.Nat.Even (NUMERAL 0).
Definition term17 (x0 : nat) := imp ((fun y0 : nat => forall y1 : nat, (Coq.Arith.PeanoNat.Nat.Even (Nat.add y0 y1)) = ((Coq.Arith.PeanoNat.Nat.Even y0) = (Coq.Arith.PeanoNat.Nat.Even y1))) x0).
Definition term64 (x0 : nat) (x1 : nat) := ~ ((Coq.Arith.PeanoNat.Nat.Even x0) = (Coq.Arith.PeanoNat.Nat.Even x1)).
Definition term89 (x0 : nat) (x1 : nat) (x2 : nat) := (Coq.Arith.PeanoNat.Nat.Even x2) -> (Coq.Arith.PeanoNat.Nat.Even x0) -> (~ ((Coq.Arith.PeanoNat.Nat.Even x1) = (Coq.Arith.PeanoNat.Nat.Even x2))) = ((~ (Coq.Arith.PeanoNat.Nat.Even x1)) = (Coq.Arith.PeanoNat.Nat.Even x2)).
Definition term42 := @eq Prop (Coq.Arith.PeanoNat.Nat.Even (NUMERAL 0)).
Definition term86 (x0 : nat) := ~ (~ (Coq.Arith.PeanoNat.Nat.Even x0)).
Definition term70 (x0 : nat) := fun y0 : nat => (~ ((Coq.Arith.PeanoNat.Nat.Even x0) = (Coq.Arith.PeanoNat.Nat.Even y0))) = ((~ (Coq.Arith.PeanoNat.Nat.Even x0)) = (Coq.Arith.PeanoNat.Nat.Even y0)).
Definition term88 (x0 : nat) := (~ (Coq.Arith.PeanoNat.Nat.Even x0)) -> True.
Definition term9 := (((fun y0 : nat => forall y1 : nat, (Coq.Arith.PeanoNat.Nat.Even (Nat.add y0 y1)) = ((Coq.Arith.PeanoNat.Nat.Even y0) = (Coq.Arith.PeanoNat.Nat.Even y1))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (Coq.Arith.PeanoNat.Nat.Even (Nat.add y1 y2)) = ((Coq.Arith.PeanoNat.Nat.Even y1) = (Coq.Arith.PeanoNat.Nat.Even y2))) y0) -> (fun y1 : nat => forall y2 : nat, (Coq.Arith.PeanoNat.Nat.Even (Nat.add y1 y2)) = ((Coq.Arith.PeanoNat.Nat.Even y1) = (Coq.Arith.PeanoNat.Nat.Even y2))) (S y0))) -> forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Coq.Arith.PeanoNat.Nat.Even (Nat.add y1 y2)) = ((Coq.Arith.PeanoNat.Nat.Even y1) = (Coq.Arith.PeanoNat.Nat.Even y2))) y0.
Definition term8 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term61 (x0 : nat) (x1 : nat) := Coq.Arith.PeanoNat.Nat.Even (Nat.add (S x0) x1).
Definition term52 (x0 : nat) := forall y0 : nat, (Nat.add (S x0) y0) = (S (Nat.add x0 y0)).
Definition term79 (x0 : nat) := imp (Coq.Arith.PeanoNat.Nat.Even x0).
Definition term29 := imp (((fun y0 : nat => forall y1 : nat, (Coq.Arith.PeanoNat.Nat.Even (Nat.add y0 y1)) = ((Coq.Arith.PeanoNat.Nat.Even y0) = (Coq.Arith.PeanoNat.Nat.Even y1))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (Coq.Arith.PeanoNat.Nat.Even (Nat.add y1 y2)) = ((Coq.Arith.PeanoNat.Nat.Even y1) = (Coq.Arith.PeanoNat.Nat.Even y2))) y0) -> (fun y1 : nat => forall y2 : nat, (Coq.Arith.PeanoNat.Nat.Even (Nat.add y1 y2)) = ((Coq.Arith.PeanoNat.Nat.Even y1) = (Coq.Arith.PeanoNat.Nat.Even y2))) (S y0))).
Definition term84 (x0 : nat) := (Coq.Arith.PeanoNat.Nat.Even x0) -> True.
Definition term83 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Coq.Arith.PeanoNat.Nat.Even x2)) -> (~ (Coq.Arith.PeanoNat.Nat.Even x0)) -> (~ ((Coq.Arith.PeanoNat.Nat.Even x1) = (Coq.Arith.PeanoNat.Nat.Even x2))) = ((~ (Coq.Arith.PeanoNat.Nat.Even x1)) = (Coq.Arith.PeanoNat.Nat.Even x2)).
Definition term66 (x0 : nat) (x1 : nat) := @eq Prop (~ ((Coq.Arith.PeanoNat.Nat.Even x0) = (Coq.Arith.PeanoNat.Nat.Even x1))).
Definition term67 (x0 : nat) := @eq Prop (Coq.Arith.PeanoNat.Nat.Even (S x0)).
Definition term25 := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (Coq.Arith.PeanoNat.Nat.Even (Nat.add y1 y2)) = ((Coq.Arith.PeanoNat.Nat.Even y1) = (Coq.Arith.PeanoNat.Nat.Even y2))) y0) -> (fun y1 : nat => forall y2 : nat, (Coq.Arith.PeanoNat.Nat.Even (Nat.add y1 y2)) = ((Coq.Arith.PeanoNat.Nat.Even y1) = (Coq.Arith.PeanoNat.Nat.Even y2))) (S y0).
Definition term59 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even (Nat.add x0 y0)) = ((Coq.Arith.PeanoNat.Nat.Even x0) = (Coq.Arith.PeanoNat.Nat.Even y0))) x1.
Definition term85 (x0 : nat) := (~ (Coq.Arith.PeanoNat.Nat.Even x0)) -> (Coq.Arith.PeanoNat.Nat.Even x0) = False.
Definition term56 := forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even (S y0)) = (~ (Coq.Arith.PeanoNat.Nat.Even y0)).
Definition term4 := forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Odd y0) = (~ (Coq.Arith.PeanoNat.Nat.Even y0)).
Definition term77 (x0 : nat) (x1 : nat) (x2 : nat) := (Coq.Arith.PeanoNat.Nat.Odd x0) -> (~ ((Coq.Arith.PeanoNat.Nat.Even x1) = (Coq.Arith.PeanoNat.Nat.Even x2))) = ((~ (Coq.Arith.PeanoNat.Nat.Even x1)) = (Coq.Arith.PeanoNat.Nat.Even x2)).
Definition term53 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add (S x0) y0) = (S (Nat.add x0 y0))) x1.
Definition term13 := and ((fun y0 : nat => forall y1 : nat, (Coq.Arith.PeanoNat.Nat.Even (Nat.add y0 y1)) = ((Coq.Arith.PeanoNat.Nat.Even y0) = (Coq.Arith.PeanoNat.Nat.Even y1))) (NUMERAL 0)).
Definition term18 (x0 : nat) := imp (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even (Nat.add x0 y0)) = ((Coq.Arith.PeanoNat.Nat.Even x0) = (Coq.Arith.PeanoNat.Nat.Even y0))).
Definition term14 := and (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even (Nat.add (NUMERAL 0) y0)) = ((Coq.Arith.PeanoNat.Nat.Even (NUMERAL 0)) = (Coq.Arith.PeanoNat.Nat.Even y0))).
Definition term19 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Coq.Arith.PeanoNat.Nat.Even (Nat.add y0 y1)) = ((Coq.Arith.PeanoNat.Nat.Even y0) = (Coq.Arith.PeanoNat.Nat.Even y1))) (S x0).
Definition term11 := (fun y0 : nat => forall y1 : nat, (Coq.Arith.PeanoNat.Nat.Even (Nat.add y0 y1)) = ((Coq.Arith.PeanoNat.Nat.Even y0) = (Coq.Arith.PeanoNat.Nat.Even y1))) (NUMERAL 0).
Definition term3 := forall y0 : nat, (~ (Coq.Arith.PeanoNat.Nat.Even y0)) = (Coq.Arith.PeanoNat.Nat.Odd y0).
Definition term37 (x0 : nat) := Nat.add (NUMERAL 0) x0.
Definition term30 := imp ((forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even (Nat.add (NUMERAL 0) y0)) = ((Coq.Arith.PeanoNat.Nat.Even (NUMERAL 0)) = (Coq.Arith.PeanoNat.Nat.Even y0))) /\ (forall y0 : nat, (forall y1 : nat, (Coq.Arith.PeanoNat.Nat.Even (Nat.add y0 y1)) = ((Coq.Arith.PeanoNat.Nat.Even y0) = (Coq.Arith.PeanoNat.Nat.Even y1))) -> forall y1 : nat, (Coq.Arith.PeanoNat.Nat.Even (Nat.add (S y0) y1)) = ((Coq.Arith.PeanoNat.Nat.Even (S y0)) = (Coq.Arith.PeanoNat.Nat.Even y1)))).
Definition term55 (x0 : nat) (x1 : nat) := S (Nat.add x0 x1).
Definition term2 := fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Odd y0) = (~ (Coq.Arith.PeanoNat.Nat.Even y0)).
Definition term58 (x0 : nat) := Coq.Arith.PeanoNat.Nat.Even (S x0).
Definition term76 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Coq.Arith.PeanoNat.Nat.Even x2)) -> (Coq.Arith.PeanoNat.Nat.Even x0) -> (~ ((Coq.Arith.PeanoNat.Nat.Even x1) = (Coq.Arith.PeanoNat.Nat.Even x2))) = ((~ (Coq.Arith.PeanoNat.Nat.Even x1)) = (Coq.Arith.PeanoNat.Nat.Even x2)).
Definition term50 := forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1)).
Definition term33 := forall y0 : nat, forall y1 : nat, (Coq.Arith.PeanoNat.Nat.Even (Nat.add y0 y1)) = ((Coq.Arith.PeanoNat.Nat.Even y0) = (Coq.Arith.PeanoNat.Nat.Even y1)).
Definition term38 (x0 : nat) := Coq.Arith.PeanoNat.Nat.Even (Nat.add (NUMERAL 0) x0).
Definition term71 (x0 : nat) := forall y0 : nat, (~ ((Coq.Arith.PeanoNat.Nat.Even x0) = (Coq.Arith.PeanoNat.Nat.Even y0))) = ((~ (Coq.Arith.PeanoNat.Nat.Even x0)) = (Coq.Arith.PeanoNat.Nat.Even y0)).
Definition term20 (x0 : nat) := forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even (Nat.add (S x0) y0)) = ((Coq.Arith.PeanoNat.Nat.Even (S x0)) = (Coq.Arith.PeanoNat.Nat.Even y0)).
Definition term16 (x0 : nat) := forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even (Nat.add x0 y0)) = ((Coq.Arith.PeanoNat.Nat.Even x0) = (Coq.Arith.PeanoNat.Nat.Even y0)).
Definition term12 := forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even (Nat.add (NUMERAL 0) y0)) = ((Coq.Arith.PeanoNat.Nat.Even (NUMERAL 0)) = (Coq.Arith.PeanoNat.Nat.Even y0)).
Definition term45 := forall y0 : nat, True.
Definition term35 := forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0.
Definition term75 (x0 : nat) (x1 : nat) (x2 : nat) := (Coq.Arith.PeanoNat.Nat.Odd x2) -> (Coq.Arith.PeanoNat.Nat.Even x0) -> (~ ((Coq.Arith.PeanoNat.Nat.Even x1) = (Coq.Arith.PeanoNat.Nat.Even x2))) = ((~ (Coq.Arith.PeanoNat.Nat.Even x1)) = (Coq.Arith.PeanoNat.Nat.Even x2)).
Definition term36 (x0 : nat) := (fun y0 : nat => (Nat.add (NUMERAL 0) y0) = y0) x0.
Definition term44 := fun y0 : nat => True.
Definition term68 (x0 : nat) := @eq Prop (~ (Coq.Arith.PeanoNat.Nat.Even x0)).
Definition term60 (x0 : nat) (x1 : nat) := Coq.Arith.PeanoNat.Nat.Even (Nat.add x0 x1).
Definition term81 (x0 : nat) (x1 : nat) (x2 : nat) := (Coq.Arith.PeanoNat.Nat.Even x2) -> (~ (Coq.Arith.PeanoNat.Nat.Even x0)) -> (~ ((Coq.Arith.PeanoNat.Nat.Even x1) = (Coq.Arith.PeanoNat.Nat.Even x2))) = ((~ (Coq.Arith.PeanoNat.Nat.Even x1)) = (Coq.Arith.PeanoNat.Nat.Even x2)).
Definition term24 := fun y0 : nat => (forall y1 : nat, (Coq.Arith.PeanoNat.Nat.Even (Nat.add y0 y1)) = ((Coq.Arith.PeanoNat.Nat.Even y0) = (Coq.Arith.PeanoNat.Nat.Even y1))) -> forall y1 : nat, (Coq.Arith.PeanoNat.Nat.Even (Nat.add (S y0) y1)) = ((Coq.Arith.PeanoNat.Nat.Even (S y0)) = (Coq.Arith.PeanoNat.Nat.Even y1)).
Definition term23 := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, (Coq.Arith.PeanoNat.Nat.Even (Nat.add y1 y2)) = ((Coq.Arith.PeanoNat.Nat.Even y1) = (Coq.Arith.PeanoNat.Nat.Even y2))) y0) -> (fun y1 : nat => forall y2 : nat, (Coq.Arith.PeanoNat.Nat.Even (Nat.add y1 y2)) = ((Coq.Arith.PeanoNat.Nat.Even y1) = (Coq.Arith.PeanoNat.Nat.Even y2))) (S y0).
Definition term80 (x0 : nat) (x1 : nat) (x2 : nat) := (Coq.Arith.PeanoNat.Nat.Even x2) -> (Coq.Arith.PeanoNat.Nat.Odd x0) -> (~ ((Coq.Arith.PeanoNat.Nat.Even x1) = (Coq.Arith.PeanoNat.Nat.Even x2))) = ((~ (Coq.Arith.PeanoNat.Nat.Even x1)) = (Coq.Arith.PeanoNat.Nat.Even x2)).
Definition term48 := (forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))).
Definition term39 (x0 : nat) := @eq Prop (Coq.Arith.PeanoNat.Nat.Even (Nat.add (NUMERAL 0) x0)).
Definition term28 := (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even (Nat.add (NUMERAL 0) y0)) = ((Coq.Arith.PeanoNat.Nat.Even (NUMERAL 0)) = (Coq.Arith.PeanoNat.Nat.Even y0))) /\ (forall y0 : nat, (forall y1 : nat, (Coq.Arith.PeanoNat.Nat.Even (Nat.add y0 y1)) = ((Coq.Arith.PeanoNat.Nat.Even y0) = (Coq.Arith.PeanoNat.Nat.Even y1))) -> forall y1 : nat, (Coq.Arith.PeanoNat.Nat.Even (Nat.add (S y0) y1)) = ((Coq.Arith.PeanoNat.Nat.Even (S y0)) = (Coq.Arith.PeanoNat.Nat.Even y1))).
Definition term31 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (Coq.Arith.PeanoNat.Nat.Even (Nat.add y1 y2)) = ((Coq.Arith.PeanoNat.Nat.Even y1) = (Coq.Arith.PeanoNat.Nat.Even y2))) y0.
Definition term65 (x0 : nat) (x1 : nat) := @eq Prop (Coq.Arith.PeanoNat.Nat.Even (Nat.add (S x0) x1)).
Definition term51 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) x0.
Definition term15 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Coq.Arith.PeanoNat.Nat.Even (Nat.add y0 y1)) = ((Coq.Arith.PeanoNat.Nat.Even y0) = (Coq.Arith.PeanoNat.Nat.Even y1))) x0.
Definition term7 (x0 : nat) := (Coq.Arith.PeanoNat.Nat.Even x0) \/ (Coq.Arith.PeanoNat.Nat.Odd x0).
Definition term74 (x0 : nat) (x1 : nat) (x2 : nat) := (Coq.Arith.PeanoNat.Nat.Even x0) -> (~ ((Coq.Arith.PeanoNat.Nat.Even x1) = (Coq.Arith.PeanoNat.Nat.Even x2))) = ((~ (Coq.Arith.PeanoNat.Nat.Even x1)) = (Coq.Arith.PeanoNat.Nat.Even x2)).
Definition term27 := ((fun y0 : nat => forall y1 : nat, (Coq.Arith.PeanoNat.Nat.Even (Nat.add y0 y1)) = ((Coq.Arith.PeanoNat.Nat.Even y0) = (Coq.Arith.PeanoNat.Nat.Even y1))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (Coq.Arith.PeanoNat.Nat.Even (Nat.add y1 y2)) = ((Coq.Arith.PeanoNat.Nat.Even y1) = (Coq.Arith.PeanoNat.Nat.Even y2))) y0) -> (fun y1 : nat => forall y2 : nat, (Coq.Arith.PeanoNat.Nat.Even (Nat.add y1 y2)) = ((Coq.Arith.PeanoNat.Nat.Even y1) = (Coq.Arith.PeanoNat.Nat.Even y2))) (S y0)).
Definition term73 (x0 : nat) := imp (~ (Coq.Arith.PeanoNat.Nat.Even x0)).
Definition term1 := fun y0 : nat => (~ (Coq.Arith.PeanoNat.Nat.Even y0)) = (Coq.Arith.PeanoNat.Nat.Odd y0).
Definition term47 (x0 : Prop) := forall y0 : nat, x0.
Definition term78 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Coq.Arith.PeanoNat.Nat.Even x0)) -> (~ ((Coq.Arith.PeanoNat.Nat.Even x1) = (Coq.Arith.PeanoNat.Nat.Even x2))) = ((~ (Coq.Arith.PeanoNat.Nat.Even x1)) = (Coq.Arith.PeanoNat.Nat.Even x2)).
Definition term21 (x0 : nat) := ((fun y0 : nat => forall y1 : nat, (Coq.Arith.PeanoNat.Nat.Even (Nat.add y0 y1)) = ((Coq.Arith.PeanoNat.Nat.Even y0) = (Coq.Arith.PeanoNat.Nat.Even y1))) x0) -> (fun y0 : nat => forall y1 : nat, (Coq.Arith.PeanoNat.Nat.Even (Nat.add y0 y1)) = ((Coq.Arith.PeanoNat.Nat.Even y0) = (Coq.Arith.PeanoNat.Nat.Even y1))) (S x0).
Definition term32 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Coq.Arith.PeanoNat.Nat.Even (Nat.add y1 y2)) = ((Coq.Arith.PeanoNat.Nat.Even y1) = (Coq.Arith.PeanoNat.Nat.Even y2))) y0.
Definition term54 (x0 : nat) (x1 : nat) := Nat.add (S x0) x1.
Definition term10 := fun y0 : nat => forall y1 : nat, (Coq.Arith.PeanoNat.Nat.Even (Nat.add y0 y1)) = ((Coq.Arith.PeanoNat.Nat.Even y0) = (Coq.Arith.PeanoNat.Nat.Even y1)).
Definition term22 (x0 : nat) := (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even (Nat.add x0 y0)) = ((Coq.Arith.PeanoNat.Nat.Even x0) = (Coq.Arith.PeanoNat.Nat.Even y0))) -> forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even (Nat.add (S x0) y0)) = ((Coq.Arith.PeanoNat.Nat.Even (S x0)) = (Coq.Arith.PeanoNat.Nat.Even y0)).
Definition term5 (x0 : nat) := (fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Odd y0) = (~ (Coq.Arith.PeanoNat.Nat.Even y0))) x0.
