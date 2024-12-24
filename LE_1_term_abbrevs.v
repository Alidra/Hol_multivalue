Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term33 (x0 : nat) := Peano.le (NUMERAL (BIT1 0)) x0.
Definition term4 (x0 : nat) := forall y0 : nat, (Peano.le y0 x0) = (~ (Peano.lt x0 y0)).
Definition term67 := (forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0))))))).
Definition term30 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term36 := S (NUMERAL 0).
Definition term20 (x0 : nat) := (fun y0 : nat => (Peano.lt (NUMERAL 0) y0) = (~ (y0 = (NUMERAL 0)))) x0.
Definition term39 (x0 : nat) := (x0 = (NUMERAL 0)) \/ (Peano.lt x0 (NUMERAL 0)).
Definition term55 (x0 : nat) := imp (Peano.le (NUMERAL (BIT1 0)) x0).
Definition term44 := forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0.
Definition term28 := forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0.
Definition term25 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> ~ (x0 = (NUMERAL 0)).
Definition term23 (x0 : nat) := imp (~ (x0 = (NUMERAL 0))).
Definition term15 := forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False.
Definition term57 := fun y0 : nat => (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0.
Definition term26 := fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0.
Definition term22 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term5 := fun y0 : nat => forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0).
Definition term14 (x0 : nat) (x1 : nat) := (x0 = x1) \/ (Peano.lt x0 x1).
Definition term34 (x0 : nat) := ~ (Peano.lt x0 (NUMERAL (BIT1 0))).
Definition term16 (x0 : nat) := (fun y0 : nat => (Peano.lt y0 (NUMERAL 0)) = False) x0.
Definition term1 (x0 : nat) := fun y0 : nat => (~ (Peano.lt x0 y0)) = (Peano.le y0 x0).
Definition term59 := and (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0).
Definition term54 := and (forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0).
Definition term50 := and (forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))).
Definition term45 := and (forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0).
Definition term32 := and (forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0).
Definition term64 := (forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))).
Definition term43 := fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0.
Definition term40 (x0 : nat) := or (x0 = (NUMERAL 0)).
Definition term9 := forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)).
Definition term8 := forall y0 : nat, forall y1 : nat, (Peano.le y1 y0) = (~ (Peano.lt y0 y1)).
Definition term7 := forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0).
Definition term3 (x0 : nat) := forall y0 : nat, (~ (Peano.lt x0 y0)) = (Peano.le y0 x0).
Definition term13 (x0 : nat) (x1 : nat) := Peano.lt x0 (S x1).
Definition term29 := forall y0 : nat, True.
Definition term2 (x0 : nat) := fun y0 : nat => (Peano.le y0 x0) = (~ (Peano.lt x0 y0)).
Definition term48 := fun y0 : nat => (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0)).
Definition term27 := fun y0 : nat => True.
Definition term11 (x0 : nat) := forall y0 : nat, (Peano.lt x0 (S y0)) = ((x0 = y0) \/ (Peano.lt x0 y0)).
Definition term37 (x0 : nat) := Peano.lt x0 (NUMERAL (BIT1 0)).
Definition term24 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) x0.
Definition term52 := fun y0 : nat => (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0.
Definition term38 (x0 : nat) := Peano.lt x0 (S (NUMERAL 0)).
Definition term12 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt x0 (S y0)) = ((x0 = y0) \/ (Peano.lt x0 y0))) x1.
Definition term63 := (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0))).
Definition term62 := forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)).
Definition term49 := forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0)).
Definition term17 (x0 : nat) := Peano.lt x0 (NUMERAL 0).
Definition term0 (x0 : nat) (x1 : nat) := ~ (Peano.lt x0 x1).
Definition term18 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y1 y0) = (~ (Peano.lt y0 y1))) x0.
Definition term10 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1))) x0.
Definition term65 := (forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0))))).
Definition term58 := forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0.
Definition term53 := forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0.
Definition term41 (x0 : nat) := (x0 = (NUMERAL 0)) \/ False.
Definition term19 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le y0 x0) = (~ (Peano.lt x0 y0))) x1.
Definition term56 (x0 : nat) := (Peano.le (NUMERAL (BIT1 0)) x0) -> Peano.lt (NUMERAL 0) x0.
Definition term31 (x0 : Prop) := forall y0 : nat, x0.
Definition term6 := fun y0 : nat => forall y1 : nat, (Peano.le y1 y0) = (~ (Peano.lt y0 y1)).
Definition term46 (x0 : nat) := imp (Peano.lt (NUMERAL 0) x0).
Definition term51 (x0 : nat) := (Peano.lt (NUMERAL 0) x0) -> Peano.le (NUMERAL (BIT1 0)) x0.
Definition term60 (x0 : nat) := (Peano.le (NUMERAL (BIT1 0)) x0) -> ~ (x0 = (NUMERAL 0)).
Definition term42 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) x0.
Definition term66 := (forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))).
Definition term61 := fun y0 : nat => (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)).
Definition term21 (x0 : nat) := Peano.lt (NUMERAL 0) x0.
Definition term47 (x0 : nat) := (Peano.lt (NUMERAL 0) x0) -> ~ (x0 = (NUMERAL 0)).
Definition term35 := NUMERAL (BIT1 0).
