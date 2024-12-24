Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term77 (x0 : nat) (x1 : nat) := (Peano.le (S x1) x0) /\ (Peano.le x0 (S x1)).
Definition term57 (x0 : nat) := ((fun y0 : nat => ((Peano.le (NUMERAL 0) y0) /\ (Peano.le y0 (NUMERAL 0))) = ((NUMERAL 0) = y0)) x0) -> (fun y0 : nat => ((Peano.le (NUMERAL 0) y0) /\ (Peano.le y0 (NUMERAL 0))) = ((NUMERAL 0) = y0)) (S x0).
Definition term1 (x0 : nat) := ~ ((NUMERAL 0) = (S x0)).
Definition term97 := @eq Prop (Peano.le (NUMERAL 0) (NUMERAL 0)).
Definition term115 (x0 : nat) := False \/ (Peano.le (NUMERAL 0) x0).
Definition term16 (x0 : nat) := (fun y0 : nat => (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) x0.
Definition term48 := (Peano.le (NUMERAL 0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) (NUMERAL 0)).
Definition term5 := forall y0 : nat, ~ ((NUMERAL 0) = (S y0)).
Definition term106 (x0 : nat) (x1 : nat) := (Peano.le x1 x0) /\ (Peano.le x0 x1).
Definition term118 (x0 : nat) := Peano.le (S x0) (NUMERAL 0).
Definition term89 (x0 : nat) := (((Peano.le (S x0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) (S x0))) = ((S x0) = (NUMERAL 0))) /\ (forall y0 : nat, (((Peano.le (S x0) y0) /\ (Peano.le y0 (S x0))) = ((S x0) = y0)) -> ((Peano.le (S x0) (S y0)) /\ (Peano.le (S y0) (S x0))) = ((S x0) = (S y0))).
Definition term64 := (((Peano.le (NUMERAL 0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) (NUMERAL 0))) = ((NUMERAL 0) = (NUMERAL 0))) /\ (forall y0 : nat, (((Peano.le (NUMERAL 0) y0) /\ (Peano.le y0 (NUMERAL 0))) = ((NUMERAL 0) = y0)) -> ((Peano.le (NUMERAL 0) (S y0)) /\ (Peano.le (S y0) (NUMERAL 0))) = ((NUMERAL 0) = (S y0))).
Definition term36 := forall y0 : nat, (forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) = (y0 = y1)) -> forall y1 : nat, ((Peano.le (S y0) y1) /\ (Peano.le y1 (S y0))) = ((S y0) = y1).
Definition term105 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Peano.le x0 y0) /\ (Peano.le y0 x0)) = (x0 = y0)) x1.
Definition term102 (x0 : nat) := forall y0 : nat, (Peano.le (S x0) (S y0)) = (Peano.le x0 y0).
Definition term99 (x0 : nat) := forall y0 : nat, ((S x0) = (S y0)) = (x0 = y0).
Definition term26 (x0 : nat) := forall y0 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 x0)) = (x0 = y0).
Definition term44 := ((forall y0 : nat, ((Peano.le (NUMERAL 0) y0) /\ (Peano.le y0 (NUMERAL 0))) = ((NUMERAL 0) = y0)) /\ (forall y0 : nat, (forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) = (y0 = y1)) -> forall y1 : nat, ((Peano.le (S y0) y1) /\ (Peano.le y1 (S y0))) = ((S y0) = y1))) -> forall y0 : nat, forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) = (y0 = y1).
Definition term93 (x0 : nat) := forall y0 : nat, (fun y1 : nat => ((Peano.le (S x0) y1) /\ (Peano.le y1 (S x0))) = ((S x0) = y1)) y0.
Definition term68 := forall y0 : nat, (fun y1 : nat => ((Peano.le (NUMERAL 0) y1) /\ (Peano.le y1 (NUMERAL 0))) = ((NUMERAL 0) = y1)) y0.
Definition term88 (x0 : nat) := ((fun y0 : nat => ((Peano.le (S x0) y0) /\ (Peano.le y0 (S x0))) = ((S x0) = y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Peano.le (S x0) y1) /\ (Peano.le y1 (S x0))) = ((S x0) = y1)) y0) -> (fun y1 : nat => ((Peano.le (S x0) y1) /\ (Peano.le y1 (S x0))) = ((S x0) = y1)) (S y0)).
Definition term63 := ((fun y0 : nat => ((Peano.le (NUMERAL 0) y0) /\ (Peano.le y0 (NUMERAL 0))) = ((NUMERAL 0) = y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Peano.le (NUMERAL 0) y1) /\ (Peano.le y1 (NUMERAL 0))) = ((NUMERAL 0) = y1)) y0) -> (fun y1 : nat => ((Peano.le (NUMERAL 0) y1) /\ (Peano.le y1 (NUMERAL 0))) = ((NUMERAL 0) = y1)) (S y0)).
Definition term96 := @eq Prop ((Peano.le (NUMERAL 0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) (NUMERAL 0))).
Definition term27 (x0 : nat) := imp ((fun y0 : nat => forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) = (y0 = y1)) x0).
Definition term54 (x0 : nat) := imp (((Peano.le (NUMERAL 0) x0) /\ (Peano.le x0 (NUMERAL 0))) = ((NUMERAL 0) = x0)).
Definition term122 (x0 : nat) := False /\ (Peano.le (NUMERAL 0) x0).
Definition term82 (x0 : nat) (x1 : nat) := ((fun y0 : nat => ((Peano.le (S x0) y0) /\ (Peano.le y0 (S x0))) = ((S x0) = y0)) x1) -> (fun y0 : nat => ((Peano.le (S x0) y0) /\ (Peano.le y0 (S x0))) = ((S x0) = y0)) (S x1).
Definition term70 (x0 : nat) := (((fun y0 : nat => ((Peano.le (S x0) y0) /\ (Peano.le y0 (S x0))) = ((S x0) = y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Peano.le (S x0) y1) /\ (Peano.le y1 (S x0))) = ((S x0) = y1)) y0) -> (fun y1 : nat => ((Peano.le (S x0) y1) /\ (Peano.le y1 (S x0))) = ((S x0) = y1)) (S y0))) -> forall y0 : nat, (fun y1 : nat => ((Peano.le (S x0) y1) /\ (Peano.le y1 (S x0))) = ((S x0) = y1)) y0.
Definition term45 := (((fun y0 : nat => ((Peano.le (NUMERAL 0) y0) /\ (Peano.le y0 (NUMERAL 0))) = ((NUMERAL 0) = y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Peano.le (NUMERAL 0) y1) /\ (Peano.le y1 (NUMERAL 0))) = ((NUMERAL 0) = y1)) y0) -> (fun y1 : nat => ((Peano.le (NUMERAL 0) y1) /\ (Peano.le y1 (NUMERAL 0))) = ((NUMERAL 0) = y1)) (S y0))) -> forall y0 : nat, (fun y1 : nat => ((Peano.le (NUMERAL 0) y1) /\ (Peano.le y1 (NUMERAL 0))) = ((NUMERAL 0) = y1)) y0.
Definition term19 := (((fun y0 : nat => forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) = (y0 = y1)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Peano.le y1 y2) /\ (Peano.le y2 y1)) = (y1 = y2)) y0) -> (fun y1 : nat => forall y2 : nat, ((Peano.le y1 y2) /\ (Peano.le y2 y1)) = (y1 = y2)) (S y0))) -> forall y0 : nat, (fun y1 : nat => forall y2 : nat, ((Peano.le y1 y2) /\ (Peano.le y2 y1)) = (y1 = y2)) y0.
Definition term58 (x0 : nat) := (((Peano.le (NUMERAL 0) x0) /\ (Peano.le x0 (NUMERAL 0))) = ((NUMERAL 0) = x0)) -> ((Peano.le (NUMERAL 0) (S x0)) /\ (Peano.le (S x0) (NUMERAL 0))) = ((NUMERAL 0) = (S x0)).
Definition term79 (x0 : nat) (x1 : nat) := imp (((Peano.le (S x0) x1) /\ (Peano.le x1 (S x0))) = ((S x0) = x1)).
Definition term18 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term90 (x0 : nat) := imp (((fun y0 : nat => ((Peano.le (S x0) y0) /\ (Peano.le y0 (S x0))) = ((S x0) = y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Peano.le (S x0) y1) /\ (Peano.le y1 (S x0))) = ((S x0) = y1)) y0) -> (fun y1 : nat => ((Peano.le (S x0) y1) /\ (Peano.le y1 (S x0))) = ((S x0) = y1)) (S y0))).
Definition term65 := imp (((fun y0 : nat => ((Peano.le (NUMERAL 0) y0) /\ (Peano.le y0 (NUMERAL 0))) = ((NUMERAL 0) = y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Peano.le (NUMERAL 0) y1) /\ (Peano.le y1 (NUMERAL 0))) = ((NUMERAL 0) = y1)) y0) -> (fun y1 : nat => ((Peano.le (NUMERAL 0) y1) /\ (Peano.le y1 (NUMERAL 0))) = ((NUMERAL 0) = y1)) (S y0))).
Definition term39 := imp (((fun y0 : nat => forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) = (y0 = y1)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Peano.le y1 y2) /\ (Peano.le y2 y1)) = (y1 = y2)) y0) -> (fun y1 : nat => forall y2 : nat, ((Peano.le y1 y2) /\ (Peano.le y2 y1)) = (y1 = y2)) (S y0))).
Definition term30 (x0 : nat) := forall y0 : nat, ((Peano.le (S x0) y0) /\ (Peano.le y0 (S x0))) = ((S x0) = y0).
Definition term22 := forall y0 : nat, ((Peano.le (NUMERAL 0) y0) /\ (Peano.le y0 (NUMERAL 0))) = ((NUMERAL 0) = y0).
Definition term117 (x0 : nat) := and (Peano.le (NUMERAL 0) x0).
Definition term112 (x0 : nat) := ((NUMERAL 0) = (S x0)) \/ (Peano.le (NUMERAL 0) x0).
Definition term86 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => ((Peano.le (S x0) y1) /\ (Peano.le y1 (S x0))) = ((S x0) = y1)) y0) -> (fun y1 : nat => ((Peano.le (S x0) y1) /\ (Peano.le y1 (S x0))) = ((S x0) = y1)) (S y0).
Definition term61 := forall y0 : nat, ((fun y1 : nat => ((Peano.le (NUMERAL 0) y1) /\ (Peano.le y1 (NUMERAL 0))) = ((NUMERAL 0) = y1)) y0) -> (fun y1 : nat => ((Peano.le (NUMERAL 0) y1) /\ (Peano.le y1 (NUMERAL 0))) = ((NUMERAL 0) = y1)) (S y0).
Definition term35 := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Peano.le y1 y2) /\ (Peano.le y2 y1)) = (y1 = y2)) y0) -> (fun y1 : nat => forall y2 : nat, ((Peano.le y1 y2) /\ (Peano.le y2 y1)) = (y1 = y2)) (S y0).
Definition term55 (x0 : nat) := (fun y0 : nat => ((Peano.le (NUMERAL 0) y0) /\ (Peano.le y0 (NUMERAL 0))) = ((NUMERAL 0) = y0)) (S x0).
Definition term20 := fun y0 : nat => forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) = (y0 = y1).
Definition term4 := forall y0 : nat, ~ ((S y0) = (NUMERAL 0)).
Definition term74 (x0 : nat) := and ((fun y0 : nat => ((Peano.le (S x0) y0) /\ (Peano.le y0 (S x0))) = ((S x0) = y0)) (NUMERAL 0)).
Definition term49 := and ((fun y0 : nat => ((Peano.le (NUMERAL 0) y0) /\ (Peano.le y0 (NUMERAL 0))) = ((NUMERAL 0) = y0)) (NUMERAL 0)).
Definition term76 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Peano.le (S x0) y0) /\ (Peano.le y0 (S x0))) = ((S x0) = y0)) x1.
Definition term3 := fun y0 : nat => ~ ((NUMERAL 0) = (S y0)).
Definition term51 (x0 : nat) := (fun y0 : nat => ((Peano.le (NUMERAL 0) y0) /\ (Peano.le y0 (NUMERAL 0))) = ((NUMERAL 0) = y0)) x0.
Definition term23 := and ((fun y0 : nat => forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) = (y0 = y1)) (NUMERAL 0)).
Definition term28 (x0 : nat) := imp (forall y0 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 x0)) = (x0 = y0)).
Definition term24 := and (forall y0 : nat, ((Peano.le (NUMERAL 0) y0) /\ (Peano.le y0 (NUMERAL 0))) = ((NUMERAL 0) = y0)).
Definition term29 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) = (y0 = y1)) (S x0).
Definition term83 (x0 : nat) (x1 : nat) := (((Peano.le (S x0) x1) /\ (Peano.le x1 (S x0))) = ((S x0) = x1)) -> ((Peano.le (S x0) (S x1)) /\ (Peano.le (S x1) (S x0))) = ((S x0) = (S x1)).
Definition term21 := (fun y0 : nat => forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) = (y0 = y1)) (NUMERAL 0).
Definition term84 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => ((Peano.le (S x0) y1) /\ (Peano.le y1 (S x0))) = ((S x0) = y1)) y0) -> (fun y1 : nat => ((Peano.le (S x0) y1) /\ (Peano.le y1 (S x0))) = ((S x0) = y1)) (S y0).
Definition term59 := fun y0 : nat => ((fun y1 : nat => ((Peano.le (NUMERAL 0) y1) /\ (Peano.le y1 (NUMERAL 0))) = ((NUMERAL 0) = y1)) y0) -> (fun y1 : nat => ((Peano.le (NUMERAL 0) y1) /\ (Peano.le y1 (NUMERAL 0))) = ((NUMERAL 0) = y1)) (S y0).
Definition term103 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le (S x0) (S y0)) = (Peano.le x0 y0)) x1.
Definition term40 := imp ((forall y0 : nat, ((Peano.le (NUMERAL 0) y0) /\ (Peano.le y0 (NUMERAL 0))) = ((NUMERAL 0) = y0)) /\ (forall y0 : nat, (forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) = (y0 = y1)) -> forall y1 : nat, ((Peano.le (S y0) y1) /\ (Peano.le y1 (S y0))) = ((S y0) = y1))).
Definition term52 (x0 : nat) := (Peano.le (NUMERAL 0) x0) /\ (Peano.le x0 (NUMERAL 0)).
Definition term43 := forall y0 : nat, forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) = (y0 = y1).
Definition term9 := forall y0 : nat, forall y1 : nat, (Peano.le y0 (S y1)) = ((y0 = (S y1)) \/ (Peano.le y0 y1)).
Definition term56 (x0 : nat) := (Peano.le (NUMERAL 0) (S x0)) /\ (Peano.le (S x0) (NUMERAL 0)).
Definition term2 := fun y0 : nat => ~ ((S y0) = (NUMERAL 0)).
Definition term71 (x0 : nat) := fun y0 : nat => ((Peano.le (S x0) y0) /\ (Peano.le y0 (S x0))) = ((S x0) = y0).
Definition term78 (x0 : nat) (x1 : nat) := imp ((fun y0 : nat => ((Peano.le (S x0) y0) /\ (Peano.le y0 (S x0))) = ((S x0) = y0)) x1).
Definition term114 (x0 : nat) := Peano.le (NUMERAL 0) x0.
Definition term11 (x0 : nat) := forall y0 : nat, (Peano.le x0 (S y0)) = ((x0 = (S y0)) \/ (Peano.le x0 y0)).
Definition term113 (x0 : nat) := or ((NUMERAL 0) = (S x0)).
Definition term94 (x0 : nat) := ((((Peano.le (S x0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) (S x0))) = ((S x0) = (NUMERAL 0))) /\ (forall y0 : nat, (((Peano.le (S x0) y0) /\ (Peano.le y0 (S x0))) = ((S x0) = y0)) -> ((Peano.le (S x0) (S y0)) /\ (Peano.le (S y0) (S x0))) = ((S x0) = (S y0)))) -> forall y0 : nat, ((Peano.le (S x0) y0) /\ (Peano.le y0 (S x0))) = ((S x0) = y0).
Definition term69 := ((((Peano.le (NUMERAL 0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) (NUMERAL 0))) = ((NUMERAL 0) = (NUMERAL 0))) /\ (forall y0 : nat, (((Peano.le (NUMERAL 0) y0) /\ (Peano.le y0 (NUMERAL 0))) = ((NUMERAL 0) = y0)) -> ((Peano.le (NUMERAL 0) (S y0)) /\ (Peano.le (S y0) (NUMERAL 0))) = ((NUMERAL 0) = (S y0)))) -> forall y0 : nat, ((Peano.le (NUMERAL 0) y0) /\ (Peano.le y0 (NUMERAL 0))) = ((NUMERAL 0) = y0).
Definition term0 (x0 : nat) := ~ ((S x0) = (NUMERAL 0)).
Definition term6 (x0 : nat) := (fun y0 : nat => ~ ((NUMERAL 0) = (S y0))) x0.
Definition term50 := and (((Peano.le (NUMERAL 0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) (NUMERAL 0))) = ((NUMERAL 0) = (NUMERAL 0))).
Definition term46 := fun y0 : nat => ((Peano.le (NUMERAL 0) y0) /\ (Peano.le y0 (NUMERAL 0))) = ((NUMERAL 0) = y0).
Definition term80 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Peano.le (S x0) y0) /\ (Peano.le y0 (S x0))) = ((S x0) = y0)) (S x1).
Definition term34 := fun y0 : nat => (forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) = (y0 = y1)) -> forall y1 : nat, ((Peano.le (S y0) y1) /\ (Peano.le y1 (S y0))) = ((S y0) = y1).
Definition term33 := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, ((Peano.le y1 y2) /\ (Peano.le y2 y1)) = (y1 = y2)) y0) -> (fun y1 : nat => forall y2 : nat, ((Peano.le y1 y2) /\ (Peano.le y2 y1)) = (y1 = y2)) (S y0).
Definition term72 (x0 : nat) := (fun y0 : nat => ((Peano.le (S x0) y0) /\ (Peano.le y0 (S x0))) = ((S x0) = y0)) (NUMERAL 0).
Definition term47 := (fun y0 : nat => ((Peano.le (NUMERAL 0) y0) /\ (Peano.le y0 (NUMERAL 0))) = ((NUMERAL 0) = y0)) (NUMERAL 0).
Definition term38 := (forall y0 : nat, ((Peano.le (NUMERAL 0) y0) /\ (Peano.le y0 (NUMERAL 0))) = ((NUMERAL 0) = y0)) /\ (forall y0 : nat, (forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) = (y0 = y1)) -> forall y1 : nat, ((Peano.le (S y0) y1) /\ (Peano.le y1 (S y0))) = ((S y0) = y1)).
Definition term121 (x0 : nat) := and (Peano.le (S x0) (NUMERAL 0)).
Definition term14 (x0 : nat) (x1 : nat) := (x0 = (S x1)) \/ (Peano.le x0 x1).
Definition term41 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, ((Peano.le y1 y2) /\ (Peano.le y2 y1)) = (y1 = y2)) y0.
Definition term101 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (S y0) (S y1)) = (Peano.le y0 y1)) x0.
Definition term98 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((S y0) = (S y1)) = (y0 = y1)) x0.
Definition term25 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) = (y0 = y1)) x0.
Definition term10 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y0 (S y1)) = ((y0 = (S y1)) \/ (Peano.le y0 y1))) x0.
Definition term37 := ((fun y0 : nat => forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) = (y0 = y1)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Peano.le y1 y2) /\ (Peano.le y2 y1)) = (y1 = y2)) y0) -> (fun y1 : nat => forall y2 : nat, ((Peano.le y1 y2) /\ (Peano.le y2 y1)) = (y1 = y2)) (S y0)).
Definition term111 (x0 : nat) := Peano.le (NUMERAL 0) (S x0).
Definition term119 (x0 : nat) := (Peano.le (NUMERAL 0) x0) /\ False.
Definition term81 (x0 : nat) (x1 : nat) := (Peano.le (S x1) (S x0)) /\ (Peano.le (S x0) (S x1)).
Definition term15 := forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0)).
Definition term85 (x0 : nat) := fun y0 : nat => (((Peano.le (S x0) y0) /\ (Peano.le y0 (S x0))) = ((S x0) = y0)) -> ((Peano.le (S x0) (S y0)) /\ (Peano.le (S y0) (S x0))) = ((S x0) = (S y0)).
Definition term60 := fun y0 : nat => (((Peano.le (NUMERAL 0) y0) /\ (Peano.le y0 (NUMERAL 0))) = ((NUMERAL 0) = y0)) -> ((Peano.le (NUMERAL 0) (S y0)) /\ (Peano.le (S y0) (NUMERAL 0))) = ((NUMERAL 0) = (S y0)).
Definition term8 (x0 : nat) := (~ ((S x0) = (NUMERAL 0))) -> ((S x0) = (NUMERAL 0)) = False.
Definition term7 (x0 : nat) := (~ ((NUMERAL 0) = (S x0))) -> ((NUMERAL 0) = (S x0)) = False.
Definition term91 (x0 : nat) := imp ((((Peano.le (S x0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) (S x0))) = ((S x0) = (NUMERAL 0))) /\ (forall y0 : nat, (((Peano.le (S x0) y0) /\ (Peano.le y0 (S x0))) = ((S x0) = y0)) -> ((Peano.le (S x0) (S y0)) /\ (Peano.le (S y0) (S x0))) = ((S x0) = (S y0)))).
Definition term66 := imp ((((Peano.le (NUMERAL 0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) (NUMERAL 0))) = ((NUMERAL 0) = (NUMERAL 0))) /\ (forall y0 : nat, (((Peano.le (NUMERAL 0) y0) /\ (Peano.le y0 (NUMERAL 0))) = ((NUMERAL 0) = y0)) -> ((Peano.le (NUMERAL 0) (S y0)) /\ (Peano.le (S y0) (NUMERAL 0))) = ((NUMERAL 0) = (S y0)))).
Definition term110 (x0 : nat) (x1 : nat) := @eq Prop (x0 = x1).
Definition term92 (x0 : nat) := fun y0 : nat => (fun y1 : nat => ((Peano.le (S x0) y1) /\ (Peano.le y1 (S x0))) = ((S x0) = y1)) y0.
Definition term67 := fun y0 : nat => (fun y1 : nat => ((Peano.le (NUMERAL 0) y1) /\ (Peano.le y1 (NUMERAL 0))) = ((NUMERAL 0) = y1)) y0.
Definition term116 (x0 : nat) := and (Peano.le (NUMERAL 0) (S x0)).
Definition term73 (x0 : nat) := (Peano.le (S x0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) (S x0)).
Definition term87 (x0 : nat) := forall y0 : nat, (((Peano.le (S x0) y0) /\ (Peano.le y0 (S x0))) = ((S x0) = y0)) -> ((Peano.le (S x0) (S y0)) /\ (Peano.le (S y0) (S x0))) = ((S x0) = (S y0)).
Definition term62 := forall y0 : nat, (((Peano.le (NUMERAL 0) y0) /\ (Peano.le y0 (NUMERAL 0))) = ((NUMERAL 0) = y0)) -> ((Peano.le (NUMERAL 0) (S y0)) /\ (Peano.le (S y0) (NUMERAL 0))) = ((NUMERAL 0) = (S y0)).
Definition term123 (x0 : nat) := @eq Prop ((Peano.le (S x0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) (S x0))).
Definition term104 (x0 : nat) (x1 : nat) := Peano.le (S x0) (S x1).
Definition term53 (x0 : nat) := imp ((fun y0 : nat => ((Peano.le (NUMERAL 0) y0) /\ (Peano.le y0 (NUMERAL 0))) = ((NUMERAL 0) = y0)) x0).
Definition term31 (x0 : nat) := ((fun y0 : nat => forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) = (y0 = y1)) x0) -> (fun y0 : nat => forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) = (y0 = y1)) (S x0).
Definition term100 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((S x0) = (S y0)) = (x0 = y0)) x1.
Definition term109 (x0 : nat) (x1 : nat) := @eq Prop ((Peano.le (S x1) (S x0)) /\ (Peano.le (S x0) (S x1))).
Definition term42 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, ((Peano.le y1 y2) /\ (Peano.le y2 y1)) = (y1 = y2)) y0.
Definition term17 (x0 : nat) := Peano.le x0 (NUMERAL 0).
Definition term107 (x0 : nat) (x1 : nat) := and (Peano.le (S x0) (S x1)).
Definition term12 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le x0 (S y0)) = ((x0 = (S y0)) \/ (Peano.le x0 y0))) x1.
Definition term13 (x0 : nat) (x1 : nat) := Peano.le x0 (S x1).
Definition term120 (x0 : nat) := @eq Prop ((Peano.le (NUMERAL 0) (S x0)) /\ (Peano.le (S x0) (NUMERAL 0))).
Definition term108 (x0 : nat) (x1 : nat) := and (Peano.le x0 x1).
Definition term95 := Peano.le (NUMERAL 0) (NUMERAL 0).
Definition term75 (x0 : nat) := and (((Peano.le (S x0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) (S x0))) = ((S x0) = (NUMERAL 0))).
Definition term32 (x0 : nat) := (forall y0 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 x0)) = (x0 = y0)) -> forall y0 : nat, ((Peano.le (S x0) y0) /\ (Peano.le y0 (S x0))) = ((S x0) = y0).
