Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term63 (x0 : nat) (x1 : nat) := (Peano.le (S x1) (S x0)) \/ (Peano.le (S x0) (S x1)).
Definition term39 (x0 : nat) := ((fun y0 : nat => (Peano.le (NUMERAL 0) y0) \/ (Peano.le y0 (NUMERAL 0))) x0) -> (fun y0 : nat => (Peano.le (NUMERAL 0) y0) \/ (Peano.le y0 (NUMERAL 0))) (S x0).
Definition term84 (x0 : nat) := or (Peano.le (S x0) (NUMERAL 0)).
Definition term37 (x0 : nat) := (fun y0 : nat => (Peano.le (NUMERAL 0) y0) \/ (Peano.le y0 (NUMERAL 0))) (S x0).
Definition term38 (x0 : nat) := (Peano.le (NUMERAL 0) (S x0)) \/ (Peano.le (S x0) (NUMERAL 0)).
Definition term82 (x0 : nat) := Peano.le (S x0) (NUMERAL 0).
Definition term36 (x0 : nat) := imp ((Peano.le (NUMERAL 0) x0) \/ (Peano.le x0 (NUMERAL 0))).
Definition term18 := forall y0 : nat, (forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) -> forall y1 : nat, (Peano.le (S y0) y1) \/ (Peano.le y1 (S y0)).
Definition term71 (x0 : nat) := ((Peano.le (S x0) (NUMERAL 0)) \/ (Peano.le (NUMERAL 0) (S x0))) /\ (forall y0 : nat, ((Peano.le (S x0) y0) \/ (Peano.le y0 (S x0))) -> (Peano.le (S x0) (S y0)) \/ (Peano.le (S y0) (S x0))).
Definition term87 (x0 : nat) := forall y0 : nat, (Peano.le (S x0) (S y0)) = (Peano.le x0 y0).
Definition term26 := ((forall y0 : nat, (Peano.le (NUMERAL 0) y0) \/ (Peano.le y0 (NUMERAL 0))) /\ (forall y0 : nat, (forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) -> forall y1 : nat, (Peano.le (S y0) y1) \/ (Peano.le y1 (S y0)))) -> forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0).
Definition term75 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (Peano.le (S x0) y1) \/ (Peano.le y1 (S x0))) y0.
Definition term50 := forall y0 : nat, (fun y1 : nat => (Peano.le (NUMERAL 0) y1) \/ (Peano.le y1 (NUMERAL 0))) y0.
Definition term90 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le x0 y0) \/ (Peano.le y0 x0)) x1.
Definition term70 (x0 : nat) := ((fun y0 : nat => (Peano.le (S x0) y0) \/ (Peano.le y0 (S x0))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Peano.le (S x0) y1) \/ (Peano.le y1 (S x0))) y0) -> (fun y1 : nat => (Peano.le (S x0) y1) \/ (Peano.le y1 (S x0))) (S y0)).
Definition term45 := ((fun y0 : nat => (Peano.le (NUMERAL 0) y0) \/ (Peano.le y0 (NUMERAL 0))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Peano.le (NUMERAL 0) y1) \/ (Peano.le y1 (NUMERAL 0))) y0) -> (fun y1 : nat => (Peano.le (NUMERAL 0) y1) \/ (Peano.le y1 (NUMERAL 0))) (S y0)).
Definition term9 (x0 : nat) := imp ((fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) x0).
Definition term4 := forall y0 : nat, (Peano.le (NUMERAL 0) y0) \/ (Peano.le y0 (NUMERAL 0)).
Definition term77 (x0 : nat) := (fun y0 : nat => Peano.le (NUMERAL 0) y0) x0.
Definition term64 (x0 : nat) (x1 : nat) := ((fun y0 : nat => (Peano.le (S x0) y0) \/ (Peano.le y0 (S x0))) x1) -> (fun y0 : nat => (Peano.le (S x0) y0) \/ (Peano.le y0 (S x0))) (S x1).
Definition term61 (x0 : nat) (x1 : nat) := imp ((Peano.le (S x1) x0) \/ (Peano.le x0 (S x1))).
Definition term32 := and ((Peano.le (NUMERAL 0) (NUMERAL 0)) \/ (Peano.le (NUMERAL 0) (NUMERAL 0))).
Definition term52 (x0 : nat) := (((fun y0 : nat => (Peano.le (S x0) y0) \/ (Peano.le y0 (S x0))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Peano.le (S x0) y1) \/ (Peano.le y1 (S x0))) y0) -> (fun y1 : nat => (Peano.le (S x0) y1) \/ (Peano.le y1 (S x0))) (S y0))) -> forall y0 : nat, (fun y1 : nat => (Peano.le (S x0) y1) \/ (Peano.le y1 (S x0))) y0.
Definition term27 := (((fun y0 : nat => (Peano.le (NUMERAL 0) y0) \/ (Peano.le y0 (NUMERAL 0))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Peano.le (NUMERAL 0) y1) \/ (Peano.le y1 (NUMERAL 0))) y0) -> (fun y1 : nat => (Peano.le (NUMERAL 0) y1) \/ (Peano.le y1 (NUMERAL 0))) (S y0))) -> forall y0 : nat, (fun y1 : nat => (Peano.le (NUMERAL 0) y1) \/ (Peano.le y1 (NUMERAL 0))) y0.
Definition term1 := (((fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (Peano.le y1 y2) \/ (Peano.le y2 y1)) y0) -> (fun y1 : nat => forall y2 : nat, (Peano.le y1 y2) \/ (Peano.le y2 y1)) (S y0))) -> forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Peano.le y1 y2) \/ (Peano.le y2 y1)) y0.
Definition term0 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term59 (x0 : nat) (x1 : nat) := (Peano.le (S x1) x0) \/ (Peano.le x0 (S x1)).
Definition term72 (x0 : nat) := imp (((fun y0 : nat => (Peano.le (S x0) y0) \/ (Peano.le y0 (S x0))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Peano.le (S x0) y1) \/ (Peano.le y1 (S x0))) y0) -> (fun y1 : nat => (Peano.le (S x0) y1) \/ (Peano.le y1 (S x0))) (S y0))).
Definition term47 := imp (((fun y0 : nat => (Peano.le (NUMERAL 0) y0) \/ (Peano.le y0 (NUMERAL 0))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Peano.le (NUMERAL 0) y1) \/ (Peano.le y1 (NUMERAL 0))) y0) -> (fun y1 : nat => (Peano.le (NUMERAL 0) y1) \/ (Peano.le y1 (NUMERAL 0))) (S y0))).
Definition term21 := imp (((fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (Peano.le y1 y2) \/ (Peano.le y2 y1)) y0) -> (fun y1 : nat => forall y2 : nat, (Peano.le y1 y2) \/ (Peano.le y2 y1)) (S y0))).
Definition term85 (x0 : nat) := (Peano.le (S x0) (NUMERAL 0)) \/ True.
Definition term54 (x0 : nat) := (fun y0 : nat => (Peano.le (S x0) y0) \/ (Peano.le y0 (S x0))) (NUMERAL 0).
Definition term62 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le (S x0) y0) \/ (Peano.le y0 (S x0))) (S x1).
Definition term40 (x0 : nat) := ((Peano.le (NUMERAL 0) x0) \/ (Peano.le x0 (NUMERAL 0))) -> (Peano.le (NUMERAL 0) (S x0)) \/ (Peano.le (S x0) (NUMERAL 0)).
Definition term68 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => (Peano.le (S x0) y1) \/ (Peano.le y1 (S x0))) y0) -> (fun y1 : nat => (Peano.le (S x0) y1) \/ (Peano.le y1 (S x0))) (S y0).
Definition term43 := forall y0 : nat, ((fun y1 : nat => (Peano.le (NUMERAL 0) y1) \/ (Peano.le y1 (NUMERAL 0))) y0) -> (fun y1 : nat => (Peano.le (NUMERAL 0) y1) \/ (Peano.le y1 (NUMERAL 0))) (S y0).
Definition term17 := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (Peano.le y1 y2) \/ (Peano.le y2 y1)) y0) -> (fun y1 : nat => forall y2 : nat, (Peano.le y1 y2) \/ (Peano.le y2 y1)) (S y0).
Definition term2 := fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0).
Definition term8 (x0 : nat) := forall y0 : nat, (Peano.le x0 y0) \/ (Peano.le y0 x0).
Definition term42 := fun y0 : nat => ((Peano.le (NUMERAL 0) y0) \/ (Peano.le y0 (NUMERAL 0))) -> (Peano.le (NUMERAL 0) (S y0)) \/ (Peano.le (S y0) (NUMERAL 0)).
Definition term57 (x0 : nat) := and ((Peano.le (S x0) (NUMERAL 0)) \/ (Peano.le (NUMERAL 0) (S x0))).
Definition term34 (x0 : nat) := (Peano.le (NUMERAL 0) x0) \/ (Peano.le x0 (NUMERAL 0)).
Definition term56 (x0 : nat) := and ((fun y0 : nat => (Peano.le (S x0) y0) \/ (Peano.le y0 (S x0))) (NUMERAL 0)).
Definition term31 := and ((fun y0 : nat => (Peano.le (NUMERAL 0) y0) \/ (Peano.le y0 (NUMERAL 0))) (NUMERAL 0)).
Definition term93 (x0 : nat) (x1 : nat) := or (Peano.le x0 x1).
Definition term28 := fun y0 : nat => (Peano.le (NUMERAL 0) y0) \/ (Peano.le y0 (NUMERAL 0)).
Definition term46 := ((Peano.le (NUMERAL 0) (NUMERAL 0)) \/ (Peano.le (NUMERAL 0) (NUMERAL 0))) /\ (forall y0 : nat, ((Peano.le (NUMERAL 0) y0) \/ (Peano.le y0 (NUMERAL 0))) -> (Peano.le (NUMERAL 0) (S y0)) \/ (Peano.le (S y0) (NUMERAL 0))).
Definition term81 (x0 : nat) := or (Peano.le (NUMERAL 0) (S x0)).
Definition term5 := and ((fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) (NUMERAL 0)).
Definition term10 (x0 : nat) := imp (forall y0 : nat, (Peano.le x0 y0) \/ (Peano.le y0 x0)).
Definition term6 := and (forall y0 : nat, (Peano.le (NUMERAL 0) y0) \/ (Peano.le y0 (NUMERAL 0))).
Definition term55 (x0 : nat) := (Peano.le (S x0) (NUMERAL 0)) \/ (Peano.le (NUMERAL 0) (S x0)).
Definition term11 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) (S x0).
Definition term3 := (fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) (NUMERAL 0).
Definition term66 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => (Peano.le (S x0) y1) \/ (Peano.le y1 (S x0))) y0) -> (fun y1 : nat => (Peano.le (S x0) y1) \/ (Peano.le y1 (S x0))) (S y0).
Definition term41 := fun y0 : nat => ((fun y1 : nat => (Peano.le (NUMERAL 0) y1) \/ (Peano.le y1 (NUMERAL 0))) y0) -> (fun y1 : nat => (Peano.le (NUMERAL 0) y1) \/ (Peano.le y1 (NUMERAL 0))) (S y0).
Definition term88 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le (S x0) (S y0)) = (Peano.le x0 y0)) x1.
Definition term22 := imp ((forall y0 : nat, (Peano.le (NUMERAL 0) y0) \/ (Peano.le y0 (NUMERAL 0))) /\ (forall y0 : nat, (forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) -> forall y1 : nat, (Peano.le (S y0) y1) \/ (Peano.le y1 (S y0)))).
Definition term74 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (Peano.le (S x0) y1) \/ (Peano.le y1 (S x0))) y0.
Definition term49 := fun y0 : nat => (fun y1 : nat => (Peano.le (NUMERAL 0) y1) \/ (Peano.le y1 (NUMERAL 0))) y0.
Definition term25 := forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0).
Definition term76 (x0 : nat) := (((Peano.le (S x0) (NUMERAL 0)) \/ (Peano.le (NUMERAL 0) (S x0))) /\ (forall y0 : nat, ((Peano.le (S x0) y0) \/ (Peano.le y0 (S x0))) -> (Peano.le (S x0) (S y0)) \/ (Peano.le (S y0) (S x0)))) -> forall y0 : nat, (Peano.le (S x0) y0) \/ (Peano.le y0 (S x0)).
Definition term51 := (((Peano.le (NUMERAL 0) (NUMERAL 0)) \/ (Peano.le (NUMERAL 0) (NUMERAL 0))) /\ (forall y0 : nat, ((Peano.le (NUMERAL 0) y0) \/ (Peano.le y0 (NUMERAL 0))) -> (Peano.le (NUMERAL 0) (S y0)) \/ (Peano.le (S y0) (NUMERAL 0)))) -> forall y0 : nat, (Peano.le (NUMERAL 0) y0) \/ (Peano.le y0 (NUMERAL 0)).
Definition term30 := (Peano.le (NUMERAL 0) (NUMERAL 0)) \/ (Peano.le (NUMERAL 0) (NUMERAL 0)).
Definition term60 (x0 : nat) (x1 : nat) := imp ((fun y0 : nat => (Peano.le (S x0) y0) \/ (Peano.le y0 (S x0))) x1).
Definition term78 (x0 : nat) := Peano.le (NUMERAL 0) x0.
Definition term91 (x0 : nat) (x1 : nat) := (Peano.le x1 x0) \/ (Peano.le x0 x1).
Definition term58 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le (S x0) y0) \/ (Peano.le y0 (S x0))) x1.
Definition term53 (x0 : nat) := fun y0 : nat => (Peano.le (S x0) y0) \/ (Peano.le y0 (S x0)).
Definition term92 (x0 : nat) (x1 : nat) := or (Peano.le (S x0) (S x1)).
Definition term16 := fun y0 : nat => (forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) -> forall y1 : nat, (Peano.le (S y0) y1) \/ (Peano.le y1 (S y0)).
Definition term15 := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, (Peano.le y1 y2) \/ (Peano.le y2 y1)) y0) -> (fun y1 : nat => forall y2 : nat, (Peano.le y1 y2) \/ (Peano.le y2 y1)) (S y0).
Definition term20 := (forall y0 : nat, (Peano.le (NUMERAL 0) y0) \/ (Peano.le y0 (NUMERAL 0))) /\ (forall y0 : nat, (forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) -> forall y1 : nat, (Peano.le (S y0) y1) \/ (Peano.le y1 (S y0))).
Definition term83 (x0 : nat) := True \/ (Peano.le (S x0) (NUMERAL 0)).
Definition term23 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (Peano.le y1 y2) \/ (Peano.le y2 y1)) y0.
Definition term86 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (S y0) (S y1)) = (Peano.le y0 y1)) x0.
Definition term7 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) x0.
Definition term19 := ((fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (Peano.le y1 y2) \/ (Peano.le y2 y1)) y0) -> (fun y1 : nat => forall y2 : nat, (Peano.le y1 y2) \/ (Peano.le y2 y1)) (S y0)).
Definition term80 (x0 : nat) := Peano.le (NUMERAL 0) (S x0).
Definition term29 := (fun y0 : nat => (Peano.le (NUMERAL 0) y0) \/ (Peano.le y0 (NUMERAL 0))) (NUMERAL 0).
Definition term12 (x0 : nat) := forall y0 : nat, (Peano.le (S x0) y0) \/ (Peano.le y0 (S x0)).
Definition term73 (x0 : nat) := imp (((Peano.le (S x0) (NUMERAL 0)) \/ (Peano.le (NUMERAL 0) (S x0))) /\ (forall y0 : nat, ((Peano.le (S x0) y0) \/ (Peano.le y0 (S x0))) -> (Peano.le (S x0) (S y0)) \/ (Peano.le (S y0) (S x0)))).
Definition term48 := imp (((Peano.le (NUMERAL 0) (NUMERAL 0)) \/ (Peano.le (NUMERAL 0) (NUMERAL 0))) /\ (forall y0 : nat, ((Peano.le (NUMERAL 0) y0) \/ (Peano.le y0 (NUMERAL 0))) -> (Peano.le (NUMERAL 0) (S y0)) \/ (Peano.le (S y0) (NUMERAL 0)))).
Definition term65 (x0 : nat) (x1 : nat) := ((Peano.le (S x1) x0) \/ (Peano.le x0 (S x1))) -> (Peano.le (S x1) (S x0)) \/ (Peano.le (S x0) (S x1)).
Definition term69 (x0 : nat) := forall y0 : nat, ((Peano.le (S x0) y0) \/ (Peano.le y0 (S x0))) -> (Peano.le (S x0) (S y0)) \/ (Peano.le (S y0) (S x0)).
Definition term44 := forall y0 : nat, ((Peano.le (NUMERAL 0) y0) \/ (Peano.le y0 (NUMERAL 0))) -> (Peano.le (NUMERAL 0) (S y0)) \/ (Peano.le (S y0) (NUMERAL 0)).
Definition term67 (x0 : nat) := fun y0 : nat => ((Peano.le (S x0) y0) \/ (Peano.le y0 (S x0))) -> (Peano.le (S x0) (S y0)) \/ (Peano.le (S y0) (S x0)).
Definition term89 (x0 : nat) (x1 : nat) := Peano.le (S x0) (S x1).
Definition term35 (x0 : nat) := imp ((fun y0 : nat => (Peano.le (NUMERAL 0) y0) \/ (Peano.le y0 (NUMERAL 0))) x0).
Definition term13 (x0 : nat) := ((fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) x0) -> (fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) (S x0).
Definition term24 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Peano.le y1 y2) \/ (Peano.le y2 y1)) y0.
Definition term33 (x0 : nat) := (fun y0 : nat => (Peano.le (NUMERAL 0) y0) \/ (Peano.le y0 (NUMERAL 0))) x0.
Definition term79 := Peano.le (NUMERAL 0) (NUMERAL 0).
Definition term14 (x0 : nat) := (forall y0 : nat, (Peano.le x0 y0) \/ (Peano.le y0 x0)) -> forall y0 : nat, (Peano.le (S x0) y0) \/ (Peano.le y0 (S x0)).
