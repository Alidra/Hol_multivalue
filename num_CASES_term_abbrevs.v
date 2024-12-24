Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term13 (x0 : nat) := ((fun y0 : nat => (y0 = (NUMERAL 0)) \/ (exists y1 : nat, y0 = (S y1))) x0) -> (fun y0 : nat => (y0 = (NUMERAL 0)) \/ (exists y1 : nat, y0 = (S y1))) (S x0).
Definition term44 (x0 : nat) := ~ ((NUMERAL 0) = (S x0)).
Definition term55 := (~ False) -> False.
Definition term34 (x0 : Prop) := ~ (~ x0).
Definition term4 := ((NUMERAL 0) = (NUMERAL 0)) \/ (exists y0 : nat, (NUMERAL 0) = (S y0)).
Definition term76 (x0 : nat) := forall y0 : nat, ~ ((S x0) = (S y0)).
Definition term47 := forall y0 : nat, ~ ((NUMERAL 0) = (S y0)).
Definition term16 := fun y0 : nat => ((y0 = (NUMERAL 0)) \/ (exists y1 : nat, y0 = (S y1))) -> ((S y0) = (NUMERAL 0)) \/ (exists y1 : nat, (S y0) = (S y1)).
Definition term57 (x0 : nat) := ~ (((S x0) = (NUMERAL 0)) \/ (exists y0 : nat, (S x0) = (S y0))).
Definition term29 := ~ (((NUMERAL 0) = (NUMERAL 0)) \/ (exists y0 : nat, (NUMERAL 0) = (S y0))).
Definition term2 := fun y0 : nat => (y0 = (NUMERAL 0)) \/ (exists y1 : nat, y0 = (S y1)).
Definition term52 := (~ ((NUMERAL 0) = (NUMERAL 0))) -> (NUMERAL 0) = (NUMERAL 0).
Definition term27 (x0 : Prop) := (~ x0) -> False.
Definition term23 := fun y0 : nat => (fun y1 : nat => (y1 = (NUMERAL 0)) \/ (exists y2 : nat, y1 = (S y2))) y0.
Definition term24 := forall y0 : nat, (fun y1 : nat => (y1 = (NUMERAL 0)) \/ (exists y2 : nat, y1 = (S y2))) y0.
Definition term83 (x0 : nat) (x1 : nat) := ((S x0) = (S x1)) -> False.
Definition term80 (x0 : nat) (x1 : nat) := (fun y0 : nat => ~ ((S x0) = (S y0))) x1.
Definition term19 := ((fun y0 : nat => (y0 = (NUMERAL 0)) \/ (exists y1 : nat, y0 = (S y1))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (y1 = (NUMERAL 0)) \/ (exists y2 : nat, y1 = (S y2))) y0) -> (fun y1 : nat => (y1 = (NUMERAL 0)) \/ (exists y2 : nat, y1 = (S y2))) (S y0)).
Definition term22 := imp ((((NUMERAL 0) = (NUMERAL 0)) \/ (exists y0 : nat, (NUMERAL 0) = (S y0))) /\ (forall y0 : nat, ((y0 = (NUMERAL 0)) \/ (exists y1 : nat, y0 = (S y1))) -> ((S y0) = (NUMERAL 0)) \/ (exists y1 : nat, (S y0) = (S y1)))).
Definition term26 := ((((NUMERAL 0) = (NUMERAL 0)) \/ (exists y0 : nat, (NUMERAL 0) = (S y0))) /\ (forall y0 : nat, ((y0 = (NUMERAL 0)) \/ (exists y1 : nat, y0 = (S y1))) -> ((S y0) = (NUMERAL 0)) \/ (exists y1 : nat, (S y0) = (S y1)))) -> forall y0 : nat, (y0 = (NUMERAL 0)) \/ (exists y1 : nat, y0 = (S y1)).
Definition term53 (x0 : Prop) := (~ x0) -> x0.
Definition term1 := (((fun y0 : nat => (y0 = (NUMERAL 0)) \/ (exists y1 : nat, y0 = (S y1))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (y1 = (NUMERAL 0)) \/ (exists y2 : nat, y1 = (S y2))) y0) -> (fun y1 : nat => (y1 = (NUMERAL 0)) \/ (exists y2 : nat, y1 = (S y2))) (S y0))) -> forall y0 : nat, (fun y1 : nat => (y1 = (NUMERAL 0)) \/ (exists y2 : nat, y1 = (S y2))) y0.
Definition term48 := and (~ ((NUMERAL 0) = (NUMERAL 0))).
Definition term79 (x0 : nat) := (~ ((S x0) = (NUMERAL 0))) /\ (forall y0 : nat, ~ ((S x0) = (S y0))).
Definition term50 := (~ ((NUMERAL 0) = (NUMERAL 0))) /\ (forall y0 : nat, ~ ((NUMERAL 0) = (S y0))).
Definition term0 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term21 := imp (((fun y0 : nat => (y0 = (NUMERAL 0)) \/ (exists y1 : nat, y0 = (S y1))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (y1 = (NUMERAL 0)) \/ (exists y2 : nat, y1 = (S y2))) y0) -> (fun y1 : nat => (y1 = (NUMERAL 0)) \/ (exists y2 : nat, y1 = (S y2))) (S y0))).
Definition term71 (x0 : nat) (x1 : nat) := (fun y0 : nat => (S x0) = (S y0)) x1.
Definition term51 := ~ ((NUMERAL 0) = (NUMERAL 0)).
Definition term17 := forall y0 : nat, ((fun y1 : nat => (y1 = (NUMERAL 0)) \/ (exists y2 : nat, y1 = (S y2))) y0) -> (fun y1 : nat => (y1 = (NUMERAL 0)) \/ (exists y2 : nat, y1 = (S y2))) (S y0).
Definition term77 (x0 : nat) := and (~ ((S x0) = (NUMERAL 0))).
Definition term54 := ((NUMERAL 0) = (NUMERAL 0)) -> False.
Definition term43 (x0 : nat) := ~ ((fun y0 : nat => (NUMERAL 0) = (S y0)) x0).
Definition term65 := forall y0 : nat, ((S y0) = (NUMERAL 0)) \/ (exists y1 : nat, (S y0) = (S y1)).
Definition term25 := forall y0 : nat, (y0 = (NUMERAL 0)) \/ (exists y1 : nat, y0 = (S y1)).
Definition term5 := and ((fun y0 : nat => (y0 = (NUMERAL 0)) \/ (exists y1 : nat, y0 = (S y1))) (NUMERAL 0)).
Definition term46 := fun y0 : nat => ~ ((NUMERAL 0) = (S y0)).
Definition term15 := fun y0 : nat => ((fun y1 : nat => (y1 = (NUMERAL 0)) \/ (exists y2 : nat, y1 = (S y2))) y0) -> (fun y1 : nat => (y1 = (NUMERAL 0)) \/ (exists y2 : nat, y1 = (S y2))) (S y0).
Definition term61 (x0 : nat) := ~ (~ (((S x0) = (NUMERAL 0)) \/ (exists y0 : nat, (S x0) = (S y0)))).
Definition term33 := ~ (~ (((NUMERAL 0) = (NUMERAL 0)) \/ (exists y0 : nat, (NUMERAL 0) = (S y0)))).
Definition term58 (x0 : nat) := ((~ (((S x0) = (NUMERAL 0)) \/ (exists y0 : nat, (S x0) = (S y0)))) -> False) -> (~ (((S x0) = (NUMERAL 0)) \/ (exists y0 : nat, (S x0) = (S y0)))) -> False.
Definition term30 := ((~ (((NUMERAL 0) = (NUMERAL 0)) \/ (exists y0 : nat, (NUMERAL 0) = (S y0)))) -> False) -> (~ (((NUMERAL 0) = (NUMERAL 0)) \/ (exists y0 : nat, (NUMERAL 0) = (S y0)))) -> False.
Definition term73 (x0 : nat) (x1 : nat) := ~ ((S x0) = (S x1)).
Definition term38 (x0 : nat -> Prop) := ~ (ex x0).
Definition term42 (x0 : nat) := (fun y0 : nat => (NUMERAL 0) = (S y0)) x0.
Definition term85 (x0 : nat) := (fun y0 : nat => (~ (((S y0) = (NUMERAL 0)) \/ (exists y1 : nat, (S y0) = (S y1)))) -> False) x0.
Definition term11 (x0 : nat) := (fun y0 : nat => (y0 = (NUMERAL 0)) \/ (exists y1 : nat, y0 = (S y1))) (S x0).
Definition term39 (x0 : nat -> Prop) := forall y0 : nat, ~ (x0 y0).
Definition term10 (x0 : nat) := imp ((x0 = (NUMERAL 0)) \/ (exists y0 : nat, x0 = (S y0))).
Definition term62 := fun y0 : nat => (~ (((S y0) = (NUMERAL 0)) \/ (exists y1 : nat, (S y0) = (S y1)))) -> False.
Definition term14 (x0 : nat) := ((x0 = (NUMERAL 0)) \/ (exists y0 : nat, x0 = (S y0))) -> ((S x0) = (NUMERAL 0)) \/ (exists y0 : nat, (S x0) = (S y0)).
Definition term64 := forall y0 : nat, (~ (((S y0) = (NUMERAL 0)) \/ (exists y1 : nat, (S y0) = (S y1)))) -> False.
Definition term59 (x0 : nat) := (((~ (((S x0) = (NUMERAL 0)) \/ (exists y0 : nat, (S x0) = (S y0)))) -> False) -> (~ (((S x0) = (NUMERAL 0)) \/ (exists y0 : nat, (S x0) = (S y0)))) -> False) -> (~ (((S x0) = (NUMERAL 0)) \/ (exists y0 : nat, (S x0) = (S y0)))) -> False.
Definition term31 := (((~ (((NUMERAL 0) = (NUMERAL 0)) \/ (exists y0 : nat, (NUMERAL 0) = (S y0)))) -> False) -> (~ (((NUMERAL 0) = (NUMERAL 0)) \/ (exists y0 : nat, (NUMERAL 0) = (S y0)))) -> False) -> (~ (((NUMERAL 0) = (NUMERAL 0)) \/ (exists y0 : nat, (NUMERAL 0) = (S y0)))) -> False.
Definition term81 (x0 : nat) := (~ ((S x0) = (S x0))) -> (S x0) = (S x0).
Definition term68 (x0 : nat) := or ((S x0) = (NUMERAL 0)).
Definition term70 (x0 : nat) := forall y0 : nat, ~ ((fun y1 : nat => (S x0) = (S y1)) y0).
Definition term41 := forall y0 : nat, ~ ((fun y1 : nat => (NUMERAL 0) = (S y1)) y0).
Definition term20 := (((NUMERAL 0) = (NUMERAL 0)) \/ (exists y0 : nat, (NUMERAL 0) = (S y0))) /\ (forall y0 : nat, ((y0 = (NUMERAL 0)) \/ (exists y1 : nat, y0 = (S y1))) -> ((S y0) = (NUMERAL 0)) \/ (exists y1 : nat, (S y0) = (S y1))).
Definition term6 := and (((NUMERAL 0) = (NUMERAL 0)) \/ (exists y0 : nat, (NUMERAL 0) = (S y0))).
Definition term67 (x0 : nat) := exists y0 : nat, (S x0) = (S y0).
Definition term78 (x0 : nat) := (~ ((S x0) = (NUMERAL 0))) /\ (~ (exists y0 : nat, (S x0) = (S y0))).
Definition term49 := (~ ((NUMERAL 0) = (NUMERAL 0))) /\ (~ (exists y0 : nat, (NUMERAL 0) = (S y0))).
Definition term7 (x0 : nat) := (fun y0 : nat => (y0 = (NUMERAL 0)) \/ (exists y1 : nat, y0 = (S y1))) x0.
Definition term84 (x0 : nat) := ((S x0) = (S x0)) -> False.
Definition term8 (x0 : nat) := (x0 = (NUMERAL 0)) \/ (exists y0 : nat, x0 = (S y0)).
Definition term12 (x0 : nat) := ((S x0) = (NUMERAL 0)) \/ (exists y0 : nat, (S x0) = (S y0)).
Definition term74 (x0 : nat) := fun y0 : nat => ~ ((fun y1 : nat => (S x0) = (S y1)) y0).
Definition term45 := fun y0 : nat => ~ ((fun y1 : nat => (NUMERAL 0) = (S y1)) y0).
Definition term3 := (fun y0 : nat => (y0 = (NUMERAL 0)) \/ (exists y1 : nat, y0 = (S y1))) (NUMERAL 0).
Definition term35 := fun y0 : nat => (NUMERAL 0) = (S y0).
Definition term72 (x0 : nat) (x1 : nat) := ~ ((fun y0 : nat => (S x0) = (S y0)) x1).
Definition term63 := fun y0 : nat => ((S y0) = (NUMERAL 0)) \/ (exists y1 : nat, (S y0) = (S y1)).
Definition term60 (x0 : nat) := (((~ (((S x0) = (NUMERAL 0)) \/ (exists y0 : nat, (S x0) = (S y0)))) -> False) -> (~ (((S x0) = (NUMERAL 0)) \/ (exists y0 : nat, (S x0) = (S y0)))) -> False) -> ((~ (((S x0) = (NUMERAL 0)) \/ (exists y0 : nat, (S x0) = (S y0)))) -> False) -> (~ (((S x0) = (NUMERAL 0)) \/ (exists y0 : nat, (S x0) = (S y0)))) -> False.
Definition term32 := (((~ (((NUMERAL 0) = (NUMERAL 0)) \/ (exists y0 : nat, (NUMERAL 0) = (S y0)))) -> False) -> (~ (((NUMERAL 0) = (NUMERAL 0)) \/ (exists y0 : nat, (NUMERAL 0) = (S y0)))) -> False) -> ((~ (((NUMERAL 0) = (NUMERAL 0)) \/ (exists y0 : nat, (NUMERAL 0) = (S y0)))) -> False) -> (~ (((NUMERAL 0) = (NUMERAL 0)) \/ (exists y0 : nat, (NUMERAL 0) = (S y0)))) -> False.
Definition term82 (x0 : nat) := ~ ((S x0) = (S x0)).
Definition term56 (x0 : nat) := (~ (((S x0) = (NUMERAL 0)) \/ (exists y0 : nat, (S x0) = (S y0)))) -> False.
Definition term28 := (~ (((NUMERAL 0) = (NUMERAL 0)) \/ (exists y0 : nat, (NUMERAL 0) = (S y0)))) -> False.
Definition term66 (x0 : nat) := fun y0 : nat => (S x0) = (S y0).
Definition term9 (x0 : nat) := imp ((fun y0 : nat => (y0 = (NUMERAL 0)) \/ (exists y1 : nat, y0 = (S y1))) x0).
Definition term37 := or ((NUMERAL 0) = (NUMERAL 0)).
Definition term75 (x0 : nat) := fun y0 : nat => ~ ((S x0) = (S y0)).
Definition term36 := exists y0 : nat, (NUMERAL 0) = (S y0).
Definition term18 := forall y0 : nat, ((y0 = (NUMERAL 0)) \/ (exists y1 : nat, y0 = (S y1))) -> ((S y0) = (NUMERAL 0)) \/ (exists y1 : nat, (S y0) = (S y1)).
Definition term69 (x0 : nat) := ~ (exists y0 : nat, (S x0) = (S y0)).
Definition term40 := ~ (exists y0 : nat, (NUMERAL 0) = (S y0)).
