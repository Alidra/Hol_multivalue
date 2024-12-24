Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term107 (x0 : nat) := and (Peano.lt (S x0) (NUMERAL 0)).
Definition term97 (x0 : nat) (x1 : nat) := and (Peano.lt (S x0) (S x1)).
Definition term68 (x0 : nat) (x1 : nat) := ~ ((Peano.lt (S x1) x0) /\ (Peano.lt x0 (S x1))).
Definition term100 (x0 : nat) := Peano.lt (NUMERAL 0) (S x0).
Definition term43 (x0 : nat) := ~ ((Peano.lt (NUMERAL 0) x0) /\ (Peano.lt x0 (NUMERAL 0))).
Definition term84 (x0 : nat) := forall y0 : nat, (fun y1 : nat => ~ ((Peano.lt (S x0) y1) /\ (Peano.lt y1 (S x0)))) y0.
Definition term59 := forall y0 : nat, (fun y1 : nat => ~ ((Peano.lt (NUMERAL 0) y1) /\ (Peano.lt y1 (NUMERAL 0)))) y0.
Definition term101 (x0 : nat) := ((NUMERAL 0) = x0) \/ (Peano.lt (NUMERAL 0) x0).
Definition term64 (x0 : nat) := ~ ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) (S x0))).
Definition term85 (x0 : nat) := ((~ ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) (S x0)))) /\ (forall y0 : nat, (~ ((Peano.lt (S x0) y0) /\ (Peano.lt y0 (S x0)))) -> ~ ((Peano.lt (S x0) (S y0)) /\ (Peano.lt (S y0) (S x0))))) -> forall y0 : nat, ~ ((Peano.lt (S x0) y0) /\ (Peano.lt y0 (S x0))).
Definition term60 := ((~ ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) (NUMERAL 0)))) /\ (forall y0 : nat, (~ ((Peano.lt (NUMERAL 0) y0) /\ (Peano.lt y0 (NUMERAL 0)))) -> ~ ((Peano.lt (NUMERAL 0) (S y0)) /\ (Peano.lt (S y0) (NUMERAL 0))))) -> forall y0 : nat, ~ ((Peano.lt (NUMERAL 0) y0) /\ (Peano.lt y0 (NUMERAL 0))).
Definition term27 := forall y0 : nat, (forall y1 : nat, ~ ((Peano.lt y0 y1) /\ (Peano.lt y1 y0))) -> forall y1 : nat, ~ ((Peano.lt (S y0) y1) /\ (Peano.lt y1 (S y0))).
Definition term79 (x0 : nat) := ((fun y0 : nat => ~ ((Peano.lt (S x0) y0) /\ (Peano.lt y0 (S x0)))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ~ ((Peano.lt (S x0) y1) /\ (Peano.lt y1 (S x0)))) y0) -> (fun y1 : nat => ~ ((Peano.lt (S x0) y1) /\ (Peano.lt y1 (S x0)))) (S y0)).
Definition term54 := ((fun y0 : nat => ~ ((Peano.lt (NUMERAL 0) y0) /\ (Peano.lt y0 (NUMERAL 0)))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ~ ((Peano.lt (NUMERAL 0) y1) /\ (Peano.lt y1 (NUMERAL 0)))) y0) -> (fun y1 : nat => ~ ((Peano.lt (NUMERAL 0) y1) /\ (Peano.lt y1 (NUMERAL 0)))) (S y0)).
Definition term90 (x0 : nat) := forall y0 : nat, (Peano.lt (S x0) (S y0)) = (Peano.lt x0 y0).
Definition term35 := ((forall y0 : nat, ~ ((Peano.lt (NUMERAL 0) y0) /\ (Peano.lt y0 (NUMERAL 0)))) /\ (forall y0 : nat, (forall y1 : nat, ~ ((Peano.lt y0 y1) /\ (Peano.lt y1 y0))) -> forall y1 : nat, ~ ((Peano.lt (S y0) y1) /\ (Peano.lt y1 (S y0))))) -> forall y0 : nat, forall y1 : nat, ~ ((Peano.lt y0 y1) /\ (Peano.lt y1 y0)).
Definition term96 (x0 : nat) (x1 : nat) := (Peano.lt x1 x0) /\ (Peano.lt x0 x1).
Definition term18 (x0 : nat) := imp ((fun y0 : nat => forall y1 : nat, ~ ((Peano.lt y0 y1) /\ (Peano.lt y1 y0))) x0).
Definition term88 := ~ (Peano.lt (NUMERAL 0) (NUMERAL 0)).
Definition term37 := fun y0 : nat => ~ ((Peano.lt (NUMERAL 0) y0) /\ (Peano.lt y0 (NUMERAL 0))).
Definition term15 := and (forall y0 : nat, ~ ((Peano.lt (NUMERAL 0) y0) /\ (Peano.lt y0 (NUMERAL 0)))).
Definition term48 (x0 : nat) := ((fun y0 : nat => ~ ((Peano.lt (NUMERAL 0) y0) /\ (Peano.lt y0 (NUMERAL 0)))) x0) -> (fun y0 : nat => ~ ((Peano.lt (NUMERAL 0) y0) /\ (Peano.lt y0 (NUMERAL 0)))) (S x0).
Definition term80 (x0 : nat) := (~ ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) (S x0)))) /\ (forall y0 : nat, (~ ((Peano.lt (S x0) y0) /\ (Peano.lt y0 (S x0)))) -> ~ ((Peano.lt (S x0) (S y0)) /\ (Peano.lt (S y0) (S x0)))).
Definition term55 := (~ ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) (NUMERAL 0)))) /\ (forall y0 : nat, (~ ((Peano.lt (NUMERAL 0) y0) /\ (Peano.lt y0 (NUMERAL 0)))) -> ~ ((Peano.lt (NUMERAL 0) (S y0)) /\ (Peano.lt (S y0) (NUMERAL 0)))).
Definition term61 (x0 : nat) := (((fun y0 : nat => ~ ((Peano.lt (S x0) y0) /\ (Peano.lt y0 (S x0)))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ~ ((Peano.lt (S x0) y1) /\ (Peano.lt y1 (S x0)))) y0) -> (fun y1 : nat => ~ ((Peano.lt (S x0) y1) /\ (Peano.lt y1 (S x0)))) (S y0))) -> forall y0 : nat, (fun y1 : nat => ~ ((Peano.lt (S x0) y1) /\ (Peano.lt y1 (S x0)))) y0.
Definition term36 := (((fun y0 : nat => ~ ((Peano.lt (NUMERAL 0) y0) /\ (Peano.lt y0 (NUMERAL 0)))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ~ ((Peano.lt (NUMERAL 0) y1) /\ (Peano.lt y1 (NUMERAL 0)))) y0) -> (fun y1 : nat => ~ ((Peano.lt (NUMERAL 0) y1) /\ (Peano.lt y1 (NUMERAL 0)))) (S y0))) -> forall y0 : nat, (fun y1 : nat => ~ ((Peano.lt (NUMERAL 0) y1) /\ (Peano.lt y1 (NUMERAL 0)))) y0.
Definition term10 := (((fun y0 : nat => forall y1 : nat, ~ ((Peano.lt y0 y1) /\ (Peano.lt y1 y0))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ~ ((Peano.lt y1 y2) /\ (Peano.lt y2 y1))) y0) -> (fun y1 : nat => forall y2 : nat, ~ ((Peano.lt y1 y2) /\ (Peano.lt y2 y1))) (S y0))) -> forall y0 : nat, (fun y1 : nat => forall y2 : nat, ~ ((Peano.lt y1 y2) /\ (Peano.lt y2 y1))) y0.
Definition term66 (x0 : nat) := and (~ ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) (S x0)))).
Definition term6 := forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False.
Definition term9 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term81 (x0 : nat) := imp (((fun y0 : nat => ~ ((Peano.lt (S x0) y0) /\ (Peano.lt y0 (S x0)))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ~ ((Peano.lt (S x0) y1) /\ (Peano.lt y1 (S x0)))) y0) -> (fun y1 : nat => ~ ((Peano.lt (S x0) y1) /\ (Peano.lt y1 (S x0)))) (S y0))).
Definition term56 := imp (((fun y0 : nat => ~ ((Peano.lt (NUMERAL 0) y0) /\ (Peano.lt y0 (NUMERAL 0)))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ~ ((Peano.lt (NUMERAL 0) y1) /\ (Peano.lt y1 (NUMERAL 0)))) y0) -> (fun y1 : nat => ~ ((Peano.lt (NUMERAL 0) y1) /\ (Peano.lt y1 (NUMERAL 0)))) (S y0))).
Definition term30 := imp (((fun y0 : nat => forall y1 : nat, ~ ((Peano.lt y0 y1) /\ (Peano.lt y1 y0))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ~ ((Peano.lt y1 y2) /\ (Peano.lt y2 y1))) y0) -> (fun y1 : nat => forall y2 : nat, ~ ((Peano.lt y1 y2) /\ (Peano.lt y2 y1))) (S y0))).
Definition term78 (x0 : nat) := forall y0 : nat, (~ ((Peano.lt (S x0) y0) /\ (Peano.lt y0 (S x0)))) -> ~ ((Peano.lt (S x0) (S y0)) /\ (Peano.lt (S y0) (S x0))).
Definition term53 := forall y0 : nat, (~ ((Peano.lt (NUMERAL 0) y0) /\ (Peano.lt y0 (NUMERAL 0)))) -> ~ ((Peano.lt (NUMERAL 0) (S y0)) /\ (Peano.lt (S y0) (NUMERAL 0))).
Definition term69 (x0 : nat) (x1 : nat) := imp ((fun y0 : nat => ~ ((Peano.lt (S x0) y0) /\ (Peano.lt y0 (S x0)))) x1).
Definition term77 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => ~ ((Peano.lt (S x0) y1) /\ (Peano.lt y1 (S x0)))) y0) -> (fun y1 : nat => ~ ((Peano.lt (S x0) y1) /\ (Peano.lt y1 (S x0)))) (S y0).
Definition term52 := forall y0 : nat, ((fun y1 : nat => ~ ((Peano.lt (NUMERAL 0) y1) /\ (Peano.lt y1 (NUMERAL 0)))) y0) -> (fun y1 : nat => ~ ((Peano.lt (NUMERAL 0) y1) /\ (Peano.lt y1 (NUMERAL 0)))) (S y0).
Definition term26 := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ~ ((Peano.lt y1 y2) /\ (Peano.lt y2 y1))) y0) -> (fun y1 : nat => forall y2 : nat, ~ ((Peano.lt y1 y2) /\ (Peano.lt y2 y1))) (S y0).
Definition term5 (x0 : nat) (x1 : nat) := (x0 = x1) \/ (Peano.lt x0 x1).
Definition term65 (x0 : nat) := and ((fun y0 : nat => ~ ((Peano.lt (S x0) y0) /\ (Peano.lt y0 (S x0)))) (NUMERAL 0)).
Definition term40 := and ((fun y0 : nat => ~ ((Peano.lt (NUMERAL 0) y0) /\ (Peano.lt y0 (NUMERAL 0)))) (NUMERAL 0)).
Definition term72 (x0 : nat) (x1 : nat) := ~ ((Peano.lt (S x1) (S x0)) /\ (Peano.lt (S x0) (S x1))).
Definition term44 (x0 : nat) := imp ((fun y0 : nat => ~ ((Peano.lt (NUMERAL 0) y0) /\ (Peano.lt y0 (NUMERAL 0)))) x0).
Definition term7 (x0 : nat) := (fun y0 : nat => (Peano.lt y0 (NUMERAL 0)) = False) x0.
Definition term14 := and ((fun y0 : nat => forall y1 : nat, ~ ((Peano.lt y0 y1) /\ (Peano.lt y1 y0))) (NUMERAL 0)).
Definition term20 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ~ ((Peano.lt y0 y1) /\ (Peano.lt y1 y0))) (S x0).
Definition term19 (x0 : nat) := imp (forall y0 : nat, ~ ((Peano.lt x0 y0) /\ (Peano.lt y0 x0))).
Definition term17 (x0 : nat) := forall y0 : nat, ~ ((Peano.lt x0 y0) /\ (Peano.lt y0 x0)).
Definition term87 := Peano.lt (NUMERAL 0) (NUMERAL 0).
Definition term12 := (fun y0 : nat => forall y1 : nat, ~ ((Peano.lt y0 y1) /\ (Peano.lt y1 y0))) (NUMERAL 0).
Definition term104 (x0 : nat) := Peano.lt (S x0) (NUMERAL 0).
Definition term31 := imp ((forall y0 : nat, ~ ((Peano.lt (NUMERAL 0) y0) /\ (Peano.lt y0 (NUMERAL 0)))) /\ (forall y0 : nat, (forall y1 : nat, ~ ((Peano.lt y0 y1) /\ (Peano.lt y1 y0))) -> forall y1 : nat, ~ ((Peano.lt (S y0) y1) /\ (Peano.lt y1 (S y0))))).
Definition term71 (x0 : nat) (x1 : nat) := (fun y0 : nat => ~ ((Peano.lt (S x0) y0) /\ (Peano.lt y0 (S x0)))) (S x1).
Definition term76 (x0 : nat) := fun y0 : nat => (~ ((Peano.lt (S x0) y0) /\ (Peano.lt y0 (S x0)))) -> ~ ((Peano.lt (S x0) (S y0)) /\ (Peano.lt (S y0) (S x0))).
Definition term51 := fun y0 : nat => (~ ((Peano.lt (NUMERAL 0) y0) /\ (Peano.lt y0 (NUMERAL 0)))) -> ~ ((Peano.lt (NUMERAL 0) (S y0)) /\ (Peano.lt (S y0) (NUMERAL 0))).
Definition term34 := forall y0 : nat, forall y1 : nat, ~ ((Peano.lt y0 y1) /\ (Peano.lt y1 y0)).
Definition term0 := forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)).
Definition term105 (x0 : nat) := (Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (S x0) (NUMERAL 0)).
Definition term4 (x0 : nat) (x1 : nat) := Peano.lt x0 (S x1).
Definition term63 (x0 : nat) := (fun y0 : nat => ~ ((Peano.lt (S x0) y0) /\ (Peano.lt y0 (S x0)))) (NUMERAL 0).
Definition term38 := (fun y0 : nat => ~ ((Peano.lt (NUMERAL 0) y0) /\ (Peano.lt y0 (NUMERAL 0)))) (NUMERAL 0).
Definition term49 (x0 : nat) := (~ ((Peano.lt (NUMERAL 0) x0) /\ (Peano.lt x0 (NUMERAL 0)))) -> ~ ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (S x0) (NUMERAL 0))).
Definition term106 (x0 : nat) := (((NUMERAL 0) = x0) \/ (Peano.lt (NUMERAL 0) x0)) /\ False.
Definition term21 (x0 : nat) := forall y0 : nat, ~ ((Peano.lt (S x0) y0) /\ (Peano.lt y0 (S x0))).
Definition term13 := forall y0 : nat, ~ ((Peano.lt (NUMERAL 0) y0) /\ (Peano.lt y0 (NUMERAL 0))).
Definition term62 (x0 : nat) := fun y0 : nat => ~ ((Peano.lt (S x0) y0) /\ (Peano.lt y0 (S x0))).
Definition term29 := (forall y0 : nat, ~ ((Peano.lt (NUMERAL 0) y0) /\ (Peano.lt y0 (NUMERAL 0)))) /\ (forall y0 : nat, (forall y1 : nat, ~ ((Peano.lt y0 y1) /\ (Peano.lt y1 y0))) -> forall y1 : nat, ~ ((Peano.lt (S y0) y1) /\ (Peano.lt y1 (S y0)))).
Definition term2 (x0 : nat) := forall y0 : nat, (Peano.lt x0 (S y0)) = ((x0 = y0) \/ (Peano.lt x0 y0)).
Definition term45 (x0 : nat) := imp (~ ((Peano.lt (NUMERAL 0) x0) /\ (Peano.lt x0 (NUMERAL 0)))).
Definition term91 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt (S x0) (S y0)) = (Peano.lt x0 y0)) x1.
Definition term103 (x0 : nat) := and (((NUMERAL 0) = x0) \/ (Peano.lt (NUMERAL 0) x0)).
Definition term94 (x0 : nat) (x1 : nat) := ~ ((Peano.lt x1 x0) /\ (Peano.lt x0 x1)).
Definition term99 (x0 : nat) (x1 : nat) := (Peano.lt (S x1) (S x0)) /\ (Peano.lt (S x0) (S x1)).
Definition term24 := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, ~ ((Peano.lt y1 y2) /\ (Peano.lt y2 y1))) y0) -> (fun y1 : nat => forall y2 : nat, ~ ((Peano.lt y1 y2) /\ (Peano.lt y2 y1))) (S y0).
Definition term98 (x0 : nat) (x1 : nat) := and (Peano.lt x0 x1).
Definition term3 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt x0 (S y0)) = ((x0 = y0) \/ (Peano.lt x0 y0))) x1.
Definition term8 (x0 : nat) := Peano.lt x0 (NUMERAL 0).
Definition term32 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, ~ ((Peano.lt y1 y2) /\ (Peano.lt y2 y1))) y0.
Definition term73 (x0 : nat) (x1 : nat) := ((fun y0 : nat => ~ ((Peano.lt (S x0) y0) /\ (Peano.lt y0 (S x0)))) x1) -> (fun y0 : nat => ~ ((Peano.lt (S x0) y0) /\ (Peano.lt y0 (S x0)))) (S x1).
Definition term89 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt (S y0) (S y1)) = (Peano.lt y0 y1)) x0.
Definition term1 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1))) x0.
Definition term67 (x0 : nat) (x1 : nat) := (fun y0 : nat => ~ ((Peano.lt (S x0) y0) /\ (Peano.lt y0 (S x0)))) x1.
Definition term42 (x0 : nat) := (fun y0 : nat => ~ ((Peano.lt (NUMERAL 0) y0) /\ (Peano.lt y0 (NUMERAL 0)))) x0.
Definition term109 (x0 : nat) := False /\ (((NUMERAL 0) = x0) \/ (Peano.lt (NUMERAL 0) x0)).
Definition term28 := ((fun y0 : nat => forall y1 : nat, ~ ((Peano.lt y0 y1) /\ (Peano.lt y1 y0))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ~ ((Peano.lt y1 y2) /\ (Peano.lt y2 y1))) y0) -> (fun y1 : nat => forall y2 : nat, ~ ((Peano.lt y1 y2) /\ (Peano.lt y2 y1))) (S y0)).
Definition term82 (x0 : nat) := imp ((~ ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) (S x0)))) /\ (forall y0 : nat, (~ ((Peano.lt (S x0) y0) /\ (Peano.lt y0 (S x0)))) -> ~ ((Peano.lt (S x0) (S y0)) /\ (Peano.lt (S y0) (S x0))))).
Definition term57 := imp ((~ ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) (NUMERAL 0)))) /\ (forall y0 : nat, (~ ((Peano.lt (NUMERAL 0) y0) /\ (Peano.lt y0 (NUMERAL 0)))) -> ~ ((Peano.lt (NUMERAL 0) (S y0)) /\ (Peano.lt (S y0) (NUMERAL 0))))).
Definition term47 (x0 : nat) := ~ ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (S x0) (NUMERAL 0))).
Definition term86 := (Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) (NUMERAL 0)).
Definition term92 (x0 : nat) (x1 : nat) := Peano.lt (S x0) (S x1).
Definition term102 (x0 : nat) := and (Peano.lt (NUMERAL 0) (S x0)).
Definition term108 (x0 : nat) := (Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) (S x0)).
Definition term83 (x0 : nat) := fun y0 : nat => (fun y1 : nat => ~ ((Peano.lt (S x0) y1) /\ (Peano.lt y1 (S x0)))) y0.
Definition term58 := fun y0 : nat => (fun y1 : nat => ~ ((Peano.lt (NUMERAL 0) y1) /\ (Peano.lt y1 (NUMERAL 0)))) y0.
Definition term16 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ~ ((Peano.lt y0 y1) /\ (Peano.lt y1 y0))) x0.
Definition term23 (x0 : nat) := (forall y0 : nat, ~ ((Peano.lt x0 y0) /\ (Peano.lt y0 x0))) -> forall y0 : nat, ~ ((Peano.lt (S x0) y0) /\ (Peano.lt y0 (S x0))).
Definition term11 := fun y0 : nat => forall y1 : nat, ~ ((Peano.lt y0 y1) /\ (Peano.lt y1 y0)).
Definition term46 (x0 : nat) := (fun y0 : nat => ~ ((Peano.lt (NUMERAL 0) y0) /\ (Peano.lt y0 (NUMERAL 0)))) (S x0).
Definition term41 := and (~ ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) (NUMERAL 0)))).
Definition term74 (x0 : nat) (x1 : nat) := (~ ((Peano.lt (S x1) x0) /\ (Peano.lt x0 (S x1)))) -> ~ ((Peano.lt (S x1) (S x0)) /\ (Peano.lt (S x0) (S x1))).
Definition term93 (x0 : nat) (x1 : nat) := (fun y0 : nat => ~ ((Peano.lt x0 y0) /\ (Peano.lt y0 x0))) x1.
Definition term25 := fun y0 : nat => (forall y1 : nat, ~ ((Peano.lt y0 y1) /\ (Peano.lt y1 y0))) -> forall y1 : nat, ~ ((Peano.lt (S y0) y1) /\ (Peano.lt y1 (S y0))).
Definition term70 (x0 : nat) (x1 : nat) := imp (~ ((Peano.lt (S x1) x0) /\ (Peano.lt x0 (S x1)))).
Definition term75 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => ~ ((Peano.lt (S x0) y1) /\ (Peano.lt y1 (S x0)))) y0) -> (fun y1 : nat => ~ ((Peano.lt (S x0) y1) /\ (Peano.lt y1 (S x0)))) (S y0).
Definition term50 := fun y0 : nat => ((fun y1 : nat => ~ ((Peano.lt (NUMERAL 0) y1) /\ (Peano.lt y1 (NUMERAL 0)))) y0) -> (fun y1 : nat => ~ ((Peano.lt (NUMERAL 0) y1) /\ (Peano.lt y1 (NUMERAL 0)))) (S y0).
Definition term22 (x0 : nat) := ((fun y0 : nat => forall y1 : nat, ~ ((Peano.lt y0 y1) /\ (Peano.lt y1 y0))) x0) -> (fun y0 : nat => forall y1 : nat, ~ ((Peano.lt y0 y1) /\ (Peano.lt y1 y0))) (S x0).
Definition term33 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, ~ ((Peano.lt y1 y2) /\ (Peano.lt y2 y1))) y0.
Definition term95 (x0 : nat) (x1 : nat) := (~ ((Peano.lt x1 x0) /\ (Peano.lt x0 x1))) -> ((Peano.lt x1 x0) /\ (Peano.lt x0 x1)) = False.
Definition term39 := ~ ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) (NUMERAL 0))).
