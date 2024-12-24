Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term3 (x0 : nat) := ~ ((NUMERAL 0) = (S x0)).
Definition term82 (x0 : nat) (x1 : nat) := ~ ((Peano.le (S x1) x0) /\ (Peano.lt x0 (S x1))).
Definition term131 (x0 : nat) := Peano.lt (NUMERAL 0) (S x0).
Definition term57 (x0 : nat) := ~ ((Peano.le (NUMERAL 0) x0) /\ (Peano.lt x0 (NUMERAL 0))).
Definition term123 (x0 : nat) := False \/ (Peano.le (NUMERAL 0) x0).
Definition term98 (x0 : nat) := forall y0 : nat, (fun y1 : nat => ~ ((Peano.le (S x0) y1) /\ (Peano.lt y1 (S x0)))) y0.
Definition term73 := forall y0 : nat, (fun y1 : nat => ~ ((Peano.le (NUMERAL 0) y1) /\ (Peano.lt y1 (NUMERAL 0)))) y0.
Definition term21 (x0 : nat) := (fun y0 : nat => (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) x0.
Definition term132 (x0 : nat) := ((NUMERAL 0) = x0) \/ (Peano.lt (NUMERAL 0) x0).
Definition term78 (x0 : nat) := ~ ((Peano.le (S x0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) (S x0))).
Definition term111 (x0 : nat) (x1 : nat) := (Peano.le x1 x0) /\ (Peano.lt x0 x1).
Definition term129 (x0 : nat) := Peano.le (S x0) (NUMERAL 0).
Definition term99 (x0 : nat) := ((~ ((Peano.le (S x0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) (S x0)))) /\ (forall y0 : nat, (~ ((Peano.le (S x0) y0) /\ (Peano.lt y0 (S x0)))) -> ~ ((Peano.le (S x0) (S y0)) /\ (Peano.lt (S y0) (S x0))))) -> forall y0 : nat, ~ ((Peano.le (S x0) y0) /\ (Peano.lt y0 (S x0))).
Definition term74 := ((~ ((Peano.le (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) (NUMERAL 0)))) /\ (forall y0 : nat, (~ ((Peano.le (NUMERAL 0) y0) /\ (Peano.lt y0 (NUMERAL 0)))) -> ~ ((Peano.le (NUMERAL 0) (S y0)) /\ (Peano.lt (S y0) (NUMERAL 0))))) -> forall y0 : nat, ~ ((Peano.le (NUMERAL 0) y0) /\ (Peano.lt y0 (NUMERAL 0))).
Definition term41 := forall y0 : nat, (forall y1 : nat, ~ ((Peano.le y0 y1) /\ (Peano.lt y1 y0))) -> forall y1 : nat, ~ ((Peano.le (S y0) y1) /\ (Peano.lt y1 (S y0))).
Definition term93 (x0 : nat) := ((fun y0 : nat => ~ ((Peano.le (S x0) y0) /\ (Peano.lt y0 (S x0)))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ~ ((Peano.le (S x0) y1) /\ (Peano.lt y1 (S x0)))) y0) -> (fun y1 : nat => ~ ((Peano.le (S x0) y1) /\ (Peano.lt y1 (S x0)))) (S y0)).
Definition term68 := ((fun y0 : nat => ~ ((Peano.le (NUMERAL 0) y0) /\ (Peano.lt y0 (NUMERAL 0)))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ~ ((Peano.le (NUMERAL 0) y1) /\ (Peano.lt y1 (NUMERAL 0)))) y0) -> (fun y1 : nat => ~ ((Peano.le (NUMERAL 0) y1) /\ (Peano.lt y1 (NUMERAL 0)))) (S y0)).
Definition term116 := and (Peano.le (NUMERAL 0) (NUMERAL 0)).
Definition term105 (x0 : nat) := forall y0 : nat, (Peano.le (S x0) (S y0)) = (Peano.le x0 y0).
Definition term101 (x0 : nat) := forall y0 : nat, (Peano.lt (S x0) (S y0)) = (Peano.lt x0 y0).
Definition term49 := ((forall y0 : nat, ~ ((Peano.le (NUMERAL 0) y0) /\ (Peano.lt y0 (NUMERAL 0)))) /\ (forall y0 : nat, (forall y1 : nat, ~ ((Peano.le y0 y1) /\ (Peano.lt y1 y0))) -> forall y1 : nat, ~ ((Peano.le (S y0) y1) /\ (Peano.lt y1 (S y0))))) -> forall y0 : nat, forall y1 : nat, ~ ((Peano.le y0 y1) /\ (Peano.lt y1 y0)).
Definition term32 (x0 : nat) := imp ((fun y0 : nat => forall y1 : nat, ~ ((Peano.le y0 y1) /\ (Peano.lt y1 y0))) x0).
Definition term51 := fun y0 : nat => ~ ((Peano.le (NUMERAL 0) y0) /\ (Peano.lt y0 (NUMERAL 0))).
Definition term29 := and (forall y0 : nat, ~ ((Peano.le (NUMERAL 0) y0) /\ (Peano.lt y0 (NUMERAL 0)))).
Definition term62 (x0 : nat) := ((fun y0 : nat => ~ ((Peano.le (NUMERAL 0) y0) /\ (Peano.lt y0 (NUMERAL 0)))) x0) -> (fun y0 : nat => ~ ((Peano.le (NUMERAL 0) y0) /\ (Peano.lt y0 (NUMERAL 0)))) (S x0).
Definition term94 (x0 : nat) := (~ ((Peano.le (S x0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) (S x0)))) /\ (forall y0 : nat, (~ ((Peano.le (S x0) y0) /\ (Peano.lt y0 (S x0)))) -> ~ ((Peano.le (S x0) (S y0)) /\ (Peano.lt (S y0) (S x0)))).
Definition term69 := (~ ((Peano.le (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) (NUMERAL 0)))) /\ (forall y0 : nat, (~ ((Peano.le (NUMERAL 0) y0) /\ (Peano.lt y0 (NUMERAL 0)))) -> ~ ((Peano.le (NUMERAL 0) (S y0)) /\ (Peano.lt (S y0) (NUMERAL 0)))).
Definition term75 (x0 : nat) := (((fun y0 : nat => ~ ((Peano.le (S x0) y0) /\ (Peano.lt y0 (S x0)))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ~ ((Peano.le (S x0) y1) /\ (Peano.lt y1 (S x0)))) y0) -> (fun y1 : nat => ~ ((Peano.le (S x0) y1) /\ (Peano.lt y1 (S x0)))) (S y0))) -> forall y0 : nat, (fun y1 : nat => ~ ((Peano.le (S x0) y1) /\ (Peano.lt y1 (S x0)))) y0.
Definition term50 := (((fun y0 : nat => ~ ((Peano.le (NUMERAL 0) y0) /\ (Peano.lt y0 (NUMERAL 0)))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ~ ((Peano.le (NUMERAL 0) y1) /\ (Peano.lt y1 (NUMERAL 0)))) y0) -> (fun y1 : nat => ~ ((Peano.le (NUMERAL 0) y1) /\ (Peano.lt y1 (NUMERAL 0)))) (S y0))) -> forall y0 : nat, (fun y1 : nat => ~ ((Peano.le (NUMERAL 0) y1) /\ (Peano.lt y1 (NUMERAL 0)))) y0.
Definition term24 := (((fun y0 : nat => forall y1 : nat, ~ ((Peano.le y0 y1) /\ (Peano.lt y1 y0))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ~ ((Peano.le y1 y2) /\ (Peano.lt y2 y1))) y0) -> (fun y1 : nat => forall y2 : nat, ~ ((Peano.le y1 y2) /\ (Peano.lt y2 y1))) (S y0))) -> forall y0 : nat, (fun y1 : nat => forall y2 : nat, ~ ((Peano.le y1 y2) /\ (Peano.lt y2 y1))) y0.
Definition term80 (x0 : nat) := and (~ ((Peano.le (S x0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) (S x0)))).
Definition term11 := forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False.
Definition term23 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term95 (x0 : nat) := imp (((fun y0 : nat => ~ ((Peano.le (S x0) y0) /\ (Peano.lt y0 (S x0)))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ~ ((Peano.le (S x0) y1) /\ (Peano.lt y1 (S x0)))) y0) -> (fun y1 : nat => ~ ((Peano.le (S x0) y1) /\ (Peano.lt y1 (S x0)))) (S y0))).
Definition term70 := imp (((fun y0 : nat => ~ ((Peano.le (NUMERAL 0) y0) /\ (Peano.lt y0 (NUMERAL 0)))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ~ ((Peano.le (NUMERAL 0) y1) /\ (Peano.lt y1 (NUMERAL 0)))) y0) -> (fun y1 : nat => ~ ((Peano.le (NUMERAL 0) y1) /\ (Peano.lt y1 (NUMERAL 0)))) (S y0))).
Definition term44 := imp (((fun y0 : nat => forall y1 : nat, ~ ((Peano.le y0 y1) /\ (Peano.lt y1 y0))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ~ ((Peano.le y1 y2) /\ (Peano.lt y2 y1))) y0) -> (fun y1 : nat => forall y2 : nat, ~ ((Peano.le y1 y2) /\ (Peano.lt y2 y1))) (S y0))).
Definition term92 (x0 : nat) := forall y0 : nat, (~ ((Peano.le (S x0) y0) /\ (Peano.lt y0 (S x0)))) -> ~ ((Peano.le (S x0) (S y0)) /\ (Peano.lt (S y0) (S x0))).
Definition term67 := forall y0 : nat, (~ ((Peano.le (NUMERAL 0) y0) /\ (Peano.lt y0 (NUMERAL 0)))) -> ~ ((Peano.le (NUMERAL 0) (S y0)) /\ (Peano.lt (S y0) (NUMERAL 0))).
Definition term125 (x0 : nat) := and (Peano.le (NUMERAL 0) x0).
Definition term120 (x0 : nat) := ((NUMERAL 0) = (S x0)) \/ (Peano.le (NUMERAL 0) x0).
Definition term83 (x0 : nat) (x1 : nat) := imp ((fun y0 : nat => ~ ((Peano.le (S x0) y0) /\ (Peano.lt y0 (S x0)))) x1).
Definition term91 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => ~ ((Peano.le (S x0) y1) /\ (Peano.lt y1 (S x0)))) y0) -> (fun y1 : nat => ~ ((Peano.le (S x0) y1) /\ (Peano.lt y1 (S x0)))) (S y0).
Definition term66 := forall y0 : nat, ((fun y1 : nat => ~ ((Peano.le (NUMERAL 0) y1) /\ (Peano.lt y1 (NUMERAL 0)))) y0) -> (fun y1 : nat => ~ ((Peano.le (NUMERAL 0) y1) /\ (Peano.lt y1 (NUMERAL 0)))) (S y0).
Definition term40 := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ~ ((Peano.le y1 y2) /\ (Peano.lt y2 y1))) y0) -> (fun y1 : nat => forall y2 : nat, ~ ((Peano.le y1 y2) /\ (Peano.lt y2 y1))) (S y0).
Definition term10 (x0 : nat) (x1 : nat) := (x0 = x1) \/ (Peano.lt x0 x1).
Definition term79 (x0 : nat) := and ((fun y0 : nat => ~ ((Peano.le (S x0) y0) /\ (Peano.lt y0 (S x0)))) (NUMERAL 0)).
Definition term54 := and ((fun y0 : nat => ~ ((Peano.le (NUMERAL 0) y0) /\ (Peano.lt y0 (NUMERAL 0)))) (NUMERAL 0)).
Definition term86 (x0 : nat) (x1 : nat) := ~ ((Peano.le (S x1) (S x0)) /\ (Peano.lt (S x0) (S x1))).
Definition term58 (x0 : nat) := imp ((fun y0 : nat => ~ ((Peano.le (NUMERAL 0) y0) /\ (Peano.lt y0 (NUMERAL 0)))) x0).
Definition term118 := (Peano.le (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) (NUMERAL 0)).
Definition term12 (x0 : nat) := (fun y0 : nat => (Peano.lt y0 (NUMERAL 0)) = False) x0.
Definition term28 := and ((fun y0 : nat => forall y1 : nat, ~ ((Peano.le y0 y1) /\ (Peano.lt y1 y0))) (NUMERAL 0)).
Definition term34 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ~ ((Peano.le y0 y1) /\ (Peano.lt y1 y0))) (S x0).
Definition term33 (x0 : nat) := imp (forall y0 : nat, ~ ((Peano.le x0 y0) /\ (Peano.lt y0 x0))).
Definition term31 (x0 : nat) := forall y0 : nat, ~ ((Peano.le x0 y0) /\ (Peano.lt y0 x0)).
Definition term117 := Peano.lt (NUMERAL 0) (NUMERAL 0).
Definition term26 := (fun y0 : nat => forall y1 : nat, ~ ((Peano.le y0 y1) /\ (Peano.lt y1 y0))) (NUMERAL 0).
Definition term106 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le (S x0) (S y0)) = (Peano.le x0 y0)) x1.
Definition term126 (x0 : nat) := Peano.lt (S x0) (NUMERAL 0).
Definition term45 := imp ((forall y0 : nat, ~ ((Peano.le (NUMERAL 0) y0) /\ (Peano.lt y0 (NUMERAL 0)))) /\ (forall y0 : nat, (forall y1 : nat, ~ ((Peano.le y0 y1) /\ (Peano.lt y1 y0))) -> forall y1 : nat, ~ ((Peano.le (S y0) y1) /\ (Peano.lt y1 (S y0))))).
Definition term85 (x0 : nat) (x1 : nat) := (fun y0 : nat => ~ ((Peano.le (S x0) y0) /\ (Peano.lt y0 (S x0)))) (S x1).
Definition term90 (x0 : nat) := fun y0 : nat => (~ ((Peano.le (S x0) y0) /\ (Peano.lt y0 (S x0)))) -> ~ ((Peano.le (S x0) (S y0)) /\ (Peano.lt (S y0) (S x0))).
Definition term65 := fun y0 : nat => (~ ((Peano.le (NUMERAL 0) y0) /\ (Peano.lt y0 (NUMERAL 0)))) -> ~ ((Peano.le (NUMERAL 0) (S y0)) /\ (Peano.lt (S y0) (NUMERAL 0))).
Definition term48 := forall y0 : nat, forall y1 : nat, ~ ((Peano.le y0 y1) /\ (Peano.lt y1 y0)).
Definition term14 := forall y0 : nat, forall y1 : nat, (Peano.le y0 (S y1)) = ((y0 = (S y1)) \/ (Peano.le y0 y1)).
Definition term5 := forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)).
Definition term9 (x0 : nat) (x1 : nat) := Peano.lt x0 (S x1).
Definition term77 (x0 : nat) := (fun y0 : nat => ~ ((Peano.le (S x0) y0) /\ (Peano.lt y0 (S x0)))) (NUMERAL 0).
Definition term52 := (fun y0 : nat => ~ ((Peano.le (NUMERAL 0) y0) /\ (Peano.lt y0 (NUMERAL 0)))) (NUMERAL 0).
Definition term63 (x0 : nat) := (~ ((Peano.le (NUMERAL 0) x0) /\ (Peano.lt x0 (NUMERAL 0)))) -> ~ ((Peano.le (NUMERAL 0) (S x0)) /\ (Peano.lt (S x0) (NUMERAL 0))).
Definition term35 (x0 : nat) := forall y0 : nat, ~ ((Peano.le (S x0) y0) /\ (Peano.lt y0 (S x0))).
Definition term27 := forall y0 : nat, ~ ((Peano.le (NUMERAL 0) y0) /\ (Peano.lt y0 (NUMERAL 0))).
Definition term76 (x0 : nat) := fun y0 : nat => ~ ((Peano.le (S x0) y0) /\ (Peano.lt y0 (S x0))).
Definition term122 (x0 : nat) := Peano.le (NUMERAL 0) x0.
Definition term43 := (forall y0 : nat, ~ ((Peano.le (NUMERAL 0) y0) /\ (Peano.lt y0 (NUMERAL 0)))) /\ (forall y0 : nat, (forall y1 : nat, ~ ((Peano.le y0 y1) /\ (Peano.lt y1 y0))) -> forall y1 : nat, ~ ((Peano.le (S y0) y1) /\ (Peano.lt y1 (S y0)))).
Definition term16 (x0 : nat) := forall y0 : nat, (Peano.le x0 (S y0)) = ((x0 = (S y0)) \/ (Peano.le x0 y0)).
Definition term7 (x0 : nat) := forall y0 : nat, (Peano.lt x0 (S y0)) = ((x0 = y0) \/ (Peano.lt x0 y0)).
Definition term114 (x0 : nat) (x1 : nat) := (Peano.le (S x1) (S x0)) /\ (Peano.lt (S x0) (S x1)).
Definition term121 (x0 : nat) := or ((NUMERAL 0) = (S x0)).
Definition term1 (x0 : nat) := ~ ((S x0) = (NUMERAL 0)).
Definition term59 (x0 : nat) := imp (~ ((Peano.le (NUMERAL 0) x0) /\ (Peano.lt x0 (NUMERAL 0)))).
Definition term102 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt (S x0) (S y0)) = (Peano.lt x0 y0)) x1.
Definition term109 (x0 : nat) (x1 : nat) := ~ ((Peano.le x1 x0) /\ (Peano.lt x0 x1)).
Definition term38 := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, ~ ((Peano.le y1 y2) /\ (Peano.lt y2 y1))) y0) -> (fun y1 : nat => forall y2 : nat, ~ ((Peano.le y1 y2) /\ (Peano.lt y2 y1))) (S y0).
Definition term8 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt x0 (S y0)) = ((x0 = y0) \/ (Peano.lt x0 y0))) x1.
Definition term130 (x0 : nat) := and (Peano.le (S x0) (NUMERAL 0)).
Definition term13 (x0 : nat) := Peano.lt x0 (NUMERAL 0).
Definition term19 (x0 : nat) (x1 : nat) := (x0 = (S x1)) \/ (Peano.le x0 x1).
Definition term46 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, ~ ((Peano.le y1 y2) /\ (Peano.lt y2 y1))) y0.
Definition term87 (x0 : nat) (x1 : nat) := ((fun y0 : nat => ~ ((Peano.le (S x0) y0) /\ (Peano.lt y0 (S x0)))) x1) -> (fun y0 : nat => ~ ((Peano.le (S x0) y0) /\ (Peano.lt y0 (S x0)))) (S x1).
Definition term104 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (S y0) (S y1)) = (Peano.le y0 y1)) x0.
Definition term100 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt (S y0) (S y1)) = (Peano.lt y0 y1)) x0.
Definition term15 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y0 (S y1)) = ((y0 = (S y1)) \/ (Peano.le y0 y1))) x0.
Definition term6 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1))) x0.
Definition term0 (x0 : nat) := (fun y0 : nat => ~ ((S y0) = (NUMERAL 0))) x0.
Definition term81 (x0 : nat) (x1 : nat) := (fun y0 : nat => ~ ((Peano.le (S x0) y0) /\ (Peano.lt y0 (S x0)))) x1.
Definition term56 (x0 : nat) := (fun y0 : nat => ~ ((Peano.le (NUMERAL 0) y0) /\ (Peano.lt y0 (NUMERAL 0)))) x0.
Definition term134 (x0 : nat) := False /\ (((NUMERAL 0) = x0) \/ (Peano.lt (NUMERAL 0) x0)).
Definition term42 := ((fun y0 : nat => forall y1 : nat, ~ ((Peano.le y0 y1) /\ (Peano.lt y1 y0))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ~ ((Peano.le y1 y2) /\ (Peano.lt y2 y1))) y0) -> (fun y1 : nat => forall y2 : nat, ~ ((Peano.le y1 y2) /\ (Peano.lt y2 y1))) (S y0)).
Definition term96 (x0 : nat) := imp ((~ ((Peano.le (S x0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) (S x0)))) /\ (forall y0 : nat, (~ ((Peano.le (S x0) y0) /\ (Peano.lt y0 (S x0)))) -> ~ ((Peano.le (S x0) (S y0)) /\ (Peano.lt (S y0) (S x0))))).
Definition term71 := imp ((~ ((Peano.le (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) (NUMERAL 0)))) /\ (forall y0 : nat, (~ ((Peano.le (NUMERAL 0) y0) /\ (Peano.lt y0 (NUMERAL 0)))) -> ~ ((Peano.le (NUMERAL 0) (S y0)) /\ (Peano.lt (S y0) (NUMERAL 0))))).
Definition term119 (x0 : nat) := Peano.le (NUMERAL 0) (S x0).
Definition term61 (x0 : nat) := ~ ((Peano.le (NUMERAL 0) (S x0)) /\ (Peano.lt (S x0) (NUMERAL 0))).
Definition term103 (x0 : nat) (x1 : nat) := Peano.lt (S x0) (S x1).
Definition term128 (x0 : nat) := (Peano.le (NUMERAL 0) x0) /\ False.
Definition term20 := forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0)).
Definition term2 (x0 : nat) := (~ ((S x0) = (NUMERAL 0))) -> ((S x0) = (NUMERAL 0)) = False.
Definition term4 (x0 : nat) := (~ ((NUMERAL 0) = (S x0))) -> ((NUMERAL 0) = (S x0)) = False.
Definition term97 (x0 : nat) := fun y0 : nat => (fun y1 : nat => ~ ((Peano.le (S x0) y1) /\ (Peano.lt y1 (S x0)))) y0.
Definition term72 := fun y0 : nat => (fun y1 : nat => ~ ((Peano.le (NUMERAL 0) y1) /\ (Peano.lt y1 (NUMERAL 0)))) y0.
Definition term30 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ~ ((Peano.le y0 y1) /\ (Peano.lt y1 y0))) x0.
Definition term37 (x0 : nat) := (forall y0 : nat, ~ ((Peano.le x0 y0) /\ (Peano.lt y0 x0))) -> forall y0 : nat, ~ ((Peano.le (S x0) y0) /\ (Peano.lt y0 (S x0))).
Definition term25 := fun y0 : nat => forall y1 : nat, ~ ((Peano.le y0 y1) /\ (Peano.lt y1 y0)).
Definition term60 (x0 : nat) := (fun y0 : nat => ~ ((Peano.le (NUMERAL 0) y0) /\ (Peano.lt y0 (NUMERAL 0)))) (S x0).
Definition term127 (x0 : nat) := (Peano.le (NUMERAL 0) (S x0)) /\ (Peano.lt (S x0) (NUMERAL 0)).
Definition term124 (x0 : nat) := and (Peano.le (NUMERAL 0) (S x0)).
Definition term55 := and (~ ((Peano.le (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) (NUMERAL 0)))).
Definition term88 (x0 : nat) (x1 : nat) := (~ ((Peano.le (S x1) x0) /\ (Peano.lt x0 (S x1)))) -> ~ ((Peano.le (S x1) (S x0)) /\ (Peano.lt (S x0) (S x1))).
Definition term108 (x0 : nat) (x1 : nat) := (fun y0 : nat => ~ ((Peano.le x0 y0) /\ (Peano.lt y0 x0))) x1.
Definition term107 (x0 : nat) (x1 : nat) := Peano.le (S x0) (S x1).
Definition term39 := fun y0 : nat => (forall y1 : nat, ~ ((Peano.le y0 y1) /\ (Peano.lt y1 y0))) -> forall y1 : nat, ~ ((Peano.le (S y0) y1) /\ (Peano.lt y1 (S y0))).
Definition term84 (x0 : nat) (x1 : nat) := imp (~ ((Peano.le (S x1) x0) /\ (Peano.lt x0 (S x1)))).
Definition term89 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => ~ ((Peano.le (S x0) y1) /\ (Peano.lt y1 (S x0)))) y0) -> (fun y1 : nat => ~ ((Peano.le (S x0) y1) /\ (Peano.lt y1 (S x0)))) (S y0).
Definition term64 := fun y0 : nat => ((fun y1 : nat => ~ ((Peano.le (NUMERAL 0) y1) /\ (Peano.lt y1 (NUMERAL 0)))) y0) -> (fun y1 : nat => ~ ((Peano.le (NUMERAL 0) y1) /\ (Peano.lt y1 (NUMERAL 0)))) (S y0).
Definition term36 (x0 : nat) := ((fun y0 : nat => forall y1 : nat, ~ ((Peano.le y0 y1) /\ (Peano.lt y1 y0))) x0) -> (fun y0 : nat => forall y1 : nat, ~ ((Peano.le y0 y1) /\ (Peano.lt y1 y0))) (S x0).
Definition term47 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, ~ ((Peano.le y1 y2) /\ (Peano.lt y2 y1))) y0.
Definition term22 (x0 : nat) := Peano.le x0 (NUMERAL 0).
Definition term112 (x0 : nat) (x1 : nat) := and (Peano.le (S x0) (S x1)).
Definition term17 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le x0 (S y0)) = ((x0 = (S y0)) \/ (Peano.le x0 y0))) x1.
Definition term18 (x0 : nat) (x1 : nat) := Peano.le x0 (S x1).
Definition term133 (x0 : nat) := (Peano.le (S x0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) (S x0)).
Definition term110 (x0 : nat) (x1 : nat) := (~ ((Peano.le x1 x0) /\ (Peano.lt x0 x1))) -> ((Peano.le x1 x0) /\ (Peano.lt x0 x1)) = False.
Definition term113 (x0 : nat) (x1 : nat) := and (Peano.le x0 x1).
Definition term53 := ~ ((Peano.le (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) (NUMERAL 0))).
Definition term115 := Peano.le (NUMERAL 0) (NUMERAL 0).
