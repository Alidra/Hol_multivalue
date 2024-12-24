Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term62 (x0 : nat) := (fun y0 : nat => (~ (Peano.lt (NUMERAL 0) y0)) = (Peano.le y0 (NUMERAL 0))) (S x0).
Definition term138 (x0 : nat) := ((fun y0 : nat => ((NUMERAL 0) = y0) \/ (Peano.lt (NUMERAL 0) y0)) x0) -> (fun y0 : nat => ((NUMERAL 0) = y0) \/ (Peano.lt (NUMERAL 0) y0)) (S x0).
Definition term65 (x0 : nat) := ((fun y0 : nat => (~ (Peano.lt (NUMERAL 0) y0)) = (Peano.le y0 (NUMERAL 0))) x0) -> (fun y0 : nat => (~ (Peano.lt (NUMERAL 0) y0)) = (Peano.le y0 (NUMERAL 0))) (S x0).
Definition term3 (x0 : nat) := ~ ((NUMERAL 0) = (S x0)).
Definition term1 (x0 : nat) := Peano.lt (NUMERAL 0) (S x0).
Definition term58 (x0 : nat) := (fun y0 : nat => (~ (Peano.lt (NUMERAL 0) y0)) = (Peano.le y0 (NUMERAL 0))) x0.
Definition term103 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (~ (Peano.lt (S x0) y1)) = (Peano.le y1 (S x0))) y0.
Definition term75 := fun y0 : nat => (fun y1 : nat => (~ (Peano.lt (NUMERAL 0) y1)) = (Peano.le y1 (NUMERAL 0))) y0.
Definition term22 (x0 : nat) := (fun y0 : nat => (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) x0.
Definition term119 (x0 : nat) := ((NUMERAL 0) = x0) \/ (Peano.lt (NUMERAL 0) x0).
Definition term124 (x0 : Prop) := ~ (~ x0).
Definition term135 (x0 : nat) := imp (((NUMERAL 0) = x0) \/ (Peano.lt (NUMERAL 0) x0)).
Definition term66 (x0 : nat) := ((~ (Peano.lt (NUMERAL 0) x0)) = (Peano.le x0 (NUMERAL 0))) -> (~ (Peano.lt (NUMERAL 0) (S x0))) = (Peano.le (S x0) (NUMERAL 0)).
Definition term7 := forall y0 : nat, ~ ((NUMERAL 0) = (S y0)).
Definition term64 (x0 : nat) := Peano.le (S x0) (NUMERAL 0).
Definition term90 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (Peano.lt (S x0) y0)) = (Peano.le y0 (S x0))) (S x1).
Definition term155 (x0 : nat) := ((NUMERAL 0) = (S x0)) \/ True.
Definition term42 := forall y0 : nat, (forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)) -> forall y1 : nat, (~ (Peano.lt (S y0) y1)) = (Peano.le y1 (S y0)).
Definition term111 (x0 : nat) := forall y0 : nat, (Peano.le (S x0) (S y0)) = (Peano.le x0 y0).
Definition term107 (x0 : nat) := forall y0 : nat, (Peano.lt (S x0) (S y0)) = (Peano.lt x0 y0).
Definition term50 := ((forall y0 : nat, (~ (Peano.lt (NUMERAL 0) y0)) = (Peano.le y0 (NUMERAL 0))) /\ (forall y0 : nat, (forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)) -> forall y1 : nat, (~ (Peano.lt (S y0) y1)) = (Peano.le y1 (S y0)))) -> forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0).
Definition term149 := forall y0 : nat, (fun y1 : nat => ((NUMERAL 0) = y1) \/ (Peano.lt (NUMERAL 0) y1)) y0.
Definition term104 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (~ (Peano.lt (S x0) y1)) = (Peano.le y1 (S x0))) y0.
Definition term76 := forall y0 : nat, (fun y1 : nat => (~ (Peano.lt (NUMERAL 0) y1)) = (Peano.le y1 (NUMERAL 0))) y0.
Definition term128 := fun y0 : nat => ((NUMERAL 0) = y0) \/ (Peano.lt (NUMERAL 0) y0).
Definition term144 := ((fun y0 : nat => ((NUMERAL 0) = y0) \/ (Peano.lt (NUMERAL 0) y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((NUMERAL 0) = y1) \/ (Peano.lt (NUMERAL 0) y1)) y0) -> (fun y1 : nat => ((NUMERAL 0) = y1) \/ (Peano.lt (NUMERAL 0) y1)) (S y0)).
Definition term99 (x0 : nat) := ((fun y0 : nat => (~ (Peano.lt (S x0) y0)) = (Peano.le y0 (S x0))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (~ (Peano.lt (S x0) y1)) = (Peano.le y1 (S x0))) y0) -> (fun y1 : nat => (~ (Peano.lt (S x0) y1)) = (Peano.le y1 (S x0))) (S y0)).
Definition term71 := ((fun y0 : nat => (~ (Peano.lt (NUMERAL 0) y0)) = (Peano.le y0 (NUMERAL 0))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (~ (Peano.lt (NUMERAL 0) y1)) = (Peano.le y1 (NUMERAL 0))) y0) -> (fun y1 : nat => (~ (Peano.lt (NUMERAL 0) y1)) = (Peano.le y1 (NUMERAL 0))) (S y0)).
Definition term33 (x0 : nat) := imp ((fun y0 : nat => forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)) x0).
Definition term54 := ~ (Peano.lt (NUMERAL 0) (NUMERAL 0)).
Definition term72 := ((~ (Peano.lt (NUMERAL 0) (NUMERAL 0))) = (Peano.le (NUMERAL 0) (NUMERAL 0))) /\ (forall y0 : nat, ((~ (Peano.lt (NUMERAL 0) y0)) = (Peano.le y0 (NUMERAL 0))) -> (~ (Peano.lt (NUMERAL 0) (S y0))) = (Peano.le (S y0) (NUMERAL 0))).
Definition term57 := and ((~ (Peano.lt (NUMERAL 0) (NUMERAL 0))) = (Peano.le (NUMERAL 0) (NUMERAL 0))).
Definition term8 (x0 : nat) := (fun y0 : nat => Peano.le (NUMERAL 0) y0) x0.
Definition term93 (x0 : nat) (x1 : nat) := ((fun y0 : nat => (~ (Peano.lt (S x0) y0)) = (Peano.le y0 (S x0))) x1) -> (fun y0 : nat => (~ (Peano.lt (S x0) y0)) = (Peano.le y0 (S x0))) (S x1).
Definition term127 := (((fun y0 : nat => ((NUMERAL 0) = y0) \/ (Peano.lt (NUMERAL 0) y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((NUMERAL 0) = y1) \/ (Peano.lt (NUMERAL 0) y1)) y0) -> (fun y1 : nat => ((NUMERAL 0) = y1) \/ (Peano.lt (NUMERAL 0) y1)) (S y0))) -> forall y0 : nat, (fun y1 : nat => ((NUMERAL 0) = y1) \/ (Peano.lt (NUMERAL 0) y1)) y0.
Definition term78 (x0 : nat) := (((fun y0 : nat => (~ (Peano.lt (S x0) y0)) = (Peano.le y0 (S x0))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (~ (Peano.lt (S x0) y1)) = (Peano.le y1 (S x0))) y0) -> (fun y1 : nat => (~ (Peano.lt (S x0) y1)) = (Peano.le y1 (S x0))) (S y0))) -> forall y0 : nat, (fun y1 : nat => (~ (Peano.lt (S x0) y1)) = (Peano.le y1 (S x0))) y0.
Definition term51 := (((fun y0 : nat => (~ (Peano.lt (NUMERAL 0) y0)) = (Peano.le y0 (NUMERAL 0))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (~ (Peano.lt (NUMERAL 0) y1)) = (Peano.le y1 (NUMERAL 0))) y0) -> (fun y1 : nat => (~ (Peano.lt (NUMERAL 0) y1)) = (Peano.le y1 (NUMERAL 0))) (S y0))) -> forall y0 : nat, (fun y1 : nat => (~ (Peano.lt (NUMERAL 0) y1)) = (Peano.le y1 (NUMERAL 0))) y0.
Definition term25 := (((fun y0 : nat => forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (~ (Peano.lt y1 y2)) = (Peano.le y2 y1)) y0) -> (fun y1 : nat => forall y2 : nat, (~ (Peano.lt y1 y2)) = (Peano.le y2 y1)) (S y0))) -> forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (Peano.lt y1 y2)) = (Peano.le y2 y1)) y0.
Definition term18 := forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False.
Definition term24 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term146 := imp (((fun y0 : nat => ((NUMERAL 0) = y0) \/ (Peano.lt (NUMERAL 0) y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((NUMERAL 0) = y1) \/ (Peano.lt (NUMERAL 0) y1)) y0) -> (fun y1 : nat => ((NUMERAL 0) = y1) \/ (Peano.lt (NUMERAL 0) y1)) (S y0))).
Definition term101 (x0 : nat) := imp (((fun y0 : nat => (~ (Peano.lt (S x0) y0)) = (Peano.le y0 (S x0))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (~ (Peano.lt (S x0) y1)) = (Peano.le y1 (S x0))) y0) -> (fun y1 : nat => (~ (Peano.lt (S x0) y1)) = (Peano.le y1 (S x0))) (S y0))).
Definition term73 := imp (((fun y0 : nat => (~ (Peano.lt (NUMERAL 0) y0)) = (Peano.le y0 (NUMERAL 0))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (~ (Peano.lt (NUMERAL 0) y1)) = (Peano.le y1 (NUMERAL 0))) y0) -> (fun y1 : nat => (~ (Peano.lt (NUMERAL 0) y1)) = (Peano.le y1 (NUMERAL 0))) (S y0))).
Definition term45 := imp (((fun y0 : nat => forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (~ (Peano.lt y1 y2)) = (Peano.le y2 y1)) y0) -> (fun y1 : nat => forall y2 : nat, (~ (Peano.lt y1 y2)) = (Peano.le y2 y1)) (S y0))).
Definition term142 := forall y0 : nat, ((fun y1 : nat => ((NUMERAL 0) = y1) \/ (Peano.lt (NUMERAL 0) y1)) y0) -> (fun y1 : nat => ((NUMERAL 0) = y1) \/ (Peano.lt (NUMERAL 0) y1)) (S y0).
Definition term97 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => (~ (Peano.lt (S x0) y1)) = (Peano.le y1 (S x0))) y0) -> (fun y1 : nat => (~ (Peano.lt (S x0) y1)) = (Peano.le y1 (S x0))) (S y0).
Definition term69 := forall y0 : nat, ((fun y1 : nat => (~ (Peano.lt (NUMERAL 0) y1)) = (Peano.le y1 (NUMERAL 0))) y0) -> (fun y1 : nat => (~ (Peano.lt (NUMERAL 0) y1)) = (Peano.le y1 (NUMERAL 0))) (S y0).
Definition term41 := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (~ (Peano.lt y1 y2)) = (Peano.le y2 y1)) y0) -> (fun y1 : nat => forall y2 : nat, (~ (Peano.lt y1 y2)) = (Peano.le y2 y1)) (S y0).
Definition term26 := fun y0 : nat => forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0).
Definition term17 (x0 : nat) (x1 : nat) := (x0 = x1) \/ (Peano.lt x0 x1).
Definition term141 := fun y0 : nat => (((NUMERAL 0) = y0) \/ (Peano.lt (NUMERAL 0) y0)) -> ((NUMERAL 0) = (S y0)) \/ (Peano.lt (NUMERAL 0) (S y0)).
Definition term86 (x0 : nat) (x1 : nat) := ~ (Peano.lt (S x0) x1).
Definition term94 (x0 : nat) (x1 : nat) := ((~ (Peano.lt (S x1) x0)) = (Peano.le x0 (S x1))) -> (~ (Peano.lt (S x1) (S x0))) = (Peano.le (S x0) (S x1)).
Definition term115 (x0 : nat) (x1 : nat) := @eq Prop (~ (Peano.lt (S x0) (S x1))).
Definition term6 := forall y0 : nat, ~ ((S y0) = (NUMERAL 0)).
Definition term96 (x0 : nat) := fun y0 : nat => ((~ (Peano.lt (S x0) y0)) = (Peano.le y0 (S x0))) -> (~ (Peano.lt (S x0) (S y0))) = (Peano.le (S y0) (S x0)).
Definition term120 (x0 : nat) := ~ (((NUMERAL 0) = x0) \/ (Peano.lt (NUMERAL 0) x0)).
Definition term131 := and ((fun y0 : nat => ((NUMERAL 0) = y0) \/ (Peano.lt (NUMERAL 0) y0)) (NUMERAL 0)).
Definition term83 (x0 : nat) := and ((fun y0 : nat => (~ (Peano.lt (S x0) y0)) = (Peano.le y0 (S x0))) (NUMERAL 0)).
Definition term56 := and ((fun y0 : nat => (~ (Peano.lt (NUMERAL 0) y0)) = (Peano.le y0 (NUMERAL 0))) (NUMERAL 0)).
Definition term153 := True \/ (Peano.lt (NUMERAL 0) (NUMERAL 0)).
Definition term63 (x0 : nat) := ~ (Peano.lt (NUMERAL 0) (S x0)).
Definition term145 := (((NUMERAL 0) = (NUMERAL 0)) \/ (Peano.lt (NUMERAL 0) (NUMERAL 0))) /\ (forall y0 : nat, (((NUMERAL 0) = y0) \/ (Peano.lt (NUMERAL 0) y0)) -> ((NUMERAL 0) = (S y0)) \/ (Peano.lt (NUMERAL 0) (S y0))).
Definition term5 := fun y0 : nat => ~ ((NUMERAL 0) = (S y0)).
Definition term19 (x0 : nat) := (fun y0 : nat => (Peano.lt y0 (NUMERAL 0)) = False) x0.
Definition term29 := and ((fun y0 : nat => forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)) (NUMERAL 0)).
Definition term34 (x0 : nat) := imp (forall y0 : nat, (~ (Peano.lt x0 y0)) = (Peano.le y0 x0)).
Definition term30 := and (forall y0 : nat, (~ (Peano.lt (NUMERAL 0) y0)) = (Peano.le y0 (NUMERAL 0))).
Definition term35 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)) (S x0).
Definition term117 := Peano.lt (NUMERAL 0) (NUMERAL 0).
Definition term91 (x0 : nat) (x1 : nat) := ~ (Peano.lt (S x0) (S x1)).
Definition term27 := (fun y0 : nat => forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)) (NUMERAL 0).
Definition term140 := fun y0 : nat => ((fun y1 : nat => ((NUMERAL 0) = y1) \/ (Peano.lt (NUMERAL 0) y1)) y0) -> (fun y1 : nat => ((NUMERAL 0) = y1) \/ (Peano.lt (NUMERAL 0) y1)) (S y0).
Definition term95 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => (~ (Peano.lt (S x0) y1)) = (Peano.le y1 (S x0))) y0) -> (fun y1 : nat => (~ (Peano.lt (S x0) y1)) = (Peano.le y1 (S x0))) (S y0).
Definition term67 := fun y0 : nat => ((fun y1 : nat => (~ (Peano.lt (NUMERAL 0) y1)) = (Peano.le y1 (NUMERAL 0))) y0) -> (fun y1 : nat => (~ (Peano.lt (NUMERAL 0) y1)) = (Peano.le y1 (NUMERAL 0))) (S y0).
Definition term112 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le (S x0) (S y0)) = (Peano.le x0 y0)) x1.
Definition term125 (x0 : nat) := Peano.lt (S x0) (NUMERAL 0).
Definition term46 := imp ((forall y0 : nat, (~ (Peano.lt (NUMERAL 0) y0)) = (Peano.le y0 (NUMERAL 0))) /\ (forall y0 : nat, (forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)) -> forall y1 : nat, (~ (Peano.lt (S y0) y1)) = (Peano.le y1 (S y0)))).
Definition term132 := and (((NUMERAL 0) = (NUMERAL 0)) \/ (Peano.lt (NUMERAL 0) (NUMERAL 0))).
Definition term49 := forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0).
Definition term12 := forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)).
Definition term4 := fun y0 : nat => ~ ((S y0) = (NUMERAL 0)).
Definition term53 := (fun y0 : nat => (~ (Peano.lt (NUMERAL 0) y0)) = (Peano.le y0 (NUMERAL 0))) (NUMERAL 0).
Definition term32 (x0 : nat) := forall y0 : nat, (~ (Peano.lt x0 y0)) = (Peano.le y0 x0).
Definition term80 (x0 : nat) := (fun y0 : nat => (~ (Peano.lt (S x0) y0)) = (Peano.le y0 (S x0))) (NUMERAL 0).
Definition term16 (x0 : nat) (x1 : nat) := Peano.lt x0 (S x1).
Definition term105 (x0 : nat) := (((~ (Peano.lt (S x0) (NUMERAL 0))) = (Peano.le (NUMERAL 0) (S x0))) /\ (forall y0 : nat, ((~ (Peano.lt (S x0) y0)) = (Peano.le y0 (S x0))) -> (~ (Peano.lt (S x0) (S y0))) = (Peano.le (S y0) (S x0)))) -> forall y0 : nat, (~ (Peano.lt (S x0) y0)) = (Peano.le y0 (S x0)).
Definition term77 := (((~ (Peano.lt (NUMERAL 0) (NUMERAL 0))) = (Peano.le (NUMERAL 0) (NUMERAL 0))) /\ (forall y0 : nat, ((~ (Peano.lt (NUMERAL 0) y0)) = (Peano.le y0 (NUMERAL 0))) -> (~ (Peano.lt (NUMERAL 0) (S y0))) = (Peano.le (S y0) (NUMERAL 0)))) -> forall y0 : nat, (~ (Peano.lt (NUMERAL 0) y0)) = (Peano.le y0 (NUMERAL 0)).
Definition term88 (x0 : nat) (x1 : nat) := imp ((fun y0 : nat => (~ (Peano.lt (S x0) y0)) = (Peano.le y0 (S x0))) x1).
Definition term9 (x0 : nat) := Peano.le (NUMERAL 0) x0.
Definition term68 := fun y0 : nat => ((~ (Peano.lt (NUMERAL 0) y0)) = (Peano.le y0 (NUMERAL 0))) -> (~ (Peano.lt (NUMERAL 0) (S y0))) = (Peano.le (S y0) (NUMERAL 0)).
Definition term14 (x0 : nat) := forall y0 : nat, (Peano.lt x0 (S y0)) = ((x0 = y0) \/ (Peano.lt x0 y0)).
Definition term150 := forall y0 : nat, ((NUMERAL 0) = y0) \/ (Peano.lt (NUMERAL 0) y0).
Definition term154 (x0 : nat) := or ((NUMERAL 0) = (S x0)).
Definition term151 := ((((NUMERAL 0) = (NUMERAL 0)) \/ (Peano.lt (NUMERAL 0) (NUMERAL 0))) /\ (forall y0 : nat, (((NUMERAL 0) = y0) \/ (Peano.lt (NUMERAL 0) y0)) -> ((NUMERAL 0) = (S y0)) \/ (Peano.lt (NUMERAL 0) (S y0)))) -> forall y0 : nat, ((NUMERAL 0) = y0) \/ (Peano.lt (NUMERAL 0) y0).
Definition term2 (x0 : nat) := ~ ((S x0) = (NUMERAL 0)).
Definition term10 (x0 : nat) := (fun y0 : nat => ~ ((NUMERAL 0) = (S y0))) x0.
Definition term108 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt (S x0) (S y0)) = (Peano.lt x0 y0)) x1.
Definition term100 (x0 : nat) := ((~ (Peano.lt (S x0) (NUMERAL 0))) = (Peano.le (NUMERAL 0) (S x0))) /\ (forall y0 : nat, ((~ (Peano.lt (S x0) y0)) = (Peano.le y0 (S x0))) -> (~ (Peano.lt (S x0) (S y0))) = (Peano.le (S y0) (S x0))).
Definition term116 (x0 : nat) (x1 : nat) := @eq Prop (Peano.le x0 x1).
Definition term52 := fun y0 : nat => (~ (Peano.lt (NUMERAL 0) y0)) = (Peano.le y0 (NUMERAL 0)).
Definition term123 (x0 : nat) := ~ (~ (((NUMERAL 0) = x0) \/ (Peano.lt (NUMERAL 0) x0))).
Definition term40 := fun y0 : nat => (forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)) -> forall y1 : nat, (~ (Peano.lt (S y0) y1)) = (Peano.le y1 (S y0)).
Definition term39 := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, (~ (Peano.lt y1 y2)) = (Peano.le y2 y1)) y0) -> (fun y1 : nat => forall y2 : nat, (~ (Peano.lt y1 y2)) = (Peano.le y2 y1)) (S y0).
Definition term122 (x0 : nat) := @eq Prop (~ (((NUMERAL 0) = x0) \/ (Peano.lt (NUMERAL 0) x0))).
Definition term15 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt x0 (S y0)) = ((x0 = y0) \/ (Peano.lt x0 y0))) x1.
Definition term133 (x0 : nat) := (fun y0 : nat => ((NUMERAL 0) = y0) \/ (Peano.lt (NUMERAL 0) y0)) x0.
Definition term118 := @eq Prop (~ (Peano.lt (NUMERAL 0) (NUMERAL 0))).
Definition term44 := (forall y0 : nat, (~ (Peano.lt (NUMERAL 0) y0)) = (Peano.le y0 (NUMERAL 0))) /\ (forall y0 : nat, (forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)) -> forall y1 : nat, (~ (Peano.lt (S y0) y1)) = (Peano.le y1 (S y0))).
Definition term130 := ((NUMERAL 0) = (NUMERAL 0)) \/ (Peano.lt (NUMERAL 0) (NUMERAL 0)).
Definition term20 (x0 : nat) := Peano.lt x0 (NUMERAL 0).
Definition term114 (x0 : nat) (x1 : nat) := ~ (Peano.lt x0 x1).
Definition term47 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (~ (Peano.lt y1 y2)) = (Peano.le y2 y1)) y0.
Definition term126 (x0 : nat) := @eq Prop (~ (Peano.lt (S x0) (NUMERAL 0))).
Definition term110 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (S y0) (S y1)) = (Peano.le y0 y1)) x0.
Definition term106 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt (S y0) (S y1)) = (Peano.lt y0 y1)) x0.
Definition term31 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)) x0.
Definition term13 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1))) x0.
Definition term129 := (fun y0 : nat => ((NUMERAL 0) = y0) \/ (Peano.lt (NUMERAL 0) y0)) (NUMERAL 0).
Definition term121 (x0 : nat) := @eq Prop (~ (Peano.lt (NUMERAL 0) (S x0))).
Definition term43 := ((fun y0 : nat => forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (~ (Peano.lt y1 y2)) = (Peano.le y2 y1)) y0) -> (fun y1 : nat => forall y2 : nat, (~ (Peano.lt y1 y2)) = (Peano.le y2 y1)) (S y0)).
Definition term82 (x0 : nat) := Peano.le (NUMERAL 0) (S x0).
Definition term109 (x0 : nat) (x1 : nat) := Peano.lt (S x0) (S x1).
Definition term85 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (Peano.lt (S x0) y0)) = (Peano.le y0 (S x0))) x1.
Definition term21 := forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0)).
Definition term84 (x0 : nat) := and ((~ (Peano.lt (S x0) (NUMERAL 0))) = (Peano.le (NUMERAL 0) (S x0))).
Definition term11 (x0 : nat) := (~ ((S x0) = (NUMERAL 0))) -> ((S x0) = (NUMERAL 0)) = False.
Definition term148 := fun y0 : nat => (fun y1 : nat => ((NUMERAL 0) = y1) \/ (Peano.lt (NUMERAL 0) y1)) y0.
Definition term79 (x0 : nat) := fun y0 : nat => (~ (Peano.lt (S x0) y0)) = (Peano.le y0 (S x0)).
Definition term137 (x0 : nat) := ((NUMERAL 0) = (S x0)) \/ (Peano.lt (NUMERAL 0) (S x0)).
Definition term147 := imp ((((NUMERAL 0) = (NUMERAL 0)) \/ (Peano.lt (NUMERAL 0) (NUMERAL 0))) /\ (forall y0 : nat, (((NUMERAL 0) = y0) \/ (Peano.lt (NUMERAL 0) y0)) -> ((NUMERAL 0) = (S y0)) \/ (Peano.lt (NUMERAL 0) (S y0)))).
Definition term102 (x0 : nat) := imp (((~ (Peano.lt (S x0) (NUMERAL 0))) = (Peano.le (NUMERAL 0) (S x0))) /\ (forall y0 : nat, ((~ (Peano.lt (S x0) y0)) = (Peano.le y0 (S x0))) -> (~ (Peano.lt (S x0) (S y0))) = (Peano.le (S y0) (S x0)))).
Definition term74 := imp (((~ (Peano.lt (NUMERAL 0) (NUMERAL 0))) = (Peano.le (NUMERAL 0) (NUMERAL 0))) /\ (forall y0 : nat, ((~ (Peano.lt (NUMERAL 0) y0)) = (Peano.le y0 (NUMERAL 0))) -> (~ (Peano.lt (NUMERAL 0) (S y0))) = (Peano.le (S y0) (NUMERAL 0)))).
Definition term59 (x0 : nat) := ~ (Peano.lt (NUMERAL 0) x0).
Definition term89 (x0 : nat) (x1 : nat) := imp ((~ (Peano.lt (S x1) x0)) = (Peano.le x0 (S x1))).
Definition term143 := forall y0 : nat, (((NUMERAL 0) = y0) \/ (Peano.lt (NUMERAL 0) y0)) -> ((NUMERAL 0) = (S y0)) \/ (Peano.lt (NUMERAL 0) (S y0)).
Definition term98 (x0 : nat) := forall y0 : nat, ((~ (Peano.lt (S x0) y0)) = (Peano.le y0 (S x0))) -> (~ (Peano.lt (S x0) (S y0))) = (Peano.le (S y0) (S x0)).
Definition term70 := forall y0 : nat, ((~ (Peano.lt (NUMERAL 0) y0)) = (Peano.le y0 (NUMERAL 0))) -> (~ (Peano.lt (NUMERAL 0) (S y0))) = (Peano.le (S y0) (NUMERAL 0)).
Definition term36 (x0 : nat) := forall y0 : nat, (~ (Peano.lt (S x0) y0)) = (Peano.le y0 (S x0)).
Definition term113 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (Peano.lt x0 y0)) = (Peano.le y0 x0)) x1.
Definition term92 (x0 : nat) (x1 : nat) := Peano.le (S x0) (S x1).
Definition term134 (x0 : nat) := imp ((fun y0 : nat => ((NUMERAL 0) = y0) \/ (Peano.lt (NUMERAL 0) y0)) x0).
Definition term60 (x0 : nat) := imp ((fun y0 : nat => (~ (Peano.lt (NUMERAL 0) y0)) = (Peano.le y0 (NUMERAL 0))) x0).
Definition term136 (x0 : nat) := (fun y0 : nat => ((NUMERAL 0) = y0) \/ (Peano.lt (NUMERAL 0) y0)) (S x0).
Definition term139 (x0 : nat) := (((NUMERAL 0) = x0) \/ (Peano.lt (NUMERAL 0) x0)) -> ((NUMERAL 0) = (S x0)) \/ (Peano.lt (NUMERAL 0) (S x0)).
Definition term152 := or ((NUMERAL 0) = (NUMERAL 0)).
Definition term37 (x0 : nat) := ((fun y0 : nat => forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)) x0) -> (fun y0 : nat => forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)) (S x0).
Definition term48 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (Peano.lt y1 y2)) = (Peano.le y2 y1)) y0.
Definition term23 (x0 : nat) := Peano.le x0 (NUMERAL 0).
Definition term87 (x0 : nat) (x1 : nat) := Peano.le x0 (S x1).
Definition term81 (x0 : nat) := ~ (Peano.lt (S x0) (NUMERAL 0)).
Definition term28 := forall y0 : nat, (~ (Peano.lt (NUMERAL 0) y0)) = (Peano.le y0 (NUMERAL 0)).
Definition term61 (x0 : nat) := imp ((~ (Peano.lt (NUMERAL 0) x0)) = (Peano.le x0 (NUMERAL 0))).
Definition term55 := Peano.le (NUMERAL 0) (NUMERAL 0).
Definition term38 (x0 : nat) := (forall y0 : nat, (~ (Peano.lt x0 y0)) = (Peano.le y0 x0)) -> forall y0 : nat, (~ (Peano.lt (S x0) y0)) = (Peano.le y0 (S x0)).
Definition term0 (x0 : nat) := (fun y0 : nat => Peano.lt (NUMERAL 0) (S y0)) x0.
