Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term242 (x0 : nat) := and (Peano.lt (S x0) (NUMERAL 0)).
Definition term81 (x0 : nat) := ((fun y0 : nat => ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y0)) -> Peano.lt (NUMERAL 0) y0) x0) -> (fun y0 : nat => ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y0)) -> Peano.lt (NUMERAL 0) y0) (S x0).
Definition term3 (x0 : nat) := ~ ((NUMERAL 0) = (S x0)).
Definition term222 (x0 : nat) (x1 : nat) := and (Peano.lt (S x0) (S x1)).
Definition term195 (x0 : nat) := Peano.lt (NUMERAL 0) (S x0).
Definition term191 (x0 : nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => ((Peano.lt (S x1) (S x0)) /\ (Peano.le (S x0) y1)) -> Peano.lt (S x1) y1) y0.
Definition term166 (x0 : nat) := fun y0 : nat => (fun y1 : nat => ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y1)) -> Peano.lt (S x0) y1) y0.
Definition term116 (x0 : nat) := fun y0 : nat => (fun y1 : nat => ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.le (S x0) y1)) -> Peano.lt (NUMERAL 0) y1) y0.
Definition term91 := fun y0 : nat => (fun y1 : nat => ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y1)) -> Peano.lt (NUMERAL 0) y1) y0.
Definition term249 (x0 : nat) := False \/ (Peano.le (NUMERAL 0) x0).
Definition term235 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.lt x0 x1) /\ (Peano.le x1 x2).
Definition term224 (x0 : nat) (x1 : nat) := (Peano.lt (S x0) (S x1)) /\ (Peano.le (S x1) (NUMERAL 0)).
Definition term213 (x0 : nat) (x1 : nat) := imp ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.le (S x0) (S x1))).
Definition term12 (x0 : nat) := (fun y0 : nat => (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) x0.
Definition term79 (x0 : nat) := (fun y0 : nat => ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y0)) -> Peano.lt (NUMERAL 0) y0) (S x0).
Definition term24 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2) x0.
Definition term196 (x0 : nat) := imp ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) (S x0))).
Definition term176 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.lt (S x1) (S x0)) /\ (Peano.le (S x0) x2)) -> Peano.lt (S x1) x2.
Definition term151 (x0 : nat) (x1 : nat) := ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x1)) -> Peano.lt (S x0) x1.
Definition term252 (x0 : nat) (x1 : nat) := False -> Peano.lt x0 x1.
Definition term200 (x0 : nat) := Peano.le (S x0) (NUMERAL 0).
Definition term243 (x0 : nat) := (Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) (NUMERAL 0)).
Definition term31 (x0 : nat) := (forall y0 : nat, forall y1 : nat, ((Peano.lt x0 y0) /\ (Peano.le y0 y1)) -> Peano.lt x0 y1) -> forall y0 : nat, forall y1 : nat, ((Peano.lt (S x0) y0) /\ (Peano.le y0 y1)) -> Peano.lt (S x0) y1.
Definition term97 (x0 : nat) := ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.le (S x0) (NUMERAL 0))) -> Peano.lt (NUMERAL 0) (NUMERAL 0).
Definition term72 := ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) (NUMERAL 0))) -> Peano.lt (NUMERAL 0) (NUMERAL 0).
Definition term150 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y0)) -> Peano.lt (S x0) y0) x1.
Definition term100 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.le (S x0) y0)) -> Peano.lt (NUMERAL 0) y0) x1.
Definition term136 (x0 : nat) := forall y0 : nat, (forall y1 : nat, ((Peano.lt (S x0) y0) /\ (Peano.le y0 y1)) -> Peano.lt (S x0) y1) -> forall y1 : nat, ((Peano.lt (S x0) (S y0)) /\ (Peano.le (S y0) y1)) -> Peano.lt (S x0) y1.
Definition term61 := forall y0 : nat, (forall y1 : nat, ((Peano.lt (NUMERAL 0) y0) /\ (Peano.le y0 y1)) -> Peano.lt (NUMERAL 0) y1) -> forall y1 : nat, ((Peano.lt (NUMERAL 0) (S y0)) /\ (Peano.le (S y0) y1)) -> Peano.lt (NUMERAL 0) y1.
Definition term35 := forall y0 : nat, (forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2) -> forall y1 : nat, forall y2 : nat, ((Peano.lt (S y0) y1) /\ (Peano.le y1 y2)) -> Peano.lt (S y0) y2.
Definition term103 (x0 : nat) (x1 : nat) := imp (((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.le (S x0) x1)) -> Peano.lt (NUMERAL 0) x1).
Definition term197 (x0 : nat) := ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) (S x0))) -> True.
Definition term129 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((Peano.lt (S x0) y0) /\ (Peano.le y0 y1)) -> Peano.lt (S x0) y1) (S x1).
Definition term130 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Peano.lt (S x1) (S x0)) /\ (Peano.le (S x0) y0)) -> Peano.lt (S x1) y0.
Definition term126 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Peano.lt (S x1) x0) /\ (Peano.le x0 y0)) -> Peano.lt (S x1) y0.
Definition term122 (x0 : nat) := forall y0 : nat, ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y0)) -> Peano.lt (S x0) y0.
Definition term55 (x0 : nat) := forall y0 : nat, ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.le (S x0) y0)) -> Peano.lt (NUMERAL 0) y0.
Definition term51 (x0 : nat) := forall y0 : nat, ((Peano.lt (NUMERAL 0) x0) /\ (Peano.le x0 y0)) -> Peano.lt (NUMERAL 0) y0.
Definition term47 := forall y0 : nat, ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y0)) -> Peano.lt (NUMERAL 0) y0.
Definition term217 (x0 : nat) := forall y0 : nat, (Peano.lt (S x0) (S y0)) = (Peano.lt x0 y0).
Definition term208 (x0 : nat) := forall y0 : nat, (Peano.le (S x0) (S y0)) = (Peano.le x0 y0).
Definition term143 (x0 : nat) := ((forall y0 : nat, ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y0)) -> Peano.lt (S x0) y0) /\ (forall y0 : nat, (forall y1 : nat, ((Peano.lt (S x0) y0) /\ (Peano.le y0 y1)) -> Peano.lt (S x0) y1) -> forall y1 : nat, ((Peano.lt (S x0) (S y0)) /\ (Peano.le (S y0) y1)) -> Peano.lt (S x0) y1)) -> forall y0 : nat, forall y1 : nat, ((Peano.lt (S x0) y0) /\ (Peano.le y0 y1)) -> Peano.lt (S x0) y1.
Definition term68 := ((forall y0 : nat, ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y0)) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (forall y1 : nat, ((Peano.lt (NUMERAL 0) y0) /\ (Peano.le y0 y1)) -> Peano.lt (NUMERAL 0) y1) -> forall y1 : nat, ((Peano.lt (NUMERAL 0) (S y0)) /\ (Peano.le (S y0) y1)) -> Peano.lt (NUMERAL 0) y1)) -> forall y0 : nat, forall y1 : nat, ((Peano.lt (NUMERAL 0) y0) /\ (Peano.le y0 y1)) -> Peano.lt (NUMERAL 0) y1.
Definition term43 := ((forall y0 : nat, forall y1 : nat, ((Peano.lt (NUMERAL 0) y0) /\ (Peano.le y0 y1)) -> Peano.lt (NUMERAL 0) y1) /\ (forall y0 : nat, (forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2) -> forall y1 : nat, forall y2 : nat, ((Peano.lt (S y0) y1) /\ (Peano.le y1 y2)) -> Peano.lt (S y0) y2)) -> forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2.
Definition term192 (x0 : nat) (x1 : nat) := forall y0 : nat, (fun y1 : nat => ((Peano.lt (S x1) (S x0)) /\ (Peano.le (S x0) y1)) -> Peano.lt (S x1) y1) y0.
Definition term167 (x0 : nat) := forall y0 : nat, (fun y1 : nat => ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y1)) -> Peano.lt (S x0) y1) y0.
Definition term117 (x0 : nat) := forall y0 : nat, (fun y1 : nat => ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.le (S x0) y1)) -> Peano.lt (NUMERAL 0) y1) y0.
Definition term92 := forall y0 : nat, (fun y1 : nat => ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y1)) -> Peano.lt (NUMERAL 0) y1) y0.
Definition term175 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Peano.lt (S x1) (S x0)) /\ (Peano.le (S x0) y0)) -> Peano.lt (S x1) y0) x2.
Definition term187 (x0 : nat) (x1 : nat) := ((fun y0 : nat => ((Peano.lt (S x1) (S x0)) /\ (Peano.le (S x0) y0)) -> Peano.lt (S x1) y0) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Peano.lt (S x1) (S x0)) /\ (Peano.le (S x0) y1)) -> Peano.lt (S x1) y1) y0) -> (fun y1 : nat => ((Peano.lt (S x1) (S x0)) /\ (Peano.le (S x0) y1)) -> Peano.lt (S x1) y1) (S y0)).
Definition term162 (x0 : nat) := ((fun y0 : nat => ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y0)) -> Peano.lt (S x0) y0) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y1)) -> Peano.lt (S x0) y1) y0) -> (fun y1 : nat => ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y1)) -> Peano.lt (S x0) y1) (S y0)).
Definition term112 (x0 : nat) := ((fun y0 : nat => ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.le (S x0) y0)) -> Peano.lt (NUMERAL 0) y0) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.le (S x0) y1)) -> Peano.lt (NUMERAL 0) y1) y0) -> (fun y1 : nat => ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.le (S x0) y1)) -> Peano.lt (NUMERAL 0) y1) (S y0)).
Definition term87 := ((fun y0 : nat => ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y0)) -> Peano.lt (NUMERAL 0) y0) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y1)) -> Peano.lt (NUMERAL 0) y1) y0) -> (fun y1 : nat => ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y1)) -> Peano.lt (NUMERAL 0) y1) (S y0)).
Definition term202 (x0 : nat) := True /\ (Peano.le (S x0) (NUMERAL 0)).
Definition term52 (x0 : nat) := imp ((fun y0 : nat => forall y1 : nat, ((Peano.lt (NUMERAL 0) y0) /\ (Peano.le y0 y1)) -> Peano.lt (NUMERAL 0) y1) x0).
Definition term26 (x0 : nat) := imp ((fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2) x0).
Definition term251 (x0 : nat) := False /\ (Peano.le (NUMERAL 0) x0).
Definition term234 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.lt (S x0) (S x1)) /\ (Peano.le (S x1) (S x2)).
Definition term214 (x0 : nat) (x1 : nat) := imp (Peano.le x0 x1).
Definition term156 (x0 : nat) (x1 : nat) := ((fun y0 : nat => ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y0)) -> Peano.lt (S x0) y0) x1) -> (fun y0 : nat => ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y0)) -> Peano.lt (S x0) y0) (S x1).
Definition term106 (x0 : nat) (x1 : nat) := ((fun y0 : nat => ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.le (S x0) y0)) -> Peano.lt (NUMERAL 0) y0) x1) -> (fun y0 : nat => ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.le (S x0) y0)) -> Peano.lt (NUMERAL 0) y0) (S x1).
Definition term157 (x0 : nat) (x1 : nat) := (((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x1)) -> Peano.lt (S x0) x1) -> ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) (S x1))) -> Peano.lt (S x0) (S x1).
Definition term169 (x0 : nat) (x1 : nat) := (((fun y0 : nat => ((Peano.lt (S x1) (S x0)) /\ (Peano.le (S x0) y0)) -> Peano.lt (S x1) y0) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Peano.lt (S x1) (S x0)) /\ (Peano.le (S x0) y1)) -> Peano.lt (S x1) y1) y0) -> (fun y1 : nat => ((Peano.lt (S x1) (S x0)) /\ (Peano.le (S x0) y1)) -> Peano.lt (S x1) y1) (S y0))) -> forall y0 : nat, (fun y1 : nat => ((Peano.lt (S x1) (S x0)) /\ (Peano.le (S x0) y1)) -> Peano.lt (S x1) y1) y0.
Definition term144 (x0 : nat) := (((fun y0 : nat => ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y0)) -> Peano.lt (S x0) y0) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y1)) -> Peano.lt (S x0) y1) y0) -> (fun y1 : nat => ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y1)) -> Peano.lt (S x0) y1) (S y0))) -> forall y0 : nat, (fun y1 : nat => ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y1)) -> Peano.lt (S x0) y1) y0.
Definition term119 (x0 : nat) := (((fun y0 : nat => forall y1 : nat, ((Peano.lt (S x0) y0) /\ (Peano.le y0 y1)) -> Peano.lt (S x0) y1) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Peano.lt (S x0) y1) /\ (Peano.le y1 y2)) -> Peano.lt (S x0) y2) y0) -> (fun y1 : nat => forall y2 : nat, ((Peano.lt (S x0) y1) /\ (Peano.le y1 y2)) -> Peano.lt (S x0) y2) (S y0))) -> forall y0 : nat, (fun y1 : nat => forall y2 : nat, ((Peano.lt (S x0) y1) /\ (Peano.le y1 y2)) -> Peano.lt (S x0) y2) y0.
Definition term94 (x0 : nat) := (((fun y0 : nat => ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.le (S x0) y0)) -> Peano.lt (NUMERAL 0) y0) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.le (S x0) y1)) -> Peano.lt (NUMERAL 0) y1) y0) -> (fun y1 : nat => ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.le (S x0) y1)) -> Peano.lt (NUMERAL 0) y1) (S y0))) -> forall y0 : nat, (fun y1 : nat => ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.le (S x0) y1)) -> Peano.lt (NUMERAL 0) y1) y0.
Definition term69 := (((fun y0 : nat => ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y0)) -> Peano.lt (NUMERAL 0) y0) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y1)) -> Peano.lt (NUMERAL 0) y1) y0) -> (fun y1 : nat => ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y1)) -> Peano.lt (NUMERAL 0) y1) (S y0))) -> forall y0 : nat, (fun y1 : nat => ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y1)) -> Peano.lt (NUMERAL 0) y1) y0.
Definition term44 := (((fun y0 : nat => forall y1 : nat, ((Peano.lt (NUMERAL 0) y0) /\ (Peano.le y0 y1)) -> Peano.lt (NUMERAL 0) y1) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Peano.lt (NUMERAL 0) y1) /\ (Peano.le y1 y2)) -> Peano.lt (NUMERAL 0) y2) y0) -> (fun y1 : nat => forall y2 : nat, ((Peano.lt (NUMERAL 0) y1) /\ (Peano.le y1 y2)) -> Peano.lt (NUMERAL 0) y2) (S y0))) -> forall y0 : nat, (fun y1 : nat => forall y2 : nat, ((Peano.lt (NUMERAL 0) y1) /\ (Peano.le y1 y2)) -> Peano.lt (NUMERAL 0) y2) y0.
Definition term18 := (((fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, forall y3 : nat, ((Peano.lt y1 y2) /\ (Peano.le y2 y3)) -> Peano.lt y1 y3) y0) -> (fun y1 : nat => forall y2 : nat, forall y3 : nat, ((Peano.lt y1 y2) /\ (Peano.le y2 y3)) -> Peano.lt y1 y3) (S y0))) -> forall y0 : nat, (fun y1 : nat => forall y2 : nat, forall y3 : nat, ((Peano.lt y1 y2) /\ (Peano.le y2 y3)) -> Peano.lt y1 y3) y0.
Definition term14 := forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False.
Definition term17 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term153 (x0 : nat) (x1 : nat) := imp (((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x1)) -> Peano.lt (S x0) x1).
Definition term172 (x0 : nat) (x1 : nat) := ((Peano.lt (S x1) (S x0)) /\ (Peano.le (S x0) (NUMERAL 0))) -> Peano.lt (S x1) (NUMERAL 0).
Definition term189 (x0 : nat) (x1 : nat) := imp (((fun y0 : nat => ((Peano.lt (S x1) (S x0)) /\ (Peano.le (S x0) y0)) -> Peano.lt (S x1) y0) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Peano.lt (S x1) (S x0)) /\ (Peano.le (S x0) y1)) -> Peano.lt (S x1) y1) y0) -> (fun y1 : nat => ((Peano.lt (S x1) (S x0)) /\ (Peano.le (S x0) y1)) -> Peano.lt (S x1) y1) (S y0))).
Definition term164 (x0 : nat) := imp (((fun y0 : nat => ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y0)) -> Peano.lt (S x0) y0) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y1)) -> Peano.lt (S x0) y1) y0) -> (fun y1 : nat => ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y1)) -> Peano.lt (S x0) y1) (S y0))).
Definition term139 (x0 : nat) := imp (((fun y0 : nat => forall y1 : nat, ((Peano.lt (S x0) y0) /\ (Peano.le y0 y1)) -> Peano.lt (S x0) y1) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Peano.lt (S x0) y1) /\ (Peano.le y1 y2)) -> Peano.lt (S x0) y2) y0) -> (fun y1 : nat => forall y2 : nat, ((Peano.lt (S x0) y1) /\ (Peano.le y1 y2)) -> Peano.lt (S x0) y2) (S y0))).
Definition term114 (x0 : nat) := imp (((fun y0 : nat => ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.le (S x0) y0)) -> Peano.lt (NUMERAL 0) y0) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.le (S x0) y1)) -> Peano.lt (NUMERAL 0) y1) y0) -> (fun y1 : nat => ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.le (S x0) y1)) -> Peano.lt (NUMERAL 0) y1) (S y0))).
Definition term89 := imp (((fun y0 : nat => ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y0)) -> Peano.lt (NUMERAL 0) y0) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y1)) -> Peano.lt (NUMERAL 0) y1) y0) -> (fun y1 : nat => ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y1)) -> Peano.lt (NUMERAL 0) y1) (S y0))).
Definition term64 := imp (((fun y0 : nat => forall y1 : nat, ((Peano.lt (NUMERAL 0) y0) /\ (Peano.le y0 y1)) -> Peano.lt (NUMERAL 0) y1) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Peano.lt (NUMERAL 0) y1) /\ (Peano.le y1 y2)) -> Peano.lt (NUMERAL 0) y2) y0) -> (fun y1 : nat => forall y2 : nat, ((Peano.lt (NUMERAL 0) y1) /\ (Peano.le y1 y2)) -> Peano.lt (NUMERAL 0) y2) (S y0))).
Definition term38 := imp (((fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, forall y3 : nat, ((Peano.lt y1 y2) /\ (Peano.le y2 y3)) -> Peano.lt y1 y3) y0) -> (fun y1 : nat => forall y2 : nat, forall y3 : nat, ((Peano.lt y1 y2) /\ (Peano.le y2 y3)) -> Peano.lt y1 y3) (S y0))).
Definition term178 (x0 : nat) (x1 : nat) (x2 : nat) := imp (((Peano.lt (S x1) (S x0)) /\ (Peano.le (S x0) x2)) -> Peano.lt (S x1) x2).
Definition term230 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((Peano.lt x0 y0) /\ (Peano.le y0 y1)) -> Peano.lt x0 y1) x1.
Definition term125 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((Peano.lt (S x0) y0) /\ (Peano.le y0 y1)) -> Peano.lt (S x0) y1) x1.
Definition term246 (x0 : nat) := ((NUMERAL 0) = (S x0)) \/ (Peano.le (NUMERAL 0) x0).
Definition term185 (x0 : nat) (x1 : nat) := forall y0 : nat, ((fun y1 : nat => ((Peano.lt (S x1) (S x0)) /\ (Peano.le (S x0) y1)) -> Peano.lt (S x1) y1) y0) -> (fun y1 : nat => ((Peano.lt (S x1) (S x0)) /\ (Peano.le (S x0) y1)) -> Peano.lt (S x1) y1) (S y0).
Definition term160 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y1)) -> Peano.lt (S x0) y1) y0) -> (fun y1 : nat => ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y1)) -> Peano.lt (S x0) y1) (S y0).
Definition term135 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Peano.lt (S x0) y1) /\ (Peano.le y1 y2)) -> Peano.lt (S x0) y2) y0) -> (fun y1 : nat => forall y2 : nat, ((Peano.lt (S x0) y1) /\ (Peano.le y1 y2)) -> Peano.lt (S x0) y2) (S y0).
Definition term110 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.le (S x0) y1)) -> Peano.lt (NUMERAL 0) y1) y0) -> (fun y1 : nat => ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.le (S x0) y1)) -> Peano.lt (NUMERAL 0) y1) (S y0).
Definition term85 := forall y0 : nat, ((fun y1 : nat => ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y1)) -> Peano.lt (NUMERAL 0) y1) y0) -> (fun y1 : nat => ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y1)) -> Peano.lt (NUMERAL 0) y1) (S y0).
Definition term60 := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Peano.lt (NUMERAL 0) y1) /\ (Peano.le y1 y2)) -> Peano.lt (NUMERAL 0) y2) y0) -> (fun y1 : nat => forall y2 : nat, ((Peano.lt (NUMERAL 0) y1) /\ (Peano.le y1 y2)) -> Peano.lt (NUMERAL 0) y2) (S y0).
Definition term34 := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, forall y3 : nat, ((Peano.lt y1 y2) /\ (Peano.le y2 y3)) -> Peano.lt y1 y3) y0) -> (fun y1 : nat => forall y2 : nat, forall y3 : nat, ((Peano.lt y1 y2) /\ (Peano.le y2 y3)) -> Peano.lt y1 y3) (S y0).
Definition term120 (x0 : nat) := fun y0 : nat => forall y1 : nat, ((Peano.lt (S x0) y0) /\ (Peano.le y0 y1)) -> Peano.lt (S x0) y1.
Definition term45 := fun y0 : nat => forall y1 : nat, ((Peano.lt (NUMERAL 0) y0) /\ (Peano.le y0 y1)) -> Peano.lt (NUMERAL 0) y1.
Definition term201 (x0 : nat) := (Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.le (S x0) (NUMERAL 0)).
Definition term80 (x0 : nat) := ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) (S x0))) -> Peano.lt (NUMERAL 0) (S x0).
Definition term188 (x0 : nat) (x1 : nat) := (((Peano.lt (S x1) (S x0)) /\ (Peano.le (S x0) (NUMERAL 0))) -> Peano.lt (S x1) (NUMERAL 0)) /\ (forall y0 : nat, (((Peano.lt (S x1) (S x0)) /\ (Peano.le (S x0) y0)) -> Peano.lt (S x1) y0) -> ((Peano.lt (S x1) (S x0)) /\ (Peano.le (S x0) (S y0))) -> Peano.lt (S x1) (S y0)).
Definition term163 (x0 : nat) := (((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) (NUMERAL 0))) -> Peano.lt (S x0) (NUMERAL 0)) /\ (forall y0 : nat, (((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y0)) -> Peano.lt (S x0) y0) -> ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) (S y0))) -> Peano.lt (S x0) (S y0)).
Definition term113 (x0 : nat) := (((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.le (S x0) (NUMERAL 0))) -> Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (forall y0 : nat, (((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.le (S x0) y0)) -> Peano.lt (NUMERAL 0) y0) -> ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.le (S x0) (S y0))) -> Peano.lt (NUMERAL 0) (S y0)).
Definition term88 := (((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) (NUMERAL 0))) -> Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (forall y0 : nat, (((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y0)) -> Peano.lt (NUMERAL 0) y0) -> ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) (S y0))) -> Peano.lt (NUMERAL 0) (S y0)).
Definition term211 (x0 : nat) (x1 : nat) := (Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.le (S x0) (S x1)).
Definition term107 (x0 : nat) (x1 : nat) := (((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.le (S x0) x1)) -> Peano.lt (NUMERAL 0) x1) -> ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.le (S x0) (S x1))) -> Peano.lt (NUMERAL 0) (S x1).
Definition term173 (x0 : nat) (x1 : nat) := and ((fun y0 : nat => ((Peano.lt (S x1) (S x0)) /\ (Peano.le (S x0) y0)) -> Peano.lt (S x1) y0) (NUMERAL 0)).
Definition term148 (x0 : nat) := and ((fun y0 : nat => ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y0)) -> Peano.lt (S x0) y0) (NUMERAL 0)).
Definition term98 (x0 : nat) := and ((fun y0 : nat => ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.le (S x0) y0)) -> Peano.lt (NUMERAL 0) y0) (NUMERAL 0)).
Definition term73 := and ((fun y0 : nat => ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y0)) -> Peano.lt (NUMERAL 0) y0) (NUMERAL 0)).
Definition term226 (x0 : nat) (x1 : nat) := imp ((Peano.lt (S x0) (S x1)) /\ (Peano.le (S x1) (NUMERAL 0))).
Definition term203 (x0 : nat) := imp ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.le (S x0) (NUMERAL 0))).
Definition term232 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Peano.lt x1 x0) /\ (Peano.le x0 y0)) -> Peano.lt x1 y0) x2.
Definition term95 (x0 : nat) := fun y0 : nat => ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.le (S x0) y0)) -> Peano.lt (NUMERAL 0) y0.
Definition term70 := fun y0 : nat => ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y0)) -> Peano.lt (NUMERAL 0) y0.
Definition term179 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Peano.lt (S x1) (S x0)) /\ (Peano.le (S x0) y0)) -> Peano.lt (S x1) y0) (S x2).
Definition term155 (x0 : nat) (x1 : nat) := ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) (S x1))) -> Peano.lt (S x0) (S x1).
Definition term15 (x0 : nat) := (fun y0 : nat => (Peano.lt y0 (NUMERAL 0)) = False) x0.
Definition term123 (x0 : nat) := and ((fun y0 : nat => forall y1 : nat, ((Peano.lt (S x0) y0) /\ (Peano.le y0 y1)) -> Peano.lt (S x0) y1) (NUMERAL 0)).
Definition term48 := and ((fun y0 : nat => forall y1 : nat, ((Peano.lt (NUMERAL 0) y0) /\ (Peano.le y0 y1)) -> Peano.lt (NUMERAL 0) y1) (NUMERAL 0)).
Definition term22 := and ((fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2) (NUMERAL 0)).
Definition term128 (x0 : nat) (x1 : nat) := imp (forall y0 : nat, ((Peano.lt (S x1) x0) /\ (Peano.le x0 y0)) -> Peano.lt (S x1) y0).
Definition term53 (x0 : nat) := imp (forall y0 : nat, ((Peano.lt (NUMERAL 0) x0) /\ (Peano.le x0 y0)) -> Peano.lt (NUMERAL 0) y0).
Definition term180 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.lt (S x1) (S x0)) /\ (Peano.le (S x0) (S x2))) -> Peano.lt (S x1) (S x2).
Definition term124 (x0 : nat) := and (forall y0 : nat, ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y0)) -> Peano.lt (S x0) y0).
Definition term49 := and (forall y0 : nat, ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y0)) -> Peano.lt (NUMERAL 0) y0).
Definition term54 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((Peano.lt (NUMERAL 0) y0) /\ (Peano.le y0 y1)) -> Peano.lt (NUMERAL 0) y1) (S x0).
Definition term28 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2) (S x0).
Definition term205 := Peano.lt (NUMERAL 0) (NUMERAL 0).
Definition term121 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((Peano.lt (S x0) y0) /\ (Peano.le y0 y1)) -> Peano.lt (S x0) y1) (NUMERAL 0).
Definition term46 := (fun y0 : nat => forall y1 : nat, ((Peano.lt (NUMERAL 0) y0) /\ (Peano.le y0 y1)) -> Peano.lt (NUMERAL 0) y1) (NUMERAL 0).
Definition term20 := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2) (NUMERAL 0).
Definition term183 (x0 : nat) (x1 : nat) := fun y0 : nat => ((fun y1 : nat => ((Peano.lt (S x1) (S x0)) /\ (Peano.le (S x0) y1)) -> Peano.lt (S x1) y1) y0) -> (fun y1 : nat => ((Peano.lt (S x1) (S x0)) /\ (Peano.le (S x0) y1)) -> Peano.lt (S x1) y1) (S y0).
Definition term158 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y1)) -> Peano.lt (S x0) y1) y0) -> (fun y1 : nat => ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y1)) -> Peano.lt (S x0) y1) (S y0).
Definition term108 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.le (S x0) y1)) -> Peano.lt (NUMERAL 0) y1) y0) -> (fun y1 : nat => ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.le (S x0) y1)) -> Peano.lt (NUMERAL 0) y1) (S y0).
Definition term83 := fun y0 : nat => ((fun y1 : nat => ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y1)) -> Peano.lt (NUMERAL 0) y1) y0) -> (fun y1 : nat => ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y1)) -> Peano.lt (NUMERAL 0) y1) (S y0).
Definition term209 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le (S x0) (S y0)) = (Peano.le x0 y0)) x1.
Definition term75 (x0 : nat) := (fun y0 : nat => ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y0)) -> Peano.lt (NUMERAL 0) y0) x0.
Definition term228 (x0 : nat) := Peano.lt (S x0) (NUMERAL 0).
Definition term140 (x0 : nat) := imp ((forall y0 : nat, ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y0)) -> Peano.lt (S x0) y0) /\ (forall y0 : nat, (forall y1 : nat, ((Peano.lt (S x0) y0) /\ (Peano.le y0 y1)) -> Peano.lt (S x0) y1) -> forall y1 : nat, ((Peano.lt (S x0) (S y0)) /\ (Peano.le (S y0) y1)) -> Peano.lt (S x0) y1)).
Definition term65 := imp ((forall y0 : nat, ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y0)) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (forall y1 : nat, ((Peano.lt (NUMERAL 0) y0) /\ (Peano.le y0 y1)) -> Peano.lt (NUMERAL 0) y1) -> forall y1 : nat, ((Peano.lt (NUMERAL 0) (S y0)) /\ (Peano.le (S y0) y1)) -> Peano.lt (NUMERAL 0) y1)).
Definition term39 := imp ((forall y0 : nat, forall y1 : nat, ((Peano.lt (NUMERAL 0) y0) /\ (Peano.le y0 y1)) -> Peano.lt (NUMERAL 0) y1) /\ (forall y0 : nat, (forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2) -> forall y1 : nat, forall y2 : nat, ((Peano.lt (S y0) y1) /\ (Peano.le y1 y2)) -> Peano.lt (S y0) y2)).
Definition term42 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2.
Definition term29 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.lt (S x0) y0) /\ (Peano.le y0 y1)) -> Peano.lt (S x0) y1.
Definition term25 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.lt x0 y0) /\ (Peano.le y0 y1)) -> Peano.lt x0 y1.
Definition term21 := forall y0 : nat, forall y1 : nat, ((Peano.lt (NUMERAL 0) y0) /\ (Peano.le y0 y1)) -> Peano.lt (NUMERAL 0) y1.
Definition term5 := forall y0 : nat, forall y1 : nat, (Peano.le y0 (S y1)) = ((y0 = (S y1)) \/ (Peano.le y0 y1)).
Definition term240 := (Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) (NUMERAL 0)).
Definition term250 (x0 : nat) (x1 : nat) := (Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) (S x1)).
Definition term184 (x0 : nat) (x1 : nat) := fun y0 : nat => (((Peano.lt (S x1) (S x0)) /\ (Peano.le (S x0) y0)) -> Peano.lt (S x1) y0) -> ((Peano.lt (S x1) (S x0)) /\ (Peano.le (S x0) (S y0))) -> Peano.lt (S x1) (S y0).
Definition term159 (x0 : nat) := fun y0 : nat => (((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y0)) -> Peano.lt (S x0) y0) -> ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) (S y0))) -> Peano.lt (S x0) (S y0).
Definition term109 (x0 : nat) := fun y0 : nat => (((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.le (S x0) y0)) -> Peano.lt (NUMERAL 0) y0) -> ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.le (S x0) (S y0))) -> Peano.lt (NUMERAL 0) (S y0).
Definition term84 := fun y0 : nat => (((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y0)) -> Peano.lt (NUMERAL 0) y0) -> ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) (S y0))) -> Peano.lt (NUMERAL 0) (S y0).
Definition term236 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((Peano.lt (S x0) (S x1)) /\ (Peano.le (S x1) (S x2))).
Definition term152 (x0 : nat) (x1 : nat) := imp ((fun y0 : nat => ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y0)) -> Peano.lt (S x0) y0) x1).
Definition term102 (x0 : nat) (x1 : nat) := imp ((fun y0 : nat => ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.le (S x0) y0)) -> Peano.lt (NUMERAL 0) y0) x1).
Definition term248 (x0 : nat) := Peano.le (NUMERAL 0) x0.
Definition term147 (x0 : nat) := ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) (NUMERAL 0))) -> Peano.lt (S x0) (NUMERAL 0).
Definition term7 (x0 : nat) := forall y0 : nat, (Peano.le x0 (S y0)) = ((x0 = (S y0)) \/ (Peano.le x0 y0)).
Definition term105 (x0 : nat) (x1 : nat) := ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.le (S x0) (S x1))) -> Peano.lt (NUMERAL 0) (S x1).
Definition term247 (x0 : nat) := or ((NUMERAL 0) = (S x0)).
Definition term193 (x0 : nat) (x1 : nat) := ((((Peano.lt (S x1) (S x0)) /\ (Peano.le (S x0) (NUMERAL 0))) -> Peano.lt (S x1) (NUMERAL 0)) /\ (forall y0 : nat, (((Peano.lt (S x1) (S x0)) /\ (Peano.le (S x0) y0)) -> Peano.lt (S x1) y0) -> ((Peano.lt (S x1) (S x0)) /\ (Peano.le (S x0) (S y0))) -> Peano.lt (S x1) (S y0))) -> forall y0 : nat, ((Peano.lt (S x1) (S x0)) /\ (Peano.le (S x0) y0)) -> Peano.lt (S x1) y0.
Definition term168 (x0 : nat) := ((((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) (NUMERAL 0))) -> Peano.lt (S x0) (NUMERAL 0)) /\ (forall y0 : nat, (((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y0)) -> Peano.lt (S x0) y0) -> ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) (S y0))) -> Peano.lt (S x0) (S y0))) -> forall y0 : nat, ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y0)) -> Peano.lt (S x0) y0.
Definition term118 (x0 : nat) := ((((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.le (S x0) (NUMERAL 0))) -> Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (forall y0 : nat, (((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.le (S x0) y0)) -> Peano.lt (NUMERAL 0) y0) -> ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.le (S x0) (S y0))) -> Peano.lt (NUMERAL 0) (S y0))) -> forall y0 : nat, ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.le (S x0) y0)) -> Peano.lt (NUMERAL 0) y0.
Definition term93 := ((((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) (NUMERAL 0))) -> Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (forall y0 : nat, (((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y0)) -> Peano.lt (NUMERAL 0) y0) -> ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) (S y0))) -> Peano.lt (NUMERAL 0) (S y0))) -> forall y0 : nat, ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y0)) -> Peano.lt (NUMERAL 0) y0.
Definition term1 (x0 : nat) := ~ ((S x0) = (NUMERAL 0)).
Definition term127 (x0 : nat) (x1 : nat) := imp ((fun y0 : nat => forall y1 : nat, ((Peano.lt (S x0) y0) /\ (Peano.le y0 y1)) -> Peano.lt (S x0) y1) x1).
Definition term218 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt (S x0) (S y0)) = (Peano.lt x0 y0)) x1.
Definition term78 (x0 : nat) := imp (((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)) -> Peano.lt (NUMERAL 0) x0).
Definition term154 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y0)) -> Peano.lt (S x0) y0) (S x1).
Definition term104 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.le (S x0) y0)) -> Peano.lt (NUMERAL 0) y0) (S x1).
Definition term171 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Peano.lt (S x1) (S x0)) /\ (Peano.le (S x0) y0)) -> Peano.lt (S x1) y0) (NUMERAL 0).
Definition term146 (x0 : nat) := (fun y0 : nat => ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y0)) -> Peano.lt (S x0) y0) (NUMERAL 0).
Definition term96 (x0 : nat) := (fun y0 : nat => ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.le (S x0) y0)) -> Peano.lt (NUMERAL 0) y0) (NUMERAL 0).
Definition term71 := (fun y0 : nat => ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y0)) -> Peano.lt (NUMERAL 0) y0) (NUMERAL 0).
Definition term134 (x0 : nat) := fun y0 : nat => (forall y1 : nat, ((Peano.lt (S x0) y0) /\ (Peano.le y0 y1)) -> Peano.lt (S x0) y1) -> forall y1 : nat, ((Peano.lt (S x0) (S y0)) /\ (Peano.le (S y0) y1)) -> Peano.lt (S x0) y1.
Definition term59 := fun y0 : nat => (forall y1 : nat, ((Peano.lt (NUMERAL 0) y0) /\ (Peano.le y0 y1)) -> Peano.lt (NUMERAL 0) y1) -> forall y1 : nat, ((Peano.lt (NUMERAL 0) (S y0)) /\ (Peano.le (S y0) y1)) -> Peano.lt (NUMERAL 0) y1.
Definition term133 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, ((Peano.lt (S x0) y1) /\ (Peano.le y1 y2)) -> Peano.lt (S x0) y2) y0) -> (fun y1 : nat => forall y2 : nat, ((Peano.lt (S x0) y1) /\ (Peano.le y1 y2)) -> Peano.lt (S x0) y2) (S y0).
Definition term58 := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, ((Peano.lt (NUMERAL 0) y1) /\ (Peano.le y1 y2)) -> Peano.lt (NUMERAL 0) y2) y0) -> (fun y1 : nat => forall y2 : nat, ((Peano.lt (NUMERAL 0) y1) /\ (Peano.le y1 y2)) -> Peano.lt (NUMERAL 0) y2) (S y0).
Definition term32 := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, forall y3 : nat, ((Peano.lt y1 y2) /\ (Peano.le y2 y3)) -> Peano.lt y1 y3) y0) -> (fun y1 : nat => forall y2 : nat, forall y3 : nat, ((Peano.lt y1 y2) /\ (Peano.le y2 y3)) -> Peano.lt y1 y3) (S y0).
Definition term223 (x0 : nat) (x1 : nat) := and (Peano.lt x0 x1).
Definition term237 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((Peano.lt x0 x1) /\ (Peano.le x1 x2)).
Definition term215 (x0 : nat) (x1 : nat) := (Peano.le x0 x1) -> True.
Definition term231 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Peano.lt x1 x0) /\ (Peano.le x0 y0)) -> Peano.lt x1 y0.
Definition term131 (x0 : nat) (x1 : nat) := ((fun y0 : nat => forall y1 : nat, ((Peano.lt (S x0) y0) /\ (Peano.le y0 y1)) -> Peano.lt (S x0) y1) x1) -> (fun y0 : nat => forall y1 : nat, ((Peano.lt (S x0) y0) /\ (Peano.le y0 y1)) -> Peano.lt (S x0) y1) (S x1).
Definition term204 (x0 : nat) := imp (Peano.le (S x0) (NUMERAL 0)).
Definition term138 (x0 : nat) := (forall y0 : nat, ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y0)) -> Peano.lt (S x0) y0) /\ (forall y0 : nat, (forall y1 : nat, ((Peano.lt (S x0) y0) /\ (Peano.le y0 y1)) -> Peano.lt (S x0) y1) -> forall y1 : nat, ((Peano.lt (S x0) (S y0)) /\ (Peano.le (S y0) y1)) -> Peano.lt (S x0) y1).
Definition term63 := (forall y0 : nat, ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y0)) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (forall y1 : nat, ((Peano.lt (NUMERAL 0) y0) /\ (Peano.le y0 y1)) -> Peano.lt (NUMERAL 0) y1) -> forall y1 : nat, ((Peano.lt (NUMERAL 0) (S y0)) /\ (Peano.le (S y0) y1)) -> Peano.lt (NUMERAL 0) y1).
Definition term16 (x0 : nat) := Peano.lt x0 (NUMERAL 0).
Definition term23 := and (forall y0 : nat, forall y1 : nat, ((Peano.lt (NUMERAL 0) y0) /\ (Peano.le y0 y1)) -> Peano.lt (NUMERAL 0) y1).
Definition term206 (x0 : nat) := (Peano.le (S x0) (NUMERAL 0)) -> Peano.lt (NUMERAL 0) (NUMERAL 0).
Definition term10 (x0 : nat) (x1 : nat) := (x0 = (S x1)) \/ (Peano.le x0 x1).
Definition term220 (x0 : nat) (x1 : nat) := imp ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) (S x1))).
Definition term253 (x0 : nat) (x1 : nat) := (Peano.lt x0 x1) /\ False.
Definition term141 (x0 : nat) := fun y0 : nat => (fun y1 : nat => forall y2 : nat, ((Peano.lt (S x0) y1) /\ (Peano.le y1 y2)) -> Peano.lt (S x0) y2) y0.
Definition term66 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, ((Peano.lt (NUMERAL 0) y1) /\ (Peano.le y1 y2)) -> Peano.lt (NUMERAL 0) y2) y0.
Definition term40 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, forall y3 : nat, ((Peano.lt y1 y2) /\ (Peano.le y2 y3)) -> Peano.lt y1 y3) y0.
Definition term229 (x0 : nat) (x1 : nat) := ((Peano.lt x1 x0) /\ (Peano.le (S x0) (NUMERAL 0))) -> Peano.lt (S x1) (NUMERAL 0).
Definition term216 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt (S y0) (S y1)) = (Peano.lt y0 y1)) x0.
Definition term207 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (S y0) (S y1)) = (Peano.le y0 y1)) x0.
Definition term50 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((Peano.lt (NUMERAL 0) y0) /\ (Peano.le y0 y1)) -> Peano.lt (NUMERAL 0) y1) x0.
Definition term6 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y0 (S y1)) = ((y0 = (S y1)) \/ (Peano.le y0 y1))) x0.
Definition term244 (x0 : nat) := imp ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) (NUMERAL 0))).
Definition term241 := imp ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) (NUMERAL 0))).
Definition term0 (x0 : nat) := (fun y0 : nat => ~ ((S y0) = (NUMERAL 0))) x0.
Definition term33 := fun y0 : nat => (forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2) -> forall y1 : nat, forall y2 : nat, ((Peano.lt (S y0) y1) /\ (Peano.le y1 y2)) -> Peano.lt (S y0) y2.
Definition term99 (x0 : nat) := and (((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.le (S x0) (NUMERAL 0))) -> Peano.lt (NUMERAL 0) (NUMERAL 0)).
Definition term74 := and (((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) (NUMERAL 0))) -> Peano.lt (NUMERAL 0) (NUMERAL 0)).
Definition term170 (x0 : nat) (x1 : nat) := fun y0 : nat => ((Peano.lt (S x1) (S x0)) /\ (Peano.le (S x0) y0)) -> Peano.lt (S x1) y0.
Definition term145 (x0 : nat) := fun y0 : nat => ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y0)) -> Peano.lt (S x0) y0.
Definition term137 (x0 : nat) := ((fun y0 : nat => forall y1 : nat, ((Peano.lt (S x0) y0) /\ (Peano.le y0 y1)) -> Peano.lt (S x0) y1) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Peano.lt (S x0) y1) /\ (Peano.le y1 y2)) -> Peano.lt (S x0) y2) y0) -> (fun y1 : nat => forall y2 : nat, ((Peano.lt (S x0) y1) /\ (Peano.le y1 y2)) -> Peano.lt (S x0) y2) (S y0)).
Definition term62 := ((fun y0 : nat => forall y1 : nat, ((Peano.lt (NUMERAL 0) y0) /\ (Peano.le y0 y1)) -> Peano.lt (NUMERAL 0) y1) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Peano.lt (NUMERAL 0) y1) /\ (Peano.le y1 y2)) -> Peano.lt (NUMERAL 0) y2) y0) -> (fun y1 : nat => forall y2 : nat, ((Peano.lt (NUMERAL 0) y1) /\ (Peano.le y1 y2)) -> Peano.lt (NUMERAL 0) y2) (S y0)).
Definition term36 := ((fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, forall y3 : nat, ((Peano.lt y1 y2) /\ (Peano.le y2 y3)) -> Peano.lt y1 y3) y0) -> (fun y1 : nat => forall y2 : nat, forall y3 : nat, ((Peano.lt y1 y2) /\ (Peano.le y2 y3)) -> Peano.lt y1 y3) (S y0)).
Definition term245 (x0 : nat) := Peano.le (NUMERAL 0) (S x0).
Definition term219 (x0 : nat) (x1 : nat) := Peano.lt (S x0) (S x1).
Definition term233 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.lt x1 x0) /\ (Peano.le x0 x2)) -> Peano.lt x1 x2.
Definition term174 (x0 : nat) (x1 : nat) := and (((Peano.lt (S x1) (S x0)) /\ (Peano.le (S x0) (NUMERAL 0))) -> Peano.lt (S x1) (NUMERAL 0)).
Definition term149 (x0 : nat) := and (((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) (NUMERAL 0))) -> Peano.lt (S x0) (NUMERAL 0)).
Definition term11 := forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0)).
Definition term221 (x0 : nat) (x1 : nat) := ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) (S x1))) -> Peano.lt x0 x1.
Definition term199 (x0 : nat) := and (Peano.lt (NUMERAL 0) (S x0)).
Definition term212 (x0 : nat) (x1 : nat) := True /\ (Peano.le x0 x1).
Definition term2 (x0 : nat) := (~ ((S x0) = (NUMERAL 0))) -> ((S x0) = (NUMERAL 0)) = False.
Definition term4 (x0 : nat) := (~ ((NUMERAL 0) = (S x0))) -> ((NUMERAL 0) = (S x0)) = False.
Definition term190 (x0 : nat) (x1 : nat) := imp ((((Peano.lt (S x1) (S x0)) /\ (Peano.le (S x0) (NUMERAL 0))) -> Peano.lt (S x1) (NUMERAL 0)) /\ (forall y0 : nat, (((Peano.lt (S x1) (S x0)) /\ (Peano.le (S x0) y0)) -> Peano.lt (S x1) y0) -> ((Peano.lt (S x1) (S x0)) /\ (Peano.le (S x0) (S y0))) -> Peano.lt (S x1) (S y0))).
Definition term165 (x0 : nat) := imp ((((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) (NUMERAL 0))) -> Peano.lt (S x0) (NUMERAL 0)) /\ (forall y0 : nat, (((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y0)) -> Peano.lt (S x0) y0) -> ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) (S y0))) -> Peano.lt (S x0) (S y0))).
Definition term115 (x0 : nat) := imp ((((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.le (S x0) (NUMERAL 0))) -> Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (forall y0 : nat, (((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.le (S x0) y0)) -> Peano.lt (NUMERAL 0) y0) -> ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.le (S x0) (S y0))) -> Peano.lt (NUMERAL 0) (S y0))).
Definition term90 := imp ((((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) (NUMERAL 0))) -> Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (forall y0 : nat, (((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y0)) -> Peano.lt (NUMERAL 0) y0) -> ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) (S y0))) -> Peano.lt (NUMERAL 0) (S y0))).
Definition term182 (x0 : nat) (x1 : nat) (x2 : nat) := (((Peano.lt (S x1) (S x0)) /\ (Peano.le (S x0) x2)) -> Peano.lt (S x1) x2) -> ((Peano.lt (S x1) (S x0)) /\ (Peano.le (S x0) (S x2))) -> Peano.lt (S x1) (S x2).
Definition term198 (x0 : nat) := (Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) (S x0)).
Definition term225 (x0 : nat) (x1 : nat) := (Peano.lt x0 x1) /\ (Peano.le (S x1) (NUMERAL 0)).
Definition term238 := and (Peano.lt (NUMERAL 0) (NUMERAL 0)).
Definition term186 (x0 : nat) (x1 : nat) := forall y0 : nat, (((Peano.lt (S x1) (S x0)) /\ (Peano.le (S x0) y0)) -> Peano.lt (S x1) y0) -> ((Peano.lt (S x1) (S x0)) /\ (Peano.le (S x0) (S y0))) -> Peano.lt (S x1) (S y0).
Definition term161 (x0 : nat) := forall y0 : nat, (((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y0)) -> Peano.lt (S x0) y0) -> ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) (S y0))) -> Peano.lt (S x0) (S y0).
Definition term111 (x0 : nat) := forall y0 : nat, (((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.le (S x0) y0)) -> Peano.lt (NUMERAL 0) y0) -> ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.le (S x0) (S y0))) -> Peano.lt (NUMERAL 0) (S y0).
Definition term86 := forall y0 : nat, (((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y0)) -> Peano.lt (NUMERAL 0) y0) -> ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) (S y0))) -> Peano.lt (NUMERAL 0) (S y0).
Definition term181 (x0 : nat) (x1 : nat) (x2 : nat) := ((fun y0 : nat => ((Peano.lt (S x1) (S x0)) /\ (Peano.le (S x0) y0)) -> Peano.lt (S x1) y0) x2) -> (fun y0 : nat => ((Peano.lt (S x1) (S x0)) /\ (Peano.le (S x0) y0)) -> Peano.lt (S x1) y0) (S x2).
Definition term177 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((fun y0 : nat => ((Peano.lt (S x1) (S x0)) /\ (Peano.le (S x0) y0)) -> Peano.lt (S x1) y0) x2).
Definition term101 (x0 : nat) (x1 : nat) := ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.le (S x0) x1)) -> Peano.lt (NUMERAL 0) x1.
Definition term210 (x0 : nat) (x1 : nat) := Peano.le (S x0) (S x1).
Definition term77 (x0 : nat) := imp ((fun y0 : nat => ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y0)) -> Peano.lt (NUMERAL 0) y0) x0).
Definition term56 (x0 : nat) := ((fun y0 : nat => forall y1 : nat, ((Peano.lt (NUMERAL 0) y0) /\ (Peano.le y0 y1)) -> Peano.lt (NUMERAL 0) y1) x0) -> (fun y0 : nat => forall y1 : nat, ((Peano.lt (NUMERAL 0) y0) /\ (Peano.le y0 y1)) -> Peano.lt (NUMERAL 0) y1) (S x0).
Definition term30 (x0 : nat) := ((fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2) x0) -> (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2) (S x0).
Definition term142 (x0 : nat) := forall y0 : nat, (fun y1 : nat => forall y2 : nat, ((Peano.lt (S x0) y1) /\ (Peano.le y1 y2)) -> Peano.lt (S x0) y2) y0.
Definition term67 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, ((Peano.lt (NUMERAL 0) y1) /\ (Peano.le y1 y2)) -> Peano.lt (NUMERAL 0) y2) y0.
Definition term41 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, forall y3 : nat, ((Peano.lt y1 y2) /\ (Peano.le y2 y3)) -> Peano.lt y1 y3) y0.
Definition term227 (x0 : nat) (x1 : nat) := imp ((Peano.lt x0 x1) /\ (Peano.le (S x1) (NUMERAL 0))).
Definition term13 (x0 : nat) := Peano.le x0 (NUMERAL 0).
Definition term27 (x0 : nat) := imp (forall y0 : nat, forall y1 : nat, ((Peano.lt x0 y0) /\ (Peano.le y0 y1)) -> Peano.lt x0 y1).
Definition term8 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le x0 (S y0)) = ((x0 = (S y0)) \/ (Peano.le x0 y0))) x1.
Definition term9 (x0 : nat) (x1 : nat) := Peano.le x0 (S x1).
Definition term82 (x0 : nat) := (((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)) -> Peano.lt (NUMERAL 0) x0) -> ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) (S x0))) -> Peano.lt (NUMERAL 0) (S x0).
Definition term37 := (forall y0 : nat, forall y1 : nat, ((Peano.lt (NUMERAL 0) y0) /\ (Peano.le y0 y1)) -> Peano.lt (NUMERAL 0) y1) /\ (forall y0 : nat, (forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2) -> forall y1 : nat, forall y2 : nat, ((Peano.lt (S y0) y1) /\ (Peano.le y1 y2)) -> Peano.lt (S y0) y2).
Definition term76 (x0 : nat) := ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)) -> Peano.lt (NUMERAL 0) x0.
Definition term19 := fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2.
Definition term239 := Peano.le (NUMERAL 0) (NUMERAL 0).
Definition term132 (x0 : nat) (x1 : nat) := (forall y0 : nat, ((Peano.lt (S x1) x0) /\ (Peano.le x0 y0)) -> Peano.lt (S x1) y0) -> forall y0 : nat, ((Peano.lt (S x1) (S x0)) /\ (Peano.le (S x0) y0)) -> Peano.lt (S x1) y0.
Definition term57 (x0 : nat) := (forall y0 : nat, ((Peano.lt (NUMERAL 0) x0) /\ (Peano.le x0 y0)) -> Peano.lt (NUMERAL 0) y0) -> forall y0 : nat, ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.le (S x0) y0)) -> Peano.lt (NUMERAL 0) y0.
Definition term194 (x0 : nat) := (fun y0 : nat => Peano.lt (NUMERAL 0) (S y0)) x0.
