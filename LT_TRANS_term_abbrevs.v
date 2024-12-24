Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term190 (x0 : nat) := imp ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) (S x0))).
Definition term208 (x0 : nat) := and (Peano.lt (S x0) (NUMERAL 0)).
Definition term67 (x0 : nat) := ((fun y0 : nat => ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y0)) -> Peano.lt (NUMERAL 0) y0) x0) -> (fun y0 : nat => ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y0)) -> Peano.lt (NUMERAL 0) y0) (S x0).
Definition term213 (x0 : nat) (x1 : nat) := and (Peano.lt (S x0) (S x1)).
Definition term186 (x0 : nat) := Peano.lt (NUMERAL 0) (S x0).
Definition term177 (x0 : nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => ((Peano.lt (S x1) (S x0)) /\ (Peano.lt (S x0) y1)) -> Peano.lt (S x1) y1) y0.
Definition term152 (x0 : nat) := fun y0 : nat => (fun y1 : nat => ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y1)) -> Peano.lt (S x0) y1) y0.
Definition term102 (x0 : nat) := fun y0 : nat => (fun y1 : nat => ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (S x0) y1)) -> Peano.lt (NUMERAL 0) y1) y0.
Definition term77 := fun y0 : nat => (fun y1 : nat => ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y1)) -> Peano.lt (NUMERAL 0) y1) y0.
Definition term191 := (Peano.lt (NUMERAL 0) (NUMERAL 0)) -> True.
Definition term65 (x0 : nat) := (fun y0 : nat => ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y0)) -> Peano.lt (NUMERAL 0) y0) (S x0).
Definition term10 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.lt y1 y2)) -> Peano.lt y0 y2) x0.
Definition term162 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.lt (S x1) (S x0)) /\ (Peano.lt (S x0) x2)) -> Peano.lt (S x1) x2.
Definition term137 (x0 : nat) (x1 : nat) := ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) x1)) -> Peano.lt (S x0) x1.
Definition term230 (x0 : nat) (x1 : nat) := False -> Peano.lt x0 x1.
Definition term17 (x0 : nat) := (forall y0 : nat, forall y1 : nat, ((Peano.lt x0 y0) /\ (Peano.lt y0 y1)) -> Peano.lt x0 y1) -> forall y0 : nat, forall y1 : nat, ((Peano.lt (S x0) y0) /\ (Peano.lt y0 y1)) -> Peano.lt (S x0) y1.
Definition term83 (x0 : nat) := ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (S x0) (NUMERAL 0))) -> Peano.lt (NUMERAL 0) (NUMERAL 0).
Definition term58 := ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) (NUMERAL 0))) -> Peano.lt (NUMERAL 0) (NUMERAL 0).
Definition term136 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y0)) -> Peano.lt (S x0) y0) x1.
Definition term86 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (S x0) y0)) -> Peano.lt (NUMERAL 0) y0) x1.
Definition term122 (x0 : nat) := forall y0 : nat, (forall y1 : nat, ((Peano.lt (S x0) y0) /\ (Peano.lt y0 y1)) -> Peano.lt (S x0) y1) -> forall y1 : nat, ((Peano.lt (S x0) (S y0)) /\ (Peano.lt (S y0) y1)) -> Peano.lt (S x0) y1.
Definition term47 := forall y0 : nat, (forall y1 : nat, ((Peano.lt (NUMERAL 0) y0) /\ (Peano.lt y0 y1)) -> Peano.lt (NUMERAL 0) y1) -> forall y1 : nat, ((Peano.lt (NUMERAL 0) (S y0)) /\ (Peano.lt (S y0) y1)) -> Peano.lt (NUMERAL 0) y1.
Definition term21 := forall y0 : nat, (forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.lt y1 y2)) -> Peano.lt y0 y2) -> forall y1 : nat, forall y2 : nat, ((Peano.lt (S y0) y1) /\ (Peano.lt y1 y2)) -> Peano.lt (S y0) y2.
Definition term89 (x0 : nat) (x1 : nat) := imp (((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (S x0) x1)) -> Peano.lt (NUMERAL 0) x1).
Definition term229 (x0 : nat) := imp ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) (NUMERAL 0))).
Definition term182 := imp ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) (NUMERAL 0))).
Definition term115 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((Peano.lt (S x0) y0) /\ (Peano.lt y0 y1)) -> Peano.lt (S x0) y1) (S x1).
Definition term116 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Peano.lt (S x1) (S x0)) /\ (Peano.lt (S x0) y0)) -> Peano.lt (S x1) y0.
Definition term112 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Peano.lt (S x1) x0) /\ (Peano.lt x0 y0)) -> Peano.lt (S x1) y0.
Definition term108 (x0 : nat) := forall y0 : nat, ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y0)) -> Peano.lt (S x0) y0.
Definition term41 (x0 : nat) := forall y0 : nat, ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (S x0) y0)) -> Peano.lt (NUMERAL 0) y0.
Definition term37 (x0 : nat) := forall y0 : nat, ((Peano.lt (NUMERAL 0) x0) /\ (Peano.lt x0 y0)) -> Peano.lt (NUMERAL 0) y0.
Definition term33 := forall y0 : nat, ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y0)) -> Peano.lt (NUMERAL 0) y0.
Definition term200 (x0 : nat) := forall y0 : nat, (Peano.lt (S x0) (S y0)) = (Peano.lt x0 y0).
Definition term129 (x0 : nat) := ((forall y0 : nat, ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y0)) -> Peano.lt (S x0) y0) /\ (forall y0 : nat, (forall y1 : nat, ((Peano.lt (S x0) y0) /\ (Peano.lt y0 y1)) -> Peano.lt (S x0) y1) -> forall y1 : nat, ((Peano.lt (S x0) (S y0)) /\ (Peano.lt (S y0) y1)) -> Peano.lt (S x0) y1)) -> forall y0 : nat, forall y1 : nat, ((Peano.lt (S x0) y0) /\ (Peano.lt y0 y1)) -> Peano.lt (S x0) y1.
Definition term54 := ((forall y0 : nat, ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y0)) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (forall y1 : nat, ((Peano.lt (NUMERAL 0) y0) /\ (Peano.lt y0 y1)) -> Peano.lt (NUMERAL 0) y1) -> forall y1 : nat, ((Peano.lt (NUMERAL 0) (S y0)) /\ (Peano.lt (S y0) y1)) -> Peano.lt (NUMERAL 0) y1)) -> forall y0 : nat, forall y1 : nat, ((Peano.lt (NUMERAL 0) y0) /\ (Peano.lt y0 y1)) -> Peano.lt (NUMERAL 0) y1.
Definition term29 := ((forall y0 : nat, forall y1 : nat, ((Peano.lt (NUMERAL 0) y0) /\ (Peano.lt y0 y1)) -> Peano.lt (NUMERAL 0) y1) /\ (forall y0 : nat, (forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.lt y1 y2)) -> Peano.lt y0 y2) -> forall y1 : nat, forall y2 : nat, ((Peano.lt (S y0) y1) /\ (Peano.lt y1 y2)) -> Peano.lt (S y0) y2)) -> forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.lt y1 y2)) -> Peano.lt y0 y2.
Definition term178 (x0 : nat) (x1 : nat) := forall y0 : nat, (fun y1 : nat => ((Peano.lt (S x1) (S x0)) /\ (Peano.lt (S x0) y1)) -> Peano.lt (S x1) y1) y0.
Definition term153 (x0 : nat) := forall y0 : nat, (fun y1 : nat => ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y1)) -> Peano.lt (S x0) y1) y0.
Definition term103 (x0 : nat) := forall y0 : nat, (fun y1 : nat => ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (S x0) y1)) -> Peano.lt (NUMERAL 0) y1) y0.
Definition term78 := forall y0 : nat, (fun y1 : nat => ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y1)) -> Peano.lt (NUMERAL 0) y1) y0.
Definition term161 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Peano.lt (S x1) (S x0)) /\ (Peano.lt (S x0) y0)) -> Peano.lt (S x1) y0) x2.
Definition term173 (x0 : nat) (x1 : nat) := ((fun y0 : nat => ((Peano.lt (S x1) (S x0)) /\ (Peano.lt (S x0) y0)) -> Peano.lt (S x1) y0) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Peano.lt (S x1) (S x0)) /\ (Peano.lt (S x0) y1)) -> Peano.lt (S x1) y1) y0) -> (fun y1 : nat => ((Peano.lt (S x1) (S x0)) /\ (Peano.lt (S x0) y1)) -> Peano.lt (S x1) y1) (S y0)).
Definition term148 (x0 : nat) := ((fun y0 : nat => ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y0)) -> Peano.lt (S x0) y0) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y1)) -> Peano.lt (S x0) y1) y0) -> (fun y1 : nat => ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y1)) -> Peano.lt (S x0) y1) (S y0)).
Definition term98 (x0 : nat) := ((fun y0 : nat => ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (S x0) y0)) -> Peano.lt (NUMERAL 0) y0) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (S x0) y1)) -> Peano.lt (NUMERAL 0) y1) y0) -> (fun y1 : nat => ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (S x0) y1)) -> Peano.lt (NUMERAL 0) y1) (S y0)).
Definition term73 := ((fun y0 : nat => ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y0)) -> Peano.lt (NUMERAL 0) y0) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y1)) -> Peano.lt (NUMERAL 0) y1) y0) -> (fun y1 : nat => ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y1)) -> Peano.lt (NUMERAL 0) y1) (S y0)).
Definition term38 (x0 : nat) := imp ((fun y0 : nat => forall y1 : nat, ((Peano.lt (NUMERAL 0) y0) /\ (Peano.lt y0 y1)) -> Peano.lt (NUMERAL 0) y1) x0).
Definition term12 (x0 : nat) := imp ((fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.lt y1 y2)) -> Peano.lt y0 y2) x0).
Definition term217 (x0 : nat) (x1 : nat) := imp ((Peano.lt (S x0) (S x1)) /\ (Peano.lt (S x1) (NUMERAL 0))).
Definition term196 (x0 : nat) := imp ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (S x0) (NUMERAL 0))).
Definition term198 (x0 : nat) := (Peano.lt (S x0) (NUMERAL 0)) -> Peano.lt (NUMERAL 0) (NUMERAL 0).
Definition term142 (x0 : nat) (x1 : nat) := ((fun y0 : nat => ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y0)) -> Peano.lt (S x0) y0) x1) -> (fun y0 : nat => ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y0)) -> Peano.lt (S x0) y0) (S x1).
Definition term92 (x0 : nat) (x1 : nat) := ((fun y0 : nat => ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (S x0) y0)) -> Peano.lt (NUMERAL 0) y0) x1) -> (fun y0 : nat => ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (S x0) y0)) -> Peano.lt (NUMERAL 0) y0) (S x1).
Definition term143 (x0 : nat) (x1 : nat) := (((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) x1)) -> Peano.lt (S x0) x1) -> ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) (S x1))) -> Peano.lt (S x0) (S x1).
Definition term155 (x0 : nat) (x1 : nat) := (((fun y0 : nat => ((Peano.lt (S x1) (S x0)) /\ (Peano.lt (S x0) y0)) -> Peano.lt (S x1) y0) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Peano.lt (S x1) (S x0)) /\ (Peano.lt (S x0) y1)) -> Peano.lt (S x1) y1) y0) -> (fun y1 : nat => ((Peano.lt (S x1) (S x0)) /\ (Peano.lt (S x0) y1)) -> Peano.lt (S x1) y1) (S y0))) -> forall y0 : nat, (fun y1 : nat => ((Peano.lt (S x1) (S x0)) /\ (Peano.lt (S x0) y1)) -> Peano.lt (S x1) y1) y0.
Definition term130 (x0 : nat) := (((fun y0 : nat => ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y0)) -> Peano.lt (S x0) y0) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y1)) -> Peano.lt (S x0) y1) y0) -> (fun y1 : nat => ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y1)) -> Peano.lt (S x0) y1) (S y0))) -> forall y0 : nat, (fun y1 : nat => ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y1)) -> Peano.lt (S x0) y1) y0.
Definition term105 (x0 : nat) := (((fun y0 : nat => forall y1 : nat, ((Peano.lt (S x0) y0) /\ (Peano.lt y0 y1)) -> Peano.lt (S x0) y1) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Peano.lt (S x0) y1) /\ (Peano.lt y1 y2)) -> Peano.lt (S x0) y2) y0) -> (fun y1 : nat => forall y2 : nat, ((Peano.lt (S x0) y1) /\ (Peano.lt y1 y2)) -> Peano.lt (S x0) y2) (S y0))) -> forall y0 : nat, (fun y1 : nat => forall y2 : nat, ((Peano.lt (S x0) y1) /\ (Peano.lt y1 y2)) -> Peano.lt (S x0) y2) y0.
Definition term80 (x0 : nat) := (((fun y0 : nat => ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (S x0) y0)) -> Peano.lt (NUMERAL 0) y0) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (S x0) y1)) -> Peano.lt (NUMERAL 0) y1) y0) -> (fun y1 : nat => ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (S x0) y1)) -> Peano.lt (NUMERAL 0) y1) (S y0))) -> forall y0 : nat, (fun y1 : nat => ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (S x0) y1)) -> Peano.lt (NUMERAL 0) y1) y0.
Definition term55 := (((fun y0 : nat => ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y0)) -> Peano.lt (NUMERAL 0) y0) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y1)) -> Peano.lt (NUMERAL 0) y1) y0) -> (fun y1 : nat => ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y1)) -> Peano.lt (NUMERAL 0) y1) (S y0))) -> forall y0 : nat, (fun y1 : nat => ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y1)) -> Peano.lt (NUMERAL 0) y1) y0.
Definition term30 := (((fun y0 : nat => forall y1 : nat, ((Peano.lt (NUMERAL 0) y0) /\ (Peano.lt y0 y1)) -> Peano.lt (NUMERAL 0) y1) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Peano.lt (NUMERAL 0) y1) /\ (Peano.lt y1 y2)) -> Peano.lt (NUMERAL 0) y2) y0) -> (fun y1 : nat => forall y2 : nat, ((Peano.lt (NUMERAL 0) y1) /\ (Peano.lt y1 y2)) -> Peano.lt (NUMERAL 0) y2) (S y0))) -> forall y0 : nat, (fun y1 : nat => forall y2 : nat, ((Peano.lt (NUMERAL 0) y1) /\ (Peano.lt y1 y2)) -> Peano.lt (NUMERAL 0) y2) y0.
Definition term4 := (((fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.lt y1 y2)) -> Peano.lt y0 y2) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, forall y3 : nat, ((Peano.lt y1 y2) /\ (Peano.lt y2 y3)) -> Peano.lt y1 y3) y0) -> (fun y1 : nat => forall y2 : nat, forall y3 : nat, ((Peano.lt y1 y2) /\ (Peano.lt y2 y3)) -> Peano.lt y1 y3) (S y0))) -> forall y0 : nat, (fun y1 : nat => forall y2 : nat, forall y3 : nat, ((Peano.lt y1 y2) /\ (Peano.lt y2 y3)) -> Peano.lt y1 y3) y0.
Definition term205 (x0 : nat) (x1 : nat) := imp ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (S x0) (S x1))).
Definition term0 := forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False.
Definition term3 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term139 (x0 : nat) (x1 : nat) := imp (((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) x1)) -> Peano.lt (S x0) x1).
Definition term158 (x0 : nat) (x1 : nat) := ((Peano.lt (S x1) (S x0)) /\ (Peano.lt (S x0) (NUMERAL 0))) -> Peano.lt (S x1) (NUMERAL 0).
Definition term175 (x0 : nat) (x1 : nat) := imp (((fun y0 : nat => ((Peano.lt (S x1) (S x0)) /\ (Peano.lt (S x0) y0)) -> Peano.lt (S x1) y0) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Peano.lt (S x1) (S x0)) /\ (Peano.lt (S x0) y1)) -> Peano.lt (S x1) y1) y0) -> (fun y1 : nat => ((Peano.lt (S x1) (S x0)) /\ (Peano.lt (S x0) y1)) -> Peano.lt (S x1) y1) (S y0))).
Definition term150 (x0 : nat) := imp (((fun y0 : nat => ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y0)) -> Peano.lt (S x0) y0) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y1)) -> Peano.lt (S x0) y1) y0) -> (fun y1 : nat => ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y1)) -> Peano.lt (S x0) y1) (S y0))).
Definition term125 (x0 : nat) := imp (((fun y0 : nat => forall y1 : nat, ((Peano.lt (S x0) y0) /\ (Peano.lt y0 y1)) -> Peano.lt (S x0) y1) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Peano.lt (S x0) y1) /\ (Peano.lt y1 y2)) -> Peano.lt (S x0) y2) y0) -> (fun y1 : nat => forall y2 : nat, ((Peano.lt (S x0) y1) /\ (Peano.lt y1 y2)) -> Peano.lt (S x0) y2) (S y0))).
Definition term100 (x0 : nat) := imp (((fun y0 : nat => ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (S x0) y0)) -> Peano.lt (NUMERAL 0) y0) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (S x0) y1)) -> Peano.lt (NUMERAL 0) y1) y0) -> (fun y1 : nat => ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (S x0) y1)) -> Peano.lt (NUMERAL 0) y1) (S y0))).
Definition term75 := imp (((fun y0 : nat => ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y0)) -> Peano.lt (NUMERAL 0) y0) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y1)) -> Peano.lt (NUMERAL 0) y1) y0) -> (fun y1 : nat => ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y1)) -> Peano.lt (NUMERAL 0) y1) (S y0))).
Definition term50 := imp (((fun y0 : nat => forall y1 : nat, ((Peano.lt (NUMERAL 0) y0) /\ (Peano.lt y0 y1)) -> Peano.lt (NUMERAL 0) y1) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Peano.lt (NUMERAL 0) y1) /\ (Peano.lt y1 y2)) -> Peano.lt (NUMERAL 0) y2) y0) -> (fun y1 : nat => forall y2 : nat, ((Peano.lt (NUMERAL 0) y1) /\ (Peano.lt y1 y2)) -> Peano.lt (NUMERAL 0) y2) (S y0))).
Definition term24 := imp (((fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.lt y1 y2)) -> Peano.lt y0 y2) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, forall y3 : nat, ((Peano.lt y1 y2) /\ (Peano.lt y2 y3)) -> Peano.lt y1 y3) y0) -> (fun y1 : nat => forall y2 : nat, forall y3 : nat, ((Peano.lt y1 y2) /\ (Peano.lt y2 y3)) -> Peano.lt y1 y3) (S y0))).
Definition term164 (x0 : nat) (x1 : nat) (x2 : nat) := imp (((Peano.lt (S x1) (S x0)) /\ (Peano.lt (S x0) x2)) -> Peano.lt (S x1) x2).
Definition term220 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((Peano.lt x0 y0) /\ (Peano.lt y0 y1)) -> Peano.lt x0 y1) x1.
Definition term111 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((Peano.lt (S x0) y0) /\ (Peano.lt y0 y1)) -> Peano.lt (S x0) y1) x1.
Definition term171 (x0 : nat) (x1 : nat) := forall y0 : nat, ((fun y1 : nat => ((Peano.lt (S x1) (S x0)) /\ (Peano.lt (S x0) y1)) -> Peano.lt (S x1) y1) y0) -> (fun y1 : nat => ((Peano.lt (S x1) (S x0)) /\ (Peano.lt (S x0) y1)) -> Peano.lt (S x1) y1) (S y0).
Definition term146 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y1)) -> Peano.lt (S x0) y1) y0) -> (fun y1 : nat => ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y1)) -> Peano.lt (S x0) y1) (S y0).
Definition term121 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Peano.lt (S x0) y1) /\ (Peano.lt y1 y2)) -> Peano.lt (S x0) y2) y0) -> (fun y1 : nat => forall y2 : nat, ((Peano.lt (S x0) y1) /\ (Peano.lt y1 y2)) -> Peano.lt (S x0) y2) (S y0).
Definition term96 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (S x0) y1)) -> Peano.lt (NUMERAL 0) y1) y0) -> (fun y1 : nat => ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (S x0) y1)) -> Peano.lt (NUMERAL 0) y1) (S y0).
Definition term71 := forall y0 : nat, ((fun y1 : nat => ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y1)) -> Peano.lt (NUMERAL 0) y1) y0) -> (fun y1 : nat => ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y1)) -> Peano.lt (NUMERAL 0) y1) (S y0).
Definition term46 := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Peano.lt (NUMERAL 0) y1) /\ (Peano.lt y1 y2)) -> Peano.lt (NUMERAL 0) y2) y0) -> (fun y1 : nat => forall y2 : nat, ((Peano.lt (NUMERAL 0) y1) /\ (Peano.lt y1 y2)) -> Peano.lt (NUMERAL 0) y2) (S y0).
Definition term20 := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, forall y3 : nat, ((Peano.lt y1 y2) /\ (Peano.lt y2 y3)) -> Peano.lt y1 y3) y0) -> (fun y1 : nat => forall y2 : nat, forall y3 : nat, ((Peano.lt y1 y2) /\ (Peano.lt y2 y3)) -> Peano.lt y1 y3) (S y0).
Definition term106 (x0 : nat) := fun y0 : nat => forall y1 : nat, ((Peano.lt (S x0) y0) /\ (Peano.lt y0 y1)) -> Peano.lt (S x0) y1.
Definition term31 := fun y0 : nat => forall y1 : nat, ((Peano.lt (NUMERAL 0) y0) /\ (Peano.lt y0 y1)) -> Peano.lt (NUMERAL 0) y1.
Definition term66 (x0 : nat) := ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) (S x0))) -> Peano.lt (NUMERAL 0) (S x0).
Definition term174 (x0 : nat) (x1 : nat) := (((Peano.lt (S x1) (S x0)) /\ (Peano.lt (S x0) (NUMERAL 0))) -> Peano.lt (S x1) (NUMERAL 0)) /\ (forall y0 : nat, (((Peano.lt (S x1) (S x0)) /\ (Peano.lt (S x0) y0)) -> Peano.lt (S x1) y0) -> ((Peano.lt (S x1) (S x0)) /\ (Peano.lt (S x0) (S y0))) -> Peano.lt (S x1) (S y0)).
Definition term149 (x0 : nat) := (((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) (NUMERAL 0))) -> Peano.lt (S x0) (NUMERAL 0)) /\ (forall y0 : nat, (((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y0)) -> Peano.lt (S x0) y0) -> ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) (S y0))) -> Peano.lt (S x0) (S y0)).
Definition term99 (x0 : nat) := (((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (S x0) (NUMERAL 0))) -> Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (forall y0 : nat, (((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (S x0) y0)) -> Peano.lt (NUMERAL 0) y0) -> ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (S x0) (S y0))) -> Peano.lt (NUMERAL 0) (S y0)).
Definition term74 := (((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) (NUMERAL 0))) -> Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (forall y0 : nat, (((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y0)) -> Peano.lt (NUMERAL 0) y0) -> ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) (S y0))) -> Peano.lt (NUMERAL 0) (S y0)).
Definition term93 (x0 : nat) (x1 : nat) := (((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (S x0) x1)) -> Peano.lt (NUMERAL 0) x1) -> ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (S x0) (S x1))) -> Peano.lt (NUMERAL 0) (S x1).
Definition term159 (x0 : nat) (x1 : nat) := and ((fun y0 : nat => ((Peano.lt (S x1) (S x0)) /\ (Peano.lt (S x0) y0)) -> Peano.lt (S x1) y0) (NUMERAL 0)).
Definition term134 (x0 : nat) := and ((fun y0 : nat => ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y0)) -> Peano.lt (S x0) y0) (NUMERAL 0)).
Definition term84 (x0 : nat) := and ((fun y0 : nat => ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (S x0) y0)) -> Peano.lt (NUMERAL 0) y0) (NUMERAL 0)).
Definition term59 := and ((fun y0 : nat => ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y0)) -> Peano.lt (NUMERAL 0) y0) (NUMERAL 0)).
Definition term216 (x0 : nat) (x1 : nat) := (Peano.lt x0 x1) /\ (Peano.lt (S x1) (NUMERAL 0)).
Definition term222 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Peano.lt x1 x0) /\ (Peano.lt x0 y0)) -> Peano.lt x1 y0) x2.
Definition term81 (x0 : nat) := fun y0 : nat => ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (S x0) y0)) -> Peano.lt (NUMERAL 0) y0.
Definition term56 := fun y0 : nat => ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y0)) -> Peano.lt (NUMERAL 0) y0.
Definition term165 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Peano.lt (S x1) (S x0)) /\ (Peano.lt (S x0) y0)) -> Peano.lt (S x1) y0) (S x2).
Definition term141 (x0 : nat) (x1 : nat) := ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) (S x1))) -> Peano.lt (S x0) (S x1).
Definition term1 (x0 : nat) := (fun y0 : nat => (Peano.lt y0 (NUMERAL 0)) = False) x0.
Definition term109 (x0 : nat) := and ((fun y0 : nat => forall y1 : nat, ((Peano.lt (S x0) y0) /\ (Peano.lt y0 y1)) -> Peano.lt (S x0) y1) (NUMERAL 0)).
Definition term34 := and ((fun y0 : nat => forall y1 : nat, ((Peano.lt (NUMERAL 0) y0) /\ (Peano.lt y0 y1)) -> Peano.lt (NUMERAL 0) y1) (NUMERAL 0)).
Definition term8 := and ((fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.lt y1 y2)) -> Peano.lt y0 y2) (NUMERAL 0)).
Definition term114 (x0 : nat) (x1 : nat) := imp (forall y0 : nat, ((Peano.lt (S x1) x0) /\ (Peano.lt x0 y0)) -> Peano.lt (S x1) y0).
Definition term39 (x0 : nat) := imp (forall y0 : nat, ((Peano.lt (NUMERAL 0) x0) /\ (Peano.lt x0 y0)) -> Peano.lt (NUMERAL 0) y0).
Definition term166 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.lt (S x1) (S x0)) /\ (Peano.lt (S x0) (S x2))) -> Peano.lt (S x1) (S x2).
Definition term110 (x0 : nat) := and (forall y0 : nat, ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y0)) -> Peano.lt (S x0) y0).
Definition term35 := and (forall y0 : nat, ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y0)) -> Peano.lt (NUMERAL 0) y0).
Definition term226 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((Peano.lt (S x0) (S x1)) /\ (Peano.lt (S x1) (S x2))).
Definition term40 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((Peano.lt (NUMERAL 0) y0) /\ (Peano.lt y0 y1)) -> Peano.lt (NUMERAL 0) y1) (S x0).
Definition term14 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.lt y1 y2)) -> Peano.lt y0 y2) (S x0).
Definition term181 := Peano.lt (NUMERAL 0) (NUMERAL 0).
Definition term107 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((Peano.lt (S x0) y0) /\ (Peano.lt y0 y1)) -> Peano.lt (S x0) y1) (NUMERAL 0).
Definition term32 := (fun y0 : nat => forall y1 : nat, ((Peano.lt (NUMERAL 0) y0) /\ (Peano.lt y0 y1)) -> Peano.lt (NUMERAL 0) y1) (NUMERAL 0).
Definition term6 := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.lt y1 y2)) -> Peano.lt y0 y2) (NUMERAL 0).
Definition term169 (x0 : nat) (x1 : nat) := fun y0 : nat => ((fun y1 : nat => ((Peano.lt (S x1) (S x0)) /\ (Peano.lt (S x0) y1)) -> Peano.lt (S x1) y1) y0) -> (fun y1 : nat => ((Peano.lt (S x1) (S x0)) /\ (Peano.lt (S x0) y1)) -> Peano.lt (S x1) y1) (S y0).
Definition term144 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y1)) -> Peano.lt (S x0) y1) y0) -> (fun y1 : nat => ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y1)) -> Peano.lt (S x0) y1) (S y0).
Definition term94 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (S x0) y1)) -> Peano.lt (NUMERAL 0) y1) y0) -> (fun y1 : nat => ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (S x0) y1)) -> Peano.lt (NUMERAL 0) y1) (S y0).
Definition term69 := fun y0 : nat => ((fun y1 : nat => ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y1)) -> Peano.lt (NUMERAL 0) y1) y0) -> (fun y1 : nat => ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y1)) -> Peano.lt (NUMERAL 0) y1) (S y0).
Definition term61 (x0 : nat) := (fun y0 : nat => ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y0)) -> Peano.lt (NUMERAL 0) y0) x0.
Definition term193 (x0 : nat) := Peano.lt (S x0) (NUMERAL 0).
Definition term126 (x0 : nat) := imp ((forall y0 : nat, ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y0)) -> Peano.lt (S x0) y0) /\ (forall y0 : nat, (forall y1 : nat, ((Peano.lt (S x0) y0) /\ (Peano.lt y0 y1)) -> Peano.lt (S x0) y1) -> forall y1 : nat, ((Peano.lt (S x0) (S y0)) /\ (Peano.lt (S y0) y1)) -> Peano.lt (S x0) y1)).
Definition term51 := imp ((forall y0 : nat, ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y0)) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (forall y1 : nat, ((Peano.lt (NUMERAL 0) y0) /\ (Peano.lt y0 y1)) -> Peano.lt (NUMERAL 0) y1) -> forall y1 : nat, ((Peano.lt (NUMERAL 0) (S y0)) /\ (Peano.lt (S y0) y1)) -> Peano.lt (NUMERAL 0) y1)).
Definition term25 := imp ((forall y0 : nat, forall y1 : nat, ((Peano.lt (NUMERAL 0) y0) /\ (Peano.lt y0 y1)) -> Peano.lt (NUMERAL 0) y1) /\ (forall y0 : nat, (forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.lt y1 y2)) -> Peano.lt y0 y2) -> forall y1 : nat, forall y2 : nat, ((Peano.lt (S y0) y1) /\ (Peano.lt y1 y2)) -> Peano.lt (S y0) y2)).
Definition term28 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.lt y1 y2)) -> Peano.lt y0 y2.
Definition term15 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.lt (S x0) y0) /\ (Peano.lt y0 y1)) -> Peano.lt (S x0) y1.
Definition term11 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.lt x0 y0) /\ (Peano.lt y0 y1)) -> Peano.lt x0 y1.
Definition term7 := forall y0 : nat, forall y1 : nat, ((Peano.lt (NUMERAL 0) y0) /\ (Peano.lt y0 y1)) -> Peano.lt (NUMERAL 0) y1.
Definition term210 (x0 : nat) := (Peano.lt (S x0) (NUMERAL 0)) /\ True.
Definition term194 (x0 : nat) := (Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (S x0) (NUMERAL 0)).
Definition term184 := (Peano.lt (NUMERAL 0) (NUMERAL 0)) -> Peano.lt (NUMERAL 0) (NUMERAL 0).
Definition term197 (x0 : nat) := imp (Peano.lt (S x0) (NUMERAL 0)).
Definition term170 (x0 : nat) (x1 : nat) := fun y0 : nat => (((Peano.lt (S x1) (S x0)) /\ (Peano.lt (S x0) y0)) -> Peano.lt (S x1) y0) -> ((Peano.lt (S x1) (S x0)) /\ (Peano.lt (S x0) (S y0))) -> Peano.lt (S x1) (S y0).
Definition term145 (x0 : nat) := fun y0 : nat => (((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y0)) -> Peano.lt (S x0) y0) -> ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) (S y0))) -> Peano.lt (S x0) (S y0).
Definition term95 (x0 : nat) := fun y0 : nat => (((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (S x0) y0)) -> Peano.lt (NUMERAL 0) y0) -> ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (S x0) (S y0))) -> Peano.lt (NUMERAL 0) (S y0).
Definition term70 := fun y0 : nat => (((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y0)) -> Peano.lt (NUMERAL 0) y0) -> ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) (S y0))) -> Peano.lt (NUMERAL 0) (S y0).
Definition term138 (x0 : nat) (x1 : nat) := imp ((fun y0 : nat => ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y0)) -> Peano.lt (S x0) y0) x1).
Definition term88 (x0 : nat) (x1 : nat) := imp ((fun y0 : nat => ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (S x0) y0)) -> Peano.lt (NUMERAL 0) y0) x1).
Definition term133 (x0 : nat) := ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) (NUMERAL 0))) -> Peano.lt (S x0) (NUMERAL 0).
Definition term91 (x0 : nat) (x1 : nat) := ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (S x0) (S x1))) -> Peano.lt (NUMERAL 0) (S x1).
Definition term209 (x0 : nat) (x1 : nat) := (Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) (S x1)).
Definition term179 (x0 : nat) (x1 : nat) := ((((Peano.lt (S x1) (S x0)) /\ (Peano.lt (S x0) (NUMERAL 0))) -> Peano.lt (S x1) (NUMERAL 0)) /\ (forall y0 : nat, (((Peano.lt (S x1) (S x0)) /\ (Peano.lt (S x0) y0)) -> Peano.lt (S x1) y0) -> ((Peano.lt (S x1) (S x0)) /\ (Peano.lt (S x0) (S y0))) -> Peano.lt (S x1) (S y0))) -> forall y0 : nat, ((Peano.lt (S x1) (S x0)) /\ (Peano.lt (S x0) y0)) -> Peano.lt (S x1) y0.
Definition term154 (x0 : nat) := ((((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) (NUMERAL 0))) -> Peano.lt (S x0) (NUMERAL 0)) /\ (forall y0 : nat, (((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y0)) -> Peano.lt (S x0) y0) -> ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) (S y0))) -> Peano.lt (S x0) (S y0))) -> forall y0 : nat, ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y0)) -> Peano.lt (S x0) y0.
Definition term104 (x0 : nat) := ((((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (S x0) (NUMERAL 0))) -> Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (forall y0 : nat, (((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (S x0) y0)) -> Peano.lt (NUMERAL 0) y0) -> ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (S x0) (S y0))) -> Peano.lt (NUMERAL 0) (S y0))) -> forall y0 : nat, ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (S x0) y0)) -> Peano.lt (NUMERAL 0) y0.
Definition term79 := ((((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) (NUMERAL 0))) -> Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (forall y0 : nat, (((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y0)) -> Peano.lt (NUMERAL 0) y0) -> ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) (S y0))) -> Peano.lt (NUMERAL 0) (S y0))) -> forall y0 : nat, ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y0)) -> Peano.lt (NUMERAL 0) y0.
Definition term113 (x0 : nat) (x1 : nat) := imp ((fun y0 : nat => forall y1 : nat, ((Peano.lt (S x0) y0) /\ (Peano.lt y0 y1)) -> Peano.lt (S x0) y1) x1).
Definition term203 (x0 : nat) (x1 : nat) := (Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (S x0) (S x1)).
Definition term201 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt (S x0) (S y0)) = (Peano.lt x0 y0)) x1.
Definition term64 (x0 : nat) := imp (((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) x0)) -> Peano.lt (NUMERAL 0) x0).
Definition term140 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y0)) -> Peano.lt (S x0) y0) (S x1).
Definition term90 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (S x0) y0)) -> Peano.lt (NUMERAL 0) y0) (S x1).
Definition term157 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Peano.lt (S x1) (S x0)) /\ (Peano.lt (S x0) y0)) -> Peano.lt (S x1) y0) (NUMERAL 0).
Definition term132 (x0 : nat) := (fun y0 : nat => ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y0)) -> Peano.lt (S x0) y0) (NUMERAL 0).
Definition term82 (x0 : nat) := (fun y0 : nat => ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (S x0) y0)) -> Peano.lt (NUMERAL 0) y0) (NUMERAL 0).
Definition term57 := (fun y0 : nat => ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y0)) -> Peano.lt (NUMERAL 0) y0) (NUMERAL 0).
Definition term206 (x0 : nat) (x1 : nat) := imp (Peano.lt x0 x1).
Definition term120 (x0 : nat) := fun y0 : nat => (forall y1 : nat, ((Peano.lt (S x0) y0) /\ (Peano.lt y0 y1)) -> Peano.lt (S x0) y1) -> forall y1 : nat, ((Peano.lt (S x0) (S y0)) /\ (Peano.lt (S y0) y1)) -> Peano.lt (S x0) y1.
Definition term45 := fun y0 : nat => (forall y1 : nat, ((Peano.lt (NUMERAL 0) y0) /\ (Peano.lt y0 y1)) -> Peano.lt (NUMERAL 0) y1) -> forall y1 : nat, ((Peano.lt (NUMERAL 0) (S y0)) /\ (Peano.lt (S y0) y1)) -> Peano.lt (NUMERAL 0) y1.
Definition term119 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, ((Peano.lt (S x0) y1) /\ (Peano.lt y1 y2)) -> Peano.lt (S x0) y2) y0) -> (fun y1 : nat => forall y2 : nat, ((Peano.lt (S x0) y1) /\ (Peano.lt y1 y2)) -> Peano.lt (S x0) y2) (S y0).
Definition term44 := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, ((Peano.lt (NUMERAL 0) y1) /\ (Peano.lt y1 y2)) -> Peano.lt (NUMERAL 0) y2) y0) -> (fun y1 : nat => forall y2 : nat, ((Peano.lt (NUMERAL 0) y1) /\ (Peano.lt y1 y2)) -> Peano.lt (NUMERAL 0) y2) (S y0).
Definition term18 := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, forall y3 : nat, ((Peano.lt y1 y2) /\ (Peano.lt y2 y3)) -> Peano.lt y1 y3) y0) -> (fun y1 : nat => forall y2 : nat, forall y3 : nat, ((Peano.lt y1 y2) /\ (Peano.lt y2 y3)) -> Peano.lt y1 y3) (S y0).
Definition term225 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.lt x0 x1) /\ (Peano.lt x1 x2).
Definition term214 (x0 : nat) (x1 : nat) := and (Peano.lt x0 x1).
Definition term212 (x0 : nat) (x1 : nat) := (Peano.lt (S x0) (NUMERAL 0)) -> Peano.lt x0 x1.
Definition term221 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Peano.lt x1 x0) /\ (Peano.lt x0 y0)) -> Peano.lt x1 y0.
Definition term117 (x0 : nat) (x1 : nat) := ((fun y0 : nat => forall y1 : nat, ((Peano.lt (S x0) y0) /\ (Peano.lt y0 y1)) -> Peano.lt (S x0) y1) x1) -> (fun y0 : nat => forall y1 : nat, ((Peano.lt (S x0) y0) /\ (Peano.lt y0 y1)) -> Peano.lt (S x0) y1) (S x1).
Definition term124 (x0 : nat) := (forall y0 : nat, ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y0)) -> Peano.lt (S x0) y0) /\ (forall y0 : nat, (forall y1 : nat, ((Peano.lt (S x0) y0) /\ (Peano.lt y0 y1)) -> Peano.lt (S x0) y1) -> forall y1 : nat, ((Peano.lt (S x0) (S y0)) /\ (Peano.lt (S y0) y1)) -> Peano.lt (S x0) y1).
Definition term49 := (forall y0 : nat, ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y0)) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (forall y1 : nat, ((Peano.lt (NUMERAL 0) y0) /\ (Peano.lt y0 y1)) -> Peano.lt (NUMERAL 0) y1) -> forall y1 : nat, ((Peano.lt (NUMERAL 0) (S y0)) /\ (Peano.lt (S y0) y1)) -> Peano.lt (NUMERAL 0) y1).
Definition term183 := imp (Peano.lt (NUMERAL 0) (NUMERAL 0)).
Definition term228 (x0 : nat) := (Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) (NUMERAL 0)).
Definition term2 (x0 : nat) := Peano.lt x0 (NUMERAL 0).
Definition term9 := and (forall y0 : nat, forall y1 : nat, ((Peano.lt (NUMERAL 0) y0) /\ (Peano.lt y0 y1)) -> Peano.lt (NUMERAL 0) y1).
Definition term189 := (Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ True.
Definition term215 (x0 : nat) (x1 : nat) := (Peano.lt (S x0) (S x1)) /\ (Peano.lt (S x1) (NUMERAL 0)).
Definition term231 (x0 : nat) (x1 : nat) := (Peano.lt x0 x1) /\ False.
Definition term127 (x0 : nat) := fun y0 : nat => (fun y1 : nat => forall y2 : nat, ((Peano.lt (S x0) y1) /\ (Peano.lt y1 y2)) -> Peano.lt (S x0) y2) y0.
Definition term52 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, ((Peano.lt (NUMERAL 0) y1) /\ (Peano.lt y1 y2)) -> Peano.lt (NUMERAL 0) y2) y0.
Definition term26 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, forall y3 : nat, ((Peano.lt y1 y2) /\ (Peano.lt y2 y3)) -> Peano.lt y1 y3) y0.
Definition term219 (x0 : nat) (x1 : nat) := ((Peano.lt x1 x0) /\ (Peano.lt (S x0) (NUMERAL 0))) -> Peano.lt (S x1) (NUMERAL 0).
Definition term199 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt (S y0) (S y1)) = (Peano.lt y0 y1)) x0.
Definition term36 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((Peano.lt (NUMERAL 0) y0) /\ (Peano.lt y0 y1)) -> Peano.lt (NUMERAL 0) y1) x0.
Definition term207 (x0 : nat) (x1 : nat) := (Peano.lt x0 x1) -> True.
Definition term19 := fun y0 : nat => (forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.lt y1 y2)) -> Peano.lt y0 y2) -> forall y1 : nat, forall y2 : nat, ((Peano.lt (S y0) y1) /\ (Peano.lt y1 y2)) -> Peano.lt (S y0) y2.
Definition term85 (x0 : nat) := and (((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (S x0) (NUMERAL 0))) -> Peano.lt (NUMERAL 0) (NUMERAL 0)).
Definition term60 := and (((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) (NUMERAL 0))) -> Peano.lt (NUMERAL 0) (NUMERAL 0)).
Definition term156 (x0 : nat) (x1 : nat) := fun y0 : nat => ((Peano.lt (S x1) (S x0)) /\ (Peano.lt (S x0) y0)) -> Peano.lt (S x1) y0.
Definition term131 (x0 : nat) := fun y0 : nat => ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y0)) -> Peano.lt (S x0) y0.
Definition term123 (x0 : nat) := ((fun y0 : nat => forall y1 : nat, ((Peano.lt (S x0) y0) /\ (Peano.lt y0 y1)) -> Peano.lt (S x0) y1) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Peano.lt (S x0) y1) /\ (Peano.lt y1 y2)) -> Peano.lt (S x0) y2) y0) -> (fun y1 : nat => forall y2 : nat, ((Peano.lt (S x0) y1) /\ (Peano.lt y1 y2)) -> Peano.lt (S x0) y2) (S y0)).
Definition term48 := ((fun y0 : nat => forall y1 : nat, ((Peano.lt (NUMERAL 0) y0) /\ (Peano.lt y0 y1)) -> Peano.lt (NUMERAL 0) y1) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Peano.lt (NUMERAL 0) y1) /\ (Peano.lt y1 y2)) -> Peano.lt (NUMERAL 0) y2) y0) -> (fun y1 : nat => forall y2 : nat, ((Peano.lt (NUMERAL 0) y1) /\ (Peano.lt y1 y2)) -> Peano.lt (NUMERAL 0) y2) (S y0)).
Definition term22 := ((fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.lt y1 y2)) -> Peano.lt y0 y2) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, forall y3 : nat, ((Peano.lt y1 y2) /\ (Peano.lt y2 y3)) -> Peano.lt y1 y3) y0) -> (fun y1 : nat => forall y2 : nat, forall y3 : nat, ((Peano.lt y1 y2) /\ (Peano.lt y2 y3)) -> Peano.lt y1 y3) (S y0)).
Definition term180 := (Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) (NUMERAL 0)).
Definition term202 (x0 : nat) (x1 : nat) := Peano.lt (S x0) (S x1).
Definition term223 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.lt x1 x0) /\ (Peano.lt x0 x2)) -> Peano.lt x1 x2.
Definition term160 (x0 : nat) (x1 : nat) := and (((Peano.lt (S x1) (S x0)) /\ (Peano.lt (S x0) (NUMERAL 0))) -> Peano.lt (S x1) (NUMERAL 0)).
Definition term135 (x0 : nat) := and (((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) (NUMERAL 0))) -> Peano.lt (S x0) (NUMERAL 0)).
Definition term192 (x0 : nat) := and (Peano.lt (NUMERAL 0) (S x0)).
Definition term227 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((Peano.lt x0 x1) /\ (Peano.lt x1 x2)).
Definition term224 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.lt (S x0) (S x1)) /\ (Peano.lt (S x1) (S x2)).
Definition term176 (x0 : nat) (x1 : nat) := imp ((((Peano.lt (S x1) (S x0)) /\ (Peano.lt (S x0) (NUMERAL 0))) -> Peano.lt (S x1) (NUMERAL 0)) /\ (forall y0 : nat, (((Peano.lt (S x1) (S x0)) /\ (Peano.lt (S x0) y0)) -> Peano.lt (S x1) y0) -> ((Peano.lt (S x1) (S x0)) /\ (Peano.lt (S x0) (S y0))) -> Peano.lt (S x1) (S y0))).
Definition term151 (x0 : nat) := imp ((((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) (NUMERAL 0))) -> Peano.lt (S x0) (NUMERAL 0)) /\ (forall y0 : nat, (((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y0)) -> Peano.lt (S x0) y0) -> ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) (S y0))) -> Peano.lt (S x0) (S y0))).
Definition term101 (x0 : nat) := imp ((((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (S x0) (NUMERAL 0))) -> Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (forall y0 : nat, (((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (S x0) y0)) -> Peano.lt (NUMERAL 0) y0) -> ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (S x0) (S y0))) -> Peano.lt (NUMERAL 0) (S y0))).
Definition term76 := imp ((((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) (NUMERAL 0))) -> Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (forall y0 : nat, (((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y0)) -> Peano.lt (NUMERAL 0) y0) -> ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) (S y0))) -> Peano.lt (NUMERAL 0) (S y0))).
Definition term211 (x0 : nat) (x1 : nat) := imp ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) (S x1))).
Definition term168 (x0 : nat) (x1 : nat) (x2 : nat) := (((Peano.lt (S x1) (S x0)) /\ (Peano.lt (S x0) x2)) -> Peano.lt (S x1) x2) -> ((Peano.lt (S x1) (S x0)) /\ (Peano.lt (S x0) (S x2))) -> Peano.lt (S x1) (S x2).
Definition term218 (x0 : nat) (x1 : nat) := imp ((Peano.lt x0 x1) /\ (Peano.lt (S x1) (NUMERAL 0))).
Definition term187 := and (Peano.lt (NUMERAL 0) (NUMERAL 0)).
Definition term172 (x0 : nat) (x1 : nat) := forall y0 : nat, (((Peano.lt (S x1) (S x0)) /\ (Peano.lt (S x0) y0)) -> Peano.lt (S x1) y0) -> ((Peano.lt (S x1) (S x0)) /\ (Peano.lt (S x0) (S y0))) -> Peano.lt (S x1) (S y0).
Definition term147 (x0 : nat) := forall y0 : nat, (((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y0)) -> Peano.lt (S x0) y0) -> ((Peano.lt (S x0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) (S y0))) -> Peano.lt (S x0) (S y0).
Definition term97 (x0 : nat) := forall y0 : nat, (((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (S x0) y0)) -> Peano.lt (NUMERAL 0) y0) -> ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (S x0) (S y0))) -> Peano.lt (NUMERAL 0) (S y0).
Definition term72 := forall y0 : nat, (((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y0)) -> Peano.lt (NUMERAL 0) y0) -> ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) (S y0))) -> Peano.lt (NUMERAL 0) (S y0).
Definition term167 (x0 : nat) (x1 : nat) (x2 : nat) := ((fun y0 : nat => ((Peano.lt (S x1) (S x0)) /\ (Peano.lt (S x0) y0)) -> Peano.lt (S x1) y0) x2) -> (fun y0 : nat => ((Peano.lt (S x1) (S x0)) /\ (Peano.lt (S x0) y0)) -> Peano.lt (S x1) y0) (S x2).
Definition term188 (x0 : nat) := (Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) (S x0)).
Definition term163 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((fun y0 : nat => ((Peano.lt (S x1) (S x0)) /\ (Peano.lt (S x0) y0)) -> Peano.lt (S x1) y0) x2).
Definition term87 (x0 : nat) (x1 : nat) := ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (S x0) x1)) -> Peano.lt (NUMERAL 0) x1.
Definition term63 (x0 : nat) := imp ((fun y0 : nat => ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) y0)) -> Peano.lt (NUMERAL 0) y0) x0).
Definition term42 (x0 : nat) := ((fun y0 : nat => forall y1 : nat, ((Peano.lt (NUMERAL 0) y0) /\ (Peano.lt y0 y1)) -> Peano.lt (NUMERAL 0) y1) x0) -> (fun y0 : nat => forall y1 : nat, ((Peano.lt (NUMERAL 0) y0) /\ (Peano.lt y0 y1)) -> Peano.lt (NUMERAL 0) y1) (S x0).
Definition term16 (x0 : nat) := ((fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.lt y1 y2)) -> Peano.lt y0 y2) x0) -> (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.lt y1 y2)) -> Peano.lt y0 y2) (S x0).
Definition term128 (x0 : nat) := forall y0 : nat, (fun y1 : nat => forall y2 : nat, ((Peano.lt (S x0) y1) /\ (Peano.lt y1 y2)) -> Peano.lt (S x0) y2) y0.
Definition term53 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, ((Peano.lt (NUMERAL 0) y1) /\ (Peano.lt y1 y2)) -> Peano.lt (NUMERAL 0) y2) y0.
Definition term27 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, forall y3 : nat, ((Peano.lt y1 y2) /\ (Peano.lt y2 y3)) -> Peano.lt y1 y3) y0.
Definition term13 (x0 : nat) := imp (forall y0 : nat, forall y1 : nat, ((Peano.lt x0 y0) /\ (Peano.lt y0 y1)) -> Peano.lt x0 y1).
Definition term68 (x0 : nat) := (((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) x0)) -> Peano.lt (NUMERAL 0) x0) -> ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) (S x0))) -> Peano.lt (NUMERAL 0) (S x0).
Definition term23 := (forall y0 : nat, forall y1 : nat, ((Peano.lt (NUMERAL 0) y0) /\ (Peano.lt y0 y1)) -> Peano.lt (NUMERAL 0) y1) /\ (forall y0 : nat, (forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.lt y1 y2)) -> Peano.lt y0 y2) -> forall y1 : nat, forall y2 : nat, ((Peano.lt (S y0) y1) /\ (Peano.lt y1 y2)) -> Peano.lt (S y0) y2).
Definition term62 (x0 : nat) := ((Peano.lt (NUMERAL 0) (NUMERAL 0)) /\ (Peano.lt (NUMERAL 0) x0)) -> Peano.lt (NUMERAL 0) x0.
Definition term195 (x0 : nat) := True /\ (Peano.lt (S x0) (NUMERAL 0)).
Definition term5 := fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.lt y1 y2)) -> Peano.lt y0 y2.
Definition term204 (x0 : nat) (x1 : nat) := True /\ (Peano.lt x0 x1).
Definition term118 (x0 : nat) (x1 : nat) := (forall y0 : nat, ((Peano.lt (S x1) x0) /\ (Peano.lt x0 y0)) -> Peano.lt (S x1) y0) -> forall y0 : nat, ((Peano.lt (S x1) (S x0)) /\ (Peano.lt (S x0) y0)) -> Peano.lt (S x1) y0.
Definition term43 (x0 : nat) := (forall y0 : nat, ((Peano.lt (NUMERAL 0) x0) /\ (Peano.lt x0 y0)) -> Peano.lt (NUMERAL 0) y0) -> forall y0 : nat, ((Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (S x0) y0)) -> Peano.lt (NUMERAL 0) y0.
Definition term185 (x0 : nat) := (fun y0 : nat => Peano.lt (NUMERAL 0) (S y0)) x0.
