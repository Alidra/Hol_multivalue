Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term71 (x0 : hreal) (x1 : hreal) := @eq Prop (forall y0 : prod hreal hreal, forall y1 : prod hreal hreal, ((treal_eq (@pair hreal hreal x0 x1) y0) /\ (treal_eq y0 y1)) -> treal_eq (@pair hreal hreal x0 x1) y1).
Definition term54 := @eq Prop (forall y0 : prod hreal hreal, forall y1 : prod hreal hreal, forall y2 : prod hreal hreal, ((treal_eq y0 y1) /\ (treal_eq y1 y2)) -> treal_eq y0 y2).
Definition term56 (x0 : hreal) (x1 : hreal) := forall y0 : prod hreal hreal, forall y1 : prod hreal hreal, ((treal_eq (@pair hreal hreal x0 x1) y0) /\ (treal_eq y0 y1)) -> treal_eq (@pair hreal hreal x0 x1) y1.
Definition term50 (x0 : prod hreal hreal) := forall y0 : prod hreal hreal, forall y1 : prod hreal hreal, ((treal_eq x0 y0) /\ (treal_eq y0 y1)) -> treal_eq x0 y1.
Definition term15 (x0 : hreal) (x1 : hreal) := fun y0 : hreal => (hreal_add x0 (hreal_add x1 y0)) = (hreal_add (hreal_add x0 x1) y0).
Definition term95 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := fun y0 : hreal => forall y1 : hreal, (fun y2 : prod hreal hreal => ((treal_eq (@pair hreal hreal x2 x3) (@pair hreal hreal x0 x1)) /\ (treal_eq (@pair hreal hreal x0 x1) y2)) -> treal_eq (@pair hreal hreal x2 x3) y2) (@pair hreal hreal y0 y1).
Definition term78 (x0 : hreal) (x1 : hreal) := fun y0 : hreal => forall y1 : hreal, (fun y2 : prod hreal hreal => forall y3 : prod hreal hreal, ((treal_eq (@pair hreal hreal x0 x1) y2) /\ (treal_eq y2 y3)) -> treal_eq (@pair hreal hreal x0 x1) y3) (@pair hreal hreal y0 y1).
Definition term61 := fun y0 : hreal => forall y1 : hreal, (fun y2 : prod hreal hreal => forall y3 : prod hreal hreal, forall y4 : prod hreal hreal, ((treal_eq y2 y3) /\ (treal_eq y3 y4)) -> treal_eq y2 y4) (@pair hreal hreal y0 y1).
Definition term92 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) (x4 : hreal) := fun y0 : hreal => ((treal_eq (@pair hreal hreal x2 x3) (@pair hreal hreal x0 x1)) /\ (treal_eq (@pair hreal hreal x0 x1) (@pair hreal hreal x4 y0))) -> treal_eq (@pair hreal hreal x2 x3) (@pair hreal hreal x4 y0).
Definition term93 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) (x4 : hreal) := forall y0 : hreal, (fun y1 : prod hreal hreal => ((treal_eq (@pair hreal hreal x2 x3) (@pair hreal hreal x0 x1)) /\ (treal_eq (@pair hreal hreal x0 x1) y1)) -> treal_eq (@pair hreal hreal x2 x3) y1) (@pair hreal hreal x4 y0).
Definition term29 (x0 : hreal) (x1 : hreal) (x2 : hreal) := (fun y0 : hreal => ((hreal_add x0 x1) = (hreal_add x0 y0)) = (x1 = y0)) x2.
Definition term18 (x0 : hreal) := fun y0 : hreal => forall y1 : hreal, (hreal_add x0 (hreal_add y0 y1)) = (hreal_add (hreal_add x0 y0) y1).
Definition term128 (x0 : hreal) (x1 : hreal) (x2 : hreal) := @eq hreal (hreal_add x0 (hreal_add x1 x2)).
Definition term39 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := (fun y0 : hreal => (treal_eq (@pair hreal hreal x0 y0) (@pair hreal hreal x2 x1)) = ((hreal_add x0 x1) = (hreal_add x2 y0))) x3.
Definition term84 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) (x4 : prod hreal hreal) := (fun y0 : prod hreal hreal => ((treal_eq (@pair hreal hreal x2 x3) (@pair hreal hreal x0 x1)) /\ (treal_eq (@pair hreal hreal x0 x1) y0)) -> treal_eq (@pair hreal hreal x2 x3) y0) x4.
Definition term42 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := forall y0 : prod a1 a0, x0 y0.
Definition term7 (x0 : hreal) (x1 : hreal) (x2 : hreal) := (fun y0 : hreal => ((hreal_add x0 y0) = (hreal_add x1 y0)) = (x0 = x1)) x2.
Definition term37 (x0 : hreal) (x1 : hreal) (x2 : hreal) := (fun y0 : hreal => forall y1 : hreal, (treal_eq (@pair hreal hreal x0 y1) (@pair hreal hreal y0 x1)) = ((hreal_add x0 x1) = (hreal_add y0 y1))) x2.
Definition term69 (x0 : hreal) (x1 : hreal) := fun y0 : prod hreal hreal => (fun y1 : prod hreal hreal => forall y2 : prod hreal hreal, ((treal_eq (@pair hreal hreal x0 x1) y1) /\ (treal_eq y1 y2)) -> treal_eq (@pair hreal hreal x0 x1) y2) y0.
Definition term51 := fun y0 : prod hreal hreal => (fun y1 : prod hreal hreal => forall y2 : prod hreal hreal, forall y3 : prod hreal hreal, ((treal_eq y1 y2) /\ (treal_eq y2 y3)) -> treal_eq y1 y3) y0.
Definition term89 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) (x4 : hreal) (x5 : hreal) := (fun y0 : prod hreal hreal => ((treal_eq (@pair hreal hreal x2 x3) (@pair hreal hreal x0 x1)) /\ (treal_eq (@pair hreal hreal x0 x1) y0)) -> treal_eq (@pair hreal hreal x2 x3) y0) (@pair hreal hreal x4 x5).
Definition term14 (x0 : hreal) (x1 : hreal) (x2 : hreal) := hreal_add (hreal_add x0 x1) x2.
Definition term117 (x0 : hreal) (x1 : hreal) := hreal_add (hreal_add x0 x1).
Definition term125 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := @eq hreal (hreal_add x0 (hreal_add x1 (hreal_add x2 x3))).
Definition term127 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) (x4 : hreal) := ((hreal_add x2 (hreal_add x1 x0)) = (hreal_add x4 (hreal_add x3 x0))) -> (hreal_add x1 x2) = (hreal_add x3 x4).
Definition term76 (x0 : hreal) (x1 : hreal) (x2 : hreal) := forall y0 : hreal, (fun y1 : prod hreal hreal => forall y2 : prod hreal hreal, ((treal_eq (@pair hreal hreal x0 x1) y1) /\ (treal_eq y1 y2)) -> treal_eq (@pair hreal hreal x0 x1) y2) (@pair hreal hreal x2 y0).
Definition term59 (x0 : hreal) := forall y0 : hreal, (fun y1 : prod hreal hreal => forall y2 : prod hreal hreal, forall y3 : prod hreal hreal, ((treal_eq y1 y2) /\ (treal_eq y2 y3)) -> treal_eq y1 y3) (@pair hreal hreal x0 y0).
Definition term87 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := @eq Prop (forall y0 : prod hreal hreal, (fun y1 : prod hreal hreal => ((treal_eq (@pair hreal hreal x2 x3) (@pair hreal hreal x0 x1)) /\ (treal_eq (@pair hreal hreal x0 x1) y1)) -> treal_eq (@pair hreal hreal x2 x3) y1) y0).
Definition term70 (x0 : hreal) (x1 : hreal) := @eq Prop (forall y0 : prod hreal hreal, (fun y1 : prod hreal hreal => forall y2 : prod hreal hreal, ((treal_eq (@pair hreal hreal x0 x1) y1) /\ (treal_eq y1 y2)) -> treal_eq (@pair hreal hreal x0 x1) y2) y0).
Definition term53 := @eq Prop (forall y0 : prod hreal hreal, (fun y1 : prod hreal hreal => forall y2 : prod hreal hreal, forall y3 : prod hreal hreal, ((treal_eq y1 y2) /\ (treal_eq y2 y3)) -> treal_eq y1 y3) y0).
Definition term57 (x0 : hreal) := fun y0 : hreal => (fun y1 : prod hreal hreal => forall y2 : prod hreal hreal, forall y3 : prod hreal hreal, ((treal_eq y1 y2) /\ (treal_eq y2 y3)) -> treal_eq y1 y3) (@pair hreal hreal x0 y0).
Definition term35 (x0 : hreal) (x1 : hreal) := (fun y0 : hreal => forall y1 : hreal, forall y2 : hreal, (treal_eq (@pair hreal hreal x0 y2) (@pair hreal hreal y1 y0)) = ((hreal_add x0 y0) = (hreal_add y1 y2))) x1.
Definition term98 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := and (treal_eq (@pair hreal hreal x0 x1) (@pair hreal hreal x2 x3)).
Definition term83 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := fun y0 : prod hreal hreal => ((treal_eq (@pair hreal hreal x2 x3) (@pair hreal hreal x0 x1)) /\ (treal_eq (@pair hreal hreal x0 x1) y0)) -> treal_eq (@pair hreal hreal x2 x3) y0.
Definition term99 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := and ((hreal_add x0 x1) = (hreal_add x2 x3)).
Definition term48 := fun y0 : prod hreal hreal => forall y1 : prod hreal hreal, forall y2 : prod hreal hreal, ((treal_eq y0 y1) /\ (treal_eq y1 y2)) -> treal_eq y0 y2.
Definition term124 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := hreal_add x0 (hreal_add x1 (hreal_add x2 x3)).
Definition term75 (x0 : hreal) (x1 : hreal) (x2 : hreal) := fun y0 : hreal => forall y1 : prod hreal hreal, ((treal_eq (@pair hreal hreal x1 x2) (@pair hreal hreal x0 y0)) /\ (treal_eq (@pair hreal hreal x0 y0) y1)) -> treal_eq (@pair hreal hreal x1 x2) y1.
Definition term32 (x0 : hreal) (x1 : hreal) (x2 : hreal) := (fun y0 : hreal => (hreal_add (hreal_add x0 x1) y0) = (hreal_add x0 (hreal_add x1 y0))) x2.
Definition term67 (x0 : hreal) (x1 : hreal) (x2 : prod hreal hreal) := (fun y0 : prod hreal hreal => forall y1 : prod hreal hreal, ((treal_eq (@pair hreal hreal x0 x1) y0) /\ (treal_eq y0 y1)) -> treal_eq (@pair hreal hreal x0 x1) y1) x2.
Definition term131 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := ((hreal_add x1 x0) = (hreal_add x3 x2)) -> (hreal_add x0 x1) = (hreal_add x2 x3).
Definition term66 (x0 : hreal) (x1 : hreal) := fun y0 : prod hreal hreal => forall y1 : prod hreal hreal, ((treal_eq (@pair hreal hreal x0 x1) y0) /\ (treal_eq y0 y1)) -> treal_eq (@pair hreal hreal x0 x1) y1.
Definition term103 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) (x4 : hreal) (x5 : hreal) := imp (((hreal_add x0 x5) = (hreal_add x2 x1)) /\ ((hreal_add x2 x3) = (hreal_add x4 x5))).
Definition term12 (x0 : hreal) (x1 : hreal) (x2 : hreal) := (fun y0 : hreal => (hreal_add x0 (hreal_add x1 y0)) = (hreal_add (hreal_add x0 x1) y0)) x2.
Definition term116 := forall y0 : hreal, forall y1 : hreal, forall y2 : hreal, forall y3 : hreal, forall y4 : hreal, forall y5 : hreal, (((hreal_add y0 y3) = (hreal_add y2 y1)) /\ ((hreal_add y2 y5) = (hreal_add y4 y3))) -> (hreal_add y0 y5) = (hreal_add y4 y1).
Definition term114 (x0 : hreal) := forall y0 : hreal, forall y1 : hreal, forall y2 : hreal, forall y3 : hreal, forall y4 : hreal, (((hreal_add x0 y2) = (hreal_add y1 y0)) /\ ((hreal_add y1 y4) = (hreal_add y3 y2))) -> (hreal_add x0 y4) = (hreal_add y3 y0).
Definition term112 (x0 : hreal) (x1 : hreal) := forall y0 : hreal, forall y1 : hreal, forall y2 : hreal, forall y3 : hreal, (((hreal_add x0 y1) = (hreal_add y0 x1)) /\ ((hreal_add y0 y3) = (hreal_add y2 y1))) -> (hreal_add x0 y3) = (hreal_add y2 x1).
Definition term110 (x0 : hreal) (x1 : hreal) (x2 : hreal) := forall y0 : hreal, forall y1 : hreal, forall y2 : hreal, (((hreal_add x1 y0) = (hreal_add x0 x2)) /\ ((hreal_add x0 y2) = (hreal_add y1 y0))) -> (hreal_add x1 y2) = (hreal_add y1 x2).
Definition term108 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := forall y0 : hreal, forall y1 : hreal, (((hreal_add x2 x1) = (hreal_add x0 x3)) /\ ((hreal_add x0 y1) = (hreal_add y0 x1))) -> (hreal_add x2 y1) = (hreal_add y0 x3).
Definition term97 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := forall y0 : hreal, forall y1 : hreal, ((treal_eq (@pair hreal hreal x2 x3) (@pair hreal hreal x0 x1)) /\ (treal_eq (@pair hreal hreal x0 x1) (@pair hreal hreal y0 y1))) -> treal_eq (@pair hreal hreal x2 x3) (@pair hreal hreal y0 y1).
Definition term82 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := forall y0 : hreal, forall y1 : hreal, (fun y2 : prod hreal hreal => ((treal_eq (@pair hreal hreal x2 x3) (@pair hreal hreal x0 x1)) /\ (treal_eq (@pair hreal hreal x0 x1) y2)) -> treal_eq (@pair hreal hreal x2 x3) y2) (@pair hreal hreal y0 y1).
Definition term80 (x0 : hreal) (x1 : hreal) := forall y0 : hreal, forall y1 : hreal, forall y2 : prod hreal hreal, ((treal_eq (@pair hreal hreal x0 x1) (@pair hreal hreal y0 y1)) /\ (treal_eq (@pair hreal hreal y0 y1) y2)) -> treal_eq (@pair hreal hreal x0 x1) y2.
Definition term77 (x0 : hreal) (x1 : hreal) (x2 : hreal) := forall y0 : hreal, forall y1 : prod hreal hreal, ((treal_eq (@pair hreal hreal x1 x2) (@pair hreal hreal x0 y0)) /\ (treal_eq (@pair hreal hreal x0 y0) y1)) -> treal_eq (@pair hreal hreal x1 x2) y1.
Definition term65 (x0 : hreal) (x1 : hreal) := forall y0 : hreal, forall y1 : hreal, (fun y2 : prod hreal hreal => forall y3 : prod hreal hreal, ((treal_eq (@pair hreal hreal x0 x1) y2) /\ (treal_eq y2 y3)) -> treal_eq (@pair hreal hreal x0 x1) y3) (@pair hreal hreal y0 y1).
Definition term63 := forall y0 : hreal, forall y1 : hreal, forall y2 : prod hreal hreal, forall y3 : prod hreal hreal, ((treal_eq (@pair hreal hreal y0 y1) y2) /\ (treal_eq y2 y3)) -> treal_eq (@pair hreal hreal y0 y1) y3.
Definition term60 (x0 : hreal) := forall y0 : hreal, forall y1 : prod hreal hreal, forall y2 : prod hreal hreal, ((treal_eq (@pair hreal hreal x0 y0) y1) /\ (treal_eq y1 y2)) -> treal_eq (@pair hreal hreal x0 y0) y2.
Definition term47 := forall y0 : hreal, forall y1 : hreal, (fun y2 : prod hreal hreal => forall y3 : prod hreal hreal, forall y4 : prod hreal hreal, ((treal_eq y2 y3) /\ (treal_eq y3 y4)) -> treal_eq y2 y4) (@pair hreal hreal y0 y1).
Definition term45 (x0 : type1233) := forall y0 : hreal, forall y1 : hreal, x0 (@pair hreal hreal y0 y1).
Definition term36 (x0 : hreal) (x1 : hreal) := forall y0 : hreal, forall y1 : hreal, (treal_eq (@pair hreal hreal x0 y1) (@pair hreal hreal y0 x1)) = ((hreal_add x0 x1) = (hreal_add y0 y1)).
Definition term34 (x0 : hreal) := forall y0 : hreal, forall y1 : hreal, forall y2 : hreal, (treal_eq (@pair hreal hreal x0 y2) (@pair hreal hreal y1 y0)) = ((hreal_add x0 y0) = (hreal_add y1 y2)).
Definition term26 (x0 : hreal) := forall y0 : hreal, forall y1 : hreal, ((hreal_add x0 y0) = (hreal_add x0 y1)) = (y0 = y1).
Definition term24 := forall y0 : hreal, forall y1 : hreal, forall y2 : hreal, (hreal_add (hreal_add y0 y1) y2) = (hreal_add y0 (hreal_add y1 y2)).
Definition term23 := forall y0 : hreal, forall y1 : hreal, forall y2 : hreal, (hreal_add y0 (hreal_add y1 y2)) = (hreal_add (hreal_add y0 y1) y2).
Definition term20 (x0 : hreal) := forall y0 : hreal, forall y1 : hreal, (hreal_add (hreal_add x0 y0) y1) = (hreal_add x0 (hreal_add y0 y1)).
Definition term9 (x0 : hreal) := forall y0 : hreal, forall y1 : hreal, (hreal_add x0 (hreal_add y0 y1)) = (hreal_add (hreal_add x0 y0) y1).
Definition term4 (x0 : hreal) := forall y0 : hreal, forall y1 : hreal, ((hreal_add x0 y1) = (hreal_add y0 y1)) = (x0 = y0).
Definition term52 := forall y0 : prod hreal hreal, forall y1 : prod hreal hreal, forall y2 : prod hreal hreal, ((treal_eq y0 y1) /\ (treal_eq y1 y2)) -> treal_eq y0 y2.
Definition term106 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) (x4 : hreal) := forall y0 : hreal, (((hreal_add x2 x1) = (hreal_add x0 x4)) /\ ((hreal_add x0 y0) = (hreal_add x3 x1))) -> (hreal_add x2 y0) = (hreal_add x3 x4).
Definition term94 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) (x4 : hreal) := forall y0 : hreal, ((treal_eq (@pair hreal hreal x2 x3) (@pair hreal hreal x0 x1)) /\ (treal_eq (@pair hreal hreal x0 x1) (@pair hreal hreal x4 y0))) -> treal_eq (@pair hreal hreal x2 x3) (@pair hreal hreal x4 y0).
Definition term119 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := @eq hreal (hreal_add (hreal_add x0 x1) (hreal_add x2 x3)).
Definition term130 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := imp ((hreal_add x0 x1) = (hreal_add x2 x3)).
Definition term129 (x0 : hreal) (x1 : hreal) (x2 : hreal) := @eq hreal (hreal_add (hreal_add x0 x1) x2).
Definition term102 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) (x4 : hreal) (x5 : hreal) := imp ((treal_eq (@pair hreal hreal x0 x1) (@pair hreal hreal x2 x3)) /\ (treal_eq (@pair hreal hreal x2 x3) (@pair hreal hreal x4 x5))).
Definition term90 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) (x4 : hreal) (x5 : hreal) := ((treal_eq (@pair hreal hreal x2 x3) (@pair hreal hreal x0 x1)) /\ (treal_eq (@pair hreal hreal x0 x1) (@pair hreal hreal x4 x5))) -> treal_eq (@pair hreal hreal x2 x3) (@pair hreal hreal x4 x5).
Definition term11 (x0 : hreal) (x1 : hreal) := forall y0 : hreal, (hreal_add x0 (hreal_add x1 y0)) = (hreal_add (hreal_add x0 x1) y0).
Definition term100 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) (x4 : hreal) (x5 : hreal) := (treal_eq (@pair hreal hreal x0 x1) (@pair hreal hreal x2 x3)) /\ (treal_eq (@pair hreal hreal x2 x3) (@pair hreal hreal x4 x5)).
Definition term74 (x0 : hreal) (x1 : hreal) (x2 : hreal) := fun y0 : hreal => (fun y1 : prod hreal hreal => forall y2 : prod hreal hreal, ((treal_eq (@pair hreal hreal x0 x1) y1) /\ (treal_eq y1 y2)) -> treal_eq (@pair hreal hreal x0 x1) y2) (@pair hreal hreal x2 y0).
Definition term115 := fun y0 : hreal => forall y1 : hreal, forall y2 : hreal, forall y3 : hreal, forall y4 : hreal, forall y5 : hreal, (((hreal_add y0 y3) = (hreal_add y2 y1)) /\ ((hreal_add y2 y5) = (hreal_add y4 y3))) -> (hreal_add y0 y5) = (hreal_add y4 y1).
Definition term113 (x0 : hreal) := fun y0 : hreal => forall y1 : hreal, forall y2 : hreal, forall y3 : hreal, forall y4 : hreal, (((hreal_add x0 y2) = (hreal_add y1 y0)) /\ ((hreal_add y1 y4) = (hreal_add y3 y2))) -> (hreal_add x0 y4) = (hreal_add y3 y0).
Definition term111 (x0 : hreal) (x1 : hreal) := fun y0 : hreal => forall y1 : hreal, forall y2 : hreal, forall y3 : hreal, (((hreal_add x0 y1) = (hreal_add y0 x1)) /\ ((hreal_add y0 y3) = (hreal_add y2 y1))) -> (hreal_add x0 y3) = (hreal_add y2 x1).
Definition term109 (x0 : hreal) (x1 : hreal) (x2 : hreal) := fun y0 : hreal => forall y1 : hreal, forall y2 : hreal, (((hreal_add x1 y0) = (hreal_add x0 x2)) /\ ((hreal_add x0 y2) = (hreal_add y1 y0))) -> (hreal_add x1 y2) = (hreal_add y1 x2).
Definition term79 (x0 : hreal) (x1 : hreal) := fun y0 : hreal => forall y1 : hreal, forall y2 : prod hreal hreal, ((treal_eq (@pair hreal hreal x0 x1) (@pair hreal hreal y0 y1)) /\ (treal_eq (@pair hreal hreal y0 y1) y2)) -> treal_eq (@pair hreal hreal x0 x1) y2.
Definition term62 := fun y0 : hreal => forall y1 : hreal, forall y2 : prod hreal hreal, forall y3 : prod hreal hreal, ((treal_eq (@pair hreal hreal y0 y1) y2) /\ (treal_eq y2 y3)) -> treal_eq (@pair hreal hreal y0 y1) y3.
Definition term22 := fun y0 : hreal => forall y1 : hreal, forall y2 : hreal, (hreal_add (hreal_add y0 y1) y2) = (hreal_add y0 (hreal_add y1 y2)).
Definition term21 := fun y0 : hreal => forall y1 : hreal, forall y2 : hreal, (hreal_add y0 (hreal_add y1 y2)) = (hreal_add (hreal_add y0 y1) y2).
Definition term44 (x0 : type1233) := forall y0 : prod hreal hreal, x0 y0.
Definition term107 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := fun y0 : hreal => forall y1 : hreal, (((hreal_add x2 x1) = (hreal_add x0 x3)) /\ ((hreal_add x0 y1) = (hreal_add y0 x1))) -> (hreal_add x2 y1) = (hreal_add y0 x3).
Definition term96 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := fun y0 : hreal => forall y1 : hreal, ((treal_eq (@pair hreal hreal x2 x3) (@pair hreal hreal x0 x1)) /\ (treal_eq (@pair hreal hreal x0 x1) (@pair hreal hreal y0 y1))) -> treal_eq (@pair hreal hreal x2 x3) (@pair hreal hreal y0 y1).
Definition term19 (x0 : hreal) := fun y0 : hreal => forall y1 : hreal, (hreal_add (hreal_add x0 y0) y1) = (hreal_add x0 (hreal_add y0 y1)).
Definition term118 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := hreal_add (hreal_add x0 x1) (hreal_add x2 x3).
Definition term28 (x0 : hreal) (x1 : hreal) := forall y0 : hreal, ((hreal_add x0 x1) = (hreal_add x0 y0)) = (x1 = y0).
Definition term85 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) (x4 : prod hreal hreal) := ((treal_eq (@pair hreal hreal x2 x3) (@pair hreal hreal x0 x1)) /\ (treal_eq (@pair hreal hreal x0 x1) x4)) -> treal_eq (@pair hreal hreal x2 x3) x4.
Definition term16 (x0 : hreal) (x1 : hreal) := fun y0 : hreal => (hreal_add (hreal_add x0 x1) y0) = (hreal_add x0 (hreal_add x1 y0)).
Definition term43 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := forall y0 : a1, forall y1 : a0, x0 (@pair a1 a0 y0 y1).
Definition term2 (x0 : hreal) (x1 : hreal) := (fun y0 : hreal => (hreal_add x0 y0) = (hreal_add y0 x0)) x1.
Definition term0 (x0 : hreal) := (fun y0 : hreal => forall y1 : hreal, (hreal_add y0 y1) = (hreal_add y1 y0)) x0.
Definition term81 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := forall y0 : prod hreal hreal, (fun y1 : prod hreal hreal => ((treal_eq (@pair hreal hreal x2 x3) (@pair hreal hreal x0 x1)) /\ (treal_eq (@pair hreal hreal x0 x1) y1)) -> treal_eq (@pair hreal hreal x2 x3) y1) y0.
Definition term126 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) (x4 : hreal) := imp ((hreal_add x0 (hreal_add x1 x4)) = (hreal_add x2 (hreal_add x3 x4))).
Definition term31 (x0 : hreal) (x1 : hreal) := (fun y0 : hreal => forall y1 : hreal, (hreal_add (hreal_add x0 y0) y1) = (hreal_add x0 (hreal_add y0 y1))) x1.
Definition term27 (x0 : hreal) (x1 : hreal) := (fun y0 : hreal => forall y1 : hreal, ((hreal_add x0 y0) = (hreal_add x0 y1)) = (y0 = y1)) x1.
Definition term10 (x0 : hreal) (x1 : hreal) := (fun y0 : hreal => forall y1 : hreal, (hreal_add x0 (hreal_add y0 y1)) = (hreal_add (hreal_add x0 y0) y1)) x1.
Definition term5 (x0 : hreal) (x1 : hreal) := (fun y0 : hreal => forall y1 : hreal, ((hreal_add x0 y1) = (hreal_add y0 y1)) = (x0 = y0)) x1.
Definition term86 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := fun y0 : prod hreal hreal => (fun y1 : prod hreal hreal => ((treal_eq (@pair hreal hreal x2 x3) (@pair hreal hreal x0 x1)) /\ (treal_eq (@pair hreal hreal x0 x1) y1)) -> treal_eq (@pair hreal hreal x2 x3) y1) y0.
Definition term55 (x0 : hreal) (x1 : hreal) := (fun y0 : prod hreal hreal => forall y1 : prod hreal hreal, forall y2 : prod hreal hreal, ((treal_eq y0 y1) /\ (treal_eq y1 y2)) -> treal_eq y0 y2) (@pair hreal hreal x0 x1).
Definition term73 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := forall y0 : prod hreal hreal, ((treal_eq (@pair hreal hreal x2 x3) (@pair hreal hreal x0 x1)) /\ (treal_eq (@pair hreal hreal x0 x1) y0)) -> treal_eq (@pair hreal hreal x2 x3) y0.
Definition term68 (x0 : prod hreal hreal) (x1 : hreal) (x2 : hreal) := forall y0 : prod hreal hreal, ((treal_eq (@pair hreal hreal x1 x2) x0) /\ (treal_eq x0 y0)) -> treal_eq (@pair hreal hreal x1 x2) y0.
Definition term132 (x0 : hreal) (x1 : hreal) := @eq hreal (hreal_add x0 x1).
Definition term104 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) (x4 : hreal) (x5 : hreal) := (((hreal_add x2 x1) = (hreal_add x0 x5)) /\ ((hreal_add x0 x3) = (hreal_add x4 x1))) -> (hreal_add x2 x3) = (hreal_add x4 x5).
Definition term17 (x0 : hreal) (x1 : hreal) := forall y0 : hreal, (hreal_add (hreal_add x0 x1) y0) = (hreal_add x0 (hreal_add x1 y0)).
Definition term105 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) (x4 : hreal) := fun y0 : hreal => (((hreal_add x2 x1) = (hreal_add x0 x4)) /\ ((hreal_add x0 y0) = (hreal_add x3 x1))) -> (hreal_add x2 y0) = (hreal_add x3 x4).
Definition term64 (x0 : hreal) (x1 : hreal) := forall y0 : prod hreal hreal, (fun y1 : prod hreal hreal => forall y2 : prod hreal hreal, ((treal_eq (@pair hreal hreal x0 x1) y1) /\ (treal_eq y1 y2)) -> treal_eq (@pair hreal hreal x0 x1) y2) y0.
Definition term46 := forall y0 : prod hreal hreal, (fun y1 : prod hreal hreal => forall y2 : prod hreal hreal, forall y3 : prod hreal hreal, ((treal_eq y1 y2) /\ (treal_eq y2 y3)) -> treal_eq y1 y3) y0.
Definition term38 (x0 : hreal) (x1 : hreal) (x2 : hreal) := forall y0 : hreal, (treal_eq (@pair hreal hreal x0 y0) (@pair hreal hreal x2 x1)) = ((hreal_add x0 x1) = (hreal_add x2 y0)).
Definition term123 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) (x4 : hreal) (x5 : hreal) := ((hreal_add (hreal_add x0 x3) (hreal_add x2 x1)) = (hreal_add (hreal_add x0 x5) (hreal_add x4 x1))) -> (hreal_add x2 x3) = (hreal_add x4 x5).
Definition term122 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) (x4 : hreal) (x5 : hreal) := ((hreal_add (hreal_add x2 x1) (hreal_add x0 x3)) = (hreal_add (hreal_add x0 x5) (hreal_add x4 x1))) -> (hreal_add x2 x3) = (hreal_add x4 x5).
Definition term6 (x0 : hreal) (x1 : hreal) := forall y0 : hreal, ((hreal_add x0 y0) = (hreal_add x1 y0)) = (x0 = x1).
Definition term72 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := (fun y0 : prod hreal hreal => forall y1 : prod hreal hreal, ((treal_eq (@pair hreal hreal x0 x1) y0) /\ (treal_eq y0 y1)) -> treal_eq (@pair hreal hreal x0 x1) y1) (@pair hreal hreal x2 x3).
Definition term1 (x0 : hreal) := forall y0 : hreal, (hreal_add x0 y0) = (hreal_add y0 x0).
Definition term13 (x0 : hreal) (x1 : hreal) (x2 : hreal) := hreal_add x0 (hreal_add x1 x2).
Definition term58 (x0 : hreal) := fun y0 : hreal => forall y1 : prod hreal hreal, forall y2 : prod hreal hreal, ((treal_eq (@pair hreal hreal x0 y0) y1) /\ (treal_eq y1 y2)) -> treal_eq (@pair hreal hreal x0 y0) y2.
Definition term121 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) (x4 : hreal) (x5 : hreal) := imp ((hreal_add (hreal_add x2 x0) (hreal_add x1 x5)) = (hreal_add (hreal_add x2 x3) (hreal_add x4 x5))).
Definition term120 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) (x4 : hreal) (x5 : hreal) := imp ((hreal_add (hreal_add x0 x5) (hreal_add x2 x1)) = (hreal_add (hreal_add x2 x3) (hreal_add x4 x5))).
Definition term40 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := treal_eq (@pair hreal hreal x0 x1) (@pair hreal hreal x2 x3).
Definition term41 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := (fun y0 : type1223 a0 a1 => (forall y1 : prod a1 a0, y0 y1) = (forall y1 : a1, forall y2 : a0, y0 (@pair a1 a0 y1 y2))) x0.
Definition term49 (x0 : prod hreal hreal) := (fun y0 : prod hreal hreal => forall y1 : prod hreal hreal, forall y2 : prod hreal hreal, ((treal_eq y0 y1) /\ (treal_eq y1 y2)) -> treal_eq y0 y2) x0.
Definition term33 (x0 : hreal) := (fun y0 : hreal => forall y1 : hreal, forall y2 : hreal, forall y3 : hreal, (treal_eq (@pair hreal hreal y0 y3) (@pair hreal hreal y2 y1)) = ((hreal_add y0 y1) = (hreal_add y2 y3))) x0.
Definition term30 (x0 : hreal) := (fun y0 : hreal => forall y1 : hreal, forall y2 : hreal, (hreal_add (hreal_add y0 y1) y2) = (hreal_add y0 (hreal_add y1 y2))) x0.
Definition term25 (x0 : hreal) := (fun y0 : hreal => forall y1 : hreal, forall y2 : hreal, ((hreal_add y0 y1) = (hreal_add y0 y2)) = (y1 = y2)) x0.
Definition term8 (x0 : hreal) := (fun y0 : hreal => forall y1 : hreal, forall y2 : hreal, (hreal_add y0 (hreal_add y1 y2)) = (hreal_add (hreal_add y0 y1) y2)) x0.
Definition term3 (x0 : hreal) := (fun y0 : hreal => forall y1 : hreal, forall y2 : hreal, ((hreal_add y0 y2) = (hreal_add y1 y2)) = (y0 = y1)) x0.
Definition term91 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) (x4 : hreal) := fun y0 : hreal => (fun y1 : prod hreal hreal => ((treal_eq (@pair hreal hreal x2 x3) (@pair hreal hreal x0 x1)) /\ (treal_eq (@pair hreal hreal x0 x1) y1)) -> treal_eq (@pair hreal hreal x2 x3) y1) (@pair hreal hreal x4 y0).
Definition term101 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) (x4 : hreal) (x5 : hreal) := ((hreal_add x0 x5) = (hreal_add x2 x1)) /\ ((hreal_add x2 x3) = (hreal_add x4 x5)).
Definition term88 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := @eq Prop (forall y0 : prod hreal hreal, ((treal_eq (@pair hreal hreal x2 x3) (@pair hreal hreal x0 x1)) /\ (treal_eq (@pair hreal hreal x0 x1) y0)) -> treal_eq (@pair hreal hreal x2 x3) y0).
