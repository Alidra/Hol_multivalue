Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term60 (x0 : nat -> Prop) := fun y0 : nat => (fun y1 : nat => (x0 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (x0 y2))) y0.
Definition term107 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := ~ ((Peano.lt x2 x0) -> ~ (x1 x2)).
Definition term23 (x0 : nat -> Prop) := fun y0 : nat => x0 y0.
Definition term108 (x0 : nat -> Prop) := ~ (all x0).
Definition term53 := (~ False) -> False.
Definition term36 (x0 : nat -> Prop) (x1 : nat) := ~ (x0 x1).
Definition term175 (x0 : nat -> Prop) (x1 : nat -> nat) (x2 : nat) := @eq Prop ((~ (x0 x2)) \/ (Peano.lt (x1 x2) x2)).
Definition term171 (x0 : nat -> Prop) (x1 : nat -> nat) (x2 : nat) := (fun y0 : nat => ((~ (x0 y0)) \/ (Peano.lt (x1 y0) y0)) /\ ((~ (x0 y0)) \/ (x0 (x1 y0)))) x2.
Definition term93 (x0 : nat -> Prop) := (forall y0 : nat, ~ ((x0 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1)))) -> (~ (forall y0 : nat, (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1)) -> ~ (x0 y0))) -> False.
Definition term89 (x0 : nat -> Prop) := forall y0 : nat, (fun y1 : nat => ~ (x0 y1)) y0.
Definition term165 (x0 : nat -> Prop) (x1 : nat -> nat) (x2 : nat) := ((~ (x0 x2)) \/ (Peano.lt (x1 x2) x2)) /\ ((~ (x0 x2)) \/ (x0 (x1 x2))).
Definition term95 (x0 : nat -> Prop) := (((forall y0 : nat, ~ ((x0 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1)))) -> (~ (forall y0 : nat, (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1)) -> ~ (x0 y0))) -> False) -> (forall y0 : nat, ~ ((x0 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1)))) -> (~ (forall y0 : nat, (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1)) -> ~ (x0 y0))) -> False) -> (forall y0 : nat, ~ ((x0 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1)))) -> (~ (forall y0 : nat, (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1)) -> ~ (x0 y0))) -> False.
Definition term18 (x0 : Prop) := ~ (~ x0).
Definition term73 (x0 : nat -> Prop) := (forall y0 : nat, (forall y1 : nat, (Peano.lt y1 y0) -> (fun y2 : nat => ~ (x0 y2)) y1) -> (fun y1 : nat => ~ (x0 y1)) y0) -> forall y0 : nat, (fun y1 : nat => ~ (x0 y1)) y0.
Definition term7 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (~ (exists y1 : a0, y0 y1)) = (forall y1 : a0, ~ (y0 y1))) x0.
Definition term155 (x0 : nat -> Prop) (x1 : nat -> nat) (x2 : nat) := (fun y0 : nat => fun y1 : nat => (~ (x0 y0)) \/ ((Peano.lt y1 y0) /\ (x0 y1))) x2 (x1 x2).
Definition term144 (x0 : nat -> Prop) := forall y0 : nat, exists y1 : nat, (fun y2 : nat => fun y3 : nat => (~ (x0 y2)) \/ ((Peano.lt y3 y2) /\ (x0 y3))) y0 y1.
Definition term142 (x0 : type1605) := forall y0 : nat, exists y1 : nat, x0 y0 y1.
Definition term139 (x0 : nat -> Prop) := forall y0 : nat, exists y1 : nat, (~ (x0 y0)) \/ ((Peano.lt y1 y0) /\ (x0 y1)).
Definition term146 (x0 : nat -> Prop) := fun y0 : nat => fun y1 : nat => (~ (x0 y0)) \/ ((Peano.lt y1 y0) /\ (x0 y1)).
Definition term181 (x0 : nat -> Prop) (x1 : nat -> nat) (x2 : nat) := (x0 x2) -> Peano.lt (x1 x2) x2.
Definition term170 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (fun y0 : nat => (~ (Peano.lt y0 x0)) \/ (~ (x1 y0))) x2.
Definition term138 (x0 : nat -> Prop) := fun y0 : nat => exists y1 : nat, (~ (x0 y0)) \/ ((Peano.lt y1 y0) /\ (x0 y1)).
Definition term156 (x0 : nat -> Prop) (x1 : nat -> nat) (x2 : nat) := (fun y0 : nat => (~ (x0 x2)) \/ ((Peano.lt y0 x2) /\ (x0 y0))) (x1 x2).
Definition term64 (x0 : nat -> Prop) := @eq Prop (~ (exists y0 : nat, (x0 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1)))).
Definition term63 (x0 : nat -> Prop) := @eq Prop (~ (exists y0 : nat, (fun y1 : nat => (x0 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (x0 y2))) y0)).
Definition term49 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => ~ (x0 y0)) x1.
Definition term77 (x0 : nat) (x1 : nat -> Prop) := forall y0 : nat, (Peano.lt y0 x0) -> (fun y1 : nat => ~ (x1 y1)) y0.
Definition term10 (x0 : Prop) := (~ x0) -> False.
Definition term82 (x0 : nat -> Prop) := fun y0 : nat => (forall y1 : nat, (Peano.lt y1 y0) -> (fun y2 : nat => ~ (x0 y2)) y1) -> (fun y1 : nat => ~ (x0 y1)) y0.
Definition term185 (x0 : nat -> Prop) (x1 : nat -> nat) (x2 : nat) := @eq Prop ((~ (x0 x2)) \/ (x0 (x1 x2))).
Definition term180 (x0 : nat -> Prop) (x1 : nat) := imp (x0 x1).
Definition term128 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (fun y0 : nat => (Peano.lt y0 x0) /\ (x1 y0)) x2.
Definition term125 (x0 : Prop) (x1 : nat -> Prop) := exists y0 : nat, x0 \/ (x1 y0).
Definition term148 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (fun y0 : nat => fun y1 : nat => (~ (x0 y0)) \/ ((Peano.lt y1 y0) /\ (x0 y1))) x1 x2.
Definition term19 := fun y0 : nat -> Prop => (~ ((exists y1 : nat, (y0 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (y0 y2))) -> exists y1 : nat, y0 y1)) -> False.
Definition term177 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term149 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (fun y0 : nat => (~ (x1 x0)) \/ ((Peano.lt y0 x0) /\ (x1 y0))) x2.
Definition term110 (x0 : nat) (x1 : nat -> Prop) := ~ (forall y0 : nat, (Peano.lt y0 x0) -> ~ (x1 y0)).
Definition term92 (x0 : nat -> Prop) := ~ (forall y0 : nat, (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1)) -> ~ (x0 y0)).
Definition term183 (x0 : nat -> nat) (x1 : nat) := ~ (Peano.lt (x0 x1) x1).
Definition term191 (x0 : Prop) (x1 : Prop) := (~ x0) \/ (~ x1).
Definition term51 (x0 : Prop) := (~ x0) -> x0.
Definition term59 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => (x0 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1))) x1.
Definition term168 (x0 : nat -> Prop) (x1 : nat -> nat) := fun y0 : nat => ((~ (x0 y0)) \/ (Peano.lt (x1 y0) y0)) /\ ((~ (x0 y0)) \/ (x0 (x1 y0))).
Definition term134 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (~ (x1 x0)) \/ ((Peano.lt x2 x0) /\ (x1 x2)).
Definition term135 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => (~ (x1 x0)) \/ ((fun y1 : nat => (Peano.lt y1 x0) /\ (x1 y1)) y0).
Definition term46 (x0 : nat -> Prop) (x1 : nat) := ~ ((fun y0 : nat => x0 y0) x1).
Definition term140 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := forall y0 : a0, exists y1 : a1, x0 y0 y1.
Definition term13 (x0 : nat -> Prop) := ~ ((exists y0 : nat, (x0 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1))) -> exists y0 : nat, x0 y0).
Definition term33 (x0 : nat -> Prop) := (~ (exists y0 : nat, x0 y0)) -> False.
Definition term158 (x0 : nat -> Prop) (x1 : nat -> nat) := fun y0 : nat => (fun y1 : nat => fun y2 : nat => (~ (x0 y1)) \/ ((Peano.lt y2 y1) /\ (x0 y2))) y0 (x1 y0).
Definition term192 (x0 : Prop) (x1 : Prop) := ~ (x0 /\ x1).
Definition term32 (x0 : nat -> Prop) := imp (exists y0 : nat, (x0 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1))).
Definition term81 (x0 : nat -> Prop) (x1 : nat) := (forall y0 : nat, (Peano.lt y0 x1) -> ~ (x0 y0)) -> ~ (x0 x1).
Definition term80 (x0 : nat -> Prop) (x1 : nat) := (forall y0 : nat, (Peano.lt y0 x1) -> (fun y1 : nat => ~ (x0 y1)) y0) -> (fun y0 : nat => ~ (x0 y0)) x1.
Definition term164 (x0 : nat -> Prop) := exists y0 : nat -> nat, forall y1 : nat, (~ (x0 y1)) \/ ((Peano.lt (y0 y1) y1) /\ (x0 (y0 y1))).
Definition term145 (x0 : nat -> Prop) := exists y0 : nat -> nat, forall y1 : nat, (fun y2 : nat => fun y3 : nat => (~ (x0 y2)) \/ ((Peano.lt y3 y2) /\ (x0 y3))) y1 (y0 y1).
Definition term143 (x0 : type1605) := exists y0 : nat -> nat, forall y1 : nat, x0 y1 (y0 y1).
Definition term17 (x0 : nat -> Prop) := ~ (~ ((exists y0 : nat, (x0 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1))) -> exists y0 : nat, x0 y0)).
Definition term186 (x0 : nat -> nat) (x1 : nat -> Prop) (x2 : nat) := @eq Prop ((x1 (x0 x2)) \/ (~ (x1 x2))).
Definition term52 (x0 : nat -> Prop) (x1 : nat) := (x0 x1) -> False.
Definition term166 (x0 : nat -> nat) (x1 : nat) := Peano.lt (x0 x1) x1.
Definition term105 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (Peano.lt x2 x0) /\ (~ (~ (x1 x2))).
Definition term70 (x0 : nat -> Prop) := imp (~ (exists y0 : nat, (x0 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1)))).
Definition term99 := fun y0 : nat -> Prop => (forall y1 : nat, ~ ((y0 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (y0 y2)))) -> (~ (forall y1 : nat, (forall y2 : nat, (Peano.lt y2 y1) -> ~ (y0 y2)) -> ~ (y0 y1))) -> False.
Definition term121 (x0 : nat -> Prop) := forall y0 : nat, (~ (x0 y0)) \/ (exists y1 : nat, (Peano.lt y1 y0) /\ (x0 y1)).
Definition term174 (x0 : nat -> nat) (x1 : nat -> Prop) (x2 : nat) := (Peano.lt (x0 x2) x2) \/ (~ (x1 x2)).
Definition term68 (x0 : nat -> Prop) := fun y0 : nat => ~ ((x0 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1))).
Definition term157 (x0 : nat -> Prop) (x1 : nat -> nat) (x2 : nat) := (~ (x0 x2)) \/ ((Peano.lt (x1 x2) x2) /\ (x0 (x1 x2))).
Definition term193 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := ~ ((Peano.lt x2 x0) /\ (x1 x2)).
Definition term22 := forall y0 : nat -> Prop, (exists y1 : nat, (y0 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (y0 y2))) -> exists y1 : nat, y0 y1.
Definition term11 (x0 : nat -> Prop) := (exists y0 : nat, (x0 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1))) -> exists y0 : nat, x0 y0.
Definition term101 := forall y0 : nat -> Prop, (forall y1 : nat, ~ ((y0 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (y0 y2)))) -> (~ (forall y1 : nat, (forall y2 : nat, (Peano.lt y2 y1) -> ~ (y0 y2)) -> ~ (y0 y1))) -> False.
Definition term24 (x0 : nat -> Prop) := exists y0 : nat, x0 y0.
Definition term190 (x0 : nat -> Prop) (x1 : nat -> nat) (x2 : nat) := ~ (x0 (x1 x2)).
Definition term50 (x0 : nat -> Prop) (x1 : nat) := (~ (x0 x1)) -> x0 x1.
Definition term150 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => (fun y1 : nat => fun y2 : nat => (~ (x0 y1)) \/ ((Peano.lt y2 y1) /\ (x0 y2))) x1 y0.
Definition term83 (x0 : nat -> Prop) := fun y0 : nat => (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1)) -> ~ (x0 y0).
Definition term182 (x0 : nat -> nat) (x1 : nat) := (~ (Peano.lt (x0 x1) x1)) -> Peano.lt (x0 x1) x1.
Definition term198 (x0 : nat -> Prop) := ((exists y0 : nat, x0 y0) -> exists y0 : nat, (x0 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1))) /\ ((exists y0 : nat, (x0 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1))) -> exists y0 : nat, x0 y0).
Definition term37 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => (~ (Peano.lt y0 x0)) \/ (~ (x1 y0)).
Definition term188 (x0 : nat -> Prop) (x1 : nat -> nat) (x2 : nat) := (x0 x2) -> x0 (x1 x2).
Definition term26 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => (Peano.lt y0 x0) -> ~ (x1 y0).
Definition term137 (x0 : nat) (x1 : nat -> Prop) := exists y0 : nat, (~ (x1 x0)) \/ ((Peano.lt y0 x0) /\ (x1 y0)).
Definition term187 (x0 : nat -> Prop) (x1 : nat -> nat) (x2 : nat) := (~ (~ (x0 x2))) -> x0 (x1 x2).
Definition term163 (x0 : nat -> Prop) := fun y0 : nat -> nat => forall y1 : nat, (~ (x0 y1)) \/ ((Peano.lt (y0 y1) y1) /\ (x0 (y0 y1))).
Definition term162 (x0 : nat -> Prop) := fun y0 : nat -> nat => forall y1 : nat, (fun y2 : nat => fun y3 : nat => (~ (x0 y2)) \/ ((Peano.lt y3 y2) /\ (x0 y3))) y1 (y0 y1).
Definition term167 (x0 : nat -> Prop) (x1 : nat -> nat) (x2 : nat) := x0 (x1 x2).
Definition term154 (x0 : nat -> Prop) := @eq Prop (forall y0 : nat, exists y1 : nat, (~ (x0 y0)) \/ ((Peano.lt y1 y0) /\ (x0 y1))).
Definition term153 (x0 : nat -> Prop) := @eq Prop (forall y0 : nat, exists y1 : nat, (fun y2 : nat => fun y3 : nat => (~ (x0 y2)) \/ ((Peano.lt y3 y2) /\ (x0 y3))) y0 y1).
Definition term87 (x0 : nat -> Prop) := imp (forall y0 : nat, (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1)) -> ~ (x0 y0)).
Definition term86 (x0 : nat -> Prop) := imp (forall y0 : nat, (forall y1 : nat, (Peano.lt y1 y0) -> (fun y2 : nat => ~ (x0 y2)) y1) -> (fun y1 : nat => ~ (x0 y1)) y0).
Definition term79 (x0 : nat) (x1 : nat -> Prop) := imp (forall y0 : nat, (Peano.lt y0 x0) -> ~ (x1 y0)).
Definition term78 (x0 : nat) (x1 : nat -> Prop) := imp (forall y0 : nat, (Peano.lt y0 x0) -> (fun y1 : nat => ~ (x1 y1)) y0).
Definition term71 (x0 : nat -> Prop) := imp (forall y0 : nat, ~ ((x0 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1)))).
Definition term133 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (~ (x1 x0)) \/ ((fun y0 : nat => (Peano.lt y0 x0) /\ (x1 y0)) x2).
Definition term90 (x0 : nat -> Prop) := (forall y0 : nat, (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1)) -> ~ (x0 y0)) -> forall y0 : nat, ~ (x0 y0).
Definition term9 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, ~ (x0 y0).
Definition term14 (x0 : nat -> Prop) := ((~ ((exists y0 : nat, (x0 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1))) -> exists y0 : nat, x0 y0)) -> False) -> (~ ((exists y0 : nat, (x0 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1))) -> exists y0 : nat, x0 y0)) -> False.
Definition term117 (x0 : nat -> Prop) (x1 : nat) := or (~ (x0 x1)).
Definition term179 (x0 : nat -> Prop) (x1 : nat) := imp (~ (~ (x0 x1))).
Definition term112 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (fun y0 : nat => (Peano.lt y0 x0) -> ~ (x1 y0)) x2.
Definition term94 (x0 : nat -> Prop) := ((forall y0 : nat, ~ ((x0 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1)))) -> (~ (forall y0 : nat, (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1)) -> ~ (x0 y0))) -> False) -> (forall y0 : nat, ~ ((x0 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1)))) -> (~ (forall y0 : nat, (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1)) -> ~ (x0 y0))) -> False.
Definition term25 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (Peano.lt x2 x0) -> ~ (x1 x2).
Definition term123 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 \/ (x1 y0).
Definition term3 (x0 : nat -> Prop) := forall y0 : nat, (forall y1 : nat, (Peano.lt y1 y0) -> x0 y1) -> x0 y0.
Definition term129 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => (fun y1 : nat => (Peano.lt y1 x0) /\ (x1 y1)) y0.
Definition term40 (x0 : nat -> Prop) := fun y0 : nat => (x0 y0) /\ (forall y1 : nat, (~ (Peano.lt y1 y0)) \/ (~ (x0 y1))).
Definition term30 (x0 : nat -> Prop) := fun y0 : nat => (x0 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1)).
Definition term161 (x0 : nat -> Prop) (x1 : nat -> nat) := forall y0 : nat, (~ (x0 y0)) \/ ((Peano.lt (x1 y0) y0) /\ (x0 (x1 y0))).
Definition term122 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 \/ (exists y0 : a0, x1 y0).
Definition term66 (x0 : nat) (x1 : nat -> Prop) := ~ ((x1 x0) /\ (forall y0 : nat, (Peano.lt y0 x0) -> ~ (x1 y0))).
Definition term113 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := ~ ((fun y0 : nat => (Peano.lt y0 x0) -> ~ (x1 y0)) x2).
Definition term42 (x0 : nat -> Prop) := ~ (ex x0).
Definition term127 (x0 : nat) (x1 : nat -> Prop) := exists y0 : nat, (~ (x1 x0)) \/ ((fun y1 : nat => (Peano.lt y1 x0) /\ (x1 y1)) y0).
Definition term45 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => x0 y0) x1.
Definition term21 := forall y0 : nat -> Prop, (~ ((exists y1 : nat, (y0 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (y0 y2))) -> exists y1 : nat, y0 y1)) -> False.
Definition term194 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := ((Peano.lt x2 x0) /\ (x1 x2)) -> False.
Definition term43 (x0 : nat -> Prop) := forall y0 : nat, ~ (x0 y0).
Definition term100 := fun y0 : nat -> Prop => (forall y1 : nat, ~ ((y0 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (y0 y2)))) -> forall y1 : nat, (forall y2 : nat, (Peano.lt y2 y1) -> ~ (y0 y2)) -> ~ (y0 y1).
Definition term8 (a0 : Type') (x0 : a0 -> Prop) := ~ (exists y0 : a0, x0 y0).
Definition term119 (x0 : nat) (x1 : nat -> Prop) := (~ (x1 x0)) \/ (exists y0 : nat, (Peano.lt y0 x0) /\ (x1 y0)).
Definition term57 (x0 : nat -> Prop) := ~ (exists y0 : nat, (fun y1 : nat => (x0 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (x0 y2))) y0).
Definition term97 (x0 : nat -> Prop) := ~ (~ (forall y0 : nat, (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1)) -> ~ (x0 y0))).
Definition term91 (x0 : nat -> Prop) := (~ (forall y0 : nat, (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1)) -> ~ (x0 y0))) -> False.
Definition term120 (x0 : nat -> Prop) := fun y0 : nat => (~ (x0 y0)) \/ (exists y1 : nat, (Peano.lt y1 y0) /\ (x0 y1)).
Definition term27 (x0 : nat) (x1 : nat -> Prop) := forall y0 : nat, (Peano.lt y0 x0) -> ~ (x1 y0).
Definition term169 (x0 : nat -> Prop) (x1 : nat -> nat) := forall y0 : nat, ((~ (x0 y0)) \/ (Peano.lt (x1 y0) y0)) /\ ((~ (x0 y0)) \/ (x0 (x1 y0))).
Definition term151 (x0 : nat -> Prop) (x1 : nat) := exists y0 : nat, (fun y1 : nat => fun y2 : nat => (~ (x0 y1)) \/ ((Peano.lt y2 y1) /\ (x0 y2))) x1 y0.
Definition term75 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (Peano.lt x2 x0) -> (fun y0 : nat => ~ (x1 y0)) x2.
Definition term103 (x0 : nat -> Prop) (x1 : nat) := ~ (~ (x0 x1)).
Definition term98 (x0 : nat -> Prop) := (forall y0 : nat, ~ ((x0 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1)))) -> forall y0 : nat, (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1)) -> ~ (x0 y0).
Definition term159 (x0 : nat -> Prop) (x1 : nat -> nat) := fun y0 : nat => (~ (x0 y0)) \/ ((Peano.lt (x1 y0) y0) /\ (x0 (x1 y0))).
Definition term130 (x0 : nat) (x1 : nat -> Prop) := exists y0 : nat, (fun y1 : nat => (Peano.lt y1 x0) /\ (x1 y1)) y0.
Definition term61 (x0 : nat -> Prop) := exists y0 : nat, (fun y1 : nat => (x0 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (x0 y2))) y0.
Definition term74 (x0 : nat) (x1 : nat) := imp (Peano.lt x0 x1).
Definition term15 (x0 : nat -> Prop) := (((~ ((exists y0 : nat, (x0 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1))) -> exists y0 : nat, x0 y0)) -> False) -> (~ ((exists y0 : nat, (x0 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1))) -> exists y0 : nat, x0 y0)) -> False) -> (~ ((exists y0 : nat, (x0 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1))) -> exists y0 : nat, x0 y0)) -> False.
Definition term55 (x0 : nat -> Prop) := (exists y0 : nat, x0 y0) -> exists y0 : nat, (x0 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1)).
Definition term104 (x0 : nat) (x1 : nat) := and (Peano.lt x0 x1).
Definition term47 (x0 : nat -> Prop) := fun y0 : nat => ~ ((fun y1 : nat => x0 y1) y0).
Definition term69 (x0 : nat -> Prop) := forall y0 : nat, ~ ((x0 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1))).
Definition term147 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => fun y1 : nat => (~ (x0 y0)) \/ ((Peano.lt y1 y0) /\ (x0 y1))) x1.
Definition term172 (x0 : nat -> Prop) (x1 : nat -> nat) (x2 : nat) := (~ (x0 x2)) \/ (Peano.lt (x1 x2) x2).
Definition term58 (x0 : nat -> Prop) := forall y0 : nat, ~ ((fun y1 : nat => (x0 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (x0 y2))) y0).
Definition term44 (x0 : nat -> Prop) := forall y0 : nat, ~ ((fun y1 : nat => x0 y1) y0).
Definition term85 (x0 : nat -> Prop) := forall y0 : nat, (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1)) -> ~ (x0 y0).
Definition term160 (x0 : nat -> Prop) (x1 : nat -> nat) := forall y0 : nat, (fun y1 : nat => fun y2 : nat => (~ (x0 y1)) \/ ((Peano.lt y2 y1) /\ (x0 y2))) y0 (x1 y0).
Definition term118 (x0 : nat) (x1 : nat -> Prop) := (~ (x1 x0)) \/ (~ (forall y0 : nat, (Peano.lt y0 x0) -> ~ (x1 y0))).
Definition term184 (x0 : nat -> nat) (x1 : nat -> Prop) (x2 : nat) := (x1 (x0 x2)) \/ (~ (x1 x2)).
Definition term54 (x0 : nat -> Prop) := (fun y0 : nat -> Prop => (~ ((exists y1 : nat, (y0 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (y0 y2))) -> exists y1 : nat, y0 y1)) -> False) x0.
Definition term76 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => (Peano.lt y0 x0) -> (fun y1 : nat => ~ (x1 y1)) y0.
Definition term115 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => (Peano.lt y0 x0) /\ (x1 y0).
Definition term199 := forall y0 : nat -> Prop, (exists y1 : nat, y0 y1) = (exists y1 : nat, (y0 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (y0 y2))).
Definition term96 (x0 : nat -> Prop) := (((forall y0 : nat, ~ ((x0 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1)))) -> (~ (forall y0 : nat, (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1)) -> ~ (x0 y0))) -> False) -> (forall y0 : nat, ~ ((x0 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1)))) -> (~ (forall y0 : nat, (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1)) -> ~ (x0 y0))) -> False) -> ((forall y0 : nat, ~ ((x0 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1)))) -> (~ (forall y0 : nat, (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1)) -> ~ (x0 y0))) -> False) -> (forall y0 : nat, ~ ((x0 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1)))) -> (~ (forall y0 : nat, (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1)) -> ~ (x0 y0))) -> False.
Definition term196 (x0 : nat -> Prop) (x1 : nat -> nat) (x2 : nat) := ((Peano.lt (x1 x2) x2) /\ (x0 (x1 x2))) -> False.
Definition term84 (x0 : nat -> Prop) := forall y0 : nat, (forall y1 : nat, (Peano.lt y1 y0) -> (fun y2 : nat => ~ (x0 y2)) y1) -> (fun y1 : nat => ~ (x0 y1)) y0.
Definition term111 (x0 : nat) (x1 : nat -> Prop) := exists y0 : nat, ~ ((fun y1 : nat => (Peano.lt y1 x0) -> ~ (x1 y1)) y0).
Definition term126 (x0 : nat) (x1 : nat -> Prop) := (~ (x1 x0)) \/ (exists y0 : nat, (fun y1 : nat => (Peano.lt y1 x0) /\ (x1 y1)) y0).
Definition term152 (x0 : nat -> Prop) := fun y0 : nat => exists y1 : nat, (fun y2 : nat => fun y3 : nat => (~ (x0 y2)) \/ ((Peano.lt y3 y2) /\ (x0 y3))) y0 y1.
Definition term178 (x0 : nat -> Prop) (x1 : nat -> nat) (x2 : nat) := (~ (~ (x0 x2))) -> Peano.lt (x1 x2) x2.
Definition term116 (x0 : nat) (x1 : nat -> Prop) := exists y0 : nat, (Peano.lt y0 x0) /\ (x1 y0).
Definition term1 (x0 : nat -> Prop) := (fun y0 : nat -> Prop => (forall y1 : nat, (forall y2 : nat, (Peano.lt y2 y1) -> y0 y2) -> y0 y1) -> forall y1 : nat, y0 y1) x0.
Definition term88 (x0 : nat -> Prop) := fun y0 : nat => (fun y1 : nat => ~ (x0 y1)) y0.
Definition term176 (x0 : nat -> nat) (x1 : nat -> Prop) (x2 : nat) := @eq Prop ((Peano.lt (x0 x2) x2) \/ (~ (x1 x2))).
Definition term72 (x0 : nat -> Prop) := (forall y0 : nat, ~ ((x0 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1)))) -> forall y0 : nat, ~ (x0 y0).
Definition term5 (x0 : nat -> Prop) := (forall y0 : nat -> Prop, (forall y1 : nat, (forall y2 : nat, (Peano.lt y2 y1) -> y0 y2) -> y0 y1) -> forall y1 : nat, y0 y1) -> forall y0 : nat, x0 y0.
Definition term2 (x0 : nat -> Prop) := (forall y0 : nat, (forall y1 : nat, (Peano.lt y1 y0) -> x0 y1) -> x0 y0) -> forall y0 : nat, x0 y0.
Definition term41 (x0 : nat -> Prop) := exists y0 : nat, (x0 y0) /\ (forall y1 : nat, (~ (Peano.lt y1 y0)) \/ (~ (x0 y1))).
Definition term31 (x0 : nat -> Prop) := exists y0 : nat, (x0 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1)).
Definition term102 := forall y0 : nat -> Prop, (forall y1 : nat, ~ ((y0 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (y0 y2)))) -> forall y1 : nat, (forall y2 : nat, (Peano.lt y2 y1) -> ~ (y0 y2)) -> ~ (y0 y1).
Definition term0 := forall y0 : nat -> Prop, (forall y1 : nat, (forall y2 : nat, (Peano.lt y2 y1) -> y0 y2) -> y0 y1) -> forall y1 : nat, y0 y1.
Definition term195 (x0 : nat -> Prop) (x1 : nat -> nat) (x2 : nat) := (Peano.lt (x1 x2) x2) /\ (x0 (x1 x2)).
Definition term34 (x0 : nat -> Prop) := ~ (exists y0 : nat, x0 y0).
Definition term28 (x0 : nat -> Prop) (x1 : nat) := and (x0 x1).
Definition term114 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => ~ ((fun y1 : nat => (Peano.lt y1 x0) -> ~ (x1 y1)) y0).
Definition term67 (x0 : nat -> Prop) := fun y0 : nat => ~ ((fun y1 : nat => (x0 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (x0 y2))) y0).
Definition term65 (x0 : nat -> Prop) (x1 : nat) := ~ ((fun y0 : nat => (x0 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1))) x1).
Definition term16 (x0 : nat -> Prop) := (((~ ((exists y0 : nat, (x0 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1))) -> exists y0 : nat, x0 y0)) -> False) -> (~ ((exists y0 : nat, (x0 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1))) -> exists y0 : nat, x0 y0)) -> False) -> ((~ ((exists y0 : nat, (x0 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1))) -> exists y0 : nat, x0 y0)) -> False) -> (~ ((exists y0 : nat, (x0 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1))) -> exists y0 : nat, x0 y0)) -> False.
Definition term6 := (forall y0 : nat -> Prop, (forall y1 : nat, (forall y2 : nat, (Peano.lt y2 y1) -> y0 y2) -> y0 y1) -> forall y1 : nat, y0 y1) -> forall y0 : nat -> Prop, (forall y1 : nat, (forall y2 : nat, (Peano.lt y2 y1) -> y0 y2) -> y0 y1) -> forall y1 : nat, y0 y1.
Definition term12 (x0 : nat -> Prop) := (~ ((exists y0 : nat, (x0 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1))) -> exists y0 : nat, x0 y0)) -> False.
Definition term56 (x0 : nat -> Prop) := (~ (exists y0 : nat, (x0 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1)))) -> ~ (exists y0 : nat, x0 y0).
Definition term35 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (~ (Peano.lt x2 x0)) \/ (~ (x1 x2)).
Definition term39 (x0 : nat) (x1 : nat -> Prop) := (x1 x0) /\ (forall y0 : nat, (~ (Peano.lt y0 x0)) \/ (~ (x1 y0))).
Definition term29 (x0 : nat) (x1 : nat -> Prop) := (x1 x0) /\ (forall y0 : nat, (Peano.lt y0 x0) -> ~ (x1 y0)).
Definition term106 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (Peano.lt x2 x0) /\ (x1 x2).
Definition term132 (x0 : nat) (x1 : nat -> Prop) := @eq Prop ((~ (x1 x0)) \/ (exists y0 : nat, (Peano.lt y0 x0) /\ (x1 y0))).
Definition term131 (x0 : nat) (x1 : nat -> Prop) := @eq Prop ((~ (x1 x0)) \/ (exists y0 : nat, (fun y1 : nat => (Peano.lt y1 x0) /\ (x1 y1)) y0)).
Definition term141 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := exists y0 : a0 -> a1, forall y1 : a0, x0 y1 (y0 y1).
Definition term173 (x0 : nat -> Prop) (x1 : nat -> nat) (x2 : nat) := (~ (x0 x2)) \/ (x0 (x1 x2)).
Definition term197 (x0 : nat -> Prop) := (fun y0 : nat -> Prop => (forall y1 : nat, ~ ((y0 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (y0 y2)))) -> (~ (forall y1 : nat, (forall y2 : nat, (Peano.lt y2 y1) -> ~ (y0 y2)) -> ~ (y0 y1))) -> False) x0.
Definition term20 := fun y0 : nat -> Prop => (exists y1 : nat, (y0 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (y0 y2))) -> exists y1 : nat, y0 y1.
Definition term109 (x0 : nat -> Prop) := exists y0 : nat, ~ (x0 y0).
Definition term124 (x0 : Prop) (x1 : nat -> Prop) := x0 \/ (exists y0 : nat, x1 y0).
Definition term62 (x0 : nat -> Prop) := ~ (exists y0 : nat, (x0 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1))).
Definition term4 (x0 : nat -> Prop) := forall y0 : nat, x0 y0.
Definition term189 (x0 : nat -> Prop) (x1 : nat -> nat) (x2 : nat) := (~ (x0 (x1 x2))) -> x0 (x1 x2).
Definition term48 (x0 : nat -> Prop) := fun y0 : nat => ~ (x0 y0).
Definition term136 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => (~ (x1 x0)) \/ ((Peano.lt y0 x0) /\ (x1 y0)).
Definition term38 (x0 : nat) (x1 : nat -> Prop) := forall y0 : nat, (~ (Peano.lt y0 x0)) \/ (~ (x1 y0)).
