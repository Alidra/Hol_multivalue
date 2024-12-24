Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term89 (x0 : nat -> Prop) := fun y0 : nat => x0 y0.
Definition term115 (x0 : nat -> Prop) (x1 : nat -> Prop) := (fun y0 : nat -> Prop => (exists y1 : nat, y0 y1) -> (forall y1 : nat, (y0 y1) -> x0 y1) -> (~ (exists y1 : nat, x0 y1)) -> False) x1.
Definition term6 (x0 : nat) (x1 : nat) := (((~ ((forall y0 : nat, (Peano.le y0 x0) -> Peano.le y0 x1) -> Peano.le x0 x1)) -> (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> False) -> (~ ((forall y0 : nat, (Peano.le y0 x0) -> Peano.le y0 x1) -> Peano.le x0 x1)) -> (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> False) -> (~ ((forall y0 : nat, (Peano.le y0 x0) -> Peano.le y0 x1) -> Peano.le x0 x1)) -> (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> False.
Definition term90 (x0 : nat -> Prop) (x1 : nat -> Prop) (x2 : nat) := (x0 x2) -> x1 x2.
Definition term61 := (~ False) -> False.
Definition term100 (x0 : nat -> Prop) (x1 : nat) := ~ (x0 x1).
Definition term103 (x0 : nat -> Prop) (x1 : nat -> Prop) (x2 : nat) := (fun y0 : nat => (~ (x0 y0)) \/ (x1 y0)) x2.
Definition term71 (x0 : nat -> Prop) (x1 : nat -> Prop) := (exists y0 : nat, x0 y0) -> (forall y0 : nat, (x0 y0) -> x1 y0) -> (~ (exists y0 : nat, x1 y0)) -> False.
Definition term119 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => (exists y1 : nat, x0 y1) -> (Peano.le y0 (minimal x0)) = (forall y1 : nat, (x0 y1) -> Peano.le y0 y1)) x1.
Definition term160 (x0 : nat -> Prop) := forall y0 : nat -> Prop, ((exists y1 : nat, x0 y1) /\ (forall y1 : nat, (x0 y1) -> y0 y1)) -> Peano.le (minimal y0) (minimal x0).
Definition term116 (x0 : nat -> Prop) (x1 : nat -> Prop) := (forall y0 : nat, (Peano.le y0 (minimal x0)) -> Peano.le y0 (minimal x1)) -> Peano.le (minimal x0) (minimal x1).
Definition term33 (x0 : nat) (x1 : nat) := fun y0 : nat => (Peano.le y0 x0) -> Peano.le y0 x1.
Definition term54 (x0 : Prop) := ~ (~ x0).
Definition term64 (x0 : nat) (x1 : nat) := ((forall y0 : nat, (Peano.le y0 x0) -> Peano.le y0 x1) -> Peano.le x0 x1) -> Peano.le x0 x1.
Definition term94 (x0 : nat -> Prop) (x1 : nat -> Prop) := forall y0 : nat, (~ (x0 y0)) \/ (x1 y0).
Definition term158 (x0 : nat -> Prop) (x1 : nat -> Prop) := Peano.le (minimal x0) (minimal x1).
Definition term154 (x0 : nat -> Prop) (x1 : nat) (x2 : nat -> Prop) := (Peano.le x1 (minimal x0)) -> Peano.le x1 (minimal x2).
Definition term104 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => ~ (x0 y0)) x1.
Definition term150 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term80 (x0 : nat -> Prop) (x1 : nat -> Prop) := (exists y0 : nat, x0 y0) -> (forall y0 : nat, (x0 y0) -> x1 y0) -> exists y0 : nat, x1 y0.
Definition term49 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x1 x0) \/ (~ (Peano.le x1 x2)).
Definition term0 (x0 : Prop) := (~ x0) -> False.
Definition term30 := fun y0 : nat => Peano.le y0 y0.
Definition term66 (x0 : nat -> Prop) (x1 : nat -> Prop) := (exists y0 : nat, x0 y0) /\ (forall y0 : nat, (x0 y0) -> x1 y0).
Definition term135 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (x0 x2) -> Peano.le x1 x2.
Definition term112 (x0 : nat -> Prop) (x1 : nat) := imp (x0 x1).
Definition term65 (x0 : nat) (x1 : nat) := ((forall y0 : nat, (Peano.le y0 x0) -> Peano.le y0 x1) -> Peano.le x0 x1) -> (forall y0 : nat, (Peano.le y0 x0) -> Peano.le y0 x1) -> Peano.le x0 x1.
Definition term1 (x0 : nat) (x1 : nat) := (forall y0 : nat, (Peano.le y0 x0) -> Peano.le y0 x1) -> Peano.le x0 x1.
Definition term18 (x0 : nat) := forall y0 : nat, (~ ((forall y1 : nat, (Peano.le y1 y0) -> Peano.le y1 x0) -> Peano.le y0 x0)) -> (forall y1 : nat, Peano.le y1 y1) -> (forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y1 y2) /\ (Peano.le y2 y3)) -> Peano.le y1 y3) -> False.
Definition term52 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term109 (x0 : nat -> Prop) (x1 : nat -> Prop) (x2 : nat) := (~ (~ (x0 x2))) -> x1 x2.
Definition term11 := imp (forall y0 : nat, Peano.le y0 y0).
Definition term134 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (fun y0 : nat => (x0 y0) -> Peano.le x1 y0) x2.
Definition term156 (x0 : nat -> Prop) (x1 : nat -> Prop) := fun y0 : nat => (Peano.le y0 (minimal x0)) -> Peano.le y0 (minimal x1).
Definition term9 := ~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2).
Definition term141 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) (x3 : Prop) := ((x1 x2) = (x1 x2)) -> ((x1 x2) -> (Peano.le x0 x2) = x3) -> ((x1 x2) -> Peano.le x0 x2) = ((x1 x2) -> x3).
Definition term45 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (~ (Peano.le y0 x0)) \/ (Peano.le y0 x1)) x2.
Definition term57 (x0 : nat) (x1 : nat) := imp (Peano.le x0 x1).
Definition term48 (x0 : Prop) := (~ x0) -> x0.
Definition term78 (x0 : nat -> Prop) (x1 : nat -> Prop) := (forall y0 : nat, (x0 y0) -> x1 y0) -> exists y0 : nat, x1 y0.
Definition term47 (x0 : nat) := ~ (Peano.le x0 x0).
Definition term99 (x0 : nat -> Prop) (x1 : nat) := ~ ((fun y0 : nat => x0 y0) x1).
Definition term59 (x0 : nat) (x1 : nat) := (~ (Peano.le x0 x1)) -> Peano.le x0 x1.
Definition term69 (x0 : nat -> Prop) := (~ (exists y0 : nat, x0 y0)) -> False.
Definition term137 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) (x3 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((x0 x2) = y0) -> (y0 -> (Peano.le x1 x2) = y1) -> ((x0 x2) -> Peano.le x1 x2) = (y0 -> y1)) x3.
Definition term128 (x0 : nat -> Prop) (x1 : nat) (x2 : nat -> Prop) (x3 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((Peano.le x1 (minimal x0)) = y0) -> (y0 -> (Peano.le x1 (minimal x2)) = y1) -> ((Peano.le x1 (minimal x0)) -> Peano.le x1 (minimal x2)) = (y0 -> y1)) x3.
Definition term113 (x0 : nat -> Prop) (x1 : nat) := (x0 x1) -> False.
Definition term4 (x0 : nat) (x1 : nat) := (~ ((forall y0 : nat, (Peano.le y0 x0) -> Peano.le y0 x1) -> Peano.le x0 x1)) -> (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> False.
Definition term46 (x0 : nat) := (~ (Peano.le x0 x0)) -> Peano.le x0 x0.
Definition term27 (x0 : nat) := fun y0 : nat => forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 y1)) -> Peano.le x0 y1.
Definition term19 (x0 : nat) := forall y0 : nat, (~ ((forall y1 : nat, (Peano.le y1 y0) -> Peano.le y1 x0) -> Peano.le y0 x0)) -> (forall y1 : nat, Peano.le y1 y1) -> ~ (forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y1 y2) /\ (Peano.le y2 y3)) -> Peano.le y1 y3).
Definition term72 (x0 : nat -> Prop) (x1 : nat -> Prop) := ((exists y0 : nat, x0 y0) -> (forall y0 : nat, (x0 y0) -> x1 y0) -> (~ (exists y0 : nat, x1 y0)) -> False) -> (exists y0 : nat, x0 y0) -> (forall y0 : nat, (x0 y0) -> x1 y0) -> (~ (exists y0 : nat, x1 y0)) -> False.
Definition term68 (x0 : nat -> Prop) := exists y0 : nat, x0 y0.
Definition term124 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term106 (x0 : nat -> Prop) (x1 : nat -> Prop) (x2 : nat) := (x0 x2) \/ (~ (x1 x2)).
Definition term105 (x0 : nat -> Prop) (x1 : nat) := (~ (x0 x1)) -> x0 x1.
Definition term44 (x0 : nat) := (fun y0 : nat => Peano.le y0 y0) x0.
Definition term39 (x0 : nat) (x1 : nat) := ~ (Peano.le x0 x1).
Definition term8 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> False.
Definition term24 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.le x1 x0) /\ (Peano.le x0 x2)) -> Peano.le x1 x2.
Definition term83 (x0 : nat -> Prop) := forall y0 : nat -> Prop, (exists y1 : nat, y0 y1) -> (forall y1 : nat, (y0 y1) -> x0 y1) -> (~ (exists y1 : nat, x0 y1)) -> False.
Definition term38 (x0 : nat) (x1 : nat) := forall y0 : nat, (~ (Peano.le y0 x0)) \/ (Peano.le y0 x1).
Definition term107 (x0 : nat -> Prop) (x1 : nat -> Prop) (x2 : nat) := @eq Prop ((~ (x0 x2)) \/ (x1 x2)).
Definition term155 (x0 : nat -> Prop) (x1 : nat) := (forall y0 : nat, (x0 y0) -> Peano.le x1 y0) -> True.
Definition term76 (x0 : nat -> Prop) (x1 : nat -> Prop) := imp (forall y0 : nat, (x0 y0) -> x1 y0).
Definition term35 (x0 : nat) (x1 : nat) := imp (forall y0 : nat, (Peano.le y0 x0) -> Peano.le y0 x1).
Definition term79 (x0 : nat -> Prop) := imp (exists y0 : nat, x0 y0).
Definition term41 (x0 : nat) (x1 : nat) := and (forall y0 : nat, (~ (Peano.le y0 x0)) \/ (Peano.le y0 x1)).
Definition term40 (x0 : nat) (x1 : nat) := and (forall y0 : nat, (Peano.le y0 x0) -> Peano.le y0 x1).
Definition term140 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) (x3 : Prop) (x4 : Prop) := ((x0 x2) = x3) -> (x3 -> (Peano.le x1 x2) = x4) -> ((x0 x2) -> Peano.le x1 x2) = (x3 -> x4).
Definition term157 (x0 : nat -> Prop) (x1 : nat -> Prop) := forall y0 : nat, (Peano.le y0 (minimal x0)) -> Peano.le y0 (minimal x1).
Definition term111 (x0 : nat -> Prop) (x1 : nat) := imp (~ (~ (x0 x1))).
Definition term34 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le y0 x0) -> Peano.le y0 x1.
Definition term131 (x0 : nat -> Prop) (x1 : nat) (x2 : nat -> Prop) (x3 : Prop) (x4 : Prop) := ((Peano.le x1 (minimal x0)) = x3) -> (x3 -> (Peano.le x1 (minimal x2)) = x4) -> ((Peano.le x1 (minimal x0)) -> Peano.le x1 (minimal x2)) = (x3 -> x4).
Definition term73 (x0 : nat -> Prop) (x1 : nat -> Prop) := (((exists y0 : nat, x0 y0) -> (forall y0 : nat, (x0 y0) -> x1 y0) -> (~ (exists y0 : nat, x1 y0)) -> False) -> (exists y0 : nat, x0 y0) -> (forall y0 : nat, (x0 y0) -> x1 y0) -> (~ (exists y0 : nat, x1 y0)) -> False) -> (exists y0 : nat, x0 y0) -> (forall y0 : nat, (x0 y0) -> x1 y0) -> (~ (exists y0 : nat, x1 y0)) -> False.
Definition term92 (x0 : nat -> Prop) (x1 : nat -> Prop) (x2 : nat) := (~ (x0 x2)) \/ (x1 x2).
Definition term82 (x0 : nat -> Prop) := fun y0 : nat -> Prop => (exists y1 : nat, y0 y1) -> (forall y1 : nat, (y0 y1) -> x0 y1) -> exists y1 : nat, x0 y1.
Definition term28 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 y1)) -> Peano.le x0 y1.
Definition term23 := forall y0 : nat, forall y1 : nat, (~ ((forall y2 : nat, (Peano.le y2 y1) -> Peano.le y2 y0) -> Peano.le y1 y0)) -> (forall y2 : nat, Peano.le y2 y2) -> ~ (forall y2 : nat, forall y3 : nat, forall y4 : nat, ((Peano.le y2 y3) /\ (Peano.le y3 y4)) -> Peano.le y2 y4).
Definition term22 := forall y0 : nat, forall y1 : nat, (~ ((forall y2 : nat, (Peano.le y2 y1) -> Peano.le y2 y0) -> Peano.le y1 y0)) -> (forall y2 : nat, Peano.le y2 y2) -> (forall y2 : nat, forall y3 : nat, forall y4 : nat, ((Peano.le y2 y3) /\ (Peano.le y3 y4)) -> Peano.le y2 y4) -> False.
Definition term10 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2.
Definition term122 (x0 : nat -> Prop) (x1 : nat) := forall y0 : nat, (x0 y0) -> Peano.le x1 y0.
Definition term144 (x0 : nat -> Prop) (x1 : nat -> Prop) (x2 : nat) := (x0 x2) -> (x1 x2) = True.
Definition term95 (x0 : nat -> Prop) := ~ (ex x0).
Definition term5 (x0 : nat) (x1 : nat) := ((~ ((forall y0 : nat, (Peano.le y0 x0) -> Peano.le y0 x1) -> Peano.le x0 x1)) -> (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> False) -> (~ ((forall y0 : nat, (Peano.le y0 x0) -> Peano.le y0 x1) -> Peano.le x0 x1)) -> (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> False.
Definition term143 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (x0 x2) -> (Peano.le x1 x2) = True.
Definition term98 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => x0 y0) x1.
Definition term13 := (forall y0 : nat, Peano.le y0 y0) -> ~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2).
Definition term149 := forall y0 : nat, True.
Definition term86 := fun y0 : nat -> Prop => forall y1 : nat -> Prop, (exists y2 : nat, y1 y2) -> (forall y2 : nat, (y1 y2) -> y0 y2) -> exists y2 : nat, y0 y2.
Definition term85 := fun y0 : nat -> Prop => forall y1 : nat -> Prop, (exists y2 : nat, y1 y2) -> (forall y2 : nat, (y1 y2) -> y0 y2) -> (~ (exists y2 : nat, y0 y2)) -> False.
Definition term15 (x0 : nat) (x1 : nat) := (~ ((forall y0 : nat, (Peano.le y0 x0) -> Peano.le y0 x1) -> Peano.le x0 x1)) -> (forall y0 : nat, Peano.le y0 y0) -> ~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2).
Definition term96 (x0 : nat -> Prop) := forall y0 : nat, ~ (x0 y0).
Definition term12 := (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> False.
Definition term147 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => (x0 y0) -> Peano.le x1 y0.
Definition term77 (x0 : nat -> Prop) (x1 : nat -> Prop) := (forall y0 : nat, (x0 y0) -> x1 y0) -> (~ (exists y0 : nat, x1 y0)) -> False.
Definition term148 := fun y0 : nat => True.
Definition term138 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) (x3 : Prop) := forall y0 : Prop, ((x0 x2) = x3) -> (x3 -> (Peano.le x1 x2) = y0) -> ((x0 x2) -> Peano.le x1 x2) = (x3 -> y0).
Definition term129 (x0 : nat -> Prop) (x1 : nat) (x2 : nat -> Prop) (x3 : Prop) := forall y0 : Prop, ((Peano.le x1 (minimal x0)) = x3) -> (x3 -> (Peano.le x1 (minimal x2)) = y0) -> ((Peano.le x1 (minimal x0)) -> Peano.le x1 (minimal x2)) = (x3 -> y0).
Definition term125 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term110 (x0 : nat -> Prop) (x1 : nat) := ~ (~ (x0 x1)).
Definition term43 (x0 : nat) (x1 : nat) := (forall y0 : nat, (~ (Peano.le y0 x0)) \/ (Peano.le y0 x1)) /\ (~ (Peano.le x0 x1)).
Definition term42 (x0 : nat) (x1 : nat) := (forall y0 : nat, (Peano.le y0 x0) -> Peano.le y0 x1) /\ (~ (Peano.le x0 x1)).
Definition term67 (x0 : nat -> Prop) (x1 : nat -> Prop) := forall y0 : nat, (x0 y0) -> x1 y0.
Definition term7 (x0 : nat) (x1 : nat) := (((~ ((forall y0 : nat, (Peano.le y0 x0) -> Peano.le y0 x1) -> Peano.le x0 x1)) -> (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> False) -> (~ ((forall y0 : nat, (Peano.le y0 x0) -> Peano.le y0 x1) -> Peano.le x0 x1)) -> (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> False) -> ((~ ((forall y0 : nat, (Peano.le y0 x0) -> Peano.le y0 x1) -> Peano.le x0 x1)) -> (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> False) -> (~ ((forall y0 : nat, (Peano.le y0 x0) -> Peano.le y0 x1) -> Peano.le x0 x1)) -> (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> False.
Definition term136 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := forall y0 : Prop, forall y1 : Prop, ((x0 x2) = y0) -> (y0 -> (Peano.le x1 x2) = y1) -> ((x0 x2) -> Peano.le x1 x2) = (y0 -> y1).
Definition term127 (x0 : nat -> Prop) (x1 : nat) (x2 : nat -> Prop) := forall y0 : Prop, forall y1 : Prop, ((Peano.le x1 (minimal x0)) = y0) -> (y0 -> (Peano.le x1 (minimal x2)) = y1) -> ((Peano.le x1 (minimal x0)) -> Peano.le x1 (minimal x2)) = (y0 -> y1).
Definition term126 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term3 (x0 : nat) (x1 : nat) := ~ ((forall y0 : nat, (Peano.le y0 x0) -> Peano.le y0 x1) -> Peano.le x0 x1).
Definition term26 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Peano.le x1 x0) /\ (Peano.le x0 y0)) -> Peano.le x1 y0.
Definition term14 (x0 : nat) (x1 : nat) := imp (~ ((forall y0 : nat, (Peano.le y0 x0) -> Peano.le y0 x1) -> Peano.le x0 x1)).
Definition term84 (x0 : nat -> Prop) := forall y0 : nat -> Prop, (exists y1 : nat, y0 y1) -> (forall y1 : nat, (y0 y1) -> x0 y1) -> exists y1 : nat, x0 y1.
Definition term74 (x0 : nat -> Prop) (x1 : nat -> Prop) := (((exists y0 : nat, x0 y0) -> (forall y0 : nat, (x0 y0) -> x1 y0) -> (~ (exists y0 : nat, x1 y0)) -> False) -> (exists y0 : nat, x0 y0) -> (forall y0 : nat, (x0 y0) -> x1 y0) -> (~ (exists y0 : nat, x1 y0)) -> False) -> ((exists y0 : nat, x0 y0) -> (forall y0 : nat, (x0 y0) -> x1 y0) -> (~ (exists y0 : nat, x1 y0)) -> False) -> (exists y0 : nat, x0 y0) -> (forall y0 : nat, (x0 y0) -> x1 y0) -> (~ (exists y0 : nat, x1 y0)) -> False.
Definition term101 (x0 : nat -> Prop) := fun y0 : nat => ~ ((fun y1 : nat => x0 y1) y0).
Definition term139 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) (x3 : Prop) (x4 : Prop) := (fun y0 : Prop => ((x0 x2) = x3) -> (x3 -> (Peano.le x1 x2) = y0) -> ((x0 x2) -> Peano.le x1 x2) = (x3 -> y0)) x4.
Definition term130 (x0 : nat -> Prop) (x1 : nat) (x2 : nat -> Prop) (x3 : Prop) (x4 : Prop) := (fun y0 : Prop => ((Peano.le x1 (minimal x0)) = x3) -> (x3 -> (Peano.le x1 (minimal x2)) = y0) -> ((Peano.le x1 (minimal x0)) -> Peano.le x1 (minimal x2)) = (x3 -> y0)) x4.
Definition term63 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ ((forall y1 : nat, (Peano.le y1 y0) -> Peano.le y1 x0) -> Peano.le y0 x0)) -> (forall y1 : nat, Peano.le y1 y1) -> (forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y1 y2) /\ (Peano.le y2 y3)) -> Peano.le y1 y3) -> False) x1.
Definition term91 (x0 : nat -> Prop) (x1 : nat -> Prop) := fun y0 : nat => (x0 y0) -> x1 y0.
Definition term121 (x0 : nat) (x1 : nat -> Prop) := Peano.le x0 (minimal x1).
Definition term161 := forall y0 : nat -> Prop, forall y1 : nat -> Prop, ((exists y2 : nat, y0 y2) /\ (forall y2 : nat, (y0 y2) -> y1 y2)) -> Peano.le (minimal y1) (minimal y0).
Definition term88 := forall y0 : nat -> Prop, forall y1 : nat -> Prop, (exists y2 : nat, y1 y2) -> (forall y2 : nat, (y1 y2) -> y0 y2) -> exists y2 : nat, y0 y2.
Definition term87 := forall y0 : nat -> Prop, forall y1 : nat -> Prop, (exists y2 : nat, y1 y2) -> (forall y2 : nat, (y1 y2) -> y0 y2) -> (~ (exists y2 : nat, y0 y2)) -> False.
Definition term123 (x0 : nat -> Prop) (x1 : nat -> Prop) (x2 : nat) := (fun y0 : nat => (x0 y0) -> x1 y0) x2.
Definition term97 (x0 : nat -> Prop) := forall y0 : nat, ~ ((fun y1 : nat => x0 y1) y0).
Definition term132 (x0 : nat -> Prop) (x1 : nat -> Prop) (x2 : nat) (x3 : Prop) := ((Peano.le x2 (minimal x1)) = (forall y0 : nat, (x1 y0) -> Peano.le x2 y0)) -> ((forall y0 : nat, (x1 y0) -> Peano.le x2 y0) -> (Peano.le x2 (minimal x0)) = x3) -> ((Peano.le x2 (minimal x1)) -> Peano.le x2 (minimal x0)) = ((forall y0 : nat, (x1 y0) -> Peano.le x2 y0) -> x3).
Definition term50 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((~ (Peano.le x1 x0)) \/ (Peano.le x1 x2)).
Definition term62 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ ((forall y2 : nat, (Peano.le y2 y1) -> Peano.le y2 y0) -> Peano.le y1 y0)) -> (forall y2 : nat, Peano.le y2 y2) -> (forall y2 : nat, forall y3 : nat, forall y4 : nat, ((Peano.le y2 y3) /\ (Peano.le y3 y4)) -> Peano.le y2 y4) -> False) x0.
Definition term17 (x0 : nat) := fun y0 : nat => (~ ((forall y1 : nat, (Peano.le y1 y0) -> Peano.le y1 x0) -> Peano.le y0 x0)) -> (forall y1 : nat, Peano.le y1 y1) -> ~ (forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y1 y2) /\ (Peano.le y2 y3)) -> Peano.le y1 y3).
Definition term55 (x0 : nat) (x1 : nat) := ~ (~ (Peano.le x0 x1)).
Definition term152 (x0 : nat -> Prop) (x1 : nat) (x2 : nat -> Prop) := (forall y0 : nat, (x0 y0) -> Peano.le x1 y0) -> (Peano.le x1 (minimal x2)) = True.
Definition term51 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((Peano.le x1 x0) \/ (~ (Peano.le x1 x2))).
Definition term145 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := ((x1 x2) -> (Peano.le x0 x2) = True) -> ((x1 x2) -> Peano.le x0 x2) = ((x1 x2) -> True).
Definition term108 (x0 : nat -> Prop) (x1 : nat -> Prop) (x2 : nat) := @eq Prop ((x0 x2) \/ (~ (x1 x2))).
Definition term93 (x0 : nat -> Prop) (x1 : nat -> Prop) := fun y0 : nat => (~ (x0 y0)) \/ (x1 y0).
Definition term81 (x0 : nat -> Prop) := fun y0 : nat -> Prop => (exists y1 : nat, y0 y1) -> (forall y1 : nat, (y0 y1) -> x0 y1) -> (~ (exists y1 : nat, x0 y1)) -> False.
Definition term37 (x0 : nat) (x1 : nat) := fun y0 : nat => (~ (Peano.le y0 x0)) \/ (Peano.le y0 x1).
Definition term146 (x0 : nat -> Prop) (x1 : nat) := (x0 x1) -> True.
Definition term31 := forall y0 : nat, Peano.le y0 y0.
Definition term25 (x0 : nat) (x1 : nat) := fun y0 : nat => ((Peano.le x1 x0) /\ (Peano.le x0 y0)) -> Peano.le x1 y0.
Definition term142 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) (x3 : Prop) := ((x1 x2) -> (Peano.le x0 x2) = x3) -> ((x1 x2) -> Peano.le x0 x2) = ((x1 x2) -> x3).
Definition term153 (x0 : nat -> Prop) (x1 : nat -> Prop) (x2 : nat) := ((forall y0 : nat, (x1 y0) -> Peano.le x2 y0) -> (Peano.le x2 (minimal x0)) = True) -> ((Peano.le x2 (minimal x1)) -> Peano.le x2 (minimal x0)) = ((forall y0 : nat, (x1 y0) -> Peano.le x2 y0) -> True).
Definition term151 (x0 : Prop) := forall y0 : nat, x0.
Definition term118 (x0 : nat -> Prop) := forall y0 : nat, (exists y1 : nat, x0 y1) -> (Peano.le y0 (minimal x0)) = (forall y1 : nat, (x0 y1) -> Peano.le y0 y1).
Definition term70 (x0 : nat -> Prop) := ~ (exists y0 : nat, x0 y0).
Definition term117 (x0 : nat -> Prop) := (fun y0 : nat -> Prop => forall y1 : nat, (exists y2 : nat, y0 y2) -> (Peano.le y1 (minimal y0)) = (forall y2 : nat, (y0 y2) -> Peano.le y1 y2)) x0.
Definition term114 (x0 : nat -> Prop) := (fun y0 : nat -> Prop => forall y1 : nat -> Prop, (exists y2 : nat, y1 y2) -> (forall y2 : nat, (y1 y2) -> y0 y2) -> (~ (exists y2 : nat, y0 y2)) -> False) x0.
Definition term2 (x0 : nat) (x1 : nat) := (~ ((forall y0 : nat, (Peano.le y0 x0) -> Peano.le y0 x1) -> Peano.le x0 x1)) -> False.
Definition term58 (x0 : nat) (x1 : nat) := (Peano.le x0 x0) -> Peano.le x0 x1.
Definition term36 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.le x1 x0)) \/ (Peano.le x1 x2).
Definition term75 (x0 : nat -> Prop) := ~ (~ (exists y0 : nat, x0 y0)).
Definition term16 (x0 : nat) := fun y0 : nat => (~ ((forall y1 : nat, (Peano.le y1 y0) -> Peano.le y1 x0) -> Peano.le y0 x0)) -> (forall y1 : nat, Peano.le y1 y1) -> (forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y1 y2) /\ (Peano.le y2 y3)) -> Peano.le y1 y3) -> False.
Definition term32 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x1 x0) -> Peano.le x1 x2.
Definition term60 (x0 : nat) (x1 : nat) := (Peano.le x0 x1) -> False.
Definition term120 (x0 : nat -> Prop) (x1 : nat) := (exists y0 : nat, x0 y0) -> (Peano.le x1 (minimal x0)) = (forall y0 : nat, (x0 y0) -> Peano.le x1 y0).
Definition term21 := fun y0 : nat => forall y1 : nat, (~ ((forall y2 : nat, (Peano.le y2 y1) -> Peano.le y2 y0) -> Peano.le y1 y0)) -> (forall y2 : nat, Peano.le y2 y2) -> ~ (forall y2 : nat, forall y3 : nat, forall y4 : nat, ((Peano.le y2 y3) /\ (Peano.le y3 y4)) -> Peano.le y2 y4).
Definition term20 := fun y0 : nat => forall y1 : nat, (~ ((forall y2 : nat, (Peano.le y2 y1) -> Peano.le y2 y0) -> Peano.le y1 y0)) -> (forall y2 : nat, Peano.le y2 y2) -> (forall y2 : nat, forall y3 : nat, forall y4 : nat, ((Peano.le y2 y3) /\ (Peano.le y3 y4)) -> Peano.le y2 y4) -> False.
Definition term133 (x0 : nat -> Prop) (x1 : nat -> Prop) (x2 : nat) (x3 : Prop) := ((forall y0 : nat, (x1 y0) -> Peano.le x2 y0) -> (Peano.le x2 (minimal x0)) = x3) -> ((Peano.le x2 (minimal x1)) -> Peano.le x2 (minimal x0)) = ((forall y0 : nat, (x1 y0) -> Peano.le x2 y0) -> x3).
Definition term29 := fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2.
Definition term102 (x0 : nat -> Prop) := fun y0 : nat => ~ (x0 y0).
Definition term159 (x0 : nat -> Prop) (x1 : nat -> Prop) := ((exists y0 : nat, x1 y0) /\ (forall y0 : nat, (x1 y0) -> x0 y0)) -> Peano.le (minimal x0) (minimal x1).
Definition term56 (x0 : nat) (x1 : nat) := imp (~ (~ (Peano.le x0 x1))).
Definition term53 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (~ (Peano.le x1 x0))) -> Peano.le x1 x2.
