Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term74 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := ~ ((Peano.lt x2 x0) -> ~ (x1 x2)).
Definition term89 (x0 : nat) (x1 : nat) := ~ (x0 = x1).
Definition term240 (x0 : nat) := (fun y0 : nat => forall y1 : nat -> Prop, (y1 y0) -> (forall y2 : nat, (Peano.lt y2 y0) -> ~ (y1 y2)) -> (~ (forall y2 : nat, ((fun y3 : nat => (y1 y3) /\ (forall y4 : nat, (Peano.lt y4 y3) -> ~ (y1 y4))) y2) = (y2 = y0))) -> (forall y2 : nat, forall y3 : nat, (Peano.lt y2 y3) \/ ((Peano.lt y3 y2) \/ (y2 = y3))) -> False) x0.
Definition term156 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := exists y0 : nat, ((fun y1 : nat => (~ (x0 x1)) \/ ((Peano.lt y1 x1) /\ (x0 y1))) y0) /\ (x1 = x2).
Definition term75 (x0 : nat -> Prop) := ~ (all x0).
Definition term238 := (~ False) -> False.
Definition term29 (x0 : nat -> Prop) (x1 : nat) := (~ (forall y0 : nat, ((fun y1 : nat => (x0 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (x0 y2))) y0) = (y0 = x1))) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) \/ ((Peano.lt y1 y0) \/ (y0 = y1))) -> False.
Definition term67 (x0 : nat -> Prop) (x1 : nat) := ~ (x0 x1).
Definition term13 (x0 : nat -> Prop) := @eq nat (@ε nat (fun y0 : nat => (x0 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1)))).
Definition term231 (x0 : nat) (x1 : nat) := imp ((~ (Peano.lt x0 x1)) /\ (~ (x0 = x1))).
Definition term49 (x0 : nat -> Prop) (x1 : nat) := forall y0 : nat, ((x0 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1))) = (y0 = x1).
Definition term163 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := and ((fun y0 : nat => (~ (x1 x0)) \/ ((Peano.lt y0 x0) /\ (x1 y0))) x2).
Definition term205 (x0 : nat -> Prop) (x1 : nat) := @eq Prop (~ (x0 x1)).
Definition term1 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0, (forall y2 : a0, (y0 y2) = (y2 = y1)) -> (@ε a0 y0) = y1) x0.
Definition term90 (x0 : nat) (x1 : nat -> Prop) := and (~ ((x1 x0) /\ (forall y0 : nat, (Peano.lt y0 x0) -> ~ (x1 y0)))).
Definition term193 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) (x3 : nat) := (((x0 x2) /\ (forall y0 : nat, (~ (Peano.lt y0 x2)) \/ (~ (x0 y0)))) /\ (~ (x2 = x3))) \/ (((~ (x0 x2)) \/ ((Peano.lt x1 x2) /\ (x0 x1))) /\ (x2 = x3)).
Definition term215 (x0 : Prop) := ~ (~ x0).
Definition term120 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := ((fun y0 : nat => ((x0 y0) /\ (forall y1 : nat, (~ (Peano.lt y1 y0)) \/ (~ (x0 y1)))) /\ (~ (y0 = x1))) x2) \/ ((fun y0 : nat => ((~ (x0 y0)) \/ (exists y1 : nat, (Peano.lt y1 y0) /\ (x0 y1))) /\ (y0 = x1)) x2).
Definition term167 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := fun y0 : nat => ((fun y1 : nat => (~ (x0 x1)) \/ ((Peano.lt y1 x1) /\ (x0 y1))) y0) /\ (x1 = x2).
Definition term199 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (fun y0 : nat => (~ (Peano.lt y0 x0)) \/ (~ (x1 y0))) x2.
Definition term131 (x0 : nat -> Prop) (x1 : nat) := exists y0 : nat, ((~ (x0 y0)) \/ (exists y1 : nat, (Peano.lt y1 y0) /\ (x0 y1))) /\ (y0 = x1).
Definition term197 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => exists y1 : nat, (((x0 y0) /\ (forall y2 : nat, (~ (Peano.lt y2 y0)) \/ (~ (x0 y2)))) /\ (~ (y0 = x1))) \/ (((~ (x0 y0)) \/ ((Peano.lt y1 y0) /\ (x0 y1))) /\ (y0 = x1)).
Definition term18 (x0 : nat -> Prop) (x1 : nat) := forall y0 : nat, ((fun y1 : nat => (x0 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (x0 y2))) y0) = (y0 = x1).
Definition term128 (x0 : nat -> Prop) (x1 : nat) := or (exists y0 : nat, ((x0 y0) /\ (forall y1 : nat, (~ (Peano.lt y1 y0)) \/ (~ (x0 y1)))) /\ (~ (y0 = x1))).
Definition term203 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => ~ (x0 y0)) x1.
Definition term132 (x0 : nat -> Prop) (x1 : nat) := (exists y0 : nat, ((x0 y0) /\ (forall y1 : nat, (~ (Peano.lt y1 y0)) \/ (~ (x0 y1)))) /\ (~ (y0 = x1))) \/ (exists y0 : nat, ((~ (x0 y0)) \/ (exists y1 : nat, (Peano.lt y1 y0) /\ (x0 y1))) /\ (y0 = x1)).
Definition term110 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term17 (x0 : Prop) := (~ x0) -> False.
Definition term243 (x0 : nat -> Prop) := forall y0 : nat, ((x0 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1))) -> (minimal x0) = y0.
Definition term117 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((x0 y0) /\ (forall y1 : nat, (~ (Peano.lt y1 y0)) \/ (~ (x0 y1)))) /\ (~ (y0 = x1))) x2.
Definition term229 (x0 : nat) (x1 : nat) := (~ (Peano.lt x0 x1)) /\ (~ (x0 = x1)).
Definition term232 (x0 : nat) (x1 : nat) := ((~ (Peano.lt x1 x0)) /\ (~ (x1 = x0))) -> Peano.lt x0 x1.
Definition term48 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => ((x0 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1))) = (y0 = x1).
Definition term34 (x0 : nat -> Prop) (x1 : nat) := imp (x0 x1).
Definition term139 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (fun y0 : nat => (Peano.lt y0 x0) /\ (x1 y0)) x2.
Definition term47 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => ((fun y1 : nat => (x0 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (x0 y2))) y0) = (y0 = x1).
Definition term136 (x0 : Prop) (x1 : nat -> Prop) := exists y0 : nat, x0 \/ (x1 y0).
Definition term91 (x0 : nat) (x1 : nat -> Prop) := and ((~ (x1 x0)) \/ (exists y0 : nat, (Peano.lt y0 x0) /\ (x1 y0))).
Definition term100 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (((x0 x1) /\ (forall y0 : nat, (Peano.lt y0 x1) -> ~ (x0 y0))) /\ (~ (x1 = x2))) \/ ((~ ((x0 x1) /\ (forall y0 : nat, (Peano.lt y0 x1) -> ~ (x0 y0)))) /\ (x1 = x2)).
Definition term212 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term157 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (fun y0 : nat => (~ (x1 x0)) \/ ((Peano.lt y0 x0) /\ (x1 y0))) x2.
Definition term162 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := @eq Prop ((exists y0 : nat, (~ (x0 x1)) \/ ((Peano.lt y0 x1) /\ (x0 y0))) /\ (x1 = x2)).
Definition term161 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := @eq Prop ((exists y0 : nat, (fun y1 : nat => (~ (x0 x1)) \/ ((Peano.lt y1 x1) /\ (x0 y1))) y0) /\ (x1 = x2)).
Definition term191 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := @eq Prop ((((x0 x1) /\ (forall y0 : nat, (~ (Peano.lt y0 x1)) \/ (~ (x0 y0)))) /\ (~ (x1 = x2))) \/ (exists y0 : nat, ((~ (x0 x1)) \/ ((Peano.lt y0 x1) /\ (x0 y0))) /\ (x1 = x2))).
Definition term190 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := @eq Prop ((((x0 x1) /\ (forall y0 : nat, (~ (Peano.lt y0 x1)) \/ (~ (x0 y0)))) /\ (~ (x1 = x2))) \/ (exists y0 : nat, (fun y1 : nat => ((~ (x0 x1)) \/ ((Peano.lt y1 x1) /\ (x0 y1))) /\ (x1 = x2)) y0)).
Definition term77 (x0 : nat) (x1 : nat -> Prop) := ~ (forall y0 : nat, (Peano.lt y0 x0) -> ~ (x1 y0)).
Definition term50 (x0 : nat -> Prop) (x1 : nat) := ~ (forall y0 : nat, ((x0 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1))) = (y0 = x1)).
Definition term20 (x0 : nat -> Prop) (x1 : nat) := ~ (forall y0 : nat, ((fun y1 : nat => (x0 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (x0 y2))) y0) = (y0 = x1)).
Definition term26 := ~ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) \/ ((Peano.lt y1 y0) \/ (y0 = y1))).
Definition term7 (a0 : Type') := (forall y0 : a0 -> Prop, forall y1 : a0, (forall y2 : a0, (y0 y2) = (y2 = y1)) -> (@ε a0 y0) = y1) -> forall y0 : a0 -> Prop, forall y1 : a0, (forall y2 : a0, (y0 y2) = (y2 = y1)) -> (@ε a0 y0) = y1.
Definition term9 (x0 : nat -> Prop) := @ε nat (fun y0 : nat => (x0 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1))).
Definition term45 (x0 : nat -> Prop) (x1 : nat) := @eq Prop ((fun y0 : nat => (x0 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1))) x1).
Definition term169 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := exists y0 : nat, ((~ (x0 x1)) \/ ((Peano.lt y0 x1) /\ (x0 y0))) /\ (x1 = x2).
Definition term234 (x0 : Prop) (x1 : Prop) := (~ x0) \/ (~ x1).
Definition term211 (x0 : Prop) := (~ x0) -> x0.
Definition term183 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => (((x0 y0) /\ (forall y1 : nat, (~ (Peano.lt y1 y0)) \/ (~ (x0 y1)))) /\ (~ (y0 = x1))) \/ (exists y1 : nat, ((~ (x0 y0)) \/ ((Peano.lt y1 y0) /\ (x0 y1))) /\ (y0 = x1)).
Definition term57 := fun y0 : nat => forall y1 : nat -> Prop, (y1 y0) -> (forall y2 : nat, (Peano.lt y2 y0) -> ~ (y1 y2)) -> (~ (forall y2 : nat, ((y1 y2) /\ (forall y3 : nat, (Peano.lt y3 y2) -> ~ (y1 y3))) = (y2 = y0))) -> ~ (forall y2 : nat, forall y3 : nat, (Peano.lt y2 y3) \/ ((Peano.lt y3 y2) \/ (y2 = y3))).
Definition term41 := fun y0 : nat => forall y1 : nat -> Prop, (y1 y0) -> (forall y2 : nat, (Peano.lt y2 y0) -> ~ (y1 y2)) -> (~ (forall y2 : nat, ((fun y3 : nat => (y1 y3) /\ (forall y4 : nat, (Peano.lt y4 y3) -> ~ (y1 y4))) y2) = (y2 = y0))) -> ~ (forall y2 : nat, forall y3 : nat, (Peano.lt y2 y3) \/ ((Peano.lt y3 y2) \/ (y2 = y3))).
Definition term40 := fun y0 : nat => forall y1 : nat -> Prop, (y1 y0) -> (forall y2 : nat, (Peano.lt y2 y0) -> ~ (y1 y2)) -> (~ (forall y2 : nat, ((fun y3 : nat => (y1 y3) /\ (forall y4 : nat, (Peano.lt y4 y3) -> ~ (y1 y4))) y2) = (y2 = y0))) -> (forall y2 : nat, forall y3 : nat, (Peano.lt y2 y3) \/ ((Peano.lt y3 y2) \/ (y2 = y3))) -> False.
Definition term217 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (x0 x1) -> ~ (Peano.lt x1 x2).
Definition term44 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => (x0 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1))) x1.
Definition term227 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term145 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (~ (x1 x0)) \/ ((Peano.lt x2 x0) /\ (x1 x2)).
Definition term146 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => (~ (x1 x0)) \/ ((fun y1 : nat => (Peano.lt y1 x0) /\ (x1 y1)) y0).
Definition term21 (x0 : nat -> Prop) (x1 : nat) := (x0 x1) -> (forall y0 : nat, (Peano.lt y0 x1) -> ~ (x0 y0)) -> (~ (forall y0 : nat, ((fun y1 : nat => (x0 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (x0 y2))) y0) = (y0 = x1))) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) \/ ((Peano.lt y1 y0) \/ (y0 = y1))) -> False.
Definition term160 (x0 : nat) (x1 : nat -> Prop) := and (exists y0 : nat, (fun y1 : nat => (~ (x1 x0)) \/ ((Peano.lt y1 x0) /\ (x1 y1))) y0).
Definition term235 (x0 : Prop) (x1 : Prop) := ~ (x0 /\ x1).
Definition term170 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => exists y1 : nat, ((~ (x0 y0)) \/ ((Peano.lt y1 y0) /\ (x0 y1))) /\ (y0 = x1).
Definition term239 (x0 : nat -> Prop) (x1 : nat) := (x0 x1) -> False.
Definition term176 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => (fun y1 : nat => exists y2 : nat, ((~ (x0 y1)) \/ ((Peano.lt y2 y1) /\ (x0 y2))) /\ (y1 = x1)) y0.
Definition term116 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => ((~ (x0 y0)) \/ (exists y1 : nat, (Peano.lt y1 y0) /\ (x0 y1))) /\ (y0 = x1).
Definition term72 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (Peano.lt x2 x0) /\ (~ (~ (x1 x2))).
Definition term175 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (fun y0 : nat => exists y1 : nat, ((~ (x0 y0)) \/ ((Peano.lt y1 y0) /\ (x0 y1))) /\ (y0 = x1)) x2.
Definition term99 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := or (((x0 x1) /\ (forall y0 : nat, (~ (Peano.lt y0 x1)) \/ (~ (x0 y0)))) /\ (~ (x1 = x2))).
Definition term98 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := or (((x0 x1) /\ (forall y0 : nat, (Peano.lt y0 x1) -> ~ (x0 y0))) /\ (~ (x1 = x2))).
Definition term221 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term207 (x0 : nat) (x1 : nat) := (fun y0 : nat => Peano.lt x0 y0) x1.
Definition term236 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := ~ ((Peano.lt x2 x0) /\ (x1 x2)).
Definition term123 (x0 : nat -> Prop) (x1 : nat) := @eq Prop (exists y0 : nat, (((x0 y0) /\ (forall y1 : nat, (~ (Peano.lt y1 y0)) \/ (~ (x0 y1)))) /\ (~ (y0 = x1))) \/ (((~ (x0 y0)) \/ (exists y1 : nat, (Peano.lt y1 y0) /\ (x0 y1))) /\ (y0 = x1))).
Definition term122 (x0 : nat -> Prop) (x1 : nat) := @eq Prop (exists y0 : nat, ((fun y1 : nat => ((x0 y1) /\ (forall y2 : nat, (~ (Peano.lt y2 y1)) \/ (~ (x0 y2)))) /\ (~ (y1 = x1))) y0) \/ ((fun y1 : nat => ((~ (x0 y1)) \/ (exists y2 : nat, (Peano.lt y2 y1) /\ (x0 y2))) /\ (y1 = x1)) y0)).
Definition term5 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := forall y0 : a0, (x0 y0) = (y0 = x1).
Definition term210 (x0 : nat -> Prop) (x1 : nat) := (~ (x0 x1)) -> x0 x1.
Definition term68 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => (~ (Peano.lt y0 x0)) \/ (~ (x1 y0)).
Definition term173 (x0 : nat -> Prop) (x1 : nat) := (exists y0 : nat, (fun y1 : nat => ((x0 y1) /\ (forall y2 : nat, (~ (Peano.lt y2 y1)) \/ (~ (x0 y2)))) /\ (~ (y1 = x1))) y0) \/ (exists y0 : nat, (fun y1 : nat => exists y2 : nat, ((~ (x0 y1)) \/ ((Peano.lt y2 y1) /\ (x0 y2))) /\ (y1 = x1)) y0).
Definition term114 (x0 : nat -> Prop) (x1 : nat) := (exists y0 : nat, (fun y1 : nat => ((x0 y1) /\ (forall y2 : nat, (~ (Peano.lt y2 y1)) \/ (~ (x0 y2)))) /\ (~ (y1 = x1))) y0) \/ (exists y0 : nat, (fun y1 : nat => ((~ (x0 y1)) \/ (exists y2 : nat, (Peano.lt y2 y1) /\ (x0 y2))) /\ (y1 = x1)) y0).
Definition term25 := (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) \/ ((Peano.lt y1 y0) \/ (y0 = y1))) -> False.
Definition term64 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => (Peano.lt y0 x0) -> ~ (x1 y0).
Definition term148 (x0 : nat) (x1 : nat -> Prop) := exists y0 : nat, (~ (x1 x0)) \/ ((Peano.lt y0 x0) /\ (x1 y0)).
Definition term185 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (((x0 x1) /\ (forall y0 : nat, (~ (Peano.lt y0 x1)) \/ (~ (x0 y0)))) /\ (~ (x1 = x2))) \/ (exists y0 : nat, (fun y1 : nat => ((~ (x0 x1)) \/ ((Peano.lt y1 x1) /\ (x0 y1))) /\ (x1 = x2)) y0).
Definition term124 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => (fun y1 : nat => ((x0 y1) /\ (forall y2 : nat, (~ (Peano.lt y2 y1)) \/ (~ (x0 y2)))) /\ (~ (y1 = x1))) y0.
Definition term31 (x0 : nat) (x1 : nat -> Prop) := imp (forall y0 : nat, (Peano.lt y0 x0) -> ~ (x1 y0)).
Definition term209 (x0 : nat) (x1 : nat) := @eq Prop (Peano.lt x0 x1).
Definition term144 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (~ (x1 x0)) \/ ((fun y0 : nat => (Peano.lt y0 x0) /\ (x1 y0)) x2).
Definition term93 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := ((~ (x0 x1)) \/ (exists y0 : nat, (Peano.lt y0 x1) /\ (x0 y0))) /\ (x1 = x2).
Definition term4 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (forall y0 : a0, (x0 y0) = (y0 = x1)) -> (@ε a0 x0) = x1.
Definition term84 (x0 : nat -> Prop) (x1 : nat) := or (~ (x0 x1)).
Definition term216 (x0 : nat -> Prop) (x1 : nat) := imp (~ (~ (x0 x1))).
Definition term79 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (fun y0 : nat => (Peano.lt y0 x0) -> ~ (x1 y0)) x2.
Definition term63 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (Peano.lt x2 x0) -> ~ (x1 x2).
Definition term134 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 \/ (x1 y0).
Definition term3 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => (forall y1 : a0, (x0 y1) = (y1 = y0)) -> (@ε a0 x0) = y0) x1.
Definition term158 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => (fun y1 : nat => (~ (x1 x0)) \/ ((Peano.lt y1 x0) /\ (x1 y1))) y0.
Definition term15 (x0 : nat -> Prop) (x1 : nat) := (forall y0 : nat, ((fun y1 : nat => (x0 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (x0 y2))) y0) = (y0 = x1)) -> (@ε nat (fun y0 : nat => (x0 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1)))) = x1.
Definition term226 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term140 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => (fun y1 : nat => (Peano.lt y1 x0) /\ (x1 y1)) y0.
Definition term58 := forall y0 : nat, forall y1 : nat -> Prop, (y1 y0) -> (forall y2 : nat, (Peano.lt y2 y0) -> ~ (y1 y2)) -> (~ (forall y2 : nat, ((y1 y2) /\ (forall y3 : nat, (Peano.lt y3 y2) -> ~ (y1 y3))) = (y2 = y0))) -> ~ (forall y2 : nat, forall y3 : nat, (Peano.lt y2 y3) \/ ((Peano.lt y3 y2) \/ (y2 = y3))).
Definition term43 := forall y0 : nat, forall y1 : nat -> Prop, (y1 y0) -> (forall y2 : nat, (Peano.lt y2 y0) -> ~ (y1 y2)) -> (~ (forall y2 : nat, ((fun y3 : nat => (y1 y3) /\ (forall y4 : nat, (Peano.lt y4 y3) -> ~ (y1 y4))) y2) = (y2 = y0))) -> ~ (forall y2 : nat, forall y3 : nat, (Peano.lt y2 y3) \/ ((Peano.lt y3 y2) \/ (y2 = y3))).
Definition term42 := forall y0 : nat, forall y1 : nat -> Prop, (y1 y0) -> (forall y2 : nat, (Peano.lt y2 y0) -> ~ (y1 y2)) -> (~ (forall y2 : nat, ((fun y3 : nat => (y1 y3) /\ (forall y4 : nat, (Peano.lt y4 y3) -> ~ (y1 y4))) y2) = (y2 = y0))) -> (forall y2 : nat, forall y3 : nat, (Peano.lt y2 y3) \/ ((Peano.lt y3 y2) \/ (y2 = y3))) -> False.
Definition term27 := forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) \/ ((Peano.lt y1 y0) \/ (y0 = y1)).
Definition term16 (x0 : nat -> Prop) := fun y0 : nat => (x0 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1)).
Definition term196 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := exists y0 : nat, (((x0 x1) /\ (forall y1 : nat, (~ (Peano.lt y1 x1)) \/ (~ (x0 y1)))) /\ (~ (x1 = x2))) \/ (((~ (x0 x1)) \/ ((Peano.lt y0 x1) /\ (x0 y0))) /\ (x1 = x2)).
Definition term108 (x0 : nat -> Prop) (x1 : nat) := exists y0 : nat, (((x0 y0) /\ (forall y1 : nat, (~ (Peano.lt y1 y0)) \/ (~ (x0 y1)))) /\ (~ (y0 = x1))) \/ (((~ (x0 y0)) \/ (exists y1 : nat, (Peano.lt y1 y0) /\ (x0 y1))) /\ (y0 = x1)).
Definition term133 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 \/ (exists y0 : a0, x1 y0).
Definition term87 (x0 : nat) (x1 : nat -> Prop) := ~ ((x1 x0) /\ (forall y0 : nat, (Peano.lt y0 x0) -> ~ (x1 y0))).
Definition term181 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (((x0 x1) /\ (forall y0 : nat, (~ (Peano.lt y0 x1)) \/ (~ (x0 y0)))) /\ (~ (x1 = x2))) \/ (exists y0 : nat, ((~ (x0 x1)) \/ ((Peano.lt y0 x1) /\ (x0 y0))) /\ (x1 = x2)).
Definition term105 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := ~ ((fun y0 : nat => ((x0 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1))) = (y0 = x1)) x2).
Definition term80 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := ~ ((fun y0 : nat => (Peano.lt y0 x0) -> ~ (x1 y0)) x2).
Definition term186 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := exists y0 : nat, (((x0 x1) /\ (forall y1 : nat, (~ (Peano.lt y1 x1)) \/ (~ (x0 y1)))) /\ (~ (x1 = x2))) \/ ((fun y1 : nat => ((~ (x0 x1)) \/ ((Peano.lt y1 x1) /\ (x0 y1))) /\ (x1 = x2)) y0).
Definition term152 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) /\ x1.
Definition term195 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := fun y0 : nat => (((x0 x1) /\ (forall y1 : nat, (~ (Peano.lt y1 x1)) \/ (~ (x0 y1)))) /\ (~ (x1 = x2))) \/ (((~ (x0 x1)) \/ ((Peano.lt y0 x1) /\ (x0 y0))) /\ (x1 = x2)).
Definition term187 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => ((~ (x0 x1)) \/ ((Peano.lt y0 x1) /\ (x0 y0))) /\ (x1 = x2)) x3.
Definition term138 (x0 : nat) (x1 : nat -> Prop) := exists y0 : nat, (~ (x1 x0)) \/ ((fun y1 : nat => (Peano.lt y1 x0) /\ (x1 y1)) y0).
Definition term56 (x0 : nat) := forall y0 : nat -> Prop, (y0 x0) -> (forall y1 : nat, (Peano.lt y1 x0) -> ~ (y0 y1)) -> (~ (forall y1 : nat, ((y0 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (y0 y2))) = (y1 = x0))) -> ~ (forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) \/ ((Peano.lt y2 y1) \/ (y1 = y2))).
Definition term39 (x0 : nat) := forall y0 : nat -> Prop, (y0 x0) -> (forall y1 : nat, (Peano.lt y1 x0) -> ~ (y0 y1)) -> (~ (forall y1 : nat, ((fun y2 : nat => (y0 y2) /\ (forall y3 : nat, (Peano.lt y3 y2) -> ~ (y0 y3))) y1) = (y1 = x0))) -> ~ (forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) \/ ((Peano.lt y2 y1) \/ (y1 = y2))).
Definition term38 (x0 : nat) := forall y0 : nat -> Prop, (y0 x0) -> (forall y1 : nat, (Peano.lt y1 x0) -> ~ (y0 y1)) -> (~ (forall y1 : nat, ((fun y2 : nat => (y0 y2) /\ (forall y3 : nat, (Peano.lt y3 y2) -> ~ (y0 y3))) y1) = (y1 = x0))) -> (forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) \/ ((Peano.lt y2 y1) \/ (y1 = y2))) -> False.
Definition term172 (x0 : nat -> Prop) (x1 : nat) := (exists y0 : nat, ((x0 y0) /\ (forall y1 : nat, (~ (Peano.lt y1 y0)) \/ (~ (x0 y1)))) /\ (~ (y0 = x1))) \/ (exists y0 : nat, exists y1 : nat, ((~ (x0 y0)) \/ ((Peano.lt y1 y0) /\ (x0 y1))) /\ (y0 = x1)).
Definition term174 (x0 : nat -> Prop) (x1 : nat) := exists y0 : nat, ((fun y1 : nat => ((x0 y1) /\ (forall y2 : nat, (~ (Peano.lt y2 y1)) \/ (~ (x0 y2)))) /\ (~ (y1 = x1))) y0) \/ ((fun y1 : nat => exists y2 : nat, ((~ (x0 y1)) \/ ((Peano.lt y2 y1) /\ (x0 y2))) /\ (y1 = x1)) y0).
Definition term113 (x0 : nat -> Prop) (x1 : nat) := exists y0 : nat, ((fun y1 : nat => ((x0 y1) /\ (forall y2 : nat, (~ (Peano.lt y2 y1)) \/ (~ (x0 y2)))) /\ (~ (y1 = x1))) y0) \/ ((fun y1 : nat => ((~ (x0 y1)) \/ (exists y2 : nat, (Peano.lt y2 y1) /\ (x0 y2))) /\ (y1 = x1)) y0).
Definition term208 (x0 : nat) (x1 : nat) := @eq Prop ((fun y0 : nat => Peano.lt x0 y0) x1).
Definition term237 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := ((Peano.lt x2 x0) /\ (x1 x2)) -> False.
Definition term2 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, (forall y1 : a0, (x0 y1) = (y1 = y0)) -> (@ε a0 x0) = y0.
Definition term223 (x0 : nat) (x1 : nat) := @eq Prop ((Peano.lt x0 x1) \/ ((Peano.lt x1 x0) \/ (x0 = x1))).
Definition term95 (x0 : nat) (x1 : nat -> Prop) := and ((x1 x0) /\ (forall y0 : nat, (~ (Peano.lt y0 x0)) \/ (~ (x1 y0)))).
Definition term94 (x0 : nat) (x1 : nat -> Prop) := and ((x1 x0) /\ (forall y0 : nat, (Peano.lt y0 x0) -> ~ (x1 y0))).
Definition term86 (x0 : nat) (x1 : nat -> Prop) := (~ (x1 x0)) \/ (exists y0 : nat, (Peano.lt y0 x0) /\ (x1 y0)).
Definition term206 (x0 : nat) := fun y0 : nat => Peano.lt x0 y0.
Definition term154 (x0 : nat -> Prop) (x1 : Prop) := exists y0 : nat, (x0 y0) /\ x1.
Definition term19 (x0 : nat -> Prop) (x1 : nat) := (~ (forall y0 : nat, ((fun y1 : nat => (x0 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (x0 y2))) y0) = (y0 = x1))) -> False.
Definition term155 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (exists y0 : nat, (fun y1 : nat => (~ (x0 x1)) \/ ((Peano.lt y1 x1) /\ (x0 y1))) y0) /\ (x1 = x2).
Definition term150 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (exists y0 : nat, (~ (x0 x1)) \/ ((Peano.lt y0 x1) /\ (x0 y0))) /\ (x1 = x2).
Definition term11 (x0 : nat) (x1 : nat -> Prop) := forall y0 : nat, (Peano.lt y0 x0) -> ~ (x1 y0).
Definition term224 (x0 : nat) (x1 : nat) := (~ ((Peano.lt x1 x0) \/ (x1 = x0))) -> Peano.lt x0 x1.
Definition term107 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => (((x0 y0) /\ (forall y1 : nat, (~ (Peano.lt y1 y0)) \/ (~ (x0 y1)))) /\ (~ (y0 = x1))) \/ (((~ (x0 y0)) \/ (exists y1 : nat, (Peano.lt y1 y0) /\ (x0 y1))) /\ (y0 = x1)).
Definition term70 (x0 : nat -> Prop) (x1 : nat) := ~ (~ (x0 x1)).
Definition term24 (x0 : nat -> Prop) (x1 : nat) := (((x0 x1) -> (forall y0 : nat, (Peano.lt y0 x1) -> ~ (x0 y0)) -> (~ (forall y0 : nat, ((fun y1 : nat => (x0 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (x0 y2))) y0) = (y0 = x1))) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) \/ ((Peano.lt y1 y0) \/ (y0 = y1))) -> False) -> (x0 x1) -> (forall y0 : nat, (Peano.lt y0 x1) -> ~ (x0 y0)) -> (~ (forall y0 : nat, ((fun y1 : nat => (x0 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (x0 y2))) y0) = (y0 = x1))) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) \/ ((Peano.lt y1 y0) \/ (y0 = y1))) -> False) -> ((x0 x1) -> (forall y0 : nat, (Peano.lt y0 x1) -> ~ (x0 y0)) -> (~ (forall y0 : nat, ((fun y1 : nat => (x0 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (x0 y2))) y0) = (y0 = x1))) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) \/ ((Peano.lt y1 y0) \/ (y0 = y1))) -> False) -> (x0 x1) -> (forall y0 : nat, (Peano.lt y0 x1) -> ~ (x0 y0)) -> (~ (forall y0 : nat, ((fun y1 : nat => (x0 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (x0 y2))) y0) = (y0 = x1))) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) \/ ((Peano.lt y1 y0) \/ (y0 = y1))) -> False.
Definition term53 (x0 : nat -> Prop) (x1 : nat) := (forall y0 : nat, (Peano.lt y0 x1) -> ~ (x0 y0)) -> (~ (forall y0 : nat, ((x0 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1))) = (y0 = x1))) -> ~ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) \/ ((Peano.lt y1 y0) \/ (y0 = y1))).
Definition term33 (x0 : nat -> Prop) (x1 : nat) := (forall y0 : nat, (Peano.lt y0 x1) -> ~ (x0 y0)) -> (~ (forall y0 : nat, ((fun y1 : nat => (x0 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (x0 y2))) y0) = (y0 = x1))) -> ~ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) \/ ((Peano.lt y1 y0) \/ (y0 = y1))).
Definition term201 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt x0 y0) \/ ((Peano.lt y0 x0) \/ (x0 = y0))) x1.
Definition term222 (x0 : nat) (x1 : nat) := (Peano.lt x1 x0) \/ ((Peano.lt x0 x1) \/ (x0 = x1)).
Definition term189 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := exists y0 : nat, (fun y1 : nat => ((~ (x0 x1)) \/ ((Peano.lt y1 x1) /\ (x0 y1))) /\ (x1 = x2)) y0.
Definition term159 (x0 : nat) (x1 : nat -> Prop) := exists y0 : nat, (fun y1 : nat => (~ (x1 x0)) \/ ((Peano.lt y1 x0) /\ (x1 y1))) y0.
Definition term141 (x0 : nat) (x1 : nat -> Prop) := exists y0 : nat, (fun y1 : nat => (Peano.lt y1 x0) /\ (x1 y1)) y0.
Definition term130 (x0 : nat -> Prop) (x1 : nat) := exists y0 : nat, (fun y1 : nat => ((~ (x0 y1)) \/ (exists y2 : nat, (Peano.lt y2 y1) /\ (x0 y2))) /\ (y1 = x1)) y0.
Definition term125 (x0 : nat -> Prop) (x1 : nat) := exists y0 : nat, (fun y1 : nat => ((x0 y1) /\ (forall y2 : nat, (~ (Peano.lt y2 y1)) \/ (~ (x0 y2)))) /\ (~ (y1 = x1))) y0.
Definition term59 (x0 : nat) (x1 : nat) := (Peano.lt x0 x1) \/ ((Peano.lt x1 x0) \/ (x0 = x1)).
Definition term225 (x0 : nat) (x1 : nat) := (Peano.lt x0 x1) \/ (x0 = x1).
Definition term71 (x0 : nat) (x1 : nat) := and (Peano.lt x0 x1).
Definition term168 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := fun y0 : nat => ((~ (x0 x1)) \/ ((Peano.lt y0 x1) /\ (x0 y0))) /\ (x1 = x2).
Definition term12 (x0 : nat -> Prop) := @eq nat (minimal x0).
Definition term55 (x0 : nat) := fun y0 : nat -> Prop => (y0 x0) -> (forall y1 : nat, (Peano.lt y1 x0) -> ~ (y0 y1)) -> (~ (forall y1 : nat, ((y0 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (y0 y2))) = (y1 = x0))) -> ~ (forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) \/ ((Peano.lt y2 y1) \/ (y1 = y2))).
Definition term37 (x0 : nat) := fun y0 : nat -> Prop => (y0 x0) -> (forall y1 : nat, (Peano.lt y1 x0) -> ~ (y0 y1)) -> (~ (forall y1 : nat, ((fun y2 : nat => (y0 y2) /\ (forall y3 : nat, (Peano.lt y3 y2) -> ~ (y0 y3))) y1) = (y1 = x0))) -> ~ (forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) \/ ((Peano.lt y2 y1) \/ (y1 = y2))).
Definition term36 (x0 : nat) := fun y0 : nat -> Prop => (y0 x0) -> (forall y1 : nat, (Peano.lt y1 x0) -> ~ (y0 y1)) -> (~ (forall y1 : nat, ((fun y2 : nat => (y0 y2) /\ (forall y3 : nat, (Peano.lt y3 y2) -> ~ (y0 y3))) y1) = (y1 = x0))) -> (forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) \/ ((Peano.lt y2 y1) \/ (y1 = y2))) -> False.
Definition term8 (x0 : nat -> Prop) := (fun y0 : nat -> Prop => (minimal y0) = (@ε nat (fun y1 : nat => (y0 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (y0 y2))))) x0.
Definition term204 (x0 : nat -> Prop) (x1 : nat) := @eq Prop ((fun y0 : nat => ~ (x0 y0)) x1).
Definition term182 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => ((fun y1 : nat => ((x0 y1) /\ (forall y2 : nat, (~ (Peano.lt y2 y1)) \/ (~ (x0 y2)))) /\ (~ (y1 = x1))) y0) \/ ((fun y1 : nat => exists y2 : nat, ((~ (x0 y1)) \/ ((Peano.lt y2 y1) /\ (x0 y2))) /\ (y1 = x1)) y0).
Definition term214 (x0 : nat) (x1 : nat) := ~ (Peano.lt x0 x1).
Definition term244 := forall y0 : nat -> Prop, forall y1 : nat, ((y0 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (y0 y2))) -> (minimal y0) = y1.
Definition term153 (x0 : nat -> Prop) (x1 : Prop) := (exists y0 : nat, x0 y0) /\ x1.
Definition term92 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (~ ((x0 x1) /\ (forall y0 : nat, (Peano.lt y0 x1) -> ~ (x0 y0)))) /\ (x1 = x2).
Definition term184 (x0 : nat -> Prop) (x1 : nat) := exists y0 : nat, (((x0 y0) /\ (forall y1 : nat, (~ (Peano.lt y1 y0)) \/ (~ (x0 y1)))) /\ (~ (y0 = x1))) \/ (exists y1 : nat, ((~ (x0 y0)) \/ ((Peano.lt y1 y0) /\ (x0 y1))) /\ (y0 = x1)).
Definition term119 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((~ (x0 y0)) \/ (exists y1 : nat, (Peano.lt y1 y0) /\ (x0 y1))) /\ (y0 = x1)) x2.
Definition term200 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y0 y1) \/ ((Peano.lt y1 y0) \/ (y0 = y1))) x0.
Definition term23 (x0 : nat -> Prop) (x1 : nat) := (((x0 x1) -> (forall y0 : nat, (Peano.lt y0 x1) -> ~ (x0 y0)) -> (~ (forall y0 : nat, ((fun y1 : nat => (x0 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (x0 y2))) y0) = (y0 = x1))) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) \/ ((Peano.lt y1 y0) \/ (y0 = y1))) -> False) -> (x0 x1) -> (forall y0 : nat, (Peano.lt y0 x1) -> ~ (x0 y0)) -> (~ (forall y0 : nat, ((fun y1 : nat => (x0 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (x0 y2))) y0) = (y0 = x1))) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) \/ ((Peano.lt y1 y0) \/ (y0 = y1))) -> False) -> (x0 x1) -> (forall y0 : nat, (Peano.lt y0 x1) -> ~ (x0 y0)) -> (~ (forall y0 : nat, ((fun y1 : nat => (x0 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (x0 y2))) y0) = (y0 = x1))) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) \/ ((Peano.lt y1 y0) \/ (y0 = y1))) -> False.
Definition term85 (x0 : nat) (x1 : nat -> Prop) := (~ (x1 x0)) \/ (~ (forall y0 : nat, (Peano.lt y0 x0) -> ~ (x1 y0))).
Definition term180 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := ((fun y0 : nat => ((x0 y0) /\ (forall y1 : nat, (~ (Peano.lt y1 y0)) \/ (~ (x0 y1)))) /\ (~ (y0 = x1))) x2) \/ ((fun y0 : nat => exists y1 : nat, ((~ (x0 y0)) \/ ((Peano.lt y1 y0) /\ (x0 y1))) /\ (y0 = x1)) x2).
Definition term82 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => (Peano.lt y0 x0) /\ (x1 y0).
Definition term194 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := fun y0 : nat => (((x0 x1) /\ (forall y1 : nat, (~ (Peano.lt y1 x1)) \/ (~ (x0 y1)))) /\ (~ (x1 = x2))) \/ ((fun y1 : nat => ((~ (x0 x1)) \/ ((Peano.lt y1 x1) /\ (x0 y1))) /\ (x1 = x2)) y0).
Definition term149 (x0 : nat) (x1 : nat -> Prop) := and (exists y0 : nat, (~ (x1 x0)) \/ ((Peano.lt y0 x0) /\ (x1 y0))).
Definition term46 (x0 : nat) (x1 : nat -> Prop) := @eq Prop ((x1 x0) /\ (forall y0 : nat, (Peano.lt y0 x0) -> ~ (x1 y0))).
Definition term220 (x0 : nat) (x1 : nat) := (x0 = x1) -> ~ (x0 = x1).
Definition term32 (x0 : nat -> Prop) (x1 : nat) := (forall y0 : nat, (Peano.lt y0 x1) -> ~ (x0 y0)) -> (~ (forall y0 : nat, ((fun y1 : nat => (x0 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (x0 y2))) y0) = (y0 = x1))) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) \/ ((Peano.lt y1 y0) \/ (y0 = y1))) -> False.
Definition term102 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := ~ (((x0 x1) /\ (forall y0 : nat, (Peano.lt y0 x1) -> ~ (x0 y0))) = (x1 = x2)).
Definition term104 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((x0 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1))) = (y0 = x1)) x2.
Definition term103 (x0 : nat -> Prop) (x1 : nat) := exists y0 : nat, ~ ((fun y1 : nat => ((x0 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (x0 y2))) = (y1 = x1)) y0).
Definition term78 (x0 : nat) (x1 : nat -> Prop) := exists y0 : nat, ~ ((fun y1 : nat => (Peano.lt y1 x0) -> ~ (x1 y1)) y0).
Definition term6 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (forall y0 : a0 -> Prop, forall y1 : a0, (forall y2 : a0, (y0 y2) = (y2 = y1)) -> (@ε a0 y0) = y1) -> (@ε a0 x0) = x1.
Definition term233 (x0 : nat) (x1 : nat) := (~ (Peano.lt x0 x1)) -> Peano.lt x0 x1.
Definition term118 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := or ((fun y0 : nat => ((x0 y0) /\ (forall y1 : nat, (~ (Peano.lt y1 y0)) \/ (~ (x0 y1)))) /\ (~ (y0 = x1))) x2).
Definition term52 (x0 : nat -> Prop) (x1 : nat) := (~ (forall y0 : nat, ((x0 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1))) = (y0 = x1))) -> ~ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) \/ ((Peano.lt y1 y0) \/ (y0 = y1))).
Definition term30 (x0 : nat -> Prop) (x1 : nat) := (~ (forall y0 : nat, ((fun y1 : nat => (x0 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (x0 y2))) y0) = (y0 = x1))) -> ~ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) \/ ((Peano.lt y1 y0) \/ (y0 = y1))).
Definition term137 (x0 : nat) (x1 : nat -> Prop) := (~ (x1 x0)) \/ (exists y0 : nat, (fun y1 : nat => (Peano.lt y1 x0) /\ (x1 y1)) y0).
Definition term61 (x0 : nat) := forall y0 : nat, (Peano.lt x0 y0) \/ ((Peano.lt y0 x0) \/ (x0 = y0)).
Definition term83 (x0 : nat) (x1 : nat -> Prop) := exists y0 : nat, (Peano.lt y0 x0) /\ (x1 y0).
Definition term165 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) (x3 : nat) := ((fun y0 : nat => (~ (x0 x2)) \/ ((Peano.lt y0 x2) /\ (x0 y0))) x1) /\ (x2 = x3).
Definition term241 (x0 : nat) (x1 : nat -> Prop) := (fun y0 : nat -> Prop => (y0 x0) -> (forall y1 : nat, (Peano.lt y1 x0) -> ~ (y0 y1)) -> (~ (forall y1 : nat, ((fun y2 : nat => (y0 y2) /\ (forall y3 : nat, (Peano.lt y3 y2) -> ~ (y0 y3))) y1) = (y1 = x0))) -> (forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) \/ ((Peano.lt y2 y1) \/ (y1 = y2))) -> False) x1.
Definition term213 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (~ (~ (x0 x1))) -> ~ (Peano.lt x1 x2).
Definition term97 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := ((x0 x1) /\ (forall y0 : nat, (~ (Peano.lt y0 x1)) \/ (~ (x0 y0)))) /\ (~ (x1 = x2)).
Definition term96 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := ((x0 x1) /\ (forall y0 : nat, (Peano.lt y0 x1) -> ~ (x0 y0))) /\ (~ (x1 = x2)).
Definition term14 (x0 : nat -> Prop) (x1 : nat) := (forall y0 : nat, (x0 y0) = (y0 = x1)) -> (@ε nat x0) = x1.
Definition term177 (x0 : nat -> Prop) (x1 : nat) := exists y0 : nat, (fun y1 : nat => exists y2 : nat, ((~ (x0 y1)) \/ ((Peano.lt y2 y1) /\ (x0 y2))) /\ (y1 = x1)) y0.
Definition term198 (x0 : nat -> Prop) (x1 : nat) := exists y0 : nat, exists y1 : nat, (((x0 y0) /\ (forall y2 : nat, (~ (Peano.lt y2 y0)) \/ (~ (x0 y2)))) /\ (~ (y0 = x1))) \/ (((~ (x0 y0)) \/ ((Peano.lt y1 y0) /\ (x0 y1))) /\ (y0 = x1)).
Definition term171 (x0 : nat -> Prop) (x1 : nat) := exists y0 : nat, exists y1 : nat, ((~ (x0 y0)) \/ ((Peano.lt y1 y0) /\ (x0 y1))) /\ (y0 = x1).
Definition term65 (x0 : nat -> Prop) (x1 : nat) := and (x0 x1).
Definition term111 (x0 : nat -> Prop) (x1 : nat -> Prop) := exists y0 : nat, (x0 y0) \/ (x1 y0).
Definition term106 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => ~ ((fun y1 : nat => ((x0 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (x0 y2))) = (y1 = x1)) y0).
Definition term81 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => ~ ((fun y1 : nat => (Peano.lt y1 x0) -> ~ (x1 y1)) y0).
Definition term166 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) (x3 : nat) := ((~ (x0 x2)) \/ ((Peano.lt x1 x2) /\ (x0 x1))) /\ (x2 = x3).
Definition term151 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) /\ x1.
Definition term121 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => ((fun y1 : nat => ((x0 y1) /\ (forall y2 : nat, (~ (Peano.lt y2 y1)) \/ (~ (x0 y2)))) /\ (~ (y1 = x1))) y0) \/ ((fun y1 : nat => ((~ (x0 y1)) \/ (exists y2 : nat, (Peano.lt y2 y1) /\ (x0 y2))) /\ (y1 = x1)) y0).
Definition term164 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := and ((~ (x1 x0)) \/ ((Peano.lt x2 x0) /\ (x1 x2))).
Definition term127 (x0 : nat -> Prop) (x1 : nat) := or (exists y0 : nat, (fun y1 : nat => ((x0 y1) /\ (forall y2 : nat, (~ (Peano.lt y2 y1)) \/ (~ (x0 y2)))) /\ (~ (y1 = x1))) y0).
Definition term66 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (~ (Peano.lt x2 x0)) \/ (~ (x1 x2)).
Definition term88 (x0 : nat) (x1 : nat -> Prop) := (x1 x0) /\ (forall y0 : nat, (~ (Peano.lt y0 x0)) \/ (~ (x1 y0))).
Definition term10 (x0 : nat) (x1 : nat -> Prop) := (x1 x0) /\ (forall y0 : nat, (Peano.lt y0 x0) -> ~ (x1 y0)).
Definition term228 (x0 : nat) (x1 : nat) := ~ ((Peano.lt x0 x1) \/ (x0 = x1)).
Definition term73 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (Peano.lt x2 x0) /\ (x1 x2).
Definition term218 (x0 : nat) (x1 : nat) := (Peano.lt x0 x1) -> ~ (Peano.lt x0 x1).
Definition term101 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (((x0 x1) /\ (forall y0 : nat, (~ (Peano.lt y0 x1)) \/ (~ (x0 y0)))) /\ (~ (x1 = x2))) \/ (((~ (x0 x1)) \/ (exists y0 : nat, (Peano.lt y0 x1) /\ (x0 y0))) /\ (x1 = x2)).
Definition term143 (x0 : nat) (x1 : nat -> Prop) := @eq Prop ((~ (x1 x0)) \/ (exists y0 : nat, (Peano.lt y0 x0) /\ (x1 y0))).
Definition term142 (x0 : nat) (x1 : nat -> Prop) := @eq Prop ((~ (x1 x0)) \/ (exists y0 : nat, (fun y1 : nat => (Peano.lt y1 x0) /\ (x1 y1)) y0)).
Definition term60 (x0 : nat) := fun y0 : nat => (Peano.lt x0 y0) \/ ((Peano.lt y0 x0) \/ (x0 = y0)).
Definition term192 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) (x3 : nat) := (((x0 x1) /\ (forall y0 : nat, (~ (Peano.lt y0 x1)) \/ (~ (x0 y0)))) /\ (~ (x1 = x2))) \/ ((fun y0 : nat => ((~ (x0 x1)) \/ ((Peano.lt y0 x1) /\ (x0 y0))) /\ (x1 = x2)) x3).
Definition term54 (x0 : nat -> Prop) (x1 : nat) := (x0 x1) -> (forall y0 : nat, (Peano.lt y0 x1) -> ~ (x0 y0)) -> (~ (forall y0 : nat, ((x0 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1))) = (y0 = x1))) -> ~ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) \/ ((Peano.lt y1 y0) \/ (y0 = y1))).
Definition term35 (x0 : nat -> Prop) (x1 : nat) := (x0 x1) -> (forall y0 : nat, (Peano.lt y0 x1) -> ~ (x0 y0)) -> (~ (forall y0 : nat, ((fun y1 : nat => (x0 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (x0 y2))) y0) = (y0 = x1))) -> ~ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) \/ ((Peano.lt y1 y0) \/ (y0 = y1))).
Definition term109 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term76 (x0 : nat -> Prop) := exists y0 : nat, ~ (x0 y0).
Definition term0 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0, (forall y2 : a0, (y0 y2) = (y2 = y1)) -> (@ε a0 y0) = y1.
Definition term135 (x0 : Prop) (x1 : nat -> Prop) := x0 \/ (exists y0 : nat, x1 y0).
Definition term115 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => ((x0 y0) /\ (forall y1 : nat, (~ (Peano.lt y1 y0)) \/ (~ (x0 y1)))) /\ (~ (y0 = x1)).
Definition term242 (x0 : nat -> Prop) (x1 : nat) := ((x0 x1) /\ (forall y0 : nat, (Peano.lt y0 x1) -> ~ (x0 y0))) -> (minimal x0) = x1.
Definition term22 (x0 : nat -> Prop) (x1 : nat) := ((x0 x1) -> (forall y0 : nat, (Peano.lt y0 x1) -> ~ (x0 y0)) -> (~ (forall y0 : nat, ((fun y1 : nat => (x0 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (x0 y2))) y0) = (y0 = x1))) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) \/ ((Peano.lt y1 y0) \/ (y0 = y1))) -> False) -> (x0 x1) -> (forall y0 : nat, (Peano.lt y0 x1) -> ~ (x0 y0)) -> (~ (forall y0 : nat, ((fun y1 : nat => (x0 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (x0 y2))) y0) = (y0 = x1))) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) \/ ((Peano.lt y1 y0) \/ (y0 = y1))) -> False.
Definition term62 := fun y0 : nat => forall y1 : nat, (Peano.lt y0 y1) \/ ((Peano.lt y1 y0) \/ (y0 = y1)).
Definition term230 (x0 : nat) (x1 : nat) := imp (~ ((Peano.lt x0 x1) \/ (x0 = x1))).
Definition term112 (x0 : nat -> Prop) (x1 : nat -> Prop) := (exists y0 : nat, x0 y0) \/ (exists y0 : nat, x1 y0).
Definition term51 (x0 : nat -> Prop) (x1 : nat) := imp (~ (forall y0 : nat, ((x0 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1))) = (y0 = x1))).
Definition term28 (x0 : nat -> Prop) (x1 : nat) := imp (~ (forall y0 : nat, ((fun y1 : nat => (x0 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (x0 y2))) y0) = (y0 = x1))).
Definition term219 (x0 : Prop) := x0 -> ~ x0.
Definition term202 (x0 : nat -> Prop) := fun y0 : nat => ~ (x0 y0).
Definition term147 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => (~ (x1 x0)) \/ ((Peano.lt y0 x0) /\ (x1 y0)).
Definition term126 (x0 : nat -> Prop) (x1 : nat) := exists y0 : nat, ((x0 y0) /\ (forall y1 : nat, (~ (Peano.lt y1 y0)) \/ (~ (x0 y1)))) /\ (~ (y0 = x1)).
Definition term69 (x0 : nat) (x1 : nat -> Prop) := forall y0 : nat, (~ (Peano.lt y0 x0)) \/ (~ (x1 y0)).
Definition term188 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := fun y0 : nat => (fun y1 : nat => ((~ (x0 x1)) \/ ((Peano.lt y1 x1) /\ (x0 y1))) /\ (x1 = x2)) y0.
Definition term129 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => (fun y1 : nat => ((~ (x0 y1)) \/ (exists y2 : nat, (Peano.lt y2 y1) /\ (x0 y2))) /\ (y1 = x1)) y0.
Definition term179 (x0 : nat -> Prop) (x1 : nat) := @eq Prop ((exists y0 : nat, ((x0 y0) /\ (forall y1 : nat, (~ (Peano.lt y1 y0)) \/ (~ (x0 y1)))) /\ (~ (y0 = x1))) \/ (exists y0 : nat, exists y1 : nat, ((~ (x0 y0)) \/ ((Peano.lt y1 y0) /\ (x0 y1))) /\ (y0 = x1))).
Definition term178 (x0 : nat -> Prop) (x1 : nat) := @eq Prop ((exists y0 : nat, (fun y1 : nat => ((x0 y1) /\ (forall y2 : nat, (~ (Peano.lt y2 y1)) \/ (~ (x0 y2)))) /\ (~ (y1 = x1))) y0) \/ (exists y0 : nat, (fun y1 : nat => exists y2 : nat, ((~ (x0 y1)) \/ ((Peano.lt y2 y1) /\ (x0 y2))) /\ (y1 = x1)) y0)).
