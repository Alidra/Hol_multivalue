Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term7 (x0 : ind) := ~ ((IND_SUC x0) = (@ε ind (fun y0 : ind => (forall y1 : ind, forall y2 : ind, ((IND_SUC y1) = (IND_SUC y2)) = (y1 = y2)) /\ (forall y1 : ind, ~ ((IND_SUC y1) = y0))))).
Definition term14 := (forall y0 : ind, forall y1 : ind, ((IND_SUC y0) = (IND_SUC y1)) = (y0 = y1)) /\ (forall y0 : ind, ~ ((IND_SUC y0) = IND_0)).
Definition term4 := (forall y0 : ind, forall y1 : ind, ((IND_SUC y0) = (IND_SUC y1)) = (y0 = y1)) /\ (forall y0 : ind, ~ ((IND_SUC y0) = (@ε ind (fun y1 : ind => (forall y2 : ind, forall y3 : ind, ((IND_SUC y2) = (IND_SUC y3)) = (y2 = y3)) /\ (forall y2 : ind, ~ ((IND_SUC y2) = y1)))))).
Definition term12 := forall y0 : ind, ~ ((IND_SUC y0) = IND_0).
Definition term10 := fun y0 : ind => ~ ((IND_SUC y0) = IND_0).
Definition term8 (x0 : ind) := ~ ((IND_SUC x0) = IND_0).
Definition term1 := (exists y0 : ind, (forall y1 : ind, forall y2 : ind, ((IND_SUC y1) = (IND_SUC y2)) = (y1 = y2)) /\ (forall y1 : ind, ~ ((IND_SUC y1) = y0))) -> (fun y0 : ind => (forall y1 : ind, forall y2 : ind, ((IND_SUC y1) = (IND_SUC y2)) = (y1 = y2)) /\ (forall y1 : ind, ~ ((IND_SUC y1) = y0))) (@ε ind (fun y0 : ind => (forall y1 : ind, forall y2 : ind, ((IND_SUC y1) = (IND_SUC y2)) = (y1 = y2)) /\ (forall y1 : ind, ~ ((IND_SUC y1) = y0)))).
Definition term3 := (fun y0 : ind => (forall y1 : ind, forall y2 : ind, ((IND_SUC y1) = (IND_SUC y2)) = (y1 = y2)) /\ (forall y1 : ind, ~ ((IND_SUC y1) = y0))) (@ε ind (fun y0 : ind => (forall y1 : ind, forall y2 : ind, ((IND_SUC y1) = (IND_SUC y2)) = (y1 = y2)) /\ (forall y1 : ind, ~ ((IND_SUC y1) = y0)))).
Definition term6 (x0 : ind) := @eq ind (IND_SUC x0).
Definition term0 (x0 : ind -> Prop) := (ex x0) -> x0 (@ε ind x0).
Definition term5 := @ε ind (fun y0 : ind => (forall y1 : ind, forall y2 : ind, ((IND_SUC y1) = (IND_SUC y2)) = (y1 = y2)) /\ (forall y1 : ind, ~ ((IND_SUC y1) = y0))).
Definition term9 := fun y0 : ind => ~ ((IND_SUC y0) = (@ε ind (fun y1 : ind => (forall y2 : ind, forall y3 : ind, ((IND_SUC y2) = (IND_SUC y3)) = (y2 = y3)) /\ (forall y2 : ind, ~ ((IND_SUC y2) = y1))))).
Definition term2 := fun y0 : ind => (forall y1 : ind, forall y2 : ind, ((IND_SUC y1) = (IND_SUC y2)) = (y1 = y2)) /\ (forall y1 : ind, ~ ((IND_SUC y1) = y0)).
Definition term11 := forall y0 : ind, ~ ((IND_SUC y0) = (@ε ind (fun y1 : ind => (forall y2 : ind, forall y3 : ind, ((IND_SUC y2) = (IND_SUC y3)) = (y2 = y3)) /\ (forall y2 : ind, ~ ((IND_SUC y2) = y1))))).
Definition term13 := and (forall y0 : ind, forall y1 : ind, ((IND_SUC y0) = (IND_SUC y1)) = (y0 = y1)).
