Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term8 (a0 : Type') (x0 : a0 -> Prop) (x1 : list a0) := (fun y0 : list a0 => (~ (@EX a0 x0 y0)) = (@List.Forall a0 (fun y1 : a0 => ~ (x0 y1)) y0)) x1.
Definition term56 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => ~ (x0 y0)) x1.
Definition term59 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @eq Prop ((fun y0 : a0 => (fun y1 : a0 => ~ (x0 y1)) y0) x1).
Definition term23 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => forall y1 : list a0, ((~ (@EX a0 x0 y1)) = (@List.Forall a0 (fun y2 : a0 => ~ (x0 y2)) y1)) -> (~ (@EX a0 x0 (@cons a0 y0 y1))) = (@List.Forall a0 (fun y2 : a0 => ~ (x0 y2)) (@cons a0 y0 y1)).
Definition term34 (a0 : Type') (x0 : a0 -> Prop) := @eq Prop (~ (@EX a0 x0 (@nil a0))).
Definition term11 (a0 : Type') (x0 : a0 -> Prop) (x1 : list a0) := imp ((fun y0 : list a0 => (~ (@EX a0 x0 y0)) = (@List.Forall a0 (fun y1 : a0 => ~ (x0 y1)) y0)) x1).
Definition term28 (a0 : Type') (x0 : a0 -> Prop) := imp (((fun y0 : list a0 => (~ (@EX a0 x0 y0)) = (@List.Forall a0 (fun y1 : a0 => ~ (x0 y1)) y0)) (@nil a0)) /\ (forall y0 : a0, forall y1 : list a0, ((fun y2 : list a0 => (~ (@EX a0 x0 y2)) = (@List.Forall a0 (fun y3 : a0 => ~ (x0 y3)) y2)) y1) -> (fun y2 : list a0 => (~ (@EX a0 x0 y2)) = (@List.Forall a0 (fun y3 : a0 => ~ (x0 y3)) y2)) (@cons a0 y0 y1))).
Definition term33 (a0 : Type') (x0 : a0 -> Prop) := (((~ (@EX a0 x0 (@nil a0))) = (@List.Forall a0 (fun y0 : a0 => ~ (x0 y0)) (@nil a0))) /\ (forall y0 : a0, forall y1 : list a0, ((~ (@EX a0 x0 y1)) = (@List.Forall a0 (fun y2 : a0 => ~ (x0 y2)) y1)) -> (~ (@EX a0 x0 (@cons a0 y0 y1))) = (@List.Forall a0 (fun y2 : a0 => ~ (x0 y2)) (@cons a0 y0 y1)))) -> forall y0 : list a0, (~ (@EX a0 x0 y0)) = (@List.Forall a0 (fun y1 : a0 => ~ (x0 y1)) y0).
Definition term2 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : list a0 => (~ (@EX a0 x0 y0)) = (@List.Forall a0 (fun y1 : a0 => ~ (x0 y1)) y0).
Definition term57 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (x0 x1).
Definition term1 (a0 : Type') (x0 : a0 -> Prop) := (((fun y0 : list a0 => (~ (@EX a0 x0 y0)) = (@List.Forall a0 (fun y1 : a0 => ~ (x0 y1)) y0)) (@nil a0)) /\ (forall y0 : a0, forall y1 : list a0, ((fun y2 : list a0 => (~ (@EX a0 x0 y2)) = (@List.Forall a0 (fun y3 : a0 => ~ (x0 y3)) y2)) y1) -> (fun y2 : list a0 => (~ (@EX a0 x0 y2)) = (@List.Forall a0 (fun y3 : a0 => ~ (x0 y3)) y2)) (@cons a0 y0 y1))) -> forall y0 : list a0, (fun y1 : list a0 => (~ (@EX a0 x0 y1)) = (@List.Forall a0 (fun y2 : a0 => ~ (x0 y2)) y1)) y0.
Definition term0 (a0 : Type') (x0 : type1143 a0) := ((x0 (@nil a0)) /\ (forall y0 : a0, forall y1 : list a0, (x0 y1) -> x0 (@cons a0 y0 y1))) -> forall y0 : list a0, x0 y0.
Definition term17 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : list a0) := ((~ (@EX a0 x0 x2)) = (@List.Forall a0 (fun y0 : a0 => ~ (x0 y0)) x2)) -> (~ (@EX a0 x0 (@cons a0 x1 x2))) = (@List.Forall a0 (fun y0 : a0 => ~ (x0 y0)) (@cons a0 x1 x2)).
Definition term45 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : list a0) := (~ (x1 x0)) /\ (~ (@EX a0 x1 x2)).
Definition term41 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : list a0) := (x1 x0) \/ (@EX a0 x1 x2).
Definition term18 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := fun y0 : list a0 => ((fun y1 : list a0 => (~ (@EX a0 x0 y1)) = (@List.Forall a0 (fun y2 : a0 => ~ (x0 y2)) y1)) y0) -> (fun y1 : list a0 => (~ (@EX a0 x0 y1)) = (@List.Forall a0 (fun y2 : a0 => ~ (x0 y2)) y1)) (@cons a0 x1 y0).
Definition term30 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : list a0 => (fun y1 : list a0 => (~ (@EX a0 x0 y1)) = (@List.Forall a0 (fun y2 : a0 => ~ (x0 y2)) y1)) y0.
Definition term16 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : list a0) := ((fun y0 : list a0 => (~ (@EX a0 x0 y0)) = (@List.Forall a0 (fun y1 : a0 => ~ (x0 y1)) y0)) x2) -> (fun y0 : list a0 => (~ (@EX a0 x0 y0)) = (@List.Forall a0 (fun y1 : a0 => ~ (x0 y1)) y0)) (@cons a0 x1 x2).
Definition term38 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => ((~ (x0 /\ y0)) = ((~ x0) \/ (~ y0))) /\ ((~ (x0 \/ y0)) = ((~ x0) /\ (~ y0)))) x1.
Definition term39 (x0 : Prop) (x1 : Prop) := ((~ (x0 /\ x1)) = ((~ x0) \/ (~ x1))) /\ ((~ (x0 \/ x1)) = ((~ x0) /\ (~ x1))).
Definition term22 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => forall y1 : list a0, ((fun y2 : list a0 => (~ (@EX a0 x0 y2)) = (@List.Forall a0 (fun y3 : a0 => ~ (x0 y3)) y2)) y1) -> (fun y2 : list a0 => (~ (@EX a0 x0 y2)) = (@List.Forall a0 (fun y3 : a0 => ~ (x0 y3)) y2)) (@cons a0 y0 y1).
Definition term52 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : list a0) := ((fun y0 : a0 => ~ (x1 y0)) x0) /\ (@List.Forall a0 (fun y0 : a0 => ~ (x1 y0)) x2).
Definition term44 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term42 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : list a0) := ~ ((x1 x0) \/ (@EX a0 x1 x2)).
Definition term19 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := fun y0 : list a0 => ((~ (@EX a0 x0 y0)) = (@List.Forall a0 (fun y1 : a0 => ~ (x0 y1)) y0)) -> (~ (@EX a0 x0 (@cons a0 x1 y0))) = (@List.Forall a0 (fun y1 : a0 => ~ (x0 y1)) (@cons a0 x1 y0)).
Definition term51 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : list a0) := (x1 x0) /\ (@List.Forall a0 x1 x2).
Definition term36 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((~ (y0 /\ y1)) = ((~ y0) \/ (~ y1))) /\ ((~ (y0 \/ y1)) = ((~ y0) /\ (~ y1)))) x0.
Definition term37 (x0 : Prop) := forall y0 : Prop, ((~ (x0 /\ y0)) = ((~ x0) \/ (~ y0))) /\ ((~ (x0 \/ y0)) = ((~ x0) /\ (~ y0))).
Definition term49 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : list a0) := @eq Prop ((~ (x1 x0)) /\ (@List.Forall a0 (fun y0 : a0 => ~ (x1 y0)) x2)).
Definition term35 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => ~ (x0 y0).
Definition term29 (a0 : Type') (x0 : a0 -> Prop) := imp (((~ (@EX a0 x0 (@nil a0))) = (@List.Forall a0 (fun y0 : a0 => ~ (x0 y0)) (@nil a0))) /\ (forall y0 : a0, forall y1 : list a0, ((~ (@EX a0 x0 y1)) = (@List.Forall a0 (fun y2 : a0 => ~ (x0 y2)) y1)) -> (~ (@EX a0 x0 (@cons a0 y0 y1))) = (@List.Forall a0 (fun y2 : a0 => ~ (x0 y2)) (@cons a0 y0 y1)))).
Definition term10 (a0 : Type') (x0 : a0 -> Prop) (x1 : list a0) := @List.Forall a0 (fun y0 : a0 => ~ (x0 y0)) x1.
Definition term40 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : list a0) := @EX a0 x0 (@cons a0 x1 x2).
Definition term12 (a0 : Type') (x0 : a0 -> Prop) (x1 : list a0) := imp ((~ (@EX a0 x0 x1)) = (@List.Forall a0 (fun y0 : a0 => ~ (x0 y0)) x1)).
Definition term53 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term6 (a0 : Type') (x0 : a0 -> Prop) := and ((fun y0 : list a0 => (~ (@EX a0 x0 y0)) = (@List.Forall a0 (fun y1 : a0 => ~ (x0 y1)) y0)) (@nil a0)).
Definition term9 (a0 : Type') (x0 : a0 -> Prop) (x1 : list a0) := ~ (@EX a0 x0 x1).
Definition term20 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := forall y0 : list a0, ((fun y1 : list a0 => (~ (@EX a0 x0 y1)) = (@List.Forall a0 (fun y2 : a0 => ~ (x0 y2)) y1)) y0) -> (fun y1 : list a0 => (~ (@EX a0 x0 y1)) = (@List.Forall a0 (fun y2 : a0 => ~ (x0 y2)) y1)) (@cons a0 x1 y0).
Definition term43 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term54 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term60 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @eq Prop ((fun y0 : a0 => ~ (x0 y0)) x1).
Definition term61 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := and ((fun y0 : a0 => ~ (x0 y0)) x1).
Definition term21 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := forall y0 : list a0, ((~ (@EX a0 x0 y0)) = (@List.Forall a0 (fun y1 : a0 => ~ (x0 y1)) y0)) -> (~ (@EX a0 x0 (@cons a0 x1 y0))) = (@List.Forall a0 (fun y1 : a0 => ~ (x0 y1)) (@cons a0 x1 y0)).
Definition term58 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => (fun y1 : a0 => ~ (x0 y1)) y0.
Definition term14 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : list a0) := ~ (@EX a0 x0 (@cons a0 x1 x2)).
Definition term62 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : list a0, (~ (@EX a0 y0 y1)) = (@List.Forall a0 (fun y2 : a0 => ~ (y0 y2)) y1).
Definition term48 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : list a0) := @eq Prop (~ (@EX a0 x0 (@cons a0 x1 x2))).
Definition term27 (a0 : Type') (x0 : a0 -> Prop) := ((~ (@EX a0 x0 (@nil a0))) = (@List.Forall a0 (fun y0 : a0 => ~ (x0 y0)) (@nil a0))) /\ (forall y0 : a0, forall y1 : list a0, ((~ (@EX a0 x0 y1)) = (@List.Forall a0 (fun y2 : a0 => ~ (x0 y2)) y1)) -> (~ (@EX a0 x0 (@cons a0 y0 y1))) = (@List.Forall a0 (fun y2 : a0 => ~ (x0 y2)) (@cons a0 y0 y1))).
Definition term32 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : list a0, (~ (@EX a0 x0 y0)) = (@List.Forall a0 (fun y1 : a0 => ~ (x0 y1)) y0).
Definition term47 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : list a0) := (~ (x1 x0)) /\ (@List.Forall a0 (fun y0 : a0 => ~ (x1 y0)) x2).
Definition term55 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => (fun y1 : a0 => ~ (x0 y1)) y0) x1.
Definition term4 (a0 : Type') (x0 : a0 -> Prop) := ~ (@EX a0 x0 (@nil a0)).
Definition term15 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : list a0) := @List.Forall a0 (fun y0 : a0 => ~ (x0 y0)) (@cons a0 x1 x2).
Definition term3 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : list a0 => (~ (@EX a0 x0 y0)) = (@List.Forall a0 (fun y1 : a0 => ~ (x0 y1)) y0)) (@nil a0).
Definition term13 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : list a0) := (fun y0 : list a0 => (~ (@EX a0 x0 y0)) = (@List.Forall a0 (fun y1 : a0 => ~ (x0 y1)) y0)) (@cons a0 x1 x2).
Definition term31 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : list a0, (fun y1 : list a0 => (~ (@EX a0 x0 y1)) = (@List.Forall a0 (fun y2 : a0 => ~ (x0 y2)) y1)) y0.
Definition term25 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, forall y1 : list a0, ((~ (@EX a0 x0 y1)) = (@List.Forall a0 (fun y2 : a0 => ~ (x0 y2)) y1)) -> (~ (@EX a0 x0 (@cons a0 y0 y1))) = (@List.Forall a0 (fun y2 : a0 => ~ (x0 y2)) (@cons a0 y0 y1)).
Definition term24 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, forall y1 : list a0, ((fun y2 : list a0 => (~ (@EX a0 x0 y2)) = (@List.Forall a0 (fun y3 : a0 => ~ (x0 y3)) y2)) y1) -> (fun y2 : list a0 => (~ (@EX a0 x0 y2)) = (@List.Forall a0 (fun y3 : a0 => ~ (x0 y3)) y2)) (@cons a0 y0 y1).
Definition term46 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := and (~ (x0 x1)).
Definition term50 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : list a0) := @List.Forall a0 x0 (@cons a0 x1 x2).
Definition term7 (a0 : Type') (x0 : a0 -> Prop) := and ((~ (@EX a0 x0 (@nil a0))) = (@List.Forall a0 (fun y0 : a0 => ~ (x0 y0)) (@nil a0))).
Definition term26 (a0 : Type') (x0 : a0 -> Prop) := ((fun y0 : list a0 => (~ (@EX a0 x0 y0)) = (@List.Forall a0 (fun y1 : a0 => ~ (x0 y1)) y0)) (@nil a0)) /\ (forall y0 : a0, forall y1 : list a0, ((fun y2 : list a0 => (~ (@EX a0 x0 y2)) = (@List.Forall a0 (fun y3 : a0 => ~ (x0 y3)) y2)) y1) -> (fun y2 : list a0 => (~ (@EX a0 x0 y2)) = (@List.Forall a0 (fun y3 : a0 => ~ (x0 y3)) y2)) (@cons a0 y0 y1)).
Definition term5 (a0 : Type') (x0 : a0 -> Prop) := @List.Forall a0 (fun y0 : a0 => ~ (x0 y0)) (@nil a0).
