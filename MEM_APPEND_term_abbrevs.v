Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term70 (a0 : Type') := forall y0 : a0, forall y1 : list a0, forall y2 : list a0, (@List.In a0 y0 (@List.app a0 y1 y2)) = ((@List.In a0 y0 y1) \/ (@List.In a0 y0 y2)).
Definition term45 (a0 : Type') := forall y0 : a0, forall y1 : list a0, forall y2 : list a0, (@List.app a0 (@cons a0 y0 y1) y2) = (@cons a0 y0 (@List.app a0 y1 y2)).
Definition term24 (a0 : Type') (x0 : a0) := (forall y0 : list a0, (@List.In a0 x0 (@List.app a0 (@nil a0) y0)) = ((@List.In a0 x0 (@nil a0)) \/ (@List.In a0 x0 y0))) /\ (forall y0 : a0, forall y1 : list a0, (forall y2 : list a0, (@List.In a0 x0 (@List.app a0 y1 y2)) = ((@List.In a0 x0 y1) \/ (@List.In a0 x0 y2))) -> forall y2 : list a0, (@List.In a0 x0 (@List.app a0 (@cons a0 y0 y1) y2)) = ((@List.In a0 x0 (@cons a0 y0 y1)) \/ (@List.In a0 x0 y2))).
Definition term51 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : list a0) := @List.app a0 (@cons a0 x0 x1) x2.
Definition term63 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) (x3 : list a0) := @eq Prop (@List.In a0 x0 (@List.app a0 (@cons a0 x1 x2) x3)).
Definition term53 (a0 : Type') (x0 : list a0) (x1 : a0) (x2 : list a0) := (fun y0 : list a0 => (@List.In a0 x1 (@List.app a0 x0 y0)) = ((@List.In a0 x1 x0) \/ (@List.In a0 x1 y0))) x2.
Definition term49 (a0 : Type') (x0 : a0) (x1 : list a0) := forall y0 : list a0, (@List.app a0 (@cons a0 x0 x1) y0) = (@cons a0 x0 (@List.app a0 x1 y0)).
Definition term25 (a0 : Type') (x0 : a0) := imp (((fun y0 : list a0 => forall y1 : list a0, (@List.In a0 x0 (@List.app a0 y0 y1)) = ((@List.In a0 x0 y0) \/ (@List.In a0 x0 y1))) (@nil a0)) /\ (forall y0 : a0, forall y1 : list a0, ((fun y2 : list a0 => forall y3 : list a0, (@List.In a0 x0 (@List.app a0 y2 y3)) = ((@List.In a0 x0 y2) \/ (@List.In a0 x0 y3))) y1) -> (fun y2 : list a0 => forall y3 : list a0, (@List.In a0 x0 (@List.app a0 y2 y3)) = ((@List.In a0 x0 y2) \/ (@List.In a0 x0 y3))) (@cons a0 y0 y1))).
Definition term43 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term3 (a0 : Type') (x0 : a0) := (fun y0 : list a0 => forall y1 : list a0, (@List.In a0 x0 (@List.app a0 y0 y1)) = ((@List.In a0 x0 y0) \/ (@List.In a0 x0 y1))) (@nil a0).
Definition term5 (a0 : Type') (x0 : a0) := and ((fun y0 : list a0 => forall y1 : list a0, (@List.In a0 x0 (@List.app a0 y0 y1)) = ((@List.In a0 x0 y0) \/ (@List.In a0 x0 y1))) (@nil a0)).
Definition term1 (a0 : Type') (x0 : a0) := (((fun y0 : list a0 => forall y1 : list a0, (@List.In a0 x0 (@List.app a0 y0 y1)) = ((@List.In a0 x0 y0) \/ (@List.In a0 x0 y1))) (@nil a0)) /\ (forall y0 : a0, forall y1 : list a0, ((fun y2 : list a0 => forall y3 : list a0, (@List.In a0 x0 (@List.app a0 y2 y3)) = ((@List.In a0 x0 y2) \/ (@List.In a0 x0 y3))) y1) -> (fun y2 : list a0 => forall y3 : list a0, (@List.In a0 x0 (@List.app a0 y2 y3)) = ((@List.In a0 x0 y2) \/ (@List.In a0 x0 y3))) (@cons a0 y0 y1))) -> forall y0 : list a0, (fun y1 : list a0 => forall y2 : list a0, (@List.In a0 x0 (@List.app a0 y1 y2)) = ((@List.In a0 x0 y1) \/ (@List.In a0 x0 y2))) y0.
Definition term18 (a0 : Type') (x0 : a0) (x1 : a0) := forall y0 : list a0, (forall y1 : list a0, (@List.In a0 x1 (@List.app a0 y0 y1)) = ((@List.In a0 x1 y0) \/ (@List.In a0 x1 y1))) -> forall y1 : list a0, (@List.In a0 x1 (@List.app a0 (@cons a0 x0 y0) y1)) = ((@List.In a0 x1 (@cons a0 x0 y0)) \/ (@List.In a0 x1 y1)).
Definition term0 (a0 : Type') (x0 : type1143 a0) := ((x0 (@nil a0)) /\ (forall y0 : a0, forall y1 : list a0, (x0 y1) -> x0 (@cons a0 y0 y1))) -> forall y0 : list a0, x0 y0.
Definition term36 (a0 : Type') (x0 : a0) (x1 : list a0) := (@List.In a0 x0 (@nil a0)) \/ (@List.In a0 x0 x1).
Definition term47 (a0 : Type') (x0 : a0) := forall y0 : list a0, forall y1 : list a0, (@List.app a0 (@cons a0 x0 y0) y1) = (@cons a0 x0 (@List.app a0 y0 y1)).
Definition term29 (a0 : Type') (x0 : a0) := forall y0 : list a0, forall y1 : list a0, (@List.In a0 x0 (@List.app a0 y0 y1)) = ((@List.In a0 x0 y0) \/ (@List.In a0 x0 y1)).
Definition term39 (a0 : Type') (x0 : a0) (x1 : list a0) := (@List.In a0 x0 x1) \/ False.
Definition term64 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0) (x3 : list a0) := @eq Prop ((x2 = x0) \/ ((@List.In a0 x2 x1) \/ (@List.In a0 x2 x3))).
Definition term19 (a0 : Type') (x0 : a0) := fun y0 : a0 => forall y1 : list a0, ((fun y2 : list a0 => forall y3 : list a0, (@List.In a0 x0 (@List.app a0 y2 y3)) = ((@List.In a0 x0 y2) \/ (@List.In a0 x0 y3))) y1) -> (fun y2 : list a0 => forall y3 : list a0, (@List.In a0 x0 (@List.app a0 y2 y3)) = ((@List.In a0 x0 y2) \/ (@List.In a0 x0 y3))) (@cons a0 y0 y1).
Definition term66 (a0 : Type') (x0 : list a0) (x1 : a0) (x2 : a0) (x3 : list a0) := (@List.In a0 x1 x0) \/ (@List.In a0 x1 (@cons a0 x2 x3)).
Definition term46 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : list a0, forall y2 : list a0, (@List.app a0 (@cons a0 y0 y1) y2) = (@cons a0 y0 (@List.app a0 y1 y2))) x0.
Definition term68 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term65 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0) (x3 : list a0) := (@List.In a0 x2 (@cons a0 x0 x1)) \/ (@List.In a0 x2 x3).
Definition term42 (a0 : Type') := forall y0 : list a0, True.
Definition term16 (a0 : Type') (x0 : a0) (x1 : a0) := fun y0 : list a0 => (forall y1 : list a0, (@List.In a0 x1 (@List.app a0 y0 y1)) = ((@List.In a0 x1 y0) \/ (@List.In a0 x1 y1))) -> forall y1 : list a0, (@List.In a0 x1 (@List.app a0 (@cons a0 x0 y0) y1)) = ((@List.In a0 x1 (@cons a0 x0 y0)) \/ (@List.In a0 x1 y1)).
Definition term28 (a0 : Type') (x0 : a0) := forall y0 : list a0, (fun y1 : list a0 => forall y2 : list a0, (@List.In a0 x0 (@List.app a0 y1 y2)) = ((@List.In a0 x0 y1) \/ (@List.In a0 x0 y2))) y0.
Definition term32 (a0 : Type') (x0 : list a0) := (fun y0 : list a0 => (@List.app a0 (@nil a0) y0) = y0) x0.
Definition term62 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0) (x3 : list a0) := (x2 = x0) \/ ((@List.In a0 x2 x1) \/ (@List.In a0 x2 x3)).
Definition term30 (a0 : Type') (x0 : a0) := ((forall y0 : list a0, (@List.In a0 x0 (@List.app a0 (@nil a0) y0)) = ((@List.In a0 x0 (@nil a0)) \/ (@List.In a0 x0 y0))) /\ (forall y0 : a0, forall y1 : list a0, (forall y2 : list a0, (@List.In a0 x0 (@List.app a0 y1 y2)) = ((@List.In a0 x0 y1) \/ (@List.In a0 x0 y2))) -> forall y2 : list a0, (@List.In a0 x0 (@List.app a0 (@cons a0 y0 y1) y2)) = ((@List.In a0 x0 (@cons a0 y0 y1)) \/ (@List.In a0 x0 y2)))) -> forall y0 : list a0, forall y1 : list a0, (@List.In a0 x0 (@List.app a0 y0 y1)) = ((@List.In a0 x0 y0) \/ (@List.In a0 x0 y1)).
Definition term37 (a0 : Type') (x0 : list a0) (x1 : a0) := (@List.In a0 x1 x0) \/ (@List.In a0 x1 (@nil a0)).
Definition term9 (a0 : Type') (x0 : a0) (x1 : list a0) := imp ((fun y0 : list a0 => forall y1 : list a0, (@List.In a0 x0 (@List.app a0 y0 y1)) = ((@List.In a0 x0 y0) \/ (@List.In a0 x0 y1))) x1).
Definition term35 (a0 : Type') (x0 : a0) (x1 : list a0) := @eq Prop (@List.In a0 x0 x1).
Definition term26 (a0 : Type') (x0 : a0) := imp ((forall y0 : list a0, (@List.In a0 x0 (@List.app a0 (@nil a0) y0)) = ((@List.In a0 x0 (@nil a0)) \/ (@List.In a0 x0 y0))) /\ (forall y0 : a0, forall y1 : list a0, (forall y2 : list a0, (@List.In a0 x0 (@List.app a0 y1 y2)) = ((@List.In a0 x0 y1) \/ (@List.In a0 x0 y2))) -> forall y2 : list a0, (@List.In a0 x0 (@List.app a0 (@cons a0 y0 y1) y2)) = ((@List.In a0 x0 (@cons a0 y0 y1)) \/ (@List.In a0 x0 y2)))).
Definition term17 (a0 : Type') (x0 : a0) (x1 : a0) := forall y0 : list a0, ((fun y1 : list a0 => forall y2 : list a0, (@List.In a0 x0 (@List.app a0 y1 y2)) = ((@List.In a0 x0 y1) \/ (@List.In a0 x0 y2))) y0) -> (fun y1 : list a0 => forall y2 : list a0, (@List.In a0 x0 (@List.app a0 y1 y2)) = ((@List.In a0 x0 y1) \/ (@List.In a0 x0 y2))) (@cons a0 x1 y0).
Definition term27 (a0 : Type') (x0 : a0) := fun y0 : list a0 => (fun y1 : list a0 => forall y2 : list a0, (@List.In a0 x0 (@List.app a0 y1 y2)) = ((@List.In a0 x0 y1) \/ (@List.In a0 x0 y2))) y0.
Definition term31 (a0 : Type') := forall y0 : list a0, (@List.app a0 (@nil a0) y0) = y0.
Definition term11 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) := (fun y0 : list a0 => forall y1 : list a0, (@List.In a0 x0 (@List.app a0 y0 y1)) = ((@List.In a0 x0 y0) \/ (@List.In a0 x0 y1))) (@cons a0 x1 x2).
Definition term2 (a0 : Type') (x0 : a0) := fun y0 : list a0 => forall y1 : list a0, (@List.In a0 x0 (@List.app a0 y0 y1)) = ((@List.In a0 x0 y0) \/ (@List.In a0 x0 y1)).
Definition term10 (a0 : Type') (x0 : list a0) (x1 : a0) := imp (forall y0 : list a0, (@List.In a0 x1 (@List.app a0 x0 y0)) = ((@List.In a0 x1 x0) \/ (@List.In a0 x1 y0))).
Definition term20 (a0 : Type') (x0 : a0) := fun y0 : a0 => forall y1 : list a0, (forall y2 : list a0, (@List.In a0 x0 (@List.app a0 y1 y2)) = ((@List.In a0 x0 y1) \/ (@List.In a0 x0 y2))) -> forall y2 : list a0, (@List.In a0 x0 (@List.app a0 (@cons a0 y0 y1) y2)) = ((@List.In a0 x0 (@cons a0 y0 y1)) \/ (@List.In a0 x0 y2)).
Definition term52 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : list a0) := @cons a0 x0 (@List.app a0 x1 x2).
Definition term59 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) := (x1 = x0) \/ (@List.In a0 x1 x2).
Definition term55 (a0 : Type') (x0 : list a0) (x1 : a0) (x2 : list a0) := (@List.In a0 x1 x0) \/ (@List.In a0 x1 x2).
Definition term69 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0) := fun y0 : list a0 => (@List.In a0 x2 (@List.app a0 (@cons a0 x0 x1) y0)) = ((@List.In a0 x2 (@cons a0 x0 x1)) \/ (@List.In a0 x2 y0)).
Definition term48 (a0 : Type') (x0 : a0) (x1 : list a0) := (fun y0 : list a0 => forall y1 : list a0, (@List.app a0 (@cons a0 x0 y0) y1) = (@cons a0 x0 (@List.app a0 y0 y1))) x1.
Definition term7 (a0 : Type') (x0 : a0) (x1 : list a0) := (fun y0 : list a0 => forall y1 : list a0, (@List.In a0 x0 (@List.app a0 y0 y1)) = ((@List.In a0 x0 y0) \/ (@List.In a0 x0 y1))) x1.
Definition term57 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) (x3 : list a0) := @List.In a0 x0 (@cons a0 x1 (@List.app a0 x2 x3)).
Definition term23 (a0 : Type') (x0 : a0) := ((fun y0 : list a0 => forall y1 : list a0, (@List.In a0 x0 (@List.app a0 y0 y1)) = ((@List.In a0 x0 y0) \/ (@List.In a0 x0 y1))) (@nil a0)) /\ (forall y0 : a0, forall y1 : list a0, ((fun y2 : list a0 => forall y3 : list a0, (@List.In a0 x0 (@List.app a0 y2 y3)) = ((@List.In a0 x0 y2) \/ (@List.In a0 x0 y3))) y1) -> (fun y2 : list a0 => forall y3 : list a0, (@List.In a0 x0 (@List.app a0 y2 y3)) = ((@List.In a0 x0 y2) \/ (@List.In a0 x0 y3))) (@cons a0 y0 y1)).
Definition term34 (a0 : Type') (x0 : a0) (x1 : list a0) := @eq Prop (@List.In a0 x0 (@List.app a0 (@nil a0) x1)).
Definition term67 (a0 : Type') (x0 : list a0) (x1 : a0) (x2 : a0) (x3 : list a0) := (@List.In a0 x2 x0) \/ ((x2 = x1) \/ (@List.In a0 x2 x3)).
Definition term54 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : list a0) := @List.In a0 x0 (@List.app a0 x1 x2).
Definition term61 (a0 : Type') (x0 : a0) (x1 : a0) := or (x0 = x1).
Definition term58 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) := @List.In a0 x0 (@cons a0 x1 x2).
Definition term12 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0) := forall y0 : list a0, (@List.In a0 x2 (@List.app a0 (@cons a0 x0 x1) y0)) = ((@List.In a0 x2 (@cons a0 x0 x1)) \/ (@List.In a0 x2 y0)).
Definition term8 (a0 : Type') (x0 : list a0) (x1 : a0) := forall y0 : list a0, (@List.In a0 x1 (@List.app a0 x0 y0)) = ((@List.In a0 x1 x0) \/ (@List.In a0 x1 y0)).
Definition term4 (a0 : Type') (x0 : a0) := forall y0 : list a0, (@List.In a0 x0 (@List.app a0 (@nil a0) y0)) = ((@List.In a0 x0 (@nil a0)) \/ (@List.In a0 x0 y0)).
Definition term13 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) := ((fun y0 : list a0 => forall y1 : list a0, (@List.In a0 x0 (@List.app a0 y0 y1)) = ((@List.In a0 x0 y0) \/ (@List.In a0 x0 y1))) x2) -> (fun y0 : list a0 => forall y1 : list a0, (@List.In a0 x0 (@List.app a0 y0 y1)) = ((@List.In a0 x0 y0) \/ (@List.In a0 x0 y1))) (@cons a0 x1 x2).
Definition term56 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) (x3 : list a0) := @List.In a0 x0 (@List.app a0 (@cons a0 x1 x2) x3).
Definition term41 (a0 : Type') := fun y0 : list a0 => True.
Definition term33 (a0 : Type') (x0 : a0) (x1 : list a0) := @List.In a0 x0 (@List.app a0 (@nil a0) x1).
Definition term44 (a0 : Type') (x0 : Prop) := forall y0 : list a0, x0.
Definition term50 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : list a0) := (fun y0 : list a0 => (@List.app a0 (@cons a0 x0 x1) y0) = (@cons a0 x0 (@List.app a0 x1 y0))) x2.
Definition term60 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) (x3 : list a0) := (x1 = x0) \/ (@List.In a0 x1 (@List.app a0 x2 x3)).
Definition term22 (a0 : Type') (x0 : a0) := forall y0 : a0, forall y1 : list a0, (forall y2 : list a0, (@List.In a0 x0 (@List.app a0 y1 y2)) = ((@List.In a0 x0 y1) \/ (@List.In a0 x0 y2))) -> forall y2 : list a0, (@List.In a0 x0 (@List.app a0 (@cons a0 y0 y1) y2)) = ((@List.In a0 x0 (@cons a0 y0 y1)) \/ (@List.In a0 x0 y2)).
Definition term21 (a0 : Type') (x0 : a0) := forall y0 : a0, forall y1 : list a0, ((fun y2 : list a0 => forall y3 : list a0, (@List.In a0 x0 (@List.app a0 y2 y3)) = ((@List.In a0 x0 y2) \/ (@List.In a0 x0 y3))) y1) -> (fun y2 : list a0 => forall y3 : list a0, (@List.In a0 x0 (@List.app a0 y2 y3)) = ((@List.In a0 x0 y2) \/ (@List.In a0 x0 y3))) (@cons a0 y0 y1).
Definition term6 (a0 : Type') (x0 : a0) := and (forall y0 : list a0, (@List.In a0 x0 (@List.app a0 (@nil a0) y0)) = ((@List.In a0 x0 (@nil a0)) \/ (@List.In a0 x0 y0))).
Definition term40 (a0 : Type') (x0 : a0) := fun y0 : list a0 => (@List.In a0 x0 (@List.app a0 (@nil a0) y0)) = ((@List.In a0 x0 (@nil a0)) \/ (@List.In a0 x0 y0)).
Definition term14 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0) := (forall y0 : list a0, (@List.In a0 x2 (@List.app a0 x1 y0)) = ((@List.In a0 x2 x1) \/ (@List.In a0 x2 y0))) -> forall y0 : list a0, (@List.In a0 x2 (@List.app a0 (@cons a0 x0 x1) y0)) = ((@List.In a0 x2 (@cons a0 x0 x1)) \/ (@List.In a0 x2 y0)).
Definition term38 (a0 : Type') (x0 : a0) (x1 : list a0) := or (@List.In a0 x0 x1).
Definition term15 (a0 : Type') (x0 : a0) (x1 : a0) := fun y0 : list a0 => ((fun y1 : list a0 => forall y2 : list a0, (@List.In a0 x0 (@List.app a0 y1 y2)) = ((@List.In a0 x0 y1) \/ (@List.In a0 x0 y2))) y0) -> (fun y1 : list a0 => forall y2 : list a0, (@List.In a0 x0 (@List.app a0 y1 y2)) = ((@List.In a0 x0 y1) \/ (@List.In a0 x0 y2))) (@cons a0 x1 y0).