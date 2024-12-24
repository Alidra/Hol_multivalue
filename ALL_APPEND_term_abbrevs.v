Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term61 (a0 : Type') := forall y0 : a0, forall y1 : list a0, forall y2 : list a0, (@List.app a0 (@cons a0 y0 y1) y2) = (@cons a0 y0 (@List.app a0 y1 y2)).
Definition term50 (a0 : Type') (x0 : a0 -> Prop) := and (@List.Forall a0 x0 (@nil a0)).
Definition term80 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0 -> Prop) (x3 : list a0) := @eq Prop ((x2 x0) /\ ((@List.Forall a0 x2 x1) /\ (@List.Forall a0 x2 x3))).
Definition term38 (a0 : Type') (x0 : a0 -> Prop) := (forall y0 : list a0, (@List.Forall a0 x0 (@List.app a0 (@nil a0) y0)) = ((@List.Forall a0 x0 (@nil a0)) /\ (@List.Forall a0 x0 y0))) /\ (forall y0 : a0, forall y1 : list a0, (forall y2 : list a0, (@List.Forall a0 x0 (@List.app a0 y1 y2)) = ((@List.Forall a0 x0 y1) /\ (@List.Forall a0 x0 y2))) -> forall y2 : list a0, (@List.Forall a0 x0 (@List.app a0 (@cons a0 y0 y1) y2)) = ((@List.Forall a0 x0 (@cons a0 y0 y1)) /\ (@List.Forall a0 x0 y2))).
Definition term79 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : list a0) (x3 : list a0) := @eq Prop (@List.Forall a0 x0 (@List.app a0 (@cons a0 x1 x2) x3)).
Definition term71 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : list a0) := (@List.Forall a0 x1 x0) /\ (@List.Forall a0 x1 x2).
Definition term67 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : list a0) := @List.app a0 (@cons a0 x0 x1) x2.
Definition term49 (a0 : Type') (x0 : a0 -> Prop) (x1 : list a0) := @eq Prop (@List.Forall a0 x0 x1).
Definition term69 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : list a0) := (fun y0 : list a0 => (@List.Forall a0 x1 (@List.app a0 x0 y0)) = ((@List.Forall a0 x1 x0) /\ (@List.Forall a0 x1 y0))) x2.
Definition term65 (a0 : Type') (x0 : a0) (x1 : list a0) := forall y0 : list a0, (@List.app a0 (@cons a0 x0 x1) y0) = (@cons a0 x0 (@List.app a0 x1 y0)).
Definition term39 (a0 : Type') (x0 : a0 -> Prop) := imp (((fun y0 : list a0 => forall y1 : list a0, (@List.Forall a0 x0 (@List.app a0 y0 y1)) = ((@List.Forall a0 x0 y0) /\ (@List.Forall a0 x0 y1))) (@nil a0)) /\ (forall y0 : a0, forall y1 : list a0, ((fun y2 : list a0 => forall y3 : list a0, (@List.Forall a0 x0 (@List.app a0 y2 y3)) = ((@List.Forall a0 x0 y2) /\ (@List.Forall a0 x0 y3))) y1) -> (fun y2 : list a0 => forall y3 : list a0, (@List.Forall a0 x0 (@List.app a0 y2 y3)) = ((@List.Forall a0 x0 y2) /\ (@List.Forall a0 x0 y3))) (@cons a0 y0 y1))).
Definition term56 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term85 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0 -> Prop) := fun y0 : list a0 => (@List.Forall a0 x2 (@List.app a0 (@cons a0 x0 x1) y0)) = ((@List.Forall a0 x2 (@cons a0 x0 x1)) /\ (@List.Forall a0 x2 y0)).
Definition term4 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, (x0 /\ (x1 /\ y0)) = ((x0 /\ x1) /\ y0).
Definition term86 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : list a0, forall y2 : list a0, (@List.Forall a0 y0 (@List.app a0 y1 y2)) = ((@List.Forall a0 y0 y1) /\ (@List.Forall a0 y0 y2)).
Definition term6 (x0 : Prop) := fun y0 : Prop => forall y1 : Prop, (x0 /\ (y0 /\ y1)) = ((x0 /\ y0) /\ y1).
Definition term17 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : list a0 => forall y1 : list a0, (@List.Forall a0 x0 (@List.app a0 y0 y1)) = ((@List.Forall a0 x0 y0) /\ (@List.Forall a0 x0 y1))) (@nil a0).
Definition term19 (a0 : Type') (x0 : a0 -> Prop) := and ((fun y0 : list a0 => forall y1 : list a0, (@List.Forall a0 x0 (@List.app a0 y0 y1)) = ((@List.Forall a0 x0 y0) /\ (@List.Forall a0 x0 y1))) (@nil a0)).
Definition term15 (a0 : Type') (x0 : a0 -> Prop) := (((fun y0 : list a0 => forall y1 : list a0, (@List.Forall a0 x0 (@List.app a0 y0 y1)) = ((@List.Forall a0 x0 y0) /\ (@List.Forall a0 x0 y1))) (@nil a0)) /\ (forall y0 : a0, forall y1 : list a0, ((fun y2 : list a0 => forall y3 : list a0, (@List.Forall a0 x0 (@List.app a0 y2 y3)) = ((@List.Forall a0 x0 y2) /\ (@List.Forall a0 x0 y3))) y1) -> (fun y2 : list a0 => forall y3 : list a0, (@List.Forall a0 x0 (@List.app a0 y2 y3)) = ((@List.Forall a0 x0 y2) /\ (@List.Forall a0 x0 y3))) (@cons a0 y0 y1))) -> forall y0 : list a0, (fun y1 : list a0 => forall y2 : list a0, (@List.Forall a0 x0 (@List.app a0 y1 y2)) = ((@List.Forall a0 x0 y1) /\ (@List.Forall a0 x0 y2))) y0.
Definition term32 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := forall y0 : list a0, (forall y1 : list a0, (@List.Forall a0 x1 (@List.app a0 y0 y1)) = ((@List.Forall a0 x1 y0) /\ (@List.Forall a0 x1 y1))) -> forall y1 : list a0, (@List.Forall a0 x1 (@List.app a0 (@cons a0 x0 y0) y1)) = ((@List.Forall a0 x1 (@cons a0 x0 y0)) /\ (@List.Forall a0 x1 y1)).
Definition term14 (a0 : Type') (x0 : type1143 a0) := ((x0 (@nil a0)) /\ (forall y0 : a0, forall y1 : list a0, (x0 y1) -> x0 (@cons a0 y0 y1))) -> forall y0 : list a0, x0 y0.
Definition term63 (a0 : Type') (x0 : a0) := forall y0 : list a0, forall y1 : list a0, (@List.app a0 (@cons a0 x0 y0) y1) = (@cons a0 x0 (@List.app a0 y0 y1)).
Definition term43 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : list a0, forall y1 : list a0, (@List.Forall a0 x0 (@List.app a0 y0 y1)) = ((@List.Forall a0 x0 y0) /\ (@List.Forall a0 x0 y1)).
Definition term53 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : list a0 => (@List.Forall a0 x0 (@List.app a0 (@nil a0) y0)) = ((@List.Forall a0 x0 (@nil a0)) /\ (@List.Forall a0 x0 y0)).
Definition term33 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => forall y1 : list a0, ((fun y2 : list a0 => forall y3 : list a0, (@List.Forall a0 x0 (@List.app a0 y2 y3)) = ((@List.Forall a0 x0 y2) /\ (@List.Forall a0 x0 y3))) y1) -> (fun y2 : list a0 => forall y3 : list a0, (@List.Forall a0 x0 (@List.app a0 y2 y3)) = ((@List.Forall a0 x0 y2) /\ (@List.Forall a0 x0 y3))) (@cons a0 y0 y1).
Definition term83 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0 -> Prop) (x3 : list a0) := (@List.Forall a0 x2 (@cons a0 x0 x1)) /\ (@List.Forall a0 x2 x3).
Definition term11 := fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, ((y0 /\ y1) /\ y2) = (y0 /\ (y1 /\ y2)).
Definition term10 := fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, (y0 /\ (y1 /\ y2)) = ((y0 /\ y1) /\ y2).
Definition term75 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : list a0) := (x1 x0) /\ (@List.Forall a0 x1 x2).
Definition term62 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : list a0, forall y2 : list a0, (@List.app a0 (@cons a0 y0 y1) y2) = (@cons a0 y0 (@List.app a0 y1 y2))) x0.
Definition term51 (a0 : Type') (x0 : a0 -> Prop) (x1 : list a0) := (@List.Forall a0 x0 (@nil a0)) /\ (@List.Forall a0 x0 x1).
Definition term52 (a0 : Type') (x0 : a0 -> Prop) (x1 : list a0) := True /\ (@List.Forall a0 x0 x1).
Definition term76 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : list a0) (x3 : list a0) := (x1 x0) /\ (@List.Forall a0 x1 (@List.app a0 x2 x3)).
Definition term78 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0 -> Prop) (x3 : list a0) := (x2 x0) /\ ((@List.Forall a0 x2 x1) /\ (@List.Forall a0 x2 x3)).
Definition term7 (x0 : Prop) := fun y0 : Prop => forall y1 : Prop, ((x0 /\ y0) /\ y1) = (x0 /\ (y0 /\ y1)).
Definition term55 (a0 : Type') := forall y0 : list a0, True.
Definition term30 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := fun y0 : list a0 => (forall y1 : list a0, (@List.Forall a0 x1 (@List.app a0 y0 y1)) = ((@List.Forall a0 x1 y0) /\ (@List.Forall a0 x1 y1))) -> forall y1 : list a0, (@List.Forall a0 x1 (@List.app a0 (@cons a0 x0 y0) y1)) = ((@List.Forall a0 x1 (@cons a0 x0 y0)) /\ (@List.Forall a0 x1 y1)).
Definition term0 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 /\ (x1 /\ x2).
Definition term42 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : list a0, (fun y1 : list a0 => forall y2 : list a0, (@List.Forall a0 x0 (@List.app a0 y1 y2)) = ((@List.Forall a0 x0 y1) /\ (@List.Forall a0 x0 y2))) y0.
Definition term47 (a0 : Type') (x0 : a0 -> Prop) (x1 : list a0) := @List.Forall a0 x0 (@List.app a0 (@nil a0) x1).
Definition term46 (a0 : Type') (x0 : list a0) := (fun y0 : list a0 => (@List.app a0 (@nil a0) y0) = y0) x0.
Definition term60 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => ((x0 /\ x1) /\ y0) = (x0 /\ (x1 /\ y0))) x2.
Definition term5 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, ((x0 /\ x1) /\ y0) = (x0 /\ (x1 /\ y0)).
Definition term44 (a0 : Type') (x0 : a0 -> Prop) := ((forall y0 : list a0, (@List.Forall a0 x0 (@List.app a0 (@nil a0) y0)) = ((@List.Forall a0 x0 (@nil a0)) /\ (@List.Forall a0 x0 y0))) /\ (forall y0 : a0, forall y1 : list a0, (forall y2 : list a0, (@List.Forall a0 x0 (@List.app a0 y1 y2)) = ((@List.Forall a0 x0 y1) /\ (@List.Forall a0 x0 y2))) -> forall y2 : list a0, (@List.Forall a0 x0 (@List.app a0 (@cons a0 y0 y1) y2)) = ((@List.Forall a0 x0 (@cons a0 y0 y1)) /\ (@List.Forall a0 x0 y2)))) -> forall y0 : list a0, forall y1 : list a0, (@List.Forall a0 x0 (@List.app a0 y0 y1)) = ((@List.Forall a0 x0 y0) /\ (@List.Forall a0 x0 y1)).
Definition term48 (a0 : Type') (x0 : a0 -> Prop) (x1 : list a0) := @eq Prop (@List.Forall a0 x0 (@List.app a0 (@nil a0) x1)).
Definition term23 (a0 : Type') (x0 : a0 -> Prop) (x1 : list a0) := imp ((fun y0 : list a0 => forall y1 : list a0, (@List.Forall a0 x0 (@List.app a0 y0 y1)) = ((@List.Forall a0 x0 y0) /\ (@List.Forall a0 x0 y1))) x1).
Definition term72 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : list a0) (x3 : list a0) := @List.Forall a0 x0 (@List.app a0 (@cons a0 x1 x2) x3).
Definition term58 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, ((y0 /\ y1) /\ y2) = (y0 /\ (y1 /\ y2))) x0.
Definition term40 (a0 : Type') (x0 : a0 -> Prop) := imp ((forall y0 : list a0, (@List.Forall a0 x0 (@List.app a0 (@nil a0) y0)) = ((@List.Forall a0 x0 (@nil a0)) /\ (@List.Forall a0 x0 y0))) /\ (forall y0 : a0, forall y1 : list a0, (forall y2 : list a0, (@List.Forall a0 x0 (@List.app a0 y1 y2)) = ((@List.Forall a0 x0 y1) /\ (@List.Forall a0 x0 y2))) -> forall y2 : list a0, (@List.Forall a0 x0 (@List.app a0 (@cons a0 y0 y1) y2)) = ((@List.Forall a0 x0 (@cons a0 y0 y1)) /\ (@List.Forall a0 x0 y2)))).
Definition term31 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := forall y0 : list a0, ((fun y1 : list a0 => forall y2 : list a0, (@List.Forall a0 x0 (@List.app a0 y1 y2)) = ((@List.Forall a0 x0 y1) /\ (@List.Forall a0 x0 y2))) y0) -> (fun y1 : list a0 => forall y2 : list a0, (@List.Forall a0 x0 (@List.app a0 y1 y2)) = ((@List.Forall a0 x0 y1) /\ (@List.Forall a0 x0 y2))) (@cons a0 x1 y0).
Definition term41 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : list a0 => (fun y1 : list a0 => forall y2 : list a0, (@List.Forall a0 x0 (@List.app a0 y1 y2)) = ((@List.Forall a0 x0 y1) /\ (@List.Forall a0 x0 y2))) y0.
Definition term1 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 /\ x1) /\ x2.
Definition term77 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := and (x0 x1).
Definition term45 (a0 : Type') := forall y0 : list a0, (@List.app a0 (@nil a0) y0) = y0.
Definition term25 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : list a0) := (fun y0 : list a0 => forall y1 : list a0, (@List.Forall a0 x0 (@List.app a0 y0 y1)) = ((@List.Forall a0 x0 y0) /\ (@List.Forall a0 x0 y1))) (@cons a0 x1 x2).
Definition term16 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : list a0 => forall y1 : list a0, (@List.Forall a0 x0 (@List.app a0 y0 y1)) = ((@List.Forall a0 x0 y0) /\ (@List.Forall a0 x0 y1)).
Definition term24 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) := imp (forall y0 : list a0, (@List.Forall a0 x1 (@List.app a0 x0 y0)) = ((@List.Forall a0 x1 x0) /\ (@List.Forall a0 x1 y0))).
Definition term34 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => forall y1 : list a0, (forall y2 : list a0, (@List.Forall a0 x0 (@List.app a0 y1 y2)) = ((@List.Forall a0 x0 y1) /\ (@List.Forall a0 x0 y2))) -> forall y2 : list a0, (@List.Forall a0 x0 (@List.app a0 (@cons a0 y0 y1) y2)) = ((@List.Forall a0 x0 (@cons a0 y0 y1)) /\ (@List.Forall a0 x0 y2)).
Definition term68 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : list a0) := @cons a0 x0 (@List.app a0 x1 x2).
Definition term64 (a0 : Type') (x0 : a0) (x1 : list a0) := (fun y0 : list a0 => forall y1 : list a0, (@List.app a0 (@cons a0 x0 y0) y1) = (@cons a0 x0 (@List.app a0 y0 y1))) x1.
Definition term21 (a0 : Type') (x0 : a0 -> Prop) (x1 : list a0) := (fun y0 : list a0 => forall y1 : list a0, (@List.Forall a0 x0 (@List.app a0 y0 y1)) = ((@List.Forall a0 x0 y0) /\ (@List.Forall a0 x0 y1))) x1.
Definition term37 (a0 : Type') (x0 : a0 -> Prop) := ((fun y0 : list a0 => forall y1 : list a0, (@List.Forall a0 x0 (@List.app a0 y0 y1)) = ((@List.Forall a0 x0 y0) /\ (@List.Forall a0 x0 y1))) (@nil a0)) /\ (forall y0 : a0, forall y1 : list a0, ((fun y2 : list a0 => forall y3 : list a0, (@List.Forall a0 x0 (@List.app a0 y2 y3)) = ((@List.Forall a0 x0 y2) /\ (@List.Forall a0 x0 y3))) y1) -> (fun y2 : list a0 => forall y3 : list a0, (@List.Forall a0 x0 (@List.app a0 y2 y3)) = ((@List.Forall a0 x0 y2) /\ (@List.Forall a0 x0 y3))) (@cons a0 y0 y1)).
Definition term13 := forall y0 : Prop, forall y1 : Prop, forall y2 : Prop, ((y0 /\ y1) /\ y2) = (y0 /\ (y1 /\ y2)).
Definition term12 := forall y0 : Prop, forall y1 : Prop, forall y2 : Prop, (y0 /\ (y1 /\ y2)) = ((y0 /\ y1) /\ y2).
Definition term9 (x0 : Prop) := forall y0 : Prop, forall y1 : Prop, ((x0 /\ y0) /\ y1) = (x0 /\ (y0 /\ y1)).
Definition term8 (x0 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 /\ (y0 /\ y1)) = ((x0 /\ y0) /\ y1).
Definition term3 (x0 : Prop) (x1 : Prop) := fun y0 : Prop => ((x0 /\ x1) /\ y0) = (x0 /\ (x1 /\ y0)).
Definition term26 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0 -> Prop) := forall y0 : list a0, (@List.Forall a0 x2 (@List.app a0 (@cons a0 x0 x1) y0)) = ((@List.Forall a0 x2 (@cons a0 x0 x1)) /\ (@List.Forall a0 x2 y0)).
Definition term22 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) := forall y0 : list a0, (@List.Forall a0 x1 (@List.app a0 x0 y0)) = ((@List.Forall a0 x1 x0) /\ (@List.Forall a0 x1 y0)).
Definition term18 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : list a0, (@List.Forall a0 x0 (@List.app a0 (@nil a0) y0)) = ((@List.Forall a0 x0 (@nil a0)) /\ (@List.Forall a0 x0 y0)).
Definition term27 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : list a0) := ((fun y0 : list a0 => forall y1 : list a0, (@List.Forall a0 x0 (@List.app a0 y0 y1)) = ((@List.Forall a0 x0 y0) /\ (@List.Forall a0 x0 y1))) x2) -> (fun y0 : list a0 => forall y1 : list a0, (@List.Forall a0 x0 (@List.app a0 y0 y1)) = ((@List.Forall a0 x0 y0) /\ (@List.Forall a0 x0 y1))) (@cons a0 x1 x2).
Definition term70 (a0 : Type') (x0 : a0 -> Prop) (x1 : list a0) (x2 : list a0) := @List.Forall a0 x0 (@List.app a0 x1 x2).
Definition term59 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((x0 /\ y0) /\ y1) = (x0 /\ (y0 /\ y1))) x1.
Definition term54 (a0 : Type') := fun y0 : list a0 => True.
Definition term82 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : list a0) := and ((x1 x0) /\ (@List.Forall a0 x1 x2)).
Definition term84 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0 -> Prop) (x3 : list a0) := ((x2 x0) /\ (@List.Forall a0 x2 x1)) /\ (@List.Forall a0 x2 x3).
Definition term57 (a0 : Type') (x0 : Prop) := forall y0 : list a0, x0.
Definition term66 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : list a0) := (fun y0 : list a0 => (@List.app a0 (@cons a0 x0 x1) y0) = (@cons a0 x0 (@List.app a0 x1 y0))) x2.
Definition term36 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, forall y1 : list a0, (forall y2 : list a0, (@List.Forall a0 x0 (@List.app a0 y1 y2)) = ((@List.Forall a0 x0 y1) /\ (@List.Forall a0 x0 y2))) -> forall y2 : list a0, (@List.Forall a0 x0 (@List.app a0 (@cons a0 y0 y1) y2)) = ((@List.Forall a0 x0 (@cons a0 y0 y1)) /\ (@List.Forall a0 x0 y2)).
Definition term35 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, forall y1 : list a0, ((fun y2 : list a0 => forall y3 : list a0, (@List.Forall a0 x0 (@List.app a0 y2 y3)) = ((@List.Forall a0 x0 y2) /\ (@List.Forall a0 x0 y3))) y1) -> (fun y2 : list a0 => forall y3 : list a0, (@List.Forall a0 x0 (@List.app a0 y2 y3)) = ((@List.Forall a0 x0 y2) /\ (@List.Forall a0 x0 y3))) (@cons a0 y0 y1).
Definition term74 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : list a0) := @List.Forall a0 x0 (@cons a0 x1 x2).
Definition term20 (a0 : Type') (x0 : a0 -> Prop) := and (forall y0 : list a0, (@List.Forall a0 x0 (@List.app a0 (@nil a0) y0)) = ((@List.Forall a0 x0 (@nil a0)) /\ (@List.Forall a0 x0 y0))).
Definition term73 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : list a0) (x3 : list a0) := @List.Forall a0 x0 (@cons a0 x1 (@List.app a0 x2 x3)).
Definition term2 (x0 : Prop) (x1 : Prop) := fun y0 : Prop => (x0 /\ (x1 /\ y0)) = ((x0 /\ x1) /\ y0).
Definition term28 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0 -> Prop) := (forall y0 : list a0, (@List.Forall a0 x2 (@List.app a0 x1 y0)) = ((@List.Forall a0 x2 x1) /\ (@List.Forall a0 x2 y0))) -> forall y0 : list a0, (@List.Forall a0 x2 (@List.app a0 (@cons a0 x0 x1) y0)) = ((@List.Forall a0 x2 (@cons a0 x0 x1)) /\ (@List.Forall a0 x2 y0)).
Definition term81 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : list a0) := and (@List.Forall a0 x0 (@cons a0 x1 x2)).
Definition term29 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := fun y0 : list a0 => ((fun y1 : list a0 => forall y2 : list a0, (@List.Forall a0 x0 (@List.app a0 y1 y2)) = ((@List.Forall a0 x0 y1) /\ (@List.Forall a0 x0 y2))) y0) -> (fun y1 : list a0 => forall y2 : list a0, (@List.Forall a0 x0 (@List.app a0 y1 y2)) = ((@List.Forall a0 x0 y1) /\ (@List.Forall a0 x0 y2))) (@cons a0 x1 y0).
