Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0, (y0 y1) -> y0 (@ε a0 y0)) x0.
Definition term1 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := fun y0 : a0 => x0 y0.
Definition term9 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := forall y0 : a0, (x0 y0) -> x1.
Definition term17 (a0 : Type') (x0 : a0 -> Prop) := x0 (@GABS a0 x0).
Definition term24 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => x0 y0.
Definition term27 (a0 : Type') (x0 : a0 -> Prop) := ((ex x0) -> (x0 (@GABS a0 x0)) = True) -> ((ex x0) -> x0 (@GABS a0 x0)) = ((ex x0) -> True).
Definition term29 (a0 : Type') (x0 : a0 -> Prop) := (ex x0) -> True.
Definition term0 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := (fun y0 : a0 -> a1 => (fun y1 : a0 => y0 y1) = y0) x0.
Definition term25 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0, x0 y0.
Definition term12 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@GABS a0 y0) = (@ε a0 y0)) x0.
Definition term20 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => ((ex x0) = x1) -> (x1 -> (x0 (@GABS a0 x0)) = y0) -> ((ex x0) -> x0 (@GABS a0 x0)) = (x1 -> y0)) x2.
Definition term13 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term4 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => (x0 y0) -> x0 (@ε a0 x0)) x1.
Definition term23 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := ((ex x0) -> (x0 (@GABS a0 x0)) = x1) -> ((ex x0) -> x0 (@GABS a0 x0)) = ((ex x0) -> x1).
Definition term6 (a0 : Type') (x0 : a0 -> Prop) := x0 (@ε a0 x0).
Definition term19 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := forall y0 : Prop, ((ex x0) = x1) -> (x1 -> (x0 (@GABS a0 x0)) = y0) -> ((ex x0) -> x0 (@GABS a0 x0)) = (x1 -> y0).
Definition term14 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term11 (a0 : Type') (x0 : a0 -> Prop) := (exists y0 : a0, x0 y0) -> (x0 (@ε a0 x0)) = True.
Definition term16 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : Prop, forall y1 : Prop, ((ex x0) = y0) -> (y0 -> (x0 (@GABS a0 x0)) = y1) -> ((ex x0) -> x0 (@GABS a0 x0)) = (y0 -> y1).
Definition term15 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term26 (a0 : Type') (x0 : a0 -> Prop) := (ex x0) -> (x0 (@GABS a0 x0)) = True.
Definition term3 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, (x0 y0) -> x0 (@ε a0 x0).
Definition term7 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (x1 x0) -> (x1 (@ε a0 x1)) = True.
Definition term8 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, (x0 y0) -> (x0 (@ε a0 x0)) = True.
Definition term5 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (x1 x0) -> x1 (@ε a0 x1).
Definition term10 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) -> x1.
Definition term22 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := ((ex x0) = (ex x0)) -> ((ex x0) -> (x0 (@GABS a0 x0)) = x1) -> ((ex x0) -> x0 (@GABS a0 x0)) = ((ex x0) -> x1).
Definition term18 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((ex x0) = y0) -> (y0 -> (x0 (@GABS a0 x0)) = y1) -> ((ex x0) -> x0 (@GABS a0 x0)) = (y0 -> y1)) x1.
Definition term21 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) (x2 : Prop) := ((ex x0) = x1) -> (x1 -> (x0 (@GABS a0 x0)) = x2) -> ((ex x0) -> x0 (@GABS a0 x0)) = (x1 -> x2).
Definition term28 (a0 : Type') (x0 : a0 -> Prop) := (ex x0) -> x0 (@GABS a0 x0).
