Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (x0 : real) := fun y0 : real => ((real_le (real_neg y0) x0) /\ (real_le x0 y0)) = (real_le (real_abs x0) y0).
Definition term30 (x0 : real -> Prop) (x1 : real) := real_le (real_abs (sup x0)) x1.
Definition term38 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term35 := fun y0 : real => True.
Definition term22 (x0 : real -> Prop) (x1 : real) := fun y0 : real => (@IN real y0 x0) -> (real_le (real_neg x1) y0) /\ (real_le y0 x1).
Definition term20 (x0 : real -> Prop) (x1 : real) (x2 : real) := (@IN real x1 x0) -> (real_le (real_neg x2) x1) /\ (real_le x1 x2).
Definition term14 (x0 : real) (x1 : real -> Prop) (x2 : real) := (fun y0 : real => ((~ (x1 = (@EMPTY real))) /\ (forall y1 : real, (@IN real y1 x1) -> (real_le x0 y1) /\ (real_le y1 y0))) -> (real_le x0 (sup x1)) /\ (real_le (sup x1) y0)) x2.
Definition term37 := forall y0 : real, True.
Definition term17 (x0 : real) (x1 : real) := (fun y0 : real => (real_le (real_abs x0) y0) = ((real_le (real_neg y0) x0) /\ (real_le x0 y0))) x1.
Definition term39 (x0 : Prop) := forall y0 : real, x0.
Definition term15 (x0 : real) (x1 : real -> Prop) (x2 : real) := ((~ (x1 = (@EMPTY real))) /\ (forall y0 : real, (@IN real y0 x1) -> (real_le x0 y0) /\ (real_le y0 x2))) -> (real_le x0 (sup x1)) /\ (real_le (sup x1) x2).
Definition term11 (x0 : real -> Prop) := forall y0 : real, forall y1 : real, ((~ (x0 = (@EMPTY real))) /\ (forall y2 : real, (@IN real y2 x0) -> (real_le y0 y2) /\ (real_le y2 y1))) -> (real_le y0 (sup x0)) /\ (real_le (sup x0) y1).
Definition term9 := forall y0 : real, forall y1 : real, (real_le (real_abs y0) y1) = ((real_le (real_neg y1) y0) /\ (real_le y0 y1)).
Definition term8 := forall y0 : real, forall y1 : real, ((real_le (real_neg y1) y0) /\ (real_le y0 y1)) = (real_le (real_abs y0) y1).
Definition term19 (x0 : real -> Prop) (x1 : real) (x2 : real) := (@IN real x1 x0) -> real_le (real_abs x1) x2.
Definition term13 (x0 : real) (x1 : real -> Prop) := forall y0 : real, ((~ (x1 = (@EMPTY real))) /\ (forall y1 : real, (@IN real y1 x1) -> (real_le x0 y1) /\ (real_le y1 y0))) -> (real_le x0 (sup x1)) /\ (real_le (sup x1) y0).
Definition term7 := fun y0 : real => forall y1 : real, (real_le (real_abs y0) y1) = ((real_le (real_neg y1) y0) /\ (real_le y0 y1)).
Definition term41 := fun y0 : real -> Prop => True.
Definition term4 (x0 : real) := forall y0 : real, ((real_le (real_neg y0) x0) /\ (real_le x0 y0)) = (real_le (real_abs x0) y0).
Definition term43 := forall y0 : real -> Prop, True.
Definition term25 (x0 : real -> Prop) := and (~ (x0 = (@EMPTY real))).
Definition term27 (x0 : real -> Prop) (x1 : real) := (~ (x0 = (@EMPTY real))) /\ (forall y0 : real, (@IN real y0 x0) -> (real_le (real_neg x1) y0) /\ (real_le y0 x1)).
Definition term26 (x0 : real -> Prop) (x1 : real) := (~ (x0 = (@EMPTY real))) /\ (forall y0 : real, (@IN real y0 x0) -> real_le (real_abs y0) x1).
Definition term6 := fun y0 : real => forall y1 : real, ((real_le (real_neg y1) y0) /\ (real_le y0 y1)) = (real_le (real_abs y0) y1).
Definition term16 (x0 : real) := (fun y0 : real => forall y1 : real, (real_le (real_abs y0) y1) = ((real_le (real_neg y1) y0) /\ (real_le y0 y1))) x0.
Definition term29 (x0 : real -> Prop) (x1 : real) := imp ((~ (x0 = (@EMPTY real))) /\ (forall y0 : real, (@IN real y0 x0) -> (real_le (real_neg x1) y0) /\ (real_le y0 x1))).
Definition term28 (x0 : real -> Prop) (x1 : real) := imp ((~ (x0 = (@EMPTY real))) /\ (forall y0 : real, (@IN real y0 x0) -> real_le (real_abs y0) x1)).
Definition term18 (x0 : real) (x1 : real -> Prop) := imp (@IN real x0 x1).
Definition term36 (x0 : real -> Prop) := forall y0 : real, ((~ (x0 = (@EMPTY real))) /\ (forall y1 : real, (@IN real y1 x0) -> real_le (real_abs y1) y0)) -> real_le (real_abs (sup x0)) y0.
Definition term34 (x0 : real -> Prop) := fun y0 : real => ((~ (x0 = (@EMPTY real))) /\ (forall y1 : real, (@IN real y1 x0) -> real_le (real_abs y1) y0)) -> real_le (real_abs (sup x0)) y0.
Definition term21 (x0 : real -> Prop) (x1 : real) := fun y0 : real => (@IN real y0 x0) -> real_le (real_abs y0) x1.
Definition term12 (x0 : real -> Prop) (x1 : real) := (fun y0 : real => forall y1 : real, ((~ (x0 = (@EMPTY real))) /\ (forall y2 : real, (@IN real y2 x0) -> (real_le y0 y2) /\ (real_le y2 y1))) -> (real_le y0 (sup x0)) /\ (real_le (sup x0) y1)) x1.
Definition term24 (x0 : real -> Prop) (x1 : real) := forall y0 : real, (@IN real y0 x0) -> (real_le (real_neg x1) y0) /\ (real_le y0 x1).
Definition term31 (x0 : real -> Prop) (x1 : real) := (real_le (real_neg x1) (sup x0)) /\ (real_le (sup x0) x1).
Definition term42 := forall y0 : real -> Prop, forall y1 : real, ((~ (y0 = (@EMPTY real))) /\ (forall y2 : real, (@IN real y2 y0) -> real_le (real_abs y2) y1)) -> real_le (real_abs (sup y0)) y1.
Definition term40 := fun y0 : real -> Prop => forall y1 : real, ((~ (y0 = (@EMPTY real))) /\ (forall y2 : real, (@IN real y2 y0) -> real_le (real_abs y2) y1)) -> real_le (real_abs (sup y0)) y1.
Definition term10 (x0 : real -> Prop) := (fun y0 : real -> Prop => forall y1 : real, forall y2 : real, ((~ (y0 = (@EMPTY real))) /\ (forall y3 : real, (@IN real y3 y0) -> (real_le y1 y3) /\ (real_le y3 y2))) -> (real_le y1 (sup y0)) /\ (real_le (sup y0) y2)) x0.
Definition term44 (x0 : Prop) := forall y0 : real -> Prop, x0.
Definition term32 (x0 : real -> Prop) (x1 : real) := ((~ (x0 = (@EMPTY real))) /\ (forall y0 : real, (@IN real y0 x0) -> real_le (real_abs y0) x1)) -> real_le (real_abs (sup x0)) x1.
Definition term3 (x0 : real) := fun y0 : real => (real_le (real_abs x0) y0) = ((real_le (real_neg y0) x0) /\ (real_le x0 y0)).
Definition term1 (x0 : real) (x1 : real) := real_le (real_abs x0) x1.
Definition term33 (x0 : real -> Prop) (x1 : real) := ((~ (x0 = (@EMPTY real))) /\ (forall y0 : real, (@IN real y0 x0) -> (real_le (real_neg x1) y0) /\ (real_le y0 x1))) -> (real_le (real_neg x1) (sup x0)) /\ (real_le (sup x0) x1).
Definition term5 (x0 : real) := forall y0 : real, (real_le (real_abs x0) y0) = ((real_le (real_neg y0) x0) /\ (real_le x0 y0)).
Definition term0 (x0 : real) (x1 : real) := (real_le (real_neg x1) x0) /\ (real_le x0 x1).
Definition term23 (x0 : real -> Prop) (x1 : real) := forall y0 : real, (@IN real y0 x0) -> real_le (real_abs y0) x1.
