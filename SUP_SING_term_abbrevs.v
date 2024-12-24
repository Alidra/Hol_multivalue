Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term17 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term1 (x0 : real) := forall y0 : real -> Prop, (@FINITE real y0) -> (sup (@INSERT real x0 y0)) = (@COND real (y0 = (@EMPTY real)) x0 (real_max x0 (sup y0))).
Definition term6 (x0 : real) := (@FINITE real (@EMPTY real)) -> (sup (@INSERT real x0 (@EMPTY real))) = (@COND real ((@EMPTY real) = (@EMPTY real)) x0 (real_max x0 (sup (@EMPTY real)))).
Definition term4 (x0 : real) (x1 : real -> Prop) := sup (@INSERT real x0 x1).
Definition term14 := fun y0 : real => True.
Definition term7 (x0 : real) := sup (@INSERT real x0 (@EMPTY real)).
Definition term16 := forall y0 : real, True.
Definition term18 (x0 : Prop) := forall y0 : real, x0.
Definition term15 := forall y0 : real, (sup (@INSERT real y0 (@EMPTY real))) = y0.
Definition term9 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0) (x2 : a0) := @COND a0 (x0 = x0) x1 x2.
Definition term8 (x0 : real) := @COND real ((@EMPTY real) = (@EMPTY real)) x0 (real_max x0 (sup (@EMPTY real))).
Definition term2 (x0 : real) (x1 : real -> Prop) := (fun y0 : real -> Prop => (@FINITE real y0) -> (sup (@INSERT real x0 y0)) = (@COND real (y0 = (@EMPTY real)) x0 (real_max x0 (sup y0)))) x1.
Definition term12 (x0 : real) := @eq real (sup (@INSERT real x0 (@EMPTY real))).
Definition term11 (x0 : real) := real_max x0 (sup (@EMPTY real)).
Definition term10 (x0 : real -> Prop) (x1 : real) (x2 : real) := @COND real (x0 = x0) x1 x2.
Definition term5 (x0 : real) (x1 : real -> Prop) := @COND real (x1 = (@EMPTY real)) x0 (real_max x0 (sup x1)).
Definition term3 (x0 : real) (x1 : real -> Prop) := (@FINITE real x1) -> (sup (@INSERT real x0 x1)) = (@COND real (x1 = (@EMPTY real)) x0 (real_max x0 (sup x1))).
Definition term0 (x0 : real) := (fun y0 : real => forall y1 : real -> Prop, (@FINITE real y1) -> (sup (@INSERT real y0 y1)) = (@COND real (y1 = (@EMPTY real)) y0 (real_max y0 (sup y1)))) x0.
Definition term13 := fun y0 : real => (sup (@INSERT real y0 (@EMPTY real))) = y0.
