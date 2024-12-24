Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term4 (x0 : real) (x1 : real -> Prop) := inf (@INSERT real x0 x1).
Definition term11 (x0 : real) := real_min x0 (inf (@EMPTY real)).
Definition term17 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term1 (x0 : real) := forall y0 : real -> Prop, (@FINITE real y0) -> (inf (@INSERT real x0 y0)) = (@COND real (y0 = (@EMPTY real)) x0 (real_min x0 (inf y0))).
Definition term14 := fun y0 : real => True.
Definition term3 (x0 : real) (x1 : real -> Prop) := (@FINITE real x1) -> (inf (@INSERT real x0 x1)) = (@COND real (x1 = (@EMPTY real)) x0 (real_min x0 (inf x1))).
Definition term16 := forall y0 : real, True.
Definition term18 (x0 : Prop) := forall y0 : real, x0.
Definition term15 := forall y0 : real, (inf (@INSERT real y0 (@EMPTY real))) = y0.
Definition term13 := fun y0 : real => (inf (@INSERT real y0 (@EMPTY real))) = y0.
Definition term9 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0) (x2 : a0) := @COND a0 (x0 = x0) x1 x2.
Definition term8 (x0 : real) := @COND real ((@EMPTY real) = (@EMPTY real)) x0 (real_min x0 (inf (@EMPTY real))).
Definition term2 (x0 : real) (x1 : real -> Prop) := (fun y0 : real -> Prop => (@FINITE real y0) -> (inf (@INSERT real x0 y0)) = (@COND real (y0 = (@EMPTY real)) x0 (real_min x0 (inf y0)))) x1.
Definition term12 (x0 : real) := @eq real (inf (@INSERT real x0 (@EMPTY real))).
Definition term7 (x0 : real) := inf (@INSERT real x0 (@EMPTY real)).
Definition term10 (x0 : real -> Prop) (x1 : real) (x2 : real) := @COND real (x0 = x0) x1 x2.
Definition term5 (x0 : real) (x1 : real -> Prop) := @COND real (x1 = (@EMPTY real)) x0 (real_min x0 (inf x1)).
Definition term6 (x0 : real) := (@FINITE real (@EMPTY real)) -> (inf (@INSERT real x0 (@EMPTY real))) = (@COND real ((@EMPTY real) = (@EMPTY real)) x0 (real_min x0 (inf (@EMPTY real)))).
Definition term0 (x0 : real) := (fun y0 : real => forall y1 : real -> Prop, (@FINITE real y1) -> (inf (@INSERT real y0 y1)) = (@COND real (y1 = (@EMPTY real)) y0 (real_min y0 (inf y1)))) x0.
