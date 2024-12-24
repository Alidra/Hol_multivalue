Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term22 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : type1470 a0 a1) (x2 : a1) := (fun y0 : a1 => @INTER a0 (x0 y0) (x1 y0)) x2.
Definition term35 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : type1470 a0 a1) (x2 : type1470 a0 a1) := @eq Prop (forall y0 : a1, (@IN a1 y0 x0) -> (@INTER a0 (x1 y0) (x2 y0)) = (@EMPTY a0)).
Definition term18 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : type1470 a0 a1) := fun y0 : a1 => @INTER a0 (x0 y0) (x1 y0).
Definition term42 (a0 : Type') (a1 : Type') := forall y0 : a1 -> Prop, forall y1 : type1470 a0 a1, forall y2 : type1470 a0 a1, (@DISJOINT (prod a1 a0) (@disjoint_union a0 a1 y0 y1) (@disjoint_union a0 a1 y0 y2)) = (forall y3 : a1, (@IN a1 y3 y0) -> @DISJOINT a0 (y1 y3) (y2 y3)).
Definition term26 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : type1470 a0 a1) (x2 : a1) := @eq (a0 -> Prop) ((fun y0 : a1 => @INTER a0 (x0 y0) (x1 y0)) x2).
Definition term14 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1 -> Prop) (x2 : type1470 a0 a1) := @DISJOINT (prod a1 a0) (@disjoint_union a0 a1 x1 x0) (@disjoint_union a0 a1 x1 x2).
Definition term38 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : type1470 a0 a1) (x2 : type1470 a0 a1) := fun y0 : a1 => (@IN a1 y0 x0) -> @DISJOINT a0 (x1 y0) (x2 y0).
Definition term13 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@DISJOINT a0 x0 y0) = ((@INTER a0 x0 y0) = (@EMPTY a0))) x1.
Definition term12 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (@DISJOINT a0 x0 y0) = ((@INTER a0 x0 y0) = (@EMPTY a0)).
Definition term1 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) := forall y0 : type1470 a0 a1, ((@disjoint_union a0 a1 x0 y0) = (@EMPTY (prod a1 a0))) = (forall y1 : a1, (@IN a1 y1 x0) -> (y0 y1) = (@EMPTY a0)).
Definition term34 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1 -> Prop) (x2 : type1470 a0 a1) := @eq Prop (@DISJOINT (prod a1 a0) (@disjoint_union a0 a1 x1 x0) (@disjoint_union a0 a1 x1 x2)).
Definition term21 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : type1470 a0 a1) (x2 : a1) := (fun y0 : a1 => (fun y1 : a1 => @INTER a0 (x0 y1) (x1 y1)) y0) x2.
Definition term23 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : type1470 a0 a1) (x2 : a1) := @INTER a0 (x0 x2) (x1 x2).
Definition term30 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : type1470 a0 a1) (x2 : type1470 a0 a1) (x3 : a1) := (@IN a1 x3 x0) -> (@INTER a0 (x1 x3) (x2 x3)) = (@EMPTY a0).
Definition term36 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : type1470 a0 a1) (x2 : a1) := @DISJOINT a0 (x0 x2) (x1 x2).
Definition term10 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : type1470 a0 a1) (x2 : type1470 a0 a1) := @disjoint_union a0 a1 x0 (fun y0 : a1 => @INTER a0 (x1 y0) (x2 y0)).
Definition term19 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term40 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : type1470 a0 a1) := forall y0 : type1470 a0 a1, (@DISJOINT (prod a1 a0) (@disjoint_union a0 a1 x0 x1) (@disjoint_union a0 a1 x0 y0)) = (forall y1 : a1, (@IN a1 y1 x0) -> @DISJOINT a0 (x1 y1) (y0 y1)).
Definition term11 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (@DISJOINT a0 y0 y1) = ((@INTER a0 y0 y1) = (@EMPTY a0))) x0.
Definition term7 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : type1470 a0 a1) := forall y0 : type1470 a0 a1, (@INTER (prod a1 a0) (@disjoint_union a0 a1 x0 x1) (@disjoint_union a0 a1 x0 y0)) = (@disjoint_union a0 a1 x0 (fun y1 : a1 => @INTER a0 (x1 y1) (y0 y1))).
Definition term31 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : type1470 a0 a1) (x2 : type1470 a0 a1) := fun y0 : a1 => (@IN a1 y0 x0) -> ((fun y1 : a1 => @INTER a0 (x1 y1) (x2 y1)) y0) = (@EMPTY a0).
Definition term28 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := imp (@IN a0 x0 x1).
Definition term41 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) := forall y0 : type1470 a0 a1, forall y1 : type1470 a0 a1, (@DISJOINT (prod a1 a0) (@disjoint_union a0 a1 x0 y0) (@disjoint_union a0 a1 x0 y1)) = (forall y2 : a1, (@IN a1 y2 x0) -> @DISJOINT a0 (y0 y2) (y1 y2)).
Definition term5 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) := forall y0 : type1470 a0 a1, forall y1 : type1470 a0 a1, (@INTER (prod a1 a0) (@disjoint_union a0 a1 x0 y0) (@disjoint_union a0 a1 x0 y1)) = (@disjoint_union a0 a1 x0 (fun y2 : a1 => @INTER a0 (y0 y2) (y1 y2))).
Definition term32 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : type1470 a0 a1) (x2 : type1470 a0 a1) := fun y0 : a1 => (@IN a1 y0 x0) -> (@INTER a0 (x1 y0) (x2 y0)) = (@EMPTY a0).
Definition term27 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : type1470 a0 a1) (x2 : a1) := @eq (a0 -> Prop) (@INTER a0 (x0 x2) (x1 x2)).
Definition term16 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : type1470 a0 a1) (x2 : type1470 a0 a1) := @eq ((prod a1 a0) -> Prop) (@disjoint_union a0 a1 x0 (fun y0 : a1 => @INTER a0 (x1 y0) (x2 y0))).
Definition term33 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : type1470 a0 a1) (x2 : type1470 a0 a1) := forall y0 : a1, (@IN a1 y0 x0) -> (@INTER a0 (x1 y0) (x2 y0)) = (@EMPTY a0).
Definition term17 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : type1470 a0 a1) (x2 : type1470 a0 a1) := forall y0 : a1, (@IN a1 y0 x0) -> ((fun y1 : a1 => @INTER a0 (x1 y1) (x2 y1)) y0) = (@EMPTY a0).
Definition term3 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : type1470 a0 a1) := forall y0 : a1, (@IN a1 y0 x0) -> (x1 y0) = (@EMPTY a0).
Definition term2 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : type1470 a0 a1) := (fun y0 : type1470 a0 a1 => ((@disjoint_union a0 a1 x0 y0) = (@EMPTY (prod a1 a0))) = (forall y1 : a1, (@IN a1 y1 x0) -> (y0 y1) = (@EMPTY a0))) x1.
Definition term24 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : type1470 a0 a1) := fun y0 : a1 => (fun y1 : a1 => @INTER a0 (x0 y1) (x1 y1)) y0.
Definition term8 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : type1470 a0 a1) (x2 : type1470 a0 a1) := (fun y0 : type1470 a0 a1 => (@INTER (prod a1 a0) (@disjoint_union a0 a1 x0 x1) (@disjoint_union a0 a1 x0 y0)) = (@disjoint_union a0 a1 x0 (fun y1 : a1 => @INTER a0 (x1 y1) (y0 y1)))) x2.
Definition term9 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1 -> Prop) (x2 : type1470 a0 a1) := @INTER (prod a1 a0) (@disjoint_union a0 a1 x1 x0) (@disjoint_union a0 a1 x1 x2).
Definition term20 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) := (fun y0 : a1 => x0 y0) x1.
Definition term29 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : type1470 a0 a1) (x2 : type1470 a0 a1) (x3 : a1) := (@IN a1 x3 x0) -> ((fun y0 : a1 => @INTER a0 (x1 y0) (x2 y0)) x3) = (@EMPTY a0).
Definition term4 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) := (fun y0 : a1 -> Prop => forall y1 : type1470 a0 a1, forall y2 : type1470 a0 a1, (@INTER (prod a1 a0) (@disjoint_union a0 a1 y0 y1) (@disjoint_union a0 a1 y0 y2)) = (@disjoint_union a0 a1 y0 (fun y3 : a1 => @INTER a0 (y1 y3) (y2 y3)))) x0.
Definition term39 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : type1470 a0 a1) (x2 : type1470 a0 a1) := forall y0 : a1, (@IN a1 y0 x0) -> @DISJOINT a0 (x1 y0) (x2 y0).
Definition term6 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : type1470 a0 a1) := (fun y0 : type1470 a0 a1 => forall y1 : type1470 a0 a1, (@INTER (prod a1 a0) (@disjoint_union a0 a1 x0 y0) (@disjoint_union a0 a1 x0 y1)) = (@disjoint_union a0 a1 x0 (fun y2 : a1 => @INTER a0 (y0 y2) (y1 y2)))) x1.
Definition term0 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) := (fun y0 : a1 -> Prop => forall y1 : type1470 a0 a1, ((@disjoint_union a0 a1 y0 y1) = (@EMPTY (prod a1 a0))) = (forall y2 : a1, (@IN a1 y2 y0) -> (y1 y2) = (@EMPTY a0))) x0.
Definition term37 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : type1470 a0 a1) (x2 : type1470 a0 a1) (x3 : a1) := (@IN a1 x3 x0) -> @DISJOINT a0 (x1 x3) (x2 x3).
Definition term15 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1 -> Prop) (x2 : type1470 a0 a1) := @eq ((prod a1 a0) -> Prop) (@INTER (prod a1 a0) (@disjoint_union a0 a1 x1 x0) (@disjoint_union a0 a1 x1 x2)).
Definition term25 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : type1470 a0 a1) (x2 : a1) := @eq (a0 -> Prop) ((fun y0 : a1 => (fun y1 : a1 => @INTER a0 (x0 y1) (x1 y1)) y0) x2).
