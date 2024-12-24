Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term9 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := (@SUBSET a0 (@support a0 real real_add x1 (@UNIV a0)) x0) -> (@sum a0 x0 x1) = (@sum a0 (@UNIV a0) x1).
Definition term19 (a0 : Type') (x0 : type1627) := (@monoidal real x0) -> forall y0 : a0 -> real, forall y1 : a0 -> Prop, (@SUBSET a0 (@support a0 real x0 y0 (@UNIV a0)) y1) -> (@iterate real a0 x0 y1 y0) = (@iterate real a0 x0 (@UNIV a0) y0).
Definition term2 (a0 : Type') (a1 : Type') (x0 : type1400 a0) := (@monoidal a0 x0) -> forall y0 : a1 -> a0, forall y1 : a1 -> Prop, (@SUBSET a1 (@support a1 a0 x0 y0 (@UNIV a1)) y1) -> (@iterate a0 a1 x0 y1 y0) = (@iterate a0 a1 x0 (@UNIV a1) y0).
Definition term0 (a0 : Type') (a1 : Type') := forall y0 : type1400 a0, (@monoidal a0 y0) -> forall y1 : a1 -> a0, forall y2 : a1 -> Prop, (@SUBSET a1 (@support a1 a0 y0 y1 (@UNIV a1)) y2) -> (@iterate a0 a1 y0 y2 y1) = (@iterate a0 a1 y0 (@UNIV a1) y1).
Definition term20 (a0 : Type') := (@monoidal real real_add) -> forall y0 : a0 -> real, forall y1 : a0 -> Prop, (@SUBSET a0 (@support a0 real real_add y0 (@UNIV a0)) y1) -> (@iterate real a0 real_add y1 y0) = (@iterate real a0 real_add (@UNIV a0) y0).
Definition term4 (a0 : Type') (a1 : Type') (x0 : type1400 a0) := (forall y0 : type1400 a0, (@monoidal a0 y0) -> forall y1 : a1 -> a0, forall y2 : a1 -> Prop, (@SUBSET a1 (@support a1 a0 y0 y1 (@UNIV a1)) y2) -> (@iterate a0 a1 y0 y2 y1) = (@iterate a0 a1 y0 (@UNIV a1) y1)) -> forall y0 : a1 -> a0, forall y1 : a1 -> Prop, (@SUBSET a1 (@support a1 a0 x0 y0 (@UNIV a1)) y1) -> (@iterate a0 a1 x0 y1 y0) = (@iterate a0 a1 x0 (@UNIV a1) y0).
Definition term16 (a0 : Type') := fun y0 : a0 -> real => forall y1 : a0 -> Prop, (@SUBSET a0 (@support a0 real real_add y0 (@UNIV a0)) y1) -> (@iterate real a0 real_add y1 y0) = (@iterate real a0 real_add (@UNIV a0) y0).
Definition term15 (a0 : Type') := fun y0 : a0 -> real => forall y1 : a0 -> Prop, (@SUBSET a0 (@support a0 real real_add y0 (@UNIV a0)) y1) -> (@sum a0 y1 y0) = (@sum a0 (@UNIV a0) y0).
Definition term1 (a0 : Type') (a1 : Type') (x0 : type1400 a0) := (fun y0 : type1400 a0 => (@monoidal a0 y0) -> forall y1 : a1 -> a0, forall y2 : a1 -> Prop, (@SUBSET a1 (@support a1 a0 y0 y1 (@UNIV a1)) y2) -> (@iterate a0 a1 y0 y2 y1) = (@iterate a0 a1 y0 (@UNIV a1) y1)) x0.
Definition term14 (a0 : Type') (x0 : a0 -> real) := forall y0 : a0 -> Prop, (@SUBSET a0 (@support a0 real real_add x0 (@UNIV a0)) y0) -> (@iterate real a0 real_add y0 x0) = (@iterate real a0 real_add (@UNIV a0) x0).
Definition term13 (a0 : Type') (x0 : a0 -> real) := forall y0 : a0 -> Prop, (@SUBSET a0 (@support a0 real real_add x0 (@UNIV a0)) y0) -> (@sum a0 y0 x0) = (@sum a0 (@UNIV a0) x0).
Definition term6 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := @eq real (@sum a0 x0 x1).
Definition term18 (a0 : Type') := forall y0 : a0 -> real, forall y1 : a0 -> Prop, (@SUBSET a0 (@support a0 real real_add y0 (@UNIV a0)) y1) -> (@iterate real a0 real_add y1 y0) = (@iterate real a0 real_add (@UNIV a0) y0).
Definition term17 (a0 : Type') := forall y0 : a0 -> real, forall y1 : a0 -> Prop, (@SUBSET a0 (@support a0 real real_add y0 (@UNIV a0)) y1) -> (@sum a0 y1 y0) = (@sum a0 (@UNIV a0) y0).
Definition term3 (a0 : Type') (a1 : Type') (x0 : type1400 a0) := forall y0 : a1 -> a0, forall y1 : a1 -> Prop, (@SUBSET a1 (@support a1 a0 x0 y0 (@UNIV a1)) y1) -> (@iterate a0 a1 x0 y1 y0) = (@iterate a0 a1 x0 (@UNIV a1) y0).
Definition term8 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) := imp (@SUBSET a0 (@support a0 real real_add x0 (@UNIV a0)) x1).
Definition term10 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := (@SUBSET a0 (@support a0 real real_add x1 (@UNIV a0)) x0) -> (@iterate real a0 real_add x0 x1) = (@iterate real a0 real_add (@UNIV a0) x1).
Definition term7 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := @eq real (@iterate real a0 real_add x0 x1).
Definition term12 (a0 : Type') (x0 : a0 -> real) := fun y0 : a0 -> Prop => (@SUBSET a0 (@support a0 real real_add x0 (@UNIV a0)) y0) -> (@iterate real a0 real_add y0 x0) = (@iterate real a0 real_add (@UNIV a0) x0).
Definition term5 (a0 : Type') (a1 : Type') := (forall y0 : type1400 a0, (@monoidal a0 y0) -> forall y1 : a1 -> a0, forall y2 : a1 -> Prop, (@SUBSET a1 (@support a1 a0 y0 y1 (@UNIV a1)) y2) -> (@iterate a0 a1 y0 y2 y1) = (@iterate a0 a1 y0 (@UNIV a1) y1)) -> forall y0 : type1400 a0, (@monoidal a0 y0) -> forall y1 : a1 -> a0, forall y2 : a1 -> Prop, (@SUBSET a1 (@support a1 a0 y0 y1 (@UNIV a1)) y2) -> (@iterate a0 a1 y0 y2 y1) = (@iterate a0 a1 y0 (@UNIV a1) y1).
Definition term11 (a0 : Type') (x0 : a0 -> real) := fun y0 : a0 -> Prop => (@SUBSET a0 (@support a0 real real_add x0 (@UNIV a0)) y0) -> (@sum a0 y0 x0) = (@sum a0 (@UNIV a0) x0).
