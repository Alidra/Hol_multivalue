Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term7 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := @eq (prod a0 a1) (@ε (prod a0 a1) (@GABS ((prod a0 a1) -> Prop) (fun y0 : type1210 a0 a1 => forall y1 : a0, forall y2 : a1, @GEQ Prop (y0 (@pair a0 a1 y1 y2)) (x0 y1 y2)))).
Definition term13 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term3 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := @GABS ((prod a0 a1) -> Prop) (fun y0 : type1210 a0 a1 => forall y1 : a0, forall y2 : a1, @GEQ Prop (y0 (@pair a0 a1 y1 y2)) (x0 y1 y2)).
Definition term1 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1412 a0 a1 a2) := @GABS ((prod a0 a1) -> a2) (fun y0 : type1209 a0 a1 a2 => forall y1 : a0, forall y2 : a1, @GEQ a2 (y0 (@pair a0 a1 y1 y2)) (x0 y1 y2)).
Definition term14 (a0 : Type') (a1 : Type') (x0 : Prop) := forall y0 : type1413 a0 a1, x0.
Definition term0 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1412 a0 a1 a2) := (fun y0 : type1412 a0 a1 a2 => (@GABS ((prod a0 a1) -> a2) (fun y1 : type1209 a0 a1 a2 => forall y2 : a0, forall y3 : a1, @GEQ a2 (y1 (@pair a0 a1 y2 y3)) (y0 y2 y3))) = (fun y1 : prod a0 a1 => y0 (@fst a0 a1 y1) (@snd a0 a1 y1))) x0.
Definition term9 (a0 : Type') (a1 : Type') := fun y0 : type1413 a0 a1 => (@ε (prod a0 a1) (@GABS ((prod a0 a1) -> Prop) (fun y1 : type1210 a0 a1 => forall y2 : a0, forall y3 : a1, @GEQ Prop (y1 (@pair a0 a1 y2 y3)) (y0 y2 y3)))) = (@ε (prod a0 a1) (fun y1 : prod a0 a1 => y0 (@fst a0 a1 y1) (@snd a0 a1 y1))).
Definition term6 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := @ε (prod a0 a1) (fun y0 : prod a0 a1 => x0 (@fst a0 a1 y0) (@snd a0 a1 y0)).
Definition term8 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := @eq (prod a0 a1) (@ε (prod a0 a1) (fun y0 : prod a0 a1 => x0 (@fst a0 a1 y0) (@snd a0 a1 y0))).
Definition term4 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := fun y0 : prod a0 a1 => x0 (@fst a0 a1 y0) (@snd a0 a1 y0).
Definition term2 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1412 a0 a1 a2) := fun y0 : prod a0 a1 => x0 (@fst a0 a1 y0) (@snd a0 a1 y0).
Definition term11 (a0 : Type') (a1 : Type') := forall y0 : type1413 a0 a1, (@ε (prod a0 a1) (@GABS ((prod a0 a1) -> Prop) (fun y1 : type1210 a0 a1 => forall y2 : a0, forall y3 : a1, @GEQ Prop (y1 (@pair a0 a1 y2 y3)) (y0 y2 y3)))) = (@ε (prod a0 a1) (fun y1 : prod a0 a1 => y0 (@fst a0 a1 y1) (@snd a0 a1 y1))).
Definition term10 (a0 : Type') (a1 : Type') := fun y0 : type1413 a0 a1 => True.
Definition term5 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := @ε (prod a0 a1) (@GABS ((prod a0 a1) -> Prop) (fun y0 : type1210 a0 a1 => forall y1 : a0, forall y2 : a1, @GEQ Prop (y0 (@pair a0 a1 y1 y2)) (x0 y1 y2))).
Definition term12 (a0 : Type') (a1 : Type') := forall y0 : type1413 a0 a1, True.
