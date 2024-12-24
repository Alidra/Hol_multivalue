Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term30 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := forall y0 : prod hreal hreal, forall y1 : prod hreal hreal, ((treal_eq x0 x1) /\ (treal_eq y0 y1)) -> (treal_le x0 y0) = (treal_le x1 y1).
Definition term14 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := (fun y0 : type1233 => fun y1 : type1233 => (real_le (mk_real (treal_eq x1)) (mk_real (treal_eq x0))) = (@ε Prop (fun y2 : Prop => exists y3 : prod hreal hreal, exists y4 : prod hreal hreal, ((treal_le y3 y4) = y2) /\ ((y0 y3) /\ (y1 y4))))) (dest_real (mk_real (treal_eq x1))).
Definition term4 (x0 : real) (x1 : real) := (fun y0 : real => @ε Prop (fun y1 : Prop => exists y2 : prod hreal hreal, exists y3 : prod hreal hreal, ((treal_le y2 y3) = y1) /\ ((dest_real x0 y2) /\ (dest_real y0 y3)))) x1.
Definition term8 (x0 : prod hreal hreal) := dest_real (mk_real (treal_eq x0)).
Definition term2 (x0 : real) := fun y0 : real => @ε Prop (fun y1 : Prop => exists y2 : prod hreal hreal, exists y3 : prod hreal hreal, ((treal_le y2 y3) = y1) /\ ((dest_real x0 y2) /\ (dest_real y0 y3))).
Definition term40 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := (treal_eq x0 x0) /\ (treal_eq x1 x1).
Definition term22 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := @ε Prop (fun y0 : Prop => exists y1 : prod hreal hreal, exists y2 : prod hreal hreal, ((treal_le y1 y2) = y0) /\ ((treal_eq x0 y1) /\ (treal_eq x1 y2))).
Definition term11 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := @ε Prop (fun y0 : Prop => exists y1 : prod hreal hreal, exists y2 : prod hreal hreal, ((treal_le y1 y2) = y0) /\ ((dest_real (mk_real (treal_eq x0)) y1) /\ (dest_real (mk_real (treal_eq x1)) y2))).
Definition term5 (x0 : real) (x1 : real) := @ε Prop (fun y0 : Prop => exists y1 : prod hreal hreal, exists y2 : prod hreal hreal, ((treal_le y1 y2) = y0) /\ ((dest_real x0 y1) /\ (dest_real x1 y2))).
Definition term51 (a0 : Type') (x0 : a0) := @ε a0 (fun y0 : a0 => x0 = y0).
Definition term37 (x0 : Prop) (x1 : prod hreal hreal) (x2 : prod hreal hreal) := exists y0 : prod hreal hreal, exists y1 : prod hreal hreal, ((treal_le y0 y1) = x0) /\ ((treal_eq x1 y0) /\ (treal_eq x2 y1)).
Definition term46 (x0 : Prop) (x1 : prod hreal hreal) (x2 : prod hreal hreal) := ((exists y0 : prod hreal hreal, exists y1 : prod hreal hreal, ((treal_le y0 y1) = x0) /\ ((treal_eq x1 y0) /\ (treal_eq x2 y1))) -> (treal_le x1 x2) = x0) /\ (((treal_le x1 x2) = x0) -> exists y0 : prod hreal hreal, exists y1 : prod hreal hreal, ((treal_le y0 y1) = x0) /\ ((treal_eq x1 y0) /\ (treal_eq x2 y1))).
Definition term20 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := (fun y0 : type1233 => (real_le (mk_real (treal_eq x0)) (mk_real (treal_eq x1))) = (@ε Prop (fun y1 : Prop => exists y2 : prod hreal hreal, exists y3 : prod hreal hreal, ((treal_le y2 y3) = y1) /\ ((dest_real (mk_real (treal_eq x0)) y2) /\ (y0 y3))))) (dest_real (mk_real (treal_eq x1))).
Definition term32 (x0 : prod hreal hreal) (x1 : prod hreal hreal) (x2 : prod hreal hreal) := forall y0 : prod hreal hreal, ((treal_eq x0 x2) /\ (treal_eq x1 y0)) -> (treal_le x0 x1) = (treal_le x2 y0).
Definition term26 (x0 : prod hreal hreal) (x1 : prod hreal hreal) (x2 : prod hreal hreal) (x3 : prod hreal hreal) := (treal_eq x0 x1) /\ (treal_eq x2 x3).
Definition term24 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := @eq Prop ((real_le (mk_real (treal_eq x0)) (mk_real (treal_eq x1))) = (@ε Prop (fun y0 : Prop => exists y1 : prod hreal hreal, exists y2 : prod hreal hreal, ((treal_le y1 y2) = y0) /\ ((dest_real (mk_real (treal_eq x0)) y1) /\ (dest_real (mk_real (treal_eq x1)) y2))))).
Definition term9 (x0 : prod hreal hreal) := fun y0 : prod hreal hreal => (treal_eq x0) = (treal_eq y0).
Definition term21 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := (fun y0 : type1233 => (real_le (mk_real (treal_eq x0)) (mk_real (treal_eq x1))) = (@ε Prop (fun y1 : Prop => exists y2 : prod hreal hreal, exists y3 : prod hreal hreal, ((treal_le y2 y3) = y1) /\ ((treal_eq x0 y2) /\ (y0 y3))))) (treal_eq x1).
Definition term33 (x0 : prod hreal hreal) (x1 : prod hreal hreal) (x2 : prod hreal hreal) (x3 : prod hreal hreal) := (fun y0 : prod hreal hreal => ((treal_eq x0 x2) /\ (treal_eq x1 y0)) -> (treal_le x0 x1) = (treal_le x2 y0)) x3.
Definition term3 (x0 : real) := @eq (real -> Prop) (real_le x0).
Definition term47 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := fun y0 : Prop => exists y1 : prod hreal hreal, exists y2 : prod hreal hreal, ((treal_le y1 y2) = y0) /\ ((treal_eq x0 y1) /\ (treal_eq x1 y2)).
Definition term1 (x0 : real) := (fun y0 : real => fun y1 : real => @ε Prop (fun y2 : Prop => exists y3 : prod hreal hreal, exists y4 : prod hreal hreal, ((treal_le y3 y4) = y2) /\ ((dest_real y0 y3) /\ (dest_real y1 y4)))) x0.
Definition term15 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := (fun y0 : type1233 => fun y1 : type1233 => (real_le (mk_real (treal_eq x1)) (mk_real (treal_eq x0))) = (@ε Prop (fun y2 : Prop => exists y3 : prod hreal hreal, exists y4 : prod hreal hreal, ((treal_le y3 y4) = y2) /\ ((y0 y3) /\ (y1 y4))))) (treal_eq x1).
Definition term31 (x0 : prod hreal hreal) (x1 : prod hreal hreal) (x2 : prod hreal hreal) := (fun y0 : prod hreal hreal => forall y1 : prod hreal hreal, ((treal_eq x0 x1) /\ (treal_eq y0 y1)) -> (treal_le x0 y0) = (treal_le x1 y1)) x2.
Definition term25 (x0 : Prop) (x1 : prod hreal hreal) (x2 : prod hreal hreal) (x3 : prod hreal hreal) (x4 : prod hreal hreal) := ((treal_le x2 x4) = x0) /\ ((treal_eq x1 x2) /\ (treal_eq x3 x4)).
Definition term53 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := @eq Prop (real_le (mk_real (treal_eq x0)) (mk_real (treal_eq x1))).
Definition term41 (x0 : Prop) (x1 : prod hreal hreal) (x2 : prod hreal hreal) := ((treal_le x1 x2) = x0) /\ ((treal_eq x1 x1) /\ (treal_eq x2 x2)).
Definition term0 := fun y0 : real => fun y1 : real => @ε Prop (fun y2 : Prop => exists y3 : prod hreal hreal, exists y4 : prod hreal hreal, ((treal_le y3 y4) = y2) /\ ((dest_real y0 y3) /\ (dest_real y1 y4))).
Definition term38 (x0 : Prop) (x1 : prod hreal hreal) (x2 : prod hreal hreal) := fun y0 : prod hreal hreal => exists y1 : prod hreal hreal, ((treal_le y0 y1) = x0) /\ ((treal_eq x1 y0) /\ (treal_eq x2 y1)).
Definition term28 (x0 : prod hreal hreal) := forall y0 : prod hreal hreal, forall y1 : prod hreal hreal, forall y2 : prod hreal hreal, ((treal_eq x0 y0) /\ (treal_eq y1 y2)) -> (treal_le x0 y1) = (treal_le y0 y2).
Definition term6 (x0 : real) (x1 : real) := @eq Prop (real_le x0 x1).
Definition term29 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := (fun y0 : prod hreal hreal => forall y1 : prod hreal hreal, forall y2 : prod hreal hreal, ((treal_eq x0 y0) /\ (treal_eq y1 y2)) -> (treal_le x0 y1) = (treal_le y0 y2)) x1.
Definition term35 (x0 : Prop) (x1 : prod hreal hreal) (x2 : prod hreal hreal) (x3 : prod hreal hreal) := exists y0 : prod hreal hreal, ((treal_le x2 y0) = x0) /\ ((treal_eq x1 x2) /\ (treal_eq x3 y0)).
Definition term23 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := @eq Prop ((fun y0 : type1233 => (real_le (mk_real (treal_eq x0)) (mk_real (treal_eq x1))) = (@ε Prop (fun y1 : Prop => exists y2 : prod hreal hreal, exists y3 : prod hreal hreal, ((treal_le y2 y3) = y1) /\ ((dest_real (mk_real (treal_eq x0)) y2) /\ (y0 y3))))) (dest_real (mk_real (treal_eq x1)))).
Definition term39 (x0 : prod hreal hreal) := (fun y0 : prod hreal hreal => treal_eq y0 y0) x0.
Definition term10 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := real_le (mk_real (treal_eq x0)) (mk_real (treal_eq x1)).
Definition term18 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := fun y0 : type1233 => (real_le (mk_real (treal_eq x1)) (mk_real (treal_eq x0))) = (@ε Prop (fun y1 : Prop => exists y2 : prod hreal hreal, exists y3 : prod hreal hreal, ((treal_le y2 y3) = y1) /\ ((dest_real (mk_real (treal_eq x1)) y2) /\ (y0 y3)))).
Definition term16 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := fun y0 : type1233 => (real_le (mk_real (treal_eq x1)) (mk_real (treal_eq x0))) = (@ε Prop (fun y1 : Prop => exists y2 : prod hreal hreal, exists y3 : prod hreal hreal, ((treal_le y2 y3) = y1) /\ ((treal_eq x1 y2) /\ (y0 y3)))).
Definition term12 (x0 : prod hreal hreal) := mk_real (treal_eq x0).
Definition term36 (x0 : Prop) (x1 : prod hreal hreal) (x2 : prod hreal hreal) (x3 : prod hreal hreal) := fun y0 : prod hreal hreal => ((treal_le x2 y0) = x0) /\ ((treal_eq x1 x2) /\ (treal_eq x3 y0)).
Definition term19 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := @eq (((prod hreal hreal) -> Prop) -> Prop) (fun y0 : type1233 => (real_le (mk_real (treal_eq x1)) (mk_real (treal_eq x0))) = (@ε Prop (fun y1 : Prop => exists y2 : prod hreal hreal, exists y3 : prod hreal hreal, ((treal_le y2 y3) = y1) /\ ((dest_real (mk_real (treal_eq x1)) y2) /\ (y0 y3))))).
Definition term49 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := @ε Prop (fun y0 : Prop => (treal_le x0 x1) = y0).
Definition term17 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := @eq (((prod hreal hreal) -> Prop) -> Prop) ((fun y0 : type1233 => fun y1 : type1233 => (real_le (mk_real (treal_eq x1)) (mk_real (treal_eq x0))) = (@ε Prop (fun y2 : Prop => exists y3 : prod hreal hreal, exists y4 : prod hreal hreal, ((treal_le y3 y4) = y2) /\ ((y0 y3) /\ (y1 y4))))) (dest_real (mk_real (treal_eq x1)))).
Definition term48 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := fun y0 : Prop => (treal_le x0 x1) = y0.
Definition term34 (x0 : prod hreal hreal) (x1 : prod hreal hreal) (x2 : prod hreal hreal) (x3 : prod hreal hreal) := ((treal_eq x0 x2) /\ (treal_eq x1 x3)) -> (treal_le x0 x1) = (treal_le x2 x3).
Definition term52 (x0 : Prop) := @ε Prop (fun y0 : Prop => x0 = y0).
Definition term13 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := fun y0 : type1233 => fun y1 : type1233 => (real_le (mk_real (treal_eq x0)) (mk_real (treal_eq x1))) = (@ε Prop (fun y2 : Prop => exists y3 : prod hreal hreal, exists y4 : prod hreal hreal, ((treal_le y3 y4) = y2) /\ ((y0 y3) /\ (y1 y4)))).
Definition term45 (x0 : prod hreal hreal) (x1 : prod hreal hreal) (x2 : Prop) := (exists y0 : prod hreal hreal, exists y1 : prod hreal hreal, ((treal_le y0 y1) = x2) /\ ((treal_eq x0 y0) /\ (treal_eq x1 y1))) -> (treal_le x0 x1) = x2.
Definition term43 (x0 : Prop) (x1 : prod hreal hreal) (x2 : prod hreal hreal) := (((treal_le x1 x2) = x0) /\ ((treal_eq x1 x1) /\ (treal_eq x2 x2))) -> exists y0 : prod hreal hreal, exists y1 : prod hreal hreal, ((treal_le y0 y1) = x0) /\ ((treal_eq x1 y0) /\ (treal_eq x2 y1)).
Definition term42 (x0 : prod hreal hreal) (x1 : prod hreal hreal) (x2 : Prop) (x3 : prod hreal hreal) (x4 : prod hreal hreal) := (((treal_le x0 x1) = x2) /\ ((treal_eq x3 x0) /\ (treal_eq x4 x1))) -> exists y0 : prod hreal hreal, exists y1 : prod hreal hreal, ((treal_le y0 y1) = x2) /\ ((treal_eq x3 y0) /\ (treal_eq x4 y1)).
Definition term27 (x0 : prod hreal hreal) := (fun y0 : prod hreal hreal => forall y1 : prod hreal hreal, forall y2 : prod hreal hreal, forall y3 : prod hreal hreal, ((treal_eq y0 y1) /\ (treal_eq y2 y3)) -> (treal_le y0 y2) = (treal_le y1 y3)) x0.
Definition term44 (x0 : Prop) (x1 : prod hreal hreal) (x2 : prod hreal hreal) := ((treal_le x1 x2) = x0) -> exists y0 : prod hreal hreal, exists y1 : prod hreal hreal, ((treal_le y0 y1) = x0) /\ ((treal_eq x1 y0) /\ (treal_eq x2 y1)).
Definition term7 (x0 : prod hreal hreal) := exists y0 : prod hreal hreal, (treal_eq x0) = (treal_eq y0).
Definition term50 (a0 : Type') (x0 : a0) := (fun y0 : a0 => (@ε a0 (fun y1 : a0 => y0 = y1)) = y0) x0.
