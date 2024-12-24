Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term28 := @eq Prop (forall y0 : prod hreal hreal, forall y1 : prod hreal hreal, (treal_mul y0 y1) = (treal_mul y1 y0)).
Definition term26 := forall y0 : prod hreal hreal, forall y1 : prod hreal hreal, (treal_mul y0 y1) = (treal_mul y1 y0).
Definition term58 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := @pair hreal hreal (hreal_add (hreal_mul x0 x2) (hreal_mul x3 x1)) (hreal_add (hreal_mul x0 x1) (hreal_mul x2 x3)).
Definition term14 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := @pair hreal hreal (hreal_add (hreal_mul x0 x3) (hreal_mul x2 x1)) (hreal_add (hreal_mul x0 x1) (hreal_mul x2 x3)).
Definition term52 (x0 : hreal) (x1 : hreal) := fun y0 : hreal => forall y1 : hreal, (fun y2 : prod hreal hreal => (treal_mul (@pair hreal hreal x0 x1) y2) = (treal_mul y2 (@pair hreal hreal x0 x1))) (@pair hreal hreal y0 y1).
Definition term35 := fun y0 : hreal => forall y1 : hreal, (fun y2 : prod hreal hreal => forall y3 : prod hreal hreal, (treal_mul y2 y3) = (treal_mul y3 y2)) (@pair hreal hreal y0 y1).
Definition term50 (x0 : hreal) (x1 : hreal) (x2 : hreal) := forall y0 : hreal, (fun y1 : prod hreal hreal => (treal_mul (@pair hreal hreal x0 x1) y1) = (treal_mul y1 (@pair hreal hreal x0 x1))) (@pair hreal hreal x2 y0).
Definition term16 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := forall y0 : prod a1 a0, x0 y0.
Definition term30 (x0 : hreal) (x1 : hreal) := forall y0 : prod hreal hreal, (treal_mul (@pair hreal hreal x0 x1) y0) = (treal_mul y0 (@pair hreal hreal x0 x1)).
Definition term10 (x0 : hreal) (x1 : hreal) (x2 : hreal) := (fun y0 : hreal => forall y1 : hreal, (treal_mul (@pair hreal hreal x0 y0) (@pair hreal hreal y1 x1)) = (@pair hreal hreal (hreal_add (hreal_mul x0 y1) (hreal_mul y0 x1)) (hreal_add (hreal_mul x0 x1) (hreal_mul y0 y1)))) x2.
Definition term63 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term25 := fun y0 : prod hreal hreal => (fun y1 : prod hreal hreal => forall y2 : prod hreal hreal, (treal_mul y1 y2) = (treal_mul y2 y1)) y0.
Definition term55 (x0 : hreal) (x1 : hreal) := hreal_add (hreal_mul x0 x1).
Definition term24 (x0 : prod hreal hreal) := forall y0 : prod hreal hreal, (treal_mul x0 y0) = (treal_mul y0 x0).
Definition term56 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := hreal_add (hreal_mul x0 x1) (hreal_mul x2 x3).
Definition term49 (x0 : hreal) (x1 : hreal) (x2 : hreal) := fun y0 : hreal => (treal_mul (@pair hreal hreal x1 x2) (@pair hreal hreal x0 y0)) = (treal_mul (@pair hreal hreal x0 y0) (@pair hreal hreal x1 x2)).
Definition term62 := forall y0 : hreal, True.
Definition term33 (x0 : hreal) := forall y0 : hreal, (fun y1 : prod hreal hreal => forall y2 : prod hreal hreal, (treal_mul y1 y2) = (treal_mul y2 y1)) (@pair hreal hreal x0 y0).
Definition term45 (x0 : hreal) (x1 : hreal) := @eq Prop (forall y0 : prod hreal hreal, (fun y1 : prod hreal hreal => (treal_mul (@pair hreal hreal x0 x1) y1) = (treal_mul y1 (@pair hreal hreal x0 x1))) y0).
Definition term27 := @eq Prop (forall y0 : prod hreal hreal, (fun y1 : prod hreal hreal => forall y2 : prod hreal hreal, (treal_mul y1 y2) = (treal_mul y2 y1)) y0).
Definition term31 (x0 : hreal) := fun y0 : hreal => (fun y1 : prod hreal hreal => forall y2 : prod hreal hreal, (treal_mul y1 y2) = (treal_mul y2 y1)) (@pair hreal hreal x0 y0).
Definition term8 (x0 : hreal) (x1 : hreal) := (fun y0 : hreal => forall y1 : hreal, forall y2 : hreal, (treal_mul (@pair hreal hreal x0 y1) (@pair hreal hreal y2 y0)) = (@pair hreal hreal (hreal_add (hreal_mul x0 y2) (hreal_mul y1 y0)) (hreal_add (hreal_mul x0 y0) (hreal_mul y1 y2)))) x1.
Definition term12 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := (fun y0 : hreal => (treal_mul (@pair hreal hreal x0 x2) (@pair hreal hreal y0 x1)) = (@pair hreal hreal (hreal_add (hreal_mul x0 y0) (hreal_mul x2 x1)) (hreal_add (hreal_mul x0 x1) (hreal_mul x2 y0)))) x3.
Definition term41 (x0 : hreal) (x1 : hreal) (x2 : prod hreal hreal) := (fun y0 : prod hreal hreal => (treal_mul (@pair hreal hreal x0 x1) y0) = (treal_mul y0 (@pair hreal hreal x0 x1))) x2.
Definition term22 := fun y0 : prod hreal hreal => forall y1 : prod hreal hreal, (treal_mul y0 y1) = (treal_mul y1 y0).
Definition term43 (x0 : prod hreal hreal) (x1 : hreal) (x2 : hreal) := treal_mul x0 (@pair hreal hreal x1 x2).
Definition term59 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := @eq (prod hreal hreal) (treal_mul (@pair hreal hreal x0 x1) (@pair hreal hreal x2 x3)).
Definition term54 (x0 : hreal) (x1 : hreal) := forall y0 : hreal, forall y1 : hreal, (treal_mul (@pair hreal hreal x0 x1) (@pair hreal hreal y0 y1)) = (treal_mul (@pair hreal hreal y0 y1) (@pair hreal hreal x0 x1)).
Definition term39 (x0 : hreal) (x1 : hreal) := forall y0 : hreal, forall y1 : hreal, (fun y2 : prod hreal hreal => (treal_mul (@pair hreal hreal x0 x1) y2) = (treal_mul y2 (@pair hreal hreal x0 x1))) (@pair hreal hreal y0 y1).
Definition term37 := forall y0 : hreal, forall y1 : hreal, forall y2 : prod hreal hreal, (treal_mul (@pair hreal hreal y0 y1) y2) = (treal_mul y2 (@pair hreal hreal y0 y1)).
Definition term34 (x0 : hreal) := forall y0 : hreal, forall y1 : prod hreal hreal, (treal_mul (@pair hreal hreal x0 y0) y1) = (treal_mul y1 (@pair hreal hreal x0 y0)).
Definition term21 := forall y0 : hreal, forall y1 : hreal, (fun y2 : prod hreal hreal => forall y3 : prod hreal hreal, (treal_mul y2 y3) = (treal_mul y3 y2)) (@pair hreal hreal y0 y1).
Definition term19 (x0 : type1233) := forall y0 : hreal, forall y1 : hreal, x0 (@pair hreal hreal y0 y1).
Definition term9 (x0 : hreal) (x1 : hreal) := forall y0 : hreal, forall y1 : hreal, (treal_mul (@pair hreal hreal x0 y0) (@pair hreal hreal y1 x1)) = (@pair hreal hreal (hreal_add (hreal_mul x0 y1) (hreal_mul y0 x1)) (hreal_add (hreal_mul x0 x1) (hreal_mul y0 y1))).
Definition term7 (x0 : hreal) := forall y0 : hreal, forall y1 : hreal, forall y2 : hreal, (treal_mul (@pair hreal hreal x0 y1) (@pair hreal hreal y2 y0)) = (@pair hreal hreal (hreal_add (hreal_mul x0 y2) (hreal_mul y1 y0)) (hreal_add (hreal_mul x0 y0) (hreal_mul y1 y2))).
Definition term46 (x0 : hreal) (x1 : hreal) := @eq Prop (forall y0 : prod hreal hreal, (treal_mul (@pair hreal hreal x0 x1) y0) = (treal_mul y0 (@pair hreal hreal x0 x1))).
Definition term11 (x0 : hreal) (x1 : hreal) (x2 : hreal) := forall y0 : hreal, (treal_mul (@pair hreal hreal x0 x2) (@pair hreal hreal y0 x1)) = (@pair hreal hreal (hreal_add (hreal_mul x0 y0) (hreal_mul x2 x1)) (hreal_add (hreal_mul x0 x1) (hreal_mul x2 y0))).
Definition term57 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := @pair hreal hreal (hreal_add (hreal_mul x0 x1) (hreal_mul x2 x3)).
Definition term60 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := @eq (prod hreal hreal) (@pair hreal hreal (hreal_add (hreal_mul x0 x2) (hreal_mul x3 x1)) (hreal_add (hreal_mul x0 x1) (hreal_mul x2 x3))).
Definition term36 := fun y0 : hreal => forall y1 : hreal, forall y2 : prod hreal hreal, (treal_mul (@pair hreal hreal y0 y1) y2) = (treal_mul y2 (@pair hreal hreal y0 y1)).
Definition term18 (x0 : type1233) := forall y0 : prod hreal hreal, x0 y0.
Definition term64 (x0 : Prop) := forall y0 : hreal, x0.
Definition term53 (x0 : hreal) (x1 : hreal) := fun y0 : hreal => forall y1 : hreal, (treal_mul (@pair hreal hreal x0 x1) (@pair hreal hreal y0 y1)) = (treal_mul (@pair hreal hreal y0 y1) (@pair hreal hreal x0 x1)).
Definition term23 (x0 : prod hreal hreal) := (fun y0 : prod hreal hreal => forall y1 : prod hreal hreal, (treal_mul y0 y1) = (treal_mul y1 y0)) x0.
Definition term17 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := forall y0 : a1, forall y1 : a0, x0 (@pair a1 a0 y0 y1).
Definition term40 (x0 : hreal) (x1 : hreal) := fun y0 : prod hreal hreal => (treal_mul (@pair hreal hreal x0 x1) y0) = (treal_mul y0 (@pair hreal hreal x0 x1)).
Definition term5 (x0 : hreal) (x1 : hreal) := (fun y0 : hreal => (hreal_mul x0 y0) = (hreal_mul y0 x0)) x1.
Definition term2 (x0 : hreal) (x1 : hreal) := (fun y0 : hreal => (hreal_add x0 y0) = (hreal_add y0 x0)) x1.
Definition term3 (x0 : hreal) := (fun y0 : hreal => forall y1 : hreal, (hreal_mul y0 y1) = (hreal_mul y1 y0)) x0.
Definition term0 (x0 : hreal) := (fun y0 : hreal => forall y1 : hreal, (hreal_add y0 y1) = (hreal_add y1 y0)) x0.
Definition term38 (x0 : hreal) (x1 : hreal) := forall y0 : prod hreal hreal, (fun y1 : prod hreal hreal => (treal_mul (@pair hreal hreal x0 x1) y1) = (treal_mul y1 (@pair hreal hreal x0 x1))) y0.
Definition term13 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := treal_mul (@pair hreal hreal x0 x1) (@pair hreal hreal x2 x3).
Definition term29 (x0 : hreal) (x1 : hreal) := (fun y0 : prod hreal hreal => forall y1 : prod hreal hreal, (treal_mul y0 y1) = (treal_mul y1 y0)) (@pair hreal hreal x0 x1).
Definition term20 := forall y0 : prod hreal hreal, (fun y1 : prod hreal hreal => forall y2 : prod hreal hreal, (treal_mul y1 y2) = (treal_mul y2 y1)) y0.
Definition term51 (x0 : hreal) (x1 : hreal) (x2 : hreal) := forall y0 : hreal, (treal_mul (@pair hreal hreal x1 x2) (@pair hreal hreal x0 y0)) = (treal_mul (@pair hreal hreal x0 y0) (@pair hreal hreal x1 x2)).
Definition term61 := fun y0 : hreal => True.
Definition term4 (x0 : hreal) := forall y0 : hreal, (hreal_mul x0 y0) = (hreal_mul y0 x0).
Definition term1 (x0 : hreal) := forall y0 : hreal, (hreal_add x0 y0) = (hreal_add y0 x0).
Definition term32 (x0 : hreal) := fun y0 : hreal => forall y1 : prod hreal hreal, (treal_mul (@pair hreal hreal x0 y0) y1) = (treal_mul y1 (@pair hreal hreal x0 y0)).
Definition term48 (x0 : hreal) (x1 : hreal) (x2 : hreal) := fun y0 : hreal => (fun y1 : prod hreal hreal => (treal_mul (@pair hreal hreal x0 x1) y1) = (treal_mul y1 (@pair hreal hreal x0 x1))) (@pair hreal hreal x2 y0).
Definition term44 (x0 : hreal) (x1 : hreal) := fun y0 : prod hreal hreal => (fun y1 : prod hreal hreal => (treal_mul (@pair hreal hreal x0 x1) y1) = (treal_mul y1 (@pair hreal hreal x0 x1))) y0.
Definition term15 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := (fun y0 : type1223 a0 a1 => (forall y1 : prod a1 a0, y0 y1) = (forall y1 : a1, forall y2 : a0, y0 (@pair a1 a0 y1 y2))) x0.
Definition term6 (x0 : hreal) := (fun y0 : hreal => forall y1 : hreal, forall y2 : hreal, forall y3 : hreal, (treal_mul (@pair hreal hreal y0 y2) (@pair hreal hreal y3 y1)) = (@pair hreal hreal (hreal_add (hreal_mul y0 y3) (hreal_mul y2 y1)) (hreal_add (hreal_mul y0 y1) (hreal_mul y2 y3)))) x0.
Definition term42 (x0 : hreal) (x1 : hreal) (x2 : prod hreal hreal) := treal_mul (@pair hreal hreal x0 x1) x2.
Definition term47 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := (fun y0 : prod hreal hreal => (treal_mul (@pair hreal hreal x0 x1) y0) = (treal_mul y0 (@pair hreal hreal x0 x1))) (@pair hreal hreal x2 x3).
