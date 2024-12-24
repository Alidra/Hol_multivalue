Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term6 := hreal_of_num (NUMERAL 0).
Definition term23 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := @pair hreal hreal (hreal_add (hreal_mul x0 x3) (hreal_mul x2 x1)) (hreal_add (hreal_mul x0 x1) (hreal_mul x2 x3)).
Definition term46 := fun y0 : hreal => forall y1 : hreal, (fun y2 : prod hreal hreal => treal_eq (treal_mul (treal_of_num (NUMERAL (BIT1 0))) y2) y2) (@pair hreal hreal y0 y1).
Definition term36 := fun y0 : prod hreal hreal => (fun y1 : prod hreal hreal => treal_eq (treal_mul (treal_of_num (NUMERAL (BIT1 0))) y1) y1) y0.
Definition term47 := fun y0 : hreal => forall y1 : hreal, treal_eq (treal_mul (treal_of_num (NUMERAL (BIT1 0))) (@pair hreal hreal y0 y1)) (@pair hreal hreal y0 y1).
Definition term13 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := (fun y0 : hreal => (treal_eq (@pair hreal hreal x0 y0) (@pair hreal hreal x2 x1)) = ((hreal_add x0 x1) = (hreal_add x2 y0))) x3.
Definition term3 (x0 : hreal) := hreal_mul (hreal_of_num (NUMERAL (BIT1 0))) x0.
Definition term35 (x0 : prod hreal hreal) := treal_eq (treal_mul (treal_of_num (NUMERAL (BIT1 0))) x0) x0.
Definition term37 := forall y0 : prod hreal hreal, treal_eq (treal_mul (treal_of_num (NUMERAL (BIT1 0))) y0) y0.
Definition term27 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := forall y0 : prod a1 a0, x0 y0.
Definition term2 (x0 : hreal) := (fun y0 : hreal => (hreal_mul (hreal_of_num (NUMERAL (BIT1 0))) y0) = y0) x0.
Definition term57 := hreal_of_num (NUMERAL (BIT1 0)).
Definition term19 (x0 : hreal) (x1 : hreal) (x2 : hreal) := (fun y0 : hreal => forall y1 : hreal, (treal_mul (@pair hreal hreal x0 y0) (@pair hreal hreal y1 x1)) = (@pair hreal hreal (hreal_add (hreal_mul x0 y1) (hreal_mul y0 x1)) (hreal_add (hreal_mul x0 x1) (hreal_mul y0 y1)))) x2.
Definition term11 (x0 : hreal) (x1 : hreal) (x2 : hreal) := (fun y0 : hreal => forall y1 : hreal, (treal_eq (@pair hreal hreal x0 y1) (@pair hreal hreal y0 x1)) = ((hreal_add x0 x1) = (hreal_add y0 y1))) x2.
Definition term74 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term43 (x0 : hreal) := fun y0 : hreal => treal_eq (treal_mul (treal_of_num (NUMERAL (BIT1 0))) (@pair hreal hreal x0 y0)) (@pair hreal hreal x0 y0).
Definition term54 (x0 : hreal) (x1 : hreal) := treal_mul (treal_of_num (NUMERAL (BIT1 0))) (@pair hreal hreal x0 x1).
Definition term45 (x0 : hreal) := forall y0 : hreal, treal_eq (treal_mul (treal_of_num (NUMERAL (BIT1 0))) (@pair hreal hreal x0 y0)) (@pair hreal hreal x0 y0).
Definition term4 (x0 : hreal) := (fun y0 : hreal => (hreal_mul (hreal_of_num (NUMERAL 0)) y0) = (hreal_of_num (NUMERAL 0))) x0.
Definition term63 (x0 : hreal) (x1 : hreal) := hreal_add (hreal_mul (hreal_of_num (NUMERAL (BIT1 0))) x0) (hreal_mul (hreal_of_num (NUMERAL 0)) x1).
Definition term44 (x0 : hreal) := forall y0 : hreal, (fun y1 : prod hreal hreal => treal_eq (treal_mul (treal_of_num (NUMERAL (BIT1 0))) y1) y1) (@pair hreal hreal x0 y0).
Definition term52 := treal_mul (treal_of_num (NUMERAL (BIT1 0))).
Definition term73 := forall y0 : hreal, True.
Definition term34 (x0 : prod hreal hreal) := (fun y0 : prod hreal hreal => treal_eq (treal_mul (treal_of_num (NUMERAL (BIT1 0))) y0) y0) x0.
Definition term53 := treal_mul (@pair hreal hreal (hreal_of_num (NUMERAL (BIT1 0))) (hreal_of_num (NUMERAL 0))).
Definition term38 := @eq Prop (forall y0 : prod hreal hreal, (fun y1 : prod hreal hreal => treal_eq (treal_mul (treal_of_num (NUMERAL (BIT1 0))) y1) y1) y0).
Definition term40 (x0 : hreal) (x1 : hreal) := (fun y0 : prod hreal hreal => treal_eq (treal_mul (treal_of_num (NUMERAL (BIT1 0))) y0) y0) (@pair hreal hreal x0 x1).
Definition term17 (x0 : hreal) (x1 : hreal) := (fun y0 : hreal => forall y1 : hreal, forall y2 : hreal, (treal_mul (@pair hreal hreal x0 y1) (@pair hreal hreal y2 y0)) = (@pair hreal hreal (hreal_add (hreal_mul x0 y2) (hreal_mul y1 y0)) (hreal_add (hreal_mul x0 y0) (hreal_mul y1 y2)))) x1.
Definition term9 (x0 : hreal) (x1 : hreal) := (fun y0 : hreal => forall y1 : hreal, forall y2 : hreal, (treal_eq (@pair hreal hreal x0 y2) (@pair hreal hreal y1 y0)) = ((hreal_add x0 y0) = (hreal_add y1 y2))) x1.
Definition term59 (x0 : hreal) (x1 : hreal) := treal_eq (@pair hreal hreal (hreal_add (hreal_mul (hreal_of_num (NUMERAL (BIT1 0))) x1) (hreal_mul (hreal_of_num (NUMERAL 0)) x0)) (hreal_add (hreal_mul (hreal_of_num (NUMERAL (BIT1 0))) x0) (hreal_mul (hreal_of_num (NUMERAL 0)) x1))).
Definition term31 := forall y0 : prod hreal hreal, (fun y1 : prod hreal hreal => treal_eq (treal_mul (treal_of_num (NUMERAL (BIT1 0))) y1) y1) y0.
Definition term69 (x0 : hreal) (x1 : hreal) := hreal_add (hreal_add (hreal_mul (hreal_of_num (NUMERAL (BIT1 0))) x0) (hreal_mul (hreal_of_num (NUMERAL 0)) x1)).
Definition term68 (x0 : hreal) := hreal_add (hreal_mul (hreal_of_num (NUMERAL (BIT1 0))) x0).
Definition term21 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := (fun y0 : hreal => (treal_mul (@pair hreal hreal x0 x2) (@pair hreal hreal y0 x1)) = (@pair hreal hreal (hreal_add (hreal_mul x0 y0) (hreal_mul x2 x1)) (hreal_add (hreal_mul x0 x1) (hreal_mul x2 y0)))) x3.
Definition term33 := fun y0 : prod hreal hreal => treal_eq (treal_mul (treal_of_num (NUMERAL (BIT1 0))) y0) y0.
Definition term64 (x0 : hreal) := fun y0 : hreal => (hreal_add (hreal_add (hreal_mul (hreal_of_num (NUMERAL (BIT1 0))) x0) (hreal_mul (hreal_of_num (NUMERAL 0)) y0)) y0) = (hreal_add x0 (hreal_add (hreal_mul (hreal_of_num (NUMERAL (BIT1 0))) y0) (hreal_mul (hreal_of_num (NUMERAL 0)) x0))).
Definition term1 (x0 : hreal) := hreal_add x0 (hreal_of_num (NUMERAL 0)).
Definition term41 (x0 : hreal) (x1 : hreal) := treal_eq (treal_mul (treal_of_num (NUMERAL (BIT1 0))) (@pair hreal hreal x0 x1)) (@pair hreal hreal x0 x1).
Definition term67 := forall y0 : hreal, forall y1 : hreal, (hreal_add (hreal_add (hreal_mul (hreal_of_num (NUMERAL (BIT1 0))) y0) (hreal_mul (hreal_of_num (NUMERAL 0)) y1)) y1) = (hreal_add y0 (hreal_add (hreal_mul (hreal_of_num (NUMERAL (BIT1 0))) y1) (hreal_mul (hreal_of_num (NUMERAL 0)) y0))).
Definition term48 := forall y0 : hreal, forall y1 : hreal, treal_eq (treal_mul (treal_of_num (NUMERAL (BIT1 0))) (@pair hreal hreal y0 y1)) (@pair hreal hreal y0 y1).
Definition term32 := forall y0 : hreal, forall y1 : hreal, (fun y2 : prod hreal hreal => treal_eq (treal_mul (treal_of_num (NUMERAL (BIT1 0))) y2) y2) (@pair hreal hreal y0 y1).
Definition term30 (x0 : type1233) := forall y0 : hreal, forall y1 : hreal, x0 (@pair hreal hreal y0 y1).
Definition term18 (x0 : hreal) (x1 : hreal) := forall y0 : hreal, forall y1 : hreal, (treal_mul (@pair hreal hreal x0 y0) (@pair hreal hreal y1 x1)) = (@pair hreal hreal (hreal_add (hreal_mul x0 y1) (hreal_mul y0 x1)) (hreal_add (hreal_mul x0 x1) (hreal_mul y0 y1))).
Definition term16 (x0 : hreal) := forall y0 : hreal, forall y1 : hreal, forall y2 : hreal, (treal_mul (@pair hreal hreal x0 y1) (@pair hreal hreal y2 y0)) = (@pair hreal hreal (hreal_add (hreal_mul x0 y2) (hreal_mul y1 y0)) (hreal_add (hreal_mul x0 y0) (hreal_mul y1 y2))).
Definition term10 (x0 : hreal) (x1 : hreal) := forall y0 : hreal, forall y1 : hreal, (treal_eq (@pair hreal hreal x0 y1) (@pair hreal hreal y0 x1)) = ((hreal_add x0 x1) = (hreal_add y0 y1)).
Definition term8 (x0 : hreal) := forall y0 : hreal, forall y1 : hreal, forall y2 : hreal, (treal_eq (@pair hreal hreal x0 y2) (@pair hreal hreal y1 y0)) = ((hreal_add x0 y0) = (hreal_add y1 y2)).
Definition term25 (x0 : nat) := @pair hreal hreal (hreal_of_num x0) (hreal_of_num (NUMERAL 0)).
Definition term56 (x0 : hreal) (x1 : hreal) := @pair hreal hreal (hreal_add (hreal_mul (hreal_of_num (NUMERAL (BIT1 0))) x1) (hreal_mul (hreal_of_num (NUMERAL 0)) x0)) (hreal_add (hreal_mul (hreal_of_num (NUMERAL (BIT1 0))) x0) (hreal_mul (hreal_of_num (NUMERAL 0)) x1)).
Definition term60 (x0 : hreal) (x1 : hreal) := treal_eq (@pair hreal hreal (hreal_add (hreal_mul (hreal_of_num (NUMERAL (BIT1 0))) x0) (hreal_mul (hreal_of_num (NUMERAL 0)) x1)) (hreal_add (hreal_mul (hreal_of_num (NUMERAL (BIT1 0))) x1) (hreal_mul (hreal_of_num (NUMERAL 0)) x0))) (@pair hreal hreal x0 x1).
Definition term61 (x0 : hreal) (x1 : hreal) := hreal_add (hreal_add (hreal_mul (hreal_of_num (NUMERAL (BIT1 0))) x0) (hreal_mul (hreal_of_num (NUMERAL 0)) x1)) x1.
Definition term55 (x0 : hreal) (x1 : hreal) := treal_mul (@pair hreal hreal (hreal_of_num (NUMERAL (BIT1 0))) (hreal_of_num (NUMERAL 0))) (@pair hreal hreal x0 x1).
Definition term20 (x0 : hreal) (x1 : hreal) (x2 : hreal) := forall y0 : hreal, (treal_mul (@pair hreal hreal x0 x2) (@pair hreal hreal y0 x1)) = (@pair hreal hreal (hreal_add (hreal_mul x0 y0) (hreal_mul x2 x1)) (hreal_add (hreal_mul x0 x1) (hreal_mul x2 y0))).
Definition term0 (x0 : hreal) := (fun y0 : hreal => (hreal_add y0 (hreal_of_num (NUMERAL 0))) = y0) x0.
Definition term29 (x0 : type1233) := forall y0 : prod hreal hreal, x0 y0.
Definition term75 (x0 : Prop) := forall y0 : hreal, x0.
Definition term66 := fun y0 : hreal => forall y1 : hreal, (hreal_add (hreal_add (hreal_mul (hreal_of_num (NUMERAL (BIT1 0))) y0) (hreal_mul (hreal_of_num (NUMERAL 0)) y1)) y1) = (hreal_add y0 (hreal_add (hreal_mul (hreal_of_num (NUMERAL (BIT1 0))) y1) (hreal_mul (hreal_of_num (NUMERAL 0)) y0))).
Definition term39 := @eq Prop (forall y0 : prod hreal hreal, treal_eq (treal_mul (treal_of_num (NUMERAL (BIT1 0))) y0) y0).
Definition term28 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := forall y0 : a1, forall y1 : a0, x0 (@pair a1 a0 y0 y1).
Definition term58 (x0 : hreal) (x1 : hreal) := treal_eq (treal_mul (treal_of_num (NUMERAL (BIT1 0))) (@pair hreal hreal x0 x1)).
Definition term22 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := treal_mul (@pair hreal hreal x0 x1) (@pair hreal hreal x2 x3).
Definition term62 (x0 : hreal) (x1 : hreal) := hreal_add x1 (hreal_add (hreal_mul (hreal_of_num (NUMERAL (BIT1 0))) x0) (hreal_mul (hreal_of_num (NUMERAL 0)) x1)).
Definition term5 (x0 : hreal) := hreal_mul (hreal_of_num (NUMERAL 0)) x0.
Definition term71 (x0 : hreal) (x1 : hreal) := @eq hreal (hreal_add x0 x1).
Definition term24 (x0 : nat) := (fun y0 : nat => (treal_of_num y0) = (@pair hreal hreal (hreal_of_num y0) (hreal_of_num (NUMERAL 0)))) x0.
Definition term65 (x0 : hreal) := forall y0 : hreal, (hreal_add (hreal_add (hreal_mul (hreal_of_num (NUMERAL (BIT1 0))) x0) (hreal_mul (hreal_of_num (NUMERAL 0)) y0)) y0) = (hreal_add x0 (hreal_add (hreal_mul (hreal_of_num (NUMERAL (BIT1 0))) y0) (hreal_mul (hreal_of_num (NUMERAL 0)) x0))).
Definition term49 := treal_of_num (NUMERAL (BIT1 0)).
Definition term12 (x0 : hreal) (x1 : hreal) (x2 : hreal) := forall y0 : hreal, (treal_eq (@pair hreal hreal x0 y0) (@pair hreal hreal x2 x1)) = ((hreal_add x0 x1) = (hreal_add x2 y0)).
Definition term72 := fun y0 : hreal => True.
Definition term50 := @pair hreal hreal (hreal_of_num (NUMERAL (BIT1 0))) (hreal_of_num (NUMERAL 0)).
Definition term42 (x0 : hreal) := fun y0 : hreal => (fun y1 : prod hreal hreal => treal_eq (treal_mul (treal_of_num (NUMERAL (BIT1 0))) y1) y1) (@pair hreal hreal x0 y0).
Definition term14 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := treal_eq (@pair hreal hreal x0 x1) (@pair hreal hreal x2 x3).
Definition term26 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := (fun y0 : type1223 a0 a1 => (forall y1 : prod a1 a0, y0 y1) = (forall y1 : a1, forall y2 : a0, y0 (@pair a1 a0 y1 y2))) x0.
Definition term51 := NUMERAL (BIT1 0).
Definition term15 (x0 : hreal) := (fun y0 : hreal => forall y1 : hreal, forall y2 : hreal, forall y3 : hreal, (treal_mul (@pair hreal hreal y0 y2) (@pair hreal hreal y3 y1)) = (@pair hreal hreal (hreal_add (hreal_mul y0 y3) (hreal_mul y2 y1)) (hreal_add (hreal_mul y0 y1) (hreal_mul y2 y3)))) x0.
Definition term7 (x0 : hreal) := (fun y0 : hreal => forall y1 : hreal, forall y2 : hreal, forall y3 : hreal, (treal_eq (@pair hreal hreal y0 y3) (@pair hreal hreal y2 y1)) = ((hreal_add y0 y1) = (hreal_add y2 y3))) x0.
Definition term70 (x0 : hreal) (x1 : hreal) := @eq hreal (hreal_add (hreal_add (hreal_mul (hreal_of_num (NUMERAL (BIT1 0))) x0) (hreal_mul (hreal_of_num (NUMERAL 0)) x1)) x1).
