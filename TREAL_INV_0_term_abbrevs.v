Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term18 := treal_inv (@pair hreal hreal (hreal_of_num (NUMERAL 0)) (hreal_of_num (NUMERAL 0))).
Definition term20 := hreal_of_num (NUMERAL 0).
Definition term8 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := (fun y0 : hreal => (treal_eq (@pair hreal hreal x0 y0) (@pair hreal hreal x2 x1)) = ((hreal_add x0 x1) = (hreal_add x2 y0))) x3.
Definition term6 (x0 : hreal) (x1 : hreal) (x2 : hreal) := (fun y0 : hreal => forall y1 : hreal, (treal_eq (@pair hreal hreal x0 y1) (@pair hreal hreal y0 x1)) = ((hreal_add x0 x1) = (hreal_add y0 y1))) x2.
Definition term11 (x0 : hreal) := forall y0 : hreal, (treal_inv (@pair hreal hreal y0 x0)) = (@COND (prod hreal hreal) (y0 = x0) (@pair hreal hreal (hreal_of_num (NUMERAL 0)) (hreal_of_num (NUMERAL 0))) (@COND (prod hreal hreal) (hreal_le x0 y0) (@pair hreal hreal (hreal_inv (@ε hreal (fun y1 : hreal => y0 = (hreal_add x0 y1)))) (hreal_of_num (NUMERAL 0))) (@pair hreal hreal (hreal_of_num (NUMERAL 0)) (hreal_inv (@ε hreal (fun y1 : hreal => x0 = (hreal_add y0 y1))))))).
Definition term16 := @pair hreal hreal (hreal_of_num (NUMERAL 0)) (hreal_of_num (NUMERAL 0)).
Definition term23 := @COND (prod hreal hreal) (hreal_le (hreal_of_num (NUMERAL 0)) (hreal_of_num (NUMERAL 0))) (@pair hreal hreal (hreal_inv (@ε hreal (fun y0 : hreal => (hreal_of_num (NUMERAL 0)) = (hreal_add (hreal_of_num (NUMERAL 0)) y0)))) (hreal_of_num (NUMERAL 0))) (@pair hreal hreal (hreal_of_num (NUMERAL 0)) (hreal_inv (@ε hreal (fun y0 : hreal => (hreal_of_num (NUMERAL 0)) = (hreal_add (hreal_of_num (NUMERAL 0)) y0))))).
Definition term19 := @COND (prod hreal hreal) ((hreal_of_num (NUMERAL 0)) = (hreal_of_num (NUMERAL 0))) (@pair hreal hreal (hreal_of_num (NUMERAL 0)) (hreal_of_num (NUMERAL 0))) (@COND (prod hreal hreal) (hreal_le (hreal_of_num (NUMERAL 0)) (hreal_of_num (NUMERAL 0))) (@pair hreal hreal (hreal_inv (@ε hreal (fun y0 : hreal => (hreal_of_num (NUMERAL 0)) = (hreal_add (hreal_of_num (NUMERAL 0)) y0)))) (hreal_of_num (NUMERAL 0))) (@pair hreal hreal (hreal_of_num (NUMERAL 0)) (hreal_inv (@ε hreal (fun y0 : hreal => (hreal_of_num (NUMERAL 0)) = (hreal_add (hreal_of_num (NUMERAL 0)) y0)))))).
Definition term4 (x0 : hreal) (x1 : hreal) := (fun y0 : hreal => forall y1 : hreal, forall y2 : hreal, (treal_eq (@pair hreal hreal x0 y2) (@pair hreal hreal y1 y0)) = ((hreal_add x0 y0) = (hreal_add y1 y2))) x1.
Definition term22 (x0 : hreal) (x1 : prod hreal hreal) (x2 : prod hreal hreal) := @COND (prod hreal hreal) (x0 = x0) x1 x2.
Definition term17 := treal_inv (treal_of_num (NUMERAL 0)).
Definition term15 := treal_of_num (NUMERAL 0).
Definition term12 (x0 : hreal) (x1 : hreal) := (fun y0 : hreal => (treal_inv (@pair hreal hreal y0 x0)) = (@COND (prod hreal hreal) (y0 = x0) (@pair hreal hreal (hreal_of_num (NUMERAL 0)) (hreal_of_num (NUMERAL 0))) (@COND (prod hreal hreal) (hreal_le x0 y0) (@pair hreal hreal (hreal_inv (@ε hreal (fun y1 : hreal => y0 = (hreal_add x0 y1)))) (hreal_of_num (NUMERAL 0))) (@pair hreal hreal (hreal_of_num (NUMERAL 0)) (hreal_inv (@ε hreal (fun y1 : hreal => x0 = (hreal_add y0 y1)))))))) x1.
Definition term28 := hreal_add (hreal_of_num (NUMERAL 0)) (hreal_of_num (NUMERAL 0)).
Definition term21 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0) (x2 : a0) := @COND a0 (x0 = x0) x1 x2.
Definition term27 := treal_eq (@pair hreal hreal (hreal_of_num (NUMERAL 0)) (hreal_of_num (NUMERAL 0))) (@pair hreal hreal (hreal_of_num (NUMERAL 0)) (hreal_of_num (NUMERAL 0))).
Definition term5 (x0 : hreal) (x1 : hreal) := forall y0 : hreal, forall y1 : hreal, (treal_eq (@pair hreal hreal x0 y1) (@pair hreal hreal y0 x1)) = ((hreal_add x0 x1) = (hreal_add y0 y1)).
Definition term3 (x0 : hreal) := forall y0 : hreal, forall y1 : hreal, forall y2 : hreal, (treal_eq (@pair hreal hreal x0 y2) (@pair hreal hreal y1 y0)) = ((hreal_add x0 y0) = (hreal_add y1 y2)).
Definition term1 (x0 : nat) := @pair hreal hreal (hreal_of_num x0) (hreal_of_num (NUMERAL 0)).
Definition term13 (x0 : hreal) (x1 : hreal) := treal_inv (@pair hreal hreal x0 x1).
Definition term26 := treal_eq (treal_inv (treal_of_num (NUMERAL 0))) (treal_of_num (NUMERAL 0)).
Definition term25 := treal_eq (@pair hreal hreal (hreal_of_num (NUMERAL 0)) (hreal_of_num (NUMERAL 0))).
Definition term10 (x0 : hreal) := (fun y0 : hreal => forall y1 : hreal, (treal_inv (@pair hreal hreal y1 y0)) = (@COND (prod hreal hreal) (y1 = y0) (@pair hreal hreal (hreal_of_num (NUMERAL 0)) (hreal_of_num (NUMERAL 0))) (@COND (prod hreal hreal) (hreal_le y0 y1) (@pair hreal hreal (hreal_inv (@ε hreal (fun y2 : hreal => y1 = (hreal_add y0 y2)))) (hreal_of_num (NUMERAL 0))) (@pair hreal hreal (hreal_of_num (NUMERAL 0)) (hreal_inv (@ε hreal (fun y2 : hreal => y0 = (hreal_add y1 y2)))))))) x0.
Definition term0 (x0 : nat) := (fun y0 : nat => (treal_of_num y0) = (@pair hreal hreal (hreal_of_num y0) (hreal_of_num (NUMERAL 0)))) x0.
Definition term24 := treal_eq (treal_inv (treal_of_num (NUMERAL 0))).
Definition term7 (x0 : hreal) (x1 : hreal) (x2 : hreal) := forall y0 : hreal, (treal_eq (@pair hreal hreal x0 y0) (@pair hreal hreal x2 x1)) = ((hreal_add x0 x1) = (hreal_add x2 y0)).
Definition term9 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := treal_eq (@pair hreal hreal x0 x1) (@pair hreal hreal x2 x3).
Definition term14 (x0 : hreal) (x1 : hreal) := @COND (prod hreal hreal) (x1 = x0) (@pair hreal hreal (hreal_of_num (NUMERAL 0)) (hreal_of_num (NUMERAL 0))) (@COND (prod hreal hreal) (hreal_le x0 x1) (@pair hreal hreal (hreal_inv (@ε hreal (fun y0 : hreal => x1 = (hreal_add x0 y0)))) (hreal_of_num (NUMERAL 0))) (@pair hreal hreal (hreal_of_num (NUMERAL 0)) (hreal_inv (@ε hreal (fun y0 : hreal => x0 = (hreal_add x1 y0)))))).
Definition term2 (x0 : hreal) := (fun y0 : hreal => forall y1 : hreal, forall y2 : hreal, forall y3 : hreal, (treal_eq (@pair hreal hreal y0 y3) (@pair hreal hreal y2 y1)) = ((hreal_add y0 y1) = (hreal_add y2 y3))) x0.
