Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term14 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := @fst a0 a1 (@pair a0 a1 x0 x1).
Definition term3 := forall y0 : prod int int, (int_coprime y0) = (exists y1 : int, exists y2 : int, (int_add (int_mul (@fst int int y0) y1) (int_mul (@snd int int y0) y2)) = (int_of_num (NUMERAL (BIT1 0)))).
Definition term18 (x0 : int) := (fun y0 : int => fun y1 : int => exists y2 : int, exists y3 : int, (int_add (int_mul y0 y2) (int_mul y1 y3)) = (int_of_num (NUMERAL (BIT1 0)))) x0.
Definition term22 (x0 : int) := fun y0 : int => exists y1 : int, exists y2 : int, (int_add (int_mul x0 y1) (int_mul y0 y2)) = (int_of_num (NUMERAL (BIT1 0))).
Definition term20 (x0 : int) (x1 : int) := fun y0 : int => exists y1 : int, exists y2 : int, (int_add (int_mul (@fst int int (@pair int int x0 x1)) y1) (int_mul y0 y2)) = (int_of_num (NUMERAL (BIT1 0))).
Definition term7 (a0 : Type') (a1 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a1, (@snd a0 a1 (@pair a0 a1 y0 y1)) = y1) x0.
Definition term12 (a0 : Type') (a1 : Type') (x0 : a0) := forall y0 : a1, (@fst a0 a1 (@pair a0 a1 x0 y0)) = x0.
Definition term26 (x0 : int) (x1 : int) := @eq Prop ((fun y0 : int => exists y1 : int, exists y2 : int, (int_add (int_mul x0 y1) (int_mul y0 y2)) = (int_of_num (NUMERAL (BIT1 0)))) x1).
Definition term29 (x0 : int) := forall y0 : int, (int_coprime (@pair int int x0 y0)) = (exists y1 : int, exists y2 : int, (int_add (int_mul x0 y1) (int_mul y0 y2)) = (int_of_num (NUMERAL (BIT1 0)))).
Definition term11 (a0 : Type') (a1 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a1, (@fst a0 a1 (@pair a0 a1 y0 y1)) = y0) x0.
Definition term4 (x0 : prod int int) := (fun y0 : prod int int => (int_coprime y0) = (exists y1 : int, exists y2 : int, (int_add (int_mul (@fst int int y0) y1) (int_mul (@snd int int y0) y2)) = (int_of_num (NUMERAL (BIT1 0))))) x0.
Definition term1 (x0 : prod int int) := (fun y0 : prod int int => exists y1 : int, exists y2 : int, (int_add (int_mul (@fst int int y0) y1) (int_mul (@snd int int y0) y2)) = (int_of_num (NUMERAL (BIT1 0)))) x0.
Definition term30 := forall y0 : int, forall y1 : int, (int_coprime (@pair int int y0 y1)) = (exists y2 : int, exists y3 : int, (int_add (int_mul y0 y2) (int_mul y1 y3)) = (int_of_num (NUMERAL (BIT1 0)))).
Definition term23 (x0 : int) := @eq (int -> Prop) (fun y0 : int => exists y1 : int, exists y2 : int, (int_add (int_mul x0 y1) (int_mul y0 y2)) = (int_of_num (NUMERAL (BIT1 0)))).
Definition term24 (x0 : int) (x1 : int) := (fun y0 : int => exists y1 : int, exists y2 : int, (int_add (int_mul x0 y1) (int_mul y0 y2)) = (int_of_num (NUMERAL (BIT1 0)))) x1.
Definition term0 := fun y0 : prod int int => exists y1 : int, exists y2 : int, (int_add (int_mul (@fst int int y0) y1) (int_mul (@snd int int y0) y2)) = (int_of_num (NUMERAL (BIT1 0))).
Definition term19 (x0 : int) (x1 : int) := (fun y0 : int => fun y1 : int => exists y2 : int, exists y3 : int, (int_add (int_mul y0 y2) (int_mul y1 y3)) = (int_of_num (NUMERAL (BIT1 0)))) (@fst int int (@pair int int x0 x1)).
Definition term21 (x0 : int) := @eq (int -> Prop) ((fun y0 : int => fun y1 : int => exists y2 : int, exists y3 : int, (int_add (int_mul y0 y2) (int_mul y1 y3)) = (int_of_num (NUMERAL (BIT1 0)))) x0).
Definition term15 (x0 : int) (x1 : int) := @fst int int (@pair int int x0 x1).
Definition term8 (a0 : Type') (a1 : Type') (x0 : a0) := forall y0 : a1, (@snd a0 a1 (@pair a0 a1 x0 y0)) = y0.
Definition term16 (x0 : int) (x1 : int) := @snd int int (@pair int int x0 x1).
Definition term5 (x0 : int) (x1 : int) := int_coprime (@pair int int x0 x1).
Definition term9 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := (fun y0 : a1 => (@snd a0 a1 (@pair a0 a1 x0 y0)) = y0) x1.
Definition term28 (x0 : int) (x1 : int) := @eq Prop (exists y0 : int, exists y1 : int, (int_add (int_mul x0 y0) (int_mul x1 y1)) = (int_of_num (NUMERAL (BIT1 0)))).
Definition term10 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := @snd a0 a1 (@pair a0 a1 x0 x1).
Definition term13 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := (fun y0 : a1 => (@fst a0 a1 (@pair a0 a1 x0 y0)) = x0) x1.
Definition term17 := fun y0 : int => fun y1 : int => exists y2 : int, exists y3 : int, (int_add (int_mul y0 y2) (int_mul y1 y3)) = (int_of_num (NUMERAL (BIT1 0))).
Definition term27 (x0 : int) (x1 : int) := exists y0 : int, exists y1 : int, (int_add (int_mul x0 y0) (int_mul x1 y1)) = (int_of_num (NUMERAL (BIT1 0))).
Definition term6 (x0 : int) (x1 : int) := exists y0 : int, exists y1 : int, (int_add (int_mul (@fst int int (@pair int int x0 x1)) y0) (int_mul (@snd int int (@pair int int x0 x1)) y1)) = (int_of_num (NUMERAL (BIT1 0))).
Definition term2 (x0 : prod int int) := exists y0 : int, exists y1 : int, (int_add (int_mul (@fst int int x0) y0) (int_mul (@snd int int x0) y1)) = (int_of_num (NUMERAL (BIT1 0))).
Definition term25 (x0 : int) (x1 : int) := (fun y0 : int => exists y1 : int, exists y2 : int, (int_add (int_mul (@fst int int (@pair int int x0 x1)) y1) (int_mul y0 y2)) = (int_of_num (NUMERAL (BIT1 0)))) (@snd int int (@pair int int x0 x1)).
