Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term29 (x0 : int) := forall y0 : int, (int_lcm (@pair int int x0 y0)) = (@COND int ((int_mul x0 y0) = (int_of_num (NUMERAL 0))) (int_of_num (NUMERAL 0)) (div (int_abs (int_mul x0 y0)) (int_gcd (@pair int int x0 y0)))).
Definition term14 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := @fst a0 a1 (@pair a0 a1 x0 x1).
Definition term6 (x0 : int) (x1 : int) := @COND int ((int_mul (@fst int int (@pair int int x0 x1)) (@snd int int (@pair int int x0 x1))) = (int_of_num (NUMERAL 0))) (int_of_num (NUMERAL 0)) (div (int_abs (int_mul (@fst int int (@pair int int x0 x1)) (@snd int int (@pair int int x0 x1)))) (int_gcd (@pair int int (@fst int int (@pair int int x0 x1)) (@snd int int (@pair int int x0 x1))))).
Definition term2 (x0 : prod int int) := @COND int ((int_mul (@fst int int x0) (@snd int int x0)) = (int_of_num (NUMERAL 0))) (int_of_num (NUMERAL 0)) (div (int_abs (int_mul (@fst int int x0) (@snd int int x0))) (int_gcd (@pair int int (@fst int int x0) (@snd int int x0)))).
Definition term0 := fun y0 : prod int int => @COND int ((int_mul (@fst int int y0) (@snd int int y0)) = (int_of_num (NUMERAL 0))) (int_of_num (NUMERAL 0)) (div (int_abs (int_mul (@fst int int y0) (@snd int int y0))) (int_gcd (@pair int int (@fst int int y0) (@snd int int y0)))).
Definition term26 (x0 : int) (x1 : int) := @eq int ((fun y0 : int => @COND int ((int_mul x0 y0) = (int_of_num (NUMERAL 0))) (int_of_num (NUMERAL 0)) (div (int_abs (int_mul x0 y0)) (int_gcd (@pair int int x0 y0)))) x1).
Definition term4 (x0 : prod int int) := (fun y0 : prod int int => (int_lcm y0) = (@COND int ((int_mul (@fst int int y0) (@snd int int y0)) = (int_of_num (NUMERAL 0))) (int_of_num (NUMERAL 0)) (div (int_abs (int_mul (@fst int int y0) (@snd int int y0))) (int_gcd (@pair int int (@fst int int y0) (@snd int int y0)))))) x0.
Definition term7 (a0 : Type') (a1 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a1, (@snd a0 a1 (@pair a0 a1 y0 y1)) = y1) x0.
Definition term12 (a0 : Type') (a1 : Type') (x0 : a0) := forall y0 : a1, (@fst a0 a1 (@pair a0 a1 x0 y0)) = x0.
Definition term19 (x0 : int) (x1 : int) := (fun y0 : int => fun y1 : int => @COND int ((int_mul y0 y1) = (int_of_num (NUMERAL 0))) (int_of_num (NUMERAL 0)) (div (int_abs (int_mul y0 y1)) (int_gcd (@pair int int y0 y1)))) (@fst int int (@pair int int x0 x1)).
Definition term25 (x0 : int) (x1 : int) := (fun y0 : int => @COND int ((int_mul (@fst int int (@pair int int x0 x1)) y0) = (int_of_num (NUMERAL 0))) (int_of_num (NUMERAL 0)) (div (int_abs (int_mul (@fst int int (@pair int int x0 x1)) y0)) (int_gcd (@pair int int (@fst int int (@pair int int x0 x1)) y0)))) (@snd int int (@pair int int x0 x1)).
Definition term11 (a0 : Type') (a1 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a1, (@fst a0 a1 (@pair a0 a1 y0 y1)) = y0) x0.
Definition term23 (x0 : int) := @eq (int -> int) (fun y0 : int => @COND int ((int_mul x0 y0) = (int_of_num (NUMERAL 0))) (int_of_num (NUMERAL 0)) (div (int_abs (int_mul x0 y0)) (int_gcd (@pair int int x0 y0)))).
Definition term28 (x0 : int) (x1 : int) := @eq int (@COND int ((int_mul x0 x1) = (int_of_num (NUMERAL 0))) (int_of_num (NUMERAL 0)) (div (int_abs (int_mul x0 x1)) (int_gcd (@pair int int x0 x1)))).
Definition term17 := fun y0 : int => fun y1 : int => @COND int ((int_mul y0 y1) = (int_of_num (NUMERAL 0))) (int_of_num (NUMERAL 0)) (div (int_abs (int_mul y0 y1)) (int_gcd (@pair int int y0 y1))).
Definition term30 := forall y0 : int, forall y1 : int, (int_lcm (@pair int int y0 y1)) = (@COND int ((int_mul y0 y1) = (int_of_num (NUMERAL 0))) (int_of_num (NUMERAL 0)) (div (int_abs (int_mul y0 y1)) (int_gcd (@pair int int y0 y1)))).
Definition term1 (x0 : prod int int) := (fun y0 : prod int int => @COND int ((int_mul (@fst int int y0) (@snd int int y0)) = (int_of_num (NUMERAL 0))) (int_of_num (NUMERAL 0)) (div (int_abs (int_mul (@fst int int y0) (@snd int int y0))) (int_gcd (@pair int int (@fst int int y0) (@snd int int y0))))) x0.
Definition term21 (x0 : int) := @eq (int -> int) ((fun y0 : int => fun y1 : int => @COND int ((int_mul y0 y1) = (int_of_num (NUMERAL 0))) (int_of_num (NUMERAL 0)) (div (int_abs (int_mul y0 y1)) (int_gcd (@pair int int y0 y1)))) x0).
Definition term18 (x0 : int) := (fun y0 : int => fun y1 : int => @COND int ((int_mul y0 y1) = (int_of_num (NUMERAL 0))) (int_of_num (NUMERAL 0)) (div (int_abs (int_mul y0 y1)) (int_gcd (@pair int int y0 y1)))) x0.
Definition term15 (x0 : int) (x1 : int) := @fst int int (@pair int int x0 x1).
Definition term8 (a0 : Type') (a1 : Type') (x0 : a0) := forall y0 : a1, (@snd a0 a1 (@pair a0 a1 x0 y0)) = y0.
Definition term24 (x0 : int) (x1 : int) := (fun y0 : int => @COND int ((int_mul x0 y0) = (int_of_num (NUMERAL 0))) (int_of_num (NUMERAL 0)) (div (int_abs (int_mul x0 y0)) (int_gcd (@pair int int x0 y0)))) x1.
Definition term16 (x0 : int) (x1 : int) := @snd int int (@pair int int x0 x1).
Definition term9 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := (fun y0 : a1 => (@snd a0 a1 (@pair a0 a1 x0 y0)) = y0) x1.
Definition term5 (x0 : int) (x1 : int) := int_lcm (@pair int int x0 x1).
Definition term10 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := @snd a0 a1 (@pair a0 a1 x0 x1).
Definition term3 := forall y0 : prod int int, (int_lcm y0) = (@COND int ((int_mul (@fst int int y0) (@snd int int y0)) = (int_of_num (NUMERAL 0))) (int_of_num (NUMERAL 0)) (div (int_abs (int_mul (@fst int int y0) (@snd int int y0))) (int_gcd (@pair int int (@fst int int y0) (@snd int int y0))))).
Definition term13 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := (fun y0 : a1 => (@fst a0 a1 (@pair a0 a1 x0 y0)) = x0) x1.
Definition term27 (x0 : int) (x1 : int) := @COND int ((int_mul x0 x1) = (int_of_num (NUMERAL 0))) (int_of_num (NUMERAL 0)) (div (int_abs (int_mul x0 x1)) (int_gcd (@pair int int x0 x1))).
Definition term22 (x0 : int) := fun y0 : int => @COND int ((int_mul x0 y0) = (int_of_num (NUMERAL 0))) (int_of_num (NUMERAL 0)) (div (int_abs (int_mul x0 y0)) (int_gcd (@pair int int x0 y0))).
Definition term20 (x0 : int) (x1 : int) := fun y0 : int => @COND int ((int_mul (@fst int int (@pair int int x0 x1)) y0) = (int_of_num (NUMERAL 0))) (int_of_num (NUMERAL 0)) (div (int_abs (int_mul (@fst int int (@pair int int x0 x1)) y0)) (int_gcd (@pair int int (@fst int int (@pair int int x0 x1)) y0))).
