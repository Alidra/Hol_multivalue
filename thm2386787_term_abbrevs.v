Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term62 := @eq Prop (forall y0 : type1674, exists y1 : type1551, forall y2 : int, forall y3 : int, @COND Prop (y3 = (int_of_num (NUMERAL 0))) (((div y2 y3) = (int_of_num (NUMERAL 0))) /\ ((y1 y2 y3) = y2)) ((int_le (int_of_num (NUMERAL 0)) (y1 y2 y3)) /\ ((int_lt (y1 y2 y3) (int_abs y3)) /\ (y2 = (int_add (int_mul (div y2 y3) y3) (y1 y2 y3)))))).
Definition term61 := @eq Prop (forall y0 : type1674, exists y1 : type1551, (fun y2 : type1674 => fun y3 : type1551 => forall y4 : int, forall y5 : int, @COND Prop (y5 = (int_of_num (NUMERAL 0))) (((div y4 y5) = (int_of_num (NUMERAL 0))) /\ ((y3 y4 y5) = y4)) ((int_le (int_of_num (NUMERAL 0)) (y3 y4 y5)) /\ ((int_lt (y3 y4 y5) (int_abs y5)) /\ (y4 = (int_add (int_mul (div y4 y5) y5) (y3 y4 y5)))))) y0 y1).
Definition term6 (x0 : int) := @ε ((prod nat (prod nat nat)) -> int -> int -> int) (fun y0 : type1305 => forall y1 : type1674, exists y2 : type1551, forall y3 : int, forall y4 : int, @COND Prop (y4 = (int_of_num (NUMERAL 0))) (((y0 y1 y3 y4) = (int_of_num (NUMERAL 0))) /\ ((y2 y3 y4) = y3)) ((int_le (int_of_num (NUMERAL 0)) (y2 y3 y4)) /\ ((int_lt (y2 y3 y4) (int_abs y4)) /\ (y3 = (int_add (int_mul (y0 y1 y3 y4) y4) (y2 y3 y4)))))) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))))) x0.
Definition term70 := fun y0 : type1305 => forall y1 : type1674, (fun y2 : type1674 => fun y3 : type1551 => forall y4 : int, forall y5 : int, @COND Prop (y5 = (int_of_num (NUMERAL 0))) (((div y4 y5) = (int_of_num (NUMERAL 0))) /\ ((y3 y4 y5) = y4)) ((int_le (int_of_num (NUMERAL 0)) (y3 y4 y5)) /\ ((int_lt (y3 y4 y5) (int_abs y5)) /\ (y4 = (int_add (int_mul (div y4 y5) y5) (y3 y4 y5)))))) y1 (y0 y1).
Definition term15 (x0 : int) := @COND Prop (x0 = (int_of_num (NUMERAL 0))).
Definition term31 (x0 : type1551) (x1 : int) (x2 : int) := (int_le (int_of_num (NUMERAL 0)) (x0 x1 x2)) /\ ((int_lt (x0 x1 x2) (int_abs x2)) /\ (x1 = (int_add (int_mul (div x1 x2) x2) (x0 x1 x2)))).
Definition term30 (x0 : type1551) (x1 : int) (x2 : int) := (int_le (int_of_num (NUMERAL 0)) (x0 x1 x2)) /\ ((int_lt (x0 x1 x2) (int_abs x2)) /\ (x1 = (int_add (int_mul (@ε ((prod nat (prod nat nat)) -> int -> int -> int) (fun y0 : type1305 => forall y1 : type1674, exists y2 : type1551, forall y3 : int, forall y4 : int, @COND Prop (y4 = (int_of_num (NUMERAL 0))) (((y0 y1 y3 y4) = (int_of_num (NUMERAL 0))) /\ ((y2 y3 y4) = y3)) ((int_le (int_of_num (NUMERAL 0)) (y2 y3 y4)) /\ ((int_lt (y2 y3 y4) (int_abs y4)) /\ (y3 = (int_add (int_mul (y0 y1 y3 y4) y4) (y2 y3 y4)))))) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))))) x1 x2) x2) (x0 x1 x2)))).
Definition term67 (x0 : type1305) := fun y0 : type1674 => forall y1 : int, forall y2 : int, @COND Prop (y2 = (int_of_num (NUMERAL 0))) (((div y1 y2) = (int_of_num (NUMERAL 0))) /\ ((x0 y0 y1 y2) = y1)) ((int_le (int_of_num (NUMERAL 0)) (x0 y0 y1 y2)) /\ ((int_lt (x0 y0 y1 y2) (int_abs y2)) /\ (y1 = (int_add (int_mul (div y1 y2) y2) (x0 y0 y1 y2))))).
Definition term7 (x0 : int) (x1 : int) := @ε ((prod nat (prod nat nat)) -> int -> int -> int) (fun y0 : type1305 => forall y1 : type1674, exists y2 : type1551, forall y3 : int, forall y4 : int, @COND Prop (y4 = (int_of_num (NUMERAL 0))) (((y0 y1 y3 y4) = (int_of_num (NUMERAL 0))) /\ ((y2 y3 y4) = y3)) ((int_le (int_of_num (NUMERAL 0)) (y2 y3 y4)) /\ ((int_lt (y2 y3 y4) (int_abs y4)) /\ (y3 = (int_add (int_mul (y0 y1 y3 y4) y4) (y2 y3 y4)))))) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))))) x0 x1.
Definition term10 := int_of_num (NUMERAL 0).
Definition term9 (x0 : int) (x1 : int) := @eq int (div x0 x1).
Definition term19 (x0 : int) (x1 : int) := int_mul (div x0 x1).
Definition term8 (x0 : int) (x1 : int) := @eq int (@ε ((prod nat (prod nat nat)) -> int -> int -> int) (fun y0 : type1305 => forall y1 : type1674, exists y2 : type1551, forall y3 : int, forall y4 : int, @COND Prop (y4 = (int_of_num (NUMERAL 0))) (((y0 y1 y3 y4) = (int_of_num (NUMERAL 0))) /\ ((y2 y3 y4) = y3)) ((int_le (int_of_num (NUMERAL 0)) (y2 y3 y4)) /\ ((int_lt (y2 y3 y4) (int_abs y4)) /\ (y3 = (int_add (int_mul (y0 y1 y3 y4) y4) (y2 y3 y4)))))) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))))) x0 x1).
Definition term64 (x0 : type1305) (x1 : type1674) := (fun y0 : type1551 => forall y1 : int, forall y2 : int, @COND Prop (y2 = (int_of_num (NUMERAL 0))) (((div y1 y2) = (int_of_num (NUMERAL 0))) /\ ((y0 y1 y2) = y1)) ((int_le (int_of_num (NUMERAL 0)) (y0 y1 y2)) /\ ((int_lt (y0 y1 y2) (int_abs y2)) /\ (y1 = (int_add (int_mul (div y1 y2) y2) (y0 y1 y2)))))) (x0 x1).
Definition term25 (x0 : type1551) (x1 : int) (x2 : int) := int_add (int_mul (div x1 x2) x2) (x0 x1 x2).
Definition term24 (x0 : type1551) (x1 : int) (x2 : int) := int_add (int_mul (@ε ((prod nat (prod nat nat)) -> int -> int -> int) (fun y0 : type1305 => forall y1 : type1674, exists y2 : type1551, forall y3 : int, forall y4 : int, @COND Prop (y4 = (int_of_num (NUMERAL 0))) (((y0 y1 y3 y4) = (int_of_num (NUMERAL 0))) /\ ((y2 y3 y4) = y3)) ((int_le (int_of_num (NUMERAL 0)) (y2 y3 y4)) /\ ((int_lt (y2 y3 y4) (int_abs y4)) /\ (y3 = (int_add (int_mul (y0 y1 y3 y4) y4) (y2 y3 y4)))))) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))))) x1 x2) x2) (x0 x1 x2).
Definition term57 (x0 : type1674) := fun y0 : type1551 => (fun y1 : type1674 => fun y2 : type1551 => forall y3 : int, forall y4 : int, @COND Prop (y4 = (int_of_num (NUMERAL 0))) (((div y3 y4) = (int_of_num (NUMERAL 0))) /\ ((y2 y3 y4) = y3)) ((int_le (int_of_num (NUMERAL 0)) (y2 y3 y4)) /\ ((int_lt (y2 y3 y4) (int_abs y4)) /\ (y3 = (int_add (int_mul (div y3 y4) y4) (y2 y3 y4)))))) x0 y0.
Definition term47 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := forall y0 : a0, exists y1 : a1, x0 y0 y1.
Definition term52 := exists y0 : type1305, forall y1 : type1674, (fun y2 : type1674 => fun y3 : type1551 => forall y4 : int, forall y5 : int, @COND Prop (y5 = (int_of_num (NUMERAL 0))) (((div y4 y5) = (int_of_num (NUMERAL 0))) /\ ((y3 y4 y5) = y4)) ((int_le (int_of_num (NUMERAL 0)) (y3 y4 y5)) /\ ((int_lt (y3 y4 y5) (int_abs y5)) /\ (y4 = (int_add (int_mul (div y4 y5) y5) (y3 y4 y5)))))) y1 (y0 y1).
Definition term50 (x0 : type1299) := exists y0 : type1305, forall y1 : type1674, x0 y1 (y0 y1).
Definition term68 (x0 : type1305) := forall y0 : type1674, (fun y1 : type1674 => fun y2 : type1551 => forall y3 : int, forall y4 : int, @COND Prop (y4 = (int_of_num (NUMERAL 0))) (((div y3 y4) = (int_of_num (NUMERAL 0))) /\ ((y2 y3 y4) = y3)) ((int_le (int_of_num (NUMERAL 0)) (y2 y3 y4)) /\ ((int_lt (y2 y3 y4) (int_abs y4)) /\ (y3 = (int_add (int_mul (div y3 y4) y4) (y2 y3 y4)))))) y0 (x0 y0).
Definition term74 := fun y0 : type368 => y0 (@ε ((prod nat (prod nat nat)) -> int -> int -> int) y0).
Definition term2 := (fun y0 : type1674 => exists y1 : type1551, forall y2 : int, forall y3 : int, @COND Prop (y3 = (int_of_num (NUMERAL 0))) (((@ε ((prod nat (prod nat nat)) -> int -> int -> int) (fun y4 : type1305 => forall y5 : type1674, exists y6 : type1551, forall y7 : int, forall y8 : int, @COND Prop (y8 = (int_of_num (NUMERAL 0))) (((y4 y5 y7 y8) = (int_of_num (NUMERAL 0))) /\ ((y6 y7 y8) = y7)) ((int_le (int_of_num (NUMERAL 0)) (y6 y7 y8)) /\ ((int_lt (y6 y7 y8) (int_abs y8)) /\ (y7 = (int_add (int_mul (y4 y5 y7 y8) y8) (y6 y7 y8)))))) y0 y2 y3) = (int_of_num (NUMERAL 0))) /\ ((y1 y2 y3) = y2)) ((int_le (int_of_num (NUMERAL 0)) (y1 y2 y3)) /\ ((int_lt (y1 y2 y3) (int_abs y3)) /\ (y2 = (int_add (int_mul (@ε ((prod nat (prod nat nat)) -> int -> int -> int) (fun y4 : type1305 => forall y5 : type1674, exists y6 : type1551, forall y7 : int, forall y8 : int, @COND Prop (y8 = (int_of_num (NUMERAL 0))) (((y4 y5 y7 y8) = (int_of_num (NUMERAL 0))) /\ ((y6 y7 y8) = y7)) ((int_le (int_of_num (NUMERAL 0)) (y6 y7 y8)) /\ ((int_lt (y6 y7 y8) (int_abs y8)) /\ (y7 = (int_add (int_mul (y4 y5 y7 y8) y8) (y6 y7 y8)))))) y0 y2 y3) y3) (y1 y2 y3)))))) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))))).
Definition term35 (x0 : type1551) (x1 : int) := fun y0 : int => @COND Prop (y0 = (int_of_num (NUMERAL 0))) (((div x1 y0) = (int_of_num (NUMERAL 0))) /\ ((x0 x1 y0) = x1)) ((int_le (int_of_num (NUMERAL 0)) (x0 x1 y0)) /\ ((int_lt (x0 x1 y0) (int_abs y0)) /\ (x1 = (int_add (int_mul (div x1 y0) y0) (x0 x1 y0))))).
Definition term34 (x0 : type1551) (x1 : int) := fun y0 : int => @COND Prop (y0 = (int_of_num (NUMERAL 0))) (((@ε ((prod nat (prod nat nat)) -> int -> int -> int) (fun y1 : type1305 => forall y2 : type1674, exists y3 : type1551, forall y4 : int, forall y5 : int, @COND Prop (y5 = (int_of_num (NUMERAL 0))) (((y1 y2 y4 y5) = (int_of_num (NUMERAL 0))) /\ ((y3 y4 y5) = y4)) ((int_le (int_of_num (NUMERAL 0)) (y3 y4 y5)) /\ ((int_lt (y3 y4 y5) (int_abs y5)) /\ (y4 = (int_add (int_mul (y1 y2 y4 y5) y5) (y3 y4 y5)))))) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))))) x1 y0) = (int_of_num (NUMERAL 0))) /\ ((x0 x1 y0) = x1)) ((int_le (int_of_num (NUMERAL 0)) (x0 x1 y0)) /\ ((int_lt (x0 x1 y0) (int_abs y0)) /\ (x1 = (int_add (int_mul (@ε ((prod nat (prod nat nat)) -> int -> int -> int) (fun y1 : type1305 => forall y2 : type1674, exists y3 : type1551, forall y4 : int, forall y5 : int, @COND Prop (y5 = (int_of_num (NUMERAL 0))) (((y1 y2 y4 y5) = (int_of_num (NUMERAL 0))) /\ ((y3 y4 y5) = y4)) ((int_le (int_of_num (NUMERAL 0)) (y3 y4 y5)) /\ ((int_lt (y3 y4 y5) (int_abs y5)) /\ (y4 = (int_add (int_mul (y1 y2 y4 y5) y5) (y3 y4 y5)))))) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))))) x1 y0) y0) (x0 x1 y0))))).
Definition term53 := fun y0 : type1674 => fun y1 : type1551 => forall y2 : int, forall y3 : int, @COND Prop (y3 = (int_of_num (NUMERAL 0))) (((div y2 y3) = (int_of_num (NUMERAL 0))) /\ ((y1 y2 y3) = y2)) ((int_le (int_of_num (NUMERAL 0)) (y1 y2 y3)) /\ ((int_lt (y1 y2 y3) (int_abs y3)) /\ (y2 = (int_add (int_mul (div y2 y3) y3) (y1 y2 y3))))).
Definition term12 (x0 : int) (x1 : int) := and ((div x0 x1) = (int_of_num (NUMERAL 0))).
Definition term3 := @pair nat (prod nat nat) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0))))))))).
Definition term73 (a0 : Type') := fun y0 : a0 -> Prop => y0 (@ε a0 y0).
Definition term69 (x0 : type1305) := forall y0 : type1674, forall y1 : int, forall y2 : int, @COND Prop (y2 = (int_of_num (NUMERAL 0))) (((div y1 y2) = (int_of_num (NUMERAL 0))) /\ ((x0 y0 y1 y2) = y1)) ((int_le (int_of_num (NUMERAL 0)) (x0 y0 y1 y2)) /\ ((int_lt (x0 y0 y1 y2) (int_abs y2)) /\ (y1 = (int_add (int_mul (div y1 y2) y2) (x0 y0 y1 y2))))).
Definition term76 := (fun y0 : type1305 => forall y1 : type1674, forall y2 : int, forall y3 : int, @COND Prop (y3 = (int_of_num (NUMERAL 0))) (((div y2 y3) = (int_of_num (NUMERAL 0))) /\ ((y0 y1 y2 y3) = y2)) ((int_le (int_of_num (NUMERAL 0)) (y0 y1 y2 y3)) /\ ((int_lt (y0 y1 y2 y3) (int_abs y3)) /\ (y2 = (int_add (int_mul (div y2 y3) y3) (y0 y1 y2 y3)))))) (@ε ((prod nat (prod nat nat)) -> int -> int -> int) (fun y0 : type1305 => forall y1 : type1674, forall y2 : int, forall y3 : int, @COND Prop (y3 = (int_of_num (NUMERAL 0))) (((div y2 y3) = (int_of_num (NUMERAL 0))) /\ ((y0 y1 y2 y3) = y2)) ((int_le (int_of_num (NUMERAL 0)) (y0 y1 y2 y3)) /\ ((int_lt (y0 y1 y2 y3) (int_abs y3)) /\ (y2 = (int_add (int_mul (div y2 y3) y3) (y0 y1 y2 y3))))))).
Definition term0 := (fun y0 : type1305 => forall y1 : type1674, exists y2 : type1551, forall y3 : int, forall y4 : int, @COND Prop (y4 = (int_of_num (NUMERAL 0))) (((y0 y1 y3 y4) = (int_of_num (NUMERAL 0))) /\ ((y2 y3 y4) = y3)) ((int_le (int_of_num (NUMERAL 0)) (y2 y3 y4)) /\ ((int_lt (y2 y3 y4) (int_abs y4)) /\ (y3 = (int_add (int_mul (y0 y1 y3 y4) y4) (y2 y3 y4)))))) (@ε ((prod nat (prod nat nat)) -> int -> int -> int) (fun y0 : type1305 => forall y1 : type1674, exists y2 : type1551, forall y3 : int, forall y4 : int, @COND Prop (y4 = (int_of_num (NUMERAL 0))) (((y0 y1 y3 y4) = (int_of_num (NUMERAL 0))) /\ ((y2 y3 y4) = y3)) ((int_le (int_of_num (NUMERAL 0)) (y2 y3 y4)) /\ ((int_lt (y2 y3 y4) (int_abs y4)) /\ (y3 = (int_add (int_mul (y0 y1 y3 y4) y4) (y2 y3 y4))))))).
Definition term75 := (fun y0 : type368 => y0 (@ε ((prod nat (prod nat nat)) -> int -> int -> int) y0)) (fun y0 : type1305 => forall y1 : type1674, forall y2 : int, forall y3 : int, @COND Prop (y3 = (int_of_num (NUMERAL 0))) (((div y2 y3) = (int_of_num (NUMERAL 0))) /\ ((y0 y1 y2 y3) = y2)) ((int_le (int_of_num (NUMERAL 0)) (y0 y1 y2 y3)) /\ ((int_lt (y0 y1 y2 y3) (int_abs y3)) /\ (y2 = (int_add (int_mul (div y2 y3) y3) (y0 y1 y2 y3)))))).
Definition term58 (x0 : type1674) := exists y0 : type1551, (fun y1 : type1674 => fun y2 : type1551 => forall y3 : int, forall y4 : int, @COND Prop (y4 = (int_of_num (NUMERAL 0))) (((div y3 y4) = (int_of_num (NUMERAL 0))) /\ ((y2 y3 y4) = y3)) ((int_le (int_of_num (NUMERAL 0)) (y2 y3 y4)) /\ ((int_lt (y2 y3 y4) (int_abs y4)) /\ (y3 = (int_add (int_mul (div y3 y4) y4) (y2 y3 y4)))))) x0 y0.
Definition term71 := fun y0 : type1305 => forall y1 : type1674, forall y2 : int, forall y3 : int, @COND Prop (y3 = (int_of_num (NUMERAL 0))) (((div y2 y3) = (int_of_num (NUMERAL 0))) /\ ((y0 y1 y2 y3) = y2)) ((int_le (int_of_num (NUMERAL 0)) (y0 y1 y2 y3)) /\ ((int_lt (y0 y1 y2 y3) (int_abs y3)) /\ (y2 = (int_add (int_mul (div y2 y3) y3) (y0 y1 y2 y3))))).
Definition term65 (x0 : type1305) (x1 : type1674) := forall y0 : int, forall y1 : int, @COND Prop (y1 = (int_of_num (NUMERAL 0))) (((div y0 y1) = (int_of_num (NUMERAL 0))) /\ ((x0 x1 y0 y1) = y0)) ((int_le (int_of_num (NUMERAL 0)) (x0 x1 y0 y1)) /\ ((int_lt (x0 x1 y0 y1) (int_abs y1)) /\ (y0 = (int_add (int_mul (div y0 y1) y1) (x0 x1 y0 y1))))).
Definition term41 (x0 : type1551) := forall y0 : int, forall y1 : int, @COND Prop (y1 = (int_of_num (NUMERAL 0))) (((div y0 y1) = (int_of_num (NUMERAL 0))) /\ ((x0 y0 y1) = y0)) ((int_le (int_of_num (NUMERAL 0)) (x0 y0 y1)) /\ ((int_lt (x0 y0 y1) (int_abs y1)) /\ (y0 = (int_add (int_mul (div y0 y1) y1) (x0 y0 y1))))).
Definition term40 (x0 : type1551) := forall y0 : int, forall y1 : int, @COND Prop (y1 = (int_of_num (NUMERAL 0))) (((@ε ((prod nat (prod nat nat)) -> int -> int -> int) (fun y2 : type1305 => forall y3 : type1674, exists y4 : type1551, forall y5 : int, forall y6 : int, @COND Prop (y6 = (int_of_num (NUMERAL 0))) (((y2 y3 y5 y6) = (int_of_num (NUMERAL 0))) /\ ((y4 y5 y6) = y5)) ((int_le (int_of_num (NUMERAL 0)) (y4 y5 y6)) /\ ((int_lt (y4 y5 y6) (int_abs y6)) /\ (y5 = (int_add (int_mul (y2 y3 y5 y6) y6) (y4 y5 y6)))))) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))))) y0 y1) = (int_of_num (NUMERAL 0))) /\ ((x0 y0 y1) = y0)) ((int_le (int_of_num (NUMERAL 0)) (x0 y0 y1)) /\ ((int_lt (x0 y0 y1) (int_abs y1)) /\ (y0 = (int_add (int_mul (@ε ((prod nat (prod nat nat)) -> int -> int -> int) (fun y2 : type1305 => forall y3 : type1674, exists y4 : type1551, forall y5 : int, forall y6 : int, @COND Prop (y6 = (int_of_num (NUMERAL 0))) (((y2 y3 y5 y6) = (int_of_num (NUMERAL 0))) /\ ((y4 y5 y6) = y5)) ((int_le (int_of_num (NUMERAL 0)) (y4 y5 y6)) /\ ((int_lt (y4 y5 y6) (int_abs y6)) /\ (y5 = (int_add (int_mul (y2 y3 y5 y6) y6) (y4 y5 y6)))))) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))))) y0 y1) y1) (x0 y0 y1))))).
Definition term33 (x0 : type1551) (x1 : int) (x2 : int) := @COND Prop (x2 = (int_of_num (NUMERAL 0))) (((div x1 x2) = (int_of_num (NUMERAL 0))) /\ ((x0 x1 x2) = x1)) ((int_le (int_of_num (NUMERAL 0)) (x0 x1 x2)) /\ ((int_lt (x0 x1 x2) (int_abs x2)) /\ (x1 = (int_add (int_mul (div x1 x2) x2) (x0 x1 x2))))).
Definition term32 (x0 : type1551) (x1 : int) (x2 : int) := @COND Prop (x2 = (int_of_num (NUMERAL 0))) (((@ε ((prod nat (prod nat nat)) -> int -> int -> int) (fun y0 : type1305 => forall y1 : type1674, exists y2 : type1551, forall y3 : int, forall y4 : int, @COND Prop (y4 = (int_of_num (NUMERAL 0))) (((y0 y1 y3 y4) = (int_of_num (NUMERAL 0))) /\ ((y2 y3 y4) = y3)) ((int_le (int_of_num (NUMERAL 0)) (y2 y3 y4)) /\ ((int_lt (y2 y3 y4) (int_abs y4)) /\ (y3 = (int_add (int_mul (y0 y1 y3 y4) y4) (y2 y3 y4)))))) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))))) x1 x2) = (int_of_num (NUMERAL 0))) /\ ((x0 x1 x2) = x1)) ((int_le (int_of_num (NUMERAL 0)) (x0 x1 x2)) /\ ((int_lt (x0 x1 x2) (int_abs x2)) /\ (x1 = (int_add (int_mul (@ε ((prod nat (prod nat nat)) -> int -> int -> int) (fun y0 : type1305 => forall y1 : type1674, exists y2 : type1551, forall y3 : int, forall y4 : int, @COND Prop (y4 = (int_of_num (NUMERAL 0))) (((y0 y1 y3 y4) = (int_of_num (NUMERAL 0))) /\ ((y2 y3 y4) = y3)) ((int_le (int_of_num (NUMERAL 0)) (y2 y3 y4)) /\ ((int_lt (y2 y3 y4) (int_abs y4)) /\ (y3 = (int_add (int_mul (y0 y1 y3 y4) y4) (y2 y3 y4)))))) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))))) x1 x2) x2) (x0 x1 x2))))).
Definition term26 (x0 : type1551) (x1 : int) (x2 : int) := and (int_lt (x0 x1 x2) (int_abs x2)).
Definition term54 (x0 : type1674) := (fun y0 : type1674 => fun y1 : type1551 => forall y2 : int, forall y3 : int, @COND Prop (y3 = (int_of_num (NUMERAL 0))) (((div y2 y3) = (int_of_num (NUMERAL 0))) /\ ((y1 y2 y3) = y2)) ((int_le (int_of_num (NUMERAL 0)) (y1 y2 y3)) /\ ((int_lt (y1 y2 y3) (int_abs y3)) /\ (y2 = (int_add (int_mul (div y2 y3) y3) (y1 y2 y3)))))) x0.
Definition term28 (x0 : type1551) (x1 : int) (x2 : int) := (int_lt (x0 x1 x2) (int_abs x2)) /\ (x1 = (int_add (int_mul (div x1 x2) x2) (x0 x1 x2))).
Definition term27 (x0 : type1551) (x1 : int) (x2 : int) := (int_lt (x0 x1 x2) (int_abs x2)) /\ (x1 = (int_add (int_mul (@ε ((prod nat (prod nat nat)) -> int -> int -> int) (fun y0 : type1305 => forall y1 : type1674, exists y2 : type1551, forall y3 : int, forall y4 : int, @COND Prop (y4 = (int_of_num (NUMERAL 0))) (((y0 y1 y3 y4) = (int_of_num (NUMERAL 0))) /\ ((y2 y3 y4) = y3)) ((int_le (int_of_num (NUMERAL 0)) (y2 y3 y4)) /\ ((int_lt (y2 y3 y4) (int_abs y4)) /\ (y3 = (int_add (int_mul (y0 y1 y3 y4) y4) (y2 y3 y4)))))) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))))) x1 x2) x2) (x0 x1 x2))).
Definition term17 (x0 : type1551) (x1 : int) (x2 : int) := @COND Prop (x1 = (int_of_num (NUMERAL 0))) (((div x2 x1) = (int_of_num (NUMERAL 0))) /\ ((x0 x2 x1) = x2)).
Definition term16 (x0 : type1551) (x1 : int) (x2 : int) := @COND Prop (x1 = (int_of_num (NUMERAL 0))) (((@ε ((prod nat (prod nat nat)) -> int -> int -> int) (fun y0 : type1305 => forall y1 : type1674, exists y2 : type1551, forall y3 : int, forall y4 : int, @COND Prop (y4 = (int_of_num (NUMERAL 0))) (((y0 y1 y3 y4) = (int_of_num (NUMERAL 0))) /\ ((y2 y3 y4) = y3)) ((int_le (int_of_num (NUMERAL 0)) (y2 y3 y4)) /\ ((int_lt (y2 y3 y4) (int_abs y4)) /\ (y3 = (int_add (int_mul (y0 y1 y3 y4) y4) (y2 y3 y4)))))) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))))) x2 x1) = (int_of_num (NUMERAL 0))) /\ ((x0 x2 x1) = x2)).
Definition term18 (x0 : int) (x1 : int) := int_mul (@ε ((prod nat (prod nat nat)) -> int -> int -> int) (fun y0 : type1305 => forall y1 : type1674, exists y2 : type1551, forall y3 : int, forall y4 : int, @COND Prop (y4 = (int_of_num (NUMERAL 0))) (((y0 y1 y3 y4) = (int_of_num (NUMERAL 0))) /\ ((y2 y3 y4) = y3)) ((int_le (int_of_num (NUMERAL 0)) (y2 y3 y4)) /\ ((int_lt (y2 y3 y4) (int_abs y4)) /\ (y3 = (int_add (int_mul (y0 y1 y3 y4) y4) (y2 y3 y4)))))) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))))) x0 x1).
Definition term20 (x0 : int) (x1 : int) := int_mul (@ε ((prod nat (prod nat nat)) -> int -> int -> int) (fun y0 : type1305 => forall y1 : type1674, exists y2 : type1551, forall y3 : int, forall y4 : int, @COND Prop (y4 = (int_of_num (NUMERAL 0))) (((y0 y1 y3 y4) = (int_of_num (NUMERAL 0))) /\ ((y2 y3 y4) = y3)) ((int_le (int_of_num (NUMERAL 0)) (y2 y3 y4)) /\ ((int_lt (y2 y3 y4) (int_abs y4)) /\ (y3 = (int_add (int_mul (y0 y1 y3 y4) y4) (y2 y3 y4)))))) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))))) x0 x1) x1.
Definition term66 (x0 : type1305) := fun y0 : type1674 => (fun y1 : type1674 => fun y2 : type1551 => forall y3 : int, forall y4 : int, @COND Prop (y4 = (int_of_num (NUMERAL 0))) (((div y3 y4) = (int_of_num (NUMERAL 0))) /\ ((y2 y3 y4) = y3)) ((int_le (int_of_num (NUMERAL 0)) (y2 y3 y4)) /\ ((int_lt (y2 y3 y4) (int_abs y4)) /\ (y3 = (int_add (int_mul (div y3 y4) y4) (y2 y3 y4)))))) y0 (x0 y0).
Definition term21 (x0 : int) (x1 : int) := int_mul (div x0 x1) x1.
Definition term14 (x0 : type1551) (x1 : int) (x2 : int) := ((div x2 x1) = (int_of_num (NUMERAL 0))) /\ ((x0 x2 x1) = x2).
Definition term13 (x0 : type1551) (x1 : int) (x2 : int) := ((@ε ((prod nat (prod nat nat)) -> int -> int -> int) (fun y0 : type1305 => forall y1 : type1674, exists y2 : type1551, forall y3 : int, forall y4 : int, @COND Prop (y4 = (int_of_num (NUMERAL 0))) (((y0 y1 y3 y4) = (int_of_num (NUMERAL 0))) /\ ((y2 y3 y4) = y3)) ((int_le (int_of_num (NUMERAL 0)) (y2 y3 y4)) /\ ((int_lt (y2 y3 y4) (int_abs y4)) /\ (y3 = (int_add (int_mul (y0 y1 y3 y4) y4) (y2 y3 y4)))))) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))))) x2 x1) = (int_of_num (NUMERAL 0))) /\ ((x0 x2 x1) = x2).
Definition term56 (x0 : type1551) := (fun y0 : type1551 => forall y1 : int, forall y2 : int, @COND Prop (y2 = (int_of_num (NUMERAL 0))) (((div y1 y2) = (int_of_num (NUMERAL 0))) /\ ((y0 y1 y2) = y1)) ((int_le (int_of_num (NUMERAL 0)) (y0 y1 y2)) /\ ((int_lt (y0 y1 y2) (int_abs y2)) /\ (y1 = (int_add (int_mul (div y1 y2) y2) (y0 y1 y2)))))) x0.
Definition term72 := exists y0 : type1305, forall y1 : type1674, forall y2 : int, forall y3 : int, @COND Prop (y3 = (int_of_num (NUMERAL 0))) (((div y2 y3) = (int_of_num (NUMERAL 0))) /\ ((y0 y1 y2 y3) = y2)) ((int_le (int_of_num (NUMERAL 0)) (y0 y1 y2 y3)) /\ ((int_lt (y0 y1 y2 y3) (int_abs y3)) /\ (y2 = (int_add (int_mul (div y2 y3) y3) (y0 y1 y2 y3))))).
Definition term44 := exists y0 : type1551, forall y1 : int, forall y2 : int, @COND Prop (y2 = (int_of_num (NUMERAL 0))) (((div y1 y2) = (int_of_num (NUMERAL 0))) /\ ((y0 y1 y2) = y1)) ((int_le (int_of_num (NUMERAL 0)) (y0 y1 y2)) /\ ((int_lt (y0 y1 y2) (int_abs y2)) /\ (y1 = (int_add (int_mul (div y1 y2) y2) (y0 y1 y2))))).
Definition term4 := exists y0 : type1551, forall y1 : int, forall y2 : int, @COND Prop (y2 = (int_of_num (NUMERAL 0))) (((@ε ((prod nat (prod nat nat)) -> int -> int -> int) (fun y3 : type1305 => forall y4 : type1674, exists y5 : type1551, forall y6 : int, forall y7 : int, @COND Prop (y7 = (int_of_num (NUMERAL 0))) (((y3 y4 y6 y7) = (int_of_num (NUMERAL 0))) /\ ((y5 y6 y7) = y6)) ((int_le (int_of_num (NUMERAL 0)) (y5 y6 y7)) /\ ((int_lt (y5 y6 y7) (int_abs y7)) /\ (y6 = (int_add (int_mul (y3 y4 y6 y7) y7) (y5 y6 y7)))))) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))))) y1 y2) = (int_of_num (NUMERAL 0))) /\ ((y0 y1 y2) = y1)) ((int_le (int_of_num (NUMERAL 0)) (y0 y1 y2)) /\ ((int_lt (y0 y1 y2) (int_abs y2)) /\ (y1 = (int_add (int_mul (@ε ((prod nat (prod nat nat)) -> int -> int -> int) (fun y3 : type1305 => forall y4 : type1674, exists y5 : type1551, forall y6 : int, forall y7 : int, @COND Prop (y7 = (int_of_num (NUMERAL 0))) (((y3 y4 y6 y7) = (int_of_num (NUMERAL 0))) /\ ((y5 y6 y7) = y6)) ((int_le (int_of_num (NUMERAL 0)) (y5 y6 y7)) /\ ((int_lt (y5 y6 y7) (int_abs y7)) /\ (y6 = (int_add (int_mul (y3 y4 y6 y7) y7) (y5 y6 y7)))))) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))))) y1 y2) y2) (y0 y1 y2))))).
Definition term45 := forall y0 : type1674, exists y1 : type1551, forall y2 : int, forall y3 : int, @COND Prop (y3 = (int_of_num (NUMERAL 0))) (((div y2 y3) = (int_of_num (NUMERAL 0))) /\ ((y1 y2 y3) = y2)) ((int_le (int_of_num (NUMERAL 0)) (y1 y2 y3)) /\ ((int_lt (y1 y2 y3) (int_abs y3)) /\ (y2 = (int_add (int_mul (div y2 y3) y3) (y1 y2 y3))))).
Definition term1 := forall y0 : type1674, exists y1 : type1551, forall y2 : int, forall y3 : int, @COND Prop (y3 = (int_of_num (NUMERAL 0))) (((@ε ((prod nat (prod nat nat)) -> int -> int -> int) (fun y4 : type1305 => forall y5 : type1674, exists y6 : type1551, forall y7 : int, forall y8 : int, @COND Prop (y8 = (int_of_num (NUMERAL 0))) (((y4 y5 y7 y8) = (int_of_num (NUMERAL 0))) /\ ((y6 y7 y8) = y7)) ((int_le (int_of_num (NUMERAL 0)) (y6 y7 y8)) /\ ((int_lt (y6 y7 y8) (int_abs y8)) /\ (y7 = (int_add (int_mul (y4 y5 y7 y8) y8) (y6 y7 y8)))))) y0 y2 y3) = (int_of_num (NUMERAL 0))) /\ ((y1 y2 y3) = y2)) ((int_le (int_of_num (NUMERAL 0)) (y1 y2 y3)) /\ ((int_lt (y1 y2 y3) (int_abs y3)) /\ (y2 = (int_add (int_mul (@ε ((prod nat (prod nat nat)) -> int -> int -> int) (fun y4 : type1305 => forall y5 : type1674, exists y6 : type1551, forall y7 : int, forall y8 : int, @COND Prop (y8 = (int_of_num (NUMERAL 0))) (((y4 y5 y7 y8) = (int_of_num (NUMERAL 0))) /\ ((y6 y7 y8) = y7)) ((int_le (int_of_num (NUMERAL 0)) (y6 y7 y8)) /\ ((int_lt (y6 y7 y8) (int_abs y8)) /\ (y7 = (int_add (int_mul (y4 y5 y7 y8) y8) (y6 y7 y8)))))) y0 y2 y3) y3) (y1 y2 y3))))).
Definition term46 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := (fun y0 : type1413 a0 a1 => (forall y1 : a0, exists y2 : a1, y0 y1 y2) = (exists y1 : a0 -> a1, forall y2 : a0, y0 y2 (y1 y2))) x0.
Definition term5 := @ε ((prod nat (prod nat nat)) -> int -> int -> int) (fun y0 : type1305 => forall y1 : type1674, exists y2 : type1551, forall y3 : int, forall y4 : int, @COND Prop (y4 = (int_of_num (NUMERAL 0))) (((y0 y1 y3 y4) = (int_of_num (NUMERAL 0))) /\ ((y2 y3 y4) = y3)) ((int_le (int_of_num (NUMERAL 0)) (y2 y3 y4)) /\ ((int_lt (y2 y3 y4) (int_abs y4)) /\ (y3 = (int_add (int_mul (y0 y1 y3 y4) y4) (y2 y3 y4)))))) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))))).
Definition term55 (x0 : type1674) (x1 : type1551) := (fun y0 : type1674 => fun y1 : type1551 => forall y2 : int, forall y3 : int, @COND Prop (y3 = (int_of_num (NUMERAL 0))) (((div y2 y3) = (int_of_num (NUMERAL 0))) /\ ((y1 y2 y3) = y2)) ((int_le (int_of_num (NUMERAL 0)) (y1 y2 y3)) /\ ((int_lt (y1 y2 y3) (int_abs y3)) /\ (y2 = (int_add (int_mul (div y2 y3) y3) (y1 y2 y3)))))) x0 x1.
Definition term23 (x0 : int) (x1 : int) := int_add (int_mul (div x0 x1) x1).
Definition term22 (x0 : int) (x1 : int) := int_add (int_mul (@ε ((prod nat (prod nat nat)) -> int -> int -> int) (fun y0 : type1305 => forall y1 : type1674, exists y2 : type1551, forall y3 : int, forall y4 : int, @COND Prop (y4 = (int_of_num (NUMERAL 0))) (((y0 y1 y3 y4) = (int_of_num (NUMERAL 0))) /\ ((y2 y3 y4) = y3)) ((int_le (int_of_num (NUMERAL 0)) (y2 y3 y4)) /\ ((int_lt (y2 y3 y4) (int_abs y4)) /\ (y3 = (int_add (int_mul (y0 y1 y3 y4) y4) (y2 y3 y4)))))) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))))) x0 x1) x1).
Definition term43 := fun y0 : type1551 => forall y1 : int, forall y2 : int, @COND Prop (y2 = (int_of_num (NUMERAL 0))) (((div y1 y2) = (int_of_num (NUMERAL 0))) /\ ((y0 y1 y2) = y1)) ((int_le (int_of_num (NUMERAL 0)) (y0 y1 y2)) /\ ((int_lt (y0 y1 y2) (int_abs y2)) /\ (y1 = (int_add (int_mul (div y1 y2) y2) (y0 y1 y2))))).
Definition term42 := fun y0 : type1551 => forall y1 : int, forall y2 : int, @COND Prop (y2 = (int_of_num (NUMERAL 0))) (((@ε ((prod nat (prod nat nat)) -> int -> int -> int) (fun y3 : type1305 => forall y4 : type1674, exists y5 : type1551, forall y6 : int, forall y7 : int, @COND Prop (y7 = (int_of_num (NUMERAL 0))) (((y3 y4 y6 y7) = (int_of_num (NUMERAL 0))) /\ ((y5 y6 y7) = y6)) ((int_le (int_of_num (NUMERAL 0)) (y5 y6 y7)) /\ ((int_lt (y5 y6 y7) (int_abs y7)) /\ (y6 = (int_add (int_mul (y3 y4 y6 y7) y7) (y5 y6 y7)))))) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))))) y1 y2) = (int_of_num (NUMERAL 0))) /\ ((y0 y1 y2) = y1)) ((int_le (int_of_num (NUMERAL 0)) (y0 y1 y2)) /\ ((int_lt (y0 y1 y2) (int_abs y2)) /\ (y1 = (int_add (int_mul (@ε ((prod nat (prod nat nat)) -> int -> int -> int) (fun y3 : type1305 => forall y4 : type1674, exists y5 : type1551, forall y6 : int, forall y7 : int, @COND Prop (y7 = (int_of_num (NUMERAL 0))) (((y3 y4 y6 y7) = (int_of_num (NUMERAL 0))) /\ ((y5 y6 y7) = y6)) ((int_le (int_of_num (NUMERAL 0)) (y5 y6 y7)) /\ ((int_lt (y5 y6 y7) (int_abs y7)) /\ (y6 = (int_add (int_mul (y3 y4 y6 y7) y7) (y5 y6 y7)))))) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))))) y1 y2) y2) (y0 y1 y2))))).
Definition term60 := fun y0 : type1674 => exists y1 : type1551, forall y2 : int, forall y3 : int, @COND Prop (y3 = (int_of_num (NUMERAL 0))) (((div y2 y3) = (int_of_num (NUMERAL 0))) /\ ((y1 y2 y3) = y2)) ((int_le (int_of_num (NUMERAL 0)) (y1 y2 y3)) /\ ((int_lt (y1 y2 y3) (int_abs y3)) /\ (y2 = (int_add (int_mul (div y2 y3) y3) (y1 y2 y3))))).
Definition term48 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := exists y0 : a0 -> a1, forall y1 : a0, x0 y1 (y0 y1).
Definition term51 := forall y0 : type1674, exists y1 : type1551, (fun y2 : type1674 => fun y3 : type1551 => forall y4 : int, forall y5 : int, @COND Prop (y5 = (int_of_num (NUMERAL 0))) (((div y4 y5) = (int_of_num (NUMERAL 0))) /\ ((y3 y4 y5) = y4)) ((int_le (int_of_num (NUMERAL 0)) (y3 y4 y5)) /\ ((int_lt (y3 y4 y5) (int_abs y5)) /\ (y4 = (int_add (int_mul (div y4 y5) y5) (y3 y4 y5)))))) y0 y1.
Definition term49 (x0 : type1299) := forall y0 : type1674, exists y1 : type1551, x0 y0 y1.
Definition term11 (x0 : int) (x1 : int) := and ((@ε ((prod nat (prod nat nat)) -> int -> int -> int) (fun y0 : type1305 => forall y1 : type1674, exists y2 : type1551, forall y3 : int, forall y4 : int, @COND Prop (y4 = (int_of_num (NUMERAL 0))) (((y0 y1 y3 y4) = (int_of_num (NUMERAL 0))) /\ ((y2 y3 y4) = y3)) ((int_le (int_of_num (NUMERAL 0)) (y2 y3 y4)) /\ ((int_lt (y2 y3 y4) (int_abs y4)) /\ (y3 = (int_add (int_mul (y0 y1 y3 y4) y4) (y2 y3 y4)))))) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))))) x0 x1) = (int_of_num (NUMERAL 0))).
Definition term63 (x0 : type1305) (x1 : type1674) := (fun y0 : type1674 => fun y1 : type1551 => forall y2 : int, forall y3 : int, @COND Prop (y3 = (int_of_num (NUMERAL 0))) (((div y2 y3) = (int_of_num (NUMERAL 0))) /\ ((y1 y2 y3) = y2)) ((int_le (int_of_num (NUMERAL 0)) (y1 y2 y3)) /\ ((int_lt (y1 y2 y3) (int_abs y3)) /\ (y2 = (int_add (int_mul (div y2 y3) y3) (y1 y2 y3)))))) x1 (x0 x1).
Definition term37 (x0 : type1551) (x1 : int) := forall y0 : int, @COND Prop (y0 = (int_of_num (NUMERAL 0))) (((div x1 y0) = (int_of_num (NUMERAL 0))) /\ ((x0 x1 y0) = x1)) ((int_le (int_of_num (NUMERAL 0)) (x0 x1 y0)) /\ ((int_lt (x0 x1 y0) (int_abs y0)) /\ (x1 = (int_add (int_mul (div x1 y0) y0) (x0 x1 y0))))).
Definition term36 (x0 : type1551) (x1 : int) := forall y0 : int, @COND Prop (y0 = (int_of_num (NUMERAL 0))) (((@ε ((prod nat (prod nat nat)) -> int -> int -> int) (fun y1 : type1305 => forall y2 : type1674, exists y3 : type1551, forall y4 : int, forall y5 : int, @COND Prop (y5 = (int_of_num (NUMERAL 0))) (((y1 y2 y4 y5) = (int_of_num (NUMERAL 0))) /\ ((y3 y4 y5) = y4)) ((int_le (int_of_num (NUMERAL 0)) (y3 y4 y5)) /\ ((int_lt (y3 y4 y5) (int_abs y5)) /\ (y4 = (int_add (int_mul (y1 y2 y4 y5) y5) (y3 y4 y5)))))) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))))) x1 y0) = (int_of_num (NUMERAL 0))) /\ ((x0 x1 y0) = x1)) ((int_le (int_of_num (NUMERAL 0)) (x0 x1 y0)) /\ ((int_lt (x0 x1 y0) (int_abs y0)) /\ (x1 = (int_add (int_mul (@ε ((prod nat (prod nat nat)) -> int -> int -> int) (fun y1 : type1305 => forall y2 : type1674, exists y3 : type1551, forall y4 : int, forall y5 : int, @COND Prop (y5 = (int_of_num (NUMERAL 0))) (((y1 y2 y4 y5) = (int_of_num (NUMERAL 0))) /\ ((y3 y4 y5) = y4)) ((int_le (int_of_num (NUMERAL 0)) (y3 y4 y5)) /\ ((int_lt (y3 y4 y5) (int_abs y5)) /\ (y4 = (int_add (int_mul (y1 y2 y4 y5) y5) (y3 y4 y5)))))) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))))) x1 y0) y0) (x0 x1 y0))))).
Definition term29 (x0 : type1551) (x1 : int) (x2 : int) := and (int_le (int_of_num (NUMERAL 0)) (x0 x1 x2)).
Definition term59 := fun y0 : type1674 => exists y1 : type1551, (fun y2 : type1674 => fun y3 : type1551 => forall y4 : int, forall y5 : int, @COND Prop (y5 = (int_of_num (NUMERAL 0))) (((div y4 y5) = (int_of_num (NUMERAL 0))) /\ ((y3 y4 y5) = y4)) ((int_le (int_of_num (NUMERAL 0)) (y3 y4 y5)) /\ ((int_lt (y3 y4 y5) (int_abs y5)) /\ (y4 = (int_add (int_mul (div y4 y5) y5) (y3 y4 y5)))))) y0 y1.
Definition term39 (x0 : type1551) := fun y0 : int => forall y1 : int, @COND Prop (y1 = (int_of_num (NUMERAL 0))) (((div y0 y1) = (int_of_num (NUMERAL 0))) /\ ((x0 y0 y1) = y0)) ((int_le (int_of_num (NUMERAL 0)) (x0 y0 y1)) /\ ((int_lt (x0 y0 y1) (int_abs y1)) /\ (y0 = (int_add (int_mul (div y0 y1) y1) (x0 y0 y1))))).
Definition term38 (x0 : type1551) := fun y0 : int => forall y1 : int, @COND Prop (y1 = (int_of_num (NUMERAL 0))) (((@ε ((prod nat (prod nat nat)) -> int -> int -> int) (fun y2 : type1305 => forall y3 : type1674, exists y4 : type1551, forall y5 : int, forall y6 : int, @COND Prop (y6 = (int_of_num (NUMERAL 0))) (((y2 y3 y5 y6) = (int_of_num (NUMERAL 0))) /\ ((y4 y5 y6) = y5)) ((int_le (int_of_num (NUMERAL 0)) (y4 y5 y6)) /\ ((int_lt (y4 y5 y6) (int_abs y6)) /\ (y5 = (int_add (int_mul (y2 y3 y5 y6) y6) (y4 y5 y6)))))) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))))) y0 y1) = (int_of_num (NUMERAL 0))) /\ ((x0 y0 y1) = y0)) ((int_le (int_of_num (NUMERAL 0)) (x0 y0 y1)) /\ ((int_lt (x0 y0 y1) (int_abs y1)) /\ (y0 = (int_add (int_mul (@ε ((prod nat (prod nat nat)) -> int -> int -> int) (fun y2 : type1305 => forall y3 : type1674, exists y4 : type1551, forall y5 : int, forall y6 : int, @COND Prop (y6 = (int_of_num (NUMERAL 0))) (((y2 y3 y5 y6) = (int_of_num (NUMERAL 0))) /\ ((y4 y5 y6) = y5)) ((int_le (int_of_num (NUMERAL 0)) (y4 y5 y6)) /\ ((int_lt (y4 y5 y6) (int_abs y6)) /\ (y5 = (int_add (int_mul (y2 y3 y5 y6) y6) (y4 y5 y6)))))) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))))) y0 y1) y1) (x0 y0 y1))))).