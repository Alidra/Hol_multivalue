Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term19 (x0 : int) (x1 : int) := div x0 (int_neg x1).
Definition term91 (x0 : int) := int_mul x0 (int_of_num (NUMERAL 0)).
Definition term50 := fun y0 : int => forall y1 : int, ((div y0 y1) = (int_of_num (NUMERAL 0))) = ((y1 = (int_of_num (NUMERAL 0))) \/ ((int_le (int_of_num (NUMERAL 0)) y0) /\ (int_lt y0 (int_abs y1)))).
Definition term6 := fun y0 : int => forall y1 : int, (y0 = y1) = ((int_le y0 y1) /\ (int_le y1 y0)).
Definition term136 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> (Peano.le (NUMERAL (BIT1 0)) x0) = True.
Definition term1 (x0 : int) := fun y0 : int => ((int_le x0 y0) /\ (int_le y0 x0)) = (x0 = y0).
Definition term124 (x0 : int) (x1 : int) := (fun y0 : int => forall y1 : int, (int_lt (int_of_num (NUMERAL 0)) x0) -> (int_le (div y0 x0) y1) = (int_lt y0 (int_mul x0 (int_add y1 (int_of_num (NUMERAL (BIT1 0))))))) x1.
Definition term115 (x0 : int) (x1 : int) := (fun y0 : int => forall y1 : int, (int_lt (int_of_num (NUMERAL 0)) x0) -> (int_le y1 (div y0 x0)) = (int_le (int_mul x0 y1) y0)) x1.
Definition term23 (x0 : int -> Prop) := (forall y0 : nat, x0 (int_of_num y0)) /\ (forall y0 : nat, x0 (int_neg (int_of_num y0))).
Definition term18 (x0 : int) (x1 : int) := (fun y0 : int => (div x0 (int_neg y0)) = (int_neg (div x0 y0))) x1.
Definition term101 (x0 : nat) := Peano.le (NUMERAL (BIT1 0)) x0.
Definition term109 (x0 : nat) (x1 : nat) := int_lt (int_of_num x0) (int_of_num x1).
Definition term144 (x0 : int) (x1 : nat) := and (int_le (div x0 (int_of_num x1)) (int_of_num (NUMERAL 0))).
Definition term80 := @eq nat (NUMERAL 0).
Definition term139 := int_add (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0))).
Definition term58 (x0 : int) (x1 : nat) := @eq Prop ((div x0 (int_of_num x1)) = (int_of_num (NUMERAL 0))).
Definition term15 := int_of_num (NUMERAL 0).
Definition term81 (x0 : int) := int_lt x0 (int_of_num (NUMERAL 0)).
Definition term60 (x0 : nat) := or ((int_neg (int_of_num x0)) = (int_of_num (NUMERAL 0))).
Definition term130 (x0 : int) := (fun y0 : int => forall y1 : int, (y0 = y1) = ((int_le y0 y1) /\ (int_le y1 y0))) x0.
Definition term16 (x0 : int) := (fun y0 : int => forall y1 : int, (div y0 (int_neg y1)) = (int_neg (div y0 y1))) x0.
Definition term116 (x0 : int) (x1 : int) := forall y0 : int, (int_lt (int_of_num (NUMERAL 0)) x0) -> (int_le y0 (div x1 x0)) = (int_le (int_mul x0 y0) x1).
Definition term142 (x0 : nat) := int_mul (int_of_num x0) (int_add (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0)))).
Definition term122 (x0 : int) := (fun y0 : int => forall y1 : int, forall y2 : int, (int_lt (int_of_num (NUMERAL 0)) y0) -> (int_le (div y1 y0) y2) = (int_lt y1 (int_mul y0 (int_add y2 (int_of_num (NUMERAL (BIT1 0))))))) x0.
Definition term113 (x0 : int) := (fun y0 : int => forall y1 : int, forall y2 : int, (int_lt (int_of_num (NUMERAL 0)) y0) -> (int_le y2 (div y1 y0)) = (int_le (int_mul y0 y2) y1)) x0.
Definition term128 (x0 : int) (x1 : int) (x2 : int) := int_le (div x0 x1) x2.
Definition term107 (x0 : nat) := forall y0 : nat, (int_lt (int_of_num x0) (int_of_num y0)) = (Peano.lt x0 y0).
Definition term74 (x0 : nat) := forall y0 : nat, ((int_of_num x0) = (int_of_num y0)) = (x0 = y0).
Definition term145 (x0 : int) (x1 : nat) := and (int_lt x0 (int_of_num x1)).
Definition term36 (x0 : int) := fun y0 : nat => (fun y1 : int => ((div x0 y1) = (int_of_num (NUMERAL 0))) = ((y1 = (int_of_num (NUMERAL 0))) \/ ((int_le (int_of_num (NUMERAL 0)) x0) /\ (int_lt x0 (int_abs y1))))) (int_of_num y0).
Definition term21 (x0 : int -> Prop) := (fun y0 : int -> Prop => (forall y1 : int, y0 y1) = ((forall y1 : nat, y0 (int_of_num y1)) /\ (forall y1 : nat, y0 (int_neg (int_of_num y1))))) x0.
Definition term153 (x0 : nat) (x1 : int) := (int_lt x1 (int_of_num x0)) /\ (int_le (int_of_num (NUMERAL 0)) x1).
Definition term79 := @eq int (int_of_num (NUMERAL 0)).
Definition term28 (x0 : int) (x1 : int) := (x1 = (int_of_num (NUMERAL 0))) \/ ((int_le (int_of_num (NUMERAL 0)) x0) /\ (int_lt x0 (int_abs x1))).
Definition term133 (x0 : int) (x1 : nat) := (int_lt (int_of_num (NUMERAL 0)) (int_of_num x1)) -> (int_le (div x0 (int_of_num x1)) (int_of_num (NUMERAL 0))) = (int_lt x0 (int_mul (int_of_num x1) (int_add (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0)))))).
Definition term68 (x0 : int) (x1 : nat) := (int_le (int_of_num (NUMERAL 0)) x0) /\ (int_lt x0 (int_abs (int_of_num x1))).
Definition term42 (x0 : int) (x1 : nat) := (fun y0 : int => ((div x0 y0) = (int_of_num (NUMERAL 0))) = ((y0 = (int_of_num (NUMERAL 0))) \/ ((int_le (int_of_num (NUMERAL 0)) x0) /\ (int_lt x0 (int_abs y0))))) (int_neg (int_of_num x1)).
Definition term103 := forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0.
Definition term125 (x0 : int) (x1 : int) := forall y0 : int, (int_lt (int_of_num (NUMERAL 0)) x1) -> (int_le (div x0 x1) y0) = (int_lt x0 (int_mul x1 (int_add y0 (int_of_num (NUMERAL (BIT1 0)))))).
Definition term82 (x0 : int) := (int_le (int_of_num (NUMERAL 0)) x0) /\ (int_lt x0 (int_of_num (NUMERAL 0))).
Definition term129 (x0 : int) (x1 : int) (x2 : int) := int_lt x0 (int_mul x1 (int_add x2 (int_of_num (NUMERAL (BIT1 0))))).
Definition term54 (x0 : int) (x1 : nat) := int_neg (div x0 (int_of_num x1)).
Definition term92 (x0 : int) := (fun y0 : int => (int_add (int_of_num (NUMERAL 0)) y0) = y0) x0.
Definition term17 (x0 : int) := forall y0 : int, (div x0 (int_neg y0)) = (int_neg (div x0 y0)).
Definition term3 (x0 : int) := forall y0 : int, ((int_le x0 y0) /\ (int_le y0 x0)) = (x0 = y0).
Definition term56 (x0 : int) (x1 : nat) := @eq int (int_neg (div x0 (int_of_num x1))).
Definition term14 (x0 : int) := (fun y0 : int => ((int_neg y0) = (int_of_num (NUMERAL 0))) = (y0 = (int_of_num (NUMERAL 0)))) x0.
Definition term110 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, (y0 /\ y1) = (y1 /\ y0)) x0.
Definition term64 (x0 : int) (x1 : nat) := int_lt x0 (int_abs (int_neg (int_of_num x1))).
Definition term134 (x0 : nat) := int_lt (int_of_num (NUMERAL 0)) (int_of_num x0).
Definition term141 (x0 : nat) := int_mul (int_of_num x0).
Definition term86 (x0 : int) (x1 : nat) := (int_le (int_of_num (NUMERAL 0)) x0) /\ (int_lt x0 (int_of_num x1)).
Definition term85 (x0 : int) (x1 : nat) := int_lt x0 (int_of_num x1).
Definition term48 (x0 : int) := forall y0 : nat, ((div x0 (int_neg (int_of_num y0))) = (int_of_num (NUMERAL 0))) = (((int_neg (int_of_num y0)) = (int_of_num (NUMERAL 0))) \/ ((int_le (int_of_num (NUMERAL 0)) x0) /\ (int_lt x0 (int_abs (int_neg (int_of_num y0)))))).
Definition term39 (x0 : int) := forall y0 : nat, ((div x0 (int_of_num y0)) = (int_of_num (NUMERAL 0))) = (((int_of_num y0) = (int_of_num (NUMERAL 0))) \/ ((int_le (int_of_num (NUMERAL 0)) x0) /\ (int_lt x0 (int_abs (int_of_num y0))))).
Definition term93 (x0 : int) := int_add (int_of_num (NUMERAL 0)) x0.
Definition term121 (x0 : int) (x1 : int) (x2 : int) := int_le (int_mul x0 x1) x2.
Definition term11 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term149 (x0 : nat) := int_mul (int_of_num x0) (int_of_num (NUMERAL 0)).
Definition term13 (x0 : int) := int_abs (int_neg x0).
Definition term67 (x0 : int) (x1 : nat) := (int_le (int_of_num (NUMERAL 0)) x0) /\ (int_lt x0 (int_abs (int_neg (int_of_num x1)))).
Definition term32 (x0 : int) := @eq Prop (forall y0 : int, ((div x0 y0) = (int_of_num (NUMERAL 0))) = ((y0 = (int_of_num (NUMERAL 0))) \/ ((int_le (int_of_num (NUMERAL 0)) x0) /\ (int_lt x0 (int_abs y0))))).
Definition term34 (x0 : int) (x1 : nat) := div x0 (int_of_num x1).
Definition term99 (x0 : nat) := (fun y0 : nat => (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) x0.
Definition term138 (x0 : int) (x1 : nat) := int_lt x0 (int_mul (int_of_num x1) (int_add (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0))))).
Definition term148 (x0 : nat) (x1 : int) := int_le (int_mul (int_of_num x0) (int_of_num (NUMERAL 0))) x1.
Definition term135 (x0 : nat) := (Peano.le (NUMERAL (BIT1 0)) x0) -> (Peano.lt (NUMERAL 0) x0) = True.
Definition term119 (x0 : int) := int_lt (int_of_num (NUMERAL 0)) x0.
Definition term25 (x0 : int) := (forall y0 : nat, (fun y1 : int => ((div x0 y1) = (int_of_num (NUMERAL 0))) = ((y1 = (int_of_num (NUMERAL 0))) \/ ((int_le (int_of_num (NUMERAL 0)) x0) /\ (int_lt x0 (int_abs y1))))) (int_of_num y0)) /\ (forall y0 : nat, (fun y1 : int => ((div x0 y1) = (int_of_num (NUMERAL 0))) = ((y1 = (int_of_num (NUMERAL 0))) \/ ((int_le (int_of_num (NUMERAL 0)) x0) /\ (int_lt x0 (int_abs y1))))) (int_neg (int_of_num y0))).
Definition term12 (x0 : int) := (fun y0 : int => (int_abs (int_neg y0)) = (int_abs y0)) x0.
Definition term55 (x0 : int) (x1 : nat) := @eq int (div x0 (int_neg (int_of_num x1))).
Definition term41 (x0 : int) := and (forall y0 : nat, ((div x0 (int_of_num y0)) = (int_of_num (NUMERAL 0))) = (((int_of_num y0) = (int_of_num (NUMERAL 0))) \/ ((int_le (int_of_num (NUMERAL 0)) x0) /\ (int_lt x0 (int_abs (int_of_num y0)))))).
Definition term112 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => (x0 /\ y0) = (y0 /\ x0)) x1.
Definition term96 := (forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))).
Definition term43 (x0 : int) (x1 : nat) := div x0 (int_neg (int_of_num x1)).
Definition term22 (x0 : int -> Prop) := forall y0 : int, x0 y0.
Definition term104 (x0 : nat) := (fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) x0.
Definition term27 (x0 : int) (x1 : int) := (fun y0 : int => ((div x0 y0) = (int_of_num (NUMERAL 0))) = ((y0 = (int_of_num (NUMERAL 0))) \/ ((int_le (int_of_num (NUMERAL 0)) x0) /\ (int_lt x0 (int_abs y0))))) x1.
Definition term10 (x0 : nat) := (x0 = (NUMERAL 0)) \/ (~ (x0 = (NUMERAL 0))).
Definition term30 (x0 : int) := forall y0 : int, ((div x0 y0) = (int_of_num (NUMERAL 0))) = ((y0 = (int_of_num (NUMERAL 0))) \/ ((int_le (int_of_num (NUMERAL 0)) x0) /\ (int_lt x0 (int_abs y0)))).
Definition term53 := forall y0 : int, (forall y1 : nat, ((div y0 (int_of_num y1)) = (int_of_num (NUMERAL 0))) = (((int_of_num y1) = (int_of_num (NUMERAL 0))) \/ ((int_le (int_of_num (NUMERAL 0)) y0) /\ (int_lt y0 (int_abs (int_of_num y1)))))) /\ (forall y1 : nat, ((div y0 (int_neg (int_of_num y1))) = (int_of_num (NUMERAL 0))) = (((int_neg (int_of_num y1)) = (int_of_num (NUMERAL 0))) \/ ((int_le (int_of_num (NUMERAL 0)) y0) /\ (int_lt y0 (int_abs (int_neg (int_of_num y1))))))).
Definition term40 (x0 : int) := and (forall y0 : nat, (fun y1 : int => ((div x0 y1) = (int_of_num (NUMERAL 0))) = ((y1 = (int_of_num (NUMERAL 0))) \/ ((int_le (int_of_num (NUMERAL 0)) x0) /\ (int_lt x0 (int_abs y1))))) (int_of_num y0)).
Definition term132 (x0 : int) (x1 : nat) := (int_le (div x0 (int_of_num x1)) (int_of_num (NUMERAL 0))) /\ (int_le (int_of_num (NUMERAL 0)) (div x0 (int_of_num x1))).
Definition term123 (x0 : int) := forall y0 : int, forall y1 : int, (int_lt (int_of_num (NUMERAL 0)) x0) -> (int_le (div y0 x0) y1) = (int_lt y0 (int_mul x0 (int_add y1 (int_of_num (NUMERAL (BIT1 0)))))).
Definition term114 (x0 : int) := forall y0 : int, forall y1 : int, (int_lt (int_of_num (NUMERAL 0)) x0) -> (int_le y1 (div y0 x0)) = (int_le (int_mul x0 y1) y0).
Definition term71 := forall y0 : int, forall y1 : nat, ((div y0 (int_of_num y1)) = (int_of_num (NUMERAL 0))) = (((int_of_num y1) = (int_of_num (NUMERAL 0))) \/ ((int_le (int_of_num (NUMERAL 0)) y0) /\ (int_lt y0 (int_abs (int_of_num y1))))).
Definition term52 := forall y0 : int, forall y1 : int, ((div y0 y1) = (int_of_num (NUMERAL 0))) = ((y1 = (int_of_num (NUMERAL 0))) \/ ((int_le (int_of_num (NUMERAL 0)) y0) /\ (int_lt y0 (int_abs y1)))).
Definition term8 := forall y0 : int, forall y1 : int, (y0 = y1) = ((int_le y0 y1) /\ (int_le y1 y0)).
Definition term7 := forall y0 : int, forall y1 : int, ((int_le y0 y1) /\ (int_le y1 y0)) = (y0 = y1).
Definition term33 (x0 : int) (x1 : nat) := (fun y0 : int => ((div x0 y0) = (int_of_num (NUMERAL 0))) = ((y0 = (int_of_num (NUMERAL 0))) \/ ((int_le (int_of_num (NUMERAL 0)) x0) /\ (int_lt x0 (int_abs y0))))) (int_of_num x1).
Definition term63 (x0 : nat) := int_abs (int_of_num x0).
Definition term51 := fun y0 : int => (forall y1 : nat, ((div y0 (int_of_num y1)) = (int_of_num (NUMERAL 0))) = (((int_of_num y1) = (int_of_num (NUMERAL 0))) \/ ((int_le (int_of_num (NUMERAL 0)) y0) /\ (int_lt y0 (int_abs (int_of_num y1)))))) /\ (forall y1 : nat, ((div y0 (int_neg (int_of_num y1))) = (int_of_num (NUMERAL 0))) = (((int_neg (int_of_num y1)) = (int_of_num (NUMERAL 0))) \/ ((int_le (int_of_num (NUMERAL 0)) y0) /\ (int_lt y0 (int_abs (int_neg (int_of_num y1))))))).
Definition term77 (x0 : int) := div x0 (int_of_num (NUMERAL 0)).
Definition term108 (x0 : nat) (x1 : nat) := (fun y0 : nat => (int_lt (int_of_num x0) (int_of_num y0)) = (Peano.lt x0 y0)) x1.
Definition term120 (x0 : int) (x1 : int) (x2 : int) := int_le x0 (div x1 x2).
Definition term5 := fun y0 : int => forall y1 : int, ((int_le y0 y1) /\ (int_le y1 y0)) = (y0 = y1).
Definition term127 (x0 : int) (x1 : int) (x2 : int) := (int_lt (int_of_num (NUMERAL 0)) x1) -> (int_le (div x0 x1) x2) = (int_lt x0 (int_mul x1 (int_add x2 (int_of_num (NUMERAL (BIT1 0)))))).
Definition term26 (x0 : int) := fun y0 : int => ((div x0 y0) = (int_of_num (NUMERAL 0))) = ((y0 = (int_of_num (NUMERAL 0))) \/ ((int_le (int_of_num (NUMERAL 0)) x0) /\ (int_lt x0 (int_abs y0)))).
Definition term44 (x0 : int) (x1 : nat) := ((int_neg (int_of_num x1)) = (int_of_num (NUMERAL 0))) \/ ((int_le (int_of_num (NUMERAL 0)) x0) /\ (int_lt x0 (int_abs (int_neg (int_of_num x1))))).
Definition term154 (x0 : int) (x1 : nat) := @eq Prop ((int_le (int_of_num (NUMERAL 0)) x0) /\ (int_lt x0 (int_of_num x1))).
Definition term126 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => (int_lt (int_of_num (NUMERAL 0)) x1) -> (int_le (div x0 x1) y0) = (int_lt x0 (int_mul x1 (int_add y0 (int_of_num (NUMERAL (BIT1 0))))))) x2.
Definition term31 (x0 : int) := @eq Prop (forall y0 : int, (fun y1 : int => ((div x0 y1) = (int_of_num (NUMERAL 0))) = ((y1 = (int_of_num (NUMERAL 0))) \/ ((int_le (int_of_num (NUMERAL 0)) x0) /\ (int_lt x0 (int_abs y1))))) y0).
Definition term78 (x0 : int) (x1 : nat) := @eq int (div x0 (int_of_num x1)).
Definition term97 := (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0))).
Definition term69 (x0 : int) := (forall y0 : nat, ((div x0 (int_of_num y0)) = (int_of_num (NUMERAL 0))) = (((int_of_num y0) = (int_of_num (NUMERAL 0))) \/ ((int_le (int_of_num (NUMERAL 0)) x0) /\ (int_lt x0 (int_abs (int_of_num y0)))))) /\ (forall y0 : nat, ((div x0 (int_of_num y0)) = (int_of_num (NUMERAL 0))) = (((int_of_num y0) = (int_of_num (NUMERAL 0))) \/ ((int_le (int_of_num (NUMERAL 0)) x0) /\ (int_lt x0 (int_abs (int_of_num y0)))))).
Definition term49 (x0 : int) := (forall y0 : nat, ((div x0 (int_of_num y0)) = (int_of_num (NUMERAL 0))) = (((int_of_num y0) = (int_of_num (NUMERAL 0))) \/ ((int_le (int_of_num (NUMERAL 0)) x0) /\ (int_lt x0 (int_abs (int_of_num y0)))))) /\ (forall y0 : nat, ((div x0 (int_neg (int_of_num y0))) = (int_of_num (NUMERAL 0))) = (((int_neg (int_of_num y0)) = (int_of_num (NUMERAL 0))) \/ ((int_le (int_of_num (NUMERAL 0)) x0) /\ (int_lt x0 (int_abs (int_neg (int_of_num y0))))))).
Definition term66 (x0 : int) := and (int_le (int_of_num (NUMERAL 0)) x0).
Definition term65 (x0 : int) (x1 : nat) := int_lt x0 (int_abs (int_of_num x1)).
Definition term89 (x0 : int) := int_mul x0 (int_of_num (NUMERAL (BIT1 0))).
Definition term59 (x0 : nat) := int_neg (int_of_num x0).
Definition term72 (x0 : nat) := (fun y0 : nat => (int_abs (int_of_num y0)) = (int_of_num y0)) x0.
Definition term131 (x0 : int) (x1 : int) := (fun y0 : int => (x0 = y0) = ((int_le x0 y0) /\ (int_le y0 x0))) x1.
Definition term106 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (int_lt (int_of_num y0) (int_of_num y1)) = (Peano.lt y0 y1)) x0.
Definition term73 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((int_of_num y0) = (int_of_num y1)) = (y0 = y1)) x0.
Definition term20 (x0 : int) (x1 : int) := int_neg (div x0 x1).
Definition term95 := (forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0))))).
Definition term98 := forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0.
Definition term29 (x0 : int) := fun y0 : int => (fun y1 : int => ((div x0 y1) = (int_of_num (NUMERAL 0))) = ((y1 = (int_of_num (NUMERAL 0))) \/ ((int_le (int_of_num (NUMERAL 0)) x0) /\ (int_lt x0 (int_abs y1))))) y0.
Definition term38 (x0 : int) := forall y0 : nat, (fun y1 : int => ((div x0 y1) = (int_of_num (NUMERAL 0))) = ((y1 = (int_of_num (NUMERAL 0))) \/ ((int_le (int_of_num (NUMERAL 0)) x0) /\ (int_lt x0 (int_abs y1))))) (int_of_num y0).
Definition term118 (x0 : int) (x1 : int) (x2 : int) := (int_lt (int_of_num (NUMERAL 0)) x0) -> (int_le x1 (div x2 x0)) = (int_le (int_mul x0 x1) x2).
Definition term0 (x0 : int) (x1 : int) := (int_le x1 x0) /\ (int_le x0 x1).
Definition term146 (x0 : nat) (x1 : int) := (int_lt (int_of_num (NUMERAL 0)) (int_of_num x0)) -> (int_le (int_of_num (NUMERAL 0)) (div x1 (int_of_num x0))) = (int_le (int_mul (int_of_num x0) (int_of_num (NUMERAL 0))) x1).
Definition term46 (x0 : int) := fun y0 : nat => ((div x0 (int_neg (int_of_num y0))) = (int_of_num (NUMERAL 0))) = (((int_neg (int_of_num y0)) = (int_of_num (NUMERAL 0))) \/ ((int_le (int_of_num (NUMERAL 0)) x0) /\ (int_lt x0 (int_abs (int_neg (int_of_num y0)))))).
Definition term37 (x0 : int) := fun y0 : nat => ((div x0 (int_of_num y0)) = (int_of_num (NUMERAL 0))) = (((int_of_num y0) = (int_of_num (NUMERAL 0))) \/ ((int_le (int_of_num (NUMERAL 0)) x0) /\ (int_lt x0 (int_abs (int_of_num y0))))).
Definition term90 (x0 : int) := (fun y0 : int => (int_mul y0 (int_of_num (NUMERAL 0))) = (int_of_num (NUMERAL 0))) x0.
Definition term76 (x0 : int) := (fun y0 : int => (div y0 (int_of_num (NUMERAL 0))) = (int_of_num (NUMERAL 0))) x0.
Definition term2 (x0 : int) := fun y0 : int => (x0 = y0) = ((int_le x0 y0) /\ (int_le y0 x0)).
Definition term84 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> (x0 = (NUMERAL 0)) = False.
Definition term100 (x0 : nat) := (Peano.le (NUMERAL (BIT1 0)) x0) -> Peano.lt (NUMERAL 0) x0.
Definition term87 (x0 : int) (x1 : nat) := False \/ ((int_le (int_of_num (NUMERAL 0)) x0) /\ (int_lt x0 (int_of_num x1))).
Definition term47 (x0 : int) := forall y0 : nat, (fun y1 : int => ((div x0 y1) = (int_of_num (NUMERAL 0))) = ((y1 = (int_of_num (NUMERAL 0))) \/ ((int_le (int_of_num (NUMERAL 0)) x0) /\ (int_lt x0 (int_abs y1))))) (int_neg (int_of_num y0)).
Definition term150 (x0 : nat) := int_le (int_mul (int_of_num x0) (int_of_num (NUMERAL 0))).
Definition term143 (x0 : nat) := int_mul (int_of_num x0) (int_of_num (NUMERAL (BIT1 0))).
Definition term88 (x0 : int) := (fun y0 : int => (int_mul y0 (int_of_num (NUMERAL (BIT1 0)))) = y0) x0.
Definition term152 (x0 : int) := int_le (int_of_num (NUMERAL 0)) x0.
Definition term105 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) x0.
Definition term83 (x0 : int) := True \/ ((int_le (int_of_num (NUMERAL 0)) x0) /\ (int_lt x0 (int_of_num (NUMERAL 0)))).
Definition term151 := int_le (int_of_num (NUMERAL 0)).
Definition term62 (x0 : nat) := int_abs (int_neg (int_of_num x0)).
Definition term111 (x0 : Prop) := forall y0 : Prop, (x0 /\ y0) = (y0 /\ x0).
Definition term117 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => (int_lt (int_of_num (NUMERAL 0)) x0) -> (int_le y0 (div x1 x0)) = (int_le (int_mul x0 y0) x1)) x2.
Definition term4 (x0 : int) := forall y0 : int, (x0 = y0) = ((int_le x0 y0) /\ (int_le y0 x0)).
Definition term75 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((int_of_num x0) = (int_of_num y0)) = (x0 = y0)) x1.
Definition term70 := fun y0 : int => forall y1 : nat, ((div y0 (int_of_num y1)) = (int_of_num (NUMERAL 0))) = (((int_of_num y1) = (int_of_num (NUMERAL 0))) \/ ((int_le (int_of_num (NUMERAL 0)) y0) /\ (int_lt y0 (int_abs (int_of_num y1))))).
Definition term94 := (forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))).
Definition term137 (x0 : int) (x1 : nat) := int_le (div x0 (int_of_num x1)) (int_of_num (NUMERAL 0)).
Definition term102 (x0 : nat) := Peano.lt (NUMERAL 0) x0.
Definition term57 (x0 : int) (x1 : nat) := @eq Prop ((div x0 (int_neg (int_of_num x1))) = (int_of_num (NUMERAL 0))).
Definition term24 (x0 : int) := forall y0 : int, (fun y1 : int => ((div x0 y1) = (int_of_num (NUMERAL 0))) = ((y1 = (int_of_num (NUMERAL 0))) \/ ((int_le (int_of_num (NUMERAL 0)) x0) /\ (int_lt x0 (int_abs y1))))) y0.
Definition term140 := int_of_num (NUMERAL (BIT1 0)).
Definition term35 (x0 : int) (x1 : nat) := ((int_of_num x1) = (int_of_num (NUMERAL 0))) \/ ((int_le (int_of_num (NUMERAL 0)) x0) /\ (int_lt x0 (int_abs (int_of_num x1)))).
Definition term147 (x0 : int) (x1 : nat) := int_le (int_of_num (NUMERAL 0)) (div x0 (int_of_num x1)).
Definition term9 (x0 : nat) := (fun y0 : Prop => y0 \/ (~ y0)) (x0 = (NUMERAL 0)).
Definition term45 (x0 : int) := fun y0 : nat => (fun y1 : int => ((div x0 y1) = (int_of_num (NUMERAL 0))) = ((y1 = (int_of_num (NUMERAL 0))) \/ ((int_le (int_of_num (NUMERAL 0)) x0) /\ (int_lt x0 (int_abs y1))))) (int_neg (int_of_num y0)).
Definition term61 (x0 : nat) := or ((int_of_num x0) = (int_of_num (NUMERAL 0))).
