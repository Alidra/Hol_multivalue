Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term40 (x0 : nat) (x1 : real) (x2 : nat) := (fun y0 : nat => (real_pow x1 (Nat.add x0 y0)) = (real_mul (real_pow x1 x0) (real_pow x1 y0))) x2.
Definition term9 := forall y0 : real, (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_mul (real_inv y0) y0) = (real_of_num (NUMERAL (BIT1 0))).
Definition term21 (x0 : real) (x1 : real) (x2 : real) := real_mul x0 (real_mul x1 x2).
Definition term60 (x0 : real) (x1 : nat) (x2 : nat) := (fun y0 : nat => (real_pow x0 (Nat.sub y0 x1)) = (real_div (real_pow x0 y0) (real_pow x0 x1))) (Nat.add x1 x2).
Definition term65 (x0 : real) (x1 : nat) (x2 : nat) := @eq real (real_pow x0 (Nat.sub (Nat.add x2 x1) x2)).
Definition term79 := real_of_num (NUMERAL 0).
Definition term78 (x0 : real) := (~ (x0 = (real_of_num (NUMERAL 0)))) -> (x0 = (real_of_num (NUMERAL 0))) = False.
Definition term64 (x0 : nat) (x1 : real) (x2 : nat) := @eq Prop ((real_pow x1 (Nat.sub x0 x2)) = (real_div (real_pow x1 x0) (real_pow x1 x2))).
Definition term81 (x0 : real) (x1 : nat) := real_mul (real_mul (real_inv (real_pow x0 x1)) (real_pow x0 x1)).
Definition term82 (x0 : nat) (x1 : nat) := fun y0 : nat => x0 = (Nat.add x1 y0).
Definition term76 (x0 : real) (x1 : nat) := real_mul (real_inv (real_pow x0 x1)) (real_pow x0 x1).
Definition term24 := fun y0 : real => (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0.
Definition term62 (x0 : nat) (x1 : real) (x2 : nat) := real_div (real_pow x1 (Nat.add x2 x0)) (real_pow x1 x2).
Definition term56 (x0 : nat) (x1 : real) (x2 : nat) := (Peano.le x2 x0) -> (real_pow x1 (Nat.sub x0 x2)) = (real_div (real_pow x1 x0) (real_pow x1 x2)).
Definition term8 := (forall y0 : real, forall y1 : nat, (~ (y0 = (real_of_num (NUMERAL 0)))) -> ~ ((real_pow y0 y1) = (real_of_num (NUMERAL 0)))) -> forall y0 : real, forall y1 : nat, (~ (y0 = (real_of_num (NUMERAL 0)))) -> ~ ((real_pow y0 y1) = (real_of_num (NUMERAL 0))).
Definition term69 (x0 : nat) (x1 : real) (x2 : nat) := real_div (real_mul (real_pow x1 x2) (real_pow x1 x0)) (real_pow x1 x2).
Definition term30 (x0 : real) := forall y0 : real, (real_mul x0 y0) = (real_mul y0 x0).
Definition term31 (x0 : real) (x1 : real) := (fun y0 : real => (real_mul x0 y0) = (real_mul y0 x0)) x1.
Definition term48 (x0 : nat) := forall y0 : nat, (Peano.le x0 y0) = (exists y1 : nat, y0 = (Nat.add x0 y1)).
Definition term3 (x0 : real) (x1 : nat) := (fun y0 : nat => (~ (x0 = (real_of_num (NUMERAL 0)))) -> ~ ((real_pow x0 y0) = (real_of_num (NUMERAL 0)))) x1.
Definition term52 (x0 : nat) (x1 : nat) := imp (Peano.le x0 x1).
Definition term34 (x0 : real) (x1 : real) := (fun y0 : real => (real_div x0 y0) = (real_mul x0 (real_inv y0))) x1.
Definition term25 := fun y0 : real => y0 = (real_mul (real_of_num (NUMERAL (BIT1 0))) y0).
Definition term43 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.sub (Nat.add y0 y1) y0) = y1) x0.
Definition term86 := forall y0 : real, forall y1 : nat, forall y2 : nat, ((~ (y0 = (real_of_num (NUMERAL 0)))) /\ (Peano.le y1 y2)) -> (real_pow y0 (Nat.sub y2 y1)) = (real_div (real_pow y0 y2) (real_pow y0 y1)).
Definition term17 (x0 : real) := forall y0 : real, forall y1 : real, (real_mul x0 (real_mul y0 y1)) = (real_mul (real_mul x0 y0) y1).
Definition term0 := forall y0 : real, forall y1 : nat, (~ (y0 = (real_of_num (NUMERAL 0)))) -> ~ ((real_pow y0 y1) = (real_of_num (NUMERAL 0))).
Definition term53 (x0 : nat) (x1 : nat) := imp (exists y0 : nat, x0 = (Nat.add x1 y0)).
Definition term74 (x0 : real) (x1 : nat) := @eq real (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 x1)).
Definition term10 (x0 : real) := (fun y0 : real => (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_mul (real_inv y0) y0) = (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term2 (x0 : real) := forall y0 : nat, (~ (x0 = (real_of_num (NUMERAL 0)))) -> ~ ((real_pow x0 y0) = (real_of_num (NUMERAL 0))).
Definition term20 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => (real_mul x0 (real_mul x1 y0)) = (real_mul (real_mul x0 x1) y0)) x2.
Definition term55 (x0 : nat) (x1 : real) (x2 : nat) := real_div (real_pow x1 x0) (real_pow x1 x2).
Definition term38 (x0 : real) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (real_pow x0 (Nat.add y0 y1)) = (real_mul (real_pow x0 y0) (real_pow x0 y1))) x1.
Definition term11 (x0 : real) := (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_mul (real_inv x0) x0) = (real_of_num (NUMERAL (BIT1 0))).
Definition term5 (x0 : real) := ~ (x0 = (real_of_num (NUMERAL 0))).
Definition term41 (x0 : real) (x1 : nat) (x2 : nat) := real_pow x0 (Nat.add x1 x2).
Definition term27 := forall y0 : real, y0 = (real_mul (real_of_num (NUMERAL (BIT1 0))) y0).
Definition term1 (x0 : real) := (fun y0 : real => forall y1 : nat, (~ (y0 = (real_of_num (NUMERAL 0)))) -> ~ ((real_pow y0 y1) = (real_of_num (NUMERAL 0)))) x0.
Definition term68 (x0 : nat) (x1 : real) (x2 : nat) := real_div (real_mul (real_pow x1 x0) (real_pow x1 x2)).
Definition term28 (x0 : real) := (fun y0 : real => y0 = (real_mul (real_of_num (NUMERAL (BIT1 0))) y0)) x0.
Definition term19 (x0 : real) (x1 : real) := forall y0 : real, (real_mul x0 (real_mul x1 y0)) = (real_mul (real_mul x0 x1) y0).
Definition term50 (x0 : nat) (x1 : nat) := exists y0 : nat, x0 = (Nat.add x1 y0).
Definition term46 (x0 : nat) (x1 : nat) := Nat.sub (Nat.add x1 x0) x1.
Definition term85 (x0 : real) := forall y0 : nat, forall y1 : nat, ((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (Peano.le y0 y1)) -> (real_pow x0 (Nat.sub y1 y0)) = (real_div (real_pow x0 y1) (real_pow x0 y0)).
Definition term37 (x0 : real) := forall y0 : nat, forall y1 : nat, (real_pow x0 (Nat.add y0 y1)) = (real_mul (real_pow x0 y0) (real_pow x0 y1)).
Definition term77 (x0 : real) (x1 : nat) := (~ ((real_pow x0 x1) = (real_of_num (NUMERAL 0)))) -> (real_mul (real_inv (real_pow x0 x1)) (real_pow x0 x1)) = (real_of_num (NUMERAL (BIT1 0))).
Definition term6 (x0 : real) (x1 : nat) := ~ ((real_pow x0 x1) = (real_of_num (NUMERAL 0))).
Definition term23 (x0 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) x0.
Definition term26 := forall y0 : real, (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0.
Definition term42 (x0 : nat) (x1 : real) (x2 : nat) := real_mul (real_pow x1 x0) (real_pow x1 x2).
Definition term54 (x0 : real) (x1 : nat) (x2 : nat) := real_pow x0 (Nat.sub x1 x2).
Definition term44 (x0 : nat) := forall y0 : nat, (Nat.sub (Nat.add x0 y0) x0) = y0.
Definition term75 (x0 : nat) (x1 : real) (x2 : nat) := real_mul (real_mul (real_inv (real_pow x1 x0)) (real_pow x1 x0)) (real_pow x1 x2).
Definition term32 (x0 : real) := (fun y0 : real => forall y1 : real, (real_div y0 y1) = (real_mul y0 (real_inv y1))) x0.
Definition term29 (x0 : real) := (fun y0 : real => forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)) x0.
Definition term39 (x0 : nat) (x1 : real) := forall y0 : nat, (real_pow x1 (Nat.add x0 y0)) = (real_mul (real_pow x1 x0) (real_pow x1 y0)).
Definition term7 (x0 : real) (x1 : nat) := (forall y0 : real, forall y1 : nat, (~ (y0 = (real_of_num (NUMERAL 0)))) -> ~ ((real_pow y0 y1) = (real_of_num (NUMERAL 0)))) -> ~ ((real_pow x0 x1) = (real_of_num (NUMERAL 0))).
Definition term15 := (forall y0 : real, (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_mul (real_inv y0) y0) = (real_of_num (NUMERAL (BIT1 0)))) -> forall y0 : real, (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_mul (real_inv y0) y0) = (real_of_num (NUMERAL (BIT1 0))).
Definition term33 (x0 : real) := forall y0 : real, (real_div x0 y0) = (real_mul x0 (real_inv y0)).
Definition term18 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, (real_mul x0 (real_mul y0 y1)) = (real_mul (real_mul x0 y0) y1)) x1.
Definition term51 (x0 : real) (x1 : nat) (x2 : nat) := (~ (x0 = (real_of_num (NUMERAL 0)))) /\ (Peano.le x1 x2).
Definition term80 := real_mul (real_of_num (NUMERAL (BIT1 0))).
Definition term14 (x0 : real) := (forall y0 : real, (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_mul (real_inv y0) y0) = (real_of_num (NUMERAL (BIT1 0)))) -> (real_mul (real_inv x0) x0) = (real_of_num (NUMERAL (BIT1 0))).
Definition term67 (x0 : real) (x1 : nat) (x2 : nat) := real_div (real_pow x0 (Nat.add x1 x2)).
Definition term58 (x0 : real) (x1 : nat) := fun y0 : nat => (real_pow x0 (Nat.sub y0 x1)) = (real_div (real_pow x0 y0) (real_pow x0 x1)).
Definition term47 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) = (exists y2 : nat, y1 = (Nat.add y0 y2))) x0.
Definition term66 (x0 : real) (x1 : nat) := @eq real (real_pow x0 x1).
Definition term36 (x0 : real) := (fun y0 : real => forall y1 : nat, forall y2 : nat, (real_pow y0 (Nat.add y1 y2)) = (real_mul (real_pow y0 y1) (real_pow y0 y2))) x0.
Definition term71 (x0 : nat) (x1 : real) (x2 : nat) := real_mul (real_inv (real_pow x1 x0)) (real_mul (real_pow x1 x0) (real_pow x1 x2)).
Definition term4 (x0 : real) (x1 : nat) := (~ (x0 = (real_of_num (NUMERAL 0)))) -> ~ ((real_pow x0 x1) = (real_of_num (NUMERAL 0))).
Definition term13 := real_of_num (NUMERAL (BIT1 0)).
Definition term22 (x0 : real) (x1 : real) (x2 : real) := real_mul (real_mul x0 x1) x2.
Definition term57 (x0 : nat) (x1 : real) (x2 : nat) := (exists y0 : nat, x0 = (Nat.add x2 y0)) -> (real_pow x1 (Nat.sub x0 x2)) = (real_div (real_pow x1 x0) (real_pow x1 x2)).
Definition term83 (x0 : nat) (x1 : real) (x2 : nat) := ((~ (x1 = (real_of_num (NUMERAL 0)))) /\ (Peano.le x2 x0)) -> (real_pow x1 (Nat.sub x0 x2)) = (real_div (real_pow x1 x0) (real_pow x1 x2)).
Definition term72 (x0 : real) (x1 : nat) := real_inv (real_pow x0 x1).
Definition term45 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.sub (Nat.add x0 y0) x0) = y0) x1.
Definition term12 (x0 : real) := real_mul (real_inv x0) x0.
Definition term63 (x0 : real) (x1 : nat) (x2 : nat) := @eq Prop ((fun y0 : nat => (real_pow x0 (Nat.sub y0 x1)) = (real_div (real_pow x0 y0) (real_pow x0 x1))) x2).
Definition term35 (x0 : real) (x1 : real) := real_mul x0 (real_inv x1).
Definition term84 (x0 : real) (x1 : nat) := forall y0 : nat, ((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (Peano.le x1 y0)) -> (real_pow x0 (Nat.sub y0 x1)) = (real_div (real_pow x0 y0) (real_pow x0 x1)).
Definition term70 (x0 : nat) (x1 : real) (x2 : nat) := real_mul (real_mul (real_pow x1 x2) (real_pow x1 x0)) (real_inv (real_pow x1 x2)).
Definition term49 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le x0 y0) = (exists y1 : nat, y0 = (Nat.add x0 y1))) x1.
Definition term61 (x0 : real) (x1 : nat) (x2 : nat) := real_pow x0 (Nat.sub (Nat.add x2 x1) x2).
Definition term16 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, (real_mul y0 (real_mul y1 y2)) = (real_mul (real_mul y0 y1) y2)) x0.
Definition term59 (x0 : real) (x1 : nat) (x2 : nat) := (fun y0 : nat => (real_pow x0 (Nat.sub y0 x1)) = (real_div (real_pow x0 y0) (real_pow x0 x1))) x2.
Definition term73 (x0 : real) (x1 : nat) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 x1).