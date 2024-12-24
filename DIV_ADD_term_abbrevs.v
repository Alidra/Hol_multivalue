Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term12 (x0 : nat) (x1 : nat) (x2 : nat) := (num_divides x1 x0) \/ (num_divides x1 x2).
Definition term45 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (x0 = (NUMERAL 0))) -> (Nat.div (Nat.mul x0 y0) x0) = y0) x1.
Definition term13 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.div (Nat.add x0 x1) x2.
Definition term23 (x0 : nat) (x1 : nat) := (num_divides (NUMERAL 0) x0) \/ (num_divides (NUMERAL 0) x1).
Definition term54 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> (Nat.div (Nat.add (Nat.mul y0 x0) x1) y0) = (Nat.add x0 (Nat.div x1 y0))) x2.
Definition term29 := @eq nat (NUMERAL 0).
Definition term66 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (~ (y2 = (NUMERAL 0))) -> (Nat.div (Nat.add y1 (Nat.mul y2 y0)) y2) = (Nat.add (Nat.div y1 y2) y0)) x0.
Definition term50 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (~ (y2 = (NUMERAL 0))) -> (Nat.div (Nat.add (Nat.mul y2 y0) y1) y2) = (Nat.add y0 (Nat.div y1 y2))) x0.
Definition term46 (x0 : nat) (x1 : nat) := (~ (x0 = (NUMERAL 0))) -> (Nat.div (Nat.mul x0 x1) x0) = x1.
Definition term20 (x0 : nat) := num_divides (NUMERAL 0) x0.
Definition term38 (x0 : nat) (x1 : nat) := or (exists y0 : nat, x0 = (Nat.mul x1 y0)).
Definition term55 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x2 = (NUMERAL 0))) -> (Nat.div (Nat.add (Nat.mul x2 x0) x1) x2) = (Nat.add x0 (Nat.div x1 x2)).
Definition term39 (x0 : nat) (x1 : nat) (x2 : nat) := (exists y0 : nat, x0 = (Nat.mul x2 y0)) \/ (exists y0 : nat, x1 = (Nat.mul x2 y0)).
Definition term41 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((exists y0 : nat, x0 = (Nat.mul x2 y0)) \/ (exists y0 : nat, x1 = (Nat.mul x2 y0))).
Definition term59 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x0 x1).
Definition term64 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, (~ (y2 = (NUMERAL 0))) -> (Nat.div (Nat.add y1 (Nat.mul y0 y2)) y2) = (Nat.add (Nat.div y1 y2) y0)) /\ (forall y0 : nat, forall y1 : nat, forall y2 : nat, (~ (y2 = (NUMERAL 0))) -> (Nat.div (Nat.add y1 (Nat.mul y2 y0)) y2) = (Nat.add (Nat.div y1 y2) y0)).
Definition term33 (x0 : nat) (x1 : nat) (x2 : nat) := ((num_divides (NUMERAL 0) x0) \/ (num_divides (NUMERAL 0) x1)) -> ((Nat.div (Nat.add x0 x1) x2) = (Nat.add (Nat.div x0 x2) (Nat.div x1 x2))) = True.
Definition term63 (x0 : nat) (x1 : nat) := Nat.div (Nat.mul x0 x1).
Definition term25 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : Prop) := (((num_divides (NUMERAL 0) x1) \/ (num_divides (NUMERAL 0) x2)) -> ((Nat.div (Nat.add x1 x2) x0) = (Nat.add (Nat.div x1 x0) (Nat.div x2 x0))) = x3) -> (((num_divides x0 x1) \/ (num_divides x0 x2)) -> (Nat.div (Nat.add x1 x2) x0) = (Nat.add (Nat.div x1 x0) (Nat.div x2 x0))) = (((num_divides (NUMERAL 0) x1) \/ (num_divides (NUMERAL 0) x2)) -> x3).
Definition term44 (x0 : nat) := forall y0 : nat, (~ (x0 = (NUMERAL 0))) -> (Nat.div (Nat.mul x0 y0) x0) = y0.
Definition term35 (x0 : nat) (x1 : nat) (x2 : nat) := ((num_divides x2 x0) \/ (num_divides x2 x1)) -> (Nat.div (Nat.add x0 x1) x2) = (Nat.add (Nat.div x0 x2) (Nat.div x1 x2)).
Definition term15 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : Prop) := (fun y0 : Prop => forall y1 : Prop, (((num_divides x2 x0) \/ (num_divides x2 x1)) = y0) -> (y0 -> ((Nat.div (Nat.add x0 x1) x2) = (Nat.add (Nat.div x0 x2) (Nat.div x1 x2))) = y1) -> (((num_divides x2 x0) \/ (num_divides x2 x1)) -> (Nat.div (Nat.add x0 x1) x2) = (Nat.add (Nat.div x0 x2) (Nat.div x1 x2))) = (y0 -> y1)) x3.
Definition term68 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (Nat.div (Nat.add y0 (Nat.mul y1 x0)) y1) = (Nat.add (Nat.div y0 y1) x0)) x1.
Definition term52 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (Nat.div (Nat.add (Nat.mul y1 x0) y0) y1) = (Nat.add x0 (Nat.div y0 y1))) x1.
Definition term14 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.div x0 x2) (Nat.div x1 x2).
Definition term2 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term47 (x0 : nat) (x1 : nat) := Nat.div (Nat.mul x1 x0) x1.
Definition term24 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : Prop) := (((num_divides x0 x1) \/ (num_divides x0 x2)) = ((num_divides (NUMERAL 0) x1) \/ (num_divides (NUMERAL 0) x2))) -> (((num_divides (NUMERAL 0) x1) \/ (num_divides (NUMERAL 0) x2)) -> ((Nat.div (Nat.add x1 x2) x0) = (Nat.add (Nat.div x1 x0) (Nat.div x2 x0))) = x3) -> (((num_divides x0 x1) \/ (num_divides x0 x2)) -> (Nat.div (Nat.add x1 x2) x0) = (Nat.add (Nat.div x1 x0) (Nat.div x2 x0))) = (((num_divides (NUMERAL 0) x1) \/ (num_divides (NUMERAL 0) x2)) -> x3).
Definition term28 (x0 : nat) (x1 : nat) (x2 : nat) := @eq nat (Nat.div (Nat.add x0 x1) x2).
Definition term8 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term48 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, (~ (y2 = (NUMERAL 0))) -> (Nat.div (Nat.add (Nat.mul y2 y0) y1) y2) = (Nat.add y0 (Nat.div y1 y2))) /\ ((forall y0 : nat, forall y1 : nat, forall y2 : nat, (~ (y2 = (NUMERAL 0))) -> (Nat.div (Nat.add y1 (Nat.mul y0 y2)) y2) = (Nat.add (Nat.div y1 y2) y0)) /\ (forall y0 : nat, forall y1 : nat, forall y2 : nat, (~ (y2 = (NUMERAL 0))) -> (Nat.div (Nat.add y1 (Nat.mul y2 y0)) y2) = (Nat.add (Nat.div y1 y2) y0))).
Definition term32 := Nat.add (NUMERAL 0) (NUMERAL 0).
Definition term42 (x0 : nat) (x1 : nat) (x2 : nat) := ((exists y0 : nat, x0 = (Nat.mul x2 y0)) \/ (exists y0 : nat, x1 = (Nat.mul x2 y0))) -> (Nat.div (Nat.add x0 x1) x2) = (Nat.add (Nat.div x0 x2) (Nat.div x1 x2)).
Definition term6 (x0 : nat) := (fun y0 : nat => (Nat.div y0 (NUMERAL 0)) = (NUMERAL 0)) x0.
Definition term53 (x0 : nat) (x1 : nat) := forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> (Nat.div (Nat.add (Nat.mul y0 x0) x1) y0) = (Nat.add x0 (Nat.div x1 y0)).
Definition term22 (x0 : nat) := or (num_divides (NUMERAL 0) x0).
Definition term62 (x0 : nat) (x1 : nat) (x2 : nat) := @eq nat (Nat.add x0 (Nat.div x1 x2)).
Definition term37 (x0 : nat) (x1 : nat) := exists y0 : nat, x0 = (Nat.mul x1 y0).
Definition term5 (x0 : nat) := Nat.add (NUMERAL 0) x0.
Definition term77 (x0 : nat) (x1 : nat) := fun y0 : nat => x0 = (Nat.mul x1 y0).
Definition term21 (x0 : nat) (x1 : nat) := or (num_divides x0 x1).
Definition term18 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : Prop) (x4 : Prop) := (((num_divides x2 x0) \/ (num_divides x2 x1)) = x3) -> (x3 -> ((Nat.div (Nat.add x0 x1) x2) = (Nat.add (Nat.div x0 x2) (Nat.div x1 x2))) = x4) -> (((num_divides x2 x0) \/ (num_divides x2 x1)) -> (Nat.div (Nat.add x0 x1) x2) = (Nat.add (Nat.div x0 x2) (Nat.div x1 x2))) = (x3 -> x4).
Definition term30 (x0 : nat) (x1 : nat) := Nat.add (Nat.div x0 x1).
Definition term34 (x0 : nat) (x1 : nat) (x2 : nat) := (((num_divides (NUMERAL 0) x1) \/ (num_divides (NUMERAL 0) x2)) -> ((Nat.div (Nat.add x1 x2) x0) = (Nat.add (Nat.div x1 x0) (Nat.div x2 x0))) = True) -> (((num_divides x0 x1) \/ (num_divides x0 x2)) -> (Nat.div (Nat.add x1 x2) x0) = (Nat.add (Nat.div x1 x0) (Nat.div x2 x0))) = (((num_divides (NUMERAL 0) x1) \/ (num_divides (NUMERAL 0) x2)) -> True).
Definition term80 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((num_divides y0 y1) \/ (num_divides y0 y2)) -> (Nat.div (Nat.add y1 y2) y0) = (Nat.add (Nat.div y1 y0) (Nat.div y2 y0)).
Definition term79 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((num_divides x0 y0) \/ (num_divides x0 y1)) -> (Nat.div (Nat.add y0 y1) x0) = (Nat.add (Nat.div y0 x0) (Nat.div y1 x0)).
Definition term67 (x0 : nat) := forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (Nat.div (Nat.add y0 (Nat.mul y1 x0)) y1) = (Nat.add (Nat.div y0 y1) x0).
Definition term65 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (~ (y2 = (NUMERAL 0))) -> (Nat.div (Nat.add y1 (Nat.mul y2 y0)) y2) = (Nat.add (Nat.div y1 y2) y0).
Definition term51 (x0 : nat) := forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (Nat.div (Nat.add (Nat.mul y1 x0) y0) y1) = (Nat.add x0 (Nat.div y0 y1)).
Definition term49 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (~ (y2 = (NUMERAL 0))) -> (Nat.div (Nat.add (Nat.mul y2 y0) y1) y2) = (Nat.add y0 (Nat.div y1 y2)).
Definition term61 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.div (Nat.add (Nat.mul x0 x1) x2).
Definition term1 (x0 : nat) := (x0 = (NUMERAL 0)) \/ (~ (x0 = (NUMERAL 0))).
Definition term76 (x0 : nat) (x1 : nat) (x2 : nat) := @eq nat (Nat.add (Nat.div x0 x1) x2).
Definition term72 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.div (Nat.add x0 (Nat.mul x2 x1)) x2.
Definition term3 := forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0.
Definition term4 (x0 : nat) := (fun y0 : nat => (Nat.add (NUMERAL 0) y0) = y0) x0.
Definition term70 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> (Nat.div (Nat.add x0 (Nat.mul y0 x1)) y0) = (Nat.add (Nat.div x0 y0) x1)) x2.
Definition term16 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : Prop) := forall y0 : Prop, (((num_divides x2 x0) \/ (num_divides x2 x1)) = x3) -> (x3 -> ((Nat.div (Nat.add x0 x1) x2) = (Nat.add (Nat.div x0 x2) (Nat.div x1 x2))) = y0) -> (((num_divides x2 x0) \/ (num_divides x2 x1)) -> (Nat.div (Nat.add x0 x1) x2) = (Nat.add (Nat.div x0 x2) (Nat.div x1 x2))) = (x3 -> y0).
Definition term9 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term27 (x0 : nat) (x1 : nat) := Nat.div (Nat.add x0 x1) (NUMERAL 0).
Definition term11 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : Prop, forall y1 : Prop, (((num_divides x2 x0) \/ (num_divides x2 x1)) = y0) -> (y0 -> ((Nat.div (Nat.add x0 x1) x2) = (Nat.add (Nat.div x0 x2) (Nat.div x1 x2))) = y1) -> (((num_divides x2 x0) \/ (num_divides x2 x1)) -> (Nat.div (Nat.add x0 x1) x2) = (Nat.add (Nat.div x0 x2) (Nat.div x1 x2))) = (y0 -> y1).
Definition term10 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term56 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.div (Nat.add (Nat.mul x2 x0) x1) x2.
Definition term19 := num_divides (NUMERAL 0).
Definition term73 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.div x0 x1) x2.
Definition term17 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : Prop) (x4 : Prop) := (fun y0 : Prop => (((num_divides x2 x0) \/ (num_divides x2 x1)) = x3) -> (x3 -> ((Nat.div (Nat.add x0 x1) x2) = (Nat.add (Nat.div x0 x2) (Nat.div x1 x2))) = y0) -> (((num_divides x2 x0) \/ (num_divides x2 x1)) -> (Nat.div (Nat.add x0 x1) x2) = (Nat.add (Nat.div x0 x2) (Nat.div x1 x2))) = (x3 -> y0)) x4.
Definition term71 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x1 = (NUMERAL 0))) -> (Nat.div (Nat.add x0 (Nat.mul x1 x2)) x1) = (Nat.add (Nat.div x0 x1) x2).
Definition term31 := Nat.add (NUMERAL 0).
Definition term26 (x0 : nat) (x1 : nat) := Nat.div (Nat.add x0 x1).
Definition term43 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (y0 = (NUMERAL 0))) -> (Nat.div (Nat.mul y0 y1) y0) = y1) x0.
Definition term75 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.div (Nat.add x0 (Nat.mul x1 x2)).
Definition term58 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> (x0 = (NUMERAL 0)) = False.
Definition term78 (x0 : nat) (x1 : nat) := forall y0 : nat, ((num_divides x1 x0) \/ (num_divides x1 y0)) -> (Nat.div (Nat.add x0 y0) x1) = (Nat.add (Nat.div x0 x1) (Nat.div y0 x1)).
Definition term60 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x0 x1) x2.
Definition term40 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((num_divides x1 x0) \/ (num_divides x1 x2)).
Definition term69 (x0 : nat) (x1 : nat) := forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> (Nat.div (Nat.add x0 (Nat.mul y0 x1)) y0) = (Nat.add (Nat.div x0 y0) x1).
Definition term7 (x0 : nat) := Nat.div x0 (NUMERAL 0).
Definition term57 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add x0 (Nat.div x1 x2).
Definition term36 (x0 : nat) (x1 : nat) := ((num_divides (NUMERAL 0) x0) \/ (num_divides (NUMERAL 0) x1)) -> True.
Definition term0 (x0 : nat) := (fun y0 : Prop => y0 \/ (~ y0)) (x0 = (NUMERAL 0)).
Definition term74 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add x0 (Nat.mul x1 x2).
