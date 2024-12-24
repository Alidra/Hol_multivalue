Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term62 (x0 : nat) (x1 : nat) := ((num_divides x0 x1) -> (((Peano.le (NUMERAL (BIT1 0)) x0) /\ (Peano.le x0 x1)) \/ (x1 = (NUMERAL 0))) = True) -> ((num_divides x0 x1) -> ((Peano.le (NUMERAL (BIT1 0)) x0) /\ (Peano.le x0 x1)) \/ (x1 = (NUMERAL 0))) = ((num_divides x0 x1) -> True).
Definition term66 (x0 : nat) := imp (num_divides (NUMERAL 0) x0).
Definition term63 (x0 : nat) (x1 : nat) := (num_divides x0 x1) -> True.
Definition term57 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> (Peano.le (NUMERAL (BIT1 0)) x0) = True.
Definition term71 (x0 : nat) := ~ ((exists y0 : nat, x0 = (Nat.mul (NUMERAL 0) y0)) -> (Peano.le (NUMERAL (BIT1 0)) (NUMERAL 0)) \/ (x0 = (NUMERAL 0))).
Definition term19 (x0 : nat) := Peano.le (NUMERAL (BIT1 0)) x0.
Definition term153 := (~ False) -> False.
Definition term80 (x0 : nat) := (~ ((exists y0 : nat, x0 = (Nat.mul (NUMERAL 0) y0)) -> (Peano.le (NUMERAL (BIT1 0)) (NUMERAL 0)) \/ (x0 = (NUMERAL 0)))) -> ~ ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))))).
Definition term55 (x0 : nat) := (Peano.lt (NUMERAL 0) x0) -> (Peano.le (NUMERAL (BIT1 0)) x0) = True.
Definition term72 (x0 : nat) := (~ ((exists y0 : nat, x0 = (Nat.mul (NUMERAL 0) y0)) -> (Peano.le (NUMERAL (BIT1 0)) (NUMERAL 0)) \/ (x0 = (NUMERAL 0)))) -> ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))))) -> False.
Definition term149 (x0 : nat) := @eq Prop (~ (x0 = (NUMERAL 0))).
Definition term20 := Peano.le (NUMERAL (BIT1 0)) (NUMERAL 0).
Definition term155 (x0 : nat) := forall y0 : nat, (num_divides x0 y0) -> ((Peano.le (NUMERAL (BIT1 0)) x0) /\ (Peano.le x0 y0)) \/ (y0 = (NUMERAL 0)).
Definition term48 (x0 : nat) := forall y0 : nat, (num_divides x0 y0) -> (Peano.le x0 y0) \/ (y0 = (NUMERAL 0)).
Definition term108 := (forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))))).
Definition term116 := forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0).
Definition term32 (x0 : nat) := (num_divides (NUMERAL 0) x0) -> (Peano.le (NUMERAL (BIT1 0)) (NUMERAL 0)) \/ (x0 = (NUMERAL 0)).
Definition term131 (x0 : nat) := fun y0 : nat => (fun y1 : nat => x0 = (Nat.mul (NUMERAL 0) y1)) y0.
Definition term78 := (forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))))))).
Definition term15 (x0 : nat) := num_divides (NUMERAL 0) x0.
Definition term150 (x0 : nat) := (~ ((Nat.mul (NUMERAL 0) x0) = (NUMERAL 0))) -> (Nat.mul (NUMERAL 0) x0) = (NUMERAL 0).
Definition term77 := ~ ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))))).
Definition term28 (x0 : nat) := (Peano.le (NUMERAL (BIT1 0)) (NUMERAL 0)) \/ (x0 = (NUMERAL 0)).
Definition term128 (x0 : nat) := (exists y0 : nat, (fun y1 : nat => x0 = (Nat.mul (NUMERAL 0) y1)) y0) /\ ((~ (Peano.le (NUMERAL (BIT1 0)) (NUMERAL 0))) /\ (~ (x0 = (NUMERAL 0)))).
Definition term88 (x0 : nat) := forall y0 : nat, (Nat.mul x0 (S y0)) = (Nat.add x0 (Nat.mul x0 y0)).
Definition term69 (x0 : Prop) := (~ x0) -> False.
Definition term74 (x0 : nat) := (((~ ((exists y0 : nat, x0 = (Nat.mul (NUMERAL 0) y0)) -> (Peano.le (NUMERAL (BIT1 0)) (NUMERAL 0)) \/ (x0 = (NUMERAL 0)))) -> ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))))) -> False) -> (~ ((exists y0 : nat, x0 = (Nat.mul (NUMERAL 0) y0)) -> (Peano.le (NUMERAL (BIT1 0)) (NUMERAL 0)) \/ (x0 = (NUMERAL 0)))) -> ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))))) -> False) -> (~ ((exists y0 : nat, x0 = (Nat.mul (NUMERAL 0) y0)) -> (Peano.le (NUMERAL (BIT1 0)) (NUMERAL 0)) \/ (x0 = (NUMERAL 0)))) -> ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))))) -> False.
Definition term98 := (forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))).
Definition term70 (x0 : nat) := (~ ((exists y0 : nat, x0 = (Nat.mul (NUMERAL 0) y0)) -> (Peano.le (NUMERAL (BIT1 0)) (NUMERAL 0)) \/ (x0 = (NUMERAL 0)))) -> False.
Definition term105 := fun y0 : nat => (Nat.mul (NUMERAL (BIT1 0)) y0) = y0.
Definition term143 (x0 : nat) := (fun y0 : nat => (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) x0.
Definition term139 (x0 : nat) (x1 : nat) := (x1 = (Nat.mul (NUMERAL 0) x0)) /\ ((~ (Peano.le (NUMERAL (BIT1 0)) (NUMERAL 0))) /\ (~ (x1 = (NUMERAL 0)))).
Definition term3 (x0 : nat) := (fun y0 : nat => Peano.le (NUMERAL 0) y0) x0.
Definition term44 := forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0.
Definition term144 := fun y0 : nat => ~ (y0 = (NUMERAL 0)).
Definition term151 (x0 : Prop) := (~ x0) -> x0.
Definition term50 (x0 : nat) (x1 : nat) := (num_divides x0 x1) -> (Peano.le x0 x1) \/ (x1 = (NUMERAL 0)).
Definition term129 (x0 : nat) := exists y0 : nat, ((fun y1 : nat => x0 = (Nat.mul (NUMERAL 0) y1)) y0) /\ ((~ (Peano.le (NUMERAL (BIT1 0)) (NUMERAL 0))) /\ (~ (x0 = (NUMERAL 0)))).
Definition term26 (x0 : nat) (x1 : nat) := or ((Peano.le (NUMERAL (BIT1 0)) x0) /\ (Peano.le x0 x1)).
Definition term68 (x0 : nat) := (exists y0 : nat, x0 = (Nat.mul (NUMERAL 0) y0)) -> (Peano.le (NUMERAL (BIT1 0)) (NUMERAL 0)) \/ (x0 = (NUMERAL 0)).
Definition term79 (x0 : nat) := imp (~ ((exists y0 : nat, x0 = (Nat.mul (NUMERAL 0) y0)) -> (Peano.le (NUMERAL (BIT1 0)) (NUMERAL 0)) \/ (x0 = (NUMERAL 0)))).
Definition term133 (x0 : nat) := and (exists y0 : nat, (fun y1 : nat => x0 = (Nat.mul (NUMERAL 0) y1)) y0).
Definition term67 (x0 : nat) := imp (exists y0 : nat, x0 = (Nat.mul (NUMERAL 0) y0)).
Definition term9 (x0 : nat) (x1 : nat) := ((Peano.le (NUMERAL (BIT1 0)) x0) /\ (Peano.le x0 x1)) \/ (x1 = (NUMERAL 0)).
Definition term22 := and (Peano.le (NUMERAL (BIT1 0)) (NUMERAL 0)).
Definition term84 := forall y0 : nat, (~ ((exists y1 : nat, y0 = (Nat.mul (NUMERAL 0) y1)) -> (Peano.le (NUMERAL (BIT1 0)) (NUMERAL 0)) \/ (y0 = (NUMERAL 0)))) -> ~ ((forall y1 : nat, (Nat.mul (NUMERAL 0) y1) = (NUMERAL 0)) /\ ((forall y1 : nat, (Nat.mul y1 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y1 : nat, (Nat.mul (NUMERAL (BIT1 0)) y1) = y1) /\ ((forall y1 : nat, (Nat.mul y1 (NUMERAL (BIT1 0))) = y1) /\ ((forall y1 : nat, forall y2 : nat, (Nat.mul (S y1) y2) = (Nat.add (Nat.mul y1 y2) y2)) /\ (forall y1 : nat, forall y2 : nat, (Nat.mul y1 (S y2)) = (Nat.add y1 (Nat.mul y1 y2)))))))).
Definition term100 := fun y0 : nat => (Nat.mul y0 (NUMERAL (BIT1 0))) = y0.
Definition term91 (x0 : nat) (x1 : nat) := Nat.mul (S x0) x1.
Definition term30 (x0 : nat) (x1 : nat) := ((num_divides (NUMERAL 0) x1) -> (((Peano.le (NUMERAL (BIT1 0)) x0) /\ (Peano.le x0 x1)) \/ (x1 = (NUMERAL 0))) = ((Peano.le (NUMERAL (BIT1 0)) (NUMERAL 0)) \/ (x1 = (NUMERAL 0)))) -> ((num_divides x0 x1) -> ((Peano.le (NUMERAL (BIT1 0)) x0) /\ (Peano.le x0 x1)) \/ (x1 = (NUMERAL 0))) = ((num_divides (NUMERAL 0) x1) -> (Peano.le (NUMERAL (BIT1 0)) (NUMERAL 0)) \/ (x1 = (NUMERAL 0))).
Definition term148 (x0 : nat) := @eq Prop ((fun y0 : nat => ~ (y0 = (NUMERAL 0))) x0).
Definition term2 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term95 := fun y0 : nat => forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1).
Definition term152 (x0 : nat) := ((Nat.mul (NUMERAL 0) x0) = (NUMERAL 0)) -> False.
Definition term85 (x0 : nat) (x1 : nat) := Nat.mul x0 (S x1).
Definition term101 := forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0.
Definition term5 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term25 := (Peano.le (NUMERAL (BIT1 0)) (NUMERAL 0)) /\ True.
Definition term42 (x0 : nat) := (fun y0 : nat => (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) x0.
Definition term38 (x0 : nat) := (fun y0 : nat => (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) x0.
Definition term56 (x0 : nat) := (Peano.le (NUMERAL (BIT1 0)) x0) -> (Peano.lt (NUMERAL 0) x0) = True.
Definition term59 (x0 : nat) (x1 : nat) := or (Peano.le x0 x1).
Definition term27 := or (Peano.le (NUMERAL (BIT1 0)) (NUMERAL 0)).
Definition term145 (x0 : nat) := (fun y0 : nat => ~ (y0 = (NUMERAL 0))) x0.
Definition term117 := and (forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)).
Definition term112 := and (forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)).
Definition term64 (x0 : nat) (x1 : nat) := exists y0 : nat, x0 = (Nat.mul x1 y0).
Definition term35 := (forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))).
Definition term146 (x0 : nat) := (fun y0 : nat => ~ (y0 = (NUMERAL 0))) (Nat.mul (NUMERAL 0) x0).
Definition term82 := fun y0 : nat => (~ ((exists y1 : nat, y0 = (Nat.mul (NUMERAL 0) y1)) -> (Peano.le (NUMERAL (BIT1 0)) (NUMERAL 0)) \/ (y0 = (NUMERAL 0)))) -> ~ ((forall y1 : nat, (Nat.mul (NUMERAL 0) y1) = (NUMERAL 0)) /\ ((forall y1 : nat, (Nat.mul y1 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y1 : nat, (Nat.mul (NUMERAL (BIT1 0)) y1) = y1) /\ ((forall y1 : nat, (Nat.mul y1 (NUMERAL (BIT1 0))) = y1) /\ ((forall y1 : nat, forall y2 : nat, (Nat.mul (S y1) y2) = (Nat.add (Nat.mul y1 y2) y2)) /\ (forall y1 : nat, forall y2 : nat, (Nat.mul y1 (S y2)) = (Nat.add y1 (Nat.mul y1 y2)))))))).
Definition term107 := and (forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0).
Definition term102 := and (forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0).
Definition term156 := forall y0 : nat, forall y1 : nat, (num_divides y0 y1) -> ((Peano.le (NUMERAL (BIT1 0)) y0) /\ (Peano.le y0 y1)) \/ (y1 = (NUMERAL 0)).
Definition term96 := forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1).
Definition term90 := forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)).
Definition term51 (x0 : nat) (x1 : nat) := (Peano.le x0 x1) \/ (x1 = (NUMERAL 0)).
Definition term45 (x0 : nat) := (fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) x0.
Definition term73 (x0 : nat) := ((~ ((exists y0 : nat, x0 = (Nat.mul (NUMERAL 0) y0)) -> (Peano.le (NUMERAL (BIT1 0)) (NUMERAL 0)) \/ (x0 = (NUMERAL 0)))) -> ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))))) -> False) -> (~ ((exists y0 : nat, x0 = (Nat.mul (NUMERAL 0) y0)) -> (Peano.le (NUMERAL (BIT1 0)) (NUMERAL 0)) \/ (x0 = (NUMERAL 0)))) -> ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))))) -> False.
Definition term125 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) /\ x1.
Definition term1 (x0 : nat) := (x0 = (NUMERAL 0)) \/ (~ (x0 = (NUMERAL 0))).
Definition term29 (x0 : nat) (x1 : nat) := (num_divides (NUMERAL 0) x1) -> (((Peano.le (NUMERAL (BIT1 0)) x0) /\ (Peano.le x0 x1)) \/ (x1 = (NUMERAL 0))) = ((Peano.le (NUMERAL (BIT1 0)) (NUMERAL 0)) \/ (x1 = (NUMERAL 0))).
Definition term12 (x0 : nat) (x1 : nat) (x2 : Prop) (x3 : Prop) := (fun y0 : Prop => ((num_divides x0 x1) = x2) -> (x2 -> (((Peano.le (NUMERAL (BIT1 0)) x0) /\ (Peano.le x0 x1)) \/ (x1 = (NUMERAL 0))) = y0) -> ((num_divides x0 x1) -> ((Peano.le (NUMERAL (BIT1 0)) x0) /\ (Peano.le x0 x1)) \/ (x1 = (NUMERAL 0))) = (x2 -> y0)) x3.
Definition term122 (x0 : nat) := (exists y0 : nat, x0 = (Nat.mul (NUMERAL 0) y0)) /\ (~ ((Peano.le (NUMERAL (BIT1 0)) (NUMERAL 0)) \/ (x0 = (NUMERAL 0)))).
Definition term13 (x0 : nat) (x1 : nat) (x2 : Prop) (x3 : Prop) := ((num_divides x0 x1) = x2) -> (x2 -> (((Peano.le (NUMERAL (BIT1 0)) x0) /\ (Peano.le x0 x1)) \/ (x1 = (NUMERAL 0))) = x3) -> ((num_divides x0 x1) -> ((Peano.le (NUMERAL (BIT1 0)) x0) /\ (Peano.le x0 x1)) \/ (x1 = (NUMERAL 0))) = (x2 -> x3).
Definition term119 (x0 : nat) := ~ ((Peano.le (NUMERAL (BIT1 0)) (NUMERAL 0)) \/ (x0 = (NUMERAL 0))).
Definition term140 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => x0 = (Nat.mul (NUMERAL 0) y1)) y0) /\ ((~ (Peano.le (NUMERAL (BIT1 0)) (NUMERAL 0))) /\ (~ (x0 = (NUMERAL 0)))).
Definition term138 (x0 : nat) (x1 : nat) := ((fun y0 : nat => x1 = (Nat.mul (NUMERAL 0) y0)) x0) /\ ((~ (Peano.le (NUMERAL (BIT1 0)) (NUMERAL 0))) /\ (~ (x1 = (NUMERAL 0)))).
Definition term106 := forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0.
Definition term65 (x0 : nat) := exists y0 : nat, x0 = (Nat.mul (NUMERAL 0) y0).
Definition term4 (x0 : nat) := Peano.le (NUMERAL 0) x0.
Definition term94 (x0 : nat) := forall y0 : nat, (Nat.mul (S x0) y0) = (Nat.add (Nat.mul x0 y0) y0).
Definition term127 (x0 : nat -> Prop) (x1 : Prop) := exists y0 : nat, (x0 y0) /\ x1.
Definition term21 (x0 : nat) := and (Peano.le (NUMERAL (BIT1 0)) x0).
Definition term11 (x0 : nat) (x1 : nat) (x2 : Prop) := forall y0 : Prop, ((num_divides x0 x1) = x2) -> (x2 -> (((Peano.le (NUMERAL (BIT1 0)) x0) /\ (Peano.le x0 x1)) \/ (x1 = (NUMERAL 0))) = y0) -> ((num_divides x0 x1) -> ((Peano.le (NUMERAL (BIT1 0)) x0) /\ (Peano.le x0 x1)) \/ (x1 = (NUMERAL 0))) = (x2 -> y0).
Definition term6 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term130 (x0 : nat) (x1 : nat) := (fun y0 : nat => x0 = (Nat.mul (NUMERAL 0) y0)) x1.
Definition term16 (x0 : nat) (x1 : nat) (x2 : Prop) := ((num_divides x0 x1) = (num_divides (NUMERAL 0) x1)) -> ((num_divides (NUMERAL 0) x1) -> (((Peano.le (NUMERAL (BIT1 0)) x0) /\ (Peano.le x0 x1)) \/ (x1 = (NUMERAL 0))) = x2) -> ((num_divides x0 x1) -> ((Peano.le (NUMERAL (BIT1 0)) x0) /\ (Peano.le x0 x1)) \/ (x1 = (NUMERAL 0))) = ((num_divides (NUMERAL 0) x1) -> x2).
Definition term83 := forall y0 : nat, (~ ((exists y1 : nat, y0 = (Nat.mul (NUMERAL 0) y1)) -> (Peano.le (NUMERAL (BIT1 0)) (NUMERAL 0)) \/ (y0 = (NUMERAL 0)))) -> ((forall y1 : nat, (Nat.mul (NUMERAL 0) y1) = (NUMERAL 0)) /\ ((forall y1 : nat, (Nat.mul y1 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y1 : nat, (Nat.mul (NUMERAL (BIT1 0)) y1) = y1) /\ ((forall y1 : nat, (Nat.mul y1 (NUMERAL (BIT1 0))) = y1) /\ ((forall y1 : nat, forall y2 : nat, (Nat.mul (S y1) y2) = (Nat.add (Nat.mul y1 y2) y2)) /\ (forall y1 : nat, forall y2 : nat, (Nat.mul y1 (S y2)) = (Nat.add y1 (Nat.mul y1 y2)))))))) -> False.
Definition term132 (x0 : nat) := exists y0 : nat, (fun y1 : nat => x0 = (Nat.mul (NUMERAL 0) y1)) y0.
Definition term110 := fun y0 : nat => (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0).
Definition term8 (x0 : nat) (x1 : nat) := forall y0 : Prop, forall y1 : Prop, ((num_divides x0 x1) = y0) -> (y0 -> (((Peano.le (NUMERAL (BIT1 0)) x0) /\ (Peano.le x0 x1)) \/ (x1 = (NUMERAL 0))) = y1) -> ((num_divides x0 x1) -> ((Peano.le (NUMERAL (BIT1 0)) x0) /\ (Peano.le x0 x1)) \/ (x1 = (NUMERAL 0))) = (y0 -> y1).
Definition term7 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term103 := (forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))).
Definition term14 := num_divides (NUMERAL 0).
Definition term93 (x0 : nat) := fun y0 : nat => (Nat.mul (S x0) y0) = (Nat.add (Nat.mul x0 y0) y0).
Definition term53 (x0 : nat) (x1 : nat) (x2 : Prop) := ((num_divides x0 x1) = (num_divides x0 x1)) -> ((num_divides x0 x1) -> (((Peano.le (NUMERAL (BIT1 0)) x0) /\ (Peano.le x0 x1)) \/ (x1 = (NUMERAL 0))) = x2) -> ((num_divides x0 x1) -> ((Peano.le (NUMERAL (BIT1 0)) x0) /\ (Peano.le x0 x1)) \/ (x1 = (NUMERAL 0))) = ((num_divides x0 x1) -> x2).
Definition term36 := (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0))).
Definition term97 := and (forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)).
Definition term76 := ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))))) -> False.
Definition term126 (x0 : nat -> Prop) (x1 : Prop) := (exists y0 : nat, x0 y0) /\ x1.
Definition term147 (x0 : nat) := ~ ((Nat.mul (NUMERAL 0) x0) = (NUMERAL 0)).
Definition term142 (x0 : nat) := exists y0 : nat, (x0 = (Nat.mul (NUMERAL 0) y0)) /\ ((~ (Peano.le (NUMERAL (BIT1 0)) (NUMERAL 0))) /\ (~ (x0 = (NUMERAL 0)))).
Definition term99 (x0 : nat) := Nat.mul x0 (NUMERAL (BIT1 0)).
Definition term47 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (num_divides y0 y1) -> (Peano.le y0 y1) \/ (y1 = (NUMERAL 0))) x0.
Definition term24 (x0 : nat) (x1 : nat) := (Peano.le (NUMERAL (BIT1 0)) x0) /\ (Peano.le x0 x1).
Definition term34 := (forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0))))).
Definition term111 := forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0).
Definition term41 := forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0.
Definition term37 := forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0.
Definition term92 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x0 x1) x1.
Definition term121 (x0 : nat) := and (exists y0 : nat, x0 = (Nat.mul (NUMERAL 0) y0)).
Definition term154 (x0 : nat) := (fun y0 : nat => (~ ((exists y1 : nat, y0 = (Nat.mul (NUMERAL 0) y1)) -> (Peano.le (NUMERAL (BIT1 0)) (NUMERAL 0)) \/ (y0 = (NUMERAL 0)))) -> ((forall y1 : nat, (Nat.mul (NUMERAL 0) y1) = (NUMERAL 0)) /\ ((forall y1 : nat, (Nat.mul y1 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y1 : nat, (Nat.mul (NUMERAL (BIT1 0)) y1) = y1) /\ ((forall y1 : nat, (Nat.mul y1 (NUMERAL (BIT1 0))) = y1) /\ ((forall y1 : nat, forall y2 : nat, (Nat.mul (S y1) y2) = (Nat.add (Nat.mul y1 y2) y2)) /\ (forall y1 : nat, forall y2 : nat, (Nat.mul y1 (S y2)) = (Nat.add y1 (Nat.mul y1 y2)))))))) -> False) x0.
Definition term86 (x0 : nat) (x1 : nat) := Nat.add x0 (Nat.mul x0 x1).
Definition term109 (x0 : nat) := Nat.mul x0 (NUMERAL 0).
Definition term81 := fun y0 : nat => (~ ((exists y1 : nat, y0 = (Nat.mul (NUMERAL 0) y1)) -> (Peano.le (NUMERAL (BIT1 0)) (NUMERAL 0)) \/ (y0 = (NUMERAL 0)))) -> ((forall y1 : nat, (Nat.mul (NUMERAL 0) y1) = (NUMERAL 0)) /\ ((forall y1 : nat, (Nat.mul y1 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y1 : nat, (Nat.mul (NUMERAL (BIT1 0)) y1) = y1) /\ ((forall y1 : nat, (Nat.mul y1 (NUMERAL (BIT1 0))) = y1) /\ ((forall y1 : nat, forall y2 : nat, (Nat.mul (S y1) y2) = (Nat.add (Nat.mul y1 y2) y2)) /\ (forall y1 : nat, forall y2 : nat, (Nat.mul y1 (S y2)) = (Nat.add y1 (Nat.mul y1 y2)))))))) -> False.
Definition term118 (x0 : nat) := fun y0 : nat => x0 = (Nat.mul (NUMERAL 0) y0).
Definition term58 (x0 : nat) (x1 : nat) := True /\ (Peano.le x0 x1).
Definition term52 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> (x0 = (NUMERAL 0)) = False.
Definition term39 (x0 : nat) := (Peano.le (NUMERAL (BIT1 0)) x0) -> Peano.lt (NUMERAL 0) x0.
Definition term61 (x0 : nat) (x1 : nat) := (num_divides x0 x1) -> (((Peano.le (NUMERAL (BIT1 0)) x0) /\ (Peano.le x0 x1)) \/ (x1 = (NUMERAL 0))) = True.
Definition term60 (x0 : nat) (x1 : nat) := (num_divides x0 x1) -> ((Peano.le x0 x1) \/ (x1 = (NUMERAL 0))) = True.
Definition term141 (x0 : nat) := fun y0 : nat => (x0 = (Nat.mul (NUMERAL 0) y0)) /\ ((~ (Peano.le (NUMERAL (BIT1 0)) (NUMERAL 0))) /\ (~ (x0 = (NUMERAL 0)))).
Definition term43 (x0 : nat) := (Peano.lt (NUMERAL 0) x0) -> Peano.le (NUMERAL (BIT1 0)) x0.
Definition term23 := Peano.le (NUMERAL 0).
Definition term120 (x0 : nat) := (~ (Peano.le (NUMERAL (BIT1 0)) (NUMERAL 0))) /\ (~ (x0 = (NUMERAL 0))).
Definition term31 (x0 : nat) (x1 : nat) := (num_divides x0 x1) -> ((Peano.le (NUMERAL (BIT1 0)) x0) /\ (Peano.le x0 x1)) \/ (x1 = (NUMERAL 0)).
Definition term114 (x0 : nat) := Nat.mul (NUMERAL 0) x0.
Definition term136 (x0 : nat) (x1 : nat) := and ((fun y0 : nat => x0 = (Nat.mul (NUMERAL 0) y0)) x1).
Definition term135 (x0 : nat) := @eq Prop ((exists y0 : nat, x0 = (Nat.mul (NUMERAL 0) y0)) /\ ((~ (Peano.le (NUMERAL (BIT1 0)) (NUMERAL 0))) /\ (~ (x0 = (NUMERAL 0))))).
Definition term134 (x0 : nat) := @eq Prop ((exists y0 : nat, (fun y1 : nat => x0 = (Nat.mul (NUMERAL 0) y1)) y0) /\ ((~ (Peano.le (NUMERAL (BIT1 0)) (NUMERAL 0))) /\ (~ (x0 = (NUMERAL 0))))).
Definition term46 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) x0.
Definition term124 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) /\ x1.
Definition term87 (x0 : nat) := fun y0 : nat => (Nat.mul x0 (S y0)) = (Nat.add x0 (Nat.mul x0 y0)).
Definition term75 (x0 : nat) := (((~ ((exists y0 : nat, x0 = (Nat.mul (NUMERAL 0) y0)) -> (Peano.le (NUMERAL (BIT1 0)) (NUMERAL 0)) \/ (x0 = (NUMERAL 0)))) -> ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))))) -> False) -> (~ ((exists y0 : nat, x0 = (Nat.mul (NUMERAL 0) y0)) -> (Peano.le (NUMERAL (BIT1 0)) (NUMERAL 0)) \/ (x0 = (NUMERAL 0)))) -> ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))))) -> False) -> ((~ ((exists y0 : nat, x0 = (Nat.mul (NUMERAL 0) y0)) -> (Peano.le (NUMERAL (BIT1 0)) (NUMERAL 0)) \/ (x0 = (NUMERAL 0)))) -> ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))))) -> False) -> (~ ((exists y0 : nat, x0 = (Nat.mul (NUMERAL 0) y0)) -> (Peano.le (NUMERAL (BIT1 0)) (NUMERAL 0)) \/ (x0 = (NUMERAL 0)))) -> ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))))) -> False.
Definition term123 (x0 : nat) := (exists y0 : nat, x0 = (Nat.mul (NUMERAL 0) y0)) /\ ((~ (Peano.le (NUMERAL (BIT1 0)) (NUMERAL 0))) /\ (~ (x0 = (NUMERAL 0)))).
Definition term54 (x0 : nat) (x1 : nat) (x2 : Prop) := ((num_divides x0 x1) -> (((Peano.le (NUMERAL (BIT1 0)) x0) /\ (Peano.le x0 x1)) \/ (x1 = (NUMERAL 0))) = x2) -> ((num_divides x0 x1) -> ((Peano.le (NUMERAL (BIT1 0)) x0) /\ (Peano.le x0 x1)) \/ (x1 = (NUMERAL 0))) = ((num_divides x0 x1) -> x2).
Definition term17 (x0 : nat) (x1 : nat) (x2 : Prop) := ((num_divides (NUMERAL 0) x1) -> (((Peano.le (NUMERAL (BIT1 0)) x0) /\ (Peano.le x0 x1)) \/ (x1 = (NUMERAL 0))) = x2) -> ((num_divides x0 x1) -> ((Peano.le (NUMERAL (BIT1 0)) x0) /\ (Peano.le x0 x1)) \/ (x1 = (NUMERAL 0))) = ((num_divides (NUMERAL 0) x1) -> x2).
Definition term113 := (forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))).
Definition term33 := (forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))).
Definition term10 (x0 : nat) (x1 : nat) (x2 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((num_divides x0 x1) = y0) -> (y0 -> (((Peano.le (NUMERAL (BIT1 0)) x0) /\ (Peano.le x0 x1)) \/ (x1 = (NUMERAL 0))) = y1) -> ((num_divides x0 x1) -> ((Peano.le (NUMERAL (BIT1 0)) x0) /\ (Peano.le x0 x1)) \/ (x1 = (NUMERAL 0))) = (y0 -> y1)) x2.
Definition term40 (x0 : nat) := Peano.lt (NUMERAL 0) x0.
Definition term0 (x0 : nat) := (fun y0 : Prop => y0 \/ (~ y0)) (x0 = (NUMERAL 0)).
Definition term89 := fun y0 : nat => forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)).
Definition term137 (x0 : nat) (x1 : nat) := and (x0 = (Nat.mul (NUMERAL 0) x1)).
Definition term104 (x0 : nat) := Nat.mul (NUMERAL (BIT1 0)) x0.
Definition term18 := Peano.le (NUMERAL (BIT1 0)).
Definition term49 (x0 : nat) (x1 : nat) := (fun y0 : nat => (num_divides x0 y0) -> (Peano.le x0 y0) \/ (y0 = (NUMERAL 0))) x1.
Definition term115 := fun y0 : nat => (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0).
