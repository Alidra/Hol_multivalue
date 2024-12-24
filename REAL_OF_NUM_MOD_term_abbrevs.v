Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term69 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1).
Definition term91 (x0 : nat) (x1 : nat) := ~ (x0 = x1).
Definition term117 := (~ False) -> False.
Definition term99 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((~ (x0 = x1)) \/ (~ (x0 = x2)))) -> x1 = x2.
Definition term31 (x0 : nat) (x1 : nat) := real_add (real_of_num (Nat.modulo x0 x1)) (real_mul (real_of_num (Nat.div x0 x1)) (real_of_num x1)).
Definition term75 (x0 : nat) := fun y0 : nat => (Nat.add x0 y0) = (Nat.add y0 x0).
Definition term114 (x0 : nat) (x1 : nat) := (((Nat.add (Nat.mul (Nat.div x1 x0) x0) (Nat.modulo x1 x0)) = (Nat.add (Nat.modulo x1 x0) (Nat.mul (Nat.div x1 x0) x0))) /\ ((Nat.add (Nat.mul (Nat.div x1 x0) x0) (Nat.modulo x1 x0)) = x1)) -> (Nat.add (Nat.modulo x1 x0) (Nat.mul (Nat.div x1 x0) x0)) = x1.
Definition term105 (x0 : Prop) := ~ (~ x0).
Definition term53 := (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> ~ ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)) = y0) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul y1 (Nat.div y0 y1)) (Nat.modulo y0 y1)) = y0)).
Definition term104 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (~ (x1 = x0))) /\ (~ (~ (x1 = x2))).
Definition term71 (x0 : nat) := forall y0 : nat, (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0)) = x0.
Definition term66 (x0 : nat) := forall y0 : nat, (Nat.add (Nat.mul y0 (Nat.div x0 y0)) (Nat.modulo x0 y0)) = x0.
Definition term41 (x0 : Prop) := (~ x0) -> False.
Definition term50 := (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)) = y0) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul y1 (Nat.div y0 y1)) (Nat.modulo y0 y1)) = y0).
Definition term7 := (forall y0 : nat, forall y1 : nat, (real_mul (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.mul y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (real_pow (real_of_num y0) y1) = (real_of_num (Nat.pow y0 y1))).
Definition term110 (x0 : nat) (x1 : nat) (x2 : nat) := imp (~ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term18 (x0 : nat) (x1 : nat) := real_add (real_of_num x0) (real_of_num x1).
Definition term22 (x0 : nat) := forall y0 : nat, ((real_of_num x0) = (real_of_num y0)) = (x0 = y0).
Definition term58 (x0 : nat) := forall y0 : nat, (~ ((Nat.add (Nat.modulo x0 y0) (Nat.mul (Nat.div x0 y0) y0)) = x0)) -> (forall y1 : nat, forall y2 : nat, (Nat.add y1 y2) = (Nat.add y2 y1)) -> ((forall y1 : nat, forall y2 : nat, (Nat.add (Nat.mul (Nat.div y1 y2) y2) (Nat.modulo y1 y2)) = y1) /\ (forall y1 : nat, forall y2 : nat, (Nat.add (Nat.mul y2 (Nat.div y1 y2)) (Nat.modulo y1 y2)) = y1)) -> False.
Definition term98 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term108 (x0 : nat) (x1 : nat) := and (x0 = x1).
Definition term54 (x0 : nat) (x1 : nat) := imp (~ ((Nat.add (Nat.modulo x1 x0) (Nat.mul (Nat.div x1 x0) x0)) = x1)).
Definition term85 (x0 : nat) (x1 : nat) := ~ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.modulo x0 x1) (Nat.mul (Nat.div x0 x1) x1))).
Definition term55 (x0 : nat) (x1 : nat) := (~ ((Nat.add (Nat.modulo x1 x0) (Nat.mul (Nat.div x1 x0) x0)) = x1)) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> ~ ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)) = y0) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul y1 (Nat.div y0 y1)) (Nat.modulo y0 y1)) = y0)).
Definition term40 (x0 : nat) (x1 : nat) := Nat.add (Nat.modulo x0 x1) (Nat.mul (Nat.div x0 x1) x1).
Definition term28 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => (x0 = (real_sub x1 y0)) = ((real_add x0 y0) = x1)) x2.
Definition term86 (x0 : Prop) := (~ x0) -> x0.
Definition term109 (x0 : nat) (x1 : nat) (x2 : nat) := (x1 = x0) /\ (x1 = x2).
Definition term100 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x1 = x0)) \/ (~ (x1 = x2)).
Definition term102 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term81 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)) = y0) x0.
Definition term96 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2))).
Definition term25 (x0 : real) := forall y0 : real, forall y1 : real, (x0 = (real_sub y0 y1)) = ((real_add x0 y1) = y0).
Definition term97 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term33 (x0 : nat) (x1 : nat) := real_of_num (Nat.mul (Nat.div x0 x1) x1).
Definition term94 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term17 (x0 : nat) (x1 : nat) := (fun y0 : nat => (real_add (real_of_num x0) (real_of_num y0)) = (real_of_num (Nat.add x0 y0))) x1.
Definition term11 (x0 : nat) (x1 : nat) := (fun y0 : nat => (real_mul (real_of_num x0) (real_of_num y0)) = (real_of_num (Nat.mul x0 y0))) x1.
Definition term77 := fun y0 : nat => forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0).
Definition term5 := (forall y0 : nat, forall y1 : nat, (real_min (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.min y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (real_mul (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.mul y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (real_pow (real_of_num y0) y1) = (real_of_num (Nat.pow y0 y1))))).
Definition term30 (x0 : nat) (x1 : nat) := real_sub (real_of_num x0) (real_mul (real_of_num (Nat.div x0 x1)) (real_of_num x1)).
Definition term64 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1).
Definition term37 (x0 : nat) (x1 : nat) := Nat.mul (Nat.div x0 x1) x1.
Definition term59 (x0 : nat) := forall y0 : nat, (~ ((Nat.add (Nat.modulo x0 y0) (Nat.mul (Nat.div x0 y0) y0)) = x0)) -> (forall y1 : nat, forall y2 : nat, (Nat.add y1 y2) = (Nat.add y2 y1)) -> ~ ((forall y1 : nat, forall y2 : nat, (Nat.add (Nat.mul (Nat.div y1 y2) y2) (Nat.modulo y1 y2)) = y1) /\ (forall y1 : nat, forall y2 : nat, (Nat.add (Nat.mul y2 (Nat.div y1 y2)) (Nat.modulo y1 y2)) = y1)).
Definition term83 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2)).
Definition term6 := (forall y0 : nat, forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (real_mul (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.mul y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (real_pow (real_of_num y0) y1) = (real_of_num (Nat.pow y0 y1)))).
Definition term3 := (forall y0 : nat, forall y1 : nat, (real_lt (real_of_num y0) (real_of_num y1)) = (Peano.lt y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (real_max (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.max y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (real_min (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.min y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (real_mul (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.mul y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (real_pow (real_of_num y0) y1) = (real_of_num (Nat.pow y0 y1))))))).
Definition term2 := (forall y0 : nat, forall y1 : nat, (real_le (real_of_num y0) (real_of_num y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (real_lt (real_of_num y0) (real_of_num y1)) = (Peano.lt y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (real_max (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.max y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (real_min (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.min y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (real_mul (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.mul y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (real_pow (real_of_num y0) y1) = (real_of_num (Nat.pow y0 y1)))))))).
Definition term1 := (forall y0 : nat, forall y1 : nat, (real_gt (real_of_num y0) (real_of_num y1)) = (Peano.gt y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (real_le (real_of_num y0) (real_of_num y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (real_lt (real_of_num y0) (real_of_num y1)) = (Peano.lt y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (real_max (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.max y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (real_min (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.min y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (real_mul (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.mul y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (real_pow (real_of_num y0) y1) = (real_of_num (Nat.pow y0 y1))))))))).
Definition term0 := (forall y0 : nat, forall y1 : nat, (real_ge (real_of_num y0) (real_of_num y1)) = (Peano.ge y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (real_gt (real_of_num y0) (real_of_num y1)) = (Peano.gt y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (real_le (real_of_num y0) (real_of_num y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (real_lt (real_of_num y0) (real_of_num y1)) = (Peano.lt y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (real_max (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.max y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (real_min (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.min y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (real_mul (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.mul y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (real_pow (real_of_num y0) y1) = (real_of_num (Nat.pow y0 y1)))))))))).
Definition term39 (x0 : nat) (x1 : nat) := @eq real (real_of_num (Nat.add (Nat.modulo x0 x1) (Nat.mul (Nat.div x0 x1) x1))).
Definition term95 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term42 (x0 : nat) (x1 : nat) := (~ ((Nat.add (Nat.modulo x1 x0) (Nat.mul (Nat.div x1 x0) x0)) = x1)) -> False.
Definition term120 (x0 : nat) := forall y0 : nat, (real_of_num (Nat.modulo x0 y0)) = (real_sub (real_of_num x0) (real_mul (real_of_num (Nat.div x0 y0)) (real_of_num y0))).
Definition term34 (x0 : nat) (x1 : nat) := real_add (real_of_num (Nat.modulo x0 x1)).
Definition term46 (x0 : nat) (x1 : nat) := (((~ ((Nat.add (Nat.modulo x1 x0) (Nat.mul (Nat.div x1 x0) x0)) = x1)) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)) = y0) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul y1 (Nat.div y0 y1)) (Nat.modulo y0 y1)) = y0)) -> False) -> (~ ((Nat.add (Nat.modulo x1 x0) (Nat.mul (Nat.div x1 x0) x0)) = x1)) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)) = y0) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul y1 (Nat.div y0 y1)) (Nat.modulo y0 y1)) = y0)) -> False) -> (~ ((Nat.add (Nat.modulo x1 x0) (Nat.mul (Nat.div x1 x0) x0)) = x1)) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)) = y0) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul y1 (Nat.div y0 y1)) (Nat.modulo y0 y1)) = y0)) -> False.
Definition term119 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ ((Nat.add (Nat.modulo x0 y0) (Nat.mul (Nat.div x0 y0) y0)) = x0)) -> (forall y1 : nat, forall y2 : nat, (Nat.add y1 y2) = (Nat.add y2 y1)) -> ((forall y1 : nat, forall y2 : nat, (Nat.add (Nat.mul (Nat.div y1 y2) y2) (Nat.modulo y1 y2)) = y1) /\ (forall y1 : nat, forall y2 : nat, (Nat.add (Nat.mul y2 (Nat.div y1 y2)) (Nat.modulo y1 y2)) = y1)) -> False) x1.
Definition term101 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term121 := forall y0 : nat, forall y1 : nat, (real_of_num (Nat.modulo y0 y1)) = (real_sub (real_of_num y0) (real_mul (real_of_num (Nat.div y0 y1)) (real_of_num y1))).
Definition term78 := forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0).
Definition term73 := forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)) = y0.
Definition term68 := forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul y1 (Nat.div y0 y1)) (Nat.modulo y0 y1)) = y0.
Definition term63 := forall y0 : nat, forall y1 : nat, (~ ((Nat.add (Nat.modulo y0 y1) (Nat.mul (Nat.div y0 y1) y1)) = y0)) -> (forall y2 : nat, forall y3 : nat, (Nat.add y2 y3) = (Nat.add y3 y2)) -> ~ ((forall y2 : nat, forall y3 : nat, (Nat.add (Nat.mul (Nat.div y2 y3) y3) (Nat.modulo y2 y3)) = y2) /\ (forall y2 : nat, forall y3 : nat, (Nat.add (Nat.mul y3 (Nat.div y2 y3)) (Nat.modulo y2 y3)) = y2)).
Definition term62 := forall y0 : nat, forall y1 : nat, (~ ((Nat.add (Nat.modulo y0 y1) (Nat.mul (Nat.div y0 y1) y1)) = y0)) -> (forall y2 : nat, forall y3 : nat, (Nat.add y2 y3) = (Nat.add y3 y2)) -> ((forall y2 : nat, forall y3 : nat, (Nat.add (Nat.mul (Nat.div y2 y3) y3) (Nat.modulo y2 y3)) = y2) /\ (forall y2 : nat, forall y3 : nat, (Nat.add (Nat.mul y3 (Nat.div y2 y3)) (Nat.modulo y2 y3)) = y2)) -> False.
Definition term20 := forall y0 : nat, forall y1 : nat, ((real_of_num y0) = (real_of_num y1)) = (y0 = y1).
Definition term14 := forall y0 : nat, forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1)).
Definition term8 := forall y0 : nat, forall y1 : nat, (real_mul (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.mul y0 y1)).
Definition term32 (x0 : nat) (x1 : nat) := real_mul (real_of_num (Nat.div x0 x1)) (real_of_num x1).
Definition term115 (x0 : nat) (x1 : nat) := (~ ((Nat.add (Nat.modulo x1 x0) (Nat.mul (Nat.div x1 x0) x0)) = x1)) -> (Nat.add (Nat.modulo x1 x0) (Nat.mul (Nat.div x1 x0) x0)) = x1.
Definition term87 (x0 : nat) (x1 : nat) := (~ ((Nat.add (Nat.mul (Nat.div x1 x0) x0) (Nat.modulo x1 x0)) = x1)) -> (Nat.add (Nat.mul (Nat.div x1 x0) x0) (Nat.modulo x1 x0)) = x1.
Definition term65 (x0 : nat) := fun y0 : nat => (Nat.add (Nat.mul y0 (Nat.div x0 y0)) (Nat.modulo x0 y0)) = x0.
Definition term52 := (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)) = y0) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul y1 (Nat.div y0 y1)) (Nat.modulo y0 y1)) = y0)) -> False.
Definition term90 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = x2) \/ (~ (x1 = x2)).
Definition term76 (x0 : nat) := forall y0 : nat, (Nat.add x0 y0) = (Nat.add y0 x0).
Definition term27 (x0 : real) (x1 : real) := forall y0 : real, (x0 = (real_sub x1 y0)) = ((real_add x0 y0) = x1).
Definition term38 (x0 : nat) (x1 : nat) := @eq real (real_add (real_of_num (Nat.modulo x0 x1)) (real_mul (real_of_num (Nat.div x0 x1)) (real_of_num x1))).
Definition term93 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x1 = x0)) \/ ((x0 = x2) \/ (~ (x1 = x2))).
Definition term47 (x0 : nat) (x1 : nat) := (((~ ((Nat.add (Nat.modulo x1 x0) (Nat.mul (Nat.div x1 x0) x0)) = x1)) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)) = y0) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul y1 (Nat.div y0 y1)) (Nat.modulo y0 y1)) = y0)) -> False) -> (~ ((Nat.add (Nat.modulo x1 x0) (Nat.mul (Nat.div x1 x0) x0)) = x1)) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)) = y0) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul y1 (Nat.div y0 y1)) (Nat.modulo y0 y1)) = y0)) -> False) -> ((~ ((Nat.add (Nat.modulo x1 x0) (Nat.mul (Nat.div x1 x0) x0)) = x1)) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)) = y0) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul y1 (Nat.div y0 y1)) (Nat.modulo y0 y1)) = y0)) -> False) -> (~ ((Nat.add (Nat.modulo x1 x0) (Nat.mul (Nat.div x1 x0) x0)) = x1)) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)) = y0) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul y1 (Nat.div y0 y1)) (Nat.modulo y0 y1)) = y0)) -> False.
Definition term49 := ~ ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)) = y0) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul y1 (Nat.div y0 y1)) (Nat.modulo y0 y1)) = y0)).
Definition term26 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, (x0 = (real_sub y0 y1)) = ((real_add x0 y1) = y0)) x1.
Definition term80 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add x0 y0) = (Nat.add y0 x0)) x1.
Definition term107 (x0 : nat) (x1 : nat) := and (~ (~ (x0 = x1))).
Definition term12 (x0 : nat) (x1 : nat) := real_mul (real_of_num x0) (real_of_num x1).
Definition term72 := fun y0 : nat => forall y1 : nat, (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)) = y0.
Definition term67 := fun y0 : nat => forall y1 : nat, (Nat.add (Nat.mul y1 (Nat.div y0 y1)) (Nat.modulo y0 y1)) = y0.
Definition term74 := and (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)) = y0).
Definition term4 := (forall y0 : nat, forall y1 : nat, (real_max (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.max y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (real_min (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.min y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (real_mul (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.mul y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (real_pow (real_of_num y0) y1) = (real_of_num (Nat.pow y0 y1)))))).
Definition term118 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ ((Nat.add (Nat.modulo y0 y1) (Nat.mul (Nat.div y0 y1) y1)) = y0)) -> (forall y2 : nat, forall y3 : nat, (Nat.add y2 y3) = (Nat.add y3 y2)) -> ((forall y2 : nat, forall y3 : nat, (Nat.add (Nat.mul (Nat.div y2 y3) y3) (Nat.modulo y2 y3)) = y2) /\ (forall y2 : nat, forall y3 : nat, (Nat.add (Nat.mul y3 (Nat.div y2 y3)) (Nat.modulo y2 y3)) = y2)) -> False) x0.
Definition term79 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) x0.
Definition term21 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((real_of_num y0) = (real_of_num y1)) = (y0 = y1)) x0.
Definition term15 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1))) x0.
Definition term9 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (real_mul (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.mul y0 y1))) x0.
Definition term70 (x0 : nat) := fun y0 : nat => (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0)) = x0.
Definition term36 (x0 : nat) (x1 : nat) := real_of_num (Nat.add (Nat.modulo x0 x1) (Nat.mul (Nat.div x0 x1) x1)).
Definition term45 (x0 : nat) (x1 : nat) := ((~ ((Nat.add (Nat.modulo x1 x0) (Nat.mul (Nat.div x1 x0) x0)) = x1)) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)) = y0) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul y1 (Nat.div y0 y1)) (Nat.modulo y0 y1)) = y0)) -> False) -> (~ ((Nat.add (Nat.modulo x1 x0) (Nat.mul (Nat.div x1 x0) x0)) = x1)) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)) = y0) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul y1 (Nat.div y0 y1)) (Nat.modulo y0 y1)) = y0)) -> False.
Definition term103 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term16 (x0 : nat) := forall y0 : nat, (real_add (real_of_num x0) (real_of_num y0)) = (real_of_num (Nat.add x0 y0)).
Definition term10 (x0 : nat) := forall y0 : nat, (real_mul (real_of_num x0) (real_of_num y0)) = (real_of_num (Nat.mul x0 y0)).
Definition term116 (x0 : nat) (x1 : nat) := ((Nat.add (Nat.modulo x1 x0) (Nat.mul (Nat.div x1 x0) x0)) = x1) -> False.
Definition term48 := ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)) = y0) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul y1 (Nat.div y0 y1)) (Nat.modulo y0 y1)) = y0)) -> False.
Definition term111 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((x1 = x0) /\ (x1 = x2)).
Definition term13 (x0 : nat) (x1 : nat) := real_of_num (Nat.mul x0 x1).
Definition term56 (x0 : nat) := fun y0 : nat => (~ ((Nat.add (Nat.modulo x0 y0) (Nat.mul (Nat.div x0 y0) y0)) = x0)) -> (forall y1 : nat, forall y2 : nat, (Nat.add y1 y2) = (Nat.add y2 y1)) -> ((forall y1 : nat, forall y2 : nat, (Nat.add (Nat.mul (Nat.div y1 y2) y2) (Nat.modulo y1 y2)) = y1) /\ (forall y1 : nat, forall y2 : nat, (Nat.add (Nat.mul y2 (Nat.div y1 y2)) (Nat.modulo y1 y2)) = y1)) -> False.
Definition term35 (x0 : nat) (x1 : nat) := real_add (real_of_num (Nat.modulo x0 x1)) (real_of_num (Nat.mul (Nat.div x0 x1) x1)).
Definition term44 (x0 : nat) (x1 : nat) := (~ ((Nat.add (Nat.modulo x1 x0) (Nat.mul (Nat.div x1 x0) x0)) = x1)) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)) = y0) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul y1 (Nat.div y0 y1)) (Nat.modulo y0 y1)) = y0)) -> False.
Definition term89 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = x2)) \/ (x1 = x2).
Definition term106 (x0 : nat) (x1 : nat) := ~ (~ (x0 = x1)).
Definition term57 (x0 : nat) := fun y0 : nat => (~ ((Nat.add (Nat.modulo x0 y0) (Nat.mul (Nat.div x0 y0) y0)) = x0)) -> (forall y1 : nat, forall y2 : nat, (Nat.add y1 y2) = (Nat.add y2 y1)) -> ~ ((forall y1 : nat, forall y2 : nat, (Nat.add (Nat.mul (Nat.div y1 y2) y2) (Nat.modulo y1 y2)) = y1) /\ (forall y1 : nat, forall y2 : nat, (Nat.add (Nat.mul y2 (Nat.div y1 y2)) (Nat.modulo y1 y2)) = y1)).
Definition term92 (x0 : nat) (x1 : nat) := or (~ (x0 = x1)).
Definition term82 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0)) = x0) x1.
Definition term23 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((real_of_num x0) = (real_of_num y0)) = (x0 = y0)) x1.
Definition term51 := imp (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)).
Definition term19 (x0 : nat) (x1 : nat) := real_of_num (Nat.add x0 x1).
Definition term24 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, (y0 = (real_sub y1 y2)) = ((real_add y0 y2) = y1)) x0.
Definition term112 (x0 : nat) (x1 : nat) (x2 : nat) := ((x0 = x1) /\ (x0 = x2)) -> x1 = x2.
Definition term84 (x0 : nat) (x1 : nat) := (~ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.modulo x0 x1) (Nat.mul (Nat.div x0 x1) x1)))) -> (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.modulo x0 x1) (Nat.mul (Nat.div x0 x1) x1)).
Definition term29 (x0 : nat) (x1 : nat) := real_of_num (Nat.modulo x0 x1).
Definition term61 := fun y0 : nat => forall y1 : nat, (~ ((Nat.add (Nat.modulo y0 y1) (Nat.mul (Nat.div y0 y1) y1)) = y0)) -> (forall y2 : nat, forall y3 : nat, (Nat.add y2 y3) = (Nat.add y3 y2)) -> ~ ((forall y2 : nat, forall y3 : nat, (Nat.add (Nat.mul (Nat.div y2 y3) y3) (Nat.modulo y2 y3)) = y2) /\ (forall y2 : nat, forall y3 : nat, (Nat.add (Nat.mul y3 (Nat.div y2 y3)) (Nat.modulo y2 y3)) = y2)).
Definition term60 := fun y0 : nat => forall y1 : nat, (~ ((Nat.add (Nat.modulo y0 y1) (Nat.mul (Nat.div y0 y1) y1)) = y0)) -> (forall y2 : nat, forall y3 : nat, (Nat.add y2 y3) = (Nat.add y3 y2)) -> ((forall y2 : nat, forall y3 : nat, (Nat.add (Nat.mul (Nat.div y2 y3) y3) (Nat.modulo y2 y3)) = y2) /\ (forall y2 : nat, forall y3 : nat, (Nat.add (Nat.mul y3 (Nat.div y2 y3)) (Nat.modulo y2 y3)) = y2)) -> False.
Definition term113 (x0 : nat) (x1 : nat) := ((Nat.add (Nat.mul (Nat.div x1 x0) x0) (Nat.modulo x1 x0)) = (Nat.add (Nat.modulo x1 x0) (Nat.mul (Nat.div x1 x0) x0))) /\ ((Nat.add (Nat.mul (Nat.div x1 x0) x0) (Nat.modulo x1 x0)) = x1).
Definition term88 (x0 : nat) (x1 : nat) := ~ ((Nat.add (Nat.mul (Nat.div x1 x0) x0) (Nat.modulo x1 x0)) = x1).
Definition term43 (x0 : nat) (x1 : nat) := ~ ((Nat.add (Nat.modulo x1 x0) (Nat.mul (Nat.div x1 x0) x0)) = x1).
