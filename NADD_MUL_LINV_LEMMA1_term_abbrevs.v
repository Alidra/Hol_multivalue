Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term42 (x0 : nadd) (x1 : nat) := (fun y0 : nat => Nat.div (Nat.mul y0 y0) (dest_nadd x0 y0)) x1.
Definition term58 (x0 : nadd) (x1 : nat) := dist (@pair nat nat (Nat.mul (dest_nadd x0 x1) (Nat.div (Nat.mul x1 x1) (dest_nadd x0 x1))) (Nat.add (Nat.mul (Nat.div (Nat.mul x1 x1) (dest_nadd x0 x1)) (dest_nadd x0 x1)) (Nat.modulo (Nat.mul x1 x1) (dest_nadd x0 x1)))).
Definition term54 (x0 : nadd) (x1 : nat) := @pair nat nat (Nat.mul (dest_nadd x0 x1) (Nat.div (Nat.mul x1 x1) (dest_nadd x0 x1))).
Definition term27 (x0 : nat) := (fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> forall y1 : nat, (y1 = (Nat.add (Nat.mul (Nat.div y1 y0) y0) (Nat.modulo y1 y0))) /\ (Peano.lt (Nat.modulo y1 y0) y0)) x0.
Definition term6 := (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.le y0 y1) -> forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.le y0 y1.
Definition term39 (x0 : nadd) (x1 : nat) := @eq Prop ((fun y0 : nat => Peano.le (dist (@pair nat nat (Nat.mul (dest_nadd x0 x1) (nadd_rinv x0 x1)) y0)) (dest_nadd x0 x1)) (Nat.mul x1 x1)).
Definition term37 (x0 : nadd) (x1 : nat) := (fun y0 : nat => Peano.le (dist (@pair nat nat (Nat.mul (dest_nadd x0 x1) (nadd_rinv x0 x1)) y0)) (dest_nadd x0 x1)) (Nat.add (Nat.mul (Nat.div (Nat.mul x1 x1) (dest_nadd x0 x1)) (dest_nadd x0 x1)) (Nat.modulo (Nat.mul x1 x1) (dest_nadd x0 x1))).
Definition term53 (x0 : nadd) (x1 : nat) := @pair nat nat (Nat.mul (dest_nadd x0 x1) (nadd_rinv x0 x1)).
Definition term36 (x0 : nadd) (x1 : nat) := (fun y0 : nat => Peano.le (dist (@pair nat nat (Nat.mul (dest_nadd x0 x1) (nadd_rinv x0 x1)) y0)) (dest_nadd x0 x1)) (Nat.mul x1 x1).
Definition term75 := forall y0 : nadd, forall y1 : nat, (~ ((dest_nadd y0 y1) = (NUMERAL 0))) -> Peano.le (dist (@pair nat nat (Nat.mul (dest_nadd y0 y1) (nadd_rinv y0 y1)) (Nat.mul y1 y1))) (dest_nadd y0 y1).
Definition term30 (x0 : nadd) (x1 : nat) := forall y0 : nat, (y0 = (Nat.add (Nat.mul (Nat.div y0 (dest_nadd x0 x1)) (dest_nadd x0 x1)) (Nat.modulo y0 (dest_nadd x0 x1)))) /\ (Peano.lt (Nat.modulo y0 (dest_nadd x0 x1)) (dest_nadd x0 x1)).
Definition term62 (x0 : nadd) (x1 : nat) := Nat.mul (Nat.div (Nat.mul x1 x1) (dest_nadd x0 x1)) (dest_nadd x0 x1).
Definition term73 (x0 : nadd) (x1 : nat) := (~ ((dest_nadd x0 x1) = (NUMERAL 0))) -> Peano.le (dist (@pair nat nat (Nat.mul (dest_nadd x0 x1) (nadd_rinv x0 x1)) (Nat.mul x1 x1))) (dest_nadd x0 x1).
Definition term5 (x0 : nat) (x1 : nat) := (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.le y0 y1) -> Peano.le x0 x1.
Definition term69 (x0 : nadd) (x1 : nat) := Peano.le (Nat.modulo (Nat.mul x1 x1) (dest_nadd x0 x1)).
Definition term70 (x0 : nadd) (x1 : nat) := Peano.le (Nat.modulo (Nat.mul x1 x1) (dest_nadd x0 x1)) (dest_nadd x0 x1).
Definition term22 (x0 : nat) (x1 : nat) := (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1).
Definition term26 := (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> forall y1 : nat, (y1 = (Nat.add (Nat.mul (Nat.div y1 y0) y0) (Nat.modulo y1 y0))) /\ (Peano.lt (Nat.modulo y1 y0) y0).
Definition term7 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (dist (@pair nat nat y0 (Nat.add y0 y1))) = y1) x0.
Definition term29 (x0 : nadd) (x1 : nat) := (~ ((dest_nadd x0 x1) = (NUMERAL 0))) -> forall y0 : nat, (y0 = (Nat.add (Nat.mul (Nat.div y0 (dest_nadd x0 x1)) (dest_nadd x0 x1)) (Nat.modulo y0 (dest_nadd x0 x1)))) /\ (Peano.lt (Nat.modulo y0 (dest_nadd x0 x1)) (dest_nadd x0 x1)).
Definition term15 (x0 : nadd) := fun y0 : nat => Nat.div (Nat.mul y0 y0) (dest_nadd x0 y0).
Definition term40 (x0 : nadd) (x1 : nat) := Peano.le (dist (@pair nat nat (Nat.mul (dest_nadd x0 x1) (nadd_rinv x0 x1)) (Nat.mul x1 x1))) (dest_nadd x0 x1).
Definition term21 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term66 (x0 : nadd) (x1 : nat) := Peano.le (dist (@pair nat nat (Nat.mul (Nat.div (Nat.mul x1 x1) (dest_nadd x0 x1)) (dest_nadd x0 x1)) (Nat.add (Nat.mul (Nat.div (Nat.mul x1 x1) (dest_nadd x0 x1)) (dest_nadd x0 x1)) (Nat.modulo (Nat.mul x1 x1) (dest_nadd x0 x1))))).
Definition term60 (x0 : nadd) (x1 : nat) := Peano.le (dist (@pair nat nat (Nat.mul (dest_nadd x0 x1) (Nat.div (Nat.mul x1 x1) (dest_nadd x0 x1))) (Nat.add (Nat.mul (Nat.div (Nat.mul x1 x1) (dest_nadd x0 x1)) (dest_nadd x0 x1)) (Nat.modulo (Nat.mul x1 x1) (dest_nadd x0 x1))))).
Definition term59 (x0 : nadd) (x1 : nat) := Peano.le (dist (@pair nat nat (Nat.mul (dest_nadd x0 x1) (nadd_rinv x0 x1)) (Nat.add (Nat.mul (Nat.div (Nat.mul x1 x1) (dest_nadd x0 x1)) (dest_nadd x0 x1)) (Nat.modulo (Nat.mul x1 x1) (dest_nadd x0 x1))))).
Definition term56 (x0 : nadd) (x1 : nat) := @pair nat nat (Nat.mul (dest_nadd x0 x1) (Nat.div (Nat.mul x1 x1) (dest_nadd x0 x1))) (Nat.add (Nat.mul (Nat.div (Nat.mul x1 x1) (dest_nadd x0 x1)) (dest_nadd x0 x1)) (Nat.modulo (Nat.mul x1 x1) (dest_nadd x0 x1))).
Definition term63 (x0 : nadd) (x1 : nat) := @pair nat nat (Nat.mul (Nat.div (Nat.mul x1 x1) (dest_nadd x0 x1)) (dest_nadd x0 x1)).
Definition term25 := forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> forall y1 : nat, (y1 = (Nat.add (Nat.mul (Nat.div y1 y0) y0) (Nat.modulo y1 y0))) /\ (Peano.lt (Nat.modulo y1 y0) y0).
Definition term43 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term16 := forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1).
Definition term0 := forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.le y0 y1.
Definition term51 (x0 : nadd) (x1 : nat) := Nat.mul (dest_nadd x0 x1) (nadd_rinv x0 x1).
Definition term68 (x0 : nadd) (x1 : nat) := Nat.modulo (Nat.mul x1 x1) (dest_nadd x0 x1).
Definition term44 (x0 : nat -> nat) (x1 : nat) := (fun y0 : nat => x0 y0) x1.
Definition term55 (x0 : nadd) (x1 : nat) := @pair nat nat (Nat.mul (dest_nadd x0 x1) (nadd_rinv x0 x1)) (Nat.add (Nat.mul (Nat.div (Nat.mul x1 x1) (dest_nadd x0 x1)) (dest_nadd x0 x1)) (Nat.modulo (Nat.mul x1 x1) (dest_nadd x0 x1))).
Definition term20 (x0 : nat) (x1 : nat) := (~ (x1 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1).
Definition term3 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt x0 y0) -> Peano.le x0 y0) x1.
Definition term49 (x0 : nadd) (x1 : nat) := @eq nat ((fun y0 : nat => Nat.div (Nat.mul y0 y0) (dest_nadd x0 y0)) x1).
Definition term65 (x0 : nadd) (x1 : nat) := dist (@pair nat nat (Nat.mul (Nat.div (Nat.mul x1 x1) (dest_nadd x0 x1)) (dest_nadd x0 x1)) (Nat.add (Nat.mul (Nat.div (Nat.mul x1 x1) (dest_nadd x0 x1)) (dest_nadd x0 x1)) (Nat.modulo (Nat.mul x1 x1) (dest_nadd x0 x1)))).
Definition term57 (x0 : nadd) (x1 : nat) := dist (@pair nat nat (Nat.mul (dest_nadd x0 x1) (nadd_rinv x0 x1)) (Nat.add (Nat.mul (Nat.div (Nat.mul x1 x1) (dest_nadd x0 x1)) (dest_nadd x0 x1)) (Nat.modulo (Nat.mul x1 x1) (dest_nadd x0 x1)))).
Definition term10 (x0 : nat) (x1 : nat) := dist (@pair nat nat x0 (Nat.add x0 x1)).
Definition term12 (x0 : nat) := forall y0 : nat, (Nat.mul x0 y0) = (Nat.mul y0 x0).
Definition term72 (x0 : nadd) (x1 : nat) := (forall y0 : nat, (y0 = (Nat.add (Nat.mul (Nat.div y0 (dest_nadd x0 x1)) (dest_nadd x0 x1)) (Nat.modulo y0 (dest_nadd x0 x1)))) /\ (Peano.lt (Nat.modulo y0 (dest_nadd x0 x1)) (dest_nadd x0 x1))) -> Peano.le (dist (@pair nat nat (Nat.mul (dest_nadd x0 x1) (nadd_rinv x0 x1)) (Nat.mul x1 x1))) (dest_nadd x0 x1).
Definition term47 (x0 : nadd) := fun y0 : nat => (fun y1 : nat => Nat.div (Nat.mul y1 y1) (dest_nadd x0 y1)) y0.
Definition term13 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.mul x0 y0) = (Nat.mul y0 x0)) x1.
Definition term67 (x0 : nadd) (x1 : nat) := Peano.le (dist (@pair nat nat (Nat.mul (Nat.div (Nat.mul x1 x1) (dest_nadd x0 x1)) (dest_nadd x0 x1)) (Nat.add (Nat.mul (Nat.div (Nat.mul x1 x1) (dest_nadd x0 x1)) (dest_nadd x0 x1)) (Nat.modulo (Nat.mul x1 x1) (dest_nadd x0 x1))))) (dest_nadd x0 x1).
Definition term61 (x0 : nadd) (x1 : nat) := Peano.le (dist (@pair nat nat (Nat.mul (dest_nadd x0 x1) (Nat.div (Nat.mul x1 x1) (dest_nadd x0 x1))) (Nat.add (Nat.mul (Nat.div (Nat.mul x1 x1) (dest_nadd x0 x1)) (dest_nadd x0 x1)) (Nat.modulo (Nat.mul x1 x1) (dest_nadd x0 x1))))) (dest_nadd x0 x1).
Definition term38 (x0 : nadd) (x1 : nat) := Peano.le (dist (@pair nat nat (Nat.mul (dest_nadd x0 x1) (nadd_rinv x0 x1)) (Nat.add (Nat.mul (Nat.div (Nat.mul x1 x1) (dest_nadd x0 x1)) (dest_nadd x0 x1)) (Nat.modulo (Nat.mul x1 x1) (dest_nadd x0 x1))))) (dest_nadd x0 x1).
Definition term8 (x0 : nat) := forall y0 : nat, (dist (@pair nat nat x0 (Nat.add x0 y0))) = y0.
Definition term23 (x0 : nat) := forall y0 : nat, (y0 = (Nat.add (Nat.mul (Nat.div y0 x0) x0) (Nat.modulo y0 x0))) /\ (Peano.lt (Nat.modulo y0 x0) x0).
Definition term34 (x0 : nadd) (x1 : nat) := Nat.add (Nat.mul (Nat.div (Nat.mul x1 x1) (dest_nadd x0 x1)) (dest_nadd x0 x1)) (Nat.modulo (Nat.mul x1 x1) (dest_nadd x0 x1)).
Definition term64 (x0 : nadd) (x1 : nat) := @pair nat nat (Nat.mul (Nat.div (Nat.mul x1 x1) (dest_nadd x0 x1)) (dest_nadd x0 x1)) (Nat.add (Nat.mul (Nat.div (Nat.mul x1 x1) (dest_nadd x0 x1)) (dest_nadd x0 x1)) (Nat.modulo (Nat.mul x1 x1) (dest_nadd x0 x1))).
Definition term17 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) x0.
Definition term11 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) x0.
Definition term1 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y0 y1) -> Peano.le y0 y1) x0.
Definition term32 (x0 : nadd) (x1 : nat) := ((Nat.mul x1 x1) = (Nat.add (Nat.mul (Nat.div (Nat.mul x1 x1) (dest_nadd x0 x1)) (dest_nadd x0 x1)) (Nat.modulo (Nat.mul x1 x1) (dest_nadd x0 x1)))) /\ (Peano.lt (Nat.modulo (Nat.mul x1 x1) (dest_nadd x0 x1)) (dest_nadd x0 x1)).
Definition term45 (x0 : nadd) (x1 : nat) := (fun y0 : nat => (fun y1 : nat => Nat.div (Nat.mul y1 y1) (dest_nadd x0 y1)) y0) x1.
Definition term48 (x0 : nadd) (x1 : nat) := @eq nat ((fun y0 : nat => (fun y1 : nat => Nat.div (Nat.mul y1 y1) (dest_nadd x0 y1)) y0) x1).
Definition term31 (x0 : nadd) (x1 : nat) := (fun y0 : nat => (y0 = (Nat.add (Nat.mul (Nat.div y0 (dest_nadd x0 x1)) (dest_nadd x0 x1)) (Nat.modulo y0 (dest_nadd x0 x1)))) /\ (Peano.lt (Nat.modulo y0 (dest_nadd x0 x1)) (dest_nadd x0 x1))) (Nat.mul x1 x1).
Definition term33 (x0 : nadd) (x1 : nat) := Peano.lt (Nat.modulo (Nat.mul x1 x1) (dest_nadd x0 x1)) (dest_nadd x0 x1).
Definition term35 (x0 : nadd) (x1 : nat) := fun y0 : nat => Peano.le (dist (@pair nat nat (Nat.mul (dest_nadd x0 x1) (nadd_rinv x0 x1)) y0)) (dest_nadd x0 x1).
Definition term14 (x0 : nadd) := (fun y0 : nadd => (nadd_rinv y0) = (fun y1 : nat => Nat.div (Nat.mul y1 y1) (dest_nadd y0 y1))) x0.
Definition term19 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0)) x1.
Definition term9 (x0 : nat) (x1 : nat) := (fun y0 : nat => (dist (@pair nat nat x0 (Nat.add x0 y0))) = y0) x1.
Definition term24 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> forall y0 : nat, (y0 = (Nat.add (Nat.mul (Nat.div y0 x0) x0) (Nat.modulo y0 x0))) /\ (Peano.lt (Nat.modulo y0 x0) x0).
Definition term28 (x0 : nadd) (x1 : nat) := ~ ((dest_nadd x0 x1) = (NUMERAL 0)).
Definition term41 (x0 : nadd) (x1 : nat) := @eq Prop (Peano.le (dist (@pair nat nat (Nat.mul (dest_nadd x0 x1) (nadd_rinv x0 x1)) (Nat.mul x1 x1))) (dest_nadd x0 x1)).
Definition term4 (x0 : nat) (x1 : nat) := (Peano.lt x0 x1) -> Peano.le x0 x1.
Definition term52 (x0 : nadd) (x1 : nat) := Nat.mul (dest_nadd x0 x1) (Nat.div (Nat.mul x1 x1) (dest_nadd x0 x1)).
Definition term2 (x0 : nat) := forall y0 : nat, (Peano.lt x0 y0) -> Peano.le x0 y0.
Definition term46 (x0 : nadd) (x1 : nat) := Nat.div (Nat.mul x1 x1) (dest_nadd x0 x1).
Definition term71 (x0 : nadd) (x1 : nat) := (Peano.lt (Nat.modulo (Nat.mul x1 x1) (dest_nadd x0 x1)) (dest_nadd x0 x1)) -> Peano.le (Nat.modulo (Nat.mul x1 x1) (dest_nadd x0 x1)) (dest_nadd x0 x1).
Definition term74 (x0 : nadd) := forall y0 : nat, (~ ((dest_nadd x0 y0) = (NUMERAL 0))) -> Peano.le (dist (@pair nat nat (Nat.mul (dest_nadd x0 y0) (nadd_rinv x0 y0)) (Nat.mul y0 y0))) (dest_nadd x0 y0).
Definition term18 (x0 : nat) := forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0).
Definition term50 (x0 : nadd) (x1 : nat) := Nat.mul (dest_nadd x0 x1).
