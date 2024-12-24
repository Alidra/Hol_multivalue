Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term82 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul (Nat.div (Nat.add x0 x1) x2) x2).
Definition term44 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1).
Definition term53 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.div (Nat.add x0 x1) x2.
Definition term79 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Nat.add x0 y0) = (Nat.add x1 y0)) = (x0 = x1).
Definition term1 (a0 : Type') (x0 : a0) := forall y0 : a0, (x0 = y0) = (y0 = x0).
Definition term91 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Nat.add y0 y1) = (Nat.add y0 y2)) = (y1 = y2)) x0.
Definition term76 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Nat.add y0 y2) = (Nat.add y1 y2)) = (y0 = y1)) x0.
Definition term70 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Nat.mul y0 y2) = (Nat.mul y1 y2)) = ((y0 = y1) \/ (y2 = (NUMERAL 0)))) x0.
Definition term17 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.add (Nat.mul y0 y2) (Nat.mul y1 y2)) = (Nat.mul (Nat.add y0 y1) y2)) x0.
Definition term55 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.add x0 x1) = (Nat.add (Nat.mul (Nat.div (Nat.add x0 x1) x2) x2) (Nat.modulo (Nat.add x0 x1) x2))) -> ((Nat.modulo (Nat.add x0 x1) x2) = (Nat.add (Nat.modulo x0 x2) (Nat.modulo x1 x2))) = ((Nat.div (Nat.add x0 x1) x2) = (Nat.add (Nat.div x0 x2) (Nat.div x1 x2))).
Definition term47 (x0 : nat) (x1 : nat) := @eq nat (Nat.add x0 x1).
Definition term39 (x0 : nat) := (fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> forall y1 : nat, (y1 = (Nat.add (Nat.mul (Nat.div y1 y0) y0) (Nat.modulo y1 y0))) /\ (Peano.lt (Nat.modulo y1 y0) y0)) x0.
Definition term80 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Nat.add x0 y0) = (Nat.add x1 y0)) = (x0 = x1)) x2.
Definition term84 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.div (Nat.add x0 x1) x2) x2.
Definition term52 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.modulo x0 x2) (Nat.modulo x1 x2).
Definition term42 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul (Nat.div (Nat.add x0 x1) x2) x2) (Nat.modulo (Nat.add x0 x1) x2).
Definition term107 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.add x0 x1) = (Nat.add (Nat.add (Nat.mul (Nat.div x0 x2) x2) (Nat.modulo x0 x2)) (Nat.add (Nat.mul (Nat.div x1 x2) x2) (Nat.modulo x1 x2)))) -> ((Nat.add x0 x1) = (Nat.add (Nat.mul (Nat.div (Nat.add x0 x1) x2) x2) (Nat.modulo (Nat.add x0 x1) x2))) -> ((Nat.modulo (Nat.add x0 x1) x2) = (Nat.add (Nat.modulo x0 x2) (Nat.modulo x1 x2))) = ((Nat.div (Nat.add x0 x1) x2) = (Nat.add (Nat.div x0 x2) (Nat.div x1 x2))).
Definition term94 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Nat.add x0 x1) = (Nat.add x0 y0)) = (x1 = y0).
Definition term41 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.add x0 x1) = (Nat.add (Nat.mul (Nat.div (Nat.add x0 x1) x2) x2) (Nat.modulo (Nat.add x0 x1) x2))) /\ (Peano.lt (Nat.modulo (Nat.add x0 x1) x2) x2).
Definition term19 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.add (Nat.mul x0 y0) (Nat.mul x1 y0)) = (Nat.mul (Nat.add x0 x1) y0)) x2.
Definition term25 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.add x0 (Nat.add x1 (Nat.add x2 x3)).
Definition term87 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.add (Nat.div x0 x2) (Nat.div x1 x2)) = (Nat.div (Nat.add x0 x1) x2)) \/ False.
Definition term88 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((Nat.add (Nat.div x0 x2) (Nat.div x1 x2)) = (Nat.div (Nat.add x0 x1) x2)).
Definition term68 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((Nat.add (Nat.mul (Nat.add (Nat.div x0 x2) (Nat.div x1 x2)) x2) (Nat.add (Nat.modulo x0 x2) (Nat.modulo x1 x2))) = (Nat.add (Nat.mul (Nat.div (Nat.add x0 x1) x2) x2) (Nat.modulo (Nat.add x0 x1) x2))).
Definition term60 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((Nat.add (Nat.add (Nat.mul (Nat.div x0 x2) x2) (Nat.mul (Nat.div x1 x2) x2)) (Nat.add (Nat.modulo x0 x2) (Nat.modulo x1 x2))) = (Nat.add (Nat.mul (Nat.div (Nat.add x0 x1) x2) x2) (Nat.modulo (Nat.add x0 x1) x2))).
Definition term50 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((Nat.add (Nat.add (Nat.mul (Nat.div x0 x2) x2) (Nat.modulo x0 x2)) (Nat.add (Nat.mul (Nat.div x1 x2) x2) (Nat.modulo x1 x2))) = (Nat.add (Nat.mul (Nat.div (Nat.add x0 x1) x2) x2) (Nat.modulo (Nat.add x0 x1) x2))).
Definition term64 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.add (Nat.mul (Nat.div x0 x2) x2) (Nat.mul (Nat.div x1 x2) x2)).
Definition term105 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.modulo (Nat.add x0 x1) x2) = (Nat.add (Nat.modulo x0 x2) (Nat.modulo x1 x2))) -> (Nat.div (Nat.add x0 x1) x2) = (Nat.add (Nat.div x0 x2) (Nat.div x1 x2)).
Definition term104 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.div (Nat.add x0 x1) x2) = (Nat.add (Nat.div x0 x2) (Nat.div x1 x2))) -> (Nat.modulo (Nat.add x0 x1) x2) = (Nat.add (Nat.modulo x0 x2) (Nat.modulo x1 x2)).
Definition term102 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.add (Nat.div x0 x2) (Nat.div x1 x2)) = (Nat.div (Nat.add x0 x1) x2)) -> (Nat.add (Nat.div x0 x2) (Nat.div x1 x2)) = (Nat.div (Nat.add x0 x1) x2).
Definition term22 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.add x0 x1) x2.
Definition term34 (x0 : nat) (x1 : nat) := (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1).
Definition term38 := (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> forall y1 : nat, (y1 = (Nat.add (Nat.mul (Nat.div y1 y0) y0) (Nat.modulo y1 y0))) /\ (Peano.lt (Nat.modulo y1 y0) y0).
Definition term0 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a0, (y0 = y1) = (y1 = y0)) x0.
Definition term8 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.add (Nat.mul x0 y0) (Nat.mul x1 y0)) = (Nat.mul (Nat.add x0 x1) y0).
Definition term43 (x0 : nat) (x1 : nat) := (fun y0 : nat => (y0 = (Nat.add (Nat.mul (Nat.div y0 x0) x0) (Nat.modulo y0 x0))) /\ (Peano.lt (Nat.modulo y0 x0) x0)) x1.
Definition term57 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.add (Nat.mul (Nat.div x0 x2) x2) (Nat.mul (Nat.div x1 x2) x2)) (Nat.add (Nat.modulo x0 x2) (Nat.modulo x1 x2)).
Definition term75 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = x1) \/ (x2 = (NUMERAL 0)).
Definition term46 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.add (Nat.mul (Nat.div x0 x2) x2) (Nat.modulo x0 x2)) (Nat.add (Nat.mul (Nat.div x1 x2) x2) (Nat.modulo x1 x2)).
Definition term101 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.add (Nat.modulo x0 x2) (Nat.modulo x1 x2)) = (Nat.modulo (Nat.add x0 x1) x2)) -> (Nat.modulo (Nat.add x0 x1) x2) = (Nat.add (Nat.modulo x0 x2) (Nat.modulo x1 x2)).
Definition term90 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.add (Nat.div x0 x2) (Nat.div x1 x2)) = (Nat.div (Nat.add x0 x1) x2)) -> (Nat.div (Nat.add x0 x1) x2) = (Nat.add (Nat.div x0 x2) (Nat.div x1 x2)).
Definition term73 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Nat.mul x0 y0) = (Nat.mul x1 y0)) = ((x0 = x1) \/ (y0 = (NUMERAL 0))).
Definition term93 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.add x0 y0) = (Nat.add x0 y1)) = (y0 = y1)) x1.
Definition term78 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.add x0 y1) = (Nat.add y0 y1)) = (x0 = y0)) x1.
Definition term72 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.mul x0 y1) = (Nat.mul y0 y1)) = ((x0 = y0) \/ (y1 = (NUMERAL 0)))) x1.
Definition term18 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add (Nat.mul x0 y1) (Nat.mul y0 y1)) = (Nat.mul (Nat.add x0 y0) y1)) x1.
Definition term54 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.div x0 x2) (Nat.div x1 x2).
Definition term99 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((Nat.add (Nat.modulo x0 x2) (Nat.modulo x1 x2)) = (Nat.modulo (Nat.add x0 x1) x2)).
Definition term33 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term10 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Nat.add (Nat.mul x0 y1) (Nat.mul y0 y1)) = (Nat.mul (Nat.add x0 y0) y1).
Definition term111 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x2 = (NUMERAL 0))) -> ((Nat.modulo (Nat.add x0 x1) x2) = (Nat.add (Nat.modulo x0 x2) (Nat.modulo x1 x2))) = ((Nat.div (Nat.add x0 x1) x2) = (Nat.add (Nat.div x0 x2) (Nat.div x1 x2))).
Definition term58 (x0 : nat) (x1 : nat) := Nat.mul (Nat.div x0 x1) x1.
Definition term110 (x0 : nat) (x1 : nat) (x2 : nat) := (forall y0 : nat, (y0 = (Nat.add (Nat.mul (Nat.div y0 x2) x2) (Nat.modulo y0 x2))) /\ (Peano.lt (Nat.modulo y0 x2) x2)) -> ((Nat.modulo (Nat.add x0 x1) x2) = (Nat.add (Nat.modulo x0 x2) (Nat.modulo x1 x2))) = ((Nat.div (Nat.add x0 x1) x2) = (Nat.add (Nat.div x0 x2) (Nat.div x1 x2))).
Definition term63 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.add (Nat.div x0 x2) (Nat.div x1 x2)) x2.
Definition term112 (x0 : nat) (x1 : nat) := forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> ((Nat.modulo (Nat.add x0 x1) y0) = (Nat.add (Nat.modulo x0 y0) (Nat.modulo x1 y0))) = ((Nat.div (Nat.add x0 x1) y0) = (Nat.add (Nat.div x0 y0) (Nat.div x1 y0))).
Definition term67 (x0 : nat) (x1 : nat) (x2 : nat) := @eq nat (Nat.add (Nat.mul (Nat.add (Nat.div x0 x2) (Nat.div x1 x2)) x2) (Nat.add (Nat.modulo x0 x2) (Nat.modulo x1 x2))).
Definition term37 := forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> forall y1 : nat, (y1 = (Nat.add (Nat.mul (Nat.div y1 y0) y0) (Nat.modulo y1 y0))) /\ (Peano.lt (Nat.modulo y1 y0) y0).
Definition term69 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.add (Nat.mul (Nat.add (Nat.div x0 x2) (Nat.div x1 x2)) x2) (Nat.add (Nat.modulo x0 x2) (Nat.modulo x1 x2))) = (Nat.add (Nat.mul (Nat.div (Nat.add x0 x1) x2) x2) (Nat.modulo (Nat.add x0 x1) x2))) -> ((Nat.modulo (Nat.add x0 x1) x2) = (Nat.add (Nat.modulo x0 x2) (Nat.modulo x1 x2))) = ((Nat.div (Nat.add x0 x1) x2) = (Nat.add (Nat.div x0 x2) (Nat.div x1 x2))).
Definition term61 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.add (Nat.add (Nat.mul (Nat.div x0 x2) x2) (Nat.mul (Nat.div x1 x2) x2)) (Nat.add (Nat.modulo x0 x2) (Nat.modulo x1 x2))) = (Nat.add (Nat.mul (Nat.div (Nat.add x0 x1) x2) x2) (Nat.modulo (Nat.add x0 x1) x2))) -> ((Nat.modulo (Nat.add x0 x1) x2) = (Nat.add (Nat.modulo x0 x2) (Nat.modulo x1 x2))) = ((Nat.div (Nat.add x0 x1) x2) = (Nat.add (Nat.div x0 x2) (Nat.div x1 x2))).
Definition term56 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.add (Nat.add (Nat.mul (Nat.div x0 x2) x2) (Nat.modulo x0 x2)) (Nat.add (Nat.mul (Nat.div x1 x2) x2) (Nat.modulo x1 x2))) = (Nat.add (Nat.mul (Nat.div (Nat.add x0 x1) x2) x2) (Nat.modulo (Nat.add x0 x1) x2))) -> ((Nat.modulo (Nat.add x0 x1) x2) = (Nat.add (Nat.modulo x0 x2) (Nat.modulo x1 x2))) = ((Nat.div (Nat.add x0 x1) x2) = (Nat.add (Nat.div x0 x2) (Nat.div x1 x2))).
Definition term74 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Nat.mul x0 y0) = (Nat.mul x1 y0)) = ((x0 = x1) \/ (y0 = (NUMERAL 0)))) x2.
Definition term26 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq nat (Nat.add (Nat.add x0 x1) (Nat.add x2 x3)).
Definition term114 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (~ (y2 = (NUMERAL 0))) -> ((Nat.modulo (Nat.add y0 y1) y2) = (Nat.add (Nat.modulo y0 y2) (Nat.modulo y1 y2))) = ((Nat.div (Nat.add y0 y1) y2) = (Nat.add (Nat.div y0 y2) (Nat.div y1 y2))).
Definition term113 (x0 : nat) := forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> ((Nat.modulo (Nat.add x0 y0) y1) = (Nat.add (Nat.modulo x0 y1) (Nat.modulo y0 y1))) = ((Nat.div (Nat.add x0 y0) y1) = (Nat.add (Nat.div x0 y1) (Nat.div y0 y1))).
Definition term92 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Nat.add x0 y0) = (Nat.add x0 y1)) = (y0 = y1).
Definition term77 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Nat.add x0 y1) = (Nat.add y0 y1)) = (x0 = y0).
Definition term71 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Nat.mul x0 y1) = (Nat.mul y0 y1)) = ((x0 = y0) \/ (y1 = (NUMERAL 0))).
Definition term28 := forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1).
Definition term16 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.add (Nat.mul y0 y2) (Nat.mul y1 y2)) = (Nat.mul (Nat.add y0 y1) y2).
Definition term15 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.mul (Nat.add y0 y1) y2) = (Nat.add (Nat.mul y0 y2) (Nat.mul y1 y2)).
Definition term12 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul x0 y1) (Nat.mul y0 y1)) = (Nat.mul (Nat.add x0 y0) y1).
Definition term11 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.mul (Nat.add x0 y0) y1) = (Nat.add (Nat.mul x0 y1) (Nat.mul y0 y1)).
Definition term106 (x0 : nat) (x1 : nat) (x2 : nat) := (((Nat.modulo (Nat.add x0 x1) x2) = (Nat.add (Nat.modulo x0 x2) (Nat.modulo x1 x2))) -> (Nat.div (Nat.add x0 x1) x2) = (Nat.add (Nat.div x0 x2) (Nat.div x1 x2))) /\ (((Nat.div (Nat.add x0 x1) x2) = (Nat.add (Nat.div x0 x2) (Nat.div x1 x2))) -> (Nat.modulo (Nat.add x0 x1) x2) = (Nat.add (Nat.modulo x0 x2) (Nat.modulo x1 x2))).
Definition term32 (x0 : nat) (x1 : nat) := (~ (x1 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1).
Definition term5 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.mul (Nat.add x0 x1) y0) = (Nat.add (Nat.mul x0 y0) (Nat.mul x1 y0)).
Definition term21 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.add (Nat.add x1 x0) x2) = (Nat.add x1 (Nat.add x0 x2))) /\ ((Nat.add x1 (Nat.add x0 x2)) = (Nat.add x0 (Nat.add x1 x2))).
Definition term109 (x0 : nat) (x1 : nat) (x2 : nat) := (x1 = (Nat.add (Nat.mul (Nat.div x1 x2) x2) (Nat.modulo x1 x2))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 x2) x2) (Nat.modulo x0 x2))) -> ((Nat.add x0 x1) = (Nat.add (Nat.mul (Nat.div (Nat.add x0 x1) x2) x2) (Nat.modulo (Nat.add x0 x1) x2))) -> ((Nat.modulo (Nat.add x0 x1) x2) = (Nat.add (Nat.modulo x0 x2) (Nat.modulo x1 x2))) = ((Nat.div (Nat.add x0 x1) x2) = (Nat.add (Nat.div x0 x2) (Nat.div x1 x2))).
Definition term62 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul (Nat.div x0 x2) x2) (Nat.mul (Nat.div x1 x2) x2).
Definition term2 (a0 : Type') (x0 : a0) (x1 : a0) := (fun y0 : a0 => (x0 = y0) = (y0 = x0)) x1.
Definition term86 (x0 : nat) (x1 : nat) (x2 : nat) := or ((Nat.add (Nat.div x0 x2) (Nat.div x1 x2)) = (Nat.div (Nat.add x0 x1) x2)).
Definition term3 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.add x0 x1) x2.
Definition term40 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (y0 = (Nat.add (Nat.mul (Nat.div y0 x0) x0) (Nat.modulo y0 x0))) /\ (Peano.lt (Nat.modulo y0 x0) x0)) (Nat.add x1 x2).
Definition term103 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.add (Nat.modulo x0 x2) (Nat.modulo x1 x2)) = (Nat.modulo (Nat.add x0 x1) x2)) -> (Nat.add (Nat.modulo x0 x2) (Nat.modulo x1 x2)) = (Nat.modulo (Nat.add x0 x1) x2).
Definition term4 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x0 x2) (Nat.mul x1 x2).
Definition term83 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul (Nat.div (Nat.add x0 x1) x2) x2) (Nat.add (Nat.modulo x0 x2) (Nat.modulo x1 x2)).
Definition term98 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul (Nat.add (Nat.div x0 x2) (Nat.div x1 x2)) x2) (Nat.modulo (Nat.add x0 x1) x2).
Definition term6 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.add (Nat.mul x0 y0) (Nat.mul x1 y0)) = (Nat.mul (Nat.add x0 x1) y0).
Definition term24 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.add (Nat.add x0 x1) (Nat.add x2 x3).
Definition term66 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul (Nat.add (Nat.div x0 x2) (Nat.div x1 x2)) x2) (Nat.add (Nat.modulo x0 x2) (Nat.modulo x1 x2)).
Definition term96 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.div (Nat.add x0 x1) x2).
Definition term85 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.add (Nat.div x0 x2) (Nat.div x1 x2)) = (Nat.div (Nat.add x0 x1) x2)) \/ (x2 = (NUMERAL 0)).
Definition term49 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((Nat.add x0 x1) = (Nat.add (Nat.mul (Nat.div (Nat.add x0 x1) x2) x2) (Nat.modulo (Nat.add x0 x1) x2))).
Definition term23 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add x0 (Nat.add x1 x2).
Definition term35 (x0 : nat) := forall y0 : nat, (y0 = (Nat.add (Nat.mul (Nat.div y0 x0) x0) (Nat.modulo y0 x0))) /\ (Peano.lt (Nat.modulo y0 x0) x0).
Definition term59 (x0 : nat) (x1 : nat) (x2 : nat) := @eq nat (Nat.add (Nat.add (Nat.mul (Nat.div x0 x2) x2) (Nat.mul (Nat.div x1 x2) x2)) (Nat.add (Nat.modulo x0 x2) (Nat.modulo x1 x2))).
Definition term48 (x0 : nat) (x1 : nat) (x2 : nat) := @eq nat (Nat.add (Nat.add (Nat.mul (Nat.div x0 x2) x2) (Nat.modulo x0 x2)) (Nat.add (Nat.mul (Nat.div x1 x2) x2) (Nat.modulo x1 x2))).
Definition term29 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) x0.
Definition term7 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.mul (Nat.add x0 x1) y0) = (Nat.add (Nat.mul x0 y0) (Nat.mul x1 y0)).
Definition term81 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> (x0 = (NUMERAL 0)) = False.
Definition term31 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0)) x1.
Definition term95 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Nat.add x0 x1) = (Nat.add x0 y0)) = (x1 = y0)) x2.
Definition term108 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = (Nat.add (Nat.mul (Nat.div x0 x2) x2) (Nat.modulo x0 x2))) -> ((Nat.add x0 x1) = (Nat.add (Nat.mul (Nat.div (Nat.add x0 x1) x2) x2) (Nat.modulo (Nat.add x0 x1) x2))) -> ((Nat.modulo (Nat.add x0 x1) x2) = (Nat.add (Nat.modulo x0 x2) (Nat.modulo x1 x2))) = ((Nat.div (Nat.add x0 x1) x2) = (Nat.add (Nat.div x0 x2) (Nat.div x1 x2))).
Definition term36 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> forall y0 : nat, (y0 = (Nat.add (Nat.mul (Nat.div y0 x0) x0) (Nat.modulo y0 x0))) /\ (Peano.lt (Nat.modulo y0 x0) x0).
Definition term65 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul (Nat.add (Nat.div x0 x2) (Nat.div x1 x2)) x2).
Definition term100 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.add (Nat.mul (Nat.add (Nat.div x0 x2) (Nat.div x1 x2)) x2) (Nat.add (Nat.modulo x0 x2) (Nat.modulo x1 x2))) = (Nat.add (Nat.mul (Nat.div (Nat.add x0 x1) x2) x2) (Nat.modulo (Nat.add x0 x1) x2))) -> (Nat.modulo (Nat.add x0 x1) x2) = (Nat.add (Nat.modulo x0 x2) (Nat.modulo x1 x2)).
Definition term89 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.add (Nat.mul (Nat.add (Nat.div x0 x2) (Nat.div x1 x2)) x2) (Nat.add (Nat.modulo x0 x2) (Nat.modulo x1 x2))) = (Nat.add (Nat.mul (Nat.div (Nat.add x0 x1) x2) x2) (Nat.modulo (Nat.add x0 x1) x2))) -> (Nat.div (Nat.add x0 x1) x2) = (Nat.add (Nat.div x0 x2) (Nat.div x1 x2)).
Definition term97 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.add (Nat.div x0 x2) (Nat.div x1 x2)).
Definition term51 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.modulo (Nat.add x0 x1) x2.
Definition term20 (a0 : Type') (x0 : a0) := (fun y0 : a0 => (y0 = y0) = True) x0.
Definition term27 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq nat (Nat.add x0 (Nat.add x1 (Nat.add x2 x3))).
Definition term30 (x0 : nat) := forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0).
Definition term45 (x0 : nat) (x1 : nat) := Nat.add (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)).
Definition term9 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Nat.mul (Nat.add x0 y0) y1) = (Nat.add (Nat.mul x0 y1) (Nat.mul y0 y1)).
Definition term14 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.add (Nat.mul y0 y2) (Nat.mul y1 y2)) = (Nat.mul (Nat.add y0 y1) y2).
Definition term13 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.mul (Nat.add y0 y1) y2) = (Nat.add (Nat.mul y0 y2) (Nat.mul y1 y2)).
