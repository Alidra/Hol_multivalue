Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term87 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1).
Definition term71 (x0 : nat) (x1 : nat) := Nat.modulo (Nat.mul x0 x1).
Definition term73 (x0 : nat) (x1 : nat) := Nat.modulo (Nat.mul x0 x1) (NUMERAL 0).
Definition term80 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x0 (Nat.modulo x1 x2)).
Definition term12 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.add (Nat.mul x0 x1) (Nat.mul x0 y0)) = (Nat.mul x0 (Nat.add x1 y0)).
Definition term61 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (exists y3 : nat, y0 = (Nat.add y1 (Nat.mul y3 y2))) -> (Nat.modulo y0 y2) = (Nat.modulo y1 y2)) x0.
Definition term44 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, (y0 = (Nat.add y1 (Nat.mul y3 y2))) -> (Nat.modulo y0 y2) = (Nat.modulo y1 y2)) x0.
Definition term40 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.mul (Nat.mul y0 y1) y2) = (Nat.mul y0 (Nat.mul y1 y2))) x0.
Definition term37 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y2)) = (Nat.mul y0 (Nat.add y1 y2))) x0.
Definition term3 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Nat.mul y0 y1) = (Nat.mul y0 y2)) = ((y0 = (NUMERAL 0)) \/ (y1 = y2))) x0.
Definition term42 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.mul (Nat.mul x0 x1) y0) = (Nat.mul x0 (Nat.mul x1 y0))) x2.
Definition term68 (x0 : nat) := Nat.modulo x0 (NUMERAL 0).
Definition term60 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, (y0 = (Nat.add y1 (Nat.mul y3 y2))) -> (Nat.modulo y0 y2) = (Nat.modulo y1 y2)) -> forall y0 : nat, forall y1 : nat, forall y2 : nat, (exists y3 : nat, y0 = (Nat.add y1 (Nat.mul y3 y2))) -> (Nat.modulo y0 y2) = (Nat.modulo y1 y2).
Definition term76 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.modulo (Nat.mul x0 x1) x2.
Definition term14 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.add (Nat.mul x0 x1) (Nat.mul x0 y0)) = (Nat.mul x0 (Nat.add x1 y0)).
Definition term98 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (Nat.div x1 x2).
Definition term97 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nat => (Nat.mul x0 x1) = (Nat.add (Nat.mul x0 (Nat.modulo x1 x2)) (Nat.mul y0 x2)).
Definition term50 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => (x0 = (Nat.add x1 (Nat.mul y0 x2))) -> (Nat.modulo x0 x2) = (Nat.modulo x1 x2)) x3.
Definition term54 (x0 : nat) (x1 : nat) (x2 : nat) := exists y0 : nat, x0 = (Nat.add x1 (Nat.mul y0 x2)).
Definition term74 (x0 : nat) (x1 : nat) (x2 : nat) := @eq nat (Nat.modulo (Nat.mul x0 (Nat.modulo x1 x2)) x2).
Definition term67 (x0 : nat) := (fun y0 : nat => (Nat.modulo y0 (NUMERAL 0)) = y0) x0.
Definition term92 (x0 : nat) (x1 : nat) := (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1).
Definition term39 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.add (Nat.mul x0 x1) (Nat.mul x0 y0)) = (Nat.mul x0 (Nat.add x1 y0))) x2.
Definition term86 (x0 : nat) (x1 : nat) := Nat.add (Nat.modulo x0 x1) (Nat.mul (Nat.div x0 x1) x1).
Definition term72 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.modulo (Nat.mul x0 (Nat.modulo x1 x2)) x2.
Definition term81 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x0 (Nat.modulo x1 x2)) (Nat.mul (Nat.mul x0 (Nat.div x1 x2)) x2).
Definition term27 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.mul x0 (Nat.mul x1 y0)) = (Nat.mul (Nat.mul x0 x1) y0).
Definition term8 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = (NUMERAL 0)) \/ (x1 = x2).
Definition term53 (x0 : nat) (x1 : nat) (x2 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, (y0 = (Nat.add y1 (Nat.mul y3 y2))) -> (Nat.modulo y0 y2) = (Nat.modulo y1 y2)) -> (Nat.modulo x0 x2) = (Nat.modulo x1 x2).
Definition term62 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (exists y2 : nat, x0 = (Nat.add y0 (Nat.mul y2 y1))) -> (Nat.modulo x0 y1) = (Nat.modulo y0 y1)) x1.
Definition term41 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul (Nat.mul x0 y0) y1) = (Nat.mul x0 (Nat.mul y0 y1))) x1.
Definition term38 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y1)) = (Nat.mul x0 (Nat.add y0 y1))) x1.
Definition term5 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.mul x0 y0) = (Nat.mul x0 y1)) = ((x0 = (NUMERAL 0)) \/ (y0 = y1))) x1.
Definition term66 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term29 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Nat.mul x0 (Nat.mul y0 y1)) = (Nat.mul (Nat.mul x0 y0) y1).
Definition term84 (x0 : nat) (x1 : nat) := Nat.mul (Nat.div x0 x1) x1.
Definition term10 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x1 x0) (Nat.mul x1 x2).
Definition term24 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.mul x0 x1) x2.
Definition term82 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x0 (Nat.modulo x1 x2)) (Nat.mul x0 (Nat.mul (Nat.div x1 x2) x2)).
Definition term101 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.mul y0 (Nat.modulo y2 y1)) y1) = (Nat.modulo (Nat.mul y0 y2) y1).
Definition term100 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.modulo (Nat.mul x0 (Nat.modulo y1 y0)) y0) = (Nat.modulo (Nat.mul x0 y1) y0).
Definition term59 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (exists y3 : nat, y0 = (Nat.add y1 (Nat.mul y3 y2))) -> (Nat.modulo y0 y2) = (Nat.modulo y1 y2).
Definition term58 (x0 : nat) := forall y0 : nat, forall y1 : nat, (exists y2 : nat, x0 = (Nat.add y0 (Nat.mul y2 y1))) -> (Nat.modulo x0 y1) = (Nat.modulo y0 y1).
Definition term47 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, (x0 = (Nat.add x1 (Nat.mul y1 y0))) -> (Nat.modulo x0 y0) = (Nat.modulo x1 y0).
Definition term45 (x0 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, (x0 = (Nat.add y0 (Nat.mul y2 y1))) -> (Nat.modulo x0 y1) = (Nat.modulo y0 y1).
Definition term43 := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, (y0 = (Nat.add y1 (Nat.mul y3 y2))) -> (Nat.modulo y0 y2) = (Nat.modulo y1 y2).
Definition term36 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.mul (Nat.mul y0 y1) y2) = (Nat.mul y0 (Nat.mul y1 y2)).
Definition term35 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.mul y0 (Nat.mul y1 y2)) = (Nat.mul (Nat.mul y0 y1) y2).
Definition term32 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.mul (Nat.mul x0 y0) y1) = (Nat.mul x0 (Nat.mul y0 y1)).
Definition term31 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.mul x0 (Nat.mul y0 y1)) = (Nat.mul (Nat.mul x0 y0) y1).
Definition term22 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y2)) = (Nat.mul y0 (Nat.add y1 y2)).
Definition term21 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.mul y0 (Nat.add y1 y2)) = (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y2)).
Definition term18 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y1)) = (Nat.mul x0 (Nat.add y0 y1)).
Definition term17 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.mul x0 (Nat.add y0 y1)) = (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y1)).
Definition term4 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Nat.mul x0 y0) = (Nat.mul x0 y1)) = ((x0 = (NUMERAL 0)) \/ (y0 = y1)).
Definition term93 (x0 : nat) (x1 : nat) := (~ (x1 = (NUMERAL 0))) -> x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)).
Definition term69 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (Nat.modulo x1 x2).
Definition term65 (x0 : nat) := (x0 = (NUMERAL 0)) \/ (~ (x0 = (NUMERAL 0))).
Definition term48 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => forall y1 : nat, (x0 = (Nat.add x1 (Nat.mul y1 y0))) -> (Nat.modulo x0 y0) = (Nat.modulo x1 y0)) x2.
Definition term46 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (x0 = (Nat.add y0 (Nat.mul y2 y1))) -> (Nat.modulo x0 y1) = (Nat.modulo y0 y1)) x1.
Definition term78 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.mul x0 (Nat.div x1 x2)) x2.
Definition term91 (x0 : nat) (x1 : nat) := (~ (x1 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1).
Definition term13 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.mul x1 (Nat.add x0 y0)) = (Nat.add (Nat.mul x1 x0) (Nat.mul x1 y0)).
Definition term6 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Nat.mul x0 x1) = (Nat.mul x0 y0)) = ((x0 = (NUMERAL 0)) \/ (x1 = y0)).
Definition term1 (x0 : nat) := forall y0 : nat, (Nat.add x0 y0) = (Nat.add y0 x0).
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add x0 y0) = (Nat.add y0 x0)) x1.
Definition term96 (x0 : nat) (x1 : nat) (x2 : nat) := exists y0 : nat, (Nat.mul x0 x1) = (Nat.add (Nat.mul x0 (Nat.modulo x1 x2)) (Nat.mul y0 x2)).
Definition term77 (x0 : nat) (x1 : nat) (x2 : nat) := (exists y0 : nat, (Nat.mul x0 x1) = (Nat.add (Nat.mul x0 (Nat.modulo x1 x2)) (Nat.mul y0 x2))) -> (Nat.modulo (Nat.mul x0 x1) x2) = (Nat.modulo (Nat.mul x0 (Nat.modulo x1 x2)) x2).
Definition term26 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.mul (Nat.mul x0 x1) y0) = (Nat.mul x0 (Nat.mul x1 y0)).
Definition term57 (x0 : nat) (x1 : nat) := forall y0 : nat, (exists y1 : nat, x0 = (Nat.add x1 (Nat.mul y1 y0))) -> (Nat.modulo x0 y0) = (Nat.modulo x1 y0).
Definition term70 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.modulo (Nat.mul x0 (Nat.modulo x1 x2)).
Definition term95 (x0 : nat) (x1 : nat) := (~ (x1 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) = True.
Definition term88 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) x0.
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) x0.
Definition term11 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.mul x1 (Nat.add x0 y0)) = (Nat.add (Nat.mul x1 x0) (Nat.mul x1 y0)).
Definition term49 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, (x0 = (Nat.add x1 (Nat.mul y0 x2))) -> (Nat.modulo x0 x2) = (Nat.modulo x1 x2).
Definition term23 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (Nat.mul x1 x2).
Definition term51 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x1 = (Nat.add x2 (Nat.mul x0 x3))) -> (Nat.modulo x1 x3) = (Nat.modulo x2 x3).
Definition term79 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (Nat.mul (Nat.div x1 x2) x2).
Definition term85 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = (NUMERAL 0)) \/ (x1 = (Nat.add (Nat.modulo x1 x2) (Nat.mul (Nat.div x1 x2) x2))).
Definition term7 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Nat.mul x0 x1) = (Nat.mul x0 y0)) = ((x0 = (NUMERAL 0)) \/ (x1 = y0))) x2.
Definition term94 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> (x0 = (NUMERAL 0)) = False.
Definition term90 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0)) x1.
Definition term75 (x0 : nat) (x1 : nat) := @eq nat (Nat.mul x0 x1).
Definition term9 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (Nat.add x1 x2).
Definition term28 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.mul (Nat.mul x0 x1) y0) = (Nat.mul x0 (Nat.mul x1 y0)).
Definition term63 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (exists y1 : nat, x0 = (Nat.add x1 (Nat.mul y1 y0))) -> (Nat.modulo x0 y0) = (Nat.modulo x1 y0)) x2.
Definition term89 (x0 : nat) := forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0).
Definition term25 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.mul x0 (Nat.mul x1 y0)) = (Nat.mul (Nat.mul x0 x1) y0).
Definition term99 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.modulo (Nat.mul x0 (Nat.modulo y0 x1)) x1) = (Nat.modulo (Nat.mul x0 y0) x1).
Definition term83 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (Nat.add (Nat.modulo x1 x2) (Nat.mul (Nat.div x1 x2) x2)).
Definition term55 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nat => x0 = (Nat.add x1 (Nat.mul y0 x2)).
Definition term64 (x0 : nat) := (fun y0 : Prop => y0 \/ (~ y0)) (x0 = (NUMERAL 0)).
Definition term30 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Nat.mul (Nat.mul x0 y0) y1) = (Nat.mul x0 (Nat.mul y0 y1)).
Definition term16 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y1)) = (Nat.mul x0 (Nat.add y0 y1)).
Definition term15 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Nat.mul x0 (Nat.add y0 y1)) = (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y1)).
Definition term56 (x0 : nat) (x1 : nat) (x2 : nat) := (exists y0 : nat, x0 = (Nat.add x1 (Nat.mul y0 x2))) -> (Nat.modulo x0 x2) = (Nat.modulo x1 x2).
Definition term34 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.mul (Nat.mul y0 y1) y2) = (Nat.mul y0 (Nat.mul y1 y2)).
Definition term33 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.mul y0 (Nat.mul y1 y2)) = (Nat.mul (Nat.mul y0 y1) y2).
Definition term20 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y2)) = (Nat.mul y0 (Nat.add y1 y2)).
Definition term19 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.mul y0 (Nat.add y1 y2)) = (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y2)).
Definition term52 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add x0 (Nat.mul x1 x2).
