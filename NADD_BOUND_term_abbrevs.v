Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term18 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.mul x1 (Nat.add x0 y0)) = (Nat.add (Nat.mul x1 x0) (Nat.mul x1 y0))) x2.
Definition term70 (x0 : nadd) (x1 : nat) (x2 : nat) := imp (Peano.le (dest_nadd x0 x1) (Nat.add (Nat.mul x1 (dest_nadd x0 (NUMERAL (BIT1 0)))) (Nat.add (Nat.mul x2 x1) x2))).
Definition term99 (x0 : nadd) := fun y0 : nat => exists y1 : nat, forall y2 : nat, Peano.le (dest_nadd x0 y2) (Nat.add (Nat.mul y0 y2) y1).
Definition term50 (x0 : nadd) (x1 : nat) (x2 : nat) := and (Peano.le (Nat.mul x2 (dest_nadd x0 (NUMERAL (BIT1 0)))) (Nat.add (Nat.mul (NUMERAL (BIT1 0)) (dest_nadd x0 x2)) (Nat.mul x1 (Nat.add x2 (NUMERAL (BIT1 0)))))).
Definition term96 (x0 : nat) (x1 : nadd) := exists y0 : nat, forall y1 : nat, Peano.le (dest_nadd x1 y1) (Nat.add (Nat.mul (Nat.add x0 (dest_nadd x1 (NUMERAL (BIT1 0)))) y1) y0).
Definition term32 (x0 : nadd) := exists y0 : nat, forall y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (Nat.mul y1 (dest_nadd x0 y2)) (Nat.mul y2 (dest_nadd x0 y1)))) (Nat.mul y0 (Nat.add y1 y2)).
Definition term62 (x0 : nadd) (x1 : nat) (x2 : nat) := ((Peano.le (Nat.mul x1 (dest_nadd x0 (NUMERAL (BIT1 0)))) (Nat.add (dest_nadd x0 x1) (Nat.mul x2 (Nat.add x1 (NUMERAL (BIT1 0)))))) /\ (Peano.le (dest_nadd x0 x1) (Nat.add (Nat.mul x1 (dest_nadd x0 (NUMERAL (BIT1 0)))) (Nat.mul x2 (Nat.add x1 (NUMERAL (BIT1 0))))))) -> Peano.le (dest_nadd x0 x1) (Nat.add (Nat.mul (Nat.add x2 (dest_nadd x0 (NUMERAL (BIT1 0)))) x1) x2).
Definition term60 (x0 : nadd) (x1 : nat) (x2 : nat) := Peano.le (dest_nadd x0 x1) (Nat.add (Nat.mul (Nat.add x2 (dest_nadd x0 (NUMERAL (BIT1 0)))) x1) x2).
Definition term2 := (forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))))).
Definition term69 (x0 : nadd) (x1 : nat) (x2 : nat) := imp (Peano.le (dest_nadd x0 x2) (Nat.add (Nat.mul x2 (dest_nadd x0 (NUMERAL (BIT1 0)))) (Nat.mul x1 (Nat.add x2 (NUMERAL (BIT1 0)))))).
Definition term24 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le (dist (@pair nat nat y0 y1)) y2) = ((Peano.le y0 (Nat.add y1 y2)) /\ (Peano.le y1 (Nat.add y0 y2)))) x0.
Definition term14 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.mul y0 (Nat.add y1 y2)) = (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y2))) x0.
Definition term7 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.mul (Nat.add y0 y1) y2) = (Nat.add (Nat.mul y0 y2) (Nat.mul y1 y2))) x0.
Definition term47 (x0 : nat) (x1 : nadd) := Peano.le (Nat.mul x0 (dest_nadd x1 (NUMERAL (BIT1 0)))).
Definition term68 (x0 : nadd) (x1 : nat) (x2 : nat) := Peano.le (dest_nadd x0 x1) (Nat.add (Nat.mul x1 (dest_nadd x0 (NUMERAL (BIT1 0)))) (Nat.add (Nat.mul x2 x1) x2)).
Definition term66 (x0 : nat) (x1 : nadd) := Nat.add (Nat.mul x0 (dest_nadd x1 (NUMERAL (BIT1 0)))).
Definition term100 (x0 : nat) (x1 : nadd) := Nat.add x0 (dest_nadd x1 (NUMERAL (BIT1 0))).
Definition term54 (x0 : nadd) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x2 (dest_nadd x0 (NUMERAL (BIT1 0)))) (Nat.mul x1 (Nat.add x2 (NUMERAL (BIT1 0)))).
Definition term64 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x0 x1).
Definition term85 (x0 : nat) (x1 : nat) (x2 : nadd) := Nat.add (Nat.mul x0 x1) (Nat.add x0 (Nat.mul x1 (dest_nadd x2 (NUMERAL (BIT1 0))))).
Definition term39 (x0 : nadd) (x1 : nat) (x2 : nat) := (Peano.le (Nat.mul x2 (dest_nadd x0 (NUMERAL (BIT1 0)))) (Nat.add (Nat.mul (NUMERAL (BIT1 0)) (dest_nadd x0 x2)) (Nat.mul x1 (Nat.add x2 (NUMERAL (BIT1 0)))))) /\ (Peano.le (Nat.mul (NUMERAL (BIT1 0)) (dest_nadd x0 x2)) (Nat.add (Nat.mul x2 (dest_nadd x0 (NUMERAL (BIT1 0)))) (Nat.mul x1 (Nat.add x2 (NUMERAL (BIT1 0)))))).
Definition term61 (x0 : nadd) (x1 : nat) (x2 : nat) := (Peano.le (dist (@pair nat nat (Nat.mul x1 (dest_nadd x0 (NUMERAL (BIT1 0)))) (Nat.mul (NUMERAL (BIT1 0)) (dest_nadd x0 x1)))) (Nat.mul x2 (Nat.add x1 (NUMERAL (BIT1 0))))) -> Peano.le (dest_nadd x0 x1) (Nat.add (Nat.mul (Nat.add x2 (dest_nadd x0 (NUMERAL (BIT1 0)))) x1) x2).
Definition term41 (x0 : nat) (x1 : nadd) := Nat.mul x0 (dest_nadd x1 (NUMERAL (BIT1 0))).
Definition term84 (x0 : nat) (x1 : nat) (x2 : nadd) := Nat.add x0 (Nat.mul x1 (dest_nadd x2 (NUMERAL (BIT1 0)))).
Definition term65 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x1 x0) x1.
Definition term94 (x0 : nat) (x1 : nat) (x2 : nadd) := (Peano.le (dest_nadd x2 x1) (Nat.add x0 (Nat.add (Nat.mul x0 x1) (Nat.mul x1 (dest_nadd x2 (NUMERAL (BIT1 0))))))) -> Peano.le (dest_nadd x2 x1) (Nat.add x0 (Nat.add (Nat.mul x0 x1) (Nat.mul x1 (dest_nadd x2 (NUMERAL (BIT1 0)))))).
Definition term28 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.le (dist (@pair nat nat x1 x0)) y0) = ((Peano.le x1 (Nat.add x0 y0)) /\ (Peano.le x0 (Nat.add x1 y0)))) x2.
Definition term5 (x0 : nat) := (fun y0 : nat => (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) x0.
Definition term89 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.add x0 x1) x2.
Definition term93 (x0 : nat) (x1 : nadd) (x2 : nat) := Nat.add x0 (Nat.mul (dest_nadd x1 (NUMERAL (BIT1 0))) x2).
Definition term71 (x0 : nat) (x1 : nadd) (x2 : nat) := Nat.mul (Nat.add x0 (dest_nadd x1 (NUMERAL (BIT1 0)))) x2.
Definition term43 (x0 : nadd) (x1 : nat) := Nat.add (Nat.mul (NUMERAL (BIT1 0)) (dest_nadd x0 x1)).
Definition term26 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (dist (@pair nat nat x0 y0)) y1) = ((Peano.le x0 (Nat.add y0 y1)) /\ (Peano.le y0 (Nat.add x0 y1)))) x1.
Definition term16 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul x0 (Nat.add y0 y1)) = (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y1))) x1.
Definition term9 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul (Nat.add x0 y0) y1) = (Nat.add (Nat.mul x0 y1) (Nat.mul y0 y1))) x1.
Definition term97 (x0 : nat) (x1 : nadd) := fun y0 : nat => forall y1 : nat, Peano.le (dest_nadd x1 y1) (Nat.add (Nat.mul (Nat.add x0 (dest_nadd x1 (NUMERAL (BIT1 0)))) y1) y0).
Definition term88 (x0 : nat) (x1 : nat) (x2 : nadd) := imp (Peano.le (dest_nadd x2 x1) (Nat.add x0 (Nat.add (Nat.mul x0 x1) (Nat.mul x1 (dest_nadd x2 (NUMERAL (BIT1 0))))))).
Definition term27 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le (dist (@pair nat nat x1 x0)) y0) = ((Peano.le x1 (Nat.add x0 y0)) /\ (Peano.le x0 (Nat.add x1 y0))).
Definition term4 := forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0.
Definition term51 (x0 : nadd) (x1 : nat) (x2 : nat) := and (Peano.le (Nat.mul x2 (dest_nadd x0 (NUMERAL (BIT1 0)))) (Nat.add (dest_nadd x0 x2) (Nat.mul x1 (Nat.add x2 (NUMERAL (BIT1 0)))))).
Definition term90 (x0 : nadd) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x2 x1) (Nat.add (Nat.mul (dest_nadd x0 (NUMERAL (BIT1 0))) x1) x2).
Definition term20 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x1 x0) (Nat.mul x1 x2).
Definition term55 (x0 : nadd) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul (NUMERAL (BIT1 0)) (dest_nadd x0 x2)) (Nat.add (Nat.mul x2 (dest_nadd x0 (NUMERAL (BIT1 0)))) (Nat.mul x1 (Nat.add x2 (NUMERAL (BIT1 0))))).
Definition term52 (x0 : nadd) (x1 : nat) := Peano.le (Nat.mul (NUMERAL (BIT1 0)) (dest_nadd x0 x1)).
Definition term35 (x0 : nadd) (x1 : nat) (x2 : nat) := forall y0 : nat, Peano.le (dist (@pair nat nat (Nat.mul x2 (dest_nadd x0 y0)) (Nat.mul y0 (dest_nadd x0 x2)))) (Nat.mul x1 (Nat.add x2 y0)).
Definition term33 (x0 : nadd) (x1 : nat) := forall y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (Nat.mul y0 (dest_nadd x0 y1)) (Nat.mul y1 (dest_nadd x0 y0)))) (Nat.mul x1 (Nat.add y0 y1)).
Definition term25 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le (dist (@pair nat nat x0 y0)) y1) = ((Peano.le x0 (Nat.add y0 y1)) /\ (Peano.le y0 (Nat.add x0 y1))).
Definition term15 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.mul x0 (Nat.add y0 y1)) = (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y1)).
Definition term8 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.mul (Nat.add x0 y0) y1) = (Nat.add (Nat.mul x0 y1) (Nat.mul y0 y1)).
Definition term56 (x0 : nadd) (x1 : nat) (x2 : nat) := Peano.le (dest_nadd x0 x2) (Nat.add (Nat.mul x2 (dest_nadd x0 (NUMERAL (BIT1 0)))) (Nat.mul x1 (Nat.add x2 (NUMERAL (BIT1 0))))).
Definition term87 (x0 : nat) (x1 : nat) (x2 : nadd) := Peano.le (dest_nadd x2 x1) (Nat.add x0 (Nat.add (Nat.mul x0 x1) (Nat.mul x1 (dest_nadd x2 (NUMERAL (BIT1 0)))))).
Definition term34 (x0 : nadd) (x1 : nat) (x2 : nat) := (fun y0 : nat => forall y1 : nat, Peano.le (dist (@pair nat nat (Nat.mul y0 (dest_nadd x0 y1)) (Nat.mul y1 (dest_nadd x0 y0)))) (Nat.mul x1 (Nat.add y0 y1))) x2.
Definition term53 (x0 : nadd) (x1 : nat) := Peano.le (dest_nadd x0 x1).
Definition term11 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.mul (Nat.add x0 x1) y0) = (Nat.add (Nat.mul x0 y0) (Nat.mul x1 y0))) x2.
Definition term0 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.add (Nat.add x1 x0) x2) = (Nat.add x1 (Nat.add x0 x2))) /\ ((Nat.add x1 (Nat.add x0 x2)) = (Nat.add x0 (Nat.add x1 x2))).
Definition term75 (x0 : nat) (x1 : nadd) (x2 : nat) := Nat.add (Nat.add (Nat.mul x0 x2) (Nat.mul (dest_nadd x1 (NUMERAL (BIT1 0))) x2)).
Definition term40 (x0 : nadd) (x1 : nat) := Nat.mul (NUMERAL (BIT1 0)) (dest_nadd x0 x1).
Definition term21 := forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0.
Definition term22 (x0 : nat) := (fun y0 : nat => (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) x0.
Definition term12 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.add x0 x1) x2.
Definition term46 (x0 : nadd) (x1 : nat) (x2 : nat) := Nat.add (dest_nadd x0 x2) (Nat.mul x1 (Nat.add x2 (NUMERAL (BIT1 0)))).
Definition term13 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x0 x2) (Nat.mul x1 x2).
Definition term17 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.mul x1 (Nat.add x0 y0)) = (Nat.add (Nat.mul x1 x0) (Nat.mul x1 y0)).
Definition term58 (x0 : nadd) (x1 : nat) (x2 : nat) := imp (Peano.le (dist (@pair nat nat (Nat.mul x2 (dest_nadd x0 (NUMERAL (BIT1 0)))) (Nat.mul (NUMERAL (BIT1 0)) (dest_nadd x0 x2)))) (Nat.mul x1 (Nat.add x2 (NUMERAL (BIT1 0))))).
Definition term83 (x0 : nat) (x1 : nadd) (x2 : nat) := Nat.add (Nat.mul x0 (dest_nadd x1 (NUMERAL (BIT1 0)))) x2.
Definition term86 (x0 : nat) (x1 : nat) (x2 : nadd) := Nat.add x0 (Nat.add (Nat.mul x0 x1) (Nat.mul x1 (dest_nadd x2 (NUMERAL (BIT1 0))))).
Definition term3 := (forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))).
Definition term63 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x1 x0) (Nat.mul x1 (NUMERAL (BIT1 0))).
Definition term102 := forall y0 : nadd, exists y1 : nat, exists y2 : nat, forall y3 : nat, Peano.le (dest_nadd y0 y3) (Nat.add (Nat.mul y1 y3) y2).
Definition term81 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add x0 (Nat.add x1 x2).
Definition term57 (x0 : nadd) (x1 : nat) (x2 : nat) := (Peano.le (Nat.mul x2 (dest_nadd x0 (NUMERAL (BIT1 0)))) (Nat.add (dest_nadd x0 x2) (Nat.mul x1 (Nat.add x2 (NUMERAL (BIT1 0)))))) /\ (Peano.le (dest_nadd x0 x2) (Nat.add (Nat.mul x2 (dest_nadd x0 (NUMERAL (BIT1 0)))) (Nat.mul x1 (Nat.add x2 (NUMERAL (BIT1 0)))))).
Definition term49 (x0 : nadd) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul x2 (dest_nadd x0 (NUMERAL (BIT1 0)))) (Nat.add (dest_nadd x0 x2) (Nat.mul x1 (Nat.add x2 (NUMERAL (BIT1 0))))).
Definition term6 (x0 : nat) := Nat.mul x0 (NUMERAL (BIT1 0)).
Definition term72 (x0 : nat) (x1 : nadd) (x2 : nat) := Nat.add (Nat.mul x0 x2) (Nat.mul (dest_nadd x1 (NUMERAL (BIT1 0))) x2).
Definition term48 (x0 : nadd) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul x2 (dest_nadd x0 (NUMERAL (BIT1 0)))) (Nat.add (Nat.mul (NUMERAL (BIT1 0)) (dest_nadd x0 x2)) (Nat.mul x1 (Nat.add x2 (NUMERAL (BIT1 0))))).
Definition term80 (x0 : nadd) (x1 : nat) (x2 : nat) := (Peano.le (dest_nadd x0 x1) (Nat.add (Nat.mul x1 (dest_nadd x0 (NUMERAL (BIT1 0)))) (Nat.add (Nat.mul x2 x1) x2))) -> Peano.le (dest_nadd x0 x1) (Nat.add (Nat.add (Nat.mul x2 x1) (Nat.mul (dest_nadd x0 (NUMERAL (BIT1 0))) x1)) x2).
Definition term10 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.mul (Nat.add x0 x1) y0) = (Nat.add (Nat.mul x0 y0) (Nat.mul x1 y0)).
Definition term79 (x0 : nadd) (x1 : nat) (x2 : nat) := (Peano.le (dest_nadd x0 x1) (Nat.add (Nat.mul x1 (dest_nadd x0 (NUMERAL (BIT1 0)))) (Nat.mul x2 (Nat.add x1 (NUMERAL (BIT1 0)))))) -> Peano.le (dest_nadd x0 x1) (Nat.add (Nat.mul (Nat.add x2 (dest_nadd x0 (NUMERAL (BIT1 0)))) x1) x2).
Definition term31 (x0 : nadd) := (fun y0 : nadd => exists y1 : nat, forall y2 : nat, forall y3 : nat, Peano.le (dist (@pair nat nat (Nat.mul y2 (dest_nadd y0 y3)) (Nat.mul y3 (dest_nadd y0 y2)))) (Nat.mul y1 (Nat.add y2 y3))) x0.
Definition term45 (x0 : nadd) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul (NUMERAL (BIT1 0)) (dest_nadd x0 x2)) (Nat.mul x1 (Nat.add x2 (NUMERAL (BIT1 0)))).
Definition term91 (x0 : nadd) (x1 : nat) := Nat.mul (dest_nadd x0 (NUMERAL (BIT1 0))) x1.
Definition term19 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (Nat.add x1 x2).
Definition term74 (x0 : nat) (x1 : nadd) (x2 : nat) := Nat.add (Nat.mul (Nat.add x0 (dest_nadd x1 (NUMERAL (BIT1 0)))) x2).
Definition term98 (x0 : nadd) := exists y0 : nat, exists y1 : nat, forall y2 : nat, Peano.le (dest_nadd x0 y2) (Nat.add (Nat.mul y0 y2) y1).
Definition term29 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (dist (@pair nat nat x0 x1)) x2.
Definition term78 (x0 : nadd) (x1 : nat) (x2 : nat) := Peano.le (dest_nadd x0 x1) (Nat.add (Nat.add (Nat.mul x2 x1) (Nat.mul (dest_nadd x0 (NUMERAL (BIT1 0))) x1)) x2).
Definition term44 (x0 : nadd) (x1 : nat) := Nat.add (dest_nadd x0 x1).
Definition term77 (x0 : nadd) (x1 : nat) (x2 : nat) := Nat.add (Nat.add (Nat.mul x2 x1) (Nat.mul (dest_nadd x0 (NUMERAL (BIT1 0))) x1)) x2.
Definition term67 (x0 : nadd) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x1 (dest_nadd x0 (NUMERAL (BIT1 0)))) (Nat.add (Nat.mul x2 x1) x2).
Definition term73 (x0 : nadd) := dest_nadd x0 (NUMERAL (BIT1 0)).
Definition term82 (x0 : nat) (x1 : nadd) (x2 : nat) := Nat.add (Nat.mul x2 x0) (Nat.add (Nat.mul x0 (dest_nadd x1 (NUMERAL (BIT1 0)))) x2).
Definition term30 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x1 (Nat.add x0 x2)) /\ (Peano.le x0 (Nat.add x1 x2)).
Definition term38 (x0 : nadd) (x1 : nat) (x2 : nat) := Peano.le (dist (@pair nat nat (Nat.mul x2 (dest_nadd x0 (NUMERAL (BIT1 0)))) (Nat.mul (NUMERAL (BIT1 0)) (dest_nadd x0 x2)))) (Nat.mul x1 (Nat.add x2 (NUMERAL (BIT1 0)))).
Definition term1 := (forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))).
Definition term95 (x0 : nadd) (x1 : nat) := forall y0 : nat, Peano.le (dest_nadd x0 y0) (Nat.add (Nat.mul (Nat.add x1 (dest_nadd x0 (NUMERAL (BIT1 0)))) y0) x1).
Definition term92 (x0 : nadd) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul (dest_nadd x0 (NUMERAL (BIT1 0))) x1) x2.
Definition term76 (x0 : nadd) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul (Nat.add x2 (dest_nadd x0 (NUMERAL (BIT1 0)))) x1) x2.
Definition term42 (x0 : nat) (x1 : nat) := Nat.mul x0 (Nat.add x1 (NUMERAL (BIT1 0))).
Definition term37 := NUMERAL (BIT1 0).
Definition term23 (x0 : nat) := Nat.mul (NUMERAL (BIT1 0)) x0.
Definition term36 (x0 : nadd) (x1 : nat) (x2 : nat) := (fun y0 : nat => Peano.le (dist (@pair nat nat (Nat.mul x2 (dest_nadd x0 y0)) (Nat.mul y0 (dest_nadd x0 x2)))) (Nat.mul x1 (Nat.add x2 y0))) (NUMERAL (BIT1 0)).
Definition term101 (x0 : nadd) := fun y0 : nat => forall y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (Nat.mul y1 (dest_nadd x0 y2)) (Nat.mul y2 (dest_nadd x0 y1)))) (Nat.mul y0 (Nat.add y1 y2)).
Definition term59 (x0 : nadd) (x1 : nat) (x2 : nat) := imp ((Peano.le (Nat.mul x2 (dest_nadd x0 (NUMERAL (BIT1 0)))) (Nat.add (dest_nadd x0 x2) (Nat.mul x1 (Nat.add x2 (NUMERAL (BIT1 0)))))) /\ (Peano.le (dest_nadd x0 x2) (Nat.add (Nat.mul x2 (dest_nadd x0 (NUMERAL (BIT1 0)))) (Nat.mul x1 (Nat.add x2 (NUMERAL (BIT1 0))))))).
