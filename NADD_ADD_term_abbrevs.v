Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term65 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.mul x1 (Nat.add x0 y0)) = (Nat.add (Nat.mul x1 x0) (Nat.mul x1 y0))) x2.
Definition term74 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, (nadd_add y0 y1) = (mk_nadd (fun y2 : nat => Nat.add (dest_nadd y0 y2) (dest_nadd y1 y2)))) x0.
Definition term102 (x0 : nat) (x1 : nadd) (x2 : nadd) (x3 : nat) := Peano.le (dist (@pair nat nat (Nat.mul x3 (Nat.add (dest_nadd x1 x0) (dest_nadd x2 x0))) (Nat.mul x0 (Nat.add (dest_nadd x1 x3) (dest_nadd x2 x3))))).
Definition term98 (x0 : nat) (x1 : nadd) (x2 : nadd) (x3 : nat) := @pair nat nat (Nat.mul x3 (Nat.add (dest_nadd x1 x0) (dest_nadd x2 x0))) (Nat.mul x0 (Nat.add (dest_nadd x1 x3) (dest_nadd x2 x3))).
Definition term35 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x2) -> Peano.le x1 x2.
Definition term115 (x0 : nadd) (x1 : nadd) := exists y0 : nat, forall y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (Nat.mul y1 (Nat.add (dest_nadd x0 y2) (dest_nadd x1 y2))) (Nat.mul y2 (Nat.add (dest_nadd x0 y1) (dest_nadd x1 y1))))) (Nat.mul y0 (Nat.add y1 y2)).
Definition term84 (x0 : nadd) (x1 : nadd) := exists y0 : nat, forall y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (Nat.mul y1 ((fun y3 : nat => Nat.add (dest_nadd x0 y3) (dest_nadd x1 y3)) y2)) (Nat.mul y2 ((fun y3 : nat => Nat.add (dest_nadd x0 y3) (dest_nadd x1 y3)) y1)))) (Nat.mul y0 (Nat.add y1 y2)).
Definition term73 (x0 : nat -> nat) := exists y0 : nat, forall y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (Nat.mul y1 (x0 y2)) (Nat.mul y2 (x0 y1)))) (Nat.mul y0 (Nat.add y1 y2)).
Definition term69 (x0 : nadd) := exists y0 : nat, forall y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (Nat.mul y1 (dest_nadd x0 y2)) (Nat.mul y2 (dest_nadd x0 y1)))) (Nat.mul y0 (Nat.add y1 y2)).
Definition term61 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.mul y0 (Nat.add y1 y2)) = (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y2))) x0.
Definition term51 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, forall y4 : nat, (Peano.le (Nat.add (dist (@pair nat nat y0 y2)) (dist (@pair nat nat y1 y3))) y4) -> Peano.le (dist (@pair nat nat (Nat.add y0 y1) (Nat.add y2 y3))) y4) x0.
Definition term29 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le y0 y1) -> (Peano.le y1 y2) -> Peano.le y0 y2) x0.
Definition term20 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, Peano.le (dist (@pair nat nat (Nat.add y0 y1) (Nat.add y2 y3))) (Nat.add (dist (@pair nat nat y0 y2)) (dist (@pair nat nat y1 y3)))) x0.
Definition term13 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.mul (Nat.add y0 y1) y2) = (Nat.add (Nat.mul y0 y2) (Nat.mul y1 y2))) x0.
Definition term1 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.add y0 y1) (Nat.add y2 y3)) x0.
Definition term7 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => ((Peano.le x0 x2) /\ (Peano.le x1 y0)) -> Peano.le (Nat.add x0 x1) (Nat.add x2 y0)) x3.
Definition term104 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat) := Peano.le (dist (@pair nat nat (Nat.mul x3 (Nat.add (dest_nadd x0 x4) (dest_nadd x1 x4))) (Nat.mul x4 (Nat.add (dest_nadd x0 x3) (dest_nadd x1 x3))))) (Nat.mul x2 (Nat.add x3 x4)).
Definition term103 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat) := Peano.le (dist (@pair nat nat (Nat.mul x3 ((fun y0 : nat => Nat.add (dest_nadd x0 y0) (dest_nadd x1 y0)) x4)) (Nat.mul x4 ((fun y0 : nat => Nat.add (dest_nadd x0 y0) (dest_nadd x1 y0)) x3)))) (Nat.mul x2 (Nat.add x3 x4)).
Definition term118 (x0 : nadd) (x1 : nat) (x2 : nadd) (x3 : nat) := @pair nat nat (Nat.add (Nat.mul x3 (dest_nadd x0 x1)) (Nat.mul x3 (dest_nadd x2 x1))) (Nat.add (Nat.mul x1 (dest_nadd x0 x3)) (Nat.mul x1 (dest_nadd x2 x3))).
Definition term60 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, forall y4 : nat, (Peano.le (Nat.add (dist (@pair nat nat y0 y2)) (dist (@pair nat nat y1 y3))) y4) -> Peano.le (dist (@pair nat nat (Nat.add y0 y1) (Nat.add y2 y3))) y4) -> forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, forall y4 : nat, (Peano.le (Nat.add (dist (@pair nat nat y0 y2)) (dist (@pair nat nat y1 y3))) y4) -> Peano.le (dist (@pair nat nat (Nat.add y0 y1) (Nat.add y2 y3))) y4.
Definition term40 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.le y0 y1) -> (Peano.le y1 y2) -> Peano.le y0 y2) -> forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> forall y2 : nat, (Peano.le y1 y2) -> Peano.le y0 y2.
Definition term12 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.add y0 y1) (Nat.add y2 y3)) -> forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.add y0 y1) (Nat.add y2 y3).
Definition term56 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := (Peano.le (Nat.add (dist (@pair nat nat x0 x2)) (dist (@pair nat nat x1 x3))) x4) -> Peano.le (dist (@pair nat nat (Nat.add x0 x1) (Nat.add x2 x3))) x4.
Definition term142 := forall y0 : nadd, forall y1 : nadd, (dest_nadd (nadd_add y0 y1)) = (fun y2 : nat => Nat.add (dest_nadd y0 y2) (dest_nadd y1 y2)).
Definition term89 (x0 : nadd) (x1 : nadd) (x2 : nat) := Nat.add (dest_nadd x0 x2) (dest_nadd x1 x2).
Definition term92 (x0 : nadd) (x1 : nadd) (x2 : nat) := @eq nat ((fun y0 : nat => Nat.add (dest_nadd x0 y0) (dest_nadd x1 y0)) x2).
Definition term79 (x0 : nadd) (x1 : nadd) := dest_nadd (mk_nadd (fun y0 : nat => Nat.add (dest_nadd x0 y0) (dest_nadd x1 y0))).
Definition term10 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (Nat.add x0 x1) (Nat.add x2 x3).
Definition term27 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (dist (@pair nat nat (Nat.add x0 x2) (Nat.add x1 x3))) (Nat.add (dist (@pair nat nat x0 x1)) (dist (@pair nat nat x2 x3))).
Definition term100 (x0 : nat) (x1 : nadd) (x2 : nadd) (x3 : nat) := dist (@pair nat nat (Nat.mul x3 (Nat.add (dest_nadd x1 x0) (dest_nadd x2 x0))) (Nat.mul x0 (Nat.add (dest_nadd x1 x3) (dest_nadd x2 x3)))).
Definition term127 (x0 : nadd) (x1 : nat) (x2 : nadd) (x3 : nat) := Peano.le (Nat.add (dist (@pair nat nat (Nat.mul x3 (dest_nadd x0 x1)) (Nat.mul x1 (dest_nadd x0 x3)))) (dist (@pair nat nat (Nat.mul x3 (dest_nadd x2 x1)) (Nat.mul x1 (dest_nadd x2 x3))))).
Definition term136 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := and (Peano.le (dist (@pair nat nat (Nat.mul x2 (dest_nadd x0 x3)) (Nat.mul x3 (dest_nadd x0 x2)))) (Nat.mul x1 (Nat.add x2 x3))).
Definition term38 (x0 : nat) := forall y0 : nat, (Peano.le x0 y0) -> forall y1 : nat, (Peano.le y0 y1) -> Peano.le x0 y1.
Definition term78 (x0 : nadd) (x1 : nadd) := dest_nadd (nadd_add x0 x1).
Definition term125 (x0 : nat) (x1 : nadd) (x2 : nat) := Nat.mul x0 (dest_nadd x1 x2).
Definition term130 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : nat) := ((Peano.le (dist (@pair nat nat (Nat.mul x4 (dest_nadd x0 x5)) (Nat.mul x5 (dest_nadd x0 x4)))) (Nat.mul x2 (Nat.add x4 x5))) /\ (Peano.le (dist (@pair nat nat (Nat.mul x4 (dest_nadd x1 x5)) (Nat.mul x5 (dest_nadd x1 x4)))) (Nat.mul x3 (Nat.add x4 x5)))) -> Peano.le (Nat.add (dist (@pair nat nat (Nat.mul x4 (dest_nadd x0 x5)) (Nat.mul x5 (dest_nadd x0 x4)))) (dist (@pair nat nat (Nat.mul x4 (dest_nadd x1 x5)) (Nat.mul x5 (dest_nadd x1 x4))))) (Nat.add (Nat.mul x2 (Nat.add x4 x5)) (Nat.mul x3 (Nat.add x4 x5))).
Definition term77 (x0 : nadd) (x1 : nadd) := mk_nadd (fun y0 : nat => Nat.add (dest_nadd x0 y0) (dest_nadd x1 y0)).
Definition term57 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := Peano.le (Nat.add (dist (@pair nat nat x0 x1)) (dist (@pair nat nat x2 x3))) x4.
Definition term71 (x0 : nat -> nat) := dest_nadd (mk_nadd x0).
Definition term88 (x0 : nadd) (x1 : nadd) (x2 : nat) := (fun y0 : nat => Nat.add (dest_nadd x0 y0) (dest_nadd x1 y0)) x2.
Definition term91 (x0 : nadd) (x1 : nadd) (x2 : nat) := @eq nat ((fun y0 : nat => (fun y1 : nat => Nat.add (dest_nadd x0 y1) (dest_nadd x1 y1)) y0) x2).
Definition term63 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul x0 (Nat.add y0 y1)) = (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y1))) x1.
Definition term31 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le x0 y0) -> (Peano.le y0 y1) -> Peano.le x0 y1) x1.
Definition term15 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul (Nat.add x0 y0) y1) = (Nat.add (Nat.mul x0 y1) (Nat.mul y0 y1))) x1.
Definition term120 (x0 : nadd) (x1 : nat) (x2 : nadd) (x3 : nat) := Peano.le (dist (@pair nat nat (Nat.add (Nat.mul x3 (dest_nadd x0 x1)) (Nat.mul x3 (dest_nadd x2 x1))) (Nat.add (Nat.mul x1 (dest_nadd x0 x3)) (Nat.mul x1 (dest_nadd x2 x3))))).
Definition term32 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le x1 x0) -> (Peano.le x0 y0) -> Peano.le x1 y0.
Definition term67 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x1 x0) (Nat.mul x1 x2).
Definition term76 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => (nadd_add x0 y0) = (mk_nadd (fun y1 : nat => Nat.add (dest_nadd x0 y1) (dest_nadd y0 y1)))) x1.
Definition term58 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := Peano.le (dist (@pair nat nat (Nat.add x0 x1) (Nat.add x2 x3))) x4.
Definition term121 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.mul (Nat.add x0 x1) (Nat.add x2 x3).
Definition term37 (x0 : nat) (x1 : nat) := (Peano.le x1 x0) -> forall y0 : nat, (Peano.le x0 y0) -> Peano.le x1 y0.
Definition term93 (x0 : nat) (x1 : nadd) (x2 : nadd) (x3 : nat) := Nat.mul x0 ((fun y0 : nat => Nat.add (dest_nadd x1 y0) (dest_nadd x2 y0)) x3).
Definition term133 (x0 : nadd) (x1 : nat) (x2 : nat) := forall y0 : nat, Peano.le (dist (@pair nat nat (Nat.mul x2 (dest_nadd x0 y0)) (Nat.mul y0 (dest_nadd x0 x2)))) (Nat.mul x1 (Nat.add x2 y0)).
Definition term108 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) := forall y0 : nat, Peano.le (dist (@pair nat nat (Nat.mul x3 (Nat.add (dest_nadd x0 y0) (dest_nadd x1 y0))) (Nat.mul y0 (Nat.add (dest_nadd x0 x3) (dest_nadd x1 x3))))) (Nat.mul x2 (Nat.add x3 y0)).
Definition term107 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) := forall y0 : nat, Peano.le (dist (@pair nat nat (Nat.mul x3 ((fun y1 : nat => Nat.add (dest_nadd x0 y1) (dest_nadd x1 y1)) y0)) (Nat.mul y0 ((fun y1 : nat => Nat.add (dest_nadd x0 y1) (dest_nadd x1 y1)) x3)))) (Nat.mul x2 (Nat.add x3 y0)).
Definition term85 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term54 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (Nat.add (dist (@pair nat nat x0 x2)) (dist (@pair nat nat x1 y0))) y1) -> Peano.le (dist (@pair nat nat (Nat.add x0 x1) (Nat.add x2 y0))) y1) x3.
Definition term116 (x0 : nadd) (x1 : nat) (x2 : nadd) (x3 : nat) := Nat.add (Nat.mul x1 (dest_nadd x0 x3)) (Nat.mul x1 (dest_nadd x2 x3)).
Definition term139 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) := forall y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (Nat.mul y0 (Nat.add (dest_nadd x0 y1) (dest_nadd x1 y1))) (Nat.mul y1 (Nat.add (dest_nadd x0 y0) (dest_nadd x1 y0))))) (Nat.mul (Nat.add x2 x3) (Nat.add y0 y1)).
Definition term112 (x0 : nadd) (x1 : nadd) (x2 : nat) := forall y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (Nat.mul y0 (Nat.add (dest_nadd x0 y1) (dest_nadd x1 y1))) (Nat.mul y1 (Nat.add (dest_nadd x0 y0) (dest_nadd x1 y0))))) (Nat.mul x2 (Nat.add y0 y1)).
Definition term111 (x0 : nadd) (x1 : nadd) (x2 : nat) := forall y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (Nat.mul y0 ((fun y2 : nat => Nat.add (dest_nadd x0 y2) (dest_nadd x1 y2)) y1)) (Nat.mul y1 ((fun y2 : nat => Nat.add (dest_nadd x0 y2) (dest_nadd x1 y2)) y0)))) (Nat.mul x2 (Nat.add y0 y1)).
Definition term70 (x0 : nadd) (x1 : nat) := forall y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (Nat.mul y0 (dest_nadd x0 y1)) (Nat.mul y1 (dest_nadd x0 y0)))) (Nat.mul x1 (Nat.add y0 y1)).
Definition term62 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.mul x0 (Nat.add y0 y1)) = (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y1)).
Definition term50 := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, forall y4 : nat, (Peano.le (Nat.add (dist (@pair nat nat y0 y2)) (dist (@pair nat nat y1 y3))) y4) -> Peano.le (dist (@pair nat nat (Nat.add y0 y1) (Nat.add y2 y3))) y4.
Definition term49 (x0 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, (Peano.le (Nat.add (dist (@pair nat nat x0 y1)) (dist (@pair nat nat y0 y2))) y3) -> Peano.le (dist (@pair nat nat (Nat.add x0 y0) (Nat.add y1 y2))) y3.
Definition term48 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.le (Nat.add (dist (@pair nat nat x0 y0)) (dist (@pair nat nat x1 y1))) y2) -> Peano.le (dist (@pair nat nat (Nat.add x0 x1) (Nat.add y0 y1))) y2.
Definition term47 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add (dist (@pair nat nat x0 x2)) (dist (@pair nat nat x1 y0))) y1) -> Peano.le (dist (@pair nat nat (Nat.add x0 x1) (Nat.add x2 y0))) y1.
Definition term39 := forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> forall y2 : nat, (Peano.le y1 y2) -> Peano.le y0 y2.
Definition term30 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le x0 y0) -> (Peano.le y0 y1) -> Peano.le x0 y1.
Definition term28 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.le y0 y1) -> (Peano.le y1 y2) -> Peano.le y0 y2.
Definition term23 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (Nat.add x0 x1) (Nat.add y0 y1))) (Nat.add (dist (@pair nat nat x0 y0)) (dist (@pair nat nat x1 y1))).
Definition term21 (x0 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (Nat.add x0 y0) (Nat.add y1 y2))) (Nat.add (dist (@pair nat nat x0 y1)) (dist (@pair nat nat y0 y2))).
Definition term14 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.mul (Nat.add x0 y0) y1) = (Nat.add (Nat.mul x0 y1) (Nat.mul y0 y1)).
Definition term4 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le x1 y1)) -> Peano.le (Nat.add x0 x1) (Nat.add y0 y1).
Definition term2 (x0 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le x0 y1) /\ (Peano.le y0 y2)) -> Peano.le (Nat.add x0 y0) (Nat.add y1 y2).
Definition term0 := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.add y0 y1) (Nat.add y2 y3).
Definition term59 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, forall y4 : nat, (Peano.le (Nat.add (dist (@pair nat nat y0 y2)) (dist (@pair nat nat y1 y3))) y4) -> Peano.le (dist (@pair nat nat (Nat.add y0 y1) (Nat.add y2 y3))) y4) -> Peano.le (dist (@pair nat nat (Nat.add x0 x1) (Nat.add x2 x3))) x4.
Definition term72 (x0 : nat -> nat) := (fun y0 : nat -> nat => (is_nadd y0) = (exists y1 : nat, forall y2 : nat, forall y3 : nat, Peano.le (dist (@pair nat nat (Nat.mul y2 (y0 y3)) (Nat.mul y3 (y0 y2)))) (Nat.mul y1 (Nat.add y2 y3)))) x0.
Definition term132 (x0 : nadd) (x1 : nat) (x2 : nat) := (fun y0 : nat => forall y1 : nat, Peano.le (dist (@pair nat nat (Nat.mul y0 (dest_nadd x0 y1)) (Nat.mul y1 (dest_nadd x0 y0)))) (Nat.mul x1 (Nat.add y0 y1))) x2.
Definition term24 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => forall y1 : nat, Peano.le (dist (@pair nat nat (Nat.add x0 x1) (Nat.add y0 y1))) (Nat.add (dist (@pair nat nat x0 y0)) (dist (@pair nat nat x1 y1)))) x2.
Definition term5 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le x1 y1)) -> Peano.le (Nat.add x0 x1) (Nat.add y0 y1)) x2.
Definition term52 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, (Peano.le (Nat.add (dist (@pair nat nat x0 y1)) (dist (@pair nat nat y0 y2))) y3) -> Peano.le (dist (@pair nat nat (Nat.add x0 y0) (Nat.add y1 y2))) y3) x1.
Definition term22 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (Nat.add x0 y0) (Nat.add y1 y2))) (Nat.add (dist (@pair nat nat x0 y1)) (dist (@pair nat nat y0 y2)))) x1.
Definition term3 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.le x0 y1) /\ (Peano.le y0 y2)) -> Peano.le (Nat.add x0 y0) (Nat.add y1 y2)) x1.
Definition term141 (x0 : nadd) := forall y0 : nadd, (dest_nadd (nadd_add x0 y0)) = (fun y1 : nat => Nat.add (dest_nadd x0 y1) (dest_nadd y0 y1)).
Definition term86 (x0 : nat -> nat) (x1 : nat) := (fun y0 : nat => x0 y0) x1.
Definition term134 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => Peano.le (dist (@pair nat nat (Nat.mul x2 (dest_nadd x0 y0)) (Nat.mul y0 (dest_nadd x0 x2)))) (Nat.mul x1 (Nat.add x2 y0))) x3.
Definition term17 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.mul (Nat.add x0 x1) y0) = (Nat.add (Nat.mul x0 y0) (Nat.mul x1 y0))) x2.
Definition term33 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.le x1 x0) -> (Peano.le x0 y0) -> Peano.le x1 y0) x2.
Definition term138 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat) := forall y0 : nat, Peano.le (dist (@pair nat nat (Nat.mul x4 (Nat.add (dest_nadd x0 y0) (dest_nadd x1 y0))) (Nat.mul y0 (Nat.add (dest_nadd x0 x4) (dest_nadd x1 x4))))) (Nat.mul (Nat.add x2 x3) (Nat.add x4 y0)).
Definition term18 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.add x0 x1) x2.
Definition term119 (x0 : nadd) (x1 : nat) (x2 : nadd) (x3 : nat) := dist (@pair nat nat (Nat.add (Nat.mul x3 (dest_nadd x0 x1)) (Nat.mul x3 (dest_nadd x2 x1))) (Nat.add (Nat.mul x1 (dest_nadd x0 x3)) (Nat.mul x1 (dest_nadd x2 x3)))).
Definition term19 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x0 x2) (Nat.mul x1 x2).
Definition term64 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.mul x1 (Nat.add x0 y0)) = (Nat.add (Nat.mul x1 x0) (Nat.mul x1 y0)).
Definition term117 (x0 : nadd) (x1 : nat) (x2 : nadd) (x3 : nat) := @pair nat nat (Nat.add (Nat.mul x1 (dest_nadd x0 x3)) (Nat.mul x1 (dest_nadd x2 x3))).
Definition term44 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.add (dist (@pair nat nat x0 x1)) (dist (@pair nat nat x2 x3)).
Definition term53 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le (Nat.add (dist (@pair nat nat x0 y0)) (dist (@pair nat nat x1 y1))) y2) -> Peano.le (dist (@pair nat nat (Nat.add x0 x1) (Nat.add y0 y1))) y2) x2.
Definition term87 (x0 : nadd) (x1 : nadd) (x2 : nat) := (fun y0 : nat => (fun y1 : nat => Nat.add (dest_nadd x0 y1) (dest_nadd x1 y1)) y0) x2.
Definition term96 (x0 : nat) (x1 : nadd) (x2 : nadd) (x3 : nat) := @pair nat nat (Nat.mul x0 (Nat.add (dest_nadd x1 x3) (dest_nadd x2 x3))).
Definition term55 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := (fun y0 : nat => (Peano.le (Nat.add (dist (@pair nat nat x0 x2)) (dist (@pair nat nat x1 x3))) y0) -> Peano.le (dist (@pair nat nat (Nat.add x0 x1) (Nat.add x2 x3))) y0) x4.
Definition term80 (x0 : nadd) (x1 : nadd) := @eq (nat -> nat) (dest_nadd (nadd_add x0 x1)).
Definition term124 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : nat) := (Peano.le (Nat.add (dist (@pair nat nat (Nat.mul x4 (dest_nadd x0 x5)) (Nat.mul x5 (dest_nadd x0 x4)))) (dist (@pair nat nat (Nat.mul x4 (dest_nadd x1 x5)) (Nat.mul x5 (dest_nadd x1 x4))))) (Nat.mul (Nat.add x2 x3) (Nat.add x4 x5))) -> Peano.le (dist (@pair nat nat (Nat.add (Nat.mul x4 (dest_nadd x0 x5)) (Nat.mul x4 (dest_nadd x1 x5))) (Nat.add (Nat.mul x5 (dest_nadd x0 x4)) (Nat.mul x5 (dest_nadd x1 x4))))) (Nat.mul (Nat.add x2 x3) (Nat.add x4 x5)).
Definition term128 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : nat) := Peano.le (Nat.add (dist (@pair nat nat (Nat.mul x4 (dest_nadd x0 x5)) (Nat.mul x5 (dest_nadd x0 x4)))) (dist (@pair nat nat (Nat.mul x4 (dest_nadd x1 x5)) (Nat.mul x5 (dest_nadd x1 x4))))) (Nat.mul (Nat.add x2 x3) (Nat.add x4 x5)).
Definition term75 (x0 : nadd) := forall y0 : nadd, (nadd_add x0 y0) = (mk_nadd (fun y1 : nat => Nat.add (dest_nadd x0 y1) (dest_nadd y0 y1))).
Definition term45 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := dist (@pair nat nat (Nat.add x0 x1) (Nat.add x2 x3)).
Definition term41 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) -> forall y2 : nat, (Peano.le y1 y2) -> Peano.le y0 y2) x0.
Definition term9 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le x0 x1) /\ (Peano.le x2 x3).
Definition term6 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, ((Peano.le x0 x2) /\ (Peano.le x1 y0)) -> Peano.le (Nat.add x0 x1) (Nat.add x2 y0).
Definition term46 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := forall y0 : nat, (Peano.le (Nat.add (dist (@pair nat nat x0 x2)) (dist (@pair nat nat x1 x3))) y0) -> Peano.le (dist (@pair nat nat (Nat.add x0 x1) (Nat.add x2 x3))) y0.
Definition term137 (x0 : nadd) (x1 : nat) (x2 : nadd) (x3 : nat) (x4 : nat) (x5 : nat) := (Peano.le (dist (@pair nat nat (Nat.mul x4 (dest_nadd x0 x5)) (Nat.mul x5 (dest_nadd x0 x4)))) (Nat.mul x1 (Nat.add x4 x5))) /\ (Peano.le (dist (@pair nat nat (Nat.mul x4 (dest_nadd x2 x5)) (Nat.mul x5 (dest_nadd x2 x4)))) (Nat.mul x3 (Nat.add x4 x5))).
Definition term43 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le (dist (@pair nat nat (Nat.add x0 x1) (Nat.add x2 x3))) (Nat.add (dist (@pair nat nat x0 x2)) (dist (@pair nat nat x1 x3)))) -> forall y0 : nat, (Peano.le (Nat.add (dist (@pair nat nat x0 x2)) (dist (@pair nat nat x1 x3))) y0) -> Peano.le (dist (@pair nat nat (Nat.add x0 x1) (Nat.add x2 x3))) y0.
Definition term34 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x1 x0) -> (Peano.le x0 x2) -> Peano.le x1 x2.
Definition term11 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.add y0 y1) (Nat.add y2 y3)) -> Peano.le (Nat.add x0 x1) (Nat.add x2 x3).
Definition term123 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : nat) := Peano.le (dist (@pair nat nat (Nat.add (Nat.mul x4 (dest_nadd x0 x5)) (Nat.mul x4 (dest_nadd x1 x5))) (Nat.add (Nat.mul x5 (dest_nadd x0 x4)) (Nat.mul x5 (dest_nadd x1 x4))))) (Nat.mul (Nat.add x2 x3) (Nat.add x4 x5)).
Definition term122 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : nat) := Peano.le (dist (@pair nat nat (Nat.mul x4 (Nat.add (dest_nadd x0 x5) (dest_nadd x1 x5))) (Nat.mul x5 (Nat.add (dest_nadd x0 x4) (dest_nadd x1 x4))))) (Nat.mul (Nat.add x2 x3) (Nat.add x4 x5)).
Definition term16 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.mul (Nat.add x0 x1) y0) = (Nat.add (Nat.mul x0 y0) (Nat.mul x1 y0)).
Definition term94 (x0 : nat) (x1 : nadd) (x2 : nadd) (x3 : nat) := Nat.mul x0 (Nat.add (dest_nadd x1 x3) (dest_nadd x2 x3)).
Definition term68 (x0 : nadd) := (fun y0 : nadd => exists y1 : nat, forall y2 : nat, forall y3 : nat, Peano.le (dist (@pair nat nat (Nat.mul y2 (dest_nadd y0 y3)) (Nat.mul y3 (dest_nadd y0 y2)))) (Nat.mul y1 (Nat.add y2 y3))) x0.
Definition term129 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : nat) := Peano.le (Nat.add (dist (@pair nat nat (Nat.mul x4 (dest_nadd x0 x5)) (Nat.mul x5 (dest_nadd x0 x4)))) (dist (@pair nat nat (Nat.mul x4 (dest_nadd x1 x5)) (Nat.mul x5 (dest_nadd x1 x4))))) (Nat.add (Nat.mul x2 (Nat.add x4 x5)) (Nat.mul x3 (Nat.add x4 x5))).
Definition term82 (x0 : nadd) (x1 : nadd) := fun y0 : nat => Nat.add (dest_nadd x0 y0) (dest_nadd x1 y0).
Definition term66 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (Nat.add x1 x2).
Definition term81 (x0 : nadd) (x1 : nadd) := @eq (nat -> nat) (dest_nadd (mk_nadd (fun y0 : nat => Nat.add (dest_nadd x0 y0) (dest_nadd x1 y0)))).
Definition term36 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le x0 y0) -> Peano.le x1 y0.
Definition term26 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => Peano.le (dist (@pair nat nat (Nat.add x0 x2) (Nat.add x1 y0))) (Nat.add (dist (@pair nat nat x0 x1)) (dist (@pair nat nat x2 y0)))) x3.
Definition term90 (x0 : nadd) (x1 : nadd) := fun y0 : nat => (fun y1 : nat => Nat.add (dest_nadd x0 y1) (dest_nadd x1 y1)) y0.
Definition term131 (x0 : nat) (x1 : nadd) (x2 : nat) := dist (@pair nat nat (Nat.mul x2 (dest_nadd x1 x0)) (Nat.mul x0 (dest_nadd x1 x2))).
Definition term126 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.add (Nat.mul x0 (Nat.add x2 x3)) (Nat.mul x1 (Nat.add x2 x3)).
Definition term8 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Peano.le x0 x2) /\ (Peano.le x1 x3)) -> Peano.le (Nat.add x0 x1) (Nat.add x2 x3).
Definition term101 (x0 : nat) (x1 : nadd) (x2 : nadd) (x3 : nat) := Peano.le (dist (@pair nat nat (Nat.mul x3 ((fun y0 : nat => Nat.add (dest_nadd x1 y0) (dest_nadd x2 y0)) x0)) (Nat.mul x0 ((fun y0 : nat => Nat.add (dest_nadd x1 y0) (dest_nadd x2 y0)) x3)))).
Definition term99 (x0 : nat) (x1 : nadd) (x2 : nadd) (x3 : nat) := dist (@pair nat nat (Nat.mul x3 ((fun y0 : nat => Nat.add (dest_nadd x1 y0) (dest_nadd x2 y0)) x0)) (Nat.mul x0 ((fun y0 : nat => Nat.add (dest_nadd x1 y0) (dest_nadd x2 y0)) x3))).
Definition term42 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le x0 y0) -> forall y1 : nat, (Peano.le y0 y1) -> Peano.le x0 y1) x1.
Definition term110 (x0 : nadd) (x1 : nadd) (x2 : nat) := fun y0 : nat => forall y1 : nat, Peano.le (dist (@pair nat nat (Nat.mul y0 (Nat.add (dest_nadd x0 y1) (dest_nadd x1 y1))) (Nat.mul y1 (Nat.add (dest_nadd x0 y0) (dest_nadd x1 y0))))) (Nat.mul x2 (Nat.add y0 y1)).
Definition term109 (x0 : nadd) (x1 : nadd) (x2 : nat) := fun y0 : nat => forall y1 : nat, Peano.le (dist (@pair nat nat (Nat.mul y0 ((fun y2 : nat => Nat.add (dest_nadd x0 y2) (dest_nadd x1 y2)) y1)) (Nat.mul y1 ((fun y2 : nat => Nat.add (dest_nadd x0 y2) (dest_nadd x1 y2)) y0)))) (Nat.mul x2 (Nat.add y0 y1)).
Definition term97 (x0 : nat) (x1 : nadd) (x2 : nadd) (x3 : nat) := @pair nat nat (Nat.mul x3 ((fun y0 : nat => Nat.add (dest_nadd x1 y0) (dest_nadd x2 y0)) x0)) (Nat.mul x0 ((fun y0 : nat => Nat.add (dest_nadd x1 y0) (dest_nadd x2 y0)) x3)).
Definition term140 (x0 : nadd) := fun y0 : nat => forall y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (Nat.mul y1 (dest_nadd x0 y2)) (Nat.mul y2 (dest_nadd x0 y1)))) (Nat.mul y0 (Nat.add y1 y2)).
Definition term114 (x0 : nadd) (x1 : nadd) := fun y0 : nat => forall y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (Nat.mul y1 (Nat.add (dest_nadd x0 y2) (dest_nadd x1 y2))) (Nat.mul y2 (Nat.add (dest_nadd x0 y1) (dest_nadd x1 y1))))) (Nat.mul y0 (Nat.add y1 y2)).
Definition term113 (x0 : nadd) (x1 : nadd) := fun y0 : nat => forall y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (Nat.mul y1 ((fun y3 : nat => Nat.add (dest_nadd x0 y3) (dest_nadd x1 y3)) y2)) (Nat.mul y2 ((fun y3 : nat => Nat.add (dest_nadd x0 y3) (dest_nadd x1 y3)) y1)))) (Nat.mul y0 (Nat.add y1 y2)).
Definition term83 (x0 : nadd) (x1 : nadd) := is_nadd (fun y0 : nat => Nat.add (dest_nadd x0 y0) (dest_nadd x1 y0)).
Definition term106 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) := fun y0 : nat => Peano.le (dist (@pair nat nat (Nat.mul x3 (Nat.add (dest_nadd x0 y0) (dest_nadd x1 y0))) (Nat.mul y0 (Nat.add (dest_nadd x0 x3) (dest_nadd x1 x3))))) (Nat.mul x2 (Nat.add x3 y0)).
Definition term105 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) := fun y0 : nat => Peano.le (dist (@pair nat nat (Nat.mul x3 ((fun y1 : nat => Nat.add (dest_nadd x0 y1) (dest_nadd x1 y1)) y0)) (Nat.mul y0 ((fun y1 : nat => Nat.add (dest_nadd x0 y1) (dest_nadd x1 y1)) x3)))) (Nat.mul x2 (Nat.add x3 y0)).
Definition term95 (x0 : nat) (x1 : nadd) (x2 : nadd) (x3 : nat) := @pair nat nat (Nat.mul x0 ((fun y0 : nat => Nat.add (dest_nadd x1 y0) (dest_nadd x2 y0)) x3)).
Definition term135 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (dist (@pair nat nat (Nat.mul x2 (dest_nadd x0 x3)) (Nat.mul x3 (dest_nadd x0 x2)))) (Nat.mul x1 (Nat.add x2 x3)).
Definition term25 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, Peano.le (dist (@pair nat nat (Nat.add x0 x2) (Nat.add x1 y0))) (Nat.add (dist (@pair nat nat x0 x1)) (dist (@pair nat nat x2 y0))).
