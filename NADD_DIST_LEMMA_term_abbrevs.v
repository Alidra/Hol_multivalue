Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term25 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.mul x1 (Nat.add x0 y0)) = (Nat.add (Nat.mul x1 x0) (Nat.mul x1 y0))) x2.
Definition term51 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (dist (@pair nat nat x0 x1)) (dist (@pair nat nat x1 x2)).
Definition term64 (x0 : nat) (x1 : nat) (x2 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, (Peano.le (Nat.add (dist (@pair nat nat y1 y0)) (dist (@pair nat nat y0 y2))) y3) -> Peano.le (dist (@pair nat nat y1 y2)) y3) -> Peano.le (dist (@pair nat nat x0 x1)) x2.
Definition term136 (x0 : nat) (x1 : nadd) (x2 : nat) := @pair nat nat (dest_nadd x1 (S (Nat.add x2 x0))) (dest_nadd x1 x2).
Definition term42 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x2) -> Peano.le x1 x2.
Definition term185 (x0 : nadd) := exists y0 : nat, forall y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 (Nat.add y1 y2)) (dest_nadd x0 y1))) (Nat.mul y0 y2).
Definition term91 (x0 : nadd) := exists y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 (S y1)) (dest_nadd x0 y1))) y0.
Definition term169 := (forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))))).
Definition term72 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (exists y3 : nat, Peano.le (Nat.add (dist (@pair nat nat y0 y3)) (dist (@pair nat nat y3 y1))) y2) -> Peano.le (dist (@pair nat nat y0 y1)) y2) x0.
Definition term57 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, (Peano.le (Nat.add (dist (@pair nat nat y1 y0)) (dist (@pair nat nat y0 y2))) y3) -> Peano.le (dist (@pair nat nat y1 y2)) y3) x0.
Definition term36 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le y0 y1) -> (Peano.le y1 y2) -> Peano.le y0 y2) x0.
Definition term29 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat y0 y2)) (Nat.add (dist (@pair nat nat y0 y1)) (dist (@pair nat nat y1 y2)))) x0.
Definition term21 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.mul y0 (Nat.add y1 y2)) = (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y2))) x0.
Definition term6 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.add y0 y1) (Nat.add y2 y3)) x0.
Definition term12 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => ((Peano.le x0 x2) /\ (Peano.le x1 y0)) -> Peano.le (Nat.add x0 x1) (Nat.add x2 y0)) x3.
Definition term123 (x0 : nadd) (x1 : nat) := @pair nat nat (dest_nadd x0 (Nat.add x1 (NUMERAL 0))) (dest_nadd x0 x1).
Definition term28 (x0 : nat) := (fun y0 : nat => (S y0) = (Nat.add y0 (NUMERAL (BIT1 0)))) x0.
Definition term167 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := ((Peano.le (dist (@pair nat nat (dest_nadd x0 (Nat.add (Nat.add x1 x3) (NUMERAL (BIT1 0)))) (dest_nadd x0 (Nat.add x1 x3)))) (Nat.mul x2 (NUMERAL (BIT1 0)))) /\ (Peano.le (dist (@pair nat nat (dest_nadd x0 (Nat.add x1 x3)) (dest_nadd x0 x1))) (Nat.mul x2 x3))) -> Peano.le (Nat.add (dist (@pair nat nat (dest_nadd x0 (Nat.add (Nat.add x1 x3) (NUMERAL (BIT1 0)))) (dest_nadd x0 (Nat.add x1 x3)))) (dist (@pair nat nat (dest_nadd x0 (Nat.add x1 x3)) (dest_nadd x0 x1)))) (Nat.add (Nat.mul x2 (NUMERAL (BIT1 0))) (Nat.mul x2 x3)).
Definition term180 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := and (Peano.le (dist (@pair nat nat (dest_nadd x0 (Nat.add (Nat.add x1 x2) (NUMERAL (BIT1 0)))) (dest_nadd x0 (Nat.add x1 x2)))) (Nat.mul x3 (NUMERAL (BIT1 0)))).
Definition term100 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => Peano.le (dist (@pair nat nat (dest_nadd x0 (Nat.add x1 y0)) (dest_nadd x0 x1))) (Nat.mul x2 y0)) x3.
Definition term71 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, (Peano.le (Nat.add (dist (@pair nat nat y1 y0)) (dist (@pair nat nat y0 y2))) y3) -> Peano.le (dist (@pair nat nat y1 y2)) y3) -> forall y0 : nat, forall y1 : nat, forall y2 : nat, (exists y3 : nat, Peano.le (Nat.add (dist (@pair nat nat y0 y3)) (dist (@pair nat nat y3 y1))) y2) -> Peano.le (dist (@pair nat nat y0 y1)) y2.
Definition term47 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.le y0 y1) -> (Peano.le y1 y2) -> Peano.le y0 y2) -> forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> forall y2 : nat, (Peano.le y1 y2) -> Peano.le y0 y2.
Definition term17 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.add y0 y1) (Nat.add y2 y3)) -> forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.add y0 y1) (Nat.add y2 y3).
Definition term142 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (dist (@pair nat nat (dest_nadd x0 (S (Nat.add x1 x3))) (dest_nadd x0 x1))) (Nat.mul x2 (S x3)).
Definition term105 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (dist (@pair nat nat (dest_nadd x0 (Nat.add x1 (S x3))) (dest_nadd x0 x1))) (Nat.mul x2 (S x3)).
Definition term2 := fun y0 : nat => (Nat.add y0 (NUMERAL (BIT1 0))) = (S y0).
Definition term151 (x0 : nadd) (x1 : nat) (x2 : nat) := dist (@pair nat nat (dest_nadd x0 (Nat.add (Nat.add x1 x2) (NUMERAL (BIT1 0)))) (dest_nadd x0 (Nat.add x1 x2))).
Definition term80 := (forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))).
Definition term179 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (dist (@pair nat nat (dest_nadd x0 (S (Nat.add x1 x2))) (dest_nadd x0 (Nat.add x1 x2)))) x3.
Definition term121 (x0 : nadd) (x1 : nat) := @pair nat nat (dest_nadd x0 (Nat.add x1 (NUMERAL 0))).
Definition term3 := forall y0 : nat, (S y0) = (Nat.add y0 (NUMERAL (BIT1 0))).
Definition term140 (x0 : nat) (x1 : nadd) (x2 : nat) := Peano.le (dist (@pair nat nat (dest_nadd x1 (S (Nat.add x2 x0))) (dest_nadd x1 x2))).
Definition term139 (x0 : nat) (x1 : nadd) (x2 : nat) := Peano.le (dist (@pair nat nat (dest_nadd x1 (Nat.add x2 (S x0))) (dest_nadd x1 x2))).
Definition term117 (x0 : nadd) (x1 : nat) (x2 : nat) := forall y0 : nat, (fun y1 : nat => Peano.le (dist (@pair nat nat (dest_nadd x0 (Nat.add x1 y1)) (dest_nadd x0 x1))) (Nat.mul x2 y1)) y0.
Definition term74 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (exists y1 : nat, Peano.le (Nat.add (dist (@pair nat nat x0 y1)) (dist (@pair nat nat y1 x1))) y0) -> Peano.le (dist (@pair nat nat x0 x1)) y0) x2.
Definition term112 (x0 : nadd) (x1 : nat) (x2 : nat) := ((fun y0 : nat => Peano.le (dist (@pair nat nat (dest_nadd x0 (Nat.add x1 y0)) (dest_nadd x0 x1))) (Nat.mul x2 y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => Peano.le (dist (@pair nat nat (dest_nadd x0 (Nat.add x1 y1)) (dest_nadd x0 x1))) (Nat.mul x2 y1)) y0) -> (fun y1 : nat => Peano.le (dist (@pair nat nat (dest_nadd x0 (Nat.add x1 y1)) (dest_nadd x0 x1))) (Nat.mul x2 y1)) (S y0)).
Definition term52 (x0 : nat) (x1 : nat) := dist (@pair nat nat x0 x1).
Definition term15 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (Nat.add x0 x1) (Nat.add x2 x3).
Definition term101 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (dist (@pair nat nat (dest_nadd x0 (Nat.add x1 x3)) (dest_nadd x0 x1))) (Nat.mul x2 x3).
Definition term172 (x0 : nat) := (fun y0 : nat => (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) x0.
Definition term88 (x0 : nat) := (fun y0 : nat => (Nat.add y0 (NUMERAL 0)) = y0) x0.
Definition term158 (x0 : nat) (x1 : nadd) (x2 : nat) := Peano.le (Nat.add (dist (@pair nat nat (dest_nadd x1 (Nat.add (Nat.add x2 x0) (NUMERAL (BIT1 0)))) (dest_nadd x1 (Nat.add x2 x0)))) (dist (@pair nat nat (dest_nadd x1 (Nat.add x2 x0)) (dest_nadd x1 x2)))).
Definition term157 (x0 : nat) (x1 : nadd) (x2 : nat) := Peano.le (Nat.add (dist (@pair nat nat (dest_nadd x1 (S (Nat.add x2 x0))) (dest_nadd x1 (Nat.add x2 x0)))) (dist (@pair nat nat (dest_nadd x1 (Nat.add x2 x0)) (dest_nadd x1 x2)))).
Definition term75 (x0 : nat) := (fun y0 : nat => Peano.le (NUMERAL 0) y0) x0.
Definition term33 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => Peano.le (dist (@pair nat nat x0 y0)) (Nat.add (dist (@pair nat nat x0 x1)) (dist (@pair nat nat x1 y0)))) x2.
Definition term106 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := ((fun y0 : nat => Peano.le (dist (@pair nat nat (dest_nadd x0 (Nat.add x1 y0)) (dest_nadd x0 x1))) (Nat.mul x2 y0)) x3) -> (fun y0 : nat => Peano.le (dist (@pair nat nat (dest_nadd x0 (Nat.add x1 y0)) (dest_nadd x0 x1))) (Nat.mul x2 y0)) (S x3).
Definition term94 (x0 : nadd) (x1 : nat) (x2 : nat) := (((fun y0 : nat => Peano.le (dist (@pair nat nat (dest_nadd x0 (Nat.add x1 y0)) (dest_nadd x0 x1))) (Nat.mul x2 y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => Peano.le (dist (@pair nat nat (dest_nadd x0 (Nat.add x1 y1)) (dest_nadd x0 x1))) (Nat.mul x2 y1)) y0) -> (fun y1 : nat => Peano.le (dist (@pair nat nat (dest_nadd x0 (Nat.add x1 y1)) (dest_nadd x0 x1))) (Nat.mul x2 y1)) (S y0))) -> forall y0 : nat, (fun y1 : nat => Peano.le (dist (@pair nat nat (dest_nadd x0 (Nat.add x1 y1)) (dest_nadd x0 x1))) (Nat.mul x2 y1)) y0.
Definition term131 (x0 : nadd) (x1 : nat) (x2 : nat) := dest_nadd x0 (Nat.add x1 (S x2)).
Definition term156 (x0 : nat) (x1 : nadd) (x2 : nat) := Nat.add (dist (@pair nat nat (dest_nadd x1 (Nat.add (Nat.add x2 x0) (NUMERAL (BIT1 0)))) (dest_nadd x1 (Nat.add x2 x0)))) (dist (@pair nat nat (dest_nadd x1 (Nat.add x2 x0)) (dest_nadd x1 x2))).
Definition term155 (x0 : nat) (x1 : nadd) (x2 : nat) := Nat.add (dist (@pair nat nat (dest_nadd x1 (S (Nat.add x2 x0))) (dest_nadd x1 (Nat.add x2 x0)))) (dist (@pair nat nat (dest_nadd x1 (Nat.add x2 x0)) (dest_nadd x1 x2))).
Definition term45 (x0 : nat) := forall y0 : nat, (Peano.le x0 y0) -> forall y1 : nat, (Peano.le y0 y1) -> Peano.le x0 y1.
Definition term125 (x0 : nadd) (x1 : nat) := dist (@pair nat nat (dest_nadd x0 (Nat.add x1 (NUMERAL 0))) (dest_nadd x0 x1)).
Definition term138 (x0 : nat) (x1 : nadd) (x2 : nat) := dist (@pair nat nat (dest_nadd x1 (S (Nat.add x2 x0))) (dest_nadd x1 x2)).
Definition term93 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term120 (x0 : nadd) (x1 : nat) := dest_nadd x0 (Nat.add x1 (NUMERAL 0)).
Definition term166 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (Nat.add (dist (@pair nat nat (dest_nadd x0 (Nat.add (Nat.add x1 x3) (NUMERAL (BIT1 0)))) (dest_nadd x0 (Nat.add x1 x3)))) (dist (@pair nat nat (dest_nadd x0 (Nat.add x1 x3)) (dest_nadd x0 x1)))) (Nat.add (Nat.mul x2 (NUMERAL (BIT1 0))) (Nat.mul x2 x3)).
Definition term114 (x0 : nadd) (x1 : nat) (x2 : nat) := imp (((fun y0 : nat => Peano.le (dist (@pair nat nat (dest_nadd x0 (Nat.add x1 y0)) (dest_nadd x0 x1))) (Nat.mul x2 y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => Peano.le (dist (@pair nat nat (dest_nadd x0 (Nat.add x1 y1)) (dest_nadd x0 x1))) (Nat.mul x2 y1)) y0) -> (fun y1 : nat => Peano.le (dist (@pair nat nat (dest_nadd x0 (Nat.add x1 y1)) (dest_nadd x0 x1))) (Nat.mul x2 y1)) (S y0))).
Definition term89 (x0 : nat) := Nat.add x0 (NUMERAL 0).
Definition term73 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (exists y2 : nat, Peano.le (Nat.add (dist (@pair nat nat x0 y2)) (dist (@pair nat nat y2 y0))) y1) -> Peano.le (dist (@pair nat nat x0 y0)) y1) x1.
Definition term38 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le x0 y0) -> (Peano.le y0 y1) -> Peano.le x0 y1) x1.
Definition term31 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, Peano.le (dist (@pair nat nat x0 y1)) (Nat.add (dist (@pair nat nat x0 y0)) (dist (@pair nat nat y0 y1)))) x1.
Definition term23 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul x0 (Nat.add y0 y1)) = (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y1))) x1.
Definition term183 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := fun y0 : nat => Peano.le (Nat.add (dist (@pair nat nat (dest_nadd x0 (S (Nat.add x1 x3))) y0)) (dist (@pair nat nat y0 (dest_nadd x0 x1)))) (Nat.mul x2 (S x3)).
Definition term110 (x0 : nadd) (x1 : nat) (x2 : nat) := forall y0 : nat, ((fun y1 : nat => Peano.le (dist (@pair nat nat (dest_nadd x0 (Nat.add x1 y1)) (dest_nadd x0 x1))) (Nat.mul x2 y1)) y0) -> (fun y1 : nat => Peano.le (dist (@pair nat nat (dest_nadd x0 (Nat.add x1 y1)) (dest_nadd x0 x1))) (Nat.mul x2 y1)) (S y0).
Definition term34 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (dist (@pair nat nat x0 x2)) (Nat.add (dist (@pair nat nat x0 x1)) (dist (@pair nat nat x1 x2))).
Definition term173 (x0 : nat) := (fun y0 : nat => (Nat.add y0 (NUMERAL (BIT1 0))) = (S y0)) x0.
Definition term141 (x0 : nat) (x1 : nat) := Nat.mul x0 (S x1).
Definition term61 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le (Nat.add (dist (@pair nat nat x1 x0)) (dist (@pair nat nat x0 x2))) x3) -> Peano.le (dist (@pair nat nat x1 x2)) x3.
Definition term174 (x0 : nadd) (x1 : nat) (x2 : nat) := (fun y0 : nat => Peano.le (dist (@pair nat nat (dest_nadd x0 (S y0)) (dest_nadd x0 y0))) x1) x2.
Definition term171 := forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0.
Definition term87 := forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0.
Definition term137 (x0 : nat) (x1 : nadd) (x2 : nat) := dist (@pair nat nat (dest_nadd x1 (Nat.add x2 (S x0))) (dest_nadd x1 x2)).
Definition term113 (x0 : nadd) (x1 : nat) (x2 : nat) := (Peano.le (dist (@pair nat nat (dest_nadd x0 (Nat.add x1 (NUMERAL 0))) (dest_nadd x0 x1))) (Nat.mul x2 (NUMERAL 0))) /\ (forall y0 : nat, (Peano.le (dist (@pair nat nat (dest_nadd x0 (Nat.add x1 y0)) (dest_nadd x0 x1))) (Nat.mul x2 y0)) -> Peano.le (dist (@pair nat nat (dest_nadd x0 (Nat.add x1 (S y0))) (dest_nadd x0 x1))) (Nat.mul x2 (S y0))).
Definition term102 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := imp ((fun y0 : nat => Peano.le (dist (@pair nat nat (dest_nadd x0 (Nat.add x1 y0)) (dest_nadd x0 x1))) (Nat.mul x2 y0)) x3).
Definition term98 (x0 : nadd) (x1 : nat) (x2 : nat) := and ((fun y0 : nat => Peano.le (dist (@pair nat nat (dest_nadd x0 (Nat.add x1 y0)) (dest_nadd x0 x1))) (Nat.mul x2 y0)) (NUMERAL 0)).
Definition term39 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le x1 x0) -> (Peano.le x0 y0) -> Peano.le x1 y0.
Definition term181 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le (dist (@pair nat nat (dest_nadd x0 (Nat.add (Nat.add x1 x3) (NUMERAL (BIT1 0)))) (dest_nadd x0 (Nat.add x1 x3)))) (Nat.mul x2 (NUMERAL (BIT1 0)))) /\ (Peano.le (dist (@pair nat nat (dest_nadd x0 (Nat.add x1 x3)) (dest_nadd x0 x1))) (Nat.mul x2 x3)).
Definition term95 (x0 : nadd) (x1 : nat) (x2 : nat) := fun y0 : nat => Peano.le (dist (@pair nat nat (dest_nadd x0 (Nat.add x1 y0)) (dest_nadd x0 x1))) (Nat.mul x2 y0).
Definition term182 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := exists y0 : nat, Peano.le (Nat.add (dist (@pair nat nat (dest_nadd x0 (S (Nat.add x1 x3))) y0)) (dist (@pair nat nat y0 (dest_nadd x0 x1)))) (Nat.mul x2 (S x3)).
Definition term62 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (Nat.add (dist (@pair nat nat x0 x1)) (dist (@pair nat nat x1 x2))) x3.
Definition term149 (x0 : nadd) (x1 : nat) (x2 : nat) := @pair nat nat (dest_nadd x0 (Nat.add (Nat.add x1 x2) (NUMERAL (BIT1 0)))) (dest_nadd x0 (Nat.add x1 x2)).
Definition term27 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x1 x0) (Nat.mul x1 x2).
Definition term108 (x0 : nadd) (x1 : nat) (x2 : nat) := fun y0 : nat => ((fun y1 : nat => Peano.le (dist (@pair nat nat (dest_nadd x0 (Nat.add x1 y1)) (dest_nadd x0 x1))) (Nat.mul x2 y1)) y0) -> (fun y1 : nat => Peano.le (dist (@pair nat nat (dest_nadd x0 (Nat.add x1 y1)) (dest_nadd x0 x1))) (Nat.mul x2 y1)) (S y0).
Definition term150 (x0 : nadd) (x1 : nat) (x2 : nat) := dist (@pair nat nat (dest_nadd x0 (S (Nat.add x1 x2))) (dest_nadd x0 (Nat.add x1 x2))).
Definition term177 (x0 : nadd) (x1 : nat) (x2 : nat) := Peano.le (dist (@pair nat nat (dest_nadd x0 (S (Nat.add x1 x2))) (dest_nadd x0 (Nat.add x1 x2)))).
Definition term176 (x0 : nadd) (x1 : nat) (x2 : nat) := Peano.le (dist (@pair nat nat (dest_nadd x0 (Nat.add (Nat.add x1 x2) (NUMERAL (BIT1 0)))) (dest_nadd x0 (Nat.add x1 x2)))).
Definition term86 (x0 : nat) (x1 : nat) := S (Nat.add x0 x1).
Definition term44 (x0 : nat) (x1 : nat) := (Peano.le x1 x0) -> forall y0 : nat, (Peano.le x0 y0) -> Peano.le x1 y0.
Definition term132 (x0 : nadd) (x1 : nat) (x2 : nat) := dest_nadd x0 (S (Nat.add x1 x2)).
Definition term184 (x0 : nadd) (x1 : nat) := forall y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 (Nat.add y0 y1)) (dest_nadd x0 y0))) (Nat.mul x1 y1).
Definition term81 := forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)).
Definition term70 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (exists y3 : nat, Peano.le (Nat.add (dist (@pair nat nat y0 y3)) (dist (@pair nat nat y3 y1))) y2) -> Peano.le (dist (@pair nat nat y0 y1)) y2.
Definition term69 (x0 : nat) := forall y0 : nat, forall y1 : nat, (exists y2 : nat, Peano.le (Nat.add (dist (@pair nat nat x0 y2)) (dist (@pair nat nat y2 y0))) y1) -> Peano.le (dist (@pair nat nat x0 y0)) y1.
Definition term56 := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, (Peano.le (Nat.add (dist (@pair nat nat y1 y0)) (dist (@pair nat nat y0 y2))) y3) -> Peano.le (dist (@pair nat nat y1 y2)) y3.
Definition term55 (x0 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.le (Nat.add (dist (@pair nat nat y0 x0)) (dist (@pair nat nat x0 y1))) y2) -> Peano.le (dist (@pair nat nat y0 y1)) y2.
Definition term54 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add (dist (@pair nat nat x1 x0)) (dist (@pair nat nat x0 y0))) y1) -> Peano.le (dist (@pair nat nat x1 y0)) y1.
Definition term46 := forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> forall y2 : nat, (Peano.le y1 y2) -> Peano.le y0 y2.
Definition term37 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le x0 y0) -> (Peano.le y0 y1) -> Peano.le x0 y1.
Definition term35 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.le y0 y1) -> (Peano.le y1 y2) -> Peano.le y0 y2.
Definition term30 (x0 : nat) := forall y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat x0 y1)) (Nat.add (dist (@pair nat nat x0 y0)) (dist (@pair nat nat y0 y1))).
Definition term22 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.mul x0 (Nat.add y0 y1)) = (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y1)).
Definition term9 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le x1 y1)) -> Peano.le (Nat.add x0 x1) (Nat.add y0 y1).
Definition term7 (x0 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le x0 y1) /\ (Peano.le y0 y2)) -> Peano.le (Nat.add x0 y0) (Nat.add y1 y2).
Definition term5 := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.add y0 y1) (Nat.add y2 y3).
Definition term59 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (Nat.add (dist (@pair nat nat x1 x0)) (dist (@pair nat nat x0 y0))) y1) -> Peano.le (dist (@pair nat nat x1 y0)) y1) x2.
Definition term10 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le x1 y1)) -> Peano.le (Nat.add x0 x1) (Nat.add y0 y1)) x2.
Definition term58 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le (Nat.add (dist (@pair nat nat y0 x0)) (dist (@pair nat nat x0 y1))) y2) -> Peano.le (dist (@pair nat nat y0 y1)) y2) x1.
Definition term8 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.le x0 y1) /\ (Peano.le y0 y2)) -> Peano.le (Nat.add x0 y0) (Nat.add y1 y2)) x1.
Definition term147 (x0 : nadd) (x1 : nat) (x2 : nat) := dest_nadd x0 (Nat.add x1 x2).
Definition term78 (x0 : nat) := dist (@pair nat nat x0 x0).
Definition term65 (x0 : nat) (x1 : nat) (x2 : nat) := exists y0 : nat, Peano.le (Nat.add (dist (@pair nat nat x0 y0)) (dist (@pair nat nat y0 x1))) x2.
Definition term118 (x0 : nadd) (x1 : nat) (x2 : nat) := forall y0 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 (Nat.add x1 y0)) (dest_nadd x0 x1))) (Nat.mul x2 y0).
Definition term178 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (dist (@pair nat nat (dest_nadd x0 (Nat.add (Nat.add x1 x2) (NUMERAL (BIT1 0)))) (dest_nadd x0 (Nat.add x1 x2)))) (Nat.mul x3 (NUMERAL (BIT1 0))).
Definition term96 (x0 : nadd) (x1 : nat) (x2 : nat) := (fun y0 : nat => Peano.le (dist (@pair nat nat (dest_nadd x0 (Nat.add x1 y0)) (dest_nadd x0 x1))) (Nat.mul x2 y0)) (NUMERAL 0).
Definition term40 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.le x1 x0) -> (Peano.le x0 y0) -> Peano.le x1 y0) x2.
Definition term153 (x0 : nadd) (x1 : nat) (x2 : nat) := Nat.add (dist (@pair nat nat (dest_nadd x0 (Nat.add (Nat.add x1 x2) (NUMERAL (BIT1 0)))) (dest_nadd x0 (Nat.add x1 x2)))).
Definition term152 (x0 : nadd) (x1 : nat) (x2 : nat) := Nat.add (dist (@pair nat nat (dest_nadd x0 (S (Nat.add x1 x2))) (dest_nadd x0 (Nat.add x1 x2)))).
Definition term116 (x0 : nadd) (x1 : nat) (x2 : nat) := fun y0 : nat => (fun y1 : nat => Peano.le (dist (@pair nat nat (dest_nadd x0 (Nat.add x1 y1)) (dest_nadd x0 x1))) (Nat.mul x2 y1)) y0.
Definition term134 (x0 : nadd) (x1 : nat) (x2 : nat) := @pair nat nat (dest_nadd x0 (S (Nat.add x1 x2))).
Definition term0 (x0 : nat) := Nat.add x0 (NUMERAL (BIT1 0)).
Definition term76 (x0 : nat) := Peano.le (NUMERAL 0) x0.
Definition term24 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.mul x1 (Nat.add x0 y0)) = (Nat.add (Nat.mul x1 x0) (Nat.mul x1 y0)).
Definition term154 (x0 : nat) (x1 : nadd) (x2 : nat) := dist (@pair nat nat (dest_nadd x1 (Nat.add x2 x0)) (dest_nadd x1 x2)).
Definition term119 (x0 : nadd) (x1 : nat) (x2 : nat) := ((Peano.le (dist (@pair nat nat (dest_nadd x0 (Nat.add x1 (NUMERAL 0))) (dest_nadd x0 x1))) (Nat.mul x2 (NUMERAL 0))) /\ (forall y0 : nat, (Peano.le (dist (@pair nat nat (dest_nadd x0 (Nat.add x1 y0)) (dest_nadd x0 x1))) (Nat.mul x2 y0)) -> Peano.le (dist (@pair nat nat (dest_nadd x0 (Nat.add x1 (S y0))) (dest_nadd x0 x1))) (Nat.mul x2 (S y0)))) -> forall y0 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 (Nat.add x1 y0)) (dest_nadd x0 x1))) (Nat.mul x2 y0).
Definition term19 (x0 : nat) := forall y0 : nat, (Nat.add x0 y0) = (Nat.add y0 x0).
Definition term124 (x0 : nadd) (x1 : nat) := @pair nat nat (dest_nadd x0 x1) (dest_nadd x0 x1).
Definition term146 (x0 : nadd) (x1 : nat) (x2 : nat) := @pair nat nat (dest_nadd x0 (Nat.add (Nat.add x1 x2) (NUMERAL (BIT1 0)))).
Definition term84 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add x0 (S y0)) = (S (Nat.add x0 y0))) x1.
Definition term107 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le (dist (@pair nat nat (dest_nadd x0 (Nat.add x1 x3)) (dest_nadd x0 x1))) (Nat.mul x2 x3)) -> Peano.le (dist (@pair nat nat (dest_nadd x0 (Nat.add x1 (S x3))) (dest_nadd x0 x1))) (Nat.mul x2 (S x3)).
Definition term109 (x0 : nadd) (x1 : nat) (x2 : nat) := fun y0 : nat => (Peano.le (dist (@pair nat nat (dest_nadd x0 (Nat.add x1 y0)) (dest_nadd x0 x1))) (Nat.mul x2 y0)) -> Peano.le (dist (@pair nat nat (dest_nadd x0 (Nat.add x1 (S y0))) (dest_nadd x0 x1))) (Nat.mul x2 (S y0)).
Definition term20 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add x0 y0) = (Nat.add y0 x0)) x1.
Definition term163 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (Nat.add (dist (@pair nat nat (dest_nadd x0 (Nat.add (Nat.add x1 x2) (NUMERAL (BIT1 0)))) (dest_nadd x0 (Nat.add x1 x2)))) (dist (@pair nat nat (dest_nadd x0 (Nat.add x1 x2)) (dest_nadd x0 x1)))) (Nat.add (Nat.mul x3 x2) (Nat.mul x3 (NUMERAL (BIT1 0)))).
Definition term170 := (forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))).
Definition term79 := (forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))).
Definition term160 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x1 x0) (Nat.mul x1 (NUMERAL (BIT1 0))).
Definition term188 := forall y0 : nadd, exists y1 : nat, forall y2 : nat, forall y3 : nat, Peano.le (dist (@pair nat nat (dest_nadd y0 (Nat.add y2 y3)) (dest_nadd y0 y2))) (Nat.mul y1 y3).
Definition term68 (x0 : nat) (x1 : nat) := forall y0 : nat, (exists y1 : nat, Peano.le (Nat.add (dist (@pair nat nat x0 y1)) (dist (@pair nat nat y1 x1))) y0) -> Peano.le (dist (@pair nat nat x0 x1)) y0.
Definition term187 (x0 : nadd) := fun y0 : nat => forall y1 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 (S y1)) (dest_nadd x0 y1))) y0.
Definition term148 (x0 : nadd) (x1 : nat) (x2 : nat) := @pair nat nat (dest_nadd x0 (S (Nat.add x1 x2))) (dest_nadd x0 (Nat.add x1 x2)).
Definition term165 (x0 : nat) := Nat.mul x0 (NUMERAL (BIT1 0)).
Definition term82 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))) x0.
Definition term48 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) -> forall y2 : nat, (Peano.le y1 y2) -> Peano.le y0 y2) x0.
Definition term18 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) x0.
Definition term66 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nat => Peano.le (Nat.add (dist (@pair nat nat x0 y0)) (dist (@pair nat nat y0 x1))) x2.
Definition term145 (x0 : nadd) (x1 : nat) (x2 : nat) := dest_nadd x0 (Nat.add (Nat.add x1 x2) (NUMERAL (BIT1 0))).
Definition term14 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le x0 x1) /\ (Peano.le x2 x3).
Definition term11 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, ((Peano.le x0 x2) /\ (Peano.le x1 y0)) -> Peano.le (Nat.add x0 x1) (Nat.add x2 y0).
Definition term53 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, (Peano.le (Nat.add (dist (@pair nat nat x1 x0)) (dist (@pair nat nat x0 x2))) y0) -> Peano.le (dist (@pair nat nat x1 x2)) y0.
Definition term50 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le (dist (@pair nat nat x1 x2)) (Nat.add (dist (@pair nat nat x1 x0)) (dist (@pair nat nat x0 x2)))) -> forall y0 : nat, (Peano.le (Nat.add (dist (@pair nat nat x1 x0)) (dist (@pair nat nat x0 x2))) y0) -> Peano.le (dist (@pair nat nat x1 x2)) y0.
Definition term129 (x0 : nat) := Nat.mul x0 (NUMERAL 0).
Definition term41 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x1 x0) -> (Peano.le x0 x2) -> Peano.le x1 x2.
Definition term16 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.add y0 y1) (Nat.add y2 y3)) -> Peano.le (Nat.add x0 x1) (Nat.add x2 x3).
Definition term130 (x0 : nat) := Peano.le (NUMERAL 0) (Nat.mul x0 (NUMERAL 0)).
Definition term85 (x0 : nat) (x1 : nat) := Nat.add x0 (S x1).
Definition term162 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (Nat.add (dist (@pair nat nat (dest_nadd x0 (S (Nat.add x1 x3))) (dest_nadd x0 (Nat.add x1 x3)))) (dist (@pair nat nat (dest_nadd x0 (Nat.add x1 x3)) (dest_nadd x0 x1)))) (Nat.mul x2 (S x3)).
Definition term133 (x0 : nadd) (x1 : nat) (x2 : nat) := @pair nat nat (dest_nadd x0 (Nat.add x1 (S x2))).
Definition term92 (x0 : nadd) (x1 : nat) := forall y0 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 (S y0)) (dest_nadd x0 y0))) x1.
Definition term90 (x0 : nadd) := (fun y0 : nadd => exists y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (dest_nadd y0 (S y2)) (dest_nadd y0 y2))) y1) x0.
Definition term99 (x0 : nadd) (x1 : nat) (x2 : nat) := and (Peano.le (dist (@pair nat nat (dest_nadd x0 (Nat.add x1 (NUMERAL 0))) (dest_nadd x0 x1))) (Nat.mul x2 (NUMERAL 0))).
Definition term115 (x0 : nadd) (x1 : nat) (x2 : nat) := imp ((Peano.le (dist (@pair nat nat (dest_nadd x0 (Nat.add x1 (NUMERAL 0))) (dest_nadd x0 x1))) (Nat.mul x2 (NUMERAL 0))) /\ (forall y0 : nat, (Peano.le (dist (@pair nat nat (dest_nadd x0 (Nat.add x1 y0)) (dest_nadd x0 x1))) (Nat.mul x2 y0)) -> Peano.le (dist (@pair nat nat (dest_nadd x0 (Nat.add x1 (S y0))) (dest_nadd x0 x1))) (Nat.mul x2 (S y0)))).
Definition term175 (x0 : nadd) (x1 : nat) (x2 : nat) := Peano.le (dist (@pair nat nat (dest_nadd x0 (S x1)) (dest_nadd x0 x1))) x2.
Definition term26 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (Nat.add x1 x2).
Definition term104 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => Peano.le (dist (@pair nat nat (dest_nadd x0 (Nat.add x1 y0)) (dest_nadd x0 x1))) (Nat.mul x2 y0)) (S x3).
Definition term63 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (dist (@pair nat nat x0 x1)) x2.
Definition term127 (x0 : nadd) (x1 : nat) := Peano.le (dist (@pair nat nat (dest_nadd x0 (Nat.add x1 (NUMERAL 0))) (dest_nadd x0 x1))).
Definition term128 := Peano.le (NUMERAL 0).
Definition term122 (x0 : nadd) (x1 : nat) := @pair nat nat (dest_nadd x0 x1).
Definition term111 (x0 : nadd) (x1 : nat) (x2 : nat) := forall y0 : nat, (Peano.le (dist (@pair nat nat (dest_nadd x0 (Nat.add x1 y0)) (dest_nadd x0 x1))) (Nat.mul x2 y0)) -> Peano.le (dist (@pair nat nat (dest_nadd x0 (Nat.add x1 (S y0))) (dest_nadd x0 x1))) (Nat.mul x2 (S y0)).
Definition term164 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x0 (NUMERAL (BIT1 0))) (Nat.mul x0 x1).
Definition term135 (x0 : nat) (x1 : nadd) (x2 : nat) := @pair nat nat (dest_nadd x1 (Nat.add x2 (S x0))) (dest_nadd x1 x2).
Definition term4 := forall y0 : nat, (Nat.add y0 (NUMERAL (BIT1 0))) = (S y0).
Definition term43 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le x0 y0) -> Peano.le x1 y0.
Definition term144 (x0 : nat) (x1 : nat) := Nat.add (Nat.add x0 x1) (NUMERAL (BIT1 0)).
Definition term67 (x0 : nat) (x1 : nat) (x2 : nat) := (exists y0 : nat, Peano.le (Nat.add (dist (@pair nat nat x0 y0)) (dist (@pair nat nat y0 x1))) x2) -> Peano.le (dist (@pair nat nat x0 x1)) x2.
Definition term1 := fun y0 : nat => (S y0) = (Nat.add y0 (NUMERAL (BIT1 0))).
Definition term143 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := (exists y0 : nat, Peano.le (Nat.add (dist (@pair nat nat (dest_nadd x0 (S (Nat.add x1 x3))) y0)) (dist (@pair nat nat y0 (dest_nadd x0 x1)))) (Nat.mul x2 (S x3))) -> Peano.le (dist (@pair nat nat (dest_nadd x0 (S (Nat.add x1 x3))) (dest_nadd x0 x1))) (Nat.mul x2 (S x3)).
Definition term77 (x0 : nat) := (fun y0 : nat => (dist (@pair nat nat y0 y0)) = (NUMERAL 0)) x0.
Definition term168 := (forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))).
Definition term13 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Peano.le x0 x2) /\ (Peano.le x1 x3)) -> Peano.le (Nat.add x0 x1) (Nat.add x2 x3).
Definition term103 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := imp (Peano.le (dist (@pair nat nat (dest_nadd x0 (Nat.add x1 x3)) (dest_nadd x0 x1))) (Nat.mul x2 x3)).
Definition term159 (x0 : nat) (x1 : nat) := Nat.mul x0 (Nat.add x1 (NUMERAL (BIT1 0))).
Definition term49 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le x0 y0) -> forall y1 : nat, (Peano.le y0 y1) -> Peano.le x0 y1) x1.
Definition term161 := NUMERAL (BIT1 0).
Definition term186 (x0 : nadd) := fun y0 : nat => forall y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 (Nat.add y1 y2)) (dest_nadd x0 y1))) (Nat.mul y0 y2).
Definition term60 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => (Peano.le (Nat.add (dist (@pair nat nat x1 x0)) (dist (@pair nat nat x0 x2))) y0) -> Peano.le (dist (@pair nat nat x1 x2)) y0) x3.
Definition term97 (x0 : nadd) (x1 : nat) (x2 : nat) := Peano.le (dist (@pair nat nat (dest_nadd x0 (Nat.add x1 (NUMERAL 0))) (dest_nadd x0 x1))) (Nat.mul x2 (NUMERAL 0)).
Definition term126 (x0 : nadd) (x1 : nat) := dist (@pair nat nat (dest_nadd x0 x1) (dest_nadd x0 x1)).
Definition term32 (x0 : nat) (x1 : nat) := forall y0 : nat, Peano.le (dist (@pair nat nat x0 y0)) (Nat.add (dist (@pair nat nat x0 x1)) (dist (@pair nat nat x1 y0))).
Definition term83 (x0 : nat) := forall y0 : nat, (Nat.add x0 (S y0)) = (S (Nat.add x0 y0)).
