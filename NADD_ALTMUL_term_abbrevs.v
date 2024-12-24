Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term156 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul (Nat.mul x0 x1) x2).
Definition term175 (x0 : nadd) (x1 : nadd) := (exists y0 : nat, exists y1 : nat, forall y2 : nat, Peano.le (dest_nadd x1 y2) (Nat.add (Nat.mul y0 y2) y1)) -> exists y0 : nat, exists y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (Nat.mul y2 (dest_nadd x0 (dest_nadd x1 y2))) (Nat.mul (dest_nadd x0 y2) (dest_nadd x1 y2)))) (Nat.add (Nat.mul y0 y2) y1).
Definition term66 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.mul x1 (Nat.add x0 y0)) = (Nat.add (Nat.mul x1 x0) (Nat.mul x1 y0))) x2.
Definition term162 (x0 : nat) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat) := (x0 = (NUMERAL 0)) \/ (Peano.le (dest_nadd x1 x3) (Nat.add (Nat.mul x2 x3) x4)).
Definition term76 (x0 : nat) (x1 : nat) := exists y0 : nat, (Peano.le x0 y0) /\ (Peano.le y0 x1).
Definition term123 (x0 : nat) (x1 : nat) := Nat.mul (Nat.add (Nat.mul x0 (NUMERAL (BIT1 0))) (Nat.mul x0 x1)).
Definition term167 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : nat) := fun y0 : nat => (Peano.le (dist (@pair nat nat (Nat.mul x3 (dest_nadd x1 (dest_nadd x0 x3))) (Nat.mul (dest_nadd x0 x3) (dest_nadd x1 x3)))) y0) /\ (Peano.le y0 (Nat.add (Nat.mul (Nat.mul x4 (Nat.add (NUMERAL (BIT1 0)) x2)) x3) (Nat.mul x4 x5))).
Definition term174 (x0 : nadd) := fun y0 : nat => exists y1 : nat, forall y2 : nat, Peano.le (dest_nadd x0 y2) (Nat.add (Nat.mul y0 y2) y1).
Definition term172 (x0 : nadd) (x1 : nadd) := fun y0 : nat => exists y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (Nat.mul y2 (dest_nadd x0 (dest_nadd x1 y2))) (Nat.mul (dest_nadd x0 y2) (dest_nadd x1 y2)))) (Nat.add (Nat.mul y0 y2) y1).
Definition term159 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.mul x0 (Nat.add (Nat.mul x1 x2) x3).
Definition term169 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) := exists y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (Nat.mul y1 (dest_nadd x0 (dest_nadd x1 y1))) (Nat.mul (dest_nadd x0 y1) (dest_nadd x1 y1)))) (Nat.add (Nat.mul (Nat.mul x2 (Nat.add (NUMERAL (BIT1 0)) x3)) y1) y0).
Definition term92 (x0 : nadd) (x1 : nat) := exists y0 : nat, forall y1 : nat, Peano.le (dest_nadd x0 y1) (Nat.add (Nat.mul x1 y1) y0).
Definition term90 (x0 : nadd) := exists y0 : nat, forall y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (Nat.mul y1 (dest_nadd x0 y2)) (Nat.mul y2 (dest_nadd x0 y1)))) (Nat.mul y0 (Nat.add y1 y2)).
Definition term157 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x0 (Nat.mul x1 x2)).
Definition term17 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.add (Nat.mul x0 x1) (Nat.mul x0 y0)) = (Nat.mul x0 (Nat.add x1 y0)).
Definition term52 := (forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))))).
Definition term151 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y2)) = (Nat.mul y0 (Nat.add y1 y2))) x0.
Definition term148 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.mul (Nat.mul y0 y1) y2) = (Nat.mul y0 (Nat.mul y1 y2))) x0.
Definition term141 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le (Nat.mul y0 y1) (Nat.mul y0 y2)) = ((y0 = (NUMERAL 0)) \/ (Peano.le y1 y2))) x0.
Definition term68 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) x0.
Definition term64 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.mul y0 (Nat.add y1 y2)) = (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y2))) x0.
Definition term57 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.mul (Nat.add y0 y1) y2) = (Nat.add (Nat.mul y0 y2) (Nat.mul y1 y2))) x0.
Definition term48 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.add (Nat.add y0 y1) y2) = (Nat.add y0 (Nat.add y1 y2))) x0.
Definition term42 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le (Nat.add y0 y1) (Nat.add y0 y2)) = (Peano.le y1 y2)) x0.
Definition term46 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.le (Nat.add x0 x1) (Nat.add x0 y0)) = (Peano.le x1 y0)) x2.
Definition term150 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.mul (Nat.mul x0 x1) y0) = (Nat.mul x0 (Nat.mul x1 y0))) x2.
Definition term81 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> forall y0 : nat, forall y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) -> Peano.le y0 y1.
Definition term165 (x0 : nat) := (x0 = (NUMERAL 0)) \/ True.
Definition term147 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = (NUMERAL 0)) \/ (Peano.le x1 x2).
Definition term136 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.add (Nat.mul (Nat.mul x2 x0) x1) (Nat.mul x2 x3).
Definition term178 := forall y0 : nadd, forall y1 : nadd, exists y2 : nat, exists y3 : nat, forall y4 : nat, Peano.le (dist (@pair nat nat (Nat.mul y4 (dest_nadd y0 (dest_nadd y1 y4))) (Nat.mul (dest_nadd y0 y4) (dest_nadd y1 y4)))) (Nat.add (Nat.mul y2 y4) y3).
Definition term19 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.add (Nat.mul x0 x1) (Nat.mul x0 y0)) = (Nat.mul x0 (Nat.add x1 y0)).
Definition term135 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x0 x1).
Definition term119 (x0 : nat) (x1 : nat) := Nat.mul x0 (Nat.add (NUMERAL (BIT1 0)) x1).
Definition term93 (x0 : nadd) (x1 : nat) (x2 : nat) := forall y0 : nat, Peano.le (dest_nadd x0 y0) (Nat.add (Nat.mul x1 y0) x2).
Definition term45 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le (Nat.add x0 x1) (Nat.add x0 y0)) = (Peano.le x1 y0).
Definition term75 (x0 : nat) (x1 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> Peano.le x0 x1.
Definition term137 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.add (Nat.mul x2 x1) (Nat.add (Nat.mul (Nat.mul x2 x0) x1) (Nat.mul x2 x3)).
Definition term130 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := Peano.le (Nat.add (Nat.mul x3 x2) (Nat.mul x3 (dest_nadd x0 x2))) (Nat.add (Nat.add (Nat.mul (Nat.mul x3 (NUMERAL (BIT1 0))) x2) (Nat.mul (Nat.mul x3 x1) x2)) (Nat.mul x3 x4)).
Definition term128 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.add (Nat.mul (Nat.mul x0 (NUMERAL (BIT1 0))) x2) (Nat.mul (Nat.mul x0 x1) x2)).
Definition term79 (x0 : nat) := forall y0 : nat, (exists y1 : nat, (Peano.le x0 y1) /\ (Peano.le y1 y0)) -> Peano.le x0 y0.
Definition term47 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.add x1 x0) (Nat.add x1 x2).
Definition term55 (x0 : nat) := (fun y0 : nat => (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) x0.
Definition term29 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.add x0 x1) x2.
Definition term154 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => Peano.le (dest_nadd x0 y0) (Nat.add (Nat.mul x1 y0) x2)) x3.
Definition term153 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.add (Nat.mul x0 x1) (Nat.mul x0 y0)) = (Nat.mul x0 (Nat.add x1 y0))) x2.
Definition term30 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.add x0 (Nat.add x1 y0)) = (Nat.add (Nat.add x0 x1) y0).
Definition term72 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Peano.le x1 x0) /\ (Peano.le x0 y0)) -> Peano.le x1 y0) x2.
Definition term118 (x0 : nat) (x1 : nadd) (x2 : nat) := Peano.le (Nat.add (Nat.mul x0 x2) (Nat.mul x0 (dest_nadd x1 x2))).
Definition term116 (x0 : nat) (x1 : nadd) (x2 : nat) := Nat.add (Nat.mul x0 x2) (Nat.mul x0 (dest_nadd x1 x2)).
Definition term101 (x0 : nadd) (x1 : nadd) (x2 : nat) := Peano.le (dist (@pair nat nat (Nat.mul x2 (dest_nadd x1 (dest_nadd x0 x2))) (Nat.mul (dest_nadd x0 x2) (dest_nadd x1 x2)))).
Definition term100 (x0 : nadd) (x1 : nadd) (x2 : nat) := Peano.le (dist (@pair nat nat (Nat.mul x2 (dest_nadd x0 (dest_nadd x1 x2))) (Nat.mul (dest_nadd x0 x2) (dest_nadd x1 x2)))).
Definition term32 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.add x0 (Nat.add x1 y0)) = (Nat.add (Nat.add x0 x1) y0).
Definition term4 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.mul x0 (Nat.mul x1 y0)) = (Nat.mul (Nat.mul x0 x1) y0).
Definition term140 (x0 : nat) (x1 : nadd) (x2 : nat) := Nat.mul x0 (dest_nadd x1 x2).
Definition term104 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : nat) := Peano.le (dist (@pair nat nat (Nat.mul x3 (dest_nadd x1 (dest_nadd x0 x3))) (Nat.mul (dest_nadd x0 x3) (dest_nadd x1 x3)))) (Nat.add (Nat.mul (Nat.mul x4 (Nat.add (NUMERAL (BIT1 0)) x2)) x3) (Nat.mul x4 x5)).
Definition term103 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : nat) := Peano.le (dist (@pair nat nat (Nat.mul x3 (dest_nadd x0 (dest_nadd x1 x3))) (Nat.mul (dest_nadd x0 x3) (dest_nadd x1 x3)))) (Nat.add (Nat.mul (Nat.mul x4 (Nat.add (NUMERAL (BIT1 0)) x2)) x3) (Nat.mul x4 x5)).
Definition term152 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y1)) = (Nat.mul x0 (Nat.add y0 y1))) x1.
Definition term149 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul (Nat.mul x0 y0) y1) = (Nat.mul x0 (Nat.mul y0 y1))) x1.
Definition term143 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (Nat.mul x0 y0) (Nat.mul x0 y1)) = ((x0 = (NUMERAL 0)) \/ (Peano.le y0 y1))) x1.
Definition term70 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 y1)) -> Peano.le x0 y1) x1.
Definition term65 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul x0 (Nat.add y0 y1)) = (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y1))) x1.
Definition term59 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul (Nat.add x0 y0) y1) = (Nat.add (Nat.mul x0 y1) (Nat.mul y0 y1))) x1.
Definition term49 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add (Nat.add x0 y0) y1) = (Nat.add x0 (Nat.add y0 y1))) x1.
Definition term44 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (Nat.add x0 y0) (Nat.add x0 y1)) = (Peano.le y0 y1)) x1.
Definition term124 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.mul x0 (Nat.add (NUMERAL (BIT1 0)) x1)) x2.
Definition term126 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul (Nat.mul x0 (NUMERAL (BIT1 0))) x2) (Nat.mul (Nat.mul x0 x1) x2).
Definition term173 (x0 : nadd) (x1 : nat) := fun y0 : nat => forall y1 : nat, Peano.le (dest_nadd x0 y1) (Nat.add (Nat.mul x1 y1) y0).
Definition term170 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) := fun y0 : nat => forall y1 : nat, Peano.le (dist (@pair nat nat (Nat.mul y1 (dest_nadd x0 (dest_nadd x1 y1))) (Nat.mul (dest_nadd x0 y1) (dest_nadd x1 y1)))) (Nat.add (Nat.mul (Nat.mul x2 (Nat.add (NUMERAL (BIT1 0)) x3)) y1) y0).
Definition term34 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Nat.add x0 (Nat.add y0 y1)) = (Nat.add (Nat.add x0 y0) y1).
Definition term6 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Nat.mul x0 (Nat.mul y0 y1)) = (Nat.mul (Nat.mul x0 y0) y1).
Definition term113 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : nat) := (Peano.le (dist (@pair nat nat (Nat.mul x3 (dest_nadd x0 (dest_nadd x1 x3))) (Nat.mul (dest_nadd x1 x3) (dest_nadd x0 x3)))) (Nat.mul x4 (Nat.add x3 (dest_nadd x1 x3)))) /\ (Peano.le (Nat.mul x4 (Nat.add x3 (dest_nadd x1 x3))) (Nat.add (Nat.mul (Nat.mul x4 (Nat.add (NUMERAL (BIT1 0)) x2)) x3) (Nat.mul x4 x5))).
Definition term54 := forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0.
Definition term95 (x0 : nadd) (x1 : nadd) (x2 : nat) := @pair nat nat (Nat.mul x2 (dest_nadd x0 (dest_nadd x1 x2))).
Definition term73 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.le x1 x0) /\ (Peano.le x0 x2)) -> Peano.le x1 x2.
Definition term134 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul (Nat.mul x0 (NUMERAL (BIT1 0))) x1).
Definition term15 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x1 x0) (Nat.mul x1 x2).
Definition term1 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.mul x0 x1) x2.
Definition term107 (x0 : nadd) (x1 : nat) (x2 : nat) := forall y0 : nat, Peano.le (dist (@pair nat nat (Nat.mul x2 (dest_nadd x0 y0)) (Nat.mul y0 (dest_nadd x0 x2)))) (Nat.mul x1 (Nat.add x2 y0)).
Definition term164 (x0 : nat) := or (x0 = (NUMERAL 0)).
Definition term161 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := Peano.le (Nat.mul x1 (dest_nadd x0 x3)) (Nat.mul x1 (Nat.add (Nat.mul x2 x3) x4)).
Definition term142 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le (Nat.mul x0 y0) (Nat.mul x0 y1)) = ((x0 = (NUMERAL 0)) \/ (Peano.le y0 y1)).
Definition term91 (x0 : nadd) (x1 : nat) := forall y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (Nat.mul y0 (dest_nadd x0 y1)) (Nat.mul y1 (dest_nadd x0 y0)))) (Nat.mul x1 (Nat.add y0 y1)).
Definition term80 := forall y0 : nat, forall y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) -> Peano.le y0 y1.
Definition term69 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 y1)) -> Peano.le x0 y1.
Definition term67 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2.
Definition term58 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.mul (Nat.add x0 y0) y1) = (Nat.add (Nat.mul x0 y1) (Nat.mul y0 y1)).
Definition term43 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add x0 y0) (Nat.add x0 y1)) = (Peano.le y0 y1).
Definition term41 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.add (Nat.add y0 y1) y2) = (Nat.add y0 (Nat.add y1 y2)).
Definition term40 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.add y0 (Nat.add y1 y2)) = (Nat.add (Nat.add y0 y1) y2).
Definition term37 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add x0 y0) y1) = (Nat.add x0 (Nat.add y0 y1)).
Definition term36 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.add x0 (Nat.add y0 y1)) = (Nat.add (Nat.add x0 y0) y1).
Definition term27 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y2)) = (Nat.mul y0 (Nat.add y1 y2)).
Definition term26 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.mul y0 (Nat.add y1 y2)) = (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y2)).
Definition term23 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y1)) = (Nat.mul x0 (Nat.add y0 y1)).
Definition term22 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.mul x0 (Nat.add y0 y1)) = (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y1)).
Definition term13 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.mul (Nat.mul y0 y1) y2) = (Nat.mul y0 (Nat.mul y1 y2)).
Definition term12 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.mul y0 (Nat.mul y1 y2)) = (Nat.mul (Nat.mul y0 y1) y2).
Definition term9 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.mul (Nat.mul x0 y0) y1) = (Nat.mul x0 (Nat.mul y0 y1)).
Definition term8 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.mul x0 (Nat.mul y0 y1)) = (Nat.mul (Nat.mul x0 y0) y1).
Definition term129 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.add (Nat.add (Nat.mul (Nat.mul x2 (NUMERAL (BIT1 0))) x1) (Nat.mul (Nat.mul x2 x0) x1)) (Nat.mul x2 x3).
Definition term158 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.add (Nat.mul x2 (Nat.mul x0 x1)) (Nat.mul x2 x3).
Definition term106 (x0 : nadd) (x1 : nat) (x2 : nat) := (fun y0 : nat => forall y1 : nat, Peano.le (dist (@pair nat nat (Nat.mul y0 (dest_nadd x0 y1)) (Nat.mul y1 (dest_nadd x0 y0)))) (Nat.mul x1 (Nat.add y0 y1))) x2.
Definition term122 (x0 : nat) (x1 : nat) := Nat.mul (Nat.mul x0 (Nat.add (NUMERAL (BIT1 0)) x1)).
Definition term132 (x0 : nat) (x1 : nat) := Nat.mul (Nat.mul x0 (NUMERAL (BIT1 0))) x1.
Definition term108 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => Peano.le (dist (@pair nat nat (Nat.mul x2 (dest_nadd x0 y0)) (Nat.mul y0 (dest_nadd x0 x2)))) (Nat.mul x1 (Nat.add x2 y0))) x3.
Definition term61 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.mul (Nat.add x0 x1) y0) = (Nat.add (Nat.mul x0 y0) (Nat.mul x1 y0))) x2.
Definition term114 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := True /\ (Peano.le (Nat.mul x3 (Nat.add x2 (dest_nadd x0 x2))) (Nat.add (Nat.mul (Nat.mul x3 (Nat.add (NUMERAL (BIT1 0)) x1)) x2) (Nat.mul x3 x4))).
Definition term168 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat) := forall y0 : nat, Peano.le (dist (@pair nat nat (Nat.mul y0 (dest_nadd x0 (dest_nadd x1 y0))) (Nat.mul (dest_nadd x0 y0) (dest_nadd x1 y0)))) (Nat.add (Nat.mul (Nat.mul x3 (Nat.add (NUMERAL (BIT1 0)) x2)) y0) (Nat.mul x3 x4)).
Definition term133 (x0 : nat) := Nat.mul (Nat.mul x0 (NUMERAL (BIT1 0))).
Definition term160 (x0 : nat) (x1 : nadd) (x2 : nat) := Peano.le (Nat.mul x0 (dest_nadd x1 x2)).
Definition term111 (x0 : nadd) (x1 : nat) (x2 : nadd) (x3 : nat) := and (Peano.le (dist (@pair nat nat (Nat.mul x3 (dest_nadd x0 (dest_nadd x2 x3))) (Nat.mul (dest_nadd x2 x3) (dest_nadd x0 x3)))) (Nat.mul x1 (Nat.add x3 (dest_nadd x2 x3)))).
Definition term112 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := Peano.le (Nat.mul x3 (Nat.add x2 (dest_nadd x0 x2))) (Nat.add (Nat.mul (Nat.mul x3 (Nat.add (NUMERAL (BIT1 0)) x1)) x2) (Nat.mul x3 x4)).
Definition term62 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.add x0 x1) x2.
Definition term63 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x0 x2) (Nat.mul x1 x2).
Definition term144 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le (Nat.mul x0 x1) (Nat.mul x0 y0)) = ((x0 = (NUMERAL 0)) \/ (Peano.le x1 y0)).
Definition term18 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.mul x1 (Nat.add x0 y0)) = (Nat.add (Nat.mul x1 x0) (Nat.mul x1 y0)).
Definition term115 (x0 : nat) (x1 : nadd) (x2 : nat) := Nat.mul x0 (Nat.add x2 (dest_nadd x1 x2)).
Definition term85 (x0 : nat) := forall y0 : nat, (Nat.mul x0 y0) = (Nat.mul y0 x0).
Definition term146 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul x1 x0) (Nat.mul x1 x2).
Definition term50 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.add (Nat.add x0 x1) y0) = (Nat.add x0 (Nat.add x1 y0))) x2.
Definition term94 (x0 : nadd) (x1 : nadd) (x2 : nat) := Nat.mul (dest_nadd x0 x2) (dest_nadd x1 x2).
Definition term86 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.mul x0 y0) = (Nat.mul y0 x0)) x1.
Definition term166 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : nat) := exists y0 : nat, (Peano.le (dist (@pair nat nat (Nat.mul x3 (dest_nadd x1 (dest_nadd x0 x3))) (Nat.mul (dest_nadd x0 x3) (dest_nadd x1 x3)))) y0) /\ (Peano.le y0 (Nat.add (Nat.mul (Nat.mul x4 (Nat.add (NUMERAL (BIT1 0)) x2)) x3) (Nat.mul x4 x5))).
Definition term53 := (forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))).
Definition term71 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Peano.le x1 x0) /\ (Peano.le x0 y0)) -> Peano.le x1 y0.
Definition term177 (x0 : nadd) := forall y0 : nadd, exists y1 : nat, exists y2 : nat, forall y3 : nat, Peano.le (dist (@pair nat nat (Nat.mul y3 (dest_nadd x0 (dest_nadd y0 y3))) (Nat.mul (dest_nadd x0 y3) (dest_nadd y0 y3)))) (Nat.add (Nat.mul y1 y3) y2).
Definition term105 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : nat) := (exists y0 : nat, (Peano.le (dist (@pair nat nat (Nat.mul x3 (dest_nadd x1 (dest_nadd x0 x3))) (Nat.mul (dest_nadd x0 x3) (dest_nadd x1 x3)))) y0) /\ (Peano.le y0 (Nat.add (Nat.mul (Nat.mul x4 (Nat.add (NUMERAL (BIT1 0)) x2)) x3) (Nat.mul x4 x5)))) -> Peano.le (dist (@pair nat nat (Nat.mul x3 (dest_nadd x1 (dest_nadd x0 x3))) (Nat.mul (dest_nadd x0 x3) (dest_nadd x1 x3)))) (Nat.add (Nat.mul (Nat.mul x4 (Nat.add (NUMERAL (BIT1 0)) x2)) x3) (Nat.mul x4 x5)).
Definition term28 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add x0 (Nat.add x1 x2).
Definition term3 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.mul (Nat.mul x0 x1) y0) = (Nat.mul x0 (Nat.mul x1 y0)).
Definition term56 (x0 : nat) := Nat.mul x0 (NUMERAL (BIT1 0)).
Definition term84 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) x0.
Definition term82 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) -> Peano.le y0 y1) x0.
Definition term110 (x0 : nadd) (x1 : nat) (x2 : nadd) (x3 : nat) := Peano.le (dist (@pair nat nat (Nat.mul x3 (dest_nadd x0 (dest_nadd x2 x3))) (Nat.mul (dest_nadd x2 x3) (dest_nadd x0 x3)))) (Nat.mul x1 (Nat.add x3 (dest_nadd x2 x3))).
Definition term16 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.mul x1 (Nat.add x0 y0)) = (Nat.add (Nat.mul x1 x0) (Nat.mul x1 y0)).
Definition term74 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x1) /\ (Peano.le x1 x2).
Definition term0 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (Nat.mul x1 x2).
Definition term131 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.add (Nat.mul (Nat.mul x2 (NUMERAL (BIT1 0))) x1) (Nat.add (Nat.mul (Nat.mul x2 x0) x1) (Nat.mul x2 x3)).
Definition term97 (x0 : nadd) (x1 : nadd) (x2 : nat) := @pair nat nat (Nat.mul x2 (dest_nadd x1 (dest_nadd x0 x2))) (Nat.mul (dest_nadd x0 x2) (dest_nadd x1 x2)).
Definition term96 (x0 : nadd) (x1 : nadd) (x2 : nat) := @pair nat nat (Nat.mul x2 (dest_nadd x0 (dest_nadd x1 x2))) (Nat.mul (dest_nadd x0 x2) (dest_nadd x1 x2)).
Definition term125 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.add (Nat.mul x0 (NUMERAL (BIT1 0))) (Nat.mul x0 x1)) x2.
Definition term145 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.le (Nat.mul x0 x1) (Nat.mul x0 y0)) = ((x0 = (NUMERAL 0)) \/ (Peano.le x1 y0))) x2.
Definition term60 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.mul (Nat.add x0 x1) y0) = (Nat.add (Nat.mul x0 y0) (Nat.mul x1 y0)).
Definition term78 (x0 : nat) (x1 : nat) := (exists y0 : nat, (Peano.le x0 y0) /\ (Peano.le y0 x1)) -> Peano.le x0 x1.
Definition term117 (x0 : nat) (x1 : nadd) (x2 : nat) := Peano.le (Nat.mul x0 (Nat.add x2 (dest_nadd x1 x2))).
Definition term102 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.add (Nat.mul (Nat.mul x2 (Nat.add (NUMERAL (BIT1 0)) x0)) x1) (Nat.mul x2 x3).
Definition term155 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (dest_nadd x0 x2) (Nat.add (Nat.mul x1 x2) x3).
Definition term89 (x0 : nadd) := (fun y0 : nadd => exists y1 : nat, forall y2 : nat, forall y3 : nat, Peano.le (dist (@pair nat nat (Nat.mul y2 (dest_nadd y0 y3)) (Nat.mul y3 (dest_nadd y0 y2)))) (Nat.mul y1 (Nat.add y2 y3))) x0.
Definition term87 (x0 : nadd) := (fun y0 : nadd => exists y1 : nat, exists y2 : nat, forall y3 : nat, Peano.le (dest_nadd y0 y3) (Nat.add (Nat.mul y1 y3) y2)) x0.
Definition term14 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (Nat.add x1 x2).
Definition term33 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.add (Nat.add x0 x1) y0) = (Nat.add x0 (Nat.add x1 y0)).
Definition term5 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.mul (Nat.mul x0 x1) y0) = (Nat.mul x0 (Nat.mul x1 y0)).
Definition term99 (x0 : nadd) (x1 : nadd) (x2 : nat) := dist (@pair nat nat (Nat.mul x2 (dest_nadd x1 (dest_nadd x0 x2))) (Nat.mul (dest_nadd x0 x2) (dest_nadd x1 x2))).
Definition term98 (x0 : nadd) (x1 : nadd) (x2 : nat) := dist (@pair nat nat (Nat.mul x2 (dest_nadd x0 (dest_nadd x1 x2))) (Nat.mul (dest_nadd x0 x2) (dest_nadd x1 x2))).
Definition term77 (x0 : nat) (x1 : nat) := fun y0 : nat => (Peano.le x0 y0) /\ (Peano.le y0 x1).
Definition term127 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul (Nat.mul x0 (Nat.add (NUMERAL (BIT1 0)) x1)) x2).
Definition term171 (x0 : nadd) (x1 : nadd) := exists y0 : nat, exists y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (Nat.mul y2 (dest_nadd x0 (dest_nadd x1 y2))) (Nat.mul (dest_nadd x0 y2) (dest_nadd x1 y2)))) (Nat.add (Nat.mul y0 y2) y1).
Definition term88 (x0 : nadd) := exists y0 : nat, exists y1 : nat, forall y2 : nat, Peano.le (dest_nadd x0 y2) (Nat.add (Nat.mul y0 y2) y1).
Definition term120 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x0 (NUMERAL (BIT1 0))) (Nat.mul x0 x1).
Definition term163 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x0 x1) x2.
Definition term31 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.add (Nat.add x0 x1) y0) = (Nat.add x0 (Nat.add x1 y0)).
Definition term2 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.mul x0 (Nat.mul x1 y0)) = (Nat.mul (Nat.mul x0 x1) y0).
Definition term51 := (forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))).
Definition term139 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := Peano.le (Nat.mul x3 (dest_nadd x0 x2)) (Nat.add (Nat.mul (Nat.mul x3 x1) x2) (Nat.mul x3 x4)).
Definition term35 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Nat.add (Nat.add x0 y0) y1) = (Nat.add x0 (Nat.add y0 y1)).
Definition term21 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y1)) = (Nat.mul x0 (Nat.add y0 y1)).
Definition term20 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Nat.mul x0 (Nat.add y0 y1)) = (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y1)).
Definition term7 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Nat.mul (Nat.mul x0 y0) y1) = (Nat.mul x0 (Nat.mul y0 y1)).
Definition term121 := NUMERAL (BIT1 0).
Definition term176 (x0 : nadd) := fun y0 : nat => forall y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (Nat.mul y1 (dest_nadd x0 y2)) (Nat.mul y2 (dest_nadd x0 y1)))) (Nat.mul y0 (Nat.add y1 y2)).
Definition term39 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.add (Nat.add y0 y1) y2) = (Nat.add y0 (Nat.add y1 y2)).
Definition term38 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.add y0 (Nat.add y1 y2)) = (Nat.add (Nat.add y0 y1) y2).
Definition term25 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y2)) = (Nat.mul y0 (Nat.add y1 y2)).
Definition term24 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.mul y0 (Nat.add y1 y2)) = (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y2)).
Definition term11 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.mul (Nat.mul y0 y1) y2) = (Nat.mul y0 (Nat.mul y1 y2)).
Definition term10 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.mul y0 (Nat.mul y1 y2)) = (Nat.mul (Nat.mul y0 y1) y2).
Definition term138 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := Peano.le (Nat.add (Nat.mul x3 x2) (Nat.mul x3 (dest_nadd x0 x2))) (Nat.add (Nat.mul x3 x2) (Nat.add (Nat.mul (Nat.mul x3 x1) x2) (Nat.mul x3 x4))).
Definition term83 (x0 : nat) (x1 : nat) := (fun y0 : nat => (exists y1 : nat, (Peano.le x0 y1) /\ (Peano.le y1 y0)) -> Peano.le x0 y0) x1.
Definition term109 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (dist (@pair nat nat (Nat.mul x2 (dest_nadd x0 x3)) (Nat.mul x3 (dest_nadd x0 x2)))) (Nat.mul x1 (Nat.add x2 x3)).
