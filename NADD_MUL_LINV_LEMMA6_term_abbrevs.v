Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term160 (x0 : nadd) := (exists y0 : nat, exists y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y1 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.mul (Nat.mul (dest_nadd x0 y2) (dest_nadd x0 y3)) (dist (@pair nat nat (Nat.mul y2 (nadd_rinv x0 y3)) (Nat.mul y3 (nadd_rinv x0 y2))))) (Nat.mul y0 (Nat.mul (Nat.mul y2 y3) (Nat.add y2 y3)))) -> exists y0 : nat, exists y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y1 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.mul (Nat.mul y2 y3) (dist (@pair nat nat (Nat.mul y2 (nadd_rinv x0 y3)) (Nat.mul y3 (nadd_rinv x0 y2))))) (Nat.mul y0 (Nat.mul (Nat.mul y2 y3) (Nat.add y2 y3))).
Definition term157 (x0 : nadd) := (exists y0 : nat, exists y1 : nat, forall y2 : nat, (Peano.le y1 y2) -> Peano.le y2 (Nat.mul y0 (dest_nadd x0 y2))) -> exists y0 : nat, exists y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y1 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.mul (Nat.mul y2 y3) (dist (@pair nat nat (Nat.mul y2 (nadd_rinv x0 y3)) (Nat.mul y3 (nadd_rinv x0 y2))))) (Nat.mul y0 (Nat.mul (Nat.mul y2 y3) (Nat.add y2 y3))).
Definition term145 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := fun y0 : nat => (Peano.le (Nat.mul (Nat.mul x3 x4) (dist (@pair nat nat (Nat.mul x3 (nadd_rinv x0 x4)) (Nat.mul x4 (nadd_rinv x0 x3))))) y0) /\ (Peano.le y0 (Nat.mul (Nat.mul x1 (Nat.mul x2 x2)) (Nat.mul (Nat.mul x3 x4) (Nat.add x3 x4)))).
Definition term9 (x0 : nat) (x1 : nat) := exists y0 : nat, (Peano.le x0 y0) /\ (Peano.le y0 x1).
Definition term88 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := (exists y0 : nat, (Peano.le (Nat.mul (Nat.mul x3 x4) (dist (@pair nat nat (Nat.mul x3 (nadd_rinv x0 x4)) (Nat.mul x4 (nadd_rinv x0 x3))))) y0) /\ (Peano.le y0 (Nat.mul (Nat.mul x1 (Nat.mul x2 x2)) (Nat.mul (Nat.mul x3 x4) (Nat.add x3 x4))))) -> Peano.le (Nat.mul (Nat.mul x3 x4) (dist (@pair nat nat (Nat.mul x3 (nadd_rinv x0 x4)) (Nat.mul x4 (nadd_rinv x0 x3))))) (Nat.mul (Nat.mul x1 (Nat.mul x2 x2)) (Nat.mul (Nat.mul x3 x4) (Nat.add x3 x4))).
Definition term159 (x0 : nadd) := fun y0 : nat => exists y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y1 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.mul (Nat.mul (dest_nadd x0 y2) (dest_nadd x0 y3)) (dist (@pair nat nat (Nat.mul y2 (nadd_rinv x0 y3)) (Nat.mul y3 (nadd_rinv x0 y2))))) (Nat.mul y0 (Nat.mul (Nat.mul y2 y3) (Nat.add y2 y3))).
Definition term156 (x0 : nadd) := fun y0 : nat => exists y1 : nat, forall y2 : nat, (Peano.le y1 y2) -> Peano.le y2 (Nat.mul y0 (dest_nadd x0 y2)).
Definition term153 (x0 : nadd) := fun y0 : nat => exists y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y1 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.mul (Nat.mul y2 y3) (dist (@pair nat nat (Nat.mul y2 (nadd_rinv x0 y3)) (Nat.mul y3 (nadd_rinv x0 y2))))) (Nat.mul y0 (Nat.mul (Nat.mul y2 y3) (Nat.add y2 y3))).
Definition term134 (x0 : nat) (x1 : nat) := and (Peano.le x1 (Nat.add x0 x1)).
Definition term30 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := Nat.mul (Nat.mul x0 x1) (Nat.mul (Nat.mul x2 x3) x4).
Definition term150 (x0 : nadd) (x1 : nat) (x2 : nat) := exists y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y0 y2)) -> Peano.le (Nat.mul (Nat.mul y1 y2) (dist (@pair nat nat (Nat.mul y1 (nadd_rinv x0 y2)) (Nat.mul y2 (nadd_rinv x0 y1))))) (Nat.mul (Nat.mul x1 (Nat.mul x2 x2)) (Nat.mul (Nat.mul y1 y2) (Nat.add y1 y2))).
Definition term84 (x0 : nat) (x1 : nadd) := exists y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> Peano.le y1 (Nat.mul x0 (dest_nadd x1 y1)).
Definition term81 (x0 : nadd) (x1 : nat) := exists y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y0 y2)) -> Peano.le (Nat.mul (Nat.mul (dest_nadd x0 y1) (dest_nadd x0 y2)) (dist (@pair nat nat (Nat.mul y1 (nadd_rinv x0 y2)) (Nat.mul y2 (nadd_rinv x0 y1))))) (Nat.mul x1 (Nat.mul (Nat.mul y1 y2) (Nat.add y1 y2))).
Definition term70 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.mul y0 (Nat.mul y1 y2)) = (Nat.mul (Nat.mul y0 y1) y2)) x0.
Definition term63 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le (Nat.mul y0 y2) (Nat.mul y1 y2)) = ((Peano.le y0 y1) \/ (y2 = (NUMERAL 0)))) x0.
Definition term56 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.mul y0 y1) (Nat.mul y2 y3)) x0.
Definition term41 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y1) /\ (Peano.le y2 y3)) -> Peano.le (Nat.mul y0 y2) (Nat.mul y1 y3)) x0.
Definition term17 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le (Nat.mul y0 y1) (Nat.mul y0 y2)) = ((y0 = (NUMERAL 0)) \/ (Peano.le y1 y2))) x0.
Definition term1 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) x0.
Definition term28 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : nat) := Nat.mul (Nat.mul x0 (Nat.mul x1 x2)) (Nat.mul (Nat.mul x3 x4) x5).
Definition term47 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => ((Peano.le x0 x2) /\ (Peano.le x1 y0)) -> Peano.le (Nat.mul x0 x1) (Nat.mul x2 y0)) x3.
Definition term51 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y1) /\ (Peano.le y2 y3)) -> Peano.le (Nat.mul y0 y2) (Nat.mul y1 y3)) -> Peano.le (Nat.mul x0 x1) (Nat.mul x2 x3).
Definition term129 (x0 : nat) (x1 : nadd) (x2 : nat) := (forall y0 : nat, forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le x0 y1)) -> Peano.le (Nat.mul (Nat.mul (dest_nadd x1 y0) (dest_nadd x1 y1)) (dist (@pair nat nat (Nat.mul y0 (nadd_rinv x1 y1)) (Nat.mul y1 (nadd_rinv x1 y0))))) (Nat.mul x2 (Nat.mul (Nat.mul y0 y1) (Nat.add y0 y1)))) -> forall y0 : nat, forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le x0 y1)) -> Peano.le (Nat.mul (Nat.mul (dest_nadd x1 y0) (dest_nadd x1 y1)) (dist (@pair nat nat (Nat.mul y0 (nadd_rinv x1 y1)) (Nat.mul y1 (nadd_rinv x1 y0))))) (Nat.mul x2 (Nat.mul (Nat.mul y0 y1) (Nat.add y0 y1))).
Definition term55 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y1) /\ (Peano.le y2 y3)) -> Peano.le (Nat.mul y0 y2) (Nat.mul y1 y3)) -> forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.mul y0 y1) (Nat.mul y2 y3).
Definition term14 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> forall y0 : nat, forall y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) -> Peano.le y0 y1.
Definition term38 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : nat) := Nat.mul (Nat.mul x0 x1) (Nat.mul x2 (Nat.mul (Nat.mul x3 x4) x5)).
Definition term23 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = (NUMERAL 0)) \/ (Peano.le x1 x2).
Definition term37 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : nat) := @eq nat (Nat.mul x0 (Nat.mul x1 (Nat.mul x2 (Nat.mul x3 (Nat.mul x4 x5))))).
Definition term32 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.mul x0 (Nat.mul (Nat.mul x1 x2) x3).
Definition term29 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : nat) := Nat.mul x0 (Nat.mul (Nat.mul x1 x2) (Nat.mul (Nat.mul x3 x4) x5)).
Definition term68 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul x0 x2) (Nat.mul x1 x2).
Definition term132 (x0 : nat) (x1 : nat) := (fun y0 : nat => Peano.le y0 (Nat.add x0 y0)) x1.
Definition term74 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.mul x0 (Nat.mul x1 y0)) = (Nat.mul (Nat.mul x0 x1) y0)) x2.
Definition term8 (x0 : nat) (x1 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> Peano.le x0 x1.
Definition term67 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.le (Nat.mul x0 y0) (Nat.mul x1 y0)) = ((Peano.le x0 x1) \/ (y0 = (NUMERAL 0)))) x2.
Definition term143 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := (Peano.le (Nat.mul (Nat.mul x3 x4) (dist (@pair nat nat (Nat.mul x3 (nadd_rinv x0 x4)) (Nat.mul x4 (nadd_rinv x0 x3))))) (Nat.mul (Nat.mul x2 x2) (Nat.mul (Nat.mul (dest_nadd x0 x3) (dest_nadd x0 x4)) (dist (@pair nat nat (Nat.mul x3 (nadd_rinv x0 x4)) (Nat.mul x4 (nadd_rinv x0 x3))))))) /\ (Peano.le (Nat.mul (Nat.mul x2 x2) (Nat.mul (Nat.mul (dest_nadd x0 x3) (dest_nadd x0 x4)) (dist (@pair nat nat (Nat.mul x3 (nadd_rinv x0 x4)) (Nat.mul x4 (nadd_rinv x0 x3)))))) (Nat.mul (Nat.mul x1 (Nat.mul x2 x2)) (Nat.mul (Nat.mul x3 x4) (Nat.add x3 x4)))).
Definition term39 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : nat) := Nat.mul x0 (Nat.mul x1 (Nat.mul x2 (Nat.mul (Nat.mul x3 x4) x5))).
Definition term34 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := Nat.mul x0 (Nat.mul x1 (Nat.mul x2 (Nat.mul x3 x4))).
Definition term12 (x0 : nat) := forall y0 : nat, (exists y1 : nat, (Peano.le x0 y1) /\ (Peano.le y1 y0)) -> Peano.le x0 y0.
Definition term146 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := Peano.le (Nat.mul (Nat.mul x3 x4) (dist (@pair nat nat (Nat.mul x3 (nadd_rinv x0 x4)) (Nat.mul x4 (nadd_rinv x0 x3))))) (Nat.mul (Nat.mul x1 (Nat.mul x2 x2)) (Nat.mul (Nat.mul x3 x4) (Nat.add x3 x4))).
Definition term100 (x0 : nat) (x1 : nadd) (x2 : nat) := Peano.le (Nat.mul (Nat.mul x2 x0) (dist (@pair nat nat (Nat.mul x2 (nadd_rinv x1 x0)) (Nat.mul x0 (nadd_rinv x1 x2))))).
Definition term137 (x0 : nat) := forall y0 : nat, Peano.le x0 (Nat.add x0 y0).
Definition term5 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Peano.le x1 x0) /\ (Peano.le x0 y0)) -> Peano.le x1 y0) x2.
Definition term31 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := Nat.mul x0 (Nat.mul x1 (Nat.mul (Nat.mul x2 x3) x4)).
Definition term92 (x0 : nat) (x1 : nat) (x2 : nadd) (x3 : nat) := Nat.mul (Nat.mul (Nat.mul x0 x0) (Nat.mul (dest_nadd x2 x3) (dest_nadd x2 x1))) (dist (@pair nat nat (Nat.mul x3 (nadd_rinv x2 x1)) (Nat.mul x1 (nadd_rinv x2 x3)))).
Definition term73 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.mul x0 (Nat.mul x1 y0)) = (Nat.mul (Nat.mul x0 x1) y0).
Definition term109 (x0 : nat) (x1 : nadd) (x2 : nat) := Nat.mul x0 (dest_nadd x1 x2).
Definition term147 (x0 : nat) (x1 : nat) (x2 : nadd) (x3 : nat) (x4 : nat) (x5 : nat) (x6 : nat) := ((Peano.le (Nat.add x0 x1) x5) /\ (Peano.le (Nat.add x0 x1) x6)) -> Peano.le (Nat.mul (Nat.mul x5 x6) (dist (@pair nat nat (Nat.mul x5 (nadd_rinv x2 x6)) (Nat.mul x6 (nadd_rinv x2 x5))))) (Nat.mul (Nat.mul x3 (Nat.mul x4 x4)) (Nat.mul (Nat.mul x5 x6) (Nat.add x5 x6))).
Definition term66 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le (Nat.mul x0 y0) (Nat.mul x1 y0)) = ((Peano.le x0 x1) \/ (y0 = (NUMERAL 0))).
Definition term72 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul x0 (Nat.mul y0 y1)) = (Nat.mul (Nat.mul x0 y0) y1)) x1.
Definition term65 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (Nat.mul x0 y1) (Nat.mul y0 y1)) = ((Peano.le x0 y0) \/ (y1 = (NUMERAL 0)))) x1.
Definition term19 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (Nat.mul x0 y0) (Nat.mul x0 y1)) = ((x0 = (NUMERAL 0)) \/ (Peano.le y0 y1))) x1.
Definition term3 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 y1)) -> Peano.le x0 y1) x1.
Definition term121 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (Nat.mul (Nat.mul x1 x2) (Nat.add x1 x2)).
Definition term101 (x0 : nat) (x1 : nat) (x2 : nadd) (x3 : nat) := Peano.le (Nat.mul (Nat.mul x3 x1) (dist (@pair nat nat (Nat.mul x3 (nadd_rinv x2 x1)) (Nat.mul x1 (nadd_rinv x2 x3))))) (Nat.mul (Nat.mul x0 x0) (Nat.mul (Nat.mul (dest_nadd x2 x3) (dest_nadd x2 x1)) (dist (@pair nat nat (Nat.mul x3 (nadd_rinv x2 x1)) (Nat.mul x1 (nadd_rinv x2 x3)))))).
Definition term140 (x0 : nat) (x1 : nat) := and (Peano.le x0 (Nat.add x0 x1)).
Definition term112 (x0 : nat) (x1 : nadd) (x2 : nat) := Peano.le x2 (Nat.mul x0 (dest_nadd x1 x2)).
Definition term96 (x0 : nat) (x1 : nat) (x2 : nadd) (x3 : nat) := Nat.mul (Nat.mul (Nat.mul x0 x0) (dest_nadd x2 x1)) (dest_nadd x2 x3).
Definition term138 (x0 : nat) (x1 : nat) := (fun y0 : nat => Peano.le x0 (Nat.add x0 y0)) x1.
Definition term141 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 (Nat.add x0 x1)) /\ (Peano.le (Nat.add x0 x1) x2).
Definition term90 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.mul (Nat.mul x0 (Nat.mul x1 x1)) (Nat.mul (Nat.mul x2 x3) (Nat.add x2 x3)).
Definition term126 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x1 x0) /\ (Peano.le x1 x2).
Definition term118 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := Peano.le (Nat.mul (Nat.mul x1 x1) (Nat.mul (Nat.mul (dest_nadd x0 x3) (dest_nadd x0 x4)) (dist (@pair nat nat (Nat.mul x3 (nadd_rinv x0 x4)) (Nat.mul x4 (nadd_rinv x0 x3)))))) (Nat.mul (Nat.mul x1 x1) (Nat.mul x2 (Nat.mul (Nat.mul x3 x4) (Nat.add x3 x4)))).
Definition term98 (x0 : nat) (x1 : nat) (x2 : nadd) (x3 : nat) := Nat.mul (Nat.mul (Nat.mul (Nat.mul x0 x0) (dest_nadd x2 x1)) (dest_nadd x2 x3)).
Definition term6 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.le x1 x0) /\ (Peano.le x0 x2)) -> Peano.le x1 x2.
Definition term62 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq nat (Nat.mul x0 (Nat.mul x1 (Nat.mul x2 x3))).
Definition term113 (x0 : nat) (x1 : nat) (x2 : nadd) (x3 : nat) := (forall y0 : nat, (Peano.le x0 y0) -> Peano.le y0 (Nat.mul x1 (dest_nadd x2 y0))) -> Peano.le x3 (Nat.mul x1 (dest_nadd x2 x3)).
Definition term87 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.add x0 x1) x2.
Definition term33 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.mul x0 (Nat.mul x1 (Nat.mul x2 x3)).
Definition term26 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.mul x0 x1) x2.
Definition term122 (x0 : nat) (x1 : nadd) (x2 : nat) (x3 : nat) := (fun y0 : nat => forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le x0 y1)) -> Peano.le (Nat.mul (Nat.mul (dest_nadd x1 y0) (dest_nadd x1 y1)) (dist (@pair nat nat (Nat.mul y0 (nadd_rinv x1 y1)) (Nat.mul y1 (nadd_rinv x1 y0))))) (Nat.mul x2 (Nat.mul (Nat.mul y0 y1) (Nat.add y0 y1)))) x3.
Definition term60 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.mul (Nat.mul x0 x1) (Nat.mul x2 x3).
Definition term102 (x0 : nat) (x1 : nat) (x2 : nadd) (x3 : nat) := Peano.le (Nat.mul (Nat.mul x3 x1) (dist (@pair nat nat (Nat.mul x3 (nadd_rinv x2 x1)) (Nat.mul x1 (nadd_rinv x2 x3))))) (Nat.mul (Nat.mul (Nat.mul (Nat.mul x0 x0) (dest_nadd x2 x3)) (dest_nadd x2 x1)) (dist (@pair nat nat (Nat.mul x3 (nadd_rinv x2 x1)) (Nat.mul x1 (nadd_rinv x2 x3))))).
Definition term149 (x0 : nat) (x1 : nat) (x2 : nadd) (x3 : nat) (x4 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.le (Nat.add x0 x1) y0) /\ (Peano.le (Nat.add x0 x1) y1)) -> Peano.le (Nat.mul (Nat.mul y0 y1) (dist (@pair nat nat (Nat.mul y0 (nadd_rinv x2 y1)) (Nat.mul y1 (nadd_rinv x2 y0))))) (Nat.mul (Nat.mul x3 (Nat.mul x4 x4)) (Nat.mul (Nat.mul y0 y1) (Nat.add y0 y1))).
Definition term82 (x0 : nat) (x1 : nadd) (x2 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le x0 y1)) -> Peano.le (Nat.mul (Nat.mul (dest_nadd x1 y0) (dest_nadd x1 y1)) (dist (@pair nat nat (Nat.mul y0 (nadd_rinv x1 y1)) (Nat.mul y1 (nadd_rinv x1 y0))))) (Nat.mul x2 (Nat.mul (Nat.mul y0 y1) (Nat.add y0 y1))).
Definition term71 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.mul x0 (Nat.mul y0 y1)) = (Nat.mul (Nat.mul x0 y0) y1).
Definition term64 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le (Nat.mul x0 y1) (Nat.mul y0 y1)) = ((Peano.le x0 y0) \/ (y1 = (NUMERAL 0))).
Definition term54 := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.mul y0 y1) (Nat.mul y2 y3).
Definition term53 (x0 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le x0 y1) /\ (Peano.le y0 y2)) -> Peano.le (Nat.mul x0 y0) (Nat.mul y1 y2).
Definition term52 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le x1 y1)) -> Peano.le (Nat.mul x0 x1) (Nat.mul y0 y1).
Definition term44 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.le x0 x1) /\ (Peano.le y0 y1)) -> Peano.le (Nat.mul x0 y0) (Nat.mul x1 y1).
Definition term42 (x0 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le x0 y0) /\ (Peano.le y1 y2)) -> Peano.le (Nat.mul x0 y1) (Nat.mul y0 y2).
Definition term40 := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y1) /\ (Peano.le y2 y3)) -> Peano.le (Nat.mul y0 y2) (Nat.mul y1 y3).
Definition term18 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le (Nat.mul x0 y0) (Nat.mul x0 y1)) = ((x0 = (NUMERAL 0)) \/ (Peano.le y0 y1)).
Definition term13 := forall y0 : nat, forall y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) -> Peano.le y0 y1.
Definition term2 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 y1)) -> Peano.le x0 y1.
Definition term0 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2.
Definition term77 (x0 : nadd) := (fun y0 : nadd => (~ (nadd_eq y0 (nadd_of_num (NUMERAL 0)))) -> exists y1 : nat, exists y2 : nat, forall y3 : nat, forall y4 : nat, ((Peano.le y2 y3) /\ (Peano.le y2 y4)) -> Peano.le (Nat.mul (Nat.mul (dest_nadd y0 y3) (dest_nadd y0 y4)) (dist (@pair nat nat (Nat.mul y3 (nadd_rinv y0 y4)) (Nat.mul y4 (nadd_rinv y0 y3))))) (Nat.mul y1 (Nat.mul (Nat.mul y3 y4) (Nat.add y3 y4)))) x0.
Definition term75 (x0 : nadd) := (fun y0 : nadd => (~ (nadd_eq y0 (nadd_of_num (NUMERAL 0)))) -> exists y1 : nat, exists y2 : nat, forall y3 : nat, (Peano.le y2 y3) -> Peano.le y3 (Nat.mul y1 (dest_nadd y0 y3))) x0.
Definition term58 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le x1 y1)) -> Peano.le (Nat.mul x0 x1) (Nat.mul y0 y1)) x2.
Definition term45 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => forall y1 : nat, ((Peano.le x0 x1) /\ (Peano.le y0 y1)) -> Peano.le (Nat.mul x0 y0) (Nat.mul x1 y1)) x2.
Definition term57 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.le x0 y1) /\ (Peano.le y0 y2)) -> Peano.le (Nat.mul x0 y0) (Nat.mul y1 y2)) x1.
Definition term43 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.le x0 y0) /\ (Peano.le y1 y2)) -> Peano.le (Nat.mul x0 y1) (Nat.mul y0 y2)) x1.
Definition term86 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le (Nat.add x1 x2) x0) /\ (Peano.le (Nat.add x1 x2) x3).
Definition term85 (x0 : nat) (x1 : nat) (x2 : nadd) := forall y0 : nat, (Peano.le x0 y0) -> Peano.le y0 (Nat.mul x1 (dest_nadd x2 y0)).
Definition term128 (x0 : nat) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat) := (forall y0 : nat, forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le x0 y1)) -> Peano.le (Nat.mul (Nat.mul (dest_nadd x1 y0) (dest_nadd x1 y1)) (dist (@pair nat nat (Nat.mul y0 (nadd_rinv x1 y1)) (Nat.mul y1 (nadd_rinv x1 y0))))) (Nat.mul x2 (Nat.mul (Nat.mul y0 y1) (Nat.add y0 y1)))) -> Peano.le (Nat.mul (Nat.mul (dest_nadd x1 x3) (dest_nadd x1 x4)) (dist (@pair nat nat (Nat.mul x3 (nadd_rinv x1 x4)) (Nat.mul x4 (nadd_rinv x1 x3))))) (Nat.mul x2 (Nat.mul (Nat.mul x3 x4) (Nat.add x3 x4))).
Definition term120 (x0 : nat) (x1 : nadd) (x2 : nat) := Nat.mul (Nat.mul (dest_nadd x1 x2) (dest_nadd x1 x0)) (dist (@pair nat nat (Nat.mul x2 (nadd_rinv x1 x0)) (Nat.mul x0 (nadd_rinv x1 x2)))).
Definition term124 (x0 : nat) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat) := (fun y0 : nat => ((Peano.le x0 x3) /\ (Peano.le x0 y0)) -> Peano.le (Nat.mul (Nat.mul (dest_nadd x1 x3) (dest_nadd x1 y0)) (dist (@pair nat nat (Nat.mul x3 (nadd_rinv x1 y0)) (Nat.mul y0 (nadd_rinv x1 x3))))) (Nat.mul x2 (Nat.mul (Nat.mul x3 y0) (Nat.add x3 y0)))) x4.
Definition term50 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (Nat.mul x0 x1) (Nat.mul x2 x3).
Definition term89 (x0 : nat) (x1 : nadd) (x2 : nat) := Nat.mul (Nat.mul x2 x0) (dist (@pair nat nat (Nat.mul x2 (nadd_rinv x1 x0)) (Nat.mul x0 (nadd_rinv x1 x2)))).
Definition term35 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : nat) := Nat.mul x0 (Nat.mul x1 (Nat.mul x2 (Nat.mul x3 (Nat.mul x4 x5)))).
Definition term110 (x0 : nat) (x1 : nat) (x2 : nadd) (x3 : nat) := (fun y0 : nat => (Peano.le x0 y0) -> Peano.le y0 (Nat.mul x1 (dest_nadd x2 y0))) x3.
Definition term20 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le (Nat.mul x0 x1) (Nat.mul x0 y0)) = ((x0 = (NUMERAL 0)) \/ (Peano.le x1 y0)).
Definition term106 (x0 : nat) (x1 : nat) (x2 : nadd) (x3 : nat) := Peano.le (Nat.mul x1 x3) (Nat.mul (Nat.mul (Nat.mul x0 x0) (dest_nadd x2 x1)) (dest_nadd x2 x3)).
Definition term103 (x0 : nat) (x1 : nat) (x2 : nadd) (x3 : nat) := (Peano.le (Nat.mul x3 x1) (Nat.mul (Nat.mul (Nat.mul x0 x0) (dest_nadd x2 x3)) (dest_nadd x2 x1))) \/ ((dist (@pair nat nat (Nat.mul x3 (nadd_rinv x2 x1)) (Nat.mul x1 (nadd_rinv x2 x3)))) = (NUMERAL 0)).
Definition term91 (x0 : nat) (x1 : nat) (x2 : nadd) (x3 : nat) := Nat.mul (Nat.mul x0 x0) (Nat.mul (Nat.mul (dest_nadd x2 x3) (dest_nadd x2 x1)) (dist (@pair nat nat (Nat.mul x3 (nadd_rinv x2 x1)) (Nat.mul x1 (nadd_rinv x2 x3))))).
Definition term59 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.mul (Nat.mul (Nat.mul x0 x1) x2) x3.
Definition term119 (x0 : nat) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat) := ((Nat.mul x0 x0) = (NUMERAL 0)) \/ (Peano.le (Nat.mul (Nat.mul (dest_nadd x1 x3) (dest_nadd x1 x4)) (dist (@pair nat nat (Nat.mul x3 (nadd_rinv x1 x4)) (Nat.mul x4 (nadd_rinv x1 x3))))) (Nat.mul x2 (Nat.mul (Nat.mul x3 x4) (Nat.add x3 x4)))).
Definition term111 (x0 : nat) (x1 : nat) (x2 : nadd) (x3 : nat) := (Peano.le x0 x3) -> Peano.le x3 (Nat.mul x1 (dest_nadd x2 x3)).
Definition term22 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul x1 x0) (Nat.mul x1 x2).
Definition term48 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Peano.le x0 x2) /\ (Peano.le x1 x3)) -> Peano.le (Nat.mul x0 x1) (Nat.mul x2 x3).
Definition term144 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := exists y0 : nat, (Peano.le (Nat.mul (Nat.mul x3 x4) (dist (@pair nat nat (Nat.mul x3 (nadd_rinv x0 x4)) (Nat.mul x4 (nadd_rinv x0 x3))))) y0) /\ (Peano.le y0 (Nat.mul (Nat.mul x1 (Nat.mul x2 x2)) (Nat.mul (Nat.mul x3 x4) (Nat.add x3 x4)))).
Definition term4 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Peano.le x1 x0) /\ (Peano.le x0 y0)) -> Peano.le x1 y0.
Definition term115 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.mul (Nat.mul x0 x0) (Nat.mul x1 (Nat.mul (Nat.mul x2 x3) (Nat.add x2 x3))).
Definition term93 (x0 : nat) (x1 : nadd) (x2 : nat) := Nat.mul (dest_nadd x1 x0) (dest_nadd x1 x2).
Definition term125 (x0 : nat) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat) := ((Peano.le x0 x3) /\ (Peano.le x0 x4)) -> Peano.le (Nat.mul (Nat.mul (dest_nadd x1 x3) (dest_nadd x1 x4)) (dist (@pair nat nat (Nat.mul x3 (nadd_rinv x1 x4)) (Nat.mul x4 (nadd_rinv x1 x3))))) (Nat.mul x2 (Nat.mul (Nat.mul x3 x4) (Nat.add x3 x4))).
Definition term162 := forall y0 : nadd, (~ (nadd_eq y0 (nadd_of_num (NUMERAL 0)))) -> exists y1 : nat, exists y2 : nat, forall y3 : nat, forall y4 : nat, ((Peano.le y2 y3) /\ (Peano.le y2 y4)) -> Peano.le (Nat.mul (Nat.mul y3 y4) (dist (@pair nat nat (Nat.mul y3 (nadd_rinv y0 y4)) (Nat.mul y4 (nadd_rinv y0 y3))))) (Nat.mul y1 (Nat.mul (Nat.mul y3 y4) (Nat.add y3 y4))).
Definition term154 (x0 : nat) (x1 : nat) := Nat.mul x0 (Nat.mul x1 x1).
Definition term105 (x0 : nat) (x1 : nat) := Peano.le (Nat.mul x0 x1).
Definition term133 (x0 : nat) (x1 : nat) := Peano.le x1 (Nat.add x0 x1).
Definition term139 (x0 : nat) (x1 : nat) := Peano.le x0 (Nat.add x0 x1).
Definition term136 (x0 : nat) := (fun y0 : nat => forall y1 : nat, Peano.le y0 (Nat.add y0 y1)) x0.
Definition term130 (x0 : nat) := (fun y0 : nat => forall y1 : nat, Peano.le y1 (Nat.add y0 y1)) x0.
Definition term15 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) -> Peano.le y0 y1) x0.
Definition term127 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (Nat.mul (Nat.mul (dest_nadd x0 x2) (dest_nadd x0 x3)) (dist (@pair nat nat (Nat.mul x2 (nadd_rinv x0 x3)) (Nat.mul x3 (nadd_rinv x0 x2))))) (Nat.mul x1 (Nat.mul (Nat.mul x2 x3) (Nat.add x2 x3))).
Definition term107 (x0 : nat) (x1 : nat) (x2 : nadd) (x3 : nat) := Peano.le (Nat.mul x0 x3) (Nat.mul (Nat.mul x1 (dest_nadd x2 x0)) (Nat.mul x1 (dest_nadd x2 x3))).
Definition term7 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x1) /\ (Peano.le x1 x2).
Definition term49 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le x0 x1) /\ (Peano.le x2 x3).
Definition term46 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, ((Peano.le x0 x2) /\ (Peano.le x1 y0)) -> Peano.le (Nat.mul x0 x1) (Nat.mul x2 y0).
Definition term27 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (Nat.mul x1 x2).
Definition term21 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.le (Nat.mul x0 x1) (Nat.mul x0 y0)) = ((x0 = (NUMERAL 0)) \/ (Peano.le x1 y0))) x2.
Definition term108 (x0 : nat) (x1 : nat) (x2 : nadd) (x3 : nat) := ((Peano.le x0 (Nat.mul x1 (dest_nadd x2 x0))) /\ (Peano.le x3 (Nat.mul x1 (dest_nadd x2 x3)))) -> Peano.le (Nat.mul x0 x3) (Nat.mul (Nat.mul x1 (dest_nadd x2 x0)) (Nat.mul x1 (dest_nadd x2 x3))).
Definition term104 (x0 : nat) (x1 : nat) (x2 : nadd) (x3 : nat) := Nat.mul (Nat.mul x1 (dest_nadd x2 x0)) (Nat.mul x1 (dest_nadd x2 x3)).
Definition term95 (x0 : nat) (x1 : nat) (x2 : nadd) (x3 : nat) := Nat.mul (Nat.mul x0 x0) (Nat.mul (dest_nadd x2 x1) (dest_nadd x2 x3)).
Definition term117 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := Peano.le (Nat.mul (Nat.mul x2 x2) (Nat.mul (Nat.mul (dest_nadd x0 x3) (dest_nadd x0 x4)) (dist (@pair nat nat (Nat.mul x3 (nadd_rinv x0 x4)) (Nat.mul x4 (nadd_rinv x0 x3)))))) (Nat.mul (Nat.mul x1 (Nat.mul x2 x2)) (Nat.mul (Nat.mul x3 x4) (Nat.add x3 x4))).
Definition term11 (x0 : nat) (x1 : nat) := (exists y0 : nat, (Peano.le x0 y0) /\ (Peano.le y0 x1)) -> Peano.le x0 x1.
Definition term36 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : nat) := @eq nat (Nat.mul (Nat.mul x0 (Nat.mul x1 x2)) (Nat.mul (Nat.mul x3 x4) x5)).
Definition term25 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.mul (Nat.mul x1 x0) x2) = (Nat.mul x1 (Nat.mul x0 x2))) /\ ((Nat.mul x1 (Nat.mul x0 x2)) = (Nat.mul x0 (Nat.mul x1 x2))).
Definition term142 (x0 : nat) (x1 : nat) (x2 : nadd) (x3 : nat) := (Peano.le x0 (Nat.mul x1 (dest_nadd x2 x0))) /\ (Peano.le x3 (Nat.mul x1 (dest_nadd x2 x3))).
Definition term116 (x0 : nat) (x1 : nat) (x2 : nadd) (x3 : nat) := Peano.le (Nat.mul (Nat.mul x0 x0) (Nat.mul (Nat.mul (dest_nadd x2 x3) (dest_nadd x2 x1)) (dist (@pair nat nat (Nat.mul x3 (nadd_rinv x2 x1)) (Nat.mul x1 (nadd_rinv x2 x3)))))).
Definition term69 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x1) \/ (x2 = (NUMERAL 0)).
Definition term61 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq nat (Nat.mul (Nat.mul (Nat.mul x0 x1) x2) x3).
Definition term10 (x0 : nat) (x1 : nat) := fun y0 : nat => (Peano.le x0 y0) /\ (Peano.le y0 x1).
Definition term152 (x0 : nadd) := exists y0 : nat, exists y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y1 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.mul (Nat.mul y2 y3) (dist (@pair nat nat (Nat.mul y2 (nadd_rinv x0 y3)) (Nat.mul y3 (nadd_rinv x0 y2))))) (Nat.mul y0 (Nat.mul (Nat.mul y2 y3) (Nat.add y2 y3))).
Definition term83 (x0 : nadd) := exists y0 : nat, exists y1 : nat, forall y2 : nat, (Peano.le y1 y2) -> Peano.le y2 (Nat.mul y0 (dest_nadd x0 y2)).
Definition term80 (x0 : nadd) := exists y0 : nat, exists y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y1 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.mul (Nat.mul (dest_nadd x0 y2) (dest_nadd x0 y3)) (dist (@pair nat nat (Nat.mul y2 (nadd_rinv x0 y3)) (Nat.mul y3 (nadd_rinv x0 y2))))) (Nat.mul y0 (Nat.mul (Nat.mul y2 y3) (Nat.add y2 y3))).
Definition term79 (x0 : nadd) := ~ (nadd_eq x0 (nadd_of_num (NUMERAL 0))).
Definition term148 (x0 : nat) (x1 : nat) (x2 : nadd) (x3 : nat) (x4 : nat) (x5 : nat) := forall y0 : nat, ((Peano.le (Nat.add x0 x1) x5) /\ (Peano.le (Nat.add x0 x1) y0)) -> Peano.le (Nat.mul (Nat.mul x5 y0) (dist (@pair nat nat (Nat.mul x5 (nadd_rinv x2 y0)) (Nat.mul y0 (nadd_rinv x2 x5))))) (Nat.mul (Nat.mul x3 (Nat.mul x4 x4)) (Nat.mul (Nat.mul x5 y0) (Nat.add x5 y0))).
Definition term123 (x0 : nat) (x1 : nadd) (x2 : nat) (x3 : nat) := forall y0 : nat, ((Peano.le x0 x3) /\ (Peano.le x0 y0)) -> Peano.le (Nat.mul (Nat.mul (dest_nadd x1 x3) (dest_nadd x1 y0)) (dist (@pair nat nat (Nat.mul x3 (nadd_rinv x1 y0)) (Nat.mul y0 (nadd_rinv x1 x3))))) (Nat.mul x2 (Nat.mul (Nat.mul x3 y0) (Nat.add x3 y0))).
Definition term97 (x0 : nat) (x1 : nat) (x2 : nadd) (x3 : nat) := Nat.mul (Nat.mul (Nat.mul x0 x0) (Nat.mul (dest_nadd x2 x1) (dest_nadd x2 x3))).
Definition term161 (x0 : nadd) := (~ (nadd_eq x0 (nadd_of_num (NUMERAL 0)))) -> exists y0 : nat, exists y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y1 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.mul (Nat.mul y2 y3) (dist (@pair nat nat (Nat.mul y2 (nadd_rinv x0 y3)) (Nat.mul y3 (nadd_rinv x0 y2))))) (Nat.mul y0 (Nat.mul (Nat.mul y2 y3) (Nat.add y2 y3))).
Definition term78 (x0 : nadd) := (~ (nadd_eq x0 (nadd_of_num (NUMERAL 0)))) -> exists y0 : nat, exists y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y1 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.mul (Nat.mul (dest_nadd x0 y2) (dest_nadd x0 y3)) (dist (@pair nat nat (Nat.mul y2 (nadd_rinv x0 y3)) (Nat.mul y3 (nadd_rinv x0 y2))))) (Nat.mul y0 (Nat.mul (Nat.mul y2 y3) (Nat.add y2 y3))).
Definition term76 (x0 : nadd) := (~ (nadd_eq x0 (nadd_of_num (NUMERAL 0)))) -> exists y0 : nat, exists y1 : nat, forall y2 : nat, (Peano.le y1 y2) -> Peano.le y2 (Nat.mul y0 (dest_nadd x0 y2)).
Definition term24 (a0 : Type') (x0 : a0) := (fun y0 : a0 => (y0 = y0) = True) x0.
Definition term135 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x1 (Nat.add x0 x1)) /\ (Peano.le (Nat.add x0 x1) x2).
Definition term99 (x0 : nat) (x1 : nat) (x2 : nadd) (x3 : nat) := Nat.mul (Nat.mul (Nat.mul (Nat.mul x0 x0) (dest_nadd x2 x3)) (dest_nadd x2 x1)) (dist (@pair nat nat (Nat.mul x3 (nadd_rinv x2 x1)) (Nat.mul x1 (nadd_rinv x2 x3)))).
Definition term94 (x0 : nat) (x1 : nadd) (x2 : nat) := dist (@pair nat nat (Nat.mul x2 (nadd_rinv x1 x0)) (Nat.mul x0 (nadd_rinv x1 x2))).
Definition term155 (x0 : nat) (x1 : nadd) := fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) -> Peano.le y1 (Nat.mul x0 (dest_nadd x1 y1)).
Definition term131 (x0 : nat) := forall y0 : nat, Peano.le y0 (Nat.add x0 y0).
Definition term158 (x0 : nadd) (x1 : nat) := fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y0 y2)) -> Peano.le (Nat.mul (Nat.mul (dest_nadd x0 y1) (dest_nadd x0 y2)) (dist (@pair nat nat (Nat.mul y1 (nadd_rinv x0 y2)) (Nat.mul y2 (nadd_rinv x0 y1))))) (Nat.mul x1 (Nat.mul (Nat.mul y1 y2) (Nat.add y1 y2))).
Definition term151 (x0 : nadd) (x1 : nat) (x2 : nat) := fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y0 y2)) -> Peano.le (Nat.mul (Nat.mul y1 y2) (dist (@pair nat nat (Nat.mul y1 (nadd_rinv x0 y2)) (Nat.mul y2 (nadd_rinv x0 y1))))) (Nat.mul (Nat.mul x1 (Nat.mul x2 x2)) (Nat.mul (Nat.mul y1 y2) (Nat.add y1 y2))).
Definition term16 (x0 : nat) (x1 : nat) := (fun y0 : nat => (exists y1 : nat, (Peano.le x0 y1) /\ (Peano.le y1 y0)) -> Peano.le x0 y0) x1.
Definition term114 (x0 : nat) (x1 : nat) (x2 : nadd) := (forall y0 : nat, (Peano.le x0 y0) -> Peano.le y0 (Nat.mul x1 (dest_nadd x2 y0))) -> forall y0 : nat, (Peano.le x0 y0) -> Peano.le y0 (Nat.mul x1 (dest_nadd x2 y0)).
