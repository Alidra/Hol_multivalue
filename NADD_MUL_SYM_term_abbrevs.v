Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term171 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul (Nat.add x0 x1) x2).
Definition term98 (x0 : nadd) (x1 : nadd) := dest_nadd (nadd_mul x0 x1).
Definition term208 (x0 : nat) (x1 : nadd) (x2 : nadd) := (exists y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (Nat.mul y1 (dest_nadd x2 (dest_nadd x1 y1))) (Nat.mul (dest_nadd x2 y1) (dest_nadd x1 y1)))) (Nat.add (Nat.mul x0 y1) y0)) -> exists y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (dest_nadd x2 (dest_nadd x1 y1)) (dest_nadd x1 (dest_nadd x2 y1)))) y0.
Definition term206 (x0 : nat) (x1 : nadd) (x2 : nadd) := (exists y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (Nat.mul y1 (dest_nadd x1 (dest_nadd x2 y1))) (Nat.mul (dest_nadd x1 y1) (dest_nadd x2 y1)))) (Nat.add (Nat.mul x0 y1) y0)) -> exists y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (dest_nadd x2 (dest_nadd x1 y1)) (dest_nadd x1 (dest_nadd x2 y1)))) y0.
Definition term100 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, (nadd_eq y0 y1) = (exists y2 : nat, forall y3 : nat, Peano.le (dist (@pair nat nat (dest_nadd y0 y3) (dest_nadd y1 y3))) y2)) x0.
Definition term151 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) := fun y0 : nat => Peano.le (Nat.mul y0 ((fun y1 : nat => dist (@pair nat nat (dest_nadd x1 (dest_nadd x0 y1)) (dest_nadd x0 (dest_nadd x1 y1)))) y0)) (Nat.add (Nat.mul x2 y0) x3).
Definition term192 (x0 : nadd) (x1 : nadd) (x2 : nat) := Peano.le (dist (@pair nat nat (Nat.mul (dest_nadd x1 x2) (dest_nadd x0 x2)) (Nat.mul x2 (dest_nadd x0 (dest_nadd x1 x2))))).
Definition term163 (x0 : nadd) (x1 : nadd) (x2 : nat) := Peano.le (dist (@pair nat nat (Nat.mul x2 (dest_nadd x1 (dest_nadd x0 x2))) (Nat.mul x2 (dest_nadd x0 (dest_nadd x1 x2))))).
Definition term118 (x0 : nadd) (x1 : nadd) (x2 : nat) := @pair nat nat (dest_nadd x1 (dest_nadd x0 x2)) (dest_nadd x0 (dest_nadd x1 x2)).
Definition term42 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (dist (@pair nat nat x0 x1)) (dist (@pair nat nat x1 x2)).
Definition term54 (x0 : nat) (x1 : nat) (x2 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, (Peano.le (Nat.add (dist (@pair nat nat y1 y0)) (dist (@pair nat nat y0 y2))) y3) -> Peano.le (dist (@pair nat nat y1 y2)) y3) -> Peano.le (dist (@pair nat nat x0 x1)) x2.
Definition term112 (x0 : nadd) (x1 : nadd) := fun y0 : nat => (fun y1 : nat => dest_nadd x0 (dest_nadd x1 y1)) y0.
Definition term207 (x0 : nadd) (x1 : nadd) := fun y0 : nat => exists y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (Nat.mul y2 (dest_nadd x0 (dest_nadd x1 y2))) (Nat.mul (dest_nadd x0 y2) (dest_nadd x1 y2)))) (Nat.add (Nat.mul y0 y2) y1).
Definition term169 (x0 : nadd) (x1 : nadd) := fun y0 : nat => exists y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (Nat.mul y2 (dest_nadd x1 (dest_nadd x0 y2))) (Nat.mul y2 (dest_nadd x0 (dest_nadd x1 y2))))) (Nat.add (Nat.mul y0 y2) y1).
Definition term160 (x0 : nadd) (x1 : nadd) := fun y0 : nat => exists y1 : nat, forall y2 : nat, Peano.le (Nat.mul y2 (dist (@pair nat nat (dest_nadd x1 (dest_nadd x0 y2)) (dest_nadd x0 (dest_nadd x1 y2))))) (Nat.add (Nat.mul y0 y2) y1).
Definition term159 (x0 : nadd) (x1 : nadd) := fun y0 : nat => exists y1 : nat, forall y2 : nat, Peano.le (Nat.mul y2 ((fun y3 : nat => dist (@pair nat nat (dest_nadd x1 (dest_nadd x0 y3)) (dest_nadd x0 (dest_nadd x1 y3)))) y2)) (Nat.add (Nat.mul y0 y2) y1).
Definition term33 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x2) -> Peano.le x1 x2.
Definition term203 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) := exists y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (Nat.mul y1 (dest_nadd x1 (dest_nadd x0 y1))) (Nat.mul y1 (dest_nadd x0 (dest_nadd x1 y1))))) (Nat.add (Nat.mul (Nat.add x2 x3) y1) y0).
Definition term168 (x0 : nadd) (x1 : nadd) (x2 : nat) := exists y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (Nat.mul y1 (dest_nadd x1 (dest_nadd x0 y1))) (Nat.mul y1 (dest_nadd x0 (dest_nadd x1 y1))))) (Nat.add (Nat.mul x2 y1) y0).
Definition term158 (x0 : nadd) (x1 : nadd) (x2 : nat) := exists y0 : nat, forall y1 : nat, Peano.le (Nat.mul y1 (dist (@pair nat nat (dest_nadd x1 (dest_nadd x0 y1)) (dest_nadd x0 (dest_nadd x1 y1))))) (Nat.add (Nat.mul x2 y1) y0).
Definition term157 (x0 : nadd) (x1 : nadd) (x2 : nat) := exists y0 : nat, forall y1 : nat, Peano.le (Nat.mul y1 ((fun y2 : nat => dist (@pair nat nat (dest_nadd x1 (dest_nadd x0 y2)) (dest_nadd x0 (dest_nadd x1 y2)))) y1)) (Nat.add (Nat.mul x2 y1) y0).
Definition term133 (x0 : nadd) (x1 : nadd) := exists y0 : nat, forall y1 : nat, Peano.le ((fun y2 : nat => dist (@pair nat nat (dest_nadd x1 (dest_nadd x0 y2)) (dest_nadd x0 (dest_nadd x1 y2)))) y1) y0.
Definition term131 (x0 : nadd) (x1 : nadd) := exists y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (dest_nadd x1 (dest_nadd x0 y1)) (dest_nadd x0 (dest_nadd x1 y1)))) y0.
Definition term105 (x0 : nadd) (x1 : nadd) := exists y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (dest_nadd (nadd_mul x1 x0) y1) (dest_nadd (nadd_mul x0 x1) y1))) y0.
Definition term103 (x0 : nadd) (x1 : nadd) := exists y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 y1) (dest_nadd x1 y1))) y0.
Definition term94 (x0 : nadd) (x1 : nadd) (x2 : nat) := exists y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (Nat.mul y1 (dest_nadd x0 (dest_nadd x1 y1))) (Nat.mul (dest_nadd x0 y1) (dest_nadd x1 y1)))) (Nat.add (Nat.mul x2 y1) y0).
Definition term88 (x0 : nat -> nat) := exists y0 : nat, forall y1 : nat, Peano.le (x0 y1) y0.
Definition term80 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.mul y0 (dist (@pair nat nat y1 y2))) = (dist (@pair nat nat (Nat.mul y0 y1) (Nat.mul y0 y2)))) x0.
Definition term73 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.mul (Nat.add y0 y1) y2) = (Nat.add (Nat.mul y0 y2) (Nat.mul y1 y2))) x0.
Definition term62 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (exists y3 : nat, Peano.le (Nat.add (dist (@pair nat nat y0 y3)) (dist (@pair nat nat y3 y1))) y2) -> Peano.le (dist (@pair nat nat y0 y1)) y2) x0.
Definition term47 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, (Peano.le (Nat.add (dist (@pair nat nat y1 y0)) (dist (@pair nat nat y0 y2))) y3) -> Peano.le (dist (@pair nat nat y1 y2)) y3) x0.
Definition term27 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le y0 y1) -> (Peano.le y1 y2) -> Peano.le y0 y2) x0.
Definition term20 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat y0 y2)) (Nat.add (dist (@pair nat nat y0 y1)) (dist (@pair nat nat y1 y2)))) x0.
Definition term8 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.add y0 y1) (Nat.add y2 y3)) x0.
Definition term139 (x0 : nadd) (x1 : nadd) (x2 : nat) := fun y0 : nat => Peano.le ((fun y1 : nat => dist (@pair nat nat (dest_nadd x1 (dest_nadd x0 y1)) (dest_nadd x0 (dest_nadd x1 y1)))) y0) x2.
Definition term14 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => ((Peano.le x0 x2) /\ (Peano.le x1 y0)) -> Peano.le (Nat.add x0 x1) (Nat.add x2 y0)) x3.
Definition term4 (x0 : nat) := forall y0 : nat, (dist (@pair nat nat x0 y0)) = (dist (@pair nat nat y0 x0)).
Definition term120 (x0 : nadd) (x1 : nadd) (x2 : nat) := dist (@pair nat nat (dest_nadd x1 (dest_nadd x0 x2)) (dest_nadd x0 (dest_nadd x1 x2))).
Definition term137 (x0 : nadd) (x1 : nadd) (x2 : nat) := Peano.le ((fun y0 : nat => dist (@pair nat nat (dest_nadd x1 (dest_nadd x0 y0)) (dest_nadd x0 (dest_nadd x1 y0)))) x2).
Definition term61 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, (Peano.le (Nat.add (dist (@pair nat nat y1 y0)) (dist (@pair nat nat y0 y2))) y3) -> Peano.le (dist (@pair nat nat y1 y2)) y3) -> forall y0 : nat, forall y1 : nat, forall y2 : nat, (exists y3 : nat, Peano.le (Nat.add (dist (@pair nat nat y0 y3)) (dist (@pair nat nat y3 y1))) y2) -> Peano.le (dist (@pair nat nat y0 y1)) y2.
Definition term38 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.le y0 y1) -> (Peano.le y1 y2) -> Peano.le y0 y2) -> forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> forall y2 : nat, (Peano.le y1 y2) -> Peano.le y0 y2.
Definition term19 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.add y0 y1) (Nat.add y2 y3)) -> forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.add y0 y1) (Nat.add y2 y3).
Definition term179 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : nat) (x6 : nat) := (exists y0 : nat, Peano.le (Nat.add (dist (@pair nat nat (Nat.mul x5 (dest_nadd x1 (dest_nadd x0 x5))) y0)) (dist (@pair nat nat y0 (Nat.mul x5 (dest_nadd x0 (dest_nadd x1 x5)))))) (Nat.add (Nat.add (Nat.mul x2 x5) x3) (Nat.add (Nat.mul x4 x5) x6))) -> Peano.le (dist (@pair nat nat (Nat.mul x5 (dest_nadd x1 (dest_nadd x0 x5))) (Nat.mul x5 (dest_nadd x0 (dest_nadd x1 x5))))) (Nat.add (Nat.add (Nat.mul x2 x5) x3) (Nat.add (Nat.mul x4 x5) x6)).
Definition term86 (x0 : nat) (x1 : nat) (x2 : nat) := dist (@pair nat nat (Nat.mul x1 x0) (Nat.mul x1 x2)).
Definition term210 := forall y0 : nadd, forall y1 : nadd, nadd_eq (nadd_mul y0 y1) (nadd_mul y1 y0).
Definition term124 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) := Peano.le (dist (@pair nat nat (dest_nadd x1 (dest_nadd x0 x2)) (dest_nadd x0 (dest_nadd x1 x2)))) x3.
Definition term87 (x0 : nat -> nat) := (fun y0 : nat -> nat => (exists y1 : nat, forall y2 : nat, Peano.le (y0 y2) y1) = (exists y1 : nat, exists y2 : nat, forall y3 : nat, Peano.le (Nat.mul y3 (y0 y3)) (Nat.add (Nat.mul y1 y3) y2))) x0.
Definition term117 (x0 : nadd) (x1 : nadd) (x2 : nat) := @pair nat nat (dest_nadd (nadd_mul x1 x0) x2) (dest_nadd (nadd_mul x0 x1) x2).
Definition term143 (x0 : nadd) (x1 : nadd) := @eq Prop (exists y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (dest_nadd x1 (dest_nadd x0 y1)) (dest_nadd x0 (dest_nadd x1 y1)))) y0).
Definition term142 (x0 : nadd) (x1 : nadd) := @eq Prop (exists y0 : nat, forall y1 : nat, Peano.le ((fun y2 : nat => dist (@pair nat nat (dest_nadd x1 (dest_nadd x0 y2)) (dest_nadd x0 (dest_nadd x1 y2)))) y1) y0).
Definition term114 (x0 : nadd) (x1 : nadd) (x2 : nat) := @eq nat ((fun y0 : nat => dest_nadd x0 (dest_nadd x1 y0)) x2).
Definition term201 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : nat) (x6 : nat) := fun y0 : nat => Peano.le (Nat.add (dist (@pair nat nat (Nat.mul x5 (dest_nadd x1 (dest_nadd x0 x5))) y0)) (dist (@pair nat nat y0 (Nat.mul x5 (dest_nadd x0 (dest_nadd x1 x5)))))) (Nat.add (Nat.add (Nat.mul x2 x5) x3) (Nat.add (Nat.mul x4 x5) x6)).
Definition term70 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.add x0 (Nat.add x1 (Nat.add x2 x3)).
Definition term64 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (exists y1 : nat, Peano.le (Nat.add (dist (@pair nat nat x0 y1)) (dist (@pair nat nat y1 x1))) y0) -> Peano.le (dist (@pair nat nat x0 x1)) y0) x2.
Definition term6 (x0 : nat) (x1 : nat) := dist (@pair nat nat x0 x1).
Definition term17 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (Nat.add x0 x1) (Nat.add x2 x3).
Definition term67 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.add x0 x1) x2.
Definition term24 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => Peano.le (dist (@pair nat nat x0 y0)) (Nat.add (dist (@pair nat nat x0 x1)) (dist (@pair nat nat x1 y0)))) x2.
Definition term200 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : nat) (x6 : nat) := exists y0 : nat, Peano.le (Nat.add (dist (@pair nat nat (Nat.mul x5 (dest_nadd x1 (dest_nadd x0 x5))) y0)) (dist (@pair nat nat y0 (Nat.mul x5 (dest_nadd x0 (dest_nadd x1 x5)))))) (Nat.add (Nat.add (Nat.mul x2 x5) x3) (Nat.add (Nat.mul x4 x5) x6)).
Definition term36 (x0 : nat) := forall y0 : nat, (Peano.le x0 y0) -> forall y1 : nat, (Peano.le y0 y1) -> Peano.le x0 y1.
Definition term126 (x0 : nadd) (x1 : nadd) (x2 : nat) := fun y0 : nat => Peano.le (dist (@pair nat nat (dest_nadd x1 (dest_nadd x0 y0)) (dest_nadd x0 (dest_nadd x1 y0)))) x2.
Definition term125 (x0 : nadd) (x1 : nadd) (x2 : nat) := fun y0 : nat => Peano.le (dist (@pair nat nat (dest_nadd (nadd_mul x1 x0) y0) (dest_nadd (nadd_mul x0 x1) y0))) x2.
Definition term92 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => exists y1 : nat, exists y2 : nat, forall y3 : nat, Peano.le (dist (@pair nat nat (Nat.mul y3 (dest_nadd x0 (dest_nadd y0 y3))) (Nat.mul (dest_nadd x0 y3) (dest_nadd y0 y3)))) (Nat.add (Nat.mul y1 y3) y2)) x1.
Definition term140 (x0 : nadd) (x1 : nadd) (x2 : nat) := forall y0 : nat, Peano.le ((fun y1 : nat => dist (@pair nat nat (dest_nadd x1 (dest_nadd x0 y1)) (dest_nadd x0 (dest_nadd x1 y1)))) y0) x2.
Definition term199 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : nat) (x6 : nat) := Peano.le (Nat.add (dist (@pair nat nat (Nat.mul x5 (dest_nadd x1 (dest_nadd x0 x5))) (Nat.mul (dest_nadd x1 x5) (dest_nadd x0 x5)))) (dist (@pair nat nat (Nat.mul (dest_nadd x1 x5) (dest_nadd x0 x5)) (Nat.mul x5 (dest_nadd x0 (dest_nadd x1 x5)))))) (Nat.add (Nat.add (Nat.mul x2 x5) x3) (Nat.add (Nat.mul x4 x5) x6)).
Definition term198 (x0 : nadd) (x1 : nadd) (x2 : nat) := Peano.le (dist (@pair nat nat (Nat.mul x2 (dest_nadd x0 (dest_nadd x1 x2))) (Nat.mul (dest_nadd x0 x2) (dest_nadd x1 x2)))).
Definition term193 (x0 : nadd) (x1 : nadd) (x2 : nat) := Peano.le (dist (@pair nat nat (Nat.mul x2 (dest_nadd x1 (dest_nadd x0 x2))) (Nat.mul (dest_nadd x0 x2) (dest_nadd x1 x2)))).
Definition term106 (x0 : nadd) (x1 : nadd) (x2 : nat) := dest_nadd (nadd_mul x0 x1) x2.
Definition term85 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (dist (@pair nat nat x1 x2)).
Definition term113 (x0 : nadd) (x1 : nadd) (x2 : nat) := @eq nat ((fun y0 : nat => (fun y1 : nat => dest_nadd x0 (dest_nadd x1 y1)) y0) x2).
Definition term97 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => (dest_nadd (nadd_mul x0 y0)) = (fun y1 : nat => dest_nadd x0 (dest_nadd y0 y1))) x1.
Definition term82 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul x0 (dist (@pair nat nat y0 y1))) = (dist (@pair nat nat (Nat.mul x0 y0) (Nat.mul x0 y1)))) x1.
Definition term75 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul (Nat.add x0 y0) y1) = (Nat.add (Nat.mul x0 y1) (Nat.mul y0 y1))) x1.
Definition term63 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (exists y2 : nat, Peano.le (Nat.add (dist (@pair nat nat x0 y2)) (dist (@pair nat nat y2 y0))) y1) -> Peano.le (dist (@pair nat nat x0 y0)) y1) x1.
Definition term29 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le x0 y0) -> (Peano.le y0 y1) -> Peano.le x0 y1) x1.
Definition term22 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, Peano.le (dist (@pair nat nat x0 y1)) (Nat.add (dist (@pair nat nat x0 y0)) (dist (@pair nat nat y0 y1)))) x1.
Definition term136 (x0 : nadd) (x1 : nadd) (x2 : nat) := (fun y0 : nat => dist (@pair nat nat (dest_nadd x1 (dest_nadd x0 y0)) (dest_nadd x0 (dest_nadd x1 y0)))) x2.
Definition term115 (x0 : nadd) (x1 : nadd) (x2 : nat) := @pair nat nat (dest_nadd (nadd_mul x0 x1) x2).
Definition term205 (x0 : nadd) (x1 : nadd) (x2 : nat) := fun y0 : nat => forall y1 : nat, Peano.le (dist (@pair nat nat (Nat.mul y1 (dest_nadd x0 (dest_nadd x1 y1))) (Nat.mul (dest_nadd x0 y1) (dest_nadd x1 y1)))) (Nat.add (Nat.mul x2 y1) y0).
Definition term204 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) := fun y0 : nat => forall y1 : nat, Peano.le (dist (@pair nat nat (Nat.mul y1 (dest_nadd x1 (dest_nadd x0 y1))) (Nat.mul y1 (dest_nadd x0 (dest_nadd x1 y1))))) (Nat.add (Nat.mul (Nat.add x2 x3) y1) y0).
Definition term167 (x0 : nadd) (x1 : nadd) (x2 : nat) := fun y0 : nat => forall y1 : nat, Peano.le (dist (@pair nat nat (Nat.mul y1 (dest_nadd x1 (dest_nadd x0 y1))) (Nat.mul y1 (dest_nadd x0 (dest_nadd x1 y1))))) (Nat.add (Nat.mul x2 y1) y0).
Definition term156 (x0 : nadd) (x1 : nadd) (x2 : nat) := fun y0 : nat => forall y1 : nat, Peano.le (Nat.mul y1 (dist (@pair nat nat (dest_nadd x1 (dest_nadd x0 y1)) (dest_nadd x0 (dest_nadd x1 y1))))) (Nat.add (Nat.mul x2 y1) y0).
Definition term155 (x0 : nadd) (x1 : nadd) (x2 : nat) := fun y0 : nat => forall y1 : nat, Peano.le (Nat.mul y1 ((fun y2 : nat => dist (@pair nat nat (dest_nadd x1 (dest_nadd x0 y2)) (dest_nadd x0 (dest_nadd x1 y2)))) y1)) (Nat.add (Nat.mul x2 y1) y0).
Definition term25 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (dist (@pair nat nat x0 x2)) (Nat.add (dist (@pair nat nat x0 x1)) (dist (@pair nat nat x1 x2))).
Definition term121 (x0 : nadd) (x1 : nadd) (x2 : nat) := Peano.le (dist (@pair nat nat (dest_nadd (nadd_mul x1 x0) x2) (dest_nadd (nadd_mul x0 x1) x2))).
Definition term154 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) := forall y0 : nat, Peano.le (Nat.mul y0 (dist (@pair nat nat (dest_nadd x1 (dest_nadd x0 y0)) (dest_nadd x0 (dest_nadd x1 y0))))) (Nat.add (Nat.mul x2 y0) x3).
Definition term153 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) := forall y0 : nat, Peano.le (Nat.mul y0 ((fun y1 : nat => dist (@pair nat nat (dest_nadd x1 (dest_nadd x0 y1)) (dest_nadd x0 (dest_nadd x1 y1)))) y0)) (Nat.add (Nat.mul x2 y0) x3).
Definition term51 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le (Nat.add (dist (@pair nat nat x1 x0)) (dist (@pair nat nat x0 x2))) x3) -> Peano.le (dist (@pair nat nat x1 x2)) x3.
Definition term138 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) := Peano.le ((fun y0 : nat => dist (@pair nat nat (dest_nadd x1 (dest_nadd x0 y0)) (dest_nadd x0 (dest_nadd x1 y0)))) x2) x3.
Definition term181 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : nat) (x6 : nat) := ((Peano.le (dist (@pair nat nat (Nat.mul x5 (dest_nadd x1 (dest_nadd x0 x5))) (Nat.mul (dest_nadd x1 x5) (dest_nadd x0 x5)))) (Nat.add (Nat.mul x2 x5) x3)) /\ (Peano.le (dist (@pair nat nat (Nat.mul (dest_nadd x1 x5) (dest_nadd x0 x5)) (Nat.mul x5 (dest_nadd x0 (dest_nadd x1 x5))))) (Nat.add (Nat.mul x4 x5) x6))) -> Peano.le (Nat.add (dist (@pair nat nat (Nat.mul x5 (dest_nadd x1 (dest_nadd x0 x5))) (Nat.mul (dest_nadd x1 x5) (dest_nadd x0 x5)))) (dist (@pair nat nat (Nat.mul (dest_nadd x1 x5) (dest_nadd x0 x5)) (Nat.mul x5 (dest_nadd x0 (dest_nadd x1 x5)))))) (Nat.add (Nat.add (Nat.mul x2 x5) x3) (Nat.add (Nat.mul x4 x5) x6)).
Definition term84 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.mul x1 (dist (@pair nat nat x0 y0))) = (dist (@pair nat nat (Nat.mul x1 x0) (Nat.mul x1 y0)))) x2.
Definition term209 (x0 : nadd) := forall y0 : nadd, nadd_eq (nadd_mul x0 y0) (nadd_mul y0 x0).
Definition term30 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le x1 x0) -> (Peano.le x0 y0) -> Peano.le x1 y0.
Definition term195 (x0 : nadd) (x1 : nadd) (x2 : nat) := @pair nat nat (Nat.mul x2 (dest_nadd x0 (dest_nadd x1 x2))).
Definition term145 (x0 : nadd) (x1 : nadd) (x2 : nat) := Nat.mul x2 (dist (@pair nat nat (dest_nadd x1 (dest_nadd x0 x2)) (dest_nadd x0 (dest_nadd x1 x2)))).
Definition term102 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => (nadd_eq x0 y0) = (exists y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 y2) (dest_nadd y0 y2))) y1)) x1.
Definition term174 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := Nat.add (Nat.add (Nat.mul x0 x2) (Nat.mul x1 x2)) (Nat.add x3 x4).
Definition term52 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (Nat.add (dist (@pair nat nat x0 x1)) (dist (@pair nat nat x1 x2))) x3.
Definition term188 (x0 : nat) (x1 : nat) (x2 : nadd) (x3 : nadd) (x4 : nat) (x5 : nat) (x6 : nat) := (Peano.le (dist (@pair nat nat (Nat.mul x5 (dest_nadd x3 (dest_nadd x2 x5))) (Nat.mul (dest_nadd x3 x5) (dest_nadd x2 x5)))) (Nat.add (Nat.mul x0 x5) x1)) /\ (Peano.le (dist (@pair nat nat (Nat.mul (dest_nadd x3 x5) (dest_nadd x2 x5)) (Nat.mul x5 (dest_nadd x2 (dest_nadd x3 x5))))) (Nat.add (Nat.mul x4 x5) x6)).
Definition term122 (x0 : nadd) (x1 : nadd) (x2 : nat) := Peano.le (dist (@pair nat nat (dest_nadd x1 (dest_nadd x0 x2)) (dest_nadd x0 (dest_nadd x1 x2)))).
Definition term71 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq nat (Nat.add (Nat.add x0 x1) (Nat.add x2 x3)).
Definition term35 (x0 : nat) (x1 : nat) := (Peano.le x1 x0) -> forall y0 : nat, (Peano.le x0 y0) -> Peano.le x1 y0.
Definition term108 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term90 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, exists y2 : nat, exists y3 : nat, forall y4 : nat, Peano.le (dist (@pair nat nat (Nat.mul y4 (dest_nadd y0 (dest_nadd y1 y4))) (Nat.mul (dest_nadd y0 y4) (dest_nadd y1 y4)))) (Nat.add (Nat.mul y2 y4) y3)) x0.
Definition term81 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.mul x0 (dist (@pair nat nat y0 y1))) = (dist (@pair nat nat (Nat.mul x0 y0) (Nat.mul x0 y1))).
Definition term74 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.mul (Nat.add x0 y0) y1) = (Nat.add (Nat.mul x0 y1) (Nat.mul y0 y1)).
Definition term60 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (exists y3 : nat, Peano.le (Nat.add (dist (@pair nat nat y0 y3)) (dist (@pair nat nat y3 y1))) y2) -> Peano.le (dist (@pair nat nat y0 y1)) y2.
Definition term59 (x0 : nat) := forall y0 : nat, forall y1 : nat, (exists y2 : nat, Peano.le (Nat.add (dist (@pair nat nat x0 y2)) (dist (@pair nat nat y2 y0))) y1) -> Peano.le (dist (@pair nat nat x0 y0)) y1.
Definition term46 := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, (Peano.le (Nat.add (dist (@pair nat nat y1 y0)) (dist (@pair nat nat y0 y2))) y3) -> Peano.le (dist (@pair nat nat y1 y2)) y3.
Definition term45 (x0 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.le (Nat.add (dist (@pair nat nat y0 x0)) (dist (@pair nat nat x0 y1))) y2) -> Peano.le (dist (@pair nat nat y0 y1)) y2.
Definition term44 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add (dist (@pair nat nat x1 x0)) (dist (@pair nat nat x0 y0))) y1) -> Peano.le (dist (@pair nat nat x1 y0)) y1.
Definition term37 := forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> forall y2 : nat, (Peano.le y1 y2) -> Peano.le y0 y2.
Definition term28 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le x0 y0) -> (Peano.le y0 y1) -> Peano.le x0 y1.
Definition term26 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.le y0 y1) -> (Peano.le y1 y2) -> Peano.le y0 y2.
Definition term21 (x0 : nat) := forall y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat x0 y1)) (Nat.add (dist (@pair nat nat x0 y0)) (dist (@pair nat nat y0 y1))).
Definition term11 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le x1 y1)) -> Peano.le (Nat.add x0 x1) (Nat.add y0 y1).
Definition term9 (x0 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le x0 y1) /\ (Peano.le y0 y2)) -> Peano.le (Nat.add x0 y0) (Nat.add y1 y2).
Definition term7 := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.add y0 y1) (Nat.add y2 y3).
Definition term116 (x0 : nadd) (x1 : nadd) (x2 : nat) := @pair nat nat (dest_nadd x0 (dest_nadd x1 x2)).
Definition term176 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : nat) (x6 : nat) := Peano.le (dist (@pair nat nat (Nat.mul x4 (dest_nadd x1 (dest_nadd x0 x4))) (Nat.mul x4 (dest_nadd x0 (dest_nadd x1 x4))))) (Nat.add (Nat.add (Nat.mul x2 x4) (Nat.mul x3 x4)) (Nat.add x5 x6)).
Definition term119 (x0 : nadd) (x1 : nadd) (x2 : nat) := dist (@pair nat nat (dest_nadd (nadd_mul x1 x0) x2) (dest_nadd (nadd_mul x0 x1) x2)).
Definition term49 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (Nat.add (dist (@pair nat nat x1 x0)) (dist (@pair nat nat x0 y0))) y1) -> Peano.le (dist (@pair nat nat x1 y0)) y1) x2.
Definition term12 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le x1 y1)) -> Peano.le (Nat.add x0 x1) (Nat.add y0 y1)) x2.
Definition term48 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le (Nat.add (dist (@pair nat nat y0 x0)) (dist (@pair nat nat x0 y1))) y2) -> Peano.le (dist (@pair nat nat y0 y1)) y2) x1.
Definition term10 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.le x0 y1) /\ (Peano.le y0 y2)) -> Peano.le (Nat.add x0 y0) (Nat.add y1 y2)) x1.
Definition term55 (x0 : nat) (x1 : nat) (x2 : nat) := exists y0 : nat, Peano.le (Nat.add (dist (@pair nat nat x0 y0)) (dist (@pair nat nat y0 x1))) x2.
Definition term96 (x0 : nadd) := forall y0 : nadd, (dest_nadd (nadd_mul x0 y0)) = (fun y1 : nat => dest_nadd x0 (dest_nadd y0 y1)).
Definition term109 (x0 : nat -> nat) (x1 : nat) := (fun y0 : nat => x0 y0) x1.
Definition term162 (x0 : nadd) (x1 : nadd) (x2 : nat) := dist (@pair nat nat (Nat.mul x2 (dest_nadd x1 (dest_nadd x0 x2))) (Nat.mul x2 (dest_nadd x0 (dest_nadd x1 x2)))).
Definition term77 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.mul (Nat.add x0 x1) y0) = (Nat.add (Nat.mul x0 y0) (Nat.mul x1 y0))) x2.
Definition term184 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat) := (fun y0 : nat => Peano.le (dist (@pair nat nat (Nat.mul y0 (dest_nadd x0 (dest_nadd x1 y0))) (Nat.mul (dest_nadd x0 y0) (dest_nadd x1 y0)))) (Nat.add (Nat.mul x2 y0) x3)) x4.
Definition term31 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.le x1 x0) -> (Peano.le x0 y0) -> Peano.le x1 y0) x2.
Definition term66 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.add (Nat.add x1 x0) x2) = (Nat.add x1 (Nat.add x0 x2))) /\ ((Nat.add x1 (Nat.add x0 x2)) = (Nat.add x0 (Nat.add x1 x2))).
Definition term202 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : nat) := forall y0 : nat, Peano.le (dist (@pair nat nat (Nat.mul y0 (dest_nadd x1 (dest_nadd x0 y0))) (Nat.mul y0 (dest_nadd x0 (dest_nadd x1 y0))))) (Nat.add (Nat.mul (Nat.add x2 x3) y0) (Nat.add x4 x5)).
Definition term95 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, (dest_nadd (nadd_mul y0 y1)) = (fun y2 : nat => dest_nadd y0 (dest_nadd y1 y2))) x0.
Definition term128 (x0 : nadd) (x1 : nadd) (x2 : nat) := forall y0 : nat, Peano.le (dist (@pair nat nat (dest_nadd x1 (dest_nadd x0 y0)) (dest_nadd x0 (dest_nadd x1 y0)))) x2.
Definition term127 (x0 : nadd) (x1 : nadd) (x2 : nat) := forall y0 : nat, Peano.le (dist (@pair nat nat (dest_nadd (nadd_mul x1 x0) y0) (dest_nadd (nadd_mul x0 x1) y0))) x2.
Definition term104 (x0 : nadd) (x1 : nadd) := nadd_eq (nadd_mul x1 x0) (nadd_mul x0 x1).
Definition term78 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.add x0 x1) x2.
Definition term79 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x0 x2) (Nat.mul x1 x2).
Definition term99 (x0 : nadd) (x1 : nadd) := fun y0 : nat => dest_nadd x0 (dest_nadd x1 y0).
Definition term83 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.mul x1 (dist (@pair nat nat x0 y0))) = (dist (@pair nat nat (Nat.mul x1 x0) (Nat.mul x1 y0))).
Definition term110 (x0 : nadd) (x1 : nadd) (x2 : nat) := (fun y0 : nat => (fun y1 : nat => dest_nadd x0 (dest_nadd x1 y1)) y0) x2.
Definition term144 (x0 : nadd) (x1 : nadd) (x2 : nat) := Nat.mul x2 ((fun y0 : nat => dist (@pair nat nat (dest_nadd x1 (dest_nadd x0 y0)) (dest_nadd x0 (dest_nadd x1 y0)))) x2).
Definition term1 (x0 : nat) := forall y0 : nat, (Nat.mul x0 y0) = (Nat.mul y0 x0).
Definition term69 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.add (Nat.add x0 x1) (Nat.add x2 x3).
Definition term191 (x0 : nadd) (x1 : nadd) (x2 : nat) := Nat.mul (dest_nadd x0 x2) (dest_nadd x1 x2).
Definition term147 (x0 : nadd) (x1 : nadd) (x2 : nat) := Peano.le (Nat.mul x2 (dist (@pair nat nat (dest_nadd x1 (dest_nadd x0 x2)) (dest_nadd x0 (dest_nadd x1 x2))))).
Definition term107 (x0 : nadd) (x1 : nadd) (x2 : nat) := (fun y0 : nat => dest_nadd x0 (dest_nadd x1 y0)) x2.
Definition term166 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) := forall y0 : nat, Peano.le (dist (@pair nat nat (Nat.mul y0 (dest_nadd x1 (dest_nadd x0 y0))) (Nat.mul y0 (dest_nadd x0 (dest_nadd x1 y0))))) (Nat.add (Nat.mul x2 y0) x3).
Definition term132 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) := forall y0 : nat, Peano.le (dist (@pair nat nat (Nat.mul y0 (dest_nadd x0 (dest_nadd x1 y0))) (Nat.mul (dest_nadd x0 y0) (dest_nadd x1 y0)))) (Nat.add (Nat.mul x2 y0) x3).
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.mul x0 y0) = (Nat.mul y0 x0)) x1.
Definition term91 (x0 : nadd) := forall y0 : nadd, exists y1 : nat, exists y2 : nat, forall y3 : nat, Peano.le (dist (@pair nat nat (Nat.mul y3 (dest_nadd x0 (dest_nadd y0 y3))) (Nat.mul (dest_nadd x0 y3) (dest_nadd y0 y3)))) (Nat.add (Nat.mul y1 y3) y2).
Definition term175 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : nat) (x6 : nat) := Peano.le (dist (@pair nat nat (Nat.mul x4 (dest_nadd x1 (dest_nadd x0 x4))) (Nat.mul x4 (dest_nadd x0 (dest_nadd x1 x4))))) (Nat.add (Nat.mul (Nat.add x2 x3) x4) (Nat.add x5 x6)).
Definition term178 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : nat) (x6 : nat) := Peano.le (dist (@pair nat nat (Nat.mul x5 (dest_nadd x1 (dest_nadd x0 x5))) (Nat.mul x5 (dest_nadd x0 (dest_nadd x1 x5))))) (Nat.add (Nat.add (Nat.mul x2 x5) x3) (Nat.add (Nat.mul x4 x5) x6)).
Definition term172 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.add (Nat.mul x0 x2) (Nat.mul x1 x2)).
Definition term68 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add x0 (Nat.add x1 x2).
Definition term58 (x0 : nat) (x1 : nat) := forall y0 : nat, (exists y1 : nat, Peano.le (Nat.add (dist (@pair nat nat x0 y1)) (dist (@pair nat nat y1 x1))) y0) -> Peano.le (dist (@pair nat nat x0 x1)) y0.
Definition term141 (x0 : nadd) (x1 : nadd) := fun y0 : nat => forall y1 : nat, Peano.le ((fun y2 : nat => dist (@pair nat nat (dest_nadd x1 (dest_nadd x0 y2)) (dest_nadd x0 (dest_nadd x1 y2)))) y1) y0.
Definition term130 (x0 : nadd) (x1 : nadd) := fun y0 : nat => forall y1 : nat, Peano.le (dist (@pair nat nat (dest_nadd x1 (dest_nadd x0 y1)) (dest_nadd x0 (dest_nadd x1 y1)))) y0.
Definition term129 (x0 : nadd) (x1 : nadd) := fun y0 : nat => forall y1 : nat, Peano.le (dist (@pair nat nat (dest_nadd (nadd_mul x1 x0) y1) (dest_nadd (nadd_mul x0 x1) y1))) y0.
Definition term135 (x0 : nadd) (x1 : nadd) := fun y0 : nat => dist (@pair nat nat (dest_nadd x1 (dest_nadd x0 y0)) (dest_nadd x0 (dest_nadd x1 y0))).
Definition term146 (x0 : nadd) (x1 : nadd) (x2 : nat) := Peano.le (Nat.mul x2 ((fun y0 : nat => dist (@pair nat nat (dest_nadd x1 (dest_nadd x0 y0)) (dest_nadd x0 (dest_nadd x1 y0)))) x2)).
Definition term186 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat) := and (Peano.le (dist (@pair nat nat (Nat.mul x3 (dest_nadd x0 (dest_nadd x1 x3))) (Nat.mul (dest_nadd x0 x3) (dest_nadd x1 x3)))) (Nat.add (Nat.mul x2 x3) x4)).
Definition term39 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) -> forall y2 : nat, (Peano.le y1 y2) -> Peano.le y0 y2) x0.
Definition term3 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (dist (@pair nat nat y0 y1)) = (dist (@pair nat nat y1 y0))) x0.
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) x0.
Definition term56 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nat => Peano.le (Nat.add (dist (@pair nat nat x0 y0)) (dist (@pair nat nat y0 x1))) x2.
Definition term16 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le x0 x1) /\ (Peano.le x2 x3).
Definition term150 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat) := Peano.le (Nat.mul x3 (dist (@pair nat nat (dest_nadd x1 (dest_nadd x0 x3)) (dest_nadd x0 (dest_nadd x1 x3))))) (Nat.add (Nat.mul x2 x3) x4).
Definition term13 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, ((Peano.le x0 x2) /\ (Peano.le x1 y0)) -> Peano.le (Nat.add x0 x1) (Nat.add x2 y0).
Definition term43 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, (Peano.le (Nat.add (dist (@pair nat nat x1 x0)) (dist (@pair nat nat x0 x2))) y0) -> Peano.le (dist (@pair nat nat x1 x2)) y0.
Definition term41 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le (dist (@pair nat nat x1 x2)) (Nat.add (dist (@pair nat nat x1 x0)) (dist (@pair nat nat x0 x2)))) -> forall y0 : nat, (Peano.le (Nat.add (dist (@pair nat nat x1 x0)) (dist (@pair nat nat x0 x2))) y0) -> Peano.le (dist (@pair nat nat x1 x2)) y0.
Definition term197 (x0 : nadd) (x1 : nadd) (x2 : nat) := @pair nat nat (Nat.mul x2 (dest_nadd x0 (dest_nadd x1 x2))) (Nat.mul (dest_nadd x0 x2) (dest_nadd x1 x2)).
Definition term196 (x0 : nadd) (x1 : nadd) (x2 : nat) := @pair nat nat (Nat.mul x2 (dest_nadd x1 (dest_nadd x0 x2))) (Nat.mul (dest_nadd x0 x2) (dest_nadd x1 x2)).
Definition term149 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat) := Peano.le (Nat.mul x3 ((fun y0 : nat => dist (@pair nat nat (dest_nadd x1 (dest_nadd x0 y0)) (dest_nadd x0 (dest_nadd x1 y0)))) x3)) (Nat.add (Nat.mul x2 x3) x4).
Definition term32 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x1 x0) -> (Peano.le x0 x2) -> Peano.le x1 x2.
Definition term18 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.add y0 y1) (Nat.add y2 y3)) -> Peano.le (Nat.add x0 x1) (Nat.add x2 x3).
Definition term76 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.mul (Nat.add x0 x1) y0) = (Nat.add (Nat.mul x0 y0) (Nat.mul x1 y0)).
Definition term123 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) := Peano.le (dist (@pair nat nat (dest_nadd (nadd_mul x1 x0) x2) (dest_nadd (nadd_mul x0 x1) x2))) x3.
Definition term101 (x0 : nadd) := forall y0 : nadd, (nadd_eq x0 y0) = (exists y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 y2) (dest_nadd y0 y2))) y1).
Definition term190 (x0 : nadd) (x1 : nadd) (x2 : nat) := dist (@pair nat nat (Nat.mul x2 (dest_nadd x1 (dest_nadd x0 x2))) (Nat.mul (dest_nadd x0 x2) (dest_nadd x1 x2))).
Definition term182 (x0 : nadd) (x1 : nadd) (x2 : nat) := dist (@pair nat nat (Nat.mul x2 (dest_nadd x0 (dest_nadd x1 x2))) (Nat.mul (dest_nadd x0 x2) (dest_nadd x1 x2))).
Definition term152 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) := fun y0 : nat => Peano.le (Nat.mul y0 (dist (@pair nat nat (dest_nadd x1 (dest_nadd x0 y0)) (dest_nadd x0 (dest_nadd x1 y0))))) (Nat.add (Nat.mul x2 y0) x3).
Definition term170 (x0 : nadd) (x1 : nadd) := exists y0 : nat, exists y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (Nat.mul y2 (dest_nadd x1 (dest_nadd x0 y2))) (Nat.mul y2 (dest_nadd x0 (dest_nadd x1 y2))))) (Nat.add (Nat.mul y0 y2) y1).
Definition term161 (x0 : nadd) (x1 : nadd) := exists y0 : nat, exists y1 : nat, forall y2 : nat, Peano.le (Nat.mul y2 (dist (@pair nat nat (dest_nadd x1 (dest_nadd x0 y2)) (dest_nadd x0 (dest_nadd x1 y2))))) (Nat.add (Nat.mul y0 y2) y1).
Definition term134 (x0 : nadd) (x1 : nadd) := exists y0 : nat, exists y1 : nat, forall y2 : nat, Peano.le (Nat.mul y2 ((fun y3 : nat => dist (@pair nat nat (dest_nadd x1 (dest_nadd x0 y3)) (dest_nadd x0 (dest_nadd x1 y3)))) y2)) (Nat.add (Nat.mul y0 y2) y1).
Definition term93 (x0 : nadd) (x1 : nadd) := exists y0 : nat, exists y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (Nat.mul y2 (dest_nadd x0 (dest_nadd x1 y2))) (Nat.mul (dest_nadd x0 y2) (dest_nadd x1 y2)))) (Nat.add (Nat.mul y0 y2) y1).
Definition term89 (x0 : nat -> nat) := exists y0 : nat, exists y1 : nat, forall y2 : nat, Peano.le (Nat.mul y2 (x0 y2)) (Nat.add (Nat.mul y0 y2) y1).
Definition term53 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (dist (@pair nat nat x0 x1)) x2.
Definition term189 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat) := True /\ (Peano.le (dist (@pair nat nat (Nat.mul (dest_nadd x1 x3) (dest_nadd x0 x3)) (Nat.mul x3 (dest_nadd x0 (dest_nadd x1 x3))))) (Nat.add (Nat.mul x2 x3) x4)).
Definition term148 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x0 x1) x2.
Definition term180 (x0 : nadd) (x1 : nadd) (x2 : nat) := Nat.mul x2 (dest_nadd x0 (dest_nadd x1 x2)).
Definition term34 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le x0 y0) -> Peano.le x1 y0.
Definition term57 (x0 : nat) (x1 : nat) (x2 : nat) := (exists y0 : nat, Peano.le (Nat.add (dist (@pair nat nat x0 y0)) (dist (@pair nat nat y0 x1))) x2) -> Peano.le (dist (@pair nat nat x0 x1)) x2.
Definition term5 (x0 : nat) (x1 : nat) := (fun y0 : nat => (dist (@pair nat nat x0 y0)) = (dist (@pair nat nat y0 x0))) x1.
Definition term65 (a0 : Type') (x0 : a0) := (fun y0 : a0 => (y0 = y0) = True) x0.
Definition term111 (x0 : nadd) (x1 : nadd) (x2 : nat) := dest_nadd x0 (dest_nadd x1 x2).
Definition term72 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq nat (Nat.add x0 (Nat.add x1 (Nat.add x2 x3))).
Definition term173 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := Nat.add (Nat.mul (Nat.add x0 x1) x2) (Nat.add x3 x4).
Definition term194 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat) := Peano.le (dist (@pair nat nat (Nat.mul x3 (dest_nadd x1 (dest_nadd x0 x3))) (Nat.mul (dest_nadd x0 x3) (dest_nadd x1 x3)))) (Nat.add (Nat.mul x2 x3) x4).
Definition term187 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat) := Peano.le (dist (@pair nat nat (Nat.mul (dest_nadd x1 x3) (dest_nadd x0 x3)) (Nat.mul x3 (dest_nadd x0 (dest_nadd x1 x3))))) (Nat.add (Nat.mul x2 x3) x4).
Definition term185 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat) := Peano.le (dist (@pair nat nat (Nat.mul x3 (dest_nadd x0 (dest_nadd x1 x3))) (Nat.mul (dest_nadd x0 x3) (dest_nadd x1 x3)))) (Nat.add (Nat.mul x2 x3) x4).
Definition term164 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat) := Peano.le (dist (@pair nat nat (Nat.mul x3 (dest_nadd x1 (dest_nadd x0 x3))) (Nat.mul x3 (dest_nadd x0 (dest_nadd x1 x3))))) (Nat.add (Nat.mul x2 x3) x4).
Definition term15 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Peano.le x0 x2) /\ (Peano.le x1 x3)) -> Peano.le (Nat.add x0 x1) (Nat.add x2 x3).
Definition term177 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := Nat.add (Nat.add (Nat.mul x0 x3) x1) (Nat.add (Nat.mul x2 x3) x4).
Definition term40 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le x0 y0) -> forall y1 : nat, (Peano.le y0 y1) -> Peano.le x0 y1) x1.
Definition term165 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) := fun y0 : nat => Peano.le (dist (@pair nat nat (Nat.mul y0 (dest_nadd x1 (dest_nadd x0 y0))) (Nat.mul y0 (dest_nadd x0 (dest_nadd x1 y0))))) (Nat.add (Nat.mul x2 y0) x3).
Definition term50 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => (Peano.le (Nat.add (dist (@pair nat nat x1 x0)) (dist (@pair nat nat x0 x2))) y0) -> Peano.le (dist (@pair nat nat x1 x2)) y0) x3.
Definition term183 (x0 : nadd) (x1 : nadd) (x2 : nat) := dist (@pair nat nat (Nat.mul (dest_nadd x1 x2) (dest_nadd x0 x2)) (Nat.mul x2 (dest_nadd x0 (dest_nadd x1 x2)))).
Definition term23 (x0 : nat) (x1 : nat) := forall y0 : nat, Peano.le (dist (@pair nat nat x0 y0)) (Nat.add (dist (@pair nat nat x0 x1)) (dist (@pair nat nat x1 y0))).
