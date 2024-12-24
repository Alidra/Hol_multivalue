Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term14 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.mul x1 (Nat.add x0 y0)) = (Nat.add (Nat.mul x1 x0) (Nat.mul x1 y0))) x2.
Definition term252 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := exists y0 : nat, (Nat.add (Nat.add (Nat.mul x1 (Nat.mul x2 x3)) (Nat.mul x2 (Nat.mul x3 (dest_nadd x0 (NUMERAL 0))))) (Nat.add (Nat.mul x1 x3) (Nat.mul x3 (dest_nadd x0 (NUMERAL 0))))) = (Nat.add (Nat.add (Nat.mul x1 x3) (Nat.mul x1 (Nat.mul x2 x3))) y0).
Definition term229 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := exists y0 : nat, (Nat.mul x3 (Nat.add (Nat.mul (Nat.add x1 (dest_nadd x0 (NUMERAL 0))) x2) (Nat.add x1 (dest_nadd x0 (NUMERAL 0))))) = (Nat.add (Nat.mul x1 (Nat.add x3 (Nat.mul x2 x3))) y0).
Definition term142 (x0 : nat) (x1 : nat) (x2 : nadd) := exists y0 : nat, (Nat.add (Nat.add (Nat.mul x0 x1) (Nat.mul x1 (dest_nadd x2 (NUMERAL 0)))) (Nat.add x0 (dest_nadd x2 (NUMERAL 0)))) = (Nat.add (Nat.add (dest_nadd x2 (NUMERAL 0)) (Nat.mul x1 (dest_nadd x2 (NUMERAL 0)))) y0).
Definition term259 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nadd) := @eq nat (Nat.add (Nat.mul x0 x2) (Nat.add (Nat.mul x0 (Nat.mul x1 x2)) (Nat.add (Nat.mul x1 (Nat.mul x2 (dest_nadd x3 (NUMERAL 0)))) (Nat.mul x2 (dest_nadd x3 (NUMERAL 0)))))).
Definition term153 (x0 : nadd) (x1 : nat) (x2 : nat) := Nat.add (dest_nadd x0 (NUMERAL 0)) (Nat.add (Nat.mul x1 (dest_nadd x0 (NUMERAL 0))) (Nat.add (Nat.mul x2 x1) x2)).
Definition term193 (x0 : nat) (x1 : nadd) (x2 : nat) := Peano.le (dist (@pair nat nat (Nat.mul x2 (dest_nadd x1 (Nat.mul x0 x2))) (Nat.mul x2 (Nat.mul x0 (dest_nadd x1 x2))))).
Definition term107 (x0 : nat) (x1 : nat) (x2 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.le (Nat.add y0 y1) y2) -> Peano.le (dist (@pair nat nat y0 y1)) y2) -> Peano.le (dist (@pair nat nat x0 x1)) x2.
Definition term186 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nadd) := (~ (x0 = (NUMERAL 0))) -> Peano.le (dist (@pair nat nat (dest_nadd x3 (Nat.mul x1 x0)) (Nat.mul x1 (dest_nadd x3 x0)))) (Nat.add (Nat.mul (Nat.add x2 (dest_nadd x3 (NUMERAL 0))) x1) (Nat.add x2 (dest_nadd x3 (NUMERAL 0)))).
Definition term115 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nadd) := (Peano.le (Nat.add (dest_nadd x3 (Nat.mul x1 x0)) (Nat.mul x1 (dest_nadd x3 x0))) (Nat.add (Nat.mul (Nat.add x2 (dest_nadd x3 (NUMERAL 0))) x1) (Nat.add x2 (dest_nadd x3 (NUMERAL 0))))) -> Peano.le (dist (@pair nat nat (dest_nadd x3 (Nat.mul x1 x0)) (Nat.mul x1 (dest_nadd x3 x0)))) (Nat.add (Nat.mul (Nat.add x2 (dest_nadd x3 (NUMERAL 0))) x1) (Nat.add x2 (dest_nadd x3 (NUMERAL 0)))).
Definition term88 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x2) -> Peano.le x1 x2.
Definition term275 (x0 : nadd) := exists y0 : nat, forall y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 (Nat.mul y1 y2)) (Nat.mul y1 (dest_nadd x0 y2)))) (Nat.add (Nat.mul y0 y1) y0).
Definition term113 (x0 : nadd) := exists y0 : nat, forall y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (Nat.mul y1 (dest_nadd x0 y2)) (Nat.mul y2 (dest_nadd x0 y1)))) (Nat.mul y0 (Nat.add y1 y2)).
Definition term235 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x0 (Nat.mul x1 x2)).
Definition term227 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nadd) := (Peano.le (Nat.mul x2 (Nat.add x0 (Nat.mul x1 x0))) (Nat.mul x0 (Nat.add (Nat.mul (Nat.add x2 (dest_nadd x3 (NUMERAL 0))) x1) (Nat.add x2 (dest_nadd x3 (NUMERAL 0)))))) -> Peano.le (dist (@pair nat nat (Nat.mul x0 (dest_nadd x3 (Nat.mul x1 x0))) (Nat.mul (Nat.mul x1 x0) (dest_nadd x3 x0)))) (Nat.mul x0 (Nat.add (Nat.mul (Nat.add x2 (dest_nadd x3 (NUMERAL 0))) x1) (Nat.add x2 (dest_nadd x3 (NUMERAL 0))))).
Definition term163 (x0 : nat) (x1 : nat) (x2 : nadd) := Nat.add x0 (Nat.add (Nat.mul x1 (dest_nadd x2 (NUMERAL 0))) (Nat.add (Nat.mul x0 x1) (dest_nadd x2 (NUMERAL 0)))).
Definition term173 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Nat.add y0 y1) = (Nat.add y0 y2)) = (y1 = y2)) x0.
Definition term101 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le (Nat.add y0 y1) y2) -> Peano.le (dist (@pair nat nat y0 y1)) y2) x0.
Definition term82 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le y0 y1) -> (Peano.le y1 y2) -> Peano.le y0 y2) x0.
Definition term74 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((y0 = (NUMERAL 0)) \/ (Peano.le y1 y2)) = (Peano.le (Nat.mul y0 y1) (Nat.mul y0 y2))) x0.
Definition term67 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.mul y0 (dist (@pair nat nat y1 y2))) = (dist (@pair nat nat (Nat.mul y0 y1) (Nat.mul y0 y2)))) x0.
Definition term31 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.mul y0 (Nat.mul y1 y2)) = (Nat.mul (Nat.mul y0 y1) y2)) x0.
Definition term17 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.mul (Nat.add y0 y1) y2) = (Nat.add (Nat.mul y0 y2) (Nat.mul y1 y2))) x0.
Definition term10 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.mul y0 (Nat.add y1 y2)) = (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y2))) x0.
Definition term3 (a0 : Type') (x0 : a0) := exists y0 : a0, x0 = y0.
Definition term266 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq nat (Nat.add x0 (Nat.add (Nat.mul x1 x3) (Nat.mul x1 (Nat.mul x2 x3)))).
Definition term171 (x0 : nat) (x1 : nat) (x2 : nadd) := @eq nat (Nat.add x0 (Nat.add (Nat.mul x1 (dest_nadd x2 (NUMERAL 0))) (dest_nadd x2 (NUMERAL 0)))).
Definition term152 (x0 : nat) (x1 : nat) (x2 : nadd) := @eq nat (Nat.add x0 (Nat.add (Nat.mul x0 x1) (Nat.add (Nat.mul x1 (dest_nadd x2 (NUMERAL 0))) (dest_nadd x2 (NUMERAL 0))))).
Definition term148 (x0 : nat) (x1 : nat) (x2 : nadd) := Nat.add (Nat.mul x0 x1) (Nat.add x0 (Nat.add (Nat.mul x1 (dest_nadd x2 (NUMERAL 0))) (dest_nadd x2 (NUMERAL 0)))).
Definition term96 (x0 : nat) (x1 : nat) := (Peano.le (dist (@pair nat nat x0 x1)) (Nat.add x0 x1)) -> forall y0 : nat, (Peano.le (Nat.add x0 x1) y0) -> Peano.le (dist (@pair nat nat x0 x1)) y0.
Definition term226 (x0 : nat) (x1 : nadd) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.le (Nat.mul x0 (Nat.add y1 y0)) y2) -> Peano.le (dist (@pair nat nat (Nat.mul y1 (dest_nadd x1 y0)) (Nat.mul y0 (dest_nadd x1 y1)))) y2) -> forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.le (Nat.mul x0 (Nat.add y1 y0)) y2) -> Peano.le (dist (@pair nat nat (Nat.mul y1 (dest_nadd x1 y0)) (Nat.mul y0 (dest_nadd x1 y1)))) y2.
Definition term108 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.le (Nat.add y0 y1) y2) -> Peano.le (dist (@pair nat nat y0 y1)) y2) -> forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.le (Nat.add y0 y1) y2) -> Peano.le (dist (@pair nat nat y0 y1)) y2.
Definition term93 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.le y0 y1) -> (Peano.le y1 y2) -> Peano.le y0 y2) -> forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> forall y2 : nat, (Peano.le y1 y2) -> Peano.le y0 y2.
Definition term222 (x0 : nat) (x1 : nat) (x2 : nadd) (x3 : nat) (x4 : nat) := (Peano.le (Nat.mul x0 (Nat.add x3 x1)) x4) -> Peano.le (dist (@pair nat nat (Nat.mul x3 (dest_nadd x2 x1)) (Nat.mul x1 (dest_nadd x2 x3)))) x4.
Definition term265 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq nat (Nat.add (Nat.add (Nat.mul x0 x2) (Nat.mul x0 (Nat.mul x1 x2))) x3).
Definition term264 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.add x0 (Nat.add (Nat.mul x1 x3) (Nat.mul x1 (Nat.mul x2 x3))).
Definition term39 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = (NUMERAL 0)) \/ (Peano.le x1 x2).
Definition term73 (x0 : nat) (x1 : nat) (x2 : nat) := dist (@pair nat nat (Nat.mul x1 x0) (Nat.mul x1 x2)).
Definition term242 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nadd) := Nat.add (Nat.add (Nat.mul x1 (Nat.mul x0 x2)) (Nat.mul x0 (Nat.mul x2 (dest_nadd x3 (NUMERAL 0))))) (Nat.add (Nat.mul x1 x2) (Nat.mul x2 (dest_nadd x3 (NUMERAL 0)))).
Definition term134 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x0 x1).
Definition term40 (x0 : nat) (x1 : nat) := fun y0 : nat => (Peano.le (Nat.mul x0 x1) (Nat.mul x0 y0)) = ((x0 = (NUMERAL 0)) \/ (Peano.le x1 y0)).
Definition term172 (x0 : nadd) (x1 : nat) (x2 : nat) := @eq nat (Nat.add (dest_nadd x0 (NUMERAL 0)) (Nat.add (Nat.mul x1 (dest_nadd x0 (NUMERAL 0))) (Nat.add (Nat.mul x2 x1) x2))).
Definition term224 (x0 : nat) (x1 : nadd) (x2 : nat) (x3 : nat) := Peano.le (dist (@pair nat nat (Nat.mul x2 (dest_nadd x1 x0)) (Nat.mul x0 (dest_nadd x1 x2)))) x3.
Definition term60 (x0 : Prop) (x1 : Prop) := @eq Prop (((~ x0) -> x1) = (x0 \/ x1)).
Definition term183 (x0 : nat) (x1 : nat) := exists y0 : nat, (Nat.add (Nat.mul x1 x0) x1) = y0.
Definition term176 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Nat.add x0 x1) = (Nat.add x0 y0)) = (x1 = y0).
Definition term273 (x0 : nat) (x1 : nat) (x2 : nadd) := forall y0 : nat, Peano.le (dist (@pair nat nat (dest_nadd x2 (Nat.mul x0 y0)) (Nat.mul x0 (dest_nadd x2 y0)))) (Nat.add (Nat.mul (Nat.add x1 (dest_nadd x2 (NUMERAL 0))) x0) (Nat.add x1 (dest_nadd x2 (NUMERAL 0)))).
Definition term243 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nadd) := @eq nat (Nat.mul x0 (Nat.add (Nat.mul (Nat.add x2 (dest_nadd x3 (NUMERAL 0))) x1) (Nat.add x2 (dest_nadd x3 (NUMERAL 0))))).
Definition term155 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x1 x0) x1.
Definition term256 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nadd) := Nat.add (Nat.mul x0 (Nat.mul x1 x2)) (Nat.add (Nat.mul x0 x2) (Nat.add (Nat.mul x1 (Nat.mul x2 (dest_nadd x3 (NUMERAL 0)))) (Nat.mul x2 (dest_nadd x3 (NUMERAL 0))))).
Definition term35 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.mul x0 (Nat.mul x1 y0)) = (Nat.mul (Nat.mul x0 x1) y0)) x2.
Definition term160 (x0 : nat) (x1 : nat) (x2 : nadd) := Nat.add x0 (Nat.add (Nat.mul x0 x1) (dest_nadd x2 (NUMERAL 0))).
Definition term263 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.add (Nat.mul x1 x3) (Nat.add x0 (Nat.mul x1 (Nat.mul x2 x3))).
Definition term25 (x0 : nat) := forall y0 : nat, (Peano.le x0 y0) = (exists y1 : nat, y0 = (Nat.add x0 y1)).
Definition term59 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term97 (x0 : nat) (x1 : nat) := dist (@pair nat nat x0 x1).
Definition term127 (x0 : nat) (x1 : nadd) (x2 : nat) := Nat.add (dest_nadd x1 (Nat.mul x0 x2)) (Nat.mul x0 (dest_nadd x1 x2)).
Definition term184 (x0 : nat) := exists y0 : nat, x0 = y0.
Definition term185 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nadd) := Peano.le (dist (@pair nat nat (dest_nadd x3 (Nat.mul x1 x0)) (Nat.mul x1 (dest_nadd x3 x0)))) (Nat.add (Nat.mul (Nat.add x2 (dest_nadd x3 (NUMERAL 0))) x1) (Nat.add x2 (dest_nadd x3 (NUMERAL 0)))).
Definition term5 (a0 : Type') := fun y0 : a0 => exists y1 : a0, y0 = y1.
Definition term143 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.add x0 x1) x2.
Definition term139 (x0 : nat) (x1 : nat) (x2 : nadd) := Nat.add (Nat.add (Nat.mul x1 x0) (Nat.mul x0 (dest_nadd x2 (NUMERAL 0)))) (Nat.add x1 (dest_nadd x2 (NUMERAL 0))).
Definition term170 (x0 : nat) (x1 : nadd) (x2 : nat) := @eq nat (Nat.add (Nat.add (dest_nadd x1 (NUMERAL 0)) (Nat.mul x0 (dest_nadd x1 (NUMERAL 0)))) x2).
Definition term91 (x0 : nat) := forall y0 : nat, (Peano.le x0 y0) -> forall y1 : nat, (Peano.le y0 y1) -> Peano.le x0 y1.
Definition term79 (x0 : nat) (x1 : nat) := (fun y0 : nat => Peano.le (dist (@pair nat nat x0 y0)) (Nat.add x0 y0)) x1.
Definition term168 (x0 : nat) (x1 : nadd) (x2 : nat) := Nat.add (dest_nadd x1 (NUMERAL 0)) (Nat.add (Nat.mul x0 (dest_nadd x1 (NUMERAL 0))) x2).
Definition term239 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nadd) := Nat.add (Nat.add (Nat.mul x0 (Nat.mul x1 x2)) (Nat.mul x1 (Nat.mul x2 (dest_nadd x3 (NUMERAL 0))))).
Definition term246 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x0 (Nat.add x2 (Nat.mul x1 x2))).
Definition term199 (x0 : nat) (x1 : nadd) (x2 : nat) := @pair nat nat (Nat.mul x2 (dest_nadd x1 (Nat.mul x0 x2))) (Nat.mul x2 (Nat.mul x0 (dest_nadd x1 x2))).
Definition term7 (a0 : Type') := forall y0 : a0, exists y1 : a0, y0 = y1.
Definition term6 (a0 : Type') := forall y0 : a0, exists y1 : a0, y1 = y0.
Definition term150 (x0 : nat) (x1 : nadd) := Nat.add (Nat.mul x0 (dest_nadd x1 (NUMERAL 0))) (dest_nadd x1 (NUMERAL 0)).
Definition term194 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nadd) := Nat.mul x0 (Nat.add (Nat.mul (Nat.add x2 (dest_nadd x3 (NUMERAL 0))) x1) (Nat.add x2 (dest_nadd x3 (NUMERAL 0)))).
Definition term62 (x0 : Prop) := (~ False) -> x0.
Definition term245 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x0 x2) (Nat.mul x0 (Nat.mul x1 x2)).
Definition term208 (x0 : nat) (x1 : nadd) (x2 : nat) := Peano.le (dist (@pair nat nat (Nat.mul x2 (dest_nadd x1 (Nat.mul x0 x2))) (Nat.mul (Nat.mul x0 x2) (dest_nadd x1 x2)))).
Definition term202 (x0 : nat) (x1 : nadd) (x2 : nat) := Peano.le (dist (@pair nat nat (Nat.mul x2 (dest_nadd x1 (Nat.mul x0 x2))) (Nat.mul (Nat.mul x2 x0) (dest_nadd x1 x2)))).
Definition term8 (a0 : Type') (x0 : a0) := (fun y0 : a0 => exists y1 : a0, y0 = y1) x0.
Definition term72 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (dist (@pair nat nat x1 x2)).
Definition term34 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.mul x0 (Nat.mul x1 y0)) = (Nat.mul (Nat.mul x0 x1) y0).
Definition term117 (x0 : nat) (x1 : nadd) (x2 : nat) := Nat.mul x0 (dest_nadd x1 x2).
Definition term204 (x0 : nat) (x1 : nat) := Nat.mul (Nat.mul x0 x1).
Definition term254 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nadd) := Nat.add (Nat.mul x0 (Nat.mul x2 (dest_nadd x3 (NUMERAL 0)))) (Nat.add (Nat.mul x1 x2) (Nat.mul x2 (dest_nadd x3 (NUMERAL 0)))).
Definition term175 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.add x0 y0) = (Nat.add x0 y1)) = (y0 = y1)) x1.
Definition term102 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (Nat.add x0 y0) y1) -> Peano.le (dist (@pair nat nat x0 y0)) y1) x1.
Definition term84 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le x0 y0) -> (Peano.le y0 y1) -> Peano.le x0 y1) x1.
Definition term75 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((x0 = (NUMERAL 0)) \/ (Peano.le y0 y1)) = (Peano.le (Nat.mul x0 y0) (Nat.mul x0 y1))) x1.
Definition term69 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul x0 (dist (@pair nat nat y0 y1))) = (dist (@pair nat nat (Nat.mul x0 y0) (Nat.mul x0 y1)))) x1.
Definition term33 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul x0 (Nat.mul y0 y1)) = (Nat.mul (Nat.mul x0 y0) y1)) x1.
Definition term19 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul (Nat.add x0 y0) y1) = (Nat.add (Nat.mul x0 y1) (Nat.mul y0 y1))) x1.
Definition term12 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul x0 (Nat.add y0 y1)) = (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y1))) x1.
Definition term247 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.add (Nat.mul x0 x2) (Nat.mul x0 (Nat.mul x1 x2))).
Definition term111 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term200 (x0 : nat) (x1 : nadd) (x2 : nat) := @pair nat nat (Nat.mul x2 (dest_nadd x1 (Nat.mul x0 x2))) (Nat.mul (Nat.mul x2 x0) (dest_nadd x1 x2)).
Definition term123 (x0 : nadd) := dest_nadd x0 (NUMERAL 0).
Definition term268 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nadd) := @eq nat (Nat.add (Nat.mul x0 (Nat.mul x1 x2)) (Nat.add (Nat.mul x0 x2) (Nat.add (Nat.mul x1 (Nat.mul x2 (dest_nadd x3 (NUMERAL 0)))) (Nat.mul x2 (dest_nadd x3 (NUMERAL 0)))))).
Definition term271 (x0 : nat) (x1 : nat) (x2 : nadd) := fun y0 : nat => (Nat.add (Nat.mul x0 (Nat.mul x1 (dest_nadd x2 (NUMERAL 0)))) (Nat.mul x1 (dest_nadd x2 (NUMERAL 0)))) = y0.
Definition term126 (x0 : nat) (x1 : nadd) := Nat.mul x0 (dest_nadd x1 (NUMERAL 0)).
Definition term257 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nadd) := Nat.add (Nat.mul x0 x2) (Nat.add (Nat.mul x0 (Nat.mul x1 x2)) (Nat.add (Nat.mul x1 (Nat.mul x2 (dest_nadd x3 (NUMERAL 0)))) (Nat.mul x2 (dest_nadd x3 (NUMERAL 0))))).
Definition term234 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nadd) := Nat.add (Nat.mul x1 (Nat.mul x0 x2)) (Nat.mul x1 (Nat.mul x2 (dest_nadd x3 (NUMERAL 0)))).
Definition term71 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.mul x1 (dist (@pair nat nat x0 y0))) = (dist (@pair nat nat (Nat.mul x1 x0) (Nat.mul x1 y0)))) x2.
Definition term137 (x0 : nat) (x1 : nat) (x2 : nadd) := Nat.add (Nat.add (Nat.mul x0 x1) (Nat.mul x1 (dest_nadd x2 (NUMERAL 0)))).
Definition term121 (x0 : nat) := (fun y0 : nat => (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) x0.
Definition term85 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le x1 x0) -> (Peano.le x0 y0) -> Peano.le x1 y0.
Definition term198 (x0 : nadd) (x1 : nat) (x2 : nat) := @pair nat nat (Nat.mul x2 (dest_nadd x0 (Nat.mul x1 x2))).
Definition term190 (x0 : nat) (x1 : nadd) (x2 : nat) := Nat.mul x2 (dist (@pair nat nat (dest_nadd x1 (Nat.mul x0 x2)) (Nat.mul x0 (dest_nadd x1 x2)))).
Definition term267 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.add (Nat.mul x1 (Nat.mul x0 x2)) (Nat.add (Nat.mul x1 x2) x3).
Definition term205 (x0 : nat) (x1 : nadd) (x2 : nat) := Nat.mul (Nat.mul x0 x2) (dest_nadd x1 x2).
Definition term165 (x0 : nat) (x1 : nat) (x2 : nadd) := Nat.add (Nat.mul x1 (dest_nadd x2 (NUMERAL 0))) (Nat.add (Nat.mul x0 x1) (dest_nadd x2 (NUMERAL 0))).
Definition term105 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.add x0 x1) x2.
Definition term16 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x1 x0) (Nat.mul x1 x2).
Definition term27 (x0 : nat) (x1 : nat) := exists y0 : nat, x0 = (Nat.add x1 y0).
Definition term166 (x0 : nat) (x1 : nat) (x2 : nadd) := Nat.add (Nat.mul x0 x1) (Nat.add (Nat.mul x1 (dest_nadd x2 (NUMERAL 0))) (dest_nadd x2 (NUMERAL 0))).
Definition term188 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nadd) := Peano.le (Nat.mul x0 (dist (@pair nat nat (dest_nadd x3 (Nat.mul x1 x0)) (Nat.mul x1 (dest_nadd x3 x0))))) (Nat.mul x0 (Nat.add (Nat.mul (Nat.add x2 (dest_nadd x3 (NUMERAL 0))) x1) (Nat.add x2 (dest_nadd x3 (NUMERAL 0))))).
Definition term90 (x0 : nat) (x1 : nat) := (Peano.le x1 x0) -> forall y0 : nat, (Peano.le x0 y0) -> Peano.le x1 y0.
Definition term37 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.mul x0 x1) x2.
Definition term211 (x0 : nadd) (x1 : nat) (x2 : nat) := forall y0 : nat, Peano.le (dist (@pair nat nat (Nat.mul x2 (dest_nadd x0 y0)) (Nat.mul y0 (dest_nadd x0 x2)))) (Nat.mul x1 (Nat.add x2 y0)).
Definition term220 (x0 : nat) (x1 : nat) (x2 : nadd) (x3 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (Nat.mul x0 (Nat.add y0 x1)) y1) -> Peano.le (dist (@pair nat nat (Nat.mul y0 (dest_nadd x2 x1)) (Nat.mul x1 (dest_nadd x2 y0)))) y1) x3.
Definition term253 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nadd) := Nat.add (Nat.mul x1 (Nat.mul x0 x2)) (Nat.add (Nat.mul x0 (Nat.mul x2 (dest_nadd x3 (NUMERAL 0)))) (Nat.add (Nat.mul x1 x2) (Nat.mul x2 (dest_nadd x3 (NUMERAL 0))))).
Definition term237 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nadd) := Nat.add (Nat.mul x0 (Nat.mul x1 x2)) (Nat.mul x1 (Nat.mul x2 (dest_nadd x3 (NUMERAL 0)))).
Definition term169 (x0 : nat) (x1 : nadd) (x2 : nat) := Nat.add (Nat.mul x0 (dest_nadd x1 (NUMERAL 0))) (Nat.add (dest_nadd x1 (NUMERAL 0)) x2).
Definition term274 (x0 : nat) (x1 : nadd) := forall y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (dest_nadd x1 (Nat.mul y0 y1)) (Nat.mul y0 (dest_nadd x1 y1)))) (Nat.add (Nat.mul (Nat.add x0 (dest_nadd x1 (NUMERAL 0))) y0) (Nat.add x0 (dest_nadd x1 (NUMERAL 0)))).
Definition term218 (x0 : nat) (x1 : nadd) := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.le (Nat.mul x0 (Nat.add y1 y0)) y2) -> Peano.le (dist (@pair nat nat (Nat.mul y1 (dest_nadd x1 y0)) (Nat.mul y0 (dest_nadd x1 y1)))) y2.
Definition term217 (x0 : nat) (x1 : nat) (x2 : nadd) := forall y0 : nat, forall y1 : nat, (Peano.le (Nat.mul x0 (Nat.add y0 x1)) y1) -> Peano.le (dist (@pair nat nat (Nat.mul y0 (dest_nadd x2 x1)) (Nat.mul x1 (dest_nadd x2 y0)))) y1.
Definition term174 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Nat.add x0 y0) = (Nat.add x0 y1)) = (y0 = y1).
Definition term114 (x0 : nadd) (x1 : nat) := forall y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (Nat.mul y0 (dest_nadd x0 y1)) (Nat.mul y1 (dest_nadd x0 y0)))) (Nat.mul x1 (Nat.add y0 y1)).
Definition term100 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.le (Nat.add y0 y1) y2) -> Peano.le (dist (@pair nat nat y0 y1)) y2.
Definition term99 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add x0 y0) y1) -> Peano.le (dist (@pair nat nat x0 y0)) y1.
Definition term92 := forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> forall y2 : nat, (Peano.le y1 y2) -> Peano.le y0 y2.
Definition term83 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le x0 y0) -> (Peano.le y0 y1) -> Peano.le x0 y1.
Definition term81 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.le y0 y1) -> (Peano.le y1 y2) -> Peano.le y0 y2.
Definition term68 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.mul x0 (dist (@pair nat nat y0 y1))) = (dist (@pair nat nat (Nat.mul x0 y0) (Nat.mul x0 y1))).
Definition term51 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((y0 = (NUMERAL 0)) \/ (Peano.le y1 y2)) = (Peano.le (Nat.mul y0 y1) (Nat.mul y0 y2)).
Definition term50 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.le (Nat.mul y0 y1) (Nat.mul y0 y2)) = ((y0 = (NUMERAL 0)) \/ (Peano.le y1 y2)).
Definition term47 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((x0 = (NUMERAL 0)) \/ (Peano.le y0 y1)) = (Peano.le (Nat.mul x0 y0) (Nat.mul x0 y1)).
Definition term46 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le (Nat.mul x0 y0) (Nat.mul x0 y1)) = ((x0 = (NUMERAL 0)) \/ (Peano.le y0 y1)).
Definition term32 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.mul x0 (Nat.mul y0 y1)) = (Nat.mul (Nat.mul x0 y0) y1).
Definition term18 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.mul (Nat.add x0 y0) y1) = (Nat.add (Nat.mul x0 y1) (Nat.mul y0 y1)).
Definition term11 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.mul x0 (Nat.add y0 y1)) = (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y1)).
Definition term214 (x0 : nat) (x1 : nat) (x2 : nadd) (x3 : nat) := (Peano.le (dist (@pair nat nat (Nat.mul x3 (dest_nadd x2 x1)) (Nat.mul x1 (dest_nadd x2 x3)))) (Nat.mul x0 (Nat.add x3 x1))) -> forall y0 : nat, (Peano.le (Nat.mul x0 (Nat.add x3 x1)) y0) -> Peano.le (dist (@pair nat nat (Nat.mul x3 (dest_nadd x2 x1)) (Nat.mul x1 (dest_nadd x2 x3)))) y0.
Definition term225 (x0 : nat) (x1 : nat) (x2 : nadd) (x3 : nat) (x4 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.le (Nat.mul x0 (Nat.add y1 y0)) y2) -> Peano.le (dist (@pair nat nat (Nat.mul y1 (dest_nadd x2 y0)) (Nat.mul y0 (dest_nadd x2 y1)))) y2) -> Peano.le (dist (@pair nat nat (Nat.mul x3 (dest_nadd x2 x1)) (Nat.mul x1 (dest_nadd x2 x3)))) x4.
Definition term110 (x0 : nat) := (x0 = (NUMERAL 0)) \/ (~ (x0 = (NUMERAL 0))).
Definition term210 (x0 : nadd) (x1 : nat) (x2 : nat) := (fun y0 : nat => forall y1 : nat, Peano.le (dist (@pair nat nat (Nat.mul y0 (dest_nadd x0 y1)) (Nat.mul y1 (dest_nadd x0 y0)))) (Nat.mul x1 (Nat.add y0 y1))) x2.
Definition term240 (x0 : nat) (x1 : nat) (x2 : nadd) := Nat.mul x0 (Nat.add x1 (dest_nadd x2 (NUMERAL 0))).
Definition term78 (x0 : nat) := forall y0 : nat, Peano.le (dist (@pair nat nat x0 y0)) (Nat.add x0 y0).
Definition term212 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => Peano.le (dist (@pair nat nat (Nat.mul x2 (dest_nadd x0 y0)) (Nat.mul y0 (dest_nadd x0 x2)))) (Nat.mul x1 (Nat.add x2 y0))) x3.
Definition term191 (x0 : nat) (x1 : nadd) (x2 : nat) := dist (@pair nat nat (Nat.mul x2 (dest_nadd x1 (Nat.mul x0 x2))) (Nat.mul x2 (Nat.mul x0 (dest_nadd x1 x2)))).
Definition term21 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.mul (Nat.add x0 x1) y0) = (Nat.add (Nat.mul x0 y0) (Nat.mul x1 y0))) x2.
Definition term178 (x0 : nadd) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x1 (dest_nadd x0 (NUMERAL 0))) (Nat.add (Nat.mul x2 x1) x2).
Definition term80 (x0 : nat) (x1 : nat) := Peano.le (dist (@pair nat nat x0 x1)) (Nat.add x0 x1).
Definition term86 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.le x1 x0) -> (Peano.le x0 y0) -> Peano.le x1 y0) x2.
Definition term164 (x0 : nat) (x1 : nat) (x2 : nadd) := Nat.add (Nat.mul x0 x1) (dest_nadd x2 (NUMERAL 0)).
Definition term156 (x0 : nadd) (x1 : nat) (x2 : nat) := Nat.add (dest_nadd x0 (NUMERAL 0)) (Nat.add (Nat.mul x2 x1) x2).
Definition term103 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.le (Nat.add x0 x1) y0) -> Peano.le (dist (@pair nat nat x0 x1)) y0) x2.
Definition term125 (x0 : nadd) := Nat.add (dest_nadd x0 (NUMERAL 0)).
Definition term22 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.add x0 x1) x2.
Definition term23 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x0 x2) (Nat.mul x1 x2).
Definition term43 (x0 : nat) (x1 : nat) := forall y0 : nat, ((x1 = (NUMERAL 0)) \/ (Peano.le x0 y0)) = (Peano.le (Nat.mul x1 x0) (Nat.mul x1 y0)).
Definition term42 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le (Nat.mul x0 x1) (Nat.mul x0 y0)) = ((x0 = (NUMERAL 0)) \/ (Peano.le x1 y0)).
Definition term13 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.mul x1 (Nat.add x0 y0)) = (Nat.add (Nat.mul x1 x0) (Nat.mul x1 y0)).
Definition term179 (x0 : nat) (x1 : nadd) (x2 : nat) := Nat.add (Nat.mul x0 (dest_nadd x1 (NUMERAL 0))) x2.
Definition term70 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.mul x1 (dist (@pair nat nat x0 y0))) = (dist (@pair nat nat (Nat.mul x1 x0) (Nat.mul x1 y0))).
Definition term230 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (Nat.add x2 (Nat.mul x1 x2)).
Definition term58 (x0 : Prop) (x1 : Prop) := @eq Prop ((fun y0 : Prop => ((~ y0) -> x0) = (y0 \/ x0)) x1).
Definition term228 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nadd) := Peano.le (Nat.mul x2 (Nat.add x0 (Nat.mul x1 x0))) (Nat.mul x0 (Nat.add (Nat.mul (Nat.add x2 (dest_nadd x3 (NUMERAL 0))) x1) (Nat.add x2 (dest_nadd x3 (NUMERAL 0))))).
Definition term167 (x0 : nat) (x1 : nadd) (x2 : nat) := Nat.add (Nat.add (dest_nadd x1 (NUMERAL 0)) (Nat.mul x0 (dest_nadd x1 (NUMERAL 0)))) x2.
Definition term219 (x0 : nat) (x1 : nadd) (x2 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le (Nat.mul x0 (Nat.add y1 y0)) y2) -> Peano.le (dist (@pair nat nat (Nat.mul y1 (dest_nadd x1 y0)) (Nat.mul y0 (dest_nadd x1 y1)))) y2) x2.
Definition term162 (x0 : nat) (x1 : nat) (x2 : nadd) := Nat.add (Nat.mul x1 (dest_nadd x2 (NUMERAL 0))) (Nat.add x0 (Nat.add (Nat.mul x0 x1) (dest_nadd x2 (NUMERAL 0)))).
Definition term76 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((x1 = (NUMERAL 0)) \/ (Peano.le x0 y0)) = (Peano.le (Nat.mul x1 x0) (Nat.mul x1 y0))) x2.
Definition term140 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nadd) := Peano.le (Nat.add (dest_nadd x3 (Nat.mul x1 x0)) (Nat.mul x1 (dest_nadd x3 x0))) (Nat.add (Nat.mul (Nat.add x2 (dest_nadd x3 (NUMERAL 0))) x1) (Nat.add x2 (dest_nadd x3 (NUMERAL 0)))).
Definition term2 (a0 : Type') (x0 : a0) := exists y0 : a0, y0 = x0.
Definition term29 (x0 : nat) := forall y0 : nat, (Nat.mul x0 y0) = (Nat.mul y0 x0).
Definition term161 (x0 : nat) (x1 : nadd) := Nat.add (Nat.mul x0 (dest_nadd x1 (NUMERAL 0))).
Definition term38 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul x1 x0) (Nat.mul x1 x2).
Definition term138 (x0 : nat) (x1 : nadd) := Nat.add x0 (dest_nadd x1 (NUMERAL 0)).
Definition term133 (x0 : nadd) (x1 : nat) := Nat.mul (dest_nadd x0 (NUMERAL 0)) x1.
Definition term221 (x0 : nat) (x1 : nat) (x2 : nadd) (x3 : nat) (x4 : nat) := (fun y0 : nat => (Peano.le (Nat.mul x0 (Nat.add x3 x1)) y0) -> Peano.le (dist (@pair nat nat (Nat.mul x3 (dest_nadd x2 x1)) (Nat.mul x1 (dest_nadd x2 x3)))) y0) x4.
Definition term4 (a0 : Type') := fun y0 : a0 => exists y1 : a0, y1 = y0.
Definition term180 (x0 : nat) (x1 : nat) (x2 : nadd) (x3 : nat) := @eq Prop ((Nat.add (Nat.add (Nat.mul x0 x1) (Nat.mul x1 (dest_nadd x2 (NUMERAL 0)))) (Nat.add x0 (dest_nadd x2 (NUMERAL 0)))) = (Nat.add (Nat.add (dest_nadd x2 (NUMERAL 0)) (Nat.mul x1 (dest_nadd x2 (NUMERAL 0)))) x3)).
Definition term135 (x0 : nat) (x1 : nat) (x2 : nadd) := Nat.add (Nat.mul x0 x1) (Nat.mul x1 (dest_nadd x2 (NUMERAL 0))).
Definition term192 (x0 : nat) (x1 : nadd) (x2 : nat) := Peano.le (Nat.mul x2 (dist (@pair nat nat (dest_nadd x1 (Nat.mul x0 x2)) (Nat.mul x0 (dest_nadd x1 x2))))).
Definition term251 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := fun y0 : nat => (Nat.add (Nat.add (Nat.mul x1 (Nat.mul x2 x3)) (Nat.mul x2 (Nat.mul x3 (dest_nadd x0 (NUMERAL 0))))) (Nat.add (Nat.mul x1 x3) (Nat.mul x3 (dest_nadd x0 (NUMERAL 0))))) = (Nat.add (Nat.add (Nat.mul x1 x3) (Nat.mul x1 (Nat.mul x2 x3))) y0).
Definition term181 (x0 : nat) (x1 : nat) (x2 : nadd) := fun y0 : nat => (Nat.add (Nat.add (Nat.mul x0 x1) (Nat.mul x1 (dest_nadd x2 (NUMERAL 0)))) (Nat.add x0 (dest_nadd x2 (NUMERAL 0)))) = (Nat.add (Nat.add (dest_nadd x2 (NUMERAL 0)) (Nat.mul x1 (dest_nadd x2 (NUMERAL 0)))) y0).
Definition term129 (x0 : nat) (x1 : nadd) (x2 : nat) := Peano.le (Nat.add (dest_nadd x1 (Nat.mul x0 x2)) (Nat.mul x0 (dest_nadd x1 x2))).
Definition term53 (x0 : Prop) := (x0 = True) \/ (x0 = False).
Definition term65 := imp (~ False).
Definition term0 (a0 : Type') (x0 : a0) := fun y0 : a0 => y0 = x0.
Definition term30 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.mul x0 y0) = (Nat.mul y0 x0)) x1.
Definition term278 := forall y0 : nadd, exists y1 : nat, forall y2 : nat, forall y3 : nat, Peano.le (dist (@pair nat nat (dest_nadd y0 (Nat.mul y2 y3)) (Nat.mul y2 (dest_nadd y0 y3)))) (Nat.add (Nat.mul y1 y2) y1).
Definition term146 (x0 : nat) (x1 : nat) (x2 : nadd) := Nat.add (Nat.mul x0 (dest_nadd x2 (NUMERAL 0))) (Nat.add x1 (dest_nadd x2 (NUMERAL 0))).
Definition term144 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add x0 (Nat.add x1 x2).
Definition term238 (x0 : nat) (x1 : nat) (x2 : nadd) (x3 : nat) := Nat.add (Nat.mul x0 (Nat.mul (Nat.add x1 (dest_nadd x2 (NUMERAL 0))) x3)).
Definition term159 (x0 : nat) (x1 : nat) (x2 : nadd) := Nat.add (Nat.mul x1 x0) (Nat.add x1 (dest_nadd x2 (NUMERAL 0))).
Definition term255 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nadd) := Nat.add (Nat.mul x0 x2) (Nat.add (Nat.mul x1 (Nat.mul x2 (dest_nadd x3 (NUMERAL 0)))) (Nat.mul x2 (dest_nadd x3 (NUMERAL 0)))).
Definition term141 (x0 : nat) (x1 : nat) (x2 : nadd) := Peano.le (Nat.add (dest_nadd x2 (NUMERAL 0)) (Nat.mul x0 (dest_nadd x2 (NUMERAL 0)))) (Nat.add (Nat.add (Nat.mul x1 x0) (Nat.mul x0 (dest_nadd x2 (NUMERAL 0)))) (Nat.add x1 (dest_nadd x2 (NUMERAL 0)))).
Definition term132 (x0 : nat) (x1 : nadd) (x2 : nat) := Nat.add (Nat.mul x0 x2) (Nat.mul (dest_nadd x1 (NUMERAL 0)) x2).
Definition term261 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.add (Nat.mul x0 (Nat.mul x1 x2)) x3.
Definition term223 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (Nat.mul x0 (Nat.add x1 x2)) x3.
Definition term94 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) -> forall y2 : nat, (Peano.le y1 y2) -> Peano.le y0 y2) x0.
Definition term77 (x0 : nat) := (fun y0 : nat => forall y1 : nat, Peano.le (dist (@pair nat nat y0 y1)) (Nat.add y0 y1)) x0.
Definition term28 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) x0.
Definition term24 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) = (exists y2 : nat, y1 = (Nat.add y0 y2))) x0.
Definition term145 (x0 : nat) (x1 : nat) (x2 : nadd) := Nat.add (Nat.mul x1 x0) (Nat.add (Nat.mul x0 (dest_nadd x2 (NUMERAL 0))) (Nat.add x1 (dest_nadd x2 (NUMERAL 0)))).
Definition term258 (x0 : nat) (x1 : nat) (x2 : nadd) := Nat.add (Nat.mul x0 (Nat.mul x1 (dest_nadd x2 (NUMERAL 0)))) (Nat.mul x1 (dest_nadd x2 (NUMERAL 0))).
Definition term120 := forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0).
Definition term131 (x0 : nat) (x1 : nadd) (x2 : nat) := Nat.mul (Nat.add x0 (dest_nadd x1 (NUMERAL 0))) x2.
Definition term209 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nadd) := Peano.le (dist (@pair nat nat (Nat.mul x0 (dest_nadd x3 (Nat.mul x1 x0))) (Nat.mul (Nat.mul x1 x0) (dest_nadd x3 x0)))) (Nat.mul x0 (Nat.add (Nat.mul (Nat.add x2 (dest_nadd x3 (NUMERAL 0))) x1) (Nat.add x2 (dest_nadd x3 (NUMERAL 0))))).
Definition term203 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nadd) := Peano.le (dist (@pair nat nat (Nat.mul x0 (dest_nadd x3 (Nat.mul x1 x0))) (Nat.mul (Nat.mul x0 x1) (dest_nadd x3 x0)))) (Nat.mul x0 (Nat.add (Nat.mul (Nat.add x2 (dest_nadd x3 (NUMERAL 0))) x1) (Nat.add x2 (dest_nadd x3 (NUMERAL 0))))).
Definition term195 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nadd) := Peano.le (dist (@pair nat nat (Nat.mul x0 (dest_nadd x3 (Nat.mul x1 x0))) (Nat.mul x0 (Nat.mul x1 (dest_nadd x3 x0))))) (Nat.mul x0 (Nat.add (Nat.mul (Nat.add x2 (dest_nadd x3 (NUMERAL 0))) x1) (Nat.add x2 (dest_nadd x3 (NUMERAL 0))))).
Definition term216 (x0 : nat) (x1 : nat) (x2 : nadd) (x3 : nat) := forall y0 : nat, (Peano.le (Nat.mul x0 (Nat.add x3 x1)) y0) -> Peano.le (dist (@pair nat nat (Nat.mul x3 (dest_nadd x2 x1)) (Nat.mul x1 (dest_nadd x2 x3)))) y0.
Definition term98 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le (Nat.add x0 x1) y0) -> Peano.le (dist (@pair nat nat x0 x1)) y0.
Definition term118 (x0 : nat) (x1 : nat) (x2 : nadd) := Nat.add (Nat.mul (Nat.add x1 (dest_nadd x2 (NUMERAL 0))) x0) (Nat.add x1 (dest_nadd x2 (NUMERAL 0))).
Definition term36 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (Nat.mul x1 x2).
Definition term54 (x0 : Prop) := fun y0 : Prop => ((~ y0) -> x0) = (y0 \/ x0).
Definition term231 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nadd) := Nat.add (Nat.mul x1 (Nat.mul (Nat.add x2 (dest_nadd x3 (NUMERAL 0))) x0)) (Nat.mul x1 (Nat.add x2 (dest_nadd x3 (NUMERAL 0)))).
Definition term249 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.add (Nat.add (Nat.mul x0 x2) (Nat.mul x0 (Nat.mul x1 x2))) x3.
Definition term196 (x0 : nat) (x1 : nadd) (x2 : nat) := Nat.mul x2 (Nat.mul x0 (dest_nadd x1 x2)).
Definition term206 (x0 : nat) (x1 : nadd) (x2 : nat) := @pair nat nat (Nat.mul x2 (dest_nadd x1 (Nat.mul x0 x2))) (Nat.mul (Nat.mul x0 x2) (dest_nadd x1 x2)).
Definition term122 (x0 : nat) := Nat.mul x0 (NUMERAL 0).
Definition term87 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x1 x0) -> (Peano.le x0 x2) -> Peano.le x1 x2.
Definition term61 (x0 : Prop) := (fun y0 : Prop => ((~ y0) -> x0) = (y0 \/ x0)) False.
Definition term20 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.mul (Nat.add x0 x1) y0) = (Nat.add (Nat.mul x0 y0) (Nat.mul x1 y0)).
Definition term116 (x0 : nadd) (x1 : nat) (x2 : nat) := dest_nadd x0 (Nat.mul x1 x2).
Definition term147 (x0 : nat) (x1 : nat) (x2 : nadd) := Nat.add x0 (Nat.add (Nat.mul x1 (dest_nadd x2 (NUMERAL 0))) (dest_nadd x2 (NUMERAL 0))).
Definition term104 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le (Nat.add x0 x1) x2) -> Peano.le (dist (@pair nat nat x0 x1)) x2.
Definition term41 (x0 : nat) (x1 : nat) := fun y0 : nat => ((x1 = (NUMERAL 0)) \/ (Peano.le x0 y0)) = (Peano.le (Nat.mul x1 x0) (Nat.mul x1 y0)).
Definition term151 (x0 : nat) (x1 : nat) (x2 : nadd) := @eq nat (Nat.add (Nat.add (Nat.mul x1 x0) (Nat.mul x0 (dest_nadd x2 (NUMERAL 0)))) (Nat.add x1 (dest_nadd x2 (NUMERAL 0)))).
Definition term128 (x0 : nat) (x1 : nadd) := Nat.add (dest_nadd x1 (NUMERAL 0)) (Nat.mul x0 (dest_nadd x1 (NUMERAL 0))).
Definition term55 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => ((~ y0) -> x0) = (y0 \/ x0)) x1.
Definition term9 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.mul (Nat.mul x1 x0) x2) = (Nat.mul x1 (Nat.mul x0 x2))) /\ ((Nat.mul x1 (Nat.mul x0 x2)) = (Nat.mul x0 (Nat.mul x1 x2))).
Definition term66 (x0 : Prop) := @eq Prop ((~ False) -> x0).
Definition term64 (x0 : Prop) := @eq Prop ((~ True) -> x0).
Definition term112 (x0 : nadd) := (fun y0 : nadd => exists y1 : nat, forall y2 : nat, forall y3 : nat, Peano.le (dist (@pair nat nat (Nat.mul y2 (dest_nadd y0 y3)) (Nat.mul y3 (dest_nadd y0 y2)))) (Nat.mul y1 (Nat.add y2 y3))) x0.
Definition term177 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Nat.add x0 x1) = (Nat.add x0 y0)) = (x1 = y0)) x2.
Definition term154 (x0 : nadd) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x1 (dest_nadd x0 (NUMERAL 0))) (Nat.add (dest_nadd x0 (NUMERAL 0)) (Nat.add (Nat.mul x2 x1) x2)).
Definition term272 (x0 : nat) (x1 : nat) (x2 : nadd) := exists y0 : nat, (Nat.add (Nat.mul x0 (Nat.mul x1 (dest_nadd x2 (NUMERAL 0)))) (Nat.mul x1 (dest_nadd x2 (NUMERAL 0)))) = y0.
Definition term15 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (Nat.add x1 x2).
Definition term207 (x0 : nat) (x1 : nadd) (x2 : nat) := dist (@pair nat nat (Nat.mul x2 (dest_nadd x1 (Nat.mul x0 x2))) (Nat.mul (Nat.mul x0 x2) (dest_nadd x1 x2))).
Definition term201 (x0 : nat) (x1 : nadd) (x2 : nat) := dist (@pair nat nat (Nat.mul x2 (dest_nadd x1 (Nat.mul x0 x2))) (Nat.mul (Nat.mul x2 x0) (dest_nadd x1 x2))).
Definition term262 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.add x0 (Nat.mul x1 (Nat.mul x2 x3)).
Definition term136 (x0 : nat) (x1 : nadd) (x2 : nat) := Nat.add (Nat.mul (Nat.add x0 (dest_nadd x1 (NUMERAL 0))) x2).
Definition term106 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (dist (@pair nat nat x0 x1)) x2.
Definition term248 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.add (Nat.mul x0 (Nat.add x2 (Nat.mul x1 x2))) x3.
Definition term232 (x0 : nat) (x1 : nat) (x2 : nadd) (x3 : nat) := Nat.mul x0 (Nat.mul (Nat.add x1 (dest_nadd x2 (NUMERAL 0))) x3).
Definition term130 (x0 : nat) (x1 : nadd) := Peano.le (Nat.add (dest_nadd x1 (NUMERAL 0)) (Nat.mul x0 (dest_nadd x1 (NUMERAL 0)))).
Definition term57 (x0 : Prop) := (~ True) -> x0.
Definition term1 (a0 : Type') (x0 : a0) := fun y0 : a0 => x0 = y0.
Definition term63 := imp (~ True).
Definition term236 (x0 : nat) (x1 : nat) (x2 : nadd) := Nat.mul x0 (Nat.mul x1 (dest_nadd x2 (NUMERAL 0))).
Definition term269 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x0 x1) x2.
Definition term124 (x0 : nadd) (x1 : nat) (x2 : nat) := Nat.add (dest_nadd x0 (Nat.mul x1 x2)).
Definition term89 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le x0 y0) -> Peano.le x1 y0.
Definition term187 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nadd) := (x0 = (NUMERAL 0)) \/ (Peano.le (dist (@pair nat nat (dest_nadd x3 (Nat.mul x1 x0)) (Nat.mul x1 (dest_nadd x3 x0)))) (Nat.add (Nat.mul (Nat.add x2 (dest_nadd x3 (NUMERAL 0))) x1) (Nat.add x2 (dest_nadd x3 (NUMERAL 0))))).
Definition term56 (x0 : Prop) := (fun y0 : Prop => ((~ y0) -> x0) = (y0 \/ x0)) True.
Definition term149 (x0 : nat) (x1 : nat) (x2 : nadd) := Nat.add x0 (Nat.add (Nat.mul x0 x1) (Nat.add (Nat.mul x1 (dest_nadd x2 (NUMERAL 0))) (dest_nadd x2 (NUMERAL 0)))).
Definition term158 (x0 : nadd) (x1 : nat) := Nat.add (dest_nadd x0 (NUMERAL 0)) x1.
Definition term157 (x0 : nat) (x1 : nadd) (x2 : nat) := Nat.add (Nat.mul x2 x0) (Nat.add (dest_nadd x1 (NUMERAL 0)) x2).
Definition term26 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le x0 y0) = (exists y1 : nat, y0 = (Nat.add x0 y1))) x1.
Definition term250 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := fun y0 : nat => (Nat.mul x3 (Nat.add (Nat.mul (Nat.add x1 (dest_nadd x0 (NUMERAL 0))) x2) (Nat.add x1 (dest_nadd x0 (NUMERAL 0))))) = (Nat.add (Nat.mul x1 (Nat.add x3 (Nat.mul x2 x3))) y0).
Definition term52 (x0 : Prop) := (fun y0 : Prop => (y0 = True) \/ (y0 = False)) x0.
Definition term260 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.add (Nat.mul x0 x2) (Nat.add (Nat.mul x0 (Nat.mul x1 x2)) x3).
Definition term119 := (forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))).
Definition term215 (x0 : nat) (x1 : nadd) (x2 : nat) := dist (@pair nat nat (Nat.mul x2 (dest_nadd x1 x0)) (Nat.mul x0 (dest_nadd x1 x2))).
Definition term189 (x0 : nat) (x1 : nadd) (x2 : nat) := dist (@pair nat nat (dest_nadd x1 (Nat.mul x0 x2)) (Nat.mul x0 (dest_nadd x1 x2))).
Definition term233 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nadd) := Nat.mul x0 (Nat.add (Nat.mul x1 x2) (Nat.mul x2 (dest_nadd x3 (NUMERAL 0)))).
Definition term270 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := @eq Prop ((Nat.add (Nat.add (Nat.mul x1 (Nat.mul x2 x3)) (Nat.mul x2 (Nat.mul x3 (dest_nadd x0 (NUMERAL 0))))) (Nat.add (Nat.mul x1 x3) (Nat.mul x3 (dest_nadd x0 (NUMERAL 0))))) = (Nat.add (Nat.add (Nat.mul x1 x3) (Nat.mul x1 (Nat.mul x2 x3))) x4)).
Definition term109 (x0 : nat) := (fun y0 : Prop => y0 \/ (~ y0)) (x0 = (NUMERAL 0)).
Definition term95 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le x0 y0) -> forall y1 : nat, (Peano.le y0 y1) -> Peano.le x0 y1) x1.
Definition term45 (x0 : nat) := fun y0 : nat => forall y1 : nat, ((x0 = (NUMERAL 0)) \/ (Peano.le y0 y1)) = (Peano.le (Nat.mul x0 y0) (Nat.mul x0 y1)).
Definition term44 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Peano.le (Nat.mul x0 y0) (Nat.mul x0 y1)) = ((x0 = (NUMERAL 0)) \/ (Peano.le y0 y1)).
Definition term244 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nadd) := @eq nat (Nat.add (Nat.add (Nat.mul x1 (Nat.mul x0 x2)) (Nat.mul x0 (Nat.mul x2 (dest_nadd x3 (NUMERAL 0))))) (Nat.add (Nat.mul x1 x2) (Nat.mul x2 (dest_nadd x3 (NUMERAL 0))))).
Definition term277 (x0 : nadd) := fun y0 : nat => forall y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (Nat.mul y1 (dest_nadd x0 y2)) (Nat.mul y2 (dest_nadd x0 y1)))) (Nat.mul y0 (Nat.add y1 y2)).
Definition term276 (x0 : nadd) := fun y0 : nat => forall y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 (Nat.mul y1 y2)) (Nat.mul y1 (dest_nadd x0 y2)))) (Nat.add (Nat.mul y0 y1) y0).
Definition term49 := fun y0 : nat => forall y1 : nat, forall y2 : nat, ((y0 = (NUMERAL 0)) \/ (Peano.le y1 y2)) = (Peano.le (Nat.mul y0 y1) (Nat.mul y0 y2)).
Definition term48 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le (Nat.mul y0 y1) (Nat.mul y0 y2)) = ((y0 = (NUMERAL 0)) \/ (Peano.le y1 y2)).
Definition term197 (x0 : nat) (x1 : nadd) (x2 : nat) := Nat.mul (Nat.mul x2 x0) (dest_nadd x1 x2).
Definition term213 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (dist (@pair nat nat (Nat.mul x2 (dest_nadd x0 x3)) (Nat.mul x3 (dest_nadd x0 x2)))) (Nat.mul x1 (Nat.add x2 x3)).
Definition term182 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.add (Nat.mul x1 x0) x1) = y0.
Definition term241 (x0 : nat) (x1 : nat) (x2 : nadd) := Nat.add (Nat.mul x1 x0) (Nat.mul x1 (dest_nadd x2 (NUMERAL 0))).
