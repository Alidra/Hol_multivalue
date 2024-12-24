Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term99 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.mul x1 (Nat.add x0 y0)) = (Nat.add (Nat.mul x1 x0) (Nat.mul x1 y0))) x2.
Definition term171 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, (nadd_le y0 y1) = (exists y2 : nat, forall y3 : nat, Peano.le (dest_nadd y0 y3) (Nat.add (dest_nadd y1 y3) y2))) x0.
Definition term160 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, (nadd_eq y0 y1) = (exists y2 : nat, forall y3 : nat, Peano.le (dist (@pair nat nat (dest_nadd y0 y3) (dest_nadd y1 y3))) y2)) x0.
Definition term349 (x0 : nadd) (x1 : nat) (x2 : nat) := dist (@pair nat nat (dest_nadd x0 x1) (Nat.add (dest_nadd x0 x1) x2)).
Definition term136 (x0 : nat) (x1 : nat) (x2 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, forall y4 : nat, (Peano.le (Nat.add (dist (@pair nat nat (Nat.add y2 y0) (Nat.add y3 y1))) (dist (@pair nat nat y0 y1))) y4) -> Peano.le (dist (@pair nat nat y2 y3)) y4) -> Peano.le (dist (@pair nat nat x0 x1)) x2.
Definition term321 (x0 : nat) (x1 : nat) := @pair nat nat (Nat.mul x0 x1).
Definition term291 (x0 : nat) (x1 : nadd) (x2 : nat) (x3 : nat) := Nat.mul x0 (Nat.add (dest_nadd x1 x2) x3).
Definition term327 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul x0 (dist (@pair nat nat x1 x2))) (Nat.mul x0 (Nat.add x1 x2)).
Definition term69 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x2) -> Peano.le x1 x2.
Definition term140 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nat => exists y1 : nat, Peano.le (Nat.add (dist (@pair nat nat (Nat.add x0 y0) (Nat.add x1 y1))) (dist (@pair nat nat y0 y1))) x2.
Definition term213 (x0 : nat) (x1 : nadd) (x2 : nadd) := (forall y0 : nat, Peano.le (dest_nadd x2 y0) (Nat.add (dest_nadd x1 y0) x0)) -> exists y0 : nadd, nadd_eq x1 (nadd_add x2 y0).
Definition term246 (x0 : nadd) (x1 : nadd) (x2 : nat -> nat) := exists y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 y1) (Nat.add (dest_nadd x1 y1) (dest_nadd (mk_nadd x2) y1)))) y0.
Definition term218 (x0 : nadd) (x1 : nadd) (x2 : nat -> nat) := exists y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 y1) (dest_nadd (nadd_add x1 (mk_nadd x2)) y1))) y0.
Definition term174 (x0 : nadd) (x1 : nadd) := exists y0 : nat, forall y1 : nat, Peano.le (dest_nadd x0 y1) (Nat.add (dest_nadd x1 y1) y0).
Definition term163 (x0 : nadd) (x1 : nadd) := exists y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 y1) (dest_nadd x1 y1))) y0.
Definition term154 (x0 : nat -> nat) := exists y0 : nat, forall y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (Nat.mul y1 (x0 y2)) (Nat.mul y2 (x0 y1)))) (Nat.mul y0 (Nat.add y1 y2)).
Definition term150 (x0 : nadd) := exists y0 : nat, forall y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (Nat.mul y1 (dest_nadd x0 y2)) (Nat.mul y2 (dest_nadd x0 y1)))) (Nat.mul y0 (Nat.add y1 y2)).
Definition term103 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.add (Nat.mul x0 x1) (Nat.mul x0 y0)) = (Nat.mul x0 (Nat.add x1 y0)).
Definition term286 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y2)) = (Nat.mul y0 (Nat.add y1 y2))) x0.
Definition term146 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (exists y3 : nat, exists y4 : nat, Peano.le (Nat.add (dist (@pair nat nat (Nat.add y0 y3) (Nat.add y1 y4))) (dist (@pair nat nat y3 y4))) y2) -> Peano.le (dist (@pair nat nat y0 y1)) y2) x0.
Definition term128 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, forall y4 : nat, (Peano.le (Nat.add (dist (@pair nat nat (Nat.add y2 y0) (Nat.add y3 y1))) (dist (@pair nat nat y0 y1))) y4) -> Peano.le (dist (@pair nat nat y2 y3)) y4) x0.
Definition term112 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, Peano.le (dist (@pair nat nat y0 y2)) (Nat.add (dist (@pair nat nat (Nat.add y0 y1) (Nat.add y2 y3))) (dist (@pair nat nat y1 y3)))) x0.
Definition term95 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.mul y0 (Nat.add y1 y2)) = (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y2))) x0.
Definition term85 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, forall y4 : nat, (Peano.le (Nat.add (dist (@pair nat nat y0 y2)) (dist (@pair nat nat y1 y3))) y4) -> Peano.le (dist (@pair nat nat (Nat.add y0 y1) (Nat.add y2 y3))) y4) x0.
Definition term63 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le y0 y1) -> (Peano.le y1 y2) -> Peano.le y0 y2) x0.
Definition term54 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, Peano.le (dist (@pair nat nat (Nat.add y0 y1) (Nat.add y2 y3))) (Nat.add (dist (@pair nat nat y0 y2)) (dist (@pair nat nat y1 y3)))) x0.
Definition term47 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.mul (Nat.add y0 y1) y2) = (Nat.add (Nat.mul y0 y2) (Nat.mul y1 y2))) x0.
Definition term35 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.add y0 y1) (Nat.add y2 y3)) x0.
Definition term25 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (dist (@pair nat nat (Nat.mul y0 y1) (Nat.mul y0 y2))) = (Nat.mul y0 (dist (@pair nat nat y1 y2)))) x0.
Definition term14 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le (Nat.mul y0 y1) (Nat.mul y0 y2)) = ((y0 = (NUMERAL 0)) \/ (Peano.le y1 y2))) x0.
Definition term270 (x0 : nat -> nat) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : nat) := and (Peano.le (dist (@pair nat nat (Nat.add (Nat.mul x4 (x0 x5)) (Nat.mul x4 (dest_nadd x1 x5))) (Nat.add (Nat.mul x5 (x0 x4)) (Nat.mul x5 (dest_nadd x1 x4))))) (Nat.mul (Nat.add x2 x3) (Nat.add x4 x5))).
Definition term41 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => ((Peano.le x0 x2) /\ (Peano.le x1 y0)) -> Peano.le (Nat.add x0 x1) (Nat.add x2 y0)) x3.
Definition term250 (x0 : nadd) (x1 : nadd) (x2 : nat -> nat) (x3 : nat) (x4 : nat) := Peano.le (dist (@pair nat nat (dest_nadd x0 x3) (Nat.add (dest_nadd x1 x3) (x2 x3)))) x4.
Definition term239 (x0 : nadd) (x1 : nadd) (x2 : nat -> nat) (x3 : nat) (x4 : nat) := Peano.le (dist (@pair nat nat (dest_nadd x0 x3) (Nat.add (dest_nadd x1 x3) (dest_nadd (mk_nadd x2) x3)))) x4.
Definition term189 (x0 : nadd) (x1 : nat) (x2 : nadd) := forall y0 : nat, exists y1 : nat, (fun y2 : nat => fun y3 : nat => (Nat.add (dest_nadd x0 y2) x1) = (Nat.add (dest_nadd x2 y2) y3)) y0 y1.
Definition term187 (x0 : type1605) := forall y0 : nat, exists y1 : nat, x0 y0 y1.
Definition term186 (x0 : nadd) (x1 : nat) (x2 : nadd) := forall y0 : nat, exists y1 : nat, (Nat.add (dest_nadd x0 y0) x1) = (Nat.add (dest_nadd x2 y0) y1).
Definition term141 (x0 : nat) (x1 : nat) (x2 : nat) := (exists y0 : nat, exists y1 : nat, Peano.le (Nat.add (dist (@pair nat nat (Nat.add x0 y0) (Nat.add x1 y1))) (dist (@pair nat nat y0 y1))) x2) -> Peano.le (dist (@pair nat nat x0 x1)) x2.
Definition term334 (x0 : nat -> nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : nat) := fun y0 : nat => exists y1 : nat, Peano.le (Nat.add (dist (@pair nat nat (Nat.add (Nat.mul x4 (x0 x5)) y0) (Nat.add (Nat.mul x5 (x0 x4)) y1))) (dist (@pair nat nat y0 y1))) (Nat.mul (Nat.add x1 (Nat.add x2 x3)) (Nat.add x4 x5)).
Definition term145 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, forall y4 : nat, (Peano.le (Nat.add (dist (@pair nat nat (Nat.add y2 y0) (Nat.add y3 y1))) (dist (@pair nat nat y0 y1))) y4) -> Peano.le (dist (@pair nat nat y2 y3)) y4) -> forall y0 : nat, forall y1 : nat, forall y2 : nat, (exists y3 : nat, exists y4 : nat, Peano.le (Nat.add (dist (@pair nat nat (Nat.add y0 y3) (Nat.add y1 y4))) (dist (@pair nat nat y3 y4))) y2) -> Peano.le (dist (@pair nat nat y0 y1)) y2.
Definition term94 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, forall y4 : nat, (Peano.le (Nat.add (dist (@pair nat nat y0 y2)) (dist (@pair nat nat y1 y3))) y4) -> Peano.le (dist (@pair nat nat (Nat.add y0 y1) (Nat.add y2 y3))) y4) -> forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, forall y4 : nat, (Peano.le (Nat.add (dist (@pair nat nat y0 y2)) (dist (@pair nat nat y1 y3))) y4) -> Peano.le (dist (@pair nat nat (Nat.add y0 y1) (Nat.add y2 y3))) y4.
Definition term74 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.le y0 y1) -> (Peano.le y1 y2) -> Peano.le y0 y2) -> forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> forall y2 : nat, (Peano.le y1 y2) -> Peano.le y0 y2.
Definition term46 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.add y0 y1) (Nat.add y2 y3)) -> forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.add y0 y1) (Nat.add y2 y3).
Definition term133 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := (Peano.le (Nat.add (dist (@pair nat nat (Nat.add x2 x0) (Nat.add x3 x1))) (dist (@pair nat nat x0 x1))) x4) -> Peano.le (dist (@pair nat nat x2 x3)) x4.
Definition term90 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := (Peano.le (Nat.add (dist (@pair nat nat x0 x2)) (dist (@pair nat nat x1 x3))) x4) -> Peano.le (dist (@pair nat nat (Nat.add x0 x1) (Nat.add x2 x3))) x4.
Definition term328 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = (NUMERAL 0)) \/ (Peano.le (dist (@pair nat nat x1 x2)) (Nat.add x1 x2)).
Definition term330 (x0 : nat) := (x0 = (NUMERAL 0)) \/ True.
Definition term20 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = (NUMERAL 0)) \/ (Peano.le x1 x2).
Definition term274 (x0 : nat -> nat) (x1 : nat) (x2 : nadd) (x3 : nat) := Nat.add (Nat.mul x1 (x0 x3)) (Nat.mul x1 (dest_nadd x2 x3)).
Definition term1 (x0 : nat) (x1 : nat) (x2 : nat) := dist (@pair nat nat (Nat.mul x1 x0) (Nat.mul x1 x2)).
Definition term184 (x0 : nadd) (x1 : nadd) (x2 : nat) := fun y0 : nat => Peano.le (dest_nadd x0 y0) (Nat.add (dest_nadd x1 y0) x2).
Definition term354 := forall y0 : nadd, forall y1 : nadd, (nadd_le y0 y1) -> exists y2 : nadd, nadd_eq y1 (nadd_add y0 y2).
Definition term104 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.add (Nat.mul x0 x1) (Nat.mul x0 y0)) = (Nat.mul x0 (Nat.add x1 y0)).
Definition term220 (x0 : nadd) (x1 : nat -> nat) := dest_nadd (nadd_add x0 (mk_nadd x1)).
Definition term175 (x0 : nadd) (x1 : nadd) := imp (nadd_le x0 x1).
Definition term259 (x0 : nat -> nat) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : nat) (x6 : nat) := Peano.le (Nat.add (dist (@pair nat nat (Nat.add (Nat.mul x5 (x0 x6)) (Nat.mul x5 (dest_nadd x1 x6))) (Nat.add (Nat.mul x6 (x0 x5)) (Nat.mul x6 (dest_nadd x1 x5))))) (dist (@pair nat nat (Nat.mul x5 (dest_nadd x1 x6)) (Nat.mul x6 (dest_nadd x1 x5))))) (Nat.add (Nat.mul x2 (Nat.add x5 x6)) (Nat.mul (Nat.add x3 x4) (Nat.add x5 x6))).
Definition term247 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) := fun y0 : nat -> nat => Peano.le (dist (@pair nat nat (dest_nadd x0 x2) (Nat.add (dest_nadd x1 x2) (y0 x2)))) x3.
Definition term197 (x0 : nadd) (x1 : nat) (x2 : nadd) (x3 : nat) := exists y0 : nat, (fun y1 : nat => fun y2 : nat => (Nat.add (dest_nadd x0 y1) x1) = (Nat.add (dest_nadd x2 y1) y2)) x3 y0.
Definition term180 (x0 : nadd) (x1 : nadd) (x2 : nat) := forall y0 : nat, Peano.le (dest_nadd x0 y0) (Nat.add (dest_nadd x1 y0) x2).
Definition term183 (x0 : nadd) (x1 : nat) (x2 : nat) := Nat.add (dest_nadd x0 x1) x2.
Definition term230 (x0 : nadd) (x1 : nat -> nat) (x2 : nat) := @eq nat ((fun y0 : nat => Nat.add (dest_nadd x0 y0) (dest_nadd (mk_nadd x1) y0)) x2).
Definition term206 (x0 : nadd) (x1 : nat) (x2 : nadd) (x3 : nat -> nat) := forall y0 : nat, (fun y1 : nat => fun y2 : nat => (Nat.add (dest_nadd x0 y1) x1) = (Nat.add (dest_nadd x2 y1) y2)) y0 (x3 y0).
Definition term300 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := dist (@pair nat nat (Nat.add (Nat.mul x1 (dest_nadd x0 x2)) (Nat.mul x1 x3)) (Nat.add (Nat.mul x2 (dest_nadd x0 x1)) (Nat.mul x2 x3))).
Definition term148 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (exists y1 : nat, exists y2 : nat, Peano.le (Nat.add (dist (@pair nat nat (Nat.add x0 y1) (Nat.add x1 y2))) (dist (@pair nat nat y1 y2))) y0) -> Peano.le (dist (@pair nat nat x0 x1)) y0) x2.
Definition term168 (x0 : nat) := forall y0 : nat, (Peano.le x0 y0) = (exists y1 : nat, y0 = (Nat.add x0 y1)).
Definition term122 (x0 : nat) (x1 : nat) := dist (@pair nat nat x0 x1).
Definition term44 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (Nat.add x0 x1) (Nat.add x2 x3).
Definition term61 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (dist (@pair nat nat (Nat.add x0 x2) (Nat.add x1 x3))) (Nat.add (dist (@pair nat nat x0 x1)) (dist (@pair nat nat x2 x3))).
Definition term221 (x0 : nadd) (x1 : nat -> nat) := fun y0 : nat => Nat.add (dest_nadd x0 y0) (dest_nadd (mk_nadd x1) y0).
Definition term346 (x0 : nadd) (x1 : nadd) (x2 : nat -> nat) (x3 : nat) := @pair nat nat (dest_nadd x0 x3) (Nat.add (dest_nadd x1 x3) (x2 x3)).
Definition term305 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (Nat.add (dist (@pair nat nat (Nat.mul x1 (dest_nadd x0 x2)) (Nat.mul x2 (dest_nadd x0 x1)))) (dist (@pair nat nat (Nat.mul x1 x3) (Nat.mul x2 x3)))).
Definition term257 (x0 : nat -> nat) (x1 : nat) (x2 : nadd) (x3 : nat) := Peano.le (Nat.add (dist (@pair nat nat (Nat.add (Nat.mul x3 (x0 x1)) (Nat.mul x3 (dest_nadd x2 x1))) (Nat.add (Nat.mul x1 (x0 x3)) (Nat.mul x1 (dest_nadd x2 x3))))) (dist (@pair nat nat (Nat.mul x3 (dest_nadd x2 x1)) (Nat.mul x1 (dest_nadd x2 x3))))).
Definition term350 (x0 : nadd) (x1 : nadd) (x2 : nat -> nat) (x3 : nat) := Peano.le (dist (@pair nat nat (dest_nadd x0 x3) (Nat.add (dest_nadd x1 x3) (x2 x3)))).
Definition term314 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := and (Peano.le (dist (@pair nat nat (Nat.mul x2 (dest_nadd x0 x3)) (Nat.mul x3 (dest_nadd x0 x2)))) (Nat.mul x1 (Nat.add x2 x3))).
Definition term313 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := and (Peano.le (dist (@pair nat nat (Nat.mul x3 (dest_nadd x0 x2)) (Nat.mul x2 (dest_nadd x0 x3)))) (Nat.mul x1 (Nat.add x2 x3))).
Definition term288 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.add (Nat.mul x0 x1) (Nat.mul x0 y0)) = (Nat.mul x0 (Nat.add x1 y0))) x2.
Definition term331 (x0 : nat -> nat) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : nat) (x6 : nat) := exists y0 : nat, Peano.le (Nat.add (dist (@pair nat nat (Nat.add (Nat.mul x5 (x0 x6)) (Nat.mul x5 (dest_nadd x1 x6))) (Nat.add (Nat.mul x6 (x0 x5)) y0))) (dist (@pair nat nat (Nat.mul x5 (dest_nadd x1 x6)) y0))) (Nat.mul (Nat.add x2 (Nat.add x3 x4)) (Nat.add x5 x6)).
Definition term298 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := @pair nat nat (Nat.add (Nat.mul x2 (dest_nadd x0 x1)) (Nat.mul x2 x3)).
Definition term72 (x0 : nat) := forall y0 : nat, (Peano.le x0 y0) -> forall y1 : nat, (Peano.le y0 y1) -> Peano.le x0 y1.
Definition term137 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := exists y0 : nat, Peano.le (Nat.add (dist (@pair nat nat (Nat.add x0 x2) (Nat.add x1 y0))) (dist (@pair nat nat x2 y0))) x3.
Definition term23 (x0 : nat) (x1 : nat) := (fun y0 : nat => Peano.le (dist (@pair nat nat x0 y0)) (Nat.add x0 y0)) x1.
Definition term158 (x0 : nadd) (x1 : nadd) := dest_nadd (nadd_add x0 x1).
Definition term165 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := forall y0 : a0, exists y1 : a1, x0 y0 y1.
Definition term342 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (dist (@pair nat nat y0 (Nat.add y0 y1))) = y1) x0.
Definition term301 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (dist (@pair nat nat (Nat.add (Nat.mul x1 (dest_nadd x0 x2)) (Nat.mul x1 x3)) (Nat.add (Nat.mul x2 (dest_nadd x0 x1)) (Nat.mul x2 x3)))).
Definition term0 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (dist (@pair nat nat x1 x2)).
Definition term185 (x0 : nadd) (x1 : nat) (x2 : nadd) := fun y0 : nat => exists y1 : nat, (Nat.add (dest_nadd x0 y0) x1) = (Nat.add (dest_nadd x2 y0) y1).
Definition term210 (x0 : nadd) (x1 : nat) (x2 : nadd) := exists y0 : nat -> nat, forall y1 : nat, (Nat.add (dest_nadd x0 y1) x1) = (Nat.add (dest_nadd x2 y1) (y0 y1)).
Definition term190 (x0 : nadd) (x1 : nat) (x2 : nadd) := exists y0 : nat -> nat, forall y1 : nat, (fun y2 : nat => fun y3 : nat => (Nat.add (dest_nadd x0 y2) x1) = (Nat.add (dest_nadd x2 y2) y3)) y1 (y0 y1).
Definition term188 (x0 : type1605) := exists y0 : nat -> nat, forall y1 : nat, x0 y1 (y0 y1).
Definition term276 (x0 : nat) (x1 : nadd) (x2 : nat) := Nat.mul x0 (dest_nadd x1 x2).
Definition term248 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat -> nat) := (fun y0 : nat -> nat => Peano.le (dist (@pair nat nat (dest_nadd x0 x2) (Nat.add (dest_nadd x1 x2) (y0 x2)))) x3) (dest_nadd (mk_nadd x4)).
Definition term309 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := ((Peano.le (dist (@pair nat nat (Nat.mul x4 (dest_nadd x0 x3)) (Nat.mul x3 (dest_nadd x0 x4)))) (Nat.mul x1 (Nat.add x3 x4))) /\ (Peano.le (dist (@pair nat nat (Nat.mul x4 x2) (Nat.mul x3 x2))) (Nat.mul x2 (Nat.add x3 x4)))) -> Peano.le (Nat.add (dist (@pair nat nat (Nat.mul x4 (dest_nadd x0 x3)) (Nat.mul x3 (dest_nadd x0 x4)))) (dist (@pair nat nat (Nat.mul x4 x2) (Nat.mul x3 x2)))) (Nat.add (Nat.mul x1 (Nat.add x3 x4)) (Nat.mul x2 (Nat.add x3 x4))).
Definition term263 (x0 : nat -> nat) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : nat) (x6 : nat) := ((Peano.le (dist (@pair nat nat (Nat.add (Nat.mul x5 (x0 x6)) (Nat.mul x5 (dest_nadd x1 x6))) (Nat.add (Nat.mul x6 (x0 x5)) (Nat.mul x6 (dest_nadd x1 x5))))) (Nat.mul (Nat.add x2 x3) (Nat.add x5 x6))) /\ (Peano.le (dist (@pair nat nat (Nat.mul x5 (dest_nadd x1 x6)) (Nat.mul x6 (dest_nadd x1 x5)))) (Nat.mul x4 (Nat.add x5 x6)))) -> Peano.le (Nat.add (dist (@pair nat nat (Nat.add (Nat.mul x5 (x0 x6)) (Nat.mul x5 (dest_nadd x1 x6))) (Nat.add (Nat.mul x6 (x0 x5)) (Nat.mul x6 (dest_nadd x1 x5))))) (dist (@pair nat nat (Nat.mul x5 (dest_nadd x1 x6)) (Nat.mul x6 (dest_nadd x1 x5))))) (Nat.add (Nat.mul (Nat.add x2 x3) (Nat.add x5 x6)) (Nat.mul x4 (Nat.add x5 x6))).
Definition term219 (x0 : nadd) (x1 : nat -> nat) := nadd_add x0 (mk_nadd x1).
Definition term347 (x0 : nadd) (x1 : nat) (x2 : nat) := @pair nat nat (dest_nadd x0 x1) (Nat.add (dest_nadd x0 x1) x2).
Definition term191 (x0 : nadd) (x1 : nat) (x2 : nadd) := fun y0 : nat => fun y1 : nat => (Nat.add (dest_nadd x0 y0) x1) = (Nat.add (dest_nadd x2 y0) y1).
Definition term134 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := Peano.le (Nat.add (dist (@pair nat nat (Nat.add x0 x2) (Nat.add x1 x3))) (dist (@pair nat nat x2 x3))) x4.
Definition term91 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := Peano.le (Nat.add (dist (@pair nat nat x0 x1)) (dist (@pair nat nat x2 x3))) x4.
Definition term152 (x0 : nat -> nat) := dest_nadd (mk_nadd x0).
Definition term335 (x0 : nat -> nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : nat) := Peano.le (dist (@pair nat nat (Nat.mul x4 (x0 x5)) (Nat.mul x5 (x0 x4)))) (Nat.mul (Nat.add x1 (Nat.add x2 x3)) (Nat.add x4 x5)).
Definition term229 (x0 : nadd) (x1 : nat -> nat) (x2 : nat) := @eq nat ((fun y0 : nat => (fun y1 : nat => Nat.add (dest_nadd x0 y1) (dest_nadd (mk_nadd x1) y1)) y0) x2).
Definition term157 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => (dest_nadd (nadd_add x0 y0)) = (fun y1 : nat => Nat.add (dest_nadd x0 y1) (dest_nadd y0 y1))) x1.
Definition term287 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y1)) = (Nat.mul x0 (Nat.add y0 y1))) x1.
Definition term147 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (exists y2 : nat, exists y3 : nat, Peano.le (Nat.add (dist (@pair nat nat (Nat.add x0 y2) (Nat.add y0 y3))) (dist (@pair nat nat y2 y3))) y1) -> Peano.le (dist (@pair nat nat x0 y0)) y1) x1.
Definition term97 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul x0 (Nat.add y0 y1)) = (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y1))) x1.
Definition term65 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le x0 y0) -> (Peano.le y0 y1) -> Peano.le x0 y1) x1.
Definition term49 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul (Nat.add x0 y0) y1) = (Nat.add (Nat.mul x0 y1) (Nat.mul y0 y1))) x1.
Definition term26 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (dist (@pair nat nat (Nat.mul x0 y0) (Nat.mul x0 y1))) = (Nat.mul x0 (dist (@pair nat nat y0 y1)))) x1.
Definition term16 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (Nat.mul x0 y0) (Nat.mul x0 y1)) = ((x0 = (NUMERAL 0)) \/ (Peano.le y0 y1))) x1.
Definition term177 (x0 : nadd) (x1 : nadd) := exists y0 : nadd, nadd_eq x0 (nadd_add x1 y0).
Definition term324 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (dist (@pair nat nat (Nat.mul x1 x0) (Nat.mul x1 x2))).
Definition term315 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (dist (@pair nat nat (Nat.mul x0 x2) (Nat.mul x1 x2))).
Definition term279 (x0 : nat -> nat) (x1 : nat) (x2 : nadd) (x3 : nat) := @pair nat nat (Nat.add (Nat.mul x3 (x0 x1)) (Nat.mul x3 (dest_nadd x2 x1))) (Nat.add (Nat.mul x1 (x0 x3)) (Nat.mul x1 (dest_nadd x2 x3))).
Definition term352 (x0 : nadd) (x1 : nadd) := fun y0 : nat => forall y1 : nat, Peano.le (dest_nadd x0 y1) (Nat.add (dest_nadd x1 y1) y0).
Definition term351 (x0 : nadd) (x1 : nadd) := fun y0 : nadd => nadd_eq x0 (nadd_add x1 y0).
Definition term256 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := Nat.add (Nat.mul x0 (Nat.add x3 x4)) (Nat.mul (Nat.add x1 x2) (Nat.add x3 x4)).
Definition term283 (x0 : nadd) (x1 : nat) (x2 : nat -> nat) (x3 : nat) := Peano.le (dist (@pair nat nat (Nat.add (Nat.mul x3 (dest_nadd x0 x1)) (Nat.mul x3 (x2 x1))) (Nat.add (Nat.mul x1 (dest_nadd x0 x3)) (Nat.mul x1 (x2 x3))))).
Definition term282 (x0 : nat -> nat) (x1 : nat) (x2 : nadd) (x3 : nat) := Peano.le (dist (@pair nat nat (Nat.add (Nat.mul x3 (x0 x1)) (Nat.mul x3 (dest_nadd x2 x1))) (Nat.add (Nat.mul x1 (x0 x3)) (Nat.mul x1 (dest_nadd x2 x3))))).
Definition term271 (x0 : nat -> nat) (x1 : nat) (x2 : nat) (x3 : nadd) (x4 : nat) (x5 : nat) (x6 : nat) := (Peano.le (dist (@pair nat nat (Nat.add (Nat.mul x5 (x0 x6)) (Nat.mul x5 (dest_nadd x3 x6))) (Nat.add (Nat.mul x6 (x0 x5)) (Nat.mul x6 (dest_nadd x3 x5))))) (Nat.mul (Nat.add x1 x2) (Nat.add x5 x6))) /\ (Peano.le (dist (@pair nat nat (Nat.mul x5 (dest_nadd x3 x6)) (Nat.mul x6 (dest_nadd x3 x5)))) (Nat.mul x4 (Nat.add x5 x6))).
Definition term252 (x0 : nadd) (x1 : nadd) (x2 : nat -> nat) (x3 : nat) (x4 : nat) := @eq Prop (Peano.le (dist (@pair nat nat (dest_nadd x0 x3) (Nat.add (dest_nadd x1 x3) (dest_nadd (mk_nadd x2) x3)))) x4).
Definition term289 (x0 : nadd) (x1 : nat -> nat) (x2 : nadd) (x3 : nat) (x4 : nat) := (fun y0 : nat => (Nat.add (dest_nadd x0 y0) (x1 y0)) = (Nat.add (dest_nadd x2 y0) x3)) x4.
Definition term222 (x0 : nadd) (x1 : nat -> nat) (x2 : nat) := dest_nadd (nadd_add x0 (mk_nadd x1)) x2.
Definition term293 (x0 : nat) (x1 : nadd) (x2 : nat) (x3 : nat) := @pair nat nat (Nat.mul x2 (Nat.add (dest_nadd x1 x0) x3)) (Nat.mul x0 (Nat.add (dest_nadd x1 x2) x3)).
Definition term237 (x0 : nadd) (x1 : nadd) (x2 : nat -> nat) (x3 : nat) := Peano.le (dist (@pair nat nat (dest_nadd x0 x3) (Nat.add (dest_nadd x1 x3) (dest_nadd (mk_nadd x2) x3)))).
Definition term341 (x0 : nat) := (fun y0 : nat => Peano.le y0 y0) x0.
Definition term251 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat -> nat) := @eq Prop ((fun y0 : nat -> nat => Peano.le (dist (@pair nat nat (dest_nadd x0 x2) (Nat.add (dest_nadd x1 x2) (y0 x2)))) x3) (dest_nadd (mk_nadd x4))).
Definition term234 (x0 : nadd) (x1 : nadd) (x2 : nat -> nat) (x3 : nat) := dist (@pair nat nat (dest_nadd x0 x3) (dest_nadd (nadd_add x1 (mk_nadd x2)) x3)).
Definition term66 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le x1 x0) -> (Peano.le x0 y0) -> Peano.le x1 y0.
Definition term306 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := Peano.le (Nat.add (dist (@pair nat nat (Nat.mul x4 (dest_nadd x0 x3)) (Nat.mul x3 (dest_nadd x0 x4)))) (dist (@pair nat nat (Nat.mul x4 x1) (Nat.mul x3 x1)))) (Nat.mul (Nat.add x1 x2) (Nat.add x3 x4)).
Definition term173 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => (nadd_le x0 y0) = (exists y1 : nat, forall y2 : nat, Peano.le (dest_nadd x0 y2) (Nat.add (dest_nadd y0 y2) y1))) x1.
Definition term162 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => (nadd_eq x0 y0) = (exists y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 y2) (dest_nadd y0 y2))) y1)) x1.
Definition term254 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := Nat.mul x0 (x1 x2).
Definition term294 (x0 : nat) (x1 : nadd) (x2 : nat) (x3 : nat) := dist (@pair nat nat (Nat.mul x2 (Nat.add (dest_nadd x1 x0) x3)) (Nat.mul x0 (Nat.add (dest_nadd x1 x2) x3))).
Definition term209 (x0 : nadd) (x1 : nat) (x2 : nadd) := fun y0 : nat -> nat => forall y1 : nat, (Nat.add (dest_nadd x0 y1) x1) = (Nat.add (dest_nadd x2 y1) (y0 y1)).
Definition term208 (x0 : nadd) (x1 : nat) (x2 : nadd) := fun y0 : nat -> nat => forall y1 : nat, (fun y2 : nat => fun y3 : nat => (Nat.add (dest_nadd x0 y2) x1) = (Nat.add (dest_nadd x2 y2) y3)) y1 (y0 y1).
Definition term235 (x0 : nadd) (x1 : nadd) (x2 : nat -> nat) (x3 : nat) := dist (@pair nat nat (dest_nadd x0 x3) (Nat.add (dest_nadd x1 x3) (dest_nadd (mk_nadd x2) x3))).
Definition term200 (x0 : nadd) (x1 : nat) (x2 : nadd) := @eq Prop (forall y0 : nat, exists y1 : nat, (Nat.add (dest_nadd x0 y0) x1) = (Nat.add (dest_nadd x2 y0) y1)).
Definition term199 (x0 : nadd) (x1 : nat) (x2 : nadd) := @eq Prop (forall y0 : nat, exists y1 : nat, (fun y2 : nat => fun y3 : nat => (Nat.add (dest_nadd x0 y2) x1) = (Nat.add (dest_nadd x2 y2) y3)) y0 y1).
Definition term211 (x0 : nadd) (x1 : nadd) (x2 : nat) := imp (forall y0 : nat, Peano.le (dest_nadd x0 y0) (Nat.add (dest_nadd x1 y0) x2)).
Definition term101 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x1 x0) (Nat.mul x1 x2).
Definition term238 (x0 : nadd) (x1 : nadd) (x2 : nat -> nat) (x3 : nat) (x4 : nat) := Peano.le (dist (@pair nat nat (dest_nadd x0 x3) (dest_nadd (nadd_add x1 (mk_nadd x2)) x3))) x4.
Definition term92 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := Peano.le (dist (@pair nat nat (Nat.add x0 x1) (Nat.add x2 x3))) x4.
Definition term170 (x0 : nat) (x1 : nat) := exists y0 : nat, x0 = (Nat.add x1 y0).
Definition term255 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := Nat.mul (Nat.add x0 (Nat.add x1 x2)) (Nat.add x3 x4).
Definition term311 (x0 : nat) (x1 : nadd) (x2 : nat) := Peano.le (dist (@pair nat nat (Nat.mul x2 (dest_nadd x1 x0)) (Nat.mul x0 (dest_nadd x1 x2)))).
Definition term295 (x0 : nat) (x1 : nadd) (x2 : nat) (x3 : nat) := Peano.le (dist (@pair nat nat (Nat.mul x2 (Nat.add (dest_nadd x1 x0) x3)) (Nat.mul x0 (Nat.add (dest_nadd x1 x2) x3)))).
Definition term261 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.mul (Nat.add x0 x1) (Nat.add x2 x3).
Definition term71 (x0 : nat) (x1 : nat) := (Peano.le x1 x0) -> forall y0 : nat, (Peano.le x0 y0) -> Peano.le x1 y0.
Definition term267 (x0 : nadd) (x1 : nat) (x2 : nat) := forall y0 : nat, Peano.le (dist (@pair nat nat (Nat.mul x2 (dest_nadd x0 y0)) (Nat.mul y0 (dest_nadd x0 x2)))) (Nat.mul x1 (Nat.add x2 y0)).
Definition term224 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term178 (x0 : nadd) (x1 : nadd) := (nadd_le x1 x0) -> exists y0 : nadd, nadd_eq x0 (nadd_add x1 y0).
Definition term131 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (Nat.add (dist (@pair nat nat (Nat.add x2 x0) (Nat.add y0 x1))) (dist (@pair nat nat x0 x1))) y1) -> Peano.le (dist (@pair nat nat x2 y0)) y1) x3.
Definition term88 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (Nat.add (dist (@pair nat nat x0 x2)) (dist (@pair nat nat x1 y0))) y1) -> Peano.le (dist (@pair nat nat (Nat.add x0 x1) (Nat.add x2 y0))) y1) x3.
Definition term329 (x0 : nat) := or (x0 = (NUMERAL 0)).
Definition term337 (x0 : nat -> nat) (x1 : nat) (x2 : nat) (x3 : nat) := forall y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (Nat.mul y0 (x0 y1)) (Nat.mul y1 (x0 y0)))) (Nat.mul (Nat.add x1 (Nat.add x2 x3)) (Nat.add y0 y1)).
Definition term151 (x0 : nadd) (x1 : nat) := forall y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (Nat.mul y0 (dest_nadd x0 y1)) (Nat.mul y1 (dest_nadd x0 y0)))) (Nat.mul x1 (Nat.add y0 y1)).
Definition term144 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (exists y3 : nat, exists y4 : nat, Peano.le (Nat.add (dist (@pair nat nat (Nat.add y0 y3) (Nat.add y1 y4))) (dist (@pair nat nat y3 y4))) y2) -> Peano.le (dist (@pair nat nat y0 y1)) y2.
Definition term143 (x0 : nat) := forall y0 : nat, forall y1 : nat, (exists y2 : nat, exists y3 : nat, Peano.le (Nat.add (dist (@pair nat nat (Nat.add x0 y2) (Nat.add y0 y3))) (dist (@pair nat nat y2 y3))) y1) -> Peano.le (dist (@pair nat nat x0 y0)) y1.
Definition term127 := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, forall y4 : nat, (Peano.le (Nat.add (dist (@pair nat nat (Nat.add y2 y0) (Nat.add y3 y1))) (dist (@pair nat nat y0 y1))) y4) -> Peano.le (dist (@pair nat nat y2 y3)) y4.
Definition term126 (x0 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, (Peano.le (Nat.add (dist (@pair nat nat (Nat.add y1 x0) (Nat.add y2 y0))) (dist (@pair nat nat x0 y0))) y3) -> Peano.le (dist (@pair nat nat y1 y2)) y3.
Definition term125 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.le (Nat.add (dist (@pair nat nat (Nat.add y0 x0) (Nat.add y1 x1))) (dist (@pair nat nat x0 x1))) y2) -> Peano.le (dist (@pair nat nat y0 y1)) y2.
Definition term124 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add (dist (@pair nat nat (Nat.add x2 x0) (Nat.add y0 x1))) (dist (@pair nat nat x0 x1))) y1) -> Peano.le (dist (@pair nat nat x2 y0)) y1.
Definition term115 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat x0 y0)) (Nat.add (dist (@pair nat nat (Nat.add x0 x1) (Nat.add y0 y1))) (dist (@pair nat nat x1 y1))).
Definition term113 (x0 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat x0 y1)) (Nat.add (dist (@pair nat nat (Nat.add x0 y0) (Nat.add y1 y2))) (dist (@pair nat nat y0 y2))).
Definition term111 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y2)) = (Nat.mul y0 (Nat.add y1 y2)).
Definition term110 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.mul y0 (Nat.add y1 y2)) = (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y2)).
Definition term107 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y1)) = (Nat.mul x0 (Nat.add y0 y1)).
Definition term96 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.mul x0 (Nat.add y0 y1)) = (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y1)).
Definition term84 := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, forall y4 : nat, (Peano.le (Nat.add (dist (@pair nat nat y0 y2)) (dist (@pair nat nat y1 y3))) y4) -> Peano.le (dist (@pair nat nat (Nat.add y0 y1) (Nat.add y2 y3))) y4.
Definition term83 (x0 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, (Peano.le (Nat.add (dist (@pair nat nat x0 y1)) (dist (@pair nat nat y0 y2))) y3) -> Peano.le (dist (@pair nat nat (Nat.add x0 y0) (Nat.add y1 y2))) y3.
Definition term82 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.le (Nat.add (dist (@pair nat nat x0 y0)) (dist (@pair nat nat x1 y1))) y2) -> Peano.le (dist (@pair nat nat (Nat.add x0 x1) (Nat.add y0 y1))) y2.
Definition term81 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add (dist (@pair nat nat x0 x2)) (dist (@pair nat nat x1 y0))) y1) -> Peano.le (dist (@pair nat nat (Nat.add x0 x1) (Nat.add x2 y0))) y1.
Definition term73 := forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> forall y2 : nat, (Peano.le y1 y2) -> Peano.le y0 y2.
Definition term64 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le x0 y0) -> (Peano.le y0 y1) -> Peano.le x0 y1.
Definition term62 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.le y0 y1) -> (Peano.le y1 y2) -> Peano.le y0 y2.
Definition term57 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (Nat.add x0 x1) (Nat.add y0 y1))) (Nat.add (dist (@pair nat nat x0 y0)) (dist (@pair nat nat x1 y1))).
Definition term55 (x0 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (Nat.add x0 y0) (Nat.add y1 y2))) (Nat.add (dist (@pair nat nat x0 y1)) (dist (@pair nat nat y0 y2))).
Definition term48 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.mul (Nat.add x0 y0) y1) = (Nat.add (Nat.mul x0 y1) (Nat.mul y0 y1)).
Definition term38 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le x1 y1)) -> Peano.le (Nat.add x0 x1) (Nat.add y0 y1).
Definition term36 (x0 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le x0 y1) /\ (Peano.le y0 y2)) -> Peano.le (Nat.add x0 y0) (Nat.add y1 y2).
Definition term34 := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.add y0 y1) (Nat.add y2 y3).
Definition term15 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le (Nat.mul x0 y0) (Nat.mul x0 y1)) = ((x0 = (NUMERAL 0)) \/ (Peano.le y0 y1)).
Definition term13 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (dist (@pair nat nat (Nat.mul y0 y1) (Nat.mul y0 y2))) = (Nat.mul y0 (dist (@pair nat nat y1 y2))).
Definition term12 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.mul y0 (dist (@pair nat nat y1 y2))) = (dist (@pair nat nat (Nat.mul y0 y1) (Nat.mul y0 y2))).
Definition term9 (x0 : nat) := forall y0 : nat, forall y1 : nat, (dist (@pair nat nat (Nat.mul x0 y0) (Nat.mul x0 y1))) = (Nat.mul x0 (dist (@pair nat nat y0 y1))).
Definition term8 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.mul x0 (dist (@pair nat nat y0 y1))) = (dist (@pair nat nat (Nat.mul x0 y0) (Nat.mul x0 y1))).
Definition term297 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.add (Nat.mul x2 (dest_nadd x0 x1)) (Nat.mul x2 x3).
Definition term201 (x0 : nadd) (x1 : nat) (x2 : nadd) (x3 : nat -> nat) (x4 : nat) := (fun y0 : nat => fun y1 : nat => (Nat.add (dest_nadd x0 y0) x1) = (Nat.add (dest_nadd x2 y0) y1)) x4 (x3 x4).
Definition term3 (x0 : nat) (x1 : nat) := fun y0 : nat => (dist (@pair nat nat (Nat.mul x0 x1) (Nat.mul x0 y0))) = (Nat.mul x0 (dist (@pair nat nat x1 y0))).
Definition term93 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, forall y4 : nat, (Peano.le (Nat.add (dist (@pair nat nat y0 y2)) (dist (@pair nat nat y1 y3))) y4) -> Peano.le (dist (@pair nat nat (Nat.add y0 y1) (Nat.add y2 y3))) y4) -> Peano.le (dist (@pair nat nat (Nat.add x0 x1) (Nat.add x2 x3))) x4.
Definition term153 (x0 : nat -> nat) := (fun y0 : nat -> nat => (is_nadd y0) = (exists y1 : nat, forall y2 : nat, forall y3 : nat, Peano.le (dist (@pair nat nat (Nat.mul y2 (y0 y3)) (Nat.mul y3 (y0 y2)))) (Nat.mul y1 (Nat.add y2 y3)))) x0.
Definition term266 (x0 : nadd) (x1 : nat) (x2 : nat) := (fun y0 : nat => forall y1 : nat, Peano.le (dist (@pair nat nat (Nat.mul y0 (dest_nadd x0 y1)) (Nat.mul y1 (dest_nadd x0 y0)))) (Nat.mul x1 (Nat.add y0 y1))) x2.
Definition term116 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => forall y1 : nat, Peano.le (dist (@pair nat nat x0 y0)) (Nat.add (dist (@pair nat nat (Nat.add x0 x1) (Nat.add y0 y1))) (dist (@pair nat nat x1 y1)))) x2.
Definition term58 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => forall y1 : nat, Peano.le (dist (@pair nat nat (Nat.add x0 x1) (Nat.add y0 y1))) (Nat.add (dist (@pair nat nat x0 y0)) (dist (@pair nat nat x1 y1)))) x2.
Definition term39 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le x1 y1)) -> Peano.le (Nat.add x0 x1) (Nat.add y0 y1)) x2.
Definition term129 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, (Peano.le (Nat.add (dist (@pair nat nat (Nat.add y1 x0) (Nat.add y2 y0))) (dist (@pair nat nat x0 y0))) y3) -> Peano.le (dist (@pair nat nat y1 y2)) y3) x1.
Definition term114 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat x0 y1)) (Nat.add (dist (@pair nat nat (Nat.add x0 y0) (Nat.add y1 y2))) (dist (@pair nat nat y0 y2)))) x1.
Definition term86 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, (Peano.le (Nat.add (dist (@pair nat nat x0 y1)) (dist (@pair nat nat y0 y2))) y3) -> Peano.le (dist (@pair nat nat (Nat.add x0 y0) (Nat.add y1 y2))) y3) x1.
Definition term56 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (Nat.add x0 y0) (Nat.add y1 y2))) (Nat.add (dist (@pair nat nat x0 y1)) (dist (@pair nat nat y0 y2)))) x1.
Definition term37 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.le x0 y1) /\ (Peano.le y0 y2)) -> Peano.le (Nat.add x0 y0) (Nat.add y1 y2)) x1.
Definition term196 (x0 : nadd) (x1 : nat) (x2 : nadd) (x3 : nat) := fun y0 : nat => (fun y1 : nat => fun y2 : nat => (Nat.add (dest_nadd x0 y1) x1) = (Nat.add (dest_nadd x2 y1) y2)) x3 y0.
Definition term156 (x0 : nadd) := forall y0 : nadd, (dest_nadd (nadd_add x0 y0)) = (fun y1 : nat => Nat.add (dest_nadd x0 y1) (dest_nadd y0 y1)).
Definition term225 (x0 : nat -> nat) (x1 : nat) := (fun y0 : nat => x0 y0) x1.
Definition term22 (x0 : nat) := forall y0 : nat, Peano.le (dist (@pair nat nat x0 y0)) (Nat.add x0 y0).
Definition term284 (x0 : nat) (x1 : nat) := Nat.mul (Nat.add x0 x1).
Definition term268 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => Peano.le (dist (@pair nat nat (Nat.mul x2 (dest_nadd x0 y0)) (Nat.mul y0 (dest_nadd x0 x2)))) (Nat.mul x1 (Nat.add x2 y0))) x3.
Definition term51 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.mul (Nat.add x0 x1) y0) = (Nat.add (Nat.mul x0 y0) (Nat.mul x1 y0))) x2.
Definition term195 (x0 : nadd) (x1 : nat) (x2 : nadd) (x3 : nat) (x4 : nat) := (fun y0 : nat => (Nat.add (dest_nadd x0 x3) x1) = (Nat.add (dest_nadd x2 x3) y0)) x4.
Definition term24 (x0 : nat) (x1 : nat) := Peano.le (dist (@pair nat nat x0 x1)) (Nat.add x0 x1).
Definition term223 (x0 : nadd) (x1 : nat -> nat) (x2 : nat) := (fun y0 : nat => Nat.add (dest_nadd x0 y0) (dest_nadd (mk_nadd x1) y0)) x2.
Definition term67 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.le x1 x0) -> (Peano.le x0 y0) -> Peano.le x1 y0) x2.
Definition term241 (x0 : nadd) (x1 : nadd) (x2 : nat -> nat) (x3 : nat) := fun y0 : nat => Peano.le (dist (@pair nat nat (dest_nadd x0 y0) (Nat.add (dest_nadd x1 y0) (dest_nadd (mk_nadd x2) y0)))) x3.
Definition term240 (x0 : nadd) (x1 : nadd) (x2 : nat -> nat) (x3 : nat) := fun y0 : nat => Peano.le (dist (@pair nat nat (dest_nadd x0 y0) (dest_nadd (nadd_add x1 (mk_nadd x2)) y0))) x3.
Definition term281 (x0 : nadd) (x1 : nat) (x2 : nat -> nat) (x3 : nat) := dist (@pair nat nat (Nat.add (Nat.mul x3 (dest_nadd x0 x1)) (Nat.mul x3 (x2 x1))) (Nat.add (Nat.mul x1 (dest_nadd x0 x3)) (Nat.mul x1 (x2 x3)))).
Definition term193 (x0 : nadd) (x1 : nat) (x2 : nadd) (x3 : nat) := fun y0 : nat => (Nat.add (dest_nadd x0 x3) x1) = (Nat.add (dest_nadd x2 x3) y0).
Definition term336 (x0 : nat -> nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := forall y0 : nat, Peano.le (dist (@pair nat nat (Nat.mul x4 (x0 y0)) (Nat.mul y0 (x0 x4)))) (Nat.mul (Nat.add x1 (Nat.add x2 x3)) (Nat.add x4 y0)).
Definition term138 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := fun y0 : nat => Peano.le (Nat.add (dist (@pair nat nat (Nat.add x0 x2) (Nat.add x1 y0))) (dist (@pair nat nat x2 y0))) x3.
Definition term155 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, (dest_nadd (nadd_add y0 y1)) = (fun y2 : nat => Nat.add (dest_nadd y0 y2) (dest_nadd y1 y2))) x0.
Definition term260 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := Nat.add (Nat.mul (Nat.add x0 x1) (Nat.add x3 x4)) (Nat.mul x2 (Nat.add x3 x4)).
Definition term249 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat -> nat) := (fun y0 : nat -> nat => Peano.le (dist (@pair nat nat (dest_nadd x0 x2) (Nat.add (dest_nadd x1 x2) (y0 x2)))) x3) x4.
Definition term52 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.add x0 x1) x2.
Definition term264 (x0 : nat -> nat) (x1 : nat) (x2 : nadd) (x3 : nat) := dist (@pair nat nat (Nat.add (Nat.mul x3 (x0 x1)) (Nat.mul x3 (dest_nadd x2 x1))) (Nat.add (Nat.mul x1 (x0 x3)) (Nat.mul x1 (dest_nadd x2 x3)))).
Definition term119 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (dist (@pair nat nat x0 x1)) (Nat.add (dist (@pair nat nat (Nat.add x0 x2) (Nat.add x1 x3))) (dist (@pair nat nat x2 x3))).
Definition term53 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x0 x2) (Nat.mul x1 x2).
Definition term98 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.mul x1 (Nat.add x0 y0)) = (Nat.add (Nat.mul x1 x0) (Nat.mul x1 y0)).
Definition term17 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le (Nat.mul x0 x1) (Nat.mul x0 y0)) = ((x0 = (NUMERAL 0)) \/ (Peano.le x1 y0)).
Definition term78 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.add (dist (@pair nat nat x0 x1)) (dist (@pair nat nat x2 x3)).
Definition term262 (x0 : nat -> nat) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : nat) (x6 : nat) := Peano.le (Nat.add (dist (@pair nat nat (Nat.add (Nat.mul x5 (x0 x6)) (Nat.mul x5 (dest_nadd x1 x6))) (Nat.add (Nat.mul x6 (x0 x5)) (Nat.mul x6 (dest_nadd x1 x5))))) (dist (@pair nat nat (Nat.mul x5 (dest_nadd x1 x6)) (Nat.mul x6 (dest_nadd x1 x5))))) (Nat.add (Nat.mul (Nat.add x2 x3) (Nat.add x5 x6)) (Nat.mul x4 (Nat.add x5 x6))).
Definition term4 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.mul x1 (dist (@pair nat nat x0 y0))) = (dist (@pair nat nat (Nat.mul x1 x0) (Nat.mul x1 y0))).
Definition term290 (x0 : nat) (x1 : nadd) (x2 : nat -> nat) (x3 : nat) := Nat.mul x0 (Nat.add (dest_nadd x1 x3) (x2 x3)).
Definition term130 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le (Nat.add (dist (@pair nat nat (Nat.add y0 x0) (Nat.add y1 x1))) (dist (@pair nat nat x0 x1))) y2) -> Peano.le (dist (@pair nat nat y0 y1)) y2) x2.
Definition term87 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le (Nat.add (dist (@pair nat nat x0 y0)) (dist (@pair nat nat x1 y1))) y2) -> Peano.le (dist (@pair nat nat (Nat.add x0 x1) (Nat.add y0 y1))) y2) x2.
Definition term226 (x0 : nadd) (x1 : nat -> nat) (x2 : nat) := (fun y0 : nat => (fun y1 : nat => Nat.add (dest_nadd x0 y1) (dest_nadd (mk_nadd x1) y1)) y0) x2.
Definition term345 (x0 : nat) (x1 : nat) := dist (@pair nat nat x0 (Nat.add x0 x1)).
Definition term214 (x0 : nat) (x1 : nadd) (x2 : nadd) := (exists y0 : nat -> nat, forall y1 : nat, (Nat.add (dest_nadd x1 y1) x0) = (Nat.add (dest_nadd x2 y1) (y0 y1))) -> exists y0 : nadd, nadd_eq x1 (nadd_add x2 y0).
Definition term179 (x0 : nadd) (x1 : nadd) := (exists y0 : nat, forall y1 : nat, Peano.le (dest_nadd x1 y1) (Nat.add (dest_nadd x0 y1) y0)) -> exists y0 : nadd, nadd_eq x0 (nadd_add x1 y0).
Definition term32 (x0 : nat) := forall y0 : nat, (Nat.add x0 y0) = (Nat.add y0 x0).
Definition term29 (x0 : nat) := forall y0 : nat, (Nat.mul x0 y0) = (Nat.mul y0 x0).
Definition term19 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul x1 x0) (Nat.mul x1 x2).
Definition term132 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := (fun y0 : nat => (Peano.le (Nat.add (dist (@pair nat nat (Nat.add x2 x0) (Nat.add x3 x1))) (dist (@pair nat nat x0 x1))) y0) -> Peano.le (dist (@pair nat nat x2 x3)) y0) x4.
Definition term89 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := (fun y0 : nat => (Peano.le (Nat.add (dist (@pair nat nat x0 x2)) (dist (@pair nat nat x1 x3))) y0) -> Peano.le (dist (@pair nat nat (Nat.add x0 x1) (Nat.add x2 x3))) y0) x4.
Definition term302 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := Peano.le (dist (@pair nat nat (Nat.add (Nat.mul x4 (dest_nadd x0 x3)) (Nat.mul x4 x1)) (Nat.add (Nat.mul x3 (dest_nadd x0 x4)) (Nat.mul x3 x1)))) (Nat.mul (Nat.add x1 x2) (Nat.add x3 x4)).
Definition term296 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := Peano.le (dist (@pair nat nat (Nat.mul x4 (Nat.add (dest_nadd x0 x3) x1)) (Nat.mul x3 (Nat.add (dest_nadd x0 x4) x1)))) (Nat.mul (Nat.add x1 x2) (Nat.add x3 x4)).
Definition term205 (x0 : nadd) (x1 : nat) (x2 : nadd) (x3 : nat -> nat) := fun y0 : nat => (Nat.add (dest_nadd x0 y0) x1) = (Nat.add (dest_nadd x2 y0) (x3 y0)).
Definition term217 (x0 : nadd) (x1 : nadd) (x2 : nat -> nat) := nadd_eq x0 (nadd_add x1 (mk_nadd x2)).
Definition term215 (x0 : nadd) (x1 : nat -> nat) (x2 : nadd) (x3 : nat) := fun y0 : nat => (Nat.add (dest_nadd x0 y0) (x1 y0)) = (Nat.add (dest_nadd x2 y0) x3).
Definition term280 (x0 : nadd) (x1 : nat) (x2 : nat -> nat) (x3 : nat) := @pair nat nat (Nat.add (Nat.mul x3 (dest_nadd x0 x1)) (Nat.mul x3 (x2 x1))) (Nat.add (Nat.mul x1 (dest_nadd x0 x3)) (Nat.mul x1 (x2 x3))).
Definition term243 (x0 : nadd) (x1 : nadd) (x2 : nat -> nat) (x3 : nat) := forall y0 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 y0) (Nat.add (dest_nadd x1 y0) (dest_nadd (mk_nadd x2) y0)))) x3.
Definition term242 (x0 : nadd) (x1 : nadd) (x2 : nat -> nat) (x3 : nat) := forall y0 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 y0) (dest_nadd (nadd_add x1 (mk_nadd x2)) y0))) x3.
Definition term33 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add x0 y0) = (Nat.add y0 x0)) x1.
Definition term30 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.mul x0 y0) = (Nat.mul y0 x0)) x1.
Definition term303 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := (Peano.le (Nat.add (dist (@pair nat nat (Nat.mul x4 (dest_nadd x0 x3)) (Nat.mul x3 (dest_nadd x0 x4)))) (dist (@pair nat nat (Nat.mul x4 x1) (Nat.mul x3 x1)))) (Nat.mul (Nat.add x1 x2) (Nat.add x3 x4))) -> Peano.le (dist (@pair nat nat (Nat.add (Nat.mul x4 (dest_nadd x0 x3)) (Nat.mul x4 x1)) (Nat.add (Nat.mul x3 (dest_nadd x0 x4)) (Nat.mul x3 x1)))) (Nat.mul (Nat.add x1 x2) (Nat.add x3 x4)).
Definition term326 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul x0 (dist (@pair nat nat x1 x2))).
Definition term339 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add x0 (Nat.add x1 x2).
Definition term343 (x0 : nat) := forall y0 : nat, (dist (@pair nat nat x0 (Nat.add x0 y0))) = y0.
Definition term292 (x0 : nat) (x1 : nadd) (x2 : nat) (x3 : nat) := @pair nat nat (Nat.mul x0 (Nat.add (dest_nadd x1 x2) x3)).
Definition term142 (x0 : nat) (x1 : nat) := forall y0 : nat, (exists y1 : nat, exists y2 : nat, Peano.le (Nat.add (dist (@pair nat nat (Nat.add x0 y1) (Nat.add x1 y2))) (dist (@pair nat nat y1 y2))) y0) -> Peano.le (dist (@pair nat nat x0 x1)) y0.
Definition term245 (x0 : nadd) (x1 : nadd) (x2 : nat -> nat) := fun y0 : nat => forall y1 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 y1) (Nat.add (dest_nadd x1 y1) (dest_nadd (mk_nadd x2) y1)))) y0.
Definition term244 (x0 : nadd) (x1 : nadd) (x2 : nat -> nat) := fun y0 : nat => forall y1 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 y1) (dest_nadd (nadd_add x1 (mk_nadd x2)) y1))) y0.
Definition term79 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := dist (@pair nat nat (Nat.add x0 x1) (Nat.add x2 x3)).
Definition term320 (x0 : nat) (x1 : nat) (x2 : nat) := True /\ (Peano.le (dist (@pair nat nat (Nat.mul x1 x0) (Nat.mul x2 x0))) (Nat.mul x0 (Nat.add x1 x2))).
Definition term192 (x0 : nadd) (x1 : nat) (x2 : nadd) (x3 : nat) := (fun y0 : nat => fun y1 : nat => (Nat.add (dest_nadd x0 y0) x1) = (Nat.add (dest_nadd x2 y0) y1)) x3.
Definition term322 (x0 : nat) (x1 : nat) (x2 : nat) := @pair nat nat (Nat.mul x0 x2) (Nat.mul x1 x2).
Definition term167 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) = (exists y2 : nat, y1 = (Nat.add y0 y2))) x0.
Definition term75 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) -> forall y2 : nat, (Peano.le y1 y2) -> Peano.le y0 y2) x0.
Definition term31 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) x0.
Definition term28 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) x0.
Definition term21 (x0 : nat) := (fun y0 : nat => forall y1 : nat, Peano.le (dist (@pair nat nat y0 y1)) (Nat.add y0 y1)) x0.
Definition term227 (x0 : nadd) (x1 : nat -> nat) (x2 : nat) := Nat.add (dest_nadd x0 x2) (dest_nadd (mk_nadd x1) x2).
Definition term102 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.mul x1 (Nat.add x0 y0)) = (Nat.add (Nat.mul x1 x0) (Nat.mul x1 y0)).
Definition term43 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le x0 x1) /\ (Peano.le x2 x3).
Definition term40 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, ((Peano.le x0 x2) /\ (Peano.le x1 y0)) -> Peano.le (Nat.add x0 x1) (Nat.add x2 y0).
Definition term123 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := forall y0 : nat, (Peano.le (Nat.add (dist (@pair nat nat (Nat.add x2 x0) (Nat.add x3 x1))) (dist (@pair nat nat x0 x1))) y0) -> Peano.le (dist (@pair nat nat x2 x3)) y0.
Definition term80 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := forall y0 : nat, (Peano.le (Nat.add (dist (@pair nat nat x0 x2)) (dist (@pair nat nat x1 x3))) y0) -> Peano.le (dist (@pair nat nat (Nat.add x0 x1) (Nat.add x2 x3))) y0.
Definition term332 (x0 : nat -> nat) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : nat) (x6 : nat) := fun y0 : nat => Peano.le (Nat.add (dist (@pair nat nat (Nat.add (Nat.mul x5 (x0 x6)) (Nat.mul x5 (dest_nadd x1 x6))) (Nat.add (Nat.mul x6 (x0 x5)) y0))) (dist (@pair nat nat (Nat.mul x5 (dest_nadd x1 x6)) y0))) (Nat.mul (Nat.add x2 (Nat.add x3 x4)) (Nat.add x5 x6)).
Definition term278 (x0 : nadd) (x1 : nat) (x2 : nat -> nat) (x3 : nat) := @pair nat nat (Nat.add (Nat.mul x1 (dest_nadd x0 x3)) (Nat.mul x1 (x2 x3))).
Definition term277 (x0 : nat -> nat) (x1 : nat) (x2 : nadd) (x3 : nat) := @pair nat nat (Nat.add (Nat.mul x1 (x0 x3)) (Nat.mul x1 (dest_nadd x2 x3))).
Definition term120 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le (dist (@pair nat nat x2 x3)) (Nat.add (dist (@pair nat nat (Nat.add x2 x0) (Nat.add x3 x1))) (dist (@pair nat nat x0 x1)))) -> forall y0 : nat, (Peano.le (Nat.add (dist (@pair nat nat (Nat.add x2 x0) (Nat.add x3 x1))) (dist (@pair nat nat x0 x1))) y0) -> Peano.le (dist (@pair nat nat x2 x3)) y0.
Definition term77 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le (dist (@pair nat nat (Nat.add x0 x1) (Nat.add x2 x3))) (Nat.add (dist (@pair nat nat x0 x2)) (dist (@pair nat nat x1 x3)))) -> forall y0 : nat, (Peano.le (Nat.add (dist (@pair nat nat x0 x2)) (dist (@pair nat nat x1 x3))) y0) -> Peano.le (dist (@pair nat nat (Nat.add x0 x1) (Nat.add x2 x3))) y0.
Definition term275 (x0 : nadd) (x1 : nat) (x2 : nat -> nat) (x3 : nat) := Nat.add (Nat.mul x1 (dest_nadd x0 x3)) (Nat.mul x1 (x2 x3)).
Definition term323 (x0 : nat) (x1 : nat) (x2 : nat) := @pair nat nat (Nat.mul x1 x0) (Nat.mul x1 x2).
Definition term68 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x1 x0) -> (Peano.le x0 x2) -> Peano.le x1 x2.
Definition term18 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.le (Nat.mul x0 x1) (Nat.mul x0 y0)) = ((x0 = (NUMERAL 0)) \/ (Peano.le x1 y0))) x2.
Definition term45 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.add y0 y1) (Nat.add y2 y3)) -> Peano.le (Nat.add x0 x1) (Nat.add x2 x3).
Definition term325 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (dist (@pair nat nat (Nat.mul x0 x1) (Nat.mul x0 x2))) (Nat.mul x0 (Nat.add x1 x2)).
Definition term317 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (dist (@pair nat nat (Nat.mul x1 x0) (Nat.mul x2 x0))) (Nat.mul x0 (Nat.add x1 x2)).
Definition term316 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (dist (@pair nat nat (Nat.mul x2 x0) (Nat.mul x1 x0))) (Nat.mul x0 (Nat.add x1 x2)).
Definition term118 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => Peano.le (dist (@pair nat nat x0 x1)) (Nat.add (dist (@pair nat nat (Nat.add x0 x2) (Nat.add x1 y0))) (dist (@pair nat nat x2 y0)))) x3.
Definition term285 (x0 : nadd) (x1 : nat -> nat) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : nat) := Peano.le (dist (@pair nat nat (Nat.add (Nat.mul x5 (dest_nadd x0 x4)) (Nat.mul x5 (x1 x4))) (Nat.add (Nat.mul x4 (dest_nadd x0 x5)) (Nat.mul x4 (x1 x5))))) (Nat.mul (Nat.add x2 x3) (Nat.add x4 x5)).
Definition term273 (x0 : nat -> nat) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : nat) := Peano.le (dist (@pair nat nat (Nat.add (Nat.mul x4 (x0 x5)) (Nat.mul x4 (dest_nadd x1 x5))) (Nat.add (Nat.mul x5 (x0 x4)) (Nat.mul x5 (dest_nadd x1 x4))))) (Nat.mul (Nat.add x2 x3) (Nat.add x4 x5)).
Definition term50 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.mul (Nat.add x0 x1) y0) = (Nat.add (Nat.mul x0 y0) (Nat.mul x1 y0)).
Definition term182 (x0 : nadd) (x1 : nat) (x2 : nadd) (x3 : nat) := exists y0 : nat, (Nat.add (dest_nadd x0 x3) x1) = (Nat.add (dest_nadd x2 x3) y0).
Definition term121 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.add (dist (@pair nat nat (Nat.add x0 x2) (Nat.add x1 x3))) (dist (@pair nat nat x2 x3)).
Definition term253 (x0 : nat -> nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : nat) := (exists y0 : nat, exists y1 : nat, Peano.le (Nat.add (dist (@pair nat nat (Nat.add (Nat.mul x4 (x0 x5)) y0) (Nat.add (Nat.mul x5 (x0 x4)) y1))) (dist (@pair nat nat y0 y1))) (Nat.mul (Nat.add x1 (Nat.add x2 x3)) (Nat.add x4 x5))) -> Peano.le (dist (@pair nat nat (Nat.mul x4 (x0 x5)) (Nat.mul x5 (x0 x4)))) (Nat.mul (Nat.add x1 (Nat.add x2 x3)) (Nat.add x4 x5)).
Definition term198 (x0 : nadd) (x1 : nat) (x2 : nadd) := fun y0 : nat => exists y1 : nat, (fun y2 : nat => fun y3 : nat => (Nat.add (dest_nadd x0 y2) x1) = (Nat.add (dest_nadd x2 y2) y3)) y0 y1.
Definition term181 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) := Peano.le (dest_nadd x0 x2) (Nat.add (dest_nadd x1 x2) x3).
Definition term176 (x0 : nadd) (x1 : nadd) := imp (exists y0 : nat, forall y1 : nat, Peano.le (dest_nadd x0 y1) (Nat.add (dest_nadd x1 y1) y0)).
Definition term194 (x0 : nadd) (x1 : nat) (x2 : nadd) (x3 : nat) (x4 : nat) := (fun y0 : nat => fun y1 : nat => (Nat.add (dest_nadd x0 y0) x1) = (Nat.add (dest_nadd x2 y0) y1)) x3 x4.
Definition term204 (x0 : nadd) (x1 : nat) (x2 : nadd) (x3 : nat -> nat) := fun y0 : nat => (fun y1 : nat => fun y2 : nat => (Nat.add (dest_nadd x0 y1) x1) = (Nat.add (dest_nadd x2 y1) y2)) y0 (x3 y0).
Definition term149 (x0 : nadd) := (fun y0 : nadd => exists y1 : nat, forall y2 : nat, forall y3 : nat, Peano.le (dist (@pair nat nat (Nat.mul y2 (dest_nadd y0 y3)) (Nat.mul y3 (dest_nadd y0 y2)))) (Nat.mul y1 (Nat.add y2 y3))) x0.
Definition term258 (x0 : nat -> nat) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : nat) (x6 : nat) := Peano.le (Nat.add (dist (@pair nat nat (Nat.add (Nat.mul x5 (x0 x6)) (Nat.mul x5 (dest_nadd x1 x6))) (Nat.add (Nat.mul x6 (x0 x5)) (Nat.mul x6 (dest_nadd x1 x5))))) (dist (@pair nat nat (Nat.mul x5 (dest_nadd x1 x6)) (Nat.mul x6 (dest_nadd x1 x5))))) (Nat.mul (Nat.add x2 (Nat.add x3 x4)) (Nat.add x5 x6)).
Definition term344 (x0 : nat) (x1 : nat) := (fun y0 : nat => (dist (@pair nat nat x0 (Nat.add x0 y0))) = y0) x1.
Definition term353 (x0 : nadd) := forall y0 : nadd, (nadd_le x0 y0) -> exists y1 : nadd, nadd_eq y0 (nadd_add x0 y1).
Definition term159 (x0 : nadd) (x1 : nadd) := fun y0 : nat => Nat.add (dest_nadd x0 y0) (dest_nadd x1 y0).
Definition term172 (x0 : nadd) := forall y0 : nadd, (nadd_le x0 y0) = (exists y1 : nat, forall y2 : nat, Peano.le (dest_nadd x0 y2) (Nat.add (dest_nadd y0 y2) y1)).
Definition term161 (x0 : nadd) := forall y0 : nadd, (nadd_eq x0 y0) = (exists y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 y2) (dest_nadd y0 y2))) y1).
Definition term348 (x0 : nadd) (x1 : nadd) (x2 : nat -> nat) (x3 : nat) := dist (@pair nat nat (dest_nadd x0 x3) (Nat.add (dest_nadd x1 x3) (x2 x3))).
Definition term319 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := (Peano.le (dist (@pair nat nat (Nat.mul x3 (dest_nadd x0 x4)) (Nat.mul x4 (dest_nadd x0 x3)))) (Nat.mul x1 (Nat.add x3 x4))) /\ (Peano.le (dist (@pair nat nat (Nat.mul x3 x2) (Nat.mul x4 x2))) (Nat.mul x2 (Nat.add x3 x4))).
Definition term318 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := (Peano.le (dist (@pair nat nat (Nat.mul x4 (dest_nadd x0 x3)) (Nat.mul x3 (dest_nadd x0 x4)))) (Nat.mul x1 (Nat.add x3 x4))) /\ (Peano.le (dist (@pair nat nat (Nat.mul x4 x2) (Nat.mul x3 x2))) (Nat.mul x2 (Nat.add x3 x4))).
Definition term100 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (Nat.add x1 x2).
Definition term6 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Nat.mul x0 (dist (@pair nat nat y0 y1))) = (dist (@pair nat nat (Nat.mul x0 y0) (Nat.mul x0 y1))).
Definition term310 (x0 : nat) (x1 : nat) (x2 : nat) := dist (@pair nat nat (Nat.mul x0 x2) (Nat.mul x1 x2)).
Definition term164 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := (fun y0 : type1413 a0 a1 => (forall y1 : a0, exists y2 : a1, y0 y1 y2) = (exists y1 : a0 -> a1, forall y2 : a0, y0 y2 (y1 y2))) x0.
Definition term333 (x0 : nat -> nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : nat) := exists y0 : nat, exists y1 : nat, Peano.le (Nat.add (dist (@pair nat nat (Nat.add (Nat.mul x4 (x0 x5)) y0) (Nat.add (Nat.mul x5 (x0 x4)) y1))) (dist (@pair nat nat y0 y1))) (Nat.mul (Nat.add x1 (Nat.add x2 x3)) (Nat.add x4 x5)).
Definition term139 (x0 : nat) (x1 : nat) (x2 : nat) := exists y0 : nat, exists y1 : nat, Peano.le (Nat.add (dist (@pair nat nat (Nat.add x0 y0) (Nat.add x1 y1))) (dist (@pair nat nat y0 y1))) x2.
Definition term135 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (dist (@pair nat nat x0 x1)) x2.
Definition term231 (x0 : nadd) (x1 : nat) := @pair nat nat (dest_nadd x0 x1).
Definition term70 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le x0 y0) -> Peano.le x1 y0.
Definition term207 (x0 : nadd) (x1 : nat) (x2 : nadd) (x3 : nat -> nat) := forall y0 : nat, (Nat.add (dest_nadd x0 y0) x1) = (Nat.add (dest_nadd x2 y0) (x3 y0)).
Definition term60 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => Peano.le (dist (@pair nat nat (Nat.add x0 x2) (Nat.add x1 y0))) (Nat.add (dist (@pair nat nat x0 x1)) (dist (@pair nat nat x2 y0)))) x3.
Definition term5 (x0 : nat) (x1 : nat) := forall y0 : nat, (dist (@pair nat nat (Nat.mul x0 x1) (Nat.mul x0 y0))) = (Nat.mul x0 (dist (@pair nat nat x1 y0))).
Definition term228 (x0 : nadd) (x1 : nat -> nat) := fun y0 : nat => (fun y1 : nat => Nat.add (dest_nadd x0 y1) (dest_nadd (mk_nadd x1) y1)) y0.
Definition term2 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.mul x1 (dist (@pair nat nat x0 y0))) = (dist (@pair nat nat (Nat.mul x1 x0) (Nat.mul x1 y0))).
Definition term169 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le x0 y0) = (exists y1 : nat, y0 = (Nat.add x0 y1))) x1.
Definition term308 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := Peano.le (Nat.add (dist (@pair nat nat (Nat.mul x4 (dest_nadd x0 x3)) (Nat.mul x3 (dest_nadd x0 x4)))) (dist (@pair nat nat (Nat.mul x4 x2) (Nat.mul x3 x2)))) (Nat.add (Nat.mul x1 (Nat.add x3 x4)) (Nat.mul x2 (Nat.add x3 x4))).
Definition term307 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := Peano.le (Nat.add (dist (@pair nat nat (Nat.mul x4 (dest_nadd x0 x3)) (Nat.mul x3 (dest_nadd x0 x4)))) (dist (@pair nat nat (Nat.mul x4 x1) (Nat.mul x3 x1)))) (Nat.add (Nat.mul x1 (Nat.add x3 x4)) (Nat.mul x2 (Nat.add x3 x4))).
Definition term166 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := exists y0 : a0 -> a1, forall y1 : a0, x0 y1 (y0 y1).
Definition term299 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := @pair nat nat (Nat.add (Nat.mul x1 (dest_nadd x0 x2)) (Nat.mul x1 x3)) (Nat.add (Nat.mul x2 (dest_nadd x0 x1)) (Nat.mul x2 x3)).
Definition term212 (x0 : nadd) (x1 : nat) (x2 : nadd) := imp (exists y0 : nat -> nat, forall y1 : nat, (Nat.add (dest_nadd x0 y1) x1) = (Nat.add (dest_nadd x2 y1) (y0 y1))).
Definition term265 (x0 : nat) (x1 : nadd) (x2 : nat) := dist (@pair nat nat (Nat.mul x2 (dest_nadd x1 x0)) (Nat.mul x0 (dest_nadd x1 x2))).
Definition term202 (x0 : nadd) (x1 : nat) (x2 : nadd) (x3 : nat -> nat) (x4 : nat) := (fun y0 : nat => (Nat.add (dest_nadd x0 x4) x1) = (Nat.add (dest_nadd x2 x4) y0)) (x3 x4).
Definition term27 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (dist (@pair nat nat (Nat.mul x0 x1) (Nat.mul x0 y0))) = (Nat.mul x0 (dist (@pair nat nat x1 y0)))) x2.
Definition term304 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.add (Nat.mul x0 (Nat.add x2 x3)) (Nat.mul x1 (Nat.add x2 x3)).
Definition term236 (x0 : nadd) (x1 : nadd) (x2 : nat -> nat) (x3 : nat) := Peano.le (dist (@pair nat nat (dest_nadd x0 x3) (dest_nadd (nadd_add x1 (mk_nadd x2)) x3))).
Definition term42 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Peano.le x0 x2) /\ (Peano.le x1 x3)) -> Peano.le (Nat.add x0 x1) (Nat.add x2 x3).
Definition term216 (x0 : nadd) (x1 : nat -> nat) (x2 : nadd) (x3 : nat) := forall y0 : nat, (Nat.add (dest_nadd x0 y0) (x1 y0)) = (Nat.add (dest_nadd x2 y0) x3).
Definition term76 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le x0 y0) -> forall y1 : nat, (Peano.le y0 y1) -> Peano.le x0 y1) x1.
Definition term106 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y1)) = (Nat.mul x0 (Nat.add y0 y1)).
Definition term105 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Nat.mul x0 (Nat.add y0 y1)) = (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y1)).
Definition term7 (x0 : nat) := fun y0 : nat => forall y1 : nat, (dist (@pair nat nat (Nat.mul x0 y0) (Nat.mul x0 y1))) = (Nat.mul x0 (dist (@pair nat nat y0 y1))).
Definition term203 (x0 : nadd) (x1 : nat -> nat) (x2 : nat) := Nat.add (dest_nadd x0 x2) (x1 x2).
Definition term232 (x0 : nadd) (x1 : nadd) (x2 : nat -> nat) (x3 : nat) := @pair nat nat (dest_nadd x0 x3) (dest_nadd (nadd_add x1 (mk_nadd x2)) x3).
Definition term340 (x0 : nadd) := fun y0 : nat => forall y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (Nat.mul y1 (dest_nadd x0 y2)) (Nat.mul y2 (dest_nadd x0 y1)))) (Nat.mul y0 (Nat.add y1 y2)).
Definition term338 (x0 : nat -> nat) := fun y0 : nat => forall y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (Nat.mul y1 (x0 y2)) (Nat.mul y2 (x0 y1)))) (Nat.mul y0 (Nat.add y1 y2)).
Definition term109 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y2)) = (Nat.mul y0 (Nat.add y1 y2)).
Definition term108 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.mul y0 (Nat.add y1 y2)) = (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y2)).
Definition term11 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (dist (@pair nat nat (Nat.mul y0 y1) (Nat.mul y0 y2))) = (Nat.mul y0 (dist (@pair nat nat y1 y2))).
Definition term10 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.mul y0 (dist (@pair nat nat y1 y2))) = (dist (@pair nat nat (Nat.mul y0 y1) (Nat.mul y0 y2))).
Definition term233 (x0 : nadd) (x1 : nadd) (x2 : nat -> nat) (x3 : nat) := @pair nat nat (dest_nadd x0 x3) (Nat.add (dest_nadd x1 x3) (dest_nadd (mk_nadd x2) x3)).
Definition term272 (x0 : nat -> nat) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : nat) := (Peano.le (dist (@pair nat nat (Nat.add (Nat.mul x4 (x0 x5)) (Nat.mul x4 (dest_nadd x1 x5))) (Nat.add (Nat.mul x5 (x0 x4)) (Nat.mul x5 (dest_nadd x1 x4))))) (Nat.mul (Nat.add x2 x3) (Nat.add x4 x5))) /\ True.
Definition term312 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (dist (@pair nat nat (Nat.mul x3 (dest_nadd x0 x2)) (Nat.mul x2 (dest_nadd x0 x3)))) (Nat.mul x1 (Nat.add x2 x3)).
Definition term269 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (dist (@pair nat nat (Nat.mul x2 (dest_nadd x0 x3)) (Nat.mul x3 (dest_nadd x0 x2)))) (Nat.mul x1 (Nat.add x2 x3)).
Definition term117 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, Peano.le (dist (@pair nat nat x0 x1)) (Nat.add (dist (@pair nat nat (Nat.add x0 x2) (Nat.add x1 y0))) (dist (@pair nat nat x2 y0))).
Definition term59 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, Peano.le (dist (@pair nat nat (Nat.add x0 x2) (Nat.add x1 y0))) (Nat.add (dist (@pair nat nat x0 x1)) (dist (@pair nat nat x2 y0))).
