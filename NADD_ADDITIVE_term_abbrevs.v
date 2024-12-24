Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term22 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.mul x1 (Nat.add x0 y0)) = (Nat.add (Nat.mul x1 x0) (Nat.mul x1 y0))) x2.
Definition term242 (x0 : nadd) (x1 : nat) (x2 : nat) := @pair nat nat (Nat.mul (Nat.add x1 x2) (dest_nadd x0 (Nat.add x1 x2))).
Definition term173 (x0 : nat) (x1 : nat) := exists y0 : nat, (Peano.le x0 y0) /\ (Peano.le y0 x1).
Definition term286 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x0 x1) (Nat.mul x0 (Nat.add x1 x1)).
Definition term243 (x0 : nat) (x1 : nadd) (x2 : nat) := @pair nat nat (Nat.mul (Nat.add x0 x2) (dest_nadd x1 (Nat.add x0 x2))) (Nat.mul (Nat.add x0 x2) (Nat.add (dest_nadd x1 x0) (dest_nadd x1 x2))).
Definition term258 (x0 : nadd) (x1 : nat) (x2 : nat) := Nat.mul x1 (dest_nadd x0 (Nat.add x1 x2)).
Definition term226 (x0 : nadd) := Peano.le (dest_nadd x0 (NUMERAL 0)).
Definition term272 (x0 : nat) := Nat.mul (Nat.add (NUMERAL (BIT1 0)) (Nat.add (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)))) x0.
Definition term95 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x2) -> Peano.le x1 x2.
Definition term245 (x0 : nat) (x1 : nadd) (x2 : nat) := dist (@pair nat nat (Nat.mul (Nat.add x0 x2) (dest_nadd x1 (Nat.add x0 x2))) (Nat.add (Nat.mul (Nat.add x0 x2) (dest_nadd x1 x0)) (Nat.mul (Nat.add x0 x2) (dest_nadd x1 x2)))).
Definition term353 (x0 : nadd) := exists y0 : nat, forall y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 (Nat.add y1 y2)) (Nat.add (dest_nadd x0 y1) (dest_nadd x0 y2)))) y0.
Definition term193 (x0 : nadd) := exists y0 : nat, forall y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (Nat.mul y1 (dest_nadd x0 y2)) (Nat.mul y2 (dest_nadd x0 y1)))) (Nat.mul y0 (Nat.add y1 y2)).
Definition term14 := (forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))))).
Definition term332 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Nat.add y0 y1) = (Nat.add y0 y2)) = (y1 = y2)) x0.
Definition term165 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) x0.
Definition term157 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((y0 = (NUMERAL 0)) \/ (Peano.le y1 y2)) = (Peano.le (Nat.mul y0 y1) (Nat.mul y0 y2))) x0.
Definition term121 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.mul y0 (dist (@pair nat nat y1 y2))) = (dist (@pair nat nat (Nat.mul y0 y1) (Nat.mul y0 y2)))) x0.
Definition term111 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, forall y4 : nat, (Peano.le (Nat.add (dist (@pair nat nat y0 y2)) (dist (@pair nat nat y1 y3))) y4) -> Peano.le (dist (@pair nat nat (Nat.add y0 y1) (Nat.add y2 y3))) y4) x0.
Definition term89 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le y0 y1) -> (Peano.le y1 y2) -> Peano.le y0 y2) x0.
Definition term80 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, Peano.le (dist (@pair nat nat (Nat.add y0 y1) (Nat.add y2 y3))) (Nat.add (dist (@pair nat nat y0 y2)) (dist (@pair nat nat y1 y3)))) x0.
Definition term25 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.mul (Nat.add y0 y1) y2) = (Nat.add (Nat.mul y0 y2) (Nat.mul y1 y2))) x0.
Definition term18 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.mul y0 (Nat.add y1 y2)) = (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y2))) x0.
Definition term1 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.add y0 y1) (Nat.add y2 y3)) x0.
Definition term7 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => ((Peano.le x0 x2) /\ (Peano.le x1 y0)) -> Peano.le (Nat.add x0 x1) (Nat.add x2 y0)) x3.
Definition term182 (x0 : nat) := forall y0 : nat, (dist (@pair nat nat x0 y0)) = (dist (@pair nat nat y0 x0)).
Definition term60 (x0 : nat) (x1 : nat) := Nat.add (NUMERAL x0) (NUMERAL x1).
Definition term59 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add (NUMERAL x0) (NUMERAL y0)) = (NUMERAL (Nat.add x0 y0))) x1.
Definition term265 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => Peano.le (Nat.add (dist (@pair nat nat (Nat.mul x2 (dest_nadd x0 (Nat.add x2 x3))) (Nat.mul (Nat.add x2 x3) (dest_nadd x0 x2)))) (dist (@pair nat nat (Nat.mul x3 (dest_nadd x0 (Nat.add x2 x3))) (Nat.mul (Nat.add x2 x3) (dest_nadd x0 x3))))) y0) (Nat.add (Nat.mul x1 (Nat.add x2 (Nat.add x2 x3))) (Nat.mul x1 (Nat.add x3 (Nat.add x2 x3)))).
Definition term283 (x0 : nat) := Nat.add x0 (Nat.add x0 x0).
Definition term53 := forall y0 : nat, (Nat.add 0 (BIT1 y0)) = (BIT1 y0).
Definition term36 := (forall y0 : nat, (Nat.add (BIT0 y0) 0) = (BIT0 y0)) /\ ((forall y0 : nat, (Nat.add (BIT1 y0) 0) = (BIT1 y0)) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT0 y1)) = (BIT0 (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT1 y1)) = (BIT1 (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT0 y1)) = (BIT1 (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT1 y1)) = (BIT0 (S (Nat.add y0 y1)))))))).
Definition term35 := (forall y0 : nat, (Nat.add 0 (BIT1 y0)) = (BIT1 y0)) /\ ((forall y0 : nat, (Nat.add (BIT0 y0) 0) = (BIT0 y0)) /\ ((forall y0 : nat, (Nat.add (BIT1 y0) 0) = (BIT1 y0)) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT0 y1)) = (BIT0 (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT1 y1)) = (BIT1 (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT0 y1)) = (BIT1 (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT1 y1)) = (BIT0 (S (Nat.add y0 y1))))))))).
Definition term34 := (forall y0 : nat, (Nat.add 0 (BIT0 y0)) = (BIT0 y0)) /\ ((forall y0 : nat, (Nat.add 0 (BIT1 y0)) = (BIT1 y0)) /\ ((forall y0 : nat, (Nat.add (BIT0 y0) 0) = (BIT0 y0)) /\ ((forall y0 : nat, (Nat.add (BIT1 y0) 0) = (BIT1 y0)) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT0 y1)) = (BIT0 (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT1 y1)) = (BIT1 (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT0 y1)) = (BIT1 (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT1 y1)) = (BIT0 (S (Nat.add y0 y1)))))))))).
Definition term287 (x0 : nat) (x1 : nat) := Nat.mul x0 (Nat.add x1 x1).
Definition term178 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> forall y0 : nat, forall y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) -> Peano.le y0 y1.
Definition term120 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, forall y4 : nat, (Peano.le (Nat.add (dist (@pair nat nat y0 y2)) (dist (@pair nat nat y1 y3))) y4) -> Peano.le (dist (@pair nat nat (Nat.add y0 y1) (Nat.add y2 y3))) y4) -> forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, forall y4 : nat, (Peano.le (Nat.add (dist (@pair nat nat y0 y2)) (dist (@pair nat nat y1 y3))) y4) -> Peano.le (dist (@pair nat nat (Nat.add y0 y1) (Nat.add y2 y3))) y4.
Definition term100 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.le y0 y1) -> (Peano.le y1 y2) -> Peano.le y0 y2) -> forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> forall y2 : nat, (Peano.le y1 y2) -> Peano.le y0 y2.
Definition term12 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.add y0 y1) (Nat.add y2 y3)) -> forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.add y0 y1) (Nat.add y2 y3).
Definition term116 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := (Peano.le (Nat.add (dist (@pair nat nat x0 x2)) (dist (@pair nat nat x1 x3))) x4) -> Peano.le (dist (@pair nat nat (Nat.add x0 x1) (Nat.add x2 x3))) x4.
Definition term282 (x0 : nat) := Nat.add (Nat.mul (NUMERAL (BIT1 0)) x0) (Nat.mul (NUMERAL (BIT1 0)) x0).
Definition term33 := ((Nat.add 0 0) = 0) /\ ((forall y0 : nat, (Nat.add 0 (BIT0 y0)) = (BIT0 y0)) /\ ((forall y0 : nat, (Nat.add 0 (BIT1 y0)) = (BIT1 y0)) /\ ((forall y0 : nat, (Nat.add (BIT0 y0) 0) = (BIT0 y0)) /\ ((forall y0 : nat, (Nat.add (BIT1 y0) 0) = (BIT1 y0)) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT0 y1)) = (BIT0 (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT1 y1)) = (BIT1 (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT0 y1)) = (BIT1 (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT1 y1)) = (BIT0 (S (Nat.add y0 y1))))))))))).
Definition term72 := Nat.add (NUMERAL (BIT1 0)) (Nat.add (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term228 (x0 : nat) := Nat.mul (NUMERAL (BIT1 (BIT1 0))) x0.
Definition term129 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = (NUMERAL 0)) \/ (Peano.le x1 x2).
Definition term127 (x0 : nat) (x1 : nat) (x2 : nat) := dist (@pair nat nat (Nat.mul x1 x0) (Nat.mul x1 x2)).
Definition term233 (x0 : nat) (x1 : nadd) (x2 : nat) (x3 : nat) := (Peano.le (dist (@pair nat nat (dest_nadd x1 (Nat.add x0 x2)) (Nat.add (dest_nadd x1 x0) (dest_nadd x1 x2)))) (Nat.mul (NUMERAL (BIT1 (BIT1 0))) x3)) /\ True.
Definition term289 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x0 x1).
Definition term196 (x0 : nadd) (x1 : nat) (x2 : nat) := dist (@pair nat nat (Nat.add (dest_nadd x0 x1) (dest_nadd x0 x2)) (dest_nadd x0 (Nat.add x1 x2))).
Definition term130 (x0 : nat) (x1 : nat) := fun y0 : nat => (Peano.le (Nat.mul x0 x1) (Nat.mul x0 y0)) = ((x0 = (NUMERAL 0)) \/ (Peano.le x1 y0)).
Definition term40 := (forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT0 y1)) = (BIT1 (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT1 y1)) = (BIT0 (S (Nat.add y0 y1)))).
Definition term45 (x0 : nat) (x1 : nat) := Nat.add (BIT1 x0) (BIT1 x1).
Definition term150 (x0 : Prop) (x1 : Prop) := @eq Prop (((~ x0) -> x1) = (x0 \/ x1)).
Definition term329 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x1 x0) (Nat.add (Nat.mul x1 x2) (Nat.add (Nat.mul x1 x2) (Nat.add (Nat.mul x1 x0) (Nat.mul x1 x2)))).
Definition term326 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x1 x0) (Nat.add (Nat.mul x1 x2) (Nat.add (Nat.mul x1 x0) (Nat.add (Nat.mul x1 x2) (Nat.mul x1 x2)))).
Definition term324 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x1 x0) (Nat.add (Nat.mul x1 x2) (Nat.add (Nat.mul x1 x0) (Nat.add (Nat.mul x1 x0) (Nat.add (Nat.mul x1 x2) (Nat.mul x1 x2))))).
Definition term318 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x1 x0) (Nat.add (Nat.mul x1 x2) (Nat.add (Nat.mul x1 x0) (Nat.add (Nat.mul x1 x0) (Nat.mul x1 x2)))).
Definition term206 (x0 : nat) (x1 : nat) := (fun y0 : nat => Peano.le y0 (Nat.add x0 y0)) x1.
Definition term335 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Nat.add x0 x1) = (Nat.add x0 y0)) = (x1 = y0).
Definition term351 (x0 : nat) (x1 : nat) (x2 : nadd) := forall y0 : nat, Peano.le (dist (@pair nat nat (dest_nadd x2 (Nat.add x0 y0)) (Nat.add (dest_nadd x2 x0) (dest_nadd x2 y0)))) (Nat.add (Nat.mul (NUMERAL (BIT1 (BIT1 0))) x1) (dest_nadd x2 (NUMERAL 0))).
Definition term237 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (Nat.mul (Nat.add x1 x2) (dist (@pair nat nat (dest_nadd x0 (Nat.add x1 x2)) (Nat.add (dest_nadd x0 x1) (dest_nadd x0 x2))))) (Nat.mul (Nat.add x1 x2) (Nat.mul (NUMERAL (BIT1 (BIT1 0))) x3)).
Definition term262 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x0 (Nat.add x1 (Nat.add x1 x2))) (Nat.mul x0 (Nat.add x2 (Nat.add x1 x2))).
Definition term172 (x0 : nat) (x1 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> Peano.le x0 x1.
Definition term295 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (Nat.add x1 (Nat.add x1 x2)).
Definition term149 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term184 (x0 : nat) (x1 : nat) := dist (@pair nat nat x0 x1).
Definition term10 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (Nat.add x0 x1) (Nat.add x2 x3).
Definition term87 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (dist (@pair nat nat (Nat.add x0 x2) (Nat.add x1 x3))) (Nat.add (dist (@pair nat nat x0 x1)) (dist (@pair nat nat x2 x3))).
Definition term176 (x0 : nat) := forall y0 : nat, (exists y1 : nat, (Peano.le x0 y1) /\ (Peano.le y1 y0)) -> Peano.le x0 y0.
Definition term52 (x0 : nat) (x1 : nat) := BIT1 (Nat.add x0 x1).
Definition term306 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.add x0 x1) x2.
Definition term239 (x0 : nat) (x1 : nadd) (x2 : nat) := dist (@pair nat nat (Nat.mul (Nat.add x0 x2) (dest_nadd x1 (Nat.add x0 x2))) (Nat.mul (Nat.add x0 x2) (Nat.add (dest_nadd x1 x0) (dest_nadd x1 x2)))).
Definition term263 (x0 : nat) (x1 : nadd) (x2 : nat) := fun y0 : nat => Peano.le (Nat.add (dist (@pair nat nat (Nat.mul x0 (dest_nadd x1 (Nat.add x0 x2))) (Nat.mul (Nat.add x0 x2) (dest_nadd x1 x0)))) (dist (@pair nat nat (Nat.mul x2 (dest_nadd x1 (Nat.add x0 x2))) (Nat.mul (Nat.add x0 x2) (dest_nadd x1 x2))))) y0.
Definition term63 := ((S 0) = (BIT1 0)) /\ ((forall y0 : nat, (S (BIT0 y0)) = (BIT1 y0)) /\ (forall y0 : nat, (S (BIT1 y0)) = (BIT0 (S y0)))).
Definition term98 (x0 : nat) := forall y0 : nat, (Peano.le x0 y0) -> forall y1 : nat, (Peano.le y0 y1) -> Peano.le x0 y1.
Definition term281 (x0 : nat) := Nat.mul (Nat.add (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))) x0.
Definition term298 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x0 (Nat.add x1 (Nat.add x1 x2))).
Definition term322 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x1 x0) (Nat.add (Nat.mul x1 x0) (Nat.add (Nat.mul x1 x0) (Nat.add (Nat.mul x1 x2) (Nat.mul x1 x2)))).
Definition term311 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x1 x0) (Nat.add (Nat.mul x1 x0) (Nat.add (Nat.mul x1 x0) (Nat.add (Nat.mul x1 x2) (Nat.add (Nat.mul x1 x2) (Nat.mul x1 x2))))).
Definition term310 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x1 x0) (Nat.add (Nat.mul x1 x0) (Nat.add (Nat.mul x1 x2) (Nat.add (Nat.mul x1 x2) (Nat.mul x1 x2)))).
Definition term75 := Nat.add (BIT1 0) (BIT0 (BIT1 0)).
Definition term161 (x0 : nat) := forall y0 : nat, Peano.le x0 (Nat.add x0 y0).
Definition term208 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (dist (@pair nat nat (Nat.add y0 y1) y0)) = y1) x0.
Definition term152 (x0 : Prop) := (~ False) -> x0.
Definition term169 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Peano.le x1 x0) /\ (Peano.le x0 y0)) -> Peano.le x1 y0) x2.
Definition term285 (x0 : nat) (x1 : nat) := Nat.mul x0 (Nat.add x1 (Nat.add x1 x1)).
Definition term301 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x0 x2) (Nat.mul x0 (Nat.add x1 x2)).
Definition term199 (x0 : nat) (x1 : nadd) (x2 : nat) := Peano.le (dist (@pair nat nat (dest_nadd x1 (Nat.add x0 x2)) (Nat.add (dest_nadd x1 x0) (dest_nadd x1 x2)))).
Definition term43 (x0 : nat) := forall y0 : nat, (Nat.add (BIT1 x0) (BIT1 y0)) = (BIT0 (S (Nat.add x0 y0))).
Definition term240 (x0 : nat) (x1 : nadd) (x2 : nat) := Nat.mul (Nat.add x0 x2) (Nat.add (dest_nadd x1 x0) (dest_nadd x1 x2)).
Definition term256 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (dist (@pair nat nat (Nat.add (Nat.mul x1 (dest_nadd x0 (Nat.add x1 x2))) (Nat.mul x2 (dest_nadd x0 (Nat.add x1 x2)))) (Nat.add (Nat.mul (Nat.add x1 x2) (dest_nadd x0 x1)) (Nat.mul (Nat.add x1 x2) (dest_nadd x0 x2))))) (Nat.mul (Nat.add x1 x2) (Nat.mul (NUMERAL (BIT1 (BIT1 0))) x3)).
Definition term249 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (dist (@pair nat nat (Nat.mul (Nat.add x1 x2) (dest_nadd x0 (Nat.add x1 x2))) (Nat.add (Nat.mul (Nat.add x1 x2) (dest_nadd x0 x1)) (Nat.mul (Nat.add x1 x2) (dest_nadd x0 x2))))) (Nat.mul (Nat.add x1 x2) (Nat.mul (NUMERAL (BIT1 (BIT1 0))) x3)).
Definition term225 (x0 : nadd) := dist (@pair nat nat (Nat.add (dest_nadd x0 (NUMERAL 0)) (dest_nadd x0 (NUMERAL 0))) (dest_nadd x0 (NUMERAL 0))).
Definition term126 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (dist (@pair nat nat x1 x2)).
Definition term257 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le (Nat.add (dist (@pair nat nat (Nat.mul x1 (dest_nadd x0 (Nat.add x1 x2))) (Nat.mul (Nat.add x1 x2) (dest_nadd x0 x1)))) (dist (@pair nat nat (Nat.mul x2 (dest_nadd x0 (Nat.add x1 x2))) (Nat.mul (Nat.add x1 x2) (dest_nadd x0 x2))))) (Nat.mul (Nat.add x1 x2) (Nat.mul (NUMERAL (BIT1 (BIT1 0))) x3))) -> Peano.le (dist (@pair nat nat (Nat.add (Nat.mul x1 (dest_nadd x0 (Nat.add x1 x2))) (Nat.mul x2 (dest_nadd x0 (Nat.add x1 x2)))) (Nat.add (Nat.mul (Nat.add x1 x2) (dest_nadd x0 x1)) (Nat.mul (Nat.add x1 x2) (dest_nadd x0 x2))))) (Nat.mul (Nat.add x1 x2) (Nat.mul (NUMERAL (BIT1 (BIT1 0))) x3)).
Definition term76 := BIT1 (Nat.add 0 (BIT1 0)).
Definition term280 (x0 : nat) := Nat.add (Nat.mul (NUMERAL (BIT1 0)) x0).
Definition term189 (x0 : nat) (x1 : nat) := (fun y0 : Prop => y0 \/ (~ y0)) ((Nat.add x0 x1) = (NUMERAL 0)).
Definition term290 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x0 x1) (Nat.add (Nat.mul x0 x1) (Nat.mul x0 x1)).
Definition term232 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nadd) := (Peano.le (dist (@pair nat nat (dest_nadd x3 (Nat.add x0 x1)) (Nat.add (dest_nadd x3 x0) (dest_nadd x3 x1)))) (Nat.mul (NUMERAL (BIT1 (BIT1 0))) x2)) /\ (Peano.le (Nat.mul (NUMERAL (BIT1 (BIT1 0))) x2) (Nat.add (Nat.mul (NUMERAL (BIT1 (BIT1 0))) x2) (dest_nadd x3 (NUMERAL 0)))).
Definition term320 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x1 x0) (Nat.add (Nat.mul x1 x2) (Nat.add (Nat.mul x1 x0) (Nat.mul x1 x2))).
Definition term313 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x1 x0) (Nat.add (Nat.mul x1 x2) (Nat.add (Nat.mul x1 x2) (Nat.mul x1 x2))).
Definition term51 (x0 : nat) (x1 : nat) := Nat.add (BIT1 x0) (BIT0 x1).
Definition term117 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := Peano.le (Nat.add (dist (@pair nat nat x0 x1)) (dist (@pair nat nat x2 x3))) x4.
Definition term46 (x0 : nat) (x1 : nat) := BIT0 (S (Nat.add x0 x1)).
Definition term73 := Nat.add (NUMERAL (BIT1 0)) (NUMERAL (BIT0 (BIT1 0))).
Definition term186 (x0 : nat) := forall y0 : nat, ((Nat.add x0 y0) = (NUMERAL 0)) = ((x0 = (NUMERAL 0)) /\ (y0 = (NUMERAL 0))).
Definition term334 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.add x0 y0) = (Nat.add x0 y1)) = (y0 = y1)) x1.
Definition term167 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 y1)) -> Peano.le x0 y1) x1.
Definition term158 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((x0 = (NUMERAL 0)) \/ (Peano.le y0 y1)) = (Peano.le (Nat.mul x0 y0) (Nat.mul x0 y1))) x1.
Definition term123 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul x0 (dist (@pair nat nat y0 y1))) = (dist (@pair nat nat (Nat.mul x0 y0) (Nat.mul x0 y1)))) x1.
Definition term91 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le x0 y0) -> (Peano.le y0 y1) -> Peano.le x0 y1) x1.
Definition term27 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul (Nat.add x0 y0) y1) = (Nat.add (Nat.mul x0 y1) (Nat.mul y0 y1))) x1.
Definition term20 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul x0 (Nat.add y0 y1)) = (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y1))) x1.
Definition term321 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x1 x0) (Nat.add (Nat.mul x1 x0) (Nat.add (Nat.mul x1 x2) (Nat.mul x1 x2))).
Definition term316 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x1 x0) (Nat.add (Nat.mul x1 x0) (Nat.add (Nat.mul x1 x0) (Nat.mul x1 x2))).
Definition term64 := Nat.add (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term236 (x0 : nat) (x1 : nadd) (x2 : nat) (x3 : nat) := ((Nat.add x0 x2) = (NUMERAL 0)) \/ (Peano.le (dist (@pair nat nat (dest_nadd x1 (Nat.add x0 x2)) (Nat.add (dest_nadd x1 x0) (dest_nadd x1 x2)))) (Nat.mul (NUMERAL (BIT1 (BIT1 0))) x3)).
Definition term54 (x0 : nat) := (fun y0 : nat => (Nat.add 0 (BIT1 y0)) = (BIT1 y0)) x0.
Definition term188 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0)).
Definition term38 := (forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT0 y1)) = (BIT0 (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT1 y1)) = (BIT1 (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT0 y1)) = (BIT1 (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT1 y1)) = (BIT0 (S (Nat.add y0 y1)))))).
Definition term224 (x0 : nadd) := @pair nat nat (Nat.add (dest_nadd x0 (NUMERAL 0)) (dest_nadd x0 (NUMERAL 0))) (dest_nadd x0 (NUMERAL 0)).
Definition term260 (x0 : nat) (x1 : nadd) (x2 : nat) := Nat.mul (Nat.add x2 x0) (dest_nadd x1 x2).
Definition term215 (x0 : nadd) := dest_nadd x0 (NUMERAL 0).
Definition term255 (x0 : nat) (x1 : nadd) (x2 : nat) := Peano.le (dist (@pair nat nat (Nat.add (Nat.mul x0 (dest_nadd x1 (Nat.add x0 x2))) (Nat.mul x2 (dest_nadd x1 (Nat.add x0 x2)))) (Nat.add (Nat.mul (Nat.add x0 x2) (dest_nadd x1 x0)) (Nat.mul (Nat.add x0 x2) (dest_nadd x1 x2))))).
Definition term247 (x0 : nat) (x1 : nadd) (x2 : nat) := Peano.le (dist (@pair nat nat (Nat.mul (Nat.add x0 x2) (dest_nadd x1 (Nat.add x0 x2))) (Nat.add (Nat.mul (Nat.add x0 x2) (dest_nadd x1 x0)) (Nat.mul (Nat.add x0 x2) (dest_nadd x1 x2))))).
Definition term299 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.add (Nat.mul x1 x0) (Nat.add (Nat.mul x1 x0) (Nat.mul x1 x2))).
Definition term162 (x0 : nat) (x1 : nat) := (fun y0 : nat => Peano.le x0 (Nat.add x0 y0)) x1.
Definition term58 (x0 : nat) := forall y0 : nat, (Nat.add (NUMERAL x0) (NUMERAL y0)) = (NUMERAL (Nat.add x0 y0)).
Definition term125 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.mul x1 (dist (@pair nat nat x0 y0))) = (dist (@pair nat nat (Nat.mul x1 x0) (Nat.mul x1 y0)))) x2.
Definition term39 := (forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT1 y1)) = (BIT1 (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT0 y1)) = (BIT1 (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT1 y1)) = (BIT0 (S (Nat.add y0 y1))))).
Definition term266 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (Nat.add (dist (@pair nat nat (Nat.mul x2 (dest_nadd x0 (Nat.add x2 x3))) (Nat.mul (Nat.add x2 x3) (dest_nadd x0 x2)))) (dist (@pair nat nat (Nat.mul x3 (dest_nadd x0 (Nat.add x2 x3))) (Nat.mul (Nat.add x2 x3) (dest_nadd x0 x3))))) (Nat.add (Nat.mul x1 (Nat.add x2 (Nat.add x2 x3))) (Nat.mul x1 (Nat.add x3 (Nat.add x2 x3)))).
Definition term222 := Nat.add (NUMERAL 0) (NUMERAL 0).
Definition term248 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.add x0 x1) (Nat.mul (NUMERAL (BIT1 (BIT1 0))) x2).
Definition term223 (x0 : nadd) (x1 : nat) (x2 : nat) := @pair nat nat (Nat.add (dest_nadd x0 x1) (dest_nadd x0 x2)) (dest_nadd x0 (Nat.add x1 x2)).
Definition term92 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le x1 x0) -> (Peano.le x0 y0) -> Peano.le x1 y0.
Definition term170 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.le x1 x0) /\ (Peano.le x0 x2)) -> Peano.le x1 x2.
Definition term229 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nadd) := (exists y0 : nat, (Peano.le (dist (@pair nat nat (dest_nadd x3 (Nat.add x0 x1)) (Nat.add (dest_nadd x3 x0) (dest_nadd x3 x1)))) y0) /\ (Peano.le y0 (Nat.add (Nat.mul (NUMERAL (BIT1 (BIT1 0))) x2) (dest_nadd x3 (NUMERAL 0))))) -> Peano.le (dist (@pair nat nat (dest_nadd x3 (Nat.add x0 x1)) (Nat.add (dest_nadd x3 x0) (dest_nadd x3 x1)))) (Nat.add (Nat.mul (NUMERAL (BIT1 (BIT1 0))) x2) (dest_nadd x3 (NUMERAL 0))).
Definition term24 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x1 x0) (Nat.mul x1 x2).
Definition term195 (x0 : nat) (x1 : nadd) (x2 : nat) := dist (@pair nat nat (dest_nadd x1 (Nat.add x0 x2)) (Nat.add (dest_nadd x1 x0) (dest_nadd x1 x2))).
Definition term55 (x0 : nat) := Nat.add 0 (BIT1 x0).
Definition term118 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := Peano.le (dist (@pair nat nat (Nat.add x0 x1) (Nat.add x2 x3))) x4.
Definition term190 (x0 : nat) (x1 : nat) := ((Nat.add x0 x1) = (NUMERAL 0)) \/ (~ ((Nat.add x0 x1) = (NUMERAL 0))).
Definition term214 (x0 : nat) := Nat.add (NUMERAL 0) x0.
Definition term200 (x0 : nadd) (x1 : nat) (x2 : nat) := Peano.le (dist (@pair nat nat (Nat.add (dest_nadd x0 x1) (dest_nadd x0 x2)) (dest_nadd x0 (Nat.add x1 x2)))).
Definition term330 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x1 x2) (Nat.add (Nat.mul x1 x2) (Nat.add (Nat.mul x1 x0) (Nat.mul x1 x2))).
Definition term97 (x0 : nat) (x1 : nat) := (Peano.le x1 x0) -> forall y0 : nat, (Peano.le x0 y0) -> Peano.le x1 y0.
Definition term342 (x0 : nadd) (x1 : nat) (x2 : nat) := forall y0 : nat, Peano.le (dist (@pair nat nat (Nat.mul x2 (dest_nadd x0 y0)) (Nat.mul y0 (dest_nadd x0 x2)))) (Nat.mul x1 (Nat.add x2 y0)).
Definition term114 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (Nat.add (dist (@pair nat nat x0 x2)) (dist (@pair nat nat x1 y0))) y1) -> Peano.le (dist (@pair nat nat (Nat.add x0 x1) (Nat.add x2 y0))) y1) x3.
Definition term74 := NUMERAL (Nat.add (BIT1 0) (BIT0 (BIT1 0))).
Definition term352 (x0 : nat) (x1 : nadd) := forall y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (dest_nadd x1 (Nat.add y0 y1)) (Nat.add (dest_nadd x1 y0) (dest_nadd x1 y1)))) (Nat.add (Nat.mul (NUMERAL (BIT1 (BIT1 0))) x0) (dest_nadd x1 (NUMERAL 0))).
Definition term333 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Nat.add x0 y0) = (Nat.add x0 y1)) = (y0 = y1).
Definition term194 (x0 : nadd) (x1 : nat) := forall y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (Nat.mul y0 (dest_nadd x0 y1)) (Nat.mul y1 (dest_nadd x0 y0)))) (Nat.mul x1 (Nat.add y0 y1)).
Definition term177 := forall y0 : nat, forall y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) -> Peano.le y0 y1.
Definition term166 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 y1)) -> Peano.le x0 y1.
Definition term164 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2.
Definition term141 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((y0 = (NUMERAL 0)) \/ (Peano.le y1 y2)) = (Peano.le (Nat.mul y0 y1) (Nat.mul y0 y2)).
Definition term140 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.le (Nat.mul y0 y1) (Nat.mul y0 y2)) = ((y0 = (NUMERAL 0)) \/ (Peano.le y1 y2)).
Definition term137 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((x0 = (NUMERAL 0)) \/ (Peano.le y0 y1)) = (Peano.le (Nat.mul x0 y0) (Nat.mul x0 y1)).
Definition term136 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le (Nat.mul x0 y0) (Nat.mul x0 y1)) = ((x0 = (NUMERAL 0)) \/ (Peano.le y0 y1)).
Definition term122 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.mul x0 (dist (@pair nat nat y0 y1))) = (dist (@pair nat nat (Nat.mul x0 y0) (Nat.mul x0 y1))).
Definition term110 := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, forall y4 : nat, (Peano.le (Nat.add (dist (@pair nat nat y0 y2)) (dist (@pair nat nat y1 y3))) y4) -> Peano.le (dist (@pair nat nat (Nat.add y0 y1) (Nat.add y2 y3))) y4.
Definition term109 (x0 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, (Peano.le (Nat.add (dist (@pair nat nat x0 y1)) (dist (@pair nat nat y0 y2))) y3) -> Peano.le (dist (@pair nat nat (Nat.add x0 y0) (Nat.add y1 y2))) y3.
Definition term108 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.le (Nat.add (dist (@pair nat nat x0 y0)) (dist (@pair nat nat x1 y1))) y2) -> Peano.le (dist (@pair nat nat (Nat.add x0 x1) (Nat.add y0 y1))) y2.
Definition term107 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add (dist (@pair nat nat x0 x2)) (dist (@pair nat nat x1 y0))) y1) -> Peano.le (dist (@pair nat nat (Nat.add x0 x1) (Nat.add x2 y0))) y1.
Definition term99 := forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> forall y2 : nat, (Peano.le y1 y2) -> Peano.le y0 y2.
Definition term90 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le x0 y0) -> (Peano.le y0 y1) -> Peano.le x0 y1.
Definition term88 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.le y0 y1) -> (Peano.le y1 y2) -> Peano.le y0 y2.
Definition term83 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (Nat.add x0 x1) (Nat.add y0 y1))) (Nat.add (dist (@pair nat nat x0 y0)) (dist (@pair nat nat x1 y1))).
Definition term81 (x0 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (Nat.add x0 y0) (Nat.add y1 y2))) (Nat.add (dist (@pair nat nat x0 y1)) (dist (@pair nat nat y0 y2))).
Definition term56 := forall y0 : nat, forall y1 : nat, (Nat.add (NUMERAL y0) (NUMERAL y1)) = (NUMERAL (Nat.add y0 y1)).
Definition term47 := forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT0 y1)) = (BIT1 (Nat.add y0 y1)).
Definition term41 := forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT1 y1)) = (BIT0 (S (Nat.add y0 y1))).
Definition term26 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.mul (Nat.add x0 y0) y1) = (Nat.add (Nat.mul x0 y1) (Nat.mul y0 y1)).
Definition term19 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.mul x0 (Nat.add y0 y1)) = (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y1)).
Definition term4 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le x1 y1)) -> Peano.le (Nat.add x0 x1) (Nat.add y0 y1).
Definition term2 (x0 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le x0 y1) /\ (Peano.le y0 y2)) -> Peano.le (Nat.add x0 y0) (Nat.add y1 y2).
Definition term0 := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.add y0 y1) (Nat.add y2 y3).
Definition term119 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, forall y4 : nat, (Peano.le (Nat.add (dist (@pair nat nat y0 y2)) (dist (@pair nat nat y1 y3))) y4) -> Peano.le (dist (@pair nat nat (Nat.add y0 y1) (Nat.add y2 y3))) y4) -> Peano.le (dist (@pair nat nat (Nat.add x0 x1) (Nat.add x2 x3))) x4.
Definition term341 (x0 : nadd) (x1 : nat) (x2 : nat) := (fun y0 : nat => forall y1 : nat, Peano.le (dist (@pair nat nat (Nat.mul y0 (dest_nadd x0 y1)) (Nat.mul y1 (dest_nadd x0 y0)))) (Nat.mul x1 (Nat.add y0 y1))) x2.
Definition term84 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => forall y1 : nat, Peano.le (dist (@pair nat nat (Nat.add x0 x1) (Nat.add y0 y1))) (Nat.add (dist (@pair nat nat x0 y0)) (dist (@pair nat nat x1 y1)))) x2.
Definition term5 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le x1 y1)) -> Peano.le (Nat.add x0 x1) (Nat.add y0 y1)) x2.
Definition term112 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, (Peano.le (Nat.add (dist (@pair nat nat x0 y1)) (dist (@pair nat nat y0 y2))) y3) -> Peano.le (dist (@pair nat nat (Nat.add x0 y0) (Nat.add y1 y2))) y3) x1.
Definition term82 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (Nat.add x0 y0) (Nat.add y1 y2))) (Nat.add (dist (@pair nat nat x0 y1)) (dist (@pair nat nat y0 y2)))) x1.
Definition term3 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.le x0 y1) /\ (Peano.le y0 y2)) -> Peano.le (Nat.add x0 y0) (Nat.add y1 y2)) x1.
Definition term198 (x0 : nadd) (x1 : nat) (x2 : nat) := dest_nadd x0 (Nat.add x1 x2).
Definition term269 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop (Peano.le (Nat.add (dist (@pair nat nat (Nat.mul x1 (dest_nadd x0 (Nat.add x1 x2))) (Nat.mul (Nat.add x1 x2) (dest_nadd x0 x1)))) (dist (@pair nat nat (Nat.mul x2 (dest_nadd x0 (Nat.add x1 x2))) (Nat.mul (Nat.add x1 x2) (dest_nadd x0 x2))))) (Nat.mul (Nat.add x1 x2) (Nat.mul (NUMERAL (BIT1 (BIT1 0))) x3))).
Definition term273 (x0 : nat) (x1 : nat) := Nat.mul (Nat.add x0 x1).
Definition term65 := NUMERAL (Nat.add (BIT1 0) (BIT1 0)).
Definition term343 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => Peano.le (dist (@pair nat nat (Nat.mul x2 (dest_nadd x0 y0)) (Nat.mul y0 (dest_nadd x0 x2)))) (Nat.mul x1 (Nat.add x2 y0))) x3.
Definition term220 (x0 : nadd) := @pair nat nat (Nat.add (dest_nadd x0 (NUMERAL 0)) (dest_nadd x0 (NUMERAL 0))).
Definition term29 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.mul (Nat.add x0 x1) y0) = (Nat.add (Nat.mul x0 y0) (Nat.mul x1 y0))) x2.
Definition term230 (x0 : nat) (x1 : nadd) := Peano.le (Nat.mul (NUMERAL (BIT1 (BIT1 0))) x0) (Nat.add (Nat.mul (NUMERAL (BIT1 (BIT1 0))) x0) (dest_nadd x1 (NUMERAL 0))).
Definition term93 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.le x1 x0) -> (Peano.le x0 y0) -> Peano.le x1 y0) x2.
Definition term312 (x0 : nat) (x1 : nat) (x2 : nat) := @eq nat (Nat.add (Nat.mul x1 x0) (Nat.add (Nat.mul x1 x0) (Nat.add (Nat.mul x1 x0) (Nat.add (Nat.mul x1 x2) (Nat.add (Nat.mul x1 x2) (Nat.mul x1 x2)))))).
Definition term278 (x0 : nat) := Nat.add (Nat.mul (NUMERAL (BIT1 0)) x0) (Nat.mul (Nat.add (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))) x0).
Definition term212 := forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0.
Definition term15 := forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0.
Definition term346 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := and (Peano.le (dist (@pair nat nat (Nat.mul x2 (dest_nadd x0 (Nat.add x2 x3))) (Nat.mul (Nat.add x2 x3) (dest_nadd x0 x2)))) (Nat.mul x1 (Nat.add x2 (Nat.add x2 x3)))).
Definition term213 (x0 : nat) := (fun y0 : nat => (Nat.add (NUMERAL 0) y0) = y0) x0.
Definition term16 (x0 : nat) := (fun y0 : nat => (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) x0.
Definition term217 (x0 : nadd) := Nat.add (dest_nadd x0 (NUMERAL 0)).
Definition term30 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.add x0 x1) x2.
Definition term68 := S (Nat.add 0 0).
Definition term31 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x0 x2) (Nat.mul x1 x2).
Definition term133 (x0 : nat) (x1 : nat) := forall y0 : nat, ((x1 = (NUMERAL 0)) \/ (Peano.le x0 y0)) = (Peano.le (Nat.mul x1 x0) (Nat.mul x1 y0)).
Definition term132 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le (Nat.mul x0 x1) (Nat.mul x0 y0)) = ((x0 = (NUMERAL 0)) \/ (Peano.le x1 y0)).
Definition term21 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.mul x1 (Nat.add x0 y0)) = (Nat.add (Nat.mul x1 x0) (Nat.mul x1 y0)).
Definition term104 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.add (dist (@pair nat nat x0 x1)) (dist (@pair nat nat x2 x3)).
Definition term124 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.mul x1 (dist (@pair nat nat x0 y0))) = (dist (@pair nat nat (Nat.mul x1 x0) (Nat.mul x1 y0))).
Definition term300 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (Nat.add x2 (Nat.add x1 x2)).
Definition term148 (x0 : Prop) (x1 : Prop) := @eq Prop ((fun y0 : Prop => ((~ y0) -> x0) = (y0 \/ x0)) x1).
Definition term113 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le (Nat.add (dist (@pair nat nat x0 y0)) (dist (@pair nat nat x1 y1))) y2) -> Peano.le (dist (@pair nat nat (Nat.add x0 x1) (Nat.add y0 y1))) y2) x2.
Definition term159 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((x1 = (NUMERAL 0)) \/ (Peano.le x0 y0)) = (Peano.le (Nat.mul x1 x0) (Nat.mul x1 y0))) x2.
Definition term234 (x0 : nat) (x1 : nadd) (x2 : nat) (x3 : nat) := Peano.le (dist (@pair nat nat (dest_nadd x1 (Nat.add x0 x2)) (Nat.add (dest_nadd x1 x0) (dest_nadd x1 x2)))) (Nat.mul (NUMERAL (BIT1 (BIT1 0))) x3).
Definition term128 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul x1 x0) (Nat.mul x1 x2).
Definition term115 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := (fun y0 : nat => (Peano.le (Nat.add (dist (@pair nat nat x0 x2)) (dist (@pair nat nat x1 x3))) y0) -> Peano.le (dist (@pair nat nat (Nat.add x0 x1) (Nat.add x2 x3))) y0) x4.
Definition term253 (x0 : nat) (x1 : nadd) (x2 : nat) := @pair nat nat (Nat.add (Nat.mul x0 (dest_nadd x1 (Nat.add x0 x2))) (Nat.mul x2 (dest_nadd x1 (Nat.add x0 x2)))) (Nat.add (Nat.mul (Nat.add x0 x2) (dest_nadd x1 x0)) (Nat.mul (Nat.add x0 x2) (dest_nadd x1 x2))).
Definition term197 (x0 : nat) (x1 : nadd) (x2 : nat) := Nat.add (dest_nadd x1 x0) (dest_nadd x1 x2).
Definition term277 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x0 (Nat.mul (Nat.add (NUMERAL (BIT1 0)) (Nat.add (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)))) x2)) (Nat.mul x1 (Nat.mul (Nat.add (NUMERAL (BIT1 0)) (Nat.add (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)))) x2)).
Definition term211 (x0 : nat) (x1 : nat) := dist (@pair nat nat (Nat.add x1 x0) x1).
Definition term309 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.add (Nat.mul x1 x0) (Nat.mul x1 x0)) (Nat.add (Nat.mul x1 x2) (Nat.add (Nat.mul x1 x2) (Nat.mul x1 x2))).
Definition term143 (x0 : Prop) := (x0 = True) \/ (x0 = False).
Definition term155 := imp (~ False).
Definition term267 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop ((fun y0 : nat => Peano.le (Nat.add (dist (@pair nat nat (Nat.mul x1 (dest_nadd x0 (Nat.add x1 x2))) (Nat.mul (Nat.add x1 x2) (dest_nadd x0 x1)))) (dist (@pair nat nat (Nat.mul x2 (dest_nadd x0 (Nat.add x1 x2))) (Nat.mul (Nat.add x1 x2) (dest_nadd x0 x2))))) y0) (Nat.mul (Nat.add x1 x2) (Nat.mul (NUMERAL (BIT1 (BIT1 0))) x3))).
Definition term71 := Nat.add (NUMERAL (BIT1 0)).
Definition term349 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nadd) := exists y0 : nat, (Peano.le (dist (@pair nat nat (dest_nadd x3 (Nat.add x0 x1)) (Nat.add (dest_nadd x3 x0) (dest_nadd x3 x1)))) y0) /\ (Peano.le y0 (Nat.add (Nat.mul (NUMERAL (BIT1 (BIT1 0))) x2) (dest_nadd x3 (NUMERAL 0)))).
Definition term70 := NUMERAL (BIT0 (BIT1 0)).
Definition term218 (x0 : nadd) := Nat.add (dest_nadd x0 (NUMERAL 0)) (dest_nadd x0 (NUMERAL 0)).
Definition term168 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Peano.le x1 x0) /\ (Peano.le x0 y0)) -> Peano.le x1 y0.
Definition term350 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nadd) := fun y0 : nat => (Peano.le (dist (@pair nat nat (dest_nadd x3 (Nat.add x0 x1)) (Nat.add (dest_nadd x3 x0) (dest_nadd x3 x1)))) y0) /\ (Peano.le y0 (Nat.add (Nat.mul (NUMERAL (BIT1 (BIT1 0))) x2) (dest_nadd x3 (NUMERAL 0)))).
Definition term44 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add (BIT1 x0) (BIT1 y0)) = (BIT0 (S (Nat.add x0 y0)))) x1.
Definition term356 := forall y0 : nadd, exists y1 : nat, forall y2 : nat, forall y3 : nat, Peano.le (dist (@pair nat nat (dest_nadd y0 (Nat.add y2 y3)) (Nat.add (dest_nadd y0 y2) (dest_nadd y0 y3)))) y1.
Definition term307 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add x0 (Nat.add x1 x2).
Definition term209 (x0 : nat) := forall y0 : nat, (dist (@pair nat nat (Nat.add x0 y0) x0)) = y0.
Definition term338 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := ((Peano.le (dist (@pair nat nat (Nat.mul x2 (dest_nadd x0 (Nat.add x2 x3))) (Nat.mul (Nat.add x2 x3) (dest_nadd x0 x2)))) (Nat.mul x1 (Nat.add x2 (Nat.add x2 x3)))) /\ (Peano.le (dist (@pair nat nat (Nat.mul x3 (dest_nadd x0 (Nat.add x2 x3))) (Nat.mul (Nat.add x2 x3) (dest_nadd x0 x3)))) (Nat.mul x1 (Nat.add x3 (Nat.add x2 x3))))) -> Peano.le (Nat.add (dist (@pair nat nat (Nat.mul x2 (dest_nadd x0 (Nat.add x2 x3))) (Nat.mul (Nat.add x2 x3) (dest_nadd x0 x2)))) (dist (@pair nat nat (Nat.mul x3 (dest_nadd x0 (Nat.add x2 x3))) (Nat.mul (Nat.add x2 x3) (dest_nadd x0 x3))))) (Nat.add (Nat.mul x1 (Nat.add x2 (Nat.add x2 x3))) (Nat.mul x1 (Nat.add x3 (Nat.add x2 x3)))).
Definition term105 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := dist (@pair nat nat (Nat.add x0 x1) (Nat.add x2 x3)).
Definition term221 := Nat.add (NUMERAL 0).
Definition term66 := Nat.add (BIT1 0) (BIT1 0).
Definition term49 (x0 : nat) := forall y0 : nat, (Nat.add (BIT1 x0) (BIT0 y0)) = (BIT1 (Nat.add x0 y0)).
Definition term207 (x0 : nat) (x1 : nat) := Peano.le x1 (Nat.add x0 x1).
Definition term163 (x0 : nat) (x1 : nat) := Peano.le x0 (Nat.add x0 x1).
Definition term204 (x0 : nat) := (fun y0 : nat => forall y1 : nat, Peano.le y1 (Nat.add y0 y1)) x0.
Definition term185 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.add y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) /\ (y1 = (NUMERAL 0)))) x0.
Definition term181 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (dist (@pair nat nat y0 y1)) = (dist (@pair nat nat y1 y0))) x0.
Definition term179 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) -> Peano.le y0 y1) x0.
Definition term160 (x0 : nat) := (fun y0 : nat => forall y1 : nat, Peano.le y0 (Nat.add y0 y1)) x0.
Definition term101 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) -> forall y2 : nat, (Peano.le y1 y2) -> Peano.le y0 y2) x0.
Definition term57 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add (NUMERAL y0) (NUMERAL y1)) = (NUMERAL (Nat.add y0 y1))) x0.
Definition term48 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add (BIT1 y0) (BIT0 y1)) = (BIT1 (Nat.add y0 y1))) x0.
Definition term42 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add (BIT1 y0) (BIT1 y1)) = (BIT0 (S (Nat.add y0 y1)))) x0.
Definition term235 (x0 : nat) (x1 : nadd) (x2 : nat) (x3 : nat) := (~ ((Nat.add x0 x2) = (NUMERAL 0))) -> Peano.le (dist (@pair nat nat (dest_nadd x1 (Nat.add x0 x2)) (Nat.add (dest_nadd x1 x0) (dest_nadd x1 x2)))) (Nat.mul (NUMERAL (BIT1 (BIT1 0))) x3).
Definition term244 (x0 : nat) (x1 : nadd) (x2 : nat) := @pair nat nat (Nat.mul (Nat.add x0 x2) (dest_nadd x1 (Nat.add x0 x2))) (Nat.add (Nat.mul (Nat.add x0 x2) (dest_nadd x1 x0)) (Nat.mul (Nat.add x0 x2) (dest_nadd x1 x2))).
Definition term347 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (dist (@pair nat nat (Nat.mul x3 (dest_nadd x0 (Nat.add x2 x3))) (Nat.mul (Nat.add x2 x3) (dest_nadd x0 x3)))) (Nat.mul x1 (Nat.add x3 (Nat.add x2 x3))).
Definition term345 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (dist (@pair nat nat (Nat.mul x2 (dest_nadd x0 (Nat.add x2 x3))) (Nat.mul (Nat.add x2 x3) (dest_nadd x0 x2)))) (Nat.mul x1 (Nat.add x2 (Nat.add x2 x3))).
Definition term171 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x1) /\ (Peano.le x1 x2).
Definition term9 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le x0 x1) /\ (Peano.le x2 x3).
Definition term270 := Nat.mul (NUMERAL (BIT1 (BIT1 0))).
Definition term6 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, ((Peano.le x0 x2) /\ (Peano.le x1 y0)) -> Peano.le (Nat.add x0 x1) (Nat.add x2 y0).
Definition term106 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := forall y0 : nat, (Peano.le (Nat.add (dist (@pair nat nat x0 x2)) (dist (@pair nat nat x1 x3))) y0) -> Peano.le (dist (@pair nat nat (Nat.add x0 x1) (Nat.add x2 x3))) y0.
Definition term144 (x0 : Prop) := fun y0 : Prop => ((~ y0) -> x0) = (y0 \/ x0).
Definition term79 := NUMERAL (BIT1 (BIT1 0)).
Definition term78 := BIT1 (BIT1 0).
Definition term252 (x0 : nadd) (x1 : nat) (x2 : nat) := @pair nat nat (Nat.add (Nat.mul x1 (dest_nadd x0 (Nat.add x1 x2))) (Nat.mul x2 (dest_nadd x0 (Nat.add x1 x2)))).
Definition term103 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le (dist (@pair nat nat (Nat.add x0 x1) (Nat.add x2 x3))) (Nat.add (dist (@pair nat nat x0 x2)) (dist (@pair nat nat x1 x3)))) -> forall y0 : nat, (Peano.le (Nat.add (dist (@pair nat nat x0 x2)) (dist (@pair nat nat x1 x3))) y0) -> Peano.le (dist (@pair nat nat (Nat.add x0 x1) (Nat.add x2 x3))) y0.
Definition term203 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nadd) := Peano.le (dist (@pair nat nat (Nat.add (dest_nadd x3 x0) (dest_nadd x3 x1)) (dest_nadd x3 (Nat.add x0 x1)))) (Nat.add (Nat.mul (NUMERAL (BIT1 (BIT1 0))) x2) (dest_nadd x3 (NUMERAL 0))).
Definition term202 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nadd) := Peano.le (dist (@pair nat nat (dest_nadd x3 (Nat.add x0 x1)) (Nat.add (dest_nadd x3 x0) (dest_nadd x3 x1)))) (Nat.add (Nat.mul (NUMERAL (BIT1 (BIT1 0))) x2) (dest_nadd x3 (NUMERAL 0))).
Definition term304 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.add (Nat.mul x1 x0) (Nat.add (Nat.mul x1 x0) (Nat.mul x1 x0))) (Nat.add (Nat.mul x1 x2) (Nat.add (Nat.mul x1 x2) (Nat.mul x1 x2))).
Definition term303 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.add (Nat.mul x1 x0) (Nat.add (Nat.mul x1 x0) (Nat.mul x1 x2))) (Nat.add (Nat.mul x1 x2) (Nat.add (Nat.mul x1 x0) (Nat.mul x1 x2))).
Definition term293 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.add (Nat.mul x0 x2) (Nat.add (Nat.mul x0 x2) (Nat.mul x0 x2))) (Nat.add (Nat.mul x1 x2) (Nat.add (Nat.mul x1 x2) (Nat.mul x1 x2))).
Definition term328 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.add (Nat.mul x1 x0) (Nat.mul x1 x2)) (Nat.add (Nat.mul x1 x2) (Nat.add (Nat.mul x1 x0) (Nat.mul x1 x2))).
Definition term94 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x1 x0) -> (Peano.le x0 x2) -> Peano.le x1 x2.
Definition term151 (x0 : Prop) := (fun y0 : Prop => ((~ y0) -> x0) = (y0 \/ x0)) False.
Definition term11 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.add y0 y1) (Nat.add y2 y3)) -> Peano.le (Nat.add x0 x1) (Nat.add x2 x3).
Definition term28 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.mul (Nat.add x0 x1) y0) = (Nat.add (Nat.mul x0 y0) (Nat.mul x1 y0)).
Definition term325 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x1 x2) (Nat.add (Nat.mul x1 x0) (Nat.add (Nat.mul x1 x0) (Nat.add (Nat.mul x1 x2) (Nat.mul x1 x2)))).
Definition term323 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x1 x2) (Nat.add (Nat.mul x1 x0) (Nat.add (Nat.mul x1 x0) (Nat.add (Nat.mul x1 x0) (Nat.add (Nat.mul x1 x2) (Nat.mul x1 x2))))).
Definition term317 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x1 x2) (Nat.add (Nat.mul x1 x0) (Nat.add (Nat.mul x1 x0) (Nat.add (Nat.mul x1 x0) (Nat.mul x1 x2)))).
Definition term77 := Nat.add 0 (BIT1 0).
Definition term69 := BIT0 (BIT1 0).
Definition term175 (x0 : nat) (x1 : nat) := (exists y0 : nat, (Peano.le x0 y0) /\ (Peano.le y0 x1)) -> Peano.le x0 x1.
Definition term131 (x0 : nat) (x1 : nat) := fun y0 : nat => ((x1 = (NUMERAL 0)) \/ (Peano.le x0 y0)) = (Peano.le (Nat.mul x1 x0) (Nat.mul x1 y0)).
Definition term227 (x0 : nat) (x1 : nadd) := Peano.le (dest_nadd x1 (NUMERAL 0)) (Nat.add (Nat.mul (NUMERAL (BIT1 (BIT1 0))) x0) (dest_nadd x1 (NUMERAL 0))).
Definition term288 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x0 x1) (Nat.mul x0 x1).
Definition term254 (x0 : nat) (x1 : nadd) (x2 : nat) := dist (@pair nat nat (Nat.add (Nat.mul x0 (dest_nadd x1 (Nat.add x0 x2))) (Nat.mul x2 (dest_nadd x1 (Nat.add x0 x2)))) (Nat.add (Nat.mul (Nat.add x0 x2) (dest_nadd x1 x0)) (Nat.mul (Nat.add x0 x2) (dest_nadd x1 x2)))).
Definition term348 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le (dist (@pair nat nat (Nat.mul x2 (dest_nadd x0 (Nat.add x2 x3))) (Nat.mul (Nat.add x2 x3) (dest_nadd x0 x2)))) (Nat.mul x1 (Nat.add x2 (Nat.add x2 x3)))) /\ (Peano.le (dist (@pair nat nat (Nat.mul x3 (dest_nadd x0 (Nat.add x2 x3))) (Nat.mul (Nat.add x2 x3) (dest_nadd x0 x3)))) (Nat.mul x1 (Nat.add x3 (Nat.add x2 x3)))).
Definition term246 (x0 : nat) (x1 : nadd) (x2 : nat) := Peano.le (Nat.mul (Nat.add x0 x2) (dist (@pair nat nat (dest_nadd x1 (Nat.add x0 x2)) (Nat.add (dest_nadd x1 x0) (dest_nadd x1 x2))))).
Definition term145 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => ((~ y0) -> x0) = (y0 \/ x0)) x1.
Definition term284 (x0 : nat) (x1 : nat) := Nat.mul x0 (Nat.mul (Nat.add (NUMERAL (BIT1 0)) (Nat.add (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)))) x1).
Definition term319 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x1 x2) (Nat.add (Nat.mul x1 x0) (Nat.add (Nat.mul x1 x0) (Nat.mul x1 x2))).
Definition term314 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x1 x2) (Nat.add (Nat.mul x1 x0) (Nat.add (Nat.mul x1 x2) (Nat.mul x1 x2))).
Definition term231 (x0 : nat) (x1 : nadd) (x2 : nat) (x3 : nat) := and (Peano.le (dist (@pair nat nat (dest_nadd x1 (Nat.add x0 x2)) (Nat.add (dest_nadd x1 x0) (dest_nadd x1 x2)))) (Nat.mul (NUMERAL (BIT1 (BIT1 0))) x3)).
Definition term327 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x1 x0) (Nat.add (Nat.add (Nat.mul x1 x0) (Nat.mul x1 x2)) (Nat.add (Nat.mul x1 x2) (Nat.add (Nat.mul x1 x0) (Nat.mul x1 x2)))).
Definition term308 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x1 x0) (Nat.add (Nat.add (Nat.mul x1 x0) (Nat.mul x1 x0)) (Nat.add (Nat.mul x1 x2) (Nat.add (Nat.mul x1 x2) (Nat.mul x1 x2)))).
Definition term302 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x1 x2) (Nat.add (Nat.mul x1 x0) (Nat.mul x1 x2)).
Definition term156 (x0 : Prop) := @eq Prop ((~ False) -> x0).
Definition term154 (x0 : Prop) := @eq Prop ((~ True) -> x0).
Definition term264 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => Peano.le (Nat.add (dist (@pair nat nat (Nat.mul x1 (dest_nadd x0 (Nat.add x1 x2))) (Nat.mul (Nat.add x1 x2) (dest_nadd x0 x1)))) (dist (@pair nat nat (Nat.mul x2 (dest_nadd x0 (Nat.add x1 x2))) (Nat.mul (Nat.add x1 x2) (dest_nadd x0 x2))))) y0) (Nat.mul (Nat.add x1 x2) (Nat.mul (NUMERAL (BIT1 (BIT1 0))) x3)).
Definition term192 (x0 : nadd) := (fun y0 : nadd => exists y1 : nat, forall y2 : nat, forall y3 : nat, Peano.le (dist (@pair nat nat (Nat.mul y2 (dest_nadd y0 y3)) (Nat.mul y3 (dest_nadd y0 y2)))) (Nat.mul y1 (Nat.add y2 y3))) x0.
Definition term336 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Nat.add x0 x1) = (Nat.add x0 y0)) = (x1 = y0)) x2.
Definition term210 (x0 : nat) (x1 : nat) := (fun y0 : nat => (dist (@pair nat nat (Nat.add x0 y0) x0)) = y0) x1.
Definition term315 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x1 x0) (Nat.add (Nat.mul x1 x2) (Nat.mul x1 x2)).
Definition term297 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x1 x0) (Nat.add (Nat.mul x1 x0) (Nat.mul x1 x2)).
Definition term261 (x0 : nat) (x1 : nadd) (x2 : nat) := Nat.mul (Nat.add x0 x2) (dest_nadd x1 x2).
Definition term23 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (Nat.add x1 x2).
Definition term340 (x0 : nat) (x1 : nadd) (x2 : nat) := dist (@pair nat nat (Nat.mul x2 (dest_nadd x1 (Nat.add x0 x2))) (Nat.mul (Nat.add x0 x2) (dest_nadd x1 x2))).
Definition term339 (x0 : nat) (x1 : nadd) (x2 : nat) := dist (@pair nat nat (Nat.mul x2 (dest_nadd x1 (Nat.add x2 x0))) (Nat.mul (Nat.add x2 x0) (dest_nadd x1 x2))).
Definition term174 (x0 : nat) (x1 : nat) := fun y0 : nat => (Peano.le x0 y0) /\ (Peano.le y0 x1).
Definition term291 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x0 (Nat.mul (Nat.add (NUMERAL (BIT1 0)) (Nat.add (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)))) x1)).
Definition term274 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.add x0 x1) (Nat.mul (Nat.add (NUMERAL (BIT1 0)) (Nat.add (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)))) x2).
Definition term250 (x0 : nadd) (x1 : nat) (x2 : nat) := Nat.mul (Nat.add x1 x2) (dest_nadd x0 (Nat.add x1 x2)).
Definition term191 (x0 : nat) (x1 : nat) := ~ ((Nat.add x0 x1) = (NUMERAL 0)).
Definition term292 (x0 : nat) (x1 : nat) := Nat.add (Nat.add (Nat.mul x0 x1) (Nat.add (Nat.mul x0 x1) (Nat.mul x0 x1))).
Definition term201 (x0 : nat) (x1 : nadd) := Nat.add (Nat.mul (NUMERAL (BIT1 (BIT1 0))) x0) (dest_nadd x1 (NUMERAL 0)).
Definition term296 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x0 x1) (Nat.mul x0 (Nat.add x1 x2)).
Definition term276 (x0 : nat) (x1 : nat) (x2 : nat) := @eq nat (Nat.mul (Nat.add x0 x1) (Nat.mul (Nat.add (NUMERAL (BIT1 0)) (Nat.add (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)))) x2)).
Definition term275 (x0 : nat) (x1 : nat) (x2 : nat) := @eq nat (Nat.mul (Nat.add x0 x1) (Nat.mul (NUMERAL (BIT1 (BIT1 0))) x2)).
Definition term147 (x0 : Prop) := (~ True) -> x0.
Definition term62 := (forall y0 : nat, (S (NUMERAL y0)) = (NUMERAL (S y0))) /\ (((S 0) = (BIT1 0)) /\ ((forall y0 : nat, (S (BIT0 y0)) = (BIT1 y0)) /\ (forall y0 : nat, (S (BIT1 y0)) = (BIT0 (S y0))))).
Definition term216 (x0 : nadd) (x1 : nat) := Nat.add (dest_nadd x0 x1).
Definition term153 := imp (~ True).
Definition term241 (x0 : nat) (x1 : nadd) (x2 : nat) := Nat.add (Nat.mul (Nat.add x0 x2) (dest_nadd x1 x0)) (Nat.mul (Nat.add x0 x2) (dest_nadd x1 x2)).
Definition term259 (x0 : nadd) (x1 : nat) (x2 : nat) := Nat.mul x2 (dest_nadd x0 (Nat.add x1 x2)).
Definition term32 := (forall y0 : nat, forall y1 : nat, (Nat.add (NUMERAL y0) (NUMERAL y1)) = (NUMERAL (Nat.add y0 y1))) /\ (((Nat.add 0 0) = 0) /\ ((forall y0 : nat, (Nat.add 0 (BIT0 y0)) = (BIT0 y0)) /\ ((forall y0 : nat, (Nat.add 0 (BIT1 y0)) = (BIT1 y0)) /\ ((forall y0 : nat, (Nat.add (BIT0 y0) 0) = (BIT0 y0)) /\ ((forall y0 : nat, (Nat.add (BIT1 y0) 0) = (BIT1 y0)) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT0 y1)) = (BIT0 (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT1 y1)) = (BIT1 (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT0 y1)) = (BIT1 (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT1 y1)) = (BIT0 (S (Nat.add y0 y1)))))))))))).
Definition term96 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le x0 y0) -> Peano.le x1 y0.
Definition term146 (x0 : Prop) := (fun y0 : Prop => ((~ y0) -> x0) = (y0 \/ x0)) True.
Definition term183 (x0 : nat) (x1 : nat) := (fun y0 : nat => (dist (@pair nat nat x0 y0)) = (dist (@pair nat nat y0 x0))) x1.
Definition term86 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => Peano.le (dist (@pair nat nat (Nat.add x0 x2) (Nat.add x1 y0))) (Nat.add (dist (@pair nat nat x0 x1)) (dist (@pair nat nat x2 y0)))) x3.
Definition term251 (x0 : nadd) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x1 (dest_nadd x0 (Nat.add x1 x2))) (Nat.mul x2 (dest_nadd x0 (Nat.add x1 x2))).
Definition term142 (x0 : Prop) := (fun y0 : Prop => (y0 = True) \/ (y0 = False)) x0.
Definition term61 (x0 : nat) (x1 : nat) := NUMERAL (Nat.add x0 x1).
Definition term238 (x0 : nat) (x1 : nadd) (x2 : nat) := Nat.mul (Nat.add x0 x2) (dist (@pair nat nat (dest_nadd x1 (Nat.add x0 x2)) (Nat.add (dest_nadd x1 x0) (dest_nadd x1 x2)))).
Definition term37 := (forall y0 : nat, (Nat.add (BIT1 y0) 0) = (BIT1 y0)) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT0 y1)) = (BIT0 (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT1 y1)) = (BIT1 (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT0 y1)) = (BIT1 (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT1 y1)) = (BIT0 (S (Nat.add y0 y1))))))).
Definition term13 := (forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))).
Definition term219 (x0 : nat) (x1 : nadd) (x2 : nat) := @pair nat nat (Nat.add (dest_nadd x1 x0) (dest_nadd x1 x2)).
Definition term8 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Peano.le x0 x2) /\ (Peano.le x1 x3)) -> Peano.le (Nat.add x0 x1) (Nat.add x2 x3).
Definition term331 (x0 : nat) (x1 : nat) (x2 : nat) := @eq nat (Nat.add (Nat.add (Nat.mul x1 x0) (Nat.add (Nat.mul x1 x0) (Nat.mul x1 x2))) (Nat.add (Nat.mul x1 x2) (Nat.add (Nat.mul x1 x0) (Nat.mul x1 x2)))).
Definition term305 (x0 : nat) (x1 : nat) (x2 : nat) := @eq nat (Nat.add (Nat.add (Nat.mul x1 x0) (Nat.add (Nat.mul x1 x0) (Nat.mul x1 x0))) (Nat.add (Nat.mul x1 x2) (Nat.add (Nat.mul x1 x2) (Nat.mul x1 x2)))).
Definition term294 (x0 : nat) (x1 : nat) (x2 : nat) := @eq nat (Nat.add (Nat.add (Nat.mul x0 x2) (Nat.add (Nat.mul x0 x2) (Nat.mul x0 x2))) (Nat.add (Nat.mul x1 x2) (Nat.add (Nat.mul x1 x2) (Nat.mul x1 x2)))).
Definition term67 := BIT0 (S (Nat.add 0 0)).
Definition term102 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le x0 y0) -> forall y1 : nat, (Peano.le y0 y1) -> Peano.le x0 y1) x1.
Definition term135 (x0 : nat) := fun y0 : nat => forall y1 : nat, ((x0 = (NUMERAL 0)) \/ (Peano.le y0 y1)) = (Peano.le (Nat.mul x0 y0) (Nat.mul x0 y1)).
Definition term134 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Peano.le (Nat.mul x0 y0) (Nat.mul x0 y1)) = ((x0 = (NUMERAL 0)) \/ (Peano.le y0 y1)).
Definition term205 (x0 : nat) := forall y0 : nat, Peano.le y0 (Nat.add x0 y0).
Definition term279 := NUMERAL (BIT1 0).
Definition term17 (x0 : nat) := Nat.mul (NUMERAL (BIT1 0)) x0.
Definition term355 (x0 : nadd) := fun y0 : nat => forall y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (Nat.mul y1 (dest_nadd x0 y2)) (Nat.mul y2 (dest_nadd x0 y1)))) (Nat.mul y0 (Nat.add y1 y2)).
Definition term354 (x0 : nadd) := fun y0 : nat => forall y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 (Nat.add y1 y2)) (Nat.add (dest_nadd x0 y1) (dest_nadd x0 y2)))) y0.
Definition term139 := fun y0 : nat => forall y1 : nat, forall y2 : nat, ((y0 = (NUMERAL 0)) \/ (Peano.le y1 y2)) = (Peano.le (Nat.mul y0 y1) (Nat.mul y0 y2)).
Definition term138 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le (Nat.mul y0 y1) (Nat.mul y0 y2)) = ((y0 = (NUMERAL 0)) \/ (Peano.le y1 y2)).
Definition term271 := Nat.mul (Nat.add (NUMERAL (BIT1 0)) (Nat.add (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)))).
Definition term180 (x0 : nat) (x1 : nat) := (fun y0 : nat => (exists y1 : nat, (Peano.le x0 y1) /\ (Peano.le y1 y0)) -> Peano.le x0 y0) x1.
Definition term50 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add (BIT1 x0) (BIT0 y0)) = (BIT1 (Nat.add x0 y0))) x1.
Definition term337 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((Nat.add (Nat.add (Nat.mul x1 x0) (Nat.add (Nat.mul x1 x0) (Nat.mul x1 x0))) (Nat.add (Nat.mul x1 x2) (Nat.add (Nat.mul x1 x2) (Nat.mul x1 x2)))) = (Nat.add (Nat.add (Nat.mul x1 x0) (Nat.add (Nat.mul x1 x0) (Nat.mul x1 x2))) (Nat.add (Nat.mul x1 x2) (Nat.add (Nat.mul x1 x0) (Nat.mul x1 x2))))).
Definition term187 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Nat.add x0 y0) = (NUMERAL 0)) = ((x0 = (NUMERAL 0)) /\ (y0 = (NUMERAL 0)))) x1.
Definition term344 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (dist (@pair nat nat (Nat.mul x2 (dest_nadd x0 x3)) (Nat.mul x3 (dest_nadd x0 x2)))) (Nat.mul x1 (Nat.add x2 x3)).
Definition term85 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, Peano.le (dist (@pair nat nat (Nat.add x0 x2) (Nat.add x1 y0))) (Nat.add (dist (@pair nat nat x0 x1)) (dist (@pair nat nat x2 y0))).
Definition term268 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (Nat.add (dist (@pair nat nat (Nat.mul x1 (dest_nadd x0 (Nat.add x1 x2))) (Nat.mul (Nat.add x1 x2) (dest_nadd x0 x1)))) (dist (@pair nat nat (Nat.mul x2 (dest_nadd x0 (Nat.add x1 x2))) (Nat.mul (Nat.add x1 x2) (dest_nadd x0 x2))))) (Nat.mul (Nat.add x1 x2) (Nat.mul (NUMERAL (BIT1 (BIT1 0))) x3)).
