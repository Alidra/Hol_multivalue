Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term217 (x0 : nadd) := (exists y0 : nat, exists y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y1 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.mul (Nat.mul y2 y3) (dist (@pair nat nat (Nat.mul y2 (nadd_rinv x0 y3)) (Nat.mul y3 (nadd_rinv x0 y2))))) (Nat.mul y0 (Nat.mul (Nat.mul y2 y3) (Nat.add y2 y3)))) -> exists y0 : nat, exists y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y1 y2) /\ (Peano.le y1 y3)) -> Peano.le (dist (@pair nat nat (Nat.mul y2 (nadd_rinv x0 y3)) (Nat.mul y3 (nadd_rinv x0 y2)))) (Nat.mul y0 (Nat.add y2 y3)).
Definition term9 (x0 : nat) (x1 : nat) := exists y0 : nat, (Peano.le x0 y0) /\ (Peano.le y0 x1).
Definition term203 (x0 : nat) := fun y0 : nat => (Peano.le (NUMERAL (BIT1 0)) y0) /\ (Peano.le y0 x0).
Definition term204 (x0 : nat) := Peano.le (NUMERAL (BIT1 0)) x0.
Definition term117 (x0 : nat) := fun y0 : nat => (Peano.lt x0 y0) = (Peano.le (S x0) y0).
Definition term207 (x0 : nat) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat) := ((Peano.le x0 x3) /\ (Peano.le x0 x4)) -> Peano.le (dist (@pair nat nat (Nat.mul x3 (nadd_rinv x1 x4)) (Nat.mul x4 (nadd_rinv x1 x3)))) (Nat.mul x2 (Nat.add x3 x4)).
Definition term216 (x0 : nadd) := fun y0 : nat => exists y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y1 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.mul (Nat.mul y2 y3) (dist (@pair nat nat (Nat.mul y2 (nadd_rinv x0 y3)) (Nat.mul y3 (nadd_rinv x0 y2))))) (Nat.mul y0 (Nat.mul (Nat.mul y2 y3) (Nat.add y2 y3))).
Definition term214 (x0 : nadd) := fun y0 : nat => exists y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y1 y2) /\ (Peano.le y1 y3)) -> Peano.le (dist (@pair nat nat (Nat.mul y2 (nadd_rinv x0 y3)) (Nat.mul y3 (nadd_rinv x0 y2)))) (Nat.mul y0 (Nat.add y2 y3)).
Definition term161 (x0 : nat) := and (Peano.le x0 (Nat.add x0 (NUMERAL (BIT1 0)))).
Definition term111 := BIT0 (Nat.mul 0 0).
Definition term211 (x0 : nadd) (x1 : nat) := exists y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y0 y2)) -> Peano.le (dist (@pair nat nat (Nat.mul y1 (nadd_rinv x0 y2)) (Nat.mul y2 (nadd_rinv x0 y1)))) (Nat.mul x1 (Nat.add y1 y2)).
Definition term151 (x0 : nadd) (x1 : nat) := exists y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y0 y2)) -> Peano.le (Nat.mul (Nat.mul y1 y2) (dist (@pair nat nat (Nat.mul y1 (nadd_rinv x0 y2)) (Nat.mul y2 (nadd_rinv x0 y1))))) (Nat.mul x1 (Nat.mul (Nat.mul y1 y2) (Nat.add y1 y2))).
Definition term136 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le (Nat.mul y0 y1) (Nat.mul y0 y2)) = ((y0 = (NUMERAL 0)) \/ (Peano.le y1 y2))) x0.
Definition term33 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.mul y0 y1) (Nat.mul y2 y3)) x0.
Definition term18 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y1) /\ (Peano.le y2 y3)) -> Peano.le (Nat.mul y0 y2) (Nat.mul y1 y3)) x0.
Definition term1 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) x0.
Definition term73 (x0 : nat) (x1 : nat) := NUMERAL (Nat.mul x0 x1).
Definition term24 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => ((Peano.le x0 x2) /\ (Peano.le x1 y0)) -> Peano.le (Nat.mul x0 x1) (Nat.mul x2 y0)) x3.
Definition term67 (x0 : nat) (x1 : nat) := Nat.add (BIT1 x0) (Nat.add (BIT0 x1) (BIT0 (BIT0 (Nat.mul x0 x1)))).
Definition term71 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.mul (NUMERAL x0) (NUMERAL y0)) = (NUMERAL (Nat.mul x0 y0))) x1.
Definition term37 := ((0 = 0) = True) /\ ((forall y0 : nat, ((BIT0 y0) = 0) = (y0 = 0)) /\ ((forall y0 : nat, ((BIT1 y0) = 0) = False) /\ ((forall y0 : nat, (0 = (BIT0 y0)) = (0 = y0)) /\ ((forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1))))))))).
Definition term36 := (forall y0 : nat, forall y1 : nat, ((NUMERAL y0) = (NUMERAL y1)) = (y0 = y1)) /\ (((0 = 0) = True) /\ ((forall y0 : nat, ((BIT0 y0) = 0) = (y0 = 0)) /\ ((forall y0 : nat, ((BIT1 y0) = 0) = False) /\ ((forall y0 : nat, (0 = (BIT0 y0)) = (0 = y0)) /\ ((forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1)))))))))).
Definition term78 := (forall y0 : nat, (Nat.add (BIT0 y0) 0) = (BIT0 y0)) /\ ((forall y0 : nat, (Nat.add (BIT1 y0) 0) = (BIT1 y0)) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT0 y1)) = (BIT0 (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT1 y1)) = (BIT1 (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT0 y1)) = (BIT1 (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT1 y1)) = (BIT0 (S (Nat.add y0 y1)))))))).
Definition term77 := (forall y0 : nat, (Nat.add 0 (BIT1 y0)) = (BIT1 y0)) /\ ((forall y0 : nat, (Nat.add (BIT0 y0) 0) = (BIT0 y0)) /\ ((forall y0 : nat, (Nat.add (BIT1 y0) 0) = (BIT1 y0)) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT0 y1)) = (BIT0 (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT1 y1)) = (BIT1 (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT0 y1)) = (BIT1 (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT1 y1)) = (BIT0 (S (Nat.add y0 y1))))))))).
Definition term76 := (forall y0 : nat, (Nat.add 0 (BIT0 y0)) = (BIT0 y0)) /\ ((forall y0 : nat, (Nat.add 0 (BIT1 y0)) = (BIT1 y0)) /\ ((forall y0 : nat, (Nat.add (BIT0 y0) 0) = (BIT0 y0)) /\ ((forall y0 : nat, (Nat.add (BIT1 y0) 0) = (BIT1 y0)) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT0 y1)) = (BIT0 (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT1 y1)) = (BIT1 (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT0 y1)) = (BIT1 (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT1 y1)) = (BIT0 (S (Nat.add y0 y1)))))))))).
Definition term40 := (forall y0 : nat, (0 = (BIT0 y0)) = (0 = y0)) /\ ((forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1)))))).
Definition term38 := (forall y0 : nat, ((BIT0 y0) = 0) = (y0 = 0)) /\ ((forall y0 : nat, ((BIT1 y0) = 0) = False) /\ ((forall y0 : nat, (0 = (BIT0 y0)) = (0 = y0)) /\ ((forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1)))))))).
Definition term208 (x0 : nat) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat) := ((Peano.le (Nat.add x0 (NUMERAL (BIT1 0))) x3) /\ (Peano.le (Nat.add x0 (NUMERAL (BIT1 0))) x4)) -> Peano.le (dist (@pair nat nat (Nat.mul x3 (nadd_rinv x1 x4)) (Nat.mul x4 (nadd_rinv x1 x3)))) (Nat.mul x2 (Nat.add x3 x4)).
Definition term176 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le (Nat.mul (Nat.mul x2 x3) (dist (@pair nat nat (Nat.mul x2 (nadd_rinv x0 x3)) (Nat.mul x3 (nadd_rinv x0 x2))))) (Nat.mul x1 (Nat.mul (Nat.mul x2 x3) (Nat.add x2 x3)))) -> Peano.le (dist (@pair nat nat (Nat.mul x2 (nadd_rinv x0 x3)) (Nat.mul x3 (nadd_rinv x0 x2)))) (Nat.mul x1 (Nat.add x2 x3)).
Definition term28 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y1) /\ (Peano.le y2 y3)) -> Peano.le (Nat.mul y0 y2) (Nat.mul y1 y3)) -> Peano.le (Nat.mul x0 x1) (Nat.mul x2 x3).
Definition term32 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y1) /\ (Peano.le y2 y3)) -> Peano.le (Nat.mul y0 y2) (Nat.mul y1 y3)) -> forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.mul y0 y1) (Nat.mul y2 y3).
Definition term14 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> forall y0 : nat, forall y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) -> Peano.le y0 y1.
Definition term75 := ((Nat.add 0 0) = 0) /\ ((forall y0 : nat, (Nat.add 0 (BIT0 y0)) = (BIT0 y0)) /\ ((forall y0 : nat, (Nat.add 0 (BIT1 y0)) = (BIT1 y0)) /\ ((forall y0 : nat, (Nat.add (BIT0 y0) 0) = (BIT0 y0)) /\ ((forall y0 : nat, (Nat.add (BIT1 y0) 0) = (BIT1 y0)) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT0 y1)) = (BIT0 (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT1 y1)) = (BIT1 (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT0 y1)) = (BIT1 (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT1 y1)) = (BIT0 (S (Nat.add y0 y1))))))))))).
Definition term54 := ((Nat.mul 0 0) = 0) /\ ((forall y0 : nat, (Nat.mul 0 (BIT0 y0)) = 0) /\ ((forall y0 : nat, (Nat.mul 0 (BIT1 y0)) = 0) /\ ((forall y0 : nat, (Nat.mul (BIT0 y0) 0) = 0) /\ ((forall y0 : nat, (Nat.mul (BIT1 y0) 0) = 0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT0 y0) (BIT0 y1)) = (BIT0 (BIT0 (Nat.mul y0 y1)))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT0 y0) (BIT1 y1)) = (Nat.add (BIT0 y0) (BIT0 (BIT0 (Nat.mul y0 y1))))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT1 y0) (BIT0 y1)) = (Nat.add (BIT0 y1) (BIT0 (BIT0 (Nat.mul y0 y1))))) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul (BIT1 y0) (BIT1 y1)) = (Nat.add (BIT1 y0) (Nat.add (BIT0 y1) (BIT0 (BIT0 (Nat.mul y0 y1))))))))))))).
Definition term142 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = (NUMERAL 0)) \/ (Peano.le x1 x2).
Definition term98 (x0 : nat) := NUMERAL (S x0).
Definition term112 := Nat.add 0 (BIT0 (Nat.mul 0 0)).
Definition term174 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := imp (Peano.le (Nat.mul (Nat.mul x2 x3) (dist (@pair nat nat (Nat.mul x2 (nadd_rinv x0 x3)) (Nat.mul x3 (nadd_rinv x0 x2))))) (Nat.mul (Nat.mul x2 x3) (Nat.mul x1 (Nat.add x2 x3)))).
Definition term100 := S (NUMERAL 0).
Definition term61 := (forall y0 : nat, forall y1 : nat, (Nat.mul (BIT1 y0) (BIT0 y1)) = (Nat.add (BIT0 y1) (BIT0 (BIT0 (Nat.mul y0 y1))))) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul (BIT1 y0) (BIT1 y1)) = (Nat.add (BIT1 y0) (Nat.add (BIT0 y1) (BIT0 (BIT0 (Nat.mul y0 y1)))))).
Definition term44 := (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1)).
Definition term197 (x0 : nat) (x1 : nat) := (fun y0 : nat => Peano.le y0 (Nat.add x0 y0)) x1.
Definition term135 (x0 : nat) := (fun y0 : nat => (y0 = (NUMERAL 0)) = (Peano.le y0 (NUMERAL 0))) x0.
Definition term51 (x0 : nat) := forall y0 : nat, ((NUMERAL x0) = (NUMERAL y0)) = (x0 = y0).
Definition term47 (x0 : nat) := forall y0 : nat, ((BIT1 x0) = (BIT1 y0)) = (x0 = y0).
Definition term173 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := imp (Peano.le (Nat.mul (Nat.mul x2 x3) (dist (@pair nat nat (Nat.mul x2 (nadd_rinv x0 x3)) (Nat.mul x3 (nadd_rinv x0 x2))))) (Nat.mul x1 (Nat.mul (Nat.mul x2 x3) (Nat.add x2 x3)))).
Definition term8 (x0 : nat) (x1 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> Peano.le x0 x1.
Definition term83 (x0 : nat) := forall y0 : nat, (Nat.add (BIT0 x0) (BIT0 y0)) = (BIT0 (Nat.add x0 y0)).
Definition term12 (x0 : nat) := forall y0 : nat, (exists y1 : nat, (Peano.le x0 y1) /\ (Peano.le y1 y0)) -> Peano.le x0 y0.
Definition term66 (x0 : nat) (x1 : nat) := Nat.mul (BIT1 x0) (BIT1 x1).
Definition term85 (x0 : nat) (x1 : nat) := Nat.add (BIT0 x0) (BIT0 x1).
Definition term171 (x0 : nat) (x1 : nadd) (x2 : nat) := Peano.le (Nat.mul (Nat.mul x2 x0) (dist (@pair nat nat (Nat.mul x2 (nadd_rinv x1 x0)) (Nat.mul x0 (nadd_rinv x1 x2))))).
Definition term94 := ((S 0) = (BIT1 0)) /\ ((forall y0 : nat, (S (BIT0 y0)) = (BIT1 y0)) /\ (forall y0 : nat, (S (BIT1 y0)) = (BIT0 (S y0)))).
Definition term157 (x0 : nat) := forall y0 : nat, Peano.le x0 (Nat.add x0 y0).
Definition term172 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (Nat.mul (Nat.mul x2 x3) (dist (@pair nat nat (Nat.mul x2 (nadd_rinv x0 x3)) (Nat.mul x3 (nadd_rinv x0 x2))))) (Nat.mul (Nat.mul x2 x3) (Nat.mul x1 (Nat.add x2 x3))).
Definition term5 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Peano.le x1 x0) /\ (Peano.le x0 y0)) -> Peano.le x1 y0) x2.
Definition term97 (x0 : nat) := S (NUMERAL x0).
Definition term168 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (Nat.mul (Nat.mul x2 x3) (dist (@pair nat nat (Nat.mul x2 (nadd_rinv x0 x3)) (Nat.mul x3 (nadd_rinv x0 x2))))) (Nat.mul x1 (Nat.mul (Nat.mul x2 x3) (Nat.add x2 x3))).
Definition term96 (x0 : nat) := (fun y0 : nat => (S (NUMERAL y0)) = (NUMERAL (S y0))) x0.
Definition term113 := Nat.add (BIT1 0).
Definition term114 := Nat.add (BIT1 0) 0.
Definition term184 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (Peano.le (dist (@pair nat nat (Nat.mul x2 (nadd_rinv x0 x3)) (Nat.mul x3 (nadd_rinv x0 x2)))) (Nat.mul x1 (Nat.add x2 x3)))) -> ~ ((Nat.mul x2 x3) = (NUMERAL 0)).
Definition term64 (x0 : nat) := forall y0 : nat, (Nat.mul (BIT1 x0) (BIT1 y0)) = (Nat.add (BIT1 x0) (Nat.add (BIT0 y0) (BIT0 (BIT0 (Nat.mul x0 y0))))).
Definition term138 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (Nat.mul x0 y0) (Nat.mul x0 y1)) = ((x0 = (NUMERAL 0)) \/ (Peano.le y0 y1))) x1.
Definition term3 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 y1)) -> Peano.le x0 y1) x1.
Definition term169 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (Nat.mul (Nat.mul x1 x2) (Nat.add x1 x2)).
Definition term192 (x0 : nat) (x1 : nat) := Peano.le (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))) (Nat.mul x0 x1).
Definition term121 := fun y0 : nat => forall y1 : nat, (Peano.lt y0 y1) = (Peano.le (S y0) y1).
Definition term120 := fun y0 : nat => forall y1 : nat, (Peano.le (S y0) y1) = (Peano.lt y0 y1).
Definition term80 := (forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT0 y1)) = (BIT0 (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT1 y1)) = (BIT1 (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT0 y1)) = (BIT1 (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT1 y1)) = (BIT0 (S (Nat.add y0 y1)))))).
Definition term59 := (forall y0 : nat, forall y1 : nat, (Nat.mul (BIT0 y0) (BIT0 y1)) = (BIT0 (BIT0 (Nat.mul y0 y1)))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT0 y0) (BIT1 y1)) = (Nat.add (BIT0 y0) (BIT0 (BIT0 (Nat.mul y0 y1))))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT1 y0) (BIT0 y1)) = (Nat.add (BIT0 y1) (BIT0 (BIT0 (Nat.mul y0 y1))))) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul (BIT1 y0) (BIT1 y1)) = (Nat.add (BIT1 y0) (Nat.add (BIT0 y1) (BIT0 (BIT0 (Nat.mul y0 y1)))))))).
Definition term42 := (forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1)))).
Definition term107 := Nat.mul (BIT1 0) (BIT1 0).
Definition term158 (x0 : nat) (x1 : nat) := (fun y0 : nat => Peano.le x0 (Nat.add x0 y0)) x1.
Definition term70 (x0 : nat) := forall y0 : nat, (Nat.mul (NUMERAL x0) (NUMERAL y0)) = (NUMERAL (Nat.mul x0 y0)).
Definition term129 (x0 : nat) (x1 : nat) := ~ (Peano.le x0 x1).
Definition term60 := (forall y0 : nat, forall y1 : nat, (Nat.mul (BIT0 y0) (BIT1 y1)) = (Nat.add (BIT0 y0) (BIT0 (BIT0 (Nat.mul y0 y1))))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT1 y0) (BIT0 y1)) = (Nat.add (BIT0 y1) (BIT0 (BIT0 (Nat.mul y0 y1))))) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul (BIT1 y0) (BIT1 y1)) = (Nat.add (BIT1 y0) (Nat.add (BIT0 y1) (BIT0 (BIT0 (Nat.mul y0 y1))))))).
Definition term43 := (forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1))).
Definition term155 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x1 x0) /\ (Peano.le x1 x2).
Definition term103 := @eq nat (S (NUMERAL 0)).
Definition term6 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.le x1 x0) /\ (Peano.le x0 x2)) -> Peano.le x1 x2.
Definition term88 (x0 : nat) := (fun y0 : nat => (Nat.add (BIT1 y0) 0) = (BIT1 y0)) x0.
Definition term105 := Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term101 := NUMERAL (S 0).
Definition term118 (x0 : nat) := forall y0 : nat, (Peano.le (S x0) y0) = (Peano.lt x0 y0).
Definition term162 (x0 : nat) (x1 : nat) := (Peano.le x0 (Nat.add x0 (NUMERAL (BIT1 0)))) /\ (Peano.le (Nat.add x0 (NUMERAL (BIT1 0))) x1).
Definition term164 (x0 : nat) (x1 : nadd) (x2 : nat) (x3 : nat) := (fun y0 : nat => forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le x0 y1)) -> Peano.le (Nat.mul (Nat.mul y0 y1) (dist (@pair nat nat (Nat.mul y0 (nadd_rinv x1 y1)) (Nat.mul y1 (nadd_rinv x1 y0))))) (Nat.mul x2 (Nat.mul (Nat.mul y0 y1) (Nat.add y0 y1)))) x3.
Definition term160 (x0 : nat) := Peano.le x0 (Nat.add x0 (NUMERAL (BIT1 0))).
Definition term210 (x0 : nat) (x1 : nadd) (x2 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.le (Nat.add x0 (NUMERAL (BIT1 0))) y0) /\ (Peano.le (Nat.add x0 (NUMERAL (BIT1 0))) y1)) -> Peano.le (dist (@pair nat nat (Nat.mul y0 (nadd_rinv x1 y1)) (Nat.mul y1 (nadd_rinv x1 y0)))) (Nat.mul x2 (Nat.add y0 y1)).
Definition term152 (x0 : nat) (x1 : nadd) (x2 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le x0 y1)) -> Peano.le (Nat.mul (Nat.mul y0 y1) (dist (@pair nat nat (Nat.mul y0 (nadd_rinv x1 y1)) (Nat.mul y1 (nadd_rinv x1 y0))))) (Nat.mul x2 (Nat.mul (Nat.mul y0 y1) (Nat.add y0 y1))).
Definition term137 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le (Nat.mul x0 y0) (Nat.mul x0 y1)) = ((x0 = (NUMERAL 0)) \/ (Peano.le y0 y1)).
Definition term123 := forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) = (Peano.le (S y0) y1).
Definition term122 := forall y0 : nat, forall y1 : nat, (Peano.le (S y0) y1) = (Peano.lt y0 y1).
Definition term81 := forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT0 y1)) = (BIT0 (Nat.add y0 y1)).
Definition term68 := forall y0 : nat, forall y1 : nat, (Nat.mul (NUMERAL y0) (NUMERAL y1)) = (NUMERAL (Nat.mul y0 y1)).
Definition term62 := forall y0 : nat, forall y1 : nat, (Nat.mul (BIT1 y0) (BIT1 y1)) = (Nat.add (BIT1 y0) (Nat.add (BIT0 y1) (BIT0 (BIT0 (Nat.mul y0 y1))))).
Definition term49 := forall y0 : nat, forall y1 : nat, ((NUMERAL y0) = (NUMERAL y1)) = (y0 = y1).
Definition term45 := forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1).
Definition term31 := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.mul y0 y1) (Nat.mul y2 y3).
Definition term30 (x0 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le x0 y1) /\ (Peano.le y0 y2)) -> Peano.le (Nat.mul x0 y0) (Nat.mul y1 y2).
Definition term29 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le x1 y1)) -> Peano.le (Nat.mul x0 x1) (Nat.mul y0 y1).
Definition term21 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.le x0 x1) /\ (Peano.le y0 y1)) -> Peano.le (Nat.mul x0 y0) (Nat.mul x1 y1).
Definition term19 (x0 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le x0 y0) /\ (Peano.le y1 y2)) -> Peano.le (Nat.mul x0 y1) (Nat.mul y0 y2).
Definition term17 := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y1) /\ (Peano.le y2 y3)) -> Peano.le (Nat.mul y0 y2) (Nat.mul y1 y3).
Definition term13 := forall y0 : nat, forall y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) -> Peano.le y0 y1.
Definition term2 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 y1)) -> Peano.le x0 y1.
Definition term0 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2.
Definition term147 (x0 : nadd) := (fun y0 : nadd => (~ (nadd_eq y0 (nadd_of_num (NUMERAL 0)))) -> exists y1 : nat, exists y2 : nat, forall y3 : nat, forall y4 : nat, ((Peano.le y2 y3) /\ (Peano.le y2 y4)) -> Peano.le (Nat.mul (Nat.mul y3 y4) (dist (@pair nat nat (Nat.mul y3 (nadd_rinv y0 y4)) (Nat.mul y4 (nadd_rinv y0 y3))))) (Nat.mul y1 (Nat.mul (Nat.mul y3 y4) (Nat.add y3 y4)))) x0.
Definition term187 (x0 : nat) (x1 : nat) := ~ (Peano.le (Nat.mul x0 x1) (NUMERAL 0)).
Definition term202 (x0 : nat) := exists y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) /\ (Peano.le y0 x0).
Definition term35 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le x1 y1)) -> Peano.le (Nat.mul x0 x1) (Nat.mul y0 y1)) x2.
Definition term22 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => forall y1 : nat, ((Peano.le x0 x1) /\ (Peano.le y0 y1)) -> Peano.le (Nat.mul x0 y0) (Nat.mul x1 y1)) x2.
Definition term127 (x0 : nat) := forall y0 : nat, (~ (Peano.le x0 y0)) = (Peano.lt y0 x0).
Definition term34 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.le x0 y1) /\ (Peano.le y0 y2)) -> Peano.le (Nat.mul x0 y0) (Nat.mul y1 y2)) x1.
Definition term20 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.le x0 y0) /\ (Peano.le y1 y2)) -> Peano.le (Nat.mul x0 y1) (Nat.mul y0 y2)) x1.
Definition term177 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le (Nat.mul (Nat.mul x2 x3) (dist (@pair nat nat (Nat.mul x2 (nadd_rinv x0 x3)) (Nat.mul x3 (nadd_rinv x0 x2))))) (Nat.mul (Nat.mul x2 x3) (Nat.mul x1 (Nat.add x2 x3)))) -> Peano.le (dist (@pair nat nat (Nat.mul x2 (nadd_rinv x0 x3)) (Nat.mul x3 (nadd_rinv x0 x2)))) (Nat.mul x1 (Nat.add x2 x3)).
Definition term65 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.mul (BIT1 x0) (BIT1 y0)) = (Nat.add (BIT1 x0) (Nat.add (BIT0 y0) (BIT0 (BIT0 (Nat.mul x0 y0)))))) x1.
Definition term89 (x0 : nat) := Nat.add (BIT1 x0) 0.
Definition term87 := forall y0 : nat, (Nat.add (BIT1 y0) 0) = (BIT1 y0).
Definition term125 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt x0 y0) = (Peano.le (S x0) y0)) x1.
Definition term166 (x0 : nat) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat) := (fun y0 : nat => ((Peano.le x0 x3) /\ (Peano.le x0 y0)) -> Peano.le (Nat.mul (Nat.mul x3 y0) (dist (@pair nat nat (Nat.mul x3 (nadd_rinv x1 y0)) (Nat.mul y0 (nadd_rinv x1 x3))))) (Nat.mul x2 (Nat.mul (Nat.mul x3 y0) (Nat.add x3 y0)))) x4.
Definition term189 (x0 : nat) (x1 : nat) := Peano.le (S (NUMERAL 0)) (Nat.mul x0 x1).
Definition term27 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (Nat.mul x0 x1) (Nat.mul x2 x3).
Definition term163 (x0 : nat) := Nat.add x0 (NUMERAL (BIT1 0)).
Definition term153 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le (Nat.add x1 (NUMERAL (BIT1 0))) x0) /\ (Peano.le (Nat.add x1 (NUMERAL (BIT1 0))) x2).
Definition term119 (x0 : nat) := forall y0 : nat, (Peano.lt x0 y0) = (Peano.le (S x0) y0).
Definition term139 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le (Nat.mul x0 x1) (Nat.mul x0 y0)) = ((x0 = (NUMERAL 0)) \/ (Peano.le x1 y0)).
Definition term132 := fun y0 : nat => (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0)).
Definition term185 (x0 : nat) (x1 : nat) := Peano.le (Nat.mul x0 x1) (NUMERAL 0).
Definition term84 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add (BIT0 x0) (BIT0 y0)) = (BIT0 (Nat.add x0 y0))) x1.
Definition term106 := NUMERAL (Nat.mul (BIT1 0) (BIT1 0)).
Definition term72 (x0 : nat) (x1 : nat) := Nat.mul (NUMERAL x0) (NUMERAL x1).
Definition term141 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul x1 x0) (Nat.mul x1 x2).
Definition term25 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Peano.le x0 x2) /\ (Peano.le x1 x3)) -> Peano.le (Nat.mul x0 x1) (Nat.mul x2 x3).
Definition term170 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.mul x1 x2) (Nat.mul x0 (Nat.add x1 x2)).
Definition term199 (x0 : nat) := Peano.le (NUMERAL (BIT1 0)) (Nat.add x0 (NUMERAL (BIT1 0))).
Definition term99 := ((NUMERAL (NUMERAL 0)) = (NUMERAL 0)) /\ ((BIT0 0) = 0).
Definition term4 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Peano.le x1 x0) /\ (Peano.le x0 y0)) -> Peano.le x1 y0.
Definition term181 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := imp (((Nat.mul x2 x3) = (NUMERAL 0)) \/ (Peano.le (dist (@pair nat nat (Nat.mul x2 (nadd_rinv x0 x3)) (Nat.mul x3 (nadd_rinv x0 x2)))) (Nat.mul x1 (Nat.add x2 x3)))).
Definition term167 (x0 : nat) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat) := ((Peano.le x0 x3) /\ (Peano.le x0 x4)) -> Peano.le (Nat.mul (Nat.mul x3 x4) (dist (@pair nat nat (Nat.mul x3 (nadd_rinv x1 x4)) (Nat.mul x4 (nadd_rinv x1 x3))))) (Nat.mul x2 (Nat.mul (Nat.mul x3 x4) (Nat.add x3 x4))).
Definition term205 (x0 : nat) (x1 : nat) := (Peano.le (NUMERAL (BIT1 0)) x0) /\ (Peano.le (NUMERAL (BIT1 0)) x1).
Definition term219 := forall y0 : nadd, (~ (nadd_eq y0 (nadd_of_num (NUMERAL 0)))) -> exists y1 : nat, exists y2 : nat, forall y3 : nat, forall y4 : nat, ((Peano.le y2 y3) /\ (Peano.le y2 y4)) -> Peano.le (dist (@pair nat nat (Nat.mul y3 (nadd_rinv y0 y4)) (Nat.mul y4 (nadd_rinv y0 y3)))) (Nat.mul y1 (Nat.add y3 y4)).
Definition term198 (x0 : nat) (x1 : nat) := Peano.le x1 (Nat.add x0 x1).
Definition term91 (x0 : nat) := (fun y0 : nat => (Nat.add 0 (BIT0 y0)) = (BIT0 y0)) x0.
Definition term104 := @eq nat (NUMERAL (BIT1 0)).
Definition term159 (x0 : nat) (x1 : nat) := Peano.le x0 (Nat.add x0 x1).
Definition term195 (x0 : nat) := (fun y0 : nat => forall y1 : nat, Peano.le y1 (Nat.add y0 y1)) x0.
Definition term156 (x0 : nat) := (fun y0 : nat => forall y1 : nat, Peano.le y0 (Nat.add y0 y1)) x0.
Definition term126 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) x0.
Definition term124 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y0 y1) = (Peano.le (S y0) y1)) x0.
Definition term82 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add (BIT0 y0) (BIT0 y1)) = (BIT0 (Nat.add y0 y1))) x0.
Definition term69 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul (NUMERAL y0) (NUMERAL y1)) = (NUMERAL (Nat.mul y0 y1))) x0.
Definition term63 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul (BIT1 y0) (BIT1 y1)) = (Nat.add (BIT1 y0) (Nat.add (BIT0 y1) (BIT0 (BIT0 (Nat.mul y0 y1)))))) x0.
Definition term50 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((NUMERAL y0) = (NUMERAL y1)) = (y0 = y1)) x0.
Definition term46 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1)) x0.
Definition term15 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) -> Peano.le y0 y1) x0.
Definition term95 := forall y0 : nat, (S (NUMERAL y0)) = (NUMERAL (S y0)).
Definition term182 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := (((Nat.mul x2 x3) = (NUMERAL 0)) \/ (Peano.le (dist (@pair nat nat (Nat.mul x2 (nadd_rinv x0 x3)) (Nat.mul x3 (nadd_rinv x0 x2)))) (Nat.mul x1 (Nat.add x2 x3)))) -> Peano.le (dist (@pair nat nat (Nat.mul x2 (nadd_rinv x0 x3)) (Nat.mul x3 (nadd_rinv x0 x2)))) (Nat.mul x1 (Nat.add x2 x3)).
Definition term7 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x1) /\ (Peano.le x1 x2).
Definition term26 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le x0 x1) /\ (Peano.le x2 x3).
Definition term23 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, ((Peano.le x0 x2) /\ (Peano.le x1 y0)) -> Peano.le (Nat.mul x0 x1) (Nat.mul x2 y0).
Definition term145 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (Nat.mul x1 x2).
Definition term108 := Nat.add (BIT1 0) (Nat.add (BIT0 0) (BIT0 (BIT0 (Nat.mul 0 0)))).
Definition term206 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := ~ (Peano.le (dist (@pair nat nat (Nat.mul x2 (nadd_rinv x0 x3)) (Nat.mul x3 (nadd_rinv x0 x2)))) (Nat.mul x1 (Nat.add x2 x3))).
Definition term190 := Peano.le (S (NUMERAL 0)).
Definition term140 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.le (Nat.mul x0 x1) (Nat.mul x0 y0)) = ((x0 = (NUMERAL 0)) \/ (Peano.le x1 y0))) x2.
Definition term134 := forall y0 : nat, (y0 = (NUMERAL 0)) = (Peano.le y0 (NUMERAL 0)).
Definition term130 := forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0)).
Definition term115 (x0 : nat) (x1 : nat) := Peano.le (S x0) x1.
Definition term188 (x0 : nat) (x1 : nat) := Peano.lt (NUMERAL 0) (Nat.mul x0 x1).
Definition term11 (x0 : nat) (x1 : nat) := (exists y0 : nat, (Peano.le x0 y0) /\ (Peano.le y0 x1)) -> Peano.le x0 x1.
Definition term178 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := ((Nat.mul x2 x3) = (NUMERAL 0)) \/ (Peano.le (dist (@pair nat nat (Nat.mul x2 (nadd_rinv x0 x3)) (Nat.mul x3 (nadd_rinv x0 x2)))) (Nat.mul x1 (Nat.add x2 x3))).
Definition term144 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.mul (Nat.mul x1 x0) x2) = (Nat.mul x1 (Nat.mul x0 x2))) /\ ((Nat.mul x1 (Nat.mul x0 x2)) = (Nat.mul x0 (Nat.mul x1 x2))).
Definition term191 := Peano.le (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term110 := BIT0 (Nat.add 0 (BIT0 (Nat.mul 0 0))).
Definition term183 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := ((Nat.mul x2 x3) = (NUMERAL 0)) -> Peano.le (dist (@pair nat nat (Nat.mul x2 (nadd_rinv x0 x3)) (Nat.mul x3 (nadd_rinv x0 x2)))) (Nat.mul x1 (Nat.add x2 x3)).
Definition term180 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (Nat.add x1 x2).
Definition term10 (x0 : nat) (x1 : nat) := fun y0 : nat => (Peano.le x0 y0) /\ (Peano.le y0 x1).
Definition term92 (x0 : nat) := Nat.add 0 (BIT0 x0).
Definition term90 := forall y0 : nat, (Nat.add 0 (BIT0 y0)) = (BIT0 y0).
Definition term186 (x0 : nat) (x1 : nat) := ~ ((Nat.mul x0 x1) = (NUMERAL 0)).
Definition term213 (x0 : nadd) := exists y0 : nat, exists y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y1 y2) /\ (Peano.le y1 y3)) -> Peano.le (dist (@pair nat nat (Nat.mul y2 (nadd_rinv x0 y3)) (Nat.mul y3 (nadd_rinv x0 y2)))) (Nat.mul y0 (Nat.add y2 y3)).
Definition term150 (x0 : nadd) := exists y0 : nat, exists y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y1 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.mul (Nat.mul y2 y3) (dist (@pair nat nat (Nat.mul y2 (nadd_rinv x0 y3)) (Nat.mul y3 (nadd_rinv x0 y2))))) (Nat.mul y0 (Nat.mul (Nat.mul y2 y3) (Nat.add y2 y3))).
Definition term86 (x0 : nat) (x1 : nat) := BIT0 (Nat.add x0 x1).
Definition term149 (x0 : nadd) := ~ (nadd_eq x0 (nadd_of_num (NUMERAL 0))).
Definition term57 := (forall y0 : nat, (Nat.mul (BIT0 y0) 0) = 0) /\ ((forall y0 : nat, (Nat.mul (BIT1 y0) 0) = 0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT0 y0) (BIT0 y1)) = (BIT0 (BIT0 (Nat.mul y0 y1)))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT0 y0) (BIT1 y1)) = (Nat.add (BIT0 y0) (BIT0 (BIT0 (Nat.mul y0 y1))))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT1 y0) (BIT0 y1)) = (Nat.add (BIT0 y1) (BIT0 (BIT0 (Nat.mul y0 y1))))) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul (BIT1 y0) (BIT1 y1)) = (Nat.add (BIT1 y0) (Nat.add (BIT0 y1) (BIT0 (BIT0 (Nat.mul y0 y1)))))))))).
Definition term56 := (forall y0 : nat, (Nat.mul 0 (BIT1 y0)) = 0) /\ ((forall y0 : nat, (Nat.mul (BIT0 y0) 0) = 0) /\ ((forall y0 : nat, (Nat.mul (BIT1 y0) 0) = 0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT0 y0) (BIT0 y1)) = (BIT0 (BIT0 (Nat.mul y0 y1)))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT0 y0) (BIT1 y1)) = (Nat.add (BIT0 y0) (BIT0 (BIT0 (Nat.mul y0 y1))))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT1 y0) (BIT0 y1)) = (Nat.add (BIT0 y1) (BIT0 (BIT0 (Nat.mul y0 y1))))) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul (BIT1 y0) (BIT1 y1)) = (Nat.add (BIT1 y0) (Nat.add (BIT0 y1) (BIT0 (BIT0 (Nat.mul y0 y1))))))))))).
Definition term55 := (forall y0 : nat, (Nat.mul 0 (BIT0 y0)) = 0) /\ ((forall y0 : nat, (Nat.mul 0 (BIT1 y0)) = 0) /\ ((forall y0 : nat, (Nat.mul (BIT0 y0) 0) = 0) /\ ((forall y0 : nat, (Nat.mul (BIT1 y0) 0) = 0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT0 y0) (BIT0 y1)) = (BIT0 (BIT0 (Nat.mul y0 y1)))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT0 y0) (BIT1 y1)) = (Nat.add (BIT0 y0) (BIT0 (BIT0 (Nat.mul y0 y1))))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT1 y0) (BIT0 y1)) = (Nat.add (BIT0 y1) (BIT0 (BIT0 (Nat.mul y0 y1))))) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul (BIT1 y0) (BIT1 y1)) = (Nat.add (BIT1 y0) (Nat.add (BIT0 y1) (BIT0 (BIT0 (Nat.mul y0 y1)))))))))))).
Definition term39 := (forall y0 : nat, ((BIT1 y0) = 0) = False) /\ ((forall y0 : nat, (0 = (BIT0 y0)) = (0 = y0)) /\ ((forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1))))))).
Definition term209 (x0 : nat) (x1 : nadd) (x2 : nat) (x3 : nat) := forall y0 : nat, ((Peano.le (Nat.add x0 (NUMERAL (BIT1 0))) x3) /\ (Peano.le (Nat.add x0 (NUMERAL (BIT1 0))) y0)) -> Peano.le (dist (@pair nat nat (Nat.mul x3 (nadd_rinv x1 y0)) (Nat.mul y0 (nadd_rinv x1 x3)))) (Nat.mul x2 (Nat.add x3 y0)).
Definition term165 (x0 : nat) (x1 : nadd) (x2 : nat) (x3 : nat) := forall y0 : nat, ((Peano.le x0 x3) /\ (Peano.le x0 y0)) -> Peano.le (Nat.mul (Nat.mul x3 y0) (dist (@pair nat nat (Nat.mul x3 (nadd_rinv x1 y0)) (Nat.mul y0 (nadd_rinv x1 x3))))) (Nat.mul x2 (Nat.mul (Nat.mul x3 y0) (Nat.add x3 y0))).
Definition term93 := (forall y0 : nat, (S (NUMERAL y0)) = (NUMERAL (S y0))) /\ (((S 0) = (BIT1 0)) /\ ((forall y0 : nat, (S (BIT0 y0)) = (BIT1 y0)) /\ (forall y0 : nat, (S (BIT1 y0)) = (BIT0 (S y0))))).
Definition term201 (x0 : nat) (x1 : nat) := (Peano.le (NUMERAL (BIT1 0)) (Nat.add x0 (NUMERAL (BIT1 0)))) /\ (Peano.le (Nat.add x0 (NUMERAL (BIT1 0))) x1).
Definition term74 := (forall y0 : nat, forall y1 : nat, (Nat.add (NUMERAL y0) (NUMERAL y1)) = (NUMERAL (Nat.add y0 y1))) /\ (((Nat.add 0 0) = 0) /\ ((forall y0 : nat, (Nat.add 0 (BIT0 y0)) = (BIT0 y0)) /\ ((forall y0 : nat, (Nat.add 0 (BIT1 y0)) = (BIT1 y0)) /\ ((forall y0 : nat, (Nat.add (BIT0 y0) 0) = (BIT0 y0)) /\ ((forall y0 : nat, (Nat.add (BIT1 y0) 0) = (BIT1 y0)) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT0 y1)) = (BIT0 (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT1 y1)) = (BIT1 (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT0 y1)) = (BIT1 (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT1 y1)) = (BIT0 (S (Nat.add y0 y1)))))))))))).
Definition term53 := (forall y0 : nat, forall y1 : nat, (Nat.mul (NUMERAL y0) (NUMERAL y1)) = (NUMERAL (Nat.mul y0 y1))) /\ (((Nat.mul 0 0) = 0) /\ ((forall y0 : nat, (Nat.mul 0 (BIT0 y0)) = 0) /\ ((forall y0 : nat, (Nat.mul 0 (BIT1 y0)) = 0) /\ ((forall y0 : nat, (Nat.mul (BIT0 y0) 0) = 0) /\ ((forall y0 : nat, (Nat.mul (BIT1 y0) 0) = 0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT0 y0) (BIT0 y1)) = (BIT0 (BIT0 (Nat.mul y0 y1)))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT0 y0) (BIT1 y1)) = (Nat.add (BIT0 y0) (BIT0 (BIT0 (Nat.mul y0 y1))))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT1 y0) (BIT0 y1)) = (Nat.add (BIT0 y1) (BIT0 (BIT0 (Nat.mul y0 y1))))) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul (BIT1 y0) (BIT1 y1)) = (Nat.add (BIT1 y0) (Nat.add (BIT0 y1) (BIT0 (BIT0 (Nat.mul y0 y1)))))))))))))).
Definition term218 (x0 : nadd) := (~ (nadd_eq x0 (nadd_of_num (NUMERAL 0)))) -> exists y0 : nat, exists y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y1 y2) /\ (Peano.le y1 y3)) -> Peano.le (dist (@pair nat nat (Nat.mul y2 (nadd_rinv x0 y3)) (Nat.mul y3 (nadd_rinv x0 y2)))) (Nat.mul y0 (Nat.add y2 y3)).
Definition term148 (x0 : nadd) := (~ (nadd_eq x0 (nadd_of_num (NUMERAL 0)))) -> exists y0 : nat, exists y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y1 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.mul (Nat.mul y2 y3) (dist (@pair nat nat (Nat.mul y2 (nadd_rinv x0 y3)) (Nat.mul y3 (nadd_rinv x0 y2))))) (Nat.mul y0 (Nat.mul (Nat.mul y2 y3) (Nat.add y2 y3))).
Definition term116 (x0 : nat) := fun y0 : nat => (Peano.le (S x0) y0) = (Peano.lt x0 y0).
Definition term128 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (Peano.le x0 y0)) = (Peano.lt y0 x0)) x1.
Definition term143 (a0 : Type') (x0 : a0) := (fun y0 : a0 => (y0 = y0) = True) x0.
Definition term194 (x0 : nat) := (exists y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) /\ (Peano.le y0 x0)) -> Peano.le (NUMERAL (BIT1 0)) x0.
Definition term133 := fun y0 : nat => (y0 = (NUMERAL 0)) = (Peano.le y0 (NUMERAL 0)).
Definition term52 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((NUMERAL x0) = (NUMERAL y0)) = (x0 = y0)) x1.
Definition term48 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((BIT1 x0) = (BIT1 y0)) = (x0 = y0)) x1.
Definition term131 (x0 : nat) := Peano.le x0 (NUMERAL 0).
Definition term79 := (forall y0 : nat, (Nat.add (BIT1 y0) 0) = (BIT1 y0)) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT0 y1)) = (BIT0 (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT1 y1)) = (BIT1 (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT0 y1)) = (BIT1 (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT1 y1)) = (BIT0 (S (Nat.add y0 y1))))))).
Definition term179 (x0 : nat) (x1 : nadd) (x2 : nat) := dist (@pair nat nat (Nat.mul x2 (nadd_rinv x1 x0)) (Nat.mul x0 (nadd_rinv x1 x2))).
Definition term200 (x0 : nat) := and (Peano.le (NUMERAL (BIT1 0)) (Nat.add x0 (NUMERAL (BIT1 0)))).
Definition term146 (x0 : nat) (x1 : nat) (x2 : nat) := @eq nat (Nat.mul x0 (Nat.mul x1 x2)).
Definition term154 (x0 : nat) (x1 : nat) := Peano.le (Nat.add x0 (NUMERAL (BIT1 0))) x1.
Definition term58 := (forall y0 : nat, (Nat.mul (BIT1 y0) 0) = 0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT0 y0) (BIT0 y1)) = (BIT0 (BIT0 (Nat.mul y0 y1)))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT0 y0) (BIT1 y1)) = (Nat.add (BIT0 y0) (BIT0 (BIT0 (Nat.mul y0 y1))))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT1 y0) (BIT0 y1)) = (Nat.add (BIT0 y1) (BIT0 (BIT0 (Nat.mul y0 y1))))) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul (BIT1 y0) (BIT1 y1)) = (Nat.add (BIT1 y0) (Nat.add (BIT0 y1) (BIT0 (BIT0 (Nat.mul y0 y1))))))))).
Definition term41 := (forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1))))).
Definition term196 (x0 : nat) := forall y0 : nat, Peano.le y0 (Nat.add x0 y0).
Definition term193 (x0 : nat) (x1 : nat) := ((Peano.le (NUMERAL (BIT1 0)) x0) /\ (Peano.le (NUMERAL (BIT1 0)) x1)) -> Peano.le (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))) (Nat.mul x0 x1).
Definition term102 := NUMERAL (BIT1 0).
Definition term215 (x0 : nadd) (x1 : nat) := fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y0 y2)) -> Peano.le (Nat.mul (Nat.mul y1 y2) (dist (@pair nat nat (Nat.mul y1 (nadd_rinv x0 y2)) (Nat.mul y2 (nadd_rinv x0 y1))))) (Nat.mul x1 (Nat.mul (Nat.mul y1 y2) (Nat.add y1 y2))).
Definition term212 (x0 : nadd) (x1 : nat) := fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y0 y2)) -> Peano.le (dist (@pair nat nat (Nat.mul y1 (nadd_rinv x0 y2)) (Nat.mul y2 (nadd_rinv x0 y1)))) (Nat.mul x1 (Nat.add y1 y2)).
Definition term109 := Nat.add (BIT0 0) (BIT0 (BIT0 (Nat.mul 0 0))).
Definition term16 (x0 : nat) (x1 : nat) := (fun y0 : nat => (exists y1 : nat, (Peano.le x0 y1) /\ (Peano.le y1 y0)) -> Peano.le x0 y0) x1.
Definition term175 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (dist (@pair nat nat (Nat.mul x2 (nadd_rinv x0 x3)) (Nat.mul x3 (nadd_rinv x0 x2)))) (Nat.mul x1 (Nat.add x2 x3)).
