Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term64 := fun y0 : real => (real_mul y0 (real_of_num (NUMERAL (BIT1 0)))) = y0.
Definition term73 (x0 : nat) (x1 : real) (x2 : nat) := (fun y0 : nat => (real_pow x1 (Nat.add x0 y0)) = (real_mul (real_pow x1 x0) (real_pow x1 y0))) x2.
Definition term20 (x0 : nat) := (fun y0 : nat => (Peano.le 0 (BIT1 y0)) = True) x0.
Definition term102 := real_of_num (NUMERAL 0).
Definition term109 (x0 : real) (x1 : nat) := True /\ (real_le (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 x1)).
Definition term14 := ((Peano.le 0 0) = True) /\ ((forall y0 : nat, (Peano.le (BIT0 y0) 0) = (Peano.le y0 0)) /\ ((forall y0 : nat, (Peano.le (BIT1 y0) 0) = False) /\ ((forall y0 : nat, (Peano.le 0 (BIT0 y0)) = True) /\ ((forall y0 : nat, (Peano.le 0 (BIT1 y0)) = True) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT0 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT1 y1)) = (Peano.le y0 y1))))))))).
Definition term13 := (forall y0 : nat, forall y1 : nat, (Peano.le (NUMERAL y0) (NUMERAL y1)) = (Peano.le y0 y1)) /\ (((Peano.le 0 0) = True) /\ ((forall y0 : nat, (Peano.le (BIT0 y0) 0) = (Peano.le y0 0)) /\ ((forall y0 : nat, (Peano.le (BIT1 y0) 0) = False) /\ ((forall y0 : nat, (Peano.le 0 (BIT0 y0)) = True) /\ ((forall y0 : nat, (Peano.le 0 (BIT1 y0)) = True) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT0 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT1 y1)) = (Peano.le y0 y1)))))))))).
Definition term15 := (forall y0 : nat, (Peano.le (BIT0 y0) 0) = (Peano.le y0 0)) /\ ((forall y0 : nat, (Peano.le (BIT1 y0) 0) = False) /\ ((forall y0 : nat, (Peano.le 0 (BIT0 y0)) = True) /\ ((forall y0 : nat, (Peano.le 0 (BIT1 y0)) = True) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT0 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT1 y1)) = (Peano.le y0 y1)))))))).
Definition term101 (x0 : real) (x1 : nat) := (exists y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le y0 (real_pow x0 x1))) -> real_le (real_of_num (NUMERAL 0)) (real_pow x0 x1).
Definition term93 (x0 : nat) (x1 : real) (x2 : nat) := @eq Prop (real_le (real_pow x1 x0) (real_pow x1 x2)).
Definition term114 (x0 : nat) (x1 : nat) := fun y0 : nat => x0 = (Nat.add x1 y0).
Definition term4 (x0 : real) (x1 : nat) := (real_le (real_of_num (NUMERAL (BIT1 0))) x0) -> real_le (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 x1).
Definition term60 := (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le y1 y2)) -> real_le (real_mul y0 y1) (real_mul y0 y2)) -> forall y0 : real, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y0 y2)) -> real_le (real_mul y1 y0) (real_mul y1 y2).
Definition term45 := (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> forall y0 : real, forall y1 : real, (exists y2 : real, (real_le y0 y2) /\ (real_le y2 y1)) -> real_le y0 y1.
Definition term10 := (forall y0 : nat, forall y1 : real, (real_le (real_of_num (NUMERAL (BIT1 0))) y1) -> real_le (real_of_num (NUMERAL (BIT1 0))) (real_pow y1 y0)) -> forall y0 : real, forall y1 : nat, (real_le (real_of_num (NUMERAL (BIT1 0))) y0) -> real_le (real_of_num (NUMERAL (BIT1 0))) (real_pow y0 y1).
Definition term40 (x0 : real) (x1 : real) := exists y0 : real, (real_le x0 y0) /\ (real_le y0 x1).
Definition term41 (x0 : real) (x1 : real) := fun y0 : real => (real_le x0 y0) /\ (real_le y0 x1).
Definition term28 (x0 : nat) := forall y0 : nat, (real_le (real_of_num x0) (real_of_num y0)) = (Peano.le x0 y0).
Definition term24 (x0 : nat) := forall y0 : nat, (Peano.le (NUMERAL x0) (NUMERAL y0)) = (Peano.le x0 y0).
Definition term77 (x0 : nat) := forall y0 : nat, (Peano.le x0 y0) = (exists y1 : nat, y0 = (Nat.add x0 y1)).
Definition term111 (x0 : real) (x1 : nat) := fun y0 : real => (real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le y0 (real_pow x0 x1)).
Definition term89 (x0 : nat) (x1 : real) (x2 : nat) := (fun y0 : nat => real_le (real_pow x1 x0) (real_pow x1 y0)) x2.
Definition term56 (x0 : real) (x1 : real) (x2 : real) := real_le (real_mul x1 x0) (real_mul x1 x2).
Definition term107 := and (real_le (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term59 := forall y0 : real, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y0 y2)) -> real_le (real_mul y1 y0) (real_mul y1 y2).
Definition term58 (x0 : real) := forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le x0 y1)) -> real_le (real_mul y0 x0) (real_mul y0 y1).
Definition term50 (x0 : real) := forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le y0 y1)) -> real_le (real_mul x0 y0) (real_mul x0 y1).
Definition term48 := forall y0 : real, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le y1 y2)) -> real_le (real_mul y0 y1) (real_mul y0 y2).
Definition term44 := forall y0 : real, forall y1 : real, (exists y2 : real, (real_le y0 y2) /\ (real_le y2 y1)) -> real_le y0 y1.
Definition term33 (x0 : real) := forall y0 : real, forall y1 : real, ((real_le x0 y0) /\ (real_le y0 y1)) -> real_le x0 y1.
Definition term31 := forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2.
Definition term9 := forall y0 : real, forall y1 : nat, (real_le (real_of_num (NUMERAL (BIT1 0))) y0) -> real_le (real_of_num (NUMERAL (BIT1 0))) (real_pow y0 y1).
Definition term98 (x0 : nat) (x1 : real) (x2 : nat) := real_le (real_mul (real_pow x1 x0) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_pow x1 x0) (real_pow x1 x2)).
Definition term37 (x0 : real) (x1 : real) (x2 : real) := ((real_le x1 x0) /\ (real_le x0 x2)) -> real_le x1 x2.
Definition term71 (x0 : real) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (real_pow x0 (Nat.add y0 y1)) = (real_mul (real_pow x0 y0) (real_pow x0 y1))) x1.
Definition term83 (x0 : real) (x1 : nat) (x2 : nat) := imp ((real_le (real_of_num (NUMERAL (BIT1 0))) x0) /\ (Peano.le x1 x2)).
Definition term21 (x0 : nat) := Peano.le 0 (BIT1 x0).
Definition term116 (x0 : nat) (x1 : nat) := forall y0 : real, ((real_le (real_of_num (NUMERAL (BIT1 0))) y0) /\ (Peano.le x0 x1)) -> real_le (real_pow y0 x0) (real_pow y0 x1).
Definition term52 (x0 : real) (x1 : real) := forall y0 : real, ((real_le (real_of_num (NUMERAL 0)) x1) /\ (real_le x0 y0)) -> real_le (real_mul x1 x0) (real_mul x1 y0).
Definition term112 (x0 : real) (x1 : nat) := real_le (real_of_num (NUMERAL 0)) (real_pow x0 x1).
Definition term85 (x0 : nat) (x1 : real) (x2 : nat) := real_le (real_pow x1 x0) (real_pow x1 x2).
Definition term96 (x0 : real) (x1 : nat) := real_mul (real_pow x0 x1) (real_of_num (NUMERAL (BIT1 0))).
Definition term74 (x0 : real) (x1 : nat) (x2 : nat) := real_pow x0 (Nat.add x1 x2).
Definition term95 (x0 : nat) (x1 : real) (x2 : nat) := real_le (real_pow x1 x0) (real_mul (real_pow x1 x0) (real_pow x1 x2)).
Definition term80 (x0 : real) := and (real_le (real_of_num (NUMERAL (BIT1 0))) x0).
Definition term1 (x0 : nat) := (fun y0 : nat => forall y1 : real, (real_le (real_of_num (NUMERAL (BIT1 0))) y1) -> real_le (real_of_num (NUMERAL (BIT1 0))) (real_pow y1 y0)) x0.
Definition term97 (x0 : real) (x1 : nat) := real_le (real_mul (real_pow x0 x1) (real_of_num (NUMERAL (BIT1 0)))).
Definition term11 (x0 : real) := (fun y0 : real => forall y1 : nat, (real_le (real_of_num (NUMERAL (BIT1 0))) y0) -> real_le (real_of_num (NUMERAL (BIT1 0))) (real_pow y0 y1)) x0.
Definition term104 := Peano.le (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term8 (x0 : real) := forall y0 : nat, (real_le (real_of_num (NUMERAL (BIT1 0))) x0) -> real_le (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 y0).
Definition term3 (x0 : nat) (x1 : real) := (fun y0 : real => (real_le (real_of_num (NUMERAL (BIT1 0))) y0) -> real_le (real_of_num (NUMERAL (BIT1 0))) (real_pow y0 x0)) x1.
Definition term39 (x0 : real) (x1 : real) := (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> real_le x0 x1.
Definition term43 (x0 : real) := forall y0 : real, (exists y1 : real, (real_le x0 y1) /\ (real_le y1 y0)) -> real_le x0 y0.
Definition term29 (x0 : nat) (x1 : nat) := (fun y0 : nat => (real_le (real_of_num x0) (real_of_num y0)) = (Peano.le x0 y0)) x1.
Definition term25 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le (NUMERAL x0) (NUMERAL y0)) = (Peano.le x0 y0)) x1.
Definition term79 (x0 : nat) (x1 : nat) := exists y0 : nat, x0 = (Nat.add x1 y0).
Definition term42 (x0 : real) (x1 : real) := (exists y0 : real, (real_le x0 y0) /\ (real_le y0 x1)) -> real_le x0 x1.
Definition term12 (x0 : real) (x1 : nat) := (fun y0 : nat => (real_le (real_of_num (NUMERAL (BIT1 0))) x0) -> real_le (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 y0)) x1.
Definition term7 (x0 : real) (x1 : nat) := (forall y0 : nat, forall y1 : real, (real_le (real_of_num (NUMERAL (BIT1 0))) y1) -> real_le (real_of_num (NUMERAL (BIT1 0))) (real_pow y1 y0)) -> real_le (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 x1).
Definition term113 (x0 : nat) (x1 : real) (x2 : nat) := (real_le (real_of_num (NUMERAL 0)) (real_pow x1 x0)) /\ (real_le (real_of_num (NUMERAL (BIT1 0))) (real_pow x1 x2)).
Definition term118 := forall y0 : nat, forall y1 : nat, forall y2 : real, ((real_le (real_of_num (NUMERAL (BIT1 0))) y2) /\ (Peano.le y0 y1)) -> real_le (real_pow y2 y0) (real_pow y2 y1).
Definition term117 (x0 : nat) := forall y0 : nat, forall y1 : real, ((real_le (real_of_num (NUMERAL (BIT1 0))) y1) /\ (Peano.le x0 y0)) -> real_le (real_pow y1 x0) (real_pow y1 y0).
Definition term70 (x0 : real) := forall y0 : nat, forall y1 : nat, (real_pow x0 (Nat.add y0 y1)) = (real_mul (real_pow x0 y0) (real_pow x0 y1)).
Definition term22 := forall y0 : nat, forall y1 : nat, (Peano.le (NUMERAL y0) (NUMERAL y1)) = (Peano.le y0 y1).
Definition term0 := forall y0 : nat, forall y1 : real, (real_le (real_of_num (NUMERAL (BIT1 0))) y1) -> real_le (real_of_num (NUMERAL (BIT1 0))) (real_pow y1 y0).
Definition term110 (x0 : real) (x1 : nat) := exists y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le y0 (real_pow x0 x1)).
Definition term55 (x0 : real) (x1 : real) (x2 : real) := (real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le x1 x2).
Definition term108 (x0 : real) (x1 : nat) := (real_le (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) /\ (real_le (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 x1)).
Definition term91 (x0 : real) (x1 : nat) (x2 : nat) := real_le (real_pow x0 x1) (real_pow x0 (Nat.add x1 x2)).
Definition term75 (x0 : nat) (x1 : real) (x2 : nat) := real_mul (real_pow x1 x0) (real_pow x1 x2).
Definition term46 (x0 : real) := (fun y0 : real => forall y1 : real, (exists y2 : real, (real_le y0 y2) /\ (real_le y2 y1)) -> real_le y0 y1) x0.
Definition term72 (x0 : nat) (x1 : real) := forall y0 : nat, (real_pow x1 (Nat.add x0 y0)) = (real_mul (real_pow x1 x0) (real_pow x1 y0)).
Definition term68 (x0 : real) := (fun y0 : real => y0 = (real_mul y0 (real_of_num (NUMERAL (BIT1 0))))) x0.
Definition term57 (x0 : real) (x1 : real) (x2 : real) := (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le y1 y2)) -> real_le (real_mul y0 y1) (real_mul y0 y2)) -> real_le (real_mul x1 x0) (real_mul x1 x2).
Definition term94 (x0 : real) (x1 : nat) := real_le (real_pow x0 x1).
Definition term87 (x0 : nat) (x1 : real) (x2 : nat) := ((real_le (real_of_num (NUMERAL (BIT1 0))) x1) /\ (exists y0 : nat, x2 = (Nat.add x0 y0))) -> real_le (real_pow x1 x0) (real_pow x1 x2).
Definition term62 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le x0 y1)) -> real_le (real_mul y0 x0) (real_mul y0 y1)) x1.
Definition term51 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le y0 y1)) -> real_le (real_mul x0 y0) (real_mul x0 y1)) x1.
Definition term34 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, ((real_le x0 y0) /\ (real_le y0 y1)) -> real_le x0 y1) x1.
Definition term53 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => ((real_le (real_of_num (NUMERAL 0)) x1) /\ (real_le x0 y0)) -> real_le (real_mul x1 x0) (real_mul x1 y0)) x2.
Definition term86 (x0 : nat) (x1 : real) (x2 : nat) := ((real_le (real_of_num (NUMERAL (BIT1 0))) x1) /\ (Peano.le x0 x2)) -> real_le (real_pow x1 x0) (real_pow x1 x2).
Definition term36 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => ((real_le x1 x0) /\ (real_le x0 y0)) -> real_le x1 y0) x2.
Definition term2 (x0 : nat) := forall y0 : real, (real_le (real_of_num (NUMERAL (BIT1 0))) y0) -> real_le (real_of_num (NUMERAL (BIT1 0))) (real_pow y0 x0).
Definition term82 (x0 : real) (x1 : nat) (x2 : nat) := (real_le (real_of_num (NUMERAL (BIT1 0))) x0) /\ (exists y0 : nat, x1 = (Nat.add x2 y0)).
Definition term76 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) = (exists y2 : nat, y1 = (Nat.add y0 y2))) x0.
Definition term27 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (real_le (real_of_num y0) (real_of_num y1)) = (Peano.le y0 y1)) x0.
Definition term23 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (NUMERAL y0) (NUMERAL y1)) = (Peano.le y0 y1)) x0.
Definition term47 (x0 : real) (x1 : real) := (fun y0 : real => (exists y1 : real, (real_le x0 y1) /\ (real_le y1 y0)) -> real_le x0 y0) x1.
Definition term69 (x0 : real) := (fun y0 : real => forall y1 : nat, forall y2 : nat, (real_pow y0 (Nat.add y1 y2)) = (real_mul (real_pow y0 y1) (real_pow y0 y2))) x0.
Definition term81 (x0 : real) (x1 : nat) (x2 : nat) := (real_le (real_of_num (NUMERAL (BIT1 0))) x0) /\ (Peano.le x1 x2).
Definition term54 (x0 : real) (x1 : real) (x2 : real) := ((real_le (real_of_num (NUMERAL 0)) x1) /\ (real_le x0 x2)) -> real_le (real_mul x1 x0) (real_mul x1 x2).
Definition term66 := forall y0 : real, (real_mul y0 (real_of_num (NUMERAL (BIT1 0)))) = y0.
Definition term106 := Peano.le 0 (BIT1 0).
Definition term115 (x0 : nat) (x1 : real) (x2 : nat) := (exists y0 : nat, x2 = (Nat.add x0 y0)) -> real_le (real_pow x1 x0) (real_pow x1 x2).
Definition term100 := real_of_num (NUMERAL (BIT1 0)).
Definition term35 (x0 : real) (x1 : real) := forall y0 : real, ((real_le x1 x0) /\ (real_le x0 y0)) -> real_le x1 y0.
Definition term26 (x0 : nat) (x1 : nat) := Peano.le (NUMERAL x0) (NUMERAL x1).
Definition term88 (x0 : nat) (x1 : real) := fun y0 : nat => real_le (real_pow x1 x0) (real_pow x1 y0).
Definition term6 (x0 : real) (x1 : nat) := real_le (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 x1).
Definition term38 (x0 : real) (x1 : real) (x2 : real) := (real_le x0 x1) /\ (real_le x1 x2).
Definition term84 (x0 : real) (x1 : nat) (x2 : nat) := imp ((real_le (real_of_num (NUMERAL (BIT1 0))) x0) /\ (exists y0 : nat, x1 = (Nat.add x2 y0))).
Definition term63 (x0 : real) := real_mul x0 (real_of_num (NUMERAL (BIT1 0))).
Definition term99 (x0 : nat) (x1 : real) (x2 : nat) := ((real_le (real_of_num (NUMERAL 0)) (real_pow x1 x0)) /\ (real_le (real_of_num (NUMERAL (BIT1 0))) (real_pow x1 x2))) -> real_le (real_mul (real_pow x1 x0) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_pow x1 x0) (real_pow x1 x2)).
Definition term92 (x0 : nat) (x1 : real) (x2 : nat) := @eq Prop ((fun y0 : nat => real_le (real_pow x1 x0) (real_pow x1 y0)) x2).
Definition term30 (x0 : nat) (x1 : nat) := real_le (real_of_num x0) (real_of_num x1).
Definition term90 (x0 : real) (x1 : nat) (x2 : nat) := (fun y0 : nat => real_le (real_pow x0 x1) (real_pow x0 y0)) (Nat.add x1 x2).
Definition term17 := (forall y0 : nat, (Peano.le 0 (BIT0 y0)) = True) /\ ((forall y0 : nat, (Peano.le 0 (BIT1 y0)) = True) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT0 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT1 y1)) = (Peano.le y0 y1)))))).
Definition term16 := (forall y0 : nat, (Peano.le (BIT1 y0) 0) = False) /\ ((forall y0 : nat, (Peano.le 0 (BIT0 y0)) = True) /\ ((forall y0 : nat, (Peano.le 0 (BIT1 y0)) = True) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT0 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT1 y1)) = (Peano.le y0 y1))))))).
Definition term103 := real_le (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term78 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le x0 y0) = (exists y1 : nat, y0 = (Nat.add x0 y1))) x1.
Definition term5 (x0 : real) := real_le (real_of_num (NUMERAL (BIT1 0))) x0.
Definition term61 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y0 y2)) -> real_le (real_mul y1 y0) (real_mul y1 y2)) x0.
Definition term49 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le y1 y2)) -> real_le (real_mul y0 y1) (real_mul y0 y2)) x0.
Definition term32 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) x0.
Definition term18 := (forall y0 : nat, (Peano.le 0 (BIT1 y0)) = True) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT0 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT1 y1)) = (Peano.le y0 y1))))).
Definition term105 := NUMERAL (BIT1 0).
Definition term67 := forall y0 : real, y0 = (real_mul y0 (real_of_num (NUMERAL (BIT1 0)))).
Definition term65 := fun y0 : real => y0 = (real_mul y0 (real_of_num (NUMERAL (BIT1 0)))).
Definition term19 := forall y0 : nat, (Peano.le 0 (BIT1 y0)) = True.
