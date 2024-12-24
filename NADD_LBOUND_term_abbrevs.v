Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term59 (x0 : nadd) (x1 : nadd) := dest_nadd (nadd_mul x0 x1).
Definition term136 (x0 : nadd) := (exists y0 : nat, exists y1 : nat, forall y2 : nat, Peano.le y2 (Nat.add (Nat.mul y0 (dest_nadd x0 y2)) y1)) -> exists y0 : nat, exists y1 : nat, forall y2 : nat, (Peano.le y1 y2) -> Peano.le y2 (Nat.mul y0 (dest_nadd x0 y2)).
Definition term61 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, (nadd_le y0 y1) = (exists y2 : nat, forall y3 : nat, Peano.le (dest_nadd y0 y3) (Nat.add (dest_nadd y1 y3) y2))) x0.
Definition term42 (x0 : nat) (x1 : nat) := exists y0 : nat, (Peano.le x0 y0) /\ (Peano.le y0 x1).
Definition term86 (x0 : nat) (x1 : nadd) := nadd_mul (nadd_of_num x0) x1.
Definition term32 (x0 : nat) := (fun y0 : nat => y0 = (Nat.mul y0 (NUMERAL (BIT1 0)))) x0.
Definition term195 (x0 : nadd) := fun y0 : nat => exists y1 : nat, forall y2 : nat, (Peano.le y1 y2) -> Peano.le y2 (Nat.mul y0 (dest_nadd x0 y2)).
Definition term130 (x0 : nadd) := fun y0 : nat => exists y1 : nat, forall y2 : nat, Peano.le y2 (Nat.add (Nat.mul y0 (dest_nadd x0 y2)) y1).
Definition term187 (x0 : nadd) (x1 : nat) := Peano.lt (dest_nadd x0 x1) (NUMERAL 0).
Definition term158 (x0 : nat) (x1 : nadd) (x2 : nat) (x3 : nat) := Peano.le (Nat.add (Nat.mul x0 (dest_nadd x1 x2)) x3).
Definition term4 (x0 : nat) := forall y0 : nat, (Peano.le y0 x0) = (~ (Peano.lt x0 y0)).
Definition term190 (x0 : nat) (x1 : nat) (x2 : nadd) (x3 : nat) := Peano.le x3 (Nat.mul (Nat.add x0 x1) (dest_nadd x2 x3)).
Definition term103 (x0 : nat) (x1 : nadd) (x2 : nat) := (fun y0 : nat => (fun y1 : nat => Nat.mul x0 y1) y0) (dest_nadd x1 x2).
Definition term193 (x0 : nat) (x1 : nat) (x2 : nadd) := exists y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> Peano.le y1 (Nat.mul (Nat.add x0 x1) (dest_nadd x2 y1)).
Definition term128 (x0 : nat) (x1 : nadd) := exists y0 : nat, forall y1 : nat, Peano.le y1 (Nat.add (Nat.mul x0 (dest_nadd x1 y1)) y0).
Definition term84 (x0 : nat) (x1 : nadd) := exists y0 : nat, forall y1 : nat, Peano.le (dest_nadd (nadd_of_num (NUMERAL (BIT1 0))) y1) (Nat.add (dest_nadd (nadd_mul (nadd_of_num x0) x1) y1) y0).
Definition term79 (x0 : nadd) := exists y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> ~ ((dest_nadd x0 y1) = (NUMERAL 0)).
Definition term64 (x0 : nadd) (x1 : nadd) := exists y0 : nat, forall y1 : nat, Peano.le (dest_nadd x0 y1) (Nat.add (dest_nadd x1 y1) y0).
Definition term117 (x0 : nat) (x1 : nadd) (x2 : nat) := Nat.add (Nat.mul x0 (dest_nadd x1 x2)).
Definition term30 := fun y0 : nat => y0 = (Nat.mul y0 (NUMERAL (BIT1 0))).
Definition term25 := (forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))))).
Definition term135 (x0 : nadd) := (exists y0 : nat, nadd_le (nadd_of_num (NUMERAL (BIT1 0))) (nadd_mul (nadd_of_num y0) x0)) -> exists y0 : nat, exists y1 : nat, forall y2 : nat, (Peano.le y1 y2) -> Peano.le y2 (Nat.mul y0 (dest_nadd x0 y2)).
Definition term148 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.mul (Nat.add y0 y1) y2) = (Nat.add (Nat.mul y0 y2) (Nat.mul y1 y2))) x0.
Definition term142 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le (Nat.add y0 y1) (Nat.add y0 y2)) = (Peano.le y1 y2)) x0.
Definition term34 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) x0.
Definition term17 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le (Nat.mul y0 y1) (Nat.mul y0 y2)) = ((y0 = (NUMERAL 0)) \/ (Peano.le y1 y2))) x0.
Definition term98 (x0 : nat) := Peano.le (dest_nadd (nadd_of_num (NUMERAL (BIT1 0))) x0).
Definition term146 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.le (Nat.add x0 x1) (Nat.add x0 y0)) = (Peano.le x1 y0)) x2.
Definition term72 (x0 : nadd) := forall y0 : nat, exists y1 : nat, nadd_le (nadd_of_num y0) (nadd_mul (nadd_of_num y1) x0).
Definition term67 (x0 : nadd) := forall y0 : nat, (~ (nadd_eq x0 (nadd_of_num (NUMERAL 0)))) -> exists y1 : nat, nadd_le (nadd_of_num y0) (nadd_mul (nadd_of_num y1) x0).
Definition term99 (x0 : nat) (x1 : nadd) := dest_nadd (nadd_mul (nadd_of_num x0) x1).
Definition term102 (x0 : nat) (x1 : nadd) (x2 : nat) := (fun y0 : nat => Nat.mul x0 y0) (dest_nadd x1 x2).
Definition term47 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> forall y0 : nat, forall y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) -> Peano.le y0 y1.
Definition term110 (x0 : nat) (x1 : nadd) (x2 : nat) := dest_nadd (nadd_mul (nadd_of_num x0) x1) x2.
Definition term23 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = (NUMERAL 0)) \/ (Peano.le x1 x2).
Definition term13 (x0 : nat) := NUMERAL (S x0).
Definition term155 (x0 : nat) (x1 : nadd) (x2 : nat) (x3 : nat) := (fun y0 : nat => Peano.le y0 (Nat.add (Nat.mul x0 (dest_nadd x1 y0)) x2)) x3.
Definition term14 := S (NUMERAL 0).
Definition term65 := forall y0 : nadd, forall y1 : nat, (~ (nadd_eq y0 (nadd_of_num (NUMERAL 0)))) -> exists y2 : nat, nadd_le (nadd_of_num y1) (nadd_mul (nadd_of_num y2) y0).
Definition term124 (x0 : nat) (x1 : nadd) (x2 : nat) := forall y0 : nat, Peano.le (dest_nadd (nadd_of_num (NUMERAL (BIT1 0))) y0) (Nat.add (dest_nadd (nadd_mul (nadd_of_num x0) x1) y0) x2).
Definition term183 (x0 : nadd) (x1 : nat) := ~ (Peano.lt (dest_nadd x0 x1) (S (NUMERAL 0))).
Definition term66 (x0 : nadd) := (fun y0 : nadd => forall y1 : nat, (~ (nadd_eq y0 (nadd_of_num (NUMERAL 0)))) -> exists y2 : nat, nadd_le (nadd_of_num y1) (nadd_mul (nadd_of_num y2) y0)) x0.
Definition term145 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le (Nat.add x0 x1) (Nat.add x0 y0)) = (Peano.le x1 y0).
Definition term115 (x0 : nat) (x1 : nadd) (x2 : nat) := @eq nat ((fun y0 : nat => Nat.mul x0 (dest_nadd x1 y0)) x2).
Definition term41 (x0 : nat) (x1 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> Peano.le x0 x1.
Definition term76 (x0 : nadd) := (fun y0 : nadd => (~ (nadd_eq y0 (nadd_of_num (NUMERAL 0)))) -> forall y1 : nat, exists y2 : nat, nadd_le (nadd_of_num y1) (nadd_mul (nadd_of_num y2) y0)) x0.
Definition term45 (x0 : nat) := forall y0 : nat, (exists y1 : nat, (Peano.le x0 y1) /\ (Peano.le y1 y0)) -> Peano.le x0 y0.
Definition term160 (x0 : nat) (x1 : nat) (x2 : nadd) (x3 : nat) := Peano.le (Nat.add (Nat.mul x0 (dest_nadd x2 x3)) x1) (Nat.add (Nat.mul x0 (dest_nadd x2 x3)) (Nat.mul x1 (dest_nadd x2 x3))).
Definition term164 (x0 : nat) := Peano.le (Nat.mul x0 (NUMERAL (BIT1 0))).
Definition term147 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.add x1 x0) (Nat.add x1 x2).
Definition term101 (x0 : nat) (x1 : nadd) (x2 : nat) := dest_nadd (nadd_of_num x0) (dest_nadd x1 x2).
Definition term162 (x0 : nat) (x1 : nat) (x2 : nadd) (x3 : nat) := (Peano.le x3 (Nat.add (Nat.mul x0 (dest_nadd x2 x3)) x1)) /\ (Peano.le (Nat.add (Nat.mul x0 (dest_nadd x2 x3)) x1) (Nat.mul (Nat.add x0 x1) (dest_nadd x2 x3))).
Definition term91 (x0 : nat) := (fun y0 : nat => y0) x0.
Definition term9 := ((S 0) = (BIT1 0)) /\ ((forall y0 : nat, (S (BIT0 y0)) = (BIT1 y0)) /\ (forall y0 : nat, (S (BIT1 y0)) = (BIT0 (S y0)))).
Definition term177 := forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False.
Definition term169 (x0 : nadd) (x1 : nat) := Peano.le (NUMERAL (BIT1 0)) (dest_nadd x0 x1).
Definition term38 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Peano.le x1 x0) /\ (Peano.le x0 y0)) -> Peano.le x1 y0) x2.
Definition term12 (x0 : nat) := S (NUMERAL x0).
Definition term11 (x0 : nat) := (fun y0 : nat => (S (NUMERAL y0)) = (NUMERAL (S y0))) x0.
Definition term132 (x0 : nadd) := imp (exists y0 : nat, nadd_le (nadd_of_num (NUMERAL (BIT1 0))) (nadd_mul (nadd_of_num y0) x0)).
Definition term108 (x0 : nat) (x1 : nadd) (x2 : nat) := Nat.mul x0 (dest_nadd x1 x2).
Definition term95 := fun y0 : nat => (fun y1 : nat => y1) y0.
Definition term71 (x0 : nat) (x1 : nadd) := exists y0 : nat, nadd_le (nadd_of_num x0) (nadd_mul (nadd_of_num y0) x1).
Definition term29 := fun y0 : nat => (Nat.mul y0 (NUMERAL (BIT1 0))) = y0.
Definition term114 (x0 : nat) (x1 : nadd) (x2 : nat) := @eq nat ((fun y0 : nat => (fun y1 : nat => Nat.mul x0 (dest_nadd x1 y1)) y0) x2).
Definition term58 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => (dest_nadd (nadd_mul x0 y0)) = (fun y1 : nat => dest_nadd x0 (dest_nadd y0 y1))) x1.
Definition term150 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul (Nat.add x0 y0) y1) = (Nat.add (Nat.mul x0 y1) (Nat.mul y0 y1))) x1.
Definition term144 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (Nat.add x0 y0) (Nat.add x0 y1)) = (Peano.le y0 y1)) x1.
Definition term36 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 y1)) -> Peano.le x0 y1) x1.
Definition term19 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (Nat.mul x0 y0) (Nat.mul x0 y1)) = ((x0 = (NUMERAL 0)) \/ (Peano.le y0 y1))) x1.
Definition term165 (x0 : nat) (x1 : nadd) (x2 : nat) := Peano.le (Nat.mul x0 (NUMERAL (BIT1 0))) (Nat.mul x0 (dest_nadd x1 x2)).
Definition term156 (x0 : nat) (x1 : nadd) (x2 : nat) (x3 : nat) := and (Peano.le x2 (Nat.add (Nat.mul x0 (dest_nadd x1 x2)) x3)).
Definition term104 (x0 : nat) (x1 : nat) := (fun y0 : nat => Nat.mul x0 y0) x1.
Definition term90 (x0 : nat) := dest_nadd (nadd_of_num (NUMERAL (BIT1 0))) x0.
Definition term126 (x0 : nat) (x1 : nadd) := fun y0 : nat => forall y1 : nat, Peano.le (dest_nadd (nadd_of_num (NUMERAL (BIT1 0))) y1) (Nat.add (dest_nadd (nadd_mul (nadd_of_num x0) x1) y1) y0).
Definition term5 := fun y0 : nat => forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0).
Definition term176 (x0 : nat) (x1 : nat) := (x0 = x1) \/ (Peano.lt x0 x1).
Definition term85 := nadd_of_num (NUMERAL (BIT1 0)).
Definition term27 := forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0.
Definition term54 (x0 : nat) := dest_nadd (nadd_of_num x0).
Definition term105 (x0 : nat) := fun y0 : nat => (fun y1 : nat => Nat.mul x0 y1) y0.
Definition term39 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.le x1 x0) /\ (Peano.le x0 x2)) -> Peano.le x1 x2.
Definition term111 (x0 : nat) (x1 : nadd) (x2 : nat) := (fun y0 : nat => Nat.mul x0 (dest_nadd x1 y0)) x2.
Definition term161 (x0 : nat) (x1 : nadd) (x2 : nat) := Peano.le x0 (Nat.mul x0 (dest_nadd x1 x2)).
Definition term106 (x0 : nat) (x1 : nadd) (x2 : nat) := @eq nat ((fun y0 : nat => (fun y1 : nat => Nat.mul x0 y1) y0) (dest_nadd x1 x2)).
Definition term63 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => (nadd_le x0 y0) = (exists y1 : nat, forall y2 : nat, Peano.le (dest_nadd x0 y2) (Nat.add (dest_nadd y0 y2) y1))) x1.
Definition term178 (x0 : nat) := (fun y0 : nat => (Peano.lt y0 (NUMERAL 0)) = False) x0.
Definition term1 (x0 : nat) := fun y0 : nat => (~ (Peano.lt x0 y0)) = (Peano.le y0 x0).
Definition term15 := NUMERAL (S 0).
Definition term141 (x0 : nat) (x1 : nat) (x2 : nadd) (x3 : nat) := Nat.mul (Nat.add x0 x1) (dest_nadd x2 x3).
Definition term87 := dest_nadd (nadd_of_num (NUMERAL (BIT1 0))).
Definition term92 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term140 (x0 : nat) (x1 : nat) (x2 : nadd) (x3 : nat) := (exists y0 : nat, (Peano.le x3 y0) /\ (Peano.le y0 (Nat.mul (Nat.add x0 x1) (dest_nadd x2 x3)))) -> Peano.le x3 (Nat.mul (Nat.add x0 x1) (dest_nadd x2 x3)).
Definition term166 (x0 : nat) (x1 : nadd) (x2 : nat) := (x0 = (NUMERAL 0)) \/ (Peano.le (NUMERAL (BIT1 0)) (dest_nadd x1 x2)).
Definition term89 := fun y0 : nat => y0.
Definition term186 (x0 : nadd) (x1 : nat) := or ((dest_nadd x0 x1) = (NUMERAL 0)).
Definition term118 (x0 : nat) (x1 : nadd) (x2 : nat) (x3 : nat) := Nat.add (dest_nadd (nadd_mul (nadd_of_num x0) x1) x2) x3.
Definition term171 := forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)).
Definition term149 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.mul (Nat.add x0 y0) y1) = (Nat.add (Nat.mul x0 y1) (Nat.mul y0 y1)).
Definition term143 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add x0 y0) (Nat.add x0 y1)) = (Peano.le y0 y1).
Definition term46 := forall y0 : nat, forall y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) -> Peano.le y0 y1.
Definition term35 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 y1)) -> Peano.le x0 y1.
Definition term33 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2.
Definition term18 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le (Nat.mul x0 y0) (Nat.mul x0 y1)) = ((x0 = (NUMERAL 0)) \/ (Peano.le y0 y1)).
Definition term8 := forall y0 : nat, forall y1 : nat, (Peano.le y1 y0) = (~ (Peano.lt y0 y1)).
Definition term7 := forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0).
Definition term137 (x0 : nat) (x1 : nadd) (x2 : nat) := (fun y0 : nat => (Peano.le x0 y0) -> ~ ((dest_nadd x1 y0) = (NUMERAL 0))) x2.
Definition term77 (x0 : nadd) := (fun y0 : nadd => (~ (nadd_eq y0 (nadd_of_num (NUMERAL 0)))) -> exists y1 : nat, forall y2 : nat, (Peano.le y1 y2) -> ~ ((dest_nadd y0 y2) = (NUMERAL 0))) x0.
Definition term3 (x0 : nat) := forall y0 : nat, (~ (Peano.lt x0 y0)) = (Peano.le y0 x0).
Definition term57 (x0 : nadd) := forall y0 : nadd, (dest_nadd (nadd_mul x0 y0)) = (fun y1 : nat => dest_nadd x0 (dest_nadd y0 y1)).
Definition term93 (x0 : nat -> nat) (x1 : nat) := (fun y0 : nat => x0 y0) x1.
Definition term192 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nadd) := forall y0 : nat, (Peano.le x0 y0) -> Peano.le y0 (Nat.mul (Nat.add x1 x2) (dest_nadd x3 y0)).
Definition term152 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.mul (Nat.add x0 x1) y0) = (Nat.add (Nat.mul x0 y0) (Nat.mul x1 y0))) x2.
Definition term175 (x0 : nat) (x1 : nat) := Peano.lt x0 (S x1).
Definition term97 (x0 : nat) := @eq nat ((fun y0 : nat => y0) x0).
Definition term56 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, (dest_nadd (nadd_mul y0 y1)) = (fun y2 : nat => dest_nadd y0 (dest_nadd y1 y2))) x0.
Definition term138 (x0 : nat) (x1 : nadd) (x2 : nat) := (Peano.le x0 x2) -> ~ ((dest_nadd x1 x2) = (NUMERAL 0)).
Definition term50 := forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0.
Definition term51 (x0 : nat) := (fun y0 : nat => (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) x0.
Definition term2 (x0 : nat) := fun y0 : nat => (Peano.le y0 x0) = (~ (Peano.lt x0 y0)).
Definition term153 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.add x0 x1) x2.
Definition term154 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x0 x2) (Nat.mul x1 x2).
Definition term60 (x0 : nadd) (x1 : nadd) := fun y0 : nat => dest_nadd x0 (dest_nadd x1 y0).
Definition term173 (x0 : nat) := forall y0 : nat, (Peano.lt x0 (S y0)) = ((x0 = y0) \/ (Peano.lt x0 y0)).
Definition term20 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le (Nat.mul x0 x1) (Nat.mul x0 y0)) = ((x0 = (NUMERAL 0)) \/ (Peano.le x1 y0)).
Definition term112 (x0 : nat) (x1 : nadd) (x2 : nat) := (fun y0 : nat => (fun y1 : nat => Nat.mul x0 (dest_nadd x1 y1)) y0) x2.
Definition term170 (x0 : nadd) (x1 : nat) := Peano.le (S (NUMERAL 0)) (dest_nadd x0 x1).
Definition term22 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul x1 x0) (Nat.mul x1 x2).
Definition term68 (x0 : nadd) (x1 : nat) := (fun y0 : nat => (~ (nadd_eq x0 (nadd_of_num (NUMERAL 0)))) -> exists y1 : nat, nadd_le (nadd_of_num y0) (nadd_mul (nadd_of_num y1) x0)) x1.
Definition term94 (x0 : nat) := (fun y0 : nat => (fun y1 : nat => y1) y0) x0.
Definition term184 (x0 : nadd) (x1 : nat) := Peano.lt (dest_nadd x0 x1) (S (NUMERAL 0)).
Definition term188 (x0 : nat) (x1 : nat) (x2 : nadd) (x3 : nat) := exists y0 : nat, (Peano.le x3 y0) /\ (Peano.le y0 (Nat.mul (Nat.add x0 x1) (dest_nadd x2 x3))).
Definition term26 := (forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))).
Definition term37 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Peano.le x1 x0) /\ (Peano.le x0 y0)) -> Peano.le x1 y0.
Definition term31 := forall y0 : nat, y0 = (Nat.mul y0 (NUMERAL (BIT1 0))).
Definition term55 (x0 : nat) := fun y0 : nat => Nat.mul x0 y0.
Definition term174 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt x0 (S y0)) = ((x0 = y0) \/ (Peano.lt x0 y0))) x1.
Definition term53 (x0 : nat) := (fun y0 : nat => (dest_nadd (nadd_of_num y0)) = (fun y1 : nat => Nat.mul y0 y1)) x0.
Definition term80 (x0 : nat) (x1 : nadd) := forall y0 : nat, (Peano.le x0 y0) -> ~ ((dest_nadd x1 y0) = (NUMERAL 0)).
Definition term185 (x0 : nadd) (x1 : nat) := ((dest_nadd x0 x1) = (NUMERAL 0)) \/ (Peano.lt (dest_nadd x0 x1) (NUMERAL 0)).
Definition term73 (x0 : nadd) := (~ (nadd_eq x0 (nadd_of_num (NUMERAL 0)))) -> forall y0 : nat, exists y1 : nat, nadd_le (nadd_of_num y0) (nadd_mul (nadd_of_num y1) x0).
Definition term179 (x0 : nat) := Peano.lt x0 (NUMERAL 0).
Definition term96 (x0 : nat) := @eq nat ((fun y0 : nat => (fun y1 : nat => y1) y0) x0).
Definition term0 (x0 : nat) (x1 : nat) := ~ (Peano.lt x0 x1).
Definition term120 (x0 : nat) (x1 : nadd) (x2 : nat) (x3 : nat) := Peano.le (dest_nadd (nadd_of_num (NUMERAL (BIT1 0))) x2) (Nat.add (dest_nadd (nadd_mul (nadd_of_num x0) x1) x2) x3).
Definition term199 := forall y0 : nadd, (~ (nadd_eq y0 (nadd_of_num (NUMERAL 0)))) -> exists y1 : nat, exists y2 : nat, forall y3 : nat, (Peano.le y2 y3) -> Peano.le y3 (Nat.mul y1 (dest_nadd y0 y3)).
Definition term28 (x0 : nat) := Nat.mul x0 (NUMERAL (BIT1 0)).
Definition term119 (x0 : nat) (x1 : nadd) (x2 : nat) (x3 : nat) := Nat.add (Nat.mul x0 (dest_nadd x1 x2)) x3.
Definition term180 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y1 y0) = (~ (Peano.lt y0 y1))) x0.
Definition term172 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1))) x0.
Definition term48 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) -> Peano.le y0 y1) x0.
Definition term10 := forall y0 : nat, (S (NUMERAL y0)) = (NUMERAL (S y0)).
Definition term78 (x0 : nadd) := (~ (nadd_eq x0 (nadd_of_num (NUMERAL 0)))) -> exists y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> ~ ((dest_nadd x0 y1) = (NUMERAL 0)).
Definition term159 (x0 : nat) (x1 : nat) (x2 : nadd) (x3 : nat) := Peano.le (Nat.add (Nat.mul x0 (dest_nadd x2 x3)) x1) (Nat.mul (Nat.add x0 x1) (dest_nadd x2 x3)).
Definition term40 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x1) /\ (Peano.le x1 x2).
Definition term125 (x0 : nat) (x1 : nadd) (x2 : nat) := forall y0 : nat, Peano.le y0 (Nat.add (Nat.mul x0 (dest_nadd x1 y0)) x2).
Definition term82 (x0 : nadd) := exists y0 : nat, nadd_le (nadd_of_num (NUMERAL (BIT1 0))) (nadd_mul (nadd_of_num y0) x0).
Definition term123 (x0 : nat) (x1 : nadd) (x2 : nat) := fun y0 : nat => Peano.le y0 (Nat.add (Nat.mul x0 (dest_nadd x1 y0)) x2).
Definition term168 := Peano.le (S (NUMERAL 0)).
Definition term122 (x0 : nat) (x1 : nadd) (x2 : nat) := fun y0 : nat => Peano.le (dest_nadd (nadd_of_num (NUMERAL (BIT1 0))) y0) (Nat.add (dest_nadd (nadd_mul (nadd_of_num x0) x1) y0) x2).
Definition term21 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.le (Nat.mul x0 x1) (Nat.mul x0 y0)) = ((x0 = (NUMERAL 0)) \/ (Peano.le x1 y0))) x2.
Definition term196 (x0 : nadd) := (forall y0 : nat, exists y1 : nat, nadd_le (nadd_of_num y0) (nadd_mul (nadd_of_num y1) x0)) -> exists y0 : nat, exists y1 : nat, forall y2 : nat, (Peano.le y1 y2) -> Peano.le y2 (Nat.mul y0 (dest_nadd x0 y2)).
Definition term163 (x0 : nat) (x1 : nadd) (x2 : nat) := True /\ (Peano.le x0 (Nat.mul x0 (dest_nadd x1 x2))).
Definition term151 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.mul (Nat.add x0 x1) y0) = (Nat.add (Nat.mul x0 y0) (Nat.mul x1 y0)).
Definition term121 (x0 : nat) (x1 : nadd) (x2 : nat) (x3 : nat) := Peano.le x2 (Nat.add (Nat.mul x0 (dest_nadd x1 x2)) x3).
Definition term109 (x0 : nat) (x1 : nadd) := fun y0 : nat => Nat.mul x0 (dest_nadd x1 y0).
Definition term181 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le y0 x0) = (~ (Peano.lt x0 y0))) x1.
Definition term191 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nadd) (x4 : nat) := (Peano.le x0 x4) -> Peano.le x4 (Nat.mul (Nat.add x1 x2) (dest_nadd x3 x4)).
Definition term44 (x0 : nat) (x1 : nat) := (exists y0 : nat, (Peano.le x0 y0) /\ (Peano.le y0 x1)) -> Peano.le x0 x1.
Definition term116 (x0 : nat) (x1 : nadd) (x2 : nat) := Nat.add (dest_nadd (nadd_mul (nadd_of_num x0) x1) x2).
Definition term182 (x0 : nadd) (x1 : nat) := (~ ((dest_nadd x0 x1) = (NUMERAL 0))) -> ((dest_nadd x0 x1) = (NUMERAL 0)) = False.
Definition term69 (x0 : nat) (x1 : nadd) := (~ (nadd_eq x1 (nadd_of_num (NUMERAL 0)))) -> exists y0 : nat, nadd_le (nadd_of_num x0) (nadd_mul (nadd_of_num y0) x1).
Definition term133 (x0 : nadd) := imp (exists y0 : nat, exists y1 : nat, forall y2 : nat, Peano.le y2 (Nat.add (Nat.mul y0 (dest_nadd x0 y2)) y1)).
Definition term88 := fun y0 : nat => Nat.mul (NUMERAL (BIT1 0)) y0.
Definition term74 := forall y0 : nadd, (~ (nadd_eq y0 (nadd_of_num (NUMERAL 0)))) -> forall y1 : nat, exists y2 : nat, nadd_le (nadd_of_num y1) (nadd_mul (nadd_of_num y2) y0).
Definition term81 (x0 : nadd) := (fun y0 : nat => exists y1 : nat, nadd_le (nadd_of_num y0) (nadd_mul (nadd_of_num y1) x0)) (NUMERAL (BIT1 0)).
Definition term100 (x0 : nat) (x1 : nadd) := fun y0 : nat => dest_nadd (nadd_of_num x0) (dest_nadd x1 y0).
Definition term62 (x0 : nadd) := forall y0 : nadd, (nadd_le x0 y0) = (exists y1 : nat, forall y2 : nat, Peano.le (dest_nadd x0 y2) (Nat.add (dest_nadd y0 y2) y1)).
Definition term43 (x0 : nat) (x1 : nat) := fun y0 : nat => (Peano.le x0 y0) /\ (Peano.le y0 x1).
Definition term197 (x0 : nadd) := fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) -> ~ ((dest_nadd x0 y1) = (NUMERAL 0)).
Definition term6 := fun y0 : nat => forall y1 : nat, (Peano.le y1 y0) = (~ (Peano.lt y0 y1)).
Definition term139 (x0 : nadd) (x1 : nat) := ~ ((dest_nadd x0 x1) = (NUMERAL 0)).
Definition term134 (x0 : nadd) := exists y0 : nat, exists y1 : nat, forall y2 : nat, (Peano.le y1 y2) -> Peano.le y2 (Nat.mul y0 (dest_nadd x0 y2)).
Definition term131 (x0 : nadd) := exists y0 : nat, exists y1 : nat, forall y2 : nat, Peano.le y2 (Nat.add (Nat.mul y0 (dest_nadd x0 y2)) y1).
Definition term70 (x0 : nadd) := ~ (nadd_eq x0 (nadd_of_num (NUMERAL 0))).
Definition term113 (x0 : nat) (x1 : nadd) := fun y0 : nat => (fun y1 : nat => Nat.mul x0 (dest_nadd x1 y1)) y0.
Definition term83 (x0 : nat) (x1 : nadd) := nadd_le (nadd_of_num (NUMERAL (BIT1 0))) (nadd_mul (nadd_of_num x0) x1).
Definition term198 (x0 : nadd) := (~ (nadd_eq x0 (nadd_of_num (NUMERAL 0)))) -> exists y0 : nat, exists y1 : nat, forall y2 : nat, (Peano.le y1 y2) -> Peano.le y2 (Nat.mul y0 (dest_nadd x0 y2)).
Definition term189 (x0 : nat) (x1 : nat) (x2 : nadd) (x3 : nat) := fun y0 : nat => (Peano.le x3 y0) /\ (Peano.le y0 (Nat.mul (Nat.add x0 x1) (dest_nadd x2 x3))).
Definition term127 (x0 : nat) (x1 : nadd) := fun y0 : nat => forall y1 : nat, Peano.le y1 (Nat.add (Nat.mul x0 (dest_nadd x1 y1)) y0).
Definition term24 := (forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))).
Definition term157 (x0 : nat) (x1 : nat) (x2 : nadd) (x3 : nat) := Nat.add (Nat.mul x0 (dest_nadd x2 x3)) (Nat.mul x1 (dest_nadd x2 x3)).
Definition term129 (x0 : nadd) := fun y0 : nat => nadd_le (nadd_of_num (NUMERAL (BIT1 0))) (nadd_mul (nadd_of_num y0) x0).
Definition term194 (x0 : nat) (x1 : nat) (x2 : nadd) := fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) -> Peano.le y1 (Nat.mul (Nat.add x0 x1) (dest_nadd x2 y1)).
Definition term107 (x0 : nat) (x1 : nadd) (x2 : nat) := @eq nat ((fun y0 : nat => Nat.mul x0 y0) (dest_nadd x1 x2)).
Definition term16 := NUMERAL (BIT1 0).
Definition term52 (x0 : nat) := Nat.mul (NUMERAL (BIT1 0)) x0.
Definition term167 := Peano.le (NUMERAL (BIT1 0)).
Definition term49 (x0 : nat) (x1 : nat) := (fun y0 : nat => (exists y1 : nat, (Peano.le x0 y1) /\ (Peano.le y1 y0)) -> Peano.le x0 y0) x1.
Definition term75 := (forall y0 : nadd, forall y1 : nat, (~ (nadd_eq y0 (nadd_of_num (NUMERAL 0)))) -> exists y2 : nat, nadd_le (nadd_of_num y1) (nadd_mul (nadd_of_num y2) y0)) -> forall y0 : nadd, (~ (nadd_eq y0 (nadd_of_num (NUMERAL 0)))) -> forall y1 : nat, exists y2 : nat, nadd_le (nadd_of_num y1) (nadd_mul (nadd_of_num y2) y0).
