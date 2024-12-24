Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term31 (x0 : nadd) (x1 : nadd) := dest_nadd (nadd_mul x0 x1).
Definition term105 (x0 : nadd) := (exists y0 : nat, exists y1 : nat, forall y2 : nat, Peano.le y2 (Nat.add (Nat.mul y0 (dest_nadd x0 y2)) y1)) -> exists y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> ~ ((dest_nadd x0 y1) = (NUMERAL 0)).
Definition term33 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, (nadd_le y0 y1) = (exists y2 : nat, forall y3 : nat, Peano.le (dest_nadd y0 y3) (Nat.add (dest_nadd y1 y3) y2))) x0.
Definition term55 (x0 : nat) (x1 : nadd) := nadd_mul (nadd_of_num x0) x1.
Definition term2 (x0 : nat) := fun y0 : nat => (Peano.lt x0 y0) = (Peano.le (S x0) y0).
Definition term99 (x0 : nadd) := fun y0 : nat => exists y1 : nat, forall y2 : nat, Peano.le y2 (Nat.add (Nat.mul y0 (dest_nadd x0 y2)) y1).
Definition term72 (x0 : nat) (x1 : nadd) (x2 : nat) := (fun y0 : nat => (fun y1 : nat => Nat.mul x0 y1) y0) (dest_nadd x1 x2).
Definition term103 (x0 : nadd) := exists y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> ~ ((dest_nadd x0 y1) = (NUMERAL 0)).
Definition term97 (x0 : nat) (x1 : nadd) := exists y0 : nat, forall y1 : nat, Peano.le y1 (Nat.add (Nat.mul x0 (dest_nadd x1 y1)) y0).
Definition term53 (x0 : nat) (x1 : nadd) := exists y0 : nat, forall y1 : nat, Peano.le (dest_nadd (nadd_of_num (NUMERAL (BIT1 0))) y1) (Nat.add (dest_nadd (nadd_mul (nadd_of_num x0) x1) y1) y0).
Definition term36 (x0 : nadd) (x1 : nadd) := exists y0 : nat, forall y1 : nat, Peano.le (dest_nadd x0 y1) (Nat.add (dest_nadd x1 y1) y0).
Definition term86 (x0 : nat) (x1 : nadd) (x2 : nat) := Nat.add (Nat.mul x0 (dest_nadd x1 x2)).
Definition term21 := (forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))))).
Definition term104 (x0 : nadd) := (exists y0 : nat, nadd_le (nadd_of_num (NUMERAL (BIT1 0))) (nadd_mul (nadd_of_num y0) x0)) -> exists y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> ~ ((dest_nadd x0 y1) = (NUMERAL 0)).
Definition term67 (x0 : nat) := Peano.le (dest_nadd (nadd_of_num (NUMERAL (BIT1 0))) x0).
Definition term44 (x0 : nadd) := forall y0 : nat, exists y1 : nat, nadd_le (nadd_of_num y0) (nadd_mul (nadd_of_num y1) x0).
Definition term39 (x0 : nadd) := forall y0 : nat, (~ (nadd_eq x0 (nadd_of_num (NUMERAL 0)))) -> exists y1 : nat, nadd_le (nadd_of_num y0) (nadd_mul (nadd_of_num y1) x0).
Definition term9 (x0 : nat) := (fun y0 : nat => (S y0) = (Nat.add y0 (NUMERAL (BIT1 0)))) x0.
Definition term131 (x0 : nat) (x1 : nadd) (x2 : nat) := exists y0 : nat, Peano.le (Nat.add (Nat.add (Nat.mul x0 (dest_nadd x1 y0)) x2) (NUMERAL (BIT1 0))) y0.
Definition term68 (x0 : nat) (x1 : nadd) := dest_nadd (nadd_mul (nadd_of_num x0) x1).
Definition term71 (x0 : nat) (x1 : nadd) (x2 : nat) := (fun y0 : nat => Nat.mul x0 y0) (dest_nadd x1 x2).
Definition term79 (x0 : nat) (x1 : nadd) (x2 : nat) := dest_nadd (nadd_mul (nadd_of_num x0) x1) x2.
Definition term113 (x0 : nat) (x1 : nadd) (x2 : nat) (x3 : nat) := (fun y0 : nat => Peano.le y0 (Nat.add (Nat.mul x0 (dest_nadd x1 y0)) x2)) x3.
Definition term37 := forall y0 : nadd, forall y1 : nat, (~ (nadd_eq y0 (nadd_of_num (NUMERAL 0)))) -> exists y2 : nat, nadd_le (nadd_of_num y1) (nadd_mul (nadd_of_num y2) y0).
Definition term93 (x0 : nat) (x1 : nadd) (x2 : nat) := forall y0 : nat, Peano.le (dest_nadd (nadd_of_num (NUMERAL (BIT1 0))) y0) (Nat.add (dest_nadd (nadd_mul (nadd_of_num x0) x1) y0) x2).
Definition term38 (x0 : nadd) := (fun y0 : nadd => forall y1 : nat, (~ (nadd_eq y0 (nadd_of_num (NUMERAL 0)))) -> exists y2 : nat, nadd_le (nadd_of_num y1) (nadd_mul (nadd_of_num y2) y0)) x0.
Definition term125 (x0 : nat) (x1 : nadd) (x2 : nat) (x3 : nat) := S (Nat.add (Nat.mul x0 (dest_nadd x1 x2)) x3).
Definition term84 (x0 : nat) (x1 : nadd) (x2 : nat) := @eq nat ((fun y0 : nat => Nat.mul x0 (dest_nadd x1 y0)) x2).
Definition term115 (x0 : nat) (x1 : nadd) (x2 : nat) := forall y0 : nat, (fun y1 : nat => Peano.le y1 (Nat.add (Nat.mul x0 (dest_nadd x1 y1)) x2)) y0.
Definition term48 (x0 : nadd) := (fun y0 : nadd => (~ (nadd_eq y0 (nadd_of_num (NUMERAL 0)))) -> forall y1 : nat, exists y2 : nat, nadd_le (nadd_of_num y1) (nadd_mul (nadd_of_num y2) y0)) x0.
Definition term108 (x0 : nat) (x1 : nadd) (x2 : nat) := ~ (forall y0 : nat, Peano.le y0 (Nat.add (Nat.mul x0 (dest_nadd x1 y0)) x2)).
Definition term129 (x0 : nat) (x1 : nadd) (x2 : nat) (x3 : nat) := Peano.le (Nat.add (Nat.add (Nat.mul x0 (dest_nadd x1 x3)) x2) (NUMERAL (BIT1 0))) x3.
Definition term70 (x0 : nat) (x1 : nadd) (x2 : nat) := dest_nadd (nadd_of_num x0) (dest_nadd x1 x2).
Definition term60 (x0 : nat) := (fun y0 : nat => y0) x0.
Definition term101 (x0 : nadd) := imp (exists y0 : nat, nadd_le (nadd_of_num (NUMERAL (BIT1 0))) (nadd_mul (nadd_of_num y0) x0)).
Definition term77 (x0 : nat) (x1 : nadd) (x2 : nat) := Nat.mul x0 (dest_nadd x1 x2).
Definition term64 := fun y0 : nat => (fun y1 : nat => y1) y0.
Definition term43 (x0 : nat) (x1 : nadd) := exists y0 : nat, nadd_le (nadd_of_num x0) (nadd_mul (nadd_of_num y0) x1).
Definition term83 (x0 : nat) (x1 : nadd) (x2 : nat) := @eq nat ((fun y0 : nat => (fun y1 : nat => Nat.mul x0 (dest_nadd x1 y1)) y0) x2).
Definition term30 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => (dest_nadd (nadd_mul x0 y0)) = (fun y1 : nat => dest_nadd x0 (dest_nadd y0 y1))) x1.
Definition term18 (a0 : Type') (x0 : a0 -> Prop) := ~ (forall y0 : a0, x0 y0).
Definition term73 (x0 : nat) (x1 : nat) := (fun y0 : nat => Nat.mul x0 y0) x1.
Definition term59 (x0 : nat) := dest_nadd (nadd_of_num (NUMERAL (BIT1 0))) x0.
Definition term95 (x0 : nat) (x1 : nadd) := fun y0 : nat => forall y1 : nat, Peano.le (dest_nadd (nadd_of_num (NUMERAL (BIT1 0))) y1) (Nat.add (dest_nadd (nadd_mul (nadd_of_num x0) x1) y1) y0).
Definition term6 := fun y0 : nat => forall y1 : nat, (Peano.lt y0 y1) = (Peano.le (S y0) y1).
Definition term5 := fun y0 : nat => forall y1 : nat, (Peano.le (S y0) y1) = (Peano.lt y0 y1).
Definition term141 (x0 : nadd) (x1 : nat) := ((dest_nadd x0 x1) = (NUMERAL 0)) -> False.
Definition term54 := nadd_of_num (NUMERAL (BIT1 0)).
Definition term26 (x0 : nat) := dest_nadd (nadd_of_num x0).
Definition term17 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (~ (forall y1 : a0, y0 y1)) = (exists y1 : a0, ~ (y0 y1))) x0.
Definition term16 (x0 : nat) (x1 : nat) := ~ (Peano.le x0 x1).
Definition term74 (x0 : nat) := fun y0 : nat => (fun y1 : nat => Nat.mul x0 y1) y0.
Definition term136 (x0 : nat) := (fun y0 : nat => (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) x0.
Definition term80 (x0 : nat) (x1 : nadd) (x2 : nat) := (fun y0 : nat => Nat.mul x0 (dest_nadd x1 y0)) x2.
Definition term75 (x0 : nat) (x1 : nadd) (x2 : nat) := @eq nat ((fun y0 : nat => (fun y1 : nat => Nat.mul x0 y1) y0) (dest_nadd x1 x2)).
Definition term35 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => (nadd_le x0 y0) = (exists y1 : nat, forall y2 : nat, Peano.le (dest_nadd x0 y2) (Nat.add (dest_nadd y0 y2) y1))) x1.
Definition term3 (x0 : nat) := forall y0 : nat, (Peano.le (S x0) y0) = (Peano.lt x0 y0).
Definition term130 (x0 : nat) (x1 : nadd) (x2 : nat) := fun y0 : nat => Peano.le (Nat.add (Nat.add (Nat.mul x0 (dest_nadd x1 y0)) x2) (NUMERAL (BIT1 0))) y0.
Definition term56 := dest_nadd (nadd_of_num (NUMERAL (BIT1 0))).
Definition term134 (x0 : nat) := Nat.add (NUMERAL 0) x0.
Definition term61 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term128 (x0 : nat) (x1 : nadd) (x2 : nat) (x3 : nat) := Peano.le (Nat.add (Nat.add (Nat.mul x0 (dest_nadd x1 x2)) x3) (NUMERAL (BIT1 0))).
Definition term19 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0, ~ (x0 y0).
Definition term58 := fun y0 : nat => y0.
Definition term87 (x0 : nat) (x1 : nadd) (x2 : nat) (x3 : nat) := Nat.add (dest_nadd (nadd_mul (nadd_of_num x0) x1) x2) x3.
Definition term8 := forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) = (Peano.le (S y0) y1).
Definition term7 := forall y0 : nat, forall y1 : nat, (Peano.le (S y0) y1) = (Peano.lt y0 y1).
Definition term14 (x0 : nat) := forall y0 : nat, (~ (Peano.le x0 y0)) = (Peano.lt y0 x0).
Definition term29 (x0 : nadd) := forall y0 : nadd, (dest_nadd (nadd_mul x0 y0)) = (fun y1 : nat => dest_nadd x0 (dest_nadd y0 y1)).
Definition term62 (x0 : nat -> nat) (x1 : nat) := (fun y0 : nat => x0 y0) x1.
Definition term12 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt x0 y0) = (Peano.le (S x0) y0)) x1.
Definition term121 (x0 : nat) (x1 : nadd) (x2 : nat) := fun y0 : nat => ~ (Peano.le y0 (Nat.add (Nat.mul x0 (dest_nadd x1 y0)) x2)).
Definition term66 (x0 : nat) := @eq nat ((fun y0 : nat => y0) x0).
Definition term143 (x0 : nat) (x1 : nadd) (x2 : nat) := (Peano.le (Nat.add x0 (NUMERAL (BIT1 0))) x2) -> ~ ((dest_nadd x1 x2) = (NUMERAL 0)).
Definition term107 (x0 : nat) (x1 : nadd) (x2 : nat) := (forall y0 : nat, Peano.le y0 (Nat.add (Nat.mul x0 (dest_nadd x1 y0)) x2)) -> False.
Definition term28 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, (dest_nadd (nadd_mul y0 y1)) = (fun y2 : nat => dest_nadd y0 (dest_nadd y1 y2))) x0.
Definition term132 := forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0.
Definition term22 := forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0.
Definition term133 (x0 : nat) := (fun y0 : nat => (Nat.add (NUMERAL 0) y0) = y0) x0.
Definition term23 (x0 : nat) := (fun y0 : nat => (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) x0.
Definition term10 (x0 : nat) := Nat.add x0 (NUMERAL (BIT1 0)).
Definition term111 (x0 : nat) (x1 : nadd) (x2 : nat) := ~ (forall y0 : nat, (fun y1 : nat => Peano.le y1 (Nat.add (Nat.mul x0 (dest_nadd x1 y1)) x2)) y0).
Definition term4 (x0 : nat) := forall y0 : nat, (Peano.lt x0 y0) = (Peano.le (S x0) y0).
Definition term32 (x0 : nadd) (x1 : nadd) := fun y0 : nat => dest_nadd x0 (dest_nadd x1 y0).
Definition term139 (x0 : nat) (x1 : nadd) (x2 : nat) (x3 : nat) := Nat.add (Nat.add (Nat.mul x0 (dest_nadd x1 x2)) x3).
Definition term118 (x0 : nat) (x1 : nadd) (x2 : nat) (x3 : nat) := ~ ((fun y0 : nat => Peano.le y0 (Nat.add (Nat.mul x0 (dest_nadd x1 y0)) x2)) x3).
Definition term81 (x0 : nat) (x1 : nadd) (x2 : nat) := (fun y0 : nat => (fun y1 : nat => Nat.mul x0 (dest_nadd x1 y1)) y0) x2.
Definition term124 (x0 : nat) (x1 : nadd) (x2 : nat) (x3 : nat) := Peano.le (S (Nat.add (Nat.mul x0 (dest_nadd x1 x3)) x2)) x3.
Definition term40 (x0 : nadd) (x1 : nat) := (fun y0 : nat => (~ (nadd_eq x0 (nadd_of_num (NUMERAL 0)))) -> exists y1 : nat, nadd_le (nadd_of_num y0) (nadd_mul (nadd_of_num y1) x0)) x1.
Definition term63 (x0 : nat) := (fun y0 : nat => (fun y1 : nat => y1) y0) x0.
Definition term27 (x0 : nat) := fun y0 : nat => Nat.mul x0 y0.
Definition term25 (x0 : nat) := (fun y0 : nat => (dest_nadd (nadd_of_num y0)) = (fun y1 : nat => Nat.mul y0 y1)) x0.
Definition term144 (x0 : nat) (x1 : nadd) := forall y0 : nat, (Peano.le (Nat.add x0 (NUMERAL (BIT1 0))) y0) -> ~ ((dest_nadd x1 y0) = (NUMERAL 0)).
Definition term138 := Nat.add (NUMERAL 0).
Definition term45 (x0 : nadd) := (~ (nadd_eq x0 (nadd_of_num (NUMERAL 0)))) -> forall y0 : nat, exists y1 : nat, nadd_le (nadd_of_num y0) (nadd_mul (nadd_of_num y1) x0).
Definition term65 (x0 : nat) := @eq nat ((fun y0 : nat => (fun y1 : nat => y1) y0) x0).
Definition term89 (x0 : nat) (x1 : nadd) (x2 : nat) (x3 : nat) := Peano.le (dest_nadd (nadd_of_num (NUMERAL (BIT1 0))) x2) (Nat.add (dest_nadd (nadd_mul (nadd_of_num x0) x1) x2) x3).
Definition term114 (x0 : nat) (x1 : nadd) (x2 : nat) := fun y0 : nat => (fun y1 : nat => Peano.le y1 (Nat.add (Nat.mul x0 (dest_nadd x1 y1)) x2)) y0.
Definition term148 := forall y0 : nadd, (~ (nadd_eq y0 (nadd_of_num (NUMERAL 0)))) -> exists y1 : nat, forall y2 : nat, (Peano.le y1 y2) -> ~ ((dest_nadd y0 y2) = (NUMERAL 0)).
Definition term88 (x0 : nat) (x1 : nadd) (x2 : nat) (x3 : nat) := Nat.add (Nat.mul x0 (dest_nadd x1 x2)) x3.
Definition term13 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) x0.
Definition term11 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y0 y1) = (Peano.le (S y0) y1)) x0.
Definition term147 (x0 : nadd) := (~ (nadd_eq x0 (nadd_of_num (NUMERAL 0)))) -> exists y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> ~ ((dest_nadd x0 y1) = (NUMERAL 0)).
Definition term117 (x0 : nat) (x1 : nadd) (x2 : nat) := @eq Prop (~ (forall y0 : nat, Peano.le y0 (Nat.add (Nat.mul x0 (dest_nadd x1 y0)) x2))).
Definition term116 (x0 : nat) (x1 : nadd) (x2 : nat) := @eq Prop (~ (forall y0 : nat, (fun y1 : nat => Peano.le y1 (Nat.add (Nat.mul x0 (dest_nadd x1 y1)) x2)) y0)).
Definition term135 := forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0).
Definition term94 (x0 : nat) (x1 : nadd) (x2 : nat) := forall y0 : nat, Peano.le y0 (Nat.add (Nat.mul x0 (dest_nadd x1 y0)) x2).
Definition term51 (x0 : nadd) := exists y0 : nat, nadd_le (nadd_of_num (NUMERAL (BIT1 0))) (nadd_mul (nadd_of_num y0) x0).
Definition term92 (x0 : nat) (x1 : nadd) (x2 : nat) := fun y0 : nat => Peano.le y0 (Nat.add (Nat.mul x0 (dest_nadd x1 y0)) x2).
Definition term137 (x0 : nat) := Nat.mul x0 (NUMERAL 0).
Definition term91 (x0 : nat) (x1 : nadd) (x2 : nat) := fun y0 : nat => Peano.le (dest_nadd (nadd_of_num (NUMERAL (BIT1 0))) y0) (Nat.add (dest_nadd (nadd_mul (nadd_of_num x0) x1) y0) x2).
Definition term146 (x0 : nadd) := (forall y0 : nat, exists y1 : nat, nadd_le (nadd_of_num y0) (nadd_mul (nadd_of_num y1) x0)) -> exists y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> ~ ((dest_nadd x0 y1) = (NUMERAL 0)).
Definition term90 (x0 : nat) (x1 : nadd) (x2 : nat) (x3 : nat) := Peano.le x2 (Nat.add (Nat.mul x0 (dest_nadd x1 x2)) x3).
Definition term78 (x0 : nat) (x1 : nadd) := fun y0 : nat => Nat.mul x0 (dest_nadd x1 y0).
Definition term112 (x0 : nat) (x1 : nadd) (x2 : nat) := exists y0 : nat, ~ ((fun y1 : nat => Peano.le y1 (Nat.add (Nat.mul x0 (dest_nadd x1 y1)) x2)) y0).
Definition term0 (x0 : nat) (x1 : nat) := Peano.le (S x0) x1.
Definition term85 (x0 : nat) (x1 : nadd) (x2 : nat) := Nat.add (dest_nadd (nadd_mul (nadd_of_num x0) x1) x2).
Definition term41 (x0 : nat) (x1 : nadd) := (~ (nadd_eq x1 (nadd_of_num (NUMERAL 0)))) -> exists y0 : nat, nadd_le (nadd_of_num x0) (nadd_mul (nadd_of_num y0) x1).
Definition term102 (x0 : nadd) := imp (exists y0 : nat, exists y1 : nat, forall y2 : nat, Peano.le y2 (Nat.add (Nat.mul y0 (dest_nadd x0 y2)) y1)).
Definition term57 := fun y0 : nat => Nat.mul (NUMERAL (BIT1 0)) y0.
Definition term46 := forall y0 : nadd, (~ (nadd_eq y0 (nadd_of_num (NUMERAL 0)))) -> forall y1 : nat, exists y2 : nat, nadd_le (nadd_of_num y1) (nadd_mul (nadd_of_num y2) y0).
Definition term49 (x0 : nadd) := (fun y0 : nat => exists y1 : nat, nadd_le (nadd_of_num y0) (nadd_mul (nadd_of_num y1) x0)) (NUMERAL (BIT1 0)).
Definition term69 (x0 : nat) (x1 : nadd) := fun y0 : nat => dest_nadd (nadd_of_num x0) (dest_nadd x1 y0).
Definition term34 (x0 : nadd) := forall y0 : nadd, (nadd_le x0 y0) = (exists y1 : nat, forall y2 : nat, Peano.le (dest_nadd x0 y2) (Nat.add (dest_nadd y0 y2) y1)).
Definition term127 (x0 : nat) (x1 : nadd) (x2 : nat) (x3 : nat) := Peano.le (S (Nat.add (Nat.mul x0 (dest_nadd x1 x2)) x3)).
Definition term145 (x0 : nadd) := fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) -> ~ ((dest_nadd x0 y1) = (NUMERAL 0)).
Definition term122 (x0 : nat) (x1 : nadd) (x2 : nat) := exists y0 : nat, ~ (Peano.le y0 (Nat.add (Nat.mul x0 (dest_nadd x1 y0)) x2)).
Definition term109 (x0 : nat -> Prop) := ~ (forall y0 : nat, x0 y0).
Definition term142 (x0 : nadd) (x1 : nat) := ~ ((dest_nadd x0 x1) = (NUMERAL 0)).
Definition term126 (x0 : nat) (x1 : nadd) (x2 : nat) (x3 : nat) := Nat.add (Nat.add (Nat.mul x0 (dest_nadd x1 x2)) x3) (NUMERAL (BIT1 0)).
Definition term100 (x0 : nadd) := exists y0 : nat, exists y1 : nat, forall y2 : nat, Peano.le y2 (Nat.add (Nat.mul y0 (dest_nadd x0 y2)) y1).
Definition term42 (x0 : nadd) := ~ (nadd_eq x0 (nadd_of_num (NUMERAL 0))).
Definition term82 (x0 : nat) (x1 : nadd) := fun y0 : nat => (fun y1 : nat => Nat.mul x0 (dest_nadd x1 y1)) y0.
Definition term120 (x0 : nat) (x1 : nadd) (x2 : nat) := fun y0 : nat => ~ ((fun y1 : nat => Peano.le y1 (Nat.add (Nat.mul x0 (dest_nadd x1 y1)) x2)) y0).
Definition term52 (x0 : nat) (x1 : nadd) := nadd_le (nadd_of_num (NUMERAL (BIT1 0))) (nadd_mul (nadd_of_num x0) x1).
Definition term140 (x0 : nat) := Peano.le (Nat.add x0 (NUMERAL (BIT1 0))).
Definition term1 (x0 : nat) := fun y0 : nat => (Peano.le (S x0) y0) = (Peano.lt x0 y0).
Definition term15 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (Peano.le x0 y0)) = (Peano.lt y0 x0)) x1.
Definition term96 (x0 : nat) (x1 : nadd) := fun y0 : nat => forall y1 : nat, Peano.le y1 (Nat.add (Nat.mul x0 (dest_nadd x1 y1)) y0).
Definition term20 := (forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))).
Definition term119 (x0 : nat) (x1 : nadd) (x2 : nat) (x3 : nat) := ~ (Peano.le x2 (Nat.add (Nat.mul x0 (dest_nadd x1 x2)) x3)).
Definition term110 (x0 : nat -> Prop) := exists y0 : nat, ~ (x0 y0).
Definition term106 (x0 : nat) (x1 : nat) := Peano.le (Nat.add x0 (NUMERAL (BIT1 0))) x1.
Definition term98 (x0 : nadd) := fun y0 : nat => nadd_le (nadd_of_num (NUMERAL (BIT1 0))) (nadd_mul (nadd_of_num y0) x0).
Definition term76 (x0 : nat) (x1 : nadd) (x2 : nat) := @eq nat ((fun y0 : nat => Nat.mul x0 y0) (dest_nadd x1 x2)).
Definition term50 := NUMERAL (BIT1 0).
Definition term24 (x0 : nat) := Nat.mul (NUMERAL (BIT1 0)) x0.
Definition term47 := (forall y0 : nadd, forall y1 : nat, (~ (nadd_eq y0 (nadd_of_num (NUMERAL 0)))) -> exists y2 : nat, nadd_le (nadd_of_num y1) (nadd_mul (nadd_of_num y2) y0)) -> forall y0 : nadd, (~ (nadd_eq y0 (nadd_of_num (NUMERAL 0)))) -> forall y1 : nat, exists y2 : nat, nadd_le (nadd_of_num y1) (nadd_mul (nadd_of_num y2) y0).
Definition term123 (x0 : nat) (x1 : nadd) (x2 : nat) (x3 : nat) := Peano.lt (Nat.add (Nat.mul x0 (dest_nadd x1 x3)) x2) x3.
