Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term64 (x0 : nat) (x1 : real) (x2 : real -> real) := (exists y0 : nat -> real, forall y1 : real, (x2 y1) = (@sum nat (dotdot (NUMERAL 0) x0) (fun y2 : nat => real_mul (y0 y2) (real_pow y1 y2)))) -> exists y0 : nat, exists y1 : nat -> real, forall y2 : real, (real_mul x1 (x2 y2)) = (@sum nat (dotdot (NUMERAL 0) y0) (fun y3 : nat => real_mul (y1 y3) (real_pow y2 y3))).
Definition term48 (x0 : real) (x1 : real -> real) := (exists y0 : nat, exists y1 : nat -> real, forall y2 : real, (x1 y2) = (@sum nat (dotdot (NUMERAL 0) y0) (fun y3 : nat => real_mul (y1 y3) (real_pow y2 y3)))) -> exists y0 : nat, exists y1 : nat -> real, forall y2 : real, (real_mul x0 (x1 y2)) = (@sum nat (dotdot (NUMERAL 0) y0) (fun y3 : nat => real_mul (y1 y3) (real_pow y2 y3))).
Definition term63 (x0 : nat) (x1 : real) (x2 : real -> real) := ((fun y0 : nat => exists y1 : nat -> real, forall y2 : real, (x2 y2) = (@sum nat (dotdot (NUMERAL 0) y0) (fun y3 : nat => real_mul (y1 y3) (real_pow y2 y3)))) x0) -> exists y0 : nat, exists y1 : nat -> real, forall y2 : real, (real_mul x1 (x2 y2)) = (@sum nat (dotdot (NUMERAL 0) y0) (fun y3 : nat => real_mul (y1 y3) (real_pow y2 y3))).
Definition term125 (x0 : nat -> real) (x1 : real) (x2 : nat) := (fun y0 : nat => real_mul (x0 y0) (real_pow x1 y0)) x2.
Definition term127 (x0 : real) (x1 : nat -> real) (x2 : real) (x3 : nat) := real_mul x0 ((fun y0 : nat => real_mul (x1 y0) (real_pow x2 y0)) x3).
Definition term105 (x0 : real) (x1 : nat -> real) := fun y0 : nat => real_mul x0 (x1 y0).
Definition term0 (x0 : real) (x1 : real) (x2 : real) := real_mul x0 (real_mul x1 x2).
Definition term111 (x0 : real) (x1 : nat -> real) (x2 : nat) := real_mul (real_mul x0 (x1 x2)).
Definition term79 (x0 : nat) (x1 : real) (x2 : real -> real) := @eq Prop ((exists y0 : nat -> real, forall y1 : real, (x2 y1) = (@sum nat (dotdot (NUMERAL 0) x0) (fun y2 : nat => real_mul (y0 y2) (real_pow y1 y2)))) -> exists y0 : nat, exists y1 : nat -> real, forall y2 : real, (real_mul x1 (x2 y2)) = (@sum nat (dotdot (NUMERAL 0) y0) (fun y3 : nat => real_mul (y1 y3) (real_pow y2 y3)))).
Definition term78 (x0 : nat) (x1 : real) (x2 : real -> real) := @eq Prop ((exists y0 : nat -> real, (fun y1 : nat -> real => forall y2 : real, (x2 y2) = (@sum nat (dotdot (NUMERAL 0) x0) (fun y3 : nat => real_mul (y1 y3) (real_pow y2 y3)))) y0) -> exists y0 : nat, exists y1 : nat -> real, forall y2 : real, (real_mul x1 (x2 y2)) = (@sum nat (dotdot (NUMERAL 0) y0) (fun y3 : nat => real_mul (y1 y3) (real_pow y2 y3)))).
Definition term60 (x0 : real) (x1 : real -> real) := @eq Prop ((exists y0 : nat, exists y1 : nat -> real, forall y2 : real, (x1 y2) = (@sum nat (dotdot (NUMERAL 0) y0) (fun y3 : nat => real_mul (y1 y3) (real_pow y2 y3)))) -> exists y0 : nat, exists y1 : nat -> real, forall y2 : real, (real_mul x0 (x1 y2)) = (@sum nat (dotdot (NUMERAL 0) y0) (fun y3 : nat => real_mul (y1 y3) (real_pow y2 y3)))).
Definition term59 (x0 : real) (x1 : real -> real) := @eq Prop ((exists y0 : nat, (fun y1 : nat => exists y2 : nat -> real, forall y3 : real, (x1 y3) = (@sum nat (dotdot (NUMERAL 0) y1) (fun y4 : nat => real_mul (y2 y4) (real_pow y3 y4)))) y0) -> exists y0 : nat, exists y1 : nat -> real, forall y2 : real, (real_mul x0 (x1 y2)) = (@sum nat (dotdot (NUMERAL 0) y0) (fun y3 : nat => real_mul (y1 y3) (real_pow y2 y3)))).
Definition term58 (x0 : real -> real) := imp (exists y0 : nat, (fun y1 : nat => exists y2 : nat -> real, forall y3 : real, (x0 y3) = (@sum nat (dotdot (NUMERAL 0) y1) (fun y4 : nat => real_mul (y2 y4) (real_pow y3 y4)))) y0).
Definition term117 (x0 : nat) := @sum nat (dotdot (NUMERAL 0) x0).
Definition term33 (x0 : real) (x1 : real -> real) (x2 : real) := @eq real ((fun y0 : real => real_mul x0 (x1 y0)) x2).
Definition term18 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := forall y0 : a0, (x0 y0) -> x1.
Definition term32 (x0 : real) (x1 : real -> real) (x2 : real) := @eq real ((fun y0 : real => (fun y1 : real => real_mul x0 (x1 y1)) y0) x2).
Definition term135 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term132 := fun y0 : real => True.
Definition term84 (x0 : nat) (x1 : real) (x2 : real -> real) := fun y0 : nat -> real => ((fun y1 : nat -> real => forall y2 : real, (x2 y2) = (@sum nat (dotdot (NUMERAL 0) x0) (fun y3 : nat => real_mul (y1 y3) (real_pow y2 y3)))) y0) -> exists y1 : nat, exists y2 : nat -> real, forall y3 : real, (real_mul x1 (x2 y3)) = (@sum nat (dotdot (NUMERAL 0) y1) (fun y4 : nat => real_mul (y2 y4) (real_pow y3 y4))).
Definition term30 (x0 : real) (x1 : real -> real) (x2 : real) := real_mul x0 (x1 x2).
Definition term19 (x0 : real -> real) := (fun y0 : real -> real => (polynomial_function y0) = (exists y1 : nat, exists y2 : nat -> real, forall y3 : real, (y0 y3) = (@sum nat (dotdot (NUMERAL 0) y1) (fun y4 : nat => real_mul (y2 y4) (real_pow y3 y4))))) x0.
Definition term37 (x0 : real) (x1 : real -> real) (x2 : nat) (x3 : nat -> real) := fun y0 : real => (real_mul x0 (x1 y0)) = (@sum nat (dotdot (NUMERAL 0) x2) (fun y1 : nat => real_mul (x3 y1) (real_pow y0 y1))).
Definition term71 (x0 : nat) (x1 : real) (x2 : real -> real) := forall y0 : nat -> real, ((fun y1 : nat -> real => forall y2 : real, (x2 y2) = (@sum nat (dotdot (NUMERAL 0) x0) (fun y3 : nat => real_mul (y1 y3) (real_pow y2 y3)))) y0) -> exists y1 : nat, exists y2 : nat -> real, forall y3 : real, (real_mul x1 (x2 y3)) = (@sum nat (dotdot (NUMERAL 0) y1) (fun y4 : nat => real_mul (y2 y4) (real_pow y3 y4))).
Definition term92 (a0 : Type') (x0 : a0 -> real) := (fun y0 : a0 -> real => forall y1 : real, forall y2 : a0 -> Prop, (@sum a0 y2 (fun y3 : a0 => real_mul y1 (y0 y3))) = (real_mul y1 (@sum a0 y2 y0))) x0.
Definition term97 (a0 : Type') (x0 : a0 -> Prop) (x1 : real) (x2 : a0 -> real) := @sum a0 x0 (fun y0 : a0 => real_mul x1 (x2 y0)).
Definition term99 (x0 : real -> real) (x1 : nat) (x2 : nat -> real) (x3 : real) := (fun y0 : real => (x0 y0) = (@sum nat (dotdot (NUMERAL 0) x1) (fun y1 : nat => real_mul (x2 y1) (real_pow y0 y1)))) x3.
Definition term134 := forall y0 : real, True.
Definition term126 (x0 : nat -> real) (x1 : real) (x2 : nat) := real_mul (x0 x2) (real_pow x1 x2).
Definition term100 (x0 : real) (x1 : nat) (x2 : nat -> real) (x3 : real) := real_mul x0 (@sum nat (dotdot (NUMERAL 0) x1) (fun y0 : nat => real_mul (x2 y0) (real_pow x3 y0))).
Definition term136 (x0 : Prop) := forall y0 : real, x0.
Definition term96 (a0 : Type') (x0 : real) (x1 : a0 -> real) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@sum a0 y0 (fun y1 : a0 => real_mul x0 (x1 y1))) = (real_mul x0 (@sum a0 y0 x1))) x2.
Definition term116 (x0 : real) (x1 : nat -> real) (x2 : real) := fun y0 : nat => real_mul x0 (real_mul (x1 y0) (real_pow x2 y0)).
Definition term65 (x0 : real) (x1 : real -> real) := fun y0 : nat => ((fun y1 : nat => exists y2 : nat -> real, forall y3 : real, (x1 y3) = (@sum nat (dotdot (NUMERAL 0) y1) (fun y4 : nat => real_mul (y2 y4) (real_pow y3 y4)))) y0) -> exists y1 : nat, exists y2 : nat -> real, forall y3 : real, (real_mul x0 (x1 y3)) = (@sum nat (dotdot (NUMERAL 0) y1) (fun y4 : nat => real_mul (y2 y4) (real_pow y3 y4))).
Definition term70 (x0 : nat) (x1 : real) (x2 : real -> real) := (exists y0 : nat -> real, (fun y1 : nat -> real => forall y2 : real, (x2 y2) = (@sum nat (dotdot (NUMERAL 0) x0) (fun y3 : nat => real_mul (y1 y3) (real_pow y2 y3)))) y0) -> exists y0 : nat, exists y1 : nat -> real, forall y2 : real, (real_mul x1 (x2 y2)) = (@sum nat (dotdot (NUMERAL 0) y0) (fun y3 : nat => real_mul (y1 y3) (real_pow y2 y3))).
Definition term51 (x0 : real) (x1 : real -> real) := (exists y0 : nat, (fun y1 : nat => exists y2 : nat -> real, forall y3 : real, (x1 y3) = (@sum nat (dotdot (NUMERAL 0) y1) (fun y4 : nat => real_mul (y2 y4) (real_pow y3 y4)))) y0) -> exists y0 : nat, exists y1 : nat -> real, forall y2 : real, (real_mul x0 (x1 y2)) = (@sum nat (dotdot (NUMERAL 0) y0) (fun y3 : nat => real_mul (y1 y3) (real_pow y2 y3))).
Definition term25 (x0 : real) (x1 : real -> real) := fun y0 : real => real_mul x0 (x1 y0).
Definition term34 (x0 : real) (x1 : real -> real) (x2 : real) := @eq real (real_mul x0 (x1 x2)).
Definition term93 (a0 : Type') (x0 : a0 -> real) := forall y0 : real, forall y1 : a0 -> Prop, (@sum a0 y1 (fun y2 : a0 => real_mul y0 (x0 y2))) = (real_mul y0 (@sum a0 y1 x0)).
Definition term13 := forall y0 : real, forall y1 : real, forall y2 : real, (real_mul (real_mul y0 y1) y2) = (real_mul y0 (real_mul y1 y2)).
Definition term12 := forall y0 : real, forall y1 : real, forall y2 : real, (real_mul y0 (real_mul y1 y2)) = (real_mul (real_mul y0 y1) y2).
Definition term9 (x0 : real) := forall y0 : real, forall y1 : real, (real_mul (real_mul x0 y0) y1) = (real_mul x0 (real_mul y0 y1)).
Definition term8 (x0 : real) := forall y0 : real, forall y1 : real, (real_mul x0 (real_mul y0 y1)) = (real_mul (real_mul x0 y0) y1).
Definition term55 (x0 : real -> real) (x1 : nat) := exists y0 : nat -> real, forall y1 : real, (x0 y1) = (@sum nat (dotdot (NUMERAL 0) x1) (fun y2 : nat => real_mul (y0 y2) (real_pow y1 y2))).
Definition term43 (x0 : real) (x1 : real -> real) (x2 : nat) := exists y0 : nat -> real, forall y1 : real, (real_mul x0 (x1 y1)) = (@sum nat (dotdot (NUMERAL 0) x2) (fun y2 : nat => real_mul (y0 y2) (real_pow y1 y2))).
Definition term42 (x0 : real) (x1 : real -> real) (x2 : nat) := exists y0 : nat -> real, forall y1 : real, ((fun y2 : real => real_mul x0 (x1 y2)) y1) = (@sum nat (dotdot (NUMERAL 0) x2) (fun y2 : nat => real_mul (y0 y2) (real_pow y1 y2))).
Definition term130 (x0 : nat) (x1 : real) (x2 : nat -> real) (x3 : real) := @eq real (@sum nat (dotdot (NUMERAL 0) x0) (fun y0 : nat => real_mul x1 (real_mul (x2 y0) (real_pow x3 y0)))).
Definition term129 (x0 : nat) (x1 : real) (x2 : nat -> real) (x3 : real) := @eq real (@sum nat (dotdot (NUMERAL 0) x0) (fun y0 : nat => real_mul x1 ((fun y1 : nat => real_mul (x2 y1) (real_pow x3 y1)) y0))).
Definition term56 (x0 : real -> real) := fun y0 : nat => (fun y1 : nat => exists y2 : nat -> real, forall y3 : real, (x0 y3) = (@sum nat (dotdot (NUMERAL 0) y1) (fun y4 : nat => real_mul (y2 y4) (real_pow y3 y4)))) y0.
Definition term124 (x0 : nat -> real) (x1 : real) := fun y0 : nat => real_mul (x0 y0) (real_pow x1 y0).
Definition term5 (x0 : real) (x1 : real) := forall y0 : real, (real_mul (real_mul x0 x1) y0) = (real_mul x0 (real_mul x1 y0)).
Definition term104 (x0 : real) (x1 : nat -> real) (x2 : nat) := (fun y0 : nat => real_mul x0 (x1 y0)) x2.
Definition term36 (x0 : real) (x1 : real -> real) (x2 : nat) (x3 : nat -> real) := fun y0 : real => ((fun y1 : real => real_mul x0 (x1 y1)) y0) = (@sum nat (dotdot (NUMERAL 0) x2) (fun y1 : nat => real_mul (x3 y1) (real_pow y0 y1))).
Definition term31 (x0 : real) (x1 : real -> real) := fun y0 : real => (fun y1 : real => real_mul x0 (x1 y1)) y0.
Definition term86 (x0 : nat) (x1 : real) (x2 : real -> real) := forall y0 : nat -> real, (forall y1 : real, (x2 y1) = (@sum nat (dotdot (NUMERAL 0) x0) (fun y2 : nat => real_mul (y0 y2) (real_pow y1 y2)))) -> exists y1 : nat, exists y2 : nat -> real, forall y3 : real, (real_mul x1 (x2 y3)) = (@sum nat (dotdot (NUMERAL 0) y1) (fun y4 : nat => real_mul (y2 y4) (real_pow y3 y4))).
Definition term83 (x0 : nat) (x1 : nat -> real) (x2 : real) (x3 : real -> real) := (forall y0 : real, (x3 y0) = (@sum nat (dotdot (NUMERAL 0) x0) (fun y1 : nat => real_mul (x1 y1) (real_pow y0 y1)))) -> exists y0 : nat, exists y1 : nat -> real, forall y2 : real, (real_mul x2 (x3 y2)) = (@sum nat (dotdot (NUMERAL 0) y0) (fun y3 : nat => real_mul (y1 y3) (real_pow y2 y3))).
Definition term87 (x0 : real) (x1 : real -> real) := fun y0 : nat => forall y1 : nat -> real, (forall y2 : real, (x1 y2) = (@sum nat (dotdot (NUMERAL 0) y0) (fun y3 : nat => real_mul (y1 y3) (real_pow y2 y3)))) -> exists y2 : nat, exists y3 : nat -> real, forall y4 : real, (real_mul x0 (x1 y4)) = (@sum nat (dotdot (NUMERAL 0) y2) (fun y5 : nat => real_mul (y3 y5) (real_pow y4 y5))).
Definition term107 (x0 : real) (x1 : nat -> real) := fun y0 : nat => (fun y1 : nat => real_mul x0 (x1 y1)) y0.
Definition term3 (x0 : real) (x1 : real) := fun y0 : real => (real_mul (real_mul x0 x1) y0) = (real_mul x0 (real_mul x1 y0)).
Definition term106 (x0 : real) (x1 : nat -> real) (x2 : nat) := real_mul x0 (x1 x2).
Definition term128 (x0 : real) (x1 : nat -> real) (x2 : real) := fun y0 : nat => real_mul x0 ((fun y1 : nat => real_mul (x1 y1) (real_pow x2 y1)) y0).
Definition term7 (x0 : real) := fun y0 : real => forall y1 : real, (real_mul (real_mul x0 y0) y1) = (real_mul x0 (real_mul y0 y1)).
Definition term52 (x0 : real) (x1 : real -> real) := forall y0 : nat, ((fun y1 : nat => exists y2 : nat -> real, forall y3 : real, (x1 y3) = (@sum nat (dotdot (NUMERAL 0) y1) (fun y4 : nat => real_mul (y2 y4) (real_pow y3 y4)))) y0) -> exists y1 : nat, exists y2 : nat -> real, forall y3 : real, (real_mul x0 (x1 y3)) = (@sum nat (dotdot (NUMERAL 0) y1) (fun y4 : nat => real_mul (y2 y4) (real_pow y3 y4))).
Definition term74 (x0 : real -> real) (x1 : nat) (x2 : nat -> real) := forall y0 : real, (x0 y0) = (@sum nat (dotdot (NUMERAL 0) x1) (fun y1 : nat => real_mul (x2 y1) (real_pow y0 y1))).
Definition term76 (x0 : real -> real) (x1 : nat) := exists y0 : nat -> real, (fun y1 : nat -> real => forall y2 : real, (x0 y2) = (@sum nat (dotdot (NUMERAL 0) x1) (fun y3 : nat => real_mul (y1 y3) (real_pow y2 y3)))) y0.
Definition term4 (x0 : real) (x1 : real) := forall y0 : real, (real_mul x0 (real_mul x1 y0)) = (real_mul (real_mul x0 x1) y0).
Definition term121 (x0 : real) (x1 : nat -> Prop) (x2 : nat -> real) := real_mul x0 (@sum nat x1 x2).
Definition term98 (a0 : Type') (x0 : real) (x1 : a0 -> Prop) (x2 : a0 -> real) := real_mul x0 (@sum a0 x1 x2).
Definition term16 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (fun y0 : Prop => ((exists y1 : a0, x0 y1) -> y0) = (forall y1 : a0, (x0 y1) -> y0)) x1.
Definition term66 (x0 : real) (x1 : real -> real) := fun y0 : nat => (exists y1 : nat -> real, forall y2 : real, (x1 y2) = (@sum nat (dotdot (NUMERAL 0) y0) (fun y3 : nat => real_mul (y1 y3) (real_pow y2 y3)))) -> exists y1 : nat, exists y2 : nat -> real, forall y3 : real, (real_mul x0 (x1 y3)) = (@sum nat (dotdot (NUMERAL 0) y1) (fun y4 : nat => real_mul (y2 y4) (real_pow y3 y4))).
Definition term75 (x0 : real -> real) (x1 : nat) := fun y0 : nat -> real => (fun y1 : nat -> real => forall y2 : real, (x0 y2) = (@sum nat (dotdot (NUMERAL 0) x1) (fun y3 : nat => real_mul (y1 y3) (real_pow y2 y3)))) y0.
Definition term26 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term67 (x0 : real) (x1 : real -> real) := forall y0 : nat, (exists y1 : nat -> real, forall y2 : real, (x1 y2) = (@sum nat (dotdot (NUMERAL 0) y0) (fun y3 : nat => real_mul (y1 y3) (real_pow y2 y3)))) -> exists y1 : nat, exists y2 : nat -> real, forall y3 : real, (real_mul x0 (x1 y3)) = (@sum nat (dotdot (NUMERAL 0) y1) (fun y4 : nat => real_mul (y2 y4) (real_pow y3 y4))).
Definition term88 (x0 : real) (x1 : real -> real) := forall y0 : nat, forall y1 : nat -> real, (forall y2 : real, (x1 y2) = (@sum nat (dotdot (NUMERAL 0) y0) (fun y3 : nat => real_mul (y1 y3) (real_pow y2 y3)))) -> exists y2 : nat, exists y3 : nat -> real, forall y4 : real, (real_mul x0 (x1 y4)) = (@sum nat (dotdot (NUMERAL 0) y2) (fun y5 : nat => real_mul (y3 y5) (real_pow y4 y5))).
Definition term119 (x0 : nat) (x1 : real) (x2 : nat -> real) (x3 : real) := @sum nat (dotdot (NUMERAL 0) x0) (fun y0 : nat => real_mul x1 (real_mul (x2 y0) (real_pow x3 y0))).
Definition term73 (x0 : real -> real) (x1 : nat) (x2 : nat -> real) := (fun y0 : nat -> real => forall y1 : real, (x0 y1) = (@sum nat (dotdot (NUMERAL 0) x1) (fun y2 : nat => real_mul (y0 y2) (real_pow y1 y2)))) x2.
Definition term108 (x0 : real) (x1 : nat -> real) (x2 : nat) := @eq real ((fun y0 : nat => (fun y1 : nat => real_mul x0 (x1 y1)) y0) x2).
Definition term102 (x0 : nat -> real) (x1 : nat) := (fun y0 : nat => x0 y0) x1.
Definition term101 (x0 : real) (x1 : nat) (x2 : nat -> real) (x3 : real) := @eq real (real_mul x0 (@sum nat (dotdot (NUMERAL 0) x1) (fun y0 : nat => real_mul (x2 y0) (real_pow x3 y0)))).
Definition term27 (x0 : real -> real) (x1 : real) := (fun y0 : real => x0 y0) x1.
Definition term6 (x0 : real) := fun y0 : real => forall y1 : real, (real_mul x0 (real_mul y0 y1)) = (real_mul (real_mul x0 y0) y1).
Definition term137 (x0 : real -> real) := forall y0 : real, (polynomial_function x0) -> polynomial_function (fun y1 : real => real_mul y0 (x0 y1)).
Definition term68 (x0 : type1010) (x1 : Prop) := (exists y0 : nat -> real, x0 y0) -> x1.
Definition term49 (x0 : nat -> Prop) (x1 : Prop) := (exists y0 : nat, x0 y0) -> x1.
Definition term80 (x0 : real -> real) (x1 : nat) (x2 : nat -> real) := imp ((fun y0 : nat -> real => forall y1 : real, (x0 y1) = (@sum nat (dotdot (NUMERAL 0) x1) (fun y2 : nat => real_mul (y0 y2) (real_pow y1 y2)))) x2).
Definition term14 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : Prop, ((exists y2 : a0, y0 y2) -> y1) = (forall y2 : a0, (y0 y2) -> y1)) x0.
Definition term53 (x0 : real -> real) := fun y0 : nat => exists y1 : nat -> real, forall y2 : real, (x0 y2) = (@sum nat (dotdot (NUMERAL 0) y0) (fun y3 : nat => real_mul (y1 y3) (real_pow y2 y3))).
Definition term45 (x0 : real) (x1 : real -> real) := fun y0 : nat => exists y1 : nat -> real, forall y2 : real, (real_mul x0 (x1 y2)) = (@sum nat (dotdot (NUMERAL 0) y0) (fun y3 : nat => real_mul (y1 y3) (real_pow y2 y3))).
Definition term44 (x0 : real) (x1 : real -> real) := fun y0 : nat => exists y1 : nat -> real, forall y2 : real, ((fun y3 : real => real_mul x0 (x1 y3)) y2) = (@sum nat (dotdot (NUMERAL 0) y0) (fun y3 : nat => real_mul (y1 y3) (real_pow y2 y3))).
Definition term77 (x0 : real -> real) (x1 : nat) := imp (exists y0 : nat -> real, (fun y1 : nat -> real => forall y2 : real, (x0 y2) = (@sum nat (dotdot (NUMERAL 0) x1) (fun y3 : nat => real_mul (y1 y3) (real_pow y2 y3)))) y0).
Definition term109 (x0 : real) (x1 : nat -> real) (x2 : nat) := @eq real ((fun y0 : nat => real_mul x0 (x1 y0)) x2).
Definition term123 (x0 : nat) := dotdot (NUMERAL 0) x0.
Definition term103 (x0 : real) (x1 : nat -> real) (x2 : nat) := (fun y0 : nat => (fun y1 : nat => real_mul x0 (x1 y1)) y0) x2.
Definition term61 (x0 : real -> real) (x1 : nat) := imp ((fun y0 : nat => exists y1 : nat -> real, forall y2 : real, (x0 y2) = (@sum nat (dotdot (NUMERAL 0) y0) (fun y3 : nat => real_mul (y1 y3) (real_pow y2 y3)))) x1).
Definition term50 (x0 : nat -> Prop) (x1 : Prop) := forall y0 : nat, (x0 y0) -> x1.
Definition term133 (x0 : real -> real) (x1 : nat) (x2 : real) (x3 : nat -> real) := forall y0 : real, (real_mul x2 (x0 y0)) = (@sum nat (dotdot (NUMERAL 0) x1) (fun y1 : nat => real_mul ((fun y2 : nat => real_mul x2 (x3 y2)) y1) (real_pow y0 y1))).
Definition term39 (x0 : real) (x1 : real -> real) (x2 : nat) (x3 : nat -> real) := forall y0 : real, (real_mul x0 (x1 y0)) = (@sum nat (dotdot (NUMERAL 0) x2) (fun y1 : nat => real_mul (x3 y1) (real_pow y0 y1))).
Definition term94 (a0 : Type') (x0 : a0 -> real) (x1 : real) := (fun y0 : real => forall y1 : a0 -> Prop, (@sum a0 y1 (fun y2 : a0 => real_mul y0 (x0 y2))) = (real_mul y0 (@sum a0 y1 x0))) x1.
Definition term90 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, (real_mul (real_mul x0 y0) y1) = (real_mul x0 (real_mul y0 y1))) x1.
Definition term85 (x0 : nat) (x1 : real) (x2 : real -> real) := fun y0 : nat -> real => (forall y1 : real, (x2 y1) = (@sum nat (dotdot (NUMERAL 0) x0) (fun y2 : nat => real_mul (y0 y2) (real_pow y1 y2)))) -> exists y1 : nat, exists y2 : nat -> real, forall y3 : real, (real_mul x1 (x2 y3)) = (@sum nat (dotdot (NUMERAL 0) y1) (fun y4 : nat => real_mul (y2 y4) (real_pow y3 y4))).
Definition term138 := forall y0 : real -> real, forall y1 : real, (polynomial_function y0) -> polynomial_function (fun y2 : real => real_mul y1 (y0 y2)).
Definition term15 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : Prop, ((exists y1 : a0, x0 y1) -> y0) = (forall y1 : a0, (x0 y1) -> y0).
Definition term110 (x0 : real) (x1 : nat -> real) (x2 : nat) := real_mul ((fun y0 : nat => real_mul x0 (x1 y0)) x2).
Definition term11 := fun y0 : real => forall y1 : real, forall y2 : real, (real_mul (real_mul y0 y1) y2) = (real_mul y0 (real_mul y1 y2)).
Definition term10 := fun y0 : real => forall y1 : real, forall y2 : real, (real_mul y0 (real_mul y1 y2)) = (real_mul (real_mul y0 y1) y2).
Definition term114 (x0 : real) (x1 : nat -> real) (x2 : real) (x3 : nat) := real_mul x0 (real_mul (x1 x3) (real_pow x2 x3)).
Definition term29 (x0 : real) (x1 : real -> real) (x2 : real) := (fun y0 : real => real_mul x0 (x1 y0)) x2.
Definition term91 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => (real_mul (real_mul x0 x1) y0) = (real_mul x0 (real_mul x1 y0))) x2.
Definition term131 (x0 : real -> real) (x1 : nat) (x2 : real) (x3 : nat -> real) := fun y0 : real => (real_mul x2 (x0 y0)) = (@sum nat (dotdot (NUMERAL 0) x1) (fun y1 : nat => real_mul ((fun y2 : nat => real_mul x2 (x3 y2)) y1) (real_pow y0 y1))).
Definition term120 (x0 : nat -> Prop) (x1 : real) (x2 : nat -> real) := @sum nat x0 (fun y0 : nat => real_mul x1 (x2 y0)).
Definition term17 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) -> x1.
Definition term1 (x0 : real) (x1 : real) (x2 : real) := real_mul (real_mul x0 x1) x2.
Definition term22 (x0 : real -> real) := imp (exists y0 : nat, exists y1 : nat -> real, forall y2 : real, (x0 y2) = (@sum nat (dotdot (NUMERAL 0) y0) (fun y3 : nat => real_mul (y1 y3) (real_pow y2 y3)))).
Definition term81 (x0 : real -> real) (x1 : nat) (x2 : nat -> real) := imp (forall y0 : real, (x0 y0) = (@sum nat (dotdot (NUMERAL 0) x1) (fun y1 : nat => real_mul (x2 y1) (real_pow y0 y1)))).
Definition term115 (x0 : real) (x1 : nat -> real) (x2 : real) := fun y0 : nat => real_mul ((fun y1 : nat => real_mul x0 (x1 y1)) y0) (real_pow x2 y0).
Definition term2 (x0 : real) (x1 : real) := fun y0 : real => (real_mul x0 (real_mul x1 y0)) = (real_mul (real_mul x0 x1) y0).
Definition term47 (x0 : real) (x1 : real -> real) := (polynomial_function x1) -> polynomial_function (fun y0 : real => real_mul x0 (x1 y0)).
Definition term112 (x0 : real) (x1 : nat -> real) (x2 : real) (x3 : nat) := real_mul ((fun y0 : nat => real_mul x0 (x1 y0)) x3) (real_pow x2 x3).
Definition term57 (x0 : real -> real) := exists y0 : nat, (fun y1 : nat => exists y2 : nat -> real, forall y3 : real, (x0 y3) = (@sum nat (dotdot (NUMERAL 0) y1) (fun y4 : nat => real_mul (y2 y4) (real_pow y3 y4)))) y0.
Definition term46 (x0 : real) (x1 : real -> real) := exists y0 : nat, exists y1 : nat -> real, forall y2 : real, (real_mul x0 (x1 y2)) = (@sum nat (dotdot (NUMERAL 0) y0) (fun y3 : nat => real_mul (y1 y3) (real_pow y2 y3))).
Definition term24 (x0 : real) (x1 : real -> real) := exists y0 : nat, exists y1 : nat -> real, forall y2 : real, ((fun y3 : real => real_mul x0 (x1 y3)) y2) = (@sum nat (dotdot (NUMERAL 0) y0) (fun y3 : nat => real_mul (y1 y3) (real_pow y2 y3))).
Definition term20 (x0 : real -> real) := exists y0 : nat, exists y1 : nat -> real, forall y2 : real, (x0 y2) = (@sum nat (dotdot (NUMERAL 0) y0) (fun y3 : nat => real_mul (y1 y3) (real_pow y2 y3))).
Definition term122 (x0 : nat) (x1 : real) (x2 : nat -> real) (x3 : real) := @sum nat (dotdot (NUMERAL 0) x0) (fun y0 : nat => real_mul x1 ((fun y1 : nat => real_mul (x2 y1) (real_pow x3 y1)) y0)).
Definition term69 (x0 : type1010) (x1 : Prop) := forall y0 : nat -> real, (x0 y0) -> x1.
Definition term21 (x0 : real -> real) := imp (polynomial_function x0).
Definition term118 (x0 : nat) (x1 : real) (x2 : nat -> real) (x3 : real) := @sum nat (dotdot (NUMERAL 0) x0) (fun y0 : nat => real_mul ((fun y1 : nat => real_mul x1 (x2 y1)) y0) (real_pow x3 y0)).
Definition term35 (x0 : nat) (x1 : nat -> real) (x2 : real) := @sum nat (dotdot (NUMERAL 0) x0) (fun y0 : nat => real_mul (x1 y0) (real_pow x2 y0)).
Definition term72 (x0 : real -> real) (x1 : nat) := fun y0 : nat -> real => forall y1 : real, (x0 y1) = (@sum nat (dotdot (NUMERAL 0) x1) (fun y2 : nat => real_mul (y0 y2) (real_pow y1 y2))).
Definition term41 (x0 : real) (x1 : real -> real) (x2 : nat) := fun y0 : nat -> real => forall y1 : real, (real_mul x0 (x1 y1)) = (@sum nat (dotdot (NUMERAL 0) x2) (fun y2 : nat => real_mul (y0 y2) (real_pow y1 y2))).
Definition term40 (x0 : real) (x1 : real -> real) (x2 : nat) := fun y0 : nat -> real => forall y1 : real, ((fun y2 : real => real_mul x0 (x1 y2)) y1) = (@sum nat (dotdot (NUMERAL 0) x2) (fun y2 : nat => real_mul (y0 y2) (real_pow y1 y2))).
Definition term113 (x0 : real) (x1 : nat -> real) (x2 : real) (x3 : nat) := real_mul (real_mul x0 (x1 x3)) (real_pow x2 x3).
Definition term62 (x0 : real -> real) (x1 : nat) := imp (exists y0 : nat -> real, forall y1 : real, (x0 y1) = (@sum nat (dotdot (NUMERAL 0) x1) (fun y2 : nat => real_mul (y0 y2) (real_pow y1 y2)))).
Definition term89 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, (real_mul (real_mul y0 y1) y2) = (real_mul y0 (real_mul y1 y2))) x0.
Definition term95 (a0 : Type') (x0 : real) (x1 : a0 -> real) := forall y0 : a0 -> Prop, (@sum a0 y0 (fun y1 : a0 => real_mul x0 (x1 y1))) = (real_mul x0 (@sum a0 y0 x1)).
Definition term28 (x0 : real) (x1 : real -> real) (x2 : real) := (fun y0 : real => (fun y1 : real => real_mul x0 (x1 y1)) y0) x2.
Definition term38 (x0 : real) (x1 : real -> real) (x2 : nat) (x3 : nat -> real) := forall y0 : real, ((fun y1 : real => real_mul x0 (x1 y1)) y0) = (@sum nat (dotdot (NUMERAL 0) x2) (fun y1 : nat => real_mul (x3 y1) (real_pow y0 y1))).
Definition term54 (x0 : real -> real) (x1 : nat) := (fun y0 : nat => exists y1 : nat -> real, forall y2 : real, (x0 y2) = (@sum nat (dotdot (NUMERAL 0) y0) (fun y3 : nat => real_mul (y1 y3) (real_pow y2 y3)))) x1.
Definition term23 (x0 : real) (x1 : real -> real) := polynomial_function (fun y0 : real => real_mul x0 (x1 y0)).
Definition term82 (x0 : nat) (x1 : nat -> real) (x2 : real) (x3 : real -> real) := ((fun y0 : nat -> real => forall y1 : real, (x3 y1) = (@sum nat (dotdot (NUMERAL 0) x0) (fun y2 : nat => real_mul (y0 y2) (real_pow y1 y2)))) x1) -> exists y0 : nat, exists y1 : nat -> real, forall y2 : real, (real_mul x2 (x3 y2)) = (@sum nat (dotdot (NUMERAL 0) y0) (fun y3 : nat => real_mul (y1 y3) (real_pow y2 y3))).
