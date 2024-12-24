Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term7 (x0 : real -> real) := forall y0 : nat, (polynomial_function x0) -> (fun y1 : nat => polynomial_function (fun y2 : real => real_pow (x0 y2) y1)) y0.
Definition term68 (x0 : real -> real) (x1 : real) (x2 : nat) := real_mul (x0 x1) (real_pow (x0 x1) x2).
Definition term47 (x0 : real -> real) := imp ((polynomial_function (fun y0 : real => real_pow (x0 y0) (NUMERAL 0))) /\ (forall y0 : nat, (polynomial_function (fun y1 : real => real_pow (x0 y1) y0)) -> polynomial_function (fun y1 : real => real_pow (x0 y1) (S y0)))).
Definition term49 (x0 : real) := (fun y0 : real => polynomial_function (fun y1 : real => y0)) x0.
Definition term15 (x0 : real -> real) := fun y0 : nat => (polynomial_function x0) -> (fun y1 : nat => polynomial_function (fun y2 : real => real_pow (x0 y2) y1)) y0.
Definition term63 (x0 : real) := forall y0 : nat, (real_pow x0 (S y0)) = (real_mul x0 (real_pow x0 y0)).
Definition term31 (x0 : real -> real) := polynomial_function (fun y0 : real => real_pow (x0 y0) (NUMERAL 0)).
Definition term66 (x0 : real) (x1 : nat) := real_mul x0 (real_pow x0 x1).
Definition term50 (x0 : real) := polynomial_function (fun y0 : real => x0).
Definition term83 (x0 : real -> real) (x1 : nat) := imp ((polynomial_function x0) /\ (polynomial_function (fun y0 : real => real_pow (x0 y0) x1))).
Definition term65 (x0 : real) (x1 : nat) := real_pow x0 (S x1).
Definition term36 (x0 : real -> real) (x1 : nat) := (fun y0 : nat => polynomial_function (fun y1 : real => real_pow (x0 y1) y0)) (S x1).
Definition term2 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (forall y1 : a0, x0 -> y0 y1) = (x0 -> forall y1 : a0, y0 y1)) x1.
Definition term64 (x0 : real) (x1 : nat) := (fun y0 : nat => (real_pow x0 (S y0)) = (real_mul x0 (real_pow x0 y0))) x1.
Definition term62 (x0 : real -> real) (x1 : real -> real) := polynomial_function (fun y0 : real => real_mul (x0 y0) (x1 y0)).
Definition term29 (x0 : real -> real) := (((fun y0 : nat => polynomial_function (fun y1 : real => real_pow (x0 y1) y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => polynomial_function (fun y2 : real => real_pow (x0 y2) y1)) y0) -> (fun y1 : nat => polynomial_function (fun y2 : real => real_pow (x0 y2) y1)) (S y0))) -> forall y0 : nat, (fun y1 : nat => polynomial_function (fun y2 : real => real_pow (x0 y2) y1)) y0.
Definition term43 (x0 : real -> real) := forall y0 : nat, (polynomial_function (fun y1 : real => real_pow (x0 y1) y0)) -> polynomial_function (fun y1 : real => real_pow (x0 y1) (S y0)).
Definition term51 (x0 : real) := real_pow x0 (NUMERAL 0).
Definition term28 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term30 (x0 : real -> real) := (fun y0 : nat => polynomial_function (fun y1 : real => real_pow (x0 y1) y0)) (NUMERAL 0).
Definition term19 (x0 : real -> real) := @eq Prop (forall y0 : nat, (polynomial_function x0) -> polynomial_function (fun y1 : real => real_pow (x0 y1) y0)).
Definition term18 (x0 : real -> real) := @eq Prop (forall y0 : nat, (polynomial_function x0) -> (fun y1 : nat => polynomial_function (fun y2 : real => real_pow (x0 y2) y1)) y0).
Definition term46 (x0 : real -> real) := imp (((fun y0 : nat => polynomial_function (fun y1 : real => real_pow (x0 y1) y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => polynomial_function (fun y2 : real => real_pow (x0 y2) y1)) y0) -> (fun y1 : nat => polynomial_function (fun y2 : real => real_pow (x0 y2) y1)) (S y0))).
Definition term11 (x0 : real -> real) (x1 : nat) := polynomial_function (fun y0 : real => real_pow (x0 y0) x1).
Definition term84 (x0 : real -> real) (x1 : nat) := ((polynomial_function x0) /\ (polynomial_function (fun y0 : real => real_pow (x0 y0) x1))) -> (polynomial_function (fun y0 : real => real_mul (x0 y0) (real_pow (x0 y0) x1))) = True.
Definition term73 (x0 : real -> real) (x1 : nat) := ((polynomial_function x0) /\ (polynomial_function (fun y0 : real => real_pow (x0 y0) x1))) -> (polynomial_function (fun y0 : real => real_mul (x0 y0) ((fun y1 : real => real_pow (x0 y1) x1) y0))) = True.
Definition term60 (x0 : real -> real) (x1 : real -> real) := ((polynomial_function x0) /\ (polynomial_function x1)) -> polynomial_function (fun y0 : real => real_mul (x0 y0) (x1 y0)).
Definition term13 (x0 : real -> real) (x1 : nat) := (polynomial_function x0) -> (fun y0 : nat => polynomial_function (fun y1 : real => real_pow (x0 y1) y0)) x1.
Definition term56 := polynomial_function (fun y0 : real => real_of_num (NUMERAL (BIT1 0))).
Definition term71 (x0 : real -> real) (x1 : nat) := polynomial_function (fun y0 : real => real_mul (x0 y0) (real_pow (x0 y0) x1)).
Definition term42 (x0 : real -> real) := forall y0 : nat, ((fun y1 : nat => polynomial_function (fun y2 : real => real_pow (x0 y2) y1)) y0) -> (fun y1 : nat => polynomial_function (fun y2 : real => real_pow (x0 y2) y1)) (S y0).
Definition term3 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := forall y0 : a0, x0 -> x1 y0.
Definition term0 (a0 : Type') (x0 : Prop) := (fun y0 : Prop => forall y1 : a0 -> Prop, (forall y2 : a0, y0 -> y1 y2) = (y0 -> forall y2 : a0, y1 y2)) x0.
Definition term72 (x0 : real -> real) (x1 : real -> real) := ((polynomial_function x0) /\ (polynomial_function x1)) -> (polynomial_function (fun y0 : real => real_mul (x0 y0) (x1 y0))) = True.
Definition term61 (x0 : real -> real) (x1 : real -> real) := (polynomial_function x0) /\ (polynomial_function x1).
Definition term57 (x0 : real -> real) := (fun y0 : real -> real => forall y1 : real -> real, ((polynomial_function y0) /\ (polynomial_function y1)) -> polynomial_function (fun y2 : real => real_mul (y0 y2) (y1 y2))) x0.
Definition term48 (x0 : real -> real) := ((polynomial_function (fun y0 : real => real_pow (x0 y0) (NUMERAL 0))) /\ (forall y0 : nat, (polynomial_function (fun y1 : real => real_pow (x0 y1) y0)) -> polynomial_function (fun y1 : real => real_pow (x0 y1) (S y0)))) -> forall y0 : nat, polynomial_function (fun y1 : real => real_pow (x0 y1) y0).
Definition term1 (a0 : Type') (x0 : Prop) := forall y0 : a0 -> Prop, (forall y1 : a0, x0 -> y0 y1) = (x0 -> forall y1 : a0, y0 y1).
Definition term53 (x0 : real -> real) (x1 : real) := real_pow (x0 x1) (NUMERAL 0).
Definition term58 (x0 : real -> real) := forall y0 : real -> real, ((polynomial_function x0) /\ (polynomial_function y0)) -> polynomial_function (fun y1 : real => real_mul (x0 y1) (y0 y1)).
Definition term8 (x0 : real -> real) := (polynomial_function x0) -> forall y0 : nat, (fun y1 : nat => polynomial_function (fun y2 : real => real_pow (x0 y2) y1)) y0.
Definition term24 := fun y0 : real -> real => forall y1 : nat, (polynomial_function y0) -> polynomial_function (fun y2 : real => real_pow (y0 y2) y1).
Definition term45 (x0 : real -> real) := (polynomial_function (fun y0 : real => real_pow (x0 y0) (NUMERAL 0))) /\ (forall y0 : nat, (polynomial_function (fun y1 : real => real_pow (x0 y1) y0)) -> polynomial_function (fun y1 : real => real_pow (x0 y1) (S y0))).
Definition term32 (x0 : real -> real) := and ((fun y0 : nat => polynomial_function (fun y1 : real => real_pow (x0 y1) y0)) (NUMERAL 0)).
Definition term27 := forall y0 : real -> real, (polynomial_function y0) -> forall y1 : nat, polynomial_function (fun y2 : real => real_pow (y0 y2) y1).
Definition term4 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 -> forall y0 : a0, x1 y0.
Definition term82 (x0 : real -> real) (x1 : nat) := @eq Prop (polynomial_function (fun y0 : real => real_mul (x0 y0) (real_pow (x0 y0) x1))).
Definition term81 (x0 : real -> real) (x1 : nat) := @eq Prop (polynomial_function (fun y0 : real => real_mul (x0 y0) ((fun y1 : real => real_pow (x0 y1) x1) y0))).
Definition term77 (x0 : real -> real) (x1 : real) := real_mul (x0 x1).
Definition term59 (x0 : real -> real) (x1 : real -> real) := (fun y0 : real -> real => ((polynomial_function x0) /\ (polynomial_function y0)) -> polynomial_function (fun y1 : real => real_mul (x0 y1) (y0 y1))) x1.
Definition term22 (x0 : real -> real) := forall y0 : nat, polynomial_function (fun y1 : real => real_pow (x0 y1) y0).
Definition term80 (x0 : real -> real) (x1 : nat) := polynomial_function (fun y0 : real => real_mul (x0 y0) ((fun y1 : real => real_pow (x0 y1) x1) y0)).
Definition term74 (x0 : real -> real) (x1 : nat) := fun y0 : real => real_pow (x0 y0) x1.
Definition term34 (x0 : real -> real) (x1 : nat) := imp ((fun y0 : nat => polynomial_function (fun y1 : real => real_pow (x0 y1) y0)) x1).
Definition term17 (x0 : real -> real) := forall y0 : nat, (polynomial_function x0) -> polynomial_function (fun y1 : real => real_pow (x0 y1) y0).
Definition term67 (x0 : real -> real) (x1 : real) (x2 : nat) := real_pow (x0 x1) (S x2).
Definition term10 (x0 : real -> real) (x1 : nat) := (fun y0 : nat => polynomial_function (fun y1 : real => real_pow (x0 y1) y0)) x1.
Definition term20 (x0 : real -> real) := fun y0 : nat => (fun y1 : nat => polynomial_function (fun y2 : real => real_pow (x0 y2) y1)) y0.
Definition term55 := fun y0 : real => real_of_num (NUMERAL (BIT1 0)).
Definition term86 (x0 : real -> real) (x1 : nat) := (polynomial_function x0) /\ (polynomial_function (fun y0 : real => real_pow (x0 y0) x1)).
Definition term40 (x0 : real -> real) := fun y0 : nat => ((fun y1 : nat => polynomial_function (fun y2 : real => real_pow (x0 y2) y1)) y0) -> (fun y1 : nat => polynomial_function (fun y2 : real => real_pow (x0 y2) y1)) (S y0).
Definition term38 (x0 : real -> real) (x1 : nat) := ((fun y0 : nat => polynomial_function (fun y1 : real => real_pow (x0 y1) y0)) x1) -> (fun y0 : nat => polynomial_function (fun y1 : real => real_pow (x0 y1) y0)) (S x1).
Definition term35 (x0 : real -> real) (x1 : nat) := imp (polynomial_function (fun y0 : real => real_pow (x0 y0) x1)).
Definition term54 (x0 : real -> real) := fun y0 : real => real_pow (x0 y0) (NUMERAL 0).
Definition term6 (x0 : Prop) (x1 : nat -> Prop) := x0 -> forall y0 : nat, x1 y0.
Definition term70 (x0 : real -> real) (x1 : nat) := fun y0 : real => real_mul (x0 y0) (real_pow (x0 y0) x1).
Definition term26 := forall y0 : real -> real, forall y1 : nat, (polynomial_function y0) -> polynomial_function (fun y2 : real => real_pow (y0 y2) y1).
Definition term75 (x0 : real -> real) (x1 : nat) (x2 : real) := (fun y0 : real => real_pow (x0 y0) x1) x2.
Definition term14 (x0 : real -> real) (x1 : nat) := (polynomial_function x0) -> polynomial_function (fun y0 : real => real_pow (x0 y0) x1).
Definition term39 (x0 : real -> real) (x1 : nat) := (polynomial_function (fun y0 : real => real_pow (x0 y0) x1)) -> polynomial_function (fun y0 : real => real_pow (x0 y0) (S x1)).
Definition term9 (x0 : real -> real) := fun y0 : nat => polynomial_function (fun y1 : real => real_pow (x0 y1) y0).
Definition term44 (x0 : real -> real) := ((fun y0 : nat => polynomial_function (fun y1 : real => real_pow (x0 y1) y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => polynomial_function (fun y2 : real => real_pow (x0 y2) y1)) y0) -> (fun y1 : nat => polynomial_function (fun y2 : real => real_pow (x0 y2) y1)) (S y0)).
Definition term52 := real_of_num (NUMERAL (BIT1 0)).
Definition term37 (x0 : real -> real) (x1 : nat) := polynomial_function (fun y0 : real => real_pow (x0 y0) (S x1)).
Definition term23 (x0 : real -> real) := (polynomial_function x0) -> forall y0 : nat, polynomial_function (fun y1 : real => real_pow (x0 y1) y0).
Definition term78 (x0 : real -> real) (x1 : nat) (x2 : real) := real_mul (x0 x2) ((fun y0 : real => real_pow (x0 y0) x1) x2).
Definition term16 (x0 : real -> real) := fun y0 : nat => (polynomial_function x0) -> polynomial_function (fun y1 : real => real_pow (x0 y1) y0).
Definition term79 (x0 : real -> real) (x1 : nat) := fun y0 : real => real_mul (x0 y0) ((fun y1 : real => real_pow (x0 y1) x1) y0).
Definition term41 (x0 : real -> real) := fun y0 : nat => (polynomial_function (fun y1 : real => real_pow (x0 y1) y0)) -> polynomial_function (fun y1 : real => real_pow (x0 y1) (S y0)).
Definition term69 (x0 : real -> real) (x1 : nat) := fun y0 : real => real_pow (x0 y0) (S x1).
Definition term33 (x0 : real -> real) := and (polynomial_function (fun y0 : real => real_pow (x0 y0) (NUMERAL 0))).
Definition term25 := fun y0 : real -> real => (polynomial_function y0) -> forall y1 : nat, polynomial_function (fun y2 : real => real_pow (y0 y2) y1).
Definition term12 (x0 : real -> real) := imp (polynomial_function x0).
Definition term76 (x0 : real -> real) (x1 : real) (x2 : nat) := real_pow (x0 x1) x2.
Definition term21 (x0 : real -> real) := forall y0 : nat, (fun y1 : nat => polynomial_function (fun y2 : real => real_pow (x0 y2) y1)) y0.
Definition term5 (x0 : Prop) (x1 : nat -> Prop) := forall y0 : nat, x0 -> x1 y0.
Definition term85 (x0 : real -> real) := and (polynomial_function x0).
