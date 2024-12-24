Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term25 (x0 : int -> Prop) := (forall y0 : nat, x0 (int_of_num y0)) /\ (forall y0 : nat, x0 (int_neg (int_of_num y0))).
Definition term2 (x0 : real) (x1 : real) := (fun y0 : real => (real_inv (real_mul x0 y0)) = (real_mul (real_inv x0) (real_inv y0))) x1.
Definition term10 (x0 : real) (x1 : real) (x2 : nat) := real_pow (real_mul x0 x1) x2.
Definition term11 (x0 : real) (x1 : real) (x2 : nat) := real_mul (real_pow x0 x2) (real_pow x1 x2).
Definition term59 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term46 (x0 : real) (x1 : real) (x2 : nat) := real_zpow (real_mul x0 x1) (int_neg (int_of_num x2)).
Definition term69 := fun y0 : real => True.
Definition term4 (x0 : real) (x1 : real) := real_mul (real_inv x0) (real_inv x1).
Definition term56 (x0 : real) (x1 : nat) := real_mul (real_pow x0 x1).
Definition term20 (x0 : real) := forall y0 : nat, (real_zpow x0 (int_of_num y0)) = (real_pow x0 y0).
Definition term37 (x0 : real) (x1 : real) (x2 : nat) := real_zpow (real_mul x0 x1) (int_of_num x2).
Definition term39 (x0 : real) (x1 : real) := fun y0 : nat => (fun y1 : int => (real_zpow (real_mul x0 x1) y1) = (real_mul (real_zpow x0 y1) (real_zpow x1 y1))) (int_of_num y0).
Definition term23 (x0 : int -> Prop) := (fun y0 : int -> Prop => (forall y1 : int, y0 y1) = ((forall y1 : nat, y0 (int_of_num y1)) /\ (forall y1 : nat, y0 (int_neg (int_of_num y1))))) x0.
Definition term71 := forall y0 : real, True.
Definition term67 (x0 : real) (x1 : nat) := real_mul (real_inv (real_pow x0 x1)).
Definition term72 (x0 : Prop) := forall y0 : real, x0.
Definition term47 (x0 : real) (x1 : real) (x2 : nat) := real_mul (real_zpow x0 (int_neg (int_of_num x2))) (real_zpow x1 (int_neg (int_of_num x2))).
Definition term74 := forall y0 : real, forall y1 : real, forall y2 : int, (real_zpow (real_mul y0 y1) y2) = (real_mul (real_zpow y0 y2) (real_zpow y1 y2)).
Definition term70 (x0 : real) := forall y0 : real, forall y1 : int, (real_zpow (real_mul x0 y0) y1) = (real_mul (real_zpow x0 y1) (real_zpow y0 y1)).
Definition term18 := forall y0 : real, forall y1 : nat, (real_zpow y0 (int_of_num y1)) = (real_pow y0 y1).
Definition term12 := forall y0 : real, forall y1 : nat, (real_zpow y0 (int_neg (int_of_num y1))) = (real_inv (real_pow y0 y1)).
Definition term6 (x0 : real) := forall y0 : real, forall y1 : nat, (real_pow (real_mul x0 y0) y1) = (real_mul (real_pow x0 y1) (real_pow y0 y1)).
Definition term51 (x0 : real) (x1 : real) := forall y0 : nat, (real_zpow (real_mul x0 x1) (int_neg (int_of_num y0))) = (real_mul (real_zpow x0 (int_neg (int_of_num y0))) (real_zpow x1 (int_neg (int_of_num y0)))).
Definition term42 (x0 : real) (x1 : real) := forall y0 : nat, (real_zpow (real_mul x0 x1) (int_of_num y0)) = (real_mul (real_zpow x0 (int_of_num y0)) (real_zpow x1 (int_of_num y0))).
Definition term35 (x0 : real) (x1 : real) := @eq Prop (forall y0 : int, (real_zpow (real_mul x0 x1) y0) = (real_mul (real_zpow x0 y0) (real_zpow x1 y0))).
Definition term19 (x0 : real) := (fun y0 : real => forall y1 : nat, (real_zpow y0 (int_of_num y1)) = (real_pow y0 y1)) x0.
Definition term13 (x0 : real) := (fun y0 : real => forall y1 : nat, (real_zpow y0 (int_neg (int_of_num y1))) = (real_inv (real_pow y0 y1))) x0.
Definition term64 (x0 : real) (x1 : real) (x2 : nat) := @eq real (real_zpow (real_mul x0 x1) (int_neg (int_of_num x2))).
Definition term15 (x0 : real) (x1 : nat) := (fun y0 : nat => (real_zpow x0 (int_neg (int_of_num y0))) = (real_inv (real_pow x0 y0))) x1.
Definition term27 (x0 : real) (x1 : real) := (forall y0 : nat, (fun y1 : int => (real_zpow (real_mul x0 x1) y1) = (real_mul (real_zpow x0 y1) (real_zpow x1 y1))) (int_of_num y0)) /\ (forall y0 : nat, (fun y1 : int => (real_zpow (real_mul x0 x1) y1) = (real_mul (real_zpow x0 y1) (real_zpow x1 y1))) (int_neg (int_of_num y0))).
Definition term44 (x0 : real) (x1 : real) := and (forall y0 : nat, (real_zpow (real_mul x0 x1) (int_of_num y0)) = (real_mul (real_zpow x0 (int_of_num y0)) (real_zpow x1 (int_of_num y0)))).
Definition term65 (x0 : real) (x1 : real) (x2 : nat) := @eq real (real_mul (real_inv (real_pow x0 x2)) (real_inv (real_pow x1 x2))).
Definition term24 (x0 : int -> Prop) := forall y0 : int, x0 y0.
Definition term55 (x0 : real) (x1 : nat) := real_mul (real_zpow x0 (int_of_num x1)).
Definition term38 (x0 : real) (x1 : real) (x2 : nat) := real_mul (real_zpow x0 (int_of_num x2)) (real_zpow x1 (int_of_num x2)).
Definition term58 := forall y0 : nat, True.
Definition term43 (x0 : real) (x1 : real) := and (forall y0 : nat, (fun y1 : int => (real_zpow (real_mul x0 x1) y1) = (real_mul (real_zpow x0 y1) (real_zpow x1 y1))) (int_of_num y0)).
Definition term0 (x0 : real) := (fun y0 : real => forall y1 : real, (real_inv (real_mul y0 y1)) = (real_mul (real_inv y0) (real_inv y1))) x0.
Definition term29 (x0 : real) (x1 : real) (x2 : int) := (fun y0 : int => (real_zpow (real_mul x0 x1) y0) = (real_mul (real_zpow x0 y0) (real_zpow x1 y0))) x2.
Definition term49 (x0 : real) (x1 : real) := fun y0 : nat => (real_zpow (real_mul x0 x1) (int_neg (int_of_num y0))) = (real_mul (real_zpow x0 (int_neg (int_of_num y0))) (real_zpow x1 (int_neg (int_of_num y0)))).
Definition term57 := fun y0 : nat => True.
Definition term54 (x0 : real) (x1 : real) (x2 : nat) := @eq real (real_mul (real_pow x0 x2) (real_pow x1 x2)).
Definition term53 (x0 : real) (x1 : real) (x2 : nat) := @eq real (real_zpow (real_mul x0 x1) (int_of_num x2)).
Definition term68 (x0 : real) := fun y0 : real => forall y1 : int, (real_zpow (real_mul x0 y0) y1) = (real_mul (real_zpow x0 y1) (real_zpow y0 y1)).
Definition term9 (x0 : real) (x1 : real) (x2 : nat) := (fun y0 : nat => (real_pow (real_mul x0 x1) y0) = (real_mul (real_pow x0 y0) (real_pow x1 y0))) x2.
Definition term63 (x0 : real) (x1 : real) (x2 : nat) := real_mul (real_inv (real_pow x0 x2)) (real_inv (real_pow x1 x2)).
Definition term16 (x0 : real) (x1 : nat) := real_zpow x0 (int_neg (int_of_num x1)).
Definition term62 (x0 : real) (x1 : real) (x2 : nat) := real_inv (real_mul (real_pow x0 x2) (real_pow x1 x2)).
Definition term40 (x0 : real) (x1 : real) := fun y0 : nat => (real_zpow (real_mul x0 x1) (int_of_num y0)) = (real_mul (real_zpow x0 (int_of_num y0)) (real_zpow x1 (int_of_num y0))).
Definition term66 (x0 : real) (x1 : nat) := real_mul (real_zpow x0 (int_neg (int_of_num x1))).
Definition term34 (x0 : real) (x1 : real) := @eq Prop (forall y0 : int, (fun y1 : int => (real_zpow (real_mul x0 x1) y1) = (real_mul (real_zpow x0 y1) (real_zpow x1 y1))) y0).
Definition term3 (x0 : real) (x1 : real) := real_inv (real_mul x0 x1).
Definition term52 (x0 : real) (x1 : real) := (forall y0 : nat, (real_zpow (real_mul x0 x1) (int_of_num y0)) = (real_mul (real_zpow x0 (int_of_num y0)) (real_zpow x1 (int_of_num y0)))) /\ (forall y0 : nat, (real_zpow (real_mul x0 x1) (int_neg (int_of_num y0))) = (real_mul (real_zpow x0 (int_neg (int_of_num y0))) (real_zpow x1 (int_neg (int_of_num y0))))).
Definition term61 (x0 : real) (x1 : real) (x2 : nat) := real_inv (real_pow (real_mul x0 x1) x2).
Definition term30 (x0 : real) (x1 : real) (x2 : int) := real_zpow (real_mul x0 x1) x2.
Definition term21 (x0 : real) (x1 : nat) := (fun y0 : nat => (real_zpow x0 (int_of_num y0)) = (real_pow x0 y0)) x1.
Definition term45 (x0 : real) (x1 : real) (x2 : nat) := (fun y0 : int => (real_zpow (real_mul x0 x1) y0) = (real_mul (real_zpow x0 y0) (real_zpow x1 y0))) (int_neg (int_of_num x2)).
Definition term73 := fun y0 : real => forall y1 : real, forall y2 : int, (real_zpow (real_mul y0 y1) y2) = (real_mul (real_zpow y0 y2) (real_zpow y1 y2)).
Definition term32 (x0 : real) (x1 : real) := fun y0 : int => (fun y1 : int => (real_zpow (real_mul x0 x1) y1) = (real_mul (real_zpow x0 y1) (real_zpow x1 y1))) y0.
Definition term41 (x0 : real) (x1 : real) := forall y0 : nat, (fun y1 : int => (real_zpow (real_mul x0 x1) y1) = (real_mul (real_zpow x0 y1) (real_zpow x1 y1))) (int_of_num y0).
Definition term1 (x0 : real) := forall y0 : real, (real_inv (real_mul x0 y0)) = (real_mul (real_inv x0) (real_inv y0)).
Definition term8 (x0 : real) (x1 : real) := forall y0 : nat, (real_pow (real_mul x0 x1) y0) = (real_mul (real_pow x0 y0) (real_pow x1 y0)).
Definition term14 (x0 : real) := forall y0 : nat, (real_zpow x0 (int_neg (int_of_num y0))) = (real_inv (real_pow x0 y0)).
Definition term17 (x0 : real) (x1 : nat) := real_inv (real_pow x0 x1).
Definition term28 (x0 : real) (x1 : real) := fun y0 : int => (real_zpow (real_mul x0 x1) y0) = (real_mul (real_zpow x0 y0) (real_zpow x1 y0)).
Definition term22 (x0 : real) (x1 : nat) := real_zpow x0 (int_of_num x1).
Definition term60 (x0 : Prop) := forall y0 : nat, x0.
Definition term31 (x0 : real) (x1 : real) (x2 : int) := real_mul (real_zpow x0 x2) (real_zpow x1 x2).
Definition term50 (x0 : real) (x1 : real) := forall y0 : nat, (fun y1 : int => (real_zpow (real_mul x0 x1) y1) = (real_mul (real_zpow x0 y1) (real_zpow x1 y1))) (int_neg (int_of_num y0)).
Definition term33 (x0 : real) (x1 : real) := forall y0 : int, (real_zpow (real_mul x0 x1) y0) = (real_mul (real_zpow x0 y0) (real_zpow x1 y0)).
Definition term5 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : nat, (real_pow (real_mul y0 y1) y2) = (real_mul (real_pow y0 y2) (real_pow y1 y2))) x0.
Definition term36 (x0 : real) (x1 : real) (x2 : nat) := (fun y0 : int => (real_zpow (real_mul x0 x1) y0) = (real_mul (real_zpow x0 y0) (real_zpow x1 y0))) (int_of_num x2).
Definition term26 (x0 : real) (x1 : real) := forall y0 : int, (fun y1 : int => (real_zpow (real_mul x0 x1) y1) = (real_mul (real_zpow x0 y1) (real_zpow x1 y1))) y0.
Definition term48 (x0 : real) (x1 : real) := fun y0 : nat => (fun y1 : int => (real_zpow (real_mul x0 x1) y1) = (real_mul (real_zpow x0 y1) (real_zpow x1 y1))) (int_neg (int_of_num y0)).
Definition term7 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : nat, (real_pow (real_mul x0 y0) y1) = (real_mul (real_pow x0 y1) (real_pow y0 y1))) x1.
