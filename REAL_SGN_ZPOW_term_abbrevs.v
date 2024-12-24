Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term40 (x0 : real) (x1 : nat) := (fun y0 : int => (real_sgn (real_zpow x0 y0)) = (real_zpow (real_sgn x0) y0)) (int_of_num x1).
Definition term29 (x0 : int -> Prop) := (forall y0 : nat, x0 (int_of_num y0)) /\ (forall y0 : nat, x0 (int_neg (int_of_num y0))).
Definition term33 (x0 : real) (x1 : int) := (fun y0 : int => (real_sgn (real_zpow x0 y0)) = (real_zpow (real_sgn x0) y0)) x1.
Definition term44 (x0 : real) := fun y0 : nat => (real_sgn (real_zpow x0 (int_of_num y0))) = (real_zpow (real_sgn x0) (int_of_num y0)).
Definition term73 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term75 (x0 : real) (x1 : nat) := real_inv (real_sgn (real_pow x0 x1)).
Definition term50 (x0 : real) (x1 : nat) := real_sgn (real_zpow x0 (int_neg (int_of_num x1))).
Definition term81 := fun y0 : real => True.
Definition term64 (x0 : real) := fun y0 : nat => (real_sgn (real_inv (real_pow x0 y0))) = (real_inv (real_pow (real_sgn x0) y0)).
Definition term51 (x0 : real) (x1 : nat) := real_zpow (real_sgn x0) (int_neg (int_of_num x1)).
Definition term68 := fun y0 : real => (forall y1 : nat, (real_sgn (real_pow y0 y1)) = (real_pow (real_sgn y0) y1)) /\ (forall y1 : nat, (real_sgn (real_inv (real_pow y0 y1))) = (real_inv (real_pow (real_sgn y0) y1))).
Definition term24 (x0 : real) := forall y0 : nat, (real_zpow x0 (int_of_num y0)) = (real_pow x0 y0).
Definition term35 (x0 : real) (x1 : int) := real_zpow (real_sgn x0) x1.
Definition term65 (x0 : real) := forall y0 : nat, (real_sgn (real_inv (real_pow x0 y0))) = (real_inv (real_pow (real_sgn x0) y0)).
Definition term27 (x0 : int -> Prop) := (fun y0 : int -> Prop => (forall y1 : int, y0 y1) = ((forall y1 : nat, y0 (int_of_num y1)) /\ (forall y1 : nat, y0 (int_neg (int_of_num y1))))) x0.
Definition term41 (x0 : real) (x1 : nat) := real_sgn (real_zpow x0 (int_of_num x1)).
Definition term55 (x0 : real) := forall y0 : nat, (real_sgn (real_zpow x0 (int_neg (int_of_num y0)))) = (real_zpow (real_sgn x0) (int_neg (int_of_num y0))).
Definition term77 (x0 : real) := forall y0 : nat, (real_sgn (real_inv (real_pow x0 y0))) = (real_inv (real_sgn (real_pow x0 y0))).
Definition term82 := forall y0 : real, True.
Definition term83 (x0 : Prop) := forall y0 : real, x0.
Definition term15 (x0 : real) (x1 : nat) := (fun y0 : nat => (real_pow (real_sgn x0) y0) = (real_sgn (real_pow x0 y0))) x1.
Definition term80 := forall y0 : real, forall y1 : nat, (real_sgn (real_inv (real_pow y0 y1))) = (real_inv (real_sgn (real_pow y0 y1))).
Definition term69 := forall y0 : real, forall y1 : int, (real_sgn (real_zpow y0 y1)) = (real_zpow (real_sgn y0) y1).
Definition term22 := forall y0 : real, forall y1 : nat, (real_zpow y0 (int_of_num y1)) = (real_pow y0 y1).
Definition term16 := forall y0 : real, forall y1 : nat, (real_zpow y0 (int_neg (int_of_num y1))) = (real_inv (real_pow y0 y1)).
Definition term13 := forall y0 : real, forall y1 : nat, (real_pow (real_sgn y0) y1) = (real_sgn (real_pow y0 y1)).
Definition term12 := forall y0 : real, forall y1 : nat, (real_sgn (real_pow y0 y1)) = (real_pow (real_sgn y0) y1).
Definition term43 (x0 : real) := fun y0 : nat => (fun y1 : int => (real_sgn (real_zpow x0 y1)) = (real_zpow (real_sgn x0) y1)) (int_of_num y0).
Definition term6 (x0 : real) := fun y0 : nat => (real_sgn (real_pow x0 y0)) = (real_pow (real_sgn x0) y0).
Definition term39 (x0 : real) := @eq Prop (forall y0 : int, (real_sgn (real_zpow x0 y0)) = (real_zpow (real_sgn x0) y0)).
Definition term23 (x0 : real) := (fun y0 : real => forall y1 : nat, (real_zpow y0 (int_of_num y1)) = (real_pow y0 y1)) x0.
Definition term17 (x0 : real) := (fun y0 : real => forall y1 : nat, (real_zpow y0 (int_neg (int_of_num y1))) = (real_inv (real_pow y0 y1))) x0.
Definition term14 (x0 : real) := (fun y0 : real => forall y1 : nat, (real_pow (real_sgn y0) y1) = (real_sgn (real_pow y0 y1))) x0.
Definition term19 (x0 : real) (x1 : nat) := (fun y0 : nat => (real_zpow x0 (int_neg (int_of_num y0))) = (real_inv (real_pow x0 y0))) x1.
Definition term31 (x0 : real) := (forall y0 : nat, (fun y1 : int => (real_sgn (real_zpow x0 y1)) = (real_zpow (real_sgn x0) y1)) (int_of_num y0)) /\ (forall y0 : nat, (fun y1 : int => (real_sgn (real_zpow x0 y1)) = (real_zpow (real_sgn x0) y1)) (int_neg (int_of_num y0))).
Definition term63 (x0 : real) (x1 : nat) := real_inv (real_pow (real_sgn x0) x1).
Definition term59 (x0 : real) := and (forall y0 : nat, (real_sgn (real_pow x0 y0)) = (real_pow (real_sgn x0) y0)).
Definition term48 (x0 : real) := and (forall y0 : nat, (real_sgn (real_zpow x0 (int_of_num y0))) = (real_zpow (real_sgn x0) (int_of_num y0))).
Definition term52 (x0 : real) := fun y0 : nat => (fun y1 : int => (real_sgn (real_zpow x0 y1)) = (real_zpow (real_sgn x0) y1)) (int_neg (int_of_num y0)).
Definition term78 (x0 : real) := True /\ (forall y0 : nat, (real_sgn (real_inv (real_pow x0 y0))) = (real_inv (real_sgn (real_pow x0 y0)))).
Definition term28 (x0 : int -> Prop) := forall y0 : int, x0 y0.
Definition term58 (x0 : real) (x1 : nat) := @eq real (real_sgn (real_pow x0 x1)).
Definition term76 (x0 : real) := fun y0 : nat => (real_sgn (real_inv (real_pow x0 y0))) = (real_inv (real_sgn (real_pow x0 y0))).
Definition term37 (x0 : real) := forall y0 : int, (real_sgn (real_zpow x0 y0)) = (real_zpow (real_sgn x0) y0).
Definition term46 (x0 : real) := forall y0 : nat, (real_sgn (real_zpow x0 (int_of_num y0))) = (real_zpow (real_sgn x0) (int_of_num y0)).
Definition term1 (x0 : real) := real_inv (real_sgn x0).
Definition term7 (x0 : real) := fun y0 : nat => (real_pow (real_sgn x0) y0) = (real_sgn (real_pow x0 y0)).
Definition term72 := forall y0 : nat, True.
Definition term79 := fun y0 : real => forall y1 : nat, (real_sgn (real_inv (real_pow y0 y1))) = (real_inv (real_sgn (real_pow y0 y1))).
Definition term11 := fun y0 : real => forall y1 : nat, (real_pow (real_sgn y0) y1) = (real_sgn (real_pow y0 y1)).
Definition term47 (x0 : real) := and (forall y0 : nat, (fun y1 : int => (real_sgn (real_zpow x0 y1)) = (real_zpow (real_sgn x0) y1)) (int_of_num y0)).
Definition term34 (x0 : real) (x1 : int) := real_sgn (real_zpow x0 x1).
Definition term5 (x0 : real) (x1 : nat) := real_pow (real_sgn x0) x1.
Definition term71 := fun y0 : nat => True.
Definition term20 (x0 : real) (x1 : nat) := real_zpow x0 (int_neg (int_of_num x1)).
Definition term49 (x0 : real) (x1 : nat) := (fun y0 : int => (real_sgn (real_zpow x0 y0)) = (real_zpow (real_sgn x0) y0)) (int_neg (int_of_num x1)).
Definition term53 (x0 : real) := fun y0 : nat => (real_sgn (real_zpow x0 (int_neg (int_of_num y0)))) = (real_zpow (real_sgn x0) (int_neg (int_of_num y0))).
Definition term38 (x0 : real) := @eq Prop (forall y0 : int, (fun y1 : int => (real_sgn (real_zpow x0 y1)) = (real_zpow (real_sgn x0) y1)) y0).
Definition term66 (x0 : real) := (forall y0 : nat, (real_sgn (real_pow x0 y0)) = (real_pow (real_sgn x0) y0)) /\ (forall y0 : nat, (real_sgn (real_inv (real_pow x0 y0))) = (real_inv (real_pow (real_sgn x0) y0))).
Definition term56 (x0 : real) := (forall y0 : nat, (real_sgn (real_zpow x0 (int_of_num y0))) = (real_zpow (real_sgn x0) (int_of_num y0))) /\ (forall y0 : nat, (real_sgn (real_zpow x0 (int_neg (int_of_num y0)))) = (real_zpow (real_sgn x0) (int_neg (int_of_num y0)))).
Definition term10 := fun y0 : real => forall y1 : nat, (real_sgn (real_pow y0 y1)) = (real_pow (real_sgn y0) y1).
Definition term32 (x0 : real) := fun y0 : int => (real_sgn (real_zpow x0 y0)) = (real_zpow (real_sgn x0) y0).
Definition term25 (x0 : real) (x1 : nat) := (fun y0 : nat => (real_zpow x0 (int_of_num y0)) = (real_pow x0 y0)) x1.
Definition term60 (x0 : real) (x1 : nat) := real_sgn (real_inv (real_pow x0 x1)).
Definition term45 (x0 : real) := forall y0 : nat, (fun y1 : int => (real_sgn (real_zpow x0 y1)) = (real_zpow (real_sgn x0) y1)) (int_of_num y0).
Definition term70 := forall y0 : real, (forall y1 : nat, (real_sgn (real_pow y0 y1)) = (real_pow (real_sgn y0) y1)) /\ (forall y1 : nat, (real_sgn (real_inv (real_pow y0 y1))) = (real_inv (real_pow (real_sgn y0) y1))).
Definition term18 (x0 : real) := forall y0 : nat, (real_zpow x0 (int_neg (int_of_num y0))) = (real_inv (real_pow x0 y0)).
Definition term4 (x0 : real) (x1 : nat) := real_sgn (real_pow x0 x1).
Definition term21 (x0 : real) (x1 : nat) := real_inv (real_pow x0 x1).
Definition term62 (x0 : real) (x1 : nat) := @eq real (real_sgn (real_inv (real_pow x0 x1))).
Definition term67 := fun y0 : real => forall y1 : int, (real_sgn (real_zpow y0 y1)) = (real_zpow (real_sgn y0) y1).
Definition term26 (x0 : real) (x1 : nat) := real_zpow x0 (int_of_num x1).
Definition term9 (x0 : real) := forall y0 : nat, (real_pow (real_sgn x0) y0) = (real_sgn (real_pow x0 y0)).
Definition term2 (x0 : real) := (fun y0 : real => (real_sgn (real_inv y0)) = (real_sgn y0)) x0.
Definition term0 (x0 : real) := (fun y0 : real => (real_inv (real_sgn y0)) = (real_sgn y0)) x0.
Definition term74 (x0 : Prop) := forall y0 : nat, x0.
Definition term8 (x0 : real) := forall y0 : nat, (real_sgn (real_pow x0 y0)) = (real_pow (real_sgn x0) y0).
Definition term54 (x0 : real) := forall y0 : nat, (fun y1 : int => (real_sgn (real_zpow x0 y1)) = (real_zpow (real_sgn x0) y1)) (int_neg (int_of_num y0)).
Definition term3 (x0 : real) := real_sgn (real_inv x0).
Definition term57 (x0 : real) (x1 : nat) := @eq real (real_sgn (real_zpow x0 (int_of_num x1))).
Definition term36 (x0 : real) := fun y0 : int => (fun y1 : int => (real_sgn (real_zpow x0 y1)) = (real_zpow (real_sgn x0) y1)) y0.
Definition term61 (x0 : real) (x1 : nat) := @eq real (real_sgn (real_zpow x0 (int_neg (int_of_num x1)))).
Definition term30 (x0 : real) := forall y0 : int, (fun y1 : int => (real_sgn (real_zpow x0 y1)) = (real_zpow (real_sgn x0) y1)) y0.
Definition term42 (x0 : real) (x1 : nat) := real_zpow (real_sgn x0) (int_of_num x1).
