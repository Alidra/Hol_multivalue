Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term45 (x0 : real) := fun y0 : int => forall y1 : int, (real_zpow (real_zpow x0 y0) y1) = (real_zpow x0 (int_mul y0 y1)).
Definition term46 (x0 : real) (x1 : int) := (fun y0 : int => forall y1 : int, (real_zpow (real_zpow x0 y0) y1) = (real_zpow x0 (int_mul y0 y1))) x1.
Definition term42 (x0 : int -> Prop) := (forall y0 : nat, x0 (int_of_num y0)) /\ (forall y0 : nat, x0 (int_neg (int_of_num y0))).
Definition term129 (x0 : nat) (x1 : nat) := int_mul (int_neg (int_of_num x0)) (int_of_num x1).
Definition term33 (x0 : int) (x1 : int) := (fun y0 : int => (int_mul x0 (int_neg y0)) = (int_neg (int_mul x0 y0))) x1.
Definition term154 (x0 : real) (x1 : nat) (x2 : nat) := real_zpow x0 (int_of_num (Nat.mul x1 x2)).
Definition term159 (x0 : real) (x1 : nat) := real_inv (real_zpow x0 (int_of_num x1)).
Definition term95 (x0 : real) (x1 : nat) (x2 : nat) := real_zpow x0 (int_neg (int_mul (int_of_num x1) (int_of_num x2))).
Definition term93 (x0 : nat) (x1 : nat) := int_mul (int_of_num x0) (int_neg (int_of_num x1)).
Definition term183 (x0 : real) (x1 : nat) := real_pow (real_inv (real_zpow x0 (int_neg (int_of_num x1)))).
Definition term182 (x0 : real) := real_pow (real_inv (real_inv x0)).
Definition term116 (x0 : real) (x1 : nat) := fun y0 : nat => (real_zpow (real_zpow x0 (int_neg (int_of_num x1))) (int_of_num y0)) = (real_zpow x0 (int_mul (int_neg (int_of_num x1)) (int_of_num y0))).
Definition term80 (x0 : real) (x1 : nat) := fun y0 : nat => (real_zpow (real_zpow x0 (int_of_num x1)) (int_of_num y0)) = (real_zpow x0 (int_mul (int_of_num x1) (int_of_num y0))).
Definition term39 (x0 : int) (x1 : int) := int_mul (int_neg x0) x1.
Definition term122 (x0 : real) (x1 : nat) (x2 : nat) := real_zpow (real_zpow x0 (int_neg (int_of_num x1))) (int_neg (int_of_num x2)).
Definition term37 (x0 : int) := forall y0 : int, (int_mul (int_neg x0) y0) = (int_neg (int_mul x0 y0)).
Definition term149 (x0 : real) (x1 : nat) (x2 : nat) := real_pow (real_zpow x0 (int_of_num x1)) x2.
Definition term193 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term36 (x0 : int) := (fun y0 : int => forall y1 : int, (int_mul (int_neg y0) y1) = (int_neg (int_mul y0 y1))) x0.
Definition term31 (x0 : int) := (fun y0 : int => forall y1 : int, (int_mul y0 (int_neg y1)) = (int_neg (int_mul y0 y1))) x0.
Definition term175 (x0 : real) (x1 : nat) := real_pow (real_zpow x0 (int_neg (int_of_num x1))).
Definition term174 (x0 : real) (x1 : nat) (x2 : nat) := real_pow (real_zpow x0 (int_neg (int_of_num x1))) x2.
Definition term196 := fun y0 : real => True.
Definition term66 (x0 : real) := (forall y0 : nat, forall y1 : int, (real_zpow (real_zpow x0 (int_of_num y0)) y1) = (real_zpow x0 (int_mul (int_of_num y0) y1))) /\ (forall y0 : nat, forall y1 : int, (real_zpow (real_zpow x0 (int_neg (int_of_num y0))) y1) = (real_zpow x0 (int_mul (int_neg (int_of_num y0)) y1))).
Definition term155 (x0 : real) (x1 : nat) := fun y0 : nat => (real_pow (real_pow x0 x1) y0) = (real_pow x0 (Nat.mul x1 y0)).
Definition term188 := fun y0 : real => (forall y1 : nat, (forall y2 : nat, (real_pow (real_pow y0 y1) y2) = (real_pow y0 (Nat.mul y1 y2))) /\ (forall y2 : nat, (real_pow (real_pow (real_inv y0) y1) y2) = (real_pow (real_inv y0) (Nat.mul y1 y2)))) /\ (forall y1 : nat, (forall y2 : nat, (real_pow (real_pow (real_inv y0) y1) y2) = (real_pow (real_inv y0) (Nat.mul y1 y2))) /\ (forall y2 : nat, (real_pow (real_pow y0 y1) y2) = (real_pow y0 (Nat.mul y1 y2)))).
Definition term146 := fun y0 : real => (forall y1 : nat, (forall y2 : nat, (real_zpow (real_zpow y0 (int_of_num y1)) (int_of_num y2)) = (real_zpow y0 (int_mul (int_of_num y1) (int_of_num y2)))) /\ (forall y2 : nat, (real_zpow (real_zpow y0 (int_of_num y1)) (int_neg (int_of_num y2))) = (real_zpow y0 (int_neg (int_mul (int_of_num y1) (int_of_num y2)))))) /\ (forall y1 : nat, (forall y2 : nat, (real_zpow (real_zpow y0 (int_neg (int_of_num y1))) (int_of_num y2)) = (real_zpow y0 (int_neg (int_mul (int_of_num y1) (int_of_num y2))))) /\ (forall y2 : nat, (real_zpow (real_zpow y0 (int_neg (int_of_num y1))) (int_neg (int_of_num y2))) = (real_zpow y0 (int_mul (int_of_num y1) (int_of_num y2))))).
Definition term163 (x0 : real) (x1 : nat) (x2 : nat) := @eq real (real_pow (real_pow (real_inv x0) x1) x2).
Definition term153 (x0 : real) (x1 : nat) (x2 : nat) := @eq real (real_pow (real_pow x0 x1) x2).
Definition term26 (x0 : real) := forall y0 : nat, (real_zpow x0 (int_of_num y0)) = (real_pow x0 y0).
Definition term179 (x0 : real) (x1 : nat) := real_inv (real_zpow x0 (int_neg (int_of_num x1))).
Definition term113 (x0 : real) (x1 : nat) (x2 : nat) := real_zpow (real_zpow x0 (int_neg (int_of_num x1))) (int_of_num x2).
Definition term5 (x0 : real) (x1 : nat) (x2 : nat) := real_pow (real_pow x0 x1) x2.
Definition term177 (x0 : real) (x1 : nat) (x2 : nat) := real_inv (real_pow (real_zpow x0 (int_neg (int_of_num x1))) x2).
Definition term157 (x0 : real) (x1 : nat) (x2 : nat) := real_inv (real_pow (real_zpow x0 (int_of_num x1)) x2).
Definition term168 (x0 : real) (x1 : nat) := fun y0 : nat => (real_pow (real_pow (real_inv x0) x1) y0) = (real_pow (real_inv x0) (Nat.mul x1 y0)).
Definition term115 (x0 : real) (x1 : nat) := fun y0 : nat => (fun y1 : int => (real_zpow (real_zpow x0 (int_neg (int_of_num x1))) y1) = (real_zpow x0 (int_mul (int_neg (int_of_num x1)) y1))) (int_of_num y0).
Definition term79 (x0 : real) (x1 : nat) := fun y0 : nat => (fun y1 : int => (real_zpow (real_zpow x0 (int_of_num x1)) y1) = (real_zpow x0 (int_mul (int_of_num x1) y1))) (int_of_num y0).
Definition term40 (x0 : int -> Prop) := (fun y0 : int -> Prop => (forall y1 : int, y0 y1) = ((forall y1 : nat, y0 (int_of_num y1)) /\ (forall y1 : nat, y0 (int_neg (int_of_num y1))))) x0.
Definition term185 (x0 : real) := fun y0 : nat => (forall y1 : nat, (real_pow (real_pow (real_inv x0) y0) y1) = (real_pow (real_inv x0) (Nat.mul y0 y1))) /\ (forall y1 : nat, (real_pow (real_pow x0 y0) y1) = (real_pow x0 (Nat.mul y0 y1))).
Definition term171 (x0 : real) := fun y0 : nat => (forall y1 : nat, (real_pow (real_pow x0 y0) y1) = (real_pow x0 (Nat.mul y0 y1))) /\ (forall y1 : nat, (real_pow (real_pow (real_inv x0) y0) y1) = (real_pow (real_inv x0) (Nat.mul y0 y1))).
Definition term142 (x0 : real) := fun y0 : nat => (forall y1 : nat, (real_zpow (real_zpow x0 (int_neg (int_of_num y0))) (int_of_num y1)) = (real_zpow x0 (int_neg (int_mul (int_of_num y0) (int_of_num y1))))) /\ (forall y1 : nat, (real_zpow (real_zpow x0 (int_neg (int_of_num y0))) (int_neg (int_of_num y1))) = (real_zpow x0 (int_mul (int_of_num y0) (int_of_num y1)))).
Definition term100 (x0 : real) := fun y0 : nat => (forall y1 : nat, (real_zpow (real_zpow x0 (int_of_num y0)) (int_of_num y1)) = (real_zpow x0 (int_mul (int_of_num y0) (int_of_num y1)))) /\ (forall y1 : nat, (real_zpow (real_zpow x0 (int_of_num y0)) (int_neg (int_of_num y1))) = (real_zpow x0 (int_neg (int_mul (int_of_num y0) (int_of_num y1))))).
Definition term197 := forall y0 : real, True.
Definition term198 (x0 : Prop) := forall y0 : real, x0.
Definition term32 (x0 : int) := forall y0 : int, (int_mul x0 (int_neg y0)) = (int_neg (int_mul x0 y0)).
Definition term134 (x0 : nat) (x1 : nat) := int_mul (int_neg (int_of_num x0)) (int_neg (int_of_num x1)).
Definition term108 (x0 : real) (x1 : nat) (x2 : int) := real_zpow x0 (int_mul (int_neg (int_of_num x1)) x2).
Definition term158 (x0 : real) (x1 : nat) (x2 : nat) := real_pow (real_inv (real_zpow x0 (int_of_num x1))) x2.
Definition term167 (x0 : real) (x1 : nat) (x2 : nat) := real_pow (real_inv x0) (Nat.mul x1 x2).
Definition term147 := forall y0 : real, forall y1 : int, forall y2 : int, (real_zpow (real_zpow y0 y1) y2) = (real_zpow y0 (int_mul y1 y2)).
Definition term24 := forall y0 : real, forall y1 : nat, (real_zpow y0 (int_of_num y1)) = (real_pow y0 y1).
Definition term19 := forall y0 : real, forall y1 : nat, (real_zpow y0 (int_neg (int_of_num y1))) = (real_inv (real_pow y0 y1)).
Definition term16 (x0 : real) (x1 : nat) := (fun y0 : nat => (real_inv (real_pow x0 y0)) = (real_pow (real_inv x0) y0)) x1.
Definition term2 (x0 : real) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (real_pow (real_pow x0 y0) y1) = (real_pow x0 (Nat.mul y0 y1))) x1.
Definition term145 := fun y0 : real => forall y1 : int, forall y2 : int, (real_zpow (real_zpow y0 y1) y2) = (real_zpow y0 (int_mul y1 y2)).
Definition term94 (x0 : nat) (x1 : nat) := int_neg (int_mul (int_of_num x0) (int_of_num x1)).
Definition term125 (x0 : real) (x1 : nat) := fun y0 : nat => (real_zpow (real_zpow x0 (int_neg (int_of_num x1))) (int_neg (int_of_num y0))) = (real_zpow x0 (int_mul (int_neg (int_of_num x1)) (int_neg (int_of_num y0)))).
Definition term89 (x0 : real) (x1 : nat) := fun y0 : nat => (real_zpow (real_zpow x0 (int_of_num x1)) (int_neg (int_of_num y0))) = (real_zpow x0 (int_mul (int_of_num x1) (int_neg (int_of_num y0)))).
Definition term72 (x0 : real) (x1 : nat) (x2 : int) := real_zpow x0 (int_mul (int_of_num x1) x2).
Definition term111 (x0 : real) (x1 : nat) := @eq Prop (forall y0 : int, (real_zpow (real_zpow x0 (int_neg (int_of_num x1))) y0) = (real_zpow x0 (int_mul (int_neg (int_of_num x1)) y0))).
Definition term75 (x0 : real) (x1 : nat) := @eq Prop (forall y0 : int, (real_zpow (real_zpow x0 (int_of_num x1)) y0) = (real_zpow x0 (int_mul (int_of_num x1) y0))).
Definition term152 (x0 : real) (x1 : nat) (x2 : nat) := @eq real (real_zpow (real_zpow x0 (int_of_num x1)) (int_of_num x2)).
Definition term25 (x0 : real) := (fun y0 : real => forall y1 : nat, (real_zpow y0 (int_of_num y1)) = (real_pow y0 y1)) x0.
Definition term20 (x0 : real) := (fun y0 : real => forall y1 : nat, (real_zpow y0 (int_neg (int_of_num y1))) = (real_inv (real_pow y0 y1))) x0.
Definition term14 (x0 : real) := (fun y0 : real => forall y1 : nat, (real_inv (real_pow y0 y1)) = (real_pow (real_inv y0) y1)) x0.
Definition term114 (x0 : real) (x1 : nat) (x2 : nat) := real_zpow x0 (int_mul (int_neg (int_of_num x1)) (int_of_num x2)).
Definition term22 (x0 : real) (x1 : nat) := (fun y0 : nat => (real_zpow x0 (int_neg (int_of_num y0))) = (real_inv (real_pow x0 y0))) x1.
Definition term104 (x0 : real) (x1 : nat) := (forall y0 : nat, (fun y1 : int => (real_zpow (real_zpow x0 (int_neg (int_of_num x1))) y1) = (real_zpow x0 (int_mul (int_neg (int_of_num x1)) y1))) (int_of_num y0)) /\ (forall y0 : nat, (fun y1 : int => (real_zpow (real_zpow x0 (int_neg (int_of_num x1))) y1) = (real_zpow x0 (int_mul (int_neg (int_of_num x1)) y1))) (int_neg (int_of_num y0))).
Definition term68 (x0 : real) (x1 : nat) := (forall y0 : nat, (fun y1 : int => (real_zpow (real_zpow x0 (int_of_num x1)) y1) = (real_zpow x0 (int_mul (int_of_num x1) y1))) (int_of_num y0)) /\ (forall y0 : nat, (fun y1 : int => (real_zpow (real_zpow x0 (int_of_num x1)) y1) = (real_zpow x0 (int_mul (int_of_num x1) y1))) (int_neg (int_of_num y0))).
Definition term44 (x0 : real) := (forall y0 : nat, (fun y1 : int => forall y2 : int, (real_zpow (real_zpow x0 y1) y2) = (real_zpow x0 (int_mul y1 y2))) (int_of_num y0)) /\ (forall y0 : nat, (fun y1 : int => forall y2 : int, (real_zpow (real_zpow x0 y1) y2) = (real_zpow x0 (int_mul y1 y2))) (int_neg (int_of_num y0))).
Definition term180 (x0 : real) (x1 : nat) := real_inv (real_pow (real_inv x0) x1).
Definition term176 (x0 : real) (x1 : nat) := and (forall y0 : nat, (real_pow (real_pow (real_inv x0) x1) y0) = (real_pow (real_inv x0) (Nat.mul x1 y0))).
Definition term173 (x0 : real) := and (forall y0 : nat, (forall y1 : nat, (real_pow (real_pow x0 y0) y1) = (real_pow x0 (Nat.mul y0 y1))) /\ (forall y1 : nat, (real_pow (real_pow (real_inv x0) y0) y1) = (real_pow (real_inv x0) (Nat.mul y0 y1)))).
Definition term156 (x0 : real) (x1 : nat) := and (forall y0 : nat, (real_pow (real_pow x0 x1) y0) = (real_pow x0 (Nat.mul x1 y0))).
Definition term133 (x0 : real) (x1 : nat) := and (forall y0 : nat, (real_zpow (real_zpow x0 (int_neg (int_of_num x1))) (int_of_num y0)) = (real_zpow x0 (int_neg (int_mul (int_of_num x1) (int_of_num y0))))).
Definition term120 (x0 : real) (x1 : nat) := and (forall y0 : nat, (real_zpow (real_zpow x0 (int_neg (int_of_num x1))) (int_of_num y0)) = (real_zpow x0 (int_mul (int_neg (int_of_num x1)) (int_of_num y0)))).
Definition term102 (x0 : real) := and (forall y0 : nat, (forall y1 : nat, (real_zpow (real_zpow x0 (int_of_num y0)) (int_of_num y1)) = (real_zpow x0 (int_mul (int_of_num y0) (int_of_num y1)))) /\ (forall y1 : nat, (real_zpow (real_zpow x0 (int_of_num y0)) (int_neg (int_of_num y1))) = (real_zpow x0 (int_neg (int_mul (int_of_num y0) (int_of_num y1)))))).
Definition term84 (x0 : real) (x1 : nat) := and (forall y0 : nat, (real_zpow (real_zpow x0 (int_of_num x1)) (int_of_num y0)) = (real_zpow x0 (int_mul (int_of_num x1) (int_of_num y0)))).
Definition term30 (x0 : int) := int_neg (int_neg x0).
Definition term78 (x0 : real) (x1 : nat) (x2 : nat) := real_zpow x0 (int_mul (int_of_num x1) (int_of_num x2)).
Definition term41 (x0 : int -> Prop) := forall y0 : int, x0 y0.
Definition term130 (x0 : real) (x1 : nat) (x2 : nat) := @eq real (real_zpow (real_zpow x0 (int_neg (int_of_num x1))) (int_of_num x2)).
Definition term8 (x0 : real) := real_inv (real_inv x0).
Definition term86 (x0 : real) (x1 : nat) (x2 : nat) := real_zpow (real_zpow x0 (int_of_num x1)) (int_neg (int_of_num x2)).
Definition term13 (x0 : nat) (x1 : nat) := int_of_num (Nat.mul x0 x1).
Definition term65 (x0 : real) := forall y0 : nat, forall y1 : int, (real_zpow (real_zpow x0 (int_neg (int_of_num y0))) y1) = (real_zpow x0 (int_mul (int_neg (int_of_num y0)) y1)).
Definition term57 (x0 : real) := forall y0 : nat, forall y1 : int, (real_zpow (real_zpow x0 (int_of_num y0)) y1) = (real_zpow x0 (int_mul (int_of_num y0) y1)).
Definition term1 (x0 : real) := forall y0 : nat, forall y1 : nat, (real_pow (real_pow x0 y0) y1) = (real_pow x0 (Nat.mul y0 y1)).
Definition term132 (x0 : real) (x1 : nat) := forall y0 : nat, (real_zpow (real_zpow x0 (int_neg (int_of_num x1))) (int_of_num y0)) = (real_zpow x0 (int_neg (int_mul (int_of_num x1) (int_of_num y0)))).
Definition term98 (x0 : real) (x1 : nat) := forall y0 : nat, (real_zpow (real_zpow x0 (int_of_num x1)) (int_neg (int_of_num y0))) = (real_zpow x0 (int_neg (int_mul (int_of_num x1) (int_of_num y0)))).
Definition term51 (x0 : real) := @eq Prop (forall y0 : int, forall y1 : int, (real_zpow (real_zpow x0 y0) y1) = (real_zpow x0 (int_mul y0 y1))).
Definition term181 (x0 : real) (x1 : nat) := real_pow (real_inv (real_inv x0)) x1.
Definition term7 (x0 : real) := (fun y0 : real => (real_inv (real_inv y0)) = y0) x0.
Definition term123 (x0 : real) (x1 : nat) (x2 : nat) := real_zpow x0 (int_mul (int_neg (int_of_num x1)) (int_neg (int_of_num x2))).
Definition term162 (x0 : real) (x1 : nat) (x2 : nat) := real_pow (real_pow (real_inv x0) x1) x2.
Definition term97 (x0 : real) (x1 : nat) := fun y0 : nat => (real_zpow (real_zpow x0 (int_of_num x1)) (int_neg (int_of_num y0))) = (real_zpow x0 (int_neg (int_mul (int_of_num x1) (int_of_num y0)))).
Definition term192 := forall y0 : nat, True.
Definition term139 (x0 : real) (x1 : nat) := fun y0 : nat => (real_zpow (real_zpow x0 (int_neg (int_of_num x1))) (int_neg (int_of_num y0))) = (real_zpow x0 (int_mul (int_of_num x1) (int_of_num y0))).
Definition term71 (x0 : real) (x1 : nat) (x2 : int) := real_zpow (real_zpow x0 (int_of_num x1)) x2.
Definition term29 (x0 : int) := (fun y0 : int => (int_neg (int_neg y0)) = y0) x0.
Definition term61 (x0 : real) (x1 : nat) := forall y0 : int, (real_zpow (real_zpow x0 (int_neg (int_of_num x1))) y0) = (real_zpow x0 (int_mul (int_neg (int_of_num x1)) y0)).
Definition term53 (x0 : real) (x1 : nat) := forall y0 : int, (real_zpow (real_zpow x0 (int_of_num x1)) y0) = (real_zpow x0 (int_mul (int_of_num x1) y0)).
Definition term47 (x0 : real) (x1 : int) := forall y0 : int, (real_zpow (real_zpow x0 x1) y0) = (real_zpow x0 (int_mul x1 y0)).
Definition term119 (x0 : real) (x1 : nat) := and (forall y0 : nat, (fun y1 : int => (real_zpow (real_zpow x0 (int_neg (int_of_num x1))) y1) = (real_zpow x0 (int_mul (int_neg (int_of_num x1)) y1))) (int_of_num y0)).
Definition term83 (x0 : real) (x1 : nat) := and (forall y0 : nat, (fun y1 : int => (real_zpow (real_zpow x0 (int_of_num x1)) y1) = (real_zpow x0 (int_mul (int_of_num x1) y1))) (int_of_num y0)).
Definition term58 (x0 : real) := and (forall y0 : nat, (fun y1 : int => forall y2 : int, (real_zpow (real_zpow x0 y1) y2) = (real_zpow x0 (int_mul y1 y2))) (int_of_num y0)).
Definition term138 (x0 : real) (x1 : nat) (x2 : nat) := @eq real (real_zpow (real_zpow x0 (int_neg (int_of_num x1))) (int_neg (int_of_num x2))).
Definition term49 (x0 : real) := forall y0 : int, forall y1 : int, (real_zpow (real_zpow x0 y0) y1) = (real_zpow x0 (int_mul y0 y1)).
Definition term161 (x0 : real) (x1 : nat) := real_pow (real_pow (real_inv x0) x1).
Definition term191 := fun y0 : nat => True.
Definition term105 (x0 : real) (x1 : nat) := fun y0 : int => (real_zpow (real_zpow x0 (int_neg (int_of_num x1))) y0) = (real_zpow x0 (int_mul (int_neg (int_of_num x1)) y0)).
Definition term69 (x0 : real) (x1 : nat) := fun y0 : int => (real_zpow (real_zpow x0 (int_of_num x1)) y0) = (real_zpow x0 (int_mul (int_of_num x1) y0)).
Definition term4 (x0 : real) (x1 : nat) (x2 : nat) := (fun y0 : nat => (real_pow (real_pow x0 x1) y0) = (real_pow x0 (Nat.mul x1 y0))) x2.
Definition term35 (x0 : int) (x1 : int) := int_neg (int_mul x0 x1).
Definition term52 (x0 : real) (x1 : nat) := (fun y0 : int => forall y1 : int, (real_zpow (real_zpow x0 y0) y1) = (real_zpow x0 (int_mul y0 y1))) (int_of_num x1).
Definition term10 (x0 : nat) := forall y0 : nat, (int_mul (int_of_num x0) (int_of_num y0)) = (int_of_num (Nat.mul x0 y0)).
Definition term60 (x0 : real) (x1 : nat) := (fun y0 : int => forall y1 : int, (real_zpow (real_zpow x0 y0) y1) = (real_zpow x0 (int_mul y0 y1))) (int_neg (int_of_num x1)).
Definition term54 (x0 : real) := fun y0 : nat => (fun y1 : int => forall y2 : int, (real_zpow (real_zpow x0 y1) y2) = (real_zpow x0 (int_mul y1 y2))) (int_of_num y0).
Definition term23 (x0 : real) (x1 : nat) := real_zpow x0 (int_neg (int_of_num x1)).
Definition term178 (x0 : real) (x1 : nat) (x2 : nat) := real_pow (real_inv (real_zpow x0 (int_neg (int_of_num x1)))) x2.
Definition term43 (x0 : real) := forall y0 : int, (fun y1 : int => forall y2 : int, (real_zpow (real_zpow x0 y1) y2) = (real_zpow x0 (int_mul y1 y2))) y0.
Definition term190 (x0 : real) (x1 : nat) (x2 : nat) := @eq real (real_pow x0 (Nat.mul x1 x2)).
Definition term112 (x0 : real) (x1 : nat) (x2 : nat) := (fun y0 : int => (real_zpow (real_zpow x0 (int_neg (int_of_num x1))) y0) = (real_zpow x0 (int_mul (int_neg (int_of_num x1)) y0))) (int_of_num x2).
Definition term76 (x0 : real) (x1 : nat) (x2 : nat) := (fun y0 : int => (real_zpow (real_zpow x0 (int_of_num x1)) y0) = (real_zpow x0 (int_mul (int_of_num x1) y0))) (int_of_num x2).
Definition term110 (x0 : real) (x1 : nat) := @eq Prop (forall y0 : int, (fun y1 : int => (real_zpow (real_zpow x0 (int_neg (int_of_num x1))) y1) = (real_zpow x0 (int_mul (int_neg (int_of_num x1)) y1))) y0).
Definition term74 (x0 : real) (x1 : nat) := @eq Prop (forall y0 : int, (fun y1 : int => (real_zpow (real_zpow x0 (int_of_num x1)) y1) = (real_zpow x0 (int_mul (int_of_num x1) y1))) y0).
Definition term50 (x0 : real) := @eq Prop (forall y0 : int, (fun y1 : int => forall y2 : int, (real_zpow (real_zpow x0 y1) y2) = (real_zpow x0 (int_mul y1 y2))) y0).
Definition term63 (x0 : real) := fun y0 : nat => forall y1 : int, (real_zpow (real_zpow x0 (int_neg (int_of_num y0))) y1) = (real_zpow x0 (int_mul (int_neg (int_of_num y0)) y1)).
Definition term55 (x0 : real) := fun y0 : nat => forall y1 : int, (real_zpow (real_zpow x0 (int_of_num y0)) y1) = (real_zpow x0 (int_mul (int_of_num y0) y1)).
Definition term187 (x0 : real) := (forall y0 : nat, (forall y1 : nat, (real_pow (real_pow x0 y0) y1) = (real_pow x0 (Nat.mul y0 y1))) /\ (forall y1 : nat, (real_pow (real_pow (real_inv x0) y0) y1) = (real_pow (real_inv x0) (Nat.mul y0 y1)))) /\ (forall y0 : nat, (forall y1 : nat, (real_pow (real_pow (real_inv x0) y0) y1) = (real_pow (real_inv x0) (Nat.mul y0 y1))) /\ (forall y1 : nat, (real_pow (real_pow x0 y0) y1) = (real_pow x0 (Nat.mul y0 y1)))).
Definition term184 (x0 : real) (x1 : nat) := (forall y0 : nat, (real_pow (real_pow (real_inv x0) x1) y0) = (real_pow (real_inv x0) (Nat.mul x1 y0))) /\ (forall y0 : nat, (real_pow (real_pow x0 x1) y0) = (real_pow x0 (Nat.mul x1 y0))).
Definition term170 (x0 : real) (x1 : nat) := (forall y0 : nat, (real_pow (real_pow x0 x1) y0) = (real_pow x0 (Nat.mul x1 y0))) /\ (forall y0 : nat, (real_pow (real_pow (real_inv x0) x1) y0) = (real_pow (real_inv x0) (Nat.mul x1 y0))).
Definition term144 (x0 : real) := (forall y0 : nat, (forall y1 : nat, (real_zpow (real_zpow x0 (int_of_num y0)) (int_of_num y1)) = (real_zpow x0 (int_mul (int_of_num y0) (int_of_num y1)))) /\ (forall y1 : nat, (real_zpow (real_zpow x0 (int_of_num y0)) (int_neg (int_of_num y1))) = (real_zpow x0 (int_neg (int_mul (int_of_num y0) (int_of_num y1)))))) /\ (forall y0 : nat, (forall y1 : nat, (real_zpow (real_zpow x0 (int_neg (int_of_num y0))) (int_of_num y1)) = (real_zpow x0 (int_neg (int_mul (int_of_num y0) (int_of_num y1))))) /\ (forall y1 : nat, (real_zpow (real_zpow x0 (int_neg (int_of_num y0))) (int_neg (int_of_num y1))) = (real_zpow x0 (int_mul (int_of_num y0) (int_of_num y1))))).
Definition term141 (x0 : real) (x1 : nat) := (forall y0 : nat, (real_zpow (real_zpow x0 (int_neg (int_of_num x1))) (int_of_num y0)) = (real_zpow x0 (int_neg (int_mul (int_of_num x1) (int_of_num y0))))) /\ (forall y0 : nat, (real_zpow (real_zpow x0 (int_neg (int_of_num x1))) (int_neg (int_of_num y0))) = (real_zpow x0 (int_mul (int_of_num x1) (int_of_num y0)))).
Definition term128 (x0 : real) (x1 : nat) := (forall y0 : nat, (real_zpow (real_zpow x0 (int_neg (int_of_num x1))) (int_of_num y0)) = (real_zpow x0 (int_mul (int_neg (int_of_num x1)) (int_of_num y0)))) /\ (forall y0 : nat, (real_zpow (real_zpow x0 (int_neg (int_of_num x1))) (int_neg (int_of_num y0))) = (real_zpow x0 (int_mul (int_neg (int_of_num x1)) (int_neg (int_of_num y0))))).
Definition term99 (x0 : real) (x1 : nat) := (forall y0 : nat, (real_zpow (real_zpow x0 (int_of_num x1)) (int_of_num y0)) = (real_zpow x0 (int_mul (int_of_num x1) (int_of_num y0)))) /\ (forall y0 : nat, (real_zpow (real_zpow x0 (int_of_num x1)) (int_neg (int_of_num y0))) = (real_zpow x0 (int_neg (int_mul (int_of_num x1) (int_of_num y0))))).
Definition term92 (x0 : real) (x1 : nat) := (forall y0 : nat, (real_zpow (real_zpow x0 (int_of_num x1)) (int_of_num y0)) = (real_zpow x0 (int_mul (int_of_num x1) (int_of_num y0)))) /\ (forall y0 : nat, (real_zpow (real_zpow x0 (int_of_num x1)) (int_neg (int_of_num y0))) = (real_zpow x0 (int_mul (int_of_num x1) (int_neg (int_of_num y0))))).
Definition term59 (x0 : real) := and (forall y0 : nat, forall y1 : int, (real_zpow (real_zpow x0 (int_of_num y0)) y1) = (real_zpow x0 (int_mul (int_of_num y0) y1))).
Definition term27 (x0 : real) (x1 : nat) := (fun y0 : nat => (real_zpow x0 (int_of_num y0)) = (real_pow x0 y0)) x1.
Definition term164 (x0 : nat) (x1 : nat) := int_neg (int_of_num (Nat.mul x0 x1)).
Definition term136 (x0 : nat) := int_neg (int_of_num x0).
Definition term9 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (int_mul (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.mul y0 y1))) x0.
Definition term11 (x0 : nat) (x1 : nat) := (fun y0 : nat => (int_mul (int_of_num x0) (int_of_num y0)) = (int_of_num (Nat.mul x0 y0))) x1.
Definition term0 (x0 : real) := (fun y0 : real => forall y1 : nat, forall y2 : nat, (real_pow (real_pow y0 y1) y2) = (real_pow y0 (Nat.mul y1 y2))) x0.
Definition term96 (x0 : real) (x1 : nat) (x2 : nat) := @eq real (real_zpow (real_zpow x0 (int_of_num x1)) (int_neg (int_of_num x2))).
Definition term18 (x0 : real) (x1 : nat) := real_pow (real_inv x0) x1.
Definition term109 (x0 : real) (x1 : nat) := fun y0 : int => (fun y1 : int => (real_zpow (real_zpow x0 (int_neg (int_of_num x1))) y1) = (real_zpow x0 (int_mul (int_neg (int_of_num x1)) y1))) y0.
Definition term73 (x0 : real) (x1 : nat) := fun y0 : int => (fun y1 : int => (real_zpow (real_zpow x0 (int_of_num x1)) y1) = (real_zpow x0 (int_mul (int_of_num x1) y1))) y0.
Definition term117 (x0 : real) (x1 : nat) := forall y0 : nat, (fun y1 : int => (real_zpow (real_zpow x0 (int_neg (int_of_num x1))) y1) = (real_zpow x0 (int_mul (int_neg (int_of_num x1)) y1))) (int_of_num y0).
Definition term81 (x0 : real) (x1 : nat) := forall y0 : nat, (fun y1 : int => (real_zpow (real_zpow x0 (int_of_num x1)) y1) = (real_zpow x0 (int_mul (int_of_num x1) y1))) (int_of_num y0).
Definition term106 (x0 : real) (x1 : nat) (x2 : int) := (fun y0 : int => (real_zpow (real_zpow x0 (int_neg (int_of_num x1))) y0) = (real_zpow x0 (int_mul (int_neg (int_of_num x1)) y0))) x2.
Definition term70 (x0 : real) (x1 : nat) (x2 : int) := (fun y0 : int => (real_zpow (real_zpow x0 (int_of_num x1)) y0) = (real_zpow x0 (int_mul (int_of_num x1) y0))) x2.
Definition term140 (x0 : real) (x1 : nat) := forall y0 : nat, (real_zpow (real_zpow x0 (int_neg (int_of_num x1))) (int_neg (int_of_num y0))) = (real_zpow x0 (int_mul (int_of_num x1) (int_of_num y0))).
Definition term127 (x0 : real) (x1 : nat) := forall y0 : nat, (real_zpow (real_zpow x0 (int_neg (int_of_num x1))) (int_neg (int_of_num y0))) = (real_zpow x0 (int_mul (int_neg (int_of_num x1)) (int_neg (int_of_num y0)))).
Definition term118 (x0 : real) (x1 : nat) := forall y0 : nat, (real_zpow (real_zpow x0 (int_neg (int_of_num x1))) (int_of_num y0)) = (real_zpow x0 (int_mul (int_neg (int_of_num x1)) (int_of_num y0))).
Definition term91 (x0 : real) (x1 : nat) := forall y0 : nat, (real_zpow (real_zpow x0 (int_of_num x1)) (int_neg (int_of_num y0))) = (real_zpow x0 (int_mul (int_of_num x1) (int_neg (int_of_num y0)))).
Definition term82 (x0 : real) (x1 : nat) := forall y0 : nat, (real_zpow (real_zpow x0 (int_of_num x1)) (int_of_num y0)) = (real_zpow x0 (int_mul (int_of_num x1) (int_of_num y0))).
Definition term189 := forall y0 : real, (forall y1 : nat, (forall y2 : nat, (real_pow (real_pow y0 y1) y2) = (real_pow y0 (Nat.mul y1 y2))) /\ (forall y2 : nat, (real_pow (real_pow (real_inv y0) y1) y2) = (real_pow (real_inv y0) (Nat.mul y1 y2)))) /\ (forall y1 : nat, (forall y2 : nat, (real_pow (real_pow (real_inv y0) y1) y2) = (real_pow (real_inv y0) (Nat.mul y1 y2))) /\ (forall y2 : nat, (real_pow (real_pow y0 y1) y2) = (real_pow y0 (Nat.mul y1 y2)))).
Definition term148 := forall y0 : real, (forall y1 : nat, (forall y2 : nat, (real_zpow (real_zpow y0 (int_of_num y1)) (int_of_num y2)) = (real_zpow y0 (int_mul (int_of_num y1) (int_of_num y2)))) /\ (forall y2 : nat, (real_zpow (real_zpow y0 (int_of_num y1)) (int_neg (int_of_num y2))) = (real_zpow y0 (int_neg (int_mul (int_of_num y1) (int_of_num y2)))))) /\ (forall y1 : nat, (forall y2 : nat, (real_zpow (real_zpow y0 (int_neg (int_of_num y1))) (int_of_num y2)) = (real_zpow y0 (int_neg (int_mul (int_of_num y1) (int_of_num y2))))) /\ (forall y2 : nat, (real_zpow (real_zpow y0 (int_neg (int_of_num y1))) (int_neg (int_of_num y2))) = (real_zpow y0 (int_mul (int_of_num y1) (int_of_num y2))))).
Definition term107 (x0 : real) (x1 : nat) (x2 : int) := real_zpow (real_zpow x0 (int_neg (int_of_num x1))) x2.
Definition term34 (x0 : int) (x1 : int) := int_mul x0 (int_neg x1).
Definition term169 (x0 : real) (x1 : nat) := forall y0 : nat, (real_pow (real_pow (real_inv x0) x1) y0) = (real_pow (real_inv x0) (Nat.mul x1 y0)).
Definition term165 (x0 : real) (x1 : nat) (x2 : nat) := real_zpow x0 (int_neg (int_of_num (Nat.mul x1 x2))).
Definition term64 (x0 : real) := forall y0 : nat, (fun y1 : int => forall y2 : int, (real_zpow (real_zpow x0 y1) y2) = (real_zpow x0 (int_mul y1 y2))) (int_neg (int_of_num y0)).
Definition term21 (x0 : real) := forall y0 : nat, (real_zpow x0 (int_neg (int_of_num y0))) = (real_inv (real_pow x0 y0)).
Definition term137 (x0 : nat) (x1 : nat) := int_neg (int_neg (int_mul (int_of_num x0) (int_of_num x1))).
Definition term135 (x0 : nat) (x1 : nat) := int_neg (int_mul (int_of_num x0) (int_neg (int_of_num x1))).
Definition term17 (x0 : real) (x1 : nat) := real_inv (real_pow x0 x1).
Definition term195 (x0 : real) (x1 : nat) (x2 : nat) := @eq real (real_pow (real_inv x0) (Nat.mul x1 x2)).
Definition term28 (x0 : real) (x1 : nat) := real_zpow x0 (int_of_num x1).
Definition term160 (x0 : real) (x1 : nat) := real_pow (real_inv (real_zpow x0 (int_of_num x1))).
Definition term194 (x0 : Prop) := forall y0 : nat, x0.
Definition term15 (x0 : real) := forall y0 : nat, (real_inv (real_pow x0 y0)) = (real_pow (real_inv x0) y0).
Definition term6 (x0 : real) (x1 : nat) (x2 : nat) := real_pow x0 (Nat.mul x1 x2).
Definition term150 (x0 : real) (x1 : nat) := real_pow (real_zpow x0 (int_of_num x1)).
Definition term3 (x0 : real) (x1 : nat) := forall y0 : nat, (real_pow (real_pow x0 x1) y0) = (real_pow x0 (Nat.mul x1 y0)).
Definition term186 (x0 : real) := forall y0 : nat, (forall y1 : nat, (real_pow (real_pow (real_inv x0) y0) y1) = (real_pow (real_inv x0) (Nat.mul y0 y1))) /\ (forall y1 : nat, (real_pow (real_pow x0 y0) y1) = (real_pow x0 (Nat.mul y0 y1))).
Definition term172 (x0 : real) := forall y0 : nat, (forall y1 : nat, (real_pow (real_pow x0 y0) y1) = (real_pow x0 (Nat.mul y0 y1))) /\ (forall y1 : nat, (real_pow (real_pow (real_inv x0) y0) y1) = (real_pow (real_inv x0) (Nat.mul y0 y1))).
Definition term143 (x0 : real) := forall y0 : nat, (forall y1 : nat, (real_zpow (real_zpow x0 (int_neg (int_of_num y0))) (int_of_num y1)) = (real_zpow x0 (int_neg (int_mul (int_of_num y0) (int_of_num y1))))) /\ (forall y1 : nat, (real_zpow (real_zpow x0 (int_neg (int_of_num y0))) (int_neg (int_of_num y1))) = (real_zpow x0 (int_mul (int_of_num y0) (int_of_num y1)))).
Definition term101 (x0 : real) := forall y0 : nat, (forall y1 : nat, (real_zpow (real_zpow x0 (int_of_num y0)) (int_of_num y1)) = (real_zpow x0 (int_mul (int_of_num y0) (int_of_num y1)))) /\ (forall y1 : nat, (real_zpow (real_zpow x0 (int_of_num y0)) (int_neg (int_of_num y1))) = (real_zpow x0 (int_neg (int_mul (int_of_num y0) (int_of_num y1))))).
Definition term87 (x0 : real) (x1 : nat) (x2 : nat) := real_zpow x0 (int_mul (int_of_num x1) (int_neg (int_of_num x2))).
Definition term38 (x0 : int) (x1 : int) := (fun y0 : int => (int_mul (int_neg x0) y0) = (int_neg (int_mul x0 y0))) x1.
Definition term126 (x0 : real) (x1 : nat) := forall y0 : nat, (fun y1 : int => (real_zpow (real_zpow x0 (int_neg (int_of_num x1))) y1) = (real_zpow x0 (int_mul (int_neg (int_of_num x1)) y1))) (int_neg (int_of_num y0)).
Definition term90 (x0 : real) (x1 : nat) := forall y0 : nat, (fun y1 : int => (real_zpow (real_zpow x0 (int_of_num x1)) y1) = (real_zpow x0 (int_mul (int_of_num x1) y1))) (int_neg (int_of_num y0)).
Definition term166 (x0 : real) (x1 : nat) (x2 : nat) := real_inv (real_pow x0 (Nat.mul x1 x2)).
Definition term121 (x0 : real) (x1 : nat) (x2 : nat) := (fun y0 : int => (real_zpow (real_zpow x0 (int_neg (int_of_num x1))) y0) = (real_zpow x0 (int_mul (int_neg (int_of_num x1)) y0))) (int_neg (int_of_num x2)).
Definition term85 (x0 : real) (x1 : nat) (x2 : nat) := (fun y0 : int => (real_zpow (real_zpow x0 (int_of_num x1)) y0) = (real_zpow x0 (int_mul (int_of_num x1) y0))) (int_neg (int_of_num x2)).
Definition term56 (x0 : real) := forall y0 : nat, (fun y1 : int => forall y2 : int, (real_zpow (real_zpow x0 y1) y2) = (real_zpow x0 (int_mul y1 y2))) (int_of_num y0).
Definition term62 (x0 : real) := fun y0 : nat => (fun y1 : int => forall y2 : int, (real_zpow (real_zpow x0 y1) y2) = (real_zpow x0 (int_mul y1 y2))) (int_neg (int_of_num y0)).
Definition term131 (x0 : real) (x1 : nat) := fun y0 : nat => (real_zpow (real_zpow x0 (int_neg (int_of_num x1))) (int_of_num y0)) = (real_zpow x0 (int_neg (int_mul (int_of_num x1) (int_of_num y0)))).
Definition term151 (x0 : real) (x1 : nat) := real_pow (real_pow x0 x1).
Definition term103 (x0 : real) (x1 : nat) := forall y0 : int, (fun y1 : int => (real_zpow (real_zpow x0 (int_neg (int_of_num x1))) y1) = (real_zpow x0 (int_mul (int_neg (int_of_num x1)) y1))) y0.
Definition term67 (x0 : real) (x1 : nat) := forall y0 : int, (fun y1 : int => (real_zpow (real_zpow x0 (int_of_num x1)) y1) = (real_zpow x0 (int_mul (int_of_num x1) y1))) y0.
Definition term12 (x0 : nat) (x1 : nat) := int_mul (int_of_num x0) (int_of_num x1).
Definition term124 (x0 : real) (x1 : nat) := fun y0 : nat => (fun y1 : int => (real_zpow (real_zpow x0 (int_neg (int_of_num x1))) y1) = (real_zpow x0 (int_mul (int_neg (int_of_num x1)) y1))) (int_neg (int_of_num y0)).
Definition term88 (x0 : real) (x1 : nat) := fun y0 : nat => (fun y1 : int => (real_zpow (real_zpow x0 (int_of_num x1)) y1) = (real_zpow x0 (int_mul (int_of_num x1) y1))) (int_neg (int_of_num y0)).
Definition term48 (x0 : real) := fun y0 : int => (fun y1 : int => forall y2 : int, (real_zpow (real_zpow x0 y1) y2) = (real_zpow x0 (int_mul y1 y2))) y0.
Definition term77 (x0 : real) (x1 : nat) (x2 : nat) := real_zpow (real_zpow x0 (int_of_num x1)) (int_of_num x2).
