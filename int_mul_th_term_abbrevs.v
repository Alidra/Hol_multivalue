Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term29 (x0 : real) (x1 : real) := (fun y0 : real => (real_mul (real_neg x0) y0) = (real_neg (real_mul x0 y0))) x1.
Definition term13 (x0 : real) := forall y0 : real, ((real_neg x0) = (real_neg y0)) = (x0 = y0).
Definition term38 (x0 : int) (x1 : int) := int_of_real (real_mul (real_of_int x0) (real_of_int x1)).
Definition term21 (x0 : real) := real_neg (real_neg x0).
Definition term81 (x0 : nat) (x1 : nat) := @eq real (real_mul (real_of_num x0) (real_of_num x1)).
Definition term106 (x0 : nat) (x1 : nat) := @eq real (real_mul (real_neg (real_of_num x0)) (real_neg (real_of_num x1))).
Definition term62 (x0 : nat) := real_neg (real_of_num x0).
Definition term60 (x0 : int) (x1 : int) (x2 : nat) := or ((real_mul (real_of_int x0) (real_of_int x1)) = (real_of_num x2)).
Definition term3 (a0 : Type') (x0 : a0) := exists y0 : a0, x0 = y0.
Definition term63 (x0 : int) (x1 : int) (x2 : nat) := ((fun y0 : nat => (real_mul (real_of_int x0) (real_of_int x1)) = (real_of_num y0)) x2) \/ ((fun y0 : nat => (real_mul (real_of_int x0) (real_of_int x1)) = (real_neg (real_of_num y0))) x2).
Definition term24 (x0 : real) (x1 : real) := (fun y0 : real => (real_mul x0 (real_neg y0)) = (real_neg (real_mul x0 y0))) x1.
Definition term43 (x0 : int) (x1 : int) := real_mul (real_of_int x0) (real_of_int x1).
Definition term61 (x0 : int) (x1 : int) (x2 : nat) := (fun y0 : nat => (real_mul (real_of_int x0) (real_of_int x1)) = (real_neg (real_of_num y0))) x2.
Definition term125 (x0 : nat) (x1 : nat) := or (exists y0 : nat, (real_neg (real_of_num (Nat.mul x0 x1))) = (real_of_num y0)).
Definition term116 (x0 : nat) (x1 : nat) := or (exists y0 : nat, (real_of_num (Nat.mul x0 x1)) = (real_of_num y0)).
Definition term109 (x0 : nat) (x1 : nat) := or (exists y0 : nat, (real_mul (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) = (real_of_num y0)).
Definition term101 (x0 : nat) (x1 : nat) := or (exists y0 : nat, (real_mul (real_neg (real_of_num x0)) (real_of_num x1)) = (real_of_num y0)).
Definition term92 (x0 : nat) (x1 : nat) := or (exists y0 : nat, (real_mul (real_of_num x0) (real_neg (real_of_num x1))) = (real_of_num y0)).
Definition term84 (x0 : nat) (x1 : nat) := or (exists y0 : nat, (real_mul (real_of_num x0) (real_of_num x1)) = (real_of_num y0)).
Definition term73 (x0 : int) (x1 : int) := or (exists y0 : nat, (real_mul (real_of_int x0) (real_of_int x1)) = (real_of_num y0)).
Definition term128 (x0 : nat) (x1 : nat) := (exists y0 : nat, (real_neg (real_of_num (Nat.mul x0 x1))) = (real_of_num y0)) \/ (exists y0 : nat, (real_neg (real_of_num (Nat.mul x0 x1))) = (real_neg (real_of_num y0))).
Definition term119 (x0 : nat) (x1 : nat) := (exists y0 : nat, (real_of_num (Nat.mul x0 x1)) = (real_of_num y0)) \/ (exists y0 : nat, (real_of_num (Nat.mul x0 x1)) = (real_neg (real_of_num y0))).
Definition term112 (x0 : nat) (x1 : nat) := (exists y0 : nat, (real_mul (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) = (real_of_num y0)) \/ (exists y0 : nat, (real_mul (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) = (real_neg (real_of_num y0))).
Definition term104 (x0 : nat) (x1 : nat) := (exists y0 : nat, (real_mul (real_neg (real_of_num x0)) (real_of_num x1)) = (real_of_num y0)) \/ (exists y0 : nat, (real_mul (real_neg (real_of_num x0)) (real_of_num x1)) = (real_neg (real_of_num y0))).
Definition term95 (x0 : nat) (x1 : nat) := (exists y0 : nat, (real_mul (real_of_num x0) (real_neg (real_of_num x1))) = (real_of_num y0)) \/ (exists y0 : nat, (real_mul (real_of_num x0) (real_neg (real_of_num x1))) = (real_neg (real_of_num y0))).
Definition term87 (x0 : nat) (x1 : nat) := (exists y0 : nat, (real_mul (real_of_num x0) (real_of_num x1)) = (real_of_num y0)) \/ (exists y0 : nat, (real_mul (real_of_num x0) (real_of_num x1)) = (real_neg (real_of_num y0))).
Definition term77 (x0 : int) (x1 : int) := (exists y0 : nat, (real_mul (real_of_int x0) (real_of_int x1)) = (real_of_num y0)) \/ (exists y0 : nat, (real_mul (real_of_int x0) (real_of_int x1)) = (real_neg (real_of_num y0))).
Definition term51 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term35 (x0 : int) := (fun y0 : int => forall y1 : int, (int_mul y0 y1) = (int_of_real (real_mul (real_of_int y0) (real_of_int y1)))) x0.
Definition term124 (x0 : nat) (x1 : nat) := exists y0 : nat, (real_neg (real_of_num (Nat.mul x0 x1))) = (real_of_num y0).
Definition term115 (x0 : nat) (x1 : nat) := exists y0 : nat, (real_of_num (Nat.mul x0 x1)) = (real_of_num y0).
Definition term74 (x0 : int) (x1 : int) := fun y0 : nat => (fun y1 : nat => (real_mul (real_of_int x0) (real_of_int x1)) = (real_neg (real_of_num y1))) y0.
Definition term134 (x0 : nat) (x1 : nat) := True \/ (exists y0 : nat, (real_of_num (Nat.mul x0 x1)) = (real_neg (real_of_num y0))).
Definition term80 (x0 : int) (x1 : int) := @eq real (real_mul (real_of_int x0) (real_of_int x1)).
Definition term120 (x0 : nat) (x1 : nat) := real_neg (real_mul (real_of_num x0) (real_of_num x1)).
Definition term132 (x0 : nat) (x1 : nat) := exists y0 : nat, (Nat.mul x0 x1) = y0.
Definition term66 (x0 : int) (x1 : int) := fun y0 : nat => ((real_mul (real_of_int x0) (real_of_int x1)) = (real_of_num y0)) \/ ((real_mul (real_of_int x0) (real_of_int x1)) = (real_neg (real_of_num y0))).
Definition term10 (x0 : nat) := forall y0 : nat, ((real_of_num x0) = (real_of_num y0)) = (x0 = y0).
Definition term110 (x0 : nat) (x1 : nat) := fun y0 : nat => (real_mul (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) = (real_neg (real_of_num y0)).
Definition term93 (x0 : nat) (x1 : nat) := fun y0 : nat => (real_mul (real_of_num x0) (real_neg (real_of_num x1))) = (real_neg (real_of_num y0)).
Definition term58 (x0 : int) (x1 : int) (x2 : nat) := (fun y0 : nat => (real_mul (real_of_int x0) (real_of_int x1)) = (real_of_num y0)) x2.
Definition term133 (x0 : nat) := exists y0 : nat, x0 = y0.
Definition term130 (x0 : nat) (x1 : nat) := real_neg (real_neg (real_of_num (Nat.mul x0 x1))).
Definition term5 (a0 : Type') := fun y0 : a0 => exists y1 : a0, y0 = y1.
Definition term36 (x0 : int) := forall y0 : int, (int_mul x0 y0) = (int_of_real (real_mul (real_of_int x0) (real_of_int y0))).
Definition term25 (x0 : real) (x1 : real) := real_mul x0 (real_neg x1).
Definition term107 (x0 : nat) (x1 : nat) := fun y0 : nat => (real_mul (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) = (real_of_num y0).
Definition term90 (x0 : nat) (x1 : nat) := fun y0 : nat => (real_mul (real_of_num x0) (real_neg (real_of_num x1))) = (real_of_num y0).
Definition term34 (x0 : real) := real_of_int (int_of_real x0).
Definition term7 (a0 : Type') := forall y0 : a0, exists y1 : a0, y0 = y1.
Definition term6 (a0 : Type') := forall y0 : a0, exists y1 : a0, y1 = y0.
Definition term8 (a0 : Type') (x0 : a0) := (fun y0 : a0 => exists y1 : a0, y0 = y1) x0.
Definition term69 (x0 : int) (x1 : int) := fun y0 : nat => (fun y1 : nat => (real_mul (real_of_int x0) (real_of_int x1)) = (real_of_num y1)) y0.
Definition term122 (x0 : nat) (x1 : nat) := @eq real (real_neg (real_of_num (Nat.mul x0 x1))).
Definition term40 (x0 : int) (x1 : int) := real_of_int (int_of_real (real_mul (real_of_int x0) (real_of_int x1))).
Definition term117 (x0 : nat) (x1 : nat) := fun y0 : nat => (real_of_num (Nat.mul x0 x1)) = (real_neg (real_of_num y0)).
Definition term31 (x0 : int) := (fun y0 : int => exists y1 : nat, ((real_of_int y0) = (real_of_num y1)) \/ ((real_of_int y0) = (real_neg (real_of_num y1)))) x0.
Definition term137 (x0 : int) := forall y0 : int, (real_of_int (int_mul x0 y0)) = (real_mul (real_of_int x0) (real_of_int y0)).
Definition term136 (x0 : int) := fun y0 : nat => ((real_of_int x0) = (real_of_num y0)) \/ ((real_of_int x0) = (real_neg (real_of_num y0))).
Definition term48 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (exists y1 : a0, (x0 y1) \/ (y0 y1)) = ((exists y1 : a0, x0 y1) \/ (exists y1 : a0, y0 y1)).
Definition term17 (x0 : nat) (x1 : nat) := (fun y0 : nat => (real_mul (real_of_num x0) (real_of_num y0)) = (real_of_num (Nat.mul x0 y0))) x1.
Definition term26 (x0 : real) (x1 : real) := real_neg (real_mul x0 x1).
Definition term127 (x0 : nat) (x1 : nat) := exists y0 : nat, (real_neg (real_of_num (Nat.mul x0 x1))) = (real_neg (real_of_num y0)).
Definition term118 (x0 : nat) (x1 : nat) := exists y0 : nat, (real_of_num (Nat.mul x0 x1)) = (real_neg (real_of_num y0)).
Definition term68 (x0 : int) (x1 : int) := @eq Prop (exists y0 : nat, ((real_mul (real_of_int x0) (real_of_int x1)) = (real_of_num y0)) \/ ((real_mul (real_of_int x0) (real_of_int x1)) = (real_neg (real_of_num y0)))).
Definition term67 (x0 : int) (x1 : int) := @eq Prop (exists y0 : nat, ((fun y1 : nat => (real_mul (real_of_int x0) (real_of_int x1)) = (real_of_num y1)) y0) \/ ((fun y1 : nat => (real_mul (real_of_int x0) (real_of_int x1)) = (real_neg (real_of_num y1))) y0)).
Definition term46 (x0 : int) (x1 : int) := exists y0 : nat, ((real_mul (real_of_int x0) (real_of_int x1)) = (real_of_num y0)) \/ ((real_mul (real_of_int x0) (real_of_int x1)) = (real_neg (real_of_num y0))).
Definition term32 (x0 : int) := exists y0 : nat, ((real_of_int x0) = (real_of_num y0)) \/ ((real_of_int x0) = (real_neg (real_of_num y0))).
Definition term96 (x0 : nat) := real_mul (real_neg (real_of_num x0)).
Definition term89 (x0 : nat) (x1 : nat) := @eq real (real_mul (real_of_num x0) (real_neg (real_of_num x1))).
Definition term99 (x0 : nat) (x1 : nat) := fun y0 : nat => (real_mul (real_neg (real_of_num x0)) (real_of_num x1)) = (real_of_num y0).
Definition term82 (x0 : nat) (x1 : nat) := fun y0 : nat => (real_mul (real_of_num x0) (real_of_num x1)) = (real_of_num y0).
Definition term56 (x0 : int) (x1 : int) := fun y0 : nat => (real_mul (real_of_int x0) (real_of_int x1)) = (real_of_num y0).
Definition term126 (x0 : nat) (x1 : nat) := fun y0 : nat => (real_neg (real_of_num (Nat.mul x0 x1))) = (real_neg (real_of_num y0)).
Definition term111 (x0 : nat) (x1 : nat) := exists y0 : nat, (real_mul (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) = (real_neg (real_of_num y0)).
Definition term103 (x0 : nat) (x1 : nat) := exists y0 : nat, (real_mul (real_neg (real_of_num x0)) (real_of_num x1)) = (real_neg (real_of_num y0)).
Definition term94 (x0 : nat) (x1 : nat) := exists y0 : nat, (real_mul (real_of_num x0) (real_neg (real_of_num x1))) = (real_neg (real_of_num y0)).
Definition term86 (x0 : nat) (x1 : nat) := exists y0 : nat, (real_mul (real_of_num x0) (real_of_num x1)) = (real_neg (real_of_num y0)).
Definition term76 (x0 : int) (x1 : int) := exists y0 : nat, (real_mul (real_of_int x0) (real_of_int x1)) = (real_neg (real_of_num y0)).
Definition term55 (x0 : int) (x1 : int) := (exists y0 : nat, (fun y1 : nat => (real_mul (real_of_int x0) (real_of_int x1)) = (real_of_num y1)) y0) \/ (exists y0 : nat, (fun y1 : nat => (real_mul (real_of_int x0) (real_of_int x1)) = (real_neg (real_of_num y1))) y0).
Definition term108 (x0 : nat) (x1 : nat) := exists y0 : nat, (real_mul (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) = (real_of_num y0).
Definition term100 (x0 : nat) (x1 : nat) := exists y0 : nat, (real_mul (real_neg (real_of_num x0)) (real_of_num x1)) = (real_of_num y0).
Definition term91 (x0 : nat) (x1 : nat) := exists y0 : nat, (real_mul (real_of_num x0) (real_neg (real_of_num x1))) = (real_of_num y0).
Definition term83 (x0 : nat) (x1 : nat) := exists y0 : nat, (real_mul (real_of_num x0) (real_of_num x1)) = (real_of_num y0).
Definition term71 (x0 : int) (x1 : int) := exists y0 : nat, (real_mul (real_of_int x0) (real_of_int x1)) = (real_of_num y0).
Definition term135 (x0 : nat) (x1 : nat) := (exists y0 : nat, (real_neg (real_of_num (Nat.mul x0 x1))) = (real_of_num y0)) \/ True.
Definition term113 (x0 : nat) (x1 : nat) := @eq real (real_of_num (Nat.mul x0 x1)).
Definition term98 (x0 : nat) (x1 : nat) := @eq real (real_mul (real_neg (real_of_num x0)) (real_of_num x1)).
Definition term97 (x0 : nat) (x1 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num x1).
Definition term20 (x0 : real) := (fun y0 : real => (real_neg (real_neg y0)) = y0) x0.
Definition term54 (x0 : int) (x1 : int) := exists y0 : nat, ((fun y1 : nat => (real_mul (real_of_int x0) (real_of_int x1)) = (real_of_num y1)) y0) \/ ((fun y1 : nat => (real_mul (real_of_int x0) (real_of_int x1)) = (real_neg (real_of_num y1))) y0).
Definition term23 (x0 : real) := forall y0 : real, (real_mul x0 (real_neg y0)) = (real_neg (real_mul x0 y0)).
Definition term33 (x0 : int) (x1 : nat) := ((real_of_int x0) = (real_of_num x1)) \/ ((real_of_int x0) = (real_neg (real_of_num x1))).
Definition term138 := forall y0 : int, forall y1 : int, (real_of_int (int_mul y0 y1)) = (real_mul (real_of_int y0) (real_of_int y1)).
Definition term27 (x0 : real) := (fun y0 : real => forall y1 : real, (real_mul (real_neg y0) y1) = (real_neg (real_mul y0 y1))) x0.
Definition term22 (x0 : real) := (fun y0 : real => forall y1 : real, (real_mul y0 (real_neg y1)) = (real_neg (real_mul y0 y1))) x0.
Definition term12 (x0 : real) := (fun y0 : real => forall y1 : real, ((real_neg y0) = (real_neg y1)) = (y0 = y1)) x0.
Definition term47 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (exists y2 : a0, (y0 y2) \/ (y1 y2)) = ((exists y2 : a0, y0 y2) \/ (exists y2 : a0, y1 y2))) x0.
Definition term30 (x0 : real) (x1 : real) := real_mul (real_neg x0) x1.
Definition term79 (x0 : nat) := real_mul (real_of_num x0).
Definition term102 (x0 : nat) (x1 : nat) := fun y0 : nat => (real_mul (real_neg (real_of_num x0)) (real_of_num x1)) = (real_neg (real_of_num y0)).
Definition term85 (x0 : nat) (x1 : nat) := fun y0 : nat => (real_mul (real_of_num x0) (real_of_num x1)) = (real_neg (real_of_num y0)).
Definition term57 (x0 : int) (x1 : int) := fun y0 : nat => (real_mul (real_of_int x0) (real_of_int x1)) = (real_neg (real_of_num y0)).
Definition term2 (a0 : Type') (x0 : a0) := exists y0 : a0, y0 = x0.
Definition term4 (a0 : Type') := fun y0 : a0 => exists y1 : a0, y1 = y0.
Definition term88 (x0 : nat) (x1 : nat) := real_mul (real_of_num x0) (real_neg (real_of_num x1)).
Definition term75 (x0 : int) (x1 : int) := exists y0 : nat, (fun y1 : nat => (real_mul (real_of_int x0) (real_of_int x1)) = (real_neg (real_of_num y1))) y0.
Definition term70 (x0 : int) (x1 : int) := exists y0 : nat, (fun y1 : nat => (real_mul (real_of_int x0) (real_of_int x1)) = (real_of_num y1)) y0.
Definition term14 (x0 : real) (x1 : real) := (fun y0 : real => ((real_neg x0) = (real_neg y0)) = (x0 = y0)) x1.
Definition term123 (x0 : nat) (x1 : nat) := fun y0 : nat => (real_neg (real_of_num (Nat.mul x0 x1))) = (real_of_num y0).
Definition term0 (a0 : Type') (x0 : a0) := fun y0 : a0 => y0 = x0.
Definition term28 (x0 : real) := forall y0 : real, (real_mul (real_neg x0) y0) = (real_neg (real_mul x0 y0)).
Definition term18 (x0 : nat) (x1 : nat) := real_mul (real_of_num x0) (real_of_num x1).
Definition term64 (x0 : int) (x1 : int) (x2 : nat) := ((real_mul (real_of_int x0) (real_of_int x1)) = (real_of_num x2)) \/ ((real_mul (real_of_int x0) (real_of_int x1)) = (real_neg (real_of_num x2))).
Definition term121 (x0 : nat) (x1 : nat) := real_neg (real_of_num (Nat.mul x0 x1)).
Definition term41 (x0 : int) (x1 : int) := @eq real (real_of_int (int_mul x0 x1)).
Definition term15 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (real_mul (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.mul y0 y1))) x0.
Definition term9 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((real_of_num y0) = (real_of_num y1)) = (y0 = y1)) x0.
Definition term105 (x0 : nat) (x1 : nat) := real_mul (real_neg (real_of_num x0)) (real_neg (real_of_num x1)).
Definition term42 (x0 : int) (x1 : int) := @eq real (real_of_int (int_of_real (real_mul (real_of_int x0) (real_of_int x1)))).
Definition term16 (x0 : nat) := forall y0 : nat, (real_mul (real_of_num x0) (real_of_num y0)) = (real_of_num (Nat.mul x0 y0)).
Definition term131 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.mul x0 x1) = y0.
Definition term59 (x0 : int) (x1 : int) (x2 : nat) := or ((fun y0 : nat => (real_mul (real_of_int x0) (real_of_int x1)) = (real_of_num y0)) x2).
Definition term39 (x0 : int) (x1 : int) := real_of_int (int_mul x0 x1).
Definition term129 (x0 : nat) (x1 : nat) := real_neg (real_mul (real_of_num x0) (real_neg (real_of_num x1))).
Definition term45 (x0 : real) := exists y0 : nat, (x0 = (real_of_num y0)) \/ (x0 = (real_neg (real_of_num y0))).
Definition term19 (x0 : nat) (x1 : nat) := real_of_num (Nat.mul x0 x1).
Definition term37 (x0 : int) (x1 : int) := (fun y0 : int => (int_mul x0 y0) = (int_of_real (real_mul (real_of_int x0) (real_of_int y0)))) x1.
Definition term52 (x0 : nat -> Prop) (x1 : nat -> Prop) := exists y0 : nat, (x0 y0) \/ (x1 y0).
Definition term1 (a0 : Type') (x0 : a0) := fun y0 : a0 => x0 = y0.
Definition term65 (x0 : int) (x1 : int) := fun y0 : nat => ((fun y1 : nat => (real_mul (real_of_int x0) (real_of_int x1)) = (real_of_num y1)) y0) \/ ((fun y1 : nat => (real_mul (real_of_int x0) (real_of_int x1)) = (real_neg (real_of_num y1))) y0).
Definition term72 (x0 : int) (x1 : int) := or (exists y0 : nat, (fun y1 : nat => (real_mul (real_of_int x0) (real_of_int x1)) = (real_of_num y1)) y0).
Definition term114 (x0 : nat) (x1 : nat) := fun y0 : nat => (real_of_num (Nat.mul x0 x1)) = (real_of_num y0).
Definition term11 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((real_of_num x0) = (real_of_num y0)) = (x0 = y0)) x1.
Definition term78 (x0 : int) := real_mul (real_of_int x0).
Definition term50 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term49 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (exists y1 : a0, (x0 y1) \/ (y0 y1)) = ((exists y1 : a0, x0 y1) \/ (exists y1 : a0, y0 y1))) x1.
Definition term53 (x0 : nat -> Prop) (x1 : nat -> Prop) := (exists y0 : nat, x0 y0) \/ (exists y0 : nat, x1 y0).
Definition term44 (x0 : int) (x1 : int) := integer (real_mul (real_of_int x0) (real_of_int x1)).
