Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term28 (x0 : nat) (x1 : nat) := real_lt (real_of_num x0) (real_of_num x1).
Definition term62 (x0 : nat) := fun y0 : nat => (real_gt (real_of_num x0) (real_of_num y0)) = (Peano.gt x0 y0).
Definition term96 (x0 : nat) (x1 : nat) := @eq real (real_mul (real_of_num x0) (real_of_num x1)).
Definition term80 (x0 : nat) := fun y0 : nat => (real_max (real_of_num x0) (real_of_num y0)) = (real_of_num (Nat.max x0 y0)).
Definition term90 (x0 : nat) (x1 : nat) := @eq real (real_add (real_of_num x0) (real_of_num x1)).
Definition term39 (x0 : nat) (x1 : nat) := (fun y0 : nat => (real_ge (real_of_num x0) (real_of_num y0)) = (Peano.ge x0 y0)) x1.
Definition term92 (x0 : nat) := fun y0 : nat => (real_add (real_of_num x0) (real_of_num y0)) = (real_of_num (Nat.add x0 y0)).
Definition term49 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term107 := (forall y0 : nat, forall y1 : nat, (real_mul (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.mul y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (real_pow (real_of_num y0) y1) = (real_of_num (Nat.pow y0 y1))).
Definition term13 (x0 : nat) (x1 : nat) := real_add (real_of_num x0) (real_of_num x1).
Definition term42 (x0 : nat) := forall y0 : nat, ((real_of_num x0) = (real_of_num y0)) = (x0 = y0).
Definition term38 (x0 : nat) := forall y0 : nat, (real_ge (real_of_num x0) (real_of_num y0)) = (Peano.ge x0 y0).
Definition term34 (x0 : nat) := forall y0 : nat, (real_gt (real_of_num x0) (real_of_num y0)) = (Peano.gt x0 y0).
Definition term30 (x0 : nat) := forall y0 : nat, (real_le (real_of_num x0) (real_of_num y0)) = (Peano.le x0 y0).
Definition term26 (x0 : nat) := forall y0 : nat, (real_lt (real_of_num x0) (real_of_num y0)) = (Peano.lt x0 y0).
Definition term60 (x0 : nat) (x1 : nat) := @eq Prop (real_gt (real_of_num x0) (real_of_num x1)).
Definition term68 (x0 : nat) := fun y0 : nat => (real_le (real_of_num x0) (real_of_num y0)) = (Peano.le x0 y0).
Definition term54 (x0 : nat) (x1 : nat) := @eq Prop (real_ge (real_of_num x0) (real_of_num x1)).
Definition term56 (x0 : nat) := fun y0 : nat => (real_ge (real_of_num x0) (real_of_num y0)) = (Peano.ge x0 y0).
Definition term66 (x0 : nat) (x1 : nat) := @eq Prop (real_le (real_of_num x0) (real_of_num x1)).
Definition term46 (x0 : nat) := fun y0 : nat => ((real_of_num x0) = (real_of_num y0)) = (x0 = y0).
Definition term91 (x0 : nat) (x1 : nat) := @eq real (real_of_num (Nat.add x0 x1)).
Definition term4 (x0 : nat) (x1 : nat) := real_of_num (Nat.pow x0 x1).
Definition term84 (x0 : nat) (x1 : nat) := @eq real (real_min (real_of_num x0) (real_of_num x1)).
Definition term72 (x0 : nat) (x1 : nat) := @eq Prop (real_lt (real_of_num x0) (real_of_num x1)).
Definition term22 (x0 : nat) (x1 : nat) := (fun y0 : nat => (real_max (real_of_num x0) (real_of_num y0)) = (real_of_num (Nat.max x0 y0))) x1.
Definition term17 (x0 : nat) (x1 : nat) := (fun y0 : nat => (real_min (real_of_num x0) (real_of_num y0)) = (real_of_num (Nat.min x0 y0))) x1.
Definition term12 (x0 : nat) (x1 : nat) := (fun y0 : nat => (real_add (real_of_num x0) (real_of_num y0)) = (real_of_num (Nat.add x0 y0))) x1.
Definition term7 (x0 : nat) (x1 : nat) := (fun y0 : nat => (real_mul (real_of_num x0) (real_of_num y0)) = (real_of_num (Nat.mul x0 y0))) x1.
Definition term75 := fun y0 : nat => forall y1 : nat, (real_lt (real_of_num y0) (real_of_num y1)) = (Peano.lt y0 y1).
Definition term69 := fun y0 : nat => forall y1 : nat, (real_le (real_of_num y0) (real_of_num y1)) = (Peano.le y0 y1).
Definition term63 := fun y0 : nat => forall y1 : nat, (real_gt (real_of_num y0) (real_of_num y1)) = (Peano.gt y0 y1).
Definition term57 := fun y0 : nat => forall y1 : nat, (real_ge (real_of_num y0) (real_of_num y1)) = (Peano.ge y0 y1).
Definition term51 := fun y0 : nat => forall y1 : nat, ((real_of_num y0) = (real_of_num y1)) = (y0 = y1).
Definition term109 := (forall y0 : nat, forall y1 : nat, (real_min (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.min y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (real_mul (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.mul y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (real_pow (real_of_num y0) y1) = (real_of_num (Nat.pow y0 y1))))).
Definition term85 (x0 : nat) (x1 : nat) := @eq real (real_of_num (Nat.min x0 x1)).
Definition term61 (x0 : nat) (x1 : nat) := @eq Prop (Peano.gt x0 x1).
Definition term108 := (forall y0 : nat, forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (real_mul (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.mul y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (real_pow (real_of_num y0) y1) = (real_of_num (Nat.pow y0 y1)))).
Definition term115 := (forall y0 : nat, forall y1 : nat, ((real_of_num y0) = (real_of_num y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, (real_ge (real_of_num y0) (real_of_num y1)) = (Peano.ge y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (real_gt (real_of_num y0) (real_of_num y1)) = (Peano.gt y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (real_le (real_of_num y0) (real_of_num y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (real_lt (real_of_num y0) (real_of_num y1)) = (Peano.lt y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (real_max (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.max y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (real_min (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.min y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (real_mul (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.mul y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (real_pow (real_of_num y0) y1) = (real_of_num (Nat.pow y0 y1))))))))))).
Definition term114 := (forall y0 : nat, forall y1 : nat, (real_ge (real_of_num y0) (real_of_num y1)) = (Peano.ge y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (real_gt (real_of_num y0) (real_of_num y1)) = (Peano.gt y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (real_le (real_of_num y0) (real_of_num y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (real_lt (real_of_num y0) (real_of_num y1)) = (Peano.lt y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (real_max (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.max y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (real_min (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.min y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (real_mul (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.mul y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (real_pow (real_of_num y0) y1) = (real_of_num (Nat.pow y0 y1)))))))))).
Definition term113 := (forall y0 : nat, forall y1 : nat, (real_gt (real_of_num y0) (real_of_num y1)) = (Peano.gt y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (real_le (real_of_num y0) (real_of_num y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (real_lt (real_of_num y0) (real_of_num y1)) = (Peano.lt y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (real_max (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.max y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (real_min (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.min y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (real_mul (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.mul y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (real_pow (real_of_num y0) y1) = (real_of_num (Nat.pow y0 y1))))))))).
Definition term112 := (forall y0 : nat, forall y1 : nat, (real_le (real_of_num y0) (real_of_num y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (real_lt (real_of_num y0) (real_of_num y1)) = (Peano.lt y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (real_max (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.max y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (real_min (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.min y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (real_mul (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.mul y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (real_pow (real_of_num y0) y1) = (real_of_num (Nat.pow y0 y1)))))))).
Definition term111 := (forall y0 : nat, forall y1 : nat, (real_lt (real_of_num y0) (real_of_num y1)) = (Peano.lt y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (real_max (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.max y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (real_min (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.min y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (real_mul (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.mul y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (real_pow (real_of_num y0) y1) = (real_of_num (Nat.pow y0 y1))))))).
Definition term98 (x0 : nat) := fun y0 : nat => (real_mul (real_of_num x0) (real_of_num y0)) = (real_of_num (Nat.mul x0 y0)).
Definition term73 (x0 : nat) (x1 : nat) := @eq Prop (Peano.lt x0 x1).
Definition term31 (x0 : nat) (x1 : nat) := (fun y0 : nat => (real_le (real_of_num x0) (real_of_num y0)) = (Peano.le x0 y0)) x1.
Definition term97 (x0 : nat) (x1 : nat) := @eq real (real_of_num (Nat.mul x0 x1)).
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => (real_pow (real_of_num x0) y0) = (real_of_num (Nat.pow x0 y0))) x1.
Definition term106 := forall y0 : nat, forall y1 : nat, (real_pow (real_of_num y0) y1) = (real_of_num (Nat.pow y0 y1)).
Definition term100 := forall y0 : nat, forall y1 : nat, (real_mul (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.mul y0 y1)).
Definition term94 := forall y0 : nat, forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1)).
Definition term88 := forall y0 : nat, forall y1 : nat, (real_min (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.min y0 y1)).
Definition term82 := forall y0 : nat, forall y1 : nat, (real_max (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.max y0 y1)).
Definition term76 := forall y0 : nat, forall y1 : nat, (real_lt (real_of_num y0) (real_of_num y1)) = (Peano.lt y0 y1).
Definition term70 := forall y0 : nat, forall y1 : nat, (real_le (real_of_num y0) (real_of_num y1)) = (Peano.le y0 y1).
Definition term64 := forall y0 : nat, forall y1 : nat, (real_gt (real_of_num y0) (real_of_num y1)) = (Peano.gt y0 y1).
Definition term58 := forall y0 : nat, forall y1 : nat, (real_ge (real_of_num y0) (real_of_num y1)) = (Peano.ge y0 y1).
Definition term52 := forall y0 : nat, forall y1 : nat, ((real_of_num y0) = (real_of_num y1)) = (y0 = y1).
Definition term35 (x0 : nat) (x1 : nat) := (fun y0 : nat => (real_gt (real_of_num x0) (real_of_num y0)) = (Peano.gt x0 y0)) x1.
Definition term48 := forall y0 : nat, True.
Definition term74 (x0 : nat) := fun y0 : nat => (real_lt (real_of_num x0) (real_of_num y0)) = (Peano.lt x0 y0).
Definition term55 (x0 : nat) (x1 : nat) := @eq Prop (Peano.ge x0 x1).
Definition term36 (x0 : nat) (x1 : nat) := real_gt (real_of_num x0) (real_of_num x1).
Definition term47 := fun y0 : nat => True.
Definition term27 (x0 : nat) (x1 : nat) := (fun y0 : nat => (real_lt (real_of_num x0) (real_of_num y0)) = (Peano.lt x0 y0)) x1.
Definition term67 (x0 : nat) (x1 : nat) := @eq Prop (Peano.le x0 x1).
Definition term44 (x0 : nat) (x1 : nat) := @eq Prop ((real_of_num x0) = (real_of_num x1)).
Definition term19 (x0 : nat) (x1 : nat) := real_of_num (Nat.min x0 x1).
Definition term24 (x0 : nat) (x1 : nat) := real_of_num (Nat.max x0 x1).
Definition term18 (x0 : nat) (x1 : nat) := real_min (real_of_num x0) (real_of_num x1).
Definition term8 (x0 : nat) (x1 : nat) := real_mul (real_of_num x0) (real_of_num x1).
Definition term78 (x0 : nat) (x1 : nat) := @eq real (real_max (real_of_num x0) (real_of_num x1)).
Definition term101 := and (forall y0 : nat, forall y1 : nat, (real_mul (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.mul y0 y1))).
Definition term95 := and (forall y0 : nat, forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1))).
Definition term89 := and (forall y0 : nat, forall y1 : nat, (real_min (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.min y0 y1))).
Definition term83 := and (forall y0 : nat, forall y1 : nat, (real_max (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.max y0 y1))).
Definition term77 := and (forall y0 : nat, forall y1 : nat, (real_lt (real_of_num y0) (real_of_num y1)) = (Peano.lt y0 y1)).
Definition term71 := and (forall y0 : nat, forall y1 : nat, (real_le (real_of_num y0) (real_of_num y1)) = (Peano.le y0 y1)).
Definition term65 := and (forall y0 : nat, forall y1 : nat, (real_gt (real_of_num y0) (real_of_num y1)) = (Peano.gt y0 y1)).
Definition term59 := and (forall y0 : nat, forall y1 : nat, (real_ge (real_of_num y0) (real_of_num y1)) = (Peano.ge y0 y1)).
Definition term53 := and (forall y0 : nat, forall y1 : nat, ((real_of_num y0) = (real_of_num y1)) = (y0 = y1)).
Definition term110 := (forall y0 : nat, forall y1 : nat, (real_max (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.max y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (real_min (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.min y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (real_mul (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.mul y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (real_pow (real_of_num y0) y1) = (real_of_num (Nat.pow y0 y1)))))).
Definition term41 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((real_of_num y0) = (real_of_num y1)) = (y0 = y1)) x0.
Definition term37 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (real_ge (real_of_num y0) (real_of_num y1)) = (Peano.ge y0 y1)) x0.
Definition term33 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (real_gt (real_of_num y0) (real_of_num y1)) = (Peano.gt y0 y1)) x0.
Definition term29 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (real_le (real_of_num y0) (real_of_num y1)) = (Peano.le y0 y1)) x0.
Definition term25 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (real_lt (real_of_num y0) (real_of_num y1)) = (Peano.lt y0 y1)) x0.
Definition term20 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (real_max (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.max y0 y1))) x0.
Definition term15 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (real_min (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.min y0 y1))) x0.
Definition term10 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1))) x0.
Definition term5 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (real_mul (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.mul y0 y1))) x0.
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (real_pow (real_of_num y0) y1) = (real_of_num (Nat.pow y0 y1))) x0.
Definition term104 (x0 : nat) := fun y0 : nat => (real_pow (real_of_num x0) y0) = (real_of_num (Nat.pow x0 y0)).
Definition term21 (x0 : nat) := forall y0 : nat, (real_max (real_of_num x0) (real_of_num y0)) = (real_of_num (Nat.max x0 y0)).
Definition term16 (x0 : nat) := forall y0 : nat, (real_min (real_of_num x0) (real_of_num y0)) = (real_of_num (Nat.min x0 y0)).
Definition term11 (x0 : nat) := forall y0 : nat, (real_add (real_of_num x0) (real_of_num y0)) = (real_of_num (Nat.add x0 y0)).
Definition term6 (x0 : nat) := forall y0 : nat, (real_mul (real_of_num x0) (real_of_num y0)) = (real_of_num (Nat.mul x0 y0)).
Definition term102 (x0 : nat) (x1 : nat) := @eq real (real_pow (real_of_num x0) x1).
Definition term45 (x0 : nat) (x1 : nat) := @eq Prop (x0 = x1).
Definition term1 (x0 : nat) := forall y0 : nat, (real_pow (real_of_num x0) y0) = (real_of_num (Nat.pow x0 y0)).
Definition term50 (x0 : Prop) := forall y0 : nat, x0.
Definition term3 (x0 : nat) (x1 : nat) := real_pow (real_of_num x0) x1.
Definition term105 := fun y0 : nat => forall y1 : nat, (real_pow (real_of_num y0) y1) = (real_of_num (Nat.pow y0 y1)).
Definition term99 := fun y0 : nat => forall y1 : nat, (real_mul (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.mul y0 y1)).
Definition term93 := fun y0 : nat => forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1)).
Definition term87 := fun y0 : nat => forall y1 : nat, (real_min (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.min y0 y1)).
Definition term81 := fun y0 : nat => forall y1 : nat, (real_max (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.max y0 y1)).
Definition term9 (x0 : nat) (x1 : nat) := real_of_num (Nat.mul x0 x1).
Definition term32 (x0 : nat) (x1 : nat) := real_le (real_of_num x0) (real_of_num x1).
Definition term40 (x0 : nat) (x1 : nat) := real_ge (real_of_num x0) (real_of_num x1).
Definition term79 (x0 : nat) (x1 : nat) := @eq real (real_of_num (Nat.max x0 x1)).
Definition term23 (x0 : nat) (x1 : nat) := real_max (real_of_num x0) (real_of_num x1).
Definition term43 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((real_of_num x0) = (real_of_num y0)) = (x0 = y0)) x1.
Definition term14 (x0 : nat) (x1 : nat) := real_of_num (Nat.add x0 x1).
Definition term86 (x0 : nat) := fun y0 : nat => (real_min (real_of_num x0) (real_of_num y0)) = (real_of_num (Nat.min x0 y0)).
Definition term103 (x0 : nat) (x1 : nat) := @eq real (real_of_num (Nat.pow x0 x1)).
