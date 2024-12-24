Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : nat) := int_of_real (real_of_num x0).
Definition term56 (x0 : nat) := exists y0 : nat, (int_of_real (real_neg (real_of_num x0))) = (int_of_num y0).
Definition term38 (x0 : nat) := exists y0 : nat, (int_of_real (real_of_num x0)) = (int_of_num y0).
Definition term14 (x0 : nat) := real_neg (real_of_num x0).
Definition term59 (x0 : nat) := or (exists y0 : nat, (int_of_real (real_neg (real_of_num x0))) = (int_of_real (real_of_num y0))).
Definition term58 (x0 : nat) := or (exists y0 : nat, (int_of_real (real_neg (real_of_num x0))) = (int_of_num y0)).
Definition term41 (x0 : nat) := or (exists y0 : nat, (int_of_real (real_of_num x0)) = (int_of_real (real_of_num y0))).
Definition term40 (x0 : nat) := or (exists y0 : nat, (int_of_real (real_of_num x0)) = (int_of_num y0)).
Definition term64 (x0 : nat) := (exists y0 : nat, (int_of_real (real_neg (real_of_num x0))) = (int_of_real (real_of_num y0))) \/ (exists y0 : nat, (int_of_real (real_neg (real_of_num x0))) = (int_of_real (real_neg (real_of_int (int_of_real (real_of_num y0)))))).
Definition term52 (x0 : nat) := (exists y0 : nat, (int_of_real (real_of_num x0)) = (int_of_real (real_of_num y0))) \/ (exists y0 : nat, (int_of_real (real_of_num x0)) = (int_of_real (real_neg (real_of_int (int_of_real (real_of_num y0)))))).
Definition term34 (x0 : nat) := (exists y0 : nat, (int_of_real (real_neg (real_of_num x0))) = (int_of_num y0)) \/ (exists y0 : nat, (int_of_real (real_neg (real_of_num x0))) = (int_neg (int_of_num y0))).
Definition term30 (x0 : nat) := (exists y0 : nat, (int_of_real (real_of_num x0)) = (int_of_num y0)) \/ (exists y0 : nat, (int_of_real (real_of_num x0)) = (int_neg (int_of_num y0))).
Definition term20 (x0 : int) := (exists y0 : nat, x0 = (int_of_num y0)) \/ (exists y0 : nat, x0 = (int_neg (int_of_num y0))).
Definition term35 (x0 : nat) := @eq int (int_of_real (real_of_num x0)).
Definition term29 (x0 : nat) := (fun y0 : int => (exists y1 : nat, y0 = (int_of_num y1)) \/ (exists y1 : nat, y0 = (int_neg (int_of_num y1)))) (int_of_real (real_of_num x0)).
Definition term22 (x0 : nat) (x1 : int) := (x1 = (int_of_real (real_of_num x0))) -> (exists y0 : nat, x1 = (int_of_num y0)) \/ (exists y0 : nat, x1 = (int_neg (int_of_num y0))).
Definition term4 := forall y0 : nat, (int_of_real (real_of_num y0)) = (int_of_num y0).
Definition term24 (x0 : int) (x1 : nat) := imp (x0 = (int_of_real (real_neg (real_of_num x1)))).
Definition term60 (x0 : nat) := fun y0 : nat => (int_of_real (real_neg (real_of_num x0))) = (int_neg (int_of_num y0)).
Definition term15 (x0 : int) := int_of_real (real_of_int x0).
Definition term11 (x0 : int) := (fun y0 : int => exists y1 : nat, ((real_of_int y0) = (real_of_num y1)) \/ ((real_of_int y0) = (real_neg (real_of_num y1)))) x0.
Definition term48 (x0 : nat) := fun y0 : nat => (int_of_real (real_of_num x0)) = (int_neg (int_of_num y0)).
Definition term65 (x0 : int) := fun y0 : nat => ((real_of_int x0) = (real_of_num y0)) \/ ((real_of_int x0) = (real_neg (real_of_num y0))).
Definition term27 := fun y0 : int => (exists y1 : nat, y0 = (int_of_num y1)) \/ (exists y1 : nat, y0 = (int_neg (int_of_num y1))).
Definition term3 := forall y0 : nat, (int_of_num y0) = (int_of_real (real_of_num y0)).
Definition term1 := fun y0 : nat => (int_of_num y0) = (int_of_real (real_of_num y0)).
Definition term12 (x0 : int) := exists y0 : nat, ((real_of_int x0) = (real_of_num y0)) \/ ((real_of_int x0) = (real_neg (real_of_num y0))).
Definition term44 (x0 : nat) := real_of_int (int_of_real (real_of_num x0)).
Definition term28 (x0 : int) := (fun y0 : int => (exists y1 : nat, y0 = (int_of_num y1)) \/ (exists y1 : nat, y0 = (int_neg (int_of_num y1)))) x0.
Definition term55 (x0 : nat) := fun y0 : nat => (int_of_real (real_neg (real_of_num x0))) = (int_of_real (real_of_num y0)).
Definition term6 (x0 : nat) := real_of_int (int_of_num x0).
Definition term16 (x0 : nat) := int_of_real (real_neg (real_of_num x0)).
Definition term49 (x0 : nat) := fun y0 : nat => (int_of_real (real_of_num x0)) = (int_of_real (real_neg (real_of_int (int_of_real (real_of_num y0))))).
Definition term54 (x0 : nat) := fun y0 : nat => (int_of_real (real_neg (real_of_num x0))) = (int_of_num y0).
Definition term62 (x0 : nat) := exists y0 : nat, (int_of_real (real_neg (real_of_num x0))) = (int_neg (int_of_num y0)).
Definition term50 (x0 : nat) := exists y0 : nat, (int_of_real (real_of_num x0)) = (int_neg (int_of_num y0)).
Definition term18 (x0 : int) (x1 : nat) := imp ((int_of_real (real_of_int x0)) = (int_of_real (real_of_num x1))).
Definition term17 (x0 : int) := @eq int (int_of_real (real_of_int x0)).
Definition term5 (x0 : nat) := (fun y0 : nat => (real_of_int (int_of_num y0)) = (real_of_num y0)) x0.
Definition term13 (x0 : int) (x1 : nat) := ((real_of_int x0) = (real_of_num x1)) \/ ((real_of_int x0) = (real_neg (real_of_num x1))).
Definition term47 (x0 : nat) := int_of_real (real_neg (real_of_int (int_of_real (real_of_num x0)))).
Definition term37 (x0 : nat) := fun y0 : nat => (int_of_real (real_of_num x0)) = (int_of_real (real_of_num y0)).
Definition term19 (x0 : int) (x1 : nat) := imp (x0 = (int_of_real (real_of_num x1))).
Definition term8 (x0 : int) := (fun y0 : int => (int_neg y0) = (int_of_real (real_neg (real_of_int y0)))) x0.
Definition term61 (x0 : nat) := fun y0 : nat => (int_of_real (real_neg (real_of_num x0))) = (int_of_real (real_neg (real_of_int (int_of_real (real_of_num y0))))).
Definition term23 (x0 : int) (x1 : nat) := imp ((int_of_real (real_of_int x0)) = (int_of_real (real_neg (real_of_num x1)))).
Definition term57 (x0 : nat) := exists y0 : nat, (int_of_real (real_neg (real_of_num x0))) = (int_of_real (real_of_num y0)).
Definition term39 (x0 : nat) := exists y0 : nat, (int_of_real (real_of_num x0)) = (int_of_real (real_of_num y0)).
Definition term33 (x0 : nat) := (fun y0 : int => (exists y1 : nat, y0 = (int_of_num y1)) \/ (exists y1 : nat, y0 = (int_neg (int_of_num y1)))) (int_of_real (real_neg (real_of_num x0))).
Definition term42 (x0 : nat) := int_neg (int_of_num x0).
Definition term7 (x0 : nat) := (fun y0 : nat => (int_of_real (real_of_num y0)) = (int_of_num y0)) x0.
Definition term31 (x0 : int) := @eq Prop ((fun y0 : int => (exists y1 : nat, y0 = (int_of_num y1)) \/ (exists y1 : nat, y0 = (int_neg (int_of_num y1)))) x0).
Definition term21 (x0 : nat) (x1 : int) := ((int_of_real (real_of_int x1)) = (int_of_real (real_of_num x0))) -> (exists y0 : nat, x1 = (int_of_num y0)) \/ (exists y0 : nat, x1 = (int_neg (int_of_num y0))).
Definition term36 (x0 : nat) := fun y0 : nat => (int_of_real (real_of_num x0)) = (int_of_num y0).
Definition term2 := fun y0 : nat => (int_of_real (real_of_num y0)) = (int_of_num y0).
Definition term26 (x0 : nat) (x1 : int) := (x1 = (int_of_real (real_neg (real_of_num x0)))) -> (exists y0 : nat, x1 = (int_of_num y0)) \/ (exists y0 : nat, x1 = (int_neg (int_of_num y0))).
Definition term45 (x0 : nat) := real_neg (real_of_int (int_of_num x0)).
Definition term63 (x0 : nat) := exists y0 : nat, (int_of_real (real_neg (real_of_num x0))) = (int_of_real (real_neg (real_of_int (int_of_real (real_of_num y0))))).
Definition term51 (x0 : nat) := exists y0 : nat, (int_of_real (real_of_num x0)) = (int_of_real (real_neg (real_of_int (int_of_real (real_of_num y0))))).
Definition term25 (x0 : nat) (x1 : int) := ((int_of_real (real_of_int x1)) = (int_of_real (real_neg (real_of_num x0)))) -> (exists y0 : nat, x1 = (int_of_num y0)) \/ (exists y0 : nat, x1 = (int_neg (int_of_num y0))).
Definition term43 (x0 : nat) := int_of_real (real_neg (real_of_int (int_of_num x0))).
Definition term66 := forall y0 : int, (exists y1 : nat, y0 = (int_of_num y1)) \/ (exists y1 : nat, y0 = (int_neg (int_of_num y1))).
Definition term46 (x0 : nat) := real_neg (real_of_int (int_of_real (real_of_num x0))).
Definition term9 (x0 : int) := int_of_real (real_neg (real_of_int x0)).
Definition term10 (x0 : nat) := (fun y0 : nat => (int_of_num y0) = (int_of_real (real_of_num y0))) x0.
Definition term53 (x0 : nat) := @eq int (int_of_real (real_neg (real_of_num x0))).
Definition term32 (x0 : int) := @eq Prop ((exists y0 : nat, x0 = (int_of_num y0)) \/ (exists y0 : nat, x0 = (int_neg (int_of_num y0)))).
