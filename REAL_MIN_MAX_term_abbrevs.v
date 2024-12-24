Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term211 (x0 : real) (x1 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1).
Definition term168 (x0 : real) (x1 : real) := real_gt (real_add x0 (real_neg x1)) (real_of_num (NUMERAL 0)).
Definition term147 (x0 : real) (x1 : real) := or ((real_ge (real_neg x1) (real_neg x0)) /\ ((fun y0 : real => (real_gt (real_add x0 y0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x1 y0) (real_of_num (NUMERAL 0)))) (real_neg x1))).
Definition term136 (x0 : real) (x1 : real) := fun y0 : real => (real_gt (real_add x0 y0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x1 y0) (real_of_num (NUMERAL 0))).
Definition term170 (x0 : real) (x1 : real) := real_add x0 (real_neg x1).
Definition term190 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term60 (x0 : real) (x1 : real) := or (real_gt (real_add (real_max (real_neg x0) (real_neg x1)) (real_min x0 x1)) (real_of_num (NUMERAL 0))).
Definition term0 (x0 : real -> Prop) := ~ (all x0).
Definition term36 := Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0))).
Definition term242 (x0 : real) (x1 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_min x1 x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg x1))).
Definition term235 (x0 : real) (x1 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_min x0 x1)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg x1))).
Definition term230 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg x0).
Definition term11 (x0 : real) := exists y0 : real, ~ ((real_min x0 y0) = (real_neg (real_max (real_neg x0) (real_neg y0)))).
Definition term28 (x0 : real) (x1 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max (real_neg x0) (real_neg x1))).
Definition term260 (x0 : real) (x1 : real) := (real_ge x0 x1) /\ ((fun y0 : real => (real_gt (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0)) (real_of_num (NUMERAL 0)))) x1).
Definition term231 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_min x0 x1)).
Definition term111 := (exists y0 : real, exists y1 : real, real_gt (real_add (real_max (real_neg y0) (real_neg y1)) (real_min y0 y1)) (real_of_num (NUMERAL 0))) \/ (exists y0 : real, exists y1 : real, real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max (real_neg y0) (real_neg y1))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_min y0 y1))) (real_of_num (NUMERAL 0))).
Definition term152 (x0 : real) (x1 : real) := real_ge (real_sub (real_neg x0) (real_neg x1)) (real_of_num (NUMERAL 0)).
Definition term52 := real_of_num (NUMERAL 0).
Definition term172 (x0 : real) (x1 : real) := real_sub (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term118 (x0 : real) (x1 : real) := (real_gt (real_add (real_max (real_neg x0) (real_neg x1)) x0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_max (real_neg x0) (real_neg x1)) x1) (real_of_num (NUMERAL 0))).
Definition term23 (x0 : real) (x1 : real) := real_max (real_neg x0) (real_neg x1).
Definition term51 (x0 : real) (x1 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max (real_neg x0) (real_neg x1))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_min x0 x1))).
Definition term56 (x0 : real) (x1 : real) := real_gt (real_add (real_max (real_neg x0) (real_neg x1)) (real_min x0 x1)).
Definition term208 (x0 : real) (x1 : real) := real_gt (real_neg x0) (real_neg x1).
Definition term117 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (real_gt (real_add x1 x0) x3) /\ (real_gt (real_add x1 x2) x3).
Definition term67 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term43 (x0 : real) (x1 : real) := real_add (real_min x0 x1) (real_max (real_neg x0) (real_neg x1)).
Definition term139 (x0 : real) (x1 : real) := and (real_gt (real_neg x0) (real_neg x1)).
Definition term145 (x0 : real) (x1 : real) := (real_ge (real_neg x1) (real_neg x0)) /\ ((fun y0 : real => (real_gt (real_add x0 y0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x1 y0) (real_of_num (NUMERAL 0)))) (real_neg x1)).
Definition term49 (x0 : real) (x1 : real) := @eq real (real_neg (real_sub (real_min x0 x1) (real_neg (real_max (real_neg x0) (real_neg x1))))).
Definition term221 (x0 : real) (x1 : real) := and (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))).
Definition term131 (x0 : real) (x1 : real) := and (real_gt (real_add (real_max (real_neg x1) (real_neg x0)) x1) (real_of_num (NUMERAL 0))).
Definition term2 (x0 : real) := ~ (forall y0 : real, (real_min x0 y0) = (real_neg (real_max (real_neg x0) (real_neg y0)))).
Definition term154 (x0 : real) := real_sub (real_neg x0).
Definition term183 (x0 : real) := real_gt (real_add x0 (real_neg x0)) (real_of_num (NUMERAL 0)).
Definition term97 (x0 : real) := or ((fun y0 : real => exists y1 : real, real_gt (real_add (real_max (real_neg y0) (real_neg y1)) (real_min y0 y1)) (real_of_num (NUMERAL 0))) x0).
Definition term285 (x0 : real) (x1 : real) := or (((real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))) /\ ((real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))))) \/ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))) /\ ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0)))))).
Definition term182 (x0 : real) (x1 : real) := real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0)).
Definition term7 (x0 : real) (x1 : real) := ~ ((fun y0 : real => (real_min x0 y0) = (real_neg (real_max (real_neg x0) (real_neg y0)))) x1).
Definition term261 (x0 : real) (x1 : real) := (real_ge x0 x1) /\ ((real_gt (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0)))).
Definition term269 (x0 : real) (x1 : real) := real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0)).
Definition term10 (x0 : real) := fun y0 : real => ~ ((real_min x0 y0) = (real_neg (real_max (real_neg x0) (real_neg y0)))).
Definition term42 (x0 : real) (x1 : real) := real_add (real_min x0 x1).
Definition term29 (x0 : real) (x1 : real) := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_max (real_neg x0) (real_neg x1)).
Definition term217 (x0 : real) (x1 : real) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0)).
Definition term155 (x0 : real) := real_sub (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term163 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1.
Definition term197 := real_add (real_of_num (NUMERAL 0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term214 (x0 : real) (x1 : real) := real_sub (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0)).
Definition term58 (x0 : real) (x1 : real) := real_gt (real_add (real_max (real_neg x0) (real_neg x1)) (real_min x0 x1)) (real_of_num (NUMERAL 0)).
Definition term120 (x0 : real) (x1 : real) := real_add x1 (real_max (real_neg x0) (real_neg x1)).
Definition term284 (x0 : real) (x1 : real) := ((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))) /\ ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))))) \/ ((real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))) /\ ((real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))))).
Definition term224 (x0 : real) (x1 : real) := ((real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))) /\ ((real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))))) \/ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))) /\ ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))))).
Definition term283 (x0 : real) (x1 : real) := or ((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))) /\ ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))))).
Definition term223 (x0 : real) (x1 : real) := or ((real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))) /\ ((real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))))).
Definition term258 (x0 : real) (x1 : real) := (real_gt (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))).
Definition term253 (x0 : real) (x1 : real) := (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))).
Definition term276 (x0 : real) (x1 : real) := real_gt (real_sub (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))).
Definition term274 (x0 : real) := real_gt (real_sub (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_of_num (NUMERAL 0))).
Definition term87 (x0 : real) := exists y0 : real, (fun y1 : real => real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max (real_neg x0) (real_neg y1))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_min x0 y1))) (real_of_num (NUMERAL 0))) y0.
Definition term82 (x0 : real) := exists y0 : real, (fun y1 : real => real_gt (real_add (real_max (real_neg x0) (real_neg y1)) (real_min x0 y1)) (real_of_num (NUMERAL 0))) y0.
Definition term126 (x0 : real) (x1 : real) := real_add x0 (real_max (real_neg x0) (real_neg x1)).
Definition term222 (x0 : real) (x1 : real) := (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))) /\ ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0)))).
Definition term286 (x0 : real) (x1 : real) := (((real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))) /\ ((real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))))) \/ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))) /\ ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0)))))) \/ (((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))) /\ ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))))) \/ ((real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))) /\ ((real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))))).
Definition term176 (x0 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num (NUMERAL 0)).
Definition term291 := forall y0 : real, forall y1 : real, (real_min y0 y1) = (real_neg (real_max (real_neg y0) (real_neg y1))).
Definition term159 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term249 (x0 : real) (x1 : real) := (fun y0 : real => (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0)) (real_of_num (NUMERAL 0)))) (real_min x0 x1).
Definition term110 := exists y0 : real, exists y1 : real, real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max (real_neg y0) (real_neg y1))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_min y0 y1))) (real_of_num (NUMERAL 0)).
Definition term105 := exists y0 : real, exists y1 : real, real_gt (real_add (real_max (real_neg y0) (real_neg y1)) (real_min y0 y1)) (real_of_num (NUMERAL 0)).
Definition term65 := exists y0 : real, exists y1 : real, (real_gt (real_add (real_max (real_neg y0) (real_neg y1)) (real_min y0 y1)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max (real_neg y0) (real_neg y1))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_min y0 y1))) (real_of_num (NUMERAL 0))).
Definition term20 := exists y0 : real, exists y1 : real, ~ ((real_min y0 y1) = (real_neg (real_max (real_neg y0) (real_neg y1)))).
Definition term54 (x0 : real) (x1 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max (real_neg x0) (real_neg x1))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_min x0 x1))) (real_of_num (NUMERAL 0)).
Definition term193 (x0 : real) := real_sub (real_add x0 (real_neg x0)).
Definition term33 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term4 (x0 : real) := fun y0 : real => (real_min x0 y0) = (real_neg (real_max (real_neg x0) (real_neg y0))).
Definition term165 (x0 : real) (x1 : real) := real_ge (real_sub (real_neg x0) (real_neg x1)).
Definition term248 (x0 : real) (x1 : real) := (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_min x0 x1))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_min x0 x1))) (real_of_num (NUMERAL 0))).
Definition term133 (x0 : real) (x1 : real) := (real_gt (real_add x0 (real_max (real_neg x0) (real_neg x1))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x1 (real_max (real_neg x0) (real_neg x1))) (real_of_num (NUMERAL 0))).
Definition term6 (x0 : real) (x1 : real) := real_neg (real_max (real_neg x0) (real_neg x1)).
Definition term106 := or (exists y0 : real, (fun y1 : real => exists y2 : real, real_gt (real_add (real_max (real_neg y1) (real_neg y2)) (real_min y1 y2)) (real_of_num (NUMERAL 0))) y0).
Definition term84 (x0 : real) := or (exists y0 : real, (fun y1 : real => real_gt (real_add (real_max (real_neg x0) (real_neg y1)) (real_min x0 y1)) (real_of_num (NUMERAL 0))) y0).
Definition term251 (x0 : real) (x1 : real) := fun y0 : real => (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0)) (real_of_num (NUMERAL 0))).
Definition term240 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_min x1 x0)) x1.
Definition term171 (x0 : real) (x1 : real) := real_sub (real_add x0 (real_neg x1)).
Definition term13 := exists y0 : real, ~ ((fun y1 : real => forall y2 : real, (real_min y1 y2) = (real_neg (real_max (real_neg y1) (real_neg y2)))) y0).
Definition term3 (x0 : real) := exists y0 : real, ~ ((fun y1 : real => (real_min x0 y1) = (real_neg (real_max (real_neg x0) (real_neg y1)))) y0).
Definition term98 (x0 : real) := (fun y0 : real => exists y1 : real, real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max (real_neg y0) (real_neg y1))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_min y0 y1))) (real_of_num (NUMERAL 0))) x0.
Definition term96 (x0 : real) := (fun y0 : real => exists y1 : real, real_gt (real_add (real_max (real_neg y0) (real_neg y1)) (real_min y0 y1)) (real_of_num (NUMERAL 0))) x0.
Definition term226 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (real_gt (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) x3) /\ (real_gt (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2)) x3).
Definition term181 (x0 : real) (x1 : real) := real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term268 (x0 : real) (x1 : real) := real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1).
Definition term47 (x0 : real) (x1 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_max (real_neg x0) (real_neg x1)) (real_min x0 x1)).
Definition term18 := fun y0 : real => ~ ((fun y1 : real => forall y2 : real, (real_min y1 y2) = (real_neg (real_max (real_neg y1) (real_neg y2)))) y0).
Definition term50 (x0 : real) (x1 : real) := real_gt (real_neg (real_sub (real_min x0 x1) (real_neg (real_max (real_neg x0) (real_neg x1))))).
Definition term125 (x0 : real) (x1 : real) := real_add (real_max (real_neg x1) (real_neg x0)) x1.
Definition term195 (x0 : real) := real_sub (real_add x0 (real_neg x0)) (real_of_num (NUMERAL 0)).
Definition term74 (x0 : real) (x1 : real) := (fun y0 : real => real_gt (real_add (real_max (real_neg x0) (real_neg y0)) (real_min x0 y0)) (real_of_num (NUMERAL 0))) x1.
Definition term122 (x0 : real) (x1 : real) := real_gt (real_add x1 (real_max (real_neg x0) (real_neg x1))).
Definition term95 := fun y0 : real => exists y1 : real, real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max (real_neg y0) (real_neg y1))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_min y0 y1))) (real_of_num (NUMERAL 0)).
Definition term94 := fun y0 : real => exists y1 : real, real_gt (real_add (real_max (real_neg y0) (real_neg y1)) (real_min y0 y1)) (real_of_num (NUMERAL 0)).
Definition term219 := and (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term146 (x0 : real) (x1 : real) := (real_ge (real_neg x1) (real_neg x0)) /\ ((real_gt (real_add x0 (real_neg x1)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x1 (real_neg x1)) (real_of_num (NUMERAL 0)))).
Definition term127 (x0 : real) (x1 : real) := real_gt (real_add (real_max (real_neg x1) (real_neg x0)) x1).
Definition term121 (x0 : real) (x1 : real) := real_gt (real_add (real_max (real_neg x0) (real_neg x1)) x1).
Definition term257 (x0 : real) (x1 : real) := (fun y0 : real => (real_gt (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0)) (real_of_num (NUMERAL 0)))) x1.
Definition term252 (x0 : real) (x1 : real) := (fun y0 : real => (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0)) (real_of_num (NUMERAL 0)))) x1.
Definition term167 (x0 : real) (x1 : real) := real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0)).
Definition term256 (x0 : real) (x1 : real) := (real_gt x0 x1) /\ ((real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0)))).
Definition term41 (x0 : real) (x1 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_max (real_neg x0) (real_neg x1)).
Definition term99 (x0 : real) := ((fun y0 : real => exists y1 : real, real_gt (real_add (real_max (real_neg y0) (real_neg y1)) (real_min y0 y1)) (real_of_num (NUMERAL 0))) x0) \/ ((fun y0 : real => exists y1 : real, real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max (real_neg y0) (real_neg y1))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_min y0 y1))) (real_of_num (NUMERAL 0))) x0).
Definition term188 (x0 : nat) := real_add (real_neg (real_of_num x0)) (real_of_num x0).
Definition term37 := Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term73 (x0 : real) := fun y0 : real => real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max (real_neg x0) (real_neg y0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_min x0 y0))) (real_of_num (NUMERAL 0)).
Definition term143 (x0 : real) (x1 : real) := (real_gt (real_add x0 (real_neg x1)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x1 (real_neg x1)) (real_of_num (NUMERAL 0))).
Definition term138 (x0 : real) (x1 : real) := (real_gt (real_add x1 (real_neg x1)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_neg x1)) (real_of_num (NUMERAL 0))).
Definition term21 (x0 : real) (x1 : real) := (real_gt (real_sub (real_min x0 x1) (real_neg (real_max (real_neg x0) (real_neg x1)))) (real_of_num (NUMERAL 0))) \/ (real_gt (real_neg (real_sub (real_min x0 x1) (real_neg (real_max (real_neg x0) (real_neg x1))))) (real_of_num (NUMERAL 0))).
Definition term68 (x0 : real -> Prop) (x1 : real -> Prop) := exists y0 : real, (x0 y0) \/ (x1 y0).
Definition term89 (x0 : real) := (exists y0 : real, real_gt (real_add (real_max (real_neg x0) (real_neg y0)) (real_min x0 y0)) (real_of_num (NUMERAL 0))) \/ (exists y0 : real, real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max (real_neg x0) (real_neg y0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_min x0 y0))) (real_of_num (NUMERAL 0))).
Definition term12 := ~ (forall y0 : real, forall y1 : real, (real_min y0 y1) = (real_neg (real_max (real_neg y0) (real_neg y1)))).
Definition term210 (x0 : real) (x1 : real) := real_gt (real_sub (real_neg x0) (real_neg x1)).
Definition term288 := Peano.lt (NUMERAL 0) (NUMERAL 0).
Definition term177 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term265 (x0 : real) (x1 : real) := @eq Prop ((real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_min x0 x1))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_min x0 x1))) (real_of_num (NUMERAL 0)))).
Definition term150 (x0 : real) (x1 : real) := @eq Prop ((real_gt (real_add x0 (real_max (real_neg x0) (real_neg x1))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x1 (real_max (real_neg x0) (real_neg x1))) (real_of_num (NUMERAL 0)))).
Definition term194 := real_sub (real_of_num (NUMERAL 0)).
Definition term88 (x0 : real) := exists y0 : real, real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max (real_neg x0) (real_neg y0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_min x0 y0))) (real_of_num (NUMERAL 0)).
Definition term83 (x0 : real) := exists y0 : real, real_gt (real_add (real_max (real_neg x0) (real_neg y0)) (real_min x0 y0)) (real_of_num (NUMERAL 0)).
Definition term259 (x0 : real) (x1 : real) := and (real_ge x0 x1).
Definition term108 := fun y0 : real => (fun y1 : real => exists y2 : real, real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max (real_neg y1) (real_neg y2))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_min y1 y2))) (real_of_num (NUMERAL 0))) y0.
Definition term103 := fun y0 : real => (fun y1 : real => exists y2 : real, real_gt (real_add (real_max (real_neg y1) (real_neg y2)) (real_min y1 y2)) (real_of_num (NUMERAL 0))) y0.
Definition term279 (x0 : real) (x1 : real) := (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))) /\ ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0)))).
Definition term69 (x0 : real -> Prop) (x1 : real -> Prop) := (exists y0 : real, x0 y0) \/ (exists y0 : real, x1 y0).
Definition term202 := real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term45 (x0 : real) (x1 : real) := real_neg (real_sub (real_min x0 x1) (real_neg (real_max (real_neg x0) (real_neg x1)))).
Definition term282 (x0 : real) (x1 : real) := (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))) /\ ((real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))).
Definition term233 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_min x0 x1)) x1.
Definition term22 (x0 : real) (x1 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max (real_neg x0) (real_neg x1)).
Definition term161 (x0 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) x0.
Definition term17 (x0 : real) := ~ ((fun y0 : real => forall y1 : real, (real_min y0 y1) = (real_neg (real_max (real_neg y0) (real_neg y1)))) x0).
Definition term64 := fun y0 : real => exists y1 : real, (real_gt (real_add (real_max (real_neg y0) (real_neg y1)) (real_min y0 y1)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max (real_neg y0) (real_neg y1))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_min y0 y1))) (real_of_num (NUMERAL 0))).
Definition term277 (x0 : real) := and (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_of_num (NUMERAL 0))).
Definition term204 (x0 : real) (x1 : real) := and (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))).
Definition term140 (x0 : real) (x1 : real) := (real_gt (real_neg x1) (real_neg x0)) /\ ((fun y0 : real => (real_gt (real_add x1 y0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 y0) (real_of_num (NUMERAL 0)))) (real_neg x1)).
Definition term232 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_min x0 x1)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg x1)).
Definition term39 := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term244 (x0 : real) (x1 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_min x1 x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg x1))) (real_of_num (NUMERAL 0)).
Definition term237 (x0 : real) (x1 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_min x0 x1)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg x1))) (real_of_num (NUMERAL 0)).
Definition term129 (x0 : real) (x1 : real) := real_gt (real_add (real_max (real_neg x1) (real_neg x0)) x1) (real_of_num (NUMERAL 0)).
Definition term123 (x0 : real) (x1 : real) := real_gt (real_add (real_max (real_neg x0) (real_neg x1)) x1) (real_of_num (NUMERAL 0)).
Definition term102 := @eq Prop (exists y0 : real, (exists y1 : real, real_gt (real_add (real_max (real_neg y0) (real_neg y1)) (real_min y0 y1)) (real_of_num (NUMERAL 0))) \/ (exists y1 : real, real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max (real_neg y0) (real_neg y1))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_min y0 y1))) (real_of_num (NUMERAL 0)))).
Definition term101 := @eq Prop (exists y0 : real, ((fun y1 : real => exists y2 : real, real_gt (real_add (real_max (real_neg y1) (real_neg y2)) (real_min y1 y2)) (real_of_num (NUMERAL 0))) y0) \/ ((fun y1 : real => exists y2 : real, real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max (real_neg y1) (real_neg y2))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_min y1 y2))) (real_of_num (NUMERAL 0))) y0)).
Definition term80 (x0 : real) := @eq Prop (exists y0 : real, (real_gt (real_add (real_max (real_neg x0) (real_neg y0)) (real_min x0 y0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max (real_neg x0) (real_neg y0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_min x0 y0))) (real_of_num (NUMERAL 0)))).
Definition term79 (x0 : real) := @eq Prop (exists y0 : real, ((fun y1 : real => real_gt (real_add (real_max (real_neg x0) (real_neg y1)) (real_min x0 y1)) (real_of_num (NUMERAL 0))) y0) \/ ((fun y1 : real => real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max (real_neg x0) (real_neg y1))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_min x0 y1))) (real_of_num (NUMERAL 0))) y0)).
Definition term151 (x0 : real) (x1 : real) := real_ge (real_neg x0) (real_neg x1).
Definition term1 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term62 (x0 : real) := fun y0 : real => (real_gt (real_add (real_max (real_neg x0) (real_neg y0)) (real_min x0 y0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max (real_neg x0) (real_neg y0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_min x0 y0))) (real_of_num (NUMERAL 0))).
Definition term53 (x0 : real) (x1 : real) := real_gt (real_neg (real_sub (real_min x0 x1) (real_neg (real_max (real_neg x0) (real_neg x1))))) (real_of_num (NUMERAL 0)).
Definition term250 (x0 : real) (x1 : real) := ((real_ge x1 x0) /\ ((fun y0 : real => (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0)) (real_of_num (NUMERAL 0)))) x0)) \/ ((real_gt x0 x1) /\ ((fun y0 : real => (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0)) (real_of_num (NUMERAL 0)))) x1)).
Definition term15 (x0 : real) := (fun y0 : real => forall y1 : real, (real_min y0 y1) = (real_neg (real_max (real_neg y0) (real_neg y1)))) x0.
Definition term287 (x0 : nat) (x1 : nat) := real_gt (real_of_num x0) (real_of_num x1).
Definition term166 (x0 : real) (x1 : real) := real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term229 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term187 (x0 : real) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term8 (x0 : real) (x1 : real) := ~ ((real_min x0 x1) = (real_neg (real_max (real_neg x0) (real_neg x1)))).
Definition term200 (x0 : real) := real_gt (real_sub (real_add x0 (real_neg x0)) (real_of_num (NUMERAL 0))).
Definition term180 (x0 : real) (x1 : real) := real_gt (real_sub (real_add x0 (real_neg x1)) (real_of_num (NUMERAL 0))).
Definition term30 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term179 (x0 : real) (x1 : real) := real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0)).
Definition term289 := (~ (forall y0 : real, forall y1 : real, (real_min y0 y1) = (real_neg (real_max (real_neg y0) (real_neg y1))))) -> False.
Definition term238 (x0 : real) (x1 : real) := real_gt (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_min x0 x1))) (real_of_num (NUMERAL 0)).
Definition term213 (x0 : real) (x1 : real) := real_sub (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1).
Definition term278 (x0 : real) (x1 : real) := and (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))).
Definition term267 (x0 : real) (x1 : real) := real_ge (real_sub x0 x1).
Definition term27 (x0 : real) (x1 : real) := real_add (real_min x0 x1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max (real_neg x0) (real_neg x1)))).
Definition term44 (x0 : real) (x1 : real) := real_add (real_max (real_neg x0) (real_neg x1)) (real_min x0 x1).
Definition term191 := real_mul (real_of_num (NUMERAL 0)).
Definition term185 (x0 : real) := real_add x0 (real_neg x0).
Definition term153 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term156 (x0 : real) (x1 : real) := real_sub (real_neg x0) (real_neg x1).
Definition term236 (x0 : real) (x1 : real) := real_gt (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_min x0 x1))).
Definition term174 (x0 : real) (x1 : real) := real_sub (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0)).
Definition term19 := fun y0 : real => exists y1 : real, ~ ((real_min y0 y1) = (real_neg (real_max (real_neg y0) (real_neg y1)))).
Definition term24 (x0 : real) (x1 : real) := real_sub (real_min x0 x1).
Definition term40 := real_mul (real_of_num (NUMERAL (BIT1 0))).
Definition term78 (x0 : real) := fun y0 : real => ((fun y1 : real => real_gt (real_add (real_max (real_neg x0) (real_neg y1)) (real_min x0 y1)) (real_of_num (NUMERAL 0))) y0) \/ ((fun y1 : real => real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max (real_neg x0) (real_neg y1))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_min x0 y1))) (real_of_num (NUMERAL 0))) y0).
Definition term135 (x0 : real) (x1 : real) := ((real_ge (real_neg x0) (real_neg x1)) /\ ((fun y0 : real => (real_gt (real_add x1 y0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 y0) (real_of_num (NUMERAL 0)))) (real_neg x0))) \/ ((real_gt (real_neg x1) (real_neg x0)) /\ ((fun y0 : real => (real_gt (real_add x1 y0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 y0) (real_of_num (NUMERAL 0)))) (real_neg x1))).
Definition term227 (x0 : real) (x1 : real) := (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_min x0 x1)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg x0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_min x0 x1)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg x1))) (real_of_num (NUMERAL 0))).
Definition term92 := exists y0 : real, ((fun y1 : real => exists y2 : real, real_gt (real_add (real_max (real_neg y1) (real_neg y2)) (real_min y1 y2)) (real_of_num (NUMERAL 0))) y0) \/ ((fun y1 : real => exists y2 : real, real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max (real_neg y1) (real_neg y2))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_min y1 y2))) (real_of_num (NUMERAL 0))) y0).
Definition term70 (x0 : real) := exists y0 : real, ((fun y1 : real => real_gt (real_add (real_max (real_neg x0) (real_neg y1)) (real_min x0 y1)) (real_of_num (NUMERAL 0))) y0) \/ ((fun y1 : real => real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max (real_neg x0) (real_neg y1))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_min x0 y1))) (real_of_num (NUMERAL 0))) y0).
Definition term46 (x0 : real) (x1 : real) := real_neg (real_add (real_max (real_neg x0) (real_neg x1)) (real_min x0 x1)).
Definition term175 (x0 : real) (x1 : real) := real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term290 := ((~ (forall y0 : real, forall y1 : real, (real_min y0 y1) = (real_neg (real_max (real_neg y0) (real_neg y1))))) -> False) -> forall y0 : real, forall y1 : real, (real_min y0 y1) = (real_neg (real_max (real_neg y0) (real_neg y1))).
Definition term280 (x0 : real) (x1 : real) := real_gt (real_sub x0 x1) (real_of_num (NUMERAL 0)).
Definition term228 (x0 : real) (x1 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_min x0 x1).
Definition term5 (x0 : real) (x1 : real) := (fun y0 : real => (real_min x0 y0) = (real_neg (real_max (real_neg x0) (real_neg y0)))) x1.
Definition term148 (x0 : real) (x1 : real) := or ((real_ge (real_neg x1) (real_neg x0)) /\ ((real_gt (real_add x0 (real_neg x1)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x1 (real_neg x1)) (real_of_num (NUMERAL 0))))).
Definition term57 (x0 : real) (x1 : real) := real_gt (real_sub (real_min x0 x1) (real_neg (real_max (real_neg x0) (real_neg x1)))) (real_of_num (NUMERAL 0)).
Definition term173 (x0 : real) (x1 : real) := real_sub (real_add x0 (real_neg x1)) (real_of_num (NUMERAL 0)).
Definition term207 (x0 : real) (x1 : real) := (real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))) /\ ((real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))).
Definition term31 (x0 : nat) (x1 : nat) := real_mul (real_neg (real_of_num x0)) (real_neg (real_of_num x1)).
Definition term178 (x0 : real) (x1 : real) := real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term254 (x0 : real) (x1 : real) := and (real_gt x0 x1).
Definition term75 (x0 : real) (x1 : real) := or ((fun y0 : real => real_gt (real_add (real_max (real_neg x0) (real_neg y0)) (real_min x0 y0)) (real_of_num (NUMERAL 0))) x1).
Definition term243 (x0 : real) (x1 : real) := real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_min x0 x1))).
Definition term239 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_min x1 x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg x1)).
Definition term205 (x0 : real) (x1 : real) := (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term34 := real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term272 (x0 : real) := real_sub (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)).
Definition term38 := real_of_num (NUMERAL (BIT1 0)).
Definition term162 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term59 (x0 : real) (x1 : real) := or (real_gt (real_sub (real_min x0 x1) (real_neg (real_max (real_neg x0) (real_neg x1)))) (real_of_num (NUMERAL 0))).
Definition term270 (x0 : real) := real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_of_num (NUMERAL 0)).
Definition term48 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max (real_neg x0) (real_neg x1))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_min x0 x1)).
Definition term273 (x0 : real) := real_sub (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_of_num (NUMERAL 0)).
Definition term128 (x0 : real) (x1 : real) := real_gt (real_add x0 (real_max (real_neg x0) (real_neg x1))).
Definition term86 (x0 : real) := fun y0 : real => (fun y1 : real => real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max (real_neg x0) (real_neg y1))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_min x0 y1))) (real_of_num (NUMERAL 0))) y0.
Definition term81 (x0 : real) := fun y0 : real => (fun y1 : real => real_gt (real_add (real_max (real_neg x0) (real_neg y1)) (real_min x0 y1)) (real_of_num (NUMERAL 0))) y0.
Definition term77 (x0 : real) (x1 : real) := ((fun y0 : real => real_gt (real_add (real_max (real_neg x0) (real_neg y0)) (real_min x0 y0)) (real_of_num (NUMERAL 0))) x1) \/ ((fun y0 : real => real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max (real_neg x0) (real_neg y0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_min x0 y0))) (real_of_num (NUMERAL 0))) x1).
Definition term141 (x0 : real) (x1 : real) := (real_gt (real_neg x1) (real_neg x0)) /\ ((real_gt (real_add x1 (real_neg x1)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_neg x1)) (real_of_num (NUMERAL 0)))).
Definition term192 (x0 : real) := real_mul (real_of_num (NUMERAL 0)) x0.
Definition term234 (x0 : real) (x1 : real) := real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_min x0 x1)).
Definition term76 (x0 : real) (x1 : real) := (fun y0 : real => real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max (real_neg x0) (real_neg y0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_min x0 y0))) (real_of_num (NUMERAL 0))) x1.
Definition term160 (x0 : real) := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) x0.
Definition term263 (x0 : real) (x1 : real) := or ((real_ge x0 x1) /\ ((real_gt (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))))).
Definition term142 (x0 : real) (x1 : real) := (fun y0 : real => (real_gt (real_add x0 y0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x1 y0) (real_of_num (NUMERAL 0)))) (real_neg x1).
Definition term137 (x0 : real) (x1 : real) := (fun y0 : real => (real_gt (real_add x1 y0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 y0) (real_of_num (NUMERAL 0)))) (real_neg x1).
Definition term9 (x0 : real) := fun y0 : real => ~ ((fun y1 : real => (real_min x0 y1) = (real_neg (real_max (real_neg x0) (real_neg y1)))) y0).
Definition term275 (x0 : real) (x1 : real) := real_gt (real_sub (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term271 (x0 : real) := real_gt (real_sub (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term184 (x0 : real) := real_gt (real_sub (real_add x0 (real_neg x0)) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term169 (x0 : real) (x1 : real) := real_gt (real_sub (real_add x0 (real_neg x1)) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term206 (x0 : real) (x1 : real) := and (real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))).
Definition term144 (x0 : real) (x1 : real) := and (real_ge (real_neg x0) (real_neg x1)).
Definition term255 (x0 : real) (x1 : real) := (real_gt x0 x1) /\ ((fun y0 : real => (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0)) (real_of_num (NUMERAL 0)))) x1).
Definition term32 (x0 : nat) (x1 : nat) := real_of_num (Nat.mul x0 x1).
Definition term55 (x0 : real) (x1 : real) := real_gt (real_sub (real_min x0 x1) (real_neg (real_max (real_neg x0) (real_neg x1)))).
Definition term119 (x0 : real) (x1 : real) := real_add (real_max (real_neg x0) (real_neg x1)) x1.
Definition term215 (x0 : real) (x1 : real) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term264 (x0 : real) (x1 : real) := ((real_ge x1 x0) /\ ((real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_of_num (NUMERAL 0))))) \/ ((real_gt x0 x1) /\ ((real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))))).
Definition term199 := real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term246 (x0 : real) (x1 : real) := and (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_min x1 x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg x1))) (real_of_num (NUMERAL 0))).
Definition term262 (x0 : real) (x1 : real) := or ((real_ge x0 x1) /\ ((fun y0 : real => (real_gt (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0)) (real_of_num (NUMERAL 0)))) x1)).
Definition term130 (x0 : real) (x1 : real) := real_gt (real_add x0 (real_max (real_neg x0) (real_neg x1))) (real_of_num (NUMERAL 0)).
Definition term134 (x0 : real) (x1 : real) := (fun y0 : real => (real_gt (real_add x0 y0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x1 y0) (real_of_num (NUMERAL 0)))) (real_max (real_neg x0) (real_neg x1)).
Definition term218 (x0 : real) := and (real_gt (real_add x0 (real_neg x0)) (real_of_num (NUMERAL 0))).
Definition term203 (x0 : real) (x1 : real) := and (real_gt (real_add x0 (real_neg x1)) (real_of_num (NUMERAL 0))).
Definition term157 (x0 : real) (x1 : real) := real_sub (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1).
Definition term164 (x0 : real) (x1 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1).
Definition term189 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term25 (x0 : real) (x1 : real) := real_sub (real_min x0 x1) (real_neg (real_max (real_neg x0) (real_neg x1))).
Definition term91 := exists y0 : real, (exists y1 : real, real_gt (real_add (real_max (real_neg y0) (real_neg y1)) (real_min y0 y1)) (real_of_num (NUMERAL 0))) \/ (exists y1 : real, real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max (real_neg y0) (real_neg y1))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_min y0 y1))) (real_of_num (NUMERAL 0))).
Definition term100 := fun y0 : real => ((fun y1 : real => exists y2 : real, real_gt (real_add (real_max (real_neg y1) (real_neg y2)) (real_min y1 y2)) (real_of_num (NUMERAL 0))) y0) \/ ((fun y1 : real => exists y2 : real, real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max (real_neg y1) (real_neg y2))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_min y1 y2))) (real_of_num (NUMERAL 0))) y0).
Definition term124 (x0 : real) (x1 : real) := real_gt (real_add x1 (real_max (real_neg x0) (real_neg x1))) (real_of_num (NUMERAL 0)).
Definition term149 (x0 : real) (x1 : real) := ((real_ge (real_neg x0) (real_neg x1)) /\ ((real_gt (real_add x1 (real_neg x0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_neg x0)) (real_of_num (NUMERAL 0))))) \/ ((real_gt (real_neg x1) (real_neg x0)) /\ ((real_gt (real_add x1 (real_neg x1)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_neg x1)) (real_of_num (NUMERAL 0))))).
Definition term281 (x0 : real) (x1 : real) := real_gt (real_sub x0 x1).
Definition term225 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x0 x1)) x2) x3.
Definition term198 := real_add (real_of_num (NUMERAL 0)).
Definition term85 (x0 : real) := or (exists y0 : real, real_gt (real_add (real_max (real_neg x0) (real_neg y0)) (real_min x0 y0)) (real_of_num (NUMERAL 0))).
Definition term107 := or (exists y0 : real, exists y1 : real, real_gt (real_add (real_max (real_neg y0) (real_neg y1)) (real_min y0 y1)) (real_of_num (NUMERAL 0))).
Definition term66 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term212 (x0 : real) (x1 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0)).
Definition term90 := fun y0 : real => (exists y1 : real, real_gt (real_add (real_max (real_neg y0) (real_neg y1)) (real_min y0 y1)) (real_of_num (NUMERAL 0))) \/ (exists y1 : real, real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max (real_neg y0) (real_neg y1))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_min y0 y1))) (real_of_num (NUMERAL 0))).
Definition term209 (x0 : real) (x1 : real) := real_gt (real_sub (real_neg x0) (real_neg x1)) (real_of_num (NUMERAL 0)).
Definition term61 (x0 : real) (x1 : real) := (real_gt (real_add (real_max (real_neg x0) (real_neg x1)) (real_min x0 x1)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max (real_neg x0) (real_neg x1))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_min x0 x1))) (real_of_num (NUMERAL 0))).
Definition term158 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term216 (x0 : real) (x1 : real) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1).
Definition term116 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_gt (real_add x0 (real_min x1 x2)) x3.
Definition term35 := NUMERAL (BIT1 0).
Definition term93 := (exists y0 : real, (fun y1 : real => exists y2 : real, real_gt (real_add (real_max (real_neg y1) (real_neg y2)) (real_min y1 y2)) (real_of_num (NUMERAL 0))) y0) \/ (exists y0 : real, (fun y1 : real => exists y2 : real, real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max (real_neg y1) (real_neg y2))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_min y1 y2))) (real_of_num (NUMERAL 0))) y0).
Definition term71 (x0 : real) := (exists y0 : real, (fun y1 : real => real_gt (real_add (real_max (real_neg x0) (real_neg y1)) (real_min x0 y1)) (real_of_num (NUMERAL 0))) y0) \/ (exists y0 : real, (fun y1 : real => real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max (real_neg x0) (real_neg y1))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_min x0 y1))) (real_of_num (NUMERAL 0))) y0).
Definition term196 := real_sub (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term63 (x0 : real) := exists y0 : real, (real_gt (real_add (real_max (real_neg x0) (real_neg y0)) (real_min x0 y0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max (real_neg x0) (real_neg y0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_min x0 y0))) (real_of_num (NUMERAL 0))).
Definition term72 (x0 : real) := fun y0 : real => real_gt (real_add (real_max (real_neg x0) (real_neg y0)) (real_min x0 y0)) (real_of_num (NUMERAL 0)).
Definition term186 (x0 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term14 := fun y0 : real => forall y1 : real, (real_min y0 y1) = (real_neg (real_max (real_neg y0) (real_neg y1))).
Definition term247 (x0 : real) (x1 : real) := and (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_min x0 x1))) (real_of_num (NUMERAL 0))).
Definition term132 (x0 : real) (x1 : real) := and (real_gt (real_add x0 (real_max (real_neg x0) (real_neg x1))) (real_of_num (NUMERAL 0))).
Definition term245 (x0 : real) (x1 : real) := real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_min x0 x1))) (real_of_num (NUMERAL 0)).
Definition term26 (x0 : real) (x1 : real) := real_sub (real_min x0 x1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max (real_neg x0) (real_neg x1))).
Definition term16 (x0 : real) := forall y0 : real, (real_min x0 y0) = (real_neg (real_max (real_neg x0) (real_neg y0))).
Definition term241 (x0 : real) (x1 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_min x0 x1)).
Definition term109 := exists y0 : real, (fun y1 : real => exists y2 : real, real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max (real_neg y1) (real_neg y2))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_min y1 y2))) (real_of_num (NUMERAL 0))) y0.
Definition term104 := exists y0 : real, (fun y1 : real => exists y2 : real, real_gt (real_add (real_max (real_neg y1) (real_neg y2)) (real_min y1 y2)) (real_of_num (NUMERAL 0))) y0.
Definition term220 (x0 : real) (x1 : real) := (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))).
Definition term266 (x0 : real) (x1 : real) := real_ge (real_sub x0 x1) (real_of_num (NUMERAL 0)).
Definition term201 := real_gt (real_of_num (NUMERAL 0)).
Definition term115 (x0 : real) := @eq Prop ((exists y0 : real, real_gt (real_add (real_max (real_neg x0) (real_neg y0)) (real_min x0 y0)) (real_of_num (NUMERAL 0))) \/ (exists y0 : real, real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max (real_neg x0) (real_neg y0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_min x0 y0))) (real_of_num (NUMERAL 0)))).
Definition term114 (x0 : real) := @eq Prop ((exists y0 : real, (fun y1 : real => real_gt (real_add (real_max (real_neg x0) (real_neg y1)) (real_min x0 y1)) (real_of_num (NUMERAL 0))) y0) \/ (exists y0 : real, (fun y1 : real => real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max (real_neg x0) (real_neg y1))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_min x0 y1))) (real_of_num (NUMERAL 0))) y0)).
Definition term113 := @eq Prop ((exists y0 : real, exists y1 : real, real_gt (real_add (real_max (real_neg y0) (real_neg y1)) (real_min y0 y1)) (real_of_num (NUMERAL 0))) \/ (exists y0 : real, exists y1 : real, real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max (real_neg y0) (real_neg y1))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_min y0 y1))) (real_of_num (NUMERAL 0)))).
Definition term112 := @eq Prop ((exists y0 : real, (fun y1 : real => exists y2 : real, real_gt (real_add (real_max (real_neg y1) (real_neg y2)) (real_min y1 y2)) (real_of_num (NUMERAL 0))) y0) \/ (exists y0 : real, (fun y1 : real => exists y2 : real, real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max (real_neg y1) (real_neg y2))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_min y1 y2))) (real_of_num (NUMERAL 0))) y0)).
