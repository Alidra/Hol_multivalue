Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term307 (x0 : real) (x1 : nat) (x2 : real) := (real_lt (real_inv x2) (real_pow (real_inv x0) x1)) -> real_lt (real_pow x0 x1) x2.
Definition term199 (x0 : real) := ~ ((real_pow x0 (NUMERAL (BIT1 0))) = x0).
Definition term49 (x0 : real) (x1 : real) := ~ (exists y0 : nat, real_lt (real_pow x0 y0) x1).
Definition term295 (x0 : real) := (real_lt (real_of_num (NUMERAL (BIT1 0))) (real_inv x0)) -> forall y0 : real, exists y1 : nat, real_lt y0 (real_pow (real_inv x0) y1).
Definition term279 (x0 : real) (x1 : real) := ((real_lt (real_of_num (NUMERAL 0)) x1) /\ (real_lt x1 x0)) -> real_lt (real_inv x0) (real_inv x1).
Definition term272 := (~ False) -> False.
Definition term230 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (x0 = x2) /\ ((x1 = x3) /\ (~ (real_lt x2 x3))).
Definition term60 := imp (forall y0 : real, forall y1 : real, (~ (real_lt y0 y1)) = (real_le y1 y0)).
Definition term57 := imp (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2).
Definition term335 (x0 : real) := real_lt (real_inv x0).
Definition term168 (x0 : real) (x1 : real) (x2 : real) := or (~ ((real_le x0 x1) /\ (real_lt x1 x2))).
Definition term66 (x0 : real) := imp (~ (real_lt (real_of_num (NUMERAL 0)) x0)).
Definition term280 (x0 : real) (x1 : real) := (real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt x0 x1).
Definition term52 (x0 : real) (x1 : real) := (((real_lt (real_of_num (NUMERAL 0)) x1) -> (real_lt x0 (real_of_num (NUMERAL (BIT1 0)))) -> (~ (real_lt (real_of_num (NUMERAL 0)) x0)) -> (~ (exists y0 : nat, real_lt (real_pow x0 y0) x1)) -> (forall y0 : real, forall y1 : real, (~ (real_lt y0 y1)) = (real_le y1 y0)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2) -> (forall y0 : real, (real_pow y0 (NUMERAL (BIT1 0))) = y0) -> False) -> (real_lt (real_of_num (NUMERAL 0)) x1) -> (real_lt x0 (real_of_num (NUMERAL (BIT1 0)))) -> (~ (real_lt (real_of_num (NUMERAL 0)) x0)) -> (~ (exists y0 : nat, real_lt (real_pow x0 y0) x1)) -> (forall y0 : real, forall y1 : real, (~ (real_lt y0 y1)) = (real_le y1 y0)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2) -> (forall y0 : real, (real_pow y0 (NUMERAL (BIT1 0))) = y0) -> False) -> (real_lt (real_of_num (NUMERAL 0)) x1) -> (real_lt x0 (real_of_num (NUMERAL (BIT1 0)))) -> (~ (real_lt (real_of_num (NUMERAL 0)) x0)) -> (~ (exists y0 : nat, real_lt (real_pow x0 y0) x1)) -> (forall y0 : real, forall y1 : real, (~ (real_lt y0 y1)) = (real_le y1 y0)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2) -> (forall y0 : real, (real_pow y0 (NUMERAL (BIT1 0))) = y0) -> False.
Definition term12 := fun y0 : real => y0 = (real_inv (real_inv y0)).
Definition term316 (x0 : real) (x1 : real) := imp (exists y0 : nat, (fun y1 : nat => real_lt (real_inv x0) (real_pow (real_inv x1) y1)) y0).
Definition term73 (x0 : real) (x1 : real) := (real_lt (real_of_num (NUMERAL 0)) x1) -> (real_lt x0 (real_of_num (NUMERAL (BIT1 0)))) -> (~ (real_lt (real_of_num (NUMERAL 0)) x0)) -> (~ (exists y0 : nat, real_lt (real_pow x0 y0) x1)) -> (forall y0 : real, forall y1 : real, (~ (real_lt y0 y1)) = (real_le y1 y0)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2) -> ~ (forall y0 : real, (real_pow y0 (NUMERAL (BIT1 0))) = y0).
Definition term50 (x0 : real) (x1 : real) := (real_lt (real_of_num (NUMERAL 0)) x1) -> (real_lt x0 (real_of_num (NUMERAL (BIT1 0)))) -> (~ (real_lt (real_of_num (NUMERAL 0)) x0)) -> (~ (exists y0 : nat, real_lt (real_pow x0 y0) x1)) -> (forall y0 : real, forall y1 : real, (~ (real_lt y0 y1)) = (real_le y1 y0)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2) -> (forall y0 : real, (real_pow y0 (NUMERAL (BIT1 0))) = y0) -> False.
Definition term291 (x0 : real) := imp (real_lt (real_inv (real_of_num (NUMERAL (BIT1 0)))) (real_inv x0)).
Definition term25 (x0 : real) (x1 : real) := (real_lt (real_of_num (NUMERAL (BIT1 0))) x1) -> exists y0 : nat, real_lt x0 (real_pow x1 y0).
Definition term223 (x0 : Prop) := ~ (~ x0).
Definition term194 := real_of_num (NUMERAL 0).
Definition term236 (x0 : real) := (((real_of_num (NUMERAL 0)) = (real_of_num (NUMERAL 0))) /\ (((real_pow x0 (NUMERAL (BIT1 0))) = x0) /\ (~ (real_lt (real_of_num (NUMERAL 0)) x0)))) -> ~ (real_lt (real_of_num (NUMERAL 0)) (real_pow x0 (NUMERAL (BIT1 0)))).
Definition term302 (x0 : real) (x1 : real) (x2 : nat) := (fun y0 : nat => real_lt (real_inv x0) (real_pow (real_inv x1) y0)) x2.
Definition term248 (x0 : real) := (~ (real_lt (real_of_num (NUMERAL 0)) x0)) -> real_lt (real_of_num (NUMERAL 0)) x0.
Definition term269 (x0 : real) (x1 : nat) (x2 : real) := (real_lt (real_pow x0 x1) x2) -> False.
Definition term161 := and (forall y0 : real, forall y1 : real, (~ (real_lt y0 y1)) \/ (~ (real_le y1 y0))).
Definition term32 (x0 : real) := (fun y0 : real => (real_lt (real_of_num (NUMERAL (BIT1 0))) y0) -> forall y1 : real, exists y2 : nat, real_lt y1 (real_pow y0 y2)) x0.
Definition term77 (x0 : real) := forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) x0) -> (real_lt y0 (real_of_num (NUMERAL (BIT1 0)))) -> (~ (real_lt (real_of_num (NUMERAL 0)) y0)) -> (~ (exists y1 : nat, real_lt (real_pow y0 y1) x0)) -> (forall y1 : real, forall y2 : real, (~ (real_lt y1 y2)) = (real_le y2 y1)) -> (forall y1 : real, forall y2 : real, forall y3 : real, ((real_le y1 y2) /\ (real_lt y2 y3)) -> real_lt y1 y3) -> ~ (forall y1 : real, (real_pow y1 (NUMERAL (BIT1 0))) = y1).
Definition term76 (x0 : real) := forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) x0) -> (real_lt y0 (real_of_num (NUMERAL (BIT1 0)))) -> (~ (real_lt (real_of_num (NUMERAL 0)) y0)) -> (~ (exists y1 : nat, real_lt (real_pow y0 y1) x0)) -> (forall y1 : real, forall y2 : real, (~ (real_lt y1 y2)) = (real_le y2 y1)) -> (forall y1 : real, forall y2 : real, forall y3 : real, ((real_le y1 y2) /\ (real_lt y2 y3)) -> real_lt y1 y3) -> (forall y1 : real, (real_pow y1 (NUMERAL (BIT1 0))) = y1) -> False.
Definition term244 (x0 : real) := (~ (real_lt (real_of_num (NUMERAL 0)) (real_pow x0 (NUMERAL (BIT1 0))))) -> real_le (real_pow x0 (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term338 (x0 : real) (x1 : real) := ((real_lt (real_of_num (NUMERAL 0)) x1) /\ (real_lt x0 (real_of_num (NUMERAL (BIT1 0))))) -> exists y0 : nat, real_lt (real_pow x0 y0) x1.
Definition term82 (x0 : real) := real_pow x0 (NUMERAL (BIT1 0)).
Definition term139 (x0 : real) := and (forall y0 : real, (~ (real_lt x0 y0)) \/ (~ (real_le y0 x0))).
Definition term222 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (~ (x0 = x2))) /\ (~ ((~ (x1 = x3)) \/ (real_lt x2 x3))).
Definition term270 (x0 : real) (x1 : real) := (real_lt (real_pow x0 (NUMERAL (BIT1 0))) x1) -> False.
Definition term258 (x0 : real) (x1 : real) (x2 : real) := (~ (~ (real_le x0 x1))) /\ (~ (~ (real_lt x1 x2))).
Definition term259 (x0 : real) (x1 : real) := ~ (~ (real_le x0 x1)).
Definition term249 (x0 : real) (x1 : real) (x2 : real) := (~ (real_lt x0 x2)) \/ (real_lt x1 x2).
Definition term212 (x0 : real) (x1 : real) (x2 : real) := (~ (x0 = x2)) \/ (real_lt x1 x2).
Definition term151 (x0 : real) := and ((fun y0 : real => forall y1 : real, (~ (real_lt y0 y1)) \/ (~ (real_le y1 y0))) x0).
Definition term14 := forall y0 : real, y0 = (real_inv (real_inv y0)).
Definition term101 (x0 : real) (x1 : real) (x2 : nat) := (fun y0 : nat => real_lt (real_pow x0 y0) x1) x2.
Definition term62 := (forall y0 : real, forall y1 : real, (~ (real_lt y0 y1)) = (real_le y1 y0)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2) -> ~ (forall y0 : real, (real_pow y0 (NUMERAL (BIT1 0))) = y0).
Definition term142 (x0 : real) := forall y0 : real, (real_lt x0 y0) \/ (real_le y0 x0).
Definition term54 := (forall y0 : real, (real_pow y0 (NUMERAL (BIT1 0))) = y0) -> False.
Definition term36 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0).
Definition term97 (x0 : real) (x1 : real) := fun y0 : nat => real_lt (real_pow x0 y0) x1.
Definition term160 := and (forall y0 : real, (fun y1 : real => forall y2 : real, (~ (real_lt y1 y2)) \/ (~ (real_le y2 y1))) y0).
Definition term138 (x0 : real) := and (forall y0 : real, (fun y1 : real => (~ (real_lt x0 y1)) \/ (~ (real_le y1 x0))) y0).
Definition term46 (x0 : Prop) := (~ x0) -> False.
Definition term262 (x0 : real) (x1 : real) (x2 : real) := imp (~ ((~ (real_le x0 x1)) \/ (~ (real_lt x1 x2)))).
Definition term310 (x0 : real) (x1 : real) := forall y0 : nat, ((fun y1 : nat => real_lt (real_inv x1) (real_pow (real_inv x0) y1)) y0) -> (fun y1 : nat => real_lt (real_pow x0 y1) x1) y0.
Definition term253 (x0 : real) (x1 : real) (x2 : real) := (real_lt x0 x2) \/ ((~ (real_le x0 x1)) \/ (~ (real_lt x1 x2))).
Definition term144 := fun y0 : real => (forall y1 : real, (~ (real_lt y0 y1)) \/ (~ (real_le y1 y0))) /\ (forall y1 : real, (real_lt y0 y1) \/ (real_le y1 y0)).
Definition term213 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (real_lt x0 x1)) \/ ((~ (x1 = x3)) \/ (real_lt x2 x3)).
Definition term336 (x0 : real) (x1 : real) (x2 : nat) := real_lt (real_inv x0) (real_inv (real_pow x1 x2)).
Definition term165 := (forall y0 : real, forall y1 : real, (~ (real_lt y0 y1)) \/ (~ (real_le y1 y0))) /\ (forall y0 : real, forall y1 : real, (real_lt y0 y1) \/ (real_le y1 y0)).
Definition term264 (x0 : real) (x1 : real) := (real_le (real_pow x0 (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_lt (real_of_num (NUMERAL 0)) x1).
Definition term55 := ~ (forall y0 : real, (real_pow y0 (NUMERAL (BIT1 0))) = y0).
Definition term109 (x0 : real) (x1 : real) := or (real_lt x0 x1).
Definition term216 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term11 := fun y0 : real => (real_inv (real_inv y0)) = y0.
Definition term147 := (forall y0 : real, (fun y1 : real => forall y2 : real, (~ (real_lt y1 y2)) \/ (~ (real_le y2 y1))) y0) /\ (forall y0 : real, (fun y1 : real => forall y2 : real, (real_lt y1 y2) \/ (real_le y2 y1)) y0).
Definition term124 (x0 : real) := (forall y0 : real, (fun y1 : real => (~ (real_lt x0 y1)) \/ (~ (real_le y1 x0))) y0) /\ (forall y0 : real, (fun y1 : real => (real_lt x0 y1) \/ (real_le y1 x0)) y0).
Definition term47 (x0 : real) (x1 : real) := exists y0 : nat, real_lt (real_pow x0 y0) x1.
Definition term325 (x0 : real) (x1 : nat) := real_lt (real_inv (real_inv (real_pow x0 x1))).
Definition term242 (x0 : real) (x1 : real) := @eq Prop ((real_le x1 x0) \/ (real_lt x0 x1)).
Definition term278 (x0 : real) (x1 : real) := (fun y0 : real => ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt x0 y0)) -> real_lt (real_inv y0) (real_inv x0)) x1.
Definition term228 (x0 : real) (x1 : real) (x2 : real) := (~ (~ (x0 = x2))) /\ (~ (real_lt x1 x2)).
Definition term197 (x0 : Prop) := (~ x0) -> x0.
Definition term29 (x0 : real) := (real_lt (real_of_num (NUMERAL (BIT1 0))) x0) -> forall y0 : real, exists y1 : nat, real_lt y0 (real_pow x0 y1).
Definition term233 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ((x2 = x0) /\ ((x3 = x1) /\ (~ (real_lt x0 x1)))) -> ~ (real_lt x2 x3).
Definition term162 := fun y0 : real => (fun y1 : real => forall y2 : real, (real_lt y1 y2) \/ (real_le y2 y1)) y0.
Definition term157 := fun y0 : real => (fun y1 : real => forall y2 : real, (~ (real_lt y1 y2)) \/ (~ (real_le y2 y1))) y0.
Definition term339 (x0 : real) := forall y0 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt x0 (real_of_num (NUMERAL (BIT1 0))))) -> exists y1 : nat, real_lt (real_pow x0 y1) y0.
Definition term314 (x0 : real) (x1 : real) := fun y0 : nat => (fun y1 : nat => real_lt (real_inv x0) (real_pow (real_inv x1) y1)) y0.
Definition term220 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term85 (x0 : real) (x1 : real) := fun y0 : real => ((real_le x1 x0) /\ (real_lt x0 y0)) -> real_lt x1 y0.
Definition term337 (x0 : real) (x1 : real) (x2 : nat) := (real_lt (real_of_num (NUMERAL 0)) (real_inv x0)) /\ (real_lt (real_inv x0) (real_inv (real_pow x1 x2))).
Definition term298 (x0 : real) (x1 : real) := exists y0 : nat, real_lt (real_inv x0) (real_pow (real_inv x1) y0).
Definition term265 (x0 : real) (x1 : real) := ((real_le (real_pow x0 (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_lt (real_of_num (NUMERAL 0)) x1)) -> real_lt (real_pow x0 (NUMERAL (BIT1 0))) x1.
Definition term254 (x0 : real) (x1 : real) (x2 : real) := @eq Prop ((~ (real_le x1 x0)) \/ ((~ (real_lt x0 x2)) \/ (real_lt x1 x2))).
Definition term48 (x0 : real) (x1 : real) := (~ (exists y0 : nat, real_lt (real_pow x0 y0) x1)) -> False.
Definition term61 := (forall y0 : real, forall y1 : real, (~ (real_lt y0 y1)) = (real_le y1 y0)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2) -> (forall y0 : real, (real_pow y0 (NUMERAL (BIT1 0))) = y0) -> False.
Definition term340 := forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y1) /\ (real_lt y0 (real_of_num (NUMERAL (BIT1 0))))) -> exists y2 : nat, real_lt (real_pow y0 y2) y1.
Definition term178 := forall y0 : real, forall y1 : real, forall y2 : real, ((~ (real_le y0 y1)) \/ (~ (real_lt y1 y2))) \/ (real_lt y0 y2).
Definition term176 (x0 : real) := forall y0 : real, forall y1 : real, ((~ (real_le x0 y0)) \/ (~ (real_lt y0 y1))) \/ (real_lt x0 y1).
Definition term164 := forall y0 : real, forall y1 : real, (real_lt y0 y1) \/ (real_le y1 y0).
Definition term159 := forall y0 : real, forall y1 : real, (~ (real_lt y0 y1)) \/ (~ (real_le y1 y0)).
Definition term118 := forall y0 : real, forall y1 : real, ((~ (real_lt y0 y1)) \/ (~ (real_le y1 y0))) /\ ((real_lt y0 y1) \/ (real_le y1 y0)).
Definition term95 := forall y0 : real, forall y1 : real, (~ (real_lt y0 y1)) = (real_le y1 y0).
Definition term90 := forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2.
Definition term88 (x0 : real) := forall y0 : real, forall y1 : real, ((real_le x0 y0) /\ (real_lt y0 y1)) -> real_lt x0 y1.
Definition term81 := forall y0 : real, forall y1 : real, (real_lt (real_of_num (NUMERAL 0)) y0) -> (real_lt y1 (real_of_num (NUMERAL (BIT1 0)))) -> (~ (real_lt (real_of_num (NUMERAL 0)) y1)) -> (~ (exists y2 : nat, real_lt (real_pow y1 y2) y0)) -> (forall y2 : real, forall y3 : real, (~ (real_lt y2 y3)) = (real_le y3 y2)) -> (forall y2 : real, forall y3 : real, forall y4 : real, ((real_le y2 y3) /\ (real_lt y3 y4)) -> real_lt y2 y4) -> ~ (forall y2 : real, (real_pow y2 (NUMERAL (BIT1 0))) = y2).
Definition term80 := forall y0 : real, forall y1 : real, (real_lt (real_of_num (NUMERAL 0)) y0) -> (real_lt y1 (real_of_num (NUMERAL (BIT1 0)))) -> (~ (real_lt (real_of_num (NUMERAL 0)) y1)) -> (~ (exists y2 : nat, real_lt (real_pow y1 y2) y0)) -> (forall y2 : real, forall y3 : real, (~ (real_lt y2 y3)) = (real_le y3 y2)) -> (forall y2 : real, forall y3 : real, forall y4 : real, ((real_le y2 y3) /\ (real_lt y3 y4)) -> real_lt y2 y4) -> (forall y2 : real, (real_pow y2 (NUMERAL (BIT1 0))) = y2) -> False.
Definition term21 := forall y0 : real, forall y1 : real, (real_lt (real_of_num (NUMERAL (BIT1 0))) y0) -> exists y2 : nat, real_lt y1 (real_pow y0 y2).
Definition term9 := forall y0 : real, forall y1 : nat, (real_inv (real_pow y0 y1)) = (real_pow (real_inv y0) y1).
Definition term8 := forall y0 : real, forall y1 : nat, (real_pow (real_inv y0) y1) = (real_inv (real_pow y0 y1)).
Definition term331 (x0 : real) (x1 : nat) := (fun y0 : nat => (real_inv (real_pow x0 y0)) = (real_pow (real_inv x0) y0)) x1.
Definition term301 (x0 : real) (x1 : real) := fun y0 : nat => real_lt (real_inv x0) (real_pow (real_inv x1) y0).
Definition term317 (x0 : real) (x1 : real) := imp (exists y0 : nat, real_lt (real_inv x0) (real_pow (real_inv x1) y0)).
Definition term255 (x0 : real) (x1 : real) (x2 : real) := @eq Prop ((real_lt x0 x2) \/ ((~ (real_le x0 x1)) \/ (~ (real_lt x1 x2)))).
Definition term15 (x0 : real) := (fun y0 : real => y0 = (real_inv (real_inv y0))) x0.
Definition term116 (x0 : real) := forall y0 : real, ((~ (real_lt x0 y0)) \/ (~ (real_le y0 x0))) /\ ((real_lt x0 y0) \/ (real_le y0 x0)).
Definition term283 (x0 : real) := ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt x0 (real_of_num (NUMERAL (BIT1 0))))) -> (real_lt (real_inv (real_of_num (NUMERAL (BIT1 0)))) (real_inv x0)) = True.
Definition term3 (x0 : real) := fun y0 : nat => (real_inv (real_pow x0 y0)) = (real_pow (real_inv x0) y0).
Definition term120 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term58 := (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2) -> (forall y0 : real, (real_pow y0 (NUMERAL (BIT1 0))) = y0) -> False.
Definition term210 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (real_lt x0 x1)) \/ ((~ (x0 = x2)) \/ ((~ (x1 = x3)) \/ (real_lt x2 x3))).
Definition term83 := fun y0 : real => (real_pow y0 (NUMERAL (BIT1 0))) = y0.
Definition term38 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term13 := forall y0 : real, (real_inv (real_inv y0)) = y0.
Definition term318 (x0 : real) (x1 : real) := fun y0 : nat => (fun y1 : nat => real_lt (real_pow x0 y1) x1) y0.
Definition term285 (x0 : real) := and (real_lt (real_of_num (NUMERAL 0)) x0).
Definition term43 (x0 : real) := ~ (real_lt (real_of_num (NUMERAL 0)) x0).
Definition term63 (x0 : real) (x1 : real) := imp (~ (exists y0 : nat, real_lt (real_pow x0 y0) x1)).
Definition term323 (x0 : real) (x1 : nat) := real_inv (real_inv (real_pow x0 x1)).
Definition term333 (x0 : real) := (real_lt (real_of_num (NUMERAL 0)) x0) -> (real_lt (real_of_num (NUMERAL 0)) (real_inv x0)) = True.
Definition term115 (x0 : real) := fun y0 : real => ((~ (real_lt x0 y0)) \/ (~ (real_le y0 x0))) /\ ((real_lt x0 y0) \/ (real_le y0 x0)).
Definition term170 (x0 : real) (x1 : real) (x2 : real) := (~ ((real_le x1 x0) /\ (real_lt x0 x2))) \/ (real_lt x1 x2).
Definition term92 (x0 : real) := fun y0 : real => (~ (real_lt x0 y0)) = (real_le y0 x0).
Definition term305 (x0 : real) (x1 : real) (x2 : nat) := imp (real_lt (real_inv x0) (real_pow (real_inv x1) x2)).
Definition term64 (x0 : real) (x1 : real) := (~ (exists y0 : nat, real_lt (real_pow x0 y0) x1)) -> (forall y0 : real, forall y1 : real, (~ (real_lt y0 y1)) = (real_le y1 y0)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2) -> (forall y0 : real, (real_pow y0 (NUMERAL (BIT1 0))) = y0) -> False.
Definition term202 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (real_lt x0 x1) \/ ((~ (x3 = x1)) \/ (~ (real_lt x2 x3))).
Definition term156 := @eq Prop (forall y0 : real, (forall y1 : real, (~ (real_lt y0 y1)) \/ (~ (real_le y1 y0))) /\ (forall y1 : real, (real_lt y0 y1) \/ (real_le y1 y0))).
Definition term155 := @eq Prop (forall y0 : real, ((fun y1 : real => forall y2 : real, (~ (real_lt y1 y2)) \/ (~ (real_le y2 y1))) y0) /\ ((fun y1 : real => forall y2 : real, (real_lt y1 y2) \/ (real_le y2 y1)) y0)).
Definition term134 (x0 : real) := @eq Prop (forall y0 : real, ((~ (real_lt x0 y0)) \/ (~ (real_le y0 x0))) /\ ((real_lt x0 y0) \/ (real_le y0 x0))).
Definition term133 (x0 : real) := @eq Prop (forall y0 : real, ((fun y1 : real => (~ (real_lt x0 y1)) \/ (~ (real_le y1 x0))) y0) /\ ((fun y1 : real => (real_lt x0 y1) \/ (real_le y1 x0)) y0)).
Definition term231 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := imp (~ ((~ (x0 = x2)) \/ ((~ (x1 = x3)) \/ (real_lt x2 x3)))).
Definition term206 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (real_lt x0 x1) \/ ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (real_lt x2 x3)))).
Definition term23 (x0 : real) := forall y0 : real, (real_lt (real_of_num (NUMERAL (BIT1 0))) x0) -> exists y1 : nat, real_lt y0 (real_pow x0 y1).
Definition term103 (x0 : real) (x1 : nat) (x2 : real) := ~ (real_lt (real_pow x0 x1) x2).
Definition term227 (x0 : real) (x1 : real) (x2 : real) := ~ ((~ (x0 = x2)) \/ (real_lt x1 x2)).
Definition term250 (x0 : real) (x1 : real) (x2 : real) := (real_lt x0 x2) \/ (~ (real_lt x1 x2)).
Definition term128 (x0 : real) (x1 : real) := (~ (real_lt x1 x0)) \/ (~ (real_le x0 x1)).
Definition term330 (x0 : real) := (fun y0 : real => forall y1 : nat, (real_inv (real_pow y0 y1)) = (real_pow (real_inv y0) y1)) x0.
Definition term117 := fun y0 : real => forall y1 : real, ((~ (real_lt y0 y1)) \/ (~ (real_le y1 y0))) /\ ((real_lt y0 y1) \/ (real_le y1 y0)).
Definition term79 := fun y0 : real => forall y1 : real, (real_lt (real_of_num (NUMERAL 0)) y0) -> (real_lt y1 (real_of_num (NUMERAL (BIT1 0)))) -> (~ (real_lt (real_of_num (NUMERAL 0)) y1)) -> (~ (exists y2 : nat, real_lt (real_pow y1 y2) y0)) -> (forall y2 : real, forall y3 : real, (~ (real_lt y2 y3)) = (real_le y3 y2)) -> (forall y2 : real, forall y3 : real, forall y4 : real, ((real_le y2 y3) /\ (real_lt y3 y4)) -> real_lt y2 y4) -> ~ (forall y2 : real, (real_pow y2 (NUMERAL (BIT1 0))) = y2).
Definition term78 := fun y0 : real => forall y1 : real, (real_lt (real_of_num (NUMERAL 0)) y0) -> (real_lt y1 (real_of_num (NUMERAL (BIT1 0)))) -> (~ (real_lt (real_of_num (NUMERAL 0)) y1)) -> (~ (exists y2 : nat, real_lt (real_pow y1 y2) y0)) -> (forall y2 : real, forall y3 : real, (~ (real_lt y2 y3)) = (real_le y3 y2)) -> (forall y2 : real, forall y3 : real, forall y4 : real, ((real_le y2 y3) /\ (real_lt y3 y4)) -> real_lt y2 y4) -> (forall y2 : real, (real_pow y2 (NUMERAL (BIT1 0))) = y2) -> False.
Definition term240 (x0 : real) (x1 : real) := (real_le x1 x0) \/ (real_lt x0 x1).
Definition term192 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (x2 = x0) -> (~ (x3 = x1)) \/ ((real_lt x0 x1) \/ (~ (real_lt x2 x3))).
Definition term114 (x0 : real) (x1 : real) := ((~ (real_lt x1 x0)) \/ (~ (real_le x0 x1))) /\ ((real_lt x1 x0) \/ (real_le x0 x1)).
Definition term328 (x0 : real) := (real_lt (real_of_num (NUMERAL 0)) x0) -> real_lt (real_of_num (NUMERAL 0)) (real_inv x0).
Definition term309 (x0 : real) (x1 : real) := fun y0 : nat => (real_lt (real_inv x1) (real_pow (real_inv x0) y0)) -> real_lt (real_pow x0 y0) x1.
Definition term93 (x0 : real) := forall y0 : real, (~ (real_lt x0 y0)) = (real_le y0 x0).
Definition term311 (x0 : real) (x1 : real) := forall y0 : nat, (real_lt (real_inv x1) (real_pow (real_inv x0) y0)) -> real_lt (real_pow x0 y0) x1.
Definition term203 (x0 : real) (x1 : real) := ~ (x0 = x1).
Definition term205 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (x2 = x0)) \/ ((real_lt x0 x1) \/ ((~ (x3 = x1)) \/ (~ (real_lt x2 x3)))).
Definition term68 (x0 : real) (x1 : real) := (~ (real_lt (real_of_num (NUMERAL 0)) x0)) -> (~ (exists y0 : nat, real_lt (real_pow x0 y0) x1)) -> (forall y0 : real, forall y1 : real, (~ (real_lt y0 y1)) = (real_le y1 y0)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2) -> ~ (forall y0 : real, (real_pow y0 (NUMERAL (BIT1 0))) = y0).
Definition term313 (x0 : real) (x1 : real) := imp (forall y0 : nat, (real_lt (real_inv x1) (real_pow (real_inv x0) y0)) -> real_lt (real_pow x0 y0) x1).
Definition term312 (x0 : real) (x1 : real) := imp (forall y0 : nat, ((fun y1 : nat => real_lt (real_inv x1) (real_pow (real_inv x0) y1)) y0) -> (fun y1 : nat => real_lt (real_pow x0 y1) x1) y0).
Definition term105 (x0 : real) (x1 : real) := fun y0 : nat => ~ (real_lt (real_pow x0 y0) x1).
Definition term65 (x0 : real) (x1 : real) := (~ (exists y0 : nat, real_lt (real_pow x0 y0) x1)) -> (forall y0 : real, forall y1 : real, (~ (real_lt y0 y1)) = (real_le y1 y0)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2) -> ~ (forall y0 : real, (real_pow y0 (NUMERAL (BIT1 0))) = y0).
Definition term91 (x0 : real) (x1 : real) := ~ (real_lt x0 x1).
Definition term33 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, (y0 \/ (y1 \/ y2)) = ((y0 \/ y1) \/ y2)) x0.
Definition term191 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (x3 = x1)) \/ ((real_lt x0 x1) \/ (~ (real_lt x2 x3))).
Definition term207 (x0 : real) (x1 : real) (x2 : real) := (~ (x2 = x0)) \/ (~ (real_lt x1 x2)).
Definition term72 (x0 : real) := imp (real_lt (real_of_num (NUMERAL 0)) x0).
Definition term187 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ((real_lt x2 x3) = (real_lt x0 x1)) -> (real_lt x0 x1) \/ (~ (real_lt x2 x3)).
Definition term217 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (real_lt x0 x1)))) -> ~ (real_lt x2 x3).
Definition term209 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := @eq Prop ((real_lt x0 x1) \/ ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (real_lt x2 x3))))).
Definition term182 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => ((~ (real_le x1 x0)) \/ (~ (real_lt x0 y0))) \/ (real_lt x1 y0)) x2.
Definition term106 (x0 : real) (x1 : real) := forall y0 : nat, ~ (real_lt (real_pow x0 y0) x1).
Definition term44 (x0 : real) (x1 : real) := (real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt x1 (real_of_num (NUMERAL (BIT1 0)))).
Definition term247 (x0 : real) := ~ (real_le (real_pow x0 (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))).
Definition term10 (x0 : real) := real_inv (real_inv x0).
Definition term51 (x0 : real) (x1 : real) := ((real_lt (real_of_num (NUMERAL 0)) x1) -> (real_lt x0 (real_of_num (NUMERAL (BIT1 0)))) -> (~ (real_lt (real_of_num (NUMERAL 0)) x0)) -> (~ (exists y0 : nat, real_lt (real_pow x0 y0) x1)) -> (forall y0 : real, forall y1 : real, (~ (real_lt y0 y1)) = (real_le y1 y0)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2) -> (forall y0 : real, (real_pow y0 (NUMERAL (BIT1 0))) = y0) -> False) -> (real_lt (real_of_num (NUMERAL 0)) x1) -> (real_lt x0 (real_of_num (NUMERAL (BIT1 0)))) -> (~ (real_lt (real_of_num (NUMERAL 0)) x0)) -> (~ (exists y0 : nat, real_lt (real_pow x0 y0) x1)) -> (forall y0 : real, forall y1 : real, (~ (real_lt y0 y1)) = (real_le y1 y0)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2) -> (forall y0 : real, (real_pow y0 (NUMERAL (BIT1 0))) = y0) -> False.
Definition term319 (x0 : real) (x1 : real) := exists y0 : nat, (fun y1 : nat => real_lt (real_pow x0 y1) x1) y0.
Definition term219 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term277 (x0 : real) := forall y0 : real, ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt x0 y0)) -> real_lt (real_inv y0) (real_inv x0).
Definition term143 (x0 : real) := (forall y0 : real, (~ (real_lt x0 y0)) \/ (~ (real_le y0 x0))) /\ (forall y0 : real, (real_lt x0 y0) \/ (real_le y0 x0)).
Definition term195 := (~ ((real_of_num (NUMERAL 0)) = (real_of_num (NUMERAL 0)))) -> (real_of_num (NUMERAL 0)) = (real_of_num (NUMERAL 0)).
Definition term229 (x0 : real) (x1 : real) (x2 : real) := (x0 = x2) /\ (~ (real_lt x1 x2)).
Definition term98 (x0 : nat -> Prop) := ~ (ex x0).
Definition term245 (x0 : real) := real_le (real_pow x0 (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term303 (x0 : real) (x1 : real) (x2 : nat) := real_lt (real_inv x0) (real_pow (real_inv x1) x2).
Definition term137 (x0 : real) := forall y0 : real, (~ (real_lt x0 y0)) \/ (~ (real_le y0 x0)).
Definition term45 (x0 : real) := real_lt x0 (real_of_num (NUMERAL (BIT1 0))).
Definition term173 (x0 : real) (x1 : real) := fun y0 : real => ((~ (real_le x1 x0)) \/ (~ (real_lt x0 y0))) \/ (real_lt x1 y0).
Definition term296 (x0 : real) := forall y0 : real, exists y1 : nat, real_lt y0 (real_pow (real_inv x0) y1).
Definition term28 (x0 : real) := forall y0 : real, exists y1 : nat, real_lt y0 (real_pow x0 y1).
Definition term112 (x0 : real) (x1 : real) := and ((~ (real_lt x1 x0)) \/ (~ (real_le x0 x1))).
Definition term235 (x0 : real) := ((real_of_num (NUMERAL 0)) = (real_of_num (NUMERAL 0))) /\ (((real_pow x0 (NUMERAL (BIT1 0))) = x0) /\ (~ (real_lt (real_of_num (NUMERAL 0)) x0))).
Definition term135 (x0 : real) := fun y0 : real => (fun y1 : real => (~ (real_lt x0 y1)) \/ (~ (real_le y1 x0))) y0.
Definition term289 := real_lt (real_of_num (NUMERAL (BIT1 0))).
Definition term306 (x0 : real) (x1 : real) (x2 : nat) := ((fun y0 : nat => real_lt (real_inv x1) (real_pow (real_inv x0) y0)) x2) -> (fun y0 : nat => real_lt (real_pow x0 y0) x1) x2.
Definition term6 := fun y0 : real => forall y1 : nat, (real_pow (real_inv y0) y1) = (real_inv (real_pow y0 y1)).
Definition term24 (x0 : real) (x1 : real) := (fun y0 : real => (real_lt (real_of_num (NUMERAL (BIT1 0))) x0) -> exists y1 : nat, real_lt y0 (real_pow x0 y1)) x1.
Definition term113 (x0 : real) (x1 : real) := ((~ (real_lt x1 x0)) \/ (~ (real_le x0 x1))) /\ ((~ (~ (real_lt x1 x0))) \/ (real_le x0 x1)).
Definition term175 (x0 : real) := fun y0 : real => forall y1 : real, ((~ (real_le x0 y0)) \/ (~ (real_lt y0 y1))) \/ (real_lt x0 y1).
Definition term149 := fun y0 : real => forall y1 : real, (real_lt y0 y1) \/ (real_le y1 y0).
Definition term94 := fun y0 : real => forall y1 : real, (~ (real_lt y0 y1)) = (real_le y1 y0).
Definition term87 (x0 : real) := fun y0 : real => forall y1 : real, ((real_le x0 y0) /\ (real_lt y0 y1)) -> real_lt x0 y1.
Definition term263 (x0 : real) (x1 : real) (x2 : real) := imp ((real_le x0 x1) /\ (real_lt x1 x2)).
Definition term2 (x0 : real) := fun y0 : nat => (real_pow (real_inv x0) y0) = (real_inv (real_pow x0 y0)).
Definition term121 (x0 : real -> Prop) (x1 : real -> Prop) := forall y0 : real, (x0 y0) /\ (x1 y0).
Definition term42 (x0 : real) := (real_lt (real_of_num (NUMERAL 0)) x0) \/ (~ (real_lt (real_of_num (NUMERAL 0)) x0)).
Definition term39 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 \/ x1) \/ x2.
Definition term99 (x0 : nat -> Prop) := forall y0 : nat, ~ (x0 y0).
Definition term276 (x0 : real) := (fun y0 : real => forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 y1)) -> real_lt (real_inv y1) (real_inv y0)) x0.
Definition term273 (x0 : real) := (fun y0 : real => forall y1 : real, (real_lt (real_of_num (NUMERAL 0)) y0) -> (real_lt y1 (real_of_num (NUMERAL (BIT1 0)))) -> (~ (real_lt (real_of_num (NUMERAL 0)) y1)) -> (~ (exists y2 : nat, real_lt (real_pow y1 y2) y0)) -> (forall y2 : real, forall y3 : real, (~ (real_lt y2 y3)) = (real_le y3 y2)) -> (forall y2 : real, forall y3 : real, forall y4 : real, ((real_le y2 y3) /\ (real_lt y3 y4)) -> real_lt y2 y4) -> (forall y2 : real, (real_pow y2 (NUMERAL (BIT1 0))) = y2) -> False) x0.
Definition term152 (x0 : real) := (fun y0 : real => forall y1 : real, (real_lt y0 y1) \/ (real_le y1 y0)) x0.
Definition term150 (x0 : real) := (fun y0 : real => forall y1 : real, (~ (real_lt y0 y1)) \/ (~ (real_le y1 y0))) x0.
Definition term22 (x0 : real) := (fun y0 : real => forall y1 : real, (real_lt (real_of_num (NUMERAL (BIT1 0))) y0) -> exists y2 : nat, real_lt y1 (real_pow y0 y2)) x0.
Definition term274 (x0 : real) (x1 : real) := (fun y0 : real => (real_lt (real_of_num (NUMERAL 0)) x0) -> (real_lt y0 (real_of_num (NUMERAL (BIT1 0)))) -> (~ (real_lt (real_of_num (NUMERAL 0)) y0)) -> (~ (exists y1 : nat, real_lt (real_pow y0 y1) x0)) -> (forall y1 : real, forall y2 : real, (~ (real_lt y1 y2)) = (real_le y2 y1)) -> (forall y1 : real, forall y2 : real, forall y3 : real, ((real_le y1 y2) /\ (real_lt y2 y3)) -> real_lt y1 y3) -> (forall y1 : real, (real_pow y1 (NUMERAL (BIT1 0))) = y1) -> False) x1.
Definition term169 (x0 : real) (x1 : real) (x2 : real) := or ((~ (real_le x0 x1)) \/ (~ (real_lt x1 x2))).
Definition term110 (x0 : real) (x1 : real) := (~ (~ (real_lt x1 x0))) \/ (real_le x0 x1).
Definition term71 (x0 : real) (x1 : real) := (real_lt x0 (real_of_num (NUMERAL (BIT1 0)))) -> (~ (real_lt (real_of_num (NUMERAL 0)) x0)) -> (~ (exists y0 : nat, real_lt (real_pow x0 y0) x1)) -> (forall y0 : real, forall y1 : real, (~ (real_lt y0 y1)) = (real_le y1 y0)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2) -> ~ (forall y0 : real, (real_pow y0 (NUMERAL (BIT1 0))) = y0).
Definition term70 (x0 : real) (x1 : real) := (real_lt x0 (real_of_num (NUMERAL (BIT1 0)))) -> (~ (real_lt (real_of_num (NUMERAL 0)) x0)) -> (~ (exists y0 : nat, real_lt (real_pow x0 y0) x1)) -> (forall y0 : real, forall y1 : real, (~ (real_lt y0 y1)) = (real_le y1 y0)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2) -> (forall y0 : real, (real_pow y0 (NUMERAL (BIT1 0))) = y0) -> False.
Definition term141 (x0 : real) := forall y0 : real, (fun y1 : real => (real_lt x0 y1) \/ (real_le y1 x0)) y0.
Definition term136 (x0 : real) := forall y0 : real, (fun y1 : real => (~ (real_lt x0 y1)) \/ (~ (real_le y1 x0))) y0.
Definition term53 (x0 : real) (x1 : real) := (((real_lt (real_of_num (NUMERAL 0)) x1) -> (real_lt x0 (real_of_num (NUMERAL (BIT1 0)))) -> (~ (real_lt (real_of_num (NUMERAL 0)) x0)) -> (~ (exists y0 : nat, real_lt (real_pow x0 y0) x1)) -> (forall y0 : real, forall y1 : real, (~ (real_lt y0 y1)) = (real_le y1 y0)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2) -> (forall y0 : real, (real_pow y0 (NUMERAL (BIT1 0))) = y0) -> False) -> (real_lt (real_of_num (NUMERAL 0)) x1) -> (real_lt x0 (real_of_num (NUMERAL (BIT1 0)))) -> (~ (real_lt (real_of_num (NUMERAL 0)) x0)) -> (~ (exists y0 : nat, real_lt (real_pow x0 y0) x1)) -> (forall y0 : real, forall y1 : real, (~ (real_lt y0 y1)) = (real_le y1 y0)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2) -> (forall y0 : real, (real_pow y0 (NUMERAL (BIT1 0))) = y0) -> False) -> ((real_lt (real_of_num (NUMERAL 0)) x1) -> (real_lt x0 (real_of_num (NUMERAL (BIT1 0)))) -> (~ (real_lt (real_of_num (NUMERAL 0)) x0)) -> (~ (exists y0 : nat, real_lt (real_pow x0 y0) x1)) -> (forall y0 : real, forall y1 : real, (~ (real_lt y0 y1)) = (real_le y1 y0)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2) -> (forall y0 : real, (real_pow y0 (NUMERAL (BIT1 0))) = y0) -> False) -> (real_lt (real_of_num (NUMERAL 0)) x1) -> (real_lt x0 (real_of_num (NUMERAL (BIT1 0)))) -> (~ (real_lt (real_of_num (NUMERAL 0)) x0)) -> (~ (exists y0 : nat, real_lt (real_pow x0 y0) x1)) -> (forall y0 : real, forall y1 : real, (~ (real_lt y0 y1)) = (real_le y1 y0)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2) -> (forall y0 : real, (real_pow y0 (NUMERAL (BIT1 0))) = y0) -> False.
Definition term211 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (x0 = x2)) \/ ((~ (real_lt x0 x1)) \/ ((~ (x1 = x3)) \/ (real_lt x2 x3))).
Definition term126 (x0 : real) := fun y0 : real => (real_lt x0 y0) \/ (real_le y0 x0).
Definition term4 (x0 : real) := forall y0 : nat, (real_pow (real_inv x0) y0) = (real_inv (real_pow x0 y0)).
Definition term154 := fun y0 : real => ((fun y1 : real => forall y2 : real, (~ (real_lt y1 y2)) \/ (~ (real_le y2 y1))) y0) /\ ((fun y1 : real => forall y2 : real, (real_lt y1 y2) \/ (real_le y2 y1)) y0).
Definition term241 (x0 : real) (x1 : real) := @eq Prop ((real_lt x1 x0) \/ (real_le x0 x1)).
Definition term69 (x0 : real) := imp (real_lt x0 (real_of_num (NUMERAL (BIT1 0)))).
Definition term315 (x0 : real) (x1 : real) := exists y0 : nat, (fun y1 : nat => real_lt (real_inv x0) (real_pow (real_inv x1) y1)) y0.
Definition term321 (x0 : real) (x1 : real) := (exists y0 : nat, real_lt (real_inv x1) (real_pow (real_inv x0) y0)) -> exists y0 : nat, real_lt (real_pow x0 y0) x1.
Definition term267 (x0 : real) (x1 : real) := (~ (real_lt (real_pow x0 (NUMERAL (BIT1 0))) x1)) -> real_lt (real_pow x0 (NUMERAL (BIT1 0))) x1.
Definition term184 (x0 : real) (x1 : real) (x2 : real) := (~ (real_le x1 x0)) \/ ((~ (real_lt x0 x2)) \/ (real_lt x1 x2)).
Definition term251 (x0 : real) (x1 : real) := or (~ (real_le x0 x1)).
Definition term96 (x0 : real) (x1 : nat) (x2 : real) := real_lt (real_pow x0 x1) x2.
Definition term34 (x0 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1).
Definition term131 (x0 : real) (x1 : real) := ((fun y0 : real => (~ (real_lt x0 y0)) \/ (~ (real_le y0 x0))) x1) /\ ((fun y0 : real => (real_lt x0 y0) \/ (real_le y0 x0)) x1).
Definition term181 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, ((~ (real_le x0 y0)) \/ (~ (real_lt y0 y1))) \/ (real_lt x0 y1)) x1.
Definition term31 := (forall y0 : real, forall y1 : real, (real_lt (real_of_num (NUMERAL (BIT1 0))) y0) -> exists y2 : nat, real_lt y1 (real_pow y0 y2)) -> forall y0 : real, (real_lt (real_of_num (NUMERAL (BIT1 0))) y0) -> forall y1 : real, exists y2 : nat, real_lt y1 (real_pow y0 y2).
Definition term260 (x0 : real) (x1 : real) := and (~ (~ (real_le x0 x1))).
Definition term225 (x0 : real) (x1 : real) := and (~ (~ (x0 = x1))).
Definition term281 (x0 : real) (x1 : real) := real_lt (real_inv x0) (real_inv x1).
Definition term327 (x0 : real) := (fun y0 : real => (real_lt (real_of_num (NUMERAL 0)) y0) -> real_lt (real_of_num (NUMERAL 0)) (real_inv y0)) x0.
Definition term18 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) -> exists y0 : a0, x1 y0.
Definition term127 (x0 : real) (x1 : real) := (fun y0 : real => (~ (real_lt x0 y0)) \/ (~ (real_le y0 x0))) x1.
Definition term239 (x0 : real) := real_lt (real_of_num (NUMERAL 0)) (real_pow x0 (NUMERAL (BIT1 0))).
Definition term171 (x0 : real) (x1 : real) (x2 : real) := ((~ (real_le x1 x0)) \/ (~ (real_lt x0 x2))) \/ (real_lt x1 x2).
Definition term275 (x0 : real) := real_lt (real_inv (real_of_num (NUMERAL (BIT1 0)))) (real_inv x0).
Definition term186 (x0 : Prop) (x1 : Prop) := (x1 = x0) -> x0 \/ (~ x1).
Definition term167 (x0 : real) (x1 : real) (x2 : real) := (~ (real_le x0 x1)) \/ (~ (real_lt x1 x2)).
Definition term198 (x0 : real) := (~ ((real_pow x0 (NUMERAL (BIT1 0))) = x0)) -> (real_pow x0 (NUMERAL (BIT1 0))) = x0.
Definition term41 (x0 : real) := real_lt (real_of_num (NUMERAL 0)) x0.
Definition term290 (x0 : real) := real_lt (real_of_num (NUMERAL (BIT1 0))) (real_inv x0).
Definition term7 := fun y0 : real => forall y1 : nat, (real_inv (real_pow y0 y1)) = (real_pow (real_inv y0) y1).
Definition term297 (x0 : real) (x1 : real) := (fun y0 : real => exists y1 : nat, real_lt y0 (real_pow (real_inv x0) y1)) (real_inv x1).
Definition term125 (x0 : real) := fun y0 : real => (~ (real_lt x0 y0)) \/ (~ (real_le y0 x0)).
Definition term214 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (x1 = x3)) \/ ((~ (real_lt x0 x1)) \/ (real_lt x2 x3)).
Definition term107 (x0 : real) (x1 : real) := ~ (~ (real_lt x0 x1)).
Definition term100 (x0 : real) (x1 : real) := forall y0 : nat, ~ ((fun y1 : nat => real_lt (real_pow x0 y1) x1) y0).
Definition term237 (x0 : real) := ~ (real_lt (real_of_num (NUMERAL 0)) (real_pow x0 (NUMERAL (BIT1 0)))).
Definition term238 (x0 : real) := (real_lt (real_of_num (NUMERAL 0)) (real_pow x0 (NUMERAL (BIT1 0)))) -> ~ (real_lt (real_of_num (NUMERAL 0)) (real_pow x0 (NUMERAL (BIT1 0)))).
Definition term177 := fun y0 : real => forall y1 : real, forall y2 : real, ((~ (real_le y0 y1)) \/ (~ (real_lt y1 y2))) \/ (real_lt y0 y2).
Definition term89 := fun y0 : real => forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2.
Definition term246 (x0 : real) := (~ (real_le (real_pow x0 (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) -> real_le (real_pow x0 (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term0 (x0 : real) (x1 : nat) := real_pow (real_inv x0) x1.
Definition term104 (x0 : real) (x1 : real) := fun y0 : nat => ~ ((fun y1 : nat => real_lt (real_pow x0 y1) x1) y0).
Definition term56 := forall y0 : real, (real_pow y0 (NUMERAL (BIT1 0))) = y0.
Definition term185 (x0 : real) (x1 : real) := ~ (real_le x0 x1).
Definition term320 (x0 : real) (x1 : real) := (exists y0 : nat, (fun y1 : nat => real_lt (real_inv x1) (real_pow (real_inv x0) y1)) y0) -> exists y0 : nat, (fun y1 : nat => real_lt (real_pow x0 y1) x1) y0.
Definition term145 := forall y0 : real, (forall y1 : real, (~ (real_lt y0 y1)) \/ (~ (real_le y1 y0))) /\ (forall y1 : real, (real_lt y0 y1) \/ (real_le y1 y0)).
Definition term334 (x0 : real) := and (real_lt (real_of_num (NUMERAL 0)) (real_inv x0)).
Definition term16 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, (x0 y0) -> x1 y0) -> (exists y0 : a0, x0 y0) -> exists y0 : a0, x1 y0.
Definition term221 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ~ ((~ (x0 = x2)) \/ ((~ (x1 = x3)) \/ (real_lt x2 x3))).
Definition term268 (x0 : real) (x1 : real) := ~ (real_lt (real_pow x0 (NUMERAL (BIT1 0))) x1).
Definition term257 (x0 : real) (x1 : real) (x2 : real) := ~ ((~ (real_le x0 x1)) \/ (~ (real_lt x1 x2))).
Definition term284 := real_of_num (NUMERAL (BIT1 0)).
Definition term86 (x0 : real) (x1 : real) := forall y0 : real, ((real_le x1 x0) /\ (real_lt x0 y0)) -> real_lt x1 y0.
Definition term30 := forall y0 : real, (real_lt (real_of_num (NUMERAL (BIT1 0))) y0) -> forall y1 : real, exists y2 : nat, real_lt y1 (real_pow y0 y2).
Definition term232 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := imp ((x0 = x2) /\ ((x1 = x3) /\ (~ (real_lt x2 x3)))).
Definition term208 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := @eq Prop ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ ((real_lt x0 x1) \/ (~ (real_lt x2 x3))))).
Definition term287 := real_inv (real_of_num (NUMERAL (BIT1 0))).
Definition term20 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((forall y0 : a0, (x0 y0) -> x1 y0) -> (exists y0 : a0, x0 y0) -> exists y0 : a0, x1 y0) -> (forall y0 : a0, (x0 y0) -> x1 y0) -> (exists y0 : a0, x0 y0) -> exists y0 : a0, x1 y0.
Definition term172 (x0 : real) (x1 : real) (x2 : real) := (real_le x0 x1) /\ (real_lt x1 x2).
Definition term163 := forall y0 : real, (fun y1 : real => forall y2 : real, (real_lt y1 y2) \/ (real_le y2 y1)) y0.
Definition term158 := forall y0 : real, (fun y1 : real => forall y2 : real, (~ (real_lt y1 y2)) \/ (~ (real_le y2 y1))) y0.
Definition term111 (x0 : real) (x1 : real) := (real_lt x1 x0) \/ (real_le x0 x1).
Definition term40 (x0 : real) := (fun y0 : Prop => y0 \/ (~ y0)) (real_lt (real_of_num (NUMERAL 0)) x0).
Definition term226 (x0 : real) (x1 : real) := and (x0 = x1).
Definition term1 (x0 : real) (x1 : nat) := real_inv (real_pow x0 x1).
Definition term153 (x0 : real) := ((fun y0 : real => forall y1 : real, (~ (real_lt y0 y1)) \/ (~ (real_le y1 y0))) x0) /\ ((fun y0 : real => forall y1 : real, (real_lt y0 y1) \/ (real_le y1 y0)) x0).
Definition term59 := (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2) -> ~ (forall y0 : real, (real_pow y0 (NUMERAL (BIT1 0))) = y0).
Definition term261 (x0 : real) (x1 : real) := and (real_le x0 x1).
Definition term190 (x0 : Prop) (x1 : Prop) := (~ x0) \/ x1.
Definition term132 (x0 : real) := fun y0 : real => ((fun y1 : real => (~ (real_lt x0 y1)) \/ (~ (real_le y1 x0))) y0) /\ ((fun y1 : real => (real_lt x0 y1) \/ (real_le y1 x0)) y0).
Definition term140 (x0 : real) := fun y0 : real => (fun y1 : real => (real_lt x0 y1) \/ (real_le y1 x0)) y0.
Definition term35 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1)) x1.
Definition term329 (x0 : real) := real_lt (real_of_num (NUMERAL 0)) (real_inv x0).
Definition term189 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (x3 = x1) -> (real_lt x0 x1) \/ (~ (real_lt x2 x3)).
Definition term256 (x0 : real) (x1 : real) (x2 : real) := (~ ((~ (real_le x1 x0)) \/ (~ (real_lt x0 x2)))) -> real_lt x1 x2.
Definition term122 (x0 : real -> Prop) (x1 : real -> Prop) := (forall y0 : real, x0 y0) /\ (forall y0 : real, x1 y0).
Definition term5 (x0 : real) := forall y0 : nat, (real_inv (real_pow x0 y0)) = (real_pow (real_inv x0) y0).
Definition term108 (x0 : real) (x1 : real) := or (~ (~ (real_lt x0 x1))).
Definition term234 (x0 : real) := ((real_pow x0 (NUMERAL (BIT1 0))) = x0) /\ (~ (real_lt (real_of_num (NUMERAL 0)) x0)).
Definition term102 (x0 : real) (x1 : real) (x2 : nat) := ~ ((fun y0 : nat => real_lt (real_pow x0 y0) x1) x2).
Definition term218 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (x0 = x2)) \/ ((~ (x1 = x3)) \/ (real_lt x2 x3)).
Definition term119 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term215 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (real_lt x0 x1)) \/ (real_lt x2 x3).
Definition term286 (x0 : real) := (real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt x0 (real_of_num (NUMERAL (BIT1 0)))).
Definition term17 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) -> x1 y0.
Definition term67 (x0 : real) (x1 : real) := (~ (real_lt (real_of_num (NUMERAL 0)) x0)) -> (~ (exists y0 : nat, real_lt (real_pow x0 y0) x1)) -> (forall y0 : real, forall y1 : real, (~ (real_lt y0 y1)) = (real_le y1 y0)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2) -> (forall y0 : real, (real_pow y0 (NUMERAL (BIT1 0))) = y0) -> False.
Definition term37 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0)) x2.
Definition term304 (x0 : real) (x1 : real) (x2 : nat) := imp ((fun y0 : nat => real_lt (real_inv x0) (real_pow (real_inv x1) y0)) x2).
Definition term252 (x0 : real) (x1 : real) (x2 : real) := (~ (real_le x0 x1)) \/ ((real_lt x0 x2) \/ (~ (real_lt x1 x2))).
Definition term326 (x0 : real) (x1 : nat) (x2 : real) := real_lt (real_inv (real_inv (real_pow x0 x1))) (real_inv (real_inv x2)).
Definition term188 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (real_lt x0 x1) \/ (~ (real_lt x2 x3)).
Definition term179 (x0 : real) (x1 : real) (x2 : nat) := (fun y0 : nat => ~ (real_lt (real_pow x0 y0) x1)) x2.
Definition term183 (x0 : real) := (fun y0 : real => (real_pow y0 (NUMERAL (BIT1 0))) = y0) x0.
Definition term224 (x0 : real) (x1 : real) := ~ (~ (x0 = x1)).
Definition term292 (x0 : real) := imp (real_lt (real_of_num (NUMERAL (BIT1 0))) (real_inv x0)).
Definition term75 (x0 : real) := fun y0 : real => (real_lt (real_of_num (NUMERAL 0)) x0) -> (real_lt y0 (real_of_num (NUMERAL (BIT1 0)))) -> (~ (real_lt (real_of_num (NUMERAL 0)) y0)) -> (~ (exists y1 : nat, real_lt (real_pow y0 y1) x0)) -> (forall y1 : real, forall y2 : real, (~ (real_lt y1 y2)) = (real_le y2 y1)) -> (forall y1 : real, forall y2 : real, forall y3 : real, ((real_le y1 y2) /\ (real_lt y2 y3)) -> real_lt y1 y3) -> ~ (forall y1 : real, (real_pow y1 (NUMERAL (BIT1 0))) = y1).
Definition term74 (x0 : real) := fun y0 : real => (real_lt (real_of_num (NUMERAL 0)) x0) -> (real_lt y0 (real_of_num (NUMERAL (BIT1 0)))) -> (~ (real_lt (real_of_num (NUMERAL 0)) y0)) -> (~ (exists y1 : nat, real_lt (real_pow y0 y1) x0)) -> (forall y1 : real, forall y2 : real, (~ (real_lt y1 y2)) = (real_le y2 y1)) -> (forall y1 : real, forall y2 : real, forall y3 : real, ((real_le y1 y2) /\ (real_lt y2 y3)) -> real_lt y1 y3) -> (forall y1 : real, (real_pow y1 (NUMERAL (BIT1 0))) = y1) -> False.
Definition term332 (x0 : real) (x1 : nat) (x2 : real) := ((real_lt (real_of_num (NUMERAL 0)) (real_inv x2)) /\ (real_lt (real_inv x2) (real_inv (real_pow x0 x1)))) -> (real_lt (real_inv (real_inv (real_pow x0 x1))) (real_inv (real_inv x2))) = True.
Definition term129 (x0 : real) (x1 : real) := and ((fun y0 : real => (~ (real_lt x0 y0)) \/ (~ (real_le y0 x0))) x1).
Definition term204 (x0 : real) (x1 : real) := or (~ (x0 = x1)).
Definition term324 (x0 : real) (x1 : nat) := real_lt (real_pow x0 x1).
Definition term166 (x0 : real) (x1 : real) (x2 : real) := ~ ((real_le x0 x1) /\ (real_lt x1 x2)).
Definition term266 (x0 : real) (x1 : real) := real_lt (real_pow x0 (NUMERAL (BIT1 0))) x1.
Definition term84 (x0 : real) (x1 : real) (x2 : real) := ((real_le x1 x0) /\ (real_lt x0 x2)) -> real_lt x1 x2.
Definition term180 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, ((~ (real_le y0 y1)) \/ (~ (real_lt y1 y2))) \/ (real_lt y0 y2)) x0.
Definition term193 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ ((real_lt x0 x1) \/ (~ (real_lt x2 x3)))).
Definition term322 (x0 : real) (x1 : real) := (forall y0 : nat, (real_lt (real_inv x1) (real_pow (real_inv x0) y0)) -> real_lt (real_pow x0 y0) x1) -> (exists y0 : nat, real_lt (real_inv x1) (real_pow (real_inv x0) y0)) -> exists y0 : nat, real_lt (real_pow x0 y0) x1.
Definition term300 (x0 : real) (x1 : real) := (forall y0 : nat, ((fun y1 : nat => real_lt (real_inv x1) (real_pow (real_inv x0) y1)) y0) -> (fun y1 : nat => real_lt (real_pow x0 y1) x1) y0) -> (exists y0 : nat, (fun y1 : nat => real_lt (real_inv x1) (real_pow (real_inv x0) y1)) y0) -> exists y0 : nat, (fun y1 : nat => real_lt (real_pow x0 y1) x1) y0.
Definition term299 (x0 : nat -> Prop) (x1 : nat -> Prop) := (forall y0 : nat, (x0 y0) -> x1 y0) -> (exists y0 : nat, x0 y0) -> exists y0 : nat, x1 y0.
Definition term288 := real_lt (real_inv (real_of_num (NUMERAL (BIT1 0)))).
Definition term200 (x0 : real) := (real_lt (real_of_num (NUMERAL 0)) x0) -> ~ (real_lt (real_of_num (NUMERAL 0)) x0).
Definition term146 := forall y0 : real, ((fun y1 : real => forall y2 : real, (~ (real_lt y1 y2)) \/ (~ (real_le y2 y1))) y0) /\ ((fun y1 : real => forall y2 : real, (real_lt y1 y2) \/ (real_le y2 y1)) y0).
Definition term123 (x0 : real) := forall y0 : real, ((fun y1 : real => (~ (real_lt x0 y1)) \/ (~ (real_le y1 x0))) y0) /\ ((fun y1 : real => (real_lt x0 y1) \/ (real_le y1 x0)) y0).
Definition term26 (x0 : real) := real_lt (real_of_num (NUMERAL (BIT1 0))) x0.
Definition term243 (x0 : real) (x1 : real) := (~ (real_lt x1 x0)) -> real_le x0 x1.
Definition term294 (x0 : real) (x1 : real) := (real_lt (real_of_num (NUMERAL (BIT1 0))) (real_inv x0)) -> exists y0 : nat, real_lt (real_pow x0 y0) x1.
Definition term293 (x0 : real) (x1 : real) := (real_lt (real_inv (real_of_num (NUMERAL (BIT1 0)))) (real_inv x0)) -> exists y0 : nat, real_lt (real_pow x0 y0) x1.
Definition term271 := NUMERAL (BIT1 0).
Definition term130 (x0 : real) (x1 : real) := (fun y0 : real => (real_lt x0 y0) \/ (real_le y0 x0)) x1.
Definition term201 (x0 : Prop) := x0 -> ~ x0.
Definition term148 := fun y0 : real => forall y1 : real, (~ (real_lt y0 y1)) \/ (~ (real_le y1 y0)).
Definition term196 := ~ ((real_of_num (NUMERAL 0)) = (real_of_num (NUMERAL 0))).
Definition term308 (x0 : real) (x1 : real) := fun y0 : nat => ((fun y1 : nat => real_lt (real_inv x1) (real_pow (real_inv x0) y1)) y0) -> (fun y1 : nat => real_lt (real_pow x0 y1) x1) y0.
Definition term282 (x0 : real) (x1 : real) := ((real_lt (real_of_num (NUMERAL 0)) x1) /\ (real_lt x1 x0)) -> (real_lt (real_inv x0) (real_inv x1)) = True.
Definition term19 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((forall y0 : a0, (x0 y0) -> x1 y0) -> (exists y0 : a0, x0 y0) -> exists y0 : a0, x1 y0) -> (exists y0 : a0, x0 y0) -> exists y0 : a0, x1 y0.
Definition term174 (x0 : real) (x1 : real) := forall y0 : real, ((~ (real_le x1 x0)) \/ (~ (real_lt x0 y0))) \/ (real_lt x1 y0).
Definition term27 (x0 : real) (x1 : real) := exists y0 : nat, real_lt x0 (real_pow x1 y0).
