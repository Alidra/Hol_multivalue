Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term207 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) := fun y0 : nat => (fun y1 : nat => ((Peano.lt y1 (@List.length a0 x0)) /\ (~ (x1 (@EL a0 y1 x0)))) /\ (forall y2 : a0, (forall y3 : nat, (~ (Peano.lt y3 (@List.length a0 x0))) \/ (~ (y2 = (@EL a0 y3 x0)))) \/ (x1 y2))) y0.
Definition term267 (a0 : Type') (x0 : nat) (x1 : list a0) := ~ ((@EL a0 x0 x1) = (@EL a0 x0 x1)).
Definition term249 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => ~ (x0 y0)) x1.
Definition term256 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) (x2 : list a0) := @eq Prop ((~ (Peano.lt x1 (@List.length a0 x2))) \/ (x0 (@EL a0 x1 x2))).
Definition term52 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) := ~ ((forall y0 : nat, (Peano.lt y0 (@List.length a0 x0)) -> x1 (@EL a0 y0 x0)) = (forall y0 : a0, (exists y1 : nat, (Peano.lt y1 (@List.length a0 x0)) /\ (y0 = (@EL a0 y1 x0))) -> x1 y0)).
Definition term123 (a0 : Type') (x0 : a0) (x1 : nat) (x2 : list a0) := and ((Peano.lt x1 (@List.length a0 x2)) /\ (x0 = (@EL a0 x1 x2))).
Definition term65 (a0 : Type') (x0 : a0 -> Prop) (x1 : list a0) := fun y0 : nat => (Peano.lt y0 (@List.length a0 x1)) /\ (~ (x0 (@EL a0 y0 x1))).
Definition term58 (x0 : nat -> Prop) := ~ (all x0).
Definition term265 := (~ False) -> False.
Definition term195 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) := exists y0 : a0, (exists y1 : nat, (forall y2 : nat, (~ (Peano.lt y2 (@List.length a0 x0))) \/ (x1 (@EL a0 y2 x0))) /\ (((Peano.lt y1 (@List.length a0 x0)) /\ (y0 = (@EL a0 y1 x0))) /\ (~ (x1 y0)))) \/ (exists y1 : nat, ((Peano.lt y1 (@List.length a0 x0)) /\ (~ (x1 (@EL a0 y1 x0)))) /\ (forall y2 : a0, (forall y3 : nat, (~ (Peano.lt y3 (@List.length a0 x0))) \/ (~ (y2 = (@EL a0 y3 x0)))) \/ (x1 y2))).
Definition term176 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) := fun y0 : nat => ((Peano.lt y0 (@List.length a0 x0)) /\ (~ (x1 (@EL a0 y0 x0)))) /\ (forall y1 : a0, (forall y2 : nat, (~ (Peano.lt y2 (@List.length a0 x0))) \/ (~ (y1 = (@EL a0 y2 x0)))) \/ (x1 y1)).
Definition term171 (a0 : Type') (x0 : a0 -> Prop) (x1 : list a0) (x2 : nat) := and ((fun y0 : nat => (Peano.lt y0 (@List.length a0 x1)) /\ (~ (x0 (@EL a0 y0 x1)))) x2).
Definition term122 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : nat) := and ((fun y0 : nat => (Peano.lt y0 (@List.length a0 x1)) /\ (x0 = (@EL a0 y0 x1))) x2).
Definition term115 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0) := (exists y0 : nat, (fun y1 : nat => (Peano.lt y1 (@List.length a0 x0)) /\ (x2 = (@EL a0 y1 x0))) y0) /\ (~ (x1 x2)).
Definition term69 (a0 : Type') (x0 : a0) (x1 : nat) (x2 : list a0) := ~ ((Peano.lt x1 (@List.length a0 x2)) /\ (x0 = (@EL a0 x1 x2))).
Definition term172 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) (x2 : list a0) := and ((Peano.lt x1 (@List.length a0 x2)) /\ (~ (x0 (@EL a0 x1 x2)))).
Definition term18 (a0 : Type') (x0 : list a0) (x1 : a0) := (fun y0 : a0 => (@List.In a0 y0 x0) = (exists y1 : nat, (Peano.lt y1 (@List.length a0 x0)) /\ (y0 = (@EL a0 y1 x0)))) x1.
Definition term46 (x0 : Prop) := ~ (~ x0).
Definition term225 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0) := forall y0 : nat, ((fun y1 : nat => (~ (Peano.lt y1 (@List.length a0 x0))) \/ (~ (x2 = (@EL a0 y1 x0)))) y0) \/ (x1 x2).
Definition term287 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) (x2 : list a0) := ((Peano.lt x1 (@List.length a0 x2)) /\ ((@EL a0 x1 x2) = (@EL a0 x1 x2))) -> x0 (@EL a0 x1 x2).
Definition term102 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) := (exists y0 : nat, (Peano.lt y0 (@List.length a0 x0)) /\ (~ (x1 (@EL a0 y0 x0)))) /\ (forall y0 : a0, (forall y1 : nat, (~ (Peano.lt y1 (@List.length a0 x0))) \/ (~ (y0 = (@EL a0 y1 x0)))) \/ (x1 y0)).
Definition term243 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0) (x3 : nat) := (fun y0 : nat => ((~ (Peano.lt y0 (@List.length a0 x0))) \/ (~ (x2 = (@EL a0 y0 x0)))) \/ (x1 x2)) x3.
Definition term262 (a0 : Type') (x0 : nat) (x1 : list a0) := imp (Peano.lt x0 (@List.length a0 x1)).
Definition term229 (a0 : Type') (x0 : a0) (x1 : list a0) := or (forall y0 : nat, (fun y1 : nat => (~ (Peano.lt y1 (@List.length a0 x1))) \/ (~ (x0 = (@EL a0 y1 x1)))) y0).
Definition term190 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0) := or (exists y0 : nat, (forall y1 : nat, (~ (Peano.lt y1 (@List.length a0 x0))) \/ (x1 (@EL a0 y1 x0))) /\ (((Peano.lt y0 (@List.length a0 x0)) /\ (x2 = (@EL a0 y0 x0))) /\ (~ (x1 x2)))).
Definition term160 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) := fun y0 : a0 => exists y1 : nat, (forall y2 : nat, (~ (Peano.lt y2 (@List.length a0 x0))) \/ (x1 (@EL a0 y2 x0))) /\ (((Peano.lt y1 (@List.length a0 x0)) /\ (y0 = (@EL a0 y1 x0))) /\ (~ (x1 y0))).
Definition term196 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term192 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0 -> Prop) := (exists y0 : nat, (forall y1 : nat, (~ (Peano.lt y1 (@List.length a0 x1))) \/ (x2 (@EL a0 y1 x1))) /\ (((Peano.lt y0 (@List.length a0 x1)) /\ (x0 = (@EL a0 y0 x1))) /\ (~ (x2 x0)))) \/ (exists y0 : nat, ((Peano.lt y0 (@List.length a0 x1)) /\ (~ (x2 (@EL a0 y0 x1)))) /\ (forall y1 : a0, (forall y2 : nat, (~ (Peano.lt y2 (@List.length a0 x1))) \/ (~ (y1 = (@EL a0 y2 x1)))) \/ (x2 y1))).
Definition term144 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) := fun y0 : a0 => (forall y1 : nat, (~ (Peano.lt y1 (@List.length a0 x0))) \/ (x1 (@EL a0 y1 x0))) /\ (exists y1 : nat, ((Peano.lt y1 (@List.length a0 x0)) /\ (y0 = (@EL a0 y1 x0))) /\ (~ (x1 y0))).
Definition term53 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) (x2 : list a0) := ~ ((Peano.lt x1 (@List.length a0 x2)) -> x0 (@EL a0 x1 x2)).
Definition term80 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (x0 x1).
Definition term281 (a0 : Type') (x0 : nat) (x1 : list a0) := and (Peano.lt x0 (@List.length a0 x1)).
Definition term88 (a0 : Type') (x0 : a0 -> Prop) := ~ (all x0).
Definition term3 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0).
Definition term133 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 /\ (x1 y0).
Definition term39 (x0 : Prop) := (~ x0) -> False.
Definition term36 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : list a0, (forall y2 : nat, (Peano.lt y2 (@List.length a0 y1)) -> y0 (@EL a0 y2 y1)) = (forall y2 : a0, (exists y3 : nat, (Peano.lt y3 (@List.length a0 y1)) /\ (y2 = (@EL a0 y3 y1))) -> y0 y2).
Definition term13 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : list a0, (@List.Forall a0 y0 y1) = (forall y2 : a0, (@List.In a0 y2 y1) -> y0 y2).
Definition term179 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) \/ x1.
Definition term28 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) := forall y0 : a0, (exists y1 : nat, (Peano.lt y1 (@List.length a0 x0)) /\ (y0 = (@EL a0 y1 x0))) -> x1 y0.
Definition term252 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @eq Prop (~ (x0 x1)).
Definition term260 (a0 : Type') (x0 : nat) (x1 : list a0) := ~ (~ (Peano.lt x0 (@List.length a0 x1))).
Definition term186 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) := or (exists y0 : a0, (fun y1 : a0 => exists y2 : nat, (forall y3 : nat, (~ (Peano.lt y3 (@List.length a0 x0))) \/ (x1 (@EL a0 y3 x0))) /\ (((Peano.lt y2 (@List.length a0 x0)) /\ (y1 = (@EL a0 y2 x0))) /\ (~ (x1 y1)))) y0).
Definition term211 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0) (x3 : nat) := or ((fun y0 : nat => (forall y1 : nat, (~ (Peano.lt y1 (@List.length a0 x0))) \/ (x1 (@EL a0 y1 x0))) /\ (((Peano.lt y0 (@List.length a0 x0)) /\ (x2 = (@EL a0 y0 x0))) /\ (~ (x1 x2)))) x3).
Definition term228 (a0 : Type') (x0 : a0) (x1 : list a0) := forall y0 : nat, (fun y1 : nat => (~ (Peano.lt y1 (@List.length a0 x1))) \/ (~ (x0 = (@EL a0 y1 x1)))) y0.
Definition term255 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) (x2 : list a0) := (x0 (@EL a0 x1 x2)) \/ (~ (Peano.lt x1 (@List.length a0 x2))).
Definition term159 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0) := exists y0 : nat, (forall y1 : nat, (~ (Peano.lt y1 (@List.length a0 x0))) \/ (x1 (@EL a0 y1 x0))) /\ (((Peano.lt y0 (@List.length a0 x0)) /\ (x2 = (@EL a0 y0 x0))) /\ (~ (x1 x2))).
Definition term164 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) := exists y0 : nat, ((fun y1 : nat => (Peano.lt y1 (@List.length a0 x0)) /\ (~ (x1 (@EL a0 y1 x0)))) y0) /\ (forall y1 : a0, (forall y2 : nat, (~ (Peano.lt y2 (@List.length a0 x0))) \/ (~ (y1 = (@EL a0 y2 x0)))) \/ (x1 y1)).
Definition term258 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term121 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0) := @eq Prop ((exists y0 : nat, (Peano.lt y0 (@List.length a0 x0)) /\ (x2 = (@EL a0 y0 x0))) /\ (~ (x1 x2))).
Definition term120 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0) := @eq Prop ((exists y0 : nat, (fun y1 : nat => (Peano.lt y1 (@List.length a0 x0)) /\ (x2 = (@EL a0 y1 x0))) y0) /\ (~ (x1 x2))).
Definition term275 (a0 : Type') (x0 : nat) (x1 : list a0) (x2 : a0 -> Prop) (x3 : a0) := (~ ((~ (Peano.lt x0 (@List.length a0 x1))) \/ (~ (x3 = (@EL a0 x0 x1))))) -> x2 x3.
Definition term238 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0) := forall y0 : nat, ((~ (Peano.lt y0 (@List.length a0 x0))) \/ (~ (x2 = (@EL a0 y0 x0)))) \/ (x1 x2).
Definition term60 (a0 : Type') (x0 : a0 -> Prop) (x1 : list a0) := ~ (forall y0 : nat, (Peano.lt y0 (@List.length a0 x1)) -> x0 (@EL a0 y0 x1)).
Definition term132 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 /\ (exists y0 : a0, x1 y0).
Definition term7 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) := forall y0 : a0, (@List.In a0 y0 x0) -> x1 y0.
Definition term142 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0) := (forall y0 : nat, (~ (Peano.lt y0 (@List.length a0 x0))) \/ (x1 (@EL a0 y0 x0))) /\ (exists y0 : nat, ((Peano.lt y0 (@List.length a0 x0)) /\ (x2 = (@EL a0 y0 x0))) /\ (~ (x1 x2))).
Definition term283 (a0 : Type') (x0 : a0) (x1 : nat) (x2 : list a0) := imp (~ ((~ (Peano.lt x1 (@List.length a0 x2))) \/ (~ (x0 = (@EL a0 x1 x2))))).
Definition term41 (a0 : Type') := ~ (forall y0 : a0 -> Prop, forall y1 : list a0, (forall y2 : nat, (Peano.lt y2 (@List.length a0 y1)) -> y0 (@EL a0 y2 y1)) = (forall y2 : a0, (exists y3 : nat, (Peano.lt y3 (@List.length a0 y1)) /\ (y2 = (@EL a0 y3 y1))) -> y0 y2)).
Definition term268 (a0 : Type') (x0 : nat) (x1 : list a0) (x2 : a0 -> Prop) (x3 : a0) := (~ (x3 = (@EL a0 x0 x1))) \/ (x2 x3).
Definition term254 (x0 : Prop) := (~ x0) -> x0.
Definition term269 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : nat) (x3 : list a0) := (x0 x1) \/ (~ (x1 = (@EL a0 x2 x3))).
Definition term217 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0 -> Prop) := exists y0 : nat, ((forall y1 : nat, (~ (Peano.lt y1 (@List.length a0 x1))) \/ (x2 (@EL a0 y1 x1))) /\ (((Peano.lt y0 (@List.length a0 x1)) /\ (x0 = (@EL a0 y0 x1))) /\ (~ (x2 x0)))) \/ (((Peano.lt y0 (@List.length a0 x1)) /\ (~ (x2 (@EL a0 y0 x1)))) /\ (forall y1 : a0, (forall y2 : nat, (~ (Peano.lt y2 (@List.length a0 x1))) \/ (~ (y1 = (@EL a0 y2 x1)))) \/ (x2 y1))).
Definition term34 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : list a0, (forall y1 : nat, (Peano.lt y1 (@List.length a0 y0)) -> x0 (@EL a0 y1 y0)) = (forall y1 : a0, (exists y2 : nat, (Peano.lt y2 (@List.length a0 y0)) /\ (y1 = (@EL a0 y2 y0))) -> x0 y1).
Definition term277 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term271 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : nat) (x3 : list a0) := (~ (Peano.lt x2 (@List.length a0 x3))) \/ ((x0 x1) \/ (~ (x1 = (@EL a0 x2 x3)))).
Definition term109 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) := ((forall y0 : nat, (Peano.lt y0 (@List.length a0 x0)) -> x1 (@EL a0 y0 x0)) /\ (~ (forall y0 : a0, (exists y1 : nat, (Peano.lt y1 (@List.length a0 x0)) /\ (y0 = (@EL a0 y1 x0))) -> x1 y0))) \/ ((~ (forall y0 : nat, (Peano.lt y0 (@List.length a0 x0)) -> x1 (@EL a0 y0 x0))) /\ (forall y0 : a0, (exists y1 : nat, (Peano.lt y1 (@List.length a0 x0)) /\ (y0 = (@EL a0 y1 x0))) -> x1 y0)).
Definition term168 (a0 : Type') (x0 : a0 -> Prop) (x1 : list a0) := and (exists y0 : nat, (fun y1 : nat => (Peano.lt y1 (@List.length a0 x1)) /\ (~ (x0 (@EL a0 y1 x1)))) y0).
Definition term119 (a0 : Type') (x0 : a0) (x1 : list a0) := and (exists y0 : nat, (fun y1 : nat => (Peano.lt y1 (@List.length a0 x1)) /\ (x0 = (@EL a0 y1 x1))) y0).
Definition term233 (a0 : Type') (x0 : a0) (x1 : nat) (x2 : list a0) := or ((~ (Peano.lt x1 (@List.length a0 x2))) \/ (~ (x0 = (@EL a0 x1 x2)))).
Definition term23 (a0 : Type') (x0 : a0) (x1 : list a0) := imp (exists y0 : nat, (Peano.lt y0 (@List.length a0 x1)) /\ (x0 = (@EL a0 y0 x1))).
Definition term29 (a0 : Type') (x0 : a0 -> Prop) (x1 : list a0) := @eq Prop (forall y0 : nat, (Peano.lt y0 (@List.length a0 x1)) -> x0 (@EL a0 y0 x1)).
Definition term150 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0) (x3 : nat) := (fun y0 : nat => ((Peano.lt y0 (@List.length a0 x0)) /\ (x2 = (@EL a0 y0 x0))) /\ (~ (x1 x2))) x3.
Definition term11 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : list a0, (@List.Forall a0 x0 y0) = (forall y1 : a0, (@List.In a0 y1 y0) -> x0 y1).
Definition term128 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0) := exists y0 : nat, ((Peano.lt y0 (@List.length a0 x0)) /\ (x2 = (@EL a0 y0 x0))) /\ (~ (x1 x2)).
Definition term54 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) (x2 : list a0) := (Peano.lt x1 (@List.length a0 x2)) /\ (~ (x0 (@EL a0 x1 x2))).
Definition term67 (a0 : Type') (x0 : a0 -> Prop) (x1 : list a0) := fun y0 : nat => (~ (Peano.lt y0 (@List.length a0 x1))) \/ (x0 (@EL a0 y0 x1)).
Definition term223 (x0 : nat -> Prop) (x1 : Prop) := forall y0 : nat, (x0 y0) \/ x1.
Definition term220 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (forall y0 : a0, x0 y0) \/ x1.
Definition term248 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => ~ (x0 y0).
Definition term92 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0) := (fun y0 : a0 => (exists y1 : nat, (Peano.lt y1 (@List.length a0 x0)) /\ (y0 = (@EL a0 y1 x0))) -> x1 y0) x2.
Definition term50 (a0 : Type') (x0 : a0 -> Prop) (x1 : list a0) := fun y0 : nat => (Peano.lt y0 (@List.length a0 x1)) -> x0 (@EL a0 y0 x1).
Definition term5 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term31 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : list a0 => (forall y1 : nat, (Peano.lt y1 (@List.length a0 y0)) -> x0 (@EL a0 y1 y0)) = (@List.Forall a0 x0 y0).
Definition term8 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : list a0 => (forall y1 : a0, (@List.In a0 y1 y0) -> x0 y1) = (@List.Forall a0 x0 y0).
Definition term21 (a0 : Type') (x0 : a0 -> Prop) (x1 : list a0) := (fun y0 : list a0 => (@List.Forall a0 x0 y0) = (forall y1 : a0, (@List.In a0 y1 y0) -> x0 y1)) x1.
Definition term185 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) := exists y0 : a0, (fun y1 : a0 => exists y2 : nat, (forall y3 : nat, (~ (Peano.lt y3 (@List.length a0 x0))) \/ (x1 (@EL a0 y3 x0))) /\ (((Peano.lt y2 (@List.length a0 x0)) /\ (y1 = (@EL a0 y2 x0))) /\ (~ (x1 y1)))) y0.
Definition term138 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) := exists y0 : a0, (fun y1 : a0 => exists y2 : nat, ((Peano.lt y2 (@List.length a0 x0)) /\ (y1 = (@EL a0 y2 x0))) /\ (~ (x1 y1))) y0.
Definition term94 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) := fun y0 : a0 => ~ ((fun y1 : a0 => (exists y2 : nat, (Peano.lt y2 (@List.length a0 x0)) /\ (y1 = (@EL a0 y2 x0))) -> x1 y1) y0).
Definition term56 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) (x2 : list a0) := x0 (@EL a0 x1 x2).
Definition term147 (x0 : Prop) (x1 : nat -> Prop) := exists y0 : nat, x0 /\ (x1 y0).
Definition term96 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) := exists y0 : a0, (exists y1 : nat, (Peano.lt y1 (@List.length a0 x0)) /\ (y0 = (@EL a0 y1 x0))) /\ (~ (x1 y0)).
Definition term206 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : nat) := (fun y0 : nat => ((Peano.lt y0 (@List.length a0 x0)) /\ (~ (x1 (@EL a0 y0 x0)))) /\ (forall y1 : a0, (forall y2 : nat, (~ (Peano.lt y2 (@List.length a0 x0))) \/ (~ (y1 = (@EL a0 y2 x0)))) \/ (x1 y1))) x2.
Definition term124 (a0 : Type') (x0 : list a0) (x1 : nat) (x2 : a0 -> Prop) (x3 : a0) := ((fun y0 : nat => (Peano.lt y0 (@List.length a0 x0)) /\ (x3 = (@EL a0 y0 x0))) x1) /\ (~ (x2 x3)).
Definition term143 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) := fun y0 : a0 => (forall y1 : nat, (~ (Peano.lt y1 (@List.length a0 x0))) \/ (x1 (@EL a0 y1 x0))) /\ ((fun y1 : a0 => exists y2 : nat, ((Peano.lt y2 (@List.length a0 x0)) /\ (y1 = (@EL a0 y2 x0))) /\ (~ (x1 y1))) y0).
Definition term227 (a0 : Type') (x0 : a0) (x1 : list a0) := fun y0 : nat => (fun y1 : nat => (~ (Peano.lt y1 (@List.length a0 x1))) \/ (~ (x0 = (@EL a0 y1 x1)))) y0.
Definition term146 (x0 : Prop) (x1 : nat -> Prop) := x0 /\ (exists y0 : nat, x1 y0).
Definition term75 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : nat) := (fun y0 : nat => (Peano.lt y0 (@List.length a0 x1)) /\ (x0 = (@EL a0 y0 x1))) x2.
Definition term98 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) := forall y0 : a0, (forall y1 : nat, (~ (Peano.lt y1 (@List.length a0 x0))) \/ (~ (y0 = (@EL a0 y1 x0)))) \/ (x1 y0).
Definition term200 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0 -> Prop) := (exists y0 : nat, (fun y1 : nat => (forall y2 : nat, (~ (Peano.lt y2 (@List.length a0 x1))) \/ (x2 (@EL a0 y2 x1))) /\ (((Peano.lt y1 (@List.length a0 x1)) /\ (x0 = (@EL a0 y1 x1))) /\ (~ (x2 x0)))) y0) \/ (exists y0 : nat, (fun y1 : nat => ((Peano.lt y1 (@List.length a0 x1)) /\ (~ (x2 (@EL a0 y1 x1)))) /\ (forall y2 : a0, (forall y3 : nat, (~ (Peano.lt y3 (@List.length a0 x1))) \/ (~ (y2 = (@EL a0 y3 x1)))) \/ (x2 y2))) y0).
Definition term17 (a0 : Type') (x0 : list a0) := forall y0 : a0, (@List.In a0 y0 x0) = (exists y1 : nat, (Peano.lt y1 (@List.length a0 x0)) /\ (y0 = (@EL a0 y1 x0))).
Definition term24 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0) := (@List.In a0 x2 x0) -> x1 x2.
Definition term166 (a0 : Type') (x0 : a0 -> Prop) (x1 : list a0) := fun y0 : nat => (fun y1 : nat => (Peano.lt y1 (@List.length a0 x1)) /\ (~ (x0 (@EL a0 y1 x1)))) y0.
Definition term151 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0) := fun y0 : nat => (fun y1 : nat => ((Peano.lt y1 (@List.length a0 x0)) /\ (x2 = (@EL a0 y1 x0))) /\ (~ (x1 x2))) y0.
Definition term116 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0) := exists y0 : nat, ((fun y1 : nat => (Peano.lt y1 (@List.length a0 x0)) /\ (x2 = (@EL a0 y1 x0))) y0) /\ (~ (x1 x2)).
Definition term108 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) := or ((forall y0 : nat, (~ (Peano.lt y0 (@List.length a0 x0))) \/ (x1 (@EL a0 y0 x0))) /\ (exists y0 : a0, (exists y1 : nat, (Peano.lt y1 (@List.length a0 x0)) /\ (y0 = (@EL a0 y1 x0))) /\ (~ (x1 y0)))).
Definition term101 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) := (~ (forall y0 : nat, (Peano.lt y0 (@List.length a0 x0)) -> x1 (@EL a0 y0 x0))) /\ (forall y0 : a0, (exists y1 : nat, (Peano.lt y1 (@List.length a0 x0)) /\ (y0 = (@EL a0 y1 x0))) -> x1 y0).
Definition term104 (a0 : Type') (x0 : a0 -> Prop) (x1 : list a0) := and (forall y0 : nat, (~ (Peano.lt y0 (@List.length a0 x1))) \/ (x0 (@EL a0 y0 x1))).
Definition term103 (a0 : Type') (x0 : a0 -> Prop) (x1 : list a0) := and (forall y0 : nat, (Peano.lt y0 (@List.length a0 x1)) -> x0 (@EL a0 y0 x1)).
Definition term174 (a0 : Type') (x0 : nat) (x1 : list a0) (x2 : a0 -> Prop) := ((Peano.lt x0 (@List.length a0 x1)) /\ (~ (x2 (@EL a0 x0 x1)))) /\ (forall y0 : a0, (forall y1 : nat, (~ (Peano.lt y1 (@List.length a0 x1))) \/ (~ (y0 = (@EL a0 y1 x1)))) \/ (x2 y0)).
Definition term0 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, (y0 \/ (y1 \/ y2)) = ((y0 \/ y1) \/ y2)) x0.
Definition term42 (a0 : Type') := ((~ (forall y0 : a0 -> Prop, forall y1 : list a0, (forall y2 : nat, (Peano.lt y2 (@List.length a0 y1)) -> y0 (@EL a0 y2 y1)) = (forall y2 : a0, (exists y3 : nat, (Peano.lt y3 (@List.length a0 y1)) /\ (y2 = (@EL a0 y3 y1))) -> y0 y2))) -> False) -> (~ (forall y0 : a0 -> Prop, forall y1 : list a0, (forall y2 : nat, (Peano.lt y2 (@List.length a0 y1)) -> y0 (@EL a0 y2 y1)) = (forall y2 : a0, (exists y3 : nat, (Peano.lt y3 (@List.length a0 y1)) /\ (y2 = (@EL a0 y3 y1))) -> y0 y2))) -> False.
Definition term236 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0) := fun y0 : nat => ((fun y1 : nat => (~ (Peano.lt y1 (@List.length a0 x0))) \/ (~ (x2 = (@EL a0 y1 x0)))) y0) \/ (x1 x2).
Definition term127 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0) := fun y0 : nat => ((Peano.lt y0 (@List.length a0 x0)) /\ (x2 = (@EL a0 y0 x0))) /\ (~ (x1 x2)).
Definition term245 (a0 : Type') (x0 : nat) (x1 : list a0) := ~ (Peano.lt x0 (@List.length a0 x1)).
Definition term276 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term89 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0, ~ (x0 y0).
Definition term285 (a0 : Type') (x0 : nat) (x1 : list a0) (x2 : a0 -> Prop) (x3 : a0) := ((Peano.lt x0 (@List.length a0 x1)) /\ (x3 = (@EL a0 x0 x1))) -> x2 x3.
Definition term16 (a0 : Type') (x0 : list a0) := (fun y0 : list a0 => forall y1 : a0, (@List.In a0 y1 y0) = (exists y2 : nat, (Peano.lt y2 (@List.length a0 y0)) /\ (y1 = (@EL a0 y2 y0)))) x0.
Definition term110 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) := ((forall y0 : nat, (~ (Peano.lt y0 (@List.length a0 x0))) \/ (x1 (@EL a0 y0 x0))) /\ (exists y0 : a0, (exists y1 : nat, (Peano.lt y1 (@List.length a0 x0)) /\ (y0 = (@EL a0 y1 x0))) /\ (~ (x1 y0)))) \/ ((exists y0 : nat, (Peano.lt y0 (@List.length a0 x0)) /\ (~ (x1 (@EL a0 y0 x0)))) /\ (forall y0 : a0, (forall y1 : nat, (~ (Peano.lt y1 (@List.length a0 x0))) \/ (~ (y0 = (@EL a0 y1 x0)))) \/ (x1 y0))).
Definition term261 (a0 : Type') (x0 : nat) (x1 : list a0) := imp (~ (~ (Peano.lt x0 (@List.length a0 x1)))).
Definition term76 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : nat) := ~ ((fun y0 : nat => (Peano.lt y0 (@List.length a0 x1)) /\ (x0 = (@EL a0 y0 x1))) x2).
Definition term63 (a0 : Type') (x0 : a0 -> Prop) (x1 : list a0) (x2 : nat) := ~ ((fun y0 : nat => (Peano.lt y0 (@List.length a0 x1)) -> x0 (@EL a0 y0 x1)) x2).
Definition term158 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0) := fun y0 : nat => (forall y1 : nat, (~ (Peano.lt y1 (@List.length a0 x0))) \/ (x1 (@EL a0 y1 x0))) /\ (((Peano.lt y0 (@List.length a0 x0)) /\ (x2 = (@EL a0 y0 x0))) /\ (~ (x1 x2))).
Definition term112 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) /\ x1.
Definition term222 (x0 : nat -> Prop) (x1 : Prop) := (forall y0 : nat, x0 y0) \/ x1.
Definition term156 (a0 : Type') (x0 : nat) (x1 : list a0) (x2 : a0 -> Prop) (x3 : a0) := (forall y0 : nat, (~ (Peano.lt y0 (@List.length a0 x1))) \/ (x2 (@EL a0 y0 x1))) /\ (((Peano.lt x0 (@List.length a0 x1)) /\ (x3 = (@EL a0 x0 x1))) /\ (~ (x2 x3))).
Definition term71 (x0 : nat -> Prop) := ~ (ex x0).
Definition term253 (a0 : Type') (x0 : nat) (x1 : list a0) := (~ (Peano.lt x0 (@List.length a0 x1))) -> Peano.lt x0 (@List.length a0 x1).
Definition term251 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @eq Prop ((fun y0 : a0 => ~ (x0 y0)) x1).
Definition term201 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0 -> Prop) := exists y0 : nat, ((fun y1 : nat => (forall y2 : nat, (~ (Peano.lt y2 (@List.length a0 x1))) \/ (x2 (@EL a0 y2 x1))) /\ (((Peano.lt y1 (@List.length a0 x1)) /\ (x0 = (@EL a0 y1 x1))) /\ (~ (x2 x0)))) y0) \/ ((fun y1 : nat => ((Peano.lt y1 (@List.length a0 x1)) /\ (~ (x2 (@EL a0 y1 x1)))) /\ (forall y2 : a0, (forall y3 : nat, (~ (Peano.lt y3 (@List.length a0 x1))) \/ (~ (y2 = (@EL a0 y3 x1)))) \/ (x2 y2))) y0).
Definition term183 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0) := (fun y0 : a0 => exists y1 : nat, (forall y2 : nat, (~ (Peano.lt y2 (@List.length a0 x0))) \/ (x1 (@EL a0 y2 x0))) /\ (((Peano.lt y1 (@List.length a0 x0)) /\ (y0 = (@EL a0 y1 x0))) /\ (~ (x1 y0)))) x2.
Definition term66 (a0 : Type') (x0 : a0 -> Prop) (x1 : list a0) := exists y0 : nat, (Peano.lt y0 (@List.length a0 x1)) /\ (~ (x0 (@EL a0 y0 x1))).
Definition term189 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0) := or ((fun y0 : a0 => exists y1 : nat, (forall y2 : nat, (~ (Peano.lt y2 (@List.length a0 x0))) \/ (x1 (@EL a0 y2 x0))) /\ (((Peano.lt y1 (@List.length a0 x0)) /\ (y0 = (@EL a0 y1 x0))) /\ (~ (x1 y0)))) x2).
Definition term270 (a0 : Type') (x0 : nat) (x1 : list a0) := or (~ (Peano.lt x0 (@List.length a0 x1))).
Definition term48 (a0 : Type') (x0 : a0) (x1 : list a0) := fun y0 : nat => (Peano.lt y0 (@List.length a0 x1)) /\ (x0 = (@EL a0 y0 x1)).
Definition term6 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 \/ x1) \/ x2.
Definition term234 (a0 : Type') (x0 : list a0) (x1 : nat) (x2 : a0 -> Prop) (x3 : a0) := ((fun y0 : nat => (~ (Peano.lt y0 (@List.length a0 x0))) \/ (~ (x3 = (@EL a0 y0 x0)))) x1) \/ (x2 x3).
Definition term72 (x0 : nat -> Prop) := forall y0 : nat, ~ (x0 y0).
Definition term272 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : nat) (x3 : list a0) := (x0 x1) \/ ((~ (Peano.lt x2 (@List.length a0 x3))) \/ (~ (x1 = (@EL a0 x2 x3)))).
Definition term180 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) \/ x1.
Definition term20 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : list a0, (@List.Forall a0 y0 y1) = (forall y2 : a0, (@List.In a0 y2 y1) -> y0 y2)) x0.
Definition term78 (a0 : Type') (x0 : a0) (x1 : list a0) := fun y0 : nat => (~ (Peano.lt y0 (@List.length a0 x1))) \/ (~ (x0 = (@EL a0 y0 x1))).
Definition term135 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) := exists y0 : a0, (forall y1 : nat, (~ (Peano.lt y1 (@List.length a0 x0))) \/ (x1 (@EL a0 y1 x0))) /\ ((fun y1 : a0 => exists y2 : nat, ((Peano.lt y2 (@List.length a0 x0)) /\ (y1 = (@EL a0 y2 x0))) /\ (~ (x1 y1))) y0).
Definition term145 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) := exists y0 : a0, (forall y1 : nat, (~ (Peano.lt y1 (@List.length a0 x0))) \/ (x1 (@EL a0 y1 x0))) /\ (exists y1 : nat, ((Peano.lt y1 (@List.length a0 x0)) /\ (y0 = (@EL a0 y1 x0))) /\ (~ (x1 y0))).
Definition term45 (a0 : Type') := ~ (~ (forall y0 : a0 -> Prop, forall y1 : list a0, (forall y2 : nat, (Peano.lt y2 (@List.length a0 y1)) -> y0 (@EL a0 y2 y1)) = (forall y2 : a0, (exists y3 : nat, (Peano.lt y3 (@List.length a0 y1)) /\ (y2 = (@EL a0 y3 y1))) -> y0 y2))).
Definition term68 (a0 : Type') (x0 : a0 -> Prop) (x1 : list a0) := forall y0 : nat, (~ (Peano.lt y0 (@List.length a0 x1))) \/ (x0 (@EL a0 y0 x1)).
Definition term114 (x0 : nat -> Prop) (x1 : Prop) := exists y0 : nat, (x0 y0) /\ x1.
Definition term184 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) := fun y0 : a0 => (fun y1 : a0 => exists y2 : nat, (forall y3 : nat, (~ (Peano.lt y3 (@List.length a0 x0))) \/ (x1 (@EL a0 y3 x0))) /\ (((Peano.lt y2 (@List.length a0 x0)) /\ (y1 = (@EL a0 y2 x0))) /\ (~ (x1 y1)))) y0.
Definition term137 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) := fun y0 : a0 => (fun y1 : a0 => exists y2 : nat, ((Peano.lt y2 (@List.length a0 x0)) /\ (y1 = (@EL a0 y2 x0))) /\ (~ (x1 y1))) y0.
Definition term33 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : list a0, (forall y1 : nat, (Peano.lt y1 (@List.length a0 y0)) -> x0 (@EL a0 y1 y0)) = (@List.Forall a0 x0 y0).
Definition term10 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : list a0, (forall y1 : a0, (@List.In a0 y1 y0) -> x0 y1) = (@List.Forall a0 x0 y0).
Definition term40 (a0 : Type') := (~ (forall y0 : a0 -> Prop, forall y1 : list a0, (forall y2 : nat, (Peano.lt y2 (@List.length a0 y1)) -> y0 (@EL a0 y2 y1)) = (forall y2 : a0, (exists y3 : nat, (Peano.lt y3 (@List.length a0 y1)) /\ (y2 = (@EL a0 y3 y1))) -> y0 y2))) -> False.
Definition term155 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0) (x3 : nat) := (forall y0 : nat, (~ (Peano.lt y0 (@List.length a0 x0))) \/ (x1 (@EL a0 y0 x0))) /\ ((fun y0 : nat => ((Peano.lt y0 (@List.length a0 x0)) /\ (x2 = (@EL a0 y0 x0))) /\ (~ (x1 x2))) x3).
Definition term221 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := forall y0 : a0, (x0 y0) \/ x1.
Definition term79 (a0 : Type') (x0 : a0) (x1 : list a0) := forall y0 : nat, (~ (Peano.lt y0 (@List.length a0 x1))) \/ (~ (x0 = (@EL a0 y0 x1))).
Definition term165 (a0 : Type') (x0 : a0 -> Prop) (x1 : list a0) (x2 : nat) := (fun y0 : nat => (Peano.lt y0 (@List.length a0 x1)) /\ (~ (x0 (@EL a0 y0 x1)))) x2.
Definition term194 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) := fun y0 : a0 => (exists y1 : nat, (forall y2 : nat, (~ (Peano.lt y2 (@List.length a0 x0))) \/ (x1 (@EL a0 y2 x0))) /\ (((Peano.lt y1 (@List.length a0 x0)) /\ (y0 = (@EL a0 y1 x0))) /\ (~ (x1 y0)))) \/ (exists y1 : nat, ((Peano.lt y1 (@List.length a0 x0)) /\ (~ (x1 (@EL a0 y1 x0)))) /\ (forall y2 : a0, (forall y3 : nat, (~ (Peano.lt y3 (@List.length a0 x0))) \/ (~ (y2 = (@EL a0 y3 x0)))) \/ (x1 y2))).
Definition term208 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) := exists y0 : nat, (fun y1 : nat => ((Peano.lt y1 (@List.length a0 x0)) /\ (~ (x1 (@EL a0 y1 x0)))) /\ (forall y2 : a0, (forall y3 : nat, (~ (Peano.lt y3 (@List.length a0 x0))) \/ (~ (y2 = (@EL a0 y3 x0)))) \/ (x1 y2))) y0.
Definition term204 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0) := exists y0 : nat, (fun y1 : nat => (forall y2 : nat, (~ (Peano.lt y2 (@List.length a0 x0))) \/ (x1 (@EL a0 y2 x0))) /\ (((Peano.lt y1 (@List.length a0 x0)) /\ (x2 = (@EL a0 y1 x0))) /\ (~ (x1 x2)))) y0.
Definition term167 (a0 : Type') (x0 : a0 -> Prop) (x1 : list a0) := exists y0 : nat, (fun y1 : nat => (Peano.lt y1 (@List.length a0 x1)) /\ (~ (x0 (@EL a0 y1 x1)))) y0.
Definition term152 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0) := exists y0 : nat, (fun y1 : nat => ((Peano.lt y1 (@List.length a0 x0)) /\ (x2 = (@EL a0 y1 x0))) /\ (~ (x1 x2))) y0.
Definition term118 (a0 : Type') (x0 : a0) (x1 : list a0) := exists y0 : nat, (fun y1 : nat => (Peano.lt y1 (@List.length a0 x1)) /\ (x0 = (@EL a0 y1 x1))) y0.
Definition term43 (a0 : Type') := (((~ (forall y0 : a0 -> Prop, forall y1 : list a0, (forall y2 : nat, (Peano.lt y2 (@List.length a0 y1)) -> y0 (@EL a0 y2 y1)) = (forall y2 : a0, (exists y3 : nat, (Peano.lt y3 (@List.length a0 y1)) /\ (y2 = (@EL a0 y3 y1))) -> y0 y2))) -> False) -> (~ (forall y0 : a0 -> Prop, forall y1 : list a0, (forall y2 : nat, (Peano.lt y2 (@List.length a0 y1)) -> y0 (@EL a0 y2 y1)) = (forall y2 : a0, (exists y3 : nat, (Peano.lt y3 (@List.length a0 y1)) /\ (y2 = (@EL a0 y3 y1))) -> y0 y2))) -> False) -> (~ (forall y0 : a0 -> Prop, forall y1 : list a0, (forall y2 : nat, (Peano.lt y2 (@List.length a0 y1)) -> y0 (@EL a0 y2 y1)) = (forall y2 : a0, (exists y3 : nat, (Peano.lt y3 (@List.length a0 y1)) /\ (y2 = (@EL a0 y3 y1))) -> y0 y2))) -> False.
Definition term1 (x0 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1).
Definition term27 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) := fun y0 : a0 => (exists y1 : nat, (Peano.lt y1 (@List.length a0 x0)) /\ (y0 = (@EL a0 y1 x0))) -> x1 y0.
Definition term95 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) := fun y0 : a0 => (exists y1 : nat, (Peano.lt y1 (@List.length a0 x0)) /\ (y0 = (@EL a0 y1 x0))) /\ (~ (x1 y0)).
Definition term250 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) (x2 : list a0) := (fun y0 : a0 => ~ (x0 y0)) (@EL a0 x1 x2).
Definition term26 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) := fun y0 : a0 => (@List.In a0 y0 x0) -> x1 y0.
Definition term38 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : list a0, (forall y2 : nat, (Peano.lt y2 (@List.length a0 y1)) -> y0 (@EL a0 y2 y1)) = (forall y2 : a0, (exists y3 : nat, (Peano.lt y3 (@List.length a0 y1)) /\ (y2 = (@EL a0 y3 y1))) -> y0 y2).
Definition term37 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : list a0, (forall y2 : nat, (Peano.lt y2 (@List.length a0 y1)) -> y0 (@EL a0 y2 y1)) = (@List.Forall a0 y0 y1).
Definition term15 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : list a0, (@List.Forall a0 y0 y1) = (forall y2 : a0, (@List.In a0 y2 y1) -> y0 y2).
Definition term14 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : list a0, (forall y2 : a0, (@List.In a0 y2 y1) -> y0 y2) = (@List.Forall a0 y0 y1).
Definition term226 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : nat) := (fun y0 : nat => (~ (Peano.lt y0 (@List.length a0 x1))) \/ (~ (x0 = (@EL a0 y0 x1)))) x2.
Definition term242 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0) := (fun y0 : a0 => forall y1 : nat, ((~ (Peano.lt y1 (@List.length a0 x0))) \/ (~ (y0 = (@EL a0 y1 x0)))) \/ (x1 y0)) x2.
Definition term70 (a0 : Type') (x0 : a0) (x1 : nat) (x2 : list a0) := (~ (Peano.lt x1 (@List.length a0 x2))) \/ (~ (x0 = (@EL a0 x1 x2))).
Definition term247 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) (x2 : list a0) := ~ (x0 (@EL a0 x1 x2)).
Definition term218 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) := fun y0 : a0 => exists y1 : nat, ((forall y2 : nat, (~ (Peano.lt y2 (@List.length a0 x0))) \/ (x1 (@EL a0 y2 x0))) /\ (((Peano.lt y1 (@List.length a0 x0)) /\ (y0 = (@EL a0 y1 x0))) /\ (~ (x1 y0)))) \/ (((Peano.lt y1 (@List.length a0 x0)) /\ (~ (x1 (@EL a0 y1 x0)))) /\ (forall y2 : a0, (forall y3 : nat, (~ (Peano.lt y3 (@List.length a0 x0))) \/ (~ (y2 = (@EL a0 y3 x0)))) \/ (x1 y2))).
Definition term25 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0) := (exists y0 : nat, (Peano.lt y0 (@List.length a0 x0)) /\ (x2 = (@EL a0 y0 x0))) -> x1 x2.
Definition term278 (a0 : Type') (x0 : a0) (x1 : nat) (x2 : list a0) := ~ ((~ (Peano.lt x1 (@List.length a0 x2))) \/ (~ (x0 = (@EL a0 x1 x2)))).
Definition term86 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0) := (~ (exists y0 : nat, (Peano.lt y0 (@List.length a0 x0)) /\ (x2 = (@EL a0 y0 x0)))) \/ (x1 x2).
Definition term162 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) := or (exists y0 : a0, exists y1 : nat, (forall y2 : nat, (~ (Peano.lt y2 (@List.length a0 x0))) \/ (x1 (@EL a0 y2 x0))) /\ (((Peano.lt y1 (@List.length a0 x0)) /\ (y0 = (@EL a0 y1 x0))) /\ (~ (x1 y0)))).
Definition term113 (x0 : nat -> Prop) (x1 : Prop) := (exists y0 : nat, x0 y0) /\ x1.
Definition term191 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0 -> Prop) := ((fun y0 : a0 => exists y1 : nat, (forall y2 : nat, (~ (Peano.lt y2 (@List.length a0 x1))) \/ (x2 (@EL a0 y2 x1))) /\ (((Peano.lt y1 (@List.length a0 x1)) /\ (y0 = (@EL a0 y1 x1))) /\ (~ (x2 y0)))) x0) \/ (exists y0 : nat, ((Peano.lt y0 (@List.length a0 x1)) /\ (~ (x2 (@EL a0 y0 x1)))) /\ (forall y1 : a0, (forall y2 : nat, (~ (Peano.lt y2 (@List.length a0 x1))) \/ (~ (y1 = (@EL a0 y2 x1)))) \/ (x2 y1))).
Definition term279 (a0 : Type') (x0 : a0) (x1 : nat) (x2 : list a0) := (~ (~ (Peano.lt x1 (@List.length a0 x2)))) /\ (~ (~ (x0 = (@EL a0 x1 x2)))).
Definition term93 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0) := ~ ((fun y0 : a0 => (exists y1 : nat, (Peano.lt y1 (@List.length a0 x0)) /\ (y0 = (@EL a0 y1 x0))) -> x1 y0) x2).
Definition term280 (a0 : Type') (x0 : nat) (x1 : list a0) := and (~ (~ (Peano.lt x0 (@List.length a0 x1)))).
Definition term74 (a0 : Type') (x0 : a0) (x1 : list a0) := forall y0 : nat, ~ ((fun y1 : nat => (Peano.lt y1 (@List.length a0 x1)) /\ (x0 = (@EL a0 y1 x1))) y0).
Definition term141 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0) := (forall y0 : nat, (~ (Peano.lt y0 (@List.length a0 x0))) \/ (x1 (@EL a0 y0 x0))) /\ ((fun y0 : a0 => exists y1 : nat, ((Peano.lt y1 (@List.length a0 x0)) /\ (y0 = (@EL a0 y1 x0))) /\ (~ (x1 y0))) x2).
Definition term178 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) := (exists y0 : a0, exists y1 : nat, (forall y2 : nat, (~ (Peano.lt y2 (@List.length a0 x0))) \/ (x1 (@EL a0 y2 x0))) /\ (((Peano.lt y1 (@List.length a0 x0)) /\ (y0 = (@EL a0 y1 x0))) /\ (~ (x1 y0)))) \/ (exists y0 : nat, ((Peano.lt y0 (@List.length a0 x0)) /\ (~ (x1 (@EL a0 y0 x0)))) /\ (forall y1 : a0, (forall y2 : nat, (~ (Peano.lt y2 (@List.length a0 x0))) \/ (~ (y1 = (@EL a0 y2 x0)))) \/ (x1 y1))).
Definition term91 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) := exists y0 : a0, ~ ((fun y1 : a0 => (exists y2 : nat, (Peano.lt y2 (@List.length a0 x0)) /\ (y1 = (@EL a0 y2 x0))) -> x1 y1) y0).
Definition term286 (a0 : Type') (x0 : nat) (x1 : list a0) := (Peano.lt x0 (@List.length a0 x1)) /\ ((@EL a0 x0 x1) = (@EL a0 x0 x1)).
Definition term57 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) (x2 : list a0) := (~ (Peano.lt x1 (@List.length a0 x2))) \/ (x0 (@EL a0 x1 x2)).
Definition term49 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) (x2 : list a0) := (Peano.lt x1 (@List.length a0 x2)) -> x0 (@EL a0 x1 x2).
Definition term47 (a0 : Type') (x0 : a0) (x1 : nat) (x2 : list a0) := (Peano.lt x1 (@List.length a0 x2)) /\ (x0 = (@EL a0 x1 x2)).
Definition term83 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0) := ~ ((exists y0 : nat, (Peano.lt y0 (@List.length a0 x0)) /\ (x2 = (@EL a0 y0 x0))) -> x1 x2).
Definition term257 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) (x2 : list a0) := @eq Prop ((x0 (@EL a0 x1 x2)) \/ (~ (Peano.lt x1 (@List.length a0 x2)))).
Definition term182 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) := exists y0 : a0, ((fun y1 : a0 => exists y2 : nat, (forall y3 : nat, (~ (Peano.lt y3 (@List.length a0 x0))) \/ (x1 (@EL a0 y3 x0))) /\ (((Peano.lt y2 (@List.length a0 x0)) /\ (y1 = (@EL a0 y2 x0))) /\ (~ (x1 y1)))) y0) \/ (exists y1 : nat, ((Peano.lt y1 (@List.length a0 x0)) /\ (~ (x1 (@EL a0 y1 x0)))) /\ (forall y2 : a0, (forall y3 : nat, (~ (Peano.lt y3 (@List.length a0 x0))) \/ (~ (y2 = (@EL a0 y3 x0)))) \/ (x1 y2))).
Definition term100 (a0 : Type') (x0 : a0 -> Prop) (x1 : list a0) := and (exists y0 : nat, (Peano.lt y0 (@List.length a0 x1)) /\ (~ (x0 (@EL a0 y0 x1)))).
Definition term81 (a0 : Type') (x0 : a0) (x1 : list a0) := and (exists y0 : nat, (Peano.lt y0 (@List.length a0 x1)) /\ (x0 = (@EL a0 y0 x1))).
Definition term157 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0) := fun y0 : nat => (forall y1 : nat, (~ (Peano.lt y1 (@List.length a0 x0))) \/ (x1 (@EL a0 y1 x0))) /\ ((fun y1 : nat => ((Peano.lt y1 (@List.length a0 x0)) /\ (x2 = (@EL a0 y1 x0))) /\ (~ (x1 x2))) y0).
Definition term107 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) := or ((forall y0 : nat, (Peano.lt y0 (@List.length a0 x0)) -> x1 (@EL a0 y0 x0)) /\ (~ (forall y0 : a0, (exists y1 : nat, (Peano.lt y1 (@List.length a0 x0)) /\ (y0 = (@EL a0 y1 x0))) -> x1 y0))).
Definition term216 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0 -> Prop) := fun y0 : nat => ((forall y1 : nat, (~ (Peano.lt y1 (@List.length a0 x1))) \/ (x2 (@EL a0 y1 x1))) /\ (((Peano.lt y0 (@List.length a0 x1)) /\ (x0 = (@EL a0 y0 x1))) /\ (~ (x2 x0)))) \/ (((Peano.lt y0 (@List.length a0 x1)) /\ (~ (x2 (@EL a0 y0 x1)))) /\ (forall y1 : a0, (forall y2 : nat, (~ (Peano.lt y2 (@List.length a0 x1))) \/ (~ (y1 = (@EL a0 y2 x1)))) \/ (x2 y1))).
Definition term266 (a0 : Type') (x0 : nat) (x1 : list a0) := (~ ((@EL a0 x0 x1) = (@EL a0 x0 x1))) -> (@EL a0 x0 x1) = (@EL a0 x0 x1).
Definition term263 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) (x2 : list a0) := (~ (x0 (@EL a0 x1 x2))) -> x0 (@EL a0 x1 x2).
Definition term224 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0) := (forall y0 : nat, (fun y1 : nat => (~ (Peano.lt y1 (@List.length a0 x0))) \/ (~ (x2 = (@EL a0 y1 x0)))) y0) \/ (x1 x2).
Definition term173 (a0 : Type') (x0 : nat) (x1 : list a0) (x2 : a0 -> Prop) := ((fun y0 : nat => (Peano.lt y0 (@List.length a0 x1)) /\ (~ (x2 (@EL a0 y0 x1)))) x0) /\ (forall y0 : a0, (forall y1 : nat, (~ (Peano.lt y1 (@List.length a0 x1))) \/ (~ (y0 = (@EL a0 y1 x1)))) \/ (x2 y0)).
Definition term9 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : list a0 => (@List.Forall a0 x0 y0) = (forall y1 : a0, (@List.In a0 y1 y0) -> x0 y1).
Definition term193 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) := fun y0 : a0 => ((fun y1 : a0 => exists y2 : nat, (forall y3 : nat, (~ (Peano.lt y3 (@List.length a0 x0))) \/ (x1 (@EL a0 y3 x0))) /\ (((Peano.lt y2 (@List.length a0 x0)) /\ (y1 = (@EL a0 y2 x0))) /\ (~ (x1 y1)))) y0) \/ (exists y1 : nat, ((Peano.lt y1 (@List.length a0 x0)) /\ (~ (x1 (@EL a0 y1 x0)))) /\ (forall y2 : a0, (forall y3 : nat, (~ (Peano.lt y3 (@List.length a0 x0))) \/ (~ (y2 = (@EL a0 y3 x0)))) \/ (x1 y2))).
Definition term61 (a0 : Type') (x0 : a0 -> Prop) (x1 : list a0) := exists y0 : nat, ~ ((fun y1 : nat => (Peano.lt y1 (@List.length a0 x1)) -> x0 (@EL a0 y1 x1)) y0).
Definition term212 (a0 : Type') (x0 : nat) (x1 : list a0) (x2 : a0 -> Prop) (x3 : a0) := or ((forall y0 : nat, (~ (Peano.lt y0 (@List.length a0 x1))) \/ (x2 (@EL a0 y0 x1))) /\ (((Peano.lt x0 (@List.length a0 x1)) /\ (x3 = (@EL a0 x0 x1))) /\ (~ (x2 x3)))).
Definition term232 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : nat) := or ((fun y0 : nat => (~ (Peano.lt y0 (@List.length a0 x1))) \/ (~ (x0 = (@EL a0 y0 x1)))) x2).
Definition term284 (a0 : Type') (x0 : a0) (x1 : nat) (x2 : list a0) := imp ((Peano.lt x1 (@List.length a0 x2)) /\ (x0 = (@EL a0 x1 x2))).
Definition term203 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0) := fun y0 : nat => (fun y1 : nat => (forall y2 : nat, (~ (Peano.lt y2 (@List.length a0 x0))) \/ (x1 (@EL a0 y2 x0))) /\ (((Peano.lt y1 (@List.length a0 x0)) /\ (x2 = (@EL a0 y1 x0))) /\ (~ (x1 x2)))) y0.
Definition term117 (a0 : Type') (x0 : a0) (x1 : list a0) := fun y0 : nat => (fun y1 : nat => (Peano.lt y1 (@List.length a0 x1)) /\ (x0 = (@EL a0 y1 x1))) y0.
Definition term202 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0) (x3 : nat) := (fun y0 : nat => (forall y1 : nat, (~ (Peano.lt y1 (@List.length a0 x0))) \/ (x1 (@EL a0 y1 x0))) /\ (((Peano.lt y0 (@List.length a0 x0)) /\ (x2 = (@EL a0 y0 x0))) /\ (~ (x1 x2)))) x3.
Definition term2 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1)) x1.
Definition term30 (a0 : Type') (x0 : a0 -> Prop) (x1 : list a0) := forall y0 : nat, (Peano.lt y0 (@List.length a0 x1)) -> x0 (@EL a0 y0 x1).
Definition term175 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) := fun y0 : nat => ((fun y1 : nat => (Peano.lt y1 (@List.length a0 x0)) /\ (~ (x1 (@EL a0 y1 x0)))) y0) /\ (forall y1 : a0, (forall y2 : nat, (~ (Peano.lt y2 (@List.length a0 x0))) \/ (~ (y1 = (@EL a0 y2 x0)))) \/ (x1 y1)).
Definition term134 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) := (forall y0 : nat, (~ (Peano.lt y0 (@List.length a0 x0))) \/ (x1 (@EL a0 y0 x0))) /\ (exists y0 : a0, (fun y1 : a0 => exists y2 : nat, ((Peano.lt y2 (@List.length a0 x0)) /\ (y1 = (@EL a0 y2 x0))) /\ (~ (x1 y1))) y0).
Definition term106 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) := (forall y0 : nat, (~ (Peano.lt y0 (@List.length a0 x0))) \/ (x1 (@EL a0 y0 x0))) /\ (exists y0 : a0, (exists y1 : nat, (Peano.lt y1 (@List.length a0 x0)) /\ (y0 = (@EL a0 y1 x0))) /\ (~ (x1 y0))).
Definition term213 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0 -> Prop) (x3 : nat) := ((fun y0 : nat => (forall y1 : nat, (~ (Peano.lt y1 (@List.length a0 x1))) \/ (x2 (@EL a0 y1 x1))) /\ (((Peano.lt y0 (@List.length a0 x1)) /\ (x0 = (@EL a0 y0 x1))) /\ (~ (x2 x0)))) x3) \/ ((fun y0 : nat => ((Peano.lt y0 (@List.length a0 x1)) /\ (~ (x2 (@EL a0 y0 x1)))) /\ (forall y1 : a0, (forall y2 : nat, (~ (Peano.lt y2 (@List.length a0 x1))) \/ (~ (y1 = (@EL a0 y2 x1)))) \/ (x2 y1))) x3).
Definition term125 (a0 : Type') (x0 : nat) (x1 : list a0) (x2 : a0 -> Prop) (x3 : a0) := ((Peano.lt x0 (@List.length a0 x1)) /\ (x3 = (@EL a0 x0 x1))) /\ (~ (x2 x3)).
Definition term99 (a0 : Type') (x0 : a0 -> Prop) (x1 : list a0) := and (~ (forall y0 : nat, (Peano.lt y0 (@List.length a0 x1)) -> x0 (@EL a0 y0 x1))).
Definition term131 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) := (forall y0 : nat, (~ (Peano.lt y0 (@List.length a0 x0))) \/ (x1 (@EL a0 y0 x0))) /\ (exists y0 : a0, exists y1 : nat, ((Peano.lt y1 (@List.length a0 x0)) /\ (y0 = (@EL a0 y1 x0))) /\ (~ (x1 y0))).
Definition term219 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) := exists y0 : a0, exists y1 : nat, ((forall y2 : nat, (~ (Peano.lt y2 (@List.length a0 x0))) \/ (x1 (@EL a0 y2 x0))) /\ (((Peano.lt y1 (@List.length a0 x0)) /\ (y0 = (@EL a0 y1 x0))) /\ (~ (x1 y0)))) \/ (((Peano.lt y1 (@List.length a0 x0)) /\ (~ (x1 (@EL a0 y1 x0)))) /\ (forall y2 : a0, (forall y3 : nat, (~ (Peano.lt y3 (@List.length a0 x0))) \/ (~ (y2 = (@EL a0 y3 x0)))) \/ (x1 y2))).
Definition term161 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) := exists y0 : a0, exists y1 : nat, (forall y2 : nat, (~ (Peano.lt y2 (@List.length a0 x0))) \/ (x1 (@EL a0 y2 x0))) /\ (((Peano.lt y1 (@List.length a0 x0)) /\ (y0 = (@EL a0 y1 x0))) /\ (~ (x1 y0))).
Definition term130 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) := exists y0 : a0, exists y1 : nat, ((Peano.lt y1 (@List.length a0 x0)) /\ (y0 = (@EL a0 y1 x0))) /\ (~ (x1 y0)).
Definition term35 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : list a0, (forall y2 : nat, (Peano.lt y2 (@List.length a0 y1)) -> y0 (@EL a0 y2 y1)) = (@List.Forall a0 y0 y1).
Definition term12 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : list a0, (forall y2 : a0, (@List.In a0 y2 y1) -> y0 y2) = (@List.Forall a0 y0 y1).
Definition term129 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) := fun y0 : a0 => exists y1 : nat, ((Peano.lt y1 (@List.length a0 x0)) /\ (y0 = (@EL a0 y1 x0))) /\ (~ (x1 y0)).
Definition term246 (a0 : Type') (x0 : a0) (x1 : nat) (x2 : list a0) := ~ (x0 = (@EL a0 x1 x2)).
Definition term154 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0) := @eq Prop ((forall y0 : nat, (~ (Peano.lt y0 (@List.length a0 x0))) \/ (x1 (@EL a0 y0 x0))) /\ (exists y0 : nat, ((Peano.lt y0 (@List.length a0 x0)) /\ (x2 = (@EL a0 y0 x0))) /\ (~ (x1 x2)))).
Definition term153 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0) := @eq Prop ((forall y0 : nat, (~ (Peano.lt y0 (@List.length a0 x0))) \/ (x1 (@EL a0 y0 x0))) /\ (exists y0 : nat, (fun y1 : nat => ((Peano.lt y1 (@List.length a0 x0)) /\ (x2 = (@EL a0 y1 x0))) /\ (~ (x1 x2))) y0)).
Definition term140 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) := @eq Prop ((forall y0 : nat, (~ (Peano.lt y0 (@List.length a0 x0))) \/ (x1 (@EL a0 y0 x0))) /\ (exists y0 : a0, exists y1 : nat, ((Peano.lt y1 (@List.length a0 x0)) /\ (y0 = (@EL a0 y1 x0))) /\ (~ (x1 y0)))).
Definition term139 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) := @eq Prop ((forall y0 : nat, (~ (Peano.lt y0 (@List.length a0 x0))) \/ (x1 (@EL a0 y0 x0))) /\ (exists y0 : a0, (fun y1 : a0 => exists y2 : nat, ((Peano.lt y2 (@List.length a0 x0)) /\ (y1 = (@EL a0 y2 x0))) /\ (~ (x1 y1))) y0)).
Definition term274 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : nat) (x3 : list a0) := @eq Prop ((x0 x1) \/ ((~ (Peano.lt x2 (@List.length a0 x3))) \/ (~ (x1 = (@EL a0 x2 x3))))).
Definition term231 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0) := @eq Prop ((forall y0 : nat, (~ (Peano.lt y0 (@List.length a0 x0))) \/ (~ (x2 = (@EL a0 y0 x0)))) \/ (x1 x2)).
Definition term230 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0) := @eq Prop ((forall y0 : nat, (fun y1 : nat => (~ (Peano.lt y1 (@List.length a0 x0))) \/ (~ (x2 = (@EL a0 y1 x0)))) y0) \/ (x1 x2)).
Definition term177 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) := exists y0 : nat, ((Peano.lt y0 (@List.length a0 x0)) /\ (~ (x1 (@EL a0 y0 x0)))) /\ (forall y1 : a0, (forall y2 : nat, (~ (Peano.lt y2 (@List.length a0 x0))) \/ (~ (y1 = (@EL a0 y2 x0)))) \/ (x1 y1)).
Definition term136 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0) := (fun y0 : a0 => exists y1 : nat, ((Peano.lt y1 (@List.length a0 x0)) /\ (y0 = (@EL a0 y1 x0))) /\ (~ (x1 y0))) x2.
Definition term199 (x0 : nat -> Prop) (x1 : nat -> Prop) := exists y0 : nat, (x0 y0) \/ (x1 y0).
Definition term241 (a0 : Type') (x0 : a0 -> Prop) (x1 : list a0) (x2 : nat) := (fun y0 : nat => (~ (Peano.lt y0 (@List.length a0 x1))) \/ (x0 (@EL a0 y0 x1))) x2.
Definition term237 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0) := fun y0 : nat => ((~ (Peano.lt y0 (@List.length a0 x0))) \/ (~ (x2 = (@EL a0 y0 x0)))) \/ (x1 x2).
Definition term62 (a0 : Type') (x0 : a0 -> Prop) (x1 : list a0) (x2 : nat) := (fun y0 : nat => (Peano.lt y0 (@List.length a0 x1)) -> x0 (@EL a0 y0 x1)) x2.
Definition term77 (a0 : Type') (x0 : a0) (x1 : list a0) := fun y0 : nat => ~ ((fun y1 : nat => (Peano.lt y1 (@List.length a0 x1)) /\ (x0 = (@EL a0 y1 x1))) y0).
Definition term64 (a0 : Type') (x0 : a0 -> Prop) (x1 : list a0) := fun y0 : nat => ~ ((fun y1 : nat => (Peano.lt y1 (@List.length a0 x1)) -> x0 (@EL a0 y1 x1)) y0).
Definition term170 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) := @eq Prop ((exists y0 : nat, (Peano.lt y0 (@List.length a0 x0)) /\ (~ (x1 (@EL a0 y0 x0)))) /\ (forall y0 : a0, (forall y1 : nat, (~ (Peano.lt y1 (@List.length a0 x0))) \/ (~ (y0 = (@EL a0 y1 x0)))) \/ (x1 y0))).
Definition term169 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) := @eq Prop ((exists y0 : nat, (fun y1 : nat => (Peano.lt y1 (@List.length a0 x0)) /\ (~ (x1 (@EL a0 y1 x0)))) y0) /\ (forall y0 : a0, (forall y1 : nat, (~ (Peano.lt y1 (@List.length a0 x0))) \/ (~ (y0 = (@EL a0 y1 x0)))) \/ (x1 y0))).
Definition term44 (a0 : Type') := (((~ (forall y0 : a0 -> Prop, forall y1 : list a0, (forall y2 : nat, (Peano.lt y2 (@List.length a0 y1)) -> y0 (@EL a0 y2 y1)) = (forall y2 : a0, (exists y3 : nat, (Peano.lt y3 (@List.length a0 y1)) /\ (y2 = (@EL a0 y3 y1))) -> y0 y2))) -> False) -> (~ (forall y0 : a0 -> Prop, forall y1 : list a0, (forall y2 : nat, (Peano.lt y2 (@List.length a0 y1)) -> y0 (@EL a0 y2 y1)) = (forall y2 : a0, (exists y3 : nat, (Peano.lt y3 (@List.length a0 y1)) /\ (y2 = (@EL a0 y3 y1))) -> y0 y2))) -> False) -> ((~ (forall y0 : a0 -> Prop, forall y1 : list a0, (forall y2 : nat, (Peano.lt y2 (@List.length a0 y1)) -> y0 (@EL a0 y2 y1)) = (forall y2 : a0, (exists y3 : nat, (Peano.lt y3 (@List.length a0 y1)) /\ (y2 = (@EL a0 y3 y1))) -> y0 y2))) -> False) -> (~ (forall y0 : a0 -> Prop, forall y1 : list a0, (forall y2 : nat, (Peano.lt y2 (@List.length a0 y1)) -> y0 (@EL a0 y2 y1)) = (forall y2 : a0, (exists y3 : nat, (Peano.lt y3 (@List.length a0 y1)) /\ (y2 = (@EL a0 y3 y1))) -> y0 y2))) -> False.
Definition term32 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : list a0 => (forall y1 : nat, (Peano.lt y1 (@List.length a0 y0)) -> x0 (@EL a0 y1 y0)) = (forall y1 : a0, (exists y2 : nat, (Peano.lt y2 (@List.length a0 y0)) /\ (y1 = (@EL a0 y2 y0))) -> x0 y1).
Definition term4 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0)) x2.
Definition term82 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0) := (exists y0 : nat, (Peano.lt y0 (@List.length a0 x0)) /\ (x2 = (@EL a0 y0 x0))) /\ (~ (x1 x2)).
Definition term84 (a0 : Type') (x0 : a0) (x1 : list a0) := or (~ (exists y0 : nat, (Peano.lt y0 (@List.length a0 x1)) /\ (x0 = (@EL a0 y0 x1)))).
Definition term111 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) /\ x1.
Definition term55 (a0 : Type') (x0 : nat) (x1 : list a0) := Peano.lt x0 (@List.length a0 x1).
Definition term215 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0 -> Prop) := fun y0 : nat => ((fun y1 : nat => (forall y2 : nat, (~ (Peano.lt y2 (@List.length a0 x1))) \/ (x2 (@EL a0 y2 x1))) /\ (((Peano.lt y1 (@List.length a0 x1)) /\ (x0 = (@EL a0 y1 x1))) /\ (~ (x2 x0)))) y0) \/ ((fun y1 : nat => ((Peano.lt y1 (@List.length a0 x1)) /\ (~ (x2 (@EL a0 y1 x1)))) /\ (forall y2 : a0, (forall y3 : nat, (~ (Peano.lt y3 (@List.length a0 x1))) \/ (~ (y2 = (@EL a0 y3 x1)))) \/ (x2 y2))) y0).
Definition term51 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) := (~ ((forall y0 : nat, (Peano.lt y0 (@List.length a0 x0)) -> x1 (@EL a0 y0 x0)) = (forall y0 : a0, (exists y1 : nat, (Peano.lt y1 (@List.length a0 x0)) /\ (y0 = (@EL a0 y1 x0))) -> x1 y0))) -> False.
Definition term205 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0) := or (exists y0 : nat, (fun y1 : nat => (forall y2 : nat, (~ (Peano.lt y2 (@List.length a0 x0))) \/ (x1 (@EL a0 y2 x0))) /\ (((Peano.lt y1 (@List.length a0 x0)) /\ (x2 = (@EL a0 y1 x0))) /\ (~ (x1 x2)))) y0).
Definition term235 (a0 : Type') (x0 : nat) (x1 : list a0) (x2 : a0 -> Prop) (x3 : a0) := ((~ (Peano.lt x0 (@List.length a0 x1))) \/ (~ (x3 = (@EL a0 x0 x1)))) \/ (x2 x3).
Definition term214 (a0 : Type') (x0 : a0) (x1 : nat) (x2 : list a0) (x3 : a0 -> Prop) := ((forall y0 : nat, (~ (Peano.lt y0 (@List.length a0 x2))) \/ (x3 (@EL a0 y0 x2))) /\ (((Peano.lt x1 (@List.length a0 x2)) /\ (x0 = (@EL a0 x1 x2))) /\ (~ (x3 x0)))) \/ (((Peano.lt x1 (@List.length a0 x2)) /\ (~ (x3 (@EL a0 x1 x2)))) /\ (forall y0 : a0, (forall y1 : nat, (~ (Peano.lt y1 (@List.length a0 x2))) \/ (~ (y0 = (@EL a0 y1 x2)))) \/ (x3 y0))).
Definition term264 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) (x2 : list a0) := (x0 (@EL a0 x1 x2)) -> False.
Definition term105 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) := (forall y0 : nat, (Peano.lt y0 (@List.length a0 x0)) -> x1 (@EL a0 y0 x0)) /\ (~ (forall y0 : a0, (exists y1 : nat, (Peano.lt y1 (@List.length a0 x0)) /\ (y0 = (@EL a0 y1 x0))) -> x1 y0)).
Definition term97 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) := fun y0 : a0 => (forall y1 : nat, (~ (Peano.lt y1 (@List.length a0 x0))) \/ (~ (y0 = (@EL a0 y1 x0)))) \/ (x1 y0).
Definition term240 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) := forall y0 : a0, forall y1 : nat, ((~ (Peano.lt y1 (@List.length a0 x0))) \/ (~ (y0 = (@EL a0 y1 x0)))) \/ (x1 y0).
Definition term239 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) := fun y0 : a0 => forall y1 : nat, ((~ (Peano.lt y1 (@List.length a0 x0))) \/ (~ (y0 = (@EL a0 y1 x0)))) \/ (x1 y0).
Definition term163 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) := (exists y0 : nat, (fun y1 : nat => (Peano.lt y1 (@List.length a0 x0)) /\ (~ (x1 (@EL a0 y1 x0)))) y0) /\ (forall y0 : a0, (forall y1 : nat, (~ (Peano.lt y1 (@List.length a0 x0))) \/ (~ (y0 = (@EL a0 y1 x0)))) \/ (x1 y0)).
Definition term197 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term244 (a0 : Type') (x0 : nat) (x1 : list a0) (x2 : a0 -> Prop) (x3 : a0) := (~ (Peano.lt x0 (@List.length a0 x1))) \/ ((~ (x3 = (@EL a0 x0 x1))) \/ (x2 x3)).
Definition term87 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0) := (forall y0 : nat, (~ (Peano.lt y0 (@List.length a0 x0))) \/ (~ (x2 = (@EL a0 y0 x0)))) \/ (x1 x2).
Definition term90 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) := ~ (forall y0 : a0, (exists y1 : nat, (Peano.lt y1 (@List.length a0 x0)) /\ (y0 = (@EL a0 y1 x0))) -> x1 y0).
Definition term148 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0) := (forall y0 : nat, (~ (Peano.lt y0 (@List.length a0 x0))) \/ (x1 (@EL a0 y0 x0))) /\ (exists y0 : nat, (fun y1 : nat => ((Peano.lt y1 (@List.length a0 x0)) /\ (x2 = (@EL a0 y1 x0))) /\ (~ (x1 x2))) y0).
Definition term59 (x0 : nat -> Prop) := exists y0 : nat, ~ (x0 y0).
Definition term282 (a0 : Type') (x0 : a0) (x1 : nat) (x2 : list a0) := ~ (~ (x0 = (@EL a0 x1 x2))).
Definition term259 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) (x2 : list a0) := (~ (~ (Peano.lt x1 (@List.length a0 x2)))) -> x0 (@EL a0 x1 x2).
Definition term73 (a0 : Type') (x0 : a0) (x1 : list a0) := ~ (exists y0 : nat, (Peano.lt y0 (@List.length a0 x1)) /\ (x0 = (@EL a0 y0 x1))).
Definition term198 (x0 : nat -> Prop) (x1 : nat -> Prop) := (exists y0 : nat, x0 y0) \/ (exists y0 : nat, x1 y0).
Definition term273 (a0 : Type') (x0 : nat) (x1 : list a0) (x2 : a0 -> Prop) (x3 : a0) := @eq Prop ((~ (Peano.lt x0 (@List.length a0 x1))) \/ ((~ (x3 = (@EL a0 x0 x1))) \/ (x2 x3))).
Definition term85 (a0 : Type') (x0 : a0) (x1 : list a0) := or (forall y0 : nat, (~ (Peano.lt y0 (@List.length a0 x1))) \/ (~ (x0 = (@EL a0 y0 x1)))).
Definition term126 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0) := fun y0 : nat => ((fun y1 : nat => (Peano.lt y1 (@List.length a0 x0)) /\ (x2 = (@EL a0 y1 x0))) y0) /\ (~ (x1 x2)).
Definition term181 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) := (exists y0 : a0, (fun y1 : a0 => exists y2 : nat, (forall y3 : nat, (~ (Peano.lt y3 (@List.length a0 x0))) \/ (x1 (@EL a0 y3 x0))) /\ (((Peano.lt y2 (@List.length a0 x0)) /\ (y1 = (@EL a0 y2 x0))) /\ (~ (x1 y1)))) y0) \/ (exists y0 : nat, ((Peano.lt y0 (@List.length a0 x0)) /\ (~ (x1 (@EL a0 y0 x0)))) /\ (forall y1 : a0, (forall y2 : nat, (~ (Peano.lt y2 (@List.length a0 x0))) \/ (~ (y1 = (@EL a0 y2 x0)))) \/ (x1 y1))).
Definition term149 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0) := exists y0 : nat, (forall y1 : nat, (~ (Peano.lt y1 (@List.length a0 x0))) \/ (x1 (@EL a0 y1 x0))) /\ ((fun y1 : nat => ((Peano.lt y1 (@List.length a0 x0)) /\ (x2 = (@EL a0 y1 x0))) /\ (~ (x1 x2))) y0).
Definition term22 (a0 : Type') (x0 : a0) (x1 : list a0) := imp (@List.In a0 x0 x1).
Definition term19 (a0 : Type') (x0 : a0) (x1 : list a0) := exists y0 : nat, (Peano.lt y0 (@List.length a0 x1)) /\ (x0 = (@EL a0 y0 x1)).
Definition term210 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0 -> Prop) := @eq Prop ((exists y0 : nat, (forall y1 : nat, (~ (Peano.lt y1 (@List.length a0 x1))) \/ (x2 (@EL a0 y1 x1))) /\ (((Peano.lt y0 (@List.length a0 x1)) /\ (x0 = (@EL a0 y0 x1))) /\ (~ (x2 x0)))) \/ (exists y0 : nat, ((Peano.lt y0 (@List.length a0 x1)) /\ (~ (x2 (@EL a0 y0 x1)))) /\ (forall y1 : a0, (forall y2 : nat, (~ (Peano.lt y2 (@List.length a0 x1))) \/ (~ (y1 = (@EL a0 y2 x1)))) \/ (x2 y1)))).
Definition term209 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0 -> Prop) := @eq Prop ((exists y0 : nat, (fun y1 : nat => (forall y2 : nat, (~ (Peano.lt y2 (@List.length a0 x1))) \/ (x2 (@EL a0 y2 x1))) /\ (((Peano.lt y1 (@List.length a0 x1)) /\ (x0 = (@EL a0 y1 x1))) /\ (~ (x2 x0)))) y0) \/ (exists y0 : nat, (fun y1 : nat => ((Peano.lt y1 (@List.length a0 x1)) /\ (~ (x2 (@EL a0 y1 x1)))) /\ (forall y2 : a0, (forall y3 : nat, (~ (Peano.lt y3 (@List.length a0 x1))) \/ (~ (y2 = (@EL a0 y3 x1)))) \/ (x2 y2))) y0)).
Definition term188 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) := @eq Prop ((exists y0 : a0, exists y1 : nat, (forall y2 : nat, (~ (Peano.lt y2 (@List.length a0 x0))) \/ (x1 (@EL a0 y2 x0))) /\ (((Peano.lt y1 (@List.length a0 x0)) /\ (y0 = (@EL a0 y1 x0))) /\ (~ (x1 y0)))) \/ (exists y0 : nat, ((Peano.lt y0 (@List.length a0 x0)) /\ (~ (x1 (@EL a0 y0 x0)))) /\ (forall y1 : a0, (forall y2 : nat, (~ (Peano.lt y2 (@List.length a0 x0))) \/ (~ (y1 = (@EL a0 y2 x0)))) \/ (x1 y1)))).
Definition term187 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) := @eq Prop ((exists y0 : a0, (fun y1 : a0 => exists y2 : nat, (forall y3 : nat, (~ (Peano.lt y3 (@List.length a0 x0))) \/ (x1 (@EL a0 y3 x0))) /\ (((Peano.lt y2 (@List.length a0 x0)) /\ (y1 = (@EL a0 y2 x0))) /\ (~ (x1 y1)))) y0) \/ (exists y0 : nat, ((Peano.lt y0 (@List.length a0 x0)) /\ (~ (x1 (@EL a0 y0 x0)))) /\ (forall y1 : a0, (forall y2 : nat, (~ (Peano.lt y2 (@List.length a0 x0))) \/ (~ (y1 = (@EL a0 y2 x0)))) \/ (x1 y1)))).
