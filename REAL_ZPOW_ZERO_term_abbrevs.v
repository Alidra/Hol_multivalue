Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term55 (x0 : nat) := @eq real (real_zpow (real_of_num (NUMERAL 0)) (int_neg (int_of_num x0))).
Definition term195 := (exists y0 : nat, ~ (y0 = (NUMERAL 0))) /\ (~ ((real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0)))).
Definition term175 := exists y0 : nat, y0 = (NUMERAL 0).
Definition term19 (x0 : int -> Prop) := (forall y0 : nat, x0 (int_of_num y0)) /\ (forall y0 : nat, x0 (int_neg (int_of_num y0))).
Definition term128 (x0 : nat -> Prop) := ~ (all x0).
Definition term206 := (~ False) -> False.
Definition term71 (x0 : nat) := @eq real (real_inv (@COND real (x0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))).
Definition term113 (x0 : nat) := and (~ (~ (x0 = (NUMERAL 0)))).
Definition term7 (x0 : nat) := @COND real (x0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term119 (x0 : nat) := ~ ((x0 = (NUMERAL 0)) \/ ((real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0)))).
Definition term95 := @eq real (real_inv (real_of_num (NUMERAL 0))).
Definition term98 := @COND real True (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term47 := real_of_num (NUMERAL 0).
Definition term25 (x0 : int) := @COND real (x0 = (int_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term64 (x0 : nat) := @COND real ((int_of_num x0) = (int_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term131 (x0 : nat) := (fun y0 : nat => ((~ (y0 = (NUMERAL 0))) \/ ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0))))) /\ ((y0 = (NUMERAL 0)) \/ ((real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))))) x0.
Definition term4 := int_of_num (NUMERAL 0).
Definition term123 (x0 : nat) := (~ ((~ (x0 = (NUMERAL 0))) \/ ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))))) \/ (~ ((x0 = (NUMERAL 0)) \/ ((real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))))).
Definition term65 (x0 : nat) := @COND real (x0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term155 := or (exists y0 : nat, (y0 = (NUMERAL 0)) /\ (~ ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))))).
Definition term68 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term159 := (exists y0 : nat, (y0 = (NUMERAL 0)) /\ (~ ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))))) \/ (exists y0 : nat, (~ (y0 = (NUMERAL 0))) /\ (~ ((real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))))).
Definition term137 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term40 (x0 : nat) := real_zpow (real_of_num (NUMERAL 0)) (int_neg (int_of_num x0)).
Definition term15 (x0 : real) (x1 : int) := real_zpow x0 (int_neg x1).
Definition term50 := fun y0 : nat => (real_pow (real_of_num (NUMERAL 0)) y0) = (@COND real ((int_of_num y0) = (int_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))).
Definition term115 (x0 : nat) := (~ (~ (x0 = (NUMERAL 0)))) /\ (~ ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0))))).
Definition term24 (x0 : int) := real_zpow (real_of_num (NUMERAL 0)) x0.
Definition term78 (x0 : Prop) := (~ x0) -> False.
Definition term87 := real_inv (real_of_num (NUMERAL 0)).
Definition term48 (x0 : nat) := @eq real (real_zpow (real_of_num (NUMERAL 0)) (int_of_num x0)).
Definition term9 (x0 : real) := forall y0 : nat, (real_zpow x0 (int_of_num y0)) = (real_pow x0 y0).
Definition term1 (x0 : nat) := forall y0 : nat, ((int_of_num x0) = (int_of_num y0)) = (x0 = y0).
Definition term90 := ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))) -> ~ ((real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))).
Definition term122 (x0 : nat) := or ((x0 = (NUMERAL 0)) /\ (~ ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))))).
Definition term33 := fun y0 : nat => (fun y1 : int => (real_zpow (real_of_num (NUMERAL 0)) y1) = (@COND real (y1 = (int_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) (int_of_num y0).
Definition term17 (x0 : int -> Prop) := (fun y0 : int -> Prop => (forall y1 : int, y0 y1) = ((forall y1 : nat, y0 (int_of_num y1)) /\ (forall y1 : nat, y0 (int_neg (int_of_num y1))))) x0.
Definition term108 := ~ (forall y0 : nat, ((~ (y0 = (NUMERAL 0))) \/ ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0))))) /\ ((y0 = (NUMERAL 0)) \/ ((real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))))).
Definition term80 := ~ (forall y0 : nat, (real_inv (@COND real (y0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) = (@COND real (y0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))).
Definition term169 (x0 : nat) := ((fun y0 : nat => y0 = (NUMERAL 0)) x0) /\ (~ ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0))))).
Definition term70 (x0 : nat) := real_inv (@COND real (x0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))).
Definition term105 (x0 : nat) := ((~ (x0 = (NUMERAL 0))) \/ ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0))))) /\ ((x0 = (NUMERAL 0)) \/ ((real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0)))).
Definition term182 := fun y0 : nat => ~ (y0 = (NUMERAL 0)).
Definition term204 (x0 : Prop) := (~ x0) -> x0.
Definition term114 (x0 : nat) := and (x0 = (NUMERAL 0)).
Definition term194 := and (exists y0 : nat, ~ (y0 = (NUMERAL 0))).
Definition term117 (x0 : nat) := ~ ((~ (x0 = (NUMERAL 0))) \/ ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0))))).
Definition term86 := ~ ((real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))).
Definition term73 (x0 : nat) := @COND real ((int_neg (int_of_num x0)) = (int_of_num (NUMERAL 0))).
Definition term186 (x0 : nat) := ((fun y0 : nat => ~ (y0 = (NUMERAL 0))) x0) /\ (~ ((real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0)))).
Definition term81 := (~ (forall y0 : nat, (real_inv (@COND real (y0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) = (@COND real (y0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))))) -> ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))) -> ((real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) -> False.
Definition term144 (x0 : nat) := (fun y0 : nat => (y0 = (NUMERAL 0)) /\ (~ ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))))) x0.
Definition term193 := and (exists y0 : nat, (fun y1 : nat => ~ (y1 = (NUMERAL 0))) y0).
Definition term176 := and (exists y0 : nat, (fun y1 : nat => y1 = (NUMERAL 0)) y0).
Definition term146 (x0 : nat) := (fun y0 : nat => (~ (y0 = (NUMERAL 0))) /\ (~ ((real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))))) x0.
Definition term3 (x0 : int) := (fun y0 : int => ((int_neg y0) = (int_of_num (NUMERAL 0))) = (y0 = (int_of_num (NUMERAL 0)))) x0.
Definition term96 (x0 : nat) := ((x0 = (NUMERAL 0)) = False) -> ((real_inv (@COND real (x0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) = (@COND real (x0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) = ((real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))).
Definition term62 (x0 : nat) := @COND real (x0 = (NUMERAL 0)).
Definition term147 (x0 : nat) := ((fun y0 : nat => (y0 = (NUMERAL 0)) /\ (~ ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))))) x0) \/ ((fun y0 : nat => (~ (y0 = (NUMERAL 0))) /\ (~ ((real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))))) x0).
Definition term101 (x0 : nat) := ((x0 = (NUMERAL 0)) = True) -> ((real_inv (@COND real (x0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) = (@COND real (x0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) = ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term118 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term56 (x0 : nat) := @eq real (real_inv (real_pow (real_of_num (NUMERAL 0)) x0)).
Definition term180 := exists y0 : nat, ((fun y1 : nat => ~ (y1 = (NUMERAL 0))) y0) /\ (~ ((real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0)))).
Definition term164 := exists y0 : nat, ((fun y1 : nat => y1 = (NUMERAL 0)) y0) /\ (~ ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0))))).
Definition term189 := @eq Prop (exists y0 : nat, (~ (y0 = (NUMERAL 0))) /\ (~ ((real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))))).
Definition term188 := @eq Prop (exists y0 : nat, ((fun y1 : nat => ~ (y1 = (NUMERAL 0))) y0) /\ (~ ((real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))))).
Definition term172 := @eq Prop (exists y0 : nat, (y0 = (NUMERAL 0)) /\ (~ ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))))).
Definition term171 := @eq Prop (exists y0 : nat, ((fun y1 : nat => y1 = (NUMERAL 0)) y0) /\ (~ ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))))).
Definition term150 := @eq Prop (exists y0 : nat, ((y0 = (NUMERAL 0)) /\ (~ ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))))) \/ ((~ (y0 = (NUMERAL 0))) /\ (~ ((real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0)))))).
Definition term149 := @eq Prop (exists y0 : nat, ((fun y1 : nat => (y1 = (NUMERAL 0)) /\ (~ ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))))) y0) \/ ((fun y1 : nat => (~ (y1 = (NUMERAL 0))) /\ (~ ((real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))))) y0)).
Definition term184 (x0 : nat) := and ((fun y0 : nat => ~ (y0 = (NUMERAL 0))) x0).
Definition term94 := @COND real False (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term49 (x0 : nat) := @eq real (real_pow (real_of_num (NUMERAL 0)) x0).
Definition term135 := exists y0 : nat, ((y0 = (NUMERAL 0)) /\ (~ ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))))) \/ ((~ (y0 = (NUMERAL 0))) /\ (~ ((real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))))).
Definition term132 (x0 : nat) := ~ ((fun y0 : nat => ((~ (y0 = (NUMERAL 0))) \/ ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0))))) /\ ((y0 = (NUMERAL 0)) \/ ((real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))))) x0).
Definition term14 (x0 : real) (x1 : int) := (fun y0 : int => (real_zpow x0 (int_neg y0)) = (real_inv (real_zpow x0 y0))) x1.
Definition term168 (x0 : nat) := and ((fun y0 : nat => y0 = (NUMERAL 0)) x0).
Definition term191 := exists y0 : nat, (fun y1 : nat => ~ (y1 = (NUMERAL 0))) y0.
Definition term29 := @eq Prop (forall y0 : int, (real_zpow (real_of_num (NUMERAL 0)) y0) = (@COND real (y0 = (int_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))).
Definition term205 := ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))) -> False.
Definition term8 (x0 : real) := (fun y0 : real => forall y1 : nat, (real_zpow y0 (int_of_num y1)) = (real_pow y0 y1)) x0.
Definition term183 (x0 : nat) := (fun y0 : nat => ~ (y0 = (NUMERAL 0))) x0.
Definition term89 := ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))) -> ((real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) -> False.
Definition term141 := (exists y0 : nat, (fun y1 : nat => (y1 = (NUMERAL 0)) /\ (~ ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))))) y0) \/ (exists y0 : nat, (fun y1 : nat => (~ (y1 = (NUMERAL 0))) /\ (~ ((real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))))) y0).
Definition term57 := fun y0 : nat => (real_inv (real_pow (real_of_num (NUMERAL 0)) y0)) = (@COND real ((int_neg (int_of_num y0)) = (int_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))).
Definition term45 := forall y0 : nat, (real_zpow (real_of_num (NUMERAL 0)) (int_neg (int_of_num y0))) = (@COND real ((int_neg (int_of_num y0)) = (int_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))).
Definition term36 := forall y0 : nat, (real_zpow (real_of_num (NUMERAL 0)) (int_of_num y0)) = (@COND real ((int_of_num y0) = (int_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))).
Definition term21 := (forall y0 : nat, (fun y1 : int => (real_zpow (real_of_num (NUMERAL 0)) y1) = (@COND real (y1 = (int_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) (int_of_num y0)) /\ (forall y0 : nat, (fun y1 : int => (real_zpow (real_of_num (NUMERAL 0)) y1) = (@COND real (y1 = (int_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) (int_neg (int_of_num y0))).
Definition term156 := fun y0 : nat => (fun y1 : nat => (~ (y1 = (NUMERAL 0))) /\ (~ ((real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))))) y0.
Definition term151 := fun y0 : nat => (fun y1 : nat => (y1 = (NUMERAL 0)) /\ (~ ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))))) y0.
Definition term142 := fun y0 : nat => (y0 = (NUMERAL 0)) /\ (~ ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0))))).
Definition term13 (x0 : real) := forall y0 : int, (real_zpow x0 (int_neg y0)) = (real_inv (real_zpow x0 y0)).
Definition term52 := and (forall y0 : nat, (real_pow (real_of_num (NUMERAL 0)) y0) = (@COND real ((int_of_num y0) = (int_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))).
Definition term38 := and (forall y0 : nat, (real_zpow (real_of_num (NUMERAL 0)) (int_of_num y0)) = (@COND real ((int_of_num y0) = (int_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))).
Definition term54 (x0 : nat) := real_inv (real_pow (real_of_num (NUMERAL 0)) x0).
Definition term134 := fun y0 : nat => ((y0 = (NUMERAL 0)) /\ (~ ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))))) \/ ((~ (y0 = (NUMERAL 0))) /\ (~ ((real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))))).
Definition term77 := True /\ (forall y0 : nat, (real_inv (@COND real (y0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) = (@COND real (y0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))).
Definition term120 (x0 : nat) := (~ (x0 = (NUMERAL 0))) /\ (~ ((real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0)))).
Definition term158 := exists y0 : nat, (~ (y0 = (NUMERAL 0))) /\ (~ ((real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0)))).
Definition term18 (x0 : int -> Prop) := forall y0 : int, x0 y0.
Definition term51 := forall y0 : nat, (real_pow (real_of_num (NUMERAL 0)) y0) = (@COND real ((int_of_num y0) = (int_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))).
Definition term30 (x0 : nat) := (fun y0 : int => (real_zpow (real_of_num (NUMERAL 0)) y0) = (@COND real (y0 = (int_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) (int_of_num x0).
Definition term82 := ((~ (forall y0 : nat, (real_inv (@COND real (y0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) = (@COND real (y0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))))) -> ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))) -> ((real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) -> False) -> (~ (forall y0 : nat, (real_inv (@COND real (y0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) = (@COND real (y0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))))) -> ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))) -> ((real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) -> False.
Definition term110 := (~ (forall y0 : nat, ((~ (y0 = (NUMERAL 0))) \/ ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0))))) /\ ((y0 = (NUMERAL 0)) \/ ((real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0)))))) -> ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))) -> ~ ((real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))).
Definition term92 := (~ (forall y0 : nat, (real_inv (@COND real (y0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) = (@COND real (y0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))))) -> ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))) -> ~ ((real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))).
Definition term31 (x0 : nat) := real_zpow (real_of_num (NUMERAL 0)) (int_of_num x0).
Definition term5 (x0 : nat) := (fun y0 : nat => (real_pow (real_of_num (NUMERAL 0)) y0) = (@COND real (y0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) x0.
Definition term160 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) /\ x1.
Definition term16 (x0 : real) (x1 : int) := real_inv (real_zpow x0 x1).
Definition term140 := exists y0 : nat, ((fun y1 : nat => (y1 = (NUMERAL 0)) /\ (~ ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))))) y0) \/ ((fun y1 : nat => (~ (y1 = (NUMERAL 0))) /\ (~ ((real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))))) y0).
Definition term67 := forall y0 : nat, True.
Definition term203 := (~ ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0))))) -> (real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0))).
Definition term23 (x0 : int) := (fun y0 : int => (real_zpow (real_of_num (NUMERAL 0)) y0) = (@COND real (y0 = (int_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) x0.
Definition term97 := @COND real True (real_of_num (NUMERAL (BIT1 0))).
Definition term37 := and (forall y0 : nat, (fun y1 : int => (real_zpow (real_of_num (NUMERAL 0)) y1) = (@COND real (y1 = (int_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) (int_of_num y0)).
Definition term66 := fun y0 : nat => True.
Definition term162 (x0 : nat -> Prop) (x1 : Prop) := exists y0 : nat, (x0 y0) /\ x1.
Definition term79 := (~ (forall y0 : nat, (real_inv (@COND real (y0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) = (@COND real (y0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))))) -> False.
Definition term145 (x0 : nat) := or ((fun y0 : nat => (y0 = (NUMERAL 0)) /\ (~ ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))))) x0).
Definition term192 := exists y0 : nat, ~ (y0 = (NUMERAL 0)).
Definition term153 := exists y0 : nat, (y0 = (NUMERAL 0)) /\ (~ ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0))))).
Definition term61 (x0 : nat) := @COND real ((int_of_num x0) = (int_of_num (NUMERAL 0))).
Definition term174 := exists y0 : nat, (fun y1 : nat => y1 = (NUMERAL 0)) y0.
Definition term157 := exists y0 : nat, (fun y1 : nat => (~ (y1 = (NUMERAL 0))) /\ (~ ((real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))))) y0.
Definition term152 := exists y0 : nat, (fun y1 : nat => (y1 = (NUMERAL 0)) /\ (~ ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))))) y0.
Definition term22 := fun y0 : int => (real_zpow (real_of_num (NUMERAL 0)) y0) = (@COND real (y0 = (int_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))).
Definition term84 := (((~ (forall y0 : nat, (real_inv (@COND real (y0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) = (@COND real (y0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))))) -> ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))) -> ((real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) -> False) -> (~ (forall y0 : nat, (real_inv (@COND real (y0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) = (@COND real (y0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))))) -> ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))) -> ((real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) -> False) -> ((~ (forall y0 : nat, (real_inv (@COND real (y0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) = (@COND real (y0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))))) -> ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))) -> ((real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) -> False) -> (~ (forall y0 : nat, (real_inv (@COND real (y0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) = (@COND real (y0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))))) -> ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))) -> ((real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) -> False.
Definition term126 (x0 : nat) := (~ (x0 = (NUMERAL 0))) \/ ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term185 (x0 : nat) := and (~ (x0 = (NUMERAL 0))).
Definition term43 := fun y0 : nat => (real_zpow (real_of_num (NUMERAL 0)) (int_neg (int_of_num y0))) = (@COND real ((int_neg (int_of_num y0)) = (int_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))).
Definition term143 := fun y0 : nat => (~ (y0 = (NUMERAL 0))) /\ (~ ((real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0)))).
Definition term28 := @eq Prop (forall y0 : int, (fun y1 : int => (real_zpow (real_of_num (NUMERAL 0)) y1) = (@COND real (y1 = (int_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) y0).
Definition term167 (x0 : nat) := (fun y0 : nat => y0 = (NUMERAL 0)) x0.
Definition term112 := ~ ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term179 := or ((exists y0 : nat, y0 = (NUMERAL 0)) /\ (~ ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))))).
Definition term59 := (forall y0 : nat, (real_pow (real_of_num (NUMERAL 0)) y0) = (@COND real ((int_of_num y0) = (int_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) /\ (forall y0 : nat, (real_inv (real_pow (real_of_num (NUMERAL 0)) y0)) = (@COND real ((int_neg (int_of_num y0)) = (int_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))).
Definition term46 := (forall y0 : nat, (real_zpow (real_of_num (NUMERAL 0)) (int_of_num y0)) = (@COND real ((int_of_num y0) = (int_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) /\ (forall y0 : nat, (real_zpow (real_of_num (NUMERAL 0)) (int_neg (int_of_num y0))) = (@COND real ((int_neg (int_of_num y0)) = (int_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))).
Definition term181 := (exists y0 : nat, (fun y1 : nat => ~ (y1 = (NUMERAL 0))) y0) /\ (~ ((real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0)))).
Definition term104 (x0 : nat) := ((((x0 = (NUMERAL 0)) = False) -> ((real_inv (@COND real (x0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) = (@COND real (x0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) = ((real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0)))) /\ (((x0 = (NUMERAL 0)) = True) -> ((real_inv (@COND real (x0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) = (@COND real (x0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) = ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))))) -> ((real_inv (@COND real (x0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) = (@COND real (x0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) = (((~ (x0 = (NUMERAL 0))) \/ ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0))))) /\ ((x0 = (NUMERAL 0)) \/ ((real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))))).
Definition term102 (x0 : nat) := (((x0 = (NUMERAL 0)) = False) -> ((real_inv (@COND real (x0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) = (@COND real (x0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) = ((real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0)))) /\ (((x0 = (NUMERAL 0)) = True) -> ((real_inv (@COND real (x0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) = (@COND real (x0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) = ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0))))).
Definition term163 (x0 : nat -> Prop) (x1 : Prop) := (exists y0 : nat, x0 y0) /\ x1.
Definition term10 (x0 : real) (x1 : nat) := (fun y0 : nat => (real_zpow x0 (int_of_num y0)) = (real_pow x0 y0)) x1.
Definition term103 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (((x2 = False) -> x0 = x3) /\ ((x2 = True) -> x0 = x1)) -> x0 = (((~ x2) \/ x1) /\ (x2 \/ x3)).
Definition term53 (x0 : nat) := real_inv (real_zpow (real_of_num (NUMERAL 0)) (int_of_num x0)).
Definition term72 (x0 : nat) := int_neg (int_of_num x0).
Definition term207 := (~ ((real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0)))) -> (real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0)).
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((int_of_num y0) = (int_of_num y1)) = (y0 = y1)) x0.
Definition term39 (x0 : nat) := (fun y0 : int => (real_zpow (real_of_num (NUMERAL 0)) y0) = (@COND real (y0 = (int_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) (int_neg (int_of_num x0)).
Definition term121 (x0 : nat) := or (~ ((~ (x0 = (NUMERAL 0))) \/ ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))))).
Definition term125 (x0 : nat) := ~ (((~ (x0 = (NUMERAL 0))) \/ ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0))))) /\ ((x0 = (NUMERAL 0)) \/ ((real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))))).
Definition term200 := @eq Prop ((exists y0 : nat, ~ (y0 = (NUMERAL 0))) /\ (~ ((real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))))).
Definition term199 := @eq Prop ((exists y0 : nat, (fun y1 : nat => ~ (y1 = (NUMERAL 0))) y0) /\ (~ ((real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))))).
Definition term198 := @eq Prop ((exists y0 : nat, y0 = (NUMERAL 0)) /\ (~ ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))))).
Definition term197 := @eq Prop ((exists y0 : nat, (fun y1 : nat => y1 = (NUMERAL 0)) y0) /\ (~ ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))))).
Definition term26 := fun y0 : int => (fun y1 : int => (real_zpow (real_of_num (NUMERAL 0)) y1) = (@COND real (y1 = (int_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) y0.
Definition term35 := forall y0 : nat, (fun y1 : int => (real_zpow (real_of_num (NUMERAL 0)) y1) = (@COND real (y1 = (int_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) (int_of_num y0).
Definition term177 := and (exists y0 : nat, y0 = (NUMERAL 0)).
Definition term173 := fun y0 : nat => (fun y1 : nat => y1 = (NUMERAL 0)) y0.
Definition term75 := fun y0 : nat => (real_inv (@COND real (y0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) = (@COND real (y0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))).
Definition term74 (x0 : nat) := @COND real ((int_neg (int_of_num x0)) = (int_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term27 := forall y0 : int, (real_zpow (real_of_num (NUMERAL 0)) y0) = (@COND real (y0 = (int_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))).
Definition term63 := real_of_num (NUMERAL (BIT1 0)).
Definition term93 := @COND real False (real_of_num (NUMERAL (BIT1 0))).
Definition term99 := real_inv (real_of_num (NUMERAL (BIT1 0))).
Definition term130 := exists y0 : nat, ~ ((fun y1 : nat => ((~ (y1 = (NUMERAL 0))) \/ ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0))))) /\ ((y1 = (NUMERAL 0)) \/ ((real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))))) y0).
Definition term12 (x0 : real) := (fun y0 : real => forall y1 : int, (real_zpow y0 (int_neg y1)) = (real_inv (real_zpow y0 y1))) x0.
Definition term170 := fun y0 : nat => ((fun y1 : nat => y1 = (NUMERAL 0)) y0) /\ (~ ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0))))).
Definition term41 (x0 : nat) := @COND real ((int_neg (int_of_num x0)) = (int_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term32 (x0 : nat) := @COND real ((int_of_num x0) = (int_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term11 (x0 : real) (x1 : nat) := real_zpow x0 (int_of_num x1).
Definition term190 := fun y0 : nat => (fun y1 : nat => ~ (y1 = (NUMERAL 0))) y0.
Definition term196 := ((exists y0 : nat, y0 = (NUMERAL 0)) /\ (~ ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))))) \/ ((exists y0 : nat, ~ (y0 = (NUMERAL 0))) /\ (~ ((real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))))).
Definition term69 (x0 : Prop) := forall y0 : nat, x0.
Definition term138 (x0 : nat -> Prop) (x1 : nat -> Prop) := exists y0 : nat, (x0 y0) \/ (x1 y0).
Definition term187 := fun y0 : nat => ((fun y1 : nat => ~ (y1 = (NUMERAL 0))) y0) /\ (~ ((real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0)))).
Definition term166 := fun y0 : nat => y0 = (NUMERAL 0).
Definition term44 := forall y0 : nat, (fun y1 : int => (real_zpow (real_of_num (NUMERAL 0)) y1) = (@COND real (y1 = (int_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) (int_neg (int_of_num y0)).
Definition term133 := fun y0 : nat => ~ ((fun y1 : nat => ((~ (y1 = (NUMERAL 0))) \/ ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0))))) /\ ((y1 = (NUMERAL 0)) \/ ((real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))))) y0).
Definition term127 (x0 : nat) := (x0 = (NUMERAL 0)) \/ ((real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))).
Definition term34 := fun y0 : nat => (real_zpow (real_of_num (NUMERAL 0)) (int_of_num y0)) = (@COND real ((int_of_num y0) = (int_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))).
Definition term76 := forall y0 : nat, (real_inv (@COND real (y0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) = (@COND real (y0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))).
Definition term58 := forall y0 : nat, (real_inv (real_pow (real_of_num (NUMERAL 0)) y0)) = (@COND real ((int_neg (int_of_num y0)) = (int_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))).
Definition term161 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) /\ x1.
Definition term148 := fun y0 : nat => ((fun y1 : nat => (y1 = (NUMERAL 0)) /\ (~ ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))))) y0) \/ ((fun y1 : nat => (~ (y1 = (NUMERAL 0))) /\ (~ ((real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))))) y0).
Definition term6 (x0 : nat) := real_pow (real_of_num (NUMERAL 0)) x0.
Definition term85 := ((real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) -> False.
Definition term154 := or (exists y0 : nat, (fun y1 : nat => (y1 = (NUMERAL 0)) /\ (~ ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))))) y0).
Definition term111 (x0 : nat) := ~ (~ (x0 = (NUMERAL 0))).
Definition term106 := fun y0 : nat => ((~ (y0 = (NUMERAL 0))) \/ ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0))))) /\ ((y0 = (NUMERAL 0)) \/ ((real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0)))).
Definition term178 := (exists y0 : nat, y0 = (NUMERAL 0)) /\ (~ ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0))))).
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((int_of_num x0) = (int_of_num y0)) = (x0 = y0)) x1.
Definition term88 := imp ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term116 (x0 : nat) := (x0 = (NUMERAL 0)) /\ (~ ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0))))).
Definition term100 := @eq real (real_inv (real_of_num (NUMERAL (BIT1 0)))).
Definition term136 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term129 (x0 : nat -> Prop) := exists y0 : nat, ~ (x0 y0).
Definition term20 := forall y0 : int, (fun y1 : int => (real_zpow (real_of_num (NUMERAL 0)) y1) = (@COND real (y1 = (int_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) y0.
Definition term42 := fun y0 : nat => (fun y1 : int => (real_zpow (real_of_num (NUMERAL 0)) y1) = (@COND real (y1 = (int_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) (int_neg (int_of_num y0)).
Definition term165 := (exists y0 : nat, (fun y1 : nat => y1 = (NUMERAL 0)) y0) /\ (~ ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0))))).
Definition term139 (x0 : nat -> Prop) (x1 : nat -> Prop) := (exists y0 : nat, x0 y0) \/ (exists y0 : nat, x1 y0).
Definition term107 := forall y0 : nat, ((~ (y0 = (NUMERAL 0))) \/ ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0))))) /\ ((y0 = (NUMERAL 0)) \/ ((real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0)))).
Definition term60 (x0 : nat) := @eq real (@COND real (x0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))).
Definition term109 := imp (~ (forall y0 : nat, ((~ (y0 = (NUMERAL 0))) \/ ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0))))) /\ ((y0 = (NUMERAL 0)) \/ ((real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0)))))).
Definition term91 := imp (~ (forall y0 : nat, (real_inv (@COND real (y0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) = (@COND real (y0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))))).
Definition term124 (x0 : nat) := ((x0 = (NUMERAL 0)) /\ (~ ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))))) \/ ((~ (x0 = (NUMERAL 0))) /\ (~ ((real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))))).
Definition term83 := (((~ (forall y0 : nat, (real_inv (@COND real (y0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) = (@COND real (y0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))))) -> ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))) -> ((real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) -> False) -> (~ (forall y0 : nat, (real_inv (@COND real (y0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) = (@COND real (y0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))))) -> ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))) -> ((real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) -> False) -> (~ (forall y0 : nat, (real_inv (@COND real (y0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) = (@COND real (y0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))))) -> ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))) -> ((real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) -> False.
Definition term202 := @eq Prop ((exists y0 : nat, (y0 = (NUMERAL 0)) /\ (~ ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))))) \/ (exists y0 : nat, (~ (y0 = (NUMERAL 0))) /\ (~ ((real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0)))))).
Definition term201 := @eq Prop ((exists y0 : nat, (fun y1 : nat => (y1 = (NUMERAL 0)) /\ (~ ((real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))))) y0) \/ (exists y0 : nat, (fun y1 : nat => (~ (y1 = (NUMERAL 0))) /\ (~ ((real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))))) y0)).
