Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term258 (x0 : real) (x1 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1).
Definition term170 (x0 : real) (x1 : nat) := real_gt (real_sub (real_neg (real_pow x0 x1)) (real_of_num (NUMERAL 0))).
Definition term121 (x0 : real) (x1 : real) (x2 : nat) := (real_lt (real_of_num (NUMERAL 0)) (real_pow (real_neg x0) x2)) /\ (real_le (real_of_num (NUMERAL 0)) (real_pow x1 x2)).
Definition term156 (x0 : real) (x1 : real) (x2 : nat) := ((real_lt (real_of_num (NUMERAL 0)) (real_neg (real_pow x0 x2))) /\ (real_le (real_of_num (NUMERAL 0)) (real_pow x1 x2))) -> real_lt (real_pow x0 x2) (real_pow x1 x2).
Definition term155 (x0 : real) (x1 : real) (x2 : nat) := ((real_lt (real_of_num (NUMERAL 0)) (real_pow (real_neg x0) x2)) /\ (real_le (real_of_num (NUMERAL 0)) (real_pow x1 x2))) -> real_lt (real_pow x0 x2) (real_pow x1 x2).
Definition term328 (x0 : real) (x1 : nat) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 x1)).
Definition term84 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term162 (x0 : real) (x1 : nat) := real_sub (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 x1)).
Definition term184 (x0 : real) (x1 : real) (x2 : nat) := real_ge (real_sub (real_pow x0 x2) (real_pow x1 x2)) (real_of_num (NUMERAL 0)).
Definition term78 (x0 : real) := ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0)))) -> real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0) (real_of_num (NUMERAL 0)).
Definition term49 := Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0))).
Definition term189 (x0 : real) (x1 : real) (x2 : nat) := real_ge (real_add (real_pow x0 x2) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 x2))) (real_of_num (NUMERAL 0)).
Definition term265 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term74 (x0 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_of_num (NUMERAL 0)).
Definition term66 (x0 : real) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0))).
Definition term324 (x0 : real) (x1 : real) (x2 : nat) := real_gt (real_sub (real_neg (real_pow x0 x2)) (real_neg (real_pow x1 x2))) (real_of_num (NUMERAL 0)).
Definition term6 (x0 : nat) := (fun y0 : nat => forall y1 : real, forall y2 : real, ((~ (y0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_lt y1 y2))) -> real_lt (real_pow y1 y0) (real_pow y2 y0)) x0.
Definition term235 (x0 : real) (x1 : real) (x2 : nat) := imp (real_lt (real_pow (real_neg x0) x2) (real_pow (real_neg x1) x2)).
Definition term3 := forall y0 : nat, (~ (Coq.Arith.PeanoNat.Nat.Odd y0)) = (Coq.Arith.PeanoNat.Nat.Even y0).
Definition term146 (x0 : real) (x1 : nat) := @COND real False (real_pow x0 x1).
Definition term272 (x0 : real) (x1 : real) := real_ge (real_sub (real_neg x0) (real_neg x1)) (real_of_num (NUMERAL 0)).
Definition term28 := real_of_num (NUMERAL 0).
Definition term93 (x0 : real) := (real_le (real_of_num (NUMERAL 0)) x0) \/ (real_lt (real_of_num (NUMERAL 0)) (real_neg x0)).
Definition term95 (x0 : real) := (real_le (real_of_num (NUMERAL 0)) x0) \/ (real_le (real_of_num (NUMERAL 0)) (real_neg x0)).
Definition term164 (x0 : real) (x1 : nat) := real_sub (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 x1)) (real_of_num (NUMERAL 0)).
Definition term271 (x0 : real) (x1 : real) := ~ (real_lt (real_neg x0) (real_neg x1)).
Definition term163 (x0 : real) (x1 : nat) := real_sub (real_neg (real_pow x0 x1)) (real_of_num (NUMERAL 0)).
Definition term308 (x0 : real) (x1 : real) (x2 : nat) := (real_lt (real_neg (real_pow x1 x2)) (real_neg (real_pow x0 x2))) /\ (~ (real_lt (real_pow x0 x2) (real_pow x1 x2))).
Definition term148 (x0 : real) (x1 : nat) := @COND real False (real_pow x0 x1) (real_neg (real_pow x0 x1)).
Definition term57 (x0 : real) := real_ge (real_sub (real_of_num (NUMERAL 0)) (real_neg x0)).
Definition term350 (x0 : real) (x1 : nat) := real_add (real_pow x0 x1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 x1)).
Definition term187 (x0 : real) (x1 : real) (x2 : nat) := real_ge (real_sub (real_pow x0 x2) (real_pow x1 x2)).
Definition term292 (x0 : real) (x1 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1)) (real_of_num (NUMERAL 0)).
Definition term287 (x0 : real) (x1 : real) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1))) (real_of_num (NUMERAL 0)).
Definition term229 (x0 : real) (x1 : real) := (real_le (real_of_num (NUMERAL 0)) (real_neg x0)) /\ (real_lt (real_neg x0) (real_neg x1)).
Definition term251 (x0 : nat) (x1 : real) (x2 : real) := (~ (x0 = (NUMERAL 0))) /\ ((real_lt x2 x1) /\ ((Coq.Arith.PeanoNat.Nat.Odd x0) /\ ((real_le (real_of_num (NUMERAL 0)) (real_neg x1)) /\ (~ (real_lt (real_neg x1) (real_neg x2)))))).
Definition term325 (x0 : real) (x1 : real) (x2 : nat) := real_sub (real_neg (real_pow x0 x2)) (real_neg (real_pow x1 x2)).
Definition term334 (x0 : real) (x1 : real) (x2 : nat) := and (real_lt (real_neg (real_pow x0 x2)) (real_neg (real_pow x1 x2))).
Definition term343 (x0 : real) (x1 : real) (x2 : nat) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 x2)) (real_pow x1 x2))) (real_of_num (NUMERAL 0)).
Definition term205 (x0 : real) (x1 : nat) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 x1))) (real_of_num (NUMERAL 0)).
Definition term131 (x0 : real) (x1 : nat) := (real_le (real_of_num (NUMERAL 0)) x0) -> real_le (real_of_num (NUMERAL 0)) (real_pow x0 x1).
Definition term2 := fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even y0) = (~ (Coq.Arith.PeanoNat.Nat.Odd y0)).
Definition term282 (x0 : real) (x1 : real) := and (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))).
Definition term18 := (forall y0 : nat, forall y1 : real, forall y2 : real, ((~ (y0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_lt y1 y2))) -> real_lt (real_pow y1 y0) (real_pow y2 y0)) -> forall y0 : real, forall y1 : real, forall y2 : nat, ((~ (y2 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 y1))) -> real_lt (real_pow y0 y2) (real_pow y1 y2).
Definition term261 (x0 : real) := real_sub (real_neg x0).
Definition term247 (x0 : nat) (x1 : real) (x2 : real) := (real_lt x2 x1) /\ ((Coq.Arith.PeanoNat.Nat.Odd x0) /\ ((real_le (real_of_num (NUMERAL 0)) (real_neg x1)) /\ (~ (real_lt (real_neg x1) (real_neg x2))))).
Definition term352 (x0 : real) (x1 : real) (x2 : nat) := (~ ((~ (x2 = (NUMERAL 0))) -> (real_lt x0 x1) -> (Coq.Arith.PeanoNat.Nat.Odd x2) -> (real_le (real_of_num (NUMERAL 0)) (real_neg x1)) -> (real_lt (real_neg (real_pow x1 x2)) (real_neg (real_pow x0 x2))) -> real_lt (real_pow x0 x2) (real_pow x1 x2))) -> False.
Definition term304 (x0 : nat) (x1 : real) (x2 : real) := (~ ((~ (x0 = (NUMERAL 0))) -> (real_lt x2 x1) -> (Coq.Arith.PeanoNat.Nat.Odd x0) -> (real_le (real_of_num (NUMERAL 0)) (real_neg x1)) -> real_lt (real_neg x1) (real_neg x2))) -> False.
Definition term223 (x0 : real) (x1 : real) (x2 : nat) := (~ (((real_lt (real_of_num (NUMERAL 0)) (real_neg (real_pow x0 x2))) /\ (real_le (real_of_num (NUMERAL 0)) (real_pow x1 x2))) -> real_lt (real_pow x0 x2) (real_pow x1 x2))) -> False.
Definition term91 (x0 : real) := (~ ((real_le (real_of_num (NUMERAL 0)) x0) \/ (real_lt (real_of_num (NUMERAL 0)) (real_neg x0)))) -> False.
Definition term219 (x0 : real) (x1 : nat) := (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 x1)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_pow x0 x1) (real_of_num (NUMERAL 0))).
Definition term268 (x0 : real) := real_ge (real_sub (real_neg x0) (real_of_num (NUMERAL 0))).
Definition term270 (x0 : real) := real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)).
Definition term69 (x0 : real) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) x0) (real_of_num (NUMERAL 0)).
Definition term173 (x0 : real) (x1 : nat) := real_ge (real_sub (real_pow x0 x1) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term331 (x0 : real) (x1 : real) (x2 : nat) := real_gt (real_sub (real_neg (real_pow x0 x2)) (real_neg (real_pow x1 x2))).
Definition term27 (x0 : real) := real_gt (real_sub (real_of_num (NUMERAL 0)) x0) (real_of_num (NUMERAL 0)).
Definition term321 (x0 : real) (x1 : real) (x2 : nat) := (~ (x2 = (NUMERAL 0))) /\ ((real_lt x0 x1) /\ ((Coq.Arith.PeanoNat.Nat.Odd x2) /\ ((real_le (real_of_num (NUMERAL 0)) (real_neg x1)) /\ ((real_lt (real_neg (real_pow x1 x2)) (real_neg (real_pow x0 x2))) /\ (~ (real_lt (real_pow x0 x2) (real_pow x1 x2))))))).
Definition term253 (x0 : nat) (x1 : real) (x2 : real) := (real_lt x2 x1) -> (Coq.Arith.PeanoNat.Nat.Odd x0) -> (real_le (real_of_num (NUMERAL 0)) (real_neg x1)) -> real_lt (real_neg x1) (real_neg x2).
Definition term172 (x0 : real) (x1 : nat) := real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 x1)) (real_of_num (NUMERAL 0)).
Definition term218 (x0 : real) (x1 : real) (x2 : nat) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 x2)) (real_add (real_pow x0 x2) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 x2)))).
Definition term58 (x0 : real) := real_ge x0 (real_of_num (NUMERAL 0)).
Definition term215 (x0 : real) (x1 : nat) := real_mul (real_of_num (NUMERAL 0)) (real_pow x0 x1).
Definition term174 (x0 : real) (x1 : nat) := real_sub (real_pow x0 x1) (real_of_num (NUMERAL 0)).
Definition term312 (x0 : real) (x1 : real) (x2 : nat) := (Coq.Arith.PeanoNat.Nat.Odd x2) /\ (~ ((real_le (real_of_num (NUMERAL 0)) (real_neg x1)) -> (real_lt (real_neg (real_pow x1 x2)) (real_neg (real_pow x0 x2))) -> real_lt (real_pow x0 x2) (real_pow x1 x2))).
Definition term96 (x0 : real) := real_le (real_of_num (NUMERAL 0)) (real_neg x0).
Definition term217 (x0 : real) (x1 : nat) := real_add (real_of_num (NUMERAL 0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 x1)).
Definition term238 (x0 : real) (x1 : real) (x2 : nat) := (real_lt (real_neg (real_pow x1 x2)) (real_neg (real_pow x0 x2))) -> real_lt (real_pow x0 x2) (real_pow x1 x2).
Definition term101 := ((Coq.Arith.PeanoNat.Nat.Odd 0) = False) /\ ((forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Odd (BIT0 y0)) = False) /\ (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Odd (BIT1 y0)) = True)).
Definition term262 (x0 : real) := real_sub (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term160 (x0 : real) (x1 : nat) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 x1).
Definition term267 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)).
Definition term234 (x0 : real) (x1 : real) (x2 : nat) := real_lt (real_neg (real_pow x0 x2)) (real_neg (real_pow x1 x2)).
Definition term256 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1.
Definition term201 (x0 : real) (x1 : real) (x2 : nat) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_pow x0 x2) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 x2))).
Definition term211 (x0 : real) (x1 : real) (x2 : nat) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 x2)) (real_add (real_pow x0 x2) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 x2))).
Definition term309 (x0 : real) (x1 : real) (x2 : nat) := (real_le (real_of_num (NUMERAL 0)) (real_neg x1)) /\ (~ ((real_lt (real_neg (real_pow x1 x2)) (real_neg (real_pow x0 x2))) -> real_lt (real_pow x0 x2) (real_pow x1 x2))).
Definition term200 (x0 : real) (x1 : real) (x2 : nat) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_pow x0 x2) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 x2)))) (real_of_num (NUMERAL 0)).
Definition term221 (x0 : real) (x1 : nat) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 x1)) (real_pow x0 x1)) (real_of_num (NUMERAL 0)).
Definition term59 (x0 : real) := and (~ (real_le (real_of_num (NUMERAL 0)) x0)).
Definition term110 (x0 : real) := real_pow x0 (NUMERAL 0).
Definition term147 (x0 : real) (x1 : nat) := real_neg (real_pow x0 x1).
Definition term138 (x0 : nat) := (fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even y0) = (~ (Coq.Arith.PeanoNat.Nat.Odd y0))) x0.
Definition term26 (x0 : real) := ~ (real_le (real_of_num (NUMERAL 0)) x0).
Definition term154 (x0 : real) (x1 : real) (x2 : nat) := imp ((real_lt (real_of_num (NUMERAL 0)) (real_neg (real_pow x0 x2))) /\ (real_le (real_of_num (NUMERAL 0)) (real_pow x1 x2))).
Definition term224 (x0 : real) (x1 : real) (x2 : nat) := ((~ (((real_lt (real_of_num (NUMERAL 0)) (real_neg (real_pow x0 x2))) /\ (real_le (real_of_num (NUMERAL 0)) (real_pow x1 x2))) -> real_lt (real_pow x0 x2) (real_pow x1 x2))) -> False) -> ((real_lt (real_of_num (NUMERAL 0)) (real_neg (real_pow x0 x2))) /\ (real_le (real_of_num (NUMERAL 0)) (real_pow x1 x2))) -> real_lt (real_pow x0 x2) (real_pow x1 x2).
Definition term64 := Peano.lt (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term32 (x0 : real) := real_gt (real_sub (real_of_num (NUMERAL 0)) x0).
Definition term166 (x0 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num (NUMERAL 0)).
Definition term356 (x0 : nat) := forall y0 : real, forall y1 : real, ((real_lt y0 y1) /\ (Coq.Arith.PeanoNat.Nat.Odd x0)) -> real_lt (real_pow y0 x0) (real_pow y1 x0).
Definition term17 := forall y0 : real, forall y1 : real, forall y2 : nat, ((~ (y2 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 y1))) -> real_lt (real_pow y0 y2) (real_pow y1 y2).
Definition term16 (x0 : real) := forall y0 : real, forall y1 : nat, ((~ (y1 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_lt x0 y0))) -> real_lt (real_pow x0 y1) (real_pow y0 y1).
Definition term7 (x0 : nat) := forall y0 : real, forall y1 : real, ((~ (x0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 y1))) -> real_lt (real_pow y0 x0) (real_pow y1 x0).
Definition term177 (x0 : real) (x1 : nat) := real_add (real_pow x0 x1) (real_of_num (NUMERAL 0)).
Definition term41 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term300 (x0 : real) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0).
Definition term135 (x0 : real) (x1 : nat) := real_lt (real_of_num (NUMERAL 0)) (real_pow (real_neg x0) x1).
Definition term46 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term239 (x0 : real) (x1 : real) := ~ ((real_le (real_of_num (NUMERAL 0)) (real_neg x0)) -> real_lt (real_neg x0) (real_neg x1)).
Definition term120 (x0 : real) (x1 : real) := (real_le (real_of_num (NUMERAL 0)) x0) /\ (real_lt x0 x1).
Definition term276 (x0 : real) (x1 : real) := real_ge (real_sub (real_neg x0) (real_neg x1)).
Definition term338 (x0 : real) (x1 : real) (x2 : nat) := (Coq.Arith.PeanoNat.Nat.Odd x2) /\ ((real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_of_num (NUMERAL 0))) /\ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 x2)) (real_pow x1 x2)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_pow x0 x2) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 x2))) (real_of_num (NUMERAL 0))))).
Definition term288 (x0 : real) (x1 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term157 (x0 : real) (x1 : real) (x2 : nat) := ~ (((real_lt (real_of_num (NUMERAL 0)) (real_neg (real_pow x0 x2))) /\ (real_le (real_of_num (NUMERAL 0)) (real_pow x1 x2))) -> real_lt (real_pow x0 x2) (real_pow x1 x2)).
Definition term216 (x0 : real) (x1 : nat) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 x1)) (real_pow x0 x1)).
Definition term279 (x0 : real) := and (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))).
Definition term182 (x0 : real) (x1 : real) (x2 : nat) := (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 x2)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_pow x1 x2) (real_of_num (NUMERAL 0))).
Definition term337 (x0 : real) (x1 : real) (x2 : nat) := (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_of_num (NUMERAL 0))) /\ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 x2)) (real_pow x1 x2)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_pow x0 x2) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 x2))) (real_of_num (NUMERAL 0)))).
Definition term297 (x0 : real) (x1 : real) := real_gt (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1))) (real_of_num (NUMERAL 0)).
Definition term75 (x0 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term355 (x0 : real) (x1 : nat) := forall y0 : real, ((real_lt x0 y0) /\ (Coq.Arith.PeanoNat.Nat.Odd x1)) -> real_lt (real_pow x0 x1) (real_pow y0 x1).
Definition term9 (x0 : real) (x1 : nat) := forall y0 : real, ((~ (x1 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_lt x0 y0))) -> real_lt (real_pow x0 x1) (real_pow y0 x1).
Definition term99 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term263 (x0 : real) := real_sub (real_neg x0) (real_of_num (NUMERAL 0)).
Definition term133 (x0 : real) (x1 : nat) := (real_lt (real_of_num (NUMERAL 0)) x0) -> (real_lt (real_of_num (NUMERAL 0)) (real_pow x0 x1)) = True.
Definition term132 (x0 : real) (x1 : nat) := real_le (real_of_num (NUMERAL 0)) (real_pow x0 x1).
Definition term125 (x0 : real) (x1 : nat) := (real_lt (real_of_num (NUMERAL 0)) x0) -> real_lt (real_of_num (NUMERAL 0)) (real_pow x0 x1).
Definition term214 (x0 : real) (x1 : nat) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 x1).
Definition term106 (x0 : real) (x1 : real) := and (real_lt x0 x1).
Definition term149 := real_lt (real_of_num (NUMERAL 0)).
Definition term179 (x0 : real) (x1 : nat) := real_ge (real_pow x0 x1).
Definition term192 (x0 : real) (x1 : real) (x2 : nat) := ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 x2)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_pow x1 x2) (real_of_num (NUMERAL 0)))) /\ (real_ge (real_add (real_pow x0 x2) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 x2))) (real_of_num (NUMERAL 0))).
Definition term178 (x0 : real) (x1 : nat) := real_ge (real_sub (real_pow x0 x1) (real_of_num (NUMERAL 0))).
Definition term315 (x0 : real) (x1 : real) (x2 : nat) := (real_le (real_of_num (NUMERAL 0)) (real_neg x1)) -> (real_lt (real_neg (real_pow x1 x2)) (real_neg (real_pow x0 x2))) -> real_lt (real_pow x0 x2) (real_pow x1 x2).
Definition term36 (x0 : real) := real_ge (real_sub (real_of_num (NUMERAL 0)) (real_neg x0)) (real_of_num (NUMERAL 0)).
Definition term119 (x0 : real) := and (real_le (real_of_num (NUMERAL 0)) x0).
Definition term198 (x0 : real) (x1 : real) (x2 : nat) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_pow x0 x2) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 x2))) (real_of_num (NUMERAL 0))).
Definition term280 (x0 : real) (x1 : real) := (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))).
Definition term349 (x0 : real) (x1 : real) (x2 : nat) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 x2)) (real_pow x0 x2)) (real_add (real_pow x1 x2) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 x2))).
Definition term348 (x0 : real) (x1 : real) (x2 : nat) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 x2)) (real_pow x1 x2)) (real_add (real_pow x0 x2) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 x2))).
Definition term351 (x0 : real) (x1 : real) (x2 : nat) := real_gt (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 x2)) (real_pow x1 x2)) (real_add (real_pow x0 x2) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 x2)))).
Definition term332 (x0 : real) (x1 : real) (x2 : nat) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 x2)) (real_pow x1 x2)).
Definition term207 (x0 : real) (x1 : nat) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 x1))).
Definition term283 (x0 : nat) (x1 : real) (x2 : real) := (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2) (real_of_num (NUMERAL 0))) /\ ((Coq.Arith.PeanoNat.Nat.Odd x0) /\ ((real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2)) (real_of_num (NUMERAL 0))))).
Definition term139 (x0 : real) := (fun y0 : real => forall y1 : nat, (real_pow (real_neg y0) y1) = (@COND real (Coq.Arith.PeanoNat.Nat.Even y1) (real_pow y0 y1) (real_neg (real_pow y0 y1)))) x0.
Definition term128 (x0 : real) := (fun y0 : real => forall y1 : nat, (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (real_pow y0 y1)) x0.
Definition term122 (x0 : real) := (fun y0 : real => forall y1 : nat, (real_lt (real_of_num (NUMERAL 0)) y0) -> real_lt (real_of_num (NUMERAL 0)) (real_pow y0 y1)) x0.
Definition term278 (x0 : real) (x1 : real) := real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0)).
Definition term4 := forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even y0) = (~ (Coq.Arith.PeanoNat.Nat.Odd y0)).
Definition term129 (x0 : real) := forall y0 : nat, (real_le (real_of_num (NUMERAL 0)) x0) -> real_le (real_of_num (NUMERAL 0)) (real_pow x0 y0).
Definition term123 (x0 : real) := forall y0 : nat, (real_lt (real_of_num (NUMERAL 0)) x0) -> real_lt (real_of_num (NUMERAL 0)) (real_pow x0 y0).
Definition term212 (x0 : real) (x1 : real) (x2 : nat) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 x2)) (real_pow x0 x2)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 x2)).
Definition term82 (x0 : nat) := real_add (real_neg (real_of_num x0)) (real_of_num x0).
Definition term50 := Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term176 (x0 : real) (x1 : nat) := real_add (real_pow x0 x1).
Definition term183 (x0 : real) (x1 : real) (x2 : nat) := ~ (real_lt (real_pow x0 x2) (real_pow x1 x2)).
Definition term117 (x0 : real) (x1 : real) (x2 : nat) := ((~ (x2 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_lt x0 x1))) -> (real_lt (real_pow x0 x2) (real_pow x1 x2)) = True.
Definition term158 (x0 : real) (x1 : real) (x2 : nat) := ((real_lt (real_of_num (NUMERAL 0)) (real_neg (real_pow x0 x2))) /\ (real_le (real_of_num (NUMERAL 0)) (real_pow x1 x2))) /\ (~ (real_lt (real_pow x0 x2) (real_pow x1 x2))).
Definition term186 (x0 : real) (x1 : real) (x2 : nat) := real_add (real_pow x0 x2) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 x2)).
Definition term109 (x0 : real) (x1 : real) (x2 : nat) := imp ((real_lt x0 x1) /\ (Coq.Arith.PeanoNat.Nat.Odd x2)).
Definition term103 (x0 : nat) := (fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Odd (NUMERAL y0)) = (Coq.Arith.PeanoNat.Nat.Odd y0)) x0.
Definition term90 := Peano.lt (NUMERAL 0) (NUMERAL 0).
Definition term167 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term310 (x0 : real) (x1 : real) (x2 : nat) := (real_le (real_of_num (NUMERAL 0)) (real_neg x1)) /\ ((real_lt (real_neg (real_pow x1 x2)) (real_neg (real_pow x0 x2))) /\ (~ (real_lt (real_pow x0 x2) (real_pow x1 x2)))).
Definition term102 := forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Odd (NUMERAL y0)) = (Coq.Arith.PeanoNat.Nat.Odd y0).
Definition term37 := real_sub (real_of_num (NUMERAL 0)).
Definition term249 (x0 : nat) (x1 : real) (x2 : real) := (Coq.Arith.PeanoNat.Nat.Odd x0) -> (real_le (real_of_num (NUMERAL 0)) (real_neg x1)) -> real_lt (real_neg x1) (real_neg x2).
Definition term130 (x0 : real) (x1 : nat) := (fun y0 : nat => (real_le (real_of_num (NUMERAL 0)) x0) -> real_le (real_of_num (NUMERAL 0)) (real_pow x0 y0)) x1.
Definition term313 (x0 : real) (x1 : real) (x2 : nat) := (Coq.Arith.PeanoNat.Nat.Odd x2) /\ ((real_le (real_of_num (NUMERAL 0)) (real_neg x1)) /\ ((real_lt (real_neg (real_pow x1 x2)) (real_neg (real_pow x0 x2))) /\ (~ (real_lt (real_pow x0 x2) (real_pow x1 x2))))).
Definition term140 (x0 : real) := forall y0 : nat, (real_pow (real_neg x0) y0) = (@COND real (Coq.Arith.PeanoNat.Nat.Even y0) (real_pow x0 y0) (real_neg (real_pow x0 y0))).
Definition term285 (x0 : real) (x1 : real) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))).
Definition term40 (x0 : real) := real_add (real_of_num (NUMERAL 0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)).
Definition term107 (x0 : real) (x1 : real) (x2 : nat) := (real_lt x0 x1) /\ (Coq.Arith.PeanoNat.Nat.Odd x2).
Definition term151 (x0 : real) (x1 : nat) := and (real_lt (real_of_num (NUMERAL 0)) (real_neg (real_pow x0 x1))).
Definition term150 (x0 : real) (x1 : nat) := real_lt (real_of_num (NUMERAL 0)) (real_neg (real_pow x0 x1)).
Definition term188 (x0 : real) (x1 : real) (x2 : nat) := real_ge (real_add (real_pow x0 x2) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 x2))).
Definition term89 := real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term213 (x0 : real) (x1 : nat) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 x1)) (real_pow x0 x1).
Definition term112 (x0 : real) := real_lt (real_pow x0 (NUMERAL 0)).
Definition term143 (x0 : real) (x1 : nat) := @COND real (Coq.Arith.PeanoNat.Nat.Even x1) (real_pow x0 x1) (real_neg (real_pow x0 x1)).
Definition term357 := forall y0 : nat, forall y1 : real, forall y2 : real, ((real_lt y1 y2) /\ (Coq.Arith.PeanoNat.Nat.Odd y0)) -> real_lt (real_pow y1 y0) (real_pow y2 y0).
Definition term5 := forall y0 : nat, forall y1 : real, forall y2 : real, ((~ (y0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_lt y1 y2))) -> real_lt (real_pow y1 y0) (real_pow y2 y0).
Definition term354 (x0 : real) (x1 : real) (x2 : nat) := (~ (x2 = (NUMERAL 0))) -> (real_lt x0 x1) -> (Coq.Arith.PeanoNat.Nat.Odd x2) -> (real_le (real_of_num (NUMERAL 0)) (real_neg x1)) -> (real_lt (real_neg (real_pow x1 x2)) (real_neg (real_pow x0 x2))) -> real_lt (real_pow x0 x2) (real_pow x1 x2).
Definition term306 (x0 : nat) (x1 : real) (x2 : real) := (~ (x0 = (NUMERAL 0))) -> (real_lt x2 x1) -> (Coq.Arith.PeanoNat.Nat.Odd x0) -> (real_le (real_of_num (NUMERAL 0)) (real_neg x1)) -> real_lt (real_neg x1) (real_neg x2).
Definition term68 (x0 : real) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0)))) -> real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) x0) (real_of_num (NUMERAL 0)).
Definition term54 (x0 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) x0.
Definition term100 := (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Odd (NUMERAL y0)) = (Coq.Arith.PeanoNat.Nat.Odd y0)) /\ (((Coq.Arith.PeanoNat.Nat.Odd 0) = False) /\ ((forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Odd (BIT0 y0)) = False) /\ (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Odd (BIT1 y0)) = True))).
Definition term98 (x0 : nat) := (x0 = (NUMERAL 0)) \/ (~ (x0 = (NUMERAL 0))).
Definition term326 (x0 : real) (x1 : real) (x2 : nat) := real_sub (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 x2)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 x2)).
Definition term80 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0.
Definition term1 := fun y0 : nat => (~ (Coq.Arith.PeanoNat.Nat.Odd y0)) = (Coq.Arith.PeanoNat.Nat.Even y0).
Definition term52 := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term67 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) -> real_ge (real_mul x0 x1) (real_of_num (NUMERAL 0)).
Definition term245 (x0 : real) (x1 : real) := (real_le (real_of_num (NUMERAL 0)) (real_neg x0)) -> real_lt (real_neg x0) (real_neg x1).
Definition term322 (x0 : real) (x1 : real) (x2 : nat) := ~ ((~ (x2 = (NUMERAL 0))) -> (real_lt x0 x1) -> (Coq.Arith.PeanoNat.Nat.Odd x2) -> (real_le (real_of_num (NUMERAL 0)) (real_neg x1)) -> (real_lt (real_neg (real_pow x1 x2)) (real_neg (real_pow x0 x2))) -> real_lt (real_pow x0 x2) (real_pow x1 x2)).
Definition term252 (x0 : nat) (x1 : real) (x2 : real) := ~ ((~ (x0 = (NUMERAL 0))) -> (real_lt x2 x1) -> (Coq.Arith.PeanoNat.Nat.Odd x0) -> (real_le (real_of_num (NUMERAL 0)) (real_neg x1)) -> real_lt (real_neg x1) (real_neg x2)).
Definition term231 (x0 : nat) (x1 : real) (x2 : real) := (~ (x0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) (real_neg x1)) /\ (real_lt (real_neg x1) (real_neg x2))).
Definition term232 (x0 : real) (x1 : nat) := real_lt (real_pow (real_neg x0) x1).
Definition term23 (x0 : real) := (~ (real_le (real_of_num (NUMERAL 0)) x0)) /\ (~ (real_lt (real_of_num (NUMERAL 0)) (real_neg x0))).
Definition term340 (x0 : real) (x1 : real) (x2 : nat) := (~ (x2 = (NUMERAL 0))) /\ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))) /\ ((Coq.Arith.PeanoNat.Nat.Odd x2) /\ ((real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_of_num (NUMERAL 0))) /\ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 x2)) (real_pow x1 x2)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_pow x0 x2) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 x2))) (real_of_num (NUMERAL 0))))))).
Definition term284 (x0 : nat) (x1 : real) (x2 : real) := (~ (x0 = (NUMERAL 0))) /\ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2) (real_of_num (NUMERAL 0))) /\ ((Coq.Arith.PeanoNat.Nat.Odd x0) /\ ((real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2)) (real_of_num (NUMERAL 0)))))).
Definition term336 (x0 : real) (x1 : real) (x2 : nat) := (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 x2)) (real_pow x1 x2)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_pow x0 x2) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 x2))) (real_of_num (NUMERAL 0))).
Definition term208 (x0 : real) (x1 : real) (x2 : nat) := (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 x2)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_pow x0 x2) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 x2))) (real_of_num (NUMERAL 0))).
Definition term236 (x0 : real) (x1 : real) (x2 : nat) := imp (real_lt (real_neg (real_pow x0 x2)) (real_neg (real_pow x1 x2))).
Definition term76 (x0 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)).
Definition term92 (x0 : real) := ((~ ((real_le (real_of_num (NUMERAL 0)) x0) \/ (real_lt (real_of_num (NUMERAL 0)) (real_neg x0)))) -> False) -> (real_le (real_of_num (NUMERAL 0)) x0) \/ (real_lt (real_of_num (NUMERAL 0)) (real_neg x0)).
Definition term339 (x0 : real) (x1 : real) (x2 : nat) := (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))) /\ ((Coq.Arith.PeanoNat.Nat.Odd x2) /\ ((real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_of_num (NUMERAL 0))) /\ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 x2)) (real_pow x1 x2)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_pow x0 x2) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 x2))) (real_of_num (NUMERAL 0)))))).
Definition term62 (x0 : nat) (x1 : nat) := real_gt (real_of_num x0) (real_of_num x1).
Definition term127 (x0 : real) (x1 : nat) := real_lt (real_of_num (NUMERAL 0)) (real_pow x0 x1).
Definition term277 (x0 : real) (x1 : real) := real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term65 := S (Nat.add 0 0).
Definition term330 (x0 : real) (x1 : real) (x2 : nat) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 x2)) (real_pow x1 x2).
Definition term317 (x0 : real) (x1 : real) (x2 : nat) := (real_lt x0 x1) /\ ((Coq.Arith.PeanoNat.Nat.Odd x2) /\ ((real_le (real_of_num (NUMERAL 0)) (real_neg x1)) /\ ((real_lt (real_neg (real_pow x1 x2)) (real_neg (real_pow x0 x2))) /\ (~ (real_lt (real_pow x0 x2) (real_pow x1 x2)))))).
Definition term81 (x0 : real) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term289 (x0 : real) (x1 : real) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1))).
Definition term24 (x0 : real) := real_le (real_of_num (NUMERAL 0)) x0.
Definition term43 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term295 (x0 : real) (x1 : real) := (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))).
Definition term299 (x0 : real) (x1 : real) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0) (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term226 (x0 : real) (x1 : real) (x2 : nat) := ((~ (x2 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) (real_neg x0)) /\ (real_lt (real_neg x0) (real_neg x1)))) -> real_lt (real_pow (real_neg x0) x2) (real_pow (real_neg x1) x2).
Definition term25 (x0 : real) := real_lt (real_of_num (NUMERAL 0)) (real_neg x0).
Definition term191 (x0 : real) (x1 : real) (x2 : nat) := and ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 x2)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_pow x1 x2) (real_of_num (NUMERAL 0)))).
Definition term60 (x0 : real) := and (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))).
Definition term228 (x0 : real) (x1 : real) := real_lt (real_neg x0) (real_neg x1).
Definition term197 (x0 : real) (x1 : nat) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 x1)).
Definition term294 (x0 : real) (x1 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1)).
Definition term335 (x0 : real) (x1 : real) (x2 : nat) := and (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 x2)) (real_pow x1 x2)) (real_of_num (NUMERAL 0))).
Definition term181 (x0 : real) (x1 : nat) := and (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 x1)) (real_of_num (NUMERAL 0))).
Definition term293 (x0 : real) (x1 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1).
Definition term85 := real_mul (real_of_num (NUMERAL 0)).
Definition term33 (x0 : real) := real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term8 (x0 : nat) (x1 : real) := (fun y0 : real => forall y1 : real, ((~ (x0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 y1))) -> real_lt (real_pow y0 x0) (real_pow y1 x0)) x1.
Definition term31 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term273 (x0 : real) (x1 : real) := real_sub (real_neg x0) (real_neg x1).
Definition term118 (x0 : nat) := and (~ (x0 = (NUMERAL 0))).
Definition term29 (x0 : real) := real_sub (real_of_num (NUMERAL 0)) x0.
Definition term329 (x0 : real) (x1 : nat) := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_pow x0 x1).
Definition term307 (x0 : real) (x1 : real) (x2 : nat) := ~ ((real_lt (real_neg (real_pow x1 x2)) (real_neg (real_pow x0 x2))) -> real_lt (real_pow x0 x2) (real_pow x1 x2)).
Definition term241 (x0 : nat) := and (Coq.Arith.PeanoNat.Nat.Odd x0).
Definition term314 (x0 : real) (x1 : real) (x2 : nat) := ~ ((Coq.Arith.PeanoNat.Nat.Odd x2) -> (real_le (real_of_num (NUMERAL 0)) (real_neg x1)) -> (real_lt (real_neg (real_pow x1 x2)) (real_neg (real_pow x0 x2))) -> real_lt (real_pow x0 x2) (real_pow x1 x2)).
Definition term113 (x0 : real) (x1 : real) := real_lt (real_pow x0 (NUMERAL 0)) (real_pow x1 (NUMERAL 0)).
Definition term124 (x0 : real) (x1 : nat) := (fun y0 : nat => (real_lt (real_of_num (NUMERAL 0)) x0) -> real_lt (real_of_num (NUMERAL 0)) (real_pow x0 y0)) x1.
Definition term53 := real_mul (real_of_num (NUMERAL (BIT1 0))).
Definition term22 (x0 : real) := ~ ((real_le (real_of_num (NUMERAL 0)) x0) \/ (real_lt (real_of_num (NUMERAL 0)) (real_neg x0))).
Definition term319 (x0 : real) (x1 : real) (x2 : nat) := (Coq.Arith.PeanoNat.Nat.Odd x2) -> (real_le (real_of_num (NUMERAL 0)) (real_neg x1)) -> (real_lt (real_neg (real_pow x1 x2)) (real_neg (real_pow x0 x2))) -> real_lt (real_pow x0 x2) (real_pow x1 x2).
Definition term141 (x0 : real) (x1 : nat) := (fun y0 : nat => (real_pow (real_neg x0) y0) = (@COND real (Coq.Arith.PeanoNat.Nat.Even y0) (real_pow x0 y0) (real_neg (real_pow x0 y0)))) x1.
Definition term126 (x0 : real) := real_lt (real_of_num (NUMERAL 0)) x0.
Definition term286 (x0 : real) (x1 : real) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0)))) -> real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1))) (real_of_num (NUMERAL 0)).
Definition term199 (x0 : real) (x1 : real) (x2 : nat) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_pow x0 x2) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 x2))) (real_of_num (NUMERAL 0)))) -> real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_pow x0 x2) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 x2)))) (real_of_num (NUMERAL 0)).
Definition term94 (x0 : real) := (fun y0 : real => (real_le (real_of_num (NUMERAL 0)) y0) \/ (real_le (real_of_num (NUMERAL 0)) (real_neg y0))) x0.
Definition term244 (x0 : nat) (x1 : real) (x2 : real) := ~ ((Coq.Arith.PeanoNat.Nat.Odd x0) -> (real_le (real_of_num (NUMERAL 0)) (real_neg x1)) -> real_lt (real_neg x1) (real_neg x2)).
Definition term254 (x0 : real) (x1 : real) := real_gt (real_sub x0 x1) (real_of_num (NUMERAL 0)).
Definition term10 (x0 : real) (x1 : nat) (x2 : real) := (fun y0 : real => ((~ (x1 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_lt x0 y0))) -> real_lt (real_pow x0 x1) (real_pow y0 x1)) x2.
Definition term320 (x0 : real) (x1 : real) (x2 : nat) := (~ (x2 = (NUMERAL 0))) /\ (~ ((real_lt x0 x1) -> (Coq.Arith.PeanoNat.Nat.Odd x2) -> (real_le (real_of_num (NUMERAL 0)) (real_neg x1)) -> (real_lt (real_neg (real_pow x1 x2)) (real_neg (real_pow x0 x2))) -> real_lt (real_pow x0 x2) (real_pow x1 x2))).
Definition term250 (x0 : nat) (x1 : real) (x2 : real) := (~ (x0 = (NUMERAL 0))) /\ (~ ((real_lt x2 x1) -> (Coq.Arith.PeanoNat.Nat.Odd x0) -> (real_le (real_of_num (NUMERAL 0)) (real_neg x1)) -> real_lt (real_neg x1) (real_neg x2))).
Definition term168 (x0 : real) (x1 : nat) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 x1)).
Definition term137 (x0 : real) (x1 : nat) := (real_le (real_of_num (NUMERAL 0)) x0) -> (real_le (real_of_num (NUMERAL 0)) (real_pow x0 x1)) = True.
Definition term237 (x0 : real) (x1 : real) (x2 : nat) := (real_lt (real_pow (real_neg x1) x2) (real_pow (real_neg x0) x2)) -> real_lt (real_pow x0 x2) (real_pow x1 x2).
Definition term180 (x0 : real) (x1 : nat) := real_ge (real_pow x0 x1) (real_of_num (NUMERAL 0)).
Definition term30 (x0 : real) := real_add (real_of_num (NUMERAL 0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term44 (x0 : nat) (x1 : nat) := real_mul (real_neg (real_of_num x0)) (real_neg (real_of_num x1)).
Definition term142 (x0 : real) (x1 : nat) := real_pow (real_neg x0) x1.
Definition term240 (x0 : real) (x1 : real) := (real_le (real_of_num (NUMERAL 0)) (real_neg x0)) /\ (~ (real_lt (real_neg x0) (real_neg x1))).
Definition term193 (x0 : real) (x1 : nat) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_pow x0 x1) (real_of_num (NUMERAL 0))).
Definition term165 (x0 : real) (x1 : nat) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 x1)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term269 (x0 : real) := real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term70 (x0 : real) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) x0).
Definition term15 (x0 : real) (x1 : real) := forall y0 : nat, ((~ (y0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_lt x0 x1))) -> real_lt (real_pow x0 y0) (real_pow x1 y0).
Definition term341 (x0 : real) (x1 : real) (x2 : nat) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 x2)) (real_pow x1 x2)) (real_of_num (NUMERAL 0))).
Definition term203 (x0 : real) (x1 : nat) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 x1)) (real_of_num (NUMERAL 0))).
Definition term11 (x0 : real) (x1 : real) (x2 : nat) := ((~ (x2 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_lt x0 x1))) -> real_lt (real_pow x0 x2) (real_pow x1 x2).
Definition term13 (x0 : real) (x1 : real) (x2 : nat) := real_lt (real_pow x0 x2) (real_pow x1 x2).
Definition term169 (x0 : real) (x1 : nat) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 x1)) (real_of_num (NUMERAL 0)).
Definition term222 (x0 : real) (x1 : nat) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 x1)) (real_pow x0 x1)).
Definition term153 (x0 : real) (x1 : real) (x2 : nat) := imp ((real_lt (real_of_num (NUMERAL 0)) (real_pow (real_neg x0) x2)) /\ (real_le (real_of_num (NUMERAL 0)) (real_pow x1 x2))).
Definition term202 (x0 : real) (x1 : real) (x2 : nat) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_pow x0 x2) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 x2)))).
Definition term159 (x0 : real) (x1 : nat) := real_gt (real_sub (real_neg (real_pow x0 x1)) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term47 := real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term56 (x0 : real) := real_add (real_of_num (NUMERAL 0)) x0.
Definition term51 := real_of_num (NUMERAL (BIT1 0)).
Definition term266 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term230 (x0 : real) (x1 : real) := True /\ (real_lt (real_neg x0) (real_neg x1)).
Definition term21 (x0 : real) (x1 : real) (x2 : nat) := (fun y0 : nat => ((~ (y0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_lt x0 x1))) -> real_lt (real_pow x0 y0) (real_pow x1 y0)) x2.
Definition term323 (x0 : real) (x1 : real) (x2 : nat) := (real_lt x0 x1) -> (Coq.Arith.PeanoNat.Nat.Odd x2) -> (real_le (real_of_num (NUMERAL 0)) (real_neg x1)) -> (real_lt (real_neg (real_pow x1 x2)) (real_neg (real_pow x0 x2))) -> real_lt (real_pow x0 x2) (real_pow x1 x2).
Definition term344 (x0 : real) (x1 : real) (x2 : nat) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 x2)) (real_pow x1 x2)).
Definition term12 (x0 : nat) (x1 : real) (x2 : real) := (~ (x0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) x1) /\ (real_lt x1 x2)).
Definition term86 (x0 : real) := real_mul (real_of_num (NUMERAL 0)) x0.
Definition term14 (x0 : real) (x1 : real) (x2 : nat) := (forall y0 : nat, forall y1 : real, forall y2 : real, ((~ (y0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_lt y1 y2))) -> real_lt (real_pow y1 y0) (real_pow y2 y0)) -> real_lt (real_pow x0 x2) (real_pow x1 x2).
Definition term246 (x0 : nat) (x1 : real) (x2 : real) := (real_lt x2 x1) /\ (~ ((Coq.Arith.PeanoNat.Nat.Odd x0) -> (real_le (real_of_num (NUMERAL 0)) (real_neg x1)) -> real_lt (real_neg x1) (real_neg x2))).
Definition term115 (x0 : real) (x1 : real) := False -> real_lt (real_pow x0 (NUMERAL 0)) (real_pow x1 (NUMERAL 0)).
Definition term333 (x0 : real) (x1 : real) (x2 : nat) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 x2)) (real_pow x1 x2)) (real_of_num (NUMERAL 0)).
Definition term134 (x0 : real) (x1 : nat) := (real_lt (real_of_num (NUMERAL 0)) (real_neg x0)) -> (real_lt (real_of_num (NUMERAL 0)) (real_pow (real_neg x0) x1)) = True.
Definition term42 (x0 : real) := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) x0.
Definition term161 (x0 : real) (x1 : nat) := real_sub (real_neg (real_pow x0 x1)).
Definition term87 (x0 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0).
Definition term116 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> (x0 = (NUMERAL 0)) = False.
Definition term190 (x0 : real) (x1 : real) (x2 : nat) := and ((real_lt (real_of_num (NUMERAL 0)) (real_neg (real_pow x0 x2))) /\ (real_le (real_of_num (NUMERAL 0)) (real_pow x1 x2))).
Definition term35 (x0 : real) := ~ (real_lt (real_of_num (NUMERAL 0)) (real_neg x0)).
Definition term79 (x0 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0) (real_of_num (NUMERAL 0)).
Definition term243 (x0 : nat) (x1 : real) (x2 : real) := (Coq.Arith.PeanoNat.Nat.Odd x0) /\ ((real_le (real_of_num (NUMERAL 0)) (real_neg x1)) /\ (~ (real_lt (real_neg x1) (real_neg x2)))).
Definition term347 (x0 : real) (x1 : real) (x2 : nat) := real_gt (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 x2)) (real_pow x1 x2)) (real_add (real_pow x0 x2) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 x2)))) (real_of_num (NUMERAL 0)).
Definition term210 (x0 : real) (x1 : real) (x2 : nat) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 x2)) (real_add (real_pow x0 x2) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 x2)))) (real_of_num (NUMERAL 0)).
Definition term136 (x0 : real) (x1 : nat) := and (real_lt (real_of_num (NUMERAL 0)) (real_pow (real_neg x0) x1)).
Definition term225 (x0 : real) (x1 : real) (x2 : nat) := real_lt (real_pow (real_neg x0) x2) (real_pow (real_neg x1) x2).
Definition term39 (x0 : real) := real_sub (real_of_num (NUMERAL 0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term144 (x0 : nat) := @COND real (Coq.Arith.PeanoNat.Nat.Even x0).
Definition term316 (x0 : real) (x1 : real) (x2 : nat) := (real_lt x0 x1) /\ (~ ((Coq.Arith.PeanoNat.Nat.Odd x2) -> (real_le (real_of_num (NUMERAL 0)) (real_neg x1)) -> (real_lt (real_neg (real_pow x1 x2)) (real_neg (real_pow x0 x2))) -> real_lt (real_pow x0 x2) (real_pow x1 x2))).
Definition term194 (x0 : real) (x1 : nat) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_pow x0 x1) (real_of_num (NUMERAL 0)))) -> real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 x1)) (real_of_num (NUMERAL 0)).
Definition term242 (x0 : nat) (x1 : real) (x2 : real) := (Coq.Arith.PeanoNat.Nat.Odd x0) /\ (~ ((real_le (real_of_num (NUMERAL 0)) (real_neg x1)) -> real_lt (real_neg x1) (real_neg x2))).
Definition term45 (x0 : nat) (x1 : nat) := real_of_num (Nat.mul x0 x1).
Definition term175 (x0 : real) (x1 : nat) := real_add (real_pow x0 x1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term105 := Coq.Arith.PeanoNat.Nat.Odd (NUMERAL 0).
Definition term264 (x0 : real) := real_sub (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)).
Definition term302 := real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term38 (x0 : real) := real_sub (real_of_num (NUMERAL 0)) (real_neg x0).
Definition term145 (x0 : real) (x1 : nat) := @COND real (Coq.Arith.PeanoNat.Nat.Even x1) (real_pow x0 x1).
Definition term353 (x0 : real) (x1 : real) (x2 : nat) := ((~ ((~ (x2 = (NUMERAL 0))) -> (real_lt x0 x1) -> (Coq.Arith.PeanoNat.Nat.Odd x2) -> (real_le (real_of_num (NUMERAL 0)) (real_neg x1)) -> (real_lt (real_neg (real_pow x1 x2)) (real_neg (real_pow x0 x2))) -> real_lt (real_pow x0 x2) (real_pow x1 x2))) -> False) -> (~ (x2 = (NUMERAL 0))) -> (real_lt x0 x1) -> (Coq.Arith.PeanoNat.Nat.Odd x2) -> (real_le (real_of_num (NUMERAL 0)) (real_neg x1)) -> (real_lt (real_neg (real_pow x1 x2)) (real_neg (real_pow x0 x2))) -> real_lt (real_pow x0 x2) (real_pow x1 x2).
Definition term305 (x0 : nat) (x1 : real) (x2 : real) := ((~ ((~ (x0 = (NUMERAL 0))) -> (real_lt x2 x1) -> (Coq.Arith.PeanoNat.Nat.Odd x0) -> (real_le (real_of_num (NUMERAL 0)) (real_neg x1)) -> real_lt (real_neg x1) (real_neg x2))) -> False) -> (~ (x0 = (NUMERAL 0))) -> (real_lt x2 x1) -> (Coq.Arith.PeanoNat.Nat.Odd x0) -> (real_le (real_of_num (NUMERAL 0)) (real_neg x1)) -> real_lt (real_neg x1) (real_neg x2).
Definition term0 (x0 : nat) := ~ (Coq.Arith.PeanoNat.Nat.Odd x0).
Definition term311 (x0 : real) (x1 : real) (x2 : nat) := ~ ((real_le (real_of_num (NUMERAL 0)) (real_neg x1)) -> (real_lt (real_neg (real_pow x1 x2)) (real_neg (real_pow x0 x2))) -> real_lt (real_pow x0 x2) (real_pow x1 x2)).
Definition term61 (x0 : real) := (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0))).
Definition term114 (x0 : real) (x1 : real) (x2 : nat) := ((real_lt x0 x1) /\ (Coq.Arith.PeanoNat.Nat.Odd x2)) -> real_lt (real_pow x0 x2) (real_pow x1 x2).
Definition term303 (x0 : real) (x1 : real) := real_gt (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1))).
Definition term34 (x0 : real) := real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)).
Definition term274 (x0 : real) (x1 : real) := real_sub (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1).
Definition term206 (x0 : real) (x1 : nat) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 x1)).
Definition term255 (x0 : real) (x1 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1).
Definition term233 (x0 : real) (x1 : nat) := real_lt (real_neg (real_pow x0 x1)).
Definition term83 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term281 (x0 : nat) (x1 : real) (x2 : real) := (Coq.Arith.PeanoNat.Nat.Odd x0) /\ ((real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2)) (real_of_num (NUMERAL 0)))).
Definition term346 (x0 : real) (x1 : real) (x2 : nat) := ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 x2)) (real_pow x1 x2)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_pow x0 x2) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 x2))) (real_of_num (NUMERAL 0)))) -> real_gt (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 x2)) (real_pow x1 x2)) (real_add (real_pow x0 x2) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 x2)))) (real_of_num (NUMERAL 0)).
Definition term342 (x0 : real) (x1 : real) (x2 : nat) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 x2)) (real_pow x1 x2)) (real_of_num (NUMERAL 0)))) -> real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 x2)) (real_pow x1 x2))) (real_of_num (NUMERAL 0)).
Definition term296 (x0 : real) (x1 : real) := ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0)))) -> real_gt (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1))) (real_of_num (NUMERAL 0)).
Definition term209 (x0 : real) (x1 : real) (x2 : nat) := ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 x2)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_pow x0 x2) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 x2))) (real_of_num (NUMERAL 0)))) -> real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 x2)) (real_add (real_pow x0 x2) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 x2)))) (real_of_num (NUMERAL 0)).
Definition term204 (x0 : real) (x1 : nat) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 x1)) (real_of_num (NUMERAL 0)))) -> real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 x1))) (real_of_num (NUMERAL 0)).
Definition term152 (x0 : real) (x1 : real) (x2 : nat) := (real_lt (real_of_num (NUMERAL 0)) (real_neg (real_pow x0 x2))) /\ (real_le (real_of_num (NUMERAL 0)) (real_pow x1 x2)).
Definition term71 (x0 : real) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))).
Definition term111 (x0 : real) (x1 : nat) := real_lt (real_pow x0 x1).
Definition term257 (x0 : real) (x1 : real) := real_gt (real_sub x0 x1).
Definition term55 := real_add (real_of_num (NUMERAL 0)).
Definition term298 (x0 : real) (x1 : real) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term19 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : nat, ((~ (y2 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 y1))) -> real_lt (real_pow y0 y2) (real_pow y1 y2)) x0.
Definition term185 (x0 : real) (x1 : real) (x2 : nat) := real_sub (real_pow x0 x2) (real_pow x1 x2).
Definition term291 (x0 : real) (x1 : real) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0)))) -> real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1)) (real_of_num (NUMERAL 0)).
Definition term220 (x0 : real) (x1 : nat) := ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 x1)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_pow x0 x1) (real_of_num (NUMERAL 0)))) -> real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 x1)) (real_pow x0 x1)) (real_of_num (NUMERAL 0)).
Definition term73 (x0 : real) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))) -> real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_of_num (NUMERAL 0)).
Definition term259 (x0 : real) (x1 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0)).
Definition term275 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term171 (x0 : real) (x1 : nat) := real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 x1)).
Definition term97 (x0 : nat) := (fun y0 : Prop => y0 \/ (~ y0)) (x0 = (NUMERAL 0)).
Definition term108 (x0 : real) (x1 : real) := (real_lt x0 x1) /\ False.
Definition term48 := NUMERAL (BIT1 0).
Definition term327 (x0 : real) (x1 : real) (x2 : nat) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 x2)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 x2))).
Definition term104 (x0 : nat) := Coq.Arith.PeanoNat.Nat.Odd (NUMERAL x0).
Definition term227 (x0 : real) := and (real_le (real_of_num (NUMERAL 0)) (real_neg x0)).
Definition term77 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) -> real_gt (real_add x0 x1) (real_of_num (NUMERAL 0)).
Definition term72 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_gt x1 (real_of_num (NUMERAL 0)))) -> real_gt (real_mul x0 x1) (real_of_num (NUMERAL 0)).
Definition term301 (x0 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term63 := real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term345 (x0 : real) (x1 : real) (x2 : nat) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 x2)) (real_pow x1 x2))).
Definition term196 (x0 : real) (x1 : nat) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 x1).
Definition term318 (x0 : real) (x1 : real) (x2 : nat) := ~ ((real_lt x0 x1) -> (Coq.Arith.PeanoNat.Nat.Odd x2) -> (real_le (real_of_num (NUMERAL 0)) (real_neg x1)) -> (real_lt (real_neg (real_pow x1 x2)) (real_neg (real_pow x0 x2))) -> real_lt (real_pow x0 x2) (real_pow x1 x2)).
Definition term248 (x0 : nat) (x1 : real) (x2 : real) := ~ ((real_lt x2 x1) -> (Coq.Arith.PeanoNat.Nat.Odd x0) -> (real_le (real_of_num (NUMERAL 0)) (real_neg x1)) -> real_lt (real_neg x1) (real_neg x2)).
Definition term20 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : nat, ((~ (y1 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_lt x0 y0))) -> real_lt (real_pow x0 y1) (real_pow y0 y1)) x1.
Definition term290 (x0 : real) (x1 : real) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))).
Definition term260 (x0 : real) := real_ge (real_sub (real_neg x0) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term88 := real_gt (real_of_num (NUMERAL 0)).
Definition term195 (x0 : real) (x1 : nat) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 x1)) (real_of_num (NUMERAL 0)).
