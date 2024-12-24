Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term38 := ~ ((real_of_num (NUMERAL (BIT1 0))) = (real_of_num (NUMERAL 0))).
Definition term26 (x0 : real) := fun y0 : nat => (fun y1 : nat => ((real_pow x0 y1) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ (y1 = (NUMERAL 0))))) y0.
Definition term57 (x0 : Prop) := ~ (~ x0).
Definition term5 := real_of_num (NUMERAL 0).
Definition term34 := @eq Prop ((real_of_num (NUMERAL (BIT1 0))) = (real_of_num (NUMERAL 0))).
Definition term19 (x0 : real) := fun y0 : nat => (((real_pow x0 y0) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ (y0 = (NUMERAL 0))))) -> ((real_pow x0 (S y0)) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ ((S y0) = (NUMERAL 0)))).
Definition term73 (x0 : nat) (x1 : real) := (fun y0 : Prop => (y0 \/ (y0 /\ (~ (x0 = (NUMERAL 0))))) = y0) (x1 = (real_of_num (NUMERAL 0))).
Definition term31 (x0 : real) := @eq real (real_pow x0 (NUMERAL 0)).
Definition term79 (x0 : nat) := False \/ (False /\ (~ (x0 = (NUMERAL 0)))).
Definition term43 (x0 : real) := forall y0 : nat, (real_pow x0 (S y0)) = (real_mul x0 (real_pow x0 y0)).
Definition term72 (x0 : nat) := fun y0 : Prop => (y0 \/ (y0 /\ (~ (x0 = (NUMERAL 0))))) = y0.
Definition term45 (x0 : real) (x1 : nat) := real_mul x0 (real_pow x0 x1).
Definition term23 (x0 : real) := (((real_pow x0 (NUMERAL 0)) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ ((NUMERAL 0) = (NUMERAL 0))))) /\ (forall y0 : nat, (((real_pow x0 y0) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ (y0 = (NUMERAL 0))))) -> ((real_pow x0 (S y0)) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ ((S y0) = (NUMERAL 0))))).
Definition term27 (x0 : real) := forall y0 : nat, (fun y1 : nat => ((real_pow x0 y1) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ (y1 = (NUMERAL 0))))) y0.
Definition term22 (x0 : real) := ((fun y0 : nat => ((real_pow x0 y0) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ (y0 = (NUMERAL 0))))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((real_pow x0 y1) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ (y1 = (NUMERAL 0))))) y0) -> (fun y1 : nat => ((real_pow x0 y1) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ (y1 = (NUMERAL 0))))) (S y0)).
Definition term14 (x0 : real) (x1 : nat) := real_pow x0 (S x1).
Definition term44 (x0 : real) (x1 : nat) := (fun y0 : nat => (real_pow x0 (S y0)) = (real_mul x0 (real_pow x0 y0))) x1.
Definition term16 (x0 : real) (x1 : nat) := ((fun y0 : nat => ((real_pow x0 y0) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ (y0 = (NUMERAL 0))))) x1) -> (fun y0 : nat => ((real_pow x0 y0) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ (y0 = (NUMERAL 0))))) (S x1).
Definition term1 (x0 : real) := (((fun y0 : nat => ((real_pow x0 y0) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ (y0 = (NUMERAL 0))))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((real_pow x0 y1) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ (y1 = (NUMERAL 0))))) y0) -> (fun y1 : nat => ((real_pow x0 y1) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ (y1 = (NUMERAL 0))))) (S y0))) -> forall y0 : nat, (fun y1 : nat => ((real_pow x0 y1) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ (y1 = (NUMERAL 0))))) y0.
Definition term80 (x0 : nat) := True /\ (~ (x0 = (NUMERAL 0))).
Definition term4 (x0 : real) := real_pow x0 (NUMERAL 0).
Definition term78 (x0 : nat) := (fun y0 : Prop => (y0 \/ (y0 /\ (~ (x0 = (NUMERAL 0))))) = y0) False.
Definition term0 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term61 (x0 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num (NUMERAL 0)).
Definition term84 := forall y0 : real, forall y1 : nat, ((real_pow y0 y1) = (real_of_num (NUMERAL 0))) = ((y0 = (real_of_num (NUMERAL 0))) /\ (~ (y1 = (NUMERAL 0)))).
Definition term54 (x0 : real) (x1 : nat) := @eq Prop ((real_pow x0 (S x1)) = (real_of_num (NUMERAL 0))).
Definition term24 (x0 : real) := imp (((fun y0 : nat => ((real_pow x0 y0) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ (y0 = (NUMERAL 0))))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((real_pow x0 y1) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ (y1 = (NUMERAL 0))))) y0) -> (fun y1 : nat => ((real_pow x0 y1) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ (y1 = (NUMERAL 0))))) (S y0))).
Definition term8 (x0 : real) := and (((real_pow x0 (NUMERAL 0)) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ ((NUMERAL 0) = (NUMERAL 0))))).
Definition term35 := ~ ((NUMERAL 0) = (NUMERAL 0)).
Definition term20 (x0 : real) := forall y0 : nat, ((fun y1 : nat => ((real_pow x0 y1) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ (y1 = (NUMERAL 0))))) y0) -> (fun y1 : nat => ((real_pow x0 y1) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ (y1 = (NUMERAL 0))))) (S y0).
Definition term83 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term42 (x0 : real) (x1 : real) := (x0 = (real_of_num (NUMERAL 0))) \/ (x1 = (real_of_num (NUMERAL 0))).
Definition term7 (x0 : real) := and ((fun y0 : nat => ((real_pow x0 y0) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ (y0 = (NUMERAL 0))))) (NUMERAL 0)).
Definition term51 (x0 : real) (x1 : nat) := (x0 = (real_of_num (NUMERAL 0))) \/ ((real_pow x0 x1) = (real_of_num (NUMERAL 0))).
Definition term33 (x0 : real) := @eq Prop ((real_pow x0 (NUMERAL 0)) = (real_of_num (NUMERAL 0))).
Definition term62 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term70 (x0 : real) := (fun y0 : Prop => (y0 = True) \/ (y0 = False)) (x0 = (real_of_num (NUMERAL 0))).
Definition term18 (x0 : real) := fun y0 : nat => ((fun y1 : nat => ((real_pow x0 y1) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ (y1 = (NUMERAL 0))))) y0) -> (fun y1 : nat => ((real_pow x0 y1) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ (y1 = (NUMERAL 0))))) (S y0).
Definition term40 (x0 : real) := forall y0 : real, ((real_mul x0 y0) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) \/ (y0 = (real_of_num (NUMERAL 0)))).
Definition term53 (x0 : real) (x1 : nat) := (x0 = (real_of_num (NUMERAL 0))) \/ ((x0 = (real_of_num (NUMERAL 0))) /\ (~ (x1 = (NUMERAL 0)))).
Definition term9 (x0 : real) (x1 : nat) := (fun y0 : nat => ((real_pow x0 y0) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ (y0 = (NUMERAL 0))))) x1.
Definition term29 (x0 : real) := ((((real_pow x0 (NUMERAL 0)) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ ((NUMERAL 0) = (NUMERAL 0))))) /\ (forall y0 : nat, (((real_pow x0 y0) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ (y0 = (NUMERAL 0))))) -> ((real_pow x0 (S y0)) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ ((S y0) = (NUMERAL 0)))))) -> forall y0 : nat, ((real_pow x0 y0) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ (y0 = (NUMERAL 0)))).
Definition term15 (x0 : real) (x1 : nat) := (x0 = (real_of_num (NUMERAL 0))) /\ (~ ((S x1) = (NUMERAL 0))).
Definition term39 (x0 : real) := (fun y0 : real => forall y1 : real, ((real_mul y0 y1) = (real_of_num (NUMERAL 0))) = ((y0 = (real_of_num (NUMERAL 0))) \/ (y1 = (real_of_num (NUMERAL 0))))) x0.
Definition term11 (x0 : real) (x1 : nat) := imp ((fun y0 : nat => ((real_pow x0 y0) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ (y0 = (NUMERAL 0))))) x1).
Definition term17 (x0 : real) (x1 : nat) := (((real_pow x0 x1) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ (x1 = (NUMERAL 0))))) -> ((real_pow x0 (S x1)) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ ((S x1) = (NUMERAL 0)))).
Definition term67 := S (Nat.add 0 0).
Definition term37 (x0 : real) := (x0 = (real_of_num (NUMERAL 0))) /\ False.
Definition term47 (x0 : nat) := ~ ((S x0) = (NUMERAL 0)).
Definition term65 := real_add (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term49 (x0 : real) (x1 : nat) := @eq real (real_pow x0 (S x1)).
Definition term59 := real_sub (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term55 (x0 : real) (x1 : nat) := @eq Prop ((x0 = (real_of_num (NUMERAL 0))) \/ ((x0 = (real_of_num (NUMERAL 0))) /\ (~ (x1 = (NUMERAL 0))))).
Definition term6 (x0 : real) := (x0 = (real_of_num (NUMERAL 0))) /\ (~ ((NUMERAL 0) = (NUMERAL 0))).
Definition term10 (x0 : real) (x1 : nat) := (x0 = (real_of_num (NUMERAL 0))) /\ (~ (x1 = (NUMERAL 0))).
Definition term81 (x0 : nat) := ~ (False \/ (False /\ (~ (x0 = (NUMERAL 0))))).
Definition term46 (x0 : nat) := (fun y0 : nat => ~ ((S y0) = (NUMERAL 0))) x0.
Definition term60 := real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term66 := @eq real (real_sub (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))).
Definition term12 (x0 : real) (x1 : nat) := imp (((real_pow x0 x1) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ (x1 = (NUMERAL 0))))).
Definition term58 := ~ (~ ((real_of_num (NUMERAL (BIT1 0))) = (real_of_num (NUMERAL 0)))).
Definition term2 (x0 : real) := fun y0 : nat => ((real_pow x0 y0) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ (y0 = (NUMERAL 0)))).
Definition term56 (x0 : real) := (x0 = (real_of_num (NUMERAL 0))) /\ True.
Definition term30 := real_of_num (NUMERAL (BIT1 0)).
Definition term41 (x0 : real) (x1 : real) := (fun y0 : real => ((real_mul x0 y0) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) \/ (y0 = (real_of_num (NUMERAL 0))))) x1.
Definition term69 := ((~ (~ ((real_of_num (NUMERAL (BIT1 0))) = (real_of_num (NUMERAL 0))))) -> False) -> ~ ((real_of_num (NUMERAL (BIT1 0))) = (real_of_num (NUMERAL 0))).
Definition term48 (x0 : nat) := (~ ((S x0) = (NUMERAL 0))) -> ((S x0) = (NUMERAL 0)) = False.
Definition term76 (x0 : nat) (x1 : real) := @eq Prop ((fun y0 : Prop => (y0 \/ (y0 /\ (~ (x0 = (NUMERAL 0))))) = y0) (x1 = (real_of_num (NUMERAL 0)))).
Definition term64 := real_add (real_of_num (NUMERAL (BIT1 0))).
Definition term52 (x0 : real) := or (x0 = (real_of_num (NUMERAL 0))).
Definition term25 (x0 : real) := imp ((((real_pow x0 (NUMERAL 0)) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ ((NUMERAL 0) = (NUMERAL 0))))) /\ (forall y0 : nat, (((real_pow x0 y0) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ (y0 = (NUMERAL 0))))) -> ((real_pow x0 (S y0)) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ ((S y0) = (NUMERAL 0)))))).
Definition term32 := @eq real (real_of_num (NUMERAL (BIT1 0))).
Definition term36 (x0 : real) := and (x0 = (real_of_num (NUMERAL 0))).
Definition term77 (x0 : nat) (x1 : real) := @eq Prop (((x1 = (real_of_num (NUMERAL 0))) \/ ((x1 = (real_of_num (NUMERAL 0))) /\ (~ (x0 = (NUMERAL 0))))) = (x1 = (real_of_num (NUMERAL 0)))).
Definition term21 (x0 : real) := forall y0 : nat, (((real_pow x0 y0) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ (y0 = (NUMERAL 0))))) -> ((real_pow x0 (S y0)) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ ((S y0) = (NUMERAL 0)))).
Definition term50 (x0 : real) (x1 : nat) := @eq real (real_mul x0 (real_pow x0 x1)).
Definition term13 (x0 : real) (x1 : nat) := (fun y0 : nat => ((real_pow x0 y0) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ (y0 = (NUMERAL 0))))) (S x1).
Definition term3 (x0 : real) := (fun y0 : nat => ((real_pow x0 y0) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ (y0 = (NUMERAL 0))))) (NUMERAL 0).
Definition term74 (x0 : nat) := (fun y0 : Prop => (y0 \/ (y0 /\ (~ (x0 = (NUMERAL 0))))) = y0) True.
Definition term75 (x0 : nat) := True \/ (True /\ (~ (x0 = (NUMERAL 0)))).
Definition term68 := (~ (~ ((real_of_num (NUMERAL (BIT1 0))) = (real_of_num (NUMERAL 0))))) -> False.
Definition term82 (x0 : nat) := False /\ (~ (x0 = (NUMERAL 0))).
Definition term71 (x0 : real) := ((x0 = (real_of_num (NUMERAL 0))) = True) \/ ((x0 = (real_of_num (NUMERAL 0))) = False).
Definition term63 := NUMERAL (BIT1 0).
Definition term28 (x0 : real) := forall y0 : nat, ((real_pow x0 y0) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ (y0 = (NUMERAL 0)))).
