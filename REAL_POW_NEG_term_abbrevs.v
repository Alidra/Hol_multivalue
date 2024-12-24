Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term15 (x0 : real) (x1 : nat) := imp ((real_pow (real_neg x0) x1) = (@COND real (Coq.Arith.PeanoNat.Nat.Even x1) (real_pow x0 x1) (real_neg (real_pow x0 x1)))).
Definition term45 (x0 : nat) := (fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even (S y0)) = (~ (Coq.Arith.PeanoNat.Nat.Even y0))) x0.
Definition term65 (x0 : real) (x1 : real) := (fun y0 : real => (real_mul (real_neg x0) y0) = (real_neg (real_mul x0 y0))) x1.
Definition term71 (x0 : real) (x1 : nat) := @COND real True (real_pow x0 x1).
Definition term22 (x0 : real) := fun y0 : nat => ((real_pow (real_neg x0) y0) = (@COND real (Coq.Arith.PeanoNat.Nat.Even y0) (real_pow x0 y0) (real_neg (real_pow x0 y0)))) -> (real_pow (real_neg x0) (S y0)) = (@COND real (Coq.Arith.PeanoNat.Nat.Even (S y0)) (real_pow x0 (S y0)) (real_neg (real_pow x0 (S y0)))).
Definition term79 (x0 : real) := real_neg (real_neg x0).
Definition term29 (x0 : real) := fun y0 : nat => (fun y1 : nat => (real_pow (real_neg x0) y1) = (@COND real (Coq.Arith.PeanoNat.Nat.Even y1) (real_pow x0 y1) (real_neg (real_pow x0 y1)))) y0.
Definition term85 (x0 : real) (x1 : nat) := @COND real False (real_pow x0 x1).
Definition term58 (x0 : real) (x1 : nat) := @COND real (Coq.Arith.PeanoNat.Nat.Even (S x1)) (real_pow x0 (S x1)).
Definition term82 (x0 : real) (x1 : real) := (fun y0 : real => (real_mul x0 (real_neg y0)) = (real_neg (real_mul x0 y0))) x1.
Definition term86 (x0 : real) (x1 : nat) := @COND real False (real_pow x0 x1) (real_neg (real_pow x0 x1)).
Definition term52 (x0 : real) := real_mul (real_neg x0).
Definition term47 (x0 : real) := forall y0 : nat, (real_pow x0 (S y0)) = (real_mul x0 (real_pow x0 y0)).
Definition term18 (x0 : real) (x1 : nat) := @COND real (Coq.Arith.PeanoNat.Nat.Even (S x1)) (real_pow x0 (S x1)) (real_neg (real_pow x0 (S x1))).
Definition term2 (x0 : nat) := ~ (Coq.Arith.PeanoNat.Nat.Even x0).
Definition term26 (x0 : real) := ((real_pow (real_neg x0) (NUMERAL 0)) = (@COND real (Coq.Arith.PeanoNat.Nat.Even (NUMERAL 0)) (real_pow x0 (NUMERAL 0)) (real_neg (real_pow x0 (NUMERAL 0))))) /\ (forall y0 : nat, ((real_pow (real_neg x0) y0) = (@COND real (Coq.Arith.PeanoNat.Nat.Even y0) (real_pow x0 y0) (real_neg (real_pow x0 y0)))) -> (real_pow (real_neg x0) (S y0)) = (@COND real (Coq.Arith.PeanoNat.Nat.Even (S y0)) (real_pow x0 (S y0)) (real_neg (real_pow x0 (S y0))))).
Definition term76 (x0 : real) (x1 : nat) := @COND real False (real_mul x0 (real_pow x0 x1)).
Definition term50 (x0 : real) (x1 : nat) := real_mul x0 (real_pow x0 x1).
Definition term30 (x0 : real) := forall y0 : nat, (fun y1 : nat => (real_pow (real_neg x0) y1) = (@COND real (Coq.Arith.PeanoNat.Nat.Even y1) (real_pow x0 y1) (real_neg (real_pow x0 y1)))) y0.
Definition term37 := Coq.Arith.PeanoNat.Nat.Even (NUMERAL 0).
Definition term88 (x0 : real) (x1 : nat) := real_neg (real_neg (real_mul x0 (real_pow x0 x1))).
Definition term25 (x0 : real) := ((fun y0 : nat => (real_pow (real_neg x0) y0) = (@COND real (Coq.Arith.PeanoNat.Nat.Even y0) (real_pow x0 y0) (real_neg (real_pow x0 y0)))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (real_pow (real_neg x0) y1) = (@COND real (Coq.Arith.PeanoNat.Nat.Even y1) (real_pow x0 y1) (real_neg (real_pow x0 y1)))) y0) -> (fun y1 : nat => (real_pow (real_neg x0) y1) = (@COND real (Coq.Arith.PeanoNat.Nat.Even y1) (real_pow x0 y1) (real_neg (real_pow x0 y1)))) (S y0)).
Definition term74 (x0 : real) (x1 : nat) := real_mul x0 (@COND real (Coq.Arith.PeanoNat.Nat.Even x1) (real_pow x0 x1) (real_neg (real_pow x0 x1))).
Definition term49 (x0 : real) (x1 : nat) := real_pow x0 (S x1).
Definition term48 (x0 : real) (x1 : nat) := (fun y0 : nat => (real_pow x0 (S y0)) = (real_mul x0 (real_pow x0 y0))) x1.
Definition term83 (x0 : real) (x1 : real) := real_mul x0 (real_neg x1).
Definition term19 (x0 : real) (x1 : nat) := ((fun y0 : nat => (real_pow (real_neg x0) y0) = (@COND real (Coq.Arith.PeanoNat.Nat.Even y0) (real_pow x0 y0) (real_neg (real_pow x0 y0)))) x1) -> (fun y0 : nat => (real_pow (real_neg x0) y0) = (@COND real (Coq.Arith.PeanoNat.Nat.Even y0) (real_pow x0 y0) (real_neg (real_pow x0 y0)))) (S x1).
Definition term4 (x0 : real) := (((fun y0 : nat => (real_pow (real_neg x0) y0) = (@COND real (Coq.Arith.PeanoNat.Nat.Even y0) (real_pow x0 y0) (real_neg (real_pow x0 y0)))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (real_pow (real_neg x0) y1) = (@COND real (Coq.Arith.PeanoNat.Nat.Even y1) (real_pow x0 y1) (real_neg (real_pow x0 y1)))) y0) -> (fun y1 : nat => (real_pow (real_neg x0) y1) = (@COND real (Coq.Arith.PeanoNat.Nat.Even y1) (real_pow x0 y1) (real_neg (real_pow x0 y1)))) (S y0))) -> forall y0 : nat, (fun y1 : nat => (real_pow (real_neg x0) y1) = (@COND real (Coq.Arith.PeanoNat.Nat.Even y1) (real_pow x0 y1) (real_neg (real_pow x0 y1)))) y0.
Definition term33 (x0 : real) := real_pow x0 (NUMERAL 0).
Definition term72 (x0 : real) (x1 : nat) := real_neg (real_pow x0 x1).
Definition term38 := @COND real (Coq.Arith.PeanoNat.Nat.Even (NUMERAL 0)).
Definition term3 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term6 (x0 : real) := (fun y0 : nat => (real_pow (real_neg x0) y0) = (@COND real (Coq.Arith.PeanoNat.Nat.Even y0) (real_pow x0 y0) (real_neg (real_pow x0 y0)))) (NUMERAL 0).
Definition term5 (x0 : real) := fun y0 : nat => (real_pow (real_neg x0) y0) = (@COND real (Coq.Arith.PeanoNat.Nat.Even y0) (real_pow x0 y0) (real_neg (real_pow x0 y0))).
Definition term92 := forall y0 : real, forall y1 : nat, (real_pow (real_neg y0) y1) = (@COND real (Coq.Arith.PeanoNat.Nat.Even y1) (real_pow y0 y1) (real_neg (real_pow y0 y1))).
Definition term27 (x0 : real) := imp (((fun y0 : nat => (real_pow (real_neg x0) y0) = (@COND real (Coq.Arith.PeanoNat.Nat.Even y0) (real_pow x0 y0) (real_neg (real_pow x0 y0)))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (real_pow (real_neg x0) y1) = (@COND real (Coq.Arith.PeanoNat.Nat.Even y1) (real_pow x0 y1) (real_neg (real_pow x0 y1)))) y0) -> (fun y1 : nat => (real_pow (real_neg x0) y1) = (@COND real (Coq.Arith.PeanoNat.Nat.Even y1) (real_pow x0 y1) (real_neg (real_pow x0 y1)))) (S y0))).
Definition term20 (x0 : real) (x1 : nat) := ((real_pow (real_neg x0) x1) = (@COND real (Coq.Arith.PeanoNat.Nat.Even x1) (real_pow x0 x1) (real_neg (real_pow x0 x1)))) -> (real_pow (real_neg x0) (S x1)) = (@COND real (Coq.Arith.PeanoNat.Nat.Even (S x1)) (real_pow x0 (S x1)) (real_neg (real_pow x0 (S x1)))).
Definition term73 (x0 : real) (x1 : nat) := @COND real True (real_pow x0 x1) (real_neg (real_pow x0 x1)).
Definition term62 (x0 : real) (x1 : nat) := @COND real (~ (Coq.Arith.PeanoNat.Nat.Even x1)) (real_mul x0 (real_pow x0 x1)) (real_neg (real_mul x0 (real_pow x0 x1))).
Definition term23 (x0 : real) := forall y0 : nat, ((fun y1 : nat => (real_pow (real_neg x0) y1) = (@COND real (Coq.Arith.PeanoNat.Nat.Even y1) (real_pow x0 y1) (real_neg (real_pow x0 y1)))) y0) -> (fun y1 : nat => (real_pow (real_neg x0) y1) = (@COND real (Coq.Arith.PeanoNat.Nat.Even y1) (real_pow x0 y1) (real_neg (real_pow x0 y1)))) (S y0).
Definition term67 (x0 : real) (x1 : real) := real_neg (real_mul x0 x1).
Definition term8 (x0 : real) := @COND real (Coq.Arith.PeanoNat.Nat.Even (NUMERAL 0)) (real_pow x0 (NUMERAL 0)) (real_neg (real_pow x0 (NUMERAL 0))).
Definition term55 (x0 : real) (x1 : nat) := @eq real (real_mul (real_neg x0) (@COND real (Coq.Arith.PeanoNat.Nat.Even x1) (real_pow x0 x1) (real_neg (real_pow x0 x1)))).
Definition term84 (x0 : nat) := (~ (Coq.Arith.PeanoNat.Nat.Even x0)) -> (Coq.Arith.PeanoNat.Nat.Even x0) = False.
Definition term60 (x0 : real) (x1 : nat) := real_neg (real_pow x0 (S x1)).
Definition term9 (x0 : real) := and ((fun y0 : nat => (real_pow (real_neg x0) y0) = (@COND real (Coq.Arith.PeanoNat.Nat.Even y0) (real_pow x0 y0) (real_neg (real_pow x0 y0)))) (NUMERAL 0)).
Definition term44 := forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even (S y0)) = (~ (Coq.Arith.PeanoNat.Nat.Even y0)).
Definition term90 (x0 : real) (x1 : nat) := @COND real True (real_mul x0 (real_pow x0 x1)).
Definition term21 (x0 : real) := fun y0 : nat => ((fun y1 : nat => (real_pow (real_neg x0) y1) = (@COND real (Coq.Arith.PeanoNat.Nat.Even y1) (real_pow x0 y1) (real_neg (real_pow x0 y1)))) y0) -> (fun y1 : nat => (real_pow (real_neg x0) y1) = (@COND real (Coq.Arith.PeanoNat.Nat.Even y1) (real_pow x0 y1) (real_neg (real_pow x0 y1)))) (S y0).
Definition term31 (x0 : real) := forall y0 : nat, (real_pow (real_neg x0) y0) = (@COND real (Coq.Arith.PeanoNat.Nat.Even y0) (real_pow x0 y0) (real_neg (real_pow x0 y0))).
Definition term46 (x0 : nat) := Coq.Arith.PeanoNat.Nat.Even (S x0).
Definition term13 (x0 : real) (x1 : nat) := @COND real (Coq.Arith.PeanoNat.Nat.Even x1) (real_pow x0 x1) (real_neg (real_pow x0 x1)).
Definition term78 (x0 : real) := (fun y0 : real => (real_neg (real_neg y0)) = y0) x0.
Definition term81 (x0 : real) := forall y0 : real, (real_mul x0 (real_neg y0)) = (real_neg (real_mul x0 y0)).
Definition term32 (x0 : real) := (((real_pow (real_neg x0) (NUMERAL 0)) = (@COND real (Coq.Arith.PeanoNat.Nat.Even (NUMERAL 0)) (real_pow x0 (NUMERAL 0)) (real_neg (real_pow x0 (NUMERAL 0))))) /\ (forall y0 : nat, ((real_pow (real_neg x0) y0) = (@COND real (Coq.Arith.PeanoNat.Nat.Even y0) (real_pow x0 y0) (real_neg (real_pow x0 y0)))) -> (real_pow (real_neg x0) (S y0)) = (@COND real (Coq.Arith.PeanoNat.Nat.Even (S y0)) (real_pow x0 (S y0)) (real_neg (real_pow x0 (S y0)))))) -> forall y0 : nat, (real_pow (real_neg x0) y0) = (@COND real (Coq.Arith.PeanoNat.Nat.Even y0) (real_pow x0 y0) (real_neg (real_pow x0 y0))).
Definition term40 := @COND real True (real_of_num (NUMERAL (BIT1 0))).
Definition term77 (x0 : real) (x1 : nat) := @COND real False (real_mul x0 (real_pow x0 x1)) (real_neg (real_mul x0 (real_pow x0 x1))).
Definition term80 (x0 : real) := (fun y0 : real => forall y1 : real, (real_mul y0 (real_neg y1)) = (real_neg (real_mul y0 y1))) x0.
Definition term63 (x0 : real) := (fun y0 : real => forall y1 : real, (real_mul (real_neg y0) y1) = (real_neg (real_mul y0 y1))) x0.
Definition term14 (x0 : real) (x1 : nat) := imp ((fun y0 : nat => (real_pow (real_neg x0) y0) = (@COND real (Coq.Arith.PeanoNat.Nat.Even y0) (real_pow x0 y0) (real_neg (real_pow x0 y0)))) x1).
Definition term56 (x0 : nat) := @COND real (Coq.Arith.PeanoNat.Nat.Even (S x0)).
Definition term66 (x0 : real) (x1 : real) := real_mul (real_neg x0) x1.
Definition term42 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term57 (x0 : nat) := @COND real (~ (Coq.Arith.PeanoNat.Nat.Even x0)).
Definition term91 (x0 : real) (x1 : nat) := @COND real True (real_mul x0 (real_pow x0 x1)) (real_neg (real_mul x0 (real_pow x0 x1))).
Definition term68 (x0 : real) (x1 : nat) := real_neg (real_mul x0 (@COND real (Coq.Arith.PeanoNat.Nat.Even x1) (real_pow x0 x1) (real_neg (real_pow x0 x1)))).
Definition term64 (x0 : real) := forall y0 : real, (real_mul (real_neg x0) y0) = (real_neg (real_mul x0 y0)).
Definition term53 (x0 : real) (x1 : nat) := real_mul (real_neg x0) (@COND real (Coq.Arith.PeanoNat.Nat.Even x1) (real_pow x0 x1) (real_neg (real_pow x0 x1))).
Definition term0 (x0 : nat) := (fun y0 : Prop => y0 \/ (~ y0)) (Coq.Arith.PeanoNat.Nat.Even x0).
Definition term10 (x0 : real) := and ((real_pow (real_neg x0) (NUMERAL 0)) = (@COND real (Coq.Arith.PeanoNat.Nat.Even (NUMERAL 0)) (real_pow x0 (NUMERAL 0)) (real_neg (real_pow x0 (NUMERAL 0))))).
Definition term11 (x0 : real) (x1 : nat) := (fun y0 : nat => (real_pow (real_neg x0) y0) = (@COND real (Coq.Arith.PeanoNat.Nat.Even y0) (real_pow x0 y0) (real_neg (real_pow x0 y0)))) x1.
Definition term54 (x0 : real) (x1 : nat) := @eq real (real_pow (real_neg x0) (S x1)).
Definition term41 (x0 : real) := real_neg (real_pow x0 (NUMERAL 0)).
Definition term12 (x0 : real) (x1 : nat) := real_pow (real_neg x0) x1.
Definition term7 (x0 : real) := real_pow (real_neg x0) (NUMERAL 0).
Definition term43 := @COND real True (real_of_num (NUMERAL (BIT1 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term34 := real_of_num (NUMERAL (BIT1 0)).
Definition term75 (x0 : real) (x1 : nat) := @eq real (real_neg (real_mul x0 (real_pow x0 x1))).
Definition term61 (x0 : real) (x1 : nat) := real_neg (real_mul x0 (real_pow x0 x1)).
Definition term39 (x0 : real) := @COND real (Coq.Arith.PeanoNat.Nat.Even (NUMERAL 0)) (real_pow x0 (NUMERAL 0)).
Definition term87 (x0 : real) (x1 : nat) := real_mul x0 (real_neg (real_pow x0 x1)).
Definition term35 (x0 : real) := @eq real (real_pow (real_neg x0) (NUMERAL 0)).
Definition term59 (x0 : real) (x1 : nat) := @COND real (~ (Coq.Arith.PeanoNat.Nat.Even x1)) (real_mul x0 (real_pow x0 x1)).
Definition term28 (x0 : real) := imp (((real_pow (real_neg x0) (NUMERAL 0)) = (@COND real (Coq.Arith.PeanoNat.Nat.Even (NUMERAL 0)) (real_pow x0 (NUMERAL 0)) (real_neg (real_pow x0 (NUMERAL 0))))) /\ (forall y0 : nat, ((real_pow (real_neg x0) y0) = (@COND real (Coq.Arith.PeanoNat.Nat.Even y0) (real_pow x0 y0) (real_neg (real_pow x0 y0)))) -> (real_pow (real_neg x0) (S y0)) = (@COND real (Coq.Arith.PeanoNat.Nat.Even (S y0)) (real_pow x0 (S y0)) (real_neg (real_pow x0 (S y0)))))).
Definition term69 (x0 : nat) := @COND real (Coq.Arith.PeanoNat.Nat.Even x0).
Definition term36 := @eq real (real_of_num (NUMERAL (BIT1 0))).
Definition term24 (x0 : real) := forall y0 : nat, ((real_pow (real_neg x0) y0) = (@COND real (Coq.Arith.PeanoNat.Nat.Even y0) (real_pow x0 y0) (real_neg (real_pow x0 y0)))) -> (real_pow (real_neg x0) (S y0)) = (@COND real (Coq.Arith.PeanoNat.Nat.Even (S y0)) (real_pow x0 (S y0)) (real_neg (real_pow x0 (S y0)))).
Definition term70 (x0 : real) (x1 : nat) := @COND real (Coq.Arith.PeanoNat.Nat.Even x1) (real_pow x0 x1).
Definition term51 (x0 : real) (x1 : nat) := real_mul (real_neg x0) (real_pow (real_neg x0) x1).
Definition term89 (x0 : real) (x1 : nat) := @eq real (real_mul x0 (real_pow x0 x1)).
Definition term1 (x0 : nat) := (Coq.Arith.PeanoNat.Nat.Even x0) \/ (~ (Coq.Arith.PeanoNat.Nat.Even x0)).
Definition term17 (x0 : real) (x1 : nat) := real_pow (real_neg x0) (S x1).
Definition term16 (x0 : real) (x1 : nat) := (fun y0 : nat => (real_pow (real_neg x0) y0) = (@COND real (Coq.Arith.PeanoNat.Nat.Even y0) (real_pow x0 y0) (real_neg (real_pow x0 y0)))) (S x1).
