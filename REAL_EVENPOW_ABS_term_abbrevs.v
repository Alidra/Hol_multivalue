Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term39 (x0 : nat) (x1 : real) := True -> ((x0 = (NUMERAL 0)) \/ ((real_abs (real_abs x1)) = (real_abs x1))) = True.
Definition term2 (x0 : nat) := (fun y0 : nat => forall y1 : real, forall y2 : real, ((real_pow y1 y0) = (real_pow y2 y0)) = (@COND Prop (Coq.Arith.PeanoNat.Nat.Even y0) ((y0 = (NUMERAL 0)) \/ ((real_abs y1) = (real_abs y2))) (y1 = y2))) x0.
Definition term18 (x0 : real) (x1 : nat) (x2 : Prop) := ((Coq.Arith.PeanoNat.Nat.Even x1) -> ((real_pow (real_abs x0) x1) = (real_pow x0 x1)) = x2) -> ((Coq.Arith.PeanoNat.Nat.Even x1) -> (real_pow (real_abs x0) x1) = (real_pow x0 x1)) = ((Coq.Arith.PeanoNat.Nat.Even x1) -> x2).
Definition term53 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term38 (x0 : nat) := (x0 = (NUMERAL 0)) \/ True.
Definition term55 := fun y0 : real => forall y1 : nat, (Coq.Arith.PeanoNat.Nat.Even y1) -> (real_pow (real_abs y0) y1) = (real_pow y0 y1).
Definition term41 (x0 : nat) (x1 : real) (x2 : Prop) := ((~ True) -> ((real_abs x1) = x1) = x2) -> (@COND Prop (Coq.Arith.PeanoNat.Nat.Even x0) ((x0 = (NUMERAL 0)) \/ ((real_abs (real_abs x1)) = (real_abs x1))) ((real_abs x1) = x1)) = (@COND Prop True True x2).
Definition term34 (x0 : nat) (x1 : real) (x2 : Prop) (x3 : Prop) := (True -> ((x0 = (NUMERAL 0)) \/ ((real_abs (real_abs x1)) = (real_abs x1))) = x2) -> ((~ True) -> ((real_abs x1) = x1) = x3) -> (@COND Prop (Coq.Arith.PeanoNat.Nat.Even x0) ((x0 = (NUMERAL 0)) \/ ((real_abs (real_abs x1)) = (real_abs x1))) ((real_abs x1) = x1)) = (@COND Prop True x2 x3).
Definition term56 := fun y0 : real => True.
Definition term21 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) (x3 : Prop) (x4 : a0) := forall y0 : a0, (x0 = x3) -> (x3 -> x1 = x4) -> ((~ x3) -> x2 = y0) -> (@COND a0 x0 x1 x2) = (@COND a0 x3 x4 y0).
Definition term47 (x0 : real) (x1 : nat) := (Coq.Arith.PeanoNat.Nat.Even x1) -> (real_pow (real_abs x0) x1) = (real_pow x0 x1).
Definition term58 := forall y0 : real, True.
Definition term59 (x0 : Prop) := forall y0 : real, x0.
Definition term57 := forall y0 : real, forall y1 : nat, (Coq.Arith.PeanoNat.Nat.Even y1) -> (real_pow (real_abs y0) y1) = (real_pow y0 y1).
Definition term3 (x0 : nat) := forall y0 : real, forall y1 : real, ((real_pow y0 x0) = (real_pow y1 x0)) = (@COND Prop (Coq.Arith.PeanoNat.Nat.Even x0) ((x0 = (NUMERAL 0)) \/ ((real_abs y0) = (real_abs y1))) (y0 = y1)).
Definition term29 (x0 : nat) (x1 : real) (x2 : Prop) (x3 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((Coq.Arith.PeanoNat.Nat.Even x0) = x2) -> (x2 -> ((x0 = (NUMERAL 0)) \/ ((real_abs (real_abs x1)) = (real_abs x1))) = y0) -> ((~ x2) -> ((real_abs x1) = x1) = y1) -> (@COND Prop (Coq.Arith.PeanoNat.Nat.Even x0) ((x0 = (NUMERAL 0)) \/ ((real_abs (real_abs x1)) = (real_abs x1))) ((real_abs x1) = x1)) = (@COND Prop x2 y0 y1)) x3.
Definition term12 (x0 : real) (x1 : nat) := real_pow (real_abs x0) x1.
Definition term48 (x0 : nat) := (Coq.Arith.PeanoNat.Nat.Even x0) -> True.
Definition term43 (x0 : nat) (x1 : real) := ((~ True) -> ((real_abs x1) = x1) = ((real_abs x1) = x1)) -> (@COND Prop (Coq.Arith.PeanoNat.Nat.Even x0) ((x0 = (NUMERAL 0)) \/ ((real_abs (real_abs x1)) = (real_abs x1))) ((real_abs x1) = x1)) = (@COND Prop True True ((real_abs x1) = x1)).
Definition term46 (x0 : real) (x1 : nat) := ((Coq.Arith.PeanoNat.Nat.Even x1) -> ((real_pow (real_abs x0) x1) = (real_pow x0 x1)) = True) -> ((Coq.Arith.PeanoNat.Nat.Even x1) -> (real_pow (real_abs x0) x1) = (real_pow x0 x1)) = ((Coq.Arith.PeanoNat.Nat.Even x1) -> True).
Definition term6 (x0 : nat) (x1 : real) (x2 : real) := (fun y0 : real => ((real_pow x1 x0) = (real_pow y0 x0)) = (@COND Prop (Coq.Arith.PeanoNat.Nat.Even x0) ((x0 = (NUMERAL 0)) \/ ((real_abs x1) = (real_abs y0))) (x1 = y0))) x2.
Definition term1 (x0 : real) := real_abs (real_abs x0).
Definition term8 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term27 (x0 : nat) (x1 : real) (x2 : Prop) := (fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, ((Coq.Arith.PeanoNat.Nat.Even x0) = y0) -> (y0 -> ((x0 = (NUMERAL 0)) \/ ((real_abs (real_abs x1)) = (real_abs x1))) = y1) -> ((~ y0) -> ((real_abs x1) = x1) = y2) -> (@COND Prop (Coq.Arith.PeanoNat.Nat.Even x0) ((x0 = (NUMERAL 0)) \/ ((real_abs (real_abs x1)) = (real_abs x1))) ((real_abs x1) = x1)) = (@COND Prop y0 y1 y2)) x2.
Definition term16 (x0 : real) (x1 : nat) (x2 : Prop) (x3 : Prop) := ((Coq.Arith.PeanoNat.Nat.Even x1) = x2) -> (x2 -> ((real_pow (real_abs x0) x1) = (real_pow x0 x1)) = x3) -> ((Coq.Arith.PeanoNat.Nat.Even x1) -> (real_pow (real_abs x0) x1) = (real_pow x0 x1)) = (x2 -> x3).
Definition term19 (x0 : nat) (x1 : real) := @COND Prop (Coq.Arith.PeanoNat.Nat.Even x0) ((x0 = (NUMERAL 0)) \/ ((real_abs (real_abs x1)) = (real_abs x1))) ((real_abs x1) = x1).
Definition term31 (x0 : nat) (x1 : real) (x2 : Prop) (x3 : Prop) (x4 : Prop) := (fun y0 : Prop => ((Coq.Arith.PeanoNat.Nat.Even x0) = x2) -> (x2 -> ((x0 = (NUMERAL 0)) \/ ((real_abs (real_abs x1)) = (real_abs x1))) = x3) -> ((~ x2) -> ((real_abs x1) = x1) = y0) -> (@COND Prop (Coq.Arith.PeanoNat.Nat.Even x0) ((x0 = (NUMERAL 0)) \/ ((real_abs (real_abs x1)) = (real_abs x1))) ((real_abs x1) = x1)) = (@COND Prop x2 x3 y0)) x4.
Definition term35 (x0 : real) := @eq real (real_abs (real_abs x0)).
Definition term40 (x0 : nat) (x1 : real) (x2 : Prop) := (True -> ((x0 = (NUMERAL 0)) \/ ((real_abs (real_abs x1)) = (real_abs x1))) = True) -> ((~ True) -> ((real_abs x1) = x1) = x2) -> (@COND Prop (Coq.Arith.PeanoNat.Nat.Even x0) ((x0 = (NUMERAL 0)) \/ ((real_abs (real_abs x1)) = (real_abs x1))) ((real_abs x1) = x1)) = (@COND Prop True True x2).
Definition term37 (x0 : nat) := or (x0 = (NUMERAL 0)).
Definition term45 (x0 : real) (x1 : nat) := (Coq.Arith.PeanoNat.Nat.Even x1) -> ((real_pow (real_abs x0) x1) = (real_pow x0 x1)) = True.
Definition term15 (x0 : real) (x1 : nat) (x2 : Prop) (x3 : Prop) := (fun y0 : Prop => ((Coq.Arith.PeanoNat.Nat.Even x1) = x2) -> (x2 -> ((real_pow (real_abs x0) x1) = (real_pow x0 x1)) = y0) -> ((Coq.Arith.PeanoNat.Nat.Even x1) -> (real_pow (real_abs x0) x1) = (real_pow x0 x1)) = (x2 -> y0)) x3.
Definition term52 := forall y0 : nat, True.
Definition term44 (x0 : real) := @COND Prop True True ((real_abs x0) = x0).
Definition term51 (x0 : real) := forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even y0) -> (real_pow (real_abs x0) y0) = (real_pow x0 y0).
Definition term36 (x0 : real) := @eq real (real_abs x0).
Definition term5 (x0 : nat) (x1 : real) := forall y0 : real, ((real_pow x1 x0) = (real_pow y0 x0)) = (@COND Prop (Coq.Arith.PeanoNat.Nat.Even x0) ((x0 = (NUMERAL 0)) \/ ((real_abs x1) = (real_abs y0))) (x1 = y0)).
Definition term50 := fun y0 : nat => True.
Definition term30 (x0 : nat) (x1 : real) (x2 : Prop) (x3 : Prop) := forall y0 : Prop, ((Coq.Arith.PeanoNat.Nat.Even x0) = x2) -> (x2 -> ((x0 = (NUMERAL 0)) \/ ((real_abs (real_abs x1)) = (real_abs x1))) = x3) -> ((~ x2) -> ((real_abs x1) = x1) = y0) -> (@COND Prop (Coq.Arith.PeanoNat.Nat.Even x0) ((x0 = (NUMERAL 0)) \/ ((real_abs (real_abs x1)) = (real_abs x1))) ((real_abs x1) = x1)) = (@COND Prop x2 x3 y0).
Definition term14 (x0 : real) (x1 : nat) (x2 : Prop) := forall y0 : Prop, ((Coq.Arith.PeanoNat.Nat.Even x1) = x2) -> (x2 -> ((real_pow (real_abs x0) x1) = (real_pow x0 x1)) = y0) -> ((Coq.Arith.PeanoNat.Nat.Even x1) -> (real_pow (real_abs x0) x1) = (real_pow x0 x1)) = (x2 -> y0).
Definition term9 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term17 (x0 : real) (x1 : nat) (x2 : Prop) := ((Coq.Arith.PeanoNat.Nat.Even x1) = (Coq.Arith.PeanoNat.Nat.Even x1)) -> ((Coq.Arith.PeanoNat.Nat.Even x1) -> ((real_pow (real_abs x0) x1) = (real_pow x0 x1)) = x2) -> ((Coq.Arith.PeanoNat.Nat.Even x1) -> (real_pow (real_abs x0) x1) = (real_pow x0 x1)) = ((Coq.Arith.PeanoNat.Nat.Even x1) -> x2).
Definition term0 (x0 : real) := (fun y0 : real => (real_abs (real_abs y0)) = (real_abs y0)) x0.
Definition term28 (x0 : nat) (x1 : real) (x2 : Prop) := forall y0 : Prop, forall y1 : Prop, ((Coq.Arith.PeanoNat.Nat.Even x0) = x2) -> (x2 -> ((x0 = (NUMERAL 0)) \/ ((real_abs (real_abs x1)) = (real_abs x1))) = y0) -> ((~ x2) -> ((real_abs x1) = x1) = y1) -> (@COND Prop (Coq.Arith.PeanoNat.Nat.Even x0) ((x0 = (NUMERAL 0)) \/ ((real_abs (real_abs x1)) = (real_abs x1))) ((real_abs x1) = x1)) = (@COND Prop x2 y0 y1).
Definition term25 (x0 : nat) (x1 : real) := forall y0 : Prop, forall y1 : Prop, forall y2 : Prop, ((Coq.Arith.PeanoNat.Nat.Even x0) = y0) -> (y0 -> ((x0 = (NUMERAL 0)) \/ ((real_abs (real_abs x1)) = (real_abs x1))) = y1) -> ((~ y0) -> ((real_abs x1) = x1) = y2) -> (@COND Prop (Coq.Arith.PeanoNat.Nat.Even x0) ((x0 = (NUMERAL 0)) \/ ((real_abs (real_abs x1)) = (real_abs x1))) ((real_abs x1) = x1)) = (@COND Prop y0 y1 y2).
Definition term24 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, forall y1 : Prop, forall y2 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> ((~ y0) -> x2 = y2) -> (@COND Prop x0 x1 x2) = (@COND Prop y0 y1 y2).
Definition term23 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) := forall y0 : Prop, forall y1 : a0, forall y2 : a0, (x0 = y0) -> (y0 -> x1 = y1) -> ((~ y0) -> x2 = y2) -> (@COND a0 x0 x1 x2) = (@COND a0 y0 y1 y2).
Definition term11 (x0 : real) (x1 : nat) := forall y0 : Prop, forall y1 : Prop, ((Coq.Arith.PeanoNat.Nat.Even x1) = y0) -> (y0 -> ((real_pow (real_abs x0) x1) = (real_pow x0 x1)) = y1) -> ((Coq.Arith.PeanoNat.Nat.Even x1) -> (real_pow (real_abs x0) x1) = (real_pow x0 x1)) = (y0 -> y1).
Definition term10 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term4 (x0 : nat) (x1 : real) := (fun y0 : real => forall y1 : real, ((real_pow y0 x0) = (real_pow y1 x0)) = (@COND Prop (Coq.Arith.PeanoNat.Nat.Even x0) ((x0 = (NUMERAL 0)) \/ ((real_abs y0) = (real_abs y1))) (y0 = y1))) x1.
Definition term32 (x0 : nat) (x1 : real) (x2 : Prop) (x3 : Prop) (x4 : Prop) := ((Coq.Arith.PeanoNat.Nat.Even x0) = x2) -> (x2 -> ((x0 = (NUMERAL 0)) \/ ((real_abs (real_abs x1)) = (real_abs x1))) = x3) -> ((~ x2) -> ((real_abs x1) = x1) = x4) -> (@COND Prop (Coq.Arith.PeanoNat.Nat.Even x0) ((x0 = (NUMERAL 0)) \/ ((real_abs (real_abs x1)) = (real_abs x1))) ((real_abs x1) = x1)) = (@COND Prop x2 x3 x4).
Definition term22 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) (x3 : Prop) := forall y0 : a0, forall y1 : a0, (x0 = x3) -> (x3 -> x1 = y0) -> ((~ x3) -> x2 = y1) -> (@COND a0 x0 x1 x2) = (@COND a0 x3 y0 y1).
Definition term42 (x0 : real) := (~ True) -> ((real_abs x0) = x0) = ((real_abs x0) = x0).
Definition term54 (x0 : Prop) := forall y0 : nat, x0.
Definition term7 (x0 : nat) (x1 : real) (x2 : real) := @COND Prop (Coq.Arith.PeanoNat.Nat.Even x0) ((x0 = (NUMERAL 0)) \/ ((real_abs x1) = (real_abs x2))) (x1 = x2).
Definition term33 (x0 : nat) (x1 : real) (x2 : Prop) (x3 : Prop) := ((Coq.Arith.PeanoNat.Nat.Even x0) = True) -> (True -> ((x0 = (NUMERAL 0)) \/ ((real_abs (real_abs x1)) = (real_abs x1))) = x2) -> ((~ True) -> ((real_abs x1) = x1) = x3) -> (@COND Prop (Coq.Arith.PeanoNat.Nat.Even x0) ((x0 = (NUMERAL 0)) \/ ((real_abs (real_abs x1)) = (real_abs x1))) ((real_abs x1) = x1)) = (@COND Prop True x2 x3).
Definition term26 (x0 : nat) (x1 : real) := (x0 = (NUMERAL 0)) \/ ((real_abs (real_abs x1)) = (real_abs x1)).
Definition term49 (x0 : real) := fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even y0) -> (real_pow (real_abs x0) y0) = (real_pow x0 y0).
Definition term13 (x0 : real) (x1 : nat) (x2 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((Coq.Arith.PeanoNat.Nat.Even x1) = y0) -> (y0 -> ((real_pow (real_abs x0) x1) = (real_pow x0 x1)) = y1) -> ((Coq.Arith.PeanoNat.Nat.Even x1) -> (real_pow (real_abs x0) x1) = (real_pow x0 x1)) = (y0 -> y1)) x2.
Definition term20 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) (x3 : Prop) (x4 : a0) (x5 : a0) := (x0 = x3) -> (x3 -> x1 = x4) -> ((~ x3) -> x2 = x5) -> (@COND a0 x0 x1 x2) = (@COND a0 x3 x4 x5).