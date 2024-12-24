Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term145 := fun y0 : nat => forall y1 : real, forall y2 : real, ((y0 = (NUMERAL 0)) \/ (~ ((real_pow y1 y0) = (real_pow y2 y0)))) \/ ((real_abs y1) = (real_abs y2)).
Definition term128 := fun y0 : nat => forall y1 : real, forall y2 : real, ((~ (y0 = (NUMERAL 0))) /\ ((real_pow y1 y0) = (real_pow y2 y0))) -> (real_abs y1) = (real_abs y2).
Definition term67 (x0 : Prop) (x1 : Prop) (x2 : real) (x3 : real) (x4 : nat) (x5 : Prop) := (x1 -> (fun y0 : Prop => ((real_pow x2 x4) = (real_pow x3 x4)) = y0) x0) /\ ((~ x1) -> (fun y0 : Prop => ((real_pow x2 x4) = (real_pow x3 x4)) = y0) x5).
Definition term175 := (~ False) -> False.
Definition term139 (x0 : nat) (x1 : real) (x2 : real) := ((x0 = (NUMERAL 0)) \/ (~ ((real_pow x1 x0) = (real_pow x2 x0)))) \/ ((real_abs x1) = (real_abs x2)).
Definition term89 (x0 : nat) (x1 : real) (x2 : real) := (fun y0 : real => (Coq.Arith.PeanoNat.Nat.Odd x0) -> ((real_pow x1 x0) = (real_pow y0 x0)) = (x1 = y0)) x2.
Definition term82 (x0 : nat) (x1 : real) (x2 : real) := @eq Prop ((fun y0 : Prop => ((real_pow x1 x0) = (real_pow x2 x0)) = y0) (@COND Prop (Coq.Arith.PeanoNat.Nat.Even x0) ((real_abs x1) = (real_abs x2)) (x1 = x2))).
Definition term147 (x0 : nat) := (fun y0 : nat => forall y1 : real, forall y2 : real, ((y0 = (NUMERAL 0)) \/ (~ ((real_pow y1 y0) = (real_pow y2 y0)))) \/ ((real_abs y1) = (real_abs y2))) x0.
Definition term85 (x0 : nat) := (fun y0 : nat => forall y1 : real, forall y2 : real, (Coq.Arith.PeanoNat.Nat.Odd y0) -> ((real_pow y1 y0) = (real_pow y2 y0)) = (y1 = y2)) x0.
Definition term43 := forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even (NUMERAL y0)) = (Coq.Arith.PeanoNat.Nat.Even y0).
Definition term53 := @eq nat (NUMERAL 0).
Definition term56 (x0 : real) (x1 : real) := True \/ ((real_abs x0) = (real_abs x1)).
Definition term168 (x0 : Prop) := ~ (~ x0).
Definition term135 (x0 : real) (x1 : real) (x2 : nat) := ~ ((~ (x2 = (NUMERAL 0))) /\ ((real_pow x0 x2) = (real_pow x1 x2))).
Definition term192 (x0 : real) (x1 : nat) := real_pow (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) x1.
Definition term36 := ((0 = 0) = True) /\ ((forall y0 : nat, ((BIT0 y0) = 0) = (y0 = 0)) /\ ((forall y0 : nat, ((BIT1 y0) = 0) = False) /\ ((forall y0 : nat, (0 = (BIT0 y0)) = (0 = y0)) /\ ((forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1))))))))).
Definition term35 := (forall y0 : nat, forall y1 : nat, ((NUMERAL y0) = (NUMERAL y1)) = (y0 = y1)) /\ (((0 = 0) = True) /\ ((forall y0 : nat, ((BIT0 y0) = 0) = (y0 = 0)) /\ ((forall y0 : nat, ((BIT1 y0) = 0) = False) /\ ((forall y0 : nat, (0 = (BIT0 y0)) = (0 = y0)) /\ ((forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1)))))))))).
Definition term154 (x0 : real) (x1 : real) (x2 : nat) := (~ ((real_pow x0 x2) = (real_pow x1 x2))) -> (real_pow x0 x2) = (real_pow x1 x2).
Definition term62 (x0 : nat) (x1 : real) (x2 : real) := @COND Prop (Coq.Arith.PeanoNat.Nat.Even x0) ((real_abs x1) = (real_abs x2)).
Definition term116 (x0 : real) := fun y0 : real => forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (Coq.Arith.PeanoNat.Nat.Even y1) -> (~ (((real_pow y0 y1) = (real_pow x0 y1)) -> (real_abs y0) = (real_abs x0))) -> ~ (forall y2 : nat, forall y3 : real, forall y4 : real, ((~ (y2 = (NUMERAL 0))) /\ ((real_pow y3 y2) = (real_pow y4 y2))) -> (real_abs y3) = (real_abs y4)).
Definition term115 (x0 : real) := fun y0 : real => forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (Coq.Arith.PeanoNat.Nat.Even y1) -> (~ (((real_pow y0 y1) = (real_pow x0 y1)) -> (real_abs y0) = (real_abs x0))) -> (forall y2 : nat, forall y3 : real, forall y4 : real, ((~ (y2 = (NUMERAL 0))) /\ ((real_pow y3 y2) = (real_pow y4 y2))) -> (real_abs y3) = (real_abs y4)) -> False.
Definition term23 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0).
Definition term93 (x0 : Prop) := (~ x0) -> False.
Definition term2 (x0 : real) (x1 : nat) := fun y0 : nat => (real_pow (real_pow x0 x1) y0) = (real_pow x0 (Nat.mul x1 y0)).
Definition term178 (x0 : real) (x1 : real) (x2 : nat) := (fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> (Coq.Arith.PeanoNat.Nat.Even y0) -> (~ (((real_pow x0 y0) = (real_pow x1 y0)) -> (real_abs x0) = (real_abs x1))) -> (forall y1 : nat, forall y2 : real, forall y3 : real, ((~ (y1 = (NUMERAL 0))) /\ ((real_pow y2 y1) = (real_pow y3 y1))) -> (real_abs y2) = (real_abs y3)) -> False) x2.
Definition term95 (x0 : nat) (x1 : real) (x2 : real) := (~ (((real_pow x1 x0) = (real_pow x2 x0)) -> (real_abs x1) = (real_abs x2))) -> False.
Definition term27 (x0 : nat) := ~ (Coq.Arith.PeanoNat.Nat.Even x0).
Definition term198 (x0 : real) (x1 : real) (x2 : nat) := (((real_pow x0 x2) = (real_pow x1 x2)) -> (real_abs x0) = (real_abs x1)) /\ (((real_abs x0) = (real_abs x1)) -> (real_pow x0 x2) = (real_pow x1 x2)).
Definition term83 (x0 : nat) (x1 : real) (x2 : real) := @eq Prop (((real_pow x1 x0) = (real_pow x2 x0)) = (@COND Prop (Coq.Arith.PeanoNat.Nat.Even x0) ((real_abs x1) = (real_abs x2)) (x1 = x2))).
Definition term39 (x0 : nat) := forall y0 : nat, ((NUMERAL x0) = (NUMERAL y0)) = (x0 = y0).
Definition term0 (x0 : real) (x1 : nat) (x2 : nat) := real_pow (real_pow x0 x1) x2.
Definition term51 := Coq.Arith.PeanoNat.Nat.Even (NUMERAL 0).
Definition term124 (x0 : nat) (x1 : real) := fun y0 : real => ((~ (x0 = (NUMERAL 0))) /\ ((real_pow x1 x0) = (real_pow y0 x0))) -> (real_abs x1) = (real_abs y0).
Definition term195 (x0 : real) (x1 : nat) := @eq real (real_pow x0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)).
Definition term50 (x0 : real) (x1 : real) (x2 : nat) := @eq Prop ((real_pow x0 x2) = (real_pow x1 x2)).
Definition term90 (x0 : nat) (x1 : real) (x2 : real) := (Coq.Arith.PeanoNat.Nat.Odd x0) -> ((real_pow x1 x0) = (real_pow x2 x0)) = (x1 = x2).
Definition term162 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term44 (x0 : nat) := (fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even (NUMERAL y0)) = (Coq.Arith.PeanoNat.Nat.Even y0)) x0.
Definition term172 (x0 : real) (x1 : real) (x2 : nat) := imp ((~ (x2 = (NUMERAL 0))) /\ ((real_pow x0 x2) = (real_pow x1 x2))).
Definition term102 := ~ (forall y0 : nat, forall y1 : real, forall y2 : real, ((~ (y0 = (NUMERAL 0))) /\ ((real_pow y1 y0) = (real_pow y2 y0))) -> (real_abs y1) = (real_abs y2)).
Definition term155 (x0 : Prop) := (~ x0) -> x0.
Definition term14 (x0 : nat) := (fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even y0) = (exists y1 : nat, y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) x0.
Definition term194 (x0 : real) := real_pow (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term55 (x0 : nat) (x1 : real) (x2 : real) := (x0 = (NUMERAL 0)) \/ ((real_abs x1) = (real_abs x2)).
Definition term109 (x0 : nat) := imp (~ (x0 = (NUMERAL 0))).
Definition term77 (x0 : nat) (x1 : real) (x2 : real) := (Coq.Arith.PeanoNat.Nat.Even x0) -> (fun y0 : Prop => ((real_pow x1 x0) = (real_pow x2 x0)) = y0) ((real_abs x1) = (real_abs x2)).
Definition term46 (x0 : real) := real_pow x0 (NUMERAL 0).
Definition term18 (x0 : real) (x1 : real) := (fun y0 : real => ((real_abs x0) = (real_abs y0)) = ((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))))) x1.
Definition term165 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term138 (x0 : nat) (x1 : real) (x2 : real) := (~ ((~ (x0 = (NUMERAL 0))) /\ ((real_pow x1 x0) = (real_pow x2 x0)))) \/ ((real_abs x1) = (real_abs x2)).
Definition term76 (x0 : nat) := imp (Coq.Arith.PeanoNat.Nat.Even x0).
Definition term200 (x0 : nat) := forall y0 : real, forall y1 : real, ((real_pow y0 x0) = (real_pow y1 x0)) = (@COND Prop (Coq.Arith.PeanoNat.Nat.Even x0) ((x0 = (NUMERAL 0)) \/ ((real_abs y0) = (real_abs y1))) (y0 = y1)).
Definition term144 (x0 : nat) := forall y0 : real, forall y1 : real, ((x0 = (NUMERAL 0)) \/ (~ ((real_pow y0 x0) = (real_pow y1 x0)))) \/ ((real_abs y0) = (real_abs y1)).
Definition term127 (x0 : nat) := forall y0 : real, forall y1 : real, ((~ (x0 = (NUMERAL 0))) /\ ((real_pow y0 x0) = (real_pow y1 x0))) -> (real_abs y0) = (real_abs y1).
Definition term122 := forall y0 : real, forall y1 : real, forall y2 : nat, (~ (y2 = (NUMERAL 0))) -> (Coq.Arith.PeanoNat.Nat.Even y2) -> (~ (((real_pow y1 y2) = (real_pow y0 y2)) -> (real_abs y1) = (real_abs y0))) -> ~ (forall y3 : nat, forall y4 : real, forall y5 : real, ((~ (y3 = (NUMERAL 0))) /\ ((real_pow y4 y3) = (real_pow y5 y3))) -> (real_abs y4) = (real_abs y5)).
Definition term121 := forall y0 : real, forall y1 : real, forall y2 : nat, (~ (y2 = (NUMERAL 0))) -> (Coq.Arith.PeanoNat.Nat.Even y2) -> (~ (((real_pow y1 y2) = (real_pow y0 y2)) -> (real_abs y1) = (real_abs y0))) -> (forall y3 : nat, forall y4 : real, forall y5 : real, ((~ (y3 = (NUMERAL 0))) /\ ((real_pow y4 y3) = (real_pow y5 y3))) -> (real_abs y4) = (real_abs y5)) -> False.
Definition term118 (x0 : real) := forall y0 : real, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (Coq.Arith.PeanoNat.Nat.Even y1) -> (~ (((real_pow y0 y1) = (real_pow x0 y1)) -> (real_abs y0) = (real_abs x0))) -> ~ (forall y2 : nat, forall y3 : real, forall y4 : real, ((~ (y2 = (NUMERAL 0))) /\ ((real_pow y3 y2) = (real_pow y4 y2))) -> (real_abs y3) = (real_abs y4)).
Definition term117 (x0 : real) := forall y0 : real, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (Coq.Arith.PeanoNat.Nat.Even y1) -> (~ (((real_pow y0 y1) = (real_pow x0 y1)) -> (real_abs y0) = (real_abs x0))) -> (forall y2 : nat, forall y3 : real, forall y4 : real, ((~ (y2 = (NUMERAL 0))) /\ ((real_pow y3 y2) = (real_pow y4 y2))) -> (real_abs y3) = (real_abs y4)) -> False.
Definition term86 (x0 : nat) := forall y0 : real, forall y1 : real, (Coq.Arith.PeanoNat.Nat.Odd x0) -> ((real_pow y0 x0) = (real_pow y1 x0)) = (y0 = y1).
Definition term13 := forall y0 : real, forall y1 : nat, forall y2 : nat, (real_pow y0 (Nat.mul y1 y2)) = (real_pow (real_pow y0 y1) y2).
Definition term12 := forall y0 : real, forall y1 : nat, forall y2 : nat, (real_pow (real_pow y0 y1) y2) = (real_pow y0 (Nat.mul y1 y2)).
Definition term71 (x0 : nat) (x1 : real) (x2 : real) := (fun y0 : Prop => ((real_pow x1 x0) = (real_pow x2 x0)) = y0) (x1 = x2).
Definition term5 (x0 : real) (x1 : nat) := forall y0 : nat, (real_pow x0 (Nat.mul x1 y0)) = (real_pow (real_pow x0 x1) y0).
Definition term75 (x0 : nat) (x1 : real) (x2 : real) := (fun y0 : Prop => ((real_pow x1 x0) = (real_pow x2 x0)) = y0) ((real_abs x1) = (real_abs x2)).
Definition term181 (x0 : real) (x1 : real) (x2 : nat) := ((real_abs x0) = (real_abs x1)) -> (real_pow x0 x2) = (real_pow x1 x2).
Definition term185 (x0 : real) (x1 : real) (x2 : nat) := (fun y0 : nat => (real_pow x0 y0) = (real_pow x1 y0)) x2.
Definition term112 (x0 : real) (x1 : real) := fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> (Coq.Arith.PeanoNat.Nat.Even y0) -> (~ (((real_pow x0 y0) = (real_pow x1 y0)) -> (real_abs x0) = (real_abs x1))) -> ~ (forall y1 : nat, forall y2 : real, forall y3 : real, ((~ (y1 = (NUMERAL 0))) /\ ((real_pow y2 y1) = (real_pow y3 y1))) -> (real_abs y2) = (real_abs y3)).
Definition term25 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term190 (x0 : real) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (real_pow x0 (Nat.mul y0 y1)) = (real_pow (real_pow x0 y0) y1)) x1.
Definition term34 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term7 (x0 : real) := fun y0 : nat => forall y1 : nat, (real_pow x0 (Nat.mul y0 y1)) = (real_pow (real_pow x0 y0) y1).
Definition term65 (x0 : Prop) (x1 : Prop) (x2 : Prop -> Prop) (x3 : Prop) := (x1 -> x2 x0) /\ ((~ x1) -> x2 x3).
Definition term91 (x0 : nat) := (~ (Coq.Arith.PeanoNat.Nat.Even x0)) -> (Coq.Arith.PeanoNat.Nat.Even x0) = False.
Definition term105 (x0 : nat) (x1 : real) (x2 : real) := (~ (((real_pow x1 x0) = (real_pow x2 x0)) -> (real_abs x1) = (real_abs x2))) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((~ (y0 = (NUMERAL 0))) /\ ((real_pow y1 y0) = (real_pow y2 y0))) -> (real_abs y1) = (real_abs y2)) -> False.
Definition term182 (x0 : real) (x1 : real) (x2 : nat) := ((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))) -> (real_pow x0 x2) = (real_pow x1 x2).
Definition term74 (x0 : nat) (x1 : real) (x2 : real) := (~ (Coq.Arith.PeanoNat.Nat.Even x0)) -> ((real_pow x1 x0) = (real_pow x2 x0)) = (x1 = x2).
Definition term59 (x0 : real) (x1 : real) := @COND Prop True True (x0 = x1).
Definition term184 (x0 : real) (x1 : real) := fun y0 : nat => (real_pow x0 y0) = (real_pow x1 y0).
Definition term143 (x0 : nat) := fun y0 : real => forall y1 : real, ((x0 = (NUMERAL 0)) \/ (~ ((real_pow y0 x0) = (real_pow y1 x0)))) \/ ((real_abs y0) = (real_abs y1)).
Definition term126 (x0 : nat) := fun y0 : real => forall y1 : real, ((~ (x0 = (NUMERAL 0))) /\ ((real_pow y0 x0) = (real_pow y1 x0))) -> (real_abs y0) = (real_abs y1).
Definition term31 := forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Odd y0) = (~ (Coq.Arith.PeanoNat.Nat.Even y0)).
Definition term183 (x0 : nat) := Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0.
Definition term133 (x0 : real) (x1 : real) (x2 : nat) := (~ (~ (x2 = (NUMERAL 0)))) \/ (~ ((real_pow x0 x2) = (real_pow x1 x2))).
Definition term101 := (forall y0 : nat, forall y1 : real, forall y2 : real, ((~ (y0 = (NUMERAL 0))) /\ ((real_pow y1 y0) = (real_pow y2 y0))) -> (real_abs y1) = (real_abs y2)) -> False.
Definition term114 (x0 : real) (x1 : real) := forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> (Coq.Arith.PeanoNat.Nat.Even y0) -> (~ (((real_pow x0 y0) = (real_pow x1 y0)) -> (real_abs x0) = (real_abs x1))) -> ~ (forall y1 : nat, forall y2 : real, forall y3 : real, ((~ (y1 = (NUMERAL 0))) /\ ((real_pow y2 y1) = (real_pow y3 y1))) -> (real_abs y2) = (real_abs y3)).
Definition term113 (x0 : real) (x1 : real) := forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> (Coq.Arith.PeanoNat.Nat.Even y0) -> (~ (((real_pow x0 y0) = (real_pow x1 y0)) -> (real_abs x0) = (real_abs x1))) -> (forall y1 : nat, forall y2 : real, forall y3 : real, ((~ (y1 = (NUMERAL 0))) /\ ((real_pow y2 y1) = (real_pow y3 y1))) -> (real_abs y2) = (real_abs y3)) -> False.
Definition term19 (x0 : real) := real_pow x0 (NUMERAL (BIT0 (BIT1 0))).
Definition term100 (x0 : nat) (x1 : real) (x2 : real) := (((~ (x0 = (NUMERAL 0))) -> (Coq.Arith.PeanoNat.Nat.Even x0) -> (~ (((real_pow x1 x0) = (real_pow x2 x0)) -> (real_abs x1) = (real_abs x2))) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((~ (y0 = (NUMERAL 0))) /\ ((real_pow y1 y0) = (real_pow y2 y0))) -> (real_abs y1) = (real_abs y2)) -> False) -> (~ (x0 = (NUMERAL 0))) -> (Coq.Arith.PeanoNat.Nat.Even x0) -> (~ (((real_pow x1 x0) = (real_pow x2 x0)) -> (real_abs x1) = (real_abs x2))) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((~ (y0 = (NUMERAL 0))) /\ ((real_pow y1 y0) = (real_pow y2 y0))) -> (real_abs y1) = (real_abs y2)) -> False) -> ((~ (x0 = (NUMERAL 0))) -> (Coq.Arith.PeanoNat.Nat.Even x0) -> (~ (((real_pow x1 x0) = (real_pow x2 x0)) -> (real_abs x1) = (real_abs x2))) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((~ (y0 = (NUMERAL 0))) /\ ((real_pow y1 y0) = (real_pow y2 y0))) -> (real_abs y1) = (real_abs y2)) -> False) -> (~ (x0 = (NUMERAL 0))) -> (Coq.Arith.PeanoNat.Nat.Even x0) -> (~ (((real_pow x1 x0) = (real_pow x2 x0)) -> (real_abs x1) = (real_abs x2))) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((~ (y0 = (NUMERAL 0))) /\ ((real_pow y1 y0) = (real_pow y2 y0))) -> (real_abs y1) = (real_abs y2)) -> False.
Definition term104 (x0 : nat) (x1 : real) (x2 : real) := imp (~ (((real_pow x1 x0) = (real_pow x2 x0)) -> (real_abs x1) = (real_abs x2))).
Definition term171 (x0 : real) (x1 : real) (x2 : nat) := imp (~ ((x2 = (NUMERAL 0)) \/ (~ ((real_pow x0 x2) = (real_pow x1 x2))))).
Definition term30 := forall y0 : nat, (~ (Coq.Arith.PeanoNat.Nat.Even y0)) = (Coq.Arith.PeanoNat.Nat.Odd y0).
Definition term69 (x0 : nat) (x1 : real) (x2 : real) := (fun y0 : Prop => ((real_pow x1 x0) = (real_pow x2 x0)) = y0) (@COND Prop (Coq.Arith.PeanoNat.Nat.Even x0) ((real_abs x1) = (real_abs x2)) (x1 = x2)).
Definition term20 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, (y0 \/ (y1 \/ y2)) = ((y0 \/ y1) \/ y2)) x0.
Definition term132 (x0 : nat) := or (~ (~ (x0 = (NUMERAL 0)))).
Definition term70 (x0 : nat) (x1 : real) (x2 : real) := ((Coq.Arith.PeanoNat.Nat.Even x0) -> (fun y0 : Prop => ((real_pow x1 x0) = (real_pow x2 x0)) = y0) ((real_abs x1) = (real_abs x2))) /\ ((~ (Coq.Arith.PeanoNat.Nat.Even x0)) -> (fun y0 : Prop => ((real_pow x1 x0) = (real_pow x2 x0)) = y0) (x1 = x2)).
Definition term140 (x0 : real) (x1 : real) (x2 : nat) := (~ (x2 = (NUMERAL 0))) /\ ((real_pow x0 x2) = (real_pow x1 x2)).
Definition term17 (x0 : real) := forall y0 : real, ((real_abs x0) = (real_abs y0)) = ((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))).
Definition term66 (x0 : real) (x1 : real) (x2 : nat) (x3 : Prop) (x4 : Prop) (x5 : Prop) := (fun y0 : Prop => ((real_pow x0 x2) = (real_pow x1 x2)) = y0) (@COND Prop x3 x4 x5).
Definition term54 (x0 : nat) := or (x0 = (NUMERAL 0)).
Definition term29 := fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Odd y0) = (~ (Coq.Arith.PeanoNat.Nat.Even y0)).
Definition term131 (x0 : real) (x1 : real) (x2 : nat) := ~ ((real_pow x0 x2) = (real_pow x1 x2)).
Definition term164 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term125 (x0 : nat) (x1 : real) := forall y0 : real, ((~ (x0 = (NUMERAL 0))) /\ ((real_pow x1 x0) = (real_pow y0 x0))) -> (real_abs x1) = (real_abs y0).
Definition term156 (x0 : nat) (x1 : real) (x2 : real) := (~ ((real_pow x1 x0) = (real_pow x2 x0))) \/ ((real_abs x1) = (real_abs x2)).
Definition term201 := forall y0 : nat, forall y1 : real, forall y2 : real, ((real_pow y1 y0) = (real_pow y2 y0)) = (@COND Prop (Coq.Arith.PeanoNat.Nat.Even y0) ((y0 = (NUMERAL 0)) \/ ((real_abs y1) = (real_abs y2))) (y1 = y2)).
Definition term146 := forall y0 : nat, forall y1 : real, forall y2 : real, ((y0 = (NUMERAL 0)) \/ (~ ((real_pow y1 y0) = (real_pow y2 y0)))) \/ ((real_abs y1) = (real_abs y2)).
Definition term103 := forall y0 : nat, forall y1 : real, forall y2 : real, ((~ (y0 = (NUMERAL 0))) /\ ((real_pow y1 y0) = (real_pow y2 y0))) -> (real_abs y1) = (real_abs y2).
Definition term37 := forall y0 : nat, forall y1 : nat, ((NUMERAL y0) = (NUMERAL y1)) = (y0 = y1).
Definition term9 (x0 : real) := forall y0 : nat, forall y1 : nat, (real_pow x0 (Nat.mul y0 y1)) = (real_pow (real_pow x0 y0) y1).
Definition term8 (x0 : real) := forall y0 : nat, forall y1 : nat, (real_pow (real_pow x0 y0) y1) = (real_pow x0 (Nat.mul y0 y1)).
Definition term160 (x0 : real) (x1 : real) (x2 : nat) := @eq Prop ((x2 = (NUMERAL 0)) \/ (((real_abs x0) = (real_abs x1)) \/ (~ ((real_pow x0 x2) = (real_pow x1 x2))))).
Definition term151 (x0 : real) (x1 : real) := ~ ((real_abs x0) = (real_abs x1)).
Definition term161 (x0 : real) (x1 : real) (x2 : nat) := ((real_abs x0) = (real_abs x1)) \/ ((x2 = (NUMERAL 0)) \/ (~ ((real_pow x0 x2) = (real_pow x1 x2)))).
Definition term141 (x0 : nat) (x1 : real) := fun y0 : real => ((x0 = (NUMERAL 0)) \/ (~ ((real_pow x1 x0) = (real_pow y0 x0)))) \/ ((real_abs x1) = (real_abs y0)).
Definition term33 (x0 : nat) := (x0 = (NUMERAL 0)) \/ (~ (x0 = (NUMERAL 0))).
Definition term163 (x0 : nat) (x1 : real) (x2 : real) := (~ ((x0 = (NUMERAL 0)) \/ (~ ((real_pow x1 x0) = (real_pow x2 x0))))) -> (real_abs x1) = (real_abs x2).
Definition term79 (x0 : nat) (x1 : real) (x2 : real) := and ((Coq.Arith.PeanoNat.Nat.Even x0) -> (fun y0 : Prop => ((real_pow x1 x0) = (real_pow x2 x0)) = y0) ((real_abs x1) = (real_abs x2))).
Definition term136 (x0 : real) (x1 : real) (x2 : nat) := or (~ ((~ (x2 = (NUMERAL 0))) /\ ((real_pow x0 x2) = (real_pow x1 x2)))).
Definition term92 (x0 : real) (x1 : real) := @eq Prop (x0 = x1).
Definition term159 (x0 : nat) (x1 : real) (x2 : real) := @eq Prop ((x0 = (NUMERAL 0)) \/ ((~ ((real_pow x1 x0) = (real_pow x2 x0))) \/ ((real_abs x1) = (real_abs x2)))).
Definition term26 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 \/ x1) \/ x2.
Definition term108 (x0 : nat) (x1 : real) (x2 : real) := (Coq.Arith.PeanoNat.Nat.Even x0) -> (~ (((real_pow x1 x0) = (real_pow x2 x0)) -> (real_abs x1) = (real_abs x2))) -> ~ (forall y0 : nat, forall y1 : real, forall y2 : real, ((~ (y0 = (NUMERAL 0))) /\ ((real_pow y1 y0) = (real_pow y2 y0))) -> (real_abs y1) = (real_abs y2)).
Definition term16 (x0 : real) := (fun y0 : real => forall y1 : real, ((real_abs y0) = (real_abs y1)) = ((real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_pow y1 (NUMERAL (BIT0 (BIT1 0)))))) x0.
Definition term15 (x0 : nat) := exists y0 : nat, x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0).
Definition term199 (x0 : nat) (x1 : real) := forall y0 : real, ((real_pow x1 x0) = (real_pow y0 x0)) = (@COND Prop (Coq.Arith.PeanoNat.Nat.Even x0) ((x0 = (NUMERAL 0)) \/ ((real_abs x1) = (real_abs y0))) (x1 = y0)).
Definition term94 (x0 : nat) (x1 : real) (x2 : real) := ((real_pow x1 x0) = (real_pow x2 x0)) -> (real_abs x1) = (real_abs x2).
Definition term158 (x0 : real) (x1 : real) (x2 : nat) := (x2 = (NUMERAL 0)) \/ (((real_abs x0) = (real_abs x1)) \/ (~ ((real_pow x0 x2) = (real_pow x1 x2)))).
Definition term191 (x0 : real) (x1 : nat) (x2 : nat) := (fun y0 : nat => (real_pow x0 (Nat.mul x1 y0)) = (real_pow (real_pow x0 x1) y0)) x2.
Definition term152 (x0 : nat) := (x0 = (NUMERAL 0)) -> ~ (x0 = (NUMERAL 0)).
Definition term21 (x0 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1).
Definition term148 (x0 : nat) (x1 : real) := (fun y0 : real => forall y1 : real, ((x0 = (NUMERAL 0)) \/ (~ ((real_pow y0 x0) = (real_pow y1 x0)))) \/ ((real_abs y0) = (real_abs y1))) x1.
Definition term87 (x0 : nat) (x1 : real) := (fun y0 : real => forall y1 : real, (Coq.Arith.PeanoNat.Nat.Odd x0) -> ((real_pow y0 x0) = (real_pow y1 x0)) = (y0 = y1)) x1.
Definition term193 := NUMERAL (BIT0 (BIT1 0)).
Definition term3 (x0 : real) (x1 : nat) := fun y0 : nat => (real_pow x0 (Nat.mul x1 y0)) = (real_pow (real_pow x0 x1) y0).
Definition term170 (x0 : nat) := and (~ (x0 = (NUMERAL 0))).
Definition term97 (x0 : nat) (x1 : real) (x2 : real) := (~ (x0 = (NUMERAL 0))) -> (Coq.Arith.PeanoNat.Nat.Even x0) -> (~ (((real_pow x1 x0) = (real_pow x2 x0)) -> (real_abs x1) = (real_abs x2))) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((~ (y0 = (NUMERAL 0))) /\ ((real_pow y1 y0) = (real_pow y2 y0))) -> (real_abs y1) = (real_abs y2)) -> False.
Definition term167 (x0 : real) (x1 : real) (x2 : nat) := (~ (x2 = (NUMERAL 0))) /\ (~ (~ ((real_pow x0 x2) = (real_pow x1 x2)))).
Definition term129 (x0 : nat) (x1 : real) (x2 : real) := ((real_pow x1 x0) = (real_pow x2 x0)) /\ (~ ((real_abs x1) = (real_abs x2))).
Definition term11 := fun y0 : real => forall y1 : nat, forall y2 : nat, (real_pow y0 (Nat.mul y1 y2)) = (real_pow (real_pow y0 y1) y2).
Definition term10 := fun y0 : real => forall y1 : nat, forall y2 : nat, (real_pow (real_pow y0 y1) y2) = (real_pow y0 (Nat.mul y1 y2)).
Definition term63 (x0 : nat) (x1 : real) (x2 : real) := @COND Prop (Coq.Arith.PeanoNat.Nat.Even x0) ((real_abs x1) = (real_abs x2)) (x1 = x2).
Definition term106 (x0 : nat) (x1 : real) (x2 : real) := (~ (((real_pow x1 x0) = (real_pow x2 x0)) -> (real_abs x1) = (real_abs x2))) -> ~ (forall y0 : nat, forall y1 : real, forall y2 : real, ((~ (y0 = (NUMERAL 0))) /\ ((real_pow y1 y0) = (real_pow y2 y0))) -> (real_abs y1) = (real_abs y2)).
Definition term38 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((NUMERAL y0) = (NUMERAL y1)) = (y0 = y1)) x0.
Definition term120 := fun y0 : real => forall y1 : real, forall y2 : nat, (~ (y2 = (NUMERAL 0))) -> (Coq.Arith.PeanoNat.Nat.Even y2) -> (~ (((real_pow y1 y2) = (real_pow y0 y2)) -> (real_abs y1) = (real_abs y0))) -> ~ (forall y3 : nat, forall y4 : real, forall y5 : real, ((~ (y3 = (NUMERAL 0))) /\ ((real_pow y4 y3) = (real_pow y5 y3))) -> (real_abs y4) = (real_abs y5)).
Definition term119 := fun y0 : real => forall y1 : real, forall y2 : nat, (~ (y2 = (NUMERAL 0))) -> (Coq.Arith.PeanoNat.Nat.Even y2) -> (~ (((real_pow y1 y2) = (real_pow y0 y2)) -> (real_abs y1) = (real_abs y0))) -> (forall y3 : nat, forall y4 : real, forall y5 : real, ((~ (y3 = (NUMERAL 0))) /\ ((real_pow y4 y3) = (real_pow y5 y3))) -> (real_abs y4) = (real_abs y5)) -> False.
Definition term48 (x0 : real) (x1 : nat) := @eq real (real_pow x0 x1).
Definition term173 (x0 : real) (x1 : real) := (~ ((real_abs x0) = (real_abs x1))) -> (real_abs x0) = (real_abs x1).
Definition term189 (x0 : real) := (fun y0 : real => forall y1 : nat, forall y2 : nat, (real_pow y0 (Nat.mul y1 y2)) = (real_pow (real_pow y0 y1) y2)) x0.
Definition term149 (x0 : nat) (x1 : real) (x2 : real) := (fun y0 : real => ((x0 = (NUMERAL 0)) \/ (~ ((real_pow x1 x0) = (real_pow y0 x0)))) \/ ((real_abs x1) = (real_abs y0))) x2.
Definition term72 (x0 : nat) := imp (~ (Coq.Arith.PeanoNat.Nat.Even x0)).
Definition term107 (x0 : nat) (x1 : real) (x2 : real) := (Coq.Arith.PeanoNat.Nat.Even x0) -> (~ (((real_pow x1 x0) = (real_pow x2 x0)) -> (real_abs x1) = (real_abs x2))) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((~ (y0 = (NUMERAL 0))) /\ ((real_pow y1 y0) = (real_pow y2 y0))) -> (real_abs y1) = (real_abs y2)) -> False.
Definition term187 (x0 : real) (x1 : nat) := real_pow x0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1).
Definition term80 (x0 : nat) (x1 : real) (x2 : real) := and ((Coq.Arith.PeanoNat.Nat.Even x0) -> ((real_pow x1 x0) = (real_pow x2 x0)) = ((real_abs x1) = (real_abs x2))).
Definition term81 (x0 : nat) (x1 : real) (x2 : real) := ((Coq.Arith.PeanoNat.Nat.Even x0) -> ((real_pow x1 x0) = (real_pow x2 x0)) = ((real_abs x1) = (real_abs x2))) /\ ((~ (Coq.Arith.PeanoNat.Nat.Even x0)) -> ((real_pow x1 x0) = (real_pow x2 x0)) = (x1 = x2)).
Definition term28 := fun y0 : nat => (~ (Coq.Arith.PeanoNat.Nat.Even y0)) = (Coq.Arith.PeanoNat.Nat.Odd y0).
Definition term47 := real_of_num (NUMERAL (BIT1 0)).
Definition term111 (x0 : real) (x1 : real) := fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> (Coq.Arith.PeanoNat.Nat.Even y0) -> (~ (((real_pow x0 y0) = (real_pow x1 y0)) -> (real_abs x0) = (real_abs x1))) -> (forall y1 : nat, forall y2 : real, forall y3 : real, ((~ (y1 = (NUMERAL 0))) /\ ((real_pow y2 y1) = (real_pow y3 y1))) -> (real_abs y2) = (real_abs y3)) -> False.
Definition term41 := (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even (NUMERAL y0)) = (Coq.Arith.PeanoNat.Nat.Even y0)) /\ (((Coq.Arith.PeanoNat.Nat.Even 0) = True) /\ ((forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even (BIT0 y0)) = True) /\ (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even (BIT1 y0)) = False))).
Definition term197 (x0 : nat) := fun y0 : nat => x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0).
Definition term150 (x0 : nat) (x1 : real) (x2 : real) := (x0 = (NUMERAL 0)) \/ ((~ ((real_pow x1 x0) = (real_pow x2 x0))) \/ ((real_abs x1) = (real_abs x2))).
Definition term60 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> (x0 = (NUMERAL 0)) = False.
Definition term22 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1)) x1.
Definition term179 (x0 : real) (x1 : real) := imp ((real_abs x0) = (real_abs x1)).
Definition term96 (x0 : nat) (x1 : real) (x2 : real) := ~ (((real_pow x1 x0) = (real_pow x2 x0)) -> (real_abs x1) = (real_abs x2)).
Definition term1 (x0 : real) (x1 : nat) (x2 : nat) := real_pow x0 (Nat.mul x1 x2).
Definition term58 (x0 : nat) (x1 : real) (x2 : real) := @COND Prop (Coq.Arith.PeanoNat.Nat.Even x0) ((x0 = (NUMERAL 0)) \/ ((real_abs x1) = (real_abs x2))) (x1 = x2).
Definition term61 (x0 : real) (x1 : real) := False \/ ((real_abs x0) = (real_abs x1)).
Definition term4 (x0 : real) (x1 : nat) := forall y0 : nat, (real_pow (real_pow x0 x1) y0) = (real_pow x0 (Nat.mul x1 y0)).
Definition term52 (x0 : nat) := @COND Prop (Coq.Arith.PeanoNat.Nat.Even x0).
Definition term78 (x0 : nat) (x1 : real) (x2 : real) := (Coq.Arith.PeanoNat.Nat.Even x0) -> ((real_pow x1 x0) = (real_pow x2 x0)) = ((real_abs x1) = (real_abs x2)).
Definition term188 (x0 : real) (x1 : real) (x2 : nat) := @eq Prop ((fun y0 : nat => (real_pow x0 y0) = (real_pow x1 y0)) x2).
Definition term68 (x0 : real) (x1 : real) (x2 : nat) := fun y0 : Prop => ((real_pow x0 x2) = (real_pow x1 x2)) = y0.
Definition term88 (x0 : nat) (x1 : real) := forall y0 : real, (Coq.Arith.PeanoNat.Nat.Odd x0) -> ((real_pow x1 x0) = (real_pow y0 x0)) = (x1 = y0).
Definition term49 := @eq real (real_of_num (NUMERAL (BIT1 0))).
Definition term57 (x0 : nat) (x1 : real) (x2 : real) := @COND Prop (Coq.Arith.PeanoNat.Nat.Even x0) ((x0 = (NUMERAL 0)) \/ ((real_abs x1) = (real_abs x2))).
Definition term110 (x0 : nat) (x1 : real) (x2 : real) := (~ (x0 = (NUMERAL 0))) -> (Coq.Arith.PeanoNat.Nat.Even x0) -> (~ (((real_pow x1 x0) = (real_pow x2 x0)) -> (real_abs x1) = (real_abs x2))) -> ~ (forall y0 : nat, forall y1 : real, forall y2 : real, ((~ (y0 = (NUMERAL 0))) /\ ((real_pow y1 y0) = (real_pow y2 y0))) -> (real_abs y1) = (real_abs y2)).
Definition term24 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0)) x2.
Definition term157 (x0 : real) (x1 : real) (x2 : nat) := ((real_abs x0) = (real_abs x1)) \/ (~ ((real_pow x0 x2) = (real_pow x1 x2))).
Definition term64 (x0 : Prop -> Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := x0 (@COND Prop x1 x2 x3).
Definition term130 (x0 : nat) := ~ (~ (x0 = (NUMERAL 0))).
Definition term166 (x0 : real) (x1 : real) (x2 : nat) := ~ ((x2 = (NUMERAL 0)) \/ (~ ((real_pow x0 x2) = (real_pow x1 x2)))).
Definition term196 (x0 : real) (x1 : nat) := @eq real (real_pow (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) x1).
Definition term180 (x0 : real) (x1 : real) := imp ((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))).
Definition term40 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((NUMERAL x0) = (NUMERAL y0)) = (x0 = y0)) x1.
Definition term98 (x0 : nat) (x1 : real) (x2 : real) := ((~ (x0 = (NUMERAL 0))) -> (Coq.Arith.PeanoNat.Nat.Even x0) -> (~ (((real_pow x1 x0) = (real_pow x2 x0)) -> (real_abs x1) = (real_abs x2))) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((~ (y0 = (NUMERAL 0))) /\ ((real_pow y1 y0) = (real_pow y2 y0))) -> (real_abs y1) = (real_abs y2)) -> False) -> (~ (x0 = (NUMERAL 0))) -> (Coq.Arith.PeanoNat.Nat.Even x0) -> (~ (((real_pow x1 x0) = (real_pow x2 x0)) -> (real_abs x1) = (real_abs x2))) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((~ (y0 = (NUMERAL 0))) /\ ((real_pow y1 y0) = (real_pow y2 y0))) -> (real_abs y1) = (real_abs y2)) -> False.
Definition term73 (x0 : nat) (x1 : real) (x2 : real) := (~ (Coq.Arith.PeanoNat.Nat.Even x0)) -> (fun y0 : Prop => ((real_pow x1 x0) = (real_pow x2 x0)) = y0) (x1 = x2).
Definition term186 (x0 : real) (x1 : real) (x2 : nat) := (fun y0 : nat => (real_pow x0 y0) = (real_pow x1 y0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x2).
Definition term123 (x0 : nat) (x1 : real) (x2 : real) := ((~ (x0 = (NUMERAL 0))) /\ ((real_pow x1 x0) = (real_pow x2 x0))) -> (real_abs x1) = (real_abs x2).
Definition term176 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : nat, (~ (y2 = (NUMERAL 0))) -> (Coq.Arith.PeanoNat.Nat.Even y2) -> (~ (((real_pow y1 y2) = (real_pow y0 y2)) -> (real_abs y1) = (real_abs y0))) -> (forall y3 : nat, forall y4 : real, forall y5 : real, ((~ (y3 = (NUMERAL 0))) /\ ((real_pow y4 y3) = (real_pow y5 y3))) -> (real_abs y4) = (real_abs y5)) -> False) x0.
Definition term134 (x0 : real) (x1 : real) (x2 : nat) := (x2 = (NUMERAL 0)) \/ (~ ((real_pow x0 x2) = (real_pow x1 x2))).
Definition term137 (x0 : real) (x1 : real) (x2 : nat) := or ((x2 = (NUMERAL 0)) \/ (~ ((real_pow x0 x2) = (real_pow x1 x2)))).
Definition term174 (x0 : real) (x1 : real) := ((real_abs x0) = (real_abs x1)) -> False.
Definition term45 (x0 : nat) := Coq.Arith.PeanoNat.Nat.Even (NUMERAL x0).
Definition term32 (x0 : nat) := (fun y0 : Prop => y0 \/ (~ y0)) (x0 = (NUMERAL 0)).
Definition term6 (x0 : real) := fun y0 : nat => forall y1 : nat, (real_pow (real_pow x0 y0) y1) = (real_pow x0 (Nat.mul y0 y1)).
Definition term153 (x0 : Prop) := x0 -> ~ x0.
Definition term142 (x0 : nat) (x1 : real) := forall y0 : real, ((x0 = (NUMERAL 0)) \/ (~ ((real_pow x1 x0) = (real_pow y0 x0)))) \/ ((real_abs x1) = (real_abs y0)).
Definition term99 (x0 : nat) (x1 : real) (x2 : real) := (((~ (x0 = (NUMERAL 0))) -> (Coq.Arith.PeanoNat.Nat.Even x0) -> (~ (((real_pow x1 x0) = (real_pow x2 x0)) -> (real_abs x1) = (real_abs x2))) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((~ (y0 = (NUMERAL 0))) /\ ((real_pow y1 y0) = (real_pow y2 y0))) -> (real_abs y1) = (real_abs y2)) -> False) -> (~ (x0 = (NUMERAL 0))) -> (Coq.Arith.PeanoNat.Nat.Even x0) -> (~ (((real_pow x1 x0) = (real_pow x2 x0)) -> (real_abs x1) = (real_abs x2))) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((~ (y0 = (NUMERAL 0))) /\ ((real_pow y1 y0) = (real_pow y2 y0))) -> (real_abs y1) = (real_abs y2)) -> False) -> (~ (x0 = (NUMERAL 0))) -> (Coq.Arith.PeanoNat.Nat.Even x0) -> (~ (((real_pow x1 x0) = (real_pow x2 x0)) -> (real_abs x1) = (real_abs x2))) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((~ (y0 = (NUMERAL 0))) /\ ((real_pow y1 y0) = (real_pow y2 y0))) -> (real_abs y1) = (real_abs y2)) -> False.
Definition term169 (x0 : real) (x1 : real) (x2 : nat) := ~ (~ ((real_pow x0 x2) = (real_pow x1 x2))).
Definition term177 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (Coq.Arith.PeanoNat.Nat.Even y1) -> (~ (((real_pow y0 y1) = (real_pow x0 y1)) -> (real_abs y0) = (real_abs x0))) -> (forall y2 : nat, forall y3 : real, forall y4 : real, ((~ (y2 = (NUMERAL 0))) /\ ((real_pow y3 y2) = (real_pow y4 y2))) -> (real_abs y3) = (real_abs y4)) -> False) x1.
Definition term42 := ((Coq.Arith.PeanoNat.Nat.Even 0) = True) /\ ((forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even (BIT0 y0)) = True) /\ (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even (BIT1 y0)) = False)).
Definition term84 (x0 : nat) := (fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Odd y0) = (~ (Coq.Arith.PeanoNat.Nat.Even y0))) x0.
