Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term156 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) /\ (forall y2 : nat, ~ (x0 = (Nat.mul y2 (NUMERAL (BIT0 (BIT1 0))))))) y0.
Definition term92 := fun y0 : nat => (fun y1 : nat => (forall y2 : nat, ~ (y1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y2))) /\ (exists y2 : nat, y1 = (Nat.mul y2 (NUMERAL (BIT0 (BIT1 0)))))) y0.
Definition term87 := fun y0 : nat => (fun y1 : nat => (exists y2 : nat, y1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y2)) /\ (forall y2 : nat, ~ (y1 = (Nat.mul y2 (NUMERAL (BIT0 (BIT1 0))))))) y0.
Definition term40 (x0 : nat) (x1 : nat) := ~ (x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)).
Definition term6 (x0 : nat) := @eq Prop (Coq.Arith.PeanoNat.Nat.Even x0).
Definition term11 := fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even y0) = ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)).
Definition term64 (x0 : nat -> Prop) := ~ (all x0).
Definition term197 := (~ False) -> False.
Definition term18 := (~ (forall y0 : nat, (exists y1 : nat, y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) = (exists y1 : nat, y0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0))))))) -> (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> False.
Definition term63 (x0 : nat) := ~ ((exists y0 : nat, x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) = (exists y0 : nat, x0 = (Nat.mul y0 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term164 (x0 : nat) (x1 : nat) := or ((fun y0 : nat => (x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) /\ (forall y1 : nat, ~ (x0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0))))))) x1).
Definition term172 (x0 : nat) := @eq Prop ((fun y0 : Prop => y0 = (exists y1 : nat, ((x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) /\ (forall y2 : nat, ~ (x0 = (Nat.mul y2 (NUMERAL (BIT0 (BIT1 0))))))) \/ ((forall y2 : nat, ~ (x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y2))) /\ (x0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0)))))))) ((exists y0 : nat, (x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) /\ (forall y1 : nat, ~ (x0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0))))))) \/ (exists y0 : nat, (forall y1 : nat, ~ (x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) /\ (x0 = (Nat.mul y0 (NUMERAL (BIT0 (BIT1 0)))))))).
Definition term128 (x0 : nat) (x1 : nat) := (forall y0 : nat, ~ (x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0))) /\ (x0 = (Nat.mul x1 (NUMERAL (BIT0 (BIT1 0))))).
Definition term102 (x0 : nat) := fun y0 : nat => (fun y1 : nat => x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) y0.
Definition term174 := fun y0 : nat => exists y1 : nat, ((y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) /\ (forall y2 : nat, ~ (y0 = (Nat.mul y2 (NUMERAL (BIT0 (BIT1 0))))))) \/ ((forall y2 : nat, ~ (y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y2))) /\ (y0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term132 := fun y0 : nat => exists y1 : nat, (forall y2 : nat, ~ (y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y2))) /\ (y0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0))))).
Definition term52 (x0 : nat) := and (~ (exists y0 : nat, x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0))).
Definition term147 (x0 : nat) := or (exists y0 : nat, (x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) /\ (forall y1 : nat, ~ (x0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0))))))).
Definition term91 := or (exists y0 : nat, (exists y1 : nat, y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) /\ (forall y1 : nat, ~ (y0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0))))))).
Definition term80 (x0 : nat) := (fun y0 : nat => (exists y1 : nat, y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) /\ (forall y1 : nat, ~ (y0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0))))))) x0.
Definition term191 (x0 : nat) (x1 : nat) := @eq Prop (~ (x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1))).
Definition term196 (x0 : nat) := ((Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) = (Nat.mul x0 (NUMERAL (BIT0 (BIT1 0))))) -> False.
Definition term195 (x0 : nat) (x1 : nat) := ((Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) = (Nat.mul x1 (NUMERAL (BIT0 (BIT1 0))))) -> False.
Definition term149 (x0 : nat) := (exists y0 : nat, (x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) /\ (forall y1 : nat, ~ (x0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0))))))) \/ (exists y0 : nat, (forall y1 : nat, ~ (x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) /\ (x0 = (Nat.mul y0 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term95 := (exists y0 : nat, (exists y1 : nat, y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) /\ (forall y1 : nat, ~ (y0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0))))))) \/ (exists y0 : nat, (forall y1 : nat, ~ (y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) /\ (exists y1 : nat, y0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term73 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term67 (x0 : nat) := (fun y0 : nat => (exists y1 : nat, y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) = (exists y1 : nat, y0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0)))))) x0.
Definition term131 (x0 : nat) := exists y0 : nat, (forall y1 : nat, ~ (x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) /\ (x0 = (Nat.mul y0 (NUMERAL (BIT0 (BIT1 0))))).
Definition term118 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 /\ (x1 y0).
Definition term15 (x0 : Prop) := (~ x0) -> False.
Definition term9 (x0 : nat) := exists y0 : nat, x0 = (Nat.mul y0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term180 (x0 : nat) := fun y0 : nat => ~ (y0 = (Nat.mul x0 (NUMERAL (BIT0 (BIT1 0))))).
Definition term8 (x0 : nat) := Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0))).
Definition term70 := fun y0 : nat => ((exists y1 : nat, y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) /\ (forall y1 : nat, ~ (y0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0))))))) \/ ((forall y1 : nat, ~ (y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) /\ (exists y1 : nat, y0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term100 (x0 : nat) := (exists y0 : nat, (fun y1 : nat => x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) y0) /\ (forall y0 : nat, ~ (x0 = (Nat.mul y0 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term171 (x0 : nat) := (fun y0 : Prop => y0 = (exists y1 : nat, ((x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) /\ (forall y2 : nat, ~ (x0 = (Nat.mul y2 (NUMERAL (BIT0 (BIT1 0))))))) \/ ((forall y2 : nat, ~ (x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y2))) /\ (x0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0)))))))) ((exists y0 : nat, (x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) /\ (forall y1 : nat, ~ (x0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0))))))) \/ (exists y0 : nat, (forall y1 : nat, ~ (x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) /\ (x0 = (Nat.mul y0 (NUMERAL (BIT0 (BIT1 0))))))).
Definition term14 := forall y0 : nat, (exists y1 : nat, y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) = (exists y1 : nat, y0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0))))).
Definition term170 (x0 : nat) := exists y0 : nat, ((x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) /\ (forall y1 : nat, ~ (x0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0))))))) \/ ((forall y1 : nat, ~ (x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) /\ (x0 = (Nat.mul y0 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term101 (x0 : nat) := exists y0 : nat, ((fun y1 : nat => x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) y0) /\ (forall y1 : nat, ~ (x0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term17 := ~ (forall y0 : nat, (exists y1 : nat, y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) = (exists y1 : nat, y0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term23 := ~ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)).
Definition term117 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 /\ (exists y0 : a0, x1 y0).
Definition term53 (x0 : nat) := and (forall y0 : nat, ~ (x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0))).
Definition term57 (x0 : nat) := (exists y0 : nat, x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) /\ (~ (exists y0 : nat, x0 = (Nat.mul y0 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term194 (x0 : Prop) := (~ x0) -> x0.
Definition term4 (x0 : nat) := (fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even y0) = (exists y1 : nat, y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) x0.
Definition term169 (x0 : nat) := fun y0 : nat => ((x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) /\ (forall y1 : nat, ~ (x0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0))))))) \/ ((forall y1 : nat, ~ (x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) /\ (x0 = (Nat.mul y0 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term71 := exists y0 : nat, ((exists y1 : nat, y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) /\ (forall y1 : nat, ~ (y0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0))))))) \/ ((forall y1 : nat, ~ (y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) /\ (exists y1 : nat, y0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term148 (x0 : nat) := ((fun y0 : nat => exists y1 : nat, (y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) /\ (forall y2 : nat, ~ (y0 = (Nat.mul y2 (NUMERAL (BIT0 (BIT1 0))))))) x0) \/ ((fun y0 : nat => exists y1 : nat, (forall y2 : nat, ~ (y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y2))) /\ (y0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0)))))) x0).
Definition term178 (x0 : nat) (x1 : nat) := (fun y0 : nat => ~ (x0 = (Nat.mul y0 (NUMERAL (BIT0 (BIT1 0)))))) x1.
Definition term185 (x0 : nat) (x1 : nat) := @eq Prop (~ (x0 = (Nat.mul x1 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term141 (x0 : nat) := (fun y0 : nat => exists y1 : nat, (forall y2 : nat, ~ (y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y2))) /\ (y0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0)))))) x0.
Definition term137 (x0 : nat) := (fun y0 : nat => exists y1 : nat, (y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) /\ (forall y2 : nat, ~ (y0 = (Nat.mul y2 (NUMERAL (BIT0 (BIT1 0))))))) x0.
Definition term104 (x0 : nat) := and (exists y0 : nat, (fun y1 : nat => x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) y0).
Definition term27 (x0 : nat) := fun y0 : nat => (Nat.mul x0 y0) = (Nat.mul y0 x0).
Definition term182 (x0 : nat) (x1 : nat) := (fun y0 : nat => ~ (y0 = (Nat.mul x0 (NUMERAL (BIT0 (BIT1 0)))))) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1).
Definition term199 (x0 : nat) := ~ ((Nat.mul x0 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)).
Definition term200 (x0 : nat) (x1 : nat) := ((Nat.mul x0 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) -> False.
Definition term94 := exists y0 : nat, (forall y1 : nat, ~ (y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) /\ (exists y1 : nat, y0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0))))).
Definition term121 (x0 : nat) := (forall y0 : nat, ~ (x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0))) /\ (exists y0 : nat, (fun y1 : nat => x0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0))))) y0).
Definition term142 := fun y0 : nat => (fun y1 : nat => exists y2 : nat, (forall y3 : nat, ~ (y1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y3))) /\ (y1 = (Nat.mul y2 (NUMERAL (BIT0 (BIT1 0)))))) y0.
Definition term138 := fun y0 : nat => (fun y1 : nat => exists y2 : nat, (y1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y2)) /\ (forall y3 : nat, ~ (y1 = (Nat.mul y3 (NUMERAL (BIT0 (BIT1 0))))))) y0.
Definition term31 (x0 : nat) := fun y0 : nat => x0 = (Nat.mul y0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term173 (x0 : nat) := @eq Prop (((exists y0 : nat, (x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) /\ (forall y1 : nat, ~ (x0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0))))))) \/ (exists y0 : nat, (forall y1 : nat, ~ (x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) /\ (x0 = (Nat.mul y0 (NUMERAL (BIT0 (BIT1 0))))))) = (exists y0 : nat, ((x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) /\ (forall y1 : nat, ~ (x0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0))))))) \/ ((forall y1 : nat, ~ (x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) /\ (x0 = (Nat.mul y0 (NUMERAL (BIT0 (BIT1 0)))))))).
Definition term83 (x0 : nat) := ((fun y0 : nat => (exists y1 : nat, y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) /\ (forall y1 : nat, ~ (y0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0))))))) x0) \/ ((fun y0 : nat => (forall y1 : nat, ~ (y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) /\ (exists y1 : nat, y0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0)))))) x0).
Definition term198 (x0 : nat) := (~ ((Nat.mul x0 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0))) -> (Nat.mul x0 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0).
Definition term29 := fun y0 : nat => forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0).
Definition term187 (x0 : nat) (x1 : nat) := (fun y0 : nat => ~ (y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0))) x1.
Definition term86 := @eq Prop (exists y0 : nat, ((exists y1 : nat, y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) /\ (forall y1 : nat, ~ (y0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0))))))) \/ ((forall y1 : nat, ~ (y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) /\ (exists y1 : nat, y0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0))))))).
Definition term85 := @eq Prop (exists y0 : nat, ((fun y1 : nat => (exists y2 : nat, y1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y2)) /\ (forall y2 : nat, ~ (y1 = (Nat.mul y2 (NUMERAL (BIT0 (BIT1 0))))))) y0) \/ ((fun y1 : nat => (forall y2 : nat, ~ (y1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y2))) /\ (exists y2 : nat, y1 = (Nat.mul y2 (NUMERAL (BIT0 (BIT1 0)))))) y0)).
Definition term7 (x0 : nat) := @eq Prop (exists y0 : nat, x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)).
Definition term193 (x0 : nat) := ~ ((Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) = (Nat.mul x0 (NUMERAL (BIT0 (BIT1 0))))).
Definition term68 (x0 : nat) := ~ ((fun y0 : nat => (exists y1 : nat, y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) = (exists y1 : nat, y0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0)))))) x0).
Definition term60 (x0 : nat) := or ((exists y0 : nat, x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) /\ (forall y0 : nat, ~ (x0 = (Nat.mul y0 (NUMERAL (BIT0 (BIT1 0))))))).
Definition term120 (x0 : Prop) (x1 : nat -> Prop) := exists y0 : nat, x0 /\ (x1 y0).
Definition term155 (x0 : nat) (x1 : nat) := (fun y0 : nat => (x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) /\ (forall y1 : nat, ~ (x0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0))))))) x1.
Definition term119 (x0 : Prop) (x1 : nat -> Prop) := x0 /\ (exists y0 : nat, x1 y0).
Definition term192 (x0 : nat) := (~ ((Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) = (Nat.mul x0 (NUMERAL (BIT0 (BIT1 0)))))) -> (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) = (Nat.mul x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term32 (x0 : nat) := Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0.
Definition term153 (x0 : nat) := (exists y0 : nat, (fun y1 : nat => (x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) /\ (forall y2 : nat, ~ (x0 = (Nat.mul y2 (NUMERAL (BIT0 (BIT1 0))))))) y0) \/ (exists y0 : nat, (fun y1 : nat => (forall y2 : nat, ~ (x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y2))) /\ (x0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0)))))) y0).
Definition term135 := (exists y0 : nat, (fun y1 : nat => exists y2 : nat, (y1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y2)) /\ (forall y3 : nat, ~ (y1 = (Nat.mul y3 (NUMERAL (BIT0 (BIT1 0))))))) y0) \/ (exists y0 : nat, (fun y1 : nat => exists y2 : nat, (forall y3 : nat, ~ (y1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y3))) /\ (y1 = (Nat.mul y2 (NUMERAL (BIT0 (BIT1 0)))))) y0).
Definition term77 := (exists y0 : nat, (fun y1 : nat => (exists y2 : nat, y1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y2)) /\ (forall y2 : nat, ~ (y1 = (Nat.mul y2 (NUMERAL (BIT0 (BIT1 0))))))) y0) \/ (exists y0 : nat, (fun y1 : nat => (forall y2 : nat, ~ (y1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y2))) /\ (exists y2 : nat, y1 = (Nat.mul y2 (NUMERAL (BIT0 (BIT1 0)))))) y0).
Definition term22 := (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> False.
Definition term109 (x0 : nat) (x1 : nat) := ((fun y0 : nat => x1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) x0) /\ (forall y0 : nat, ~ (x1 = (Nat.mul y0 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term12 := fun y0 : nat => (exists y1 : nat, y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) = (exists y1 : nat, y0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0))))).
Definition term54 (x0 : nat) := (~ (exists y0 : nat, x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0))) /\ (exists y0 : nat, x0 = (Nat.mul y0 (NUMERAL (BIT0 (BIT1 0))))).
Definition term20 := (((~ (forall y0 : nat, (exists y1 : nat, y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) = (exists y1 : nat, y0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0))))))) -> (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> False) -> (~ (forall y0 : nat, (exists y1 : nat, y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) = (exists y1 : nat, y0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0))))))) -> (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> False) -> (~ (forall y0 : nat, (exists y1 : nat, y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) = (exists y1 : nat, y0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0))))))) -> (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> False.
Definition term50 (x0 : nat) := fun y0 : nat => ~ (x0 = (Nat.mul y0 (NUMERAL (BIT0 (BIT1 0))))).
Definition term179 (x0 : nat) (x1 : nat) := (fun y0 : nat => ~ (x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0))) x1.
Definition term167 (x0 : nat) (x1 : nat) := ((x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) /\ (forall y0 : nat, ~ (x0 = (Nat.mul y0 (NUMERAL (BIT0 (BIT1 0))))))) \/ ((forall y0 : nat, ~ (x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0))) /\ (x0 = (Nat.mul x1 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term24 := forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0).
Definition term97 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) /\ x1.
Definition term159 (x0 : nat) (x1 : nat) := (fun y0 : nat => (forall y1 : nat, ~ (x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) /\ (x0 = (Nat.mul y0 (NUMERAL (BIT0 (BIT1 0)))))) x1.
Definition term82 (x0 : nat) := (fun y0 : nat => (forall y1 : nat, ~ (y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) /\ (exists y1 : nat, y0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0)))))) x0.
Definition term34 (x0 : nat -> Prop) := ~ (ex x0).
Definition term152 := exists y0 : nat, (exists y1 : nat, (y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) /\ (forall y2 : nat, ~ (y0 = (Nat.mul y2 (NUMERAL (BIT0 (BIT1 0))))))) \/ (exists y1 : nat, (forall y2 : nat, ~ (y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y2))) /\ (y0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term154 (x0 : nat) := exists y0 : nat, ((fun y1 : nat => (x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) /\ (forall y2 : nat, ~ (x0 = (Nat.mul y2 (NUMERAL (BIT0 (BIT1 0))))))) y0) \/ ((fun y1 : nat => (forall y2 : nat, ~ (x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y2))) /\ (x0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0)))))) y0).
Definition term136 := exists y0 : nat, ((fun y1 : nat => exists y2 : nat, (y1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y2)) /\ (forall y3 : nat, ~ (y1 = (Nat.mul y3 (NUMERAL (BIT0 (BIT1 0))))))) y0) \/ ((fun y1 : nat => exists y2 : nat, (forall y3 : nat, ~ (y1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y3))) /\ (y1 = (Nat.mul y2 (NUMERAL (BIT0 (BIT1 0)))))) y0).
Definition term76 := exists y0 : nat, ((fun y1 : nat => (exists y2 : nat, y1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y2)) /\ (forall y2 : nat, ~ (y1 = (Nat.mul y2 (NUMERAL (BIT0 (BIT1 0))))))) y0) \/ ((fun y1 : nat => (forall y2 : nat, ~ (y1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y2))) /\ (exists y2 : nat, y1 = (Nat.mul y2 (NUMERAL (BIT0 (BIT1 0)))))) y0).
Definition term79 := fun y0 : nat => (forall y1 : nat, ~ (y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) /\ (exists y1 : nat, y0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0))))).
Definition term183 (x0 : nat) (x1 : nat) := ~ ((Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) = (Nat.mul x1 (NUMERAL (BIT0 (BIT1 0))))).
Definition term35 (x0 : nat -> Prop) := forall y0 : nat, ~ (x0 y0).
Definition term5 (x0 : nat) := exists y0 : nat, x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0).
Definition term42 (x0 : nat) := fun y0 : nat => ~ (x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)).
Definition term186 (x0 : nat) := fun y0 : nat => ~ (y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)).
Definition term78 := fun y0 : nat => (exists y1 : nat, y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) /\ (forall y1 : nat, ~ (y0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term89 := exists y0 : nat, (exists y1 : nat, y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) /\ (forall y1 : nat, ~ (y0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term116 := or (exists y0 : nat, exists y1 : nat, (y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) /\ (forall y2 : nat, ~ (y0 = (Nat.mul y2 (NUMERAL (BIT0 (BIT1 0))))))).
Definition term188 (x0 : nat) (x1 : nat) := (fun y0 : nat => ~ (y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0))) (Nat.mul x1 (NUMERAL (BIT0 (BIT1 0)))).
Definition term99 (x0 : nat -> Prop) (x1 : Prop) := exists y0 : nat, (x0 y0) /\ x1.
Definition term16 := (~ (forall y0 : nat, (exists y1 : nat, y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) = (exists y1 : nat, y0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0))))))) -> False.
Definition term81 (x0 : nat) := or ((fun y0 : nat => (exists y1 : nat, y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) /\ (forall y1 : nat, ~ (y0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0))))))) x0).
Definition term28 (x0 : nat) := forall y0 : nat, (Nat.mul x0 y0) = (Nat.mul y0 x0).
Definition term3 (x0 : nat) (x1 : nat) := exists y0 : nat, x0 = (Nat.mul y0 x1).
Definition term55 (x0 : nat) := (forall y0 : nat, ~ (x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0))) /\ (exists y0 : nat, x0 = (Nat.mul y0 (NUMERAL (BIT0 (BIT1 0))))).
Definition term38 (x0 : nat) (x1 : nat) := (fun y0 : nat => x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) x1.
Definition term181 (x0 : nat) (x1 : nat) := (fun y0 : nat => ~ (y0 = (Nat.mul x0 (NUMERAL (BIT0 (BIT1 0)))))) x1.
Definition term130 (x0 : nat) := fun y0 : nat => (forall y1 : nat, ~ (x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) /\ (x0 = (Nat.mul y0 (NUMERAL (BIT0 (BIT1 0))))).
Definition term161 (x0 : nat) := exists y0 : nat, (fun y1 : nat => (forall y2 : nat, ~ (x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y2))) /\ (x0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0)))))) y0.
Definition term157 (x0 : nat) := exists y0 : nat, (fun y1 : nat => (x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) /\ (forall y2 : nat, ~ (x0 = (Nat.mul y2 (NUMERAL (BIT0 (BIT1 0))))))) y0.
Definition term124 (x0 : nat) := exists y0 : nat, (fun y1 : nat => x0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0))))) y0.
Definition term103 (x0 : nat) := exists y0 : nat, (fun y1 : nat => x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) y0.
Definition term93 := exists y0 : nat, (fun y1 : nat => (forall y2 : nat, ~ (y1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y2))) /\ (exists y2 : nat, y1 = (Nat.mul y2 (NUMERAL (BIT0 (BIT1 0)))))) y0.
Definition term88 := exists y0 : nat, (fun y1 : nat => (exists y2 : nat, y1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y2)) /\ (forall y2 : nat, ~ (y1 = (Nat.mul y2 (NUMERAL (BIT0 (BIT1 0))))))) y0.
Definition term177 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.mul x0 y0) = (Nat.mul y0 x0)) x1.
Definition term10 := NUMERAL (BIT0 (BIT1 0)).
Definition term43 (x0 : nat) := forall y0 : nat, ~ (x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)).
Definition term151 := fun y0 : nat => (exists y1 : nat, (y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) /\ (forall y2 : nat, ~ (y0 = (Nat.mul y2 (NUMERAL (BIT0 (BIT1 0))))))) \/ (exists y1 : nat, (forall y2 : nat, ~ (y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y2))) /\ (y0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Nat.modulo x0 y0) = (NUMERAL 0)) = (exists y1 : nat, x0 = (Nat.mul y1 y0))) x1.
Definition term190 (x0 : nat) (x1 : nat) := @eq Prop ((fun y0 : nat => ~ (y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0))) x1).
Definition term184 (x0 : nat) (x1 : nat) := @eq Prop ((fun y0 : nat => ~ (y0 = (Nat.mul x0 (NUMERAL (BIT0 (BIT1 0)))))) x1).
Definition term150 := fun y0 : nat => ((fun y1 : nat => exists y2 : nat, (y1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y2)) /\ (forall y3 : nat, ~ (y1 = (Nat.mul y3 (NUMERAL (BIT0 (BIT1 0))))))) y0) \/ ((fun y1 : nat => exists y2 : nat, (forall y3 : nat, ~ (y1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y3))) /\ (y1 = (Nat.mul y2 (NUMERAL (BIT0 (BIT1 0)))))) y0).
Definition term62 (x0 : nat) := ((exists y0 : nat, x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) /\ (forall y0 : nat, ~ (x0 = (Nat.mul y0 (NUMERAL (BIT0 (BIT1 0))))))) \/ ((forall y0 : nat, ~ (x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0))) /\ (exists y0 : nat, x0 = (Nat.mul y0 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term98 (x0 : nat -> Prop) (x1 : Prop) := (exists y0 : nat, x0 y0) /\ x1.
Definition term146 (x0 : nat) := or ((fun y0 : nat => exists y1 : nat, (y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) /\ (forall y2 : nat, ~ (y0 = (Nat.mul y2 (NUMERAL (BIT0 (BIT1 0))))))) x0).
Definition term45 (x0 : nat) := forall y0 : nat, ~ ((fun y1 : nat => x0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0))))) y0).
Definition term37 (x0 : nat) := forall y0 : nat, ~ ((fun y1 : nat => x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) y0).
Definition term51 (x0 : nat) := forall y0 : nat, ~ (x0 = (Nat.mul y0 (NUMERAL (BIT0 (BIT1 0))))).
Definition term13 := forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even y0) = ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)).
Definition term111 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) y0) /\ (forall y1 : nat, ~ (x0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term176 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) x0.
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.modulo y0 y1) = (NUMERAL 0)) = (exists y2 : nat, y0 = (Nat.mul y2 y1))) x0.
Definition term114 := fun y0 : nat => exists y1 : nat, (y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) /\ (forall y2 : nat, ~ (y0 = (Nat.mul y2 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term56 (x0 : nat) := and (exists y0 : nat, x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)).
Definition term129 (x0 : nat) := fun y0 : nat => (forall y1 : nat, ~ (x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) /\ ((fun y1 : nat => x0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0))))) y0).
Definition term110 (x0 : nat) (x1 : nat) := (x1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) /\ (forall y0 : nat, ~ (x1 = (Nat.mul y0 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term66 := exists y0 : nat, ~ ((fun y1 : nat => (exists y2 : nat, y1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y2)) = (exists y2 : nat, y1 = (Nat.mul y2 (NUMERAL (BIT0 (BIT1 0)))))) y0).
Definition term33 (x0 : nat) := fun y0 : nat => x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0).
Definition term201 (x0 : nat) := ((Nat.mul x0 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) -> False.
Definition term134 := (exists y0 : nat, exists y1 : nat, (y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) /\ (forall y2 : nat, ~ (y0 = (Nat.mul y2 (NUMERAL (BIT0 (BIT1 0))))))) \/ (exists y0 : nat, exists y1 : nat, (forall y2 : nat, ~ (y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y2))) /\ (y0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term26 := (~ (forall y0 : nat, (exists y1 : nat, y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) = (exists y1 : nat, y0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0))))))) -> ~ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)).
Definition term160 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (forall y2 : nat, ~ (x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y2))) /\ (x0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0)))))) y0.
Definition term61 (x0 : nat) := ((exists y0 : nat, x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) /\ (~ (exists y0 : nat, x0 = (Nat.mul y0 (NUMERAL (BIT0 (BIT1 0))))))) \/ ((~ (exists y0 : nat, x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0))) /\ (exists y0 : nat, x0 = (Nat.mul y0 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term123 (x0 : nat) := fun y0 : nat => (fun y1 : nat => x0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0))))) y0.
Definition term165 (x0 : nat) (x1 : nat) := or ((x1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) /\ (forall y0 : nat, ~ (x1 = (Nat.mul y0 (NUMERAL (BIT0 (BIT1 0))))))).
Definition term1 (x0 : nat) := forall y0 : nat, ((Nat.modulo x0 y0) = (NUMERAL 0)) = (exists y1 : nat, x0 = (Nat.mul y1 y0)).
Definition term126 (x0 : nat) := @eq Prop ((forall y0 : nat, ~ (x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0))) /\ (exists y0 : nat, x0 = (Nat.mul y0 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term125 (x0 : nat) := @eq Prop ((forall y0 : nat, ~ (x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0))) /\ (exists y0 : nat, (fun y1 : nat => x0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0))))) y0)).
Definition term127 (x0 : nat) (x1 : nat) := (forall y0 : nat, ~ (x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0))) /\ ((fun y0 : nat => x0 = (Nat.mul y0 (NUMERAL (BIT0 (BIT1 0))))) x1).
Definition term143 := exists y0 : nat, (fun y1 : nat => exists y2 : nat, (forall y3 : nat, ~ (y1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y3))) /\ (y1 = (Nat.mul y2 (NUMERAL (BIT0 (BIT1 0)))))) y0.
Definition term139 := exists y0 : nat, (fun y1 : nat => exists y2 : nat, (y1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y2)) /\ (forall y3 : nat, ~ (y1 = (Nat.mul y3 (NUMERAL (BIT0 (BIT1 0))))))) y0.
Definition term175 := exists y0 : nat, exists y1 : nat, ((y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) /\ (forall y2 : nat, ~ (y0 = (Nat.mul y2 (NUMERAL (BIT0 (BIT1 0))))))) \/ ((forall y2 : nat, ~ (y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y2))) /\ (y0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term133 := exists y0 : nat, exists y1 : nat, (forall y2 : nat, ~ (y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y2))) /\ (y0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0))))).
Definition term115 := exists y0 : nat, exists y1 : nat, (y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) /\ (forall y2 : nat, ~ (y0 = (Nat.mul y2 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term113 (x0 : nat) := exists y0 : nat, (x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) /\ (forall y1 : nat, ~ (x0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term74 (x0 : nat -> Prop) (x1 : nat -> Prop) := exists y0 : nat, (x0 y0) \/ (x1 y0).
Definition term107 (x0 : nat) (x1 : nat) := and ((fun y0 : nat => x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) x1).
Definition term69 := fun y0 : nat => ~ ((fun y1 : nat => (exists y2 : nat, y1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y2)) = (exists y2 : nat, y1 = (Nat.mul y2 (NUMERAL (BIT0 (BIT1 0)))))) y0).
Definition term49 (x0 : nat) := fun y0 : nat => ~ ((fun y1 : nat => x0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0))))) y0).
Definition term41 (x0 : nat) := fun y0 : nat => ~ ((fun y1 : nat => x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) y0).
Definition term47 (x0 : nat) (x1 : nat) := ~ ((fun y0 : nat => x0 = (Nat.mul y0 (NUMERAL (BIT0 (BIT1 0))))) x1).
Definition term39 (x0 : nat) (x1 : nat) := ~ ((fun y0 : nat => x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) x1).
Definition term106 (x0 : nat) := @eq Prop ((exists y0 : nat, x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) /\ (forall y0 : nat, ~ (x0 = (Nat.mul y0 (NUMERAL (BIT0 (BIT1 0))))))).
Definition term105 (x0 : nat) := @eq Prop ((exists y0 : nat, (fun y1 : nat => x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) y0) /\ (forall y0 : nat, ~ (x0 = (Nat.mul y0 (NUMERAL (BIT0 (BIT1 0))))))).
Definition term48 (x0 : nat) (x1 : nat) := ~ (x0 = (Nat.mul x1 (NUMERAL (BIT0 (BIT1 0))))).
Definition term59 (x0 : nat) := or ((exists y0 : nat, x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) /\ (~ (exists y0 : nat, x0 = (Nat.mul y0 (NUMERAL (BIT0 (BIT1 0))))))).
Definition term96 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) /\ x1.
Definition term168 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => (x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) /\ (forall y2 : nat, ~ (x0 = (Nat.mul y2 (NUMERAL (BIT0 (BIT1 0))))))) y0) \/ ((fun y1 : nat => (forall y2 : nat, ~ (x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y2))) /\ (x0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0)))))) y0).
Definition term84 := fun y0 : nat => ((fun y1 : nat => (exists y2 : nat, y1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y2)) /\ (forall y2 : nat, ~ (y1 = (Nat.mul y2 (NUMERAL (BIT0 (BIT1 0))))))) y0) \/ ((fun y1 : nat => (forall y2 : nat, ~ (y1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y2))) /\ (exists y2 : nat, y1 = (Nat.mul y2 (NUMERAL (BIT0 (BIT1 0)))))) y0).
Definition term158 (x0 : nat) := or (exists y0 : nat, (fun y1 : nat => (x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) /\ (forall y2 : nat, ~ (x0 = (Nat.mul y2 (NUMERAL (BIT0 (BIT1 0))))))) y0).
Definition term140 := or (exists y0 : nat, (fun y1 : nat => exists y2 : nat, (y1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y2)) /\ (forall y3 : nat, ~ (y1 = (Nat.mul y3 (NUMERAL (BIT0 (BIT1 0))))))) y0).
Definition term90 := or (exists y0 : nat, (fun y1 : nat => (exists y2 : nat, y1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y2)) /\ (forall y2 : nat, ~ (y1 = (Nat.mul y2 (NUMERAL (BIT0 (BIT1 0))))))) y0).
Definition term19 := ((~ (forall y0 : nat, (exists y1 : nat, y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) = (exists y1 : nat, y0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0))))))) -> (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> False) -> (~ (forall y0 : nat, (exists y1 : nat, y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) = (exists y1 : nat, y0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0))))))) -> (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> False.
Definition term21 := (((~ (forall y0 : nat, (exists y1 : nat, y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) = (exists y1 : nat, y0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0))))))) -> (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> False) -> (~ (forall y0 : nat, (exists y1 : nat, y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) = (exists y1 : nat, y0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0))))))) -> (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> False) -> ((~ (forall y0 : nat, (exists y1 : nat, y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) = (exists y1 : nat, y0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0))))))) -> (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> False) -> (~ (forall y0 : nat, (exists y1 : nat, y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) = (exists y1 : nat, y0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0))))))) -> (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> False.
Definition term166 (x0 : nat) (x1 : nat) := ((fun y0 : nat => (x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) /\ (forall y1 : nat, ~ (x0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0))))))) x1) \/ ((fun y0 : nat => (forall y1 : nat, ~ (x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) /\ (x0 = (Nat.mul y0 (NUMERAL (BIT0 (BIT1 0)))))) x1).
Definition term58 (x0 : nat) := (exists y0 : nat, x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) /\ (forall y0 : nat, ~ (x0 = (Nat.mul y0 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term112 (x0 : nat) := fun y0 : nat => (x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) /\ (forall y1 : nat, ~ (x0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term189 (x0 : nat) (x1 : nat) := ~ ((Nat.mul x0 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)).
Definition term72 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term65 (x0 : nat -> Prop) := exists y0 : nat, ~ (x0 y0).
Definition term30 (x0 : nat) := Nat.mul x0 (NUMERAL (BIT0 (BIT1 0))).
Definition term44 (x0 : nat) := ~ (exists y0 : nat, x0 = (Nat.mul y0 (NUMERAL (BIT0 (BIT1 0))))).
Definition term36 (x0 : nat) := ~ (exists y0 : nat, x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)).
Definition term108 (x0 : nat) (x1 : nat) := and (x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)).
Definition term46 (x0 : nat) (x1 : nat) := (fun y0 : nat => x0 = (Nat.mul y0 (NUMERAL (BIT0 (BIT1 0))))) x1.
Definition term75 (x0 : nat -> Prop) (x1 : nat -> Prop) := (exists y0 : nat, x0 y0) \/ (exists y0 : nat, x1 y0).
Definition term25 := imp (~ (forall y0 : nat, (exists y1 : nat, y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) = (exists y1 : nat, y0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0))))))).
Definition term122 (x0 : nat) := exists y0 : nat, (forall y1 : nat, ~ (x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) /\ ((fun y1 : nat => x0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0))))) y0).
Definition term163 (x0 : nat) := @eq Prop ((exists y0 : nat, (x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) /\ (forall y1 : nat, ~ (x0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0))))))) \/ (exists y0 : nat, (forall y1 : nat, ~ (x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) /\ (x0 = (Nat.mul y0 (NUMERAL (BIT0 (BIT1 0))))))).
Definition term162 (x0 : nat) := @eq Prop ((exists y0 : nat, (fun y1 : nat => (x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) /\ (forall y2 : nat, ~ (x0 = (Nat.mul y2 (NUMERAL (BIT0 (BIT1 0))))))) y0) \/ (exists y0 : nat, (fun y1 : nat => (forall y2 : nat, ~ (x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y2))) /\ (x0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0)))))) y0)).
Definition term145 := @eq Prop ((exists y0 : nat, exists y1 : nat, (y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) /\ (forall y2 : nat, ~ (y0 = (Nat.mul y2 (NUMERAL (BIT0 (BIT1 0))))))) \/ (exists y0 : nat, exists y1 : nat, (forall y2 : nat, ~ (y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y2))) /\ (y0 = (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0))))))).
Definition term144 := @eq Prop ((exists y0 : nat, (fun y1 : nat => exists y2 : nat, (y1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y2)) /\ (forall y3 : nat, ~ (y1 = (Nat.mul y3 (NUMERAL (BIT0 (BIT1 0))))))) y0) \/ (exists y0 : nat, (fun y1 : nat => exists y2 : nat, (forall y3 : nat, ~ (y1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y3))) /\ (y1 = (Nat.mul y2 (NUMERAL (BIT0 (BIT1 0)))))) y0)).
