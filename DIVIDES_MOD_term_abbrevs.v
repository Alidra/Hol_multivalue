Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term204 (x0 : nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => (x0 = (Nat.mul x1 y1)) /\ (forall y2 : nat, ~ (x0 = (Nat.mul y2 x1)))) y0.
Definition term96 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (forall y2 : nat, ~ (y1 = (Nat.mul x0 y2))) /\ (exists y2 : nat, y1 = (Nat.mul y2 x0))) y0.
Definition term91 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (exists y2 : nat, y1 = (Nat.mul x0 y2)) /\ (forall y2 : nat, ~ (y1 = (Nat.mul y2 x0)))) y0.
Definition term238 (x0 : nat) (x1 : nat) := (~ ((Nat.mul x1 x0) = (Nat.mul x0 x1))) -> (Nat.mul x1 x0) = (Nat.mul x0 x1).
Definition term61 (x0 : nat -> Prop) := ~ (all x0).
Definition term243 := (~ False) -> False.
Definition term18 := (~ (forall y0 : nat, forall y1 : nat, (exists y2 : nat, y1 = (Nat.mul y0 y2)) = (exists y2 : nat, y1 = (Nat.mul y2 y0)))) -> (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> False.
Definition term133 (x0 : nat) (x1 : nat) (x2 : nat) := and ((fun y0 : nat => x0 = (Nat.mul x1 y0)) x2).
Definition term60 (x0 : nat) (x1 : nat) := ~ ((exists y0 : nat, x0 = (Nat.mul x1 y0)) = (exists y0 : nat, x0 = (Nat.mul y0 x1))).
Definition term85 (x0 : nat) (x1 : nat) := or ((fun y0 : nat => (exists y1 : nat, y0 = (Nat.mul x0 y1)) /\ (forall y1 : nat, ~ (y0 = (Nat.mul y1 x0)))) x1).
Definition term220 (x0 : nat) (x1 : nat) := @eq Prop ((fun y0 : Prop => y0 = (exists y1 : nat, ((x0 = (Nat.mul x1 y1)) /\ (forall y2 : nat, ~ (x0 = (Nat.mul y2 x1)))) \/ ((forall y2 : nat, ~ (x0 = (Nat.mul x1 y2))) /\ (x0 = (Nat.mul y1 x1))))) ((exists y0 : nat, (x0 = (Nat.mul x1 y0)) /\ (forall y1 : nat, ~ (x0 = (Nat.mul y1 x1)))) \/ (exists y0 : nat, (forall y1 : nat, ~ (x0 = (Nat.mul x1 y1))) /\ (x0 = (Nat.mul y0 x1))))).
Definition term86 (x0 : nat) (x1 : nat) := (fun y0 : nat => (forall y1 : nat, ~ (y0 = (Nat.mul x0 y1))) /\ (exists y1 : nat, y0 = (Nat.mul y1 x0))) x1.
Definition term214 (x0 : nat) (x1 : nat) (x2 : nat) := ((fun y0 : nat => (x0 = (Nat.mul x1 y0)) /\ (forall y1 : nat, ~ (x0 = (Nat.mul y1 x1)))) x2) \/ ((fun y0 : nat => (forall y1 : nat, ~ (x0 = (Nat.mul x1 y1))) /\ (x0 = (Nat.mul y0 x1))) x2).
Definition term151 (x0 : nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => x0 = (Nat.mul y1 x1)) y0.
Definition term128 (x0 : nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => x0 = (Nat.mul x1 y1)) y0.
Definition term158 (x0 : nat) (x1 : nat) := fun y0 : nat => (forall y1 : nat, ~ (x0 = (Nat.mul x1 y1))) /\ (x0 = (Nat.mul y0 x1)).
Definition term222 (x0 : nat) := fun y0 : nat => exists y1 : nat, ((y0 = (Nat.mul x0 y1)) /\ (forall y2 : nat, ~ (y0 = (Nat.mul y2 x0)))) \/ ((forall y2 : nat, ~ (y0 = (Nat.mul x0 y2))) /\ (y0 = (Nat.mul y1 x0))).
Definition term160 (x0 : nat) := fun y0 : nat => exists y1 : nat, (forall y2 : nat, ~ (y0 = (Nat.mul x0 y2))) /\ (y0 = (Nat.mul y1 x0)).
Definition term74 := fun y0 : nat => exists y1 : nat, ((exists y2 : nat, y1 = (Nat.mul y0 y2)) /\ (forall y2 : nat, ~ (y1 = (Nat.mul y2 y0)))) \/ ((forall y2 : nat, ~ (y1 = (Nat.mul y0 y2))) /\ (exists y2 : nat, y1 = (Nat.mul y2 y0))).
Definition term49 (x0 : nat) (x1 : nat) := and (~ (exists y0 : nat, x0 = (Nat.mul x1 y0))).
Definition term195 (x0 : nat) (x1 : nat) := or (exists y0 : nat, (x0 = (Nat.mul x1 y0)) /\ (forall y1 : nat, ~ (x0 = (Nat.mul y1 x1)))).
Definition term95 (x0 : nat) := or (exists y0 : nat, (exists y1 : nat, y0 = (Nat.mul x0 y1)) /\ (forall y1 : nat, ~ (y0 = (Nat.mul y1 x0)))).
Definition term197 (x0 : nat) (x1 : nat) := (exists y0 : nat, (x0 = (Nat.mul x1 y0)) /\ (forall y1 : nat, ~ (x0 = (Nat.mul y1 x1)))) \/ (exists y0 : nat, (forall y1 : nat, ~ (x0 = (Nat.mul x1 y1))) /\ (x0 = (Nat.mul y0 x1))).
Definition term99 (x0 : nat) := (exists y0 : nat, (exists y1 : nat, y0 = (Nat.mul x0 y1)) /\ (forall y1 : nat, ~ (y0 = (Nat.mul y1 x0)))) \/ (exists y0 : nat, (forall y1 : nat, ~ (y0 = (Nat.mul x0 y1))) /\ (exists y1 : nat, y0 = (Nat.mul y1 x0))).
Definition term77 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term146 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 /\ (x1 y0).
Definition term15 (x0 : Prop) := (~ x0) -> False.
Definition term233 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((Nat.mul x2 x0) = (Nat.mul x1 x2)).
Definition term68 (x0 : nat) := fun y0 : nat => ((exists y1 : nat, y0 = (Nat.mul x0 y1)) /\ (forall y1 : nat, ~ (y0 = (Nat.mul y1 x0)))) \/ ((forall y1 : nat, ~ (y0 = (Nat.mul x0 y1))) /\ (exists y1 : nat, y0 = (Nat.mul y1 x0))).
Definition term126 (x0 : nat) (x1 : nat) := (exists y0 : nat, (fun y1 : nat => x0 = (Nat.mul x1 y1)) y0) /\ (forall y0 : nat, ~ (x0 = (Nat.mul y0 x1))).
Definition term5 (x0 : nat) (x1 : nat) := @eq Prop (num_divides x0 x1).
Definition term219 (x0 : nat) (x1 : nat) := (fun y0 : Prop => y0 = (exists y1 : nat, ((x0 = (Nat.mul x1 y1)) /\ (forall y2 : nat, ~ (x0 = (Nat.mul y2 x1)))) \/ ((forall y2 : nat, ~ (x0 = (Nat.mul x1 y2))) /\ (x0 = (Nat.mul y1 x1))))) ((exists y0 : nat, (x0 = (Nat.mul x1 y0)) /\ (forall y1 : nat, ~ (x0 = (Nat.mul y1 x1)))) \/ (exists y0 : nat, (forall y1 : nat, ~ (x0 = (Nat.mul x1 y1))) /\ (x0 = (Nat.mul y0 x1)))).
Definition term134 (x0 : nat) (x1 : nat) (x2 : nat) := and (x0 = (Nat.mul x1 x2)).
Definition term244 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.mul x0 x1) = (Nat.mul x1 x2)) -> False.
Definition term241 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.mul x2 x0) = (Nat.mul x1 x2)) -> False.
Definition term10 (x0 : nat) := forall y0 : nat, (exists y1 : nat, y0 = (Nat.mul x0 y1)) = (exists y1 : nat, y0 = (Nat.mul y1 x0)).
Definition term207 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (forall y1 : nat, ~ (x0 = (Nat.mul x1 y1))) /\ (x0 = (Nat.mul y0 x1))) x2.
Definition term218 (x0 : nat) (x1 : nat) := exists y0 : nat, ((x0 = (Nat.mul x1 y0)) /\ (forall y1 : nat, ~ (x0 = (Nat.mul y1 x1)))) \/ ((forall y1 : nat, ~ (x0 = (Nat.mul x1 y1))) /\ (x0 = (Nat.mul y0 x1))).
Definition term47 (x0 : nat) (x1 : nat) := fun y0 : nat => ~ (x0 = (Nat.mul y0 x1)).
Definition term127 (x0 : nat) (x1 : nat) := exists y0 : nat, ((fun y1 : nat => x0 = (Nat.mul x1 y1)) y0) /\ (forall y1 : nat, ~ (x0 = (Nat.mul y1 x1))).
Definition term44 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => x0 = (Nat.mul y0 x1)) x2.
Definition term63 (x0 : nat) := ~ (forall y0 : nat, (exists y1 : nat, y0 = (Nat.mul x0 y1)) = (exists y1 : nat, y0 = (Nat.mul y1 x0))).
Definition term23 := ~ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)).
Definition term17 := ~ (forall y0 : nat, forall y1 : nat, (exists y2 : nat, y1 = (Nat.mul y0 y2)) = (exists y2 : nat, y1 = (Nat.mul y2 y0))).
Definition term145 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 /\ (exists y0 : a0, x1 y0).
Definition term50 (x0 : nat) (x1 : nat) := and (forall y0 : nat, ~ (x0 = (Nat.mul x1 y0))).
Definition term54 (x0 : nat) (x1 : nat) := (exists y0 : nat, x0 = (Nat.mul x1 y0)) /\ (~ (exists y0 : nat, x0 = (Nat.mul y0 x1))).
Definition term240 (x0 : Prop) := (~ x0) -> x0.
Definition term69 (x0 : nat) := exists y0 : nat, ((exists y1 : nat, y0 = (Nat.mul x0 y1)) /\ (forall y1 : nat, ~ (y0 = (Nat.mul y1 x0)))) \/ ((forall y1 : nat, ~ (y0 = (Nat.mul x0 y1))) /\ (exists y1 : nat, y0 = (Nat.mul y1 x0))).
Definition term178 (x0 : nat) := ((fun y0 : nat => exists y1 : nat, exists y2 : nat, (y1 = (Nat.mul y0 y2)) /\ (forall y3 : nat, ~ (y1 = (Nat.mul y3 y0)))) x0) \/ ((fun y0 : nat => exists y1 : nat, exists y2 : nat, (forall y3 : nat, ~ (y1 = (Nat.mul y0 y3))) /\ (y1 = (Nat.mul y2 y0))) x0).
Definition term109 (x0 : nat) := ((fun y0 : nat => exists y1 : nat, (exists y2 : nat, y1 = (Nat.mul y0 y2)) /\ (forall y2 : nat, ~ (y1 = (Nat.mul y2 y0)))) x0) \/ ((fun y0 : nat => exists y1 : nat, (forall y2 : nat, ~ (y1 = (Nat.mul y0 y2))) /\ (exists y2 : nat, y1 = (Nat.mul y2 y0))) x0).
Definition term229 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ~ (x0 = (Nat.mul x1 y0))) x2.
Definition term228 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ~ (x0 = (Nat.mul y0 x1))) x2.
Definition term108 (x0 : nat) := (fun y0 : nat => exists y1 : nat, (forall y2 : nat, ~ (y1 = (Nat.mul y0 y2))) /\ (exists y2 : nat, y1 = (Nat.mul y2 y0))) x0.
Definition term106 (x0 : nat) := (fun y0 : nat => exists y1 : nat, (exists y2 : nat, y1 = (Nat.mul y0 y2)) /\ (forall y2 : nat, ~ (y1 = (Nat.mul y2 y0)))) x0.
Definition term7 (x0 : nat) := fun y0 : nat => (num_divides x0 y0) = ((Nat.modulo y0 x0) = (NUMERAL 0)).
Definition term130 (x0 : nat) (x1 : nat) := and (exists y0 : nat, (fun y1 : nat => x0 = (Nat.mul x1 y1)) y0).
Definition term27 (x0 : nat) := fun y0 : nat => (Nat.mul x0 y0) = (Nat.mul y0 x0).
Definition term98 (x0 : nat) := exists y0 : nat, (forall y1 : nat, ~ (y0 = (Nat.mul x0 y1))) /\ (exists y1 : nat, y0 = (Nat.mul y1 x0)).
Definition term149 (x0 : nat) (x1 : nat) := (forall y0 : nat, ~ (x0 = (Nat.mul x1 y0))) /\ (exists y0 : nat, (fun y1 : nat => x0 = (Nat.mul y1 x1)) y0).
Definition term190 (x0 : nat) := fun y0 : nat => (fun y1 : nat => exists y2 : nat, (forall y3 : nat, ~ (y1 = (Nat.mul x0 y3))) /\ (y1 = (Nat.mul y2 x0))) y0.
Definition term186 (x0 : nat) := fun y0 : nat => (fun y1 : nat => exists y2 : nat, (y1 = (Nat.mul x0 y2)) /\ (forall y3 : nat, ~ (y1 = (Nat.mul y3 x0)))) y0.
Definition term172 := fun y0 : nat => (fun y1 : nat => exists y2 : nat, exists y3 : nat, (forall y4 : nat, ~ (y2 = (Nat.mul y1 y4))) /\ (y2 = (Nat.mul y3 y1))) y0.
Definition term168 := fun y0 : nat => (fun y1 : nat => exists y2 : nat, exists y3 : nat, (y2 = (Nat.mul y1 y3)) /\ (forall y4 : nat, ~ (y2 = (Nat.mul y4 y1)))) y0.
Definition term118 := fun y0 : nat => (fun y1 : nat => exists y2 : nat, (forall y3 : nat, ~ (y2 = (Nat.mul y1 y3))) /\ (exists y3 : nat, y2 = (Nat.mul y3 y1))) y0.
Definition term113 := fun y0 : nat => (fun y1 : nat => exists y2 : nat, (exists y3 : nat, y2 = (Nat.mul y1 y3)) /\ (forall y3 : nat, ~ (y2 = (Nat.mul y3 y1)))) y0.
Definition term221 (x0 : nat) (x1 : nat) := @eq Prop (((exists y0 : nat, (x0 = (Nat.mul x1 y0)) /\ (forall y1 : nat, ~ (x0 = (Nat.mul y1 x1)))) \/ (exists y0 : nat, (forall y1 : nat, ~ (x0 = (Nat.mul x1 y1))) /\ (x0 = (Nat.mul y0 x1)))) = (exists y0 : nat, ((x0 = (Nat.mul x1 y0)) /\ (forall y1 : nat, ~ (x0 = (Nat.mul y1 x1)))) \/ ((forall y1 : nat, ~ (x0 = (Nat.mul x1 y1))) /\ (x0 = (Nat.mul y0 x1))))).
Definition term36 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => x0 = (Nat.mul x1 y0)) x2.
Definition term29 := fun y0 : nat => forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0).
Definition term30 (x0 : nat) (x1 : nat) := fun y0 : nat => x0 = (Nat.mul y0 x1).
Definition term112 := @eq Prop (exists y0 : nat, (exists y1 : nat, (exists y2 : nat, y1 = (Nat.mul y0 y2)) /\ (forall y2 : nat, ~ (y1 = (Nat.mul y2 y0)))) \/ (exists y1 : nat, (forall y2 : nat, ~ (y1 = (Nat.mul y0 y2))) /\ (exists y2 : nat, y1 = (Nat.mul y2 y0)))).
Definition term111 := @eq Prop (exists y0 : nat, ((fun y1 : nat => exists y2 : nat, (exists y3 : nat, y2 = (Nat.mul y1 y3)) /\ (forall y3 : nat, ~ (y2 = (Nat.mul y3 y1)))) y0) \/ ((fun y1 : nat => exists y2 : nat, (forall y3 : nat, ~ (y2 = (Nat.mul y1 y3))) /\ (exists y3 : nat, y2 = (Nat.mul y3 y1))) y0)).
Definition term90 (x0 : nat) := @eq Prop (exists y0 : nat, ((exists y1 : nat, y0 = (Nat.mul x0 y1)) /\ (forall y1 : nat, ~ (y0 = (Nat.mul y1 x0)))) \/ ((forall y1 : nat, ~ (y0 = (Nat.mul x0 y1))) /\ (exists y1 : nat, y0 = (Nat.mul y1 x0)))).
Definition term89 (x0 : nat) := @eq Prop (exists y0 : nat, ((fun y1 : nat => (exists y2 : nat, y1 = (Nat.mul x0 y2)) /\ (forall y2 : nat, ~ (y1 = (Nat.mul y2 x0)))) y0) \/ ((fun y1 : nat => (forall y2 : nat, ~ (y1 = (Nat.mul x0 y2))) /\ (exists y2 : nat, y1 = (Nat.mul y2 x0))) y0)).
Definition term6 (x0 : nat) (x1 : nat) := @eq Prop (exists y0 : nat, x0 = (Nat.mul x1 y0)).
Definition term57 (x0 : nat) (x1 : nat) := or ((exists y0 : nat, x0 = (Nat.mul x1 y0)) /\ (forall y0 : nat, ~ (x0 = (Nat.mul y0 x1)))).
Definition term148 (x0 : Prop) (x1 : nat -> Prop) := exists y0 : nat, x0 /\ (x1 y0).
Definition term239 (x0 : nat) (x1 : nat) := ~ ((Nat.mul x1 x0) = (Nat.mul x0 x1)).
Definition term147 (x0 : Prop) (x1 : nat -> Prop) := x0 /\ (exists y0 : nat, x1 y0).
Definition term201 (x0 : nat) (x1 : nat) := (exists y0 : nat, (fun y1 : nat => (x0 = (Nat.mul x1 y1)) /\ (forall y2 : nat, ~ (x0 = (Nat.mul y2 x1)))) y0) \/ (exists y0 : nat, (fun y1 : nat => (forall y2 : nat, ~ (x0 = (Nat.mul x1 y2))) /\ (x0 = (Nat.mul y1 x1))) y0).
Definition term183 (x0 : nat) := (exists y0 : nat, (fun y1 : nat => exists y2 : nat, (y1 = (Nat.mul x0 y2)) /\ (forall y3 : nat, ~ (y1 = (Nat.mul y3 x0)))) y0) \/ (exists y0 : nat, (fun y1 : nat => exists y2 : nat, (forall y3 : nat, ~ (y1 = (Nat.mul x0 y3))) /\ (y1 = (Nat.mul y2 x0))) y0).
Definition term165 := (exists y0 : nat, (fun y1 : nat => exists y2 : nat, exists y3 : nat, (y2 = (Nat.mul y1 y3)) /\ (forall y4 : nat, ~ (y2 = (Nat.mul y4 y1)))) y0) \/ (exists y0 : nat, (fun y1 : nat => exists y2 : nat, exists y3 : nat, (forall y4 : nat, ~ (y2 = (Nat.mul y1 y4))) /\ (y2 = (Nat.mul y3 y1))) y0).
Definition term103 := (exists y0 : nat, (fun y1 : nat => exists y2 : nat, (exists y3 : nat, y2 = (Nat.mul y1 y3)) /\ (forall y3 : nat, ~ (y2 = (Nat.mul y3 y1)))) y0) \/ (exists y0 : nat, (fun y1 : nat => exists y2 : nat, (forall y3 : nat, ~ (y2 = (Nat.mul y1 y3))) /\ (exists y3 : nat, y2 = (Nat.mul y3 y1))) y0).
Definition term81 (x0 : nat) := (exists y0 : nat, (fun y1 : nat => (exists y2 : nat, y1 = (Nat.mul x0 y2)) /\ (forall y2 : nat, ~ (y1 = (Nat.mul y2 x0)))) y0) \/ (exists y0 : nat, (fun y1 : nat => (forall y2 : nat, ~ (y1 = (Nat.mul x0 y2))) /\ (exists y2 : nat, y1 = (Nat.mul y2 x0))) y0).
Definition term22 := (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> False.
Definition term135 (x0 : nat) (x1 : nat) (x2 : nat) := ((fun y0 : nat => x1 = (Nat.mul x2 y0)) x0) /\ (forall y0 : nat, ~ (x1 = (Nat.mul y0 x2))).
Definition term8 (x0 : nat) := fun y0 : nat => (exists y1 : nat, y0 = (Nat.mul x0 y1)) = (exists y1 : nat, y0 = (Nat.mul y1 x0)).
Definition term51 (x0 : nat) (x1 : nat) := (~ (exists y0 : nat, x0 = (Nat.mul x1 y0))) /\ (exists y0 : nat, x0 = (Nat.mul y0 x1)).
Definition term4 (x0 : nat) (x1 : nat) := exists y0 : nat, x0 = (Nat.mul x1 y0).
Definition term20 := (((~ (forall y0 : nat, forall y1 : nat, (exists y2 : nat, y1 = (Nat.mul y0 y2)) = (exists y2 : nat, y1 = (Nat.mul y2 y0)))) -> (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> False) -> (~ (forall y0 : nat, forall y1 : nat, (exists y2 : nat, y1 = (Nat.mul y0 y2)) = (exists y2 : nat, y1 = (Nat.mul y2 y0)))) -> (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> False) -> (~ (forall y0 : nat, forall y1 : nat, (exists y2 : nat, y1 = (Nat.mul y0 y2)) = (exists y2 : nat, y1 = (Nat.mul y2 y0)))) -> (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> False.
Definition term31 (x0 : nat) (x1 : nat) := fun y0 : nat => x0 = (Nat.mul x1 y0).
Definition term230 (x0 : nat) (x1 : nat) := fun y0 : nat => ~ (y0 = (Nat.mul x0 x1)).
Definition term194 (x0 : nat) (x1 : nat) := or ((fun y0 : nat => exists y1 : nat, (y0 = (Nat.mul x0 y1)) /\ (forall y2 : nat, ~ (y0 = (Nat.mul y2 x0)))) x1).
Definition term189 (x0 : nat) (x1 : nat) := (fun y0 : nat => exists y1 : nat, (forall y2 : nat, ~ (y0 = (Nat.mul x0 y2))) /\ (y0 = (Nat.mul y1 x0))) x1.
Definition term185 (x0 : nat) (x1 : nat) := (fun y0 : nat => exists y1 : nat, (y0 = (Nat.mul x0 y1)) /\ (forall y2 : nat, ~ (y0 = (Nat.mul y2 x0)))) x1.
Definition term24 := forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0).
Definition term14 := forall y0 : nat, forall y1 : nat, (exists y2 : nat, y1 = (Nat.mul y0 y2)) = (exists y2 : nat, y1 = (Nat.mul y2 y0)).
Definition term13 := forall y0 : nat, forall y1 : nat, (num_divides y0 y1) = ((Nat.modulo y1 y0) = (NUMERAL 0)).
Definition term45 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((fun y0 : nat => x0 = (Nat.mul y0 x1)) x2).
Definition term37 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((fun y0 : nat => x0 = (Nat.mul x1 y0)) x2).
Definition term123 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) /\ x1.
Definition term32 (x0 : nat -> Prop) := ~ (ex x0).
Definition term224 := fun y0 : nat => exists y1 : nat, exists y2 : nat, ((y1 = (Nat.mul y0 y2)) /\ (forall y3 : nat, ~ (y1 = (Nat.mul y3 y0)))) \/ ((forall y3 : nat, ~ (y1 = (Nat.mul y0 y3))) /\ (y1 = (Nat.mul y2 y0))).
Definition term162 := fun y0 : nat => exists y1 : nat, exists y2 : nat, (forall y3 : nat, ~ (y1 = (Nat.mul y0 y3))) /\ (y1 = (Nat.mul y2 y0)).
Definition term142 := fun y0 : nat => exists y1 : nat, exists y2 : nat, (y1 = (Nat.mul y0 y2)) /\ (forall y3 : nat, ~ (y1 = (Nat.mul y3 y0))).
Definition term200 (x0 : nat) := exists y0 : nat, (exists y1 : nat, (y0 = (Nat.mul x0 y1)) /\ (forall y2 : nat, ~ (y0 = (Nat.mul y2 x0)))) \/ (exists y1 : nat, (forall y2 : nat, ~ (y0 = (Nat.mul x0 y2))) /\ (y0 = (Nat.mul y1 x0))).
Definition term182 := exists y0 : nat, (exists y1 : nat, exists y2 : nat, (y1 = (Nat.mul y0 y2)) /\ (forall y3 : nat, ~ (y1 = (Nat.mul y3 y0)))) \/ (exists y1 : nat, exists y2 : nat, (forall y3 : nat, ~ (y1 = (Nat.mul y0 y3))) /\ (y1 = (Nat.mul y2 y0))).
Definition term101 := exists y0 : nat, (exists y1 : nat, (exists y2 : nat, y1 = (Nat.mul y0 y2)) /\ (forall y2 : nat, ~ (y1 = (Nat.mul y2 y0)))) \/ (exists y1 : nat, (forall y2 : nat, ~ (y1 = (Nat.mul y0 y2))) /\ (exists y2 : nat, y1 = (Nat.mul y2 y0))).
Definition term12 := fun y0 : nat => forall y1 : nat, (exists y2 : nat, y1 = (Nat.mul y0 y2)) = (exists y2 : nat, y1 = (Nat.mul y2 y0)).
Definition term202 (x0 : nat) (x1 : nat) := exists y0 : nat, ((fun y1 : nat => (x0 = (Nat.mul x1 y1)) /\ (forall y2 : nat, ~ (x0 = (Nat.mul y2 x1)))) y0) \/ ((fun y1 : nat => (forall y2 : nat, ~ (x0 = (Nat.mul x1 y2))) /\ (x0 = (Nat.mul y1 x1))) y0).
Definition term184 (x0 : nat) := exists y0 : nat, ((fun y1 : nat => exists y2 : nat, (y1 = (Nat.mul x0 y2)) /\ (forall y3 : nat, ~ (y1 = (Nat.mul y3 x0)))) y0) \/ ((fun y1 : nat => exists y2 : nat, (forall y3 : nat, ~ (y1 = (Nat.mul x0 y3))) /\ (y1 = (Nat.mul y2 x0))) y0).
Definition term166 := exists y0 : nat, ((fun y1 : nat => exists y2 : nat, exists y3 : nat, (y2 = (Nat.mul y1 y3)) /\ (forall y4 : nat, ~ (y2 = (Nat.mul y4 y1)))) y0) \/ ((fun y1 : nat => exists y2 : nat, exists y3 : nat, (forall y4 : nat, ~ (y2 = (Nat.mul y1 y4))) /\ (y2 = (Nat.mul y3 y1))) y0).
Definition term102 := exists y0 : nat, ((fun y1 : nat => exists y2 : nat, (exists y3 : nat, y2 = (Nat.mul y1 y3)) /\ (forall y3 : nat, ~ (y2 = (Nat.mul y3 y1)))) y0) \/ ((fun y1 : nat => exists y2 : nat, (forall y3 : nat, ~ (y2 = (Nat.mul y1 y3))) /\ (exists y3 : nat, y2 = (Nat.mul y3 y1))) y0).
Definition term80 (x0 : nat) := exists y0 : nat, ((fun y1 : nat => (exists y2 : nat, y1 = (Nat.mul x0 y2)) /\ (forall y2 : nat, ~ (y1 = (Nat.mul y2 x0)))) y0) \/ ((fun y1 : nat => (forall y2 : nat, ~ (y1 = (Nat.mul x0 y2))) /\ (exists y2 : nat, y1 = (Nat.mul y2 x0))) y0).
Definition term83 (x0 : nat) := fun y0 : nat => (forall y1 : nat, ~ (y0 = (Nat.mul x0 y1))) /\ (exists y1 : nat, y0 = (Nat.mul y1 x0)).
Definition term33 (x0 : nat -> Prop) := forall y0 : nat, ~ (x0 y0).
Definition term82 (x0 : nat) := fun y0 : nat => (exists y1 : nat, y0 = (Nat.mul x0 y1)) /\ (forall y1 : nat, ~ (y0 = (Nat.mul y1 x0))).
Definition term93 (x0 : nat) := exists y0 : nat, (exists y1 : nat, y0 = (Nat.mul x0 y1)) /\ (forall y1 : nat, ~ (y0 = (Nat.mul y1 x0))).
Definition term196 (x0 : nat) (x1 : nat) := ((fun y0 : nat => exists y1 : nat, (y0 = (Nat.mul x0 y1)) /\ (forall y2 : nat, ~ (y0 = (Nat.mul y2 x0)))) x1) \/ ((fun y0 : nat => exists y1 : nat, (forall y2 : nat, ~ (y0 = (Nat.mul x0 y2))) /\ (y0 = (Nat.mul y1 x0))) x1).
Definition term177 (x0 : nat) := or (exists y0 : nat, exists y1 : nat, (y0 = (Nat.mul x0 y1)) /\ (forall y2 : nat, ~ (y0 = (Nat.mul y2 x0)))).
Definition term144 := or (exists y0 : nat, exists y1 : nat, exists y2 : nat, (y1 = (Nat.mul y0 y2)) /\ (forall y3 : nat, ~ (y1 = (Nat.mul y3 y0)))).
Definition term117 := or (exists y0 : nat, exists y1 : nat, (exists y2 : nat, y1 = (Nat.mul y0 y2)) /\ (forall y2 : nat, ~ (y1 = (Nat.mul y2 y0)))).
Definition term125 (x0 : nat -> Prop) (x1 : Prop) := exists y0 : nat, (x0 y0) /\ x1.
Definition term16 := (~ (forall y0 : nat, forall y1 : nat, (exists y2 : nat, y1 = (Nat.mul y0 y2)) = (exists y2 : nat, y1 = (Nat.mul y2 y0)))) -> False.
Definition term73 := fun y0 : nat => ~ ((fun y1 : nat => forall y2 : nat, (exists y3 : nat, y2 = (Nat.mul y1 y3)) = (exists y3 : nat, y2 = (Nat.mul y3 y1))) y0).
Definition term28 (x0 : nat) := forall y0 : nat, (Nat.mul x0 y0) = (Nat.mul y0 x0).
Definition term217 (x0 : nat) (x1 : nat) := fun y0 : nat => ((x0 = (Nat.mul x1 y0)) /\ (forall y1 : nat, ~ (x0 = (Nat.mul y1 x1)))) \/ ((forall y1 : nat, ~ (x0 = (Nat.mul x1 y1))) /\ (x0 = (Nat.mul y0 x1))).
Definition term3 (x0 : nat) (x1 : nat) := exists y0 : nat, x0 = (Nat.mul y0 x1).
Definition term52 (x0 : nat) (x1 : nat) := (forall y0 : nat, ~ (x0 = (Nat.mul x1 y0))) /\ (exists y0 : nat, x0 = (Nat.mul y0 x1)).
Definition term159 (x0 : nat) (x1 : nat) := exists y0 : nat, (forall y1 : nat, ~ (x0 = (Nat.mul x1 y1))) /\ (x0 = (Nat.mul y0 x1)).
Definition term209 (x0 : nat) (x1 : nat) := exists y0 : nat, (fun y1 : nat => (forall y2 : nat, ~ (x0 = (Nat.mul x1 y2))) /\ (x0 = (Nat.mul y1 x1))) y0.
Definition term205 (x0 : nat) (x1 : nat) := exists y0 : nat, (fun y1 : nat => (x0 = (Nat.mul x1 y1)) /\ (forall y2 : nat, ~ (x0 = (Nat.mul y2 x1)))) y0.
Definition term152 (x0 : nat) (x1 : nat) := exists y0 : nat, (fun y1 : nat => x0 = (Nat.mul y1 x1)) y0.
Definition term129 (x0 : nat) (x1 : nat) := exists y0 : nat, (fun y1 : nat => x0 = (Nat.mul x1 y1)) y0.
Definition term97 (x0 : nat) := exists y0 : nat, (fun y1 : nat => (forall y2 : nat, ~ (y1 = (Nat.mul x0 y2))) /\ (exists y2 : nat, y1 = (Nat.mul y2 x0))) y0.
Definition term92 (x0 : nat) := exists y0 : nat, (fun y1 : nat => (exists y2 : nat, y1 = (Nat.mul x0 y2)) /\ (forall y2 : nat, ~ (y1 = (Nat.mul y2 x0)))) y0.
Definition term156 (x0 : nat) (x1 : nat) (x2 : nat) := (forall y0 : nat, ~ (x0 = (Nat.mul x2 y0))) /\ (x0 = (Nat.mul x1 x2)).
Definition term227 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.mul x0 y0) = (Nat.mul y0 x0)) x1.
Definition term235 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop (~ (x0 = (Nat.mul x1 x2))).
Definition term48 (x0 : nat) (x1 : nat) := forall y0 : nat, ~ (x0 = (Nat.mul y0 x1)).
Definition term41 (x0 : nat) (x1 : nat) := forall y0 : nat, ~ (x0 = (Nat.mul x1 y0)).
Definition term234 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((fun y0 : nat => ~ (y0 = (Nat.mul x0 x1))) x2).
Definition term199 (x0 : nat) := fun y0 : nat => (exists y1 : nat, (y0 = (Nat.mul x0 y1)) /\ (forall y2 : nat, ~ (y0 = (Nat.mul y2 x0)))) \/ (exists y1 : nat, (forall y2 : nat, ~ (y0 = (Nat.mul x0 y2))) /\ (y0 = (Nat.mul y1 x0))).
Definition term100 := fun y0 : nat => (exists y1 : nat, (exists y2 : nat, y1 = (Nat.mul y0 y2)) /\ (forall y2 : nat, ~ (y1 = (Nat.mul y2 y0)))) \/ (exists y1 : nat, (forall y2 : nat, ~ (y1 = (Nat.mul y0 y2))) /\ (exists y2 : nat, y1 = (Nat.mul y2 y0))).
Definition term242 (x0 : nat) (x1 : nat) := ((Nat.mul x1 x0) = (Nat.mul x0 x1)) -> False.
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Nat.modulo x0 y0) = (NUMERAL 0)) = (exists y1 : nat, x0 = (Nat.mul y1 y0))) x1.
Definition term198 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => exists y2 : nat, (y1 = (Nat.mul x0 y2)) /\ (forall y3 : nat, ~ (y1 = (Nat.mul y3 x0)))) y0) \/ ((fun y1 : nat => exists y2 : nat, (forall y3 : nat, ~ (y1 = (Nat.mul x0 y3))) /\ (y1 = (Nat.mul y2 x0))) y0).
Definition term180 := fun y0 : nat => ((fun y1 : nat => exists y2 : nat, exists y3 : nat, (y2 = (Nat.mul y1 y3)) /\ (forall y4 : nat, ~ (y2 = (Nat.mul y4 y1)))) y0) \/ ((fun y1 : nat => exists y2 : nat, exists y3 : nat, (forall y4 : nat, ~ (y2 = (Nat.mul y1 y4))) /\ (y2 = (Nat.mul y3 y1))) y0).
Definition term110 := fun y0 : nat => ((fun y1 : nat => exists y2 : nat, (exists y3 : nat, y2 = (Nat.mul y1 y3)) /\ (forall y3 : nat, ~ (y2 = (Nat.mul y3 y1)))) y0) \/ ((fun y1 : nat => exists y2 : nat, (forall y3 : nat, ~ (y2 = (Nat.mul y1 y3))) /\ (exists y3 : nat, y2 = (Nat.mul y3 y1))) y0).
Definition term72 (x0 : nat) := ~ ((fun y0 : nat => forall y1 : nat, (exists y2 : nat, y1 = (Nat.mul y0 y2)) = (exists y2 : nat, y1 = (Nat.mul y2 y0))) x0).
Definition term59 (x0 : nat) (x1 : nat) := ((exists y0 : nat, x0 = (Nat.mul x1 y0)) /\ (forall y0 : nat, ~ (x0 = (Nat.mul y0 x1)))) \/ ((forall y0 : nat, ~ (x0 = (Nat.mul x1 y0))) /\ (exists y0 : nat, x0 = (Nat.mul y0 x1))).
Definition term124 (x0 : nat -> Prop) (x1 : Prop) := (exists y0 : nat, x0 y0) /\ x1.
Definition term176 (x0 : nat) := or ((fun y0 : nat => exists y1 : nat, exists y2 : nat, (y1 = (Nat.mul y0 y2)) /\ (forall y3 : nat, ~ (y1 = (Nat.mul y3 y0)))) x0).
Definition term107 (x0 : nat) := or ((fun y0 : nat => exists y1 : nat, (exists y2 : nat, y1 = (Nat.mul y0 y2)) /\ (forall y2 : nat, ~ (y1 = (Nat.mul y2 y0)))) x0).
Definition term43 (x0 : nat) (x1 : nat) := forall y0 : nat, ~ ((fun y1 : nat => x0 = (Nat.mul y1 x1)) y0).
Definition term35 (x0 : nat) (x1 : nat) := forall y0 : nat, ~ ((fun y1 : nat => x0 = (Nat.mul x1 y1)) y0).
Definition term137 (x0 : nat) (x1 : nat) := fun y0 : nat => ((fun y1 : nat => x0 = (Nat.mul x1 y1)) y0) /\ (forall y1 : nat, ~ (x0 = (Nat.mul y1 x1))).
Definition term226 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) x0.
Definition term71 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (exists y2 : nat, y1 = (Nat.mul y0 y2)) = (exists y2 : nat, y1 = (Nat.mul y2 y0))) x0.
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.modulo y0 y1) = (NUMERAL 0)) = (exists y2 : nat, y0 = (Nat.mul y2 y1))) x0.
Definition term140 (x0 : nat) := fun y0 : nat => exists y1 : nat, (y0 = (Nat.mul x0 y1)) /\ (forall y2 : nat, ~ (y0 = (Nat.mul y2 x0))).
Definition term105 := fun y0 : nat => exists y1 : nat, (forall y2 : nat, ~ (y1 = (Nat.mul y0 y2))) /\ (exists y2 : nat, y1 = (Nat.mul y2 y0)).
Definition term104 := fun y0 : nat => exists y1 : nat, (exists y2 : nat, y1 = (Nat.mul y0 y2)) /\ (forall y2 : nat, ~ (y1 = (Nat.mul y2 y0))).
Definition term53 (x0 : nat) (x1 : nat) := and (exists y0 : nat, x0 = (Nat.mul x1 y0)).
Definition term157 (x0 : nat) (x1 : nat) := fun y0 : nat => (forall y1 : nat, ~ (x0 = (Nat.mul x1 y1))) /\ ((fun y1 : nat => x0 = (Nat.mul y1 x1)) y0).
Definition term136 (x0 : nat) (x1 : nat) (x2 : nat) := (x1 = (Nat.mul x2 x0)) /\ (forall y0 : nat, ~ (x1 = (Nat.mul y0 x2))).
Definition term70 := exists y0 : nat, ~ ((fun y1 : nat => forall y2 : nat, (exists y3 : nat, y2 = (Nat.mul y1 y3)) = (exists y3 : nat, y2 = (Nat.mul y3 y1))) y0).
Definition term64 (x0 : nat) := exists y0 : nat, ~ ((fun y1 : nat => (exists y2 : nat, y1 = (Nat.mul x0 y2)) = (exists y2 : nat, y1 = (Nat.mul y2 x0))) y0).
Definition term212 (x0 : nat) (x1 : nat) (x2 : nat) := or ((fun y0 : nat => (x0 = (Nat.mul x1 y0)) /\ (forall y1 : nat, ~ (x0 = (Nat.mul y1 x1)))) x2).
Definition term179 (x0 : nat) := (exists y0 : nat, exists y1 : nat, (y0 = (Nat.mul x0 y1)) /\ (forall y2 : nat, ~ (y0 = (Nat.mul y2 x0)))) \/ (exists y0 : nat, exists y1 : nat, (forall y2 : nat, ~ (y0 = (Nat.mul x0 y2))) /\ (y0 = (Nat.mul y1 x0))).
Definition term164 := (exists y0 : nat, exists y1 : nat, exists y2 : nat, (y1 = (Nat.mul y0 y2)) /\ (forall y3 : nat, ~ (y1 = (Nat.mul y3 y0)))) \/ (exists y0 : nat, exists y1 : nat, exists y2 : nat, (forall y3 : nat, ~ (y1 = (Nat.mul y0 y3))) /\ (y1 = (Nat.mul y2 y0))).
Definition term121 := (exists y0 : nat, exists y1 : nat, (exists y2 : nat, y1 = (Nat.mul y0 y2)) /\ (forall y2 : nat, ~ (y1 = (Nat.mul y2 y0)))) \/ (exists y0 : nat, exists y1 : nat, (forall y2 : nat, ~ (y1 = (Nat.mul y0 y2))) /\ (exists y2 : nat, y1 = (Nat.mul y2 y0))).
Definition term26 := (~ (forall y0 : nat, forall y1 : nat, (exists y2 : nat, y1 = (Nat.mul y0 y2)) = (exists y2 : nat, y1 = (Nat.mul y2 y0)))) -> ~ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)).
Definition term84 (x0 : nat) (x1 : nat) := (fun y0 : nat => (exists y1 : nat, y0 = (Nat.mul x0 y1)) /\ (forall y1 : nat, ~ (y0 = (Nat.mul y1 x0)))) x1.
Definition term208 (x0 : nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => (forall y2 : nat, ~ (x0 = (Nat.mul x1 y2))) /\ (x0 = (Nat.mul y1 x1))) y0.
Definition term58 (x0 : nat) (x1 : nat) := ((exists y0 : nat, x0 = (Nat.mul x1 y0)) /\ (~ (exists y0 : nat, x0 = (Nat.mul y0 x1)))) \/ ((~ (exists y0 : nat, x0 = (Nat.mul x1 y0))) /\ (exists y0 : nat, x0 = (Nat.mul y0 x1))).
Definition term236 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ~ (y0 = (Nat.mul x2 x0))) (Nat.mul x1 x2).
Definition term232 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ~ (y0 = (Nat.mul x0 x1))) (Nat.mul x1 x2).
Definition term231 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ~ (y0 = (Nat.mul x0 x1))) x2.
Definition term155 (x0 : nat) (x1 : nat) (x2 : nat) := (forall y0 : nat, ~ (x0 = (Nat.mul x1 y0))) /\ ((fun y0 : nat => x0 = (Nat.mul y0 x1)) x2).
Definition term181 := fun y0 : nat => (exists y1 : nat, exists y2 : nat, (y1 = (Nat.mul y0 y2)) /\ (forall y3 : nat, ~ (y1 = (Nat.mul y3 y0)))) \/ (exists y1 : nat, exists y2 : nat, (forall y3 : nat, ~ (y1 = (Nat.mul y0 y3))) /\ (y1 = (Nat.mul y2 y0))).
Definition term237 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((Nat.mul x0 x1) = (Nat.mul x1 x2)).
Definition term171 (x0 : nat) := (fun y0 : nat => exists y1 : nat, exists y2 : nat, (forall y3 : nat, ~ (y1 = (Nat.mul y0 y3))) /\ (y1 = (Nat.mul y2 y0))) x0.
Definition term167 (x0 : nat) := (fun y0 : nat => exists y1 : nat, exists y2 : nat, (y1 = (Nat.mul y0 y2)) /\ (forall y3 : nat, ~ (y1 = (Nat.mul y3 y0)))) x0.
Definition term213 (x0 : nat) (x1 : nat) (x2 : nat) := or ((x1 = (Nat.mul x2 x0)) /\ (forall y0 : nat, ~ (x1 = (Nat.mul y0 x2)))).
Definition term1 (x0 : nat) := forall y0 : nat, ((Nat.modulo x0 y0) = (NUMERAL 0)) = (exists y1 : nat, x0 = (Nat.mul y1 y0)).
Definition term154 (x0 : nat) (x1 : nat) := @eq Prop ((forall y0 : nat, ~ (x0 = (Nat.mul x1 y0))) /\ (exists y0 : nat, x0 = (Nat.mul y0 x1))).
Definition term153 (x0 : nat) (x1 : nat) := @eq Prop ((forall y0 : nat, ~ (x0 = (Nat.mul x1 y0))) /\ (exists y0 : nat, (fun y1 : nat => x0 = (Nat.mul y1 x1)) y0)).
Definition term191 (x0 : nat) := exists y0 : nat, (fun y1 : nat => exists y2 : nat, (forall y3 : nat, ~ (y1 = (Nat.mul x0 y3))) /\ (y1 = (Nat.mul y2 x0))) y0.
Definition term187 (x0 : nat) := exists y0 : nat, (fun y1 : nat => exists y2 : nat, (y1 = (Nat.mul x0 y2)) /\ (forall y3 : nat, ~ (y1 = (Nat.mul y3 x0)))) y0.
Definition term173 := exists y0 : nat, (fun y1 : nat => exists y2 : nat, exists y3 : nat, (forall y4 : nat, ~ (y2 = (Nat.mul y1 y4))) /\ (y2 = (Nat.mul y3 y1))) y0.
Definition term169 := exists y0 : nat, (fun y1 : nat => exists y2 : nat, exists y3 : nat, (y2 = (Nat.mul y1 y3)) /\ (forall y4 : nat, ~ (y2 = (Nat.mul y4 y1)))) y0.
Definition term119 := exists y0 : nat, (fun y1 : nat => exists y2 : nat, (forall y3 : nat, ~ (y2 = (Nat.mul y1 y3))) /\ (exists y3 : nat, y2 = (Nat.mul y3 y1))) y0.
Definition term114 := exists y0 : nat, (fun y1 : nat => exists y2 : nat, (exists y3 : nat, y2 = (Nat.mul y1 y3)) /\ (forall y3 : nat, ~ (y2 = (Nat.mul y3 y1)))) y0.
Definition term225 := exists y0 : nat, exists y1 : nat, exists y2 : nat, ((y1 = (Nat.mul y0 y2)) /\ (forall y3 : nat, ~ (y1 = (Nat.mul y3 y0)))) \/ ((forall y3 : nat, ~ (y1 = (Nat.mul y0 y3))) /\ (y1 = (Nat.mul y2 y0))).
Definition term223 (x0 : nat) := exists y0 : nat, exists y1 : nat, ((y0 = (Nat.mul x0 y1)) /\ (forall y2 : nat, ~ (y0 = (Nat.mul y2 x0)))) \/ ((forall y2 : nat, ~ (y0 = (Nat.mul x0 y2))) /\ (y0 = (Nat.mul y1 x0))).
Definition term163 := exists y0 : nat, exists y1 : nat, exists y2 : nat, (forall y3 : nat, ~ (y1 = (Nat.mul y0 y3))) /\ (y1 = (Nat.mul y2 y0)).
Definition term161 (x0 : nat) := exists y0 : nat, exists y1 : nat, (forall y2 : nat, ~ (y0 = (Nat.mul x0 y2))) /\ (y0 = (Nat.mul y1 x0)).
Definition term143 := exists y0 : nat, exists y1 : nat, exists y2 : nat, (y1 = (Nat.mul y0 y2)) /\ (forall y3 : nat, ~ (y1 = (Nat.mul y3 y0))).
Definition term141 (x0 : nat) := exists y0 : nat, exists y1 : nat, (y0 = (Nat.mul x0 y1)) /\ (forall y2 : nat, ~ (y0 = (Nat.mul y2 x0))).
Definition term120 := exists y0 : nat, exists y1 : nat, (forall y2 : nat, ~ (y1 = (Nat.mul y0 y2))) /\ (exists y2 : nat, y1 = (Nat.mul y2 y0)).
Definition term115 := exists y0 : nat, exists y1 : nat, (exists y2 : nat, y1 = (Nat.mul y0 y2)) /\ (forall y2 : nat, ~ (y1 = (Nat.mul y2 y0))).
Definition term75 := exists y0 : nat, exists y1 : nat, ((exists y2 : nat, y1 = (Nat.mul y0 y2)) /\ (forall y2 : nat, ~ (y1 = (Nat.mul y2 y0)))) \/ ((forall y2 : nat, ~ (y1 = (Nat.mul y0 y2))) /\ (exists y2 : nat, y1 = (Nat.mul y2 y0))).
Definition term139 (x0 : nat) (x1 : nat) := exists y0 : nat, (x0 = (Nat.mul x1 y0)) /\ (forall y1 : nat, ~ (x0 = (Nat.mul y1 x1))).
Definition term78 (x0 : nat -> Prop) (x1 : nat -> Prop) := exists y0 : nat, (x0 y0) \/ (x1 y0).
Definition term40 (x0 : nat) (x1 : nat) := fun y0 : nat => ~ (x0 = (Nat.mul x1 y0)).
Definition term67 (x0 : nat) := fun y0 : nat => ~ ((fun y1 : nat => (exists y2 : nat, y1 = (Nat.mul x0 y2)) = (exists y2 : nat, y1 = (Nat.mul y2 x0))) y0).
Definition term46 (x0 : nat) (x1 : nat) := fun y0 : nat => ~ ((fun y1 : nat => x0 = (Nat.mul y1 x1)) y0).
Definition term39 (x0 : nat) (x1 : nat) := fun y0 : nat => ~ ((fun y1 : nat => x0 = (Nat.mul x1 y1)) y0).
Definition term66 (x0 : nat) (x1 : nat) := ~ ((fun y0 : nat => (exists y1 : nat, y0 = (Nat.mul x0 y1)) = (exists y1 : nat, y0 = (Nat.mul y1 x0))) x1).
Definition term132 (x0 : nat) (x1 : nat) := @eq Prop ((exists y0 : nat, x0 = (Nat.mul x1 y0)) /\ (forall y0 : nat, ~ (x0 = (Nat.mul y0 x1)))).
Definition term131 (x0 : nat) (x1 : nat) := @eq Prop ((exists y0 : nat, (fun y1 : nat => x0 = (Nat.mul x1 y1)) y0) /\ (forall y0 : nat, ~ (x0 = (Nat.mul y0 x1)))).
Definition term56 (x0 : nat) (x1 : nat) := or ((exists y0 : nat, x0 = (Nat.mul x1 y0)) /\ (~ (exists y0 : nat, x0 = (Nat.mul y0 x1)))).
Definition term122 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) /\ x1.
Definition term216 (x0 : nat) (x1 : nat) := fun y0 : nat => ((fun y1 : nat => (x0 = (Nat.mul x1 y1)) /\ (forall y2 : nat, ~ (x0 = (Nat.mul y2 x1)))) y0) \/ ((fun y1 : nat => (forall y2 : nat, ~ (x0 = (Nat.mul x1 y2))) /\ (x0 = (Nat.mul y1 x1))) y0).
Definition term88 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => (exists y2 : nat, y1 = (Nat.mul x0 y2)) /\ (forall y2 : nat, ~ (y1 = (Nat.mul y2 x0)))) y0) \/ ((fun y1 : nat => (forall y2 : nat, ~ (y1 = (Nat.mul x0 y2))) /\ (exists y2 : nat, y1 = (Nat.mul y2 x0))) y0).
Definition term203 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (x0 = (Nat.mul x1 y0)) /\ (forall y1 : nat, ~ (x0 = (Nat.mul y1 x1)))) x2.
Definition term206 (x0 : nat) (x1 : nat) := or (exists y0 : nat, (fun y1 : nat => (x0 = (Nat.mul x1 y1)) /\ (forall y2 : nat, ~ (x0 = (Nat.mul y2 x1)))) y0).
Definition term188 (x0 : nat) := or (exists y0 : nat, (fun y1 : nat => exists y2 : nat, (y1 = (Nat.mul x0 y2)) /\ (forall y3 : nat, ~ (y1 = (Nat.mul y3 x0)))) y0).
Definition term170 := or (exists y0 : nat, (fun y1 : nat => exists y2 : nat, exists y3 : nat, (y2 = (Nat.mul y1 y3)) /\ (forall y4 : nat, ~ (y2 = (Nat.mul y4 y1)))) y0).
Definition term116 := or (exists y0 : nat, (fun y1 : nat => exists y2 : nat, (exists y3 : nat, y2 = (Nat.mul y1 y3)) /\ (forall y3 : nat, ~ (y2 = (Nat.mul y3 y1)))) y0).
Definition term94 (x0 : nat) := or (exists y0 : nat, (fun y1 : nat => (exists y2 : nat, y1 = (Nat.mul x0 y2)) /\ (forall y2 : nat, ~ (y1 = (Nat.mul y2 x0)))) y0).
Definition term19 := ((~ (forall y0 : nat, forall y1 : nat, (exists y2 : nat, y1 = (Nat.mul y0 y2)) = (exists y2 : nat, y1 = (Nat.mul y2 y0)))) -> (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> False) -> (~ (forall y0 : nat, forall y1 : nat, (exists y2 : nat, y1 = (Nat.mul y0 y2)) = (exists y2 : nat, y1 = (Nat.mul y2 y0)))) -> (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> False.
Definition term9 (x0 : nat) := forall y0 : nat, (num_divides x0 y0) = ((Nat.modulo y0 x0) = (NUMERAL 0)).
Definition term38 (x0 : nat) (x1 : nat) (x2 : nat) := ~ (x0 = (Nat.mul x1 x2)).
Definition term21 := (((~ (forall y0 : nat, forall y1 : nat, (exists y2 : nat, y1 = (Nat.mul y0 y2)) = (exists y2 : nat, y1 = (Nat.mul y2 y0)))) -> (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> False) -> (~ (forall y0 : nat, forall y1 : nat, (exists y2 : nat, y1 = (Nat.mul y0 y2)) = (exists y2 : nat, y1 = (Nat.mul y2 y0)))) -> (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> False) -> ((~ (forall y0 : nat, forall y1 : nat, (exists y2 : nat, y1 = (Nat.mul y0 y2)) = (exists y2 : nat, y1 = (Nat.mul y2 y0)))) -> (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> False) -> (~ (forall y0 : nat, forall y1 : nat, (exists y2 : nat, y1 = (Nat.mul y0 y2)) = (exists y2 : nat, y1 = (Nat.mul y2 y0)))) -> (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> False.
Definition term87 (x0 : nat) (x1 : nat) := ((fun y0 : nat => (exists y1 : nat, y0 = (Nat.mul x0 y1)) /\ (forall y1 : nat, ~ (y0 = (Nat.mul y1 x0)))) x1) \/ ((fun y0 : nat => (forall y1 : nat, ~ (y0 = (Nat.mul x0 y1))) /\ (exists y1 : nat, y0 = (Nat.mul y1 x0))) x1).
Definition term55 (x0 : nat) (x1 : nat) := (exists y0 : nat, x0 = (Nat.mul x1 y0)) /\ (forall y0 : nat, ~ (x0 = (Nat.mul y0 x1))).
Definition term65 (x0 : nat) (x1 : nat) := (fun y0 : nat => (exists y1 : nat, y0 = (Nat.mul x0 y1)) = (exists y1 : nat, y0 = (Nat.mul y1 x0))) x1.
Definition term138 (x0 : nat) (x1 : nat) := fun y0 : nat => (x0 = (Nat.mul x1 y0)) /\ (forall y1 : nat, ~ (x0 = (Nat.mul y1 x1))).
Definition term76 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term62 (x0 : nat -> Prop) := exists y0 : nat, ~ (x0 y0).
Definition term42 (x0 : nat) (x1 : nat) := ~ (exists y0 : nat, x0 = (Nat.mul y0 x1)).
Definition term34 (x0 : nat) (x1 : nat) := ~ (exists y0 : nat, x0 = (Nat.mul x1 y0)).
Definition term11 := fun y0 : nat => forall y1 : nat, (num_divides y0 y1) = ((Nat.modulo y1 y0) = (NUMERAL 0)).
Definition term79 (x0 : nat -> Prop) (x1 : nat -> Prop) := (exists y0 : nat, x0 y0) \/ (exists y0 : nat, x1 y0).
Definition term25 := imp (~ (forall y0 : nat, forall y1 : nat, (exists y2 : nat, y1 = (Nat.mul y0 y2)) = (exists y2 : nat, y1 = (Nat.mul y2 y0)))).
Definition term215 (x0 : nat) (x1 : nat) (x2 : nat) := ((x0 = (Nat.mul x2 x1)) /\ (forall y0 : nat, ~ (x0 = (Nat.mul y0 x2)))) \/ ((forall y0 : nat, ~ (x0 = (Nat.mul x2 y0))) /\ (x0 = (Nat.mul x1 x2))).
Definition term150 (x0 : nat) (x1 : nat) := exists y0 : nat, (forall y1 : nat, ~ (x0 = (Nat.mul x1 y1))) /\ ((fun y1 : nat => x0 = (Nat.mul y1 x1)) y0).
Definition term211 (x0 : nat) (x1 : nat) := @eq Prop ((exists y0 : nat, (x0 = (Nat.mul x1 y0)) /\ (forall y1 : nat, ~ (x0 = (Nat.mul y1 x1)))) \/ (exists y0 : nat, (forall y1 : nat, ~ (x0 = (Nat.mul x1 y1))) /\ (x0 = (Nat.mul y0 x1)))).
Definition term210 (x0 : nat) (x1 : nat) := @eq Prop ((exists y0 : nat, (fun y1 : nat => (x0 = (Nat.mul x1 y1)) /\ (forall y2 : nat, ~ (x0 = (Nat.mul y2 x1)))) y0) \/ (exists y0 : nat, (fun y1 : nat => (forall y2 : nat, ~ (x0 = (Nat.mul x1 y2))) /\ (x0 = (Nat.mul y1 x1))) y0)).
Definition term193 (x0 : nat) := @eq Prop ((exists y0 : nat, exists y1 : nat, (y0 = (Nat.mul x0 y1)) /\ (forall y2 : nat, ~ (y0 = (Nat.mul y2 x0)))) \/ (exists y0 : nat, exists y1 : nat, (forall y2 : nat, ~ (y0 = (Nat.mul x0 y2))) /\ (y0 = (Nat.mul y1 x0)))).
Definition term192 (x0 : nat) := @eq Prop ((exists y0 : nat, (fun y1 : nat => exists y2 : nat, (y1 = (Nat.mul x0 y2)) /\ (forall y3 : nat, ~ (y1 = (Nat.mul y3 x0)))) y0) \/ (exists y0 : nat, (fun y1 : nat => exists y2 : nat, (forall y3 : nat, ~ (y1 = (Nat.mul x0 y3))) /\ (y1 = (Nat.mul y2 x0))) y0)).
Definition term175 := @eq Prop ((exists y0 : nat, exists y1 : nat, exists y2 : nat, (y1 = (Nat.mul y0 y2)) /\ (forall y3 : nat, ~ (y1 = (Nat.mul y3 y0)))) \/ (exists y0 : nat, exists y1 : nat, exists y2 : nat, (forall y3 : nat, ~ (y1 = (Nat.mul y0 y3))) /\ (y1 = (Nat.mul y2 y0)))).
Definition term174 := @eq Prop ((exists y0 : nat, (fun y1 : nat => exists y2 : nat, exists y3 : nat, (y2 = (Nat.mul y1 y3)) /\ (forall y4 : nat, ~ (y2 = (Nat.mul y4 y1)))) y0) \/ (exists y0 : nat, (fun y1 : nat => exists y2 : nat, exists y3 : nat, (forall y4 : nat, ~ (y2 = (Nat.mul y1 y4))) /\ (y2 = (Nat.mul y3 y1))) y0)).
