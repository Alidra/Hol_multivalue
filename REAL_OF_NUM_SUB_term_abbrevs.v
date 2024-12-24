Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term111 (x0 : nat) (x1 : nat) := ~ ((real_add (real_add (real_of_num x1) (real_neg (real_of_num x1))) (real_of_num x0)) = (real_add (real_of_num x0) (real_add (real_of_num x1) (real_neg (real_of_num x1))))).
Definition term20 (x0 : real) (x1 : real) := real_add x0 (real_neg x1).
Definition term176 := (~ False) -> False.
Definition term75 := imp (forall y0 : real, forall y1 : real, (real_add y0 y1) = (real_add y1 y0)).
Definition term70 (x0 : nat) (x1 : nat) := (((~ ((real_add (real_of_num x1) (real_add (real_of_num x0) (real_neg (real_of_num x0)))) = (real_of_num x1))) -> (forall y0 : real, (real_add (real_of_num (NUMERAL 0)) y0) = y0) -> (forall y0 : real, forall y1 : real, (real_add y0 y1) = (real_add y1 y0)) -> (forall y0 : real, (real_add (real_neg y0) y0) = (real_of_num (NUMERAL 0))) -> False) -> (~ ((real_add (real_of_num x1) (real_add (real_of_num x0) (real_neg (real_of_num x0)))) = (real_of_num x1))) -> (forall y0 : real, (real_add (real_of_num (NUMERAL 0)) y0) = y0) -> (forall y0 : real, forall y1 : real, (real_add y0 y1) = (real_add y1 y0)) -> (forall y0 : real, (real_add (real_neg y0) y0) = (real_of_num (NUMERAL 0))) -> False) -> (~ ((real_add (real_of_num x1) (real_add (real_of_num x0) (real_neg (real_of_num x0)))) = (real_of_num x1))) -> (forall y0 : real, (real_add (real_of_num (NUMERAL 0)) y0) = y0) -> (forall y0 : real, forall y1 : real, (real_add y0 y1) = (real_add y1 y0)) -> (forall y0 : real, (real_add (real_neg y0) y0) = (real_of_num (NUMERAL 0))) -> False.
Definition term60 (x0 : nat) (x1 : nat) := @eq real (real_sub (real_add (real_of_num x0) (real_of_num x1)) (real_of_num x1)).
Definition term58 (x0 : nat) (x1 : nat) := @eq real (real_sub (real_add (real_of_num x1) (real_of_num x0)) (real_of_num x1)).
Definition term174 (x0 : nat) (x1 : nat) := (~ ((real_add (real_of_num x1) (real_add (real_of_num x0) (real_neg (real_of_num x0)))) = (real_of_num x1))) -> (real_add (real_of_num x1) (real_add (real_of_num x0) (real_neg (real_of_num x0)))) = (real_of_num x1).
Definition term51 (x0 : nat) (x1 : nat) := real_sub (real_of_num (Nat.add x0 x1)).
Definition term61 (x0 : nat) (x1 : nat) := real_add (real_add (real_of_num x0) (real_of_num x1)) (real_neg (real_of_num x1)).
Definition term63 (x0 : nat) := real_neg (real_of_num x0).
Definition term134 (x0 : Prop) := ~ (~ x0).
Definition term92 := real_of_num (NUMERAL 0).
Definition term164 (x0 : nat) (x1 : nat) := (~ ((real_add (real_of_num (NUMERAL 0)) (real_of_num x1)) = (real_add (real_add (real_of_num x0) (real_neg (real_of_num x0))) (real_of_num x1)))) -> (real_add (real_of_num (NUMERAL 0)) (real_of_num x1)) = (real_add (real_add (real_of_num x0) (real_neg (real_of_num x0))) (real_of_num x1)).
Definition term173 (x0 : nat) (x1 : nat) := (((real_add (real_add (real_of_num x0) (real_neg (real_of_num x0))) (real_of_num x1)) = (real_add (real_of_num x1) (real_add (real_of_num x0) (real_neg (real_of_num x0))))) /\ ((real_add (real_add (real_of_num x0) (real_neg (real_of_num x0))) (real_of_num x1)) = (real_of_num x1))) -> (real_add (real_of_num x1) (real_add (real_of_num x0) (real_neg (real_of_num x0)))) = (real_of_num x1).
Definition term156 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (~ (x0 = x1))) /\ (~ (~ (x2 = x3))).
Definition term133 (x0 : real) (x1 : real) (x2 : real) := (~ (~ (x1 = x0))) /\ (~ (~ (x1 = x2))).
Definition term179 (x0 : nat) (x1 : nat) := fun y0 : nat => x0 = (Nat.add x1 y0).
Definition term152 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := @eq Prop (((real_add x0 x2) = (real_add x1 x3)) \/ ((~ (x0 = x1)) \/ (~ (x2 = x3)))).
Definition term26 (x0 : nat) := fun y0 : nat => (real_add (real_of_num x0) (real_of_num y0)) = (real_of_num (Nat.add x0 y0)).
Definition term117 (x0 : nat) := ~ ((real_add (real_neg (real_of_num x0)) (real_of_num x0)) = (real_add (real_of_num x0) (real_neg (real_of_num x0)))).
Definition term74 := forall y0 : real, (real_add (real_neg y0) y0) = (real_of_num (NUMERAL 0)).
Definition term43 (x0 : nat) (x1 : nat) := real_of_num (Nat.sub x0 x1).
Definition term175 (x0 : nat) (x1 : nat) := ((real_add (real_of_num x1) (real_add (real_of_num x0) (real_neg (real_of_num x0)))) = (real_of_num x1)) -> False.
Definition term146 (x0 : nat) := (~ ((real_of_num x0) = (real_of_num x0))) -> (real_of_num x0) = (real_of_num x0).
Definition term65 (x0 : Prop) := (~ x0) -> False.
Definition term158 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := imp (~ ((~ (x0 = x1)) \/ (~ (x2 = x3)))).
Definition term139 (x0 : real) (x1 : real) (x2 : real) := imp (~ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term73 := ~ (forall y0 : real, (real_add (real_neg y0) y0) = (real_of_num (NUMERAL 0))).
Definition term24 (x0 : nat) (x1 : nat) := real_add (real_of_num x0) (real_of_num x1).
Definition term22 (x0 : real) := forall y0 : real, (real_add x0 y0) = (real_add y0 x0).
Definition term109 (x0 : nat) := real_add (real_of_num x0) (real_neg (real_of_num x0)).
Definition term23 (x0 : real) (x1 : real) := (fun y0 : real => (real_add x0 y0) = (real_add y0 x0)) x1.
Definition term37 (x0 : nat) := forall y0 : nat, (Peano.le x0 y0) = (exists y1 : nat, y0 = (Nat.add x0 y1)).
Definition term59 (x0 : nat) (x1 : nat) := real_sub (real_add (real_of_num x0) (real_of_num x1)) (real_of_num x1).
Definition term127 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term57 (x0 : nat) (x1 : nat) := real_sub (real_add (real_of_num x1) (real_of_num x0)) (real_of_num x1).
Definition term94 (x0 : real) := fun y0 : real => (real_add x0 y0) = (real_add y0 x0).
Definition term40 (x0 : nat) (x1 : nat) := imp (Peano.le x0 x1).
Definition term112 (x0 : Prop) := (~ x0) -> x0.
Definition term66 (x0 : nat) (x1 : nat) := (~ ((real_add (real_of_num x1) (real_add (real_of_num x0) (real_neg (real_of_num x0)))) = (real_of_num x1))) -> False.
Definition term159 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := imp ((x0 = x1) /\ (x2 = x3)).
Definition term45 (x0 : nat) (x1 : nat) := (exists y0 : nat, x0 = (Nat.add x1 y0)) -> (real_sub (real_of_num x0) (real_of_num x1)) = (real_of_num (Nat.sub x0 x1)).
Definition term129 (x0 : real) (x1 : real) (x2 : real) := (~ (x1 = x0)) \/ (~ (x1 = x2)).
Definition term131 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term105 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (x0 = x2) -> (~ (x1 = x3)) \/ ((real_add x0 x1) = (real_add x2 x3)).
Definition term44 (x0 : nat) (x1 : nat) := (Peano.le x1 x0) -> (real_sub (real_of_num x0) (real_of_num x1)) = (real_of_num (Nat.sub x0 x1)).
Definition term46 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.sub (Nat.add y0 y1) y0) = y1) x0.
Definition term125 (x0 : real) (x1 : real) (x2 : real) := @eq Prop ((~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2))).
Definition term96 := forall y0 : real, forall y1 : real, (real_add y0 y1) = (real_add y1 y0).
Definition term13 := forall y0 : real, forall y1 : real, forall y2 : real, (real_add (real_add y0 y1) y2) = (real_add y0 (real_add y1 y2)).
Definition term12 := forall y0 : real, forall y1 : real, forall y2 : real, (real_add y0 (real_add y1 y2)) = (real_add (real_add y0 y1) y2).
Definition term9 (x0 : real) := forall y0 : real, forall y1 : real, (real_add (real_add x0 y0) y1) = (real_add x0 (real_add y0 y1)).
Definition term8 (x0 : real) := forall y0 : real, forall y1 : real, (real_add x0 (real_add y0 y1)) = (real_add (real_add x0 y0) y1).
Definition term41 (x0 : nat) (x1 : nat) := imp (exists y0 : nat, x0 = (Nat.add x1 y0)).
Definition term126 (x0 : real) (x1 : real) (x2 : real) := @eq Prop ((x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term169 (x0 : nat) (x1 : nat) := (((real_add (real_of_num (NUMERAL 0)) (real_of_num x1)) = (real_add (real_add (real_of_num x0) (real_neg (real_of_num x0))) (real_of_num x1))) /\ ((real_add (real_of_num (NUMERAL 0)) (real_of_num x1)) = (real_of_num x1))) -> (real_add (real_add (real_of_num x0) (real_neg (real_of_num x0))) (real_of_num x1)) = (real_of_num x1).
Definition term161 (x0 : nat) (x1 : nat) := ((real_of_num (NUMERAL 0)) = (real_add (real_of_num x0) (real_neg (real_of_num x0)))) /\ ((real_of_num x1) = (real_of_num x1)).
Definition term76 := (forall y0 : real, forall y1 : real, (real_add y0 y1) = (real_add y1 y0)) -> (forall y0 : real, (real_add (real_neg y0) y0) = (real_of_num (NUMERAL 0))) -> False.
Definition term153 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ ((~ (x0 = x2)) \/ (~ (x1 = x3)))) -> (real_add x0 x1) = (real_add x2 x3).
Definition term114 (x0 : nat) := (~ ((real_add (real_neg (real_of_num x0)) (real_of_num x0)) = (real_of_num (NUMERAL 0)))) -> (real_add (real_neg (real_of_num x0)) (real_of_num x0)) = (real_of_num (NUMERAL 0)).
Definition term83 (x0 : nat) := fun y0 : nat => (~ ((real_add (real_of_num x0) (real_add (real_of_num y0) (real_neg (real_of_num y0)))) = (real_of_num x0))) -> (forall y1 : real, (real_add (real_of_num (NUMERAL 0)) y1) = y1) -> (forall y1 : real, forall y2 : real, (real_add y1 y2) = (real_add y2 y1)) -> (forall y1 : real, (real_add (real_neg y1) y1) = (real_of_num (NUMERAL 0))) -> False.
Definition term115 (x0 : nat) := ~ ((real_add (real_neg (real_of_num x0)) (real_of_num x0)) = (real_of_num (NUMERAL 0))).
Definition term123 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term170 (x0 : nat) (x1 : nat) := (~ ((real_add (real_add (real_of_num x0) (real_neg (real_of_num x0))) (real_of_num x1)) = (real_of_num x1))) -> (real_add (real_add (real_of_num x0) (real_neg (real_of_num x0))) (real_of_num x1)) = (real_of_num x1).
Definition term143 (x0 : nat) := (((real_add (real_neg (real_of_num x0)) (real_of_num x0)) = (real_of_num (NUMERAL 0))) /\ ((real_add (real_neg (real_of_num x0)) (real_of_num x0)) = (real_add (real_of_num x0) (real_neg (real_of_num x0))))) -> (real_of_num (NUMERAL 0)) = (real_add (real_of_num x0) (real_neg (real_of_num x0))).
Definition term150 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ((real_add x0 x2) = (real_add x1 x3)) \/ ((~ (x0 = x1)) \/ (~ (x2 = x3))).
Definition term42 (x0 : nat) (x1 : nat) := real_sub (real_of_num x0) (real_of_num x1).
Definition term53 (x0 : nat) (x1 : nat) := @eq real (real_sub (real_of_num x0) (real_of_num x1)).
Definition term5 (x0 : real) (x1 : real) := forall y0 : real, (real_add (real_add x0 x1) y0) = (real_add x0 (real_add x1 y0)).
Definition term64 (x0 : nat) (x1 : nat) := @eq real (real_add (real_of_num x0) (real_add (real_of_num x1) (real_neg (real_of_num x1)))).
Definition term52 (x0 : nat) (x1 : nat) := real_sub (real_of_num (Nat.add x1 x0)) (real_of_num x1).
Definition term171 (x0 : nat) (x1 : nat) := ~ ((real_add (real_add (real_of_num x0) (real_neg (real_of_num x0))) (real_of_num x1)) = (real_of_num x1)).
Definition term107 (x0 : real) (x1 : real) (x2 : real) := (~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2)).
Definition term82 (x0 : nat) (x1 : nat) := (~ ((real_add (real_of_num x1) (real_add (real_of_num x0) (real_neg (real_of_num x0)))) = (real_of_num x1))) -> (forall y0 : real, (real_add (real_of_num (NUMERAL 0)) y0) = y0) -> (forall y0 : real, forall y1 : real, (real_add y0 y1) = (real_add y1 y0)) -> ~ (forall y0 : real, (real_add (real_neg y0) y0) = (real_of_num (NUMERAL 0))).
Definition term100 (x0 : real) := (fun y0 : real => (real_add (real_of_num (NUMERAL 0)) y0) = y0) x0.
Definition term35 (x0 : nat) (x1 : nat) := (fun y0 : nat => (real_of_num (Nat.add x0 y0)) = (real_add (real_of_num x0) (real_of_num y0))) x1.
Definition term7 (x0 : real) := fun y0 : real => forall y1 : real, (real_add (real_add x0 y0) y1) = (real_add x0 (real_add y0 y1)).
Definition term2 (x0 : real) (x1 : real) := fun y0 : real => (real_add x0 (real_add x1 y0)) = (real_add (real_add x0 x1) y0).
Definition term113 (x0 : nat) := real_add (real_neg (real_of_num x0)) (real_of_num x0).
Definition term86 (x0 : nat) := forall y0 : nat, (~ ((real_add (real_of_num x0) (real_add (real_of_num y0) (real_neg (real_of_num y0)))) = (real_of_num x0))) -> (forall y1 : real, (real_add (real_of_num (NUMERAL 0)) y1) = y1) -> (forall y1 : real, forall y2 : real, (real_add y1 y2) = (real_add y2 y1)) -> ~ (forall y1 : real, (real_add (real_neg y1) y1) = (real_of_num (NUMERAL 0))).
Definition term85 (x0 : nat) := forall y0 : nat, (~ ((real_add (real_of_num x0) (real_add (real_of_num y0) (real_neg (real_of_num y0)))) = (real_of_num x0))) -> (forall y1 : real, (real_add (real_of_num (NUMERAL 0)) y1) = y1) -> (forall y1 : real, forall y2 : real, (real_add y1 y2) = (real_add y2 y1)) -> (forall y1 : real, (real_add (real_neg y1) y1) = (real_of_num (NUMERAL 0))) -> False.
Definition term120 (x0 : real) (x1 : real) := ~ (x0 = x1).
Definition term71 (x0 : nat) (x1 : nat) := (((~ ((real_add (real_of_num x1) (real_add (real_of_num x0) (real_neg (real_of_num x0)))) = (real_of_num x1))) -> (forall y0 : real, (real_add (real_of_num (NUMERAL 0)) y0) = y0) -> (forall y0 : real, forall y1 : real, (real_add y0 y1) = (real_add y1 y0)) -> (forall y0 : real, (real_add (real_neg y0) y0) = (real_of_num (NUMERAL 0))) -> False) -> (~ ((real_add (real_of_num x1) (real_add (real_of_num x0) (real_neg (real_of_num x0)))) = (real_of_num x1))) -> (forall y0 : real, (real_add (real_of_num (NUMERAL 0)) y0) = y0) -> (forall y0 : real, forall y1 : real, (real_add y0 y1) = (real_add y1 y0)) -> (forall y0 : real, (real_add (real_neg y0) y0) = (real_of_num (NUMERAL 0))) -> False) -> ((~ ((real_add (real_of_num x1) (real_add (real_of_num x0) (real_neg (real_of_num x0)))) = (real_of_num x1))) -> (forall y0 : real, (real_add (real_of_num (NUMERAL 0)) y0) = y0) -> (forall y0 : real, forall y1 : real, (real_add y0 y1) = (real_add y1 y0)) -> (forall y0 : real, (real_add (real_neg y0) y0) = (real_of_num (NUMERAL 0))) -> False) -> (~ ((real_add (real_of_num x1) (real_add (real_of_num x0) (real_neg (real_of_num x0)))) = (real_of_num x1))) -> (forall y0 : real, (real_add (real_of_num (NUMERAL 0)) y0) = y0) -> (forall y0 : real, forall y1 : real, (real_add y0 y1) = (real_add y1 y0)) -> (forall y0 : real, (real_add (real_neg y0) y0) = (real_of_num (NUMERAL 0))) -> False.
Definition term91 (x0 : real) := real_add (real_neg x0) x0.
Definition term4 (x0 : real) (x1 : real) := forall y0 : real, (real_add x0 (real_add x1 y0)) = (real_add (real_add x0 x1) y0).
Definition term39 (x0 : nat) (x1 : nat) := exists y0 : nat, x0 = (Nat.add x1 y0).
Definition term119 (x0 : real) (x1 : real) (x2 : real) := (x0 = x2) \/ (~ (x1 = x2)).
Definition term49 (x0 : nat) (x1 : nat) := Nat.sub (Nat.add x1 x0) x1.
Definition term130 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term181 := forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> (real_sub (real_of_num y1) (real_of_num y0)) = (real_of_num (Nat.sub y1 y0)).
Definition term90 := forall y0 : nat, forall y1 : nat, (~ ((real_add (real_of_num y0) (real_add (real_of_num y1) (real_neg (real_of_num y1)))) = (real_of_num y0))) -> (forall y2 : real, (real_add (real_of_num (NUMERAL 0)) y2) = y2) -> (forall y2 : real, forall y3 : real, (real_add y2 y3) = (real_add y3 y2)) -> ~ (forall y2 : real, (real_add (real_neg y2) y2) = (real_of_num (NUMERAL 0))).
Definition term89 := forall y0 : nat, forall y1 : nat, (~ ((real_add (real_of_num y0) (real_add (real_of_num y1) (real_neg (real_of_num y1)))) = (real_of_num y0))) -> (forall y2 : real, (real_add (real_of_num (NUMERAL 0)) y2) = y2) -> (forall y2 : real, forall y3 : real, (real_add y2 y3) = (real_add y3 y2)) -> (forall y2 : real, (real_add (real_neg y2) y2) = (real_of_num (NUMERAL 0))) -> False.
Definition term33 := forall y0 : nat, forall y1 : nat, (real_of_num (Nat.add y0 y1)) = (real_add (real_of_num y0) (real_of_num y1)).
Definition term32 := forall y0 : nat, forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1)).
Definition term99 := forall y0 : real, (real_add (real_of_num (NUMERAL 0)) y0) = y0.
Definition term144 (x0 : nat) := (~ ((real_of_num (NUMERAL 0)) = (real_add (real_of_num x0) (real_neg (real_of_num x0))))) -> (real_of_num (NUMERAL 0)) = (real_add (real_of_num x0) (real_neg (real_of_num x0))).
Definition term151 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := @eq Prop ((~ (x0 = x2)) \/ ((~ (x1 = x3)) \/ ((real_add x0 x1) = (real_add x2 x3)))).
Definition term29 (x0 : nat) := forall y0 : nat, (real_of_num (Nat.add x0 y0)) = (real_add (real_of_num x0) (real_of_num y0)).
Definition term93 := fun y0 : real => (real_add (real_neg y0) y0) = (real_of_num (NUMERAL 0)).
Definition term172 (x0 : nat) (x1 : nat) := ((real_add (real_add (real_of_num x0) (real_neg (real_of_num x0))) (real_of_num x1)) = (real_add (real_of_num x1) (real_add (real_of_num x0) (real_neg (real_of_num x0))))) /\ ((real_add (real_add (real_of_num x0) (real_neg (real_of_num x0))) (real_of_num x1)) = (real_of_num x1)).
Definition term95 := fun y0 : real => forall y1 : real, (real_add y0 y1) = (real_add y1 y0).
Definition term6 (x0 : real) := fun y0 : real => forall y1 : real, (real_add x0 (real_add y0 y1)) = (real_add (real_add x0 y0) y1).
Definition term16 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => (real_add (real_add x0 x1) y0) = (real_add x0 (real_add x1 y0))) x2.
Definition term72 := (forall y0 : real, (real_add (real_neg y0) y0) = (real_of_num (NUMERAL 0))) -> False.
Definition term165 (x0 : nat) (x1 : nat) := ~ ((real_add (real_of_num (NUMERAL 0)) (real_of_num x1)) = (real_add (real_add (real_of_num x0) (real_neg (real_of_num x0))) (real_of_num x1))).
Definition term47 (x0 : nat) := forall y0 : nat, (Nat.sub (Nat.add x0 y0) x0) = y0.
Definition term102 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (x1 = x3) -> (real_add x0 x1) = (real_add x2 x3).
Definition term21 (x0 : real) := (fun y0 : real => forall y1 : real, (real_add y0 y1) = (real_add y1 y0)) x0.
Definition term17 (x0 : real) := (fun y0 : real => forall y1 : real, (real_sub y0 y1) = (real_add y0 (real_neg y1))) x0.
Definition term166 (x0 : nat) := (~ ((real_add (real_of_num (NUMERAL 0)) (real_of_num x0)) = (real_of_num x0))) -> (real_add (real_of_num (NUMERAL 0)) (real_of_num x0)) = (real_of_num x0).
Definition term138 (x0 : real) (x1 : real) (x2 : real) := (x1 = x0) /\ (x1 = x2).
Definition term101 (x0 : real) := (fun y0 : real => (real_add (real_neg y0) y0) = (real_of_num (NUMERAL 0))) x0.
Definition term124 (x0 : real) (x1 : real) (x2 : real) := (x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term122 (x0 : real) (x1 : real) (x2 : real) := (~ (x1 = x0)) \/ ((x0 = x2) \/ (~ (x1 = x2))).
Definition term168 (x0 : nat) (x1 : nat) := ((real_add (real_of_num (NUMERAL 0)) (real_of_num x1)) = (real_add (real_add (real_of_num x0) (real_neg (real_of_num x0))) (real_of_num x1))) /\ ((real_add (real_of_num (NUMERAL 0)) (real_of_num x1)) = (real_of_num x1)).
Definition term18 (x0 : real) := forall y0 : real, (real_sub x0 y0) = (real_add x0 (real_neg y0)).
Definition term15 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, (real_add (real_add x0 y0) y1) = (real_add x0 (real_add y0 y1))) x1.
Definition term136 (x0 : real) (x1 : real) := and (~ (~ (x0 = x1))).
Definition term79 := (forall y0 : real, (real_add (real_of_num (NUMERAL 0)) y0) = y0) -> (forall y0 : real, forall y1 : real, (real_add y0 y1) = (real_add y1 y0)) -> (forall y0 : real, (real_add (real_neg y0) y0) = (real_of_num (NUMERAL 0))) -> False.
Definition term69 (x0 : nat) (x1 : nat) := ((~ ((real_add (real_of_num x1) (real_add (real_of_num x0) (real_neg (real_of_num x0)))) = (real_of_num x1))) -> (forall y0 : real, (real_add (real_of_num (NUMERAL 0)) y0) = y0) -> (forall y0 : real, forall y1 : real, (real_add y0 y1) = (real_add y1 y0)) -> (forall y0 : real, (real_add (real_neg y0) y0) = (real_of_num (NUMERAL 0))) -> False) -> (~ ((real_add (real_of_num x1) (real_add (real_of_num x0) (real_neg (real_of_num x0)))) = (real_of_num x1))) -> (forall y0 : real, (real_add (real_of_num (NUMERAL 0)) y0) = y0) -> (forall y0 : real, forall y1 : real, (real_add y0 y1) = (real_add y1 y0)) -> (forall y0 : real, (real_add (real_neg y0) y0) = (real_of_num (NUMERAL 0))) -> False.
Definition term78 := imp (forall y0 : real, (real_add (real_of_num (NUMERAL 0)) y0) = y0).
Definition term19 (x0 : real) (x1 : real) := (fun y0 : real => (real_sub x0 y0) = (real_add x0 (real_neg y0))) x1.
Definition term0 (x0 : real) (x1 : real) (x2 : real) := real_add x0 (real_add x1 x2).
Definition term50 (x0 : nat) := real_sub (real_of_num x0).
Definition term160 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ((x0 = x2) /\ (x1 = x3)) -> (real_add x0 x1) = (real_add x2 x3).
Definition term55 (x0 : nat) (x1 : nat) := Nat.sub (Nat.add x0 x1).
Definition term149 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (x0 = x1)) \/ (((real_add x0 x2) = (real_add x1 x3)) \/ (~ (x2 = x3))).
Definition term56 (x0 : nat) (x1 : nat) := real_sub (real_add (real_of_num x0) (real_of_num x1)).
Definition term142 (x0 : nat) := ((real_add (real_neg (real_of_num x0)) (real_of_num x0)) = (real_of_num (NUMERAL 0))) /\ ((real_add (real_neg (real_of_num x0)) (real_of_num x0)) = (real_add (real_of_num x0) (real_neg (real_of_num x0)))).
Definition term62 (x0 : nat) (x1 : nat) := real_add (real_of_num x0) (real_add (real_of_num x1) (real_neg (real_of_num x1))).
Definition term177 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ ((real_add (real_of_num y0) (real_add (real_of_num y1) (real_neg (real_of_num y1)))) = (real_of_num y0))) -> (forall y2 : real, (real_add (real_of_num (NUMERAL 0)) y2) = y2) -> (forall y2 : real, forall y3 : real, (real_add y2 y3) = (real_add y3 y2)) -> (forall y2 : real, (real_add (real_neg y2) y2) = (real_of_num (NUMERAL 0))) -> False) x0.
Definition term36 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) = (exists y2 : nat, y1 = (Nat.add y0 y2))) x0.
Definition term34 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (real_of_num (Nat.add y0 y1)) = (real_add (real_of_num y0) (real_of_num y1))) x0.
Definition term11 := fun y0 : real => forall y1 : real, forall y2 : real, (real_add (real_add y0 y1) y2) = (real_add y0 (real_add y1 y2)).
Definition term10 := fun y0 : real => forall y1 : real, forall y2 : real, (real_add y0 (real_add y1 y2)) = (real_add (real_add y0 y1) y2).
Definition term162 (x0 : nat) (x1 : nat) := (((real_of_num (NUMERAL 0)) = (real_add (real_of_num x0) (real_neg (real_of_num x0)))) /\ ((real_of_num x1) = (real_of_num x1))) -> (real_add (real_of_num (NUMERAL 0)) (real_of_num x1)) = (real_add (real_add (real_of_num x0) (real_neg (real_of_num x0))) (real_of_num x1)).
Definition term148 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ((real_add x0 x2) = (real_add x1 x3)) \/ (~ (x2 = x3)).
Definition term147 (x0 : nat) := ~ ((real_of_num x0) = (real_of_num x0)).
Definition term67 (x0 : nat) (x1 : nat) := ~ ((real_add (real_of_num x1) (real_add (real_of_num x0) (real_neg (real_of_num x0)))) = (real_of_num x1)).
Definition term178 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ ((real_add (real_of_num x0) (real_add (real_of_num y0) (real_neg (real_of_num y0)))) = (real_of_num x0))) -> (forall y1 : real, (real_add (real_of_num (NUMERAL 0)) y1) = y1) -> (forall y1 : real, forall y2 : real, (real_add y1 y2) = (real_add y2 y1)) -> (forall y1 : real, (real_add (real_neg y1) y1) = (real_of_num (NUMERAL 0))) -> False) x1.
Definition term116 (x0 : nat) := (~ ((real_add (real_neg (real_of_num x0)) (real_of_num x0)) = (real_add (real_of_num x0) (real_neg (real_of_num x0))))) -> (real_add (real_neg (real_of_num x0)) (real_of_num x0)) = (real_add (real_of_num x0) (real_neg (real_of_num x0))).
Definition term3 (x0 : real) (x1 : real) := fun y0 : real => (real_add (real_add x0 x1) y0) = (real_add x0 (real_add x1 y0)).
Definition term157 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (x0 = x1) /\ (x2 = x3).
Definition term97 (x0 : real) := real_add (real_of_num (NUMERAL 0)) x0.
Definition term141 (x0 : real) (x1 : real) (x2 : real) := ((x0 = x1) /\ (x0 = x2)) -> x1 = x2.
Definition term155 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ~ ((~ (x0 = x1)) \/ (~ (x2 = x3))).
Definition term132 (x0 : real) (x1 : real) (x2 : real) := ~ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term28 (x0 : nat) := forall y0 : nat, (real_add (real_of_num x0) (real_of_num y0)) = (real_of_num (Nat.add x0 y0)).
Definition term128 (x0 : real) (x1 : real) (x2 : real) := (~ ((~ (x0 = x1)) \/ (~ (x0 = x2)))) -> x1 = x2.
Definition term145 (x0 : nat) := ~ ((real_of_num (NUMERAL 0)) = (real_add (real_of_num x0) (real_neg (real_of_num x0)))).
Definition term137 (x0 : real) (x1 : real) := and (x0 = x1).
Definition term48 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.sub (Nat.add x0 y0) x0) = y0) x1.
Definition term77 := (forall y0 : real, forall y1 : real, (real_add y0 y1) = (real_add y1 y0)) -> ~ (forall y0 : real, (real_add (real_neg y0) y0) = (real_of_num (NUMERAL 0))).
Definition term103 (x0 : Prop) (x1 : Prop) := (~ x0) \/ x1.
Definition term154 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (x0 = x1)) \/ (~ (x2 = x3)).
Definition term180 (x0 : nat) := forall y0 : nat, (Peano.le x0 y0) -> (real_sub (real_of_num y0) (real_of_num x0)) = (real_of_num (Nat.sub y0 x0)).
Definition term68 (x0 : nat) (x1 : nat) := (~ ((real_add (real_of_num x1) (real_add (real_of_num x0) (real_neg (real_of_num x0)))) = (real_of_num x1))) -> (forall y0 : real, (real_add (real_of_num (NUMERAL 0)) y0) = y0) -> (forall y0 : real, forall y1 : real, (real_add y0 y1) = (real_add y1 y0)) -> (forall y0 : real, (real_add (real_neg y0) y0) = (real_of_num (NUMERAL 0))) -> False.
Definition term167 (x0 : nat) := ~ ((real_add (real_of_num (NUMERAL 0)) (real_of_num x0)) = (real_of_num x0)).
Definition term106 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (x0 = x2)) \/ ((~ (x1 = x3)) \/ ((real_add x0 x1) = (real_add x2 x3))).
Definition term54 (x0 : nat) (x1 : nat) := @eq real (real_sub (real_of_num (Nat.add x1 x0)) (real_of_num x1)).
Definition term30 := fun y0 : nat => forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1)).
Definition term80 := (forall y0 : real, (real_add (real_of_num (NUMERAL 0)) y0) = y0) -> (forall y0 : real, forall y1 : real, (real_add y0 y1) = (real_add y1 y0)) -> ~ (forall y0 : real, (real_add (real_neg y0) y0) = (real_of_num (NUMERAL 0))).
Definition term140 (x0 : real) (x1 : real) (x2 : real) := imp ((x1 = x0) /\ (x1 = x2)).
Definition term104 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (x1 = x3)) \/ ((real_add x0 x1) = (real_add x2 x3)).
Definition term163 (x0 : nat) := real_add (real_of_num (NUMERAL 0)) (real_of_num x0).
Definition term118 (x0 : real) (x1 : real) (x2 : real) := (~ (x0 = x2)) \/ (x1 = x2).
Definition term108 (x0 : nat) (x1 : nat) := real_add (real_add (real_of_num x0) (real_neg (real_of_num x0))) (real_of_num x1).
Definition term135 (x0 : real) (x1 : real) := ~ (~ (x0 = x1)).
Definition term1 (x0 : real) (x1 : real) (x2 : real) := real_add (real_add x0 x1) x2.
Definition term38 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le x0 y0) = (exists y1 : nat, y0 = (Nat.add x0 y1))) x1.
Definition term121 (x0 : real) (x1 : real) := or (~ (x0 = x1)).
Definition term27 (x0 : nat) := fun y0 : nat => (real_of_num (Nat.add x0 y0)) = (real_add (real_of_num x0) (real_of_num y0)).
Definition term25 (x0 : nat) (x1 : nat) := real_of_num (Nat.add x0 x1).
Definition term14 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, (real_add (real_add y0 y1) y2) = (real_add y0 (real_add y1 y2))) x0.
Definition term88 := fun y0 : nat => forall y1 : nat, (~ ((real_add (real_of_num y0) (real_add (real_of_num y1) (real_neg (real_of_num y1)))) = (real_of_num y0))) -> (forall y2 : real, (real_add (real_of_num (NUMERAL 0)) y2) = y2) -> (forall y2 : real, forall y3 : real, (real_add y2 y3) = (real_add y3 y2)) -> ~ (forall y2 : real, (real_add (real_neg y2) y2) = (real_of_num (NUMERAL 0))).
Definition term87 := fun y0 : nat => forall y1 : nat, (~ ((real_add (real_of_num y0) (real_add (real_of_num y1) (real_neg (real_of_num y1)))) = (real_of_num y0))) -> (forall y2 : real, (real_add (real_of_num (NUMERAL 0)) y2) = y2) -> (forall y2 : real, forall y3 : real, (real_add y2 y3) = (real_add y3 y2)) -> (forall y2 : real, (real_add (real_neg y2) y2) = (real_of_num (NUMERAL 0))) -> False.
Definition term31 := fun y0 : nat => forall y1 : nat, (real_of_num (Nat.add y0 y1)) = (real_add (real_of_num y0) (real_of_num y1)).
Definition term98 := fun y0 : real => (real_add (real_of_num (NUMERAL 0)) y0) = y0.
Definition term84 (x0 : nat) := fun y0 : nat => (~ ((real_add (real_of_num x0) (real_add (real_of_num y0) (real_neg (real_of_num y0)))) = (real_of_num x0))) -> (forall y1 : real, (real_add (real_of_num (NUMERAL 0)) y1) = y1) -> (forall y1 : real, forall y2 : real, (real_add y1 y2) = (real_add y2 y1)) -> ~ (forall y1 : real, (real_add (real_neg y1) y1) = (real_of_num (NUMERAL 0))).
Definition term110 (x0 : nat) (x1 : nat) := (~ ((real_add (real_add (real_of_num x1) (real_neg (real_of_num x1))) (real_of_num x0)) = (real_add (real_of_num x0) (real_add (real_of_num x1) (real_neg (real_of_num x1)))))) -> (real_add (real_add (real_of_num x1) (real_neg (real_of_num x1))) (real_of_num x0)) = (real_add (real_of_num x0) (real_add (real_of_num x1) (real_neg (real_of_num x1)))).
Definition term81 (x0 : nat) (x1 : nat) := imp (~ ((real_add (real_of_num x1) (real_add (real_of_num x0) (real_neg (real_of_num x0)))) = (real_of_num x1))).
