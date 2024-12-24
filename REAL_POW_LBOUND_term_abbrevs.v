Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term118 (x0 : real) (x1 : real) := real_sub (real_add (real_mul x0 x1) (real_add x1 (real_of_num (NUMERAL (BIT1 0))))).
Definition term112 (x0 : real) (x1 : real) := and (real_ge (real_mul x0 (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL 0))).
Definition term311 (x0 : nat) (x1 : real) := real_mul (real_add (real_of_num x0) (real_of_num (NUMERAL (BIT1 0)))) x1.
Definition term75 (x0 : real) (x1 : real) := real_add (real_add (real_mul x0 x1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 x1))) (real_add (real_add x1 (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))).
Definition term14 (x0 : real) (x1 : real) := real_add (real_mul x0 x1).
Definition term82 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term70 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 x1)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term144 (x0 : real) (x1 : real) := or ((real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_add x0 (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_mul (real_add (real_of_num (NUMERAL (BIT1 0))) x1) (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul x0 x1)))) /\ (~ (real_le (real_of_num (NUMERAL 0)) (real_mul x0 (real_mul x1 x1))))).
Definition term207 (x0 : real) := ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0)))) -> real_gt (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) x0) (real_of_num (NUMERAL 0)).
Definition term265 (x0 : real) (x1 : nat) := (real_le (real_of_num (NUMERAL 0)) x0) -> (fun y0 : nat => real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num y0) x0)) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x0) y0)) x1.
Definition term45 := Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0))).
Definition term347 (x0 : nat) (x1 : real) := ((real_le (real_of_num (NUMERAL 0)) (real_of_num x0)) /\ (real_le (real_of_num (NUMERAL 0)) (real_mul x1 x1))) -> (real_le (real_of_num (NUMERAL 0)) (real_mul (real_of_num x0) (real_mul x1 x1))) = True.
Definition term326 (x0 : real) (x1 : nat) := ((real_le (real_of_num (NUMERAL 0)) (real_add (real_of_num (NUMERAL (BIT1 0))) x0)) /\ (real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num x1) x0)) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x0) x1))) -> (real_le (real_mul (real_add (real_of_num (NUMERAL (BIT1 0))) x0) (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num x1) x0))) (real_mul (real_add (real_of_num (NUMERAL (BIT1 0))) x0) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x0) x1))) = True.
Definition term131 (x0 : real) (x1 : real) := real_ge (real_sub (real_mul x0 (real_mul x1 x1)) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term197 (x0 : real) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0))).
Definition term337 (x0 : nat) := (fun y0 : nat => real_le (real_of_num (NUMERAL 0)) (real_of_num y0)) x0.
Definition term352 (x0 : nat) (x1 : real) := (real_le (real_of_num (NUMERAL 0)) (real_of_num x0)) /\ (real_le (real_of_num (NUMERAL 0)) (real_mul x1 x1)).
Definition term80 := real_of_num (NUMERAL 0).
Definition term51 (x0 : real) (x1 : real) := real_add x1 (real_add (real_mul x0 x1) (real_of_num (NUMERAL (BIT1 0)))).
Definition term303 := real_le (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term48 (x0 : real) (x1 : real) := real_add (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul x0 x1)).
Definition term275 (x0 : real) := (real_le (real_of_num (NUMERAL 0)) x0) -> forall y0 : nat, real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num y0) x0)) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x0) y0).
Definition term56 (x0 : real) (x1 : real) := real_sub (real_add (real_mul x0 (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))) (real_add (real_mul x0 x1) (real_add x1 (real_of_num (NUMERAL (BIT1 0)))))) (real_add (real_mul x0 x1) (real_add x1 (real_of_num (NUMERAL (BIT1 0))))).
Definition term279 (x0 : real) := real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num (NUMERAL 0)) x0)) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x0) (NUMERAL 0)).
Definition term244 (x0 : nat) := (fun y0 : nat => (real_of_num (S y0)) = (real_add (real_of_num y0) (real_of_num (NUMERAL (BIT1 0))))) x0.
Definition term128 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) (real_add (real_add (real_mul x0 x1) (real_add x1 (real_of_num (NUMERAL (BIT1 0))))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 x1)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_neg (real_of_num (NUMERAL (BIT1 0))))))).
Definition term332 (x0 : real) (x1 : nat) := real_le (real_mul (real_add (real_of_num (NUMERAL (BIT1 0))) x0) (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num x1) x0))) (real_mul (real_add (real_of_num (NUMERAL (BIT1 0))) x0) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x0) x1)).
Definition term185 (x0 : real) := ~ (real_le (real_of_num (NUMERAL 0)) (real_add (real_of_num (NUMERAL (BIT1 0))) x0)).
Definition term61 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add x0 (real_of_num (NUMERAL (BIT1 0)))).
Definition term108 (x0 : real) (x1 : real) := real_gt (real_sub (real_of_num (NUMERAL 0)) (real_mul x0 (real_mul x1 x1))).
Definition term57 (x0 : real) (x1 : real) := real_add (real_add (real_mul x0 (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))) (real_add (real_mul x0 x1) (real_add x1 (real_of_num (NUMERAL (BIT1 0)))))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul x0 x1) (real_add x1 (real_of_num (NUMERAL (BIT1 0)))))).
Definition term264 (x0 : real) := imp (real_le (real_of_num (NUMERAL 0)) x0).
Definition term315 (x0 : real) (x1 : nat) := real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_add (real_of_num x1) (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_mul (real_add (real_of_num (NUMERAL (BIT1 0))) x0) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x0) x1)).
Definition term307 (x0 : real) (x1 : nat) := real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num (S x1)) x0)) (real_mul (real_add (real_of_num (NUMERAL (BIT1 0))) x0) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x0) x1)).
Definition term259 (x0 : real) := forall y0 : nat, (real_le (real_of_num (NUMERAL 0)) x0) -> (fun y1 : nat => real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num y1) x0)) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x0) y1)) y0.
Definition term53 (x0 : real) (x1 : real) := real_sub (real_mul (real_add (real_of_num (NUMERAL (BIT1 0))) x1) (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul x0 x1))).
Definition term54 (x0 : real) (x1 : real) := real_sub (real_add (real_mul x0 (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))) (real_add (real_mul x0 x1) (real_add x1 (real_of_num (NUMERAL (BIT1 0)))))).
Definition term17 (x0 : real) (x1 : real) := real_add (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul x0 x1) x1).
Definition term142 (x0 : real) (x1 : real) := (~ (real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_add x0 (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_mul (real_add (real_of_num (NUMERAL (BIT1 0))) x1) (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul x0 x1))))) /\ (real_le (real_of_num (NUMERAL 0)) (real_mul x0 (real_mul x1 x1))).
Definition term169 (x0 : real) (x1 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) (real_mul x0 (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term248 (x0 : real) := forall y0 : nat, (real_pow x0 (S y0)) = (real_mul x0 (real_pow x0 y0)).
Definition term143 (x0 : real) (x1 : real) := (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_mul x0 (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL 0))).
Definition term235 := (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> forall y0 : real, forall y1 : real, (exists y2 : real, (real_le y0 y2) /\ (real_le y2 y1)) -> real_le y0 y1.
Definition term331 (x0 : real) (x1 : nat) := (real_le (real_of_num (NUMERAL 0)) (real_add (real_of_num (NUMERAL (BIT1 0))) x0)) /\ (real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num x1) x0)) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x0) x1)).
Definition term230 (x0 : real) (x1 : real) := exists y0 : real, (real_le x0 y0) /\ (real_le y0 x1).
Definition term325 (x0 : real) (x1 : real) (x2 : real) := ((real_le (real_of_num (NUMERAL 0)) x1) /\ (real_le x0 x2)) -> (real_le (real_mul x1 x0) (real_mul x1 x2)) = True.
Definition term8 (x0 : real) (x1 : real) := real_mul x0 (real_add x1 (real_of_num (NUMERAL (BIT1 0)))).
Definition term218 (x0 : real) := (~ ((real_le (real_of_num (NUMERAL 0)) x0) -> real_le (real_of_num (NUMERAL 0)) (real_add (real_of_num (NUMERAL (BIT1 0))) x0))) -> False.
Definition term173 (x0 : real) (x1 : real) := (~ ((real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_add x0 (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_mul (real_add (real_of_num (NUMERAL (BIT1 0))) x1) (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul x0 x1)))) = (real_le (real_of_num (NUMERAL 0)) (real_mul x0 (real_mul x1 x1))))) -> False.
Definition term293 (x0 : real) := (real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num (NUMERAL 0)) x0)) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x0) (NUMERAL 0))) /\ (forall y0 : nat, (real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num y0) x0)) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x0) y0)) -> real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num (S y0)) x0)) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x0) (S y0))).
Definition term239 (x0 : nat) := real_of_num (S x0).
Definition term125 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 x1)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))).
Definition term168 (x0 : real) (x1 : real) := real_mul (real_of_num (NUMERAL 0)) (real_mul x0 (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))).
Definition term231 (x0 : real) (x1 : real) := fun y0 : real => (real_le x0 y0) /\ (real_le y0 x1).
Definition term134 (x0 : real) (x1 : real) := real_sub (real_mul x0 (real_mul x1 x1)) (real_of_num (NUMERAL 0)).
Definition term199 (x0 : real) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) x0) (real_of_num (NUMERAL 0)).
Definition term215 := real_gt (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term251 (x0 : real) (x1 : nat) := real_mul x0 (real_pow x0 x1).
Definition term273 (x0 : real) := forall y0 : nat, (fun y1 : nat => real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num y1) x0)) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x0) y1)) y0.
Definition term94 (x0 : nat) := real_add (real_of_num x0) (real_neg (real_of_num x0)).
Definition term129 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term349 (x0 : real) := ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le (real_of_num (NUMERAL 0)) x0)) -> (real_le (real_of_num (NUMERAL 0)) (real_mul x0 x0)) = True.
Definition term191 (x0 : real) := real_gt (real_sub (real_of_num (NUMERAL 0)) (real_add (real_of_num (NUMERAL (BIT1 0))) x0)).
Definition term78 (x0 : real) (x1 : real) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 x1).
Definition term292 (x0 : real) := ((fun y0 : nat => real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num y0) x0)) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x0) y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num y1) x0)) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x0) y1)) y0) -> (fun y1 : nat => real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num y1) x0)) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x0) y1)) (S y0)).
Definition term250 (x0 : real) (x1 : nat) := real_pow x0 (S x1).
Definition term328 (x0 : real) (x1 : nat) := real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x0) x1.
Definition term353 (x0 : real) (x1 : nat) := exists y0 : real, (real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_add (real_of_num x1) (real_of_num (NUMERAL (BIT1 0)))) x0)) y0) /\ (real_le y0 (real_mul (real_add (real_of_num (NUMERAL (BIT1 0))) x0) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x0) x1))).
Definition term289 (x0 : real) := fun y0 : nat => (real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num y0) x0)) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x0) y0)) -> real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num (S y0)) x0)) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x0) (S y0)).
Definition term184 (x0 : real) := real_ge x0 (real_of_num (NUMERAL 0)).
Definition term343 (x0 : real) (x1 : real) := (real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le (real_of_num (NUMERAL 0)) x1).
Definition term243 := forall y0 : nat, (real_of_num (S y0)) = (real_add (real_of_num y0) (real_of_num (NUMERAL (BIT1 0)))).
Definition term196 (x0 : real) := (real_ge x0 (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))).
Definition term254 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (forall y1 : a0, x0 -> y0 y1) = (x0 -> forall y1 : a0, y0 y1)) x1.
Definition term249 (x0 : real) (x1 : nat) := (fun y0 : nat => (real_pow x0 (S y0)) = (real_mul x0 (real_pow x0 y0))) x1.
Definition term126 (x0 : real) (x1 : real) := real_add (real_add (real_mul x0 x1) (real_add x1 (real_of_num (NUMERAL (BIT1 0))))).
Definition term345 (x0 : nat) (x1 : real) := real_le (real_of_num (NUMERAL 0)) (real_mul (real_of_num x0) (real_mul x1 x1)).
Definition term157 (x0 : real) (x1 : real) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) (real_of_num (NUMERAL 0))).
Definition term114 (x0 : real) (x1 : real) := (real_ge (real_mul x0 (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) (real_of_num (NUMERAL 0))).
Definition term336 (x0 : nat) (x1 : real) := real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_add (real_of_num x0) (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_mul (real_add (real_of_num (NUMERAL (BIT1 0))) x1) (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num x0) x1))).
Definition term286 (x0 : real) (x1 : nat) := ((fun y0 : nat => real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num y0) x0)) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x0) y0)) x1) -> (fun y0 : nat => real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num y0) x0)) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x0) y0)) (S x1).
Definition term195 (x0 : real) := and (real_ge x0 (real_of_num (NUMERAL 0))).
Definition term217 (x0 : nat) (x1 : nat) := real_gt (real_neg (real_of_num x0)) (real_of_num x1).
Definition term174 (x0 : real) (x1 : real) := ((~ ((real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_add x0 (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_mul (real_add (real_of_num (NUMERAL (BIT1 0))) x1) (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul x0 x1)))) = (real_le (real_of_num (NUMERAL 0)) (real_mul x0 (real_mul x1 x1))))) -> False) -> (real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_add x0 (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_mul (real_add (real_of_num (NUMERAL (BIT1 0))) x1) (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul x0 x1)))) = (real_le (real_of_num (NUMERAL 0)) (real_mul x0 (real_mul x1 x1))).
Definition term66 := real_neg (real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)))).
Definition term324 (x0 : real) (x1 : real) (x2 : real) := real_le (real_mul x1 x0) (real_mul x1 x2).
Definition term182 (x0 : real) := real_add x0 (real_of_num (NUMERAL 0)).
Definition term316 (x0 : real) (x1 : nat) := (exists y0 : real, (real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_add (real_of_num x1) (real_of_num (NUMERAL (BIT1 0)))) x0)) y0) /\ (real_le y0 (real_mul (real_add (real_of_num (NUMERAL (BIT1 0))) x0) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x0) x1)))) -> real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_add (real_of_num x1) (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_mul (real_add (real_of_num (NUMERAL (BIT1 0))) x0) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x0) x1)).
Definition term167 (x0 : real) (x1 : real) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))).
Definition term277 (x0 : real) := (((fun y0 : nat => real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num y0) x0)) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x0) y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num y1) x0)) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x0) y1)) y0) -> (fun y1 : nat => real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num y1) x0)) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x0) y1)) (S y0))) -> forall y0 : nat, (fun y1 : nat => real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num y1) x0)) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x0) y1)) y0.
Definition term281 (x0 : real) := and (real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num (NUMERAL 0)) x0)) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x0) (NUMERAL 0))).
Definition term313 (x0 : nat) (x1 : real) := real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_add (real_of_num x0) (real_of_num (NUMERAL (BIT1 0)))) x1).
Definition term6 (x0 : real) (x1 : real) := real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_add x0 (real_of_num (NUMERAL (BIT1 0)))) x1).
Definition term301 (x0 : real) := real_pow x0 (NUMERAL 0).
Definition term204 (x0 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term85 (x0 : real) (x1 : real) := real_add (real_add (real_mul x0 x1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 x1))).
Definition term113 (x0 : real) (x1 : real) := (real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_add x0 (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_mul (real_add (real_of_num (NUMERAL (BIT1 0))) x1) (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul x0 x1)))) /\ (~ (real_le (real_of_num (NUMERAL 0)) (real_mul x0 (real_mul x1 x1)))).
Definition term276 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term99 (x0 : real) (x1 : real) := real_ge (real_mul x0 (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))).
Definition term214 (x0 : real) := real_gt (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) x0).
Definition term115 (x0 : real) (x1 : real) := ~ (real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_add x0 (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_mul (real_add (real_of_num (NUMERAL (BIT1 0))) x1) (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul x0 x1)))).
Definition term149 := Peano.lt (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term165 (x0 : real) (x1 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) (real_mul x0 (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term137 (x0 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num (NUMERAL 0)).
Definition term356 := forall y0 : real, forall y1 : nat, (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num y1) y0)) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) y0) y1).
Definition term318 (x0 : real) := forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le y0 y1)) -> real_le (real_mul x0 y0) (real_mul x0 y1).
Definition term234 := forall y0 : real, forall y1 : real, (exists y2 : real, (real_le y0 y2) /\ (real_le y2 y1)) -> real_le y0 y1.
Definition term223 (x0 : real) := forall y0 : real, forall y1 : real, ((real_le x0 y0) /\ (real_le y0 y1)) -> real_le x0 y1.
Definition term221 := forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2.
Definition term271 (x0 : real) := @eq Prop (forall y0 : nat, (real_le (real_of_num (NUMERAL 0)) x0) -> real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num y0) x0)) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x0) y0)).
Definition term270 (x0 : real) := @eq Prop (forall y0 : nat, (real_le (real_of_num (NUMERAL 0)) x0) -> (fun y1 : nat => real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num y1) x0)) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x0) y1)) y0).
Definition term212 (x0 : real) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0).
Definition term210 (x0 : real) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term294 (x0 : real) := imp (((fun y0 : nat => real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num y0) x0)) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x0) y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num y1) x0)) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x0) y1)) y0) -> (fun y1 : nat => real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num y1) x0)) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x0) y1)) (S y0))).
Definition term140 (x0 : real) (x1 : real) := and (~ (real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_add x0 (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_mul (real_add (real_of_num (NUMERAL (BIT1 0))) x1) (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul x0 x1))))).
Definition term285 (x0 : real) (x1 : nat) := real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num (S x1)) x0)) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x0) (S x1)).
Definition term219 (x0 : real) := ((~ ((real_le (real_of_num (NUMERAL 0)) x0) -> real_le (real_of_num (NUMERAL 0)) (real_add (real_of_num (NUMERAL (BIT1 0))) x0))) -> False) -> (real_le (real_of_num (NUMERAL 0)) x0) -> real_le (real_of_num (NUMERAL 0)) (real_add (real_of_num (NUMERAL (BIT1 0))) x0).
Definition term155 (x0 : real) (x1 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul x0 (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))).
Definition term19 (x0 : real) := real_add (real_of_num (NUMERAL (BIT1 0))) x0.
Definition term9 (x0 : real) := real_add x0 (real_of_num (NUMERAL (BIT1 0))).
Definition term180 (x0 : real) := real_sub x0 (real_of_num (NUMERAL 0)).
Definition term98 (x0 : real) (x1 : real) := real_ge (real_sub (real_mul (real_add (real_of_num (NUMERAL (BIT1 0))) x1) (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul x0 x1))) (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_add x0 (real_of_num (NUMERAL (BIT1 0)))) x1))).
Definition term268 (x0 : real) := fun y0 : nat => (real_le (real_of_num (NUMERAL 0)) x0) -> real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num y0) x0)) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x0) y0).
Definition term104 (x0 : real) (x1 : real) := real_sub (real_of_num (NUMERAL 0)) (real_mul x0 (real_mul x1 x1)).
Definition term266 (x0 : real) (x1 : nat) := (real_le (real_of_num (NUMERAL 0)) x0) -> real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num x1) x0)) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x0) x1).
Definition term227 (x0 : real) (x1 : real) (x2 : real) := ((real_le x1 x0) /\ (real_le x0 x2)) -> real_le x1 x2.
Definition term58 (x0 : real) (x1 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul x0 x1) (real_add x1 (real_of_num (NUMERAL (BIT1 0))))).
Definition term312 (x0 : nat) (x1 : real) := real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num (S x0)) x1).
Definition term290 (x0 : real) := forall y0 : nat, ((fun y1 : nat => real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num y1) x0)) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x0) y1)) y0) -> (fun y1 : nat => real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num y1) x0)) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x0) y1)) (S y0).
Definition term340 (x0 : real) := forall y0 : real, ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le (real_of_num (NUMERAL 0)) y0)) -> real_le (real_of_num (NUMERAL 0)) (real_mul x0 y0).
Definition term320 (x0 : real) (x1 : real) := forall y0 : real, ((real_le (real_of_num (NUMERAL 0)) x1) /\ (real_le x0 y0)) -> real_le (real_mul x1 x0) (real_mul x1 y0).
Definition term55 (x0 : real) (x1 : real) := real_sub (real_mul (real_add (real_of_num (NUMERAL (BIT1 0))) x1) (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul x0 x1))) (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_add x0 (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term255 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := forall y0 : a0, x0 -> x1 y0.
Definition term77 (x0 : real) (x1 : real) := real_add (real_mul x0 x1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 x1)).
Definition term252 (a0 : Type') (x0 : Prop) := (fun y0 : Prop => forall y1 : a0 -> Prop, (forall y2 : a0, y0 -> y1 y2) = (y0 -> forall y2 : a0, y1 y2)) x0.
Definition term62 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term21 (x0 : real) (x1 : real) := real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul x0 x1).
Definition term238 (x0 : nat) := real_add (real_of_num x0) (real_of_num (NUMERAL (BIT1 0))).
Definition term161 (x0 : real) (x1 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term181 (x0 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term253 (a0 : Type') (x0 : Prop) := forall y0 : a0 -> Prop, (forall y1 : a0, x0 -> y0 y1) = (x0 -> forall y1 : a0, y0 y1).
Definition term267 (x0 : real) := fun y0 : nat => (real_le (real_of_num (NUMERAL 0)) x0) -> (fun y1 : nat => real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num y1) x0)) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x0) y1)) y0.
Definition term28 (x0 : real) (x1 : real) := real_add (real_mul x1 (real_mul x0 x1)) (real_mul x1 (real_of_num (NUMERAL (BIT1 0)))).
Definition term186 (x0 : real) := real_gt (real_sub (real_of_num (NUMERAL 0)) (real_add (real_of_num (NUMERAL (BIT1 0))) x0)) (real_of_num (NUMERAL 0)).
Definition term194 (x0 : real) := and (real_le (real_of_num (NUMERAL 0)) x0).
Definition term351 (x0 : real) := real_le (real_of_num (NUMERAL 0)) (real_mul x0 x0).
Definition term280 (x0 : real) := and ((fun y0 : nat => real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num y0) x0)) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x0) y0)) (NUMERAL 0)).
Definition term88 (x0 : real) := real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_add (real_of_num (NUMERAL (BIT1 0))) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term338 (x0 : nat) := real_le (real_of_num (NUMERAL 0)) (real_of_num x0).
Definition term23 (x0 : real) := real_mul (real_add (real_of_num (NUMERAL (BIT1 0))) x0).
Definition term269 (x0 : real) := forall y0 : nat, (real_le (real_of_num (NUMERAL 0)) x0) -> real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num y0) x0)) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x0) y0).
Definition term79 (x0 : nat) := real_add (real_neg (real_of_num x0)) (real_of_num x0).
Definition term46 := Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term105 (x0 : real) (x1 : real) := real_sub (real_of_num (NUMERAL 0)) (real_mul x0 (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))).
Definition term348 (x0 : nat) := and (real_le (real_of_num (NUMERAL 0)) (real_of_num x0)).
Definition term192 (x0 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term284 (x0 : real) (x1 : nat) := (fun y0 : nat => real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num y0) x0)) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x0) y0)) (S x1).
Definition term31 (x0 : real) := real_pow x0 (NUMERAL (BIT0 (BIT1 0))).
Definition term341 (x0 : real) (x1 : real) := (fun y0 : real => ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le (real_of_num (NUMERAL 0)) y0)) -> real_le (real_of_num (NUMERAL 0)) (real_mul x0 y0)) x1.
Definition term229 (x0 : real) (x1 : real) := (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> real_le x0 x1.
Definition term172 := Peano.lt (NUMERAL 0) (NUMERAL 0).
Definition term138 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term233 (x0 : real) := forall y0 : real, (exists y1 : real, (real_le x0 y1) /\ (real_le y1 y0)) -> real_le x0 y0.
Definition term288 (x0 : real) := fun y0 : nat => ((fun y1 : nat => real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num y1) x0)) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x0) y1)) y0) -> (fun y1 : nat => real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num y1) x0)) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x0) y1)) (S y0).
Definition term110 (x0 : real) (x1 : real) := real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term103 := real_sub (real_of_num (NUMERAL 0)).
Definition term256 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 -> forall y0 : a0, x1 y0.
Definition term232 (x0 : real) (x1 : real) := (exists y0 : real, (real_le x0 y0) /\ (real_le y0 x1)) -> real_le x0 x1.
Definition term107 (x0 : real) (x1 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))).
Definition term205 (x0 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))))).
Definition term122 (x0 : real) (x1 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul x0 (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))) (real_add (real_mul x0 x1) (real_add x1 (real_of_num (NUMERAL (BIT1 0)))))).
Definition term49 (x0 : real) (x1 : real) := real_add (real_add (real_mul x0 (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))) x1) (real_add (real_mul x0 x1) (real_of_num (NUMERAL (BIT1 0)))).
Definition term297 (x0 : real) := real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num (NUMERAL 0)) x0).
Definition term327 (x0 : nat) (x1 : real) := real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num x0) x1).
Definition term216 := real_gt (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term171 := real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term139 (x0 : real) (x1 : real) := real_ge (real_sub (real_mul x0 (real_mul x1 x1)) (real_of_num (NUMERAL 0))).
Definition term166 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) (real_mul x0 (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))).
Definition term160 (x0 : real) (x1 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))))) (real_of_num (NUMERAL 0)).
Definition term151 (x0 : real) (x1 : real) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_mul x0 (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL 0))).
Definition term198 (x0 : real) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0)))) -> real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) x0) (real_of_num (NUMERAL 0)).
Definition term133 (x0 : real) (x1 : real) := real_sub (real_mul x0 (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))).
Definition term323 (x0 : real) (x1 : real) (x2 : real) := (real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le x1 x2).
Definition term13 (x0 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) x0.
Definition term93 (x0 : real) := real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)).
Definition term72 (x0 : real) (x1 : real) := real_add (real_add (real_mul x0 (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))) (real_add (real_mul x0 x1) (real_add x1 (real_of_num (NUMERAL (BIT1 0)))))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 x1)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))).
Definition term71 (x0 : real) (x1 : real) := real_add (real_add (real_mul x0 (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))) (real_add (real_mul x0 x1) (real_add x1 (real_of_num (NUMERAL (BIT1 0)))))).
Definition term154 (x0 : real) (x1 : real) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul x0 (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term63 (x0 : nat) (x1 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num x1).
Definition term69 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 x1)).
Definition term211 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0.
Definition term15 (x0 : real) (x1 : real) := real_add (real_mul x0 x1) x1.
Definition term109 (x0 : real) (x1 : real) := real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term132 (x0 : real) (x1 : real) := real_sub (real_mul x0 (real_mul x1 x1)).
Definition term152 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) -> real_ge (real_mul x0 x1) (real_of_num (NUMERAL 0)).
Definition term123 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul x0 x1) (real_add x1 (real_of_num (NUMERAL (BIT1 0)))))).
Definition term193 (x0 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term29 (x0 : real) (x1 : real) := real_mul x1 (real_mul x0 x1).
Definition term25 (x0 : real) (x1 : real) := real_mul (real_add x1 (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul x0 x1) (real_of_num (NUMERAL (BIT1 0)))).
Definition term38 (x0 : real) (x1 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul x0 x1) (real_of_num (NUMERAL (BIT1 0)))).
Definition term260 (x0 : real) := (real_le (real_of_num (NUMERAL 0)) x0) -> forall y0 : nat, (fun y1 : nat => real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num y1) x0)) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x0) y1)) y0.
Definition term59 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 x1)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add x1 (real_of_num (NUMERAL (BIT1 0))))).
Definition term339 (x0 : real) := (fun y0 : real => forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le (real_of_num (NUMERAL 0)) y1)) -> real_le (real_of_num (NUMERAL 0)) (real_mul y0 y1)) x0.
Definition term236 (x0 : real) := (fun y0 : real => forall y1 : real, (exists y2 : real, (real_le y0 y2) /\ (real_le y2 y1)) -> real_le y0 y1) x0.
Definition term282 (x0 : real) (x1 : nat) := imp ((fun y0 : nat => real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num y0) x0)) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x0) y0)) x1).
Definition term18 (x0 : real) (x1 : real) := real_add (real_mul x0 x1) (real_add (real_of_num (NUMERAL (BIT1 0))) x1).
Definition term42 := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term147 (x0 : nat) (x1 : nat) := real_gt (real_of_num x0) (real_of_num x1).
Definition term308 (x0 : nat) := real_mul (real_of_num (S x0)).
Definition term20 (x0 : real) (x1 : real) := real_add (real_mul x0 x1) (real_add x1 (real_of_num (NUMERAL (BIT1 0)))).
Definition term119 (x0 : real) (x1 : real) := real_sub (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_add x0 (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_mul (real_add (real_of_num (NUMERAL (BIT1 0))) x1) (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul x0 x1))).
Definition term39 (x0 : real) (x1 : real) := real_add (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul x0 x1)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term330 (x0 : real) := and (real_le (real_of_num (NUMERAL 0)) (real_add (real_of_num (NUMERAL (BIT1 0))) x0)).
Definition term150 := S (Nat.add 0 0).
Definition term344 (x0 : real) (x1 : real) := real_le (real_of_num (NUMERAL 0)) (real_mul x0 x1).
Definition term91 (x0 : real) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term100 (x0 : real) (x1 : real) := real_ge (real_mul x0 (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term283 (x0 : real) (x1 : nat) := imp (real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num x1) x0)) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x0) x1)).
Definition term177 (x0 : real) := real_le (real_of_num (NUMERAL 0)) x0.
Definition term60 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term37 (x0 : real) (x1 : real) := real_add (real_add (real_mul x0 (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))) x1).
Definition term296 (x0 : real) := ((real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num (NUMERAL 0)) x0)) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x0) (NUMERAL 0))) /\ (forall y0 : nat, (real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num y0) x0)) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x0) y0)) -> real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num (S y0)) x0)) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x0) (S y0)))) -> forall y0 : nat, real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num y0) x0)) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x0) y0).
Definition term117 (x0 : real) (x1 : real) := real_sub (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_add x0 (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term65 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term304 (x0 : real) (x1 : nat) := real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x0) (S x1).
Definition term309 (x0 : nat) := real_mul (real_add (real_of_num x0) (real_of_num (NUMERAL (BIT1 0)))).
Definition term272 (x0 : real) := fun y0 : nat => (fun y1 : nat => real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num y1) x0)) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x0) y1)) y0.
Definition term335 (x0 : nat) (x1 : real) := (real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_add (real_of_num x0) (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_mul (real_add (real_of_num (NUMERAL (BIT1 0))) x1) (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num x0) x1)))) /\ True.
Definition term298 := real_add (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term247 (x0 : real) := (fun y0 : real => (real_mul (real_of_num (NUMERAL 0)) y0) = (real_of_num (NUMERAL 0))) x0.
Definition term190 (x0 : real) := real_add (real_of_num (NUMERAL 0)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term101 (x0 : real) (x1 : real) := ~ (real_le (real_of_num (NUMERAL 0)) (real_mul x0 (real_mul x1 x1))).
Definition term203 (x0 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term178 (x0 : real) := real_le (real_of_num (NUMERAL 0)) (real_add (real_of_num (NUMERAL (BIT1 0))) x0).
Definition term83 := real_mul (real_of_num (NUMERAL 0)).
Definition term319 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le y0 y1)) -> real_le (real_mul x0 y0) (real_mul x0 y1)) x1.
Definition term224 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, ((real_le x0 y0) /\ (real_le y0 y1)) -> real_le x0 y1) x1.
Definition term89 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term187 (x0 : real) := real_sub (real_of_num (NUMERAL 0)) (real_add (real_of_num (NUMERAL (BIT1 0))) x0).
Definition term188 (x0 : real) := real_sub (real_of_num (NUMERAL 0)) (real_add x0 (real_of_num (NUMERAL (BIT1 0)))).
Definition term321 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => ((real_le (real_of_num (NUMERAL 0)) x1) /\ (real_le x0 y0)) -> real_le (real_mul x1 x0) (real_mul x1 y0)) x2.
Definition term189 (x0 : real) := real_add (real_of_num (NUMERAL 0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add x0 (real_of_num (NUMERAL (BIT1 0))))).
Definition term208 (x0 : real) := real_gt (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) x0) (real_of_num (NUMERAL 0)).
Definition term201 (x0 : real) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))).
Definition term36 (x0 : real) (x1 : real) := real_add (real_mul x1 (real_add (real_mul x0 x1) (real_of_num (NUMERAL (BIT1 0))))).
Definition term40 (x0 : nat) (x1 : nat) := real_mul (real_of_num x0) (real_of_num x1).
Definition term209 (x0 : real) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) x0.
Definition term35 (x0 : real) (x1 : real) := real_add (real_mul x0 (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))) x1.
Definition term226 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => ((real_le x1 x0) /\ (real_le x0 y0)) -> real_le x1 y0) x2.
Definition term76 (x0 : real) (x1 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 x1).
Definition term135 (x0 : real) (x1 : real) := real_sub (real_mul x0 (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term258 (x0 : Prop) (x1 : nat -> Prop) := x0 -> forall y0 : nat, x1 y0.
Definition term206 (x0 : real) := (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0))).
Definition term263 (x0 : real) (x1 : nat) := real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num x1) x0)) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x0) x1).
Definition term153 (x0 : real) (x1 : real) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_mul x0 (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL 0)))) -> real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul x0 (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term329 (x0 : real) := (real_le (real_of_num (NUMERAL 0)) x0) -> (real_le (real_of_num (NUMERAL 0)) (real_add (real_of_num (NUMERAL (BIT1 0))) x0)) = True.
Definition term24 (x0 : real) := real_mul (real_add x0 (real_of_num (NUMERAL (BIT1 0)))).
Definition term50 (x0 : real) (x1 : real) := real_add (real_mul x0 (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))) (real_add x1 (real_add (real_mul x0 x1) (real_of_num (NUMERAL (BIT1 0))))).
Definition term64 (x0 : nat) (x1 : nat) := real_neg (real_of_num (Nat.mul x0 x1)).
Definition term87 (x0 : real) := real_add (real_add x0 (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term242 := forall y0 : nat, (real_add (real_of_num y0) (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (S y0)).
Definition term30 (x0 : real) (x1 : real) := real_mul x0 (real_mul x1 x1).
Definition term162 (x0 : real) (x1 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))))).
Definition term0 (x0 : real) (x1 : real) := ~ ((real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_add x0 (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_mul (real_add (real_of_num (NUMERAL (BIT1 0))) x1) (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul x0 x1)))) = (real_le (real_of_num (NUMERAL 0)) (real_mul x0 (real_mul x1 x1)))).
Definition term333 (x0 : nat) (x1 : real) := and (real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_add (real_of_num x0) (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_mul (real_add (real_of_num (NUMERAL (BIT1 0))) x1) (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num x0) x1)))).
Definition term111 (x0 : real) (x1 : real) := and (real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_add x0 (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_mul (real_add (real_of_num (NUMERAL (BIT1 0))) x1) (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul x0 x1)))).
Definition term237 (x0 : real) (x1 : real) := (fun y0 : real => (exists y1 : real, (real_le x0 y1) /\ (real_le y1 y0)) -> real_le x0 y0) x1.
Definition term245 (x0 : real) := (fun y0 : real => real_le y0 y0) x0.
Definition term200 (x0 : real) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) x0).
Definition term287 (x0 : real) (x1 : nat) := (real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num x1) x0)) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x0) x1)) -> real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num (S x1)) x0)) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x0) (S x1)).
Definition term33 (x0 : real) (x1 : real) := real_add (real_mul x1 (real_mul x0 x1)).
Definition term322 (x0 : real) (x1 : real) (x2 : real) := ((real_le (real_of_num (NUMERAL 0)) x1) /\ (real_le x0 x2)) -> real_le (real_mul x1 x0) (real_mul x1 x2).
Definition term355 (x0 : nat) (x1 : real) := real_mul (real_add (real_of_num (NUMERAL (BIT1 0))) x1) (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num x0) x1)).
Definition term32 (x0 : real) (x1 : real) := real_mul x0 (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))).
Definition term43 := real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term278 (x0 : real) := (fun y0 : nat => real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num y0) x0)) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x0) y0)) (NUMERAL 0).
Definition term11 := real_of_num (NUMERAL (BIT1 0)).
Definition term225 (x0 : real) (x1 : real) := forall y0 : real, ((real_le x1 x0) /\ (real_le x0 y0)) -> real_le x1 y0.
Definition term67 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term120 (x0 : real) (x1 : real) := real_sub (real_add (real_mul x0 x1) (real_add x1 (real_of_num (NUMERAL (BIT1 0))))) (real_add (real_mul x0 (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))) (real_add (real_mul x0 x1) (real_add x1 (real_of_num (NUMERAL (BIT1 0)))))).
Definition term156 (x0 : real) (x1 : real) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul x0 (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term124 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term47 (x0 : real) (x1 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul x0 x1).
Definition term26 (x0 : real) (x1 : real) := real_add (real_mul x1 (real_add (real_mul x0 x1) (real_of_num (NUMERAL (BIT1 0))))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul x0 x1) (real_of_num (NUMERAL (BIT1 0))))).
Definition term213 := real_add (real_of_num (NUMERAL 0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term354 (x0 : real) (x1 : nat) := fun y0 : real => (real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_add (real_of_num x1) (real_of_num (NUMERAL (BIT1 0)))) x0)) y0) /\ (real_le y0 (real_mul (real_add (real_of_num (NUMERAL (BIT1 0))) x0) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x0) x1))).
Definition term22 (x0 : real) (x1 : real) := real_add (real_mul x0 x1) (real_of_num (NUMERAL (BIT1 0))).
Definition term92 (x0 : real) := real_mul (real_of_num (NUMERAL 0)) x0.
Definition term3 (x0 : real) (x1 : real) := real_le (real_of_num (NUMERAL 0)) (real_mul x0 (real_mul x1 x1)).
Definition term299 (x0 : real) := real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num (NUMERAL 0)) x0)).
Definition term16 := real_add (real_of_num (NUMERAL (BIT1 0))).
Definition term334 (x0 : real) (x1 : nat) := (real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_add (real_of_num x1) (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_mul (real_add (real_of_num (NUMERAL (BIT1 0))) x0) (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num x1) x0)))) /\ (real_le (real_mul (real_add (real_of_num (NUMERAL (BIT1 0))) x0) (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num x1) x0))) (real_mul (real_add (real_of_num (NUMERAL (BIT1 0))) x0) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x0) x1))).
Definition term145 (x0 : real) (x1 : real) := or ((real_ge (real_mul x0 (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) (real_of_num (NUMERAL 0)))).
Definition term95 := real_add (real_of_num (NUMERAL (BIT1 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term228 (x0 : real) (x1 : real) (x2 : real) := (real_le x0 x1) /\ (real_le x1 x2).
Definition term27 (x0 : real) (x1 : real) := real_mul x1 (real_add (real_mul x0 x1) (real_of_num (NUMERAL (BIT1 0)))).
Definition term342 (x0 : real) (x1 : real) := ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le (real_of_num (NUMERAL 0)) x1)) -> real_le (real_of_num (NUMERAL 0)) (real_mul x0 x1).
Definition term34 (x0 : real) (x1 : real) := real_add (real_mul x0 (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))).
Definition term136 (x0 : real) (x1 : real) := real_add (real_mul x0 (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term116 (x0 : real) (x1 : real) := real_gt (real_sub (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_add x0 (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_mul (real_add (real_of_num (NUMERAL (BIT1 0))) x1) (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul x0 x1)))) (real_of_num (NUMERAL 0)).
Definition term5 (x0 : real) (x1 : real) := real_mul (real_add (real_of_num (NUMERAL (BIT1 0))) x1) (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul x0 x1)).
Definition term97 (x0 : real) (x1 : real) := real_add (real_mul x0 (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term295 (x0 : real) := imp ((real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num (NUMERAL 0)) x0)) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x0) (NUMERAL 0))) /\ (forall y0 : nat, (real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num y0) x0)) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x0) y0)) -> real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num (S y0)) x0)) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x0) (S y0)))).
Definition term2 (x0 : real) (x1 : real) := real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_add x0 (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_mul (real_add (real_of_num (NUMERAL (BIT1 0))) x1) (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul x0 x1))).
Definition term12 (x0 : real) := real_mul x0 (real_of_num (NUMERAL (BIT1 0))).
Definition term176 (x0 : real) := (real_le (real_of_num (NUMERAL 0)) x0) /\ (~ (real_le (real_of_num (NUMERAL 0)) (real_add (real_of_num (NUMERAL (BIT1 0))) x0))).
Definition term346 (x0 : real) (x1 : real) := ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le (real_of_num (NUMERAL 0)) x1)) -> (real_le (real_of_num (NUMERAL 0)) (real_mul x0 x1)) = True.
Definition term310 (x0 : nat) (x1 : real) := real_mul (real_of_num (S x0)) x1.
Definition term146 (x0 : real) (x1 : real) := ((real_ge (real_mul x0 (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) (real_of_num (NUMERAL 0)))) \/ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_mul x0 (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL 0)))).
Definition term262 (x0 : real) (x1 : nat) := (fun y0 : nat => real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num y0) x0)) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x0) y0)) x1.
Definition term220 (x0 : real) := (real_le (real_of_num (NUMERAL 0)) x0) -> real_le (real_of_num (NUMERAL 0)) (real_add (real_of_num (NUMERAL (BIT1 0))) x0).
Definition term10 (x0 : real) (x1 : real) := real_add (real_mul x1 x0) (real_mul x1 (real_of_num (NUMERAL (BIT1 0)))).
Definition term84 (x0 : real) (x1 : real) := real_mul (real_of_num (NUMERAL 0)) (real_mul x0 x1).
Definition term41 (x0 : nat) (x1 : nat) := real_of_num (Nat.mul x0 x1).
Definition term314 (x0 : nat) (x1 : real) := real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_add (real_of_num x0) (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term306 (x0 : nat) (x1 : real) := real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num (S x0)) x1)).
Definition term74 (x0 : real) (x1 : real) := real_add (real_add (real_mul x0 x1) (real_add x1 (real_of_num (NUMERAL (BIT1 0))))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 x1)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))).
Definition term350 (x0 : real) := (real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le (real_of_num (NUMERAL 0)) x0).
Definition term291 (x0 : real) := forall y0 : nat, (real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num y0) x0)) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x0) y0)) -> real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num (S y0)) x0)) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x0) (S y0)).
Definition term4 (x0 : real) (x1 : real) := real_ge (real_sub (real_mul (real_add (real_of_num (NUMERAL (BIT1 0))) x1) (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul x0 x1))) (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_add x0 (real_of_num (NUMERAL (BIT1 0)))) x1))) (real_of_num (NUMERAL 0)).
Definition term96 := real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term130 (x0 : real) (x1 : real) := real_gt (real_sub (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_add x0 (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_mul (real_add (real_of_num (NUMERAL (BIT1 0))) x1) (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul x0 x1)))).
Definition term175 (x0 : real) := ~ ((real_le (real_of_num (NUMERAL 0)) x0) -> real_le (real_of_num (NUMERAL 0)) (real_add (real_of_num (NUMERAL (BIT1 0))) x0)).
Definition term302 (x0 : real) := real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x0) (NUMERAL 0).
Definition term141 (x0 : real) (x1 : real) := and (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) (real_of_num (NUMERAL 0))).
Definition term7 (x0 : real) (x1 : real) := real_mul (real_add x0 (real_of_num (NUMERAL (BIT1 0)))) x1.
Definition term1 (x0 : real) (x1 : real) := ((real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_add x0 (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_mul (real_add (real_of_num (NUMERAL (BIT1 0))) x1) (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul x0 x1)))) /\ (~ (real_le (real_of_num (NUMERAL 0)) (real_mul x0 (real_mul x1 x1))))) \/ ((~ (real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_add x0 (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_mul (real_add (real_of_num (NUMERAL (BIT1 0))) x1) (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul x0 x1))))) /\ (real_le (real_of_num (NUMERAL 0)) (real_mul x0 (real_mul x1 x1)))).
Definition term127 (x0 : real) (x1 : real) := real_add (real_add (real_mul x0 x1) (real_add x1 (real_of_num (NUMERAL (BIT1 0))))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 x1)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_neg (real_of_num (NUMERAL (BIT1 0))))))).
Definition term300 := real_le (real_of_num (NUMERAL (BIT1 0))).
Definition term68 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term240 := fun y0 : nat => (real_add (real_of_num y0) (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (S y0)).
Definition term52 (x0 : real) (x1 : real) := real_add (real_mul x0 (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))) (real_add (real_mul x0 x1) (real_add x1 (real_of_num (NUMERAL (BIT1 0))))).
Definition term261 (x0 : real) := fun y0 : nat => real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num y0) x0)) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x0) y0).
Definition term246 (x0 : real) := (fun y0 : real => (real_add y0 (real_of_num (NUMERAL 0))) = y0) x0.
Definition term81 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term102 (x0 : real) (x1 : real) := real_gt (real_sub (real_of_num (NUMERAL 0)) (real_mul x0 (real_mul x1 x1))) (real_of_num (NUMERAL 0)).
Definition term202 (x0 : real) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)))) -> real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term164 (x0 : real) (x1 : real) := ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_mul x0 (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL 0)))) -> real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) (real_mul x0 (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term159 (x0 : real) (x1 : real) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) (real_of_num (NUMERAL 0)))) -> real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))))) (real_of_num (NUMERAL 0)).
Definition term106 (x0 : real) (x1 : real) := real_add (real_of_num (NUMERAL 0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term86 := real_add (real_of_num (NUMERAL 0)).
Definition term183 (x0 : real) := real_ge (real_sub x0 (real_of_num (NUMERAL 0))).
Definition term317 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le y1 y2)) -> real_le (real_mul y0 y1) (real_mul y0 y2)) x0.
Definition term222 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) x0.
Definition term179 (x0 : real) := real_ge (real_sub x0 (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term274 (x0 : real) := forall y0 : nat, real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num y0) x0)) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x0) y0).
Definition term257 (x0 : Prop) (x1 : nat -> Prop) := forall y0 : nat, x0 -> x1 y0.
Definition term305 (x0 : real) (x1 : nat) := real_mul (real_add (real_of_num (NUMERAL (BIT1 0))) x0) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x0) x1).
Definition term241 := fun y0 : nat => (real_of_num (S y0)) = (real_add (real_of_num y0) (real_of_num (NUMERAL (BIT1 0)))).
Definition term44 := NUMERAL (BIT1 0).
Definition term163 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) -> real_gt (real_add x0 x1) (real_of_num (NUMERAL 0)).
Definition term158 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_gt x1 (real_of_num (NUMERAL 0)))) -> real_gt (real_mul x0 x1) (real_of_num (NUMERAL 0)).
Definition term90 (x0 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term148 := real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term73 (x0 : real) (x1 : real) := real_add (real_mul x0 (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))) (real_add (real_add (real_mul x0 x1) (real_add x1 (real_of_num (NUMERAL (BIT1 0))))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 x1)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_neg (real_of_num (NUMERAL (BIT1 0))))))).
Definition term170 := real_gt (real_of_num (NUMERAL 0)).
Definition term121 (x0 : real) (x1 : real) := real_add (real_add (real_mul x0 x1) (real_add x1 (real_of_num (NUMERAL (BIT1 0))))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul x0 (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))) (real_add (real_mul x0 x1) (real_add x1 (real_of_num (NUMERAL (BIT1 0))))))).
