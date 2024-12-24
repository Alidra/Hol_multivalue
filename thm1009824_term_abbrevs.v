Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term14 (x0 : nat) (x1 : nat) := exists y0 : nat, (NUMERAL x0) = (Nat.add (NUMERAL x1) (S y0)).
Definition term82 (x0 : nat) (x1 : nat) := ~ (x0 = x1).
Definition term96 := (~ False) -> False.
Definition term68 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ~ (x0 = (S (Nat.add x1 y0)))) x2.
Definition term50 (x0 : nat) := fun y0 : nat => (Nat.add x0 y0) = (Nat.add y0 x0).
Definition term22 (x0 : nat) (x1 : nat) := exists y0 : nat, x0 = (S (Nat.add x1 y0)).
Definition term87 (x0 : Prop) := ~ (~ x0).
Definition term97 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (~ (((S (Nat.add y2 y0)) = y1) -> exists y3 : nat, y1 = (S (Nat.add y0 y3)))) -> (forall y3 : nat, forall y4 : nat, (Nat.add y3 y4) = (Nat.add y4 y3)) -> False) x0.
Definition term81 (x0 : nat) (x1 : nat) := ((S x0) = (S x1)) \/ (~ (x0 = x1)).
Definition term78 (x0 : nat) (x1 : nat) := (~ ((Nat.add x1 x0) = (Nat.add x0 x1))) -> (Nat.add x1 x0) = (Nat.add x0 x1).
Definition term29 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (((S (Nat.add x0 x2)) = x1) -> exists y0 : nat, x1 = (S (Nat.add x2 y0)))) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> False.
Definition term91 (x0 : nat) (x1 : nat) := ((Nat.add x1 x0) = (Nat.add x0 x1)) -> (S (Nat.add x1 x0)) = (S (Nat.add x0 x1)).
Definition term31 (x0 : nat) (x1 : nat) (x2 : nat) := (((~ (((S (Nat.add x0 x2)) = x1) -> exists y0 : nat, x1 = (S (Nat.add x2 y0)))) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> False) -> (~ (((S (Nat.add x0 x2)) = x1) -> exists y0 : nat, x1 = (S (Nat.add x2 y0)))) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> False) -> (~ (((S (Nat.add x0 x2)) = x1) -> exists y0 : nat, x1 = (S (Nat.add x2 y0)))) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> False.
Definition term70 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ~ (y0 = (S (Nat.add x0 x1)))) x2.
Definition term26 (x0 : Prop) := (~ x0) -> False.
Definition term23 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((S (Nat.add x0 x1)) = x2).
Definition term1 := (forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))).
Definition term64 (x0 : nat) (x1 : nat) (x2 : nat) := ((S (Nat.add x0 x2)) = x1) /\ (~ (exists y0 : nat, x1 = (S (Nat.add x2 y0)))).
Definition term93 (x0 : nat) (x1 : nat) := ~ ((S (Nat.add x1 x0)) = (S (Nat.add x0 x1))).
Definition term72 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((S (Nat.add x0 x1)) = (S (Nat.add x1 x2))).
Definition term9 (x0 : nat) := forall y0 : nat, (Peano.lt x0 y0) = (exists y1 : nat, y0 = (Nat.add x0 (S y1))).
Definition term85 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term34 := ~ (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)).
Definition term80 (x0 : Prop) := (~ x0) -> x0.
Definition term63 (x0 : nat) (x1 : nat) (x2 : nat) := and ((S (Nat.add x0 x1)) = x2).
Definition term36 (x0 : nat) (x1 : nat) (x2 : nat) := imp (~ (((S (Nat.add x0 x2)) = x1) -> exists y0 : nat, x1 = (S (Nat.add x2 y0)))).
Definition term18 (x0 : nat) := Nat.add (NUMERAL x0).
Definition term98 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (~ (((S (Nat.add y1 x0)) = y0) -> exists y2 : nat, y0 = (S (Nat.add x0 y2)))) -> (forall y2 : nat, forall y3 : nat, (Nat.add y2 y3) = (Nat.add y3 y2)) -> False) x1.
Definition term84 (x0 : nat) (x1 : nat) := @eq Prop (((S x0) = (S x1)) \/ (~ (x0 = x1))).
Definition term52 := fun y0 : nat => forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0).
Definition term39 (x0 : nat) (x1 : nat) := fun y0 : nat => (~ (((S (Nat.add y0 x1)) = x0) -> exists y1 : nat, x0 = (S (Nat.add x1 y1)))) -> ~ (forall y1 : nat, forall y2 : nat, (Nat.add y1 y2) = (Nat.add y2 y1)).
Definition term74 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop (~ (x0 = (S (Nat.add x1 x2)))).
Definition term19 (x0 : nat) (x1 : nat) := Nat.add (NUMERAL x0) x1.
Definition term33 := (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> False.
Definition term90 (x0 : nat) (x1 : nat) := imp (x0 = x1).
Definition term12 (x0 : nat) := (fun y0 : nat => (NUMERAL y0) = y0) x0.
Definition term7 (x0 : nat) (x1 : nat) := S (Nat.add x0 x1).
Definition term62 (x0 : nat) (x1 : nat) := forall y0 : nat, ~ (x0 = (S (Nat.add x1 y0))).
Definition term49 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (~ (((S (Nat.add y2 y0)) = y1) -> exists y3 : nat, y1 = (S (Nat.add y0 y3)))) -> ~ (forall y3 : nat, forall y4 : nat, (Nat.add y3 y4) = (Nat.add y4 y3)).
Definition term48 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (~ (((S (Nat.add y2 y0)) = y1) -> exists y3 : nat, y1 = (S (Nat.add y0 y3)))) -> (forall y3 : nat, forall y4 : nat, (Nat.add y3 y4) = (Nat.add y4 y3)) -> False.
Definition term45 (x0 : nat) := forall y0 : nat, forall y1 : nat, (~ (((S (Nat.add y1 x0)) = y0) -> exists y2 : nat, y0 = (S (Nat.add x0 y2)))) -> ~ (forall y2 : nat, forall y3 : nat, (Nat.add y2 y3) = (Nat.add y3 y2)).
Definition term44 (x0 : nat) := forall y0 : nat, forall y1 : nat, (~ (((S (Nat.add y1 x0)) = y0) -> exists y2 : nat, y0 = (S (Nat.add x0 y2)))) -> (forall y2 : nat, forall y3 : nat, (Nat.add y2 y3) = (Nat.add y3 y2)) -> False.
Definition term35 := forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0).
Definition term2 := forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)).
Definition term28 (x0 : nat) (x1 : nat) (x2 : nat) := ~ (((S (Nat.add x0 x2)) = x1) -> exists y0 : nat, x1 = (S (Nat.add x2 y0))).
Definition term58 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((fun y0 : nat => x0 = (S (Nat.add x1 y0))) x2).
Definition term59 (x0 : nat) (x1 : nat) (x2 : nat) := ~ (x0 = (S (Nat.add x1 x2))).
Definition term53 (x0 : nat -> Prop) := ~ (ex x0).
Definition term71 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ~ (y0 = (S (Nat.add x2 x0)))) (S (Nat.add x1 x2)).
Definition term92 (x0 : nat) (x1 : nat) := (~ ((S (Nat.add x1 x0)) = (S (Nat.add x0 x1)))) -> (S (Nat.add x1 x0)) = (S (Nat.add x0 x1)).
Definition term54 (x0 : nat -> Prop) := forall y0 : nat, ~ (x0 y0).
Definition term11 (x0 : nat) (x1 : nat) := exists y0 : nat, x0 = (Nat.add x1 (S y0)).
Definition term51 (x0 : nat) := forall y0 : nat, (Nat.add x0 y0) = (Nat.add y0 x0).
Definition term40 (x0 : nat) (x1 : nat) := forall y0 : nat, (~ (((S (Nat.add y0 x1)) = x0) -> exists y1 : nat, x0 = (S (Nat.add x1 y1)))) -> (forall y1 : nat, forall y2 : nat, (Nat.add y1 y2) = (Nat.add y2 y1)) -> False.
Definition term5 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add x0 (S y0)) = (S (Nat.add x0 y0))) x1.
Definition term67 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add x0 y0) = (Nat.add y0 x0)) x1.
Definition term0 := (forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))).
Definition term73 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((fun y0 : nat => ~ (y0 = (S (Nat.add x0 x1)))) x2).
Definition term56 (x0 : nat) (x1 : nat) := forall y0 : nat, ~ ((fun y1 : nat => x0 = (S (Nat.add x1 y1))) y0).
Definition term66 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) x0.
Definition term8 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y0 y1) = (exists y2 : nat, y1 = (Nat.add y0 (S y2)))) x0.
Definition term3 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))) x0.
Definition term30 (x0 : nat) (x1 : nat) (x2 : nat) := ((~ (((S (Nat.add x0 x2)) = x1) -> exists y0 : nat, x1 = (S (Nat.add x2 y0)))) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> False) -> (~ (((S (Nat.add x0 x2)) = x1) -> exists y0 : nat, x1 = (S (Nat.add x2 y0)))) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> False.
Definition term15 (x0 : nat) := @eq nat (NUMERAL x0).
Definition term16 (x0 : nat) (x1 : nat) := Nat.add (NUMERAL x0) (S x1).
Definition term75 (x0 : nat) (x1 : nat) := (x0 = x1) -> (S x0) = (S x1).
Definition term6 (x0 : nat) (x1 : nat) := Nat.add x0 (S x1).
Definition term21 (x0 : nat) (x1 : nat) := fun y0 : nat => x0 = (S (Nat.add x1 y0)).
Definition term25 (x0 : nat) (x1 : nat) (x2 : nat) := ((S (Nat.add x0 x2)) = x1) -> exists y0 : nat, x1 = (S (Nat.add x2 y0)).
Definition term13 (x0 : nat) (x1 : nat) := Peano.lt (NUMERAL x0) (NUMERAL x1).
Definition term76 (x0 : Prop) (x1 : Prop) := (~ x0) \/ x1.
Definition term57 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => x0 = (S (Nat.add x1 y0))) x2.
Definition term37 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (((S (Nat.add x0 x2)) = x1) -> exists y0 : nat, x1 = (S (Nat.add x2 y0)))) -> ~ (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)).
Definition term61 (x0 : nat) (x1 : nat) := fun y0 : nat => ~ (x0 = (S (Nat.add x1 y0))).
Definition term86 (x0 : nat) (x1 : nat) := (~ (~ (x0 = x1))) -> (S x0) = (S x1).
Definition term79 (x0 : nat) (x1 : nat) := ~ ((Nat.add x1 x0) = (Nat.add x0 x1)).
Definition term24 (x0 : nat) (x1 : nat) (x2 : nat) := ((S (Nat.add x0 x1)) = x2) -> (Peano.lt (NUMERAL x1) (NUMERAL x2)) = True.
Definition term43 (x0 : nat) := fun y0 : nat => forall y1 : nat, (~ (((S (Nat.add y1 x0)) = y0) -> exists y2 : nat, y0 = (S (Nat.add x0 y2)))) -> ~ (forall y2 : nat, forall y3 : nat, (Nat.add y2 y3) = (Nat.add y3 y2)).
Definition term83 (x0 : nat) (x1 : nat) := @eq Prop ((~ (x0 = x1)) \/ ((S x0) = (S x1))).
Definition term77 (x0 : nat) (x1 : nat) := (~ (x0 = x1)) \/ ((S x0) = (S x1)).
Definition term69 (x0 : nat) (x1 : nat) := fun y0 : nat => ~ (y0 = (S (Nat.add x0 x1))).
Definition term60 (x0 : nat) (x1 : nat) := fun y0 : nat => ~ ((fun y1 : nat => x0 = (S (Nat.add x1 y1))) y0).
Definition term27 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (((S (Nat.add x0 x2)) = x1) -> exists y0 : nat, x1 = (S (Nat.add x2 y0)))) -> False.
Definition term41 (x0 : nat) (x1 : nat) := forall y0 : nat, (~ (((S (Nat.add y0 x1)) = x0) -> exists y1 : nat, x0 = (S (Nat.add x1 y1)))) -> ~ (forall y1 : nat, forall y2 : nat, (Nat.add y1 y2) = (Nat.add y2 y1)).
Definition term88 (x0 : nat) (x1 : nat) := ~ (~ (x0 = x1)).
Definition term32 (x0 : nat) (x1 : nat) (x2 : nat) := (((~ (((S (Nat.add x0 x2)) = x1) -> exists y0 : nat, x1 = (S (Nat.add x2 y0)))) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> False) -> (~ (((S (Nat.add x0 x2)) = x1) -> exists y0 : nat, x1 = (S (Nat.add x2 y0)))) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> False) -> ((~ (((S (Nat.add x0 x2)) = x1) -> exists y0 : nat, x1 = (S (Nat.add x2 y0)))) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> False) -> (~ (((S (Nat.add x0 x2)) = x1) -> exists y0 : nat, x1 = (S (Nat.add x2 y0)))) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> False.
Definition term10 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt x0 y0) = (exists y1 : nat, y0 = (Nat.add x0 (S y1)))) x1.
Definition term65 (x0 : nat) (x1 : nat) (x2 : nat) := ((S (Nat.add x0 x2)) = x1) /\ (forall y0 : nat, ~ (x1 = (S (Nat.add x2 y0)))).
Definition term17 (x0 : nat) (x1 : nat) := S (Nat.add (NUMERAL x0) x1).
Definition term42 (x0 : nat) := fun y0 : nat => forall y1 : nat, (~ (((S (Nat.add y1 x0)) = y0) -> exists y2 : nat, y0 = (S (Nat.add x0 y2)))) -> (forall y2 : nat, forall y3 : nat, (Nat.add y2 y3) = (Nat.add y3 y2)) -> False.
Definition term55 (x0 : nat) (x1 : nat) := ~ (exists y0 : nat, x0 = (S (Nat.add x1 y0))).
Definition term99 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (~ (((S (Nat.add y0 x1)) = x0) -> exists y1 : nat, x0 = (S (Nat.add x1 y1)))) -> (forall y1 : nat, forall y2 : nat, (Nat.add y1 y2) = (Nat.add y2 y1)) -> False) x2.
Definition term38 (x0 : nat) (x1 : nat) := fun y0 : nat => (~ (((S (Nat.add y0 x1)) = x0) -> exists y1 : nat, x0 = (S (Nat.add x1 y1)))) -> (forall y1 : nat, forall y2 : nat, (Nat.add y1 y2) = (Nat.add y2 y1)) -> False.
Definition term47 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (~ (((S (Nat.add y2 y0)) = y1) -> exists y3 : nat, y1 = (S (Nat.add y0 y3)))) -> ~ (forall y3 : nat, forall y4 : nat, (Nat.add y3 y4) = (Nat.add y4 y3)).
Definition term46 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (~ (((S (Nat.add y2 y0)) = y1) -> exists y3 : nat, y1 = (S (Nat.add y0 y3)))) -> (forall y3 : nat, forall y4 : nat, (Nat.add y3 y4) = (Nat.add y4 y3)) -> False.
Definition term95 (x0 : nat) (x1 : nat) := ((S (Nat.add x1 x0)) = (S (Nat.add x0 x1))) -> False.
Definition term94 (x0 : nat) (x1 : nat) (x2 : nat) := ((S (Nat.add x0 x1)) = (S (Nat.add x1 x2))) -> False.
Definition term20 (x0 : nat) (x1 : nat) := fun y0 : nat => (NUMERAL x0) = (Nat.add (NUMERAL x1) (S y0)).
Definition term89 (x0 : nat) (x1 : nat) := imp (~ (~ (x0 = x1))).
Definition term4 (x0 : nat) := forall y0 : nat, (Nat.add x0 (S y0)) = (S (Nat.add x0 y0)).
