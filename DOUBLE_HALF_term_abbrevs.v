Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term62 (x0 : nat) (x1 : nat) := ((x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) -> ((Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.div x0 (NUMERAL (BIT0 (BIT1 0))))) = x0) = True) -> ((x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) -> (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.div x0 (NUMERAL (BIT0 (BIT1 0))))) = x0) = ((x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) -> True).
Definition term37 (x0 : nat) := imp (exists y0 : nat, (fun y1 : nat => x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) y0).
Definition term63 (x0 : nat) (x1 : nat) := (x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) -> True.
Definition term99 (x0 : nat) := Nat.mul (Nat.div x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term10 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := forall y0 : a0, (x0 y0) -> x1.
Definition term35 (x0 : nat) := fun y0 : nat => (fun y1 : nat => x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) y0.
Definition term66 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term108 := fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even y0) -> (Nat.mul (Nat.div y0 (NUMERAL (BIT0 (BIT1 0)))) (NUMERAL (BIT0 (BIT1 0)))) = y0.
Definition term68 := fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even y0) -> (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.div y0 (NUMERAL (BIT0 (BIT1 0))))) = y0.
Definition term57 (x0 : nat) := Nat.div x0 (NUMERAL (BIT0 (BIT1 0))).
Definition term77 (x0 : nat) (x1 : Prop) := ((Coq.Arith.PeanoNat.Nat.Even x0) = (exists y0 : nat, x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0))) -> ((exists y0 : nat, x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) -> ((Nat.mul (Nat.div x0 (NUMERAL (BIT0 (BIT1 0)))) (NUMERAL (BIT0 (BIT1 0)))) = x0) = x1) -> ((Coq.Arith.PeanoNat.Nat.Even x0) -> (Nat.mul (Nat.div x0 (NUMERAL (BIT0 (BIT1 0)))) (NUMERAL (BIT0 (BIT1 0)))) = x0) = ((exists y0 : nat, x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) -> x1).
Definition term22 (x0 : nat) (x1 : Prop) := ((Coq.Arith.PeanoNat.Nat.Even x0) = (exists y0 : nat, x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0))) -> ((exists y0 : nat, x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) -> ((Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.div x0 (NUMERAL (BIT0 (BIT1 0))))) = x0) = x1) -> ((Coq.Arith.PeanoNat.Nat.Even x0) -> (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.div x0 (NUMERAL (BIT0 (BIT1 0))))) = x0) = ((exists y0 : nat, x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) -> x1).
Definition term4 (x0 : nat) := (fun y0 : nat => (Nat.div (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) (NUMERAL (BIT0 (BIT1 0)))) = y0) x0.
Definition term11 (x0 : nat) := (fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even y0) = (exists y1 : nat, y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) x0.
Definition term115 (x0 : nat) (x1 : nat) := (x0 = (Nat.mul x1 (NUMERAL (BIT0 (BIT1 0))))) -> True.
Definition term83 (x0 : nat) := (exists y0 : nat, (fun y1 : nat => x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) y0) -> (Nat.mul (Nat.div x0 (NUMERAL (BIT0 (BIT1 0)))) (NUMERAL (BIT0 (BIT1 0)))) = x0.
Definition term30 (x0 : nat) := (exists y0 : nat, (fun y1 : nat => x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) y0) -> (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.div x0 (NUMERAL (BIT0 (BIT1 0))))) = x0.
Definition term106 (x0 : nat) := fun y0 : nat => (x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) -> (Nat.mul y0 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0).
Definition term38 (x0 : nat) := imp (exists y0 : nat, x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)).
Definition term55 (x0 : nat) := Nat.div (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0).
Definition term104 (x0 : nat) (x1 : nat) := ((x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) -> ((Nat.mul (Nat.div x0 (NUMERAL (BIT0 (BIT1 0)))) (NUMERAL (BIT0 (BIT1 0)))) = x0) = ((Nat.mul x1 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1))) -> ((x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) -> (Nat.mul (Nat.div x0 (NUMERAL (BIT0 (BIT1 0)))) (NUMERAL (BIT0 (BIT1 0)))) = x0) = ((x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) -> (Nat.mul x1 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)).
Definition term105 (x0 : nat) (x1 : nat) := (x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) -> (Nat.mul x1 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1).
Definition term72 (x0 : nat) := Nat.mul (Nat.div x0 (NUMERAL (BIT0 (BIT1 0)))) (NUMERAL (BIT0 (BIT1 0))).
Definition term88 (x0 : nat) (x1 : nat) := (x1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) -> (Nat.mul (Nat.div x1 (NUMERAL (BIT0 (BIT1 0)))) (NUMERAL (BIT0 (BIT1 0)))) = x1.
Definition term44 (x0 : nat) (x1 : nat) := (x1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) -> (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.div x1 (NUMERAL (BIT0 (BIT1 0))))) = x1.
Definition term75 (x0 : nat) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => ((Coq.Arith.PeanoNat.Nat.Even x0) = x1) -> (x1 -> ((Nat.mul (Nat.div x0 (NUMERAL (BIT0 (BIT1 0)))) (NUMERAL (BIT0 (BIT1 0)))) = x0) = y0) -> ((Coq.Arith.PeanoNat.Nat.Even x0) -> (Nat.mul (Nat.div x0 (NUMERAL (BIT0 (BIT1 0)))) (NUMERAL (BIT0 (BIT1 0)))) = x0) = (x1 -> y0)) x2.
Definition term20 (x0 : nat) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => ((Coq.Arith.PeanoNat.Nat.Even x0) = x1) -> (x1 -> ((Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.div x0 (NUMERAL (BIT0 (BIT1 0))))) = x0) = y0) -> ((Coq.Arith.PeanoNat.Nat.Even x0) -> (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.div x0 (NUMERAL (BIT0 (BIT1 0))))) = x0) = (x1 -> y0)) x2.
Definition term3 := forall y0 : nat, (Nat.div (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) (NUMERAL (BIT0 (BIT1 0)))) = y0.
Definition term13 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term82 (x0 : nat) := (exists y0 : nat, x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) -> (Nat.mul (Nat.div x0 (NUMERAL (BIT0 (BIT1 0)))) (NUMERAL (BIT0 (BIT1 0)))) = x0.
Definition term27 (x0 : nat) := (exists y0 : nat, x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) -> (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.div x0 (NUMERAL (BIT0 (BIT1 0))))) = x0.
Definition term58 := Nat.mul (NUMERAL (BIT0 (BIT1 0))).
Definition term103 (x0 : nat) (x1 : nat) := (x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) -> ((Nat.mul (Nat.div x0 (NUMERAL (BIT0 (BIT1 0)))) (NUMERAL (BIT0 (BIT1 0)))) = x0) = ((Nat.mul x1 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)).
Definition term34 (x0 : nat) := Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0.
Definition term102 (x0 : nat) := @eq nat (Nat.mul x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term97 (x0 : nat) (x1 : nat) (x2 : Prop) := ((x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) = (x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1))) -> ((x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) -> ((Nat.mul (Nat.div x0 (NUMERAL (BIT0 (BIT1 0)))) (NUMERAL (BIT0 (BIT1 0)))) = x0) = x2) -> ((x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) -> (Nat.mul (Nat.div x0 (NUMERAL (BIT0 (BIT1 0)))) (NUMERAL (BIT0 (BIT1 0)))) = x0) = ((x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) -> x2).
Definition term53 (x0 : nat) (x1 : nat) (x2 : Prop) := ((x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) = (x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1))) -> ((x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) -> ((Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.div x0 (NUMERAL (BIT0 (BIT1 0))))) = x0) = x2) -> ((x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) -> (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.div x0 (NUMERAL (BIT0 (BIT1 0))))) = x0) = ((x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) -> x2).
Definition term60 (x0 : nat) := @eq nat (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0).
Definition term87 (x0 : nat) (x1 : nat) := ((fun y0 : nat => x1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) x0) -> (Nat.mul (Nat.div x1 (NUMERAL (BIT0 (BIT1 0)))) (NUMERAL (BIT0 (BIT1 0)))) = x1.
Definition term43 (x0 : nat) (x1 : nat) := ((fun y0 : nat => x1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) x0) -> (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.div x1 (NUMERAL (BIT0 (BIT1 0))))) = x1.
Definition term70 := and (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even y0) -> (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.div y0 (NUMERAL (BIT0 (BIT1 0))))) = y0).
Definition term113 := True /\ (forall y0 : nat, forall y1 : nat, (y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) -> (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)).
Definition term8 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (fun y0 : Prop => ((exists y1 : a0, x0 y1) -> y0) = (forall y1 : a0, (x0 y1) -> y0)) x1.
Definition term80 (x0 : nat) := ((exists y0 : nat, x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) -> ((Nat.mul (Nat.div x0 (NUMERAL (BIT0 (BIT1 0)))) (NUMERAL (BIT0 (BIT1 0)))) = x0) = ((Nat.mul (Nat.div x0 (NUMERAL (BIT0 (BIT1 0)))) (NUMERAL (BIT0 (BIT1 0)))) = x0)) -> ((Coq.Arith.PeanoNat.Nat.Even x0) -> (Nat.mul (Nat.div x0 (NUMERAL (BIT0 (BIT1 0)))) (NUMERAL (BIT0 (BIT1 0)))) = x0) = ((exists y0 : nat, x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) -> (Nat.mul (Nat.div x0 (NUMERAL (BIT0 (BIT1 0)))) (NUMERAL (BIT0 (BIT1 0)))) = x0).
Definition term25 (x0 : nat) := ((exists y0 : nat, x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) -> ((Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.div x0 (NUMERAL (BIT0 (BIT1 0))))) = x0) = ((Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.div x0 (NUMERAL (BIT0 (BIT1 0))))) = x0)) -> ((Coq.Arith.PeanoNat.Nat.Even x0) -> (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.div x0 (NUMERAL (BIT0 (BIT1 0))))) = x0) = ((exists y0 : nat, x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) -> (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.div x0 (NUMERAL (BIT0 (BIT1 0))))) = x0).
Definition term91 (x0 : nat) := forall y0 : nat, (x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) -> (Nat.mul (Nat.div x0 (NUMERAL (BIT0 (BIT1 0)))) (NUMERAL (BIT0 (BIT1 0)))) = x0.
Definition term47 (x0 : nat) := forall y0 : nat, (x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) -> (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.div x0 (NUMERAL (BIT0 (BIT1 0))))) = x0.
Definition term111 := forall y0 : nat, forall y1 : nat, (y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) -> (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1).
Definition term95 (x0 : nat) (x1 : nat) (x2 : Prop) (x3 : Prop) := (fun y0 : Prop => ((x1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) = x2) -> (x2 -> ((Nat.mul (Nat.div x1 (NUMERAL (BIT0 (BIT1 0)))) (NUMERAL (BIT0 (BIT1 0)))) = x1) = y0) -> ((x1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) -> (Nat.mul (Nat.div x1 (NUMERAL (BIT0 (BIT1 0)))) (NUMERAL (BIT0 (BIT1 0)))) = x1) = (x2 -> y0)) x3.
Definition term51 (x0 : nat) (x1 : nat) (x2 : Prop) (x3 : Prop) := (fun y0 : Prop => ((x1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) = x2) -> (x2 -> ((Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.div x1 (NUMERAL (BIT0 (BIT1 0))))) = x1) = y0) -> ((x1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) -> (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.div x1 (NUMERAL (BIT0 (BIT1 0))))) = x1) = (x2 -> y0)) x3.
Definition term65 := forall y0 : nat, True.
Definition term28 (x0 : nat -> Prop) (x1 : Prop) := (exists y0 : nat, x0 y0) -> x1.
Definition term12 (x0 : nat) := exists y0 : nat, x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0).
Definition term41 (x0 : nat) (x1 : nat) := imp ((fun y0 : nat => x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) x1).
Definition term6 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : Prop, ((exists y2 : a0, y0 y2) -> y1) = (forall y2 : a0, (y0 y2) -> y1)) x0.
Definition term64 := fun y0 : nat => True.
Definition term29 (x0 : nat -> Prop) (x1 : Prop) := forall y0 : nat, (x0 y0) -> x1.
Definition term94 (x0 : nat) (x1 : nat) (x2 : Prop) := forall y0 : Prop, ((x1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) = x2) -> (x2 -> ((Nat.mul (Nat.div x1 (NUMERAL (BIT0 (BIT1 0)))) (NUMERAL (BIT0 (BIT1 0)))) = x1) = y0) -> ((x1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) -> (Nat.mul (Nat.div x1 (NUMERAL (BIT0 (BIT1 0)))) (NUMERAL (BIT0 (BIT1 0)))) = x1) = (x2 -> y0).
Definition term74 (x0 : nat) (x1 : Prop) := forall y0 : Prop, ((Coq.Arith.PeanoNat.Nat.Even x0) = x1) -> (x1 -> ((Nat.mul (Nat.div x0 (NUMERAL (BIT0 (BIT1 0)))) (NUMERAL (BIT0 (BIT1 0)))) = x0) = y0) -> ((Coq.Arith.PeanoNat.Nat.Even x0) -> (Nat.mul (Nat.div x0 (NUMERAL (BIT0 (BIT1 0)))) (NUMERAL (BIT0 (BIT1 0)))) = x0) = (x1 -> y0).
Definition term50 (x0 : nat) (x1 : nat) (x2 : Prop) := forall y0 : Prop, ((x1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) = x2) -> (x2 -> ((Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.div x1 (NUMERAL (BIT0 (BIT1 0))))) = x1) = y0) -> ((x1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) -> (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.div x1 (NUMERAL (BIT0 (BIT1 0))))) = x1) = (x2 -> y0).
Definition term19 (x0 : nat) (x1 : Prop) := forall y0 : Prop, ((Coq.Arith.PeanoNat.Nat.Even x0) = x1) -> (x1 -> ((Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.div x0 (NUMERAL (BIT0 (BIT1 0))))) = x0) = y0) -> ((Coq.Arith.PeanoNat.Nat.Even x0) -> (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.div x0 (NUMERAL (BIT0 (BIT1 0))))) = x0) = (x1 -> y0).
Definition term14 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term1 (x0 : nat) := forall y0 : nat, (Nat.mul x0 y0) = (Nat.mul y0 x0).
Definition term33 (x0 : nat) (x1 : nat) := (fun y0 : nat => x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) x1.
Definition term36 (x0 : nat) := exists y0 : nat, (fun y1 : nat => x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) y0.
Definition term92 (x0 : nat) (x1 : nat) := forall y0 : Prop, forall y1 : Prop, ((x1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) = y0) -> (y0 -> ((Nat.mul (Nat.div x1 (NUMERAL (BIT0 (BIT1 0)))) (NUMERAL (BIT0 (BIT1 0)))) = x1) = y1) -> ((x1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) -> (Nat.mul (Nat.div x1 (NUMERAL (BIT0 (BIT1 0)))) (NUMERAL (BIT0 (BIT1 0)))) = x1) = (y0 -> y1).
Definition term71 (x0 : nat) := forall y0 : Prop, forall y1 : Prop, ((Coq.Arith.PeanoNat.Nat.Even x0) = y0) -> (y0 -> ((Nat.mul (Nat.div x0 (NUMERAL (BIT0 (BIT1 0)))) (NUMERAL (BIT0 (BIT1 0)))) = x0) = y1) -> ((Coq.Arith.PeanoNat.Nat.Even x0) -> (Nat.mul (Nat.div x0 (NUMERAL (BIT0 (BIT1 0)))) (NUMERAL (BIT0 (BIT1 0)))) = x0) = (y0 -> y1).
Definition term48 (x0 : nat) (x1 : nat) := forall y0 : Prop, forall y1 : Prop, ((x1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) = y0) -> (y0 -> ((Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.div x1 (NUMERAL (BIT0 (BIT1 0))))) = x1) = y1) -> ((x1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) -> (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.div x1 (NUMERAL (BIT0 (BIT1 0))))) = x1) = (y0 -> y1).
Definition term16 (x0 : nat) := forall y0 : Prop, forall y1 : Prop, ((Coq.Arith.PeanoNat.Nat.Even x0) = y0) -> (y0 -> ((Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.div x0 (NUMERAL (BIT0 (BIT1 0))))) = x0) = y1) -> ((Coq.Arith.PeanoNat.Nat.Even x0) -> (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.div x0 (NUMERAL (BIT0 (BIT1 0))))) = x0) = (y0 -> y1).
Definition term15 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term78 (x0 : nat) (x1 : Prop) := ((exists y0 : nat, x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) -> ((Nat.mul (Nat.div x0 (NUMERAL (BIT0 (BIT1 0)))) (NUMERAL (BIT0 (BIT1 0)))) = x0) = x1) -> ((Coq.Arith.PeanoNat.Nat.Even x0) -> (Nat.mul (Nat.div x0 (NUMERAL (BIT0 (BIT1 0)))) (NUMERAL (BIT0 (BIT1 0)))) = x0) = ((exists y0 : nat, x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) -> x1).
Definition term23 (x0 : nat) (x1 : Prop) := ((exists y0 : nat, x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) -> ((Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.div x0 (NUMERAL (BIT0 (BIT1 0))))) = x0) = x1) -> ((Coq.Arith.PeanoNat.Nat.Even x0) -> (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.div x0 (NUMERAL (BIT0 (BIT1 0))))) = x0) = ((exists y0 : nat, x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) -> x1).
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.mul x0 y0) = (Nat.mul y0 x0)) x1.
Definition term56 := NUMERAL (BIT0 (BIT1 0)).
Definition term61 (x0 : nat) (x1 : nat) := (x1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) -> ((Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.div x1 (NUMERAL (BIT0 (BIT1 0))))) = x1) = True.
Definition term112 := (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even y0) -> (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.div y0 (NUMERAL (BIT0 (BIT1 0))))) = y0) /\ (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even y0) -> (Nat.mul (Nat.div y0 (NUMERAL (BIT0 (BIT1 0)))) (NUMERAL (BIT0 (BIT1 0)))) = y0).
Definition term59 (x0 : nat) := @eq nat (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.div x0 (NUMERAL (BIT0 (BIT1 0))))).
Definition term7 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : Prop, ((exists y1 : a0, x0 y1) -> y0) = (forall y1 : a0, (x0 y1) -> y0).
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) x0.
Definition term107 (x0 : nat) := forall y0 : nat, (x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) -> (Nat.mul y0 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0).
Definition term101 (x0 : nat) := @eq nat (Nat.mul (Nat.div x0 (NUMERAL (BIT0 (BIT1 0)))) (NUMERAL (BIT0 (BIT1 0)))).
Definition term96 (x0 : nat) (x1 : nat) (x2 : Prop) (x3 : Prop) := ((x1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) = x2) -> (x2 -> ((Nat.mul (Nat.div x1 (NUMERAL (BIT0 (BIT1 0)))) (NUMERAL (BIT0 (BIT1 0)))) = x1) = x3) -> ((x1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) -> (Nat.mul (Nat.div x1 (NUMERAL (BIT0 (BIT1 0)))) (NUMERAL (BIT0 (BIT1 0)))) = x1) = (x2 -> x3).
Definition term52 (x0 : nat) (x1 : nat) (x2 : Prop) (x3 : Prop) := ((x1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) = x2) -> (x2 -> ((Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.div x1 (NUMERAL (BIT0 (BIT1 0))))) = x1) = x3) -> ((x1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) -> (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.div x1 (NUMERAL (BIT0 (BIT1 0))))) = x1) = (x2 -> x3).
Definition term5 (x0 : nat) := Nat.div (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (NUMERAL (BIT0 (BIT1 0))).
Definition term84 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) y0) -> (Nat.mul (Nat.div x0 (NUMERAL (BIT0 (BIT1 0)))) (NUMERAL (BIT0 (BIT1 0)))) = x0.
Definition term31 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) y0) -> (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.div x0 (NUMERAL (BIT0 (BIT1 0))))) = x0.
Definition term89 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) y0) -> (Nat.mul (Nat.div x0 (NUMERAL (BIT0 (BIT1 0)))) (NUMERAL (BIT0 (BIT1 0)))) = x0.
Definition term45 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) y0) -> (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.div x0 (NUMERAL (BIT0 (BIT1 0))))) = x0.
Definition term9 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) -> x1.
Definition term42 (x0 : nat) (x1 : nat) := imp (x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)).
Definition term32 (x0 : nat) := fun y0 : nat => x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0).
Definition term110 := forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even y0) -> (Nat.mul (Nat.div y0 (NUMERAL (BIT0 (BIT1 0)))) (NUMERAL (BIT0 (BIT1 0)))) = y0.
Definition term69 := forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even y0) -> (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.div y0 (NUMERAL (BIT0 (BIT1 0))))) = y0.
Definition term79 (x0 : nat) := (exists y0 : nat, x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) -> ((Nat.mul (Nat.div x0 (NUMERAL (BIT0 (BIT1 0)))) (NUMERAL (BIT0 (BIT1 0)))) = x0) = ((Nat.mul (Nat.div x0 (NUMERAL (BIT0 (BIT1 0)))) (NUMERAL (BIT0 (BIT1 0)))) = x0).
Definition term24 (x0 : nat) := (exists y0 : nat, x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) -> ((Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.div x0 (NUMERAL (BIT0 (BIT1 0))))) = x0) = ((Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.div x0 (NUMERAL (BIT0 (BIT1 0))))) = x0).
Definition term73 (x0 : nat) (x1 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((Coq.Arith.PeanoNat.Nat.Even x0) = y0) -> (y0 -> ((Nat.mul (Nat.div x0 (NUMERAL (BIT0 (BIT1 0)))) (NUMERAL (BIT0 (BIT1 0)))) = x0) = y1) -> ((Coq.Arith.PeanoNat.Nat.Even x0) -> (Nat.mul (Nat.div x0 (NUMERAL (BIT0 (BIT1 0)))) (NUMERAL (BIT0 (BIT1 0)))) = x0) = (y0 -> y1)) x1.
Definition term18 (x0 : nat) (x1 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((Coq.Arith.PeanoNat.Nat.Even x0) = y0) -> (y0 -> ((Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.div x0 (NUMERAL (BIT0 (BIT1 0))))) = x0) = y1) -> ((Coq.Arith.PeanoNat.Nat.Even x0) -> (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.div x0 (NUMERAL (BIT0 (BIT1 0))))) = x0) = (y0 -> y1)) x1.
Definition term86 (x0 : nat) := @eq Prop ((exists y0 : nat, x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) -> (Nat.mul (Nat.div x0 (NUMERAL (BIT0 (BIT1 0)))) (NUMERAL (BIT0 (BIT1 0)))) = x0).
Definition term85 (x0 : nat) := @eq Prop ((exists y0 : nat, (fun y1 : nat => x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) y0) -> (Nat.mul (Nat.div x0 (NUMERAL (BIT0 (BIT1 0)))) (NUMERAL (BIT0 (BIT1 0)))) = x0).
Definition term40 (x0 : nat) := @eq Prop ((exists y0 : nat, x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) -> (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.div x0 (NUMERAL (BIT0 (BIT1 0))))) = x0).
Definition term39 (x0 : nat) := @eq Prop ((exists y0 : nat, (fun y1 : nat => x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) y0) -> (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.div x0 (NUMERAL (BIT0 (BIT1 0))))) = x0).
Definition term67 (x0 : Prop) := forall y0 : nat, x0.
Definition term76 (x0 : nat) (x1 : Prop) (x2 : Prop) := ((Coq.Arith.PeanoNat.Nat.Even x0) = x1) -> (x1 -> ((Nat.mul (Nat.div x0 (NUMERAL (BIT0 (BIT1 0)))) (NUMERAL (BIT0 (BIT1 0)))) = x0) = x2) -> ((Coq.Arith.PeanoNat.Nat.Even x0) -> (Nat.mul (Nat.div x0 (NUMERAL (BIT0 (BIT1 0)))) (NUMERAL (BIT0 (BIT1 0)))) = x0) = (x1 -> x2).
Definition term21 (x0 : nat) (x1 : Prop) (x2 : Prop) := ((Coq.Arith.PeanoNat.Nat.Even x0) = x1) -> (x1 -> ((Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.div x0 (NUMERAL (BIT0 (BIT1 0))))) = x0) = x2) -> ((Coq.Arith.PeanoNat.Nat.Even x0) -> (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.div x0 (NUMERAL (BIT0 (BIT1 0))))) = x0) = (x1 -> x2).
Definition term17 (x0 : nat) := Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.div x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term98 (x0 : nat) (x1 : nat) (x2 : Prop) := ((x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) -> ((Nat.mul (Nat.div x0 (NUMERAL (BIT0 (BIT1 0)))) (NUMERAL (BIT0 (BIT1 0)))) = x0) = x2) -> ((x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) -> (Nat.mul (Nat.div x0 (NUMERAL (BIT0 (BIT1 0)))) (NUMERAL (BIT0 (BIT1 0)))) = x0) = ((x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) -> x2).
Definition term54 (x0 : nat) (x1 : nat) (x2 : Prop) := ((x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) -> ((Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.div x0 (NUMERAL (BIT0 (BIT1 0))))) = x0) = x2) -> ((x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) -> (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.div x0 (NUMERAL (BIT0 (BIT1 0))))) = x0) = ((x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) -> x2).
Definition term81 (x0 : nat) := (Coq.Arith.PeanoNat.Nat.Even x0) -> (Nat.mul (Nat.div x0 (NUMERAL (BIT0 (BIT1 0)))) (NUMERAL (BIT0 (BIT1 0)))) = x0.
Definition term26 (x0 : nat) := (Coq.Arith.PeanoNat.Nat.Even x0) -> (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.div x0 (NUMERAL (BIT0 (BIT1 0))))) = x0.
Definition term93 (x0 : nat) (x1 : nat) (x2 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((x1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) = y0) -> (y0 -> ((Nat.mul (Nat.div x1 (NUMERAL (BIT0 (BIT1 0)))) (NUMERAL (BIT0 (BIT1 0)))) = x1) = y1) -> ((x1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) -> (Nat.mul (Nat.div x1 (NUMERAL (BIT0 (BIT1 0)))) (NUMERAL (BIT0 (BIT1 0)))) = x1) = (y0 -> y1)) x2.
Definition term49 (x0 : nat) (x1 : nat) (x2 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((x1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) = y0) -> (y0 -> ((Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.div x1 (NUMERAL (BIT0 (BIT1 0))))) = x1) = y1) -> ((x1 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) -> (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.div x1 (NUMERAL (BIT0 (BIT1 0))))) = x1) = (y0 -> y1)) x2.
Definition term114 (x0 : nat) (x1 : nat) := imp (x0 = (Nat.mul x1 (NUMERAL (BIT0 (BIT1 0))))).
Definition term90 (x0 : nat) := fun y0 : nat => (x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) -> (Nat.mul (Nat.div x0 (NUMERAL (BIT0 (BIT1 0)))) (NUMERAL (BIT0 (BIT1 0)))) = x0.
Definition term46 (x0 : nat) := fun y0 : nat => (x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) -> (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.div x0 (NUMERAL (BIT0 (BIT1 0))))) = x0.
Definition term100 (x0 : nat) := Nat.mul x0 (NUMERAL (BIT0 (BIT1 0))).
Definition term109 := fun y0 : nat => forall y1 : nat, (y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) -> (Nat.mul y1 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1).