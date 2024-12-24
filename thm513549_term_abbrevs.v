Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term16 (x0 : nat) := ((fun y0 : nat => (Nat.pred (Nat.add y0 y0)) = (@COND nat (y0 = 0) 0 (S (Nat.add (Nat.pred y0) (Nat.pred y0))))) x0) -> (fun y0 : nat => (Nat.pred (Nat.add y0 y0)) = (@COND nat (y0 = 0) 0 (S (Nat.add (Nat.pred y0) (Nat.pred y0))))) (S x0).
Definition term35 := @COND nat ((NUMERAL 0) = 0) 0.
Definition term26 := fun y0 : nat => (fun y1 : nat => (Nat.pred (Nat.add y1 y1)) = (@COND nat (y1 = 0) 0 (S (Nat.add (Nat.pred y1) (Nat.pred y1))))) y0.
Definition term33 := @eq nat (NUMERAL 0).
Definition term58 (x0 : nat) := @COND nat False 0 (S (Nat.add x0 x0)).
Definition term8 (x0 : nat) := (fun y0 : nat => (Nat.pred (Nat.add y0 y0)) = (@COND nat (y0 = 0) 0 (S (Nat.add (Nat.pred y0) (Nat.pred y0))))) x0.
Definition term23 := ((Nat.pred (Nat.add (NUMERAL 0) (NUMERAL 0))) = (@COND nat ((NUMERAL 0) = 0) 0 (S (Nat.add (Nat.pred (NUMERAL 0)) (Nat.pred (NUMERAL 0)))))) /\ (forall y0 : nat, ((Nat.pred (Nat.add y0 y0)) = (@COND nat (y0 = 0) 0 (S (Nat.add (Nat.pred y0) (Nat.pred y0))))) -> (Nat.pred (Nat.add (S y0) (S y0))) = (@COND nat ((S y0) = 0) 0 (S (Nat.add (Nat.pred (S y0)) (Nat.pred (S y0)))))).
Definition term27 := forall y0 : nat, (fun y1 : nat => (Nat.pred (Nat.add y1 y1)) = (@COND nat (y1 = 0) 0 (S (Nat.add (Nat.pred y1) (Nat.pred y1))))) y0.
Definition term52 (x0 : nat) := @eq nat (S (Nat.add x0 x0)).
Definition term49 (x0 : nat) := Nat.pred (S (S (Nat.add x0 x0))).
Definition term22 := ((fun y0 : nat => (Nat.pred (Nat.add y0 y0)) = (@COND nat (y0 = 0) 0 (S (Nat.add (Nat.pred y0) (Nat.pred y0))))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Nat.pred (Nat.add y1 y1)) = (@COND nat (y1 = 0) 0 (S (Nat.add (Nat.pred y1) (Nat.pred y1))))) y0) -> (fun y1 : nat => (Nat.pred (Nat.add y1 y1)) = (@COND nat (y1 = 0) 0 (S (Nat.add (Nat.pred y1) (Nat.pred y1))))) (S y0)).
Definition term1 := (((fun y0 : nat => (Nat.pred (Nat.add y0 y0)) = (@COND nat (y0 = 0) 0 (S (Nat.add (Nat.pred y0) (Nat.pred y0))))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Nat.pred (Nat.add y1 y1)) = (@COND nat (y1 = 0) 0 (S (Nat.add (Nat.pred y1) (Nat.pred y1))))) y0) -> (fun y1 : nat => (Nat.pred (Nat.add y1 y1)) = (@COND nat (y1 = 0) 0 (S (Nat.add (Nat.pred y1) (Nat.pred y1))))) (S y0))) -> forall y0 : nat, (fun y1 : nat => (Nat.pred (Nat.add y1 y1)) = (@COND nat (y1 = 0) 0 (S (Nat.add (Nat.pred y1) (Nat.pred y1))))) y0.
Definition term38 := Nat.add (Nat.pred (NUMERAL 0)) (Nat.pred (NUMERAL 0)).
Definition term0 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term46 (x0 : nat) := Nat.add x0 (S x0).
Definition term24 := imp (((fun y0 : nat => (Nat.pred (Nat.add y0 y0)) = (@COND nat (y0 = 0) 0 (S (Nat.add (Nat.pred y0) (Nat.pred y0))))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Nat.pred (Nat.add y1 y1)) = (@COND nat (y1 = 0) 0 (S (Nat.add (Nat.pred y1) (Nat.pred y1))))) y0) -> (fun y1 : nat => (Nat.pred (Nat.add y1 y1)) = (@COND nat (y1 = 0) 0 (S (Nat.add (Nat.pred y1) (Nat.pred y1))))) (S y0))).
Definition term20 := forall y0 : nat, ((fun y1 : nat => (Nat.pred (Nat.add y1 y1)) = (@COND nat (y1 = 0) 0 (S (Nat.add (Nat.pred y1) (Nat.pred y1))))) y0) -> (fun y1 : nat => (Nat.pred (Nat.add y1 y1)) = (@COND nat (y1 = 0) 0 (S (Nat.add (Nat.pred y1) (Nat.pred y1))))) (S y0).
Definition term32 := @eq nat (Nat.pred (Nat.add (NUMERAL 0) (NUMERAL 0))).
Definition term47 (x0 : nat) := S (Nat.add x0 x0).
Definition term51 (x0 : nat) := @eq nat (Nat.pred (Nat.add (S x0) (S x0))).
Definition term6 := and ((fun y0 : nat => (Nat.pred (Nat.add y0 y0)) = (@COND nat (y0 = 0) 0 (S (Nat.add (Nat.pred y0) (Nat.pred y0))))) (NUMERAL 0)).
Definition term31 := Nat.add (NUMERAL 0) (NUMERAL 0).
Definition term53 (x0 : nat) := @COND nat ((S x0) = 0).
Definition term57 (x0 : nat) := S (Nat.add (Nat.pred (S x0)) (Nat.pred (S x0))).
Definition term43 (x0 : nat) := Nat.add (S x0) (S x0).
Definition term18 := fun y0 : nat => ((fun y1 : nat => (Nat.pred (Nat.add y1 y1)) = (@COND nat (y1 = 0) 0 (S (Nat.add (Nat.pred y1) (Nat.pred y1))))) y0) -> (fun y1 : nat => (Nat.pred (Nat.add y1 y1)) = (@COND nat (y1 = 0) 0 (S (Nat.add (Nat.pred y1) (Nat.pred y1))))) (S y0).
Definition term17 (x0 : nat) := ((Nat.pred (Nat.add x0 x0)) = (@COND nat (x0 = 0) 0 (S (Nat.add (Nat.pred x0) (Nat.pred x0))))) -> (Nat.pred (Nat.add (S x0) (S x0))) = (@COND nat ((S x0) = 0) 0 (S (Nat.add (Nat.pred (S x0)) (Nat.pred (S x0))))).
Definition term42 (x0 : nat) (x1 : nat) := S (Nat.add x0 x1).
Definition term2 := fun y0 : nat => (Nat.pred (Nat.add y0 y0)) = (@COND nat (y0 = 0) 0 (S (Nat.add (Nat.pred y0) (Nat.pred y0)))).
Definition term56 (x0 : nat) := Nat.add (Nat.pred (S x0)) (Nat.pred (S x0)).
Definition term28 := forall y0 : nat, (Nat.pred (Nat.add y0 y0)) = (@COND nat (y0 = 0) 0 (S (Nat.add (Nat.pred y0) (Nat.pred y0)))).
Definition term29 := (((Nat.pred (Nat.add (NUMERAL 0) (NUMERAL 0))) = (@COND nat ((NUMERAL 0) = 0) 0 (S (Nat.add (Nat.pred (NUMERAL 0)) (Nat.pred (NUMERAL 0)))))) /\ (forall y0 : nat, ((Nat.pred (Nat.add y0 y0)) = (@COND nat (y0 = 0) 0 (S (Nat.add (Nat.pred y0) (Nat.pred y0))))) -> (Nat.pred (Nat.add (S y0) (S y0))) = (@COND nat ((S y0) = 0) 0 (S (Nat.add (Nat.pred (S y0)) (Nat.pred (S y0))))))) -> forall y0 : nat, (Nat.pred (Nat.add y0 y0)) = (@COND nat (y0 = 0) 0 (S (Nat.add (Nat.pred y0) (Nat.pred y0)))).
Definition term4 := Nat.pred (Nat.add (NUMERAL 0) (NUMERAL 0)).
Definition term13 (x0 : nat) := (fun y0 : nat => (Nat.pred (Nat.add y0 y0)) = (@COND nat (y0 = 0) 0 (S (Nat.add (Nat.pred y0) (Nat.pred y0))))) (S x0).
Definition term39 := S (Nat.add (Nat.pred (NUMERAL 0)) (Nat.pred (NUMERAL 0))).
Definition term9 (x0 : nat) := Nat.pred (Nat.add x0 x0).
Definition term3 := (fun y0 : nat => (Nat.pred (Nat.add y0 y0)) = (@COND nat (y0 = 0) 0 (S (Nat.add (Nat.pred y0) (Nat.pred y0))))) (NUMERAL 0).
Definition term15 (x0 : nat) := @COND nat ((S x0) = 0) 0 (S (Nat.add (Nat.pred (S x0)) (Nat.pred (S x0)))).
Definition term5 := @COND nat ((NUMERAL 0) = 0) 0 (S (Nat.add (Nat.pred (NUMERAL 0)) (Nat.pred (NUMERAL 0)))).
Definition term40 := @COND nat True 0 (S 0).
Definition term30 := Nat.add (NUMERAL 0).
Definition term14 (x0 : nat) := Nat.pred (Nat.add (S x0) (S x0)).
Definition term36 := Nat.pred (NUMERAL 0).
Definition term10 (x0 : nat) := @COND nat (x0 = 0) 0 (S (Nat.add (Nat.pred x0) (Nat.pred x0))).
Definition term37 := Nat.add (Nat.pred (NUMERAL 0)).
Definition term45 (x0 : nat) (x1 : nat) := Nat.add x0 (S x1).
Definition term7 := and ((Nat.pred (Nat.add (NUMERAL 0) (NUMERAL 0))) = (@COND nat ((NUMERAL 0) = 0) 0 (S (Nat.add (Nat.pred (NUMERAL 0)) (Nat.pred (NUMERAL 0)))))).
Definition term55 (x0 : nat) := Nat.add (Nat.pred (S x0)).
Definition term25 := imp (((Nat.pred (Nat.add (NUMERAL 0) (NUMERAL 0))) = (@COND nat ((NUMERAL 0) = 0) 0 (S (Nat.add (Nat.pred (NUMERAL 0)) (Nat.pred (NUMERAL 0)))))) /\ (forall y0 : nat, ((Nat.pred (Nat.add y0 y0)) = (@COND nat (y0 = 0) 0 (S (Nat.add (Nat.pred y0) (Nat.pred y0))))) -> (Nat.pred (Nat.add (S y0) (S y0))) = (@COND nat ((S y0) = 0) 0 (S (Nat.add (Nat.pred (S y0)) (Nat.pred (S y0))))))).
Definition term21 := forall y0 : nat, ((Nat.pred (Nat.add y0 y0)) = (@COND nat (y0 = 0) 0 (S (Nat.add (Nat.pred y0) (Nat.pred y0))))) -> (Nat.pred (Nat.add (S y0) (S y0))) = (@COND nat ((S y0) = 0) 0 (S (Nat.add (Nat.pred (S y0)) (Nat.pred (S y0))))).
Definition term44 (x0 : nat) := S (Nat.add x0 (S x0)).
Definition term54 (x0 : nat) := @COND nat ((S x0) = 0) 0.
Definition term11 (x0 : nat) := imp ((fun y0 : nat => (Nat.pred (Nat.add y0 y0)) = (@COND nat (y0 = 0) 0 (S (Nat.add (Nat.pred y0) (Nat.pred y0))))) x0).
Definition term12 (x0 : nat) := imp ((Nat.pred (Nat.add x0 x0)) = (@COND nat (x0 = 0) 0 (S (Nat.add (Nat.pred x0) (Nat.pred x0))))).
Definition term34 := @COND nat ((NUMERAL 0) = 0).
Definition term41 (x0 : nat) (x1 : nat) := Nat.add (S x0) x1.
Definition term48 (x0 : nat) := S (S (Nat.add x0 x0)).
Definition term50 (x0 : nat) := Nat.pred (S x0).
Definition term19 := fun y0 : nat => ((Nat.pred (Nat.add y0 y0)) = (@COND nat (y0 = 0) 0 (S (Nat.add (Nat.pred y0) (Nat.pred y0))))) -> (Nat.pred (Nat.add (S y0) (S y0))) = (@COND nat ((S y0) = 0) 0 (S (Nat.add (Nat.pred (S y0)) (Nat.pred (S y0))))).
