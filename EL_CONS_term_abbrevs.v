Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term19 (a0 : Type') (x0 : nat) := (forall y0 : a0, forall y1 : list a0, (@EL a0 x0 (@cons a0 y0 y1)) = (@COND a0 (x0 = (NUMERAL 0)) y0 (@EL a0 (Nat.sub x0 (NUMERAL (BIT1 0))) y1))) -> forall y0 : a0, forall y1 : list a0, (@EL a0 (S x0) (@cons a0 y0 y1)) = (@COND a0 ((S x0) = (NUMERAL 0)) y0 (@EL a0 (Nat.sub (S x0) (NUMERAL (BIT1 0))) y1)).
Definition term40 (a0 : Type') (x0 : a0) := fun y0 : list a0 => (@EL a0 (NUMERAL 0) (@cons a0 x0 y0)) = (@COND a0 ((NUMERAL 0) = (NUMERAL 0)) x0 (@EL a0 (Nat.sub (NUMERAL 0) (NUMERAL (BIT1 0))) y0)).
Definition term34 (a0 : Type') (x0 : a0) (x1 : list a0) := @hd a0 (@cons a0 x0 x1).
Definition term64 (a0 : Type') (x0 : nat) := fun y0 : a0 => forall y1 : list a0, (@EL a0 (S x0) (@cons a0 y0 y1)) = (@COND a0 ((S x0) = (NUMERAL 0)) y0 (@EL a0 (Nat.sub (S x0) (NUMERAL (BIT1 0))) y1)).
Definition term46 (a0 : Type') := fun y0 : a0 => forall y1 : list a0, (@EL a0 (NUMERAL 0) (@cons a0 y0 y1)) = (@COND a0 ((NUMERAL 0) = (NUMERAL 0)) y0 (@EL a0 (Nat.sub (NUMERAL 0) (NUMERAL (BIT1 0))) y1)).
Definition term44 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term54 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : list a0) := @eq a0 (@EL a0 (S x0) (@cons a0 x1 x2)).
Definition term23 (a0 : Type') := forall y0 : nat, (forall y1 : a0, forall y2 : list a0, (@EL a0 y0 (@cons a0 y1 y2)) = (@COND a0 (y0 = (NUMERAL 0)) y1 (@EL a0 (Nat.sub y0 (NUMERAL (BIT1 0))) y2))) -> forall y1 : a0, forall y2 : list a0, (@EL a0 (S y0) (@cons a0 y1 y2)) = (@COND a0 ((S y0) = (NUMERAL 0)) y1 (@EL a0 (Nat.sub (S y0) (NUMERAL (BIT1 0))) y2)).
Definition term49 (a0 : Type') (x0 : nat) (x1 : list a0) := @EL a0 (S x0) x1.
Definition term55 (a0 : Type') (x0 : nat) (x1 : list a0) := @eq a0 (@EL a0 x0 x1).
Definition term32 (a0 : Type') (x0 : list a0) := @EL a0 (NUMERAL 0) x0.
Definition term31 (a0 : Type') := ((forall y0 : a0, forall y1 : list a0, (@EL a0 (NUMERAL 0) (@cons a0 y0 y1)) = (@COND a0 ((NUMERAL 0) = (NUMERAL 0)) y0 (@EL a0 (Nat.sub (NUMERAL 0) (NUMERAL (BIT1 0))) y1))) /\ (forall y0 : nat, (forall y1 : a0, forall y2 : list a0, (@EL a0 y0 (@cons a0 y1 y2)) = (@COND a0 (y0 = (NUMERAL 0)) y1 (@EL a0 (Nat.sub y0 (NUMERAL (BIT1 0))) y2))) -> forall y1 : a0, forall y2 : list a0, (@EL a0 (S y0) (@cons a0 y1 y2)) = (@COND a0 ((S y0) = (NUMERAL 0)) y1 (@EL a0 (Nat.sub (S y0) (NUMERAL (BIT1 0))) y2)))) -> forall y0 : nat, forall y1 : a0, forall y2 : list a0, (@EL a0 y0 (@cons a0 y1 y2)) = (@COND a0 (y0 = (NUMERAL 0)) y1 (@EL a0 (Nat.sub y0 (NUMERAL (BIT1 0))) y2)).
Definition term48 (a0 : Type') := forall y0 : a0, True.
Definition term33 (a0 : Type') (x0 : a0) (x1 : list a0) := @EL a0 (NUMERAL 0) (@cons a0 x0 x1).
Definition term38 (a0 : Type') (x0 : a0) (x1 : list a0) := @COND a0 ((NUMERAL 0) = (NUMERAL 0)) x0 (@EL a0 (Nat.sub (NUMERAL 0) (NUMERAL (BIT1 0))) x1).
Definition term14 (a0 : Type') (x0 : nat) := imp ((fun y0 : nat => forall y1 : a0, forall y2 : list a0, (@EL a0 y0 (@cons a0 y1 y2)) = (@COND a0 (y0 = (NUMERAL 0)) y1 (@EL a0 (Nat.sub y0 (NUMERAL (BIT1 0))) y2))) x0).
Definition term63 (a0 : Type') (x0 : a0) (x1 : nat) := forall y0 : list a0, (@EL a0 (S x1) (@cons a0 x0 y0)) = (@COND a0 ((S x1) = (NUMERAL 0)) x0 (@EL a0 (Nat.sub (S x1) (NUMERAL (BIT1 0))) y0)).
Definition term42 (a0 : Type') (x0 : a0) := forall y0 : list a0, (@EL a0 (NUMERAL 0) (@cons a0 x0 y0)) = (@COND a0 ((NUMERAL 0) = (NUMERAL 0)) x0 (@EL a0 (Nat.sub (NUMERAL 0) (NUMERAL (BIT1 0))) y0)).
Definition term0 (x0 : nat) := (fun y0 : nat => (Nat.sub (S y0) (NUMERAL (BIT1 0))) = y0) x0.
Definition term6 (a0 : Type') := (((fun y0 : nat => forall y1 : a0, forall y2 : list a0, (@EL a0 y0 (@cons a0 y1 y2)) = (@COND a0 (y0 = (NUMERAL 0)) y1 (@EL a0 (Nat.sub y0 (NUMERAL (BIT1 0))) y2))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : a0, forall y3 : list a0, (@EL a0 y1 (@cons a0 y2 y3)) = (@COND a0 (y1 = (NUMERAL 0)) y2 (@EL a0 (Nat.sub y1 (NUMERAL (BIT1 0))) y3))) y0) -> (fun y1 : nat => forall y2 : a0, forall y3 : list a0, (@EL a0 y1 (@cons a0 y2 y3)) = (@COND a0 (y1 = (NUMERAL 0)) y2 (@EL a0 (Nat.sub y1 (NUMERAL (BIT1 0))) y3))) (S y0))) -> forall y0 : nat, (fun y1 : nat => forall y2 : a0, forall y3 : list a0, (@EL a0 y1 (@cons a0 y2 y3)) = (@COND a0 (y1 = (NUMERAL 0)) y2 (@EL a0 (Nat.sub y1 (NUMERAL (BIT1 0))) y3))) y0.
Definition term7 (a0 : Type') := fun y0 : nat => forall y1 : a0, forall y2 : list a0, (@EL a0 y0 (@cons a0 y1 y2)) = (@COND a0 (y0 = (NUMERAL 0)) y1 (@EL a0 (Nat.sub y0 (NUMERAL (BIT1 0))) y2)).
Definition term12 (a0 : Type') (x0 : nat) := (fun y0 : nat => forall y1 : a0, forall y2 : list a0, (@EL a0 y0 (@cons a0 y1 y2)) = (@COND a0 (y0 = (NUMERAL 0)) y1 (@EL a0 (Nat.sub y0 (NUMERAL (BIT1 0))) y2))) x0.
Definition term1 (x0 : nat) := Nat.sub (S x0) (NUMERAL (BIT1 0)).
Definition term5 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term26 (a0 : Type') := imp (((fun y0 : nat => forall y1 : a0, forall y2 : list a0, (@EL a0 y0 (@cons a0 y1 y2)) = (@COND a0 (y0 = (NUMERAL 0)) y1 (@EL a0 (Nat.sub y0 (NUMERAL (BIT1 0))) y2))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : a0, forall y3 : list a0, (@EL a0 y1 (@cons a0 y2 y3)) = (@COND a0 (y1 = (NUMERAL 0)) y2 (@EL a0 (Nat.sub y1 (NUMERAL (BIT1 0))) y3))) y0) -> (fun y1 : nat => forall y2 : a0, forall y3 : list a0, (@EL a0 y1 (@cons a0 y2 y3)) = (@COND a0 (y1 = (NUMERAL 0)) y2 (@EL a0 (Nat.sub y1 (NUMERAL (BIT1 0))) y3))) (S y0))).
Definition term50 (a0 : Type') (x0 : nat) (x1 : list a0) := @EL a0 x0 (@tl a0 x1).
Definition term56 (a0 : Type') (x0 : nat) := @COND a0 ((S x0) = (NUMERAL 0)).
Definition term53 (a0 : Type') (x0 : a0) (x1 : list a0) := @tl a0 (@cons a0 x0 x1).
Definition term22 (a0 : Type') := forall y0 : nat, ((fun y1 : nat => forall y2 : a0, forall y3 : list a0, (@EL a0 y1 (@cons a0 y2 y3)) = (@COND a0 (y1 = (NUMERAL 0)) y2 (@EL a0 (Nat.sub y1 (NUMERAL (BIT1 0))) y3))) y0) -> (fun y1 : nat => forall y2 : a0, forall y3 : list a0, (@EL a0 y1 (@cons a0 y2 y3)) = (@COND a0 (y1 = (NUMERAL 0)) y2 (@EL a0 (Nat.sub y1 (NUMERAL (BIT1 0))) y3))) (S y0).
Definition term43 (a0 : Type') := forall y0 : list a0, True.
Definition term36 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0) (x2 : a0) := @COND a0 (x0 = x0) x1 x2.
Definition term10 (a0 : Type') := and ((fun y0 : nat => forall y1 : a0, forall y2 : list a0, (@EL a0 y0 (@cons a0 y1 y2)) = (@COND a0 (y0 = (NUMERAL 0)) y1 (@EL a0 (Nat.sub y0 (NUMERAL (BIT1 0))) y2))) (NUMERAL 0)).
Definition term16 (a0 : Type') (x0 : nat) := (fun y0 : nat => forall y1 : a0, forall y2 : list a0, (@EL a0 y0 (@cons a0 y1 y2)) = (@COND a0 (y0 = (NUMERAL 0)) y1 (@EL a0 (Nat.sub y0 (NUMERAL (BIT1 0))) y2))) (S x0).
Definition term8 (a0 : Type') := (fun y0 : nat => forall y1 : a0, forall y2 : list a0, (@EL a0 y0 (@cons a0 y1 y2)) = (@COND a0 (y0 = (NUMERAL 0)) y1 (@EL a0 (Nat.sub y0 (NUMERAL (BIT1 0))) y2))) (NUMERAL 0).
Definition term27 (a0 : Type') := imp ((forall y0 : a0, forall y1 : list a0, (@EL a0 (NUMERAL 0) (@cons a0 y0 y1)) = (@COND a0 ((NUMERAL 0) = (NUMERAL 0)) y0 (@EL a0 (Nat.sub (NUMERAL 0) (NUMERAL (BIT1 0))) y1))) /\ (forall y0 : nat, (forall y1 : a0, forall y2 : list a0, (@EL a0 y0 (@cons a0 y1 y2)) = (@COND a0 (y0 = (NUMERAL 0)) y1 (@EL a0 (Nat.sub y0 (NUMERAL (BIT1 0))) y2))) -> forall y1 : a0, forall y2 : list a0, (@EL a0 (S y0) (@cons a0 y1 y2)) = (@COND a0 ((S y0) = (NUMERAL 0)) y1 (@EL a0 (Nat.sub (S y0) (NUMERAL (BIT1 0))) y2)))).
Definition term60 (a0 : Type') (x0 : a0) (x1 : nat) (x2 : list a0) := @COND a0 ((S x1) = (NUMERAL 0)) x0 (@EL a0 (Nat.sub (S x1) (NUMERAL (BIT1 0))) x2).
Definition term37 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : a0) := @COND a0 (x0 = x0) x1 x2.
Definition term30 (a0 : Type') := forall y0 : nat, forall y1 : a0, forall y2 : list a0, (@EL a0 y0 (@cons a0 y1 y2)) = (@COND a0 (y0 = (NUMERAL 0)) y1 (@EL a0 (Nat.sub y0 (NUMERAL (BIT1 0))) y2)).
Definition term47 (a0 : Type') := fun y0 : a0 => True.
Definition term57 (a0 : Type') (x0 : nat) (x1 : a0) := @COND a0 ((S x0) = (NUMERAL 0)) x1.
Definition term15 (a0 : Type') (x0 : nat) := imp (forall y0 : a0, forall y1 : list a0, (@EL a0 x0 (@cons a0 y0 y1)) = (@COND a0 (x0 = (NUMERAL 0)) y0 (@EL a0 (Nat.sub x0 (NUMERAL (BIT1 0))) y1))).
Definition term61 (a0 : Type') (x0 : a0) (x1 : nat) (x2 : list a0) := @COND a0 False x0 (@EL a0 x1 x2).
Definition term3 (x0 : nat) := ~ ((S x0) = (NUMERAL 0)).
Definition term11 (a0 : Type') := and (forall y0 : a0, forall y1 : list a0, (@EL a0 (NUMERAL 0) (@cons a0 y0 y1)) = (@COND a0 ((NUMERAL 0) = (NUMERAL 0)) y0 (@EL a0 (Nat.sub (NUMERAL 0) (NUMERAL (BIT1 0))) y1))).
Definition term39 (a0 : Type') (x0 : list a0) := @EL a0 (Nat.sub (NUMERAL 0) (NUMERAL (BIT1 0))) x0.
Definition term20 (a0 : Type') := fun y0 : nat => ((fun y1 : nat => forall y2 : a0, forall y3 : list a0, (@EL a0 y1 (@cons a0 y2 y3)) = (@COND a0 (y1 = (NUMERAL 0)) y2 (@EL a0 (Nat.sub y1 (NUMERAL (BIT1 0))) y3))) y0) -> (fun y1 : nat => forall y2 : a0, forall y3 : list a0, (@EL a0 y1 (@cons a0 y2 y3)) = (@COND a0 (y1 = (NUMERAL 0)) y2 (@EL a0 (Nat.sub y1 (NUMERAL (BIT1 0))) y3))) (S y0).
Definition term25 (a0 : Type') := (forall y0 : a0, forall y1 : list a0, (@EL a0 (NUMERAL 0) (@cons a0 y0 y1)) = (@COND a0 ((NUMERAL 0) = (NUMERAL 0)) y0 (@EL a0 (Nat.sub (NUMERAL 0) (NUMERAL (BIT1 0))) y1))) /\ (forall y0 : nat, (forall y1 : a0, forall y2 : list a0, (@EL a0 y0 (@cons a0 y1 y2)) = (@COND a0 (y0 = (NUMERAL 0)) y1 (@EL a0 (Nat.sub y0 (NUMERAL (BIT1 0))) y2))) -> forall y1 : a0, forall y2 : list a0, (@EL a0 (S y0) (@cons a0 y1 y2)) = (@COND a0 ((S y0) = (NUMERAL 0)) y1 (@EL a0 (Nat.sub (S y0) (NUMERAL (BIT1 0))) y2))).
Definition term21 (a0 : Type') := fun y0 : nat => (forall y1 : a0, forall y2 : list a0, (@EL a0 y0 (@cons a0 y1 y2)) = (@COND a0 (y0 = (NUMERAL 0)) y1 (@EL a0 (Nat.sub y0 (NUMERAL (BIT1 0))) y2))) -> forall y1 : a0, forall y2 : list a0, (@EL a0 (S y0) (@cons a0 y1 y2)) = (@COND a0 ((S y0) = (NUMERAL 0)) y1 (@EL a0 (Nat.sub (S y0) (NUMERAL (BIT1 0))) y2)).
Definition term28 (a0 : Type') := fun y0 : nat => (fun y1 : nat => forall y2 : a0, forall y3 : list a0, (@EL a0 y1 (@cons a0 y2 y3)) = (@COND a0 (y1 = (NUMERAL 0)) y2 (@EL a0 (Nat.sub y1 (NUMERAL (BIT1 0))) y3))) y0.
Definition term2 (x0 : nat) := (fun y0 : nat => ~ ((S y0) = (NUMERAL 0))) x0.
Definition term62 (a0 : Type') (x0 : a0) (x1 : nat) := fun y0 : list a0 => (@EL a0 (S x1) (@cons a0 x0 y0)) = (@COND a0 ((S x1) = (NUMERAL 0)) x0 (@EL a0 (Nat.sub (S x1) (NUMERAL (BIT1 0))) y0)).
Definition term24 (a0 : Type') := ((fun y0 : nat => forall y1 : a0, forall y2 : list a0, (@EL a0 y0 (@cons a0 y1 y2)) = (@COND a0 (y0 = (NUMERAL 0)) y1 (@EL a0 (Nat.sub y0 (NUMERAL (BIT1 0))) y2))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : a0, forall y3 : list a0, (@EL a0 y1 (@cons a0 y2 y3)) = (@COND a0 (y1 = (NUMERAL 0)) y2 (@EL a0 (Nat.sub y1 (NUMERAL (BIT1 0))) y3))) y0) -> (fun y1 : nat => forall y2 : a0, forall y3 : list a0, (@EL a0 y1 (@cons a0 y2 y3)) = (@COND a0 (y1 = (NUMERAL 0)) y2 (@EL a0 (Nat.sub y1 (NUMERAL (BIT1 0))) y3))) (S y0)).
Definition term35 (a0 : Type') (x0 : a0) (x1 : list a0) := @eq a0 (@EL a0 (NUMERAL 0) (@cons a0 x0 x1)).
Definition term4 (x0 : nat) := (~ ((S x0) = (NUMERAL 0))) -> ((S x0) = (NUMERAL 0)) = False.
Definition term58 (a0 : Type') (x0 : nat) := @EL a0 (Nat.sub (S x0) (NUMERAL (BIT1 0))).
Definition term52 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : list a0) := @EL a0 x0 (@tl a0 (@cons a0 x1 x2)).
Definition term59 (a0 : Type') (x0 : nat) (x1 : list a0) := @EL a0 (Nat.sub (S x0) (NUMERAL (BIT1 0))) x1.
Definition term41 (a0 : Type') := fun y0 : list a0 => True.
Definition term51 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : list a0) := @EL a0 (S x0) (@cons a0 x1 x2).
Definition term45 (a0 : Type') (x0 : Prop) := forall y0 : list a0, x0.
Definition term18 (a0 : Type') (x0 : nat) := ((fun y0 : nat => forall y1 : a0, forall y2 : list a0, (@EL a0 y0 (@cons a0 y1 y2)) = (@COND a0 (y0 = (NUMERAL 0)) y1 (@EL a0 (Nat.sub y0 (NUMERAL (BIT1 0))) y2))) x0) -> (fun y0 : nat => forall y1 : a0, forall y2 : list a0, (@EL a0 y0 (@cons a0 y1 y2)) = (@COND a0 (y0 = (NUMERAL 0)) y1 (@EL a0 (Nat.sub y0 (NUMERAL (BIT1 0))) y2))) (S x0).
Definition term29 (a0 : Type') := forall y0 : nat, (fun y1 : nat => forall y2 : a0, forall y3 : list a0, (@EL a0 y1 (@cons a0 y2 y3)) = (@COND a0 (y1 = (NUMERAL 0)) y2 (@EL a0 (Nat.sub y1 (NUMERAL (BIT1 0))) y3))) y0.
Definition term17 (a0 : Type') (x0 : nat) := forall y0 : a0, forall y1 : list a0, (@EL a0 (S x0) (@cons a0 y0 y1)) = (@COND a0 ((S x0) = (NUMERAL 0)) y0 (@EL a0 (Nat.sub (S x0) (NUMERAL (BIT1 0))) y1)).
Definition term13 (a0 : Type') (x0 : nat) := forall y0 : a0, forall y1 : list a0, (@EL a0 x0 (@cons a0 y0 y1)) = (@COND a0 (x0 = (NUMERAL 0)) y0 (@EL a0 (Nat.sub x0 (NUMERAL (BIT1 0))) y1)).
Definition term9 (a0 : Type') := forall y0 : a0, forall y1 : list a0, (@EL a0 (NUMERAL 0) (@cons a0 y0 y1)) = (@COND a0 ((NUMERAL 0) = (NUMERAL 0)) y0 (@EL a0 (Nat.sub (NUMERAL 0) (NUMERAL (BIT1 0))) y1)).
