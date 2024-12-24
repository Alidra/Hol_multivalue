Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term63 (a0 : Type') (x0 : nat -> a0) (x1 : nat) := @eq nat (@List.length a0 (@list_of_seq a0 x0 (S x1))).
Definition term58 (a0 : Type') (x0 : nat -> a0) (x1 : nat) := @List.length a0 (@cons a0 (x0 x1) (@nil a0)).
Definition term29 := @eq nat (NUMERAL 0).
Definition term44 (a0 : Type') (x0 : list a0) (x1 : list a0) := @List.length a0 (@List.app a0 x0 x1).
Definition term3 (a0 : Type') (x0 : nat -> a0) := (fun y0 : nat => (@List.length a0 (@list_of_seq a0 x0 y0)) = y0) (NUMERAL 0).
Definition term50 (a0 : Type') (x0 : a0) (x1 : list a0) := @List.length a0 (@cons a0 x0 x1).
Definition term52 (a0 : Type') (x0 : nat -> a0) (x1 : nat) := @list_of_seq a0 x0 (S x1).
Definition term60 := S (NUMERAL 0).
Definition term31 := (forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))).
Definition term48 (a0 : Type') (x0 : a0) := forall y0 : list a0, (@List.length a0 (@cons a0 x0 y0)) = (S (@List.length a0 y0)).
Definition term51 (a0 : Type') (x0 : list a0) := S (@List.length a0 x0).
Definition term22 (a0 : Type') (x0 : nat -> a0) := imp (((@List.length a0 (@list_of_seq a0 x0 (NUMERAL 0))) = (NUMERAL 0)) /\ (forall y0 : nat, ((@List.length a0 (@list_of_seq a0 x0 y0)) = y0) -> (@List.length a0 (@list_of_seq a0 x0 (S y0))) = (S y0))).
Definition term55 (a0 : Type') (x0 : nat -> a0) (x1 : nat) := Nat.add (@List.length a0 (@list_of_seq a0 x0 x1)) (@List.length a0 (@cons a0 (x0 x1) (@nil a0))).
Definition term39 (x0 : nat) := (fun y0 : nat => (Nat.add y0 (NUMERAL 0)) = y0) x0.
Definition term8 (a0 : Type') (x0 : nat -> a0) (x1 : nat) := @List.length a0 (@list_of_seq a0 x0 x1).
Definition term27 (a0 : Type') (x0 : nat -> a0) := @list_of_seq a0 x0 (NUMERAL 0).
Definition term1 (a0 : Type') (x0 : nat -> a0) := (((fun y0 : nat => (@List.length a0 (@list_of_seq a0 x0 y0)) = y0) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (@List.length a0 (@list_of_seq a0 x0 y1)) = y1) y0) -> (fun y1 : nat => (@List.length a0 (@list_of_seq a0 x0 y1)) = y1) (S y0))) -> forall y0 : nat, (fun y1 : nat => (@List.length a0 (@list_of_seq a0 x0 y1)) = y1) y0.
Definition term18 (a0 : Type') (x0 : nat -> a0) := forall y0 : nat, ((@List.length a0 (@list_of_seq a0 x0 y0)) = y0) -> (@List.length a0 (@list_of_seq a0 x0 (S y0))) = (S y0).
Definition term0 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term21 (a0 : Type') (x0 : nat -> a0) := imp (((fun y0 : nat => (@List.length a0 (@list_of_seq a0 x0 y0)) = y0) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (@List.length a0 (@list_of_seq a0 x0 y1)) = y1) y0) -> (fun y1 : nat => (@List.length a0 (@list_of_seq a0 x0 y1)) = y1) (S y0))).
Definition term40 (x0 : nat) := Nat.add x0 (NUMERAL 0).
Definition term41 (a0 : Type') (x0 : list a0) := (fun y0 : list a0 => forall y1 : list a0, (@List.length a0 (@List.app a0 y0 y1)) = (Nat.add (@List.length a0 y0) (@List.length a0 y1))) x0.
Definition term17 (a0 : Type') (x0 : nat -> a0) := forall y0 : nat, ((fun y1 : nat => (@List.length a0 (@list_of_seq a0 x0 y1)) = y1) y0) -> (fun y1 : nat => (@List.length a0 (@list_of_seq a0 x0 y1)) = y1) (S y0).
Definition term16 (a0 : Type') (x0 : nat -> a0) := fun y0 : nat => ((@List.length a0 (@list_of_seq a0 x0 y0)) = y0) -> (@List.length a0 (@list_of_seq a0 x0 (S y0))) = (S y0).
Definition term19 (a0 : Type') (x0 : nat -> a0) := ((fun y0 : nat => (@List.length a0 (@list_of_seq a0 x0 y0)) = y0) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (@List.length a0 (@list_of_seq a0 x0 y1)) = y1) y0) -> (fun y1 : nat => (@List.length a0 (@list_of_seq a0 x0 y1)) = y1) (S y0)).
Definition term57 (a0 : Type') (x0 : nat -> a0) (x1 : nat) := Nat.add (@List.length a0 (@list_of_seq a0 x0 x1)).
Definition term23 (a0 : Type') (x0 : nat -> a0) := fun y0 : nat => (fun y1 : nat => (@List.length a0 (@list_of_seq a0 x0 y1)) = y1) y0.
Definition term38 := forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0.
Definition term15 (a0 : Type') (x0 : nat -> a0) := fun y0 : nat => ((fun y1 : nat => (@List.length a0 (@list_of_seq a0 x0 y1)) = y1) y0) -> (fun y1 : nat => (@List.length a0 (@list_of_seq a0 x0 y1)) = y1) (S y0).
Definition term20 (a0 : Type') (x0 : nat -> a0) := ((@List.length a0 (@list_of_seq a0 x0 (NUMERAL 0))) = (NUMERAL 0)) /\ (forall y0 : nat, ((@List.length a0 (@list_of_seq a0 x0 y0)) = y0) -> (@List.length a0 (@list_of_seq a0 x0 (S y0))) = (S y0)).
Definition term37 (x0 : nat) (x1 : nat) := S (Nat.add x0 x1).
Definition term47 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : list a0, (@List.length a0 (@cons a0 y0 y1)) = (S (@List.length a0 y1))) x0.
Definition term32 := forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)).
Definition term24 (a0 : Type') (x0 : nat -> a0) := forall y0 : nat, (fun y1 : nat => (@List.length a0 (@list_of_seq a0 x0 y1)) = y1) y0.
Definition term61 (x0 : nat) := Nat.add x0 (S (NUMERAL 0)).
Definition term12 (a0 : Type') (x0 : nat -> a0) (x1 : nat) := @List.length a0 (@list_of_seq a0 x0 (S x1)).
Definition term45 (a0 : Type') (x0 : list a0) (x1 : list a0) := Nat.add (@List.length a0 x0) (@List.length a0 x1).
Definition term4 (a0 : Type') (x0 : nat -> a0) := @List.length a0 (@list_of_seq a0 x0 (NUMERAL 0)).
Definition term56 (a0 : Type') (x0 : nat -> a0) (x1 : nat) := @cons a0 (x0 x1) (@nil a0).
Definition term6 (a0 : Type') (x0 : nat -> a0) := and ((@List.length a0 (@list_of_seq a0 x0 (NUMERAL 0))) = (NUMERAL 0)).
Definition term49 (a0 : Type') (x0 : a0) (x1 : list a0) := (fun y0 : list a0 => (@List.length a0 (@cons a0 x0 y0)) = (S (@List.length a0 y0))) x1.
Definition term11 (a0 : Type') (x0 : nat -> a0) (x1 : nat) := (fun y0 : nat => (@List.length a0 (@list_of_seq a0 x0 y0)) = y0) (S x1).
Definition term35 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add x0 (S y0)) = (S (Nat.add x0 y0))) x1.
Definition term30 := (forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))).
Definition term65 (a0 : Type') := forall y0 : nat -> a0, forall y1 : nat, (@List.length a0 (@list_of_seq a0 y0 y1)) = y1.
Definition term25 (a0 : Type') (x0 : nat -> a0) := forall y0 : nat, (@List.length a0 (@list_of_seq a0 x0 y0)) = y0.
Definition term64 (x0 : nat) := @eq nat (S x0).
Definition term28 (a0 : Type') (x0 : nat -> a0) := @eq nat (@List.length a0 (@list_of_seq a0 x0 (NUMERAL 0))).
Definition term33 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))) x0.
Definition term59 (a0 : Type') := S (@List.length a0 (@nil a0)).
Definition term14 (a0 : Type') (x0 : nat -> a0) (x1 : nat) := ((@List.length a0 (@list_of_seq a0 x0 x1)) = x1) -> (@List.length a0 (@list_of_seq a0 x0 (S x1))) = (S x1).
Definition term62 (x0 : nat) := S (Nat.add x0 (NUMERAL 0)).
Definition term10 (a0 : Type') (x0 : nat -> a0) (x1 : nat) := imp ((@List.length a0 (@list_of_seq a0 x0 x1)) = x1).
Definition term9 (a0 : Type') (x0 : nat -> a0) (x1 : nat) := imp ((fun y0 : nat => (@List.length a0 (@list_of_seq a0 x0 y0)) = y0) x1).
Definition term13 (a0 : Type') (x0 : nat -> a0) (x1 : nat) := ((fun y0 : nat => (@List.length a0 (@list_of_seq a0 x0 y0)) = y0) x1) -> (fun y0 : nat => (@List.length a0 (@list_of_seq a0 x0 y0)) = y0) (S x1).
Definition term5 (a0 : Type') (x0 : nat -> a0) := and ((fun y0 : nat => (@List.length a0 (@list_of_seq a0 x0 y0)) = y0) (NUMERAL 0)).
Definition term54 (a0 : Type') (x0 : nat -> a0) (x1 : nat) := @List.length a0 (@List.app a0 (@list_of_seq a0 x0 x1) (@cons a0 (x0 x1) (@nil a0))).
Definition term36 (x0 : nat) (x1 : nat) := Nat.add x0 (S x1).
Definition term7 (a0 : Type') (x0 : nat -> a0) (x1 : nat) := (fun y0 : nat => (@List.length a0 (@list_of_seq a0 x0 y0)) = y0) x1.
Definition term43 (a0 : Type') (x0 : list a0) (x1 : list a0) := (fun y0 : list a0 => (@List.length a0 (@List.app a0 x0 y0)) = (Nat.add (@List.length a0 x0) (@List.length a0 y0))) x1.
Definition term2 (a0 : Type') (x0 : nat -> a0) := fun y0 : nat => (@List.length a0 (@list_of_seq a0 x0 y0)) = y0.
Definition term42 (a0 : Type') (x0 : list a0) := forall y0 : list a0, (@List.length a0 (@List.app a0 x0 y0)) = (Nat.add (@List.length a0 x0) (@List.length a0 y0)).
Definition term53 (a0 : Type') (x0 : nat -> a0) (x1 : nat) := @List.app a0 (@list_of_seq a0 x0 x1) (@cons a0 (x0 x1) (@nil a0)).
Definition term46 (a0 : Type') := forall y0 : a0, forall y1 : list a0, (@List.length a0 (@cons a0 y0 y1)) = (S (@List.length a0 y1)).
Definition term26 (a0 : Type') (x0 : nat -> a0) := (((@List.length a0 (@list_of_seq a0 x0 (NUMERAL 0))) = (NUMERAL 0)) /\ (forall y0 : nat, ((@List.length a0 (@list_of_seq a0 x0 y0)) = y0) -> (@List.length a0 (@list_of_seq a0 x0 (S y0))) = (S y0))) -> forall y0 : nat, (@List.length a0 (@list_of_seq a0 x0 y0)) = y0.
Definition term34 (x0 : nat) := forall y0 : nat, (Nat.add x0 (S y0)) = (S (Nat.add x0 y0)).
