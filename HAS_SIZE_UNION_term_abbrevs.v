Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term36 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : nat) (x3 : nat) := (@FINITE a0 (@UNION a0 x0 x1)) /\ ((@CARD a0 (@UNION a0 x0 x1)) = (Nat.add x2 x3)).
Definition term28 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : nat) (x3 : nat) (x4 : Prop) (x5 : Prop) := (((@HAS_SIZE a0 x0 x2) /\ ((@HAS_SIZE a0 x1 x3) /\ (@DISJOINT a0 x0 x1))) = x4) -> (x4 -> (@HAS_SIZE a0 (@UNION a0 x0 x1) (Nat.add x2 x3)) = x5) -> (((@HAS_SIZE a0 x0 x2) /\ ((@HAS_SIZE a0 x1 x3) /\ (@DISJOINT a0 x0 x1))) -> @HAS_SIZE a0 (@UNION a0 x0 x1) (Nat.add x2 x3)) = (x4 -> x5).
Definition term43 (x0 : nat) (x1 : nat) := @eq nat (Nat.add x0 x1).
Definition term4 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@FINITE a0 x0) /\ ((@FINITE a0 x1) /\ ((@INTER a0 x0 x1) = (@EMPTY a0))).
Definition term52 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term13 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @FINITE a0 (@UNION a0 x0 x1).
Definition term44 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : nat) (x3 : nat) := (((@FINITE a0 x0) /\ ((@CARD a0 x0) = x2)) /\ (((@FINITE a0 x1) /\ ((@CARD a0 x1) = x3)) /\ ((@INTER a0 x0 x1) = (@EMPTY a0)))) -> (@HAS_SIZE a0 (@UNION a0 x0 x1) (Nat.add x2 x3)) = True.
Definition term62 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : nat, forall y3 : nat, ((@HAS_SIZE a0 y0 y2) /\ ((@HAS_SIZE a0 y1 y3) /\ (@DISJOINT a0 y0 y1))) -> @HAS_SIZE a0 (@UNION a0 y0 y1) (Nat.add y2 y3).
Definition term58 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, forall y1 : nat, forall y2 : nat, ((@HAS_SIZE a0 x0 y1) /\ ((@HAS_SIZE a0 y0 y2) /\ (@DISJOINT a0 x0 y0))) -> @HAS_SIZE a0 (@UNION a0 x0 y0) (Nat.add y1 y2).
Definition term12 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@FINITE a0 (@UNION a0 x0 y0)) = ((@FINITE a0 x0) /\ (@FINITE a0 y0))) x1.
Definition term46 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : nat) (x3 : nat) := ((@HAS_SIZE a0 x0 x2) /\ ((@HAS_SIZE a0 x1 x3) /\ (@DISJOINT a0 x0 x1))) -> @HAS_SIZE a0 (@UNION a0 x0 x1) (Nat.add x2 x3).
Definition term60 (a0 : Type') (x0 : Prop) := forall y0 : a0 -> Prop, x0.
Definition term39 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @eq (a0 -> Prop) (@INTER a0 x0 x1).
Definition term14 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@FINITE a0 x0) /\ (@FINITE a0 x1).
Definition term56 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => forall y1 : nat, forall y2 : nat, ((@HAS_SIZE a0 x0 y1) /\ ((@HAS_SIZE a0 y0 y2) /\ (@DISJOINT a0 x0 y0))) -> @HAS_SIZE a0 (@UNION a0 x0 y0) (Nat.add y1 y2).
Definition term30 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := and ((@FINITE a0 x0) /\ ((@CARD a0 x0) = x1)).
Definition term1 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, ((@FINITE a0 x0) /\ ((@FINITE a0 y0) /\ ((@INTER a0 x0 y0) = (@EMPTY a0)))) -> (@CARD a0 (@UNION a0 x0 y0)) = (Nat.add (@CARD a0 x0) (@CARD a0 y0)).
Definition term9 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@DISJOINT a0 x0 y0) = ((@INTER a0 x0 y0) = (@EMPTY a0))) x1.
Definition term29 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := and (@HAS_SIZE a0 x0 x1).
Definition term8 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (@DISJOINT a0 x0 y0) = ((@INTER a0 x0 y0) = (@EMPTY a0)).
Definition term41 (a0 : Type') (x0 : a0 -> Prop) := Nat.add (@CARD a0 x0).
Definition term3 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((@FINITE a0 x0) /\ ((@FINITE a0 x1) /\ ((@INTER a0 x0 x1) = (@EMPTY a0)))) -> (@CARD a0 (@UNION a0 x0 x1)) = (Nat.add (@CARD a0 x0) (@CARD a0 x1)).
Definition term42 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @eq nat (@CARD a0 (@UNION a0 x0 x1)).
Definition term37 (a0 : Type') (x0 : a0 -> Prop) := and (@FINITE a0 x0).
Definition term19 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term24 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : nat) (x3 : nat) := @HAS_SIZE a0 (@UNION a0 x0 x1) (Nat.add x2 x3).
Definition term17 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (fun y0 : nat => (@HAS_SIZE a0 x0 y0) = ((@FINITE a0 x0) /\ ((@CARD a0 x0) = y0))) x1.
Definition term32 (a0 : Type') (x0 : nat) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := ((@FINITE a0 x2) /\ ((@CARD a0 x2) = x0)) /\ ((@INTER a0 x1 x2) = (@EMPTY a0)).
Definition term45 (a0 : Type') (x0 : nat) (x1 : nat) (x2 : a0 -> Prop) (x3 : a0 -> Prop) := ((((@FINITE a0 x2) /\ ((@CARD a0 x2) = x0)) /\ (((@FINITE a0 x3) /\ ((@CARD a0 x3) = x1)) /\ ((@INTER a0 x2 x3) = (@EMPTY a0)))) -> (@HAS_SIZE a0 (@UNION a0 x2 x3) (Nat.add x0 x1)) = True) -> (((@HAS_SIZE a0 x2 x0) /\ ((@HAS_SIZE a0 x3 x1) /\ (@DISJOINT a0 x2 x3))) -> @HAS_SIZE a0 (@UNION a0 x2 x3) (Nat.add x0 x1)) = ((((@FINITE a0 x2) /\ ((@CARD a0 x2) = x0)) /\ (((@FINITE a0 x3) /\ ((@CARD a0 x3) = x1)) /\ ((@INTER a0 x2 x3) = (@EMPTY a0)))) -> True).
Definition term55 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : nat, forall y1 : nat, ((@HAS_SIZE a0 x0 y0) /\ ((@HAS_SIZE a0 x1 y1) /\ (@DISJOINT a0 x0 x1))) -> @HAS_SIZE a0 (@UNION a0 x0 x1) (Nat.add y0 y1).
Definition term33 (a0 : Type') (x0 : nat) (x1 : nat) (x2 : a0 -> Prop) (x3 : a0 -> Prop) := ((@FINITE a0 x2) /\ ((@CARD a0 x2) = x0)) /\ (((@FINITE a0 x3) /\ ((@CARD a0 x3) = x1)) /\ ((@INTER a0 x2 x3) = (@EMPTY a0))).
Definition term51 := forall y0 : nat, True.
Definition term15 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : nat, (@HAS_SIZE a0 y0 y1) = ((@FINITE a0 y0) /\ ((@CARD a0 y0) = y1))) x0.
Definition term10 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (@FINITE a0 (@UNION a0 y0 y1)) = ((@FINITE a0 y0) /\ (@FINITE a0 y1))) x0.
Definition term7 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (@DISJOINT a0 y0 y1) = ((@INTER a0 y0 y1) = (@EMPTY a0))) x0.
Definition term0 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, ((@FINITE a0 y0) /\ ((@FINITE a0 y1) /\ ((@INTER a0 y0 y1) = (@EMPTY a0)))) -> (@CARD a0 (@UNION a0 y0 y1)) = (Nat.add (@CARD a0 y0) (@CARD a0 y1))) x0.
Definition term2 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => ((@FINITE a0 x0) /\ ((@FINITE a0 y0) /\ ((@INTER a0 x0 y0) = (@EMPTY a0)))) -> (@CARD a0 (@UNION a0 x0 y0)) = (Nat.add (@CARD a0 x0) (@CARD a0 y0))) x1.
Definition term49 := fun y0 : nat => True.
Definition term35 (a0 : Type') (x0 : nat) (x1 : nat) (x2 : a0 -> Prop) (x3 : a0 -> Prop) (x4 : Prop) := ((((@FINITE a0 x2) /\ ((@CARD a0 x2) = x0)) /\ (((@FINITE a0 x3) /\ ((@CARD a0 x3) = x1)) /\ ((@INTER a0 x2 x3) = (@EMPTY a0)))) -> (@HAS_SIZE a0 (@UNION a0 x2 x3) (Nat.add x0 x1)) = x4) -> (((@HAS_SIZE a0 x2 x0) /\ ((@HAS_SIZE a0 x3 x1) /\ (@DISJOINT a0 x2 x3))) -> @HAS_SIZE a0 (@UNION a0 x2 x3) (Nat.add x0 x1)) = ((((@FINITE a0 x2) /\ ((@CARD a0 x2) = x0)) /\ (((@FINITE a0 x3) /\ ((@CARD a0 x3) = x1)) /\ ((@INTER a0 x2 x3) = (@EMPTY a0)))) -> x4).
Definition term26 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : nat) (x3 : nat) (x4 : Prop) := forall y0 : Prop, (((@HAS_SIZE a0 x0 x2) /\ ((@HAS_SIZE a0 x1 x3) /\ (@DISJOINT a0 x0 x1))) = x4) -> (x4 -> (@HAS_SIZE a0 (@UNION a0 x0 x1) (Nat.add x2 x3)) = y0) -> (((@HAS_SIZE a0 x0 x2) /\ ((@HAS_SIZE a0 x1 x3) /\ (@DISJOINT a0 x0 x1))) -> @HAS_SIZE a0 (@UNION a0 x0 x1) (Nat.add x2 x3)) = (x4 -> y0).
Definition term20 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term11 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (@FINITE a0 (@UNION a0 x0 y0)) = ((@FINITE a0 x0) /\ (@FINITE a0 y0)).
Definition term57 (a0 : Type') := fun y0 : a0 -> Prop => True.
Definition term38 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := and (@FINITE a0 (@UNION a0 x0 x1)).
Definition term18 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (@FINITE a0 x0) /\ ((@CARD a0 x0) = x1).
Definition term22 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : nat) (x3 : nat) := forall y0 : Prop, forall y1 : Prop, (((@HAS_SIZE a0 x0 x2) /\ ((@HAS_SIZE a0 x1 x3) /\ (@DISJOINT a0 x0 x1))) = y0) -> (y0 -> (@HAS_SIZE a0 (@UNION a0 x0 x1) (Nat.add x2 x3)) = y1) -> (((@HAS_SIZE a0 x0 x2) /\ ((@HAS_SIZE a0 x1 x3) /\ (@DISJOINT a0 x0 x1))) -> @HAS_SIZE a0 (@UNION a0 x0 x1) (Nat.add x2 x3)) = (y0 -> y1).
Definition term21 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term27 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : nat) (x3 : nat) (x4 : Prop) (x5 : Prop) := (fun y0 : Prop => (((@HAS_SIZE a0 x0 x2) /\ ((@HAS_SIZE a0 x1 x3) /\ (@DISJOINT a0 x0 x1))) = x4) -> (x4 -> (@HAS_SIZE a0 (@UNION a0 x0 x1) (Nat.add x2 x3)) = y0) -> (((@HAS_SIZE a0 x0 x2) /\ ((@HAS_SIZE a0 x1 x3) /\ (@DISJOINT a0 x0 x1))) -> @HAS_SIZE a0 (@UNION a0 x0 x1) (Nat.add x2 x3)) = (x4 -> y0)) x5.
Definition term23 (a0 : Type') (x0 : nat) (x1 : nat) (x2 : a0 -> Prop) (x3 : a0 -> Prop) := (@HAS_SIZE a0 x2 x0) /\ ((@HAS_SIZE a0 x3 x1) /\ (@DISJOINT a0 x2 x3)).
Definition term50 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : nat) := forall y0 : nat, ((@HAS_SIZE a0 x0 x2) /\ ((@HAS_SIZE a0 x1 y0) /\ (@DISJOINT a0 x0 x1))) -> @HAS_SIZE a0 (@UNION a0 x0 x1) (Nat.add x2 y0).
Definition term48 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : nat) := fun y0 : nat => ((@HAS_SIZE a0 x0 x2) /\ ((@HAS_SIZE a0 x1 y0) /\ (@DISJOINT a0 x0 x1))) -> @HAS_SIZE a0 (@UNION a0 x0 x1) (Nat.add x2 y0).
Definition term34 (a0 : Type') (x0 : nat) (x1 : nat) (x2 : a0 -> Prop) (x3 : a0 -> Prop) (x4 : Prop) := (((@HAS_SIZE a0 x2 x0) /\ ((@HAS_SIZE a0 x3 x1) /\ (@DISJOINT a0 x2 x3))) = (((@FINITE a0 x2) /\ ((@CARD a0 x2) = x0)) /\ (((@FINITE a0 x3) /\ ((@CARD a0 x3) = x1)) /\ ((@INTER a0 x2 x3) = (@EMPTY a0))))) -> ((((@FINITE a0 x2) /\ ((@CARD a0 x2) = x0)) /\ (((@FINITE a0 x3) /\ ((@CARD a0 x3) = x1)) /\ ((@INTER a0 x2 x3) = (@EMPTY a0)))) -> (@HAS_SIZE a0 (@UNION a0 x2 x3) (Nat.add x0 x1)) = x4) -> (((@HAS_SIZE a0 x2 x0) /\ ((@HAS_SIZE a0 x3 x1) /\ (@DISJOINT a0 x2 x3))) -> @HAS_SIZE a0 (@UNION a0 x2 x3) (Nat.add x0 x1)) = ((((@FINITE a0 x2) /\ ((@CARD a0 x2) = x0)) /\ (((@FINITE a0 x3) /\ ((@CARD a0 x3) = x1)) /\ ((@INTER a0 x2 x3) = (@EMPTY a0)))) -> x4).
Definition term31 (a0 : Type') (x0 : nat) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (@HAS_SIZE a0 x2 x0) /\ (@DISJOINT a0 x1 x2).
Definition term16 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : nat, (@HAS_SIZE a0 x0 y0) = ((@FINITE a0 x0) /\ ((@CARD a0 x0) = y0)).
Definition term40 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@FINITE a0 x1) /\ ((@INTER a0 x0 x1) = (@EMPTY a0)).
Definition term53 (x0 : Prop) := forall y0 : nat, x0.
Definition term5 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @CARD a0 (@UNION a0 x0 x1).
Definition term61 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, forall y2 : nat, forall y3 : nat, ((@HAS_SIZE a0 y0 y2) /\ ((@HAS_SIZE a0 y1 y3) /\ (@DISJOINT a0 y0 y1))) -> @HAS_SIZE a0 (@UNION a0 y0 y1) (Nat.add y2 y3).
Definition term47 (a0 : Type') (x0 : nat) (x1 : nat) (x2 : a0 -> Prop) (x3 : a0 -> Prop) := (((@FINITE a0 x2) /\ ((@CARD a0 x2) = x0)) /\ (((@FINITE a0 x3) /\ ((@CARD a0 x3) = x1)) /\ ((@INTER a0 x2 x3) = (@EMPTY a0)))) -> True.
Definition term6 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := Nat.add (@CARD a0 x0) (@CARD a0 x1).
Definition term25 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : nat) (x3 : nat) (x4 : Prop) := (fun y0 : Prop => forall y1 : Prop, (((@HAS_SIZE a0 x0 x2) /\ ((@HAS_SIZE a0 x1 x3) /\ (@DISJOINT a0 x0 x1))) = y0) -> (y0 -> (@HAS_SIZE a0 (@UNION a0 x0 x1) (Nat.add x2 x3)) = y1) -> (((@HAS_SIZE a0 x0 x2) /\ ((@HAS_SIZE a0 x1 x3) /\ (@DISJOINT a0 x0 x1))) -> @HAS_SIZE a0 (@UNION a0 x0 x1) (Nat.add x2 x3)) = (y0 -> y1)) x4.
Definition term54 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : nat => forall y1 : nat, ((@HAS_SIZE a0 x0 y0) /\ ((@HAS_SIZE a0 x1 y1) /\ (@DISJOINT a0 x0 x1))) -> @HAS_SIZE a0 (@UNION a0 x0 x1) (Nat.add y0 y1).
Definition term59 (a0 : Type') := forall y0 : a0 -> Prop, True.
