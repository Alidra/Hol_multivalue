Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term45 (x0 : nat) := @eq nat (BIT0 x0).
Definition term12 := fun y0 : nat => ((Nat.sub 0 y0) = 0) /\ ((Nat.sub y0 0) = y0).
Definition term57 := True /\ ((forall y0 : nat, forall y1 : nat, (Nat.sub (BIT0 y0) (BIT0 y1)) = (BIT0 (Nat.sub y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.sub (BIT0 y0) (BIT1 y1)) = (Nat.pred (BIT0 (Nat.sub y0 y1)))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.sub (BIT1 y0) (BIT0 y1)) = (@COND nat (Peano.le y1 y0) (BIT1 (Nat.sub y0 y1)) 0)) /\ (forall y0 : nat, forall y1 : nat, (Nat.sub (BIT1 y0) (BIT1 y1)) = (BIT0 (Nat.sub y0 y1)))))).
Definition term47 := forall y0 : nat, (Nat.sub (BIT0 y0) 0) = (BIT0 y0).
Definition term58 := (forall y0 : nat, (Nat.sub (BIT0 y0) 0) = (BIT0 y0)) /\ ((forall y0 : nat, (Nat.sub (BIT1 y0) 0) = (BIT1 y0)) /\ ((forall y0 : nat, forall y1 : nat, (Nat.sub (BIT0 y0) (BIT0 y1)) = (BIT0 (Nat.sub y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.sub (BIT0 y0) (BIT1 y1)) = (Nat.pred (BIT0 (Nat.sub y0 y1)))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.sub (BIT1 y0) (BIT0 y1)) = (@COND nat (Peano.le y1 y0) (BIT1 (Nat.sub y0 y1)) 0)) /\ (forall y0 : nat, forall y1 : nat, (Nat.sub (BIT1 y0) (BIT1 y1)) = (BIT0 (Nat.sub y0 y1))))))).
Definition term61 := ((Nat.sub 0 0) = 0) /\ ((forall y0 : nat, (Nat.sub 0 (BIT0 y0)) = 0) /\ ((forall y0 : nat, (Nat.sub 0 (BIT1 y0)) = 0) /\ ((forall y0 : nat, (Nat.sub (BIT0 y0) 0) = (BIT0 y0)) /\ ((forall y0 : nat, (Nat.sub (BIT1 y0) 0) = (BIT1 y0)) /\ ((forall y0 : nat, forall y1 : nat, (Nat.sub (BIT0 y0) (BIT0 y1)) = (BIT0 (Nat.sub y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.sub (BIT0 y0) (BIT1 y1)) = (Nat.pred (BIT0 (Nat.sub y0 y1)))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.sub (BIT1 y0) (BIT0 y1)) = (@COND nat (Peano.le y1 y0) (BIT1 (Nat.sub y0 y1)) 0)) /\ (forall y0 : nat, forall y1 : nat, (Nat.sub (BIT1 y0) (BIT1 y1)) = (BIT0 (Nat.sub y0 y1)))))))))).
Definition term26 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term42 := and (forall y0 : nat, (Nat.sub 0 (BIT1 y0)) = 0).
Definition term37 := and (forall y0 : nat, (Nat.sub 0 (BIT0 y0)) = 0).
Definition term7 (x0 : nat) := @eq nat (Nat.sub x0 (NUMERAL 0)).
Definition term40 := fun y0 : nat => (Nat.sub 0 (BIT1 y0)) = 0.
Definition term35 := fun y0 : nat => (Nat.sub 0 (BIT0 y0)) = 0.
Definition term17 (x0 : nat) := Nat.sub (NUMERAL x0).
Definition term31 := @eq nat (Nat.sub 0 0).
Definition term8 (x0 : nat) := @eq nat (Nat.sub x0 0).
Definition term4 (x0 : nat) := and ((Nat.sub (NUMERAL 0) x0) = (NUMERAL 0)).
Definition term55 := (forall y0 : nat, forall y1 : nat, (Nat.sub (BIT0 y0) (BIT0 y1)) = (BIT0 (Nat.sub y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.sub (BIT0 y0) (BIT1 y1)) = (Nat.pred (BIT0 (Nat.sub y0 y1)))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.sub (BIT1 y0) (BIT0 y1)) = (@COND nat (Peano.le y1 y0) (BIT1 (Nat.sub y0 y1)) 0)) /\ (forall y0 : nat, forall y1 : nat, (Nat.sub (BIT1 y0) (BIT1 y1)) = (BIT0 (Nat.sub y0 y1))))).
Definition term24 (x0 : nat) := forall y0 : nat, (Nat.sub (NUMERAL x0) (NUMERAL y0)) = (NUMERAL (Nat.sub x0 y0)).
Definition term1 (x0 : nat) := Nat.sub (NUMERAL 0) x0.
Definition term21 (x0 : nat) (x1 : nat) := NUMERAL (Nat.sub x0 x1).
Definition term33 (x0 : nat) := Nat.sub 0 (BIT0 x0).
Definition term54 := and (forall y0 : nat, (Nat.sub (BIT1 y0) 0) = (BIT1 y0)).
Definition term48 := and (forall y0 : nat, (Nat.sub (BIT0 y0) 0) = (BIT0 y0)).
Definition term16 (x0 : nat) := (fun y0 : nat => (NUMERAL y0) = y0) x0.
Definition term22 (x0 : nat) := fun y0 : nat => (Nat.sub (NUMERAL x0) (NUMERAL y0)) = (NUMERAL (Nat.sub x0 y0)).
Definition term41 := forall y0 : nat, (Nat.sub 0 (BIT1 y0)) = 0.
Definition term36 := forall y0 : nat, (Nat.sub 0 (BIT0 y0)) = 0.
Definition term29 := forall y0 : nat, forall y1 : nat, (Nat.sub (NUMERAL y0) (NUMERAL y1)) = (NUMERAL (Nat.sub y0 y1)).
Definition term51 (x0 : nat) := @eq nat (BIT1 x0).
Definition term19 (x0 : nat) (x1 : nat) := @eq nat (Nat.sub (NUMERAL x0) (NUMERAL x1)).
Definition term52 := fun y0 : nat => (Nat.sub (BIT1 y0) 0) = (BIT1 y0).
Definition term53 := forall y0 : nat, (Nat.sub (BIT1 y0) 0) = (BIT1 y0).
Definition term25 := forall y0 : nat, True.
Definition term23 := fun y0 : nat => True.
Definition term3 (x0 : nat) := @eq nat (Nat.sub 0 x0).
Definition term30 := and (forall y0 : nat, forall y1 : nat, (Nat.sub (NUMERAL y0) (NUMERAL y1)) = (NUMERAL (Nat.sub y0 y1))).
Definition term0 := Nat.sub (NUMERAL 0).
Definition term49 (x0 : nat) := Nat.sub (BIT1 x0) 0.
Definition term6 (x0 : nat) := Nat.sub x0 (NUMERAL 0).
Definition term11 := fun y0 : nat => ((Nat.sub (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((Nat.sub y0 (NUMERAL 0)) = y0).
Definition term9 (x0 : nat) := ((Nat.sub (NUMERAL 0) x0) = (NUMERAL 0)) /\ ((Nat.sub x0 (NUMERAL 0)) = x0).
Definition term13 := forall y0 : nat, ((Nat.sub (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((Nat.sub y0 (NUMERAL 0)) = y0).
Definition term15 (x0 : nat) := (fun y0 : nat => ((Nat.sub 0 y0) = 0) /\ ((Nat.sub y0 0) = y0)) x0.
Definition term34 (x0 : nat) := @eq nat (Nat.sub 0 (BIT0 x0)).
Definition term20 (x0 : nat) (x1 : nat) := @eq nat (Nat.sub x0 x1).
Definition term2 (x0 : nat) := @eq nat (Nat.sub (NUMERAL 0) x0).
Definition term43 (x0 : nat) := Nat.sub (BIT0 x0) 0.
Definition term5 (x0 : nat) := and ((Nat.sub 0 x0) = 0).
Definition term46 := fun y0 : nat => (Nat.sub (BIT0 y0) 0) = (BIT0 y0).
Definition term10 (x0 : nat) := ((Nat.sub 0 x0) = 0) /\ ((Nat.sub x0 0) = x0).
Definition term27 (x0 : Prop) := forall y0 : nat, x0.
Definition term28 := fun y0 : nat => forall y1 : nat, (Nat.sub (NUMERAL y0) (NUMERAL y1)) = (NUMERAL (Nat.sub y0 y1)).
Definition term60 := (forall y0 : nat, (Nat.sub 0 (BIT0 y0)) = 0) /\ ((forall y0 : nat, (Nat.sub 0 (BIT1 y0)) = 0) /\ ((forall y0 : nat, (Nat.sub (BIT0 y0) 0) = (BIT0 y0)) /\ ((forall y0 : nat, (Nat.sub (BIT1 y0) 0) = (BIT1 y0)) /\ ((forall y0 : nat, forall y1 : nat, (Nat.sub (BIT0 y0) (BIT0 y1)) = (BIT0 (Nat.sub y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.sub (BIT0 y0) (BIT1 y1)) = (Nat.pred (BIT0 (Nat.sub y0 y1)))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.sub (BIT1 y0) (BIT0 y1)) = (@COND nat (Peano.le y1 y0) (BIT1 (Nat.sub y0 y1)) 0)) /\ (forall y0 : nat, forall y1 : nat, (Nat.sub (BIT1 y0) (BIT1 y1)) = (BIT0 (Nat.sub y0 y1))))))))).
Definition term59 := (forall y0 : nat, (Nat.sub 0 (BIT1 y0)) = 0) /\ ((forall y0 : nat, (Nat.sub (BIT0 y0) 0) = (BIT0 y0)) /\ ((forall y0 : nat, (Nat.sub (BIT1 y0) 0) = (BIT1 y0)) /\ ((forall y0 : nat, forall y1 : nat, (Nat.sub (BIT0 y0) (BIT0 y1)) = (BIT0 (Nat.sub y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.sub (BIT0 y0) (BIT1 y1)) = (Nat.pred (BIT0 (Nat.sub y0 y1)))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.sub (BIT1 y0) (BIT0 y1)) = (@COND nat (Peano.le y1 y0) (BIT1 (Nat.sub y0 y1)) 0)) /\ (forall y0 : nat, forall y1 : nat, (Nat.sub (BIT1 y0) (BIT1 y1)) = (BIT0 (Nat.sub y0 y1)))))))).
Definition term18 (x0 : nat) (x1 : nat) := Nat.sub (NUMERAL x0) (NUMERAL x1).
Definition term50 (x0 : nat) := @eq nat (Nat.sub (BIT1 x0) 0).
Definition term44 (x0 : nat) := @eq nat (Nat.sub (BIT0 x0) 0).
Definition term38 (x0 : nat) := Nat.sub 0 (BIT1 x0).
Definition term62 := (forall y0 : nat, forall y1 : nat, (Nat.sub (NUMERAL y0) (NUMERAL y1)) = (NUMERAL (Nat.sub y0 y1))) /\ (((Nat.sub 0 0) = 0) /\ ((forall y0 : nat, (Nat.sub 0 (BIT0 y0)) = 0) /\ ((forall y0 : nat, (Nat.sub 0 (BIT1 y0)) = 0) /\ ((forall y0 : nat, (Nat.sub (BIT0 y0) 0) = (BIT0 y0)) /\ ((forall y0 : nat, (Nat.sub (BIT1 y0) 0) = (BIT1 y0)) /\ ((forall y0 : nat, forall y1 : nat, (Nat.sub (BIT0 y0) (BIT0 y1)) = (BIT0 (Nat.sub y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.sub (BIT0 y0) (BIT1 y1)) = (Nat.pred (BIT0 (Nat.sub y0 y1)))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.sub (BIT1 y0) (BIT0 y1)) = (@COND nat (Peano.le y1 y0) (BIT1 (Nat.sub y0 y1)) 0)) /\ (forall y0 : nat, forall y1 : nat, (Nat.sub (BIT1 y0) (BIT1 y1)) = (BIT0 (Nat.sub y0 y1))))))))))).
Definition term32 := and ((Nat.sub 0 0) = 0).
Definition term56 := (forall y0 : nat, (Nat.sub (BIT1 y0) 0) = (BIT1 y0)) /\ ((forall y0 : nat, forall y1 : nat, (Nat.sub (BIT0 y0) (BIT0 y1)) = (BIT0 (Nat.sub y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.sub (BIT0 y0) (BIT1 y1)) = (Nat.pred (BIT0 (Nat.sub y0 y1)))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.sub (BIT1 y0) (BIT0 y1)) = (@COND nat (Peano.le y1 y0) (BIT1 (Nat.sub y0 y1)) 0)) /\ (forall y0 : nat, forall y1 : nat, (Nat.sub (BIT1 y0) (BIT1 y1)) = (BIT0 (Nat.sub y0 y1)))))).
Definition term39 (x0 : nat) := @eq nat (Nat.sub 0 (BIT1 x0)).
Definition term14 := forall y0 : nat, ((Nat.sub 0 y0) = 0) /\ ((Nat.sub y0 0) = y0).
