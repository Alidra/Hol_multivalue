Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term58 := (forall y0 : nat, (Nat.pow 0 (BIT1 y0)) = 0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.pow (BIT0 y0) (BIT1 y1)) = (Nat.mul (BIT0 y0) (Nat.mul (Nat.pow (BIT0 y0) y1) (Nat.pow (BIT0 y0) y1)))) /\ (forall y0 : nat, forall y1 : nat, (Nat.pow (BIT1 y0) (BIT1 y1)) = (Nat.mul (BIT1 y0) (Nat.mul (Nat.pow (BIT1 y0) y1) (Nat.pow (BIT1 y0) y1))))).
Definition term50 (x0 : nat) := Nat.mul (BIT1 x0).
Definition term70 := (forall y0 : nat, (Nat.pow (BIT0 y0) 0) = (BIT1 0)) /\ ((forall y0 : nat, (Nat.pow (BIT1 y0) 0) = (BIT1 0)) /\ ((forall y0 : nat, (Nat.pow 0 (BIT0 y0)) = (Nat.mul (Nat.pow 0 y0) (Nat.pow 0 y0))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.pow (BIT0 y0) (BIT0 y1)) = (Nat.mul (Nat.pow (BIT0 y0) y1) (Nat.pow (BIT0 y0) y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.pow (BIT1 y0) (BIT0 y1)) = (Nat.mul (Nat.pow (BIT1 y0) y1) (Nat.pow (BIT1 y0) y1))) /\ ((forall y0 : nat, (Nat.pow 0 (BIT1 y0)) = 0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.pow (BIT0 y0) (BIT1 y1)) = (Nat.mul (BIT0 y0) (Nat.mul (Nat.pow (BIT0 y0) y1) (Nat.pow (BIT0 y0) y1)))) /\ (forall y0 : nat, forall y1 : nat, (Nat.pow (BIT1 y0) (BIT1 y1)) = (Nat.mul (BIT1 y0) (Nat.mul (Nat.pow (BIT1 y0) y1) (Nat.pow (BIT1 y0) y1)))))))))).
Definition term68 := (forall y0 : nat, (Nat.pow (BIT1 y0) 0) = (BIT1 0)) /\ ((forall y0 : nat, (Nat.pow 0 (BIT0 y0)) = (Nat.mul (Nat.pow 0 y0) (Nat.pow 0 y0))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.pow (BIT0 y0) (BIT0 y1)) = (Nat.mul (Nat.pow (BIT0 y0) y1) (Nat.pow (BIT0 y0) y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.pow (BIT1 y0) (BIT0 y1)) = (Nat.mul (Nat.pow (BIT1 y0) y1) (Nat.pow (BIT1 y0) y1))) /\ ((forall y0 : nat, (Nat.pow 0 (BIT1 y0)) = 0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.pow (BIT0 y0) (BIT1 y1)) = (Nat.mul (BIT0 y0) (Nat.mul (Nat.pow (BIT0 y0) y1) (Nat.pow (BIT0 y0) y1)))) /\ (forall y0 : nat, forall y1 : nat, (Nat.pow (BIT1 y0) (BIT1 y1)) = (Nat.mul (BIT1 y0) (Nat.mul (Nat.pow (BIT1 y0) y1) (Nat.pow (BIT1 y0) y1))))))))).
Definition term66 := (forall y0 : nat, (Nat.pow 0 (BIT0 y0)) = (Nat.mul (Nat.pow 0 y0) (Nat.pow 0 y0))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.pow (BIT0 y0) (BIT0 y1)) = (Nat.mul (Nat.pow (BIT0 y0) y1) (Nat.pow (BIT0 y0) y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.pow (BIT1 y0) (BIT0 y1)) = (Nat.mul (Nat.pow (BIT1 y0) y1) (Nat.pow (BIT1 y0) y1))) /\ ((forall y0 : nat, (Nat.pow 0 (BIT1 y0)) = 0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.pow (BIT0 y0) (BIT1 y1)) = (Nat.mul (BIT0 y0) (Nat.mul (Nat.pow (BIT0 y0) y1) (Nat.pow (BIT0 y0) y1)))) /\ (forall y0 : nat, forall y1 : nat, (Nat.pow (BIT1 y0) (BIT1 y1)) = (Nat.mul (BIT1 y0) (Nat.mul (Nat.pow (BIT1 y0) y1) (Nat.pow (BIT1 y0) y1)))))))).
Definition term37 (x0 : nat) := @eq nat (Nat.pow (BIT1 x0) 0).
Definition term35 (x0 : nat) := @eq nat (Nat.pow (BIT0 x0) 0).
Definition term14 (x0 : nat) (x1 : nat) := @eq nat (Nat.pow (BIT1 x0) (BIT0 x1)).
Definition term56 := (forall y0 : nat, forall y1 : nat, (Nat.pow (BIT0 y0) (BIT1 y1)) = (Nat.mul (BIT0 y0) (Nat.mul (Nat.pow (BIT0 y0) y1) (Nat.pow (BIT0 y0) y1)))) /\ (forall y0 : nat, forall y1 : nat, (Nat.pow (BIT1 y0) (BIT1 y1)) = (Nat.mul (BIT1 y0) (Nat.mul (Nat.pow (BIT1 y0) y1) (Nat.pow (BIT1 y0) y1)))).
Definition term31 (x0 : nat) (x1 : nat) := Nat.mul (BIT1 x0) (Nat.mul (Nat.pow (BIT1 x0) x1) (Nat.pow (BIT1 x0) x1)).
Definition term0 (x0 : nat) := Nat.pow 0 (BIT0 x0).
Definition term8 (x0 : nat) (x1 : nat) := @eq nat (Nat.pow (BIT0 x0) (BIT0 x1)).
Definition term1 (x0 : nat) := Nat.pow 0 (Nat.add x0 x0).
Definition term51 (x0 : nat) (x1 : nat) := @eq nat (Nat.mul (BIT1 x0) (Nat.mul (Nat.pow (BIT1 x0) x1) (Nat.pow (BIT1 x0) x1))).
Definition term43 (x0 : nat) (x1 : nat) := Nat.pow x0 (S x1).
Definition term40 (x0 : nat) := @eq nat (Nat.mul (Nat.pow 0 x0) (Nat.pow 0 x0)).
Definition term11 (x0 : nat) := Nat.pow (BIT1 x0).
Definition term26 (x0 : nat) (x1 : nat) := Nat.mul (BIT0 x0) (Nat.mul (Nat.pow (BIT0 x0) x1) (Nat.pow (BIT0 x0) x1)).
Definition term54 (x0 : nat) := forall y0 : nat, (Nat.pow (BIT0 x0) (BIT1 y0)) = (Nat.mul (BIT0 x0) (Nat.mul (Nat.pow (BIT0 x0) y0) (Nat.pow (BIT0 x0) y0))).
Definition term52 (x0 : nat) := forall y0 : nat, (Nat.pow (BIT1 x0) (BIT1 y0)) = (Nat.mul (BIT1 x0) (Nat.mul (Nat.pow (BIT1 x0) y0) (Nat.pow (BIT1 x0) y0))).
Definition term7 (x0 : nat) (x1 : nat) := Nat.pow (BIT0 x0) (Nat.add x1 x1).
Definition term13 (x0 : nat) (x1 : nat) := Nat.pow (BIT1 x0) (Nat.add x1 x1).
Definition term61 := (forall y0 : nat, forall y1 : nat, (Nat.pow (BIT1 y0) (BIT0 y1)) = (Nat.mul (Nat.pow (BIT1 y0) y1) (Nat.pow (BIT1 y0) y1))) /\ ((forall y0 : nat, (Nat.pow 0 (BIT1 y0)) = 0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.pow (BIT0 y0) (BIT1 y1)) = (Nat.mul (BIT0 y0) (Nat.mul (Nat.pow (BIT0 y0) y1) (Nat.pow (BIT0 y0) y1)))) /\ (forall y0 : nat, forall y1 : nat, (Nat.pow (BIT1 y0) (BIT1 y1)) = (Nat.mul (BIT1 y0) (Nat.mul (Nat.pow (BIT1 y0) y1) (Nat.pow (BIT1 y0) y1)))))).
Definition term17 (x0 : nat) := S (Nat.add x0 x0).
Definition term38 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.pow x0 (Nat.add x1 x2).
Definition term42 (x0 : nat) (x1 : nat) := @eq nat (Nat.mul (Nat.pow (BIT1 x0) x1) (Nat.pow (BIT1 x0) x1)).
Definition term41 (x0 : nat) (x1 : nat) := @eq nat (Nat.mul (Nat.pow (BIT0 x0) x1) (Nat.pow (BIT0 x0) x1)).
Definition term32 := @eq nat (Nat.pow 0 0).
Definition term27 (x0 : nat) (x1 : nat) := Nat.pow (BIT1 x0) (BIT1 x1).
Definition term57 := forall y0 : nat, (Nat.pow 0 (BIT1 y0)) = 0.
Definition term9 (x0 : nat) (x1 : nat) := @eq nat (Nat.pow (BIT0 x0) (Nat.add x1 x1)).
Definition term63 := forall y0 : nat, forall y1 : nat, (Nat.pow (BIT0 y0) (BIT0 y1)) = (Nat.mul (Nat.pow (BIT0 y0) y1) (Nat.pow (BIT0 y0) y1)).
Definition term60 := forall y0 : nat, forall y1 : nat, (Nat.pow (BIT1 y0) (BIT0 y1)) = (Nat.mul (Nat.pow (BIT1 y0) y1) (Nat.pow (BIT1 y0) y1)).
Definition term55 := forall y0 : nat, forall y1 : nat, (Nat.pow (BIT0 y0) (BIT1 y1)) = (Nat.mul (BIT0 y0) (Nat.mul (Nat.pow (BIT0 y0) y1) (Nat.pow (BIT0 y0) y1))).
Definition term53 := forall y0 : nat, forall y1 : nat, (Nat.pow (BIT1 y0) (BIT1 y1)) = (Nat.mul (BIT1 y0) (Nat.mul (Nat.pow (BIT1 y0) y1) (Nat.pow (BIT1 y0) y1))).
Definition term29 (x0 : nat) (x1 : nat) := @eq nat (Nat.pow (BIT1 x0) (BIT1 x1)).
Definition term24 (x0 : nat) (x1 : nat) := @eq nat (Nat.pow (BIT0 x0) (BIT1 x1)).
Definition term36 (x0 : nat) := Nat.pow (BIT1 x0) 0.
Definition term15 (x0 : nat) (x1 : nat) := @eq nat (Nat.pow (BIT1 x0) (Nat.add x1 x1)).
Definition term25 (x0 : nat) (x1 : nat) := @eq nat (Nat.pow (BIT0 x0) (S (Nat.add x1 x1))).
Definition term48 (x0 : nat) (x1 : nat) := @eq nat (Nat.mul (BIT0 x0) (Nat.mul (Nat.pow (BIT0 x0) x1) (Nat.pow (BIT0 x0) x1))).
Definition term71 := ((Nat.pow 0 0) = (BIT1 0)) /\ ((forall y0 : nat, (Nat.pow (BIT0 y0) 0) = (BIT1 0)) /\ ((forall y0 : nat, (Nat.pow (BIT1 y0) 0) = (BIT1 0)) /\ ((forall y0 : nat, (Nat.pow 0 (BIT0 y0)) = (Nat.mul (Nat.pow 0 y0) (Nat.pow 0 y0))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.pow (BIT0 y0) (BIT0 y1)) = (Nat.mul (Nat.pow (BIT0 y0) y1) (Nat.pow (BIT0 y0) y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.pow (BIT1 y0) (BIT0 y1)) = (Nat.mul (Nat.pow (BIT1 y0) y1) (Nat.pow (BIT1 y0) y1))) /\ ((forall y0 : nat, (Nat.pow 0 (BIT1 y0)) = 0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.pow (BIT0 y0) (BIT1 y1)) = (Nat.mul (BIT0 y0) (Nat.mul (Nat.pow (BIT0 y0) y1) (Nat.pow (BIT0 y0) y1)))) /\ (forall y0 : nat, forall y1 : nat, (Nat.pow (BIT1 y0) (BIT1 y1)) = (Nat.mul (BIT1 y0) (Nat.mul (Nat.pow (BIT1 y0) y1) (Nat.pow (BIT1 y0) y1))))))))))).
Definition term44 (x0 : nat) (x1 : nat) := Nat.mul x0 (Nat.pow x0 x1).
Definition term16 (x0 : nat) (x1 : nat) := Nat.mul (Nat.pow (BIT1 x0) x1) (Nat.pow (BIT1 x0) x1).
Definition term10 (x0 : nat) (x1 : nat) := Nat.mul (Nat.pow (BIT0 x0) x1) (Nat.pow (BIT0 x0) x1).
Definition term45 (x0 : nat) := Nat.mul 0 (Nat.pow 0 (Nat.add x0 x0)).
Definition term34 (x0 : nat) := Nat.pow (BIT0 x0) 0.
Definition term65 := forall y0 : nat, (Nat.pow 0 (BIT0 y0)) = (Nat.mul (Nat.pow 0 y0) (Nat.pow 0 y0)).
Definition term62 (x0 : nat) := forall y0 : nat, (Nat.pow (BIT0 x0) (BIT0 y0)) = (Nat.mul (Nat.pow (BIT0 x0) y0) (Nat.pow (BIT0 x0) y0)).
Definition term59 (x0 : nat) := forall y0 : nat, (Nat.pow (BIT1 x0) (BIT0 y0)) = (Nat.mul (Nat.pow (BIT1 x0) y0) (Nat.pow (BIT1 x0) y0)).
Definition term30 (x0 : nat) (x1 : nat) := @eq nat (Nat.pow (BIT1 x0) (S (Nat.add x1 x1))).
Definition term6 (x0 : nat) (x1 : nat) := Nat.pow (BIT0 x0) (BIT0 x1).
Definition term47 (x0 : nat) := Nat.mul (BIT0 x0).
Definition term5 (x0 : nat) := Nat.pow (BIT0 x0).
Definition term2 (x0 : nat) := @eq nat (Nat.pow 0 (BIT0 x0)).
Definition term64 := (forall y0 : nat, forall y1 : nat, (Nat.pow (BIT0 y0) (BIT0 y1)) = (Nat.mul (Nat.pow (BIT0 y0) y1) (Nat.pow (BIT0 y0) y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.pow (BIT1 y0) (BIT0 y1)) = (Nat.mul (Nat.pow (BIT1 y0) y1) (Nat.pow (BIT1 y0) y1))) /\ ((forall y0 : nat, (Nat.pow 0 (BIT1 y0)) = 0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.pow (BIT0 y0) (BIT1 y1)) = (Nat.mul (BIT0 y0) (Nat.mul (Nat.pow (BIT0 y0) y1) (Nat.pow (BIT0 y0) y1)))) /\ (forall y0 : nat, forall y1 : nat, (Nat.pow (BIT1 y0) (BIT1 y1)) = (Nat.mul (BIT1 y0) (Nat.mul (Nat.pow (BIT1 y0) y1) (Nat.pow (BIT1 y0) y1))))))).
Definition term18 (x0 : nat) := Nat.pow 0 (BIT1 x0).
Definition term20 (x0 : nat) := @eq nat (Nat.pow 0 (BIT1 x0)).
Definition term19 (x0 : nat) := Nat.pow 0 (S (Nat.add x0 x0)).
Definition term23 (x0 : nat) (x1 : nat) := Nat.pow (BIT0 x0) (S (Nat.add x1 x1)).
Definition term12 (x0 : nat) (x1 : nat) := Nat.pow (BIT1 x0) (BIT0 x1).
Definition term69 := forall y0 : nat, (Nat.pow (BIT0 y0) 0) = (BIT1 0).
Definition term67 := forall y0 : nat, (Nat.pow (BIT1 y0) 0) = (BIT1 0).
Definition term22 (x0 : nat) (x1 : nat) := Nat.pow (BIT0 x0) (BIT1 x1).
Definition term21 (x0 : nat) := @eq nat (Nat.pow 0 (S (Nat.add x0 x0))).
Definition term46 (x0 : nat) (x1 : nat) := Nat.mul (BIT0 x0) (Nat.pow (BIT0 x0) (Nat.add x1 x1)).
Definition term39 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.pow x1 x0) (Nat.pow x1 x2).
Definition term49 (x0 : nat) (x1 : nat) := Nat.mul (BIT1 x0) (Nat.pow (BIT1 x0) (Nat.add x1 x1)).
Definition term28 (x0 : nat) (x1 : nat) := Nat.pow (BIT1 x0) (S (Nat.add x1 x1)).
Definition term33 := @eq nat (BIT1 0).
Definition term4 (x0 : nat) := Nat.mul (Nat.pow 0 x0) (Nat.pow 0 x0).
Definition term3 (x0 : nat) := @eq nat (Nat.pow 0 (Nat.add x0 x0)).
