Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term37 (a0 : Type') := forall y0 : a0, forall y1 : nat -> a0, forall y2 : nat, (@FCONS a0 y0 y1 (S y2)) = (y1 y2).
Definition term36 (a0 : Type') := forall y0 : a0, forall y1 : nat -> a0, forall y2 : nat, (@ε ((prod nat (prod nat (prod nat (prod nat nat)))) -> a0 -> (nat -> a0) -> nat -> a0) (fun y3 : type1275 a0 => forall y4 : type1672, (forall y5 : a0, forall y6 : nat -> a0, (y3 y4 y5 y6 (NUMERAL 0)) = y5) /\ (forall y5 : a0, forall y6 : nat -> a0, forall y7 : nat, (y3 y4 y5 y6 (S y7)) = (y6 y7))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))))))) y0 y1 (S y2)) = (y1 y2).
Definition term31 (a0 : Type') (x0 : a0) := fun y0 : nat -> a0 => forall y1 : nat, (@FCONS a0 x0 y0 (S y1)) = (y0 y1).
Definition term30 (a0 : Type') (x0 : a0) := fun y0 : nat -> a0 => forall y1 : nat, (@ε ((prod nat (prod nat (prod nat (prod nat nat)))) -> a0 -> (nat -> a0) -> nat -> a0) (fun y2 : type1275 a0 => forall y3 : type1672, (forall y4 : a0, forall y5 : nat -> a0, (y2 y3 y4 y5 (NUMERAL 0)) = y4) /\ (forall y4 : a0, forall y5 : nat -> a0, forall y6 : nat, (y2 y3 y4 y5 (S y6)) = (y5 y6))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))))))) x0 y0 (S y1)) = (y0 y1).
Definition term2 (a0 : Type') := (fun y0 : type1672 => (forall y1 : a0, forall y2 : nat -> a0, (@ε ((prod nat (prod nat (prod nat (prod nat nat)))) -> a0 -> (nat -> a0) -> nat -> a0) (fun y3 : type1275 a0 => forall y4 : type1672, (forall y5 : a0, forall y6 : nat -> a0, (y3 y4 y5 y6 (NUMERAL 0)) = y5) /\ (forall y5 : a0, forall y6 : nat -> a0, forall y7 : nat, (y3 y4 y5 y6 (S y7)) = (y6 y7))) y0 y1 y2 (NUMERAL 0)) = y1) /\ (forall y1 : a0, forall y2 : nat -> a0, forall y3 : nat, (@ε ((prod nat (prod nat (prod nat (prod nat nat)))) -> a0 -> (nat -> a0) -> nat -> a0) (fun y4 : type1275 a0 => forall y5 : type1672, (forall y6 : a0, forall y7 : nat -> a0, (y4 y5 y6 y7 (NUMERAL 0)) = y6) /\ (forall y6 : a0, forall y7 : nat -> a0, forall y8 : nat, (y4 y5 y6 y7 (S y8)) = (y7 y8))) y0 y1 y2 (S y3)) = (y2 y3))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))))))).
Definition term0 (a0 : Type') := (fun y0 : type1275 a0 => forall y1 : type1672, (forall y2 : a0, forall y3 : nat -> a0, (y0 y1 y2 y3 (NUMERAL 0)) = y2) /\ (forall y2 : a0, forall y3 : nat -> a0, forall y4 : nat, (y0 y1 y2 y3 (S y4)) = (y3 y4))) (@ε ((prod nat (prod nat (prod nat (prod nat nat)))) -> a0 -> (nat -> a0) -> nat -> a0) (fun y0 : type1275 a0 => forall y1 : type1672, (forall y2 : a0, forall y3 : nat -> a0, (y0 y1 y2 y3 (NUMERAL 0)) = y2) /\ (forall y2 : a0, forall y3 : nat -> a0, forall y4 : nat, (y0 y1 y2 y3 (S y4)) = (y3 y4)))).
Definition term1 (a0 : Type') := forall y0 : type1672, (forall y1 : a0, forall y2 : nat -> a0, (@ε ((prod nat (prod nat (prod nat (prod nat nat)))) -> a0 -> (nat -> a0) -> nat -> a0) (fun y3 : type1275 a0 => forall y4 : type1672, (forall y5 : a0, forall y6 : nat -> a0, (y3 y4 y5 y6 (NUMERAL 0)) = y5) /\ (forall y5 : a0, forall y6 : nat -> a0, forall y7 : nat, (y3 y4 y5 y6 (S y7)) = (y6 y7))) y0 y1 y2 (NUMERAL 0)) = y1) /\ (forall y1 : a0, forall y2 : nat -> a0, forall y3 : nat, (@ε ((prod nat (prod nat (prod nat (prod nat nat)))) -> a0 -> (nat -> a0) -> nat -> a0) (fun y4 : type1275 a0 => forall y5 : type1672, (forall y6 : a0, forall y7 : nat -> a0, (y4 y5 y6 y7 (NUMERAL 0)) = y6) /\ (forall y6 : a0, forall y7 : nat -> a0, forall y8 : nat, (y4 y5 y6 y7 (S y8)) = (y7 y8))) y0 y1 y2 (S y3)) = (y2 y3)).
Definition term15 (a0 : Type') (x0 : a0) := forall y0 : nat -> a0, (@FCONS a0 x0 y0 (NUMERAL 0)) = x0.
Definition term14 (a0 : Type') (x0 : a0) := forall y0 : nat -> a0, (@ε ((prod nat (prod nat (prod nat (prod nat nat)))) -> a0 -> (nat -> a0) -> nat -> a0) (fun y1 : type1275 a0 => forall y2 : type1672, (forall y3 : a0, forall y4 : nat -> a0, (y1 y2 y3 y4 (NUMERAL 0)) = y3) /\ (forall y3 : a0, forall y4 : nat -> a0, forall y5 : nat, (y1 y2 y3 y4 (S y5)) = (y4 y5))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))))))) x0 y0 (NUMERAL 0)) = x0.
Definition term19 (a0 : Type') := forall y0 : a0, forall y1 : nat -> a0, (@FCONS a0 y0 y1 (NUMERAL 0)) = y0.
Definition term18 (a0 : Type') := forall y0 : a0, forall y1 : nat -> a0, (@ε ((prod nat (prod nat (prod nat (prod nat nat)))) -> a0 -> (nat -> a0) -> nat -> a0) (fun y2 : type1275 a0 => forall y3 : type1672, (forall y4 : a0, forall y5 : nat -> a0, (y2 y3 y4 y5 (NUMERAL 0)) = y4) /\ (forall y4 : a0, forall y5 : nat -> a0, forall y6 : nat, (y2 y3 y4 y5 (S y6)) = (y5 y6))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))))))) y0 y1 (NUMERAL 0)) = y0.
Definition term3 := @pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0))))))))))).
Definition term25 (a0 : Type') (x0 : a0) (x1 : nat -> a0) (x2 : nat) := @eq a0 (@FCONS a0 x0 x1 (S x2)).
Definition term9 (a0 : Type') (x0 : a0) (x1 : nat -> a0) := @FCONS a0 x0 x1 (NUMERAL 0).
Definition term38 (a0 : Type') := (forall y0 : a0, forall y1 : nat -> a0, (@FCONS a0 y0 y1 (NUMERAL 0)) = y0) /\ (forall y0 : a0, forall y1 : nat -> a0, forall y2 : nat, (@FCONS a0 y0 y1 (S y2)) = (y1 y2)).
Definition term4 (a0 : Type') := (forall y0 : a0, forall y1 : nat -> a0, (@ε ((prod nat (prod nat (prod nat (prod nat nat)))) -> a0 -> (nat -> a0) -> nat -> a0) (fun y2 : type1275 a0 => forall y3 : type1672, (forall y4 : a0, forall y5 : nat -> a0, (y2 y3 y4 y5 (NUMERAL 0)) = y4) /\ (forall y4 : a0, forall y5 : nat -> a0, forall y6 : nat, (y2 y3 y4 y5 (S y6)) = (y5 y6))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))))))) y0 y1 (NUMERAL 0)) = y0) /\ (forall y0 : a0, forall y1 : nat -> a0, forall y2 : nat, (@ε ((prod nat (prod nat (prod nat (prod nat nat)))) -> a0 -> (nat -> a0) -> nat -> a0) (fun y3 : type1275 a0 => forall y4 : type1672, (forall y5 : a0, forall y6 : nat -> a0, (y3 y4 y5 y6 (NUMERAL 0)) = y5) /\ (forall y5 : a0, forall y6 : nat -> a0, forall y7 : nat, (y3 y4 y5 y6 (S y7)) = (y6 y7))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))))))) y0 y1 (S y2)) = (y1 y2)).
Definition term27 (a0 : Type') (x0 : a0) (x1 : nat -> a0) := fun y0 : nat => (@FCONS a0 x0 x1 (S y0)) = (x1 y0).
Definition term26 (a0 : Type') (x0 : a0) (x1 : nat -> a0) := fun y0 : nat => (@ε ((prod nat (prod nat (prod nat (prod nat nat)))) -> a0 -> (nat -> a0) -> nat -> a0) (fun y1 : type1275 a0 => forall y2 : type1672, (forall y3 : a0, forall y4 : nat -> a0, (y1 y2 y3 y4 (NUMERAL 0)) = y3) /\ (forall y3 : a0, forall y4 : nat -> a0, forall y5 : nat, (y1 y2 y3 y4 (S y5)) = (y4 y5))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))))))) x0 x1 (S y0)) = (x1 y0).
Definition term10 (a0 : Type') (x0 : a0) (x1 : nat -> a0) := @eq a0 (@ε ((prod nat (prod nat (prod nat (prod nat nat)))) -> a0 -> (nat -> a0) -> nat -> a0) (fun y0 : type1275 a0 => forall y1 : type1672, (forall y2 : a0, forall y3 : nat -> a0, (y0 y1 y2 y3 (NUMERAL 0)) = y2) /\ (forall y2 : a0, forall y3 : nat -> a0, forall y4 : nat, (y0 y1 y2 y3 (S y4)) = (y3 y4))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))))))) x0 x1 (NUMERAL 0)).
Definition term6 (a0 : Type') (x0 : a0) := @ε ((prod nat (prod nat (prod nat (prod nat nat)))) -> a0 -> (nat -> a0) -> nat -> a0) (fun y0 : type1275 a0 => forall y1 : type1672, (forall y2 : a0, forall y3 : nat -> a0, (y0 y1 y2 y3 (NUMERAL 0)) = y2) /\ (forall y2 : a0, forall y3 : nat -> a0, forall y4 : nat, (y0 y1 y2 y3 (S y4)) = (y3 y4))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))))))) x0.
Definition term24 (a0 : Type') (x0 : a0) (x1 : nat -> a0) (x2 : nat) := @eq a0 (@ε ((prod nat (prod nat (prod nat (prod nat nat)))) -> a0 -> (nat -> a0) -> nat -> a0) (fun y0 : type1275 a0 => forall y1 : type1672, (forall y2 : a0, forall y3 : nat -> a0, (y0 y1 y2 y3 (NUMERAL 0)) = y2) /\ (forall y2 : a0, forall y3 : nat -> a0, forall y4 : nat, (y0 y1 y2 y3 (S y4)) = (y3 y4))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))))))) x0 x1 (S x2)).
Definition term13 (a0 : Type') (x0 : a0) := fun y0 : nat -> a0 => (@FCONS a0 x0 y0 (NUMERAL 0)) = x0.
Definition term12 (a0 : Type') (x0 : a0) := fun y0 : nat -> a0 => (@ε ((prod nat (prod nat (prod nat (prod nat nat)))) -> a0 -> (nat -> a0) -> nat -> a0) (fun y1 : type1275 a0 => forall y2 : type1672, (forall y3 : a0, forall y4 : nat -> a0, (y1 y2 y3 y4 (NUMERAL 0)) = y3) /\ (forall y3 : a0, forall y4 : nat -> a0, forall y5 : nat, (y1 y2 y3 y4 (S y5)) = (y4 y5))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))))))) x0 y0 (NUMERAL 0)) = x0.
Definition term22 (a0 : Type') (x0 : a0) (x1 : nat -> a0) (x2 : nat) := @ε ((prod nat (prod nat (prod nat (prod nat nat)))) -> a0 -> (nat -> a0) -> nat -> a0) (fun y0 : type1275 a0 => forall y1 : type1672, (forall y2 : a0, forall y3 : nat -> a0, (y0 y1 y2 y3 (NUMERAL 0)) = y2) /\ (forall y2 : a0, forall y3 : nat -> a0, forall y4 : nat, (y0 y1 y2 y3 (S y4)) = (y3 y4))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))))))) x0 x1 (S x2).
Definition term21 (a0 : Type') := and (forall y0 : a0, forall y1 : nat -> a0, (@FCONS a0 y0 y1 (NUMERAL 0)) = y0).
Definition term20 (a0 : Type') := and (forall y0 : a0, forall y1 : nat -> a0, (@ε ((prod nat (prod nat (prod nat (prod nat nat)))) -> a0 -> (nat -> a0) -> nat -> a0) (fun y2 : type1275 a0 => forall y3 : type1672, (forall y4 : a0, forall y5 : nat -> a0, (y2 y3 y4 y5 (NUMERAL 0)) = y4) /\ (forall y4 : a0, forall y5 : nat -> a0, forall y6 : nat, (y2 y3 y4 y5 (S y6)) = (y5 y6))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))))))) y0 y1 (NUMERAL 0)) = y0).
Definition term33 (a0 : Type') (x0 : a0) := forall y0 : nat -> a0, forall y1 : nat, (@FCONS a0 x0 y0 (S y1)) = (y0 y1).
Definition term32 (a0 : Type') (x0 : a0) := forall y0 : nat -> a0, forall y1 : nat, (@ε ((prod nat (prod nat (prod nat (prod nat nat)))) -> a0 -> (nat -> a0) -> nat -> a0) (fun y2 : type1275 a0 => forall y3 : type1672, (forall y4 : a0, forall y5 : nat -> a0, (y2 y3 y4 y5 (NUMERAL 0)) = y4) /\ (forall y4 : a0, forall y5 : nat -> a0, forall y6 : nat, (y2 y3 y4 y5 (S y6)) = (y5 y6))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))))))) x0 y0 (S y1)) = (y0 y1).
Definition term17 (a0 : Type') := fun y0 : a0 => forall y1 : nat -> a0, (@FCONS a0 y0 y1 (NUMERAL 0)) = y0.
Definition term16 (a0 : Type') := fun y0 : a0 => forall y1 : nat -> a0, (@ε ((prod nat (prod nat (prod nat (prod nat nat)))) -> a0 -> (nat -> a0) -> nat -> a0) (fun y2 : type1275 a0 => forall y3 : type1672, (forall y4 : a0, forall y5 : nat -> a0, (y2 y3 y4 y5 (NUMERAL 0)) = y4) /\ (forall y4 : a0, forall y5 : nat -> a0, forall y6 : nat, (y2 y3 y4 y5 (S y6)) = (y5 y6))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))))))) y0 y1 (NUMERAL 0)) = y0.
Definition term11 (a0 : Type') (x0 : a0) (x1 : nat -> a0) := @eq a0 (@FCONS a0 x0 x1 (NUMERAL 0)).
Definition term7 (a0 : Type') (x0 : a0) (x1 : nat -> a0) := @ε ((prod nat (prod nat (prod nat (prod nat nat)))) -> a0 -> (nat -> a0) -> nat -> a0) (fun y0 : type1275 a0 => forall y1 : type1672, (forall y2 : a0, forall y3 : nat -> a0, (y0 y1 y2 y3 (NUMERAL 0)) = y2) /\ (forall y2 : a0, forall y3 : nat -> a0, forall y4 : nat, (y0 y1 y2 y3 (S y4)) = (y3 y4))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))))))) x0 x1.
Definition term8 (a0 : Type') (x0 : a0) (x1 : nat -> a0) := @ε ((prod nat (prod nat (prod nat (prod nat nat)))) -> a0 -> (nat -> a0) -> nat -> a0) (fun y0 : type1275 a0 => forall y1 : type1672, (forall y2 : a0, forall y3 : nat -> a0, (y0 y1 y2 y3 (NUMERAL 0)) = y2) /\ (forall y2 : a0, forall y3 : nat -> a0, forall y4 : nat, (y0 y1 y2 y3 (S y4)) = (y3 y4))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))))))) x0 x1 (NUMERAL 0).
Definition term5 (a0 : Type') := @ε ((prod nat (prod nat (prod nat (prod nat nat)))) -> a0 -> (nat -> a0) -> nat -> a0) (fun y0 : type1275 a0 => forall y1 : type1672, (forall y2 : a0, forall y3 : nat -> a0, (y0 y1 y2 y3 (NUMERAL 0)) = y2) /\ (forall y2 : a0, forall y3 : nat -> a0, forall y4 : nat, (y0 y1 y2 y3 (S y4)) = (y3 y4))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))))))).
Definition term35 (a0 : Type') := fun y0 : a0 => forall y1 : nat -> a0, forall y2 : nat, (@FCONS a0 y0 y1 (S y2)) = (y1 y2).
Definition term34 (a0 : Type') := fun y0 : a0 => forall y1 : nat -> a0, forall y2 : nat, (@ε ((prod nat (prod nat (prod nat (prod nat nat)))) -> a0 -> (nat -> a0) -> nat -> a0) (fun y3 : type1275 a0 => forall y4 : type1672, (forall y5 : a0, forall y6 : nat -> a0, (y3 y4 y5 y6 (NUMERAL 0)) = y5) /\ (forall y5 : a0, forall y6 : nat -> a0, forall y7 : nat, (y3 y4 y5 y6 (S y7)) = (y6 y7))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))))))) y0 y1 (S y2)) = (y1 y2).
Definition term29 (a0 : Type') (x0 : a0) (x1 : nat -> a0) := forall y0 : nat, (@FCONS a0 x0 x1 (S y0)) = (x1 y0).
Definition term28 (a0 : Type') (x0 : a0) (x1 : nat -> a0) := forall y0 : nat, (@ε ((prod nat (prod nat (prod nat (prod nat nat)))) -> a0 -> (nat -> a0) -> nat -> a0) (fun y1 : type1275 a0 => forall y2 : type1672, (forall y3 : a0, forall y4 : nat -> a0, (y1 y2 y3 y4 (NUMERAL 0)) = y3) /\ (forall y3 : a0, forall y4 : nat -> a0, forall y5 : nat, (y1 y2 y3 y4 (S y5)) = (y4 y5))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))))))) x0 x1 (S y0)) = (x1 y0).
Definition term23 (a0 : Type') (x0 : a0) (x1 : nat -> a0) (x2 : nat) := @FCONS a0 x0 x1 (S x2).