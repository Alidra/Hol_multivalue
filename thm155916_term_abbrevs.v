Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term18 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1).
Definition term32 (x0 : nat) := forall y0 : nat, @COND Prop (y0 = (NUMERAL 0)) (((Nat.div x0 y0) = (NUMERAL 0)) /\ ((Nat.modulo x0 y0) = x0)) ((x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0)).
Definition term31 (x0 : nat) := forall y0 : nat, @COND Prop (y0 = (NUMERAL 0)) (((Nat.div x0 y0) = (NUMERAL 0)) /\ ((@ε ((prod nat (prod nat nat)) -> nat -> nat -> nat) (fun y1 : type1306 => forall y2 : type1674, forall y3 : nat, forall y4 : nat, @COND Prop (y4 = (NUMERAL 0)) (((Nat.div y3 y4) = (NUMERAL 0)) /\ ((y1 y2 y3 y4) = y3)) ((y3 = (Nat.add (Nat.mul (Nat.div y3 y4) y4) (y1 y2 y3 y4))) /\ (Peano.lt (y1 y2 y3 y4) y4))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))))) x0 y0) = x0)) ((x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (@ε ((prod nat (prod nat nat)) -> nat -> nat -> nat) (fun y1 : type1306 => forall y2 : type1674, forall y3 : nat, forall y4 : nat, @COND Prop (y4 = (NUMERAL 0)) (((Nat.div y3 y4) = (NUMERAL 0)) /\ ((y1 y2 y3 y4) = y3)) ((y3 = (Nat.add (Nat.mul (Nat.div y3 y4) y4) (y1 y2 y3 y4))) /\ (Peano.lt (y1 y2 y3 y4) y4))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))))) x0 y0))) /\ (Peano.lt (@ε ((prod nat (prod nat nat)) -> nat -> nat -> nat) (fun y1 : type1306 => forall y2 : type1674, forall y3 : nat, forall y4 : nat, @COND Prop (y4 = (NUMERAL 0)) (((Nat.div y3 y4) = (NUMERAL 0)) /\ ((y1 y2 y3 y4) = y3)) ((y3 = (Nat.add (Nat.mul (Nat.div y3 y4) y4) (y1 y2 y3 y4))) /\ (Peano.lt (y1 y2 y3 y4) y4))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))))) x0 y0) y0)).
Definition term8 (x0 : nat) (x1 : nat) := @eq nat (@ε ((prod nat (prod nat nat)) -> nat -> nat -> nat) (fun y0 : type1306 => forall y1 : type1674, forall y2 : nat, forall y3 : nat, @COND Prop (y3 = (NUMERAL 0)) (((Nat.div y2 y3) = (NUMERAL 0)) /\ ((y0 y1 y2 y3) = y2)) ((y2 = (Nat.add (Nat.mul (Nat.div y2 y3) y3) (y0 y1 y2 y3))) /\ (Peano.lt (y0 y1 y2 y3) y3))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))))) x0 x1).
Definition term6 (x0 : nat) := @ε ((prod nat (prod nat nat)) -> nat -> nat -> nat) (fun y0 : type1306 => forall y1 : type1674, forall y2 : nat, forall y3 : nat, @COND Prop (y3 = (NUMERAL 0)) (((Nat.div y2 y3) = (NUMERAL 0)) /\ ((y0 y1 y2 y3) = y2)) ((y2 = (Nat.add (Nat.mul (Nat.div y2 y3) y3) (y0 y1 y2 y3))) /\ (Peano.lt (y0 y1 y2 y3) y3))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))))) x0.
Definition term15 (x0 : nat) (x1 : nat) := @COND Prop (x0 = (NUMERAL 0)) (((Nat.div x1 x0) = (NUMERAL 0)) /\ ((Nat.modulo x1 x0) = x1)).
Definition term14 (x0 : nat) (x1 : nat) := @COND Prop (x0 = (NUMERAL 0)) (((Nat.div x1 x0) = (NUMERAL 0)) /\ ((@ε ((prod nat (prod nat nat)) -> nat -> nat -> nat) (fun y0 : type1306 => forall y1 : type1674, forall y2 : nat, forall y3 : nat, @COND Prop (y3 = (NUMERAL 0)) (((Nat.div y2 y3) = (NUMERAL 0)) /\ ((y0 y1 y2 y3) = y2)) ((y2 = (Nat.add (Nat.mul (Nat.div y2 y3) y3) (y0 y1 y2 y3))) /\ (Peano.lt (y0 y1 y2 y3) y3))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))))) x1 x0) = x1)).
Definition term26 (x0 : nat) (x1 : nat) := (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1).
Definition term23 (x0 : nat) (x1 : nat) := Peano.lt (@ε ((prod nat (prod nat nat)) -> nat -> nat -> nat) (fun y0 : type1306 => forall y1 : type1674, forall y2 : nat, forall y3 : nat, @COND Prop (y3 = (NUMERAL 0)) (((Nat.div y2 y3) = (NUMERAL 0)) /\ ((y0 y1 y2 y3) = y2)) ((y2 = (Nat.add (Nat.mul (Nat.div y2 y3) y3) (y0 y1 y2 y3))) /\ (Peano.lt (y0 y1 y2 y3) y3))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))))) x0 x1) x1.
Definition term16 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul (Nat.div x0 x1) x1).
Definition term9 (x0 : nat) (x1 : nat) := @eq nat (Nat.modulo x0 x1).
Definition term13 (x0 : nat) := @COND Prop (x0 = (NUMERAL 0)).
Definition term22 (x0 : nat) (x1 : nat) := Peano.lt (Nat.modulo x0 x1).
Definition term12 (x0 : nat) (x1 : nat) := ((Nat.div x1 x0) = (NUMERAL 0)) /\ ((Nat.modulo x1 x0) = x1).
Definition term11 (x0 : nat) (x1 : nat) := ((Nat.div x1 x0) = (NUMERAL 0)) /\ ((@ε ((prod nat (prod nat nat)) -> nat -> nat -> nat) (fun y0 : type1306 => forall y1 : type1674, forall y2 : nat, forall y3 : nat, @COND Prop (y3 = (NUMERAL 0)) (((Nat.div y2 y3) = (NUMERAL 0)) /\ ((y0 y1 y2 y3) = y2)) ((y2 = (Nat.add (Nat.mul (Nat.div y2 y3) y3) (y0 y1 y2 y3))) /\ (Peano.lt (y0 y1 y2 y3) y3))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))))) x1 x0) = x1).
Definition term28 (x0 : nat) (x1 : nat) := @COND Prop (x1 = (NUMERAL 0)) (((Nat.div x0 x1) = (NUMERAL 0)) /\ ((Nat.modulo x0 x1) = x0)) ((x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1)).
Definition term27 (x0 : nat) (x1 : nat) := @COND Prop (x1 = (NUMERAL 0)) (((Nat.div x0 x1) = (NUMERAL 0)) /\ ((@ε ((prod nat (prod nat nat)) -> nat -> nat -> nat) (fun y0 : type1306 => forall y1 : type1674, forall y2 : nat, forall y3 : nat, @COND Prop (y3 = (NUMERAL 0)) (((Nat.div y2 y3) = (NUMERAL 0)) /\ ((y0 y1 y2 y3) = y2)) ((y2 = (Nat.add (Nat.mul (Nat.div y2 y3) y3) (y0 y1 y2 y3))) /\ (Peano.lt (y0 y1 y2 y3) y3))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))))) x0 x1) = x0)) ((x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (@ε ((prod nat (prod nat nat)) -> nat -> nat -> nat) (fun y0 : type1306 => forall y1 : type1674, forall y2 : nat, forall y3 : nat, @COND Prop (y3 = (NUMERAL 0)) (((Nat.div y2 y3) = (NUMERAL 0)) /\ ((y0 y1 y2 y3) = y2)) ((y2 = (Nat.add (Nat.mul (Nat.div y2 y3) y3) (y0 y1 y2 y3))) /\ (Peano.lt (y0 y1 y2 y3) y3))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))))) x0 x1))) /\ (Peano.lt (@ε ((prod nat (prod nat nat)) -> nat -> nat -> nat) (fun y0 : type1306 => forall y1 : type1674, forall y2 : nat, forall y3 : nat, @COND Prop (y3 = (NUMERAL 0)) (((Nat.div y2 y3) = (NUMERAL 0)) /\ ((y0 y1 y2 y3) = y2)) ((y2 = (Nat.add (Nat.mul (Nat.div y2 y3) y3) (y0 y1 y2 y3))) /\ (Peano.lt (y0 y1 y2 y3) y3))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))))) x0 x1) x1)).
Definition term1 := forall y0 : type1674, forall y1 : nat, forall y2 : nat, @COND Prop (y2 = (NUMERAL 0)) (((Nat.div y1 y2) = (NUMERAL 0)) /\ ((@ε ((prod nat (prod nat nat)) -> nat -> nat -> nat) (fun y3 : type1306 => forall y4 : type1674, forall y5 : nat, forall y6 : nat, @COND Prop (y6 = (NUMERAL 0)) (((Nat.div y5 y6) = (NUMERAL 0)) /\ ((y3 y4 y5 y6) = y5)) ((y5 = (Nat.add (Nat.mul (Nat.div y5 y6) y6) (y3 y4 y5 y6))) /\ (Peano.lt (y3 y4 y5 y6) y6))) y0 y1 y2) = y1)) ((y1 = (Nat.add (Nat.mul (Nat.div y1 y2) y2) (@ε ((prod nat (prod nat nat)) -> nat -> nat -> nat) (fun y3 : type1306 => forall y4 : type1674, forall y5 : nat, forall y6 : nat, @COND Prop (y6 = (NUMERAL 0)) (((Nat.div y5 y6) = (NUMERAL 0)) /\ ((y3 y4 y5 y6) = y5)) ((y5 = (Nat.add (Nat.mul (Nat.div y5 y6) y6) (y3 y4 y5 y6))) /\ (Peano.lt (y3 y4 y5 y6) y6))) y0 y1 y2))) /\ (Peano.lt (@ε ((prod nat (prod nat nat)) -> nat -> nat -> nat) (fun y3 : type1306 => forall y4 : type1674, forall y5 : nat, forall y6 : nat, @COND Prop (y6 = (NUMERAL 0)) (((Nat.div y5 y6) = (NUMERAL 0)) /\ ((y3 y4 y5 y6) = y5)) ((y5 = (Nat.add (Nat.mul (Nat.div y5 y6) y6) (y3 y4 y5 y6))) /\ (Peano.lt (y3 y4 y5 y6) y6))) y0 y1 y2) y2)).
Definition term0 := (fun y0 : type1306 => forall y1 : type1674, forall y2 : nat, forall y3 : nat, @COND Prop (y3 = (NUMERAL 0)) (((Nat.div y2 y3) = (NUMERAL 0)) /\ ((y0 y1 y2 y3) = y2)) ((y2 = (Nat.add (Nat.mul (Nat.div y2 y3) y3) (y0 y1 y2 y3))) /\ (Peano.lt (y0 y1 y2 y3) y3))) (@ε ((prod nat (prod nat nat)) -> nat -> nat -> nat) (fun y0 : type1306 => forall y1 : type1674, forall y2 : nat, forall y3 : nat, @COND Prop (y3 = (NUMERAL 0)) (((Nat.div y2 y3) = (NUMERAL 0)) /\ ((y0 y1 y2 y3) = y2)) ((y2 = (Nat.add (Nat.mul (Nat.div y2 y3) y3) (y0 y1 y2 y3))) /\ (Peano.lt (y0 y1 y2 y3) y3)))).
Definition term10 (x0 : nat) (x1 : nat) := and ((Nat.div x0 x1) = (NUMERAL 0)).
Definition term35 := forall y0 : nat, forall y1 : nat, @COND Prop (y1 = (NUMERAL 0)) (((Nat.div y0 y1) = (NUMERAL 0)) /\ ((Nat.modulo y0 y1) = y0)) ((y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term4 := forall y0 : nat, forall y1 : nat, @COND Prop (y1 = (NUMERAL 0)) (((Nat.div y0 y1) = (NUMERAL 0)) /\ ((@ε ((prod nat (prod nat nat)) -> nat -> nat -> nat) (fun y2 : type1306 => forall y3 : type1674, forall y4 : nat, forall y5 : nat, @COND Prop (y5 = (NUMERAL 0)) (((Nat.div y4 y5) = (NUMERAL 0)) /\ ((y2 y3 y4 y5) = y4)) ((y4 = (Nat.add (Nat.mul (Nat.div y4 y5) y5) (y2 y3 y4 y5))) /\ (Peano.lt (y2 y3 y4 y5) y5))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))))) y0 y1) = y0)) ((y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (@ε ((prod nat (prod nat nat)) -> nat -> nat -> nat) (fun y2 : type1306 => forall y3 : type1674, forall y4 : nat, forall y5 : nat, @COND Prop (y5 = (NUMERAL 0)) (((Nat.div y4 y5) = (NUMERAL 0)) /\ ((y2 y3 y4 y5) = y4)) ((y4 = (Nat.add (Nat.mul (Nat.div y4 y5) y5) (y2 y3 y4 y5))) /\ (Peano.lt (y2 y3 y4 y5) y5))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))))) y0 y1))) /\ (Peano.lt (@ε ((prod nat (prod nat nat)) -> nat -> nat -> nat) (fun y2 : type1306 => forall y3 : type1674, forall y4 : nat, forall y5 : nat, @COND Prop (y5 = (NUMERAL 0)) (((Nat.div y4 y5) = (NUMERAL 0)) /\ ((y2 y3 y4 y5) = y4)) ((y4 = (Nat.add (Nat.mul (Nat.div y4 y5) y5) (y2 y3 y4 y5))) /\ (Peano.lt (y2 y3 y4 y5) y5))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))))) y0 y1) y1)).
Definition term34 := fun y0 : nat => forall y1 : nat, @COND Prop (y1 = (NUMERAL 0)) (((Nat.div y0 y1) = (NUMERAL 0)) /\ ((Nat.modulo y0 y1) = y0)) ((y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term33 := fun y0 : nat => forall y1 : nat, @COND Prop (y1 = (NUMERAL 0)) (((Nat.div y0 y1) = (NUMERAL 0)) /\ ((@ε ((prod nat (prod nat nat)) -> nat -> nat -> nat) (fun y2 : type1306 => forall y3 : type1674, forall y4 : nat, forall y5 : nat, @COND Prop (y5 = (NUMERAL 0)) (((Nat.div y4 y5) = (NUMERAL 0)) /\ ((y2 y3 y4 y5) = y4)) ((y4 = (Nat.add (Nat.mul (Nat.div y4 y5) y5) (y2 y3 y4 y5))) /\ (Peano.lt (y2 y3 y4 y5) y5))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))))) y0 y1) = y0)) ((y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (@ε ((prod nat (prod nat nat)) -> nat -> nat -> nat) (fun y2 : type1306 => forall y3 : type1674, forall y4 : nat, forall y5 : nat, @COND Prop (y5 = (NUMERAL 0)) (((Nat.div y4 y5) = (NUMERAL 0)) /\ ((y2 y3 y4 y5) = y4)) ((y4 = (Nat.add (Nat.mul (Nat.div y4 y5) y5) (y2 y3 y4 y5))) /\ (Peano.lt (y2 y3 y4 y5) y5))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))))) y0 y1))) /\ (Peano.lt (@ε ((prod nat (prod nat nat)) -> nat -> nat -> nat) (fun y2 : type1306 => forall y3 : type1674, forall y4 : nat, forall y5 : nat, @COND Prop (y5 = (NUMERAL 0)) (((Nat.div y4 y5) = (NUMERAL 0)) /\ ((y2 y3 y4 y5) = y4)) ((y4 = (Nat.add (Nat.mul (Nat.div y4 y5) y5) (y2 y3 y4 y5))) /\ (Peano.lt (y2 y3 y4 y5) y5))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))))) y0 y1) y1)).
Definition term20 (x0 : nat) (x1 : nat) := and (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))).
Definition term19 (x0 : nat) (x1 : nat) := and (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (@ε ((prod nat (prod nat nat)) -> nat -> nat -> nat) (fun y0 : type1306 => forall y1 : type1674, forall y2 : nat, forall y3 : nat, @COND Prop (y3 = (NUMERAL 0)) (((Nat.div y2 y3) = (NUMERAL 0)) /\ ((y0 y1 y2 y3) = y2)) ((y2 = (Nat.add (Nat.mul (Nat.div y2 y3) y3) (y0 y1 y2 y3))) /\ (Peano.lt (y0 y1 y2 y3) y3))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))))) x0 x1))).
Definition term17 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul (Nat.div x0 x1) x1) (@ε ((prod nat (prod nat nat)) -> nat -> nat -> nat) (fun y0 : type1306 => forall y1 : type1674, forall y2 : nat, forall y3 : nat, @COND Prop (y3 = (NUMERAL 0)) (((Nat.div y2 y3) = (NUMERAL 0)) /\ ((y0 y1 y2 y3) = y2)) ((y2 = (Nat.add (Nat.mul (Nat.div y2 y3) y3) (y0 y1 y2 y3))) /\ (Peano.lt (y0 y1 y2 y3) y3))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))))) x0 x1).
Definition term3 := @pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0))))))))).
Definition term21 (x0 : nat) (x1 : nat) := Peano.lt (@ε ((prod nat (prod nat nat)) -> nat -> nat -> nat) (fun y0 : type1306 => forall y1 : type1674, forall y2 : nat, forall y3 : nat, @COND Prop (y3 = (NUMERAL 0)) (((Nat.div y2 y3) = (NUMERAL 0)) /\ ((y0 y1 y2 y3) = y2)) ((y2 = (Nat.add (Nat.mul (Nat.div y2 y3) y3) (y0 y1 y2 y3))) /\ (Peano.lt (y0 y1 y2 y3) y3))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))))) x0 x1).
Definition term24 (x0 : nat) (x1 : nat) := Peano.lt (Nat.modulo x0 x1) x1.
Definition term2 := (fun y0 : type1674 => forall y1 : nat, forall y2 : nat, @COND Prop (y2 = (NUMERAL 0)) (((Nat.div y1 y2) = (NUMERAL 0)) /\ ((@ε ((prod nat (prod nat nat)) -> nat -> nat -> nat) (fun y3 : type1306 => forall y4 : type1674, forall y5 : nat, forall y6 : nat, @COND Prop (y6 = (NUMERAL 0)) (((Nat.div y5 y6) = (NUMERAL 0)) /\ ((y3 y4 y5 y6) = y5)) ((y5 = (Nat.add (Nat.mul (Nat.div y5 y6) y6) (y3 y4 y5 y6))) /\ (Peano.lt (y3 y4 y5 y6) y6))) y0 y1 y2) = y1)) ((y1 = (Nat.add (Nat.mul (Nat.div y1 y2) y2) (@ε ((prod nat (prod nat nat)) -> nat -> nat -> nat) (fun y3 : type1306 => forall y4 : type1674, forall y5 : nat, forall y6 : nat, @COND Prop (y6 = (NUMERAL 0)) (((Nat.div y5 y6) = (NUMERAL 0)) /\ ((y3 y4 y5 y6) = y5)) ((y5 = (Nat.add (Nat.mul (Nat.div y5 y6) y6) (y3 y4 y5 y6))) /\ (Peano.lt (y3 y4 y5 y6) y6))) y0 y1 y2))) /\ (Peano.lt (@ε ((prod nat (prod nat nat)) -> nat -> nat -> nat) (fun y3 : type1306 => forall y4 : type1674, forall y5 : nat, forall y6 : nat, @COND Prop (y6 = (NUMERAL 0)) (((Nat.div y5 y6) = (NUMERAL 0)) /\ ((y3 y4 y5 y6) = y5)) ((y5 = (Nat.add (Nat.mul (Nat.div y5 y6) y6) (y3 y4 y5 y6))) /\ (Peano.lt (y3 y4 y5 y6) y6))) y0 y1 y2) y2))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))))).
Definition term5 := @ε ((prod nat (prod nat nat)) -> nat -> nat -> nat) (fun y0 : type1306 => forall y1 : type1674, forall y2 : nat, forall y3 : nat, @COND Prop (y3 = (NUMERAL 0)) (((Nat.div y2 y3) = (NUMERAL 0)) /\ ((y0 y1 y2 y3) = y2)) ((y2 = (Nat.add (Nat.mul (Nat.div y2 y3) y3) (y0 y1 y2 y3))) /\ (Peano.lt (y0 y1 y2 y3) y3))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))))).
Definition term7 (x0 : nat) (x1 : nat) := @ε ((prod nat (prod nat nat)) -> nat -> nat -> nat) (fun y0 : type1306 => forall y1 : type1674, forall y2 : nat, forall y3 : nat, @COND Prop (y3 = (NUMERAL 0)) (((Nat.div y2 y3) = (NUMERAL 0)) /\ ((y0 y1 y2 y3) = y2)) ((y2 = (Nat.add (Nat.mul (Nat.div y2 y3) y3) (y0 y1 y2 y3))) /\ (Peano.lt (y0 y1 y2 y3) y3))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))))) x0 x1.
Definition term25 (x0 : nat) (x1 : nat) := (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (@ε ((prod nat (prod nat nat)) -> nat -> nat -> nat) (fun y0 : type1306 => forall y1 : type1674, forall y2 : nat, forall y3 : nat, @COND Prop (y3 = (NUMERAL 0)) (((Nat.div y2 y3) = (NUMERAL 0)) /\ ((y0 y1 y2 y3) = y2)) ((y2 = (Nat.add (Nat.mul (Nat.div y2 y3) y3) (y0 y1 y2 y3))) /\ (Peano.lt (y0 y1 y2 y3) y3))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))))) x0 x1))) /\ (Peano.lt (@ε ((prod nat (prod nat nat)) -> nat -> nat -> nat) (fun y0 : type1306 => forall y1 : type1674, forall y2 : nat, forall y3 : nat, @COND Prop (y3 = (NUMERAL 0)) (((Nat.div y2 y3) = (NUMERAL 0)) /\ ((y0 y1 y2 y3) = y2)) ((y2 = (Nat.add (Nat.mul (Nat.div y2 y3) y3) (y0 y1 y2 y3))) /\ (Peano.lt (y0 y1 y2 y3) y3))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))))) x0 x1) x1).
Definition term30 (x0 : nat) := fun y0 : nat => @COND Prop (y0 = (NUMERAL 0)) (((Nat.div x0 y0) = (NUMERAL 0)) /\ ((Nat.modulo x0 y0) = x0)) ((x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0)).
Definition term29 (x0 : nat) := fun y0 : nat => @COND Prop (y0 = (NUMERAL 0)) (((Nat.div x0 y0) = (NUMERAL 0)) /\ ((@ε ((prod nat (prod nat nat)) -> nat -> nat -> nat) (fun y1 : type1306 => forall y2 : type1674, forall y3 : nat, forall y4 : nat, @COND Prop (y4 = (NUMERAL 0)) (((Nat.div y3 y4) = (NUMERAL 0)) /\ ((y1 y2 y3 y4) = y3)) ((y3 = (Nat.add (Nat.mul (Nat.div y3 y4) y4) (y1 y2 y3 y4))) /\ (Peano.lt (y1 y2 y3 y4) y4))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))))) x0 y0) = x0)) ((x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (@ε ((prod nat (prod nat nat)) -> nat -> nat -> nat) (fun y1 : type1306 => forall y2 : type1674, forall y3 : nat, forall y4 : nat, @COND Prop (y4 = (NUMERAL 0)) (((Nat.div y3 y4) = (NUMERAL 0)) /\ ((y1 y2 y3 y4) = y3)) ((y3 = (Nat.add (Nat.mul (Nat.div y3 y4) y4) (y1 y2 y3 y4))) /\ (Peano.lt (y1 y2 y3 y4) y4))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))))) x0 y0))) /\ (Peano.lt (@ε ((prod nat (prod nat nat)) -> nat -> nat -> nat) (fun y1 : type1306 => forall y2 : type1674, forall y3 : nat, forall y4 : nat, @COND Prop (y4 = (NUMERAL 0)) (((Nat.div y3 y4) = (NUMERAL 0)) /\ ((y1 y2 y3 y4) = y3)) ((y3 = (Nat.add (Nat.mul (Nat.div y3 y4) y4) (y1 y2 y3 y4))) /\ (Peano.lt (y1 y2 y3 y4) y4))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))))) x0 y0) y0)).