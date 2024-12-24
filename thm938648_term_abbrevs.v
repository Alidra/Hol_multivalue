Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term85 := ((NUMERAL 0) = 0) /\ ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL (BIT0 (BIT1 0)))).
Definition term63 (x0 : nat) (x1 : nat) := ~ (x0 = x1).
Definition term33 := ~ ((Nat.pow 0 (NUMERAL (BIT0 (BIT1 0)))) = 0).
Definition term43 := ((Nat.pow (NUMERAL 0) (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)) -> ~ (forall y0 : nat, (NUMERAL y0) = y0).
Definition term111 := (~ False) -> False.
Definition term7 := (forall y0 : nat, (Nat.pow 0 (BIT1 y0)) = 0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.pow (BIT0 y0) (BIT1 y1)) = (Nat.mul (BIT0 y0) (Nat.mul (Nat.pow (BIT0 y0) y1) (Nat.pow (BIT0 y0) y1)))) /\ (forall y0 : nat, forall y1 : nat, (Nat.pow (BIT1 y0) (BIT1 y1)) = (Nat.mul (BIT1 y0) (Nat.mul (Nat.pow (BIT1 y0) y1) (Nat.pow (BIT1 y0) y1))))).
Definition term95 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((~ (x0 = x1)) \/ (~ (x0 = x2)))) -> x1 = x2.
Definition term23 := Nat.pow (NUMERAL 0) (NUMERAL (BIT0 (BIT1 0))).
Definition term54 := (~ ((Nat.pow (NUMERAL 0) (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0))) -> (Nat.pow (NUMERAL 0) (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0).
Definition term26 := Nat.pow 0 (BIT0 (BIT1 0)).
Definition term81 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x0 = x1) /\ (x2 = x3).
Definition term77 (x0 : Prop) := ~ (~ x0).
Definition term18 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.pow (NUMERAL x0) (NUMERAL y0)) = (NUMERAL (Nat.pow x0 y0))) x1.
Definition term4 := (forall y0 : nat, (Nat.pow 0 (BIT0 y0)) = (Nat.mul (Nat.pow 0 y0) (Nat.pow 0 y0))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.pow (BIT0 y0) (BIT0 y1)) = (Nat.mul (Nat.pow (BIT0 y0) y1) (Nat.pow (BIT0 y0) y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.pow (BIT1 y0) (BIT0 y1)) = (Nat.mul (Nat.pow (BIT1 y0) y1) (Nat.pow (BIT1 y0) y1))) /\ ((forall y0 : nat, (Nat.pow 0 (BIT1 y0)) = 0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.pow (BIT0 y0) (BIT1 y1)) = (Nat.mul (BIT0 y0) (Nat.mul (Nat.pow (BIT0 y0) y1) (Nat.pow (BIT0 y0) y1)))) /\ (forall y0 : nat, forall y1 : nat, (Nat.pow (BIT1 y0) (BIT1 y1)) = (Nat.mul (BIT1 y0) (Nat.mul (Nat.pow (BIT1 y0) y1) (Nat.pow (BIT1 y0) y1)))))))).
Definition term3 := (forall y0 : nat, (Nat.pow (BIT1 y0) 0) = (BIT1 0)) /\ ((forall y0 : nat, (Nat.pow 0 (BIT0 y0)) = (Nat.mul (Nat.pow 0 y0) (Nat.pow 0 y0))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.pow (BIT0 y0) (BIT0 y1)) = (Nat.mul (Nat.pow (BIT0 y0) y1) (Nat.pow (BIT0 y0) y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.pow (BIT1 y0) (BIT0 y1)) = (Nat.mul (Nat.pow (BIT1 y0) y1) (Nat.pow (BIT1 y0) y1))) /\ ((forall y0 : nat, (Nat.pow 0 (BIT1 y0)) = 0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.pow (BIT0 y0) (BIT1 y1)) = (Nat.mul (BIT0 y0) (Nat.mul (Nat.pow (BIT0 y0) y1) (Nat.pow (BIT0 y0) y1)))) /\ (forall y0 : nat, forall y1 : nat, (Nat.pow (BIT1 y0) (BIT1 y1)) = (Nat.mul (BIT1 y0) (Nat.mul (Nat.pow (BIT1 y0) y1) (Nat.pow (BIT1 y0) y1))))))))).
Definition term2 := (forall y0 : nat, (Nat.pow (BIT0 y0) 0) = (BIT1 0)) /\ ((forall y0 : nat, (Nat.pow (BIT1 y0) 0) = (BIT1 0)) /\ ((forall y0 : nat, (Nat.pow 0 (BIT0 y0)) = (Nat.mul (Nat.pow 0 y0) (Nat.pow 0 y0))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.pow (BIT0 y0) (BIT0 y1)) = (Nat.mul (Nat.pow (BIT0 y0) y1) (Nat.pow (BIT0 y0) y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.pow (BIT1 y0) (BIT0 y1)) = (Nat.mul (Nat.pow (BIT1 y0) y1) (Nat.pow (BIT1 y0) y1))) /\ ((forall y0 : nat, (Nat.pow 0 (BIT1 y0)) = 0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.pow (BIT0 y0) (BIT1 y1)) = (Nat.mul (BIT0 y0) (Nat.mul (Nat.pow (BIT0 y0) y1) (Nat.pow (BIT0 y0) y1)))) /\ (forall y0 : nat, forall y1 : nat, (Nat.pow (BIT1 y0) (BIT1 y1)) = (Nat.mul (BIT1 y0) (Nat.mul (Nat.pow (BIT1 y0) y1) (Nat.pow (BIT1 y0) y1)))))))))).
Definition term106 := ~ ((NUMERAL 0) = (Nat.pow 0 (NUMERAL (BIT0 (BIT1 0))))).
Definition term76 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (~ (x0 = x1))) /\ (~ (~ (x2 = x3))).
Definition term98 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (~ (x1 = x0))) /\ (~ (~ (x1 = x2))).
Definition term69 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop (((Nat.pow x0 x2) = (Nat.pow x1 x3)) \/ ((~ (x0 = x1)) \/ (~ (x2 = x3)))).
Definition term22 := ((Nat.mul 0 0) = 0) /\ ((forall y0 : nat, (Nat.mul 0 (BIT0 y0)) = 0) /\ ((forall y0 : nat, (Nat.mul 0 (BIT1 y0)) = 0) /\ ((forall y0 : nat, (Nat.mul (BIT0 y0) 0) = 0) /\ ((forall y0 : nat, (Nat.mul (BIT1 y0) 0) = 0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT0 y0) (BIT0 y1)) = (BIT0 (BIT0 (Nat.mul y0 y1)))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT0 y0) (BIT1 y1)) = (Nat.add (BIT0 y0) (BIT0 (BIT0 (Nat.mul y0 y1))))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT1 y0) (BIT0 y1)) = (Nat.add (BIT0 y1) (BIT0 (BIT0 (Nat.mul y0 y1))))) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul (BIT1 y0) (BIT1 y1)) = (Nat.add (BIT1 y0) (Nat.add (BIT0 y1) (BIT0 (BIT0 (Nat.mul y0 y1))))))))))))).
Definition term109 := (~ ((Nat.pow 0 (NUMERAL (BIT0 (BIT1 0)))) = 0)) -> (Nat.pow 0 (NUMERAL (BIT0 (BIT1 0)))) = 0.
Definition term38 := (forall y0 : nat, (NUMERAL y0) = y0) -> False.
Definition term30 (x0 : Prop) := (~ x0) -> False.
Definition term100 (x0 : nat) (x1 : nat) (x2 : nat) := imp (~ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term82 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := imp (~ ((~ (x0 = x1)) \/ (~ (x2 = x3)))).
Definition term31 := Nat.pow 0 (NUMERAL (BIT0 (BIT1 0))).
Definition term41 := imp ((Nat.pow (NUMERAL 0) (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)).
Definition term107 := ((NUMERAL 0) = (Nat.pow 0 (NUMERAL (BIT0 (BIT1 0))))) /\ ((NUMERAL 0) = 0).
Definition term13 (x0 : nat) := Nat.pow 0 (BIT0 x0).
Definition term45 := (~ ((Nat.pow 0 (NUMERAL (BIT0 (BIT1 0)))) = 0)) -> ((Nat.pow (NUMERAL 0) (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)) -> ~ (forall y0 : nat, (NUMERAL y0) = y0).
Definition term70 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term80 (x0 : nat) (x1 : nat) := and (x0 = x1).
Definition term105 := (~ ((NUMERAL 0) = (Nat.pow 0 (NUMERAL (BIT0 (BIT1 0)))))) -> (NUMERAL 0) = (Nat.pow 0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term56 (x0 : Prop) := (~ x0) -> x0.
Definition term99 (x0 : nat) (x1 : nat) (x2 : nat) := (x1 = x0) /\ (x1 = x2).
Definition term83 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := imp ((x0 = x1) /\ (x2 = x3)).
Definition term96 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x1 = x0)) \/ (~ (x1 = x2)).
Definition term74 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term93 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2))).
Definition term94 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term57 := (~ ((NUMERAL 0) = 0)) -> (NUMERAL 0) = 0.
Definition term66 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term67 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Nat.pow x0 x2) = (Nat.pow x1 x3)) \/ ((~ (x0 = x1)) \/ (~ (x2 = x3))).
Definition term6 := (forall y0 : nat, forall y1 : nat, (Nat.pow (BIT1 y0) (BIT0 y1)) = (Nat.mul (Nat.pow (BIT1 y0) y1) (Nat.pow (BIT1 y0) y1))) /\ ((forall y0 : nat, (Nat.pow 0 (BIT1 y0)) = 0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.pow (BIT0 y0) (BIT1 y1)) = (Nat.mul (BIT0 y0) (Nat.mul (Nat.pow (BIT0 y0) y1) (Nat.pow (BIT0 y0) y1)))) /\ (forall y0 : nat, forall y1 : nat, (Nat.pow (BIT1 y0) (BIT1 y1)) = (Nat.mul (BIT1 y0) (Nat.mul (Nat.pow (BIT1 y0) y1) (Nat.pow (BIT1 y0) y1)))))).
Definition term28 := Nat.pow 0 (BIT1 0).
Definition term62 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Nat.pow x0 x2) = (Nat.pow x1 x3)) \/ (~ (x2 = x3)).
Definition term17 (x0 : nat) := forall y0 : nat, (Nat.pow (NUMERAL x0) (NUMERAL y0)) = (NUMERAL (Nat.pow x0 y0)).
Definition term60 := (~ ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL (BIT0 (BIT1 0))))) -> (NUMERAL (BIT0 (BIT1 0))) = (NUMERAL (BIT0 (BIT1 0))).
Definition term50 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x1 = x3)) \/ ((Nat.pow x0 x1) = (Nat.pow x2 x3)).
Definition term53 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2)).
Definition term92 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term103 := ((Nat.pow (NUMERAL 0) (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)) /\ ((Nat.pow (NUMERAL 0) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.pow 0 (NUMERAL (BIT0 (BIT1 0))))).
Definition term84 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((x0 = x2) /\ (x1 = x3)) -> (Nat.pow x0 x1) = (Nat.pow x2 x3).
Definition term32 := (~ ((Nat.pow 0 (NUMERAL (BIT0 (BIT1 0)))) = 0)) -> False.
Definition term47 (x0 : nat) := (fun y0 : nat => (NUMERAL y0) = y0) x0.
Definition term108 := (((NUMERAL 0) = (Nat.pow 0 (NUMERAL (BIT0 (BIT1 0))))) /\ ((NUMERAL 0) = 0)) -> (Nat.pow 0 (NUMERAL (BIT0 (BIT1 0)))) = 0.
Definition term71 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ ((~ (x0 = x2)) \/ (~ (x1 = x3)))) -> (Nat.pow x0 x1) = (Nat.pow x2 x3).
Definition term8 := forall y0 : nat, (Nat.pow 0 (BIT1 y0)) = 0.
Definition term73 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term12 (x0 : nat) := (fun y0 : nat => (Nat.pow 0 (BIT0 y0)) = (Nat.mul (Nat.pow 0 y0) (Nat.pow 0 y0))) x0.
Definition term15 := forall y0 : nat, forall y1 : nat, (Nat.pow (NUMERAL y0) (NUMERAL y1)) = (NUMERAL (Nat.pow y0 y1)).
Definition term24 := NUMERAL (Nat.pow 0 (BIT0 (BIT1 0))).
Definition term42 := ((Nat.pow (NUMERAL 0) (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False.
Definition term86 := (((NUMERAL 0) = 0) /\ ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL (BIT0 (BIT1 0))))) -> (Nat.pow (NUMERAL 0) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.pow 0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term68 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop ((~ (x0 = x2)) \/ ((~ (x1 = x3)) \/ ((Nat.pow x0 x1) = (Nat.pow x2 x3)))).
Definition term0 := (forall y0 : nat, forall y1 : nat, (Nat.pow (NUMERAL y0) (NUMERAL y1)) = (NUMERAL (Nat.pow y0 y1))) /\ (((Nat.pow 0 0) = (BIT1 0)) /\ ((forall y0 : nat, (Nat.pow (BIT0 y0) 0) = (BIT1 0)) /\ ((forall y0 : nat, (Nat.pow (BIT1 y0) 0) = (BIT1 0)) /\ ((forall y0 : nat, (Nat.pow 0 (BIT0 y0)) = (Nat.mul (Nat.pow 0 y0) (Nat.pow 0 y0))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.pow (BIT0 y0) (BIT0 y1)) = (Nat.mul (Nat.pow (BIT0 y0) y1) (Nat.pow (BIT0 y0) y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.pow (BIT1 y0) (BIT0 y1)) = (Nat.mul (Nat.pow (BIT1 y0) y1) (Nat.pow (BIT1 y0) y1))) /\ ((forall y0 : nat, (Nat.pow 0 (BIT1 y0)) = 0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.pow (BIT0 y0) (BIT1 y1)) = (Nat.mul (BIT0 y0) (Nat.mul (Nat.pow (BIT0 y0) y1) (Nat.pow (BIT0 y0) y1)))) /\ (forall y0 : nat, forall y1 : nat, (Nat.pow (BIT1 y0) (BIT1 y1)) = (Nat.mul (BIT1 y0) (Nat.mul (Nat.pow (BIT1 y0) y1) (Nat.pow (BIT1 y0) y1)))))))))))).
Definition term48 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x1 = x3) -> (Nat.pow x0 x1) = (Nat.pow x2 x3).
Definition term1 := ((Nat.pow 0 0) = (BIT1 0)) /\ ((forall y0 : nat, (Nat.pow (BIT0 y0) 0) = (BIT1 0)) /\ ((forall y0 : nat, (Nat.pow (BIT1 y0) 0) = (BIT1 0)) /\ ((forall y0 : nat, (Nat.pow 0 (BIT0 y0)) = (Nat.mul (Nat.pow 0 y0) (Nat.pow 0 y0))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.pow (BIT0 y0) (BIT0 y1)) = (Nat.mul (Nat.pow (BIT0 y0) y1) (Nat.pow (BIT0 y0) y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.pow (BIT1 y0) (BIT0 y1)) = (Nat.mul (Nat.pow (BIT1 y0) y1) (Nat.pow (BIT1 y0) y1))) /\ ((forall y0 : nat, (Nat.pow 0 (BIT1 y0)) = 0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.pow (BIT0 y0) (BIT1 y1)) = (Nat.mul (BIT0 y0) (Nat.mul (Nat.pow (BIT0 y0) y1) (Nat.pow (BIT0 y0) y1)))) /\ (forall y0 : nat, forall y1 : nat, (Nat.pow (BIT1 y0) (BIT1 y1)) = (Nat.mul (BIT1 y0) (Nat.mul (Nat.pow (BIT1 y0) y1) (Nat.pow (BIT1 y0) y1))))))))))).
Definition term40 := forall y0 : nat, (NUMERAL y0) = y0.
Definition term90 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = x2) \/ (~ (x1 = x2)).
Definition term11 := forall y0 : nat, (Nat.pow 0 (BIT0 y0)) = (Nat.mul (Nat.pow 0 y0) (Nat.pow 0 y0)).
Definition term91 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x1 = x0)) \/ ((x0 = x2) \/ (~ (x1 = x2))).
Definition term37 := (((~ ((Nat.pow 0 (NUMERAL (BIT0 (BIT1 0)))) = 0)) -> ((Nat.pow (NUMERAL 0) (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False) -> (~ ((Nat.pow 0 (NUMERAL (BIT0 (BIT1 0)))) = 0)) -> ((Nat.pow (NUMERAL 0) (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False) -> ((~ ((Nat.pow 0 (NUMERAL (BIT0 (BIT1 0)))) = 0)) -> ((Nat.pow (NUMERAL 0) (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False) -> (~ ((Nat.pow 0 (NUMERAL (BIT0 (BIT1 0)))) = 0)) -> ((Nat.pow (NUMERAL 0) (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False.
Definition term110 := ((Nat.pow 0 (NUMERAL (BIT0 (BIT1 0)))) = 0) -> False.
Definition term79 (x0 : nat) (x1 : nat) := and (~ (~ (x0 = x1))).
Definition term59 := NUMERAL (BIT0 (BIT1 0)).
Definition term9 (x0 : nat) := (fun y0 : nat => (Nat.pow 0 (BIT1 y0)) = 0) x0.
Definition term5 := (forall y0 : nat, forall y1 : nat, (Nat.pow (BIT0 y0) (BIT0 y1)) = (Nat.mul (Nat.pow (BIT0 y0) y1) (Nat.pow (BIT0 y0) y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.pow (BIT1 y0) (BIT0 y1)) = (Nat.mul (Nat.pow (BIT1 y0) y1) (Nat.pow (BIT1 y0) y1))) /\ ((forall y0 : nat, (Nat.pow 0 (BIT1 y0)) = 0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.pow (BIT0 y0) (BIT1 y1)) = (Nat.mul (BIT0 y0) (Nat.mul (Nat.pow (BIT0 y0) y1) (Nat.pow (BIT0 y0) y1)))) /\ (forall y0 : nat, forall y1 : nat, (Nat.pow (BIT1 y0) (BIT1 y1)) = (Nat.mul (BIT1 y0) (Nat.mul (Nat.pow (BIT1 y0) y1) (Nat.pow (BIT1 y0) y1))))))).
Definition term10 (x0 : nat) := Nat.pow 0 (BIT1 x0).
Definition term65 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x0 = x1)) \/ (((Nat.pow x0 x2) = (Nat.pow x1 x3)) \/ (~ (x2 = x3))).
Definition term55 := ~ ((Nat.pow (NUMERAL 0) (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)).
Definition term34 := (~ ((Nat.pow 0 (NUMERAL (BIT0 (BIT1 0)))) = 0)) -> ((Nat.pow (NUMERAL 0) (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False.
Definition term16 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.pow (NUMERAL y0) (NUMERAL y1)) = (NUMERAL (Nat.pow y0 y1))) x0.
Definition term29 := Nat.mul (Nat.pow 0 (BIT1 0)).
Definition term87 := (~ ((Nat.pow (NUMERAL 0) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.pow 0 (NUMERAL (BIT0 (BIT1 0)))))) -> (Nat.pow (NUMERAL 0) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.pow 0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term97 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term75 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ~ ((~ (x0 = x1)) \/ (~ (x2 = x3))).
Definition term25 := BIT0 (BIT1 0).
Definition term51 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x0 = x2) -> (~ (x1 = x3)) \/ ((Nat.pow x0 x1) = (Nat.pow x2 x3)).
Definition term36 := (((~ ((Nat.pow 0 (NUMERAL (BIT0 (BIT1 0)))) = 0)) -> ((Nat.pow (NUMERAL 0) (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False) -> (~ ((Nat.pow 0 (NUMERAL (BIT0 (BIT1 0)))) = 0)) -> ((Nat.pow (NUMERAL 0) (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False) -> (~ ((Nat.pow 0 (NUMERAL (BIT0 (BIT1 0)))) = 0)) -> ((Nat.pow (NUMERAL 0) (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False.
Definition term49 (x0 : Prop) (x1 : Prop) := (~ x0) \/ x1.
Definition term20 (x0 : nat) (x1 : nat) := NUMERAL (Nat.pow x0 x1).
Definition term72 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x0 = x1)) \/ (~ (x2 = x3)).
Definition term46 := fun y0 : nat => (NUMERAL y0) = y0.
Definition term27 := Nat.mul (Nat.pow 0 (BIT1 0)) (Nat.pow 0 (BIT1 0)).
Definition term19 (x0 : nat) (x1 : nat) := Nat.pow (NUMERAL x0) (NUMERAL x1).
Definition term61 := ~ ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL (BIT0 (BIT1 0)))).
Definition term52 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x0 = x2)) \/ ((~ (x1 = x3)) \/ ((Nat.pow x0 x1) = (Nat.pow x2 x3))).
Definition term104 := (((Nat.pow (NUMERAL 0) (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)) /\ ((Nat.pow (NUMERAL 0) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.pow 0 (NUMERAL (BIT0 (BIT1 0)))))) -> (NUMERAL 0) = (Nat.pow 0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term58 := ~ ((NUMERAL 0) = 0).
Definition term101 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((x1 = x0) /\ (x1 = x2)).
Definition term21 := (forall y0 : nat, forall y1 : nat, (Nat.mul (NUMERAL y0) (NUMERAL y1)) = (NUMERAL (Nat.mul y0 y1))) /\ (((Nat.mul 0 0) = 0) /\ ((forall y0 : nat, (Nat.mul 0 (BIT0 y0)) = 0) /\ ((forall y0 : nat, (Nat.mul 0 (BIT1 y0)) = 0) /\ ((forall y0 : nat, (Nat.mul (BIT0 y0) 0) = 0) /\ ((forall y0 : nat, (Nat.mul (BIT1 y0) 0) = 0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT0 y0) (BIT0 y1)) = (BIT0 (BIT0 (Nat.mul y0 y1)))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT0 y0) (BIT1 y1)) = (Nat.add (BIT0 y0) (BIT0 (BIT0 (Nat.mul y0 y1))))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT1 y0) (BIT0 y1)) = (Nat.add (BIT0 y1) (BIT0 (BIT0 (Nat.mul y0 y1))))) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul (BIT1 y0) (BIT1 y1)) = (Nat.add (BIT1 y0) (Nat.add (BIT0 y1) (BIT0 (BIT0 (Nat.mul y0 y1)))))))))))))).
Definition term89 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = x2)) \/ (x1 = x2).
Definition term39 := ~ (forall y0 : nat, (NUMERAL y0) = y0).
Definition term44 := imp (~ ((Nat.pow 0 (NUMERAL (BIT0 (BIT1 0)))) = 0)).
Definition term78 (x0 : nat) (x1 : nat) := ~ (~ (x0 = x1)).
Definition term64 (x0 : nat) (x1 : nat) := or (~ (x0 = x1)).
Definition term88 := ~ ((Nat.pow (NUMERAL 0) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.pow 0 (NUMERAL (BIT0 (BIT1 0))))).
Definition term102 (x0 : nat) (x1 : nat) (x2 : nat) := ((x0 = x1) /\ (x0 = x2)) -> x1 = x2.
Definition term35 := ((~ ((Nat.pow 0 (NUMERAL (BIT0 (BIT1 0)))) = 0)) -> ((Nat.pow (NUMERAL 0) (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False) -> (~ ((Nat.pow 0 (NUMERAL (BIT0 (BIT1 0)))) = 0)) -> ((Nat.pow (NUMERAL 0) (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False.
Definition term14 (x0 : nat) := Nat.mul (Nat.pow 0 x0) (Nat.pow 0 x0).
