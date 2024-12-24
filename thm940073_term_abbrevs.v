Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term119 (x0 : nat) (x1 : nat) := ~ (x0 = x1).
Definition term167 := (~ False) -> False.
Definition term87 := Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0))).
Definition term7 := (forall y0 : nat, (Nat.pow 0 (BIT1 y0)) = 0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.pow (BIT0 y0) (BIT1 y1)) = (Nat.mul (BIT0 y0) (Nat.mul (Nat.pow (BIT0 y0) y1) (Nat.pow (BIT0 y0) y1)))) /\ (forall y0 : nat, forall y1 : nat, (Nat.pow (BIT1 y0) (BIT1 y1)) = (Nat.mul (BIT1 y0) (Nat.mul (Nat.pow (BIT1 y0) y1) (Nat.pow (BIT1 y0) y1))))).
Definition term151 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((~ (x0 = x1)) \/ (~ (x0 = x2)))) -> x1 = x2.
Definition term91 := ((~ ((Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0)))) = (BIT1 0))) -> ((Nat.pow (NUMERAL (BIT1 0)) (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0))) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False) -> (~ ((Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0)))) = (BIT1 0))) -> ((Nat.pow (NUMERAL (BIT1 0)) (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0))) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False.
Definition term80 := BIT0 (Nat.mul 0 0).
Definition term137 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x0 = x1) /\ (x2 = x3).
Definition term133 (x0 : Prop) := ~ (~ x0).
Definition term44 (x0 : nat) (x1 : nat) := Nat.add (BIT1 x0) (Nat.add (BIT0 x1) (BIT0 (BIT0 (Nat.mul x0 x1)))).
Definition term27 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.pow (NUMERAL x0) (NUMERAL y0)) = (NUMERAL (Nat.pow x0 y0))) x1.
Definition term49 := (forall y0 : nat, (Nat.add (BIT0 y0) 0) = (BIT0 y0)) /\ ((forall y0 : nat, (Nat.add (BIT1 y0) 0) = (BIT1 y0)) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT0 y1)) = (BIT0 (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT1 y1)) = (BIT1 (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT0 y1)) = (BIT1 (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT1 y1)) = (BIT0 (S (Nat.add y0 y1)))))))).
Definition term48 := (forall y0 : nat, (Nat.add 0 (BIT1 y0)) = (BIT1 y0)) /\ ((forall y0 : nat, (Nat.add (BIT0 y0) 0) = (BIT0 y0)) /\ ((forall y0 : nat, (Nat.add (BIT1 y0) 0) = (BIT1 y0)) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT0 y1)) = (BIT0 (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT1 y1)) = (BIT1 (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT0 y1)) = (BIT1 (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT1 y1)) = (BIT0 (S (Nat.add y0 y1))))))))).
Definition term47 := (forall y0 : nat, (Nat.add 0 (BIT0 y0)) = (BIT0 y0)) /\ ((forall y0 : nat, (Nat.add 0 (BIT1 y0)) = (BIT1 y0)) /\ ((forall y0 : nat, (Nat.add (BIT0 y0) 0) = (BIT0 y0)) /\ ((forall y0 : nat, (Nat.add (BIT1 y0) 0) = (BIT1 y0)) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT0 y1)) = (BIT0 (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT1 y1)) = (BIT1 (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT0 y1)) = (BIT1 (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT1 y1)) = (BIT0 (S (Nat.add y0 y1)))))))))).
Definition term4 := (forall y0 : nat, (Nat.pow 0 (BIT0 y0)) = (Nat.mul (Nat.pow 0 y0) (Nat.pow 0 y0))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.pow (BIT0 y0) (BIT0 y1)) = (Nat.mul (Nat.pow (BIT0 y0) y1) (Nat.pow (BIT0 y0) y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.pow (BIT1 y0) (BIT0 y1)) = (Nat.mul (Nat.pow (BIT1 y0) y1) (Nat.pow (BIT1 y0) y1))) /\ ((forall y0 : nat, (Nat.pow 0 (BIT1 y0)) = 0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.pow (BIT0 y0) (BIT1 y1)) = (Nat.mul (BIT0 y0) (Nat.mul (Nat.pow (BIT0 y0) y1) (Nat.pow (BIT0 y0) y1)))) /\ (forall y0 : nat, forall y1 : nat, (Nat.pow (BIT1 y0) (BIT1 y1)) = (Nat.mul (BIT1 y0) (Nat.mul (Nat.pow (BIT1 y0) y1) (Nat.pow (BIT1 y0) y1)))))))).
Definition term3 := (forall y0 : nat, (Nat.pow (BIT1 y0) 0) = (BIT1 0)) /\ ((forall y0 : nat, (Nat.pow 0 (BIT0 y0)) = (Nat.mul (Nat.pow 0 y0) (Nat.pow 0 y0))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.pow (BIT0 y0) (BIT0 y1)) = (Nat.mul (Nat.pow (BIT0 y0) y1) (Nat.pow (BIT0 y0) y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.pow (BIT1 y0) (BIT0 y1)) = (Nat.mul (Nat.pow (BIT1 y0) y1) (Nat.pow (BIT1 y0) y1))) /\ ((forall y0 : nat, (Nat.pow 0 (BIT1 y0)) = 0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.pow (BIT0 y0) (BIT1 y1)) = (Nat.mul (BIT0 y0) (Nat.mul (Nat.pow (BIT0 y0) y1) (Nat.pow (BIT0 y0) y1)))) /\ (forall y0 : nat, forall y1 : nat, (Nat.pow (BIT1 y0) (BIT1 y1)) = (Nat.mul (BIT1 y0) (Nat.mul (Nat.pow (BIT1 y0) y1) (Nat.pow (BIT1 y0) y1))))))))).
Definition term2 := (forall y0 : nat, (Nat.pow (BIT0 y0) 0) = (BIT1 0)) /\ ((forall y0 : nat, (Nat.pow (BIT1 y0) 0) = (BIT1 0)) /\ ((forall y0 : nat, (Nat.pow 0 (BIT0 y0)) = (Nat.mul (Nat.pow 0 y0) (Nat.pow 0 y0))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.pow (BIT0 y0) (BIT0 y1)) = (Nat.mul (Nat.pow (BIT0 y0) y1) (Nat.pow (BIT0 y0) y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.pow (BIT1 y0) (BIT0 y1)) = (Nat.mul (Nat.pow (BIT1 y0) y1) (Nat.pow (BIT1 y0) y1))) /\ ((forall y0 : nat, (Nat.pow 0 (BIT1 y0)) = 0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.pow (BIT0 y0) (BIT1 y1)) = (Nat.mul (BIT0 y0) (Nat.mul (Nat.pow (BIT0 y0) y1) (Nat.pow (BIT0 y0) y1)))) /\ (forall y0 : nat, forall y1 : nat, (Nat.pow (BIT1 y0) (BIT1 y1)) = (Nat.mul (BIT1 y0) (Nat.mul (Nat.pow (BIT1 y0) y1) (Nat.pow (BIT1 y0) y1)))))))))).
Definition term132 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (~ (x0 = x1))) /\ (~ (~ (x2 = x3))).
Definition term154 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (~ (x1 = x0))) /\ (~ (~ (x1 = x2))).
Definition term125 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop (((Nat.pow x0 x2) = (Nat.pow x1 x3)) \/ ((~ (x0 = x1)) \/ (~ (x2 = x3)))).
Definition term46 := ((Nat.add 0 0) = 0) /\ ((forall y0 : nat, (Nat.add 0 (BIT0 y0)) = (BIT0 y0)) /\ ((forall y0 : nat, (Nat.add 0 (BIT1 y0)) = (BIT1 y0)) /\ ((forall y0 : nat, (Nat.add (BIT0 y0) 0) = (BIT0 y0)) /\ ((forall y0 : nat, (Nat.add (BIT1 y0) 0) = (BIT1 y0)) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT0 y1)) = (BIT0 (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT1 y1)) = (BIT1 (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT0 y1)) = (BIT1 (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT1 y1)) = (BIT0 (S (Nat.add y0 y1))))))))))).
Definition term31 := ((Nat.mul 0 0) = 0) /\ ((forall y0 : nat, (Nat.mul 0 (BIT0 y0)) = 0) /\ ((forall y0 : nat, (Nat.mul 0 (BIT1 y0)) = 0) /\ ((forall y0 : nat, (Nat.mul (BIT0 y0) 0) = 0) /\ ((forall y0 : nat, (Nat.mul (BIT1 y0) 0) = 0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT0 y0) (BIT0 y1)) = (BIT0 (BIT0 (Nat.mul y0 y1)))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT0 y0) (BIT1 y1)) = (Nat.add (BIT0 y0) (BIT0 (BIT0 (Nat.mul y0 y1))))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT1 y0) (BIT0 y1)) = (Nat.add (BIT0 y1) (BIT0 (BIT0 (Nat.mul y0 y1))))) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul (BIT1 y0) (BIT1 y1)) = (Nat.add (BIT1 y0) (Nat.add (BIT0 y1) (BIT0 (BIT0 (Nat.mul y0 y1))))))))))))).
Definition term71 := Nat.mul (BIT1 0) (Nat.mul (Nat.pow (BIT1 0) 0) (Nat.pow (BIT1 0) 0)).
Definition term143 := (~ ((Nat.pow (NUMERAL (BIT1 0)) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0)))))) -> (Nat.pow (NUMERAL (BIT1 0)) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0)))).
Definition term114 := ~ ((NUMERAL (BIT1 0)) = (BIT1 0)).
Definition term94 := (forall y0 : nat, (NUMERAL y0) = y0) -> False.
Definition term142 := (((NUMERAL (BIT1 0)) = (BIT1 0)) /\ ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL (BIT0 (BIT1 0))))) -> (Nat.pow (NUMERAL (BIT1 0)) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0)))).
Definition term160 := (((Nat.pow (NUMERAL (BIT1 0)) (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0))) /\ ((Nat.pow (NUMERAL (BIT1 0)) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0)))))) -> (NUMERAL (BIT1 0)) = (Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0)))).
Definition term81 := Nat.add 0 (BIT0 (Nat.mul 0 0)).
Definition term86 (x0 : Prop) := (~ x0) -> False.
Definition term38 := (forall y0 : nat, forall y1 : nat, (Nat.mul (BIT1 y0) (BIT0 y1)) = (Nat.add (BIT0 y1) (BIT0 (BIT0 (Nat.mul y0 y1))))) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul (BIT1 y0) (BIT1 y1)) = (Nat.add (BIT1 y0) (Nat.add (BIT0 y1) (BIT0 (BIT0 (Nat.mul y0 y1)))))).
Definition term8 := (forall y0 : nat, forall y1 : nat, (Nat.pow (BIT0 y0) (BIT1 y1)) = (Nat.mul (BIT0 y0) (Nat.mul (Nat.pow (BIT0 y0) y1) (Nat.pow (BIT0 y0) y1)))) /\ (forall y0 : nat, forall y1 : nat, (Nat.pow (BIT1 y0) (BIT1 y1)) = (Nat.mul (BIT1 y0) (Nat.mul (Nat.pow (BIT1 y0) y1) (Nat.pow (BIT1 y0) y1)))).
Definition term156 (x0 : nat) (x1 : nat) (x2 : nat) := imp (~ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term138 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := imp (~ ((~ (x0 = x1)) \/ (~ (x2 = x3)))).
Definition term14 (x0 : nat) (x1 : nat) := Nat.mul (BIT1 x0) (Nat.mul (Nat.pow (BIT1 x0) x1) (Nat.pow (BIT1 x0) x1)).
Definition term54 (x0 : nat) := forall y0 : nat, (Nat.add (BIT0 x0) (BIT0 y0)) = (BIT0 (Nat.add x0 y0)).
Definition term126 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term136 (x0 : nat) (x1 : nat) := and (x0 = x1).
Definition term69 := Nat.mul (Nat.pow (BIT1 0) (BIT1 0)) (Nat.pow (BIT1 0) (BIT1 0)).
Definition term43 (x0 : nat) (x1 : nat) := Nat.mul (BIT1 x0) (BIT1 x1).
Definition term56 (x0 : nat) (x1 : nat) := Nat.add (BIT0 x0) (BIT0 x1).
Definition term162 := ~ ((NUMERAL (BIT1 0)) = (Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0))))).
Definition term112 (x0 : Prop) := (~ x0) -> x0.
Definition term155 (x0 : nat) (x1 : nat) (x2 : nat) := (x1 = x0) /\ (x1 = x2).
Definition term139 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := imp ((x0 = x1) /\ (x2 = x3)).
Definition term66 := NUMERAL (Nat.pow (BIT1 0) (BIT0 (BIT1 0))).
Definition term92 := (((~ ((Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0)))) = (BIT1 0))) -> ((Nat.pow (NUMERAL (BIT1 0)) (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0))) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False) -> (~ ((Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0)))) = (BIT1 0))) -> ((Nat.pow (NUMERAL (BIT1 0)) (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0))) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False) -> (~ ((Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0)))) = (BIT1 0))) -> ((Nat.pow (NUMERAL (BIT1 0)) (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0))) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False.
Definition term152 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x1 = x0)) \/ (~ (x1 = x2)).
Definition term130 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term149 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2))).
Definition term163 := ((NUMERAL (BIT1 0)) = (Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0))))) /\ ((NUMERAL (BIT1 0)) = (BIT1 0)).
Definition term150 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term82 := Nat.add (BIT1 0).
Definition term83 := Nat.add (BIT1 0) 0.
Definition term122 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term41 (x0 : nat) := forall y0 : nat, (Nat.mul (BIT1 x0) (BIT1 y0)) = (Nat.add (BIT1 x0) (Nat.add (BIT0 y0) (BIT0 (BIT0 (Nat.mul x0 y0))))).
Definition term11 (x0 : nat) := forall y0 : nat, (Nat.pow (BIT1 x0) (BIT1 y0)) = (Nat.mul (BIT1 x0) (Nat.mul (Nat.pow (BIT1 x0) y0) (Nat.pow (BIT1 x0) y0))).
Definition term123 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Nat.pow x0 x2) = (Nat.pow x1 x3)) \/ ((~ (x0 = x1)) \/ (~ (x2 = x3))).
Definition term51 := (forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT0 y1)) = (BIT0 (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT1 y1)) = (BIT1 (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT0 y1)) = (BIT1 (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT1 y1)) = (BIT0 (S (Nat.add y0 y1)))))).
Definition term36 := (forall y0 : nat, forall y1 : nat, (Nat.mul (BIT0 y0) (BIT0 y1)) = (BIT0 (BIT0 (Nat.mul y0 y1)))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT0 y0) (BIT1 y1)) = (Nat.add (BIT0 y0) (BIT0 (BIT0 (Nat.mul y0 y1))))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT1 y0) (BIT0 y1)) = (Nat.add (BIT0 y1) (BIT0 (BIT0 (Nat.mul y0 y1))))) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul (BIT1 y0) (BIT1 y1)) = (Nat.add (BIT1 y0) (Nat.add (BIT0 y1) (BIT0 (BIT0 (Nat.mul y0 y1)))))))).
Definition term6 := (forall y0 : nat, forall y1 : nat, (Nat.pow (BIT1 y0) (BIT0 y1)) = (Nat.mul (Nat.pow (BIT1 y0) y1) (Nat.pow (BIT1 y0) y1))) /\ ((forall y0 : nat, (Nat.pow 0 (BIT1 y0)) = 0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.pow (BIT0 y0) (BIT1 y1)) = (Nat.mul (BIT0 y0) (Nat.mul (Nat.pow (BIT0 y0) y1) (Nat.pow (BIT0 y0) y1)))) /\ (forall y0 : nat, forall y1 : nat, (Nat.pow (BIT1 y0) (BIT1 y1)) = (Nat.mul (BIT1 y0) (Nat.mul (Nat.pow (BIT1 y0) y1) (Nat.pow (BIT1 y0) y1)))))).
Definition term118 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Nat.pow x0 x2) = (Nat.pow x1 x3)) \/ (~ (x2 = x3)).
Definition term76 := Nat.mul (BIT1 0) (BIT1 0).
Definition term26 (x0 : nat) := forall y0 : nat, (Nat.pow (NUMERAL x0) (NUMERAL y0)) = (NUMERAL (Nat.pow x0 y0)).
Definition term12 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.pow (BIT1 x0) (BIT1 y0)) = (Nat.mul (BIT1 x0) (Nat.mul (Nat.pow (BIT1 x0) y0) (Nat.pow (BIT1 x0) y0)))) x1.
Definition term159 := ((Nat.pow (NUMERAL (BIT1 0)) (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0))) /\ ((Nat.pow (NUMERAL (BIT1 0)) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0))))).
Definition term116 := (~ ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL (BIT0 (BIT1 0))))) -> (NUMERAL (BIT0 (BIT1 0))) = (NUMERAL (BIT0 (BIT1 0))).
Definition term106 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x1 = x3)) \/ ((Nat.pow x0 x1) = (Nat.pow x2 x3)).
Definition term109 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2)).
Definition term97 := imp ((Nat.pow (NUMERAL (BIT1 0)) (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0))).
Definition term88 := (~ ((Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0)))) = (BIT1 0))) -> False.
Definition term37 := (forall y0 : nat, forall y1 : nat, (Nat.mul (BIT0 y0) (BIT1 y1)) = (Nat.add (BIT0 y0) (BIT0 (BIT0 (Nat.mul y0 y1))))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT1 y0) (BIT0 y1)) = (Nat.add (BIT0 y1) (BIT0 (BIT0 (Nat.mul y0 y1))))) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul (BIT1 y0) (BIT1 y1)) = (Nat.add (BIT1 y0) (Nat.add (BIT0 y1) (BIT0 (BIT0 (Nat.mul y0 y1))))))).
Definition term166 := ((Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0)))) = (BIT1 0)) -> False.
Definition term148 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term141 := ((NUMERAL (BIT1 0)) = (BIT1 0)) /\ ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL (BIT0 (BIT1 0)))).
Definition term140 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((x0 = x2) /\ (x1 = x3)) -> (Nat.pow x0 x1) = (Nat.pow x2 x3).
Definition term59 (x0 : nat) := (fun y0 : nat => (Nat.add (BIT1 y0) 0) = (BIT1 y0)) x0.
Definition term13 (x0 : nat) (x1 : nat) := Nat.pow (BIT1 x0) (BIT1 x1).
Definition term101 := (~ ((Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0)))) = (BIT1 0))) -> ((Nat.pow (NUMERAL (BIT1 0)) (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0))) -> ~ (forall y0 : nat, (NUMERAL y0) = y0).
Definition term103 (x0 : nat) := (fun y0 : nat => (NUMERAL y0) = y0) x0.
Definition term84 := Nat.mul (Nat.pow (BIT1 0) (BIT1 0)).
Definition term18 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.pow (BIT1 x0) (BIT0 y0)) = (Nat.mul (Nat.pow (BIT1 x0) y0) (Nat.pow (BIT1 x0) y0))) x1.
Definition term127 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ ((~ (x0 = x2)) \/ (~ (x1 = x3)))) -> (Nat.pow x0 x1) = (Nat.pow x2 x3).
Definition term129 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term52 := forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT0 y1)) = (BIT0 (Nat.add y0 y1)).
Definition term39 := forall y0 : nat, forall y1 : nat, (Nat.mul (BIT1 y0) (BIT1 y1)) = (Nat.add (BIT1 y0) (Nat.add (BIT0 y1) (BIT0 (BIT0 (Nat.mul y0 y1))))).
Definition term24 := forall y0 : nat, forall y1 : nat, (Nat.pow (NUMERAL y0) (NUMERAL y1)) = (NUMERAL (Nat.pow y0 y1)).
Definition term15 := forall y0 : nat, forall y1 : nat, (Nat.pow (BIT1 y0) (BIT0 y1)) = (Nat.mul (Nat.pow (BIT1 y0) y1) (Nat.pow (BIT1 y0) y1)).
Definition term9 := forall y0 : nat, forall y1 : nat, (Nat.pow (BIT1 y0) (BIT1 y1)) = (Nat.mul (BIT1 y0) (Nat.mul (Nat.pow (BIT1 y0) y1) (Nat.pow (BIT1 y0) y1))).
Definition term42 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.mul (BIT1 x0) (BIT1 y0)) = (Nat.add (BIT1 x0) (Nat.add (BIT0 y0) (BIT0 (BIT0 (Nat.mul x0 y0)))))) x1.
Definition term124 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop ((~ (x0 = x2)) \/ ((~ (x1 = x3)) \/ ((Nat.pow x0 x1) = (Nat.pow x2 x3)))).
Definition term60 (x0 : nat) := Nat.add (BIT1 x0) 0.
Definition term22 (x0 : nat) := (fun y0 : nat => (Nat.pow (BIT1 y0) 0) = (BIT1 0)) x0.
Definition term23 (x0 : nat) := Nat.pow (BIT1 x0) 0.
Definition term58 := forall y0 : nat, (Nat.add (BIT1 y0) 0) = (BIT1 y0).
Definition term0 := (forall y0 : nat, forall y1 : nat, (Nat.pow (NUMERAL y0) (NUMERAL y1)) = (NUMERAL (Nat.pow y0 y1))) /\ (((Nat.pow 0 0) = (BIT1 0)) /\ ((forall y0 : nat, (Nat.pow (BIT0 y0) 0) = (BIT1 0)) /\ ((forall y0 : nat, (Nat.pow (BIT1 y0) 0) = (BIT1 0)) /\ ((forall y0 : nat, (Nat.pow 0 (BIT0 y0)) = (Nat.mul (Nat.pow 0 y0) (Nat.pow 0 y0))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.pow (BIT0 y0) (BIT0 y1)) = (Nat.mul (Nat.pow (BIT0 y0) y1) (Nat.pow (BIT0 y0) y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.pow (BIT1 y0) (BIT0 y1)) = (Nat.mul (Nat.pow (BIT1 y0) y1) (Nat.pow (BIT1 y0) y1))) /\ ((forall y0 : nat, (Nat.pow 0 (BIT1 y0)) = 0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.pow (BIT0 y0) (BIT1 y1)) = (Nat.mul (BIT0 y0) (Nat.mul (Nat.pow (BIT0 y0) y1) (Nat.pow (BIT0 y0) y1)))) /\ (forall y0 : nat, forall y1 : nat, (Nat.pow (BIT1 y0) (BIT1 y1)) = (Nat.mul (BIT1 y0) (Nat.mul (Nat.pow (BIT1 y0) y1) (Nat.pow (BIT1 y0) y1)))))))))))).
Definition term104 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x1 = x3) -> (Nat.pow x0 x1) = (Nat.pow x2 x3).
Definition term1 := ((Nat.pow 0 0) = (BIT1 0)) /\ ((forall y0 : nat, (Nat.pow (BIT0 y0) 0) = (BIT1 0)) /\ ((forall y0 : nat, (Nat.pow (BIT1 y0) 0) = (BIT1 0)) /\ ((forall y0 : nat, (Nat.pow 0 (BIT0 y0)) = (Nat.mul (Nat.pow 0 y0) (Nat.pow 0 y0))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.pow (BIT0 y0) (BIT0 y1)) = (Nat.mul (Nat.pow (BIT0 y0) y1) (Nat.pow (BIT0 y0) y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.pow (BIT1 y0) (BIT0 y1)) = (Nat.mul (Nat.pow (BIT1 y0) y1) (Nat.pow (BIT1 y0) y1))) /\ ((forall y0 : nat, (Nat.pow 0 (BIT1 y0)) = 0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.pow (BIT0 y0) (BIT1 y1)) = (Nat.mul (BIT0 y0) (Nat.mul (Nat.pow (BIT0 y0) y1) (Nat.pow (BIT0 y0) y1)))) /\ (forall y0 : nat, forall y1 : nat, (Nat.pow (BIT1 y0) (BIT1 y1)) = (Nat.mul (BIT1 y0) (Nat.mul (Nat.pow (BIT1 y0) y1) (Nat.pow (BIT1 y0) y1))))))))))).
Definition term20 (x0 : nat) (x1 : nat) := Nat.mul (Nat.pow (BIT1 x0) x1) (Nat.pow (BIT1 x0) x1).
Definition term96 := forall y0 : nat, (NUMERAL y0) = y0.
Definition term164 := (((NUMERAL (BIT1 0)) = (Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0))))) /\ ((NUMERAL (BIT1 0)) = (BIT1 0))) -> (Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0)))) = (BIT1 0).
Definition term146 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = x2) \/ (~ (x1 = x2)).
Definition term17 (x0 : nat) := forall y0 : nat, (Nat.pow (BIT1 x0) (BIT0 y0)) = (Nat.mul (Nat.pow (BIT1 x0) y0) (Nat.pow (BIT1 x0) y0)).
Definition term99 := ((Nat.pow (NUMERAL (BIT1 0)) (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0))) -> ~ (forall y0 : nat, (NUMERAL y0) = y0).
Definition term55 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add (BIT0 x0) (BIT0 y0)) = (BIT0 (Nat.add x0 y0))) x1.
Definition term70 := Nat.pow (BIT1 0) (BIT1 0).
Definition term100 := imp (~ ((Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0)))) = (BIT1 0))).
Definition term89 := ~ ((Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0)))) = (BIT1 0)).
Definition term147 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x1 = x0)) \/ ((x0 = x2) \/ (~ (x1 = x2))).
Definition term65 := Nat.pow (NUMERAL (BIT1 0)) (NUMERAL (BIT0 (BIT1 0))).
Definition term111 := ~ ((Nat.pow (NUMERAL (BIT1 0)) (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0))).
Definition term93 := (((~ ((Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0)))) = (BIT1 0))) -> ((Nat.pow (NUMERAL (BIT1 0)) (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0))) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False) -> (~ ((Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0)))) = (BIT1 0))) -> ((Nat.pow (NUMERAL (BIT1 0)) (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0))) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False) -> ((~ ((Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0)))) = (BIT1 0))) -> ((Nat.pow (NUMERAL (BIT1 0)) (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0))) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False) -> (~ ((Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0)))) = (BIT1 0))) -> ((Nat.pow (NUMERAL (BIT1 0)) (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0))) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False.
Definition term135 (x0 : nat) (x1 : nat) := and (~ (~ (x0 = x1))).
Definition term115 := NUMERAL (BIT0 (BIT1 0)).
Definition term64 := ((NUMERAL (NUMERAL 0)) = (NUMERAL 0)) /\ ((BIT0 0) = 0).
Definition term72 := Nat.pow (BIT1 0) 0.
Definition term113 := (~ ((NUMERAL (BIT1 0)) = (BIT1 0))) -> (NUMERAL (BIT1 0)) = (BIT1 0).
Definition term5 := (forall y0 : nat, forall y1 : nat, (Nat.pow (BIT0 y0) (BIT0 y1)) = (Nat.mul (Nat.pow (BIT0 y0) y1) (Nat.pow (BIT0 y0) y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.pow (BIT1 y0) (BIT0 y1)) = (Nat.mul (Nat.pow (BIT1 y0) y1) (Nat.pow (BIT1 y0) y1))) /\ ((forall y0 : nat, (Nat.pow 0 (BIT1 y0)) = 0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.pow (BIT0 y0) (BIT1 y1)) = (Nat.mul (BIT0 y0) (Nat.mul (Nat.pow (BIT0 y0) y1) (Nat.pow (BIT0 y0) y1)))) /\ (forall y0 : nat, forall y1 : nat, (Nat.pow (BIT1 y0) (BIT1 y1)) = (Nat.mul (BIT1 y0) (Nat.mul (Nat.pow (BIT1 y0) y1) (Nat.pow (BIT1 y0) y1))))))).
Definition term121 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x0 = x1)) \/ (((Nat.pow x0 x2) = (Nat.pow x1 x3)) \/ (~ (x2 = x3))).
Definition term98 := ((Nat.pow (NUMERAL (BIT1 0)) (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0))) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False.
Definition term62 (x0 : nat) := (fun y0 : nat => (Nat.add 0 (BIT0 y0)) = (BIT0 y0)) x0.
Definition term53 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add (BIT0 y0) (BIT0 y1)) = (BIT0 (Nat.add y0 y1))) x0.
Definition term40 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul (BIT1 y0) (BIT1 y1)) = (Nat.add (BIT1 y0) (Nat.add (BIT0 y1) (BIT0 (BIT0 (Nat.mul y0 y1)))))) x0.
Definition term25 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.pow (NUMERAL y0) (NUMERAL y1)) = (NUMERAL (Nat.pow y0 y1))) x0.
Definition term16 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.pow (BIT1 y0) (BIT0 y1)) = (Nat.mul (Nat.pow (BIT1 y0) y1) (Nat.pow (BIT1 y0) y1))) x0.
Definition term10 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.pow (BIT1 y0) (BIT1 y1)) = (Nat.mul (BIT1 y0) (Nat.mul (Nat.pow (BIT1 y0) y1) (Nat.pow (BIT1 y0) y1)))) x0.
Definition term19 (x0 : nat) (x1 : nat) := Nat.pow (BIT1 x0) (BIT0 x1).
Definition term74 := Nat.mul (BIT1 0).
Definition term77 := Nat.add (BIT1 0) (Nat.add (BIT0 0) (BIT0 (BIT0 (Nat.mul 0 0)))).
Definition term161 := (~ ((NUMERAL (BIT1 0)) = (Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0)))))) -> (NUMERAL (BIT1 0)) = (Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0)))).
Definition term21 := forall y0 : nat, (Nat.pow (BIT1 y0) 0) = (BIT1 0).
Definition term153 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term131 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ~ ((~ (x0 = x1)) \/ (~ (x2 = x3))).
Definition term67 := BIT0 (BIT1 0).
Definition term107 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x0 = x2) -> (~ (x1 = x3)) \/ ((Nat.pow x0 x1) = (Nat.pow x2 x3)).
Definition term105 (x0 : Prop) (x1 : Prop) := (~ x0) \/ x1.
Definition term29 (x0 : nat) (x1 : nat) := NUMERAL (Nat.pow x0 x1).
Definition term128 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x0 = x1)) \/ (~ (x2 = x3)).
Definition term102 := fun y0 : nat => (NUMERAL y0) = y0.
Definition term28 (x0 : nat) (x1 : nat) := Nat.pow (NUMERAL x0) (NUMERAL x1).
Definition term79 := BIT0 (Nat.add 0 (BIT0 (Nat.mul 0 0))).
Definition term117 := ~ ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL (BIT0 (BIT1 0)))).
Definition term90 := (~ ((Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0)))) = (BIT1 0))) -> ((Nat.pow (NUMERAL (BIT1 0)) (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0))) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False.
Definition term108 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x0 = x2)) \/ ((~ (x1 = x3)) \/ ((Nat.pow x0 x1) = (Nat.pow x2 x3))).
Definition term63 (x0 : nat) := Nat.add 0 (BIT0 x0).
Definition term61 := forall y0 : nat, (Nat.add 0 (BIT0 y0)) = (BIT0 y0).
Definition term157 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((x1 = x0) /\ (x1 = x2)).
Definition term57 (x0 : nat) (x1 : nat) := BIT0 (Nat.add x0 x1).
Definition term34 := (forall y0 : nat, (Nat.mul (BIT0 y0) 0) = 0) /\ ((forall y0 : nat, (Nat.mul (BIT1 y0) 0) = 0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT0 y0) (BIT0 y1)) = (BIT0 (BIT0 (Nat.mul y0 y1)))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT0 y0) (BIT1 y1)) = (Nat.add (BIT0 y0) (BIT0 (BIT0 (Nat.mul y0 y1))))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT1 y0) (BIT0 y1)) = (Nat.add (BIT0 y1) (BIT0 (BIT0 (Nat.mul y0 y1))))) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul (BIT1 y0) (BIT1 y1)) = (Nat.add (BIT1 y0) (Nat.add (BIT0 y1) (BIT0 (BIT0 (Nat.mul y0 y1)))))))))).
Definition term33 := (forall y0 : nat, (Nat.mul 0 (BIT1 y0)) = 0) /\ ((forall y0 : nat, (Nat.mul (BIT0 y0) 0) = 0) /\ ((forall y0 : nat, (Nat.mul (BIT1 y0) 0) = 0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT0 y0) (BIT0 y1)) = (BIT0 (BIT0 (Nat.mul y0 y1)))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT0 y0) (BIT1 y1)) = (Nat.add (BIT0 y0) (BIT0 (BIT0 (Nat.mul y0 y1))))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT1 y0) (BIT0 y1)) = (Nat.add (BIT0 y1) (BIT0 (BIT0 (Nat.mul y0 y1))))) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul (BIT1 y0) (BIT1 y1)) = (Nat.add (BIT1 y0) (Nat.add (BIT0 y1) (BIT0 (BIT0 (Nat.mul y0 y1))))))))))).
Definition term32 := (forall y0 : nat, (Nat.mul 0 (BIT0 y0)) = 0) /\ ((forall y0 : nat, (Nat.mul 0 (BIT1 y0)) = 0) /\ ((forall y0 : nat, (Nat.mul (BIT0 y0) 0) = 0) /\ ((forall y0 : nat, (Nat.mul (BIT1 y0) 0) = 0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT0 y0) (BIT0 y1)) = (BIT0 (BIT0 (Nat.mul y0 y1)))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT0 y0) (BIT1 y1)) = (Nat.add (BIT0 y0) (BIT0 (BIT0 (Nat.mul y0 y1))))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT1 y0) (BIT0 y1)) = (Nat.add (BIT0 y1) (BIT0 (BIT0 (Nat.mul y0 y1))))) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul (BIT1 y0) (BIT1 y1)) = (Nat.add (BIT1 y0) (Nat.add (BIT0 y1) (BIT0 (BIT0 (Nat.mul y0 y1)))))))))))).
Definition term45 := (forall y0 : nat, forall y1 : nat, (Nat.add (NUMERAL y0) (NUMERAL y1)) = (NUMERAL (Nat.add y0 y1))) /\ (((Nat.add 0 0) = 0) /\ ((forall y0 : nat, (Nat.add 0 (BIT0 y0)) = (BIT0 y0)) /\ ((forall y0 : nat, (Nat.add 0 (BIT1 y0)) = (BIT1 y0)) /\ ((forall y0 : nat, (Nat.add (BIT0 y0) 0) = (BIT0 y0)) /\ ((forall y0 : nat, (Nat.add (BIT1 y0) 0) = (BIT1 y0)) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT0 y1)) = (BIT0 (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT1 y1)) = (BIT1 (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT0 y1)) = (BIT1 (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT1 y1)) = (BIT0 (S (Nat.add y0 y1)))))))))))).
Definition term30 := (forall y0 : nat, forall y1 : nat, (Nat.mul (NUMERAL y0) (NUMERAL y1)) = (NUMERAL (Nat.mul y0 y1))) /\ (((Nat.mul 0 0) = 0) /\ ((forall y0 : nat, (Nat.mul 0 (BIT0 y0)) = 0) /\ ((forall y0 : nat, (Nat.mul 0 (BIT1 y0)) = 0) /\ ((forall y0 : nat, (Nat.mul (BIT0 y0) 0) = 0) /\ ((forall y0 : nat, (Nat.mul (BIT1 y0) 0) = 0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT0 y0) (BIT0 y1)) = (BIT0 (BIT0 (Nat.mul y0 y1)))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT0 y0) (BIT1 y1)) = (Nat.add (BIT0 y0) (BIT0 (BIT0 (Nat.mul y0 y1))))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT1 y0) (BIT0 y1)) = (Nat.add (BIT0 y1) (BIT0 (BIT0 (Nat.mul y0 y1))))) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul (BIT1 y0) (BIT1 y1)) = (Nat.add (BIT1 y0) (Nat.add (BIT0 y1) (BIT0 (BIT0 (Nat.mul y0 y1)))))))))))))).
Definition term145 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = x2)) \/ (x1 = x2).
Definition term144 := ~ ((Nat.pow (NUMERAL (BIT1 0)) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0))))).
Definition term95 := ~ (forall y0 : nat, (NUMERAL y0) = y0).
Definition term134 (x0 : nat) (x1 : nat) := ~ (~ (x0 = x1)).
Definition term120 (x0 : nat) (x1 : nat) := or (~ (x0 = x1)).
Definition term165 := (~ ((Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0)))) = (BIT1 0))) -> (Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0)))) = (BIT1 0).
Definition term50 := (forall y0 : nat, (Nat.add (BIT1 y0) 0) = (BIT1 y0)) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT0 y1)) = (BIT0 (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT1 y1)) = (BIT1 (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT0 y1)) = (BIT1 (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT1 y1)) = (BIT0 (S (Nat.add y0 y1))))))).
Definition term158 (x0 : nat) (x1 : nat) (x2 : nat) := ((x0 = x1) /\ (x0 = x2)) -> x1 = x2.
Definition term73 := Nat.mul (Nat.pow (BIT1 0) 0).
Definition term35 := (forall y0 : nat, (Nat.mul (BIT1 y0) 0) = 0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT0 y0) (BIT0 y1)) = (BIT0 (BIT0 (Nat.mul y0 y1)))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT0 y0) (BIT1 y1)) = (Nat.add (BIT0 y0) (BIT0 (BIT0 (Nat.mul y0 y1))))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT1 y0) (BIT0 y1)) = (Nat.add (BIT0 y1) (BIT0 (BIT0 (Nat.mul y0 y1))))) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul (BIT1 y0) (BIT1 y1)) = (Nat.add (BIT1 y0) (Nat.add (BIT0 y1) (BIT0 (BIT0 (Nat.mul y0 y1))))))))).
Definition term85 := NUMERAL (BIT1 0).
Definition term110 := (~ ((Nat.pow (NUMERAL (BIT1 0)) (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0)))) -> (Nat.pow (NUMERAL (BIT1 0)) (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0)).
Definition term75 := Nat.mul (Nat.pow (BIT1 0) 0) (Nat.pow (BIT1 0) 0).
Definition term78 := Nat.add (BIT0 0) (BIT0 (BIT0 (Nat.mul 0 0))).
Definition term68 := Nat.pow (BIT1 0) (BIT0 (BIT1 0)).
