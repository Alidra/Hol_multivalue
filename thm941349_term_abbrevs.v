Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term192 (x0 : nat) (x1 : nat) := ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)) \/ ((Nat.add (Nat.mul x0 x0) x0) = (Nat.add x0 x1)).
Definition term134 (x0 : nat) (x1 : nat) := Nat.add (Nat.add x0 x1) (Nat.add x0 x1).
Definition term179 (x0 : nat) := Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.add (Nat.mul x0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) (Nat.add x0 x0)).
Definition term103 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.mul x0 (S y0)) = (Nat.add x0 (Nat.mul x0 y0))) x1.
Definition term127 (x0 : nat) (x1 : nat) := @eq nat (Nat.pow (BIT1 x0) x1).
Definition term3 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Nat.add x0 y0) = (Nat.add x1 y0)) = (x0 = x1).
Definition term118 := fun y0 : nat => (NUMERAL (BIT0 (BIT1 0))) = y0.
Definition term28 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.add (Nat.mul x0 x1) (Nat.mul x0 y0)) = (Nat.mul x0 (Nat.add x1 y0)).
Definition term97 := (forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))))).
Definition term50 (x0 : nat) := @eq nat (Nat.mul x0 (Nat.mul x0 (NUMERAL (BIT0 (BIT1 0))))).
Definition term82 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.mul (Nat.mul y0 y1) y2) = (Nat.mul y0 (Nat.mul y1 y2))) x0.
Definition term39 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y2)) = (Nat.mul y0 (Nat.add y1 y2))) x0.
Definition term19 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Nat.mul y0 y1) = (Nat.mul y0 y2)) = ((y0 = (NUMERAL 0)) \/ (y1 = y2))) x0.
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Nat.add y0 y2) = (Nat.add y1 y2)) = (y0 = y1)) x0.
Definition term8 := ((0 = 0) = True) /\ ((forall y0 : nat, ((BIT0 y0) = 0) = (y0 = 0)) /\ ((forall y0 : nat, ((BIT1 y0) = 0) = False) /\ ((forall y0 : nat, (0 = (BIT0 y0)) = (0 = y0)) /\ ((forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1))))))))).
Definition term195 (x0 : nat) := @eq nat (Nat.add (Nat.mul x0 x0) x0).
Definition term84 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.mul (Nat.mul x0 x1) y0) = (Nat.mul x0 (Nat.mul x1 y0))) x2.
Definition term9 := (forall y0 : nat, ((BIT0 y0) = 0) = (y0 = 0)) /\ ((forall y0 : nat, ((BIT1 y0) = 0) = False) /\ ((forall y0 : nat, (0 = (BIT0 y0)) = (0 = y0)) /\ ((forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1)))))))).
Definition term4 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Nat.add x0 y0) = (Nat.add x1 y0)) = (x0 = x1)) x2.
Definition term191 := or ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)).
Definition term160 (x0 : nat) := S (Nat.add (Nat.mul (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0))) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)).
Definition term162 (x0 : nat) := Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.mul (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)).
Definition term140 (x0 : nat) (x1 : nat) := fun y0 : nat => ((Nat.pow x0 y0) = x1) = ((Nat.pow (S (Nat.add x0 x0)) y0) = (S (Nat.add (Nat.add (Nat.add x0 x1) (Nat.add x0 x1)) (Nat.add (Nat.add x0 x1) (Nat.add x0 x1))))).
Definition term57 (x0 : nat) := (fun y0 : nat => (Nat.add y0 y0) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) x0.
Definition term163 (x0 : nat) := Nat.add (Nat.mul (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0))).
Definition term102 (x0 : nat) := forall y0 : nat, (Nat.mul x0 (S y0)) = (Nat.add x0 (Nat.mul x0 y0)).
Definition term30 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.add (Nat.mul x0 x1) (Nat.mul x0 y0)) = (Nat.mul x0 (Nat.add x1 y0)).
Definition term129 (x0 : nat) := Nat.pow (S (Nat.add x0 x0)).
Definition term99 := (forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))).
Definition term89 := (forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))).
Definition term132 (x0 : nat) (x1 : nat) := S (Nat.add (BIT0 (Nat.add x0 x1)) (BIT0 (Nat.add x0 x1))).
Definition term152 (x0 : nat) (x1 : nat) := Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.add x0 x1).
Definition term139 (x0 : nat) (x1 : nat) := S (Nat.add (Nat.add (Nat.add x0 x1) (Nat.add x0 x1)) (Nat.add (Nat.add x0 x1) (Nat.add x0 x1))).
Definition term109 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.mul (S x0) y0) = (Nat.add (Nat.mul x0 y0) y0)) x1.
Definition term185 (x0 : nat) := @eq nat (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.mul x0 x0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0))).
Definition term64 (x0 : nat) := Nat.add x0 (Nat.mul x0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)).
Definition term86 (x0 : nat) := forall y0 : nat, ((S x0) = (S y0)) = (x0 = y0).
Definition term17 (x0 : nat) := forall y0 : nat, ((NUMERAL x0) = (NUMERAL y0)) = (x0 = y0).
Definition term175 (x0 : nat) := Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.add x0 (Nat.mul x0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)))) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0).
Definition term169 (x0 : nat) := Nat.mul (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0).
Definition term178 (x0 : nat) := @eq nat (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.add (Nat.add x0 (Nat.mul x0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0))) x0)).
Definition term117 := exists y0 : nat, (NUMERAL (BIT0 (BIT1 0))) = y0.
Definition term170 (x0 : nat) := Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.mul x0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)).
Definition term59 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.add x0 x1) x2.
Definition term41 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.add (Nat.mul x0 x1) (Nat.mul x0 y0)) = (Nat.mul x0 (Nat.add x1 y0))) x2.
Definition term165 (x0 : nat) := Nat.add (Nat.mul (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0))) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0).
Definition term12 (x0 : nat) := (fun y0 : nat => ((BIT1 y0) = 0) = False) x0.
Definition term174 (x0 : nat) := Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.add x0 (Nat.mul x0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)))).
Definition term14 (x0 : nat) := (fun y0 : nat => ((BIT0 y0) = 0) = (y0 = 0)) x0.
Definition term150 (x0 : nat) := @eq nat (Nat.pow (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) (NUMERAL (BIT0 (BIT1 0)))).
Definition term149 (x0 : nat) := @eq nat (Nat.pow (S (Nat.add x0 x0)) (NUMERAL (BIT0 (BIT1 0)))).
Definition term156 (x0 : nat) := @eq nat (Nat.mul x0 x0).
Definition term66 (x0 : nat) := @eq nat (Nat.add (Nat.add x0 (Nat.mul x0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0))) x0).
Definition term159 (x0 : nat) := Nat.add (Nat.mul (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0))) (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)).
Definition term72 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.mul x0 (Nat.mul x1 y0)) = (Nat.mul (Nat.mul x0 x1) y0).
Definition term123 (x0 : nat) := Nat.pow (BIT1 x0).
Definition term24 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = (NUMERAL 0)) \/ (x1 = x2).
Definition term171 (x0 : nat) := Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0).
Definition term83 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul (Nat.mul x0 y0) y1) = (Nat.mul x0 (Nat.mul y0 y1))) x1.
Definition term40 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y1)) = (Nat.mul x0 (Nat.add y0 y1))) x1.
Definition term21 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.mul x0 y0) = (Nat.mul x0 y1)) = ((x0 = (NUMERAL 0)) \/ (y0 = y1))) x1.
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.add x0 y1) = (Nat.add y0 y1)) = (x0 = y0)) x1.
Definition term110 (x0 : nat) (x1 : nat) := Nat.mul (S x0) x1.
Definition term143 (x0 : nat) := Nat.pow (S (Nat.add x0 x0)) (NUMERAL (BIT0 (BIT1 0))).
Definition term74 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Nat.mul x0 (Nat.mul y0 y1)) = (Nat.mul (Nat.mul x0 y0) y1).
Definition term104 (x0 : nat) (x1 : nat) := Nat.mul x0 (S x1).
Definition term115 (x0 : nat) := S (Nat.add x0 x0).
Definition term146 (x0 : nat) := S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0).
Definition term53 := fun y0 : nat => (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (Nat.add y0 y0).
Definition term141 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Nat.pow x0 y0) = x1) = ((Nat.pow (S (Nat.add x0 x0)) y0) = (S (Nat.add (Nat.add (Nat.add x0 x1) (Nat.add x0 x1)) (Nat.add (Nat.add x0 x1) (Nat.add x0 x1)))))) x2.
Definition term138 (x0 : nat) (x1 : nat) := Nat.add (Nat.add (Nat.add x0 x1) (Nat.add x0 x1)) (Nat.add (Nat.add x0 x1) (Nat.add x0 x1)).
Definition term153 := Nat.mul (NUMERAL (BIT0 (BIT1 0))).
Definition term68 (x0 : nat) := Nat.add (Nat.mul x0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) (Nat.add x0 x0).
Definition term44 (x0 : nat) := Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0.
Definition term11 := forall y0 : nat, ((BIT1 y0) = 0) = False.
Definition term116 (x0 : nat) := (fun y0 : nat => (BIT0 y0) = (Nat.add y0 y0)) x0.
Definition term164 (x0 : nat) := Nat.add (Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.mul (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0))).
Definition term55 := forall y0 : nat, (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (Nat.add y0 y0).
Definition term26 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x1 x0) (Nat.mul x1 x2).
Definition term177 (x0 : nat) := @eq nat (Nat.add (Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.mul (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0))) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)).
Definition term47 (x0 : nat) := Nat.mul x0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0).
Definition term95 (x0 : nat) (x1 : nat) := S (Nat.add x0 x1).
Definition term69 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.mul x0 x1) x2.
Definition term124 (x0 : nat) := Nat.pow (BIT1 x0) (NUMERAL (BIT0 (BIT1 0))).
Definition term13 := forall y0 : nat, ((BIT0 y0) = 0) = (y0 = 0).
Definition term106 := forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1).
Definition term100 := forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)).
Definition term90 := forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)).
Definition term81 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.mul (Nat.mul y0 y1) y2) = (Nat.mul y0 (Nat.mul y1 y2)).
Definition term80 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.mul y0 (Nat.mul y1 y2)) = (Nat.mul (Nat.mul y0 y1) y2).
Definition term77 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.mul (Nat.mul x0 y0) y1) = (Nat.mul x0 (Nat.mul y0 y1)).
Definition term76 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.mul x0 (Nat.mul y0 y1)) = (Nat.mul (Nat.mul x0 y0) y1).
Definition term38 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y2)) = (Nat.mul y0 (Nat.add y1 y2)).
Definition term37 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.mul y0 (Nat.add y1 y2)) = (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y2)).
Definition term34 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y1)) = (Nat.mul x0 (Nat.add y0 y1)).
Definition term33 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.mul x0 (Nat.add y0 y1)) = (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y1)).
Definition term20 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Nat.mul x0 y0) = (Nat.mul x0 y1)) = ((x0 = (NUMERAL 0)) \/ (y0 = y1)).
Definition term15 := forall y0 : nat, forall y1 : nat, ((NUMERAL y0) = (NUMERAL y1)) = (y0 = y1).
Definition term1 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Nat.add x0 y1) = (Nat.add y0 y1)) = (x0 = y0).
Definition term136 (x0 : nat) (x1 : nat) := Nat.add (Nat.add (Nat.add x0 x1) (Nat.add x0 x1)).
Definition term166 (x0 : nat) := Nat.add (Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.mul (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0))) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0).
Definition term161 (x0 : nat) := Nat.mul (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)).
Definition term58 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.add (Nat.add x1 x0) x2) = (Nat.add x1 (Nat.add x0 x2))) /\ ((Nat.add x1 (Nat.add x0 x2)) = (Nat.add x0 (Nat.add x1 x2))).
Definition term182 (x0 : nat) := Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.mul x0 x0)).
Definition term108 (x0 : nat) := forall y0 : nat, (Nat.mul (S x0) y0) = (Nat.add (Nat.mul x0 y0) y0).
Definition term56 := forall y0 : nat, (Nat.add y0 y0) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0).
Definition term29 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.mul x1 (Nat.add x0 y0)) = (Nat.add (Nat.mul x1 x0) (Nat.mul x1 y0)).
Definition term22 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Nat.mul x0 x1) = (Nat.mul x0 y0)) = ((x0 = (NUMERAL 0)) \/ (x1 = y0)).
Definition term114 (x0 : nat) := (fun y0 : nat => (BIT1 y0) = (S (Nat.add y0 y0))) x0.
Definition term189 (x0 : nat) (x1 : nat) := ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)) \/ ((Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.add (Nat.mul x0 x0) x0)) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.add x0 x1))).
Definition term188 (x0 : nat) := @eq nat (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.add (Nat.mul x0 x0) x0))).
Definition term113 (x0 : nat) := Nat.pow x0 (NUMERAL (BIT0 (BIT1 0))).
Definition term172 (x0 : nat) := Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.mul x0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0))).
Definition term6 (x0 : nat) := forall y0 : nat, (Nat.add x0 y0) = (Nat.add y0 x0).
Definition term121 (x0 : nat) (x1 : nat) := @eq Prop ((Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1).
Definition term193 (x0 : nat) := Nat.add (Nat.mul x0 x0) x0.
Definition term93 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add x0 (S y0)) = (S (Nat.add x0 y0))) x1.
Definition term120 (x0 : nat) (x1 : nat) := @eq nat (Nat.pow x0 x1).
Definition term7 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add x0 y0) = (Nat.add y0 x0)) x1.
Definition term98 := (forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))).
Definition term88 := (forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))).
Definition term46 := NUMERAL (BIT0 (BIT1 0)).
Definition term126 (x0 : nat) := @eq nat (Nat.pow (BIT1 x0) (NUMERAL (BIT0 (BIT1 0)))).
Definition term155 (x0 : nat) (x1 : nat) := S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.add x0 x1))).
Definition term60 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add x0 (Nat.add x1 x2).
Definition term48 (x0 : nat) := Nat.mul x0 (Nat.mul x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term61 (x0 : nat) := Nat.add (Nat.add x0 (Nat.mul x0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0))) x0.
Definition term184 (x0 : nat) := Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.mul x0 x0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)).
Definition term125 (x0 : nat) (x1 : nat) := Nat.pow (BIT1 x0) x1.
Definition term71 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.mul (Nat.mul x0 x1) y0) = (Nat.mul x0 (Nat.mul x1 y0)).
Definition term119 (x0 : nat) := @eq nat (Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term62 (x0 : nat) := Nat.add x0 (Nat.add (Nat.mul x0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) x0).
Definition term54 := fun y0 : nat => (Nat.add y0 y0) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0).
Definition term151 (x0 : nat) (x1 : nat) := Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.add (Nat.add x0 x1) (Nat.add x0 x1)).
Definition term135 (x0 : nat) (x1 : nat) := Nat.add (BIT0 (Nat.add x0 x1)).
Definition term107 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) x0.
Definition term101 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))) x0.
Definition term91 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))) x0.
Definition term85 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((S y0) = (S y1)) = (y0 = y1)) x0.
Definition term16 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((NUMERAL y0) = (NUMERAL y1)) = (y0 = y1)) x0.
Definition term5 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) x0.
Definition term27 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.mul x1 (Nat.add x0 y0)) = (Nat.add (Nat.mul x1 x0) (Nat.mul x1 y0)).
Definition term51 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (Nat.mul x1 x2).
Definition term111 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x0 x1) x1.
Definition term168 (x0 : nat) := @eq nat (S (Nat.add (Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.mul (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0))) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0))).
Definition term187 (x0 : nat) := Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.add (Nat.mul x0 x0) x0)).
Definition term105 (x0 : nat) (x1 : nat) := Nat.add x0 (Nat.mul x0 x1).
Definition term147 (x0 : nat) := Nat.pow (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)).
Definition term23 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Nat.mul x0 x1) = (Nat.mul x0 y0)) = ((x0 = (NUMERAL 0)) \/ (x1 = y0))) x2.
Definition term148 (x0 : nat) := Nat.pow (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) (NUMERAL (BIT0 (BIT1 0))).
Definition term167 (x0 : nat) := S (Nat.add (Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.mul (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0))) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)).
Definition term190 := BIT0 (BIT1 0).
Definition term94 (x0 : nat) (x1 : nat) := Nat.add x0 (S x1).
Definition term142 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Nat.pow x0 y0) = x1) = ((Nat.pow (S (Nat.add x0 x0)) y0) = (S (Nat.add (Nat.add (Nat.add x0 x1) (Nat.add x0 x1)) (Nat.add (Nat.add x0 x1) (Nat.add x0 x1)))))) (NUMERAL (BIT0 (BIT1 0))).
Definition term122 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((Nat.pow x0 x1) = x2).
Definition term112 (x0 : nat) := (fun y0 : nat => (Nat.pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul y0 y0)) x0.
Definition term43 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.mul (Nat.mul x1 x0) x2) = (Nat.mul x1 (Nat.mul x0 x2))) /\ ((Nat.mul x1 (Nat.mul x0 x2)) = (Nat.mul x0 (Nat.mul x1 x2))).
Definition term130 (x0 : nat) (x1 : nat) := Nat.pow (S (Nat.add x0 x0)) x1.
Definition term25 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (Nat.add x1 x2).
Definition term73 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.mul (Nat.mul x0 x1) y0) = (Nat.mul x0 (Nat.mul x1 y0)).
Definition term144 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((fun y0 : nat => ((Nat.pow x0 y0) = x1) = ((Nat.pow (S (Nat.add x0 x0)) y0) = (S (Nat.add (Nat.add (Nat.add x0 x1) (Nat.add x0 x1)) (Nat.add (Nat.add x0 x1) (Nat.add x0 x1)))))) x2).
Definition term145 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop (((Nat.pow x1 x0) = x2) = ((Nat.pow (S (Nat.add x1 x1)) x0) = (S (Nat.add (Nat.add (Nat.add x1 x2) (Nat.add x1 x2)) (Nat.add (Nat.add x1 x2) (Nat.add x1 x2)))))).
Definition term133 (x0 : nat) (x1 : nat) := BIT0 (Nat.add x0 x1).
Definition term186 (x0 : nat) := Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.add (Nat.mul x0 x0) x0).
Definition term158 (x0 : nat) := Nat.mul (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)).
Definition term157 (x0 : nat) (x1 : nat) := @eq Prop ((Nat.mul x0 x0) = x1).
Definition term10 := (forall y0 : nat, ((BIT1 y0) = 0) = False) /\ ((forall y0 : nat, (0 = (BIT0 y0)) = (0 = y0)) /\ ((forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1))))))).
Definition term183 (x0 : nat) := Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.mul x0 x0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0).
Definition term42 (a0 : Type') (x0 : a0) := (fun y0 : a0 => (y0 = y0) = True) x0.
Definition term173 (x0 : nat) := Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.add x0 (Nat.mul x0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0))).
Definition term70 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.mul x0 (Nat.mul x1 y0)) = (Nat.mul (Nat.mul x0 x1) y0).
Definition term87 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((S x0) = (S y0)) = (x0 = y0)) x1.
Definition term18 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((NUMERAL x0) = (NUMERAL y0)) = (x0 = y0)) x1.
Definition term96 := (forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))).
Definition term131 (x0 : nat) (x1 : nat) := @eq nat (Nat.pow (S (Nat.add x0 x0)) x1).
Definition term194 (x0 : nat) (x1 : nat) := False \/ ((Nat.add (Nat.mul x0 x0) x0) = (Nat.add x0 x1)).
Definition term176 (x0 : nat) := Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.add (Nat.add x0 (Nat.mul x0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0))) x0).
Definition term67 (x0 : nat) := @eq nat (Nat.add x0 (Nat.add x0 (Nat.mul x0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)))).
Definition term154 (x0 : nat) (x1 : nat) := Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.add x0 x1)).
Definition term65 (x0 : nat) := Nat.add x0 (Nat.add x0 (Nat.mul x0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0))).
Definition term52 (x0 : nat) := Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.mul x0 x0).
Definition term180 (x0 : nat) := @eq nat (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.add (Nat.mul x0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) (Nat.add x0 x0))).
Definition term45 (x0 : nat) := Nat.mul x0 (NUMERAL (BIT0 (BIT1 0))).
Definition term75 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Nat.mul (Nat.mul x0 y0) y1) = (Nat.mul x0 (Nat.mul y0 y1)).
Definition term32 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y1)) = (Nat.mul x0 (Nat.add y0 y1)).
Definition term31 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Nat.mul x0 (Nat.add y0 y1)) = (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y1)).
Definition term63 (x0 : nat) := Nat.add (Nat.mul x0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) x0.
Definition term128 (x0 : nat) (x1 : nat) := BIT1 (BIT0 (Nat.add x0 x1)).
Definition term137 (x0 : nat) (x1 : nat) := Nat.add (BIT0 (Nat.add x0 x1)) (BIT0 (Nat.add x0 x1)).
Definition term79 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.mul (Nat.mul y0 y1) y2) = (Nat.mul y0 (Nat.mul y1 y2)).
Definition term78 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.mul y0 (Nat.mul y1 y2)) = (Nat.mul (Nat.mul y0 y1) y2).
Definition term36 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y2)) = (Nat.mul y0 (Nat.add y1 y2)).
Definition term35 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.mul y0 (Nat.add y1 y2)) = (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y2)).
Definition term181 (x0 : nat) := Nat.add (Nat.mul x0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)).
Definition term49 (x0 : nat) := @eq nat (Nat.mul x0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)).
Definition term92 (x0 : nat) := forall y0 : nat, (Nat.add x0 (S y0)) = (S (Nat.add x0 y0)).
