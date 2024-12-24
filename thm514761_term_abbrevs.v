Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term175 (x0 : nat) (x1 : nat) := @eq nat (Nat.add (Nat.add x0 x0) (Nat.mul (Nat.add x0 x0) (Nat.add x1 x1))).
Definition term214 (x0 : nat) (x1 : nat) := Nat.add (Nat.add (Nat.add x0 x0) (Nat.mul (Nat.add x0 x0) (Nat.add x1 x1))).
Definition term92 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.mul x0 (S y0)) = (Nat.add x0 (Nat.mul x0 y0))) x1.
Definition term144 (x0 : nat) := @eq nat (Nat.mul (BIT1 x0) 0).
Definition term139 (x0 : nat) := @eq nat (Nat.mul (BIT0 x0) 0).
Definition term107 (x0 : nat) := Nat.mul (NUMERAL x0).
Definition term27 (x0 : nat) := @eq nat (Nat.mul 0 x0).
Definition term70 := (forall y0 : nat, (Nat.mul (BIT1 0) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (BIT1 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))))).
Definition term69 := (forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))))).
Definition term23 := (forall y0 : nat, (Nat.add 0 y0) = y0) /\ ((forall y0 : nat, (Nat.add y0 0) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))))).
Definition term22 := (forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0) /\ ((forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))))).
Definition term30 := forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0).
Definition term111 (x0 : nat) (x1 : nat) := NUMERAL (Nat.mul x0 x1).
Definition term222 (x0 : nat) (x1 : nat) := Nat.add (BIT1 x0) (Nat.add (BIT0 x1) (BIT0 (BIT0 (Nat.mul x0 x1)))).
Definition term190 (x0 : nat) := Nat.mul (BIT1 x0).
Definition term225 (x0 : nat) (x1 : nat) := Nat.add (Nat.add x0 x0) (Nat.add (Nat.add x1 x1) (Nat.add (Nat.add (Nat.mul x0 x1) (Nat.mul x0 x1)) (Nat.add (Nat.mul x0 x1) (Nat.mul x0 x1)))).
Definition term180 (x0 : nat) := fun y0 : nat => (Nat.mul (BIT0 x0) (BIT1 y0)) = (Nat.add (BIT0 x0) (BIT0 (BIT0 (Nat.mul x0 y0)))).
Definition term73 := (forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))))))).
Definition term138 (x0 : nat) := Nat.mul (BIT0 x0) 0.
Definition term47 (x0 : nat) := Nat.mul (BIT1 0) x0.
Definition term193 (x0 : nat) (x1 : nat) := Nat.mul (S (Nat.add x0 x0)) (Nat.add x1 x1).
Definition term153 (x0 : nat) (x1 : nat) := @eq nat (Nat.mul (Nat.add x0 x0) (Nat.add x1 x1)).
Definition term248 := ((Nat.mul 0 0) = 0) /\ ((forall y0 : nat, (Nat.mul 0 (BIT0 y0)) = 0) /\ ((forall y0 : nat, (Nat.mul 0 (BIT1 y0)) = 0) /\ ((forall y0 : nat, (Nat.mul (BIT0 y0) 0) = 0) /\ ((forall y0 : nat, (Nat.mul (BIT1 y0) 0) = 0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT0 y0) (BIT0 y1)) = (BIT0 (BIT0 (Nat.mul y0 y1)))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT0 y0) (BIT1 y1)) = (Nat.add (BIT0 y0) (BIT0 (BIT0 (Nat.mul y0 y1))))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT1 y0) (BIT0 y1)) = (Nat.add (BIT0 y1) (BIT0 (BIT0 (Nat.mul y0 y1))))) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul (BIT1 y0) (BIT1 y1)) = (Nat.add (BIT1 y0) (Nat.add (BIT0 y1) (BIT0 (BIT0 (Nat.mul y0 y1))))))))))))).
Definition term143 (x0 : nat) := Nat.mul (BIT1 x0) 0.
Definition term29 := fun y0 : nat => (Nat.mul 0 y0) = 0.
Definition term147 := and (forall y0 : nat, (Nat.mul (BIT1 y0) 0) = 0).
Definition term142 := and (forall y0 : nat, (Nat.mul (BIT0 y0) 0) = 0).
Definition term137 := and (forall y0 : nat, (Nat.mul 0 (BIT1 y0)) = 0).
Definition term132 := and (forall y0 : nat, 0 = 0).
Definition term131 := and (forall y0 : nat, (Nat.mul 0 (BIT0 y0)) = 0).
Definition term42 := and (forall y0 : nat, (Nat.mul y0 0) = 0).
Definition term33 := and (forall y0 : nat, (Nat.mul 0 y0) = 0).
Definition term91 (x0 : nat) := forall y0 : nat, (Nat.mul x0 (S y0)) = (Nat.add x0 (Nat.mul x0 y0)).
Definition term36 (x0 : nat) := @eq nat (Nat.mul x0 0).
Definition term12 (x0 : nat) := @eq nat (Nat.add x0 0).
Definition term31 := forall y0 : nat, (Nat.mul 0 y0) = 0.
Definition term235 := (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul (Nat.add y0 y0) (Nat.add y1 y1)) (Nat.add y1 y1)) = (Nat.add (Nat.add y1 y1) (Nat.add (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1)) (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1))))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add (Nat.add y0 y0) (Nat.mul (Nat.add y0 y0) (Nat.add y1 y1))) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y0) (Nat.add (Nat.add y1 y1) (Nat.add (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1)) (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1)))))).
Definition term234 := (forall y0 : nat, forall y1 : nat, (Nat.mul (BIT1 y0) (BIT0 y1)) = (Nat.add (BIT0 y1) (BIT0 (BIT0 (Nat.mul y0 y1))))) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul (BIT1 y0) (BIT1 y1)) = (Nat.add (BIT1 y0) (Nat.add (BIT0 y1) (BIT0 (BIT0 (Nat.mul y0 y1)))))).
Definition term66 := (forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))).
Definition term19 := (forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))).
Definition term176 (x0 : nat) := Nat.add (BIT0 x0).
Definition term156 (x0 : nat) (x1 : nat) := BIT0 (Nat.mul x0 x1).
Definition term101 (x0 : nat) := (fun y0 : nat => (Nat.mul y0 0) = 0) x0.
Definition term158 (x0 : nat) (x1 : nat) := Nat.add (BIT0 (Nat.mul x0 x1)).
Definition term51 := fun y0 : nat => (Nat.mul (BIT1 0) y0) = y0.
Definition term50 := fun y0 : nat => (Nat.mul (NUMERAL (BIT1 0)) y0) = y0.
Definition term98 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.mul (S x0) y0) = (Nat.add (Nat.mul x0 y0) y0)) x1.
Definition term128 := fun y0 : nat => 0 = 0.
Definition term76 (x0 : nat) := forall y0 : nat, ((S x0) = (S y0)) = (x0 = y0).
Definition term112 (x0 : nat) := fun y0 : nat => (Nat.mul (NUMERAL x0) (NUMERAL y0)) = (NUMERAL (Nat.mul x0 y0)).
Definition term213 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul (Nat.add x0 x0) (S (Nat.add x1 x1))).
Definition term209 (x0 : nat) (x1 : nat) := Nat.mul (BIT1 x0) (BIT1 x1).
Definition term249 := (0 = 0) /\ ((forall y0 : nat, 0 = 0) /\ ((forall y0 : nat, 0 = 0) /\ ((forall y0 : nat, 0 = 0) /\ ((forall y0 : nat, 0 = 0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1)) (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1)))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.mul (Nat.add y0 y0) (Nat.add y1 y1))) = (Nat.add (Nat.add y0 y0) (Nat.add (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1)) (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1))))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul (Nat.add y0 y0) (Nat.add y1 y1)) (Nat.add y1 y1)) = (Nat.add (Nat.add y1 y1) (Nat.add (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1)) (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1))))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add (Nat.add y0 y0) (Nat.mul (Nat.add y0 y0) (Nat.add y1 y1))) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y0) (Nat.add (Nat.add y1 y1) (Nat.add (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1)) (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1))))))))))))).
Definition term61 := fun y0 : nat => (Nat.mul y0 (BIT1 0)) = y0.
Definition term133 (x0 : nat) := Nat.mul 0 (BIT1 x0).
Definition term212 (x0 : nat) (x1 : nat) := S (Nat.add (Nat.mul (Nat.add x0 x0) (S (Nat.add x1 x1))) (Nat.add x1 x1)).
Definition term122 := @eq nat (Nat.mul 0 0).
Definition term163 (x0 : nat) := forall y0 : nat, (Nat.mul (BIT0 x0) (BIT0 y0)) = (BIT0 (BIT0 (Nat.mul x0 y0))).
Definition term86 (x0 : nat) := forall y0 : nat, (Nat.add (S x0) y0) = (S (Nat.add x0 y0)).
Definition term161 (x0 : nat) := fun y0 : nat => (Nat.mul (BIT0 x0) (BIT0 y0)) = (BIT0 (BIT0 (Nat.mul x0 y0))).
Definition term58 (x0 : nat) := @eq nat (Nat.mul x0 (NUMERAL (BIT1 0))).
Definition term13 := fun y0 : nat => (Nat.add y0 (NUMERAL 0)) = y0.
Definition term10 (x0 : nat) := Nat.add x0 (NUMERAL 0).
Definition term152 (x0 : nat) (x1 : nat) := @eq nat (Nat.mul (BIT0 x0) (BIT0 x1)).
Definition term60 := fun y0 : nat => (Nat.mul y0 (NUMERAL (BIT1 0))) = y0.
Definition term220 (x0 : nat) := Nat.add (BIT1 x0).
Definition term229 (x0 : nat) := forall y0 : nat, (Nat.add (Nat.add (Nat.add x0 x0) (Nat.mul (Nat.add x0 x0) (Nat.add y0 y0))) (Nat.add y0 y0)) = (Nat.add (Nat.add x0 x0) (Nat.add (Nat.add y0 y0) (Nat.add (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y0)) (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y0))))).
Definition term228 (x0 : nat) := forall y0 : nat, (Nat.mul (BIT1 x0) (BIT1 y0)) = (Nat.add (BIT1 x0) (Nat.add (BIT0 y0) (BIT0 (BIT0 (Nat.mul x0 y0))))).
Definition term202 (x0 : nat) := forall y0 : nat, (Nat.add (Nat.mul (Nat.add x0 x0) (Nat.add y0 y0)) (Nat.add y0 y0)) = (Nat.add (Nat.add y0 y0) (Nat.add (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y0)) (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y0)))).
Definition term183 (x0 : nat) := forall y0 : nat, (Nat.add (Nat.add x0 x0) (Nat.mul (Nat.add x0 x0) (Nat.add y0 y0))) = (Nat.add (Nat.add x0 x0) (Nat.add (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y0)) (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y0)))).
Definition term164 (x0 : nat) := forall y0 : nat, (Nat.mul (Nat.add x0 x0) (Nat.add y0 y0)) = (Nat.add (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y0)) (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y0))).
Definition term99 (x0 : nat) (x1 : nat) := Nat.mul (S x0) x1.
Definition term159 (x0 : nat) (x1 : nat) := Nat.add (Nat.add (Nat.mul x0 x1) (Nat.mul x0 x1)).
Definition term117 := fun y0 : nat => forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y0 y1).
Definition term239 := (forall y0 : nat, forall y1 : nat, (Nat.mul (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1)) (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1)))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.mul (Nat.add y0 y0) (Nat.add y1 y1))) = (Nat.add (Nat.add y0 y0) (Nat.add (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1)) (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1))))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul (Nat.add y0 y0) (Nat.add y1 y1)) (Nat.add y1 y1)) = (Nat.add (Nat.add y1 y1) (Nat.add (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1)) (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1))))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add (Nat.add y0 y0) (Nat.mul (Nat.add y0 y0) (Nat.add y1 y1))) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y0) (Nat.add (Nat.add y1 y1) (Nat.add (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1)) (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1)))))))).
Definition term238 := (forall y0 : nat, forall y1 : nat, (Nat.mul (BIT0 y0) (BIT0 y1)) = (BIT0 (BIT0 (Nat.mul y0 y1)))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT0 y0) (BIT1 y1)) = (Nat.add (BIT0 y0) (BIT0 (BIT0 (Nat.mul y0 y1))))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT1 y0) (BIT0 y1)) = (Nat.add (BIT0 y1) (BIT0 (BIT0 (Nat.mul y0 y1))))) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul (BIT1 y0) (BIT1 y1)) = (Nat.add (BIT1 y0) (Nat.add (BIT0 y1) (BIT0 (BIT0 (Nat.mul y0 y1)))))))).
Definition term160 (x0 : nat) (x1 : nat) := Nat.add (Nat.add (Nat.mul x0 x1) (Nat.mul x0 x1)) (Nat.add (Nat.mul x0 x1) (Nat.mul x0 x1)).
Definition term93 (x0 : nat) (x1 : nat) := Nat.mul x0 (S x1).
Definition term146 := forall y0 : nat, (Nat.mul (BIT1 y0) 0) = 0.
Definition term141 := forall y0 : nat, (Nat.mul (BIT0 y0) 0) = 0.
Definition term40 := forall y0 : nat, (Nat.mul y0 0) = 0.
Definition term104 (x0 : nat) := S (Nat.add x0 x0).
Definition term2 (x0 : nat) := @eq nat (Nat.add (NUMERAL 0) x0).
Definition term227 (x0 : nat) := fun y0 : nat => (Nat.add (Nat.add (Nat.add x0 x0) (Nat.mul (Nat.add x0 x0) (Nat.add y0 y0))) (Nat.add y0 y0)) = (Nat.add (Nat.add x0 x0) (Nat.add (Nat.add y0 y0) (Nat.add (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y0)) (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y0))))).
Definition term114 (x0 : nat) := forall y0 : nat, (Nat.mul (NUMERAL x0) (NUMERAL y0)) = (NUMERAL (Nat.mul x0 y0)).
Definition term150 (x0 : nat) (x1 : nat) := Nat.mul (BIT0 x0) (BIT0 x1).
Definition term63 := forall y0 : nat, (Nat.mul y0 (BIT1 0)) = y0.
Definition term62 := forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0.
Definition term15 := forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0.
Definition term237 := (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.mul (Nat.add y0 y0) (Nat.add y1 y1))) = (Nat.add (Nat.add y0 y0) (Nat.add (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1)) (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1))))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul (Nat.add y0 y0) (Nat.add y1 y1)) (Nat.add y1 y1)) = (Nat.add (Nat.add y1 y1) (Nat.add (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1)) (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1))))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add (Nat.add y0 y0) (Nat.mul (Nat.add y0 y0) (Nat.add y1 y1))) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y0) (Nat.add (Nat.add y1 y1) (Nat.add (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1)) (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1))))))).
Definition term236 := (forall y0 : nat, forall y1 : nat, (Nat.mul (BIT0 y0) (BIT1 y1)) = (Nat.add (BIT0 y0) (BIT0 (BIT0 (Nat.mul y0 y1))))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT1 y0) (BIT0 y1)) = (Nat.add (BIT0 y1) (BIT0 (BIT0 (Nat.mul y0 y1))))) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul (BIT1 y0) (BIT1 y1)) = (Nat.add (BIT1 y0) (Nat.add (BIT0 y1) (BIT0 (BIT0 (Nat.mul y0 y1))))))).
Definition term35 (x0 : nat) := @eq nat (Nat.mul x0 (NUMERAL 0)).
Definition term105 (x0 : nat) := (fun y0 : nat => (BIT0 y0) = (Nat.add y0 y0)) x0.
Definition term11 (x0 : nat) := @eq nat (Nat.add x0 (NUMERAL 0)).
Definition term48 (x0 : nat) := @eq nat (Nat.mul (NUMERAL (BIT1 0)) x0).
Definition term102 (x0 : nat) := (fun y0 : nat => (Nat.mul 0 y0) = 0) x0.
Definition term87 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add (S x0) y0) = (S (Nat.add x0 y0))) x1.
Definition term41 := and (forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)).
Definition term32 := and (forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)).
Definition term115 (x0 : nat) := forall y0 : nat, (Nat.mul x0 y0) = (Nat.mul x0 y0).
Definition term151 (x0 : nat) (x1 : nat) := Nat.mul (Nat.add x0 x0) (Nat.add x1 x1).
Definition term106 (x0 : nat) := (fun y0 : nat => (NUMERAL y0) = y0) x0.
Definition term218 (x0 : nat) (x1 : nat) := @eq nat (Nat.mul (BIT1 x0) (BIT1 x1)).
Definition term1 (x0 : nat) := Nat.add (NUMERAL 0) x0.
Definition term14 := fun y0 : nat => (Nat.add y0 0) = y0.
Definition term83 (x0 : nat) (x1 : nat) := S (Nat.add x0 x1).
Definition term226 (x0 : nat) := fun y0 : nat => (Nat.mul (BIT1 x0) (BIT1 y0)) = (Nat.add (BIT1 x0) (Nat.add (BIT0 y0) (BIT0 (BIT0 (Nat.mul x0 y0))))).
Definition term136 := forall y0 : nat, (Nat.mul 0 (BIT1 y0)) = 0.
Definition term129 := forall y0 : nat, (Nat.mul 0 (BIT0 y0)) = 0.
Definition term65 := and (forall y0 : nat, (Nat.mul y0 (BIT1 0)) = y0).
Definition term64 := and (forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0).
Definition term55 := and (forall y0 : nat, (Nat.mul (BIT1 0) y0) = y0).
Definition term54 := and (forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0).
Definition term18 := and (forall y0 : nat, (Nat.add y0 0) = y0).
Definition term17 := and (forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0).
Definition term9 := and (forall y0 : nat, (Nat.add 0 y0) = y0).
Definition term8 := and (forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0).
Definition term49 (x0 : nat) := @eq nat (Nat.mul (BIT1 0) x0).
Definition term26 (x0 : nat) := @eq nat (Nat.mul (NUMERAL 0) x0).
Definition term233 := forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add (Nat.add y0 y0) (Nat.mul (Nat.add y0 y0) (Nat.add y1 y1))) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y0) (Nat.add (Nat.add y1 y1) (Nat.add (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1)) (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1))))).
Definition term232 := forall y0 : nat, forall y1 : nat, (Nat.mul (BIT1 y0) (BIT1 y1)) = (Nat.add (BIT1 y0) (Nat.add (BIT0 y1) (BIT0 (BIT0 (Nat.mul y0 y1))))).
Definition term206 := forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul (Nat.add y0 y0) (Nat.add y1 y1)) (Nat.add y1 y1)) = (Nat.add (Nat.add y1 y1) (Nat.add (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1)) (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1)))).
Definition term205 := forall y0 : nat, forall y1 : nat, (Nat.mul (BIT1 y0) (BIT0 y1)) = (Nat.add (BIT0 y1) (BIT0 (BIT0 (Nat.mul y0 y1)))).
Definition term187 := forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.mul (Nat.add y0 y0) (Nat.add y1 y1))) = (Nat.add (Nat.add y0 y0) (Nat.add (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1)) (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1)))).
Definition term186 := forall y0 : nat, forall y1 : nat, (Nat.mul (BIT0 y0) (BIT1 y1)) = (Nat.add (BIT0 y0) (BIT0 (BIT0 (Nat.mul y0 y1)))).
Definition term168 := forall y0 : nat, forall y1 : nat, (Nat.mul (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1)) (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1))).
Definition term167 := forall y0 : nat, forall y1 : nat, (Nat.mul (BIT0 y0) (BIT0 y1)) = (BIT0 (BIT0 (Nat.mul y0 y1))).
Definition term119 := forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y0 y1).
Definition term118 := forall y0 : nat, forall y1 : nat, (Nat.mul (NUMERAL y0) (NUMERAL y1)) = (NUMERAL (Nat.mul y0 y1)).
Definition term95 := forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1).
Definition term89 := forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)).
Definition term84 := forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1)).
Definition term78 := forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)).
Definition term154 (x0 : nat) (x1 : nat) := BIT0 (BIT0 (Nat.mul x0 x1)).
Definition term178 (x0 : nat) (x1 : nat) := Nat.add (BIT0 x0) (BIT0 (BIT0 (Nat.mul x0 x1))).
Definition term53 := forall y0 : nat, (Nat.mul (BIT1 0) y0) = y0.
Definition term52 := forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0.
Definition term7 := forall y0 : nat, (Nat.add 0 y0) = y0.
Definition term6 := forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0.
Definition term126 (x0 : nat) := @eq nat (Nat.mul 0 (BIT0 x0)).
Definition term57 (x0 : nat) := Nat.mul x0 (BIT1 0).
Definition term5 := fun y0 : nat => (Nat.add 0 y0) = y0.
Definition term97 (x0 : nat) := forall y0 : nat, (Nat.mul (S x0) y0) = (Nat.add (Nat.mul x0 y0) y0).
Definition term221 (x0 : nat) := Nat.add (S (Nat.add x0 x0)).
Definition term103 (x0 : nat) := (fun y0 : nat => (BIT1 y0) = (S (Nat.add y0 y0))) x0.
Definition term108 (x0 : nat) (x1 : nat) := Nat.mul (NUMERAL x0) (NUMERAL x1).
Definition term124 := and (0 = 0).
Definition term194 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul (Nat.add x0 x0) (Nat.add x1 x1)) (Nat.add x1 x1).
Definition term224 (x0 : nat) (x1 : nat) := S (Nat.add (Nat.add x0 x0) (Nat.add (Nat.add x1 x1) (Nat.add (Nat.add (Nat.mul x0 x1) (Nat.mul x0 x1)) (Nat.add (Nat.mul x0 x1) (Nat.mul x0 x1))))).
Definition term148 (x0 : nat) := Nat.mul (BIT0 x0).
Definition term113 (x0 : nat) := fun y0 : nat => (Nat.mul x0 y0) = (Nat.mul x0 y0).
Definition term37 := fun y0 : nat => (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0).
Definition term81 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add x0 (S y0)) = (S (Nat.add x0 y0))) x1.
Definition term198 (x0 : nat) (x1 : nat) := Nat.add (Nat.add x1 x1) (Nat.add (Nat.add (Nat.mul x0 x1) (Nat.mul x0 x1)) (Nat.add (Nat.mul x0 x1) (Nat.mul x0 x1))).
Definition term181 (x0 : nat) := fun y0 : nat => (Nat.add (Nat.add x0 x0) (Nat.mul (Nat.add x0 x0) (Nat.add y0 y0))) = (Nat.add (Nat.add x0 x0) (Nat.add (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y0)) (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y0)))).
Definition term68 := (forall y0 : nat, (Nat.mul y0 (BIT1 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))).
Definition term67 := (forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))).
Definition term21 := (forall y0 : nat, (Nat.add y0 0) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))).
Definition term20 := (forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))).
Definition term38 := fun y0 : nat => (Nat.mul y0 0) = 0.
Definition term200 (x0 : nat) := fun y0 : nat => (Nat.add (Nat.mul (Nat.add x0 x0) (Nat.add y0 y0)) (Nat.add y0 y0)) = (Nat.add (Nat.add y0 y0) (Nat.add (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y0)) (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y0)))).
Definition term135 := fun y0 : nat => (Nat.mul 0 (BIT1 y0)) = 0.
Definition term127 := fun y0 : nat => (Nat.mul 0 (BIT0 y0)) = 0.
Definition term0 := Nat.add (NUMERAL 0).
Definition term208 := and (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul (Nat.add y0 y0) (Nat.add y1 y1)) (Nat.add y1 y1)) = (Nat.add (Nat.add y1 y1) (Nat.add (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1)) (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1))))).
Definition term207 := and (forall y0 : nat, forall y1 : nat, (Nat.mul (BIT1 y0) (BIT0 y1)) = (Nat.add (BIT0 y1) (BIT0 (BIT0 (Nat.mul y0 y1))))).
Definition term189 := and (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.mul (Nat.add y0 y0) (Nat.add y1 y1))) = (Nat.add (Nat.add y0 y0) (Nat.add (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1)) (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1))))).
Definition term188 := and (forall y0 : nat, forall y1 : nat, (Nat.mul (BIT0 y0) (BIT1 y1)) = (Nat.add (BIT0 y0) (BIT0 (BIT0 (Nat.mul y0 y1))))).
Definition term170 := and (forall y0 : nat, forall y1 : nat, (Nat.mul (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1)) (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1)))).
Definition term169 := and (forall y0 : nat, forall y1 : nat, (Nat.mul (BIT0 y0) (BIT0 y1)) = (BIT0 (BIT0 (Nat.mul y0 y1)))).
Definition term121 := and (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y0 y1)).
Definition term120 := and (forall y0 : nat, forall y1 : nat, (Nat.mul (NUMERAL y0) (NUMERAL y1)) = (NUMERAL (Nat.mul y0 y1))).
Definition term56 (x0 : nat) := Nat.mul x0 (NUMERAL (BIT1 0)).
Definition term96 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) x0.
Definition term90 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))) x0.
Definition term85 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) x0.
Definition term79 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))) x0.
Definition term75 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((S y0) = (S y1)) = (y0 = y1)) x0.
Definition term219 (x0 : nat) (x1 : nat) := @eq nat (S (Nat.add (Nat.add (Nat.add x0 x0) (Nat.mul (Nat.add x0 x0) (Nat.add x1 x1))) (Nat.add x1 x1))).
Definition term39 := forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0).
Definition term199 (x0 : nat) := fun y0 : nat => (Nat.mul (BIT1 x0) (BIT0 y0)) = (Nat.add (BIT0 y0) (BIT0 (BIT0 (Nat.mul x0 y0)))).
Definition term45 := Nat.mul (BIT1 0).
Definition term100 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x0 x1) x1.
Definition term215 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul (Nat.add x0 x0) (S (Nat.add x1 x1))) (Nat.add x1 x1).
Definition term94 (x0 : nat) (x1 : nat) := Nat.add x0 (Nat.mul x0 x1).
Definition term191 (x0 : nat) := Nat.mul (S (Nat.add x0 x0)).
Definition term34 (x0 : nat) := Nat.mul x0 (NUMERAL 0).
Definition term173 (x0 : nat) (x1 : nat) := Nat.add (Nat.add x0 x0) (Nat.mul (Nat.add x0 x0) (Nat.add x1 x1)).
Definition term16 := forall y0 : nat, (Nat.add y0 0) = y0.
Definition term197 (x0 : nat) (x1 : nat) := Nat.add (BIT0 x1) (BIT0 (BIT0 (Nat.mul x0 x1))).
Definition term171 (x0 : nat) (x1 : nat) := Nat.mul (BIT0 x0) (BIT1 x1).
Definition term82 (x0 : nat) (x1 : nat) := Nat.add x0 (S x1).
Definition term172 (x0 : nat) (x1 : nat) := Nat.mul (Nat.add x0 x0) (S (Nat.add x1 x1)).
Definition term210 (x0 : nat) (x1 : nat) := Nat.mul (S (Nat.add x0 x0)) (S (Nat.add x1 x1)).
Definition term196 (x0 : nat) (x1 : nat) := @eq nat (Nat.add (Nat.mul (Nat.add x0 x0) (Nat.add x1 x1)) (Nat.add x1 x1)).
Definition term125 (x0 : nat) := Nat.mul 0 (BIT0 x0).
Definition term157 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x0 x1) (Nat.mul x0 x1).
Definition term162 (x0 : nat) := fun y0 : nat => (Nat.mul (Nat.add x0 x0) (Nat.add y0 y0)) = (Nat.add (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y0)) (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y0))).
Definition term177 (x0 : nat) := Nat.add (Nat.add x0 x0).
Definition term110 (x0 : nat) (x1 : nat) := @eq nat (Nat.mul x0 x1).
Definition term145 := fun y0 : nat => (Nat.mul (BIT1 y0) 0) = 0.
Definition term140 := fun y0 : nat => (Nat.mul (BIT0 y0) 0) = 0.
Definition term59 (x0 : nat) := @eq nat (Nat.mul x0 (BIT1 0)).
Definition term155 (x0 : nat) (x1 : nat) := Nat.add (BIT0 (Nat.mul x0 x1)) (BIT0 (Nat.mul x0 x1)).
Definition term223 (x0 : nat) (x1 : nat) := Nat.add (S (Nat.add x0 x0)) (Nat.add (Nat.add x1 x1) (Nat.add (Nat.add (Nat.mul x0 x1) (Nat.mul x0 x1)) (Nat.add (Nat.mul x0 x1) (Nat.mul x0 x1)))).
Definition term165 := fun y0 : nat => forall y1 : nat, (Nat.mul (BIT0 y0) (BIT0 y1)) = (BIT0 (BIT0 (Nat.mul y0 y1))).
Definition term116 := fun y0 : nat => forall y1 : nat, (Nat.mul (NUMERAL y0) (NUMERAL y1)) = (NUMERAL (Nat.mul y0 y1)).
Definition term217 (x0 : nat) (x1 : nat) := S (Nat.add (Nat.add (Nat.add x0 x0) (Nat.mul (Nat.add x0 x0) (Nat.add x1 x1))) (Nat.add x1 x1)).
Definition term4 := fun y0 : nat => (Nat.add (NUMERAL 0) y0) = y0.
Definition term192 (x0 : nat) (x1 : nat) := Nat.mul (BIT1 x0) (BIT0 x1).
Definition term24 := Nat.mul (NUMERAL 0).
Definition term134 (x0 : nat) := @eq nat (Nat.mul 0 (BIT1 x0)).
Definition term247 := (forall y0 : nat, 0 = 0) /\ ((forall y0 : nat, 0 = 0) /\ ((forall y0 : nat, 0 = 0) /\ ((forall y0 : nat, 0 = 0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1)) (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1)))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.mul (Nat.add y0 y0) (Nat.add y1 y1))) = (Nat.add (Nat.add y0 y0) (Nat.add (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1)) (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1))))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul (Nat.add y0 y0) (Nat.add y1 y1)) (Nat.add y1 y1)) = (Nat.add (Nat.add y1 y1) (Nat.add (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1)) (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1))))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add (Nat.add y0 y0) (Nat.mul (Nat.add y0 y0) (Nat.add y1 y1))) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y0) (Nat.add (Nat.add y1 y1) (Nat.add (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1)) (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1)))))))))))).
Definition term246 := (forall y0 : nat, (Nat.mul 0 (BIT0 y0)) = 0) /\ ((forall y0 : nat, (Nat.mul 0 (BIT1 y0)) = 0) /\ ((forall y0 : nat, (Nat.mul (BIT0 y0) 0) = 0) /\ ((forall y0 : nat, (Nat.mul (BIT1 y0) 0) = 0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT0 y0) (BIT0 y1)) = (BIT0 (BIT0 (Nat.mul y0 y1)))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT0 y0) (BIT1 y1)) = (Nat.add (BIT0 y0) (BIT0 (BIT0 (Nat.mul y0 y1))))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT1 y0) (BIT0 y1)) = (Nat.add (BIT0 y1) (BIT0 (BIT0 (Nat.mul y0 y1))))) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul (BIT1 y0) (BIT1 y1)) = (Nat.add (BIT1 y0) (Nat.add (BIT0 y1) (BIT0 (BIT0 (Nat.mul y0 y1)))))))))))).
Definition term245 := (forall y0 : nat, 0 = 0) /\ ((forall y0 : nat, 0 = 0) /\ ((forall y0 : nat, 0 = 0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1)) (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1)))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.mul (Nat.add y0 y0) (Nat.add y1 y1))) = (Nat.add (Nat.add y0 y0) (Nat.add (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1)) (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1))))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul (Nat.add y0 y0) (Nat.add y1 y1)) (Nat.add y1 y1)) = (Nat.add (Nat.add y1 y1) (Nat.add (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1)) (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1))))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add (Nat.add y0 y0) (Nat.mul (Nat.add y0 y0) (Nat.add y1 y1))) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y0) (Nat.add (Nat.add y1 y1) (Nat.add (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1)) (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1))))))))))).
Definition term244 := (forall y0 : nat, (Nat.mul 0 (BIT1 y0)) = 0) /\ ((forall y0 : nat, (Nat.mul (BIT0 y0) 0) = 0) /\ ((forall y0 : nat, (Nat.mul (BIT1 y0) 0) = 0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT0 y0) (BIT0 y1)) = (BIT0 (BIT0 (Nat.mul y0 y1)))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT0 y0) (BIT1 y1)) = (Nat.add (BIT0 y0) (BIT0 (BIT0 (Nat.mul y0 y1))))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT1 y0) (BIT0 y1)) = (Nat.add (BIT0 y1) (BIT0 (BIT0 (Nat.mul y0 y1))))) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul (BIT1 y0) (BIT1 y1)) = (Nat.add (BIT1 y0) (Nat.add (BIT0 y1) (BIT0 (BIT0 (Nat.mul y0 y1))))))))))).
Definition term243 := (forall y0 : nat, 0 = 0) /\ ((forall y0 : nat, 0 = 0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1)) (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1)))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.mul (Nat.add y0 y0) (Nat.add y1 y1))) = (Nat.add (Nat.add y0 y0) (Nat.add (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1)) (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1))))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul (Nat.add y0 y0) (Nat.add y1 y1)) (Nat.add y1 y1)) = (Nat.add (Nat.add y1 y1) (Nat.add (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1)) (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1))))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add (Nat.add y0 y0) (Nat.mul (Nat.add y0 y0) (Nat.add y1 y1))) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y0) (Nat.add (Nat.add y1 y1) (Nat.add (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1)) (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1)))))))))).
Definition term242 := (forall y0 : nat, (Nat.mul (BIT0 y0) 0) = 0) /\ ((forall y0 : nat, (Nat.mul (BIT1 y0) 0) = 0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT0 y0) (BIT0 y1)) = (BIT0 (BIT0 (Nat.mul y0 y1)))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT0 y0) (BIT1 y1)) = (Nat.add (BIT0 y0) (BIT0 (BIT0 (Nat.mul y0 y1))))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT1 y0) (BIT0 y1)) = (Nat.add (BIT0 y1) (BIT0 (BIT0 (Nat.mul y0 y1))))) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul (BIT1 y0) (BIT1 y1)) = (Nat.add (BIT1 y0) (Nat.add (BIT0 y1) (BIT0 (BIT0 (Nat.mul y0 y1)))))))))).
Definition term74 := (forall y0 : nat, (Nat.mul 0 y0) = 0) /\ ((forall y0 : nat, (Nat.mul y0 0) = 0) /\ ((forall y0 : nat, (Nat.mul (BIT1 0) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (BIT1 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))))))).
Definition term25 (x0 : nat) := Nat.mul (NUMERAL 0) x0.
Definition term3 (x0 : nat) := @eq nat (Nat.add 0 x0).
Definition term109 (x0 : nat) (x1 : nat) := @eq nat (Nat.mul (NUMERAL x0) (NUMERAL x1)).
Definition term211 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul (Nat.add x0 x0) (S (Nat.add x1 x1))) (S (Nat.add x1 x1)).
Definition term251 := (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y0 y1)) /\ ((0 = 0) /\ ((forall y0 : nat, 0 = 0) /\ ((forall y0 : nat, 0 = 0) /\ ((forall y0 : nat, 0 = 0) /\ ((forall y0 : nat, 0 = 0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1)) (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1)))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.mul (Nat.add y0 y0) (Nat.add y1 y1))) = (Nat.add (Nat.add y0 y0) (Nat.add (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1)) (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1))))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul (Nat.add y0 y0) (Nat.add y1 y1)) (Nat.add y1 y1)) = (Nat.add (Nat.add y1 y1) (Nat.add (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1)) (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1))))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add (Nat.add y0 y0) (Nat.mul (Nat.add y0 y0) (Nat.add y1 y1))) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y0) (Nat.add (Nat.add y1 y1) (Nat.add (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1)) (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1)))))))))))))).
Definition term174 (x0 : nat) (x1 : nat) := @eq nat (Nat.mul (BIT0 x0) (BIT1 x1)).
Definition term250 := (forall y0 : nat, forall y1 : nat, (Nat.mul (NUMERAL y0) (NUMERAL y1)) = (NUMERAL (Nat.mul y0 y1))) /\ (((Nat.mul 0 0) = 0) /\ ((forall y0 : nat, (Nat.mul 0 (BIT0 y0)) = 0) /\ ((forall y0 : nat, (Nat.mul 0 (BIT1 y0)) = 0) /\ ((forall y0 : nat, (Nat.mul (BIT0 y0) 0) = 0) /\ ((forall y0 : nat, (Nat.mul (BIT1 y0) 0) = 0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT0 y0) (BIT0 y1)) = (BIT0 (BIT0 (Nat.mul y0 y1)))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT0 y0) (BIT1 y1)) = (Nat.add (BIT0 y0) (BIT0 (BIT0 (Nat.mul y0 y1))))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT1 y0) (BIT0 y1)) = (Nat.add (BIT0 y1) (BIT0 (BIT0 (Nat.mul y0 y1))))) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul (BIT1 y0) (BIT1 y1)) = (Nat.add (BIT1 y0) (Nat.add (BIT0 y1) (BIT0 (BIT0 (Nat.mul y0 y1)))))))))))))).
Definition term195 (x0 : nat) (x1 : nat) := @eq nat (Nat.mul (BIT1 x0) (BIT0 x1)).
Definition term44 := Nat.mul (NUMERAL (BIT1 0)).
Definition term123 := and ((Nat.mul 0 0) = 0).
Definition term77 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((S x0) = (S y0)) = (x0 = y0)) x1.
Definition term216 (x0 : nat) (x1 : nat) := Nat.add (Nat.add (Nat.add x0 x0) (Nat.mul (Nat.add x0 x0) (Nat.add x1 x1))) (Nat.add x1 x1).
Definition term71 := (forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))).
Definition term149 (x0 : nat) := Nat.mul (Nat.add x0 x0).
Definition term88 (x0 : nat) (x1 : nat) := Nat.add (S x0) x1.
Definition term241 := (forall y0 : nat, 0 = 0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1)) (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1)))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.mul (Nat.add y0 y0) (Nat.add y1 y1))) = (Nat.add (Nat.add y0 y0) (Nat.add (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1)) (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1))))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul (Nat.add y0 y0) (Nat.add y1 y1)) (Nat.add y1 y1)) = (Nat.add (Nat.add y1 y1) (Nat.add (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1)) (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1))))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add (Nat.add y0 y0) (Nat.mul (Nat.add y0 y0) (Nat.add y1 y1))) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y0) (Nat.add (Nat.add y1 y1) (Nat.add (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1)) (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1))))))))).
Definition term240 := (forall y0 : nat, (Nat.mul (BIT1 y0) 0) = 0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT0 y0) (BIT0 y1)) = (BIT0 (BIT0 (Nat.mul y0 y1)))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT0 y0) (BIT1 y1)) = (Nat.add (BIT0 y0) (BIT0 (BIT0 (Nat.mul y0 y1))))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (BIT1 y0) (BIT0 y1)) = (Nat.add (BIT0 y1) (BIT0 (BIT0 (Nat.mul y0 y1))))) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul (BIT1 y0) (BIT1 y1)) = (Nat.add (BIT1 y0) (Nat.add (BIT0 y1) (BIT0 (BIT0 (Nat.mul y0 y1))))))))).
Definition term72 := (forall y0 : nat, (Nat.mul y0 0) = 0) /\ ((forall y0 : nat, (Nat.mul (BIT1 0) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (BIT1 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))).
Definition term231 := fun y0 : nat => forall y1 : nat, (Nat.add (Nat.add (Nat.add y0 y0) (Nat.mul (Nat.add y0 y0) (Nat.add y1 y1))) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y0) (Nat.add (Nat.add y1 y1) (Nat.add (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1)) (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1))))).
Definition term230 := fun y0 : nat => forall y1 : nat, (Nat.mul (BIT1 y0) (BIT1 y1)) = (Nat.add (BIT1 y0) (Nat.add (BIT0 y1) (BIT0 (BIT0 (Nat.mul y0 y1))))).
Definition term204 := fun y0 : nat => forall y1 : nat, (Nat.add (Nat.mul (Nat.add y0 y0) (Nat.add y1 y1)) (Nat.add y1 y1)) = (Nat.add (Nat.add y1 y1) (Nat.add (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1)) (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1)))).
Definition term203 := fun y0 : nat => forall y1 : nat, (Nat.mul (BIT1 y0) (BIT0 y1)) = (Nat.add (BIT0 y1) (BIT0 (BIT0 (Nat.mul y0 y1)))).
Definition term185 := fun y0 : nat => forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.mul (Nat.add y0 y0) (Nat.add y1 y1))) = (Nat.add (Nat.add y0 y0) (Nat.add (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1)) (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1)))).
Definition term184 := fun y0 : nat => forall y1 : nat, (Nat.mul (BIT0 y0) (BIT1 y1)) = (Nat.add (BIT0 y0) (BIT0 (BIT0 (Nat.mul y0 y1)))).
Definition term166 := fun y0 : nat => forall y1 : nat, (Nat.mul (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1)) (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y1))).
Definition term43 := NUMERAL (BIT1 0).
Definition term46 (x0 : nat) := Nat.mul (NUMERAL (BIT1 0)) x0.
Definition term179 (x0 : nat) (x1 : nat) := Nat.add (Nat.add x0 x0) (Nat.add (Nat.add (Nat.mul x0 x1) (Nat.mul x0 x1)) (Nat.add (Nat.mul x0 x1) (Nat.mul x0 x1))).
Definition term28 := fun y0 : nat => (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0).
Definition term201 (x0 : nat) := forall y0 : nat, (Nat.mul (BIT1 x0) (BIT0 y0)) = (Nat.add (BIT0 y0) (BIT0 (BIT0 (Nat.mul x0 y0)))).
Definition term182 (x0 : nat) := forall y0 : nat, (Nat.mul (BIT0 x0) (BIT1 y0)) = (Nat.add (BIT0 x0) (BIT0 (BIT0 (Nat.mul x0 y0)))).
Definition term130 := forall y0 : nat, 0 = 0.
Definition term80 (x0 : nat) := forall y0 : nat, (Nat.add x0 (S y0)) = (S (Nat.add x0 y0)).
