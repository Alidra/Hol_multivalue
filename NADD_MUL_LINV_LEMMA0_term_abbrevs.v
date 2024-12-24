Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term263 (x0 : nadd) := (exists y0 : nat, exists y1 : nat, forall y2 : nat, (Peano.le y1 y2) -> Peano.le y2 (Nat.mul y0 (dest_nadd x0 y2))) -> exists y0 : nat, exists y1 : nat, exists y2 : nat, forall y3 : nat, (Peano.le y2 y3) -> Peano.le (nadd_rinv x0 y3) (Nat.add (Nat.mul y0 y3) y1).
Definition term207 (x0 : nat) (x1 : nadd) (x2 : nat) := Peano.le (Nat.mul (nadd_rinv x1 x2) (Nat.mul x0 (dest_nadd x1 x2))).
Definition term96 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le ((fun y0 : nat => nadd_rinv x0 y0) x2) (Nat.add ((fun y0 : nat => Nat.mul x1 y0) x2) x3).
Definition term55 (x0 : nat) (x1 : nat) := exists y0 : nat, (Peano.le x0 y0) /\ (Peano.le y0 x1).
Definition term97 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (nadd_rinv x0 x2) (Nat.add (Nat.mul x1 x2) x3).
Definition term225 (x0 : nadd) (x1 : nat) := (fun y0 : nat => Nat.div (Nat.mul y0 y0) (dest_nadd x0 y0)) x1.
Definition term236 (x0 : nadd) (x1 : nat) := Peano.le (Nat.mul (dest_nadd x0 x1) (nadd_rinv x0 x1)).
Definition term86 (x0 : nadd) := fun y0 : nat => nadd_rinv x0 y0.
Definition term213 (x0 : nadd) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul x1 (Nat.mul (dest_nadd x0 x2) (nadd_rinv x0 x2))) (Nat.mul x1 (Nat.mul x2 x2)).
Definition term262 (x0 : nadd) := fun y0 : nat => exists y1 : nat, forall y2 : nat, (Peano.le y1 y2) -> Peano.le y2 (Nat.mul y0 (dest_nadd x0 y2)).
Definition term121 (x0 : nadd) := fun y0 : nat => exists y1 : nat, forall y2 : nat, Peano.le (nadd_rinv x0 y2) (Nat.add (Nat.mul y0 y2) y1).
Definition term119 (x0 : nadd) (x1 : nat) := fun y0 : nat => exists y1 : nat, forall y2 : nat, (Peano.le y1 y2) -> Peano.le (nadd_rinv x0 y2) (Nat.add (Nat.mul x1 y2) y0).
Definition term118 (x0 : nadd) (x1 : nat) := fun y0 : nat => exists y1 : nat, forall y2 : nat, (Peano.le y1 y2) -> Peano.le ((fun y3 : nat => nadd_rinv x0 y3) y2) (Nat.add ((fun y3 : nat => Nat.mul x1 y3) y2) y0).
Definition term238 (x0 : nadd) (x1 : nat) := Peano.le (Nat.mul (dest_nadd x0 x1) (nadd_rinv x0 x1)) (Nat.mul x1 x1).
Definition term259 (x0 : nadd) (x1 : nat) := exists y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> Peano.le (nadd_rinv x0 y1) (Nat.add (Nat.mul x1 y1) (NUMERAL 0)).
Definition term126 (x0 : nat) (x1 : nadd) := exists y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> Peano.le y1 (Nat.mul x0 (dest_nadd x1 y1)).
Definition term117 (x0 : nadd) (x1 : nat) (x2 : nat) := exists y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> Peano.le (nadd_rinv x0 y1) (Nat.add (Nat.mul x1 y1) x2).
Definition term116 (x0 : nadd) (x1 : nat) (x2 : nat) := exists y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> Peano.le ((fun y2 : nat => nadd_rinv x0 y2) y1) (Nat.add ((fun y2 : nat => Nat.mul x1 y2) y1) x2).
Definition term104 (x0 : nadd) (x1 : nat) := exists y0 : nat, forall y1 : nat, Peano.le (nadd_rinv x0 y1) (Nat.add (Nat.mul x1 y1) y0).
Definition term84 (x0 : nadd) (x1 : nat) := exists y0 : nat, forall y1 : nat, Peano.le ((fun y2 : nat => nadd_rinv x0 y2) y1) (Nat.add ((fun y2 : nat => Nat.mul x1 y2) y1) y0).
Definition term81 (x0 : nat -> nat) (x1 : nat -> nat) := exists y0 : nat, forall y1 : nat, Peano.le (x0 y1) (Nat.add (x1 y1) y0).
Definition term136 (x0 : nat) := (fun y0 : nat => (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) x0.
Definition term160 := @eq nat (NUMERAL 0).
Definition term258 (x0 : nat) (x1 : nadd) (x2 : nat) := forall y0 : nat, (Peano.le (S x0) y0) -> Peano.le (nadd_rinv x1 y0) (Nat.add (Nat.mul x2 y0) (NUMERAL 0)).
Definition term220 := forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0).
Definition term47 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) x0.
Definition term43 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.mul (Nat.mul y0 y1) y2) = (Nat.mul y0 (Nat.mul y1 y2))) x0.
Definition term36 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le (Nat.mul y0 y1) (Nat.mul y0 y2)) = ((y0 = (NUMERAL 0)) \/ (Peano.le y1 y2))) x0.
Definition term163 (x0 : nadd) (x1 : nat) := imp (Peano.le (Nat.mul (nadd_rinv x0 (NUMERAL 0)) (NUMERAL 0)) (Nat.mul (Nat.mul x1 (NUMERAL 0)) (NUMERAL 0))).
Definition term155 (x0 : nadd) (x1 : nat) := @eq Prop (Peano.le (Nat.mul (nadd_rinv x0 (NUMERAL 0)) (NUMERAL 0)) (Nat.mul (Nat.mul x1 (NUMERAL 0)) (NUMERAL 0))).
Definition term45 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.mul (Nat.mul x0 x1) y0) = (Nat.mul x0 (Nat.mul x1 y0))) x2.
Definition term18 (x0 : nat) := (fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> forall y1 : nat, (y1 = (Nat.add (Nat.mul (Nat.div y1 y0) y0) (Nat.modulo y1 y0))) /\ (Peano.lt (Nat.modulo y1 y0) y0)) x0.
Definition term139 (x0 : nat) := Peano.le (S x0) (NUMERAL 0).
Definition term60 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> forall y0 : nat, forall y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) -> Peano.le y0 y1.
Definition term42 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = (NUMERAL 0)) \/ (Peano.le x1 x2).
Definition term249 (x0 : nadd) (x1 : nat) := Peano.le (Nat.mul (dest_nadd x0 x1) (Nat.div (Nat.mul x1 x1) (dest_nadd x0 x1))) (Nat.add (Nat.mul (Nat.div (Nat.mul x1 x1) (dest_nadd x0 x1)) (dest_nadd x0 x1)) (Nat.modulo (Nat.mul x1 x1) (dest_nadd x0 x1))).
Definition term99 (x0 : nadd) (x1 : nat) (x2 : nat) := fun y0 : nat => Peano.le (nadd_rinv x0 y0) (Nat.add (Nat.mul x1 y0) x2).
Definition term93 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x0 x1).
Definition term244 (x0 : nadd) (x1 : nat) := forall y0 : nat, (y0 = (Nat.add (Nat.mul (Nat.div y0 (dest_nadd x0 x1)) (dest_nadd x0 x1)) (Nat.modulo y0 (dest_nadd x0 x1)))) /\ (Peano.lt (Nat.modulo y0 (dest_nadd x0 x1)) (dest_nadd x0 x1)).
Definition term250 (x0 : nadd) (x1 : nat) := Nat.mul (Nat.div (Nat.mul x1 x1) (dest_nadd x0 x1)) (dest_nadd x0 x1).
Definition term101 (x0 : nadd) (x1 : nat) (x2 : nat) := forall y0 : nat, Peano.le (nadd_rinv x0 y0) (Nat.add (Nat.mul x1 y0) x2).
Definition term234 (x0 : nat) := Nat.div (Nat.mul x0 x0) (NUMERAL 0).
Definition term221 (x0 : nat) := (fun y0 : nat => (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) x0.
Definition term106 (x0 : nadd) (x1 : nat) := @eq Prop (exists y0 : nat, forall y1 : nat, Peano.le (nadd_rinv x0 y1) (Nat.add (Nat.mul x1 y1) y0)).
Definition term105 (x0 : nadd) (x1 : nat) := @eq Prop (exists y0 : nat, forall y1 : nat, Peano.le ((fun y2 : nat => nadd_rinv x0 y2) y1) (Nat.add ((fun y2 : nat => Nat.mul x1 y2) y1) y0)).
Definition term152 (x0 : nat) := Nat.mul (Nat.mul x0 (NUMERAL 0)) (NUMERAL 0).
Definition term205 (x0 : nat) (x1 : nadd) (x2 : nat) := Nat.mul (nadd_rinv x1 x2) (Nat.mul x0 (dest_nadd x1 x2)).
Definition term162 (x0 : nadd) (x1 : nat) (x2 : nat) := imp ((Peano.le (Nat.mul (nadd_rinv x0 x2) x2) (Nat.mul (Nat.mul x1 x2) x2)) = ((Peano.le (nadd_rinv x0 x2) (Nat.mul x1 x2)) \/ (x2 = (NUMERAL 0)))).
Definition term202 (x0 : nat) := (x0 = (S x0)) \/ True.
Definition term241 (x0 : nadd) (x1 : nat) := Peano.le (Nat.mul (dest_nadd x0 x1) (Nat.div (Nat.mul x1 x1) (dest_nadd x0 x1))).
Definition term151 (x0 : nat) (x1 : nat) := Nat.mul (Nat.mul x0 x1) x1.
Definition term54 (x0 : nat) (x1 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> Peano.le x0 x1.
Definition term245 (x0 : nadd) (x1 : nat) (x2 : nat) := (fun y0 : nat => (y0 = (Nat.add (Nat.mul (Nat.div y0 (dest_nadd x0 x1)) (dest_nadd x0 x1)) (Nat.modulo y0 (dest_nadd x0 x1)))) /\ (Peano.lt (Nat.modulo y0 (dest_nadd x0 x1)) (dest_nadd x0 x1))) x2.
Definition term144 (x0 : nadd) (x1 : nat) := Nat.mul (nadd_rinv x0 x1) x1.
Definition term173 := fun y0 : Prop => y0.
Definition term58 (x0 : nat) := forall y0 : nat, (exists y1 : nat, (Peano.le x0 y1) /\ (Peano.le y1 y0)) -> Peano.le x0 y0.
Definition term131 (x0 : nadd) (x1 : nat) (x2 : nat) := Peano.le (nadd_rinv x0 x2) (Nat.mul x1 x2).
Definition term254 (x0 : nadd) (x1 : nat) := (forall y0 : nat, (y0 = (Nat.add (Nat.mul (Nat.div y0 (dest_nadd x0 x1)) (dest_nadd x0 x1)) (Nat.modulo y0 (dest_nadd x0 x1)))) /\ (Peano.lt (Nat.modulo y0 (dest_nadd x0 x1)) (dest_nadd x0 x1))) -> Peano.le (Nat.mul (dest_nadd x0 x1) (Nat.div (Nat.mul x1 x1) (dest_nadd x0 x1))) (Nat.mul x1 x1).
Definition term98 (x0 : nadd) (x1 : nat) (x2 : nat) := fun y0 : nat => Peano.le ((fun y1 : nat => nadd_rinv x0 y1) y0) (Nat.add ((fun y1 : nat => Nat.mul x1 y1) y0) x2).
Definition term74 (x0 : nat) := (fun y0 : nat => (Nat.add y0 (NUMERAL 0)) = y0) x0.
Definition term218 (x0 : nat) := (fun y0 : nat => Peano.le (NUMERAL 0) y0) x0.
Definition term13 (x0 : nat) (x1 : nat) := (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1).
Definition term107 (x0 : nat) (x1 : nat) := imp (Peano.le x0 x1).
Definition term186 (x0 : nadd) (x1 : nat) (x2 : nat) := (((nadd_rinv x0 x2) = (NUMERAL 0)) \/ (Peano.le x2 (Nat.mul x1 (dest_nadd x0 x2)))) /\ (Peano.le (Nat.mul (nadd_rinv x0 x2) (Nat.mul x1 (dest_nadd x0 x2))) (Nat.mul (Nat.mul x1 x2) x2)).
Definition term17 := (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> forall y1 : nat, (y1 = (Nat.add (Nat.mul (Nat.div y1 y0) y0) (Nat.modulo y1 y0))) /\ (Peano.lt (Nat.modulo y1 y0) y0).
Definition term1 (x0 : nat) := forall y0 : nat, Peano.le x0 (Nat.add x0 y0).
Definition term51 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Peano.le x1 x0) /\ (Peano.le x0 y0)) -> Peano.le x1 y0) x2.
Definition term243 (x0 : nadd) (x1 : nat) := (~ ((dest_nadd x0 x1) = (NUMERAL 0))) -> forall y0 : nat, (y0 = (Nat.add (Nat.mul (Nat.div y0 (dest_nadd x0 x1)) (dest_nadd x0 x1)) (Nat.modulo y0 (dest_nadd x0 x1)))) /\ (Peano.lt (Nat.modulo y0 (dest_nadd x0 x1)) (dest_nadd x0 x1)).
Definition term71 (x0 : nadd) (x1 : nat) (x2 : nat) := (Peano.le (nadd_rinv x0 x2) (Nat.mul x1 x2)) \/ (x2 = (NUMERAL 0)).
Definition term26 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.mul x0 (Nat.mul x1 y0)) = (Nat.mul (Nat.mul x0 x1) y0).
Definition term181 (x0 : nat) (x1 : nadd) (x2 : nat) := Nat.mul x0 (dest_nadd x1 x2).
Definition term19 (x0 : nadd) (x1 : nat) := (fun y0 : Prop => y0 \/ (~ y0)) ((dest_nadd x0 x1) = (NUMERAL 0)).
Definition term217 (x0 : nadd) := fun y0 : nat => Nat.div (Nat.mul y0 y0) (dest_nadd x0 y0).
Definition term75 (x0 : nat) := Nat.add x0 (NUMERAL 0).
Definition term149 (x0 : nat) (x1 : nat) := Nat.mul (Nat.mul x0 x1).
Definition term183 (x0 : nat) (x1 : nadd) (x2 : nat) := and (((nadd_rinv x1 x2) = (NUMERAL 0)) \/ (Peano.le x2 (Nat.mul x0 (dest_nadd x1 x2)))).
Definition term142 (x0 : nadd) (x1 : nat) := Nat.mul (nadd_rinv x0 x1).
Definition term68 (x0 : nadd) (x1 : nat) (x2 : nat) := forall y0 : nat, (Peano.le (Nat.mul (nadd_rinv x0 x2) y0) (Nat.mul (Nat.mul x1 x2) y0)) = ((Peano.le (nadd_rinv x0 x2) (Nat.mul x1 x2)) \/ (y0 = (NUMERAL 0))).
Definition term49 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 y1)) -> Peano.le x0 y1) x1.
Definition term44 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul (Nat.mul x0 y0) y1) = (Nat.mul x0 (Nat.mul y0 y1))) x1.
Definition term38 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (Nat.mul x0 y0) (Nat.mul x0 y1)) = ((x0 = (NUMERAL 0)) \/ (Peano.le y0 y1))) x1.
Definition term156 (x0 : nadd) := Peano.le (nadd_rinv x0 (NUMERAL 0)).
Definition term70 (x0 : nadd) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul (nadd_rinv x0 x2) x2) (Nat.mul (Nat.mul x1 x2) x2).
Definition term177 (x0 : nadd) (x1 : nat) (x2 : nat) := @eq Prop (Peano.le (nadd_rinv x0 x2) (Nat.mul x1 x2)).
Definition term91 (x0 : nat) (x1 : nat) := (fun y0 : nat => Nat.mul x0 y0) x1.
Definition term12 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term103 (x0 : nadd) (x1 : nat) := fun y0 : nat => forall y1 : nat, Peano.le (nadd_rinv x0 y1) (Nat.add (Nat.mul x1 y1) y0).
Definition term102 (x0 : nadd) (x1 : nat) := fun y0 : nat => forall y1 : nat, Peano.le ((fun y2 : nat => nadd_rinv x0 y2) y1) (Nat.add ((fun y2 : nat => Nat.mul x1 y2) y1) y0).
Definition term28 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Nat.mul x0 (Nat.mul y0 y1)) = (Nat.mul (Nat.mul x0 y0) y1).
Definition term189 (x0 : nat) (x1 : nadd) (x2 : nat) := Peano.le x2 (Nat.mul x0 (dest_nadd x1 x2)).
Definition term109 (x0 : nat) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat) := (Peano.le x0 x3) -> Peano.le (nadd_rinv x1 x3) (Nat.add (Nat.mul x2 x3) x4).
Definition term185 (x0 : nadd) (x1 : nat) (x2 : nat) := (Peano.le (Nat.mul (nadd_rinv x0 x2) x2) (Nat.mul (nadd_rinv x0 x2) (Nat.mul x1 (dest_nadd x0 x2)))) /\ (Peano.le (Nat.mul (nadd_rinv x0 x2) (Nat.mul x1 (dest_nadd x0 x2))) (Nat.mul (Nat.mul x1 x2) x2)).
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => Peano.le x0 (Nat.add x0 y0)) x1.
Definition term73 := forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0.
Definition term145 (x0 : nadd) := Nat.mul (nadd_rinv x0 (NUMERAL 0)) (NUMERAL 0).
Definition term192 (x0 : nat) := (fun y0 : nat => Peano.le y0 y0) x0.
Definition term111 (x0 : nat) (x1 : nadd) (x2 : nat) (x3 : nat) := fun y0 : nat => (Peano.le x0 y0) -> Peano.le (nadd_rinv x1 y0) (Nat.add (Nat.mul x2 y0) x3).
Definition term159 (x0 : nadd) (x1 : nat) := or (Peano.le (nadd_rinv x0 (NUMERAL 0)) (Nat.mul x1 (NUMERAL 0))).
Definition term157 (x0 : nadd) (x1 : nat) := Peano.le (nadd_rinv x0 (NUMERAL 0)) (Nat.mul x1 (NUMERAL 0)).
Definition term214 (x0 : nat) (x1 : nadd) (x2 : nat) := (x0 = (NUMERAL 0)) \/ (Peano.le (Nat.mul (dest_nadd x1 x2) (nadd_rinv x1 x2)) (Nat.mul x2 x2)).
Definition term113 (x0 : nat) (x1 : nadd) (x2 : nat) (x3 : nat) := forall y0 : nat, (Peano.le x0 y0) -> Peano.le (nadd_rinv x1 y0) (Nat.add (Nat.mul x2 y0) x3).
Definition term112 (x0 : nat) (x1 : nadd) (x2 : nat) (x3 : nat) := forall y0 : nat, (Peano.le x0 y0) -> Peano.le ((fun y1 : nat => nadd_rinv x1 y1) y0) (Nat.add ((fun y1 : nat => Nat.mul x2 y1) y0) x3).
Definition term52 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.le x1 x0) /\ (Peano.le x0 x2)) -> Peano.le x1 x2.
Definition term110 (x0 : nat) (x1 : nadd) (x2 : nat) (x3 : nat) := fun y0 : nat => (Peano.le x0 y0) -> Peano.le ((fun y1 : nat => nadd_rinv x1 y1) y0) (Nat.add ((fun y1 : nat => Nat.mul x2 y1) y0) x3).
Definition term247 (x0 : nat) (x1 : nadd) (x2 : nat) := Nat.add (Nat.mul (Nat.div x0 (dest_nadd x1 x2)) (dest_nadd x1 x2)) (Nat.modulo x0 (dest_nadd x1 x2)).
Definition term80 (x0 : nat -> nat) (x1 : nat -> nat) := (fun y0 : nat -> nat => (exists y1 : nat, forall y2 : nat, Peano.le (x0 y2) (Nat.add (y0 y2) y1)) = (exists y1 : nat, exists y2 : nat, forall y3 : nat, (Peano.le y2 y3) -> Peano.le (x0 y3) (Nat.add (y0 y3) y1))) x1.
Definition term204 (x0 : nat) (x1 : nat) := (Peano.le x0 (S x0)) /\ (Peano.le (S x0) x1).
Definition term16 := forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> forall y1 : nat, (y1 = (Nat.add (Nat.mul (Nat.div y1 y0) y0) (Nat.modulo y1 y0))) /\ (Peano.lt (Nat.modulo y1 y0) y0).
Definition term190 (x0 : nat) (x1 : nat) (x2 : nadd) (x3 : nat) := (forall y0 : nat, (Peano.le x0 y0) -> Peano.le y0 (Nat.mul x1 (dest_nadd x2 y0))) -> Peano.le x3 (Nat.mul x1 (dest_nadd x2 x3)).
Definition term20 (x0 : nadd) (x1 : nat) := ((dest_nadd x0 x1) = (NUMERAL 0)) \/ (~ ((dest_nadd x0 x1) = (NUMERAL 0))).
Definition term175 (x0 : nadd) (x1 : nat) (x2 : nat) := (fun y0 : Prop => y0) (Peano.le (Nat.mul (nadd_rinv x0 x2) x2) (Nat.mul (Nat.mul x1 x2) x2)).
Definition term90 (x0 : nadd) (x1 : nat) := Peano.le (nadd_rinv x0 x1).
Definition term165 (x0 : nadd) (x1 : nat) := (Peano.le (Nat.mul (nadd_rinv x0 (NUMERAL 0)) (NUMERAL 0)) (Nat.mul (Nat.mul x1 (NUMERAL 0)) (NUMERAL 0))) -> Peano.le (nadd_rinv x0 (NUMERAL 0)) (Nat.mul x1 (NUMERAL 0)).
Definition term23 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.mul x0 x1) x2.
Definition term226 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term147 (x0 : nadd) := Peano.le (Nat.mul (nadd_rinv x0 (NUMERAL 0)) (NUMERAL 0)).
Definition term257 (x0 : nat) (x1 : nadd) (x2 : nat) (x3 : nat) := (Peano.le (S x0) x3) -> Peano.le (nadd_rinv x1 x3) (Nat.add (Nat.mul x2 x3) (NUMERAL 0)).
Definition term108 (x0 : nat) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat) := (Peano.le x0 x3) -> Peano.le ((fun y0 : nat => nadd_rinv x1 y0) x3) (Nat.add ((fun y0 : nat => Nat.mul x2 y0) x3) x4).
Definition term193 := forall y0 : nat, forall y1 : nat, (Peano.le y0 (S y1)) = ((y0 = (S y1)) \/ (Peano.le y0 y1)).
Definition term66 (x0 : nadd) (x1 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le (Nat.mul (nadd_rinv x0 x1) y1) (Nat.mul y0 y1)) = ((Peano.le (nadd_rinv x0 x1) y0) \/ (y1 = (NUMERAL 0))).
Definition term59 := forall y0 : nat, forall y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) -> Peano.le y0 y1.
Definition term48 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 y1)) -> Peano.le x0 y1.
Definition term46 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2.
Definition term37 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le (Nat.mul x0 y0) (Nat.mul x0 y1)) = ((x0 = (NUMERAL 0)) \/ (Peano.le y0 y1)).
Definition term35 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.mul (Nat.mul y0 y1) y2) = (Nat.mul y0 (Nat.mul y1 y2)).
Definition term34 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.mul y0 (Nat.mul y1 y2)) = (Nat.mul (Nat.mul y0 y1) y2).
Definition term31 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.mul (Nat.mul x0 y0) y1) = (Nat.mul x0 (Nat.mul y0 y1)).
Definition term30 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.mul x0 (Nat.mul y0 y1)) = (Nat.mul (Nat.mul x0 y0) y1).
Definition term7 := forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1).
Definition term215 (x0 : nadd) (x1 : nat) := Nat.mul (dest_nadd x0 x1) (nadd_rinv x0 x1).
Definition term64 (x0 : nat) := (x0 = (NUMERAL 0)) \/ (~ (x0 = (NUMERAL 0))).
Definition term76 (x0 : nadd) := (fun y0 : nadd => (~ (nadd_eq y0 (nadd_of_num (NUMERAL 0)))) -> exists y1 : nat, exists y2 : nat, forall y3 : nat, (Peano.le y2 y3) -> Peano.le y3 (Nat.mul y1 (dest_nadd y0 y3))) x0.
Definition term122 (x0 : nadd) := fun y0 : nat => exists y1 : nat, exists y2 : nat, forall y3 : nat, (Peano.le y2 y3) -> Peano.le (nadd_rinv x0 y3) (Nat.add (Nat.mul y0 y3) y1).
Definition term253 (x0 : nadd) (x1 : nat) := Nat.modulo (Nat.mul x1 x1) (dest_nadd x0 x1).
Definition term179 (x0 : nat) (x1 : nadd) (x2 : nat) := Peano.le (Nat.mul (nadd_rinv x1 x2) x2) (Nat.mul (nadd_rinv x1 x2) (Nat.mul x0 (dest_nadd x1 x2))).
Definition term227 (x0 : nat -> nat) (x1 : nat) := (fun y0 : nat => x0 y0) x1.
Definition term255 (x0 : nadd) (x1 : nat) (x2 : nat) := exists y0 : nat, (Peano.le (Nat.mul (nadd_rinv x0 x2) x2) y0) /\ (Peano.le y0 (Nat.mul (Nat.mul x1 x2) x2)).
Definition term127 (x0 : nat) (x1 : nat) (x2 : nadd) := forall y0 : nat, (Peano.le x0 y0) -> Peano.le y0 (Nat.mul x1 (dest_nadd x2 y0)).
Definition term146 (x0 : nadd) (x1 : nat) := Peano.le (Nat.mul (nadd_rinv x0 x1) x1).
Definition term200 (x0 : nat) := (x0 = (S x0)) \/ (Peano.le x0 x0).
Definition term251 (x0 : nadd) (x1 : nat) := Peano.le (Nat.mul (Nat.div (Nat.mul x1 x1) (dest_nadd x0 x1)) (dest_nadd x0 x1)).
Definition term11 (x0 : nat) (x1 : nat) := (~ (x1 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1).
Definition term208 (x0 : nat) (x1 : nadd) (x2 : nat) := Peano.le (Nat.mul (Nat.mul x0 (dest_nadd x1 x2)) (nadd_rinv x1 x2)).
Definition term242 (x0 : nadd) (x1 : nat) := Peano.le (Nat.mul (dest_nadd x0 x1) (Nat.div (Nat.mul x1 x1) (dest_nadd x0 x1))) (Nat.mul x1 x1).
Definition term88 (x0 : nadd) (x1 : nat) := (fun y0 : nat => nadd_rinv x0 y0) x1.
Definition term235 (x0 : nat) := Nat.mul (NUMERAL 0) (Nat.div (Nat.mul x0 x0) (NUMERAL 0)).
Definition term219 (x0 : nat) := Peano.le (NUMERAL 0) x0.
Definition term187 (x0 : nat) (x1 : nat) (x2 : nadd) (x3 : nat) := (fun y0 : nat => (Peano.le x0 y0) -> Peano.le y0 (Nat.mul x1 (dest_nadd x2 y0))) x3.
Definition term195 (x0 : nat) := forall y0 : nat, (Peano.le x0 (S y0)) = ((x0 = (S y0)) \/ (Peano.le x0 y0)).
Definition term39 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le (Nat.mul x0 x1) (Nat.mul x0 y0)) = ((x0 = (NUMERAL 0)) \/ (Peano.le x1 y0)).
Definition term232 (x0 : nadd) (x1 : nat) := @eq nat ((fun y0 : nat => Nat.div (Nat.mul y0 y0) (dest_nadd x0 y0)) x1).
Definition term133 (x0 : nat) := ~ ((S x0) = (NUMERAL 0)).
Definition term94 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add ((fun y0 : nat => Nat.mul x0 y0) x1) x2.
Definition term188 (x0 : nat) (x1 : nat) (x2 : nadd) (x3 : nat) := (Peano.le x0 x3) -> Peano.le x3 (Nat.mul x1 (dest_nadd x2 x3)).
Definition term184 (x0 : nadd) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul (nadd_rinv x0 x2) (Nat.mul x1 (dest_nadd x0 x2))) (Nat.mul (Nat.mul x1 x2) x2).
Definition term5 (x0 : nat) := forall y0 : nat, (Nat.mul x0 y0) = (Nat.mul y0 x0).
Definition term41 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul x1 x0) (Nat.mul x1 x2).
Definition term252 (x0 : nadd) (x1 : nat) := Peano.le (Nat.mul (Nat.div (Nat.mul x1 x1) (dest_nadd x0 x1)) (dest_nadd x0 x1)) (Nat.add (Nat.mul (Nat.div (Nat.mul x1 x1) (dest_nadd x0 x1)) (dest_nadd x0 x1)) (Nat.modulo (Nat.mul x1 x1) (dest_nadd x0 x1))).
Definition term230 (x0 : nadd) := fun y0 : nat => (fun y1 : nat => Nat.div (Nat.mul y1 y1) (dest_nadd x0 y1)) y0.
Definition term167 (x0 : nadd) (x1 : nat) := False -> (Peano.le (Nat.mul (nadd_rinv x0 (NUMERAL 0)) (NUMERAL 0)) (Nat.mul (Nat.mul x1 (NUMERAL 0)) (NUMERAL 0))) -> Peano.le (nadd_rinv x0 (NUMERAL 0)) (Nat.mul x1 (NUMERAL 0)).
Definition term210 (x0 : nat) (x1 : nadd) (x2 : nat) := Nat.mul x0 (Nat.mul (dest_nadd x1 x2) (nadd_rinv x1 x2)).
Definition term6 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.mul x0 y0) = (Nat.mul y0 x0)) x1.
Definition term72 := (forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))).
Definition term150 (x0 : nat) := Nat.mul (Nat.mul x0 (NUMERAL 0)).
Definition term50 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Peano.le x1 x0) /\ (Peano.le x0 y0)) -> Peano.le x1 y0.
Definition term171 (x0 : nadd) (x1 : nat) (x2 : nat) := ((Peano.le (Nat.mul (nadd_rinv x0 x2) x2) (Nat.mul (Nat.mul x1 x2) x2)) = (Peano.le (nadd_rinv x0 x2) (Nat.mul x1 x2))) -> Peano.le (nadd_rinv x0 x2) (Nat.mul x1 x2).
Definition term87 (x0 : nat) := fun y0 : nat => Nat.mul x0 y0.
Definition term154 (x0 : nadd) (x1 : nat) (x2 : nat) := @eq Prop (Peano.le (Nat.mul (nadd_rinv x0 x2) x2) (Nat.mul (Nat.mul x1 x2) x2)).
Definition term14 (x0 : nat) := forall y0 : nat, (y0 = (Nat.add (Nat.mul (Nat.div y0 x0) x0) (Nat.modulo y0 x0))) /\ (Peano.lt (Nat.modulo y0 x0) x0).
Definition term180 (x0 : nat) (x1 : nadd) (x2 : nat) := ((nadd_rinv x1 x2) = (NUMERAL 0)) \/ (Peano.le x2 (Nat.mul x0 (dest_nadd x1 x2))).
Definition term25 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.mul (Nat.mul x0 x1) y0) = (Nat.mul x0 (Nat.mul x1 y0)).
Definition term248 (x0 : nadd) (x1 : nat) := Nat.add (Nat.mul (Nat.div (Nat.mul x1 x1) (dest_nadd x0 x1)) (dest_nadd x0 x1)) (Nat.modulo (Nat.mul x1 x1) (dest_nadd x0 x1)).
Definition term265 := forall y0 : nadd, (~ (nadd_eq y0 (nadd_of_num (NUMERAL 0)))) -> exists y1 : nat, exists y2 : nat, forall y3 : nat, Peano.le (nadd_rinv y0 y3) (Nat.add (Nat.mul y1 y3) y2).
Definition term212 (x0 : nat) (x1 : nat) := Nat.mul x0 (Nat.mul x1 x1).
Definition term198 (x0 : nat) (x1 : nat) := (x0 = (S x1)) \/ (Peano.le x0 x1).
Definition term3 (x0 : nat) (x1 : nat) := Peano.le x0 (Nat.add x0 x1).
Definition term194 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y0 (S y1)) = ((y0 = (S y1)) \/ (Peano.le y0 y1))) x0.
Definition term61 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) -> Peano.le y0 y1) x0.
Definition term8 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) x0.
Definition term4 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) x0.
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, Peano.le y0 (Nat.add y0 y1)) x0.
Definition term182 (x0 : nat) (x1 : nadd) (x2 : nat) := and (Peano.le (Nat.mul (nadd_rinv x1 x2) x2) (Nat.mul (nadd_rinv x1 x2) (Nat.mul x0 (dest_nadd x1 x2)))).
Definition term132 (x0 : nat) := (fun y0 : nat => ~ ((S y0) = (NUMERAL 0))) x0.
Definition term172 (x0 : nat) (x1 : nadd) (x2 : nat) (x3 : nat) := (Peano.le (S x0) x3) -> ((Peano.le (Nat.mul (nadd_rinv x1 x3) x3) (Nat.mul (Nat.mul x2 x3) x3)) = (Peano.le (nadd_rinv x1 x3) (Nat.mul x2 x3))) -> Peano.le (nadd_rinv x1 x3) (Nat.mul x2 x3).
Definition term166 (x0 : nat) (x1 : nadd) (x2 : nat) (x3 : nat) := (Peano.le (S x0) x3) -> ((Peano.le (Nat.mul (nadd_rinv x1 x3) x3) (Nat.mul (Nat.mul x2 x3) x3)) = ((Peano.le (nadd_rinv x1 x3) (Nat.mul x2 x3)) \/ (x3 = (NUMERAL 0)))) -> Peano.le (nadd_rinv x1 x3) (Nat.mul x2 x3).
Definition term53 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x1) /\ (Peano.le x1 x2).
Definition term170 (x0 : nadd) (x1 : nat) (x2 : nat) := imp ((Peano.le (Nat.mul (nadd_rinv x0 x2) x2) (Nat.mul (Nat.mul x1 x2) x2)) = (Peano.le (nadd_rinv x0 x2) (Nat.mul x1 x2))).
Definition term22 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (Nat.mul x1 x2).
Definition term233 (x0 : nat) := Nat.div (Nat.mul x0 x0).
Definition term228 (x0 : nadd) (x1 : nat) := (fun y0 : nat => (fun y1 : nat => Nat.div (Nat.mul y1 y1) (dest_nadd x0 y1)) y0) x1.
Definition term69 (x0 : nadd) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.le (Nat.mul (nadd_rinv x0 x2) y0) (Nat.mul (Nat.mul x1 x2) y0)) = ((Peano.le (nadd_rinv x0 x2) (Nat.mul x1 x2)) \/ (y0 = (NUMERAL 0)))) x2.
Definition term211 (x0 : nat) (x1 : nadd) (x2 : nat) := Peano.le (Nat.mul x0 (Nat.mul (dest_nadd x1 x2) (nadd_rinv x1 x2))).
Definition term92 (x0 : nat) (x1 : nat) := Nat.add ((fun y0 : nat => Nat.mul x0 y0) x1).
Definition term148 (x0 : nat) := Nat.mul x0 (NUMERAL 0).
Definition term231 (x0 : nadd) (x1 : nat) := @eq nat ((fun y0 : nat => (fun y1 : nat => Nat.div (Nat.mul y1 y1) (dest_nadd x0 y1)) y0) x1).
Definition term79 (x0 : nat -> nat) := forall y0 : nat -> nat, (exists y1 : nat, forall y2 : nat, Peano.le (x0 y2) (Nat.add (y0 y2) y1)) = (exists y1 : nat, exists y2 : nat, forall y3 : nat, (Peano.le y2 y3) -> Peano.le (x0 y3) (Nat.add (y0 y3) y1)).
Definition term161 (x0 : nadd) (x1 : nat) := (Peano.le (nadd_rinv x0 (NUMERAL 0)) (Nat.mul x1 (NUMERAL 0))) \/ True.
Definition term141 (x0 : nadd) := nadd_rinv x0 (NUMERAL 0).
Definition term40 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.le (Nat.mul x0 x1) (Nat.mul x0 y0)) = ((x0 = (NUMERAL 0)) \/ (Peano.le x1 y0))) x2.
Definition term89 (x0 : nadd) (x1 : nat) := Peano.le ((fun y0 : nat => nadd_rinv x0 y0) x1).
Definition term135 := forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0)).
Definition term128 (x0 : nat) (x1 : nat) := Peano.le (S x0) x1.
Definition term216 (x0 : nadd) := (fun y0 : nadd => (nadd_rinv y0) = (fun y1 : nat => Nat.div (Nat.mul y1 y1) (dest_nadd y0 y1))) x0.
Definition term57 (x0 : nat) (x1 : nat) := (exists y0 : nat, (Peano.le x0 y0) /\ (Peano.le y0 x1)) -> Peano.le x0 x1.
Definition term134 (x0 : nat) := (~ ((S x0) = (NUMERAL 0))) -> ((S x0) = (NUMERAL 0)) = False.
Definition term153 (x0 : nadd) (x1 : nat) := Peano.le (Nat.mul (nadd_rinv x0 (NUMERAL 0)) (NUMERAL 0)) (Nat.mul (Nat.mul x1 (NUMERAL 0)) (NUMERAL 0)).
Definition term206 (x0 : nat) (x1 : nadd) (x2 : nat) := Nat.mul (Nat.mul x0 (dest_nadd x1 x2)) (nadd_rinv x1 x2).
Definition term168 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> (x0 = (NUMERAL 0)) = False.
Definition term246 (x0 : nat) (x1 : nadd) (x2 : nat) := (x0 = (Nat.add (Nat.mul (Nat.div x0 (dest_nadd x1 x2)) (dest_nadd x1 x2)) (Nat.modulo x0 (dest_nadd x1 x2)))) /\ (Peano.lt (Nat.modulo x0 (dest_nadd x1 x2)) (dest_nadd x1 x2)).
Definition term10 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0)) x1.
Definition term239 (x0 : nat) := Peano.le (NUMERAL 0) (Nat.mul x0 x0).
Definition term209 (x0 : nadd) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul (Nat.mul x1 (dest_nadd x0 x2)) (nadd_rinv x0 x2)) (Nat.mul (Nat.mul x1 x2) x2).
Definition term15 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> forall y0 : nat, (y0 = (Nat.add (Nat.mul (Nat.div y0 x0) x0) (Nat.modulo y0 x0))) /\ (Peano.lt (Nat.modulo y0 x0) x0).
Definition term140 (x0 : nat) (x1 : nat) := imp (Peano.le (S x0) x1).
Definition term176 (x0 : nadd) (x1 : nat) (x2 : nat) := @eq Prop ((fun y0 : Prop => y0) (Peano.le (nadd_rinv x0 x2) (Nat.mul x1 x2))).
Definition term27 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.mul (Nat.mul x0 x1) y0) = (Nat.mul x0 (Nat.mul x1 y0)).
Definition term56 (x0 : nat) (x1 : nat) := fun y0 : nat => (Peano.le x0 y0) /\ (Peano.le y0 x1).
Definition term21 (x0 : nadd) (x1 : nat) := ~ ((dest_nadd x0 x1) = (NUMERAL 0)).
Definition term125 (x0 : nadd) := exists y0 : nat, exists y1 : nat, forall y2 : nat, (Peano.le y1 y2) -> Peano.le y2 (Nat.mul y0 (dest_nadd x0 y2)).
Definition term124 (x0 : nadd) := exists y0 : nat, exists y1 : nat, exists y2 : nat, forall y3 : nat, (Peano.le y2 y3) -> Peano.le (nadd_rinv x0 y3) (Nat.add (Nat.mul y0 y3) y1).
Definition term123 (x0 : nadd) := exists y0 : nat, exists y1 : nat, forall y2 : nat, Peano.le (nadd_rinv x0 y2) (Nat.add (Nat.mul y0 y2) y1).
Definition term120 (x0 : nadd) (x1 : nat) := exists y0 : nat, exists y1 : nat, forall y2 : nat, (Peano.le y1 y2) -> Peano.le (nadd_rinv x0 y2) (Nat.add (Nat.mul x1 y2) y0).
Definition term85 (x0 : nadd) (x1 : nat) := exists y0 : nat, exists y1 : nat, forall y2 : nat, (Peano.le y1 y2) -> Peano.le ((fun y3 : nat => nadd_rinv x0 y3) y2) (Nat.add ((fun y3 : nat => Nat.mul x1 y3) y2) y0).
Definition term82 (x0 : nat -> nat) (x1 : nat -> nat) := exists y0 : nat, exists y1 : nat, forall y2 : nat, (Peano.le y1 y2) -> Peano.le (x0 y2) (Nat.add (x1 y2) y0).
Definition term174 (x0 : nadd) (x1 : nat) (x2 : nat) := (fun y0 : Prop => y0) (Peano.le (nadd_rinv x0 x2) (Nat.mul x1 x2)).
Definition term78 (x0 : nat -> nat) := (fun y0 : nat -> nat => forall y1 : nat -> nat, (exists y2 : nat, forall y3 : nat, Peano.le (y0 y3) (Nat.add (y1 y3) y2)) = (exists y2 : nat, exists y3 : nat, forall y4 : nat, (Peano.le y3 y4) -> Peano.le (y0 y4) (Nat.add (y1 y4) y2))) x0.
Definition term237 := Peano.le (NUMERAL 0).
Definition term224 := Nat.mul (NUMERAL 0).
Definition term83 (x0 : nadd) := ~ (nadd_eq x0 (nadd_of_num (NUMERAL 0))).
Definition term67 (x0 : nadd) (x1 : nat) (x2 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (Nat.mul (nadd_rinv x0 x2) y1) (Nat.mul y0 y1)) = ((Peano.le (nadd_rinv x0 x2) y0) \/ (y1 = (NUMERAL 0)))) (Nat.mul x1 x2).
Definition term138 (x0 : nat) := Peano.le (S x0).
Definition term164 (x0 : nadd) (x1 : nat) (x2 : nat) := ((Peano.le (Nat.mul (nadd_rinv x0 x2) x2) (Nat.mul (Nat.mul x1 x2) x2)) = ((Peano.le (nadd_rinv x0 x2) (Nat.mul x1 x2)) \/ (x2 = (NUMERAL 0)))) -> Peano.le (nadd_rinv x0 x2) (Nat.mul x1 x2).
Definition term222 (x0 : nat) := Nat.mul (NUMERAL 0) x0.
Definition term100 (x0 : nadd) (x1 : nat) (x2 : nat) := forall y0 : nat, Peano.le ((fun y1 : nat => nadd_rinv x0 y1) y0) (Nat.add ((fun y1 : nat => Nat.mul x1 y1) y0) x2).
Definition term240 (x0 : nadd) (x1 : nat) := Nat.mul (dest_nadd x0 x1) (Nat.div (Nat.mul x1 x1) (dest_nadd x0 x1)).
Definition term95 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x0 x1) x2.
Definition term201 (x0 : nat) := or (x0 = (S x0)).
Definition term169 (x0 : nadd) (x1 : nat) (x2 : nat) := (Peano.le (nadd_rinv x0 x2) (Nat.mul x1 x2)) \/ False.
Definition term264 (x0 : nadd) := (~ (nadd_eq x0 (nadd_of_num (NUMERAL 0)))) -> exists y0 : nat, exists y1 : nat, forall y2 : nat, Peano.le (nadd_rinv x0 y2) (Nat.add (Nat.mul y0 y2) y1).
Definition term77 (x0 : nadd) := (~ (nadd_eq x0 (nadd_of_num (NUMERAL 0)))) -> exists y0 : nat, exists y1 : nat, forall y2 : nat, (Peano.le y1 y2) -> Peano.le y2 (Nat.mul y0 (dest_nadd x0 y2)).
Definition term158 (x0 : nadd) (x1 : nat) (x2 : nat) := or (Peano.le (nadd_rinv x0 x2) (Nat.mul x1 x2)).
Definition term129 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x0 x1) (NUMERAL 0).
Definition term229 (x0 : nadd) (x1 : nat) := Nat.div (Nat.mul x1 x1) (dest_nadd x0 x1).
Definition term199 (x0 : nat) := Peano.le x0 (S x0).
Definition term9 (x0 : nat) := forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0).
Definition term24 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.mul x0 (Nat.mul x1 y0)) = (Nat.mul (Nat.mul x0 x1) y0).
Definition term256 (x0 : nadd) (x1 : nat) (x2 : nat) := fun y0 : nat => (Peano.le (Nat.mul (nadd_rinv x0 x2) x2) y0) /\ (Peano.le y0 (Nat.mul (Nat.mul x1 x2) x2)).
Definition term203 (x0 : nat) := and (Peano.le x0 (S x0)).
Definition term137 (x0 : nat) := Peano.le x0 (NUMERAL 0).
Definition term196 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le x0 (S y0)) = ((x0 = (S y0)) \/ (Peano.le x0 y0))) x1.
Definition term197 (x0 : nat) (x1 : nat) := Peano.le x0 (S x1).
Definition term178 (x0 : nadd) (x1 : nat) (x2 : nat) := (exists y0 : nat, (Peano.le (Nat.mul (nadd_rinv x0 x2) x2) y0) /\ (Peano.le y0 (Nat.mul (Nat.mul x1 x2) x2))) -> Peano.le (Nat.mul (nadd_rinv x0 x2) x2) (Nat.mul (Nat.mul x1 x2) x2).
Definition term63 (x0 : nat) := (fun y0 : Prop => y0 \/ (~ y0)) (x0 = (NUMERAL 0)).
Definition term143 (x0 : nadd) := Nat.mul (nadd_rinv x0 (NUMERAL 0)).
Definition term261 (x0 : nat) (x1 : nadd) := fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) -> Peano.le y1 (Nat.mul x0 (dest_nadd x1 y1)).
Definition term260 (x0 : nadd) (x1 : nat) := fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) -> Peano.le (nadd_rinv x0 y1) (Nat.add (Nat.mul x1 y1) (NUMERAL 0)).
Definition term115 (x0 : nadd) (x1 : nat) (x2 : nat) := fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) -> Peano.le (nadd_rinv x0 y1) (Nat.add (Nat.mul x1 y1) x2).
Definition term114 (x0 : nadd) (x1 : nat) (x2 : nat) := fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) -> Peano.le ((fun y2 : nat => nadd_rinv x0 y2) y1) (Nat.add ((fun y2 : nat => Nat.mul x1 y2) y1) x2).
Definition term29 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Nat.mul (Nat.mul x0 y0) y1) = (Nat.mul x0 (Nat.mul y0 y1)).
Definition term33 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.mul (Nat.mul y0 y1) y2) = (Nat.mul y0 (Nat.mul y1 y2)).
Definition term32 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.mul y0 (Nat.mul y1 y2)) = (Nat.mul (Nat.mul y0 y1) y2).
Definition term62 (x0 : nat) (x1 : nat) := (fun y0 : nat => (exists y1 : nat, (Peano.le x0 y1) /\ (Peano.le y1 y0)) -> Peano.le x0 y0) x1.
Definition term191 (x0 : nat) (x1 : nat) (x2 : nadd) := (forall y0 : nat, (Peano.le x0 y0) -> Peano.le y0 (Nat.mul x1 (dest_nadd x2 y0))) -> forall y0 : nat, (Peano.le x0 y0) -> Peano.le y0 (Nat.mul x1 (dest_nadd x2 y0)).
Definition term65 (x0 : nadd) (x1 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le (Nat.mul y0 y2) (Nat.mul y1 y2)) = ((Peano.le y0 y1) \/ (y2 = (NUMERAL 0)))) (nadd_rinv x0 x1).
Definition term223 (x0 : nadd) (x1 : nat) := Nat.mul (dest_nadd x0 x1).
Definition term130 (x0 : nadd) (x1 : nat) (x2 : nat) := Peano.le (nadd_rinv x0 x2) (Nat.add (Nat.mul x1 x2) (NUMERAL 0)).
