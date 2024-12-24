Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term131 (x0 : nat) (x1 : nat) := ~ (x0 = x1).
Definition term113 := (fun y0 : nat => y0 = (S (NUMERAL 0))) (NUMERAL 0).
Definition term85 (x0 : nat -> Prop) := ~ (all x0).
Definition term119 := (~ False) -> False.
Definition term62 := (~ (forall y0 : nat, ((y0 = (S (NUMERAL 0))) \/ (y0 = (NUMERAL 0))) -> (~ (y0 = (NUMERAL 0))) = (y0 = (S (NUMERAL 0))))) -> (forall y0 : nat, ~ ((S y0) = (NUMERAL 0))) -> False.
Definition term139 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((~ (x0 = x1)) \/ (~ (x0 = x2)))) -> x1 = x2.
Definition term67 := ~ (forall y0 : nat, ~ ((S y0) = (NUMERAL 0))).
Definition term73 (x0 : nat) := and (~ (~ (x0 = (NUMERAL 0)))).
Definition term33 (x0 : nat) := (~ ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0))) -> (Peano.lt (Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))) (NUMERAL (BIT0 (BIT1 0)))) = True.
Definition term52 (x0 : nat) := @eq Prop (~ (x0 = (NUMERAL 0))).
Definition term111 := fun y0 : nat => y0 = (S (NUMERAL 0)).
Definition term145 (x0 : Prop) := ~ (~ x0).
Definition term95 := fun y0 : nat => ~ (y0 = (S (NUMERAL 0))).
Definition term37 := @eq nat (S (NUMERAL (BIT1 0))).
Definition term97 := (fun y0 : nat => ~ (y0 = (S (NUMERAL 0)))) (S (NUMERAL 0)).
Definition term144 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (~ (x1 = x0))) /\ (~ (~ (x1 = x2))).
Definition term112 (x0 : nat) := (fun y0 : nat => y0 = (S (NUMERAL 0))) x0.
Definition term39 := S (NUMERAL 0).
Definition term120 := (~ ((NUMERAL 0) = (NUMERAL 0))) -> (NUMERAL 0) = (NUMERAL 0).
Definition term59 (x0 : Prop) := (~ x0) -> False.
Definition term150 (x0 : nat) (x1 : nat) (x2 : nat) := imp (~ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term19 (x0 : nat) := ~ (Coq.Arith.PeanoNat.Nat.Even x0).
Definition term25 (x0 : nat) := Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0))).
Definition term96 (x0 : nat) := (fun y0 : nat => ~ (y0 = (S (NUMERAL 0)))) x0.
Definition term156 (x0 : nat) := (Peano.lt (Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))) (NUMERAL (BIT0 (BIT1 0)))) -> (~ ((Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0))) = ((Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0))).
Definition term36 := @eq nat (NUMERAL (BIT0 (BIT1 0))).
Definition term40 := S (S (NUMERAL 0)).
Definition term53 (x0 : nat) := (Peano.lt x0 (NUMERAL (BIT0 (BIT1 0)))) -> (~ (x0 = (NUMERAL 0))) = (x0 = (NUMERAL (BIT1 0))).
Definition term56 := fun y0 : nat => ((y0 = (S (NUMERAL 0))) \/ (y0 = (NUMERAL 0))) -> (~ (y0 = (NUMERAL 0))) = (y0 = (S (NUMERAL 0))).
Definition term138 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term148 (x0 : nat) (x1 : nat) := and (x0 = x1).
Definition term45 (x0 : nat) := (x0 = (NUMERAL 0)) \/ (Peano.lt x0 (NUMERAL 0)).
Definition term61 := ~ (forall y0 : nat, ((y0 = (S (NUMERAL 0))) \/ (y0 = (NUMERAL 0))) -> (~ (y0 = (NUMERAL 0))) = (y0 = (S (NUMERAL 0)))).
Definition term77 (x0 : nat) := or ((~ (x0 = (NUMERAL 0))) /\ (~ (x0 = (S (NUMERAL 0))))).
Definition term17 (x0 : nat) (x1 : nat) := (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1).
Definition term101 := fun y0 : nat => ~ (y0 = (NUMERAL 0)).
Definition term117 (x0 : Prop) := (~ x0) -> x0.
Definition term149 (x0 : nat) (x1 : nat) (x2 : nat) := (x1 = x0) /\ (x1 = x2).
Definition term74 (x0 : nat) := and (x0 = (NUMERAL 0)).
Definition term108 := (fun y0 : nat => y0 = (NUMERAL 0)) (S (NUMERAL 0)).
Definition term84 (x0 : nat) := ~ (((x0 = (S (NUMERAL 0))) \/ (x0 = (NUMERAL 0))) -> (~ (x0 = (NUMERAL 0))) = (x0 = (S (NUMERAL 0)))).
Definition term140 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x1 = x0)) \/ (~ (x1 = x2)).
Definition term6 := forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False.
Definition term118 := ((S (NUMERAL 0)) = (S (NUMERAL 0))) -> False.
Definition term50 (x0 : nat) := imp (Peano.lt x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term142 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term136 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2))).
Definition term125 := ((S (NUMERAL 0)) = (NUMERAL 0)) -> False.
Definition term137 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term29 (x0 : nat) := @eq Prop (~ ((Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0))).
Definition term91 := fun y0 : nat => ((y0 = (S (NUMERAL 0))) \/ (y0 = (NUMERAL 0))) /\ (((~ (y0 = (NUMERAL 0))) /\ (~ (y0 = (S (NUMERAL 0))))) \/ ((y0 = (NUMERAL 0)) /\ (y0 = (S (NUMERAL 0))))).
Definition term104 := ~ ((NUMERAL 0) = (NUMERAL 0)).
Definition term134 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term115 (x0 : nat) := @eq Prop (x0 = (S (NUMERAL 0))).
Definition term105 (x0 : nat) := @eq Prop ((fun y0 : nat => ~ (y0 = (NUMERAL 0))) x0).
Definition term99 (x0 : nat) := @eq Prop ((fun y0 : nat => ~ (y0 = (S (NUMERAL 0)))) x0).
Definition term16 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term5 (x0 : nat) (x1 : nat) := (x0 = x1) \/ (Peano.lt x0 x1).
Definition term79 (x0 : nat) := ((~ (x0 = (NUMERAL 0))) /\ (~ (x0 = (S (NUMERAL 0))))) \/ ((x0 = (NUMERAL 0)) /\ (x0 = (S (NUMERAL 0)))).
Definition term100 (x0 : nat) := @eq Prop (~ (x0 = (S (NUMERAL 0)))).
Definition term121 := ((NUMERAL 0) = (NUMERAL 0)) -> False.
Definition term116 := (~ ((S (NUMERAL 0)) = (S (NUMERAL 0)))) -> (S (NUMERAL 0)) = (S (NUMERAL 0)).
Definition term76 (x0 : nat) := (x0 = (NUMERAL 0)) /\ (x0 = (S (NUMERAL 0))).
Definition term89 (x0 : nat) := ~ ((fun y0 : nat => ((y0 = (S (NUMERAL 0))) \/ (y0 = (NUMERAL 0))) -> (~ (y0 = (NUMERAL 0))) = (y0 = (S (NUMERAL 0)))) x0).
Definition term68 := forall y0 : nat, ~ ((S y0) = (NUMERAL 0)).
Definition term126 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2)).
Definition term75 (x0 : nat) := (~ (~ (x0 = (NUMERAL 0)))) /\ (x0 = (S (NUMERAL 0))).
Definition term135 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term102 (x0 : nat) := (fun y0 : nat => ~ (y0 = (NUMERAL 0))) x0.
Definition term23 := forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Odd y0) = (~ (Coq.Arith.PeanoNat.Nat.Even y0)).
Definition term31 (x0 : nat) := Peano.lt (Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))) (NUMERAL (BIT0 (BIT1 0))).
Definition term7 (x0 : nat) := (fun y0 : nat => (Peano.lt y0 (NUMERAL 0)) = False) x0.
Definition term22 := forall y0 : nat, (~ (Coq.Arith.PeanoNat.Nat.Even y0)) = (Coq.Arith.PeanoNat.Nat.Odd y0).
Definition term64 := (((~ (forall y0 : nat, ((y0 = (S (NUMERAL 0))) \/ (y0 = (NUMERAL 0))) -> (~ (y0 = (NUMERAL 0))) = (y0 = (S (NUMERAL 0))))) -> (forall y0 : nat, ~ ((S y0) = (NUMERAL 0))) -> False) -> (~ (forall y0 : nat, ((y0 = (S (NUMERAL 0))) \/ (y0 = (NUMERAL 0))) -> (~ (y0 = (NUMERAL 0))) = (y0 = (S (NUMERAL 0))))) -> (forall y0 : nat, ~ ((S y0) = (NUMERAL 0))) -> False) -> (~ (forall y0 : nat, ((y0 = (S (NUMERAL 0))) \/ (y0 = (NUMERAL 0))) -> (~ (y0 = (NUMERAL 0))) = (y0 = (S (NUMERAL 0))))) -> (forall y0 : nat, ~ ((S y0) = (NUMERAL 0))) -> False.
Definition term155 (x0 : nat) := (fun y0 : nat => (Peano.lt y0 (NUMERAL (BIT0 (BIT1 0)))) -> (~ (y0 = (NUMERAL 0))) = (y0 = (NUMERAL (BIT1 0)))) (Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term27 (x0 : nat) := ~ ((Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)).
Definition term46 (x0 : nat) := or (x0 = (NUMERAL 0)).
Definition term21 := fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Odd y0) = (~ (Coq.Arith.PeanoNat.Nat.Even y0)).
Definition term141 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term0 := forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)).
Definition term42 (x0 : nat) := Peano.lt x0 (S (S (NUMERAL 0))).
Definition term71 := fun y0 : nat => ~ ((S y0) = (NUMERAL 0)).
Definition term122 := (~ ((S (NUMERAL 0)) = (NUMERAL 0))) -> (S (NUMERAL 0)) = (NUMERAL 0).
Definition term55 := fun y0 : nat => (Peano.lt y0 (NUMERAL (BIT0 (BIT1 0)))) -> (~ (y0 = (NUMERAL 0))) = (y0 = (NUMERAL (BIT1 0))).
Definition term43 (x0 : nat) := (x0 = (S (NUMERAL 0))) \/ (Peano.lt x0 (S (NUMERAL 0))).
Definition term94 (x0 : nat) := ~ (x0 = (S (NUMERAL 0))).
Definition term4 (x0 : nat) (x1 : nat) := Peano.lt x0 (S x1).
Definition term103 := (fun y0 : nat => ~ (y0 = (NUMERAL 0))) (NUMERAL 0).
Definition term35 := S (NUMERAL (BIT1 0)).
Definition term15 (x0 : nat) (x1 : nat) := (~ (x1 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1).
Definition term154 := (((NUMERAL 0) = (S (NUMERAL 0))) /\ ((NUMERAL 0) = (NUMERAL 0))) -> (S (NUMERAL 0)) = (NUMERAL 0).
Definition term157 := forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Odd y0) = ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0))).
Definition term81 (x0 : nat) := and ((x0 = (S (NUMERAL 0))) \/ (x0 = (NUMERAL 0))).
Definition term88 (x0 : nat) := (fun y0 : nat => ((y0 = (S (NUMERAL 0))) \/ (y0 = (NUMERAL 0))) -> (~ (y0 = (NUMERAL 0))) = (y0 = (S (NUMERAL 0)))) x0.
Definition term130 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = x2) \/ (~ (x1 = x2)).
Definition term2 (x0 : nat) := forall y0 : nat, (Peano.lt x0 (S y0)) = ((x0 = y0) \/ (Peano.lt x0 y0)).
Definition term92 := exists y0 : nat, ((y0 = (S (NUMERAL 0))) \/ (y0 = (NUMERAL 0))) /\ (((~ (y0 = (NUMERAL 0))) /\ (~ (y0 = (S (NUMERAL 0))))) \/ ((y0 = (NUMERAL 0)) /\ (y0 = (S (NUMERAL 0))))).
Definition term10 (x0 : nat) := ~ ((S x0) = (NUMERAL 0)).
Definition term60 := (~ (forall y0 : nat, ((y0 = (S (NUMERAL 0))) \/ (y0 = (NUMERAL 0))) -> (~ (y0 = (NUMERAL 0))) = (y0 = (S (NUMERAL 0))))) -> False.
Definition term83 (x0 : nat) := ((x0 = (S (NUMERAL 0))) \/ (x0 = (NUMERAL 0))) /\ (((~ (x0 = (NUMERAL 0))) /\ (~ (x0 = (S (NUMERAL 0))))) \/ ((x0 = (NUMERAL 0)) /\ (x0 = (S (NUMERAL 0))))).
Definition term133 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x1 = x0)) \/ ((x0 = x2) \/ (~ (x1 = x2))).
Definition term48 (x0 : nat) := or (x0 = (S (NUMERAL 0))).
Definition term98 := ~ ((S (NUMERAL 0)) = (S (NUMERAL 0))).
Definition term66 := (forall y0 : nat, ~ ((S y0) = (NUMERAL 0))) -> False.
Definition term147 (x0 : nat) (x1 : nat) := and (~ (~ (x0 = x1))).
Definition term34 := NUMERAL (BIT0 (BIT1 0)).
Definition term49 (x0 : nat) := (x0 = (S (NUMERAL 0))) \/ (x0 = (NUMERAL 0)).
Definition term44 (x0 : nat) := Peano.lt x0 (S (NUMERAL 0)).
Definition term3 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt x0 (S y0)) = ((x0 = y0) \/ (Peano.lt x0 y0))) x1.
Definition term93 (x0 : nat) := (~ (x0 = (NUMERAL 0))) /\ (~ (x0 = (S (NUMERAL 0)))).
Definition term107 (x0 : nat) := (fun y0 : nat => y0 = (NUMERAL 0)) x0.
Definition term153 := ((NUMERAL 0) = (S (NUMERAL 0))) /\ ((NUMERAL 0) = (NUMERAL 0)).
Definition term8 (x0 : nat) := Peano.lt x0 (NUMERAL 0).
Definition term114 (x0 : nat) := @eq Prop ((fun y0 : nat => y0 = (S (NUMERAL 0))) x0).
Definition term109 (x0 : nat) := @eq Prop ((fun y0 : nat => y0 = (NUMERAL 0)) x0).
Definition term12 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) x0.
Definition term1 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1))) x0.
Definition term9 (x0 : nat) := (fun y0 : nat => ~ ((S y0) = (NUMERAL 0))) x0.
Definition term82 (x0 : nat) := ((x0 = (S (NUMERAL 0))) \/ (x0 = (NUMERAL 0))) /\ (~ ((~ (x0 = (NUMERAL 0))) = (x0 = (S (NUMERAL 0))))).
Definition term38 := ~ ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)).
Definition term32 (x0 : nat) (x1 : nat) := (~ (x1 = (NUMERAL 0))) -> (Peano.lt (Nat.modulo x0 x1) x1) = True.
Definition term20 := fun y0 : nat => (~ (Coq.Arith.PeanoNat.Nat.Even y0)) = (Coq.Arith.PeanoNat.Nat.Odd y0).
Definition term143 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term47 (x0 : nat) := (x0 = (NUMERAL 0)) \/ False.
Definition term87 := exists y0 : nat, ~ ((fun y1 : nat => ((y1 = (S (NUMERAL 0))) \/ (y1 = (NUMERAL 0))) -> (~ (y1 = (NUMERAL 0))) = (y1 = (S (NUMERAL 0)))) y0).
Definition term70 := (~ (forall y0 : nat, ((y0 = (S (NUMERAL 0))) \/ (y0 = (NUMERAL 0))) -> (~ (y0 = (NUMERAL 0))) = (y0 = (S (NUMERAL 0))))) -> ~ (forall y0 : nat, ~ ((S y0) = (NUMERAL 0))).
Definition term11 (x0 : nat) := (~ ((S x0) = (NUMERAL 0))) -> ((S x0) = (NUMERAL 0)) = False.
Definition term51 (x0 : nat) := imp ((x0 = (S (NUMERAL 0))) \/ (x0 = (NUMERAL 0))).
Definition term18 (x0 : nat) (x1 : nat) := Peano.lt (Nat.modulo x0 x1) x1.
Definition term14 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0)) x1.
Definition term80 (x0 : nat) := ~ ((~ (x0 = (NUMERAL 0))) = (x0 = (S (NUMERAL 0)))).
Definition term151 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((x1 = x0) /\ (x1 = x2)).
Definition term106 := fun y0 : nat => y0 = (NUMERAL 0).
Definition term58 := forall y0 : nat, ((y0 = (S (NUMERAL 0))) \/ (y0 = (NUMERAL 0))) -> (~ (y0 = (NUMERAL 0))) = (y0 = (S (NUMERAL 0))).
Definition term57 := forall y0 : nat, (Peano.lt y0 (NUMERAL (BIT0 (BIT1 0)))) -> (~ (y0 = (NUMERAL 0))) = (y0 = (NUMERAL (BIT1 0))).
Definition term123 := ~ ((S (NUMERAL 0)) = (NUMERAL 0)).
Definition term90 := fun y0 : nat => ~ ((fun y1 : nat => ((y1 = (S (NUMERAL 0))) \/ (y1 = (NUMERAL 0))) -> (~ (y1 = (NUMERAL 0))) = (y1 = (S (NUMERAL 0)))) y0).
Definition term127 := (~ ((NUMERAL 0) = (S (NUMERAL 0)))) -> (NUMERAL 0) = (S (NUMERAL 0)).
Definition term129 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = x2)) \/ (x1 = x2).
Definition term41 (x0 : nat) := Peano.lt x0 (NUMERAL (BIT0 (BIT1 0))).
Definition term63 := ((~ (forall y0 : nat, ((y0 = (S (NUMERAL 0))) \/ (y0 = (NUMERAL 0))) -> (~ (y0 = (NUMERAL 0))) = (y0 = (S (NUMERAL 0))))) -> (forall y0 : nat, ~ ((S y0) = (NUMERAL 0))) -> False) -> (~ (forall y0 : nat, ((y0 = (S (NUMERAL 0))) \/ (y0 = (NUMERAL 0))) -> (~ (y0 = (NUMERAL 0))) = (y0 = (S (NUMERAL 0))))) -> (forall y0 : nat, ~ ((S y0) = (NUMERAL 0))) -> False.
Definition term72 (x0 : nat) := ~ (~ (x0 = (NUMERAL 0))).
Definition term146 (x0 : nat) (x1 : nat) := ~ (~ (x0 = x1)).
Definition term65 := (((~ (forall y0 : nat, ((y0 = (S (NUMERAL 0))) \/ (y0 = (NUMERAL 0))) -> (~ (y0 = (NUMERAL 0))) = (y0 = (S (NUMERAL 0))))) -> (forall y0 : nat, ~ ((S y0) = (NUMERAL 0))) -> False) -> (~ (forall y0 : nat, ((y0 = (S (NUMERAL 0))) \/ (y0 = (NUMERAL 0))) -> (~ (y0 = (NUMERAL 0))) = (y0 = (S (NUMERAL 0))))) -> (forall y0 : nat, ~ ((S y0) = (NUMERAL 0))) -> False) -> ((~ (forall y0 : nat, ((y0 = (S (NUMERAL 0))) \/ (y0 = (NUMERAL 0))) -> (~ (y0 = (NUMERAL 0))) = (y0 = (S (NUMERAL 0))))) -> (forall y0 : nat, ~ ((S y0) = (NUMERAL 0))) -> False) -> (~ (forall y0 : nat, ((y0 = (S (NUMERAL 0))) \/ (y0 = (NUMERAL 0))) -> (~ (y0 = (NUMERAL 0))) = (y0 = (S (NUMERAL 0))))) -> (forall y0 : nat, ~ ((S y0) = (NUMERAL 0))) -> False.
Definition term124 (x0 : nat) := ((S x0) = (NUMERAL 0)) -> False.
Definition term13 (x0 : nat) := forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0).
Definition term54 (x0 : nat) := ((x0 = (S (NUMERAL 0))) \/ (x0 = (NUMERAL 0))) -> (~ (x0 = (NUMERAL 0))) = (x0 = (S (NUMERAL 0))).
Definition term132 (x0 : nat) (x1 : nat) := or (~ (x0 = x1)).
Definition term152 (x0 : nat) (x1 : nat) (x2 : nat) := ((x0 = x1) /\ (x0 = x2)) -> x1 = x2.
Definition term86 (x0 : nat -> Prop) := exists y0 : nat, ~ (x0 y0).
Definition term28 (x0 : nat) := @eq Prop (Coq.Arith.PeanoNat.Nat.Odd x0).
Definition term110 (x0 : nat) := @eq Prop (x0 = (NUMERAL 0)).
Definition term24 (x0 : nat) := (fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even y0) = ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0))) x0.
Definition term30 := NUMERAL (BIT1 0).
Definition term69 := imp (~ (forall y0 : nat, ((y0 = (S (NUMERAL 0))) \/ (y0 = (NUMERAL 0))) -> (~ (y0 = (NUMERAL 0))) = (y0 = (S (NUMERAL 0))))).
Definition term78 (x0 : nat) := ((~ (x0 = (NUMERAL 0))) /\ (~ (x0 = (S (NUMERAL 0))))) \/ ((~ (~ (x0 = (NUMERAL 0)))) /\ (x0 = (S (NUMERAL 0)))).
Definition term128 := ~ ((NUMERAL 0) = (S (NUMERAL 0))).
Definition term26 (x0 : nat) := (fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Odd y0) = (~ (Coq.Arith.PeanoNat.Nat.Even y0))) x0.
