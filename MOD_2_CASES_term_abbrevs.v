Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term37 (x0 : nat) := (((Coq.Arith.PeanoNat.Nat.Even x0) = False) -> ((Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))) = (@COND nat (Coq.Arith.PeanoNat.Nat.Even x0) (NUMERAL 0) (NUMERAL (BIT1 0)))) = ((Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0)))) /\ (((Coq.Arith.PeanoNat.Nat.Even x0) = True) -> ((Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))) = (@COND nat (Coq.Arith.PeanoNat.Nat.Even x0) (NUMERAL 0) (NUMERAL (BIT1 0)))) = ((Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0))).
Definition term119 (x0 : nat) := (fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Odd y0) \/ (Coq.Arith.PeanoNat.Nat.Even y0)) x0.
Definition term185 (x0 : nat) := (~ (Coq.Arith.PeanoNat.Nat.Even x0)) -> Coq.Arith.PeanoNat.Nat.Even x0.
Definition term20 := fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even y0) = ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)).
Definition term64 (x0 : nat -> Prop) := ~ (all x0).
Definition term166 (x0 : nat) := (fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even y0) \/ (~ ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)))) x0.
Definition term198 := (~ False) -> False.
Definition term52 (x0 : nat) := (Coq.Arith.PeanoNat.Nat.Even x0) /\ (~ ((Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0))).
Definition term159 (x0 : nat) := ((Coq.Arith.PeanoNat.Nat.Even x0) \/ (~ ((Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)))) /\ ((~ (Coq.Arith.PeanoNat.Nat.Even x0)) \/ ((Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0))).
Definition term162 := forall y0 : nat, ((fun y1 : nat => (Coq.Arith.PeanoNat.Nat.Even y1) \/ (~ ((Nat.modulo y1 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)))) y0) /\ ((fun y1 : nat => (~ (Coq.Arith.PeanoNat.Nat.Even y1)) \/ ((Nat.modulo y1 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0))) y0).
Definition term136 := forall y0 : nat, ((fun y1 : nat => (Coq.Arith.PeanoNat.Nat.Odd y1) \/ (~ ((Nat.modulo y1 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0))))) y0) /\ ((fun y1 : nat => (~ (Coq.Arith.PeanoNat.Nat.Odd y1)) \/ ((Nat.modulo y1 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0)))) y0).
Definition term112 := forall y0 : nat, ((fun y1 : nat => (~ (Coq.Arith.PeanoNat.Nat.Odd y1)) \/ (~ (Coq.Arith.PeanoNat.Nat.Even y1))) y0) /\ ((fun y1 : nat => (Coq.Arith.PeanoNat.Nat.Odd y1) \/ (Coq.Arith.PeanoNat.Nat.Even y1)) y0).
Definition term26 := forall y0 : nat, (~ (Coq.Arith.PeanoNat.Nat.Odd y0)) = (Coq.Arith.PeanoNat.Nat.Even y0).
Definition term210 (x0 : nat) := (~ ((Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0)))) -> (Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0)).
Definition term192 (x0 : Prop) := ~ (~ x0).
Definition term28 (x0 : nat) := @COND nat (Coq.Arith.PeanoNat.Nat.Even x0) (NUMERAL 0).
Definition term46 := (~ (forall y0 : nat, ((~ (Coq.Arith.PeanoNat.Nat.Even y0)) \/ ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0))) /\ ((Coq.Arith.PeanoNat.Nat.Even y0) \/ ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0)))))) -> (forall y0 : nat, (~ (Coq.Arith.PeanoNat.Nat.Odd y0)) = (Coq.Arith.PeanoNat.Nat.Even y0)) -> (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Odd y0) = ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0)))) -> ~ (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even y0) = ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0))).
Definition term18 := (~ (forall y0 : nat, (Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (@COND nat (Coq.Arith.PeanoNat.Nat.Even y0) (NUMERAL 0) (NUMERAL (BIT1 0))))) -> (forall y0 : nat, (~ (Coq.Arith.PeanoNat.Nat.Odd y0)) = (Coq.Arith.PeanoNat.Nat.Even y0)) -> (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Odd y0) = ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0)))) -> ~ (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even y0) = ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0))).
Definition term172 := fun y0 : nat => ((fun y1 : nat => (Coq.Arith.PeanoNat.Nat.Even y1) \/ (~ ((Nat.modulo y1 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)))) y0) /\ ((fun y1 : nat => (~ (Coq.Arith.PeanoNat.Nat.Even y1)) \/ ((Nat.modulo y1 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0))) y0).
Definition term147 := fun y0 : nat => ((fun y1 : nat => (Coq.Arith.PeanoNat.Nat.Odd y1) \/ (~ ((Nat.modulo y1 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0))))) y0) /\ ((fun y1 : nat => (~ (Coq.Arith.PeanoNat.Nat.Odd y1)) \/ ((Nat.modulo y1 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0)))) y0).
Definition term121 := fun y0 : nat => ((fun y1 : nat => (~ (Coq.Arith.PeanoNat.Nat.Odd y1)) \/ (~ (Coq.Arith.PeanoNat.Nat.Even y1))) y0) /\ ((fun y1 : nat => (Coq.Arith.PeanoNat.Nat.Odd y1) \/ (Coq.Arith.PeanoNat.Nat.Even y1)) y0).
Definition term140 (x0 : nat) := (fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Odd y0) \/ (~ ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0))))) x0.
Definition term91 := or (exists y0 : nat, (Coq.Arith.PeanoNat.Nat.Even y0) /\ (~ ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)))).
Definition term165 := fun y0 : nat => (~ (Coq.Arith.PeanoNat.Nat.Even y0)) \/ ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)).
Definition term95 := (exists y0 : nat, (Coq.Arith.PeanoNat.Nat.Even y0) /\ (~ ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)))) \/ (exists y0 : nat, (~ (Coq.Arith.PeanoNat.Nat.Even y0)) /\ (~ ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0))))).
Definition term73 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term60 (x0 : nat) := ((Coq.Arith.PeanoNat.Nat.Even x0) /\ (~ ((Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)))) \/ ((~ (Coq.Arith.PeanoNat.Nat.Even x0)) /\ (~ ((Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0))))).
Definition term203 (x0 : nat) := ((Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0))) \/ (~ (Coq.Arith.PeanoNat.Nat.Odd x0)).
Definition term164 := fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even y0) \/ (~ ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0))).
Definition term12 := (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Odd y0) = ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0)))) -> (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even y0) = ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0))) -> False.
Definition term0 (x0 : Prop) := (~ x0) -> False.
Definition term163 := (forall y0 : nat, (fun y1 : nat => (Coq.Arith.PeanoNat.Nat.Even y1) \/ (~ ((Nat.modulo y1 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)))) y0) /\ (forall y0 : nat, (fun y1 : nat => (~ (Coq.Arith.PeanoNat.Nat.Even y1)) \/ ((Nat.modulo y1 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0))) y0).
Definition term137 := (forall y0 : nat, (fun y1 : nat => (Coq.Arith.PeanoNat.Nat.Odd y1) \/ (~ ((Nat.modulo y1 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0))))) y0) /\ (forall y0 : nat, (fun y1 : nat => (~ (Coq.Arith.PeanoNat.Nat.Odd y1)) \/ ((Nat.modulo y1 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0)))) y0).
Definition term113 := (forall y0 : nat, (fun y1 : nat => (~ (Coq.Arith.PeanoNat.Nat.Odd y1)) \/ (~ (Coq.Arith.PeanoNat.Nat.Even y1))) y0) /\ (forall y0 : nat, (fun y1 : nat => (Coq.Arith.PeanoNat.Nat.Odd y1) \/ (Coq.Arith.PeanoNat.Nat.Even y1)) y0).
Definition term22 := fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Odd y0) = ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0))).
Definition term131 := forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Odd y0) \/ (Coq.Arith.PeanoNat.Nat.Even y0).
Definition term54 (x0 : nat) := ~ (Coq.Arith.PeanoNat.Nat.Even x0).
Definition term191 (x0 : nat) := (~ (~ (Coq.Arith.PeanoNat.Nat.Even x0))) -> (Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0).
Definition term19 (x0 : nat) := Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0))).
Definition term208 (x0 : nat) := imp (Coq.Arith.PeanoNat.Nat.Odd x0).
Definition term105 (x0 : nat) := ((~ (Coq.Arith.PeanoNat.Nat.Odd x0)) \/ (~ (Coq.Arith.PeanoNat.Nat.Even x0))) /\ ((Coq.Arith.PeanoNat.Nat.Odd x0) \/ (Coq.Arith.PeanoNat.Nat.Even x0)).
Definition term181 := forall y0 : nat, (fun y1 : nat => (~ (Coq.Arith.PeanoNat.Nat.Even y1)) \/ ((Nat.modulo y1 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0))) y0.
Definition term176 := forall y0 : nat, (fun y1 : nat => (Coq.Arith.PeanoNat.Nat.Even y1) \/ (~ ((Nat.modulo y1 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)))) y0.
Definition term156 := forall y0 : nat, (fun y1 : nat => (~ (Coq.Arith.PeanoNat.Nat.Odd y1)) \/ ((Nat.modulo y1 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0)))) y0.
Definition term151 := forall y0 : nat, (fun y1 : nat => (Coq.Arith.PeanoNat.Nat.Odd y1) \/ (~ ((Nat.modulo y1 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0))))) y0.
Definition term130 := forall y0 : nat, (fun y1 : nat => (Coq.Arith.PeanoNat.Nat.Odd y1) \/ (Coq.Arith.PeanoNat.Nat.Even y1)) y0.
Definition term125 := forall y0 : nat, (fun y1 : nat => (~ (Coq.Arith.PeanoNat.Nat.Odd y1)) \/ (~ (Coq.Arith.PeanoNat.Nat.Even y1))) y0.
Definition term134 := fun y0 : nat => ((Coq.Arith.PeanoNat.Nat.Odd y0) \/ (~ ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0))))) /\ ((~ (Coq.Arith.PeanoNat.Nat.Odd y0)) \/ ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0)))).
Definition term201 (x0 : nat) := (~ (Coq.Arith.PeanoNat.Nat.Even x0)) -> Coq.Arith.PeanoNat.Nat.Odd x0.
Definition term190 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term110 (x0 : nat -> Prop) (x1 : nat -> Prop) := forall y0 : nat, (x0 y0) /\ (x1 y0).
Definition term44 := ~ (forall y0 : nat, ((~ (Coq.Arith.PeanoNat.Nat.Even y0)) \/ ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0))) /\ ((Coq.Arith.PeanoNat.Nat.Even y0) \/ ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0))))).
Definition term9 := ~ (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even y0) = ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0))).
Definition term3 := ~ (forall y0 : nat, (Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (@COND nat (Coq.Arith.PeanoNat.Nat.Even y0) (NUMERAL 0) (NUMERAL (BIT1 0)))).
Definition term211 (x0 : nat) := ((Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0))) -> False.
Definition term80 (x0 : nat) := (fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even y0) /\ (~ ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)))) x0.
Definition term47 (x0 : nat) := ~ (~ (Coq.Arith.PeanoNat.Nat.Even x0)).
Definition term143 (x0 : nat) := and ((Coq.Arith.PeanoNat.Nat.Odd x0) \/ (~ ((Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0))))).
Definition term205 (x0 : nat) := @eq Prop (((Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0))) \/ (~ (Coq.Arith.PeanoNat.Nat.Odd x0))).
Definition term186 (x0 : Prop) := (~ x0) -> x0.
Definition term49 (x0 : nat) := and (~ (~ (Coq.Arith.PeanoNat.Nat.Even x0))).
Definition term195 (x0 : nat) := (Coq.Arith.PeanoNat.Nat.Even x0) -> (Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0).
Definition term99 (x0 : nat) := or (~ (~ (Coq.Arith.PeanoNat.Nat.Odd x0))).
Definition term82 (x0 : nat) := (fun y0 : nat => (~ (Coq.Arith.PeanoNat.Nat.Even y0)) /\ (~ ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0))))) x0.
Definition term194 (x0 : nat) := imp (Coq.Arith.PeanoNat.Nat.Even x0).
Definition term174 := @eq Prop (forall y0 : nat, ((Coq.Arith.PeanoNat.Nat.Even y0) \/ (~ ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)))) /\ ((~ (Coq.Arith.PeanoNat.Nat.Even y0)) \/ ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)))).
Definition term173 := @eq Prop (forall y0 : nat, ((fun y1 : nat => (Coq.Arith.PeanoNat.Nat.Even y1) \/ (~ ((Nat.modulo y1 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)))) y0) /\ ((fun y1 : nat => (~ (Coq.Arith.PeanoNat.Nat.Even y1)) \/ ((Nat.modulo y1 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0))) y0)).
Definition term149 := @eq Prop (forall y0 : nat, ((Coq.Arith.PeanoNat.Nat.Odd y0) \/ (~ ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0))))) /\ ((~ (Coq.Arith.PeanoNat.Nat.Odd y0)) \/ ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0))))).
Definition term148 := @eq Prop (forall y0 : nat, ((fun y1 : nat => (Coq.Arith.PeanoNat.Nat.Odd y1) \/ (~ ((Nat.modulo y1 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0))))) y0) /\ ((fun y1 : nat => (~ (Coq.Arith.PeanoNat.Nat.Odd y1)) \/ ((Nat.modulo y1 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0)))) y0)).
Definition term123 := @eq Prop (forall y0 : nat, ((~ (Coq.Arith.PeanoNat.Nat.Odd y0)) \/ (~ (Coq.Arith.PeanoNat.Nat.Even y0))) /\ ((Coq.Arith.PeanoNat.Nat.Odd y0) \/ (Coq.Arith.PeanoNat.Nat.Even y0))).
Definition term122 := @eq Prop (forall y0 : nat, ((fun y1 : nat => (~ (Coq.Arith.PeanoNat.Nat.Odd y1)) \/ (~ (Coq.Arith.PeanoNat.Nat.Even y1))) y0) /\ ((fun y1 : nat => (Coq.Arith.PeanoNat.Nat.Odd y1) \/ (Coq.Arith.PeanoNat.Nat.Even y1)) y0)).
Definition term157 := forall y0 : nat, (~ (Coq.Arith.PeanoNat.Nat.Odd y0)) \/ ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0))).
Definition term36 (x0 : nat) := ((Coq.Arith.PeanoNat.Nat.Even x0) = True) -> ((Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))) = (@COND nat (Coq.Arith.PeanoNat.Nat.Even x0) (NUMERAL 0) (NUMERAL (BIT1 0)))) = ((Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)).
Definition term109 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term138 := fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Odd y0) \/ (~ ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0)))).
Definition term83 (x0 : nat) := ((fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even y0) /\ (~ ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)))) x0) \/ ((fun y0 : nat => (~ (Coq.Arith.PeanoNat.Nat.Even y0)) /\ (~ ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0))))) x0).
Definition term177 := forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even y0) \/ (~ ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0))).
Definition term152 := forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Odd y0) \/ (~ ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0)))).
Definition term70 := fun y0 : nat => ((Coq.Arith.PeanoNat.Nat.Even y0) /\ (~ ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)))) \/ ((~ (Coq.Arith.PeanoNat.Nat.Even y0)) /\ (~ ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0))))).
Definition term116 (x0 : nat) := (fun y0 : nat => (~ (Coq.Arith.PeanoNat.Nat.Odd y0)) \/ (~ (Coq.Arith.PeanoNat.Nat.Even y0))) x0.
Definition term86 := @eq Prop (exists y0 : nat, ((Coq.Arith.PeanoNat.Nat.Even y0) /\ (~ ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)))) \/ ((~ (Coq.Arith.PeanoNat.Nat.Even y0)) /\ (~ ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0)))))).
Definition term85 := @eq Prop (exists y0 : nat, ((fun y1 : nat => (Coq.Arith.PeanoNat.Nat.Even y1) /\ (~ ((Nat.modulo y1 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)))) y0) \/ ((fun y1 : nat => (~ (Coq.Arith.PeanoNat.Nat.Even y1)) /\ (~ ((Nat.modulo y1 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0))))) y0)).
Definition term71 := exists y0 : nat, ((Coq.Arith.PeanoNat.Nat.Even y0) /\ (~ ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)))) \/ ((~ (Coq.Arith.PeanoNat.Nat.Even y0)) /\ (~ ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0))))).
Definition term68 (x0 : nat) := ~ ((fun y0 : nat => ((~ (Coq.Arith.PeanoNat.Nat.Even y0)) \/ ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0))) /\ ((Coq.Arith.PeanoNat.Nat.Even y0) \/ ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0))))) x0).
Definition term129 := fun y0 : nat => (fun y1 : nat => (Coq.Arith.PeanoNat.Nat.Odd y1) \/ (Coq.Arith.PeanoNat.Nat.Even y1)) y0.
Definition term168 (x0 : nat) := and ((fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even y0) \/ (~ ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)))) x0).
Definition term142 (x0 : nat) := and ((fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Odd y0) \/ (~ ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0))))) x0).
Definition term118 (x0 : nat) := and ((fun y0 : nat => (~ (Coq.Arith.PeanoNat.Nat.Odd y0)) \/ (~ (Coq.Arith.PeanoNat.Nat.Even y0))) x0).
Definition term51 (x0 : nat) := (~ (~ (Coq.Arith.PeanoNat.Nat.Even x0))) /\ (~ ((Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0))).
Definition term171 (x0 : nat) := ((fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even y0) \/ (~ ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)))) x0) /\ ((fun y0 : nat => (~ (Coq.Arith.PeanoNat.Nat.Even y0)) \/ ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0))) x0).
Definition term146 (x0 : nat) := ((fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Odd y0) \/ (~ ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0))))) x0) /\ ((fun y0 : nat => (~ (Coq.Arith.PeanoNat.Nat.Odd y0)) \/ ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0)))) x0).
Definition term120 (x0 : nat) := ((fun y0 : nat => (~ (Coq.Arith.PeanoNat.Nat.Odd y0)) \/ (~ (Coq.Arith.PeanoNat.Nat.Even y0))) x0) /\ ((fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Odd y0) \/ (Coq.Arith.PeanoNat.Nat.Even y0)) x0).
Definition term204 (x0 : nat) := @eq Prop ((~ (Coq.Arith.PeanoNat.Nat.Odd x0)) \/ ((Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0)))).
Definition term59 (x0 : nat) := (~ ((~ (Coq.Arith.PeanoNat.Nat.Even x0)) \/ ((Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)))) \/ (~ ((Coq.Arith.PeanoNat.Nat.Even x0) \/ ((Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0))))).
Definition term175 := fun y0 : nat => (fun y1 : nat => (Coq.Arith.PeanoNat.Nat.Even y1) \/ (~ ((Nat.modulo y1 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)))) y0.
Definition term150 := fun y0 : nat => (fun y1 : nat => (Coq.Arith.PeanoNat.Nat.Odd y1) \/ (~ ((Nat.modulo y1 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0))))) y0.
Definition term124 := fun y0 : nat => (fun y1 : nat => (~ (Coq.Arith.PeanoNat.Nat.Odd y1)) \/ (~ (Coq.Arith.PeanoNat.Nat.Even y1))) y0.
Definition term77 := (exists y0 : nat, (fun y1 : nat => (Coq.Arith.PeanoNat.Nat.Even y1) /\ (~ ((Nat.modulo y1 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)))) y0) \/ (exists y0 : nat, (fun y1 : nat => (~ (Coq.Arith.PeanoNat.Nat.Even y1)) /\ (~ ((Nat.modulo y1 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0))))) y0).
Definition term139 := fun y0 : nat => (~ (Coq.Arith.PeanoNat.Nat.Odd y0)) \/ ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0))).
Definition term58 (x0 : nat) := or ((Coq.Arith.PeanoNat.Nat.Even x0) /\ (~ ((Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)))).
Definition term1 := forall y0 : nat, (Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (@COND nat (Coq.Arith.PeanoNat.Nat.Even y0) (NUMERAL 0) (NUMERAL (BIT1 0))).
Definition term92 := fun y0 : nat => (fun y1 : nat => (~ (Coq.Arith.PeanoNat.Nat.Even y1)) /\ (~ ((Nat.modulo y1 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0))))) y0.
Definition term87 := fun y0 : nat => (fun y1 : nat => (Coq.Arith.PeanoNat.Nat.Even y1) /\ (~ ((Nat.modulo y1 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)))) y0.
Definition term7 := (((~ (forall y0 : nat, (Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (@COND nat (Coq.Arith.PeanoNat.Nat.Even y0) (NUMERAL 0) (NUMERAL (BIT1 0))))) -> (forall y0 : nat, (~ (Coq.Arith.PeanoNat.Nat.Odd y0)) = (Coq.Arith.PeanoNat.Nat.Even y0)) -> (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Odd y0) = ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0)))) -> (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even y0) = ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0))) -> False) -> (~ (forall y0 : nat, (Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (@COND nat (Coq.Arith.PeanoNat.Nat.Even y0) (NUMERAL 0) (NUMERAL (BIT1 0))))) -> (forall y0 : nat, (~ (Coq.Arith.PeanoNat.Nat.Odd y0)) = (Coq.Arith.PeanoNat.Nat.Even y0)) -> (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Odd y0) = ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0)))) -> (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even y0) = ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0))) -> False) -> ((~ (forall y0 : nat, (Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (@COND nat (Coq.Arith.PeanoNat.Nat.Even y0) (NUMERAL 0) (NUMERAL (BIT1 0))))) -> (forall y0 : nat, (~ (Coq.Arith.PeanoNat.Nat.Odd y0)) = (Coq.Arith.PeanoNat.Nat.Even y0)) -> (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Odd y0) = ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0)))) -> (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even y0) = ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0))) -> False) -> (~ (forall y0 : nat, (Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (@COND nat (Coq.Arith.PeanoNat.Nat.Even y0) (NUMERAL 0) (NUMERAL (BIT1 0))))) -> (forall y0 : nat, (~ (Coq.Arith.PeanoNat.Nat.Odd y0)) = (Coq.Arith.PeanoNat.Nat.Even y0)) -> (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Odd y0) = ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0)))) -> (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even y0) = ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0))) -> False.
Definition term14 := imp (forall y0 : nat, (~ (Coq.Arith.PeanoNat.Nat.Odd y0)) = (Coq.Arith.PeanoNat.Nat.Even y0)).
Definition term11 := imp (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Odd y0) = ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0)))).
Definition term202 (x0 : nat) := (~ (Coq.Arith.PeanoNat.Nat.Odd x0)) -> Coq.Arith.PeanoNat.Nat.Odd x0.
Definition term98 (x0 : nat) := ~ (~ (Coq.Arith.PeanoNat.Nat.Odd x0)).
Definition term179 := and (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even y0) \/ (~ ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)))).
Definition term154 := and (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Odd y0) \/ (~ ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0))))).
Definition term128 := and (forall y0 : nat, (~ (Coq.Arith.PeanoNat.Nat.Odd y0)) \/ (~ (Coq.Arith.PeanoNat.Nat.Even y0))).
Definition term182 := forall y0 : nat, (~ (Coq.Arith.PeanoNat.Nat.Even y0)) \/ ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)).
Definition term53 (x0 : nat) := ~ ((~ (Coq.Arith.PeanoNat.Nat.Even x0)) \/ ((Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0))).
Definition term145 (x0 : nat) := (~ (Coq.Arith.PeanoNat.Nat.Odd x0)) \/ ((Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0))).
Definition term170 (x0 : nat) := (fun y0 : nat => (~ (Coq.Arith.PeanoNat.Nat.Even y0)) \/ ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0))) x0.
Definition term5 := ((~ (forall y0 : nat, (Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (@COND nat (Coq.Arith.PeanoNat.Nat.Even y0) (NUMERAL 0) (NUMERAL (BIT1 0))))) -> (forall y0 : nat, (~ (Coq.Arith.PeanoNat.Nat.Odd y0)) = (Coq.Arith.PeanoNat.Nat.Even y0)) -> (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Odd y0) = ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0)))) -> (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even y0) = ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0))) -> False) -> (~ (forall y0 : nat, (Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (@COND nat (Coq.Arith.PeanoNat.Nat.Even y0) (NUMERAL 0) (NUMERAL (BIT1 0))))) -> (forall y0 : nat, (~ (Coq.Arith.PeanoNat.Nat.Odd y0)) = (Coq.Arith.PeanoNat.Nat.Even y0)) -> (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Odd y0) = ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0)))) -> (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even y0) = ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0))) -> False.
Definition term55 (x0 : nat) := ~ ((Coq.Arith.PeanoNat.Nat.Even x0) \/ ((Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0)))).
Definition term41 := fun y0 : nat => (Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (@COND nat (Coq.Arith.PeanoNat.Nat.Even y0) (NUMERAL 0) (NUMERAL (BIT1 0))).
Definition term94 := exists y0 : nat, (~ (Coq.Arith.PeanoNat.Nat.Even y0)) /\ (~ ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0)))).
Definition term34 := @COND nat True (NUMERAL 0).
Definition term48 (x0 : nat) := ~ ((Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)).
Definition term13 := (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Odd y0) = ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0)))) -> ~ (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even y0) = ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0))).
Definition term180 := fun y0 : nat => (fun y1 : nat => (~ (Coq.Arith.PeanoNat.Nat.Even y1)) \/ ((Nat.modulo y1 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0))) y0.
Definition term155 := fun y0 : nat => (fun y1 : nat => (~ (Coq.Arith.PeanoNat.Nat.Odd y1)) \/ ((Nat.modulo y1 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0)))) y0.
Definition term56 (x0 : nat) := (~ (Coq.Arith.PeanoNat.Nat.Even x0)) /\ (~ ((Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0)))).
Definition term6 := (((~ (forall y0 : nat, (Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (@COND nat (Coq.Arith.PeanoNat.Nat.Even y0) (NUMERAL 0) (NUMERAL (BIT1 0))))) -> (forall y0 : nat, (~ (Coq.Arith.PeanoNat.Nat.Odd y0)) = (Coq.Arith.PeanoNat.Nat.Even y0)) -> (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Odd y0) = ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0)))) -> (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even y0) = ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0))) -> False) -> (~ (forall y0 : nat, (Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (@COND nat (Coq.Arith.PeanoNat.Nat.Even y0) (NUMERAL 0) (NUMERAL (BIT1 0))))) -> (forall y0 : nat, (~ (Coq.Arith.PeanoNat.Nat.Odd y0)) = (Coq.Arith.PeanoNat.Nat.Even y0)) -> (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Odd y0) = ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0)))) -> (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even y0) = ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0))) -> False) -> (~ (forall y0 : nat, (Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (@COND nat (Coq.Arith.PeanoNat.Nat.Even y0) (NUMERAL 0) (NUMERAL (BIT1 0))))) -> (forall y0 : nat, (~ (Coq.Arith.PeanoNat.Nat.Odd y0)) = (Coq.Arith.PeanoNat.Nat.Even y0)) -> (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Odd y0) = ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0)))) -> (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even y0) = ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0))) -> False.
Definition term33 (x0 : nat) := ((Coq.Arith.PeanoNat.Nat.Even x0) = False) -> ((Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))) = (@COND nat (Coq.Arith.PeanoNat.Nat.Even x0) (NUMERAL 0) (NUMERAL (BIT1 0)))) = ((Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0))).
Definition term76 := exists y0 : nat, ((fun y1 : nat => (Coq.Arith.PeanoNat.Nat.Even y1) /\ (~ ((Nat.modulo y1 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)))) y0) \/ ((fun y1 : nat => (~ (Coq.Arith.PeanoNat.Nat.Even y1)) /\ (~ ((Nat.modulo y1 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0))))) y0).
Definition term25 := fun y0 : nat => (~ (Coq.Arith.PeanoNat.Nat.Odd y0)) = (Coq.Arith.PeanoNat.Nat.Even y0).
Definition term197 (x0 : nat) := ((Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)) -> False.
Definition term103 (x0 : nat) := and ((~ (Coq.Arith.PeanoNat.Nat.Odd x0)) \/ (~ (Coq.Arith.PeanoNat.Nat.Even x0))).
Definition term23 := forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Odd y0) = ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0))).
Definition term8 := (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even y0) = ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0))) -> False.
Definition term63 (x0 : nat) := (Coq.Arith.PeanoNat.Nat.Even x0) \/ ((Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0))).
Definition term101 (x0 : nat) := (~ (~ (Coq.Arith.PeanoNat.Nat.Odd x0))) \/ (Coq.Arith.PeanoNat.Nat.Even x0).
Definition term79 := fun y0 : nat => (~ (Coq.Arith.PeanoNat.Nat.Even y0)) /\ (~ ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0)))).
Definition term2 := (~ (forall y0 : nat, (Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (@COND nat (Coq.Arith.PeanoNat.Nat.Even y0) (NUMERAL 0) (NUMERAL (BIT1 0))))) -> False.
Definition term81 (x0 : nat) := or ((fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even y0) /\ (~ ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)))) x0).
Definition term4 := (~ (forall y0 : nat, (Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (@COND nat (Coq.Arith.PeanoNat.Nat.Even y0) (NUMERAL 0) (NUMERAL (BIT1 0))))) -> (forall y0 : nat, (~ (Coq.Arith.PeanoNat.Nat.Odd y0)) = (Coq.Arith.PeanoNat.Nat.Even y0)) -> (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Odd y0) = ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0)))) -> (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even y0) = ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0))) -> False.
Definition term111 (x0 : nat -> Prop) (x1 : nat -> Prop) := (forall y0 : nat, x0 y0) /\ (forall y0 : nat, x1 y0).
Definition term114 := fun y0 : nat => (~ (Coq.Arith.PeanoNat.Nat.Odd y0)) \/ (~ (Coq.Arith.PeanoNat.Nat.Even y0)).
Definition term93 := exists y0 : nat, (fun y1 : nat => (~ (Coq.Arith.PeanoNat.Nat.Even y1)) /\ (~ ((Nat.modulo y1 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0))))) y0.
Definition term88 := exists y0 : nat, (fun y1 : nat => (Coq.Arith.PeanoNat.Nat.Even y1) /\ (~ ((Nat.modulo y1 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)))) y0.
Definition term184 (x0 : nat) := ~ ((Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0))).
Definition term141 (x0 : nat) := (Coq.Arith.PeanoNat.Nat.Odd x0) \/ (~ ((Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0)))).
Definition term183 := (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even y0) \/ (~ ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)))) /\ (forall y0 : nat, (~ (Coq.Arith.PeanoNat.Nat.Even y0)) \/ ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0))).
Definition term158 := (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Odd y0) \/ (~ ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0))))) /\ (forall y0 : nat, (~ (Coq.Arith.PeanoNat.Nat.Odd y0)) \/ ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0)))).
Definition term132 := (forall y0 : nat, (~ (Coq.Arith.PeanoNat.Nat.Odd y0)) \/ (~ (Coq.Arith.PeanoNat.Nat.Even y0))) /\ (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Odd y0) \/ (Coq.Arith.PeanoNat.Nat.Even y0)).
Definition term35 := @COND nat True (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term39 (x0 : nat) := ((((Coq.Arith.PeanoNat.Nat.Even x0) = False) -> ((Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))) = (@COND nat (Coq.Arith.PeanoNat.Nat.Even x0) (NUMERAL 0) (NUMERAL (BIT1 0)))) = ((Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0)))) /\ (((Coq.Arith.PeanoNat.Nat.Even x0) = True) -> ((Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))) = (@COND nat (Coq.Arith.PeanoNat.Nat.Even x0) (NUMERAL 0) (NUMERAL (BIT1 0)))) = ((Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)))) -> ((Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))) = (@COND nat (Coq.Arith.PeanoNat.Nat.Even x0) (NUMERAL 0) (NUMERAL (BIT1 0)))) = (((~ (Coq.Arith.PeanoNat.Nat.Even x0)) \/ ((Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0))) /\ ((Coq.Arith.PeanoNat.Nat.Even x0) \/ ((Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0))))).
Definition term16 := (forall y0 : nat, (~ (Coq.Arith.PeanoNat.Nat.Odd y0)) = (Coq.Arith.PeanoNat.Nat.Even y0)) -> (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Odd y0) = ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0)))) -> ~ (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even y0) = ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0))).
Definition term206 (x0 : nat) := (~ (~ (Coq.Arith.PeanoNat.Nat.Odd x0))) -> (Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0)).
Definition term89 := exists y0 : nat, (Coq.Arith.PeanoNat.Nat.Even y0) /\ (~ ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0))).
Definition term38 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (((x2 = False) -> x0 = x3) /\ ((x2 = True) -> x0 = x1)) -> x0 = (((~ x2) \/ x1) /\ (x2 \/ x3)).
Definition term106 := fun y0 : nat => ((~ (Coq.Arith.PeanoNat.Nat.Odd y0)) \/ (~ (Coq.Arith.PeanoNat.Nat.Even y0))) /\ ((Coq.Arith.PeanoNat.Nat.Odd y0) \/ (Coq.Arith.PeanoNat.Nat.Even y0)).
Definition term10 := forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even y0) = ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)).
Definition term133 (x0 : nat) := ((Coq.Arith.PeanoNat.Nat.Odd x0) \/ (~ ((Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0))))) /\ ((~ (Coq.Arith.PeanoNat.Nat.Odd x0)) \/ ((Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0)))).
Definition term196 (x0 : nat) := (~ ((Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0))) -> (Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0).
Definition term209 (x0 : nat) := (Coq.Arith.PeanoNat.Nat.Odd x0) -> (Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0)).
Definition term189 (x0 : nat) := @eq Prop (((Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)) \/ (~ (Coq.Arith.PeanoNat.Nat.Even x0))).
Definition term40 (x0 : nat) := ((~ (Coq.Arith.PeanoNat.Nat.Even x0)) \/ ((Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0))) /\ ((Coq.Arith.PeanoNat.Nat.Even x0) \/ ((Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0)))).
Definition term42 := fun y0 : nat => ((~ (Coq.Arith.PeanoNat.Nat.Even y0)) \/ ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0))) /\ ((Coq.Arith.PeanoNat.Nat.Even y0) \/ ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0)))).
Definition term193 (x0 : nat) := imp (~ (~ (Coq.Arith.PeanoNat.Nat.Even x0))).
Definition term100 (x0 : nat) := or (Coq.Arith.PeanoNat.Nat.Odd x0).
Definition term117 (x0 : nat) := (~ (Coq.Arith.PeanoNat.Nat.Odd x0)) \/ (~ (Coq.Arith.PeanoNat.Nat.Even x0)).
Definition term66 := exists y0 : nat, ~ ((fun y1 : nat => ((~ (Coq.Arith.PeanoNat.Nat.Even y1)) \/ ((Nat.modulo y1 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0))) /\ ((Coq.Arith.PeanoNat.Nat.Even y1) \/ ((Nat.modulo y1 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0))))) y0).
Definition term199 (x0 : nat) := (Coq.Arith.PeanoNat.Nat.Even x0) -> ~ (Coq.Arith.PeanoNat.Nat.Even x0).
Definition term144 (x0 : nat) := (fun y0 : nat => (~ (Coq.Arith.PeanoNat.Nat.Odd y0)) \/ ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0)))) x0.
Definition term32 (x0 : nat) := @eq nat (Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term178 := and (forall y0 : nat, (fun y1 : nat => (Coq.Arith.PeanoNat.Nat.Even y1) \/ (~ ((Nat.modulo y1 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)))) y0).
Definition term153 := and (forall y0 : nat, (fun y1 : nat => (Coq.Arith.PeanoNat.Nat.Odd y1) \/ (~ ((Nat.modulo y1 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0))))) y0).
Definition term127 := and (forall y0 : nat, (fun y1 : nat => (~ (Coq.Arith.PeanoNat.Nat.Odd y1)) \/ (~ (Coq.Arith.PeanoNat.Nat.Even y1))) y0).
Definition term50 (x0 : nat) := and (Coq.Arith.PeanoNat.Nat.Even x0).
Definition term207 (x0 : nat) := imp (~ (~ (Coq.Arith.PeanoNat.Nat.Odd x0))).
Definition term78 := fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even y0) /\ (~ ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0))).
Definition term62 (x0 : nat) := (~ (Coq.Arith.PeanoNat.Nat.Even x0)) \/ ((Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)).
Definition term167 (x0 : nat) := (Coq.Arith.PeanoNat.Nat.Even x0) \/ (~ ((Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0))).
Definition term187 (x0 : nat) := ((Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)) \/ (~ (Coq.Arith.PeanoNat.Nat.Even x0)).
Definition term27 (x0 : nat) := @COND nat (Coq.Arith.PeanoNat.Nat.Even x0).
Definition term169 (x0 : nat) := and ((Coq.Arith.PeanoNat.Nat.Even x0) \/ (~ ((Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)))).
Definition term108 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term74 (x0 : nat -> Prop) (x1 : nat -> Prop) := exists y0 : nat, (x0 y0) \/ (x1 y0).
Definition term69 := fun y0 : nat => ~ ((fun y1 : nat => ((~ (Coq.Arith.PeanoNat.Nat.Even y1)) \/ ((Nat.modulo y1 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0))) /\ ((Coq.Arith.PeanoNat.Nat.Even y1) \/ ((Nat.modulo y1 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0))))) y0).
Definition term24 (x0 : nat) := ~ (Coq.Arith.PeanoNat.Nat.Odd x0).
Definition term115 := fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Odd y0) \/ (Coq.Arith.PeanoNat.Nat.Even y0).
Definition term104 (x0 : nat) := ((~ (Coq.Arith.PeanoNat.Nat.Odd x0)) \/ (~ (Coq.Arith.PeanoNat.Nat.Even x0))) /\ ((~ (~ (Coq.Arith.PeanoNat.Nat.Odd x0))) \/ (Coq.Arith.PeanoNat.Nat.Even x0)).
Definition term84 := fun y0 : nat => ((fun y1 : nat => (Coq.Arith.PeanoNat.Nat.Even y1) /\ (~ ((Nat.modulo y1 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)))) y0) \/ ((fun y1 : nat => (~ (Coq.Arith.PeanoNat.Nat.Even y1)) /\ (~ ((Nat.modulo y1 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0))))) y0).
Definition term90 := or (exists y0 : nat, (fun y1 : nat => (Coq.Arith.PeanoNat.Nat.Even y1) /\ (~ ((Nat.modulo y1 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)))) y0).
Definition term188 (x0 : nat) := @eq Prop ((~ (Coq.Arith.PeanoNat.Nat.Even x0)) \/ ((Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0))).
Definition term31 := @COND nat False (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term30 (x0 : nat) := @COND nat (Coq.Arith.PeanoNat.Nat.Even x0) (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term72 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term15 := (forall y0 : nat, (~ (Coq.Arith.PeanoNat.Nat.Odd y0)) = (Coq.Arith.PeanoNat.Nat.Even y0)) -> (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Odd y0) = ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0)))) -> (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even y0) = ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0))) -> False.
Definition term65 (x0 : nat -> Prop) := exists y0 : nat, ~ (x0 y0).
Definition term107 := forall y0 : nat, ((~ (Coq.Arith.PeanoNat.Nat.Odd y0)) \/ (~ (Coq.Arith.PeanoNat.Nat.Even y0))) /\ ((Coq.Arith.PeanoNat.Nat.Odd y0) \/ (Coq.Arith.PeanoNat.Nat.Even y0)).
Definition term67 (x0 : nat) := (fun y0 : nat => ((~ (Coq.Arith.PeanoNat.Nat.Even y0)) \/ ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0))) /\ ((Coq.Arith.PeanoNat.Nat.Even y0) \/ ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0))))) x0.
Definition term29 := @COND nat False (NUMERAL 0).
Definition term21 := NUMERAL (BIT1 0).
Definition term102 (x0 : nat) := (Coq.Arith.PeanoNat.Nat.Odd x0) \/ (Coq.Arith.PeanoNat.Nat.Even x0).
Definition term75 (x0 : nat -> Prop) (x1 : nat -> Prop) := (exists y0 : nat, x0 y0) \/ (exists y0 : nat, x1 y0).
Definition term161 := forall y0 : nat, ((Coq.Arith.PeanoNat.Nat.Even y0) \/ (~ ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)))) /\ ((~ (Coq.Arith.PeanoNat.Nat.Even y0)) \/ ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0))).
Definition term135 := forall y0 : nat, ((Coq.Arith.PeanoNat.Nat.Odd y0) \/ (~ ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0))))) /\ ((~ (Coq.Arith.PeanoNat.Nat.Odd y0)) \/ ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0)))).
Definition term43 := forall y0 : nat, ((~ (Coq.Arith.PeanoNat.Nat.Even y0)) \/ ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0))) /\ ((Coq.Arith.PeanoNat.Nat.Even y0) \/ ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0)))).
Definition term45 := imp (~ (forall y0 : nat, ((~ (Coq.Arith.PeanoNat.Nat.Even y0)) \/ ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0))) /\ ((Coq.Arith.PeanoNat.Nat.Even y0) \/ ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0)))))).
Definition term17 := imp (~ (forall y0 : nat, (Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (@COND nat (Coq.Arith.PeanoNat.Nat.Even y0) (NUMERAL 0) (NUMERAL (BIT1 0))))).
Definition term61 (x0 : nat) := ~ (((~ (Coq.Arith.PeanoNat.Nat.Even x0)) \/ ((Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0))) /\ ((Coq.Arith.PeanoNat.Nat.Even x0) \/ ((Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0))))).
Definition term200 (x0 : Prop) := x0 -> ~ x0.
Definition term126 := forall y0 : nat, (~ (Coq.Arith.PeanoNat.Nat.Odd y0)) \/ (~ (Coq.Arith.PeanoNat.Nat.Even y0)).
Definition term57 (x0 : nat) := or (~ ((~ (Coq.Arith.PeanoNat.Nat.Even x0)) \/ ((Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)))).
Definition term160 := fun y0 : nat => ((Coq.Arith.PeanoNat.Nat.Even y0) \/ (~ ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)))) /\ ((~ (Coq.Arith.PeanoNat.Nat.Even y0)) \/ ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0))).
Definition term97 := @eq Prop ((exists y0 : nat, (Coq.Arith.PeanoNat.Nat.Even y0) /\ (~ ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)))) \/ (exists y0 : nat, (~ (Coq.Arith.PeanoNat.Nat.Even y0)) /\ (~ ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0)))))).
Definition term96 := @eq Prop ((exists y0 : nat, (fun y1 : nat => (Coq.Arith.PeanoNat.Nat.Even y1) /\ (~ ((Nat.modulo y1 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)))) y0) \/ (exists y0 : nat, (fun y1 : nat => (~ (Coq.Arith.PeanoNat.Nat.Even y1)) /\ (~ ((Nat.modulo y1 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0))))) y0)).
