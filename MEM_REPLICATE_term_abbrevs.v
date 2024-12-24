Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term93 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : nat) := and ((~ (x0 = x1)) /\ ((~ (x0 = x1)) \/ (x2 = (NUMERAL 0)))).
Definition term86 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : nat) := ~ ((x0 = x1) /\ (~ (x2 = (NUMERAL 0)))).
Definition term110 := (~ False) -> False.
Definition term14 (a0 : Type') (x0 : nat) := (forall y0 : a0, forall y1 : a0, (@List.In a0 y0 (@repeat_with_perm_args a0 x0 y1)) = ((y0 = y1) /\ (~ (x0 = (NUMERAL 0))))) -> forall y0 : a0, forall y1 : a0, (@List.In a0 y0 (@repeat_with_perm_args a0 (S x0) y1)) = ((y0 = y1) /\ (~ ((S x0) = (NUMERAL 0)))).
Definition term63 (a0 : Type') (x0 : a0) (x1 : nat) := forall y0 : a0, (@List.In a0 x0 (@repeat_with_perm_args a0 (S x1) y0)) = ((x0 = y0) /\ (~ ((S x1) = (NUMERAL 0)))).
Definition term44 (a0 : Type') (x0 : a0) (x1 : nat) := forall y0 : a0, (@List.In a0 x0 (@repeat_with_perm_args a0 x1 y0)) = ((x0 = y0) /\ (~ (x1 = (NUMERAL 0)))).
Definition term36 (a0 : Type') (x0 : a0) := forall y0 : a0, (@List.In a0 x0 (@repeat_with_perm_args a0 (NUMERAL 0) y0)) = ((x0 = y0) /\ (~ ((NUMERAL 0) = (NUMERAL 0)))).
Definition term84 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : nat) := (~ (x0 = x1)) \/ (~ (~ (x2 = (NUMERAL 0)))).
Definition term56 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : nat) := (x0 = x1) \/ ((x0 = x1) /\ (~ (x2 = (NUMERAL 0)))).
Definition term75 (x0 : Prop) := ~ (~ x0).
Definition term98 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : a0) := (((x1 = x2) \/ ((x1 = x2) /\ (~ (x0 = (NUMERAL 0))))) /\ (~ (x1 = x2))) \/ (((~ (x1 = x2)) /\ ((~ (x1 = x2)) \/ (x0 = (NUMERAL 0)))) /\ (x1 = x2)).
Definition term102 (a0 : Type') (x0 : a0) (x1 : a0) := (fun y0 : a0 => ~ (y0 = x0)) x1.
Definition term43 (a0 : Type') (x0 : nat) (x1 : a0) := (fun y0 : a0 => forall y1 : a0, (@List.In a0 y0 (@repeat_with_perm_args a0 x0 y1)) = ((y0 = y1) /\ (~ (x0 = (NUMERAL 0))))) x1.
Definition term38 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term18 (a0 : Type') := forall y0 : nat, (forall y1 : a0, forall y2 : a0, (@List.In a0 y1 (@repeat_with_perm_args a0 y0 y2)) = ((y1 = y2) /\ (~ (y0 = (NUMERAL 0))))) -> forall y1 : a0, forall y2 : a0, (@List.In a0 y1 (@repeat_with_perm_args a0 (S y0) y2)) = ((y1 = y2) /\ (~ ((S y0) = (NUMERAL 0)))).
Definition term68 (x0 : Prop) := (~ x0) -> False.
Definition term47 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : nat) := (x0 = x1) /\ (~ (x2 = (NUMERAL 0))).
Definition term26 (a0 : Type') := ((forall y0 : a0, forall y1 : a0, (@List.In a0 y0 (@repeat_with_perm_args a0 (NUMERAL 0) y1)) = ((y0 = y1) /\ (~ ((NUMERAL 0) = (NUMERAL 0))))) /\ (forall y0 : nat, (forall y1 : a0, forall y2 : a0, (@List.In a0 y1 (@repeat_with_perm_args a0 y0 y2)) = ((y1 = y2) /\ (~ (y0 = (NUMERAL 0))))) -> forall y1 : a0, forall y2 : a0, (@List.In a0 y1 (@repeat_with_perm_args a0 (S y0) y2)) = ((y1 = y2) /\ (~ ((S y0) = (NUMERAL 0)))))) -> forall y0 : nat, forall y1 : a0, forall y2 : a0, (@List.In a0 y1 (@repeat_with_perm_args a0 y0 y2)) = ((y1 = y2) /\ (~ (y0 = (NUMERAL 0)))).
Definition term37 (a0 : Type') := forall y0 : a0, True.
Definition term89 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : nat) := (~ (x0 = x1)) /\ (~ ((x0 = x1) /\ (~ (x2 = (NUMERAL 0))))).
Definition term9 (a0 : Type') (x0 : nat) := imp ((fun y0 : nat => forall y1 : a0, forall y2 : a0, (@List.In a0 y1 (@repeat_with_perm_args a0 y0 y2)) = ((y1 = y2) /\ (~ (y0 = (NUMERAL 0))))) x0).
Definition term66 (a0 : Type') (x0 : nat) := fun y0 : a0 => forall y1 : a0, ((y0 = y1) \/ ((y0 = y1) /\ (~ (x0 = (NUMERAL 0))))) = (y0 = y1).
Definition term108 (x0 : Prop) := (~ x0) -> x0.
Definition term1 (a0 : Type') := (((fun y0 : nat => forall y1 : a0, forall y2 : a0, (@List.In a0 y1 (@repeat_with_perm_args a0 y0 y2)) = ((y1 = y2) /\ (~ (y0 = (NUMERAL 0))))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : a0, forall y3 : a0, (@List.In a0 y2 (@repeat_with_perm_args a0 y1 y3)) = ((y2 = y3) /\ (~ (y1 = (NUMERAL 0))))) y0) -> (fun y1 : nat => forall y2 : a0, forall y3 : a0, (@List.In a0 y2 (@repeat_with_perm_args a0 y1 y3)) = ((y2 = y3) /\ (~ (y1 = (NUMERAL 0))))) (S y0))) -> forall y0 : nat, (fun y1 : nat => forall y2 : a0, forall y3 : a0, (@List.In a0 y2 (@repeat_with_perm_args a0 y1 y3)) = ((y2 = y3) /\ (~ (y1 = (NUMERAL 0))))) y0.
Definition term62 (a0 : Type') (x0 : nat) (x1 : a0) := fun y0 : a0 => ((x1 = y0) \/ ((x1 = y0) /\ (~ (x0 = (NUMERAL 0))))) = (x1 = y0).
Definition term77 (a0 : Type') := fun y0 : nat => forall y1 : a0, forall y2 : a0, ((y1 = y2) \/ ((y1 = y2) /\ (~ (y0 = (NUMERAL 0))))) = (y1 = y2).
Definition term2 (a0 : Type') := fun y0 : nat => forall y1 : a0, forall y2 : a0, (@List.In a0 y1 (@repeat_with_perm_args a0 y0 y2)) = ((y1 = y2) /\ (~ (y0 = (NUMERAL 0)))).
Definition term7 (a0 : Type') (x0 : nat) := (fun y0 : nat => forall y1 : a0, forall y2 : a0, (@List.In a0 y1 (@repeat_with_perm_args a0 y0 y2)) = ((y1 = y2) /\ (~ (y0 = (NUMERAL 0))))) x0.
Definition term0 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term83 (a0 : Type') (x0 : a0) (x1 : a0) := or (~ (x0 = x1)).
Definition term65 (a0 : Type') (x0 : nat) := fun y0 : a0 => forall y1 : a0, (@List.In a0 y0 (@repeat_with_perm_args a0 (S x0) y1)) = ((y0 = y1) /\ (~ ((S x0) = (NUMERAL 0)))).
Definition term39 (a0 : Type') := fun y0 : a0 => forall y1 : a0, (@List.In a0 y0 (@repeat_with_perm_args a0 (NUMERAL 0) y1)) = ((y0 = y1) /\ (~ ((NUMERAL 0) = (NUMERAL 0)))).
Definition term21 (a0 : Type') := imp (((fun y0 : nat => forall y1 : a0, forall y2 : a0, (@List.In a0 y1 (@repeat_with_perm_args a0 y0 y2)) = ((y1 = y2) /\ (~ (y0 = (NUMERAL 0))))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : a0, forall y3 : a0, (@List.In a0 y2 (@repeat_with_perm_args a0 y1 y3)) = ((y2 = y3) /\ (~ (y1 = (NUMERAL 0))))) y0) -> (fun y1 : nat => forall y2 : a0, forall y3 : a0, (@List.In a0 y2 (@repeat_with_perm_args a0 y1 y3)) = ((y2 = y3) /\ (~ (y1 = (NUMERAL 0))))) (S y0))).
Definition term97 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : a0) := (((x1 = x2) \/ ((x1 = x2) /\ (~ (x0 = (NUMERAL 0))))) /\ (~ (x1 = x2))) \/ ((~ ((x1 = x2) \/ ((x1 = x2) /\ (~ (x0 = (NUMERAL 0)))))) /\ (x1 = x2)).
Definition term30 := ~ ((NUMERAL 0) = (NUMERAL 0)).
Definition term17 (a0 : Type') := forall y0 : nat, ((fun y1 : nat => forall y2 : a0, forall y3 : a0, (@List.In a0 y2 (@repeat_with_perm_args a0 y1 y3)) = ((y2 = y3) /\ (~ (y1 = (NUMERAL 0))))) y0) -> (fun y1 : nat => forall y2 : a0, forall y3 : a0, (@List.In a0 y2 (@repeat_with_perm_args a0 y1 y3)) = ((y2 = y3) /\ (~ (y1 = (NUMERAL 0))))) (S y0).
Definition term87 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term48 (a0 : Type') (x0 : nat) (x1 : a0) := @repeat_with_perm_args a0 (S x0) x1.
Definition term104 (a0 : Type') (x0 : a0) := ~ (x0 = x0).
Definition term60 (a0 : Type') (x0 : a0) (x1 : a0) := (x0 = x1) /\ True.
Definition term5 (a0 : Type') := and ((fun y0 : nat => forall y1 : a0, forall y2 : a0, (@List.In a0 y1 (@repeat_with_perm_args a0 y0 y2)) = ((y1 = y2) /\ (~ (y0 = (NUMERAL 0))))) (NUMERAL 0)).
Definition term11 (a0 : Type') (x0 : nat) := (fun y0 : nat => forall y1 : a0, forall y2 : a0, (@List.In a0 y1 (@repeat_with_perm_args a0 y0 y2)) = ((y1 = y2) /\ (~ (y0 = (NUMERAL 0))))) (S x0).
Definition term3 (a0 : Type') := (fun y0 : nat => forall y1 : a0, forall y2 : a0, (@List.In a0 y1 (@repeat_with_perm_args a0 y0 y2)) = ((y1 = y2) /\ (~ (y0 = (NUMERAL 0))))) (NUMERAL 0).
Definition term71 (a0 : Type') (x0 : nat) := ((~ (forall y0 : a0, forall y1 : a0, ((y0 = y1) \/ ((y0 = y1) /\ (~ (x0 = (NUMERAL 0))))) = (y0 = y1))) -> False) -> (~ (forall y0 : a0, forall y1 : a0, ((y0 = y1) \/ ((y0 = y1) /\ (~ (x0 = (NUMERAL 0))))) = (y0 = y1))) -> False.
Definition term22 (a0 : Type') := imp ((forall y0 : a0, forall y1 : a0, (@List.In a0 y0 (@repeat_with_perm_args a0 (NUMERAL 0) y1)) = ((y0 = y1) /\ (~ ((NUMERAL 0) = (NUMERAL 0))))) /\ (forall y0 : nat, (forall y1 : a0, forall y2 : a0, (@List.In a0 y1 (@repeat_with_perm_args a0 y0 y2)) = ((y1 = y2) /\ (~ (y0 = (NUMERAL 0))))) -> forall y1 : a0, forall y2 : a0, (@List.In a0 y1 (@repeat_with_perm_args a0 (S y0) y2)) = ((y1 = y2) /\ (~ ((S y0) = (NUMERAL 0)))))).
Definition term91 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : nat) := ~ ((x0 = x1) \/ ((x0 = x1) /\ (~ (x2 = (NUMERAL 0))))).
Definition term59 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : nat) := (x0 = x1) /\ (~ ((S x2) = (NUMERAL 0))).
Definition term79 (a0 : Type') := forall y0 : nat, forall y1 : a0, forall y2 : a0, ((y1 = y2) \/ ((y1 = y2) /\ (~ (y0 = (NUMERAL 0))))) = (y1 = y2).
Definition term25 (a0 : Type') := forall y0 : nat, forall y1 : a0, forall y2 : a0, (@List.In a0 y1 (@repeat_with_perm_args a0 y0 y2)) = ((y1 = y2) /\ (~ (y0 = (NUMERAL 0)))).
Definition term35 (a0 : Type') := fun y0 : a0 => True.
Definition term88 (a0 : Type') (x0 : a0) (x1 : a0) := and (~ (x0 = x1)).
Definition term90 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : nat) := (~ (x0 = x1)) /\ ((~ (x0 = x1)) \/ (x2 = (NUMERAL 0))).
Definition term105 (a0 : Type') (x0 : a0) (x1 : a0) := @eq Prop ((fun y0 : a0 => ~ (y0 = x0)) x1).
Definition term76 (a0 : Type') := fun y0 : nat => (~ (forall y1 : a0, forall y2 : a0, ((y1 = y2) \/ ((y1 = y2) /\ (~ (y0 = (NUMERAL 0))))) = (y1 = y2))) -> False.
Definition term111 (a0 : Type') (x0 : nat) := (fun y0 : nat => (~ (forall y1 : a0, forall y2 : a0, ((y1 = y2) \/ ((y1 = y2) /\ (~ (y0 = (NUMERAL 0))))) = (y1 = y2))) -> False) x0.
Definition term10 (a0 : Type') (x0 : nat) := imp (forall y0 : a0, forall y1 : a0, (@List.In a0 y0 (@repeat_with_perm_args a0 x0 y1)) = ((y0 = y1) /\ (~ (x0 = (NUMERAL 0))))).
Definition term58 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : nat) := @eq Prop ((x0 = x1) \/ ((x0 = x1) /\ (~ (x2 = (NUMERAL 0))))).
Definition term27 (a0 : Type') (x0 : a0) := @repeat_with_perm_args a0 (NUMERAL 0) x0.
Definition term51 (a0 : Type') (x0 : a0) (x1 : nat) (x2 : a0) := @List.In a0 x0 (@cons a0 x2 (@repeat_with_perm_args a0 x1 x2)).
Definition term53 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) := (x1 = x0) \/ (@List.In a0 x1 x2).
Definition term61 (a0 : Type') (x0 : a0) (x1 : nat) := fun y0 : a0 => (@List.In a0 x0 (@repeat_with_perm_args a0 (S x1) y0)) = ((x0 = y0) /\ (~ ((S x1) = (NUMERAL 0)))).
Definition term34 (a0 : Type') (x0 : a0) := fun y0 : a0 => (@List.In a0 x0 (@repeat_with_perm_args a0 (NUMERAL 0) y0)) = ((x0 = y0) /\ (~ ((NUMERAL 0) = (NUMERAL 0)))).
Definition term94 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : a0) := (~ ((x1 = x2) \/ ((x1 = x2) /\ (~ (x0 = (NUMERAL 0)))))) /\ (x1 = x2).
Definition term74 (a0 : Type') (x0 : nat) := ~ (~ (forall y0 : a0, forall y1 : a0, ((y0 = y1) \/ ((y0 = y1) /\ (~ (x0 = (NUMERAL 0))))) = (y0 = y1))).
Definition term41 (x0 : nat) := ~ ((S x0) = (NUMERAL 0)).
Definition term69 (a0 : Type') (x0 : nat) := (~ (forall y0 : a0, forall y1 : a0, ((y0 = y1) \/ ((y0 = y1) /\ (~ (x0 = (NUMERAL 0))))) = (y0 = y1))) -> False.
Definition term6 (a0 : Type') := and (forall y0 : a0, forall y1 : a0, (@List.In a0 y0 (@repeat_with_perm_args a0 (NUMERAL 0) y1)) = ((y0 = y1) /\ (~ ((NUMERAL 0) = (NUMERAL 0))))).
Definition term81 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : a0) := ~ (((x1 = x2) \/ ((x1 = x2) /\ (~ (x0 = (NUMERAL 0))))) = (x1 = x2)).
Definition term78 (a0 : Type') := forall y0 : nat, (~ (forall y1 : a0, forall y2 : a0, ((y1 = y2) \/ ((y1 = y2) /\ (~ (y0 = (NUMERAL 0))))) = (y1 = y2))) -> False.
Definition term31 (a0 : Type') (x0 : a0) (x1 : a0) := and (x0 = x1).
Definition term72 (a0 : Type') (x0 : nat) := (((~ (forall y0 : a0, forall y1 : a0, ((y0 = y1) \/ ((y0 = y1) /\ (~ (x0 = (NUMERAL 0))))) = (y0 = y1))) -> False) -> (~ (forall y0 : a0, forall y1 : a0, ((y0 = y1) \/ ((y0 = y1) /\ (~ (x0 = (NUMERAL 0))))) = (y0 = y1))) -> False) -> (~ (forall y0 : a0, forall y1 : a0, ((y0 = y1) \/ ((y0 = y1) /\ (~ (x0 = (NUMERAL 0))))) = (y0 = y1))) -> False.
Definition term15 (a0 : Type') := fun y0 : nat => ((fun y1 : nat => forall y2 : a0, forall y3 : a0, (@List.In a0 y2 (@repeat_with_perm_args a0 y1 y3)) = ((y2 = y3) /\ (~ (y1 = (NUMERAL 0))))) y0) -> (fun y1 : nat => forall y2 : a0, forall y3 : a0, (@List.In a0 y2 (@repeat_with_perm_args a0 y1 y3)) = ((y2 = y3) /\ (~ (y1 = (NUMERAL 0))))) (S y0).
Definition term106 (a0 : Type') (x0 : a0) (x1 : a0) := @eq Prop (~ (x0 = x1)).
Definition term100 (a0 : Type') (x0 : a0) (x1 : a0) := ~ (x0 = x1).
Definition term55 (a0 : Type') (x0 : a0) (x1 : a0) := or (x0 = x1).
Definition term20 (a0 : Type') := (forall y0 : a0, forall y1 : a0, (@List.In a0 y0 (@repeat_with_perm_args a0 (NUMERAL 0) y1)) = ((y0 = y1) /\ (~ ((NUMERAL 0) = (NUMERAL 0))))) /\ (forall y0 : nat, (forall y1 : a0, forall y2 : a0, (@List.In a0 y1 (@repeat_with_perm_args a0 y0 y2)) = ((y1 = y2) /\ (~ (y0 = (NUMERAL 0))))) -> forall y1 : a0, forall y2 : a0, (@List.In a0 y1 (@repeat_with_perm_args a0 (S y0) y2)) = ((y1 = y2) /\ (~ ((S y0) = (NUMERAL 0))))).
Definition term52 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) := @List.In a0 x0 (@cons a0 x1 x2).
Definition term49 (a0 : Type') (x0 : nat) (x1 : a0) := @cons a0 x1 (@repeat_with_perm_args a0 x0 x1).
Definition term16 (a0 : Type') := fun y0 : nat => (forall y1 : a0, forall y2 : a0, (@List.In a0 y1 (@repeat_with_perm_args a0 y0 y2)) = ((y1 = y2) /\ (~ (y0 = (NUMERAL 0))))) -> forall y1 : a0, forall y2 : a0, (@List.In a0 y1 (@repeat_with_perm_args a0 (S y0) y2)) = ((y1 = y2) /\ (~ ((S y0) = (NUMERAL 0)))).
Definition term99 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : a0) := ((x1 = x2) \/ ((x1 = x2) /\ (~ (x0 = (NUMERAL 0))))) /\ (~ (x1 = x2)).
Definition term23 (a0 : Type') := fun y0 : nat => (fun y1 : nat => forall y2 : a0, forall y3 : a0, (@List.In a0 y2 (@repeat_with_perm_args a0 y1 y3)) = ((y2 = y3) /\ (~ (y1 = (NUMERAL 0))))) y0.
Definition term40 (x0 : nat) := (fun y0 : nat => ~ ((S y0) = (NUMERAL 0))) x0.
Definition term46 (a0 : Type') (x0 : a0) (x1 : nat) (x2 : a0) := @List.In a0 x0 (@repeat_with_perm_args a0 x1 x2).
Definition term19 (a0 : Type') := ((fun y0 : nat => forall y1 : a0, forall y2 : a0, (@List.In a0 y1 (@repeat_with_perm_args a0 y0 y2)) = ((y1 = y2) /\ (~ (y0 = (NUMERAL 0))))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : a0, forall y3 : a0, (@List.In a0 y2 (@repeat_with_perm_args a0 y1 y3)) = ((y2 = y3) /\ (~ (y1 = (NUMERAL 0))))) y0) -> (fun y1 : nat => forall y2 : a0, forall y3 : a0, (@List.In a0 y2 (@repeat_with_perm_args a0 y1 y3)) = ((y2 = y3) /\ (~ (y1 = (NUMERAL 0))))) (S y0)).
Definition term92 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : nat) := and (~ ((x0 = x1) \/ ((x0 = x1) /\ (~ (x2 = (NUMERAL 0)))))).
Definition term67 (a0 : Type') (x0 : nat) := forall y0 : a0, forall y1 : a0, ((y0 = y1) \/ ((y0 = y1) /\ (~ (x0 = (NUMERAL 0))))) = (y0 = y1).
Definition term12 (a0 : Type') (x0 : nat) := forall y0 : a0, forall y1 : a0, (@List.In a0 y0 (@repeat_with_perm_args a0 (S x0) y1)) = ((y0 = y1) /\ (~ ((S x0) = (NUMERAL 0)))).
Definition term8 (a0 : Type') (x0 : nat) := forall y0 : a0, forall y1 : a0, (@List.In a0 y0 (@repeat_with_perm_args a0 x0 y1)) = ((y0 = y1) /\ (~ (x0 = (NUMERAL 0)))).
Definition term4 (a0 : Type') := forall y0 : a0, forall y1 : a0, (@List.In a0 y0 (@repeat_with_perm_args a0 (NUMERAL 0) y1)) = ((y0 = y1) /\ (~ ((NUMERAL 0) = (NUMERAL 0)))).
Definition term107 (a0 : Type') (x0 : a0) := (~ (x0 = x0)) -> x0 = x0.
Definition term64 (a0 : Type') (x0 : nat) (x1 : a0) := forall y0 : a0, ((x1 = y0) \/ ((x1 = y0) /\ (~ (x0 = (NUMERAL 0))))) = (x1 = y0).
Definition term42 (x0 : nat) := (~ ((S x0) = (NUMERAL 0))) -> ((S x0) = (NUMERAL 0)) = False.
Definition term101 (a0 : Type') (x0 : a0) := fun y0 : a0 => ~ (y0 = x0).
Definition term95 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : a0) := ((~ (x1 = x2)) /\ ((~ (x1 = x2)) \/ (x0 = (NUMERAL 0)))) /\ (x1 = x2).
Definition term70 (a0 : Type') (x0 : nat) := ~ (forall y0 : a0, forall y1 : a0, ((y0 = y1) \/ ((y0 = y1) /\ (~ (x0 = (NUMERAL 0))))) = (y0 = y1)).
Definition term33 (a0 : Type') (x0 : a0) (x1 : a0) := (x0 = x1) /\ False.
Definition term28 (a0 : Type') (x0 : a0) (x1 : a0) := @List.In a0 x0 (@repeat_with_perm_args a0 (NUMERAL 0) x1).
Definition term80 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : a0) := (~ (((x1 = x2) \/ ((x1 = x2) /\ (~ (x0 = (NUMERAL 0))))) = (x1 = x2))) -> False.
Definition term73 (a0 : Type') (x0 : nat) := (((~ (forall y0 : a0, forall y1 : a0, ((y0 = y1) \/ ((y0 = y1) /\ (~ (x0 = (NUMERAL 0))))) = (y0 = y1))) -> False) -> (~ (forall y0 : a0, forall y1 : a0, ((y0 = y1) \/ ((y0 = y1) /\ (~ (x0 = (NUMERAL 0))))) = (y0 = y1))) -> False) -> ((~ (forall y0 : a0, forall y1 : a0, ((y0 = y1) \/ ((y0 = y1) /\ (~ (x0 = (NUMERAL 0))))) = (y0 = y1))) -> False) -> (~ (forall y0 : a0, forall y1 : a0, ((y0 = y1) \/ ((y0 = y1) /\ (~ (x0 = (NUMERAL 0))))) = (y0 = y1))) -> False.
Definition term82 (x0 : nat) := ~ (~ (x0 = (NUMERAL 0))).
Definition term50 (a0 : Type') (x0 : a0) (x1 : nat) (x2 : a0) := @List.In a0 x0 (@repeat_with_perm_args a0 (S x1) x2).
Definition term45 (a0 : Type') (x0 : a0) (x1 : nat) (x2 : a0) := (fun y0 : a0 => (@List.In a0 x0 (@repeat_with_perm_args a0 x1 y0)) = ((x0 = y0) /\ (~ (x1 = (NUMERAL 0))))) x2.
Definition term13 (a0 : Type') (x0 : nat) := ((fun y0 : nat => forall y1 : a0, forall y2 : a0, (@List.In a0 y1 (@repeat_with_perm_args a0 y0 y2)) = ((y1 = y2) /\ (~ (y0 = (NUMERAL 0))))) x0) -> (fun y0 : nat => forall y1 : a0, forall y2 : a0, (@List.In a0 y1 (@repeat_with_perm_args a0 y0 y2)) = ((y1 = y2) /\ (~ (y0 = (NUMERAL 0))))) (S x0).
Definition term54 (a0 : Type') (x0 : a0) (x1 : nat) (x2 : a0) := (x0 = x2) \/ (@List.In a0 x0 (@repeat_with_perm_args a0 x1 x2)).
Definition term96 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : a0) := or (((x1 = x2) \/ ((x1 = x2) /\ (~ (x0 = (NUMERAL 0))))) /\ (~ (x1 = x2))).
Definition term85 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : nat) := (~ (x0 = x1)) \/ (x2 = (NUMERAL 0)).
Definition term24 (a0 : Type') := forall y0 : nat, (fun y1 : nat => forall y2 : a0, forall y3 : a0, (@List.In a0 y2 (@repeat_with_perm_args a0 y1 y3)) = ((y2 = y3) /\ (~ (y1 = (NUMERAL 0))))) y0.
Definition term57 (a0 : Type') (x0 : a0) (x1 : nat) (x2 : a0) := @eq Prop (@List.In a0 x0 (@repeat_with_perm_args a0 (S x1) x2)).
Definition term32 (a0 : Type') (x0 : a0) (x1 : a0) := (x0 = x1) /\ (~ ((NUMERAL 0) = (NUMERAL 0))).
Definition term109 (a0 : Type') (x0 : a0) := (x0 = x0) -> False.
Definition term29 (a0 : Type') (x0 : a0) (x1 : a0) := @eq Prop (@List.In a0 x0 (@repeat_with_perm_args a0 (NUMERAL 0) x1)).
Definition term103 (a0 : Type') (x0 : a0) := (fun y0 : a0 => ~ (y0 = x0)) x0.
