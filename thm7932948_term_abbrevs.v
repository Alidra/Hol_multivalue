Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term13 (a0 : Type') (x0 : type6 a0) := @IN (tybit1 a0) (@mktybit1 a0 x0) (@UNIV (tybit1 a0)).
Definition term49 (a0 : Type') (x0 : type1351 a0) := ~ (all x0).
Definition term120 := (~ False) -> False.
Definition term27 (a0 : Type') := (~ (forall y0 : tybit1 a0, exists y1 : type6 a0, (@mktybit1 a0 y1) = y0)) -> (forall y0 : tybit1 a0, exists y1 : type6 a0, y0 = (@mktybit1 a0 y1)) -> False.
Definition term61 (a0 : Type') := forall y0 : tybit1 a0, exists y1 : type6 a0, (fun y2 : tybit1 a0 => fun y3 : type6 a0 => y2 = (@mktybit1 a0 y3)) y0 y1.
Definition term59 (a0 : Type') (x0 : type1349 a0) := forall y0 : tybit1 a0, exists y1 : type6 a0, x0 y0 y1.
Definition term26 (a0 : Type') := forall y0 : tybit1 a0, exists y1 : type6 a0, y0 = (@mktybit1 a0 y1).
Definition term10 (a0 : Type') := forall y0 : tybit1 a0, exists y1 : type6 a0, (@mktybit1 a0 y1) = y0.
Definition term106 (x0 : Prop) := ~ (~ x0).
Definition term114 (a0 : Type') (x0 : type1348 a0) (x1 : tybit1 a0) := (x1 = (@mktybit1 a0 (x0 x1))) /\ (x1 = x1).
Definition term73 (a0 : Type') (x0 : type1348 a0) (x1 : tybit1 a0) := (fun y0 : type6 a0 => x1 = (@mktybit1 a0 y0)) (x0 x1).
Definition term20 (a0 : Type') (x0 : Prop) := forall y0 : type6 a0, x0.
Definition term105 (a0 : Type') (x0 : tybit1 a0) (x1 : tybit1 a0) (x2 : tybit1 a0) := (~ (~ (x1 = x0))) /\ (~ (~ (x1 = x2))).
Definition term19 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term77 (a0 : Type') (x0 : type1348 a0) := forall y0 : tybit1 a0, (fun y1 : tybit1 a0 => fun y2 : type6 a0 => y1 = (@mktybit1 a0 y2)) y0 (x0 y0).
Definition term23 (x0 : Prop) := (~ x0) -> False.
Definition term111 (a0 : Type') (x0 : tybit1 a0) (x1 : tybit1 a0) (x2 : tybit1 a0) := imp (~ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term86 (a0 : Type') (x0 : type1348 a0) (x1 : tybit1 a0) := ~ (x1 = (@mktybit1 a0 (x0 x1))).
Definition term1 (a0 : Type') (x0 : type40 a0) (x1 : type42 a0) (x2 : type1351 a0) := ((forall y0 : tybit1 a0, (@IN (tybit1 a0) y0 x2) -> exists y1 : type6 a0, (x0 y1) = y0) /\ (forall y0 : type6 a0, (@IN (tybit1 a0) (x0 y0) x2) = (@IN (finite_sum (finite_sum a0 a0) unit) y0 x1))) -> (@IMAGE (finite_sum (finite_sum a0 a0) unit) (tybit1 a0) x0 x1) = x2.
Definition term0 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) (x1 : a1 -> Prop) (x2 : a0 -> Prop) := ((forall y0 : a0, (@IN a0 y0 x2) -> exists y1 : a1, (x0 y1) = y0) /\ (forall y0 : a1, (@IN a0 (x0 y0) x2) = (@IN a1 y0 x1))) -> (@IMAGE a1 a0 x0 x1) = x2.
Definition term4 (a0 : Type') (x0 : tybit1 a0) := exists y0 : type6 a0, (@mktybit1 a0 y0) = x0.
Definition term63 (a0 : Type') := fun y0 : tybit1 a0 => fun y1 : type6 a0 => y0 = (@mktybit1 a0 y1).
Definition term78 (a0 : Type') (x0 : type1348 a0) := forall y0 : tybit1 a0, y0 = (@mktybit1 a0 (x0 y0)).
Definition term99 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term87 (x0 : Prop) := (~ x0) -> x0.
Definition term54 (a0 : Type') := fun y0 : tybit1 a0 => ~ ((fun y1 : tybit1 a0 => exists y2 : type6 a0, (@mktybit1 a0 y2) = y1) y0).
Definition term101 (a0 : Type') (x0 : tybit1 a0) (x1 : tybit1 a0) (x2 : tybit1 a0) := (~ (x1 = x0)) \/ (~ (x1 = x2)).
Definition term103 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term57 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := forall y0 : a0, exists y1 : a1, x0 y0 y1.
Definition term3 (a0 : Type') (x0 : tybit1 a0) := imp (@IN (tybit1 a0) x0 (@UNIV (tybit1 a0))).
Definition term97 (a0 : Type') (x0 : tybit1 a0) (x1 : tybit1 a0) (x2 : tybit1 a0) := @eq Prop ((~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2))).
Definition term17 (a0 : Type') := forall y0 : type6 a0, (@IN (tybit1 a0) (@mktybit1 a0 y0) (@UNIV (tybit1 a0))) = (@IN (finite_sum (finite_sum a0 a0) unit) y0 (@UNIV (finite_sum (finite_sum a0 a0) unit))).
Definition term98 (a0 : Type') (x0 : tybit1 a0) (x1 : tybit1 a0) (x2 : tybit1 a0) := @eq Prop ((x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term81 (a0 : Type') := exists y0 : type1348 a0, forall y1 : tybit1 a0, y1 = (@mktybit1 a0 (y0 y1)).
Definition term62 (a0 : Type') := exists y0 : type1348 a0, forall y1 : tybit1 a0, (fun y2 : tybit1 a0 => fun y3 : type6 a0 => y2 = (@mktybit1 a0 y3)) y1 (y0 y1).
Definition term60 (a0 : Type') (x0 : type1349 a0) := exists y0 : type1348 a0, forall y1 : tybit1 a0, x0 y1 (y0 y1).
Definition term71 (a0 : Type') := @eq Prop (forall y0 : tybit1 a0, exists y1 : type6 a0, y0 = (@mktybit1 a0 y1)).
Definition term70 (a0 : Type') := @eq Prop (forall y0 : tybit1 a0, exists y1 : type6 a0, (fun y2 : tybit1 a0 => fun y3 : type6 a0 => y2 = (@mktybit1 a0 y3)) y0 y1).
Definition term116 (a0 : Type') (x0 : type1348 a0) (x1 : tybit1 a0) := (~ ((@mktybit1 a0 (x0 x1)) = x1)) -> (@mktybit1 a0 (x0 x1)) = x1.
Definition term95 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term40 (a0 : Type') (x0 : type42 a0) := forall y0 : type6 a0, ~ (x0 y0).
Definition term43 (a0 : Type') (x0 : tybit1 a0) (x1 : type6 a0) := (fun y0 : type6 a0 => (@mktybit1 a0 y0) = x0) x1.
Definition term96 (a0 : Type') (x0 : tybit1 a0) (x1 : tybit1 a0) (x2 : tybit1 a0) := (x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term85 (a0 : Type') (x0 : type1348 a0) (x1 : tybit1 a0) := (~ (x1 = (@mktybit1 a0 (x0 x1)))) -> x1 = (@mktybit1 a0 (x0 x1)).
Definition term2 (a0 : Type') := ((forall y0 : tybit1 a0, (@IN (tybit1 a0) y0 (@UNIV (tybit1 a0))) -> exists y1 : type6 a0, (@mktybit1 a0 y1) = y0) /\ (forall y0 : type6 a0, (@IN (tybit1 a0) (@mktybit1 a0 y0) (@UNIV (tybit1 a0))) = (@IN (finite_sum (finite_sum a0 a0) unit) y0 (@UNIV (finite_sum (finite_sum a0 a0) unit))))) -> (@IMAGE (finite_sum (finite_sum a0 a0) unit) (tybit1 a0) (@mktybit1 a0) (@UNIV (finite_sum (finite_sum a0 a0) unit))) = (@UNIV (tybit1 a0)).
Definition term16 (a0 : Type') := fun y0 : type6 a0 => True.
Definition term74 (a0 : Type') (x0 : type1348 a0) (x1 : tybit1 a0) := @mktybit1 a0 (x0 x1).
Definition term84 (a0 : Type') (x0 : tybit1 a0) (x1 : tybit1 a0) (x2 : tybit1 a0) := (~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2)).
Definition term31 (a0 : Type') := (forall y0 : tybit1 a0, exists y1 : type6 a0, y0 = (@mktybit1 a0 y1)) -> False.
Definition term76 (a0 : Type') (x0 : type1348 a0) := fun y0 : tybit1 a0 => y0 = (@mktybit1 a0 (x0 y0)).
Definition term47 (a0 : Type') (x0 : tybit1 a0) := fun y0 : type6 a0 => ~ ((@mktybit1 a0 y0) = x0).
Definition term8 (a0 : Type') := fun y0 : tybit1 a0 => exists y1 : type6 a0, (@mktybit1 a0 y1) = y0.
Definition term56 (a0 : Type') := exists y0 : tybit1 a0, forall y1 : type6 a0, ~ ((@mktybit1 a0 y1) = y0).
Definition term29 (a0 : Type') := (((~ (forall y0 : tybit1 a0, exists y1 : type6 a0, (@mktybit1 a0 y1) = y0)) -> (forall y0 : tybit1 a0, exists y1 : type6 a0, y0 = (@mktybit1 a0 y1)) -> False) -> (~ (forall y0 : tybit1 a0, exists y1 : type6 a0, (@mktybit1 a0 y1) = y0)) -> (forall y0 : tybit1 a0, exists y1 : type6 a0, y0 = (@mktybit1 a0 y1)) -> False) -> (~ (forall y0 : tybit1 a0, exists y1 : type6 a0, (@mktybit1 a0 y1) = y0)) -> (forall y0 : tybit1 a0, exists y1 : type6 a0, y0 = (@mktybit1 a0 y1)) -> False.
Definition term15 (a0 : Type') := fun y0 : type6 a0 => (@IN (tybit1 a0) (@mktybit1 a0 y0) (@UNIV (tybit1 a0))) = (@IN (finite_sum (finite_sum a0 a0) unit) y0 (@UNIV (finite_sum (finite_sum a0 a0) unit))).
Definition term48 (a0 : Type') (x0 : tybit1 a0) := forall y0 : type6 a0, ~ ((@mktybit1 a0 y0) = x0).
Definition term102 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term72 (a0 : Type') (x0 : type1348 a0) (x1 : tybit1 a0) := (fun y0 : tybit1 a0 => fun y1 : type6 a0 => y0 = (@mktybit1 a0 y1)) x1 (x0 x1).
Definition term55 (a0 : Type') := fun y0 : tybit1 a0 => forall y1 : type6 a0, ~ ((@mktybit1 a0 y1) = y0).
Definition term92 (a0 : Type') (x0 : tybit1 a0) (x1 : tybit1 a0) := ~ (x0 = x1).
Definition term39 (a0 : Type') (x0 : type42 a0) := ~ (ex x0).
Definition term46 (a0 : Type') (x0 : tybit1 a0) := fun y0 : type6 a0 => ~ ((fun y1 : type6 a0 => (@mktybit1 a0 y1) = x0) y0).
Definition term36 (a0 : Type') (x0 : tybit1 a0) := exists y0 : type6 a0, x0 = (@mktybit1 a0 y0).
Definition term83 (a0 : Type') (x0 : tybit1 a0) (x1 : type6 a0) := (fun y0 : type6 a0 => ~ ((@mktybit1 a0 y0) = x0)) x1.
Definition term52 (a0 : Type') (x0 : tybit1 a0) := (fun y0 : tybit1 a0 => exists y1 : type6 a0, (@mktybit1 a0 y1) = y0) x0.
Definition term24 (a0 : Type') := (~ (forall y0 : tybit1 a0, exists y1 : type6 a0, (@mktybit1 a0 y1) = y0)) -> False.
Definition term11 (a0 : Type') := and (forall y0 : tybit1 a0, (@IN (tybit1 a0) y0 (@UNIV (tybit1 a0))) -> exists y1 : type6 a0, (@mktybit1 a0 y1) = y0).
Definition term94 (a0 : Type') (x0 : tybit1 a0) (x1 : tybit1 a0) (x2 : tybit1 a0) := (~ (x1 = x0)) \/ ((x0 = x2) \/ (~ (x1 = x2))).
Definition term12 (a0 : Type') := and (forall y0 : tybit1 a0, exists y1 : type6 a0, (@mktybit1 a0 y1) = y0).
Definition term51 (a0 : Type') := exists y0 : tybit1 a0, ~ ((fun y1 : tybit1 a0 => exists y2 : type6 a0, (@mktybit1 a0 y2) = y1) y0).
Definition term108 (a0 : Type') (x0 : tybit1 a0) (x1 : tybit1 a0) := and (~ (~ (x0 = x1))).
Definition term50 (a0 : Type') (x0 : type1351 a0) := exists y0 : tybit1 a0, ~ (x0 y0).
Definition term42 (a0 : Type') (x0 : tybit1 a0) := forall y0 : type6 a0, ~ ((fun y1 : type6 a0 => (@mktybit1 a0 y1) = x0) y0).
Definition term45 (a0 : Type') (x0 : type6 a0) (x1 : tybit1 a0) := ~ ((@mktybit1 a0 x0) = x1).
Definition term117 (a0 : Type') (x0 : type1348 a0) (x1 : tybit1 a0) := ~ ((@mktybit1 a0 (x0 x1)) = x1).
Definition term90 (a0 : Type') (x0 : tybit1 a0) (x1 : tybit1 a0) (x2 : tybit1 a0) := (~ (x0 = x2)) \/ (x1 = x2).
Definition term82 (a0 : Type') (x0 : type1348 a0) (x1 : tybit1 a0) := (fun y0 : tybit1 a0 => y0 = (@mktybit1 a0 (x0 y0))) x1.
Definition term91 (a0 : Type') (x0 : tybit1 a0) (x1 : tybit1 a0) (x2 : tybit1 a0) := (x0 = x2) \/ (~ (x1 = x2)).
Definition term75 (a0 : Type') (x0 : type1348 a0) := fun y0 : tybit1 a0 => (fun y1 : tybit1 a0 => fun y2 : type6 a0 => y1 = (@mktybit1 a0 y2)) y0 (x0 y0).
Definition term100 (a0 : Type') (x0 : tybit1 a0) (x1 : tybit1 a0) (x2 : tybit1 a0) := (~ ((~ (x0 = x1)) \/ (~ (x0 = x2)))) -> x1 = x2.
Definition term79 (a0 : Type') := fun y0 : type1348 a0 => forall y1 : tybit1 a0, (fun y2 : tybit1 a0 => fun y3 : type6 a0 => y2 = (@mktybit1 a0 y3)) y1 (y0 y1).
Definition term88 (a0 : Type') (x0 : tybit1 a0) := (~ (x0 = x0)) -> x0 = x0.
Definition term67 (a0 : Type') (x0 : tybit1 a0) := fun y0 : type6 a0 => (fun y1 : tybit1 a0 => fun y2 : type6 a0 => y1 = (@mktybit1 a0 y2)) x0 y0.
Definition term118 (a0 : Type') (x0 : type6 a0) (x1 : tybit1 a0) := ((@mktybit1 a0 x0) = x1) -> False.
Definition term35 (a0 : Type') (x0 : tybit1 a0) := fun y0 : type6 a0 => x0 = (@mktybit1 a0 y0).
Definition term5 (a0 : Type') (x0 : tybit1 a0) := (@IN (tybit1 a0) x0 (@UNIV (tybit1 a0))) -> exists y0 : type6 a0, (@mktybit1 a0 y0) = x0.
Definition term22 (a0 : Type') := (forall y0 : tybit1 a0, exists y1 : type6 a0, (@mktybit1 a0 y1) = y0) /\ True.
Definition term113 (a0 : Type') (x0 : tybit1 a0) (x1 : tybit1 a0) (x2 : tybit1 a0) := ((x0 = x1) /\ (x0 = x2)) -> x1 = x2.
Definition term64 (a0 : Type') (x0 : tybit1 a0) := (fun y0 : tybit1 a0 => fun y1 : type6 a0 => y0 = (@mktybit1 a0 y1)) x0.
Definition term104 (a0 : Type') (x0 : tybit1 a0) (x1 : tybit1 a0) (x2 : tybit1 a0) := ~ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term38 (a0 : Type') (x0 : tybit1 a0) := fun y0 : type6 a0 => (@mktybit1 a0 y0) = x0.
Definition term32 (a0 : Type') := ~ (forall y0 : tybit1 a0, exists y1 : type6 a0, y0 = (@mktybit1 a0 y1)).
Definition term25 (a0 : Type') := ~ (forall y0 : tybit1 a0, exists y1 : type6 a0, (@mktybit1 a0 y1) = y0).
Definition term34 (a0 : Type') := (~ (forall y0 : tybit1 a0, exists y1 : type6 a0, (@mktybit1 a0 y1) = y0)) -> ~ (forall y0 : tybit1 a0, exists y1 : type6 a0, y0 = (@mktybit1 a0 y1)).
Definition term119 (a0 : Type') (x0 : type1348 a0) (x1 : tybit1 a0) := ((@mktybit1 a0 (x0 x1)) = x1) -> False.
Definition term115 (a0 : Type') (x0 : type1348 a0) (x1 : tybit1 a0) := ((x1 = (@mktybit1 a0 (x0 x1))) /\ (x1 = x1)) -> (@mktybit1 a0 (x0 x1)) = x1.
Definition term89 (a0 : Type') (x0 : tybit1 a0) := ~ (x0 = x0).
Definition term109 (a0 : Type') (x0 : tybit1 a0) (x1 : tybit1 a0) := and (x0 = x1).
Definition term110 (a0 : Type') (x0 : tybit1 a0) (x1 : tybit1 a0) (x2 : tybit1 a0) := (x1 = x0) /\ (x1 = x2).
Definition term112 (a0 : Type') (x0 : tybit1 a0) (x1 : tybit1 a0) (x2 : tybit1 a0) := imp ((x1 = x0) /\ (x1 = x2)).
Definition term53 (a0 : Type') (x0 : tybit1 a0) := ~ ((fun y0 : tybit1 a0 => exists y1 : type6 a0, (@mktybit1 a0 y1) = y0) x0).
Definition term65 (a0 : Type') (x0 : tybit1 a0) (x1 : type6 a0) := (fun y0 : tybit1 a0 => fun y1 : type6 a0 => y0 = (@mktybit1 a0 y1)) x0 x1.
Definition term68 (a0 : Type') (x0 : tybit1 a0) := exists y0 : type6 a0, (fun y1 : tybit1 a0 => fun y2 : type6 a0 => y1 = (@mktybit1 a0 y2)) x0 y0.
Definition term14 (a0 : Type') (x0 : type6 a0) := @eq Prop (@IN (tybit1 a0) (@mktybit1 a0 x0) (@UNIV (tybit1 a0))).
Definition term28 (a0 : Type') := ((~ (forall y0 : tybit1 a0, exists y1 : type6 a0, (@mktybit1 a0 y1) = y0)) -> (forall y0 : tybit1 a0, exists y1 : type6 a0, y0 = (@mktybit1 a0 y1)) -> False) -> (~ (forall y0 : tybit1 a0, exists y1 : type6 a0, (@mktybit1 a0 y1) = y0)) -> (forall y0 : tybit1 a0, exists y1 : type6 a0, y0 = (@mktybit1 a0 y1)) -> False.
Definition term6 (a0 : Type') (x0 : tybit1 a0) := True -> exists y0 : type6 a0, (@mktybit1 a0 y0) = x0.
Definition term107 (a0 : Type') (x0 : tybit1 a0) (x1 : tybit1 a0) := ~ (~ (x0 = x1)).
Definition term21 (a0 : Type') := (forall y0 : tybit1 a0, (@IN (tybit1 a0) y0 (@UNIV (tybit1 a0))) -> exists y1 : type6 a0, (@mktybit1 a0 y1) = y0) /\ (forall y0 : type6 a0, (@IN (tybit1 a0) (@mktybit1 a0 y0) (@UNIV (tybit1 a0))) = (@IN (finite_sum (finite_sum a0 a0) unit) y0 (@UNIV (finite_sum (finite_sum a0 a0) unit)))).
Definition term30 (a0 : Type') := (((~ (forall y0 : tybit1 a0, exists y1 : type6 a0, (@mktybit1 a0 y1) = y0)) -> (forall y0 : tybit1 a0, exists y1 : type6 a0, y0 = (@mktybit1 a0 y1)) -> False) -> (~ (forall y0 : tybit1 a0, exists y1 : type6 a0, (@mktybit1 a0 y1) = y0)) -> (forall y0 : tybit1 a0, exists y1 : type6 a0, y0 = (@mktybit1 a0 y1)) -> False) -> ((~ (forall y0 : tybit1 a0, exists y1 : type6 a0, (@mktybit1 a0 y1) = y0)) -> (forall y0 : tybit1 a0, exists y1 : type6 a0, y0 = (@mktybit1 a0 y1)) -> False) -> (~ (forall y0 : tybit1 a0, exists y1 : type6 a0, (@mktybit1 a0 y1) = y0)) -> (forall y0 : tybit1 a0, exists y1 : type6 a0, y0 = (@mktybit1 a0 y1)) -> False.
Definition term93 (a0 : Type') (x0 : tybit1 a0) (x1 : tybit1 a0) := or (~ (x0 = x1)).
Definition term7 (a0 : Type') := fun y0 : tybit1 a0 => (@IN (tybit1 a0) y0 (@UNIV (tybit1 a0))) -> exists y1 : type6 a0, (@mktybit1 a0 y1) = y0.
Definition term69 (a0 : Type') := fun y0 : tybit1 a0 => exists y1 : type6 a0, (fun y2 : tybit1 a0 => fun y3 : type6 a0 => y2 = (@mktybit1 a0 y3)) y0 y1.
Definition term58 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := exists y0 : a0 -> a1, forall y1 : a0, x0 y1 (y0 y1).
Definition term41 (a0 : Type') (x0 : tybit1 a0) := ~ (exists y0 : type6 a0, (@mktybit1 a0 y0) = x0).
Definition term9 (a0 : Type') := forall y0 : tybit1 a0, (@IN (tybit1 a0) y0 (@UNIV (tybit1 a0))) -> exists y1 : type6 a0, (@mktybit1 a0 y1) = y0.
Definition term66 (a0 : Type') (x0 : tybit1 a0) (x1 : type6 a0) := (fun y0 : type6 a0 => x0 = (@mktybit1 a0 y0)) x1.
Definition term80 (a0 : Type') := fun y0 : type1348 a0 => forall y1 : tybit1 a0, y1 = (@mktybit1 a0 (y0 y1)).
Definition term18 (a0 : Type') := forall y0 : type6 a0, True.
Definition term37 (a0 : Type') := fun y0 : tybit1 a0 => exists y1 : type6 a0, y0 = (@mktybit1 a0 y1).
Definition term33 (a0 : Type') := imp (~ (forall y0 : tybit1 a0, exists y1 : type6 a0, (@mktybit1 a0 y1) = y0)).
Definition term44 (a0 : Type') (x0 : tybit1 a0) (x1 : type6 a0) := ~ ((fun y0 : type6 a0 => (@mktybit1 a0 y0) = x0) x1).