Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term29 := (~ False) -> False.
Definition term9 (x0 : Prop) := ~ (~ x0).
Definition term25 (a0 : Type') := ~ (@INFINITE a0 (@UNIV a0)).
Definition term4 (a0 : Type') (a1 : Type') := ~ (((@INFINITE a1 (@UNIV a1)) \/ (@INFINITE a0 (@UNIV a0))) = ((@INFINITE a0 (@UNIV a0)) \/ (@INFINITE a1 (@UNIV a1)))).
Definition term28 (a0 : Type') := (@INFINITE a0 (@UNIV a0)) -> False.
Definition term2 (a0 : Type') (a1 : Type') := (@INFINITE a0 (@UNIV a0)) \/ (@INFINITE a1 (@UNIV a1)).
Definition term1 (a0 : Type') (a1 : Type') := (@INFINITE a1 (@UNIV a1)) \/ (@INFINITE a0 (@UNIV a0)).
Definition term0 (x0 : Prop) := (~ x0) -> False.
Definition term3 (a0 : Type') (a1 : Type') := (~ (((@INFINITE a1 (@UNIV a1)) \/ (@INFINITE a0 (@UNIV a0))) = ((@INFINITE a0 (@UNIV a0)) \/ (@INFINITE a1 (@UNIV a1))))) -> False.
Definition term19 (a0 : Type') (a1 : Type') := ((@INFINITE a1 (@UNIV a1)) \/ (@INFINITE a0 (@UNIV a0))) /\ (~ ((@INFINITE a0 (@UNIV a0)) \/ (@INFINITE a1 (@UNIV a1)))).
Definition term27 (x0 : Prop) := (~ x0) -> x0.
Definition term13 (a0 : Type') (a1 : Type') := (~ (@INFINITE a0 (@UNIV a0))) /\ (~ (@INFINITE a1 (@UNIV a1))).
Definition term11 (a0 : Type') (a1 : Type') := (~ (@INFINITE a1 (@UNIV a1))) /\ (~ (@INFINITE a0 (@UNIV a0))).
Definition term16 (a0 : Type') (a1 : Type') := (~ ((@INFINITE a1 (@UNIV a1)) \/ (@INFINITE a0 (@UNIV a0)))) /\ ((@INFINITE a0 (@UNIV a0)) \/ (@INFINITE a1 (@UNIV a1))).
Definition term8 (a0 : Type') (a1 : Type') := ~ (~ (((@INFINITE a1 (@UNIV a1)) \/ (@INFINITE a0 (@UNIV a0))) = ((@INFINITE a0 (@UNIV a0)) \/ (@INFINITE a1 (@UNIV a1))))).
Definition term14 (a0 : Type') (a1 : Type') := and (~ ((@INFINITE a1 (@UNIV a1)) \/ (@INFINITE a0 (@UNIV a0)))).
Definition term5 (a0 : Type') (a1 : Type') := ((~ (((@INFINITE a1 (@UNIV a1)) \/ (@INFINITE a0 (@UNIV a0))) = ((@INFINITE a0 (@UNIV a0)) \/ (@INFINITE a1 (@UNIV a1))))) -> False) -> (~ (((@INFINITE a1 (@UNIV a1)) \/ (@INFINITE a0 (@UNIV a0))) = ((@INFINITE a0 (@UNIV a0)) \/ (@INFINITE a1 (@UNIV a1))))) -> False.
Definition term22 (a0 : Type') (a1 : Type') := or (((@INFINITE a1 (@UNIV a1)) \/ (@INFINITE a0 (@UNIV a0))) /\ ((~ (@INFINITE a0 (@UNIV a0))) /\ (~ (@INFINITE a1 (@UNIV a1))))).
Definition term12 (a0 : Type') (a1 : Type') := ~ ((@INFINITE a0 (@UNIV a0)) \/ (@INFINITE a1 (@UNIV a1))).
Definition term10 (a0 : Type') (a1 : Type') := ~ ((@INFINITE a1 (@UNIV a1)) \/ (@INFINITE a0 (@UNIV a0))).
Definition term6 (a0 : Type') (a1 : Type') := (((~ (((@INFINITE a1 (@UNIV a1)) \/ (@INFINITE a0 (@UNIV a0))) = ((@INFINITE a0 (@UNIV a0)) \/ (@INFINITE a1 (@UNIV a1))))) -> False) -> (~ (((@INFINITE a1 (@UNIV a1)) \/ (@INFINITE a0 (@UNIV a0))) = ((@INFINITE a0 (@UNIV a0)) \/ (@INFINITE a1 (@UNIV a1))))) -> False) -> (~ (((@INFINITE a1 (@UNIV a1)) \/ (@INFINITE a0 (@UNIV a0))) = ((@INFINITE a0 (@UNIV a0)) \/ (@INFINITE a1 (@UNIV a1))))) -> False.
Definition term26 (a0 : Type') := (~ (@INFINITE a0 (@UNIV a0))) -> @INFINITE a0 (@UNIV a0).
Definition term15 (a0 : Type') (a1 : Type') := and ((~ (@INFINITE a1 (@UNIV a1))) /\ (~ (@INFINITE a0 (@UNIV a0)))).
Definition term23 (a0 : Type') (a1 : Type') := (((@INFINITE a1 (@UNIV a1)) \/ (@INFINITE a0 (@UNIV a0))) /\ (~ ((@INFINITE a0 (@UNIV a0)) \/ (@INFINITE a1 (@UNIV a1))))) \/ ((~ ((@INFINITE a1 (@UNIV a1)) \/ (@INFINITE a0 (@UNIV a0)))) /\ ((@INFINITE a0 (@UNIV a0)) \/ (@INFINITE a1 (@UNIV a1)))).
Definition term24 (a0 : Type') (a1 : Type') := (((@INFINITE a1 (@UNIV a1)) \/ (@INFINITE a0 (@UNIV a0))) /\ ((~ (@INFINITE a0 (@UNIV a0))) /\ (~ (@INFINITE a1 (@UNIV a1))))) \/ (((~ (@INFINITE a1 (@UNIV a1))) /\ (~ (@INFINITE a0 (@UNIV a0)))) /\ ((@INFINITE a0 (@UNIV a0)) \/ (@INFINITE a1 (@UNIV a1)))).
Definition term7 (a0 : Type') (a1 : Type') := (((~ (((@INFINITE a1 (@UNIV a1)) \/ (@INFINITE a0 (@UNIV a0))) = ((@INFINITE a0 (@UNIV a0)) \/ (@INFINITE a1 (@UNIV a1))))) -> False) -> (~ (((@INFINITE a1 (@UNIV a1)) \/ (@INFINITE a0 (@UNIV a0))) = ((@INFINITE a0 (@UNIV a0)) \/ (@INFINITE a1 (@UNIV a1))))) -> False) -> ((~ (((@INFINITE a1 (@UNIV a1)) \/ (@INFINITE a0 (@UNIV a0))) = ((@INFINITE a0 (@UNIV a0)) \/ (@INFINITE a1 (@UNIV a1))))) -> False) -> (~ (((@INFINITE a1 (@UNIV a1)) \/ (@INFINITE a0 (@UNIV a0))) = ((@INFINITE a0 (@UNIV a0)) \/ (@INFINITE a1 (@UNIV a1))))) -> False.
Definition term20 (a0 : Type') (a1 : Type') := ((@INFINITE a1 (@UNIV a1)) \/ (@INFINITE a0 (@UNIV a0))) /\ ((~ (@INFINITE a0 (@UNIV a0))) /\ (~ (@INFINITE a1 (@UNIV a1)))).
Definition term17 (a0 : Type') (a1 : Type') := ((~ (@INFINITE a1 (@UNIV a1))) /\ (~ (@INFINITE a0 (@UNIV a0)))) /\ ((@INFINITE a0 (@UNIV a0)) \/ (@INFINITE a1 (@UNIV a1))).
Definition term21 (a0 : Type') (a1 : Type') := or (((@INFINITE a1 (@UNIV a1)) \/ (@INFINITE a0 (@UNIV a0))) /\ (~ ((@INFINITE a0 (@UNIV a0)) \/ (@INFINITE a1 (@UNIV a1))))).
Definition term18 (a0 : Type') (a1 : Type') := and ((@INFINITE a1 (@UNIV a1)) \/ (@INFINITE a0 (@UNIV a0))).
