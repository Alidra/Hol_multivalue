Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term59 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 /\ (~ x1)) -> ~ x2.
Definition term8 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => (@FINITE a0 y0) /\ (@SUBSET a0 x0 y0).
Definition term141 := (~ False) -> False.
Definition term142 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (~ (forall y2 : a0, (y1 y2) -> (y0 y2) \/ ((y1 y2) /\ (~ (y0 y2))))) -> False) x0.
Definition term112 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) -> (x1 y0) \/ ((x0 y0) /\ (~ (x1 y0))).
Definition term50 (x0 : Prop) := True -> ~ x0.
Definition term28 (x0 : Prop) := imp (~ x0).
Definition term95 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) := (@IN a0 x1 x0) \/ (@IN a0 x1 x2).
Definition term77 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((@FINITE a0 x0) /\ (~ (@INFINITE a0 (@DIFF a0 x1 x0)))) -> ~ (@INFINITE a0 x1).
Definition term6 (a0 : Type') (x0 : a0 -> Prop) := (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> @FINITE a0 y0) -> @FINITE a0 x0.
Definition term131 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := or (~ (x0 x1)).
Definition term78 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((@FINITE a0 x0) /\ (@FINITE a0 (@DIFF a0 x1 x0))) -> @FINITE a0 x1.
Definition term39 (x0 : Prop) := ((~ True) -> ~ x0) -> x0 -> True.
Definition term68 (x0 : Prop) := ~ (~ x0).
Definition term23 (x0 : Prop) (x1 : Prop) (x2 : Prop) := @eq Prop (((x1 /\ (~ x2)) -> ~ x0) -> (x0 /\ x1) -> x2).
Definition term37 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => ((~ y0) -> ~ x0) -> x0 -> y0) x1.
Definition term115 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ (forall y0 : a0, (x0 y0) -> (x1 y0) \/ ((x0 y0) /\ (~ (x1 y0)))).
Definition term53 (x0 : Prop) := False /\ (~ x0).
Definition term57 (x0 : Prop) := imp (x0 /\ False).
Definition term66 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ (@INFINITE a0 (@DIFF a0 x0 x1)).
Definition term106 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (x0 x2) /\ (~ (x1 x2)).
Definition term91 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @UNION a0 x1 (@DIFF a0 x0 x1).
Definition term82 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @FINITE a0 (@UNION a0 x0 x1).
Definition term105 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (x0 x1).
Definition term55 (x0 : Prop) (x1 : Prop) := (False /\ (~ x0)) -> ~ x1.
Definition term127 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0, (y1 y2) -> (y0 y2) \/ ((y1 y2) /\ (~ (y0 y2))).
Definition term136 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (~ (x1 x2)) /\ (~ ((x0 x2) /\ (~ (x1 x2)))).
Definition term113 (x0 : Prop) := (~ x0) -> False.
Definition term81 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@FINITE a0 (@UNION a0 x0 y0)) = ((@FINITE a0 x0) /\ (@FINITE a0 y0))) x1.
Definition term128 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (~ ((x1 x2) \/ ((x0 x2) /\ (~ (x1 x2))))) -> False.
Definition term54 (x0 : Prop) := imp (False /\ (~ x0)).
Definition term4 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((@FINITE a0 x0) /\ (@SUBSET a0 x1 x0)) -> @FINITE a0 x1.
Definition term51 (x0 : Prop) := imp ((~ False) -> ~ x0).
Definition term47 (x0 : Prop) := imp ((~ True) -> ~ x0).
Definition term36 (x0 : Prop) := fun y0 : Prop => ((~ y0) -> ~ x0) -> x0 -> y0.
Definition term130 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (~ (x0 x1)).
Definition term109 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (x0 x2) -> (x1 x2) \/ ((x0 x2) /\ (~ (x1 x2))).
Definition term111 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (x0 y0) -> (x1 y0) \/ ((x0 y0) /\ (~ (x1 y0))).
Definition term104 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := ~ (@IN a0 x0 x1).
Definition term139 (x0 : Prop) := (~ x0) -> x0.
Definition term83 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@FINITE a0 x0) /\ (@FINITE a0 x1).
Definition term25 (x0 : Prop) (x1 : Prop) := ((False /\ (~ x1)) -> ~ x0) -> (x0 /\ False) -> x1.
Definition term20 (x0 : Prop) (x1 : Prop) := ((True /\ (~ x1)) -> ~ x0) -> (x0 /\ True) -> x1.
Definition term73 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := imp ((@FINITE a0 x1) /\ (~ (@INFINITE a0 (@DIFF a0 x0 x1)))).
Definition term38 (x0 : Prop) := (fun y0 : Prop => ((~ y0) -> ~ x0) -> x0 -> y0) True.
Definition term144 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((@INFINITE a0 x0) /\ (@FINITE a0 x1)) -> @INFINITE a0 (@DIFF a0 x0 x1).
Definition term100 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @IN a0 x0 (@DIFF a0 x1 x2).
Definition term88 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := True /\ (@SUBSET a0 x0 (@UNION a0 x1 (@DIFF a0 x0 x1))).
Definition term94 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @IN a0 x0 (@UNION a0 x1 x2).
Definition term19 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => ((y0 /\ (~ x1)) -> ~ x0) -> (x0 /\ y0) -> x1) True.
Definition term30 (x0 : Prop) (x1 : Prop) := (~ x0) -> ~ x1.
Definition term67 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ (~ (@FINITE a0 (@DIFF a0 x0 x1))).
Definition term84 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @FINITE a0 (@UNION a0 x1 (@DIFF a0 x0 x1)).
Definition term71 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@FINITE a0 x1) /\ (~ (@INFINITE a0 (@DIFF a0 x0 x1))).
Definition term45 (x0 : Prop) := (~ True) -> ~ x0.
Definition term70 (a0 : Type') (x0 : a0 -> Prop) := and (@FINITE a0 x0).
Definition term14 (a0 : Type') (x0 : a0 -> Prop) := ~ (@FINITE a0 x0).
Definition term102 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := and (@IN a0 x0 x1).
Definition term2 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, ((@FINITE a0 y0) /\ (@SUBSET a0 x0 y0)) -> @FINITE a0 x0.
Definition term86 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @SUBSET a0 x0 (@UNION a0 x1 (@DIFF a0 x0 x1)).
Definition term33 (x0 : Prop) := imp (x0 /\ True).
Definition term116 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((~ (forall y0 : a0, (x0 y0) -> (x1 y0) \/ ((x0 y0) /\ (~ (x1 y0))))) -> False) -> (~ (forall y0 : a0, (x0 y0) -> (x1 y0) \/ ((x0 y0) /\ (~ (x1 y0))))) -> False.
Definition term5 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@FINITE a0 x1) /\ (@SUBSET a0 x0 x1).
Definition term34 (x0 : Prop) (x1 : Prop) := (x0 /\ True) -> x1.
Definition term72 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@FINITE a0 x1) /\ (@FINITE a0 (@DIFF a0 x0 x1)).
Definition term121 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => forall y1 : a0, (y0 y1) -> (x0 y1) \/ ((y0 y1) /\ (~ (x0 y1))).
Definition term137 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (~ (x1 x2)) /\ ((~ (x0 x2)) \/ (x1 x2)).
Definition term29 (x0 : Prop) (x1 : Prop) := (True /\ (~ x0)) -> ~ x1.
Definition term126 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, (~ (forall y2 : a0, (y1 y2) -> (y0 y2) \/ ((y1 y2) /\ (~ (y0 y2))))) -> False.
Definition term18 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => ((y0 /\ (~ x1)) -> ~ x0) -> (x0 /\ y0) -> x1) x2.
Definition term9 (a0 : Type') (x0 : a0 -> Prop) := (exists y0 : a0 -> Prop, (@FINITE a0 y0) /\ (@SUBSET a0 x0 y0)) -> @FINITE a0 x0.
Definition term17 (x0 : Prop) (x1 : Prop) := fun y0 : Prop => ((y0 /\ (~ x1)) -> ~ x0) -> (x0 /\ y0) -> x1.
Definition term35 (x0 : Prop) (x1 : Prop) := ((~ x1) -> ~ x0) -> x0 -> x1.
Definition term132 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (~ (x0 x2)) \/ (~ (~ (x1 x2))).
Definition term103 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := and (x0 x1).
Definition term134 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ~ ((x0 x2) /\ (~ (x1 x2))).
Definition term108 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (@IN a0 x0 x1) -> @IN a0 x0 (@UNION a0 x2 (@DIFF a0 x1 x2)).
Definition term26 (x0 : Prop) := True /\ (~ x0).
Definition term49 (x0 : Prop) := (~ False) -> ~ x0.
Definition term79 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (@FINITE a0 (@UNION a0 y0 y1)) = ((@FINITE a0 y0) /\ (@FINITE a0 y1))) x0.
Definition term1 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> @FINITE a0 y0) x0.
Definition term119 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ (~ (forall y0 : a0, (x0 y0) -> (x1 y0) \/ ((x0 y0) /\ (~ (x1 y0))))).
Definition term40 (x0 : Prop) (x1 : Prop) := @eq Prop ((fun y0 : Prop => ((~ y0) -> ~ x0) -> x0 -> y0) x1).
Definition term69 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @FINITE a0 (@DIFF a0 x0 x1).
Definition term114 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (forall y0 : a0, (x0 y0) -> (x1 y0) \/ ((x0 y0) /\ (~ (x1 y0))))) -> False.
Definition term80 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (@FINITE a0 (@UNION a0 x0 y0)) = ((@FINITE a0 x0) /\ (@FINITE a0 y0)).
Definition term143 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (~ (forall y1 : a0, (y0 y1) -> (x0 y1) \/ ((y0 y1) /\ (~ (x0 y1))))) -> False) x1.
Definition term75 (a0 : Type') (x0 : a0 -> Prop) := ~ (@INFINITE a0 x0).
Definition term61 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (((x1 /\ (~ x2)) -> ~ x0) -> (x0 /\ x1) -> x2) -> (x0 /\ x1) -> x2.
Definition term52 (x0 : Prop) := (~ x0) -> ~ x0.
Definition term117 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (((~ (forall y0 : a0, (x0 y0) -> (x1 y0) \/ ((x0 y0) /\ (~ (x1 y0))))) -> False) -> (~ (forall y0 : a0, (x0 y0) -> (x1 y0) \/ ((x0 y0) /\ (~ (x1 y0))))) -> False) -> (~ (forall y0 : a0, (x0 y0) -> (x1 y0) \/ ((x0 y0) /\ (~ (x1 y0))))) -> False.
Definition term16 (x0 : Prop) := (x0 = True) \/ (x0 = False).
Definition term48 := imp (~ False).
Definition term122 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (~ (forall y1 : a0, (y0 y1) -> (x0 y1) \/ ((y0 y1) /\ (~ (x0 y1))))) -> False.
Definition term60 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 /\ x1) -> x2.
Definition term92 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := imp (@IN a0 x0 x1).
Definition term46 (x0 : Prop) := False -> ~ x0.
Definition term107 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (x1 x2) \/ ((x0 x2) /\ (~ (x1 x2))).
Definition term146 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@INFINITE a0 y0) /\ (@FINITE a0 y1)) -> @INFINITE a0 (@DIFF a0 y0 y1).
Definition term0 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> @FINITE a0 y0.
Definition term10 (a0 : Type') := forall y0 : a0 -> Prop, (exists y1 : a0 -> Prop, (@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> @FINITE a0 y0.
Definition term27 (x0 : Prop) := imp (True /\ (~ x0)).
Definition term93 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := imp (x0 x1).
Definition term96 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @IN a0 x0 (@UNION a0 x2 (@DIFF a0 x1 x2)).
Definition term32 (x0 : Prop) (x1 : Prop) := imp ((~ x0) -> ~ x1).
Definition term124 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (~ (forall y2 : a0, (y1 y2) -> (y0 y2) \/ ((y1 y2) /\ (~ (y0 y2))))) -> False.
Definition term63 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (((@FINITE a0 x1) /\ (~ (@INFINITE a0 (@DIFF a0 x0 x1)))) -> ~ (@INFINITE a0 x0)) -> ((@INFINITE a0 x0) /\ (@FINITE a0 x1)) -> @INFINITE a0 (@DIFF a0 x0 x1).
Definition term22 (x0 : Prop) (x1 : Prop) (x2 : Prop) := ((x1 /\ (~ x2)) -> ~ x0) -> (x0 /\ x1) -> x2.
Definition term90 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) -> @IN a0 y0 (@UNION a0 x1 (@DIFF a0 x0 x1)).
Definition term97 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (@IN a0 x0 x2) \/ (@IN a0 x0 (@DIFF a0 x1 x2)).
Definition term65 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ (@FINITE a0 (@DIFF a0 x0 x1)).
Definition term133 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (~ (x0 x2)) \/ (x1 x2).
Definition term76 (a0 : Type') (x0 : a0 -> Prop) := ~ (~ (@FINITE a0 x0)).
Definition term140 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (x0 x1) -> False.
Definition term101 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) := (@IN a0 x1 x0) /\ (~ (@IN a0 x1 x2)).
Definition term129 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ~ ((x1 x2) \/ ((x0 x2) /\ (~ (x1 x2)))).
Definition term89 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) -> @IN a0 y0 x1.
Definition term85 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := and (@FINITE a0 (@UNION a0 x1 (@DIFF a0 x0 x1))).
Definition term42 (x0 : Prop) := (fun y0 : Prop => ((~ y0) -> ~ x0) -> x0 -> y0) False.
Definition term74 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := imp ((@FINITE a0 x1) /\ (@FINITE a0 (@DIFF a0 x0 x1))).
Definition term145 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, ((@INFINITE a0 x0) /\ (@FINITE a0 y0)) -> @INFINITE a0 (@DIFF a0 x0 y0).
Definition term7 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0 -> Prop, (@FINITE a0 y0) /\ (@SUBSET a0 x0 y0).
Definition term125 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, forall y2 : a0, (y1 y2) -> (y0 y2) \/ ((y1 y2) /\ (~ (y0 y2))).
Definition term118 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (((~ (forall y0 : a0, (x0 y0) -> (x1 y0) \/ ((x0 y0) /\ (~ (x1 y0))))) -> False) -> (~ (forall y0 : a0, (x0 y0) -> (x1 y0) \/ ((x0 y0) /\ (~ (x1 y0))))) -> False) -> ((~ (forall y0 : a0, (x0 y0) -> (x1 y0) \/ ((x0 y0) /\ (~ (x1 y0))))) -> False) -> (~ (forall y0 : a0, (x0 y0) -> (x1 y0) \/ ((x0 y0) /\ (~ (x1 y0))))) -> False.
Definition term12 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (exists y1 : a0 -> Prop, (@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> @FINITE a0 y0) x0.
Definition term120 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => (~ (forall y1 : a0, (y0 y1) -> (x0 y1) \/ ((y0 y1) /\ (~ (x0 y1))))) -> False.
Definition term44 := imp (~ True).
Definition term98 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := or (@IN a0 x0 x1).
Definition term62 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (((x1 /\ (~ x2)) -> ~ x0) -> (x0 /\ x1) -> x2) -> ((x1 /\ (~ x2)) -> ~ x0) -> (x0 /\ x1) -> x2.
Definition term43 (x0 : Prop) := ((~ False) -> ~ x0) -> x0 -> False.
Definition term110 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (@IN a0 y0 x0) -> @IN a0 y0 (@UNION a0 x1 (@DIFF a0 x0 x1)).
Definition term58 (x0 : Prop) (x1 : Prop) := (x0 /\ False) -> x1.
Definition term15 (x0 : Prop) := (fun y0 : Prop => (y0 = True) \/ (y0 = False)) x0.
Definition term3 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => ((@FINITE a0 y0) /\ (@SUBSET a0 x0 y0)) -> @FINITE a0 x0) x1.
Definition term13 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@INFINITE a0 y0) = (~ (@FINITE a0 y0))) x0.
Definition term135 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := and (~ (x0 x1)).
Definition term138 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (~ (x0 x1)) -> x0 x1.
Definition term123 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, forall y1 : a0, (y0 y1) -> (x0 y1) \/ ((y0 y1) /\ (~ (x0 y1))).
Definition term11 (a0 : Type') := (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> @FINITE a0 y0) -> forall y0 : a0 -> Prop, (exists y1 : a0 -> Prop, (@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> @FINITE a0 y0.
Definition term87 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@FINITE a0 (@UNION a0 x1 (@DIFF a0 x0 x1))) /\ (@SUBSET a0 x0 (@UNION a0 x1 (@DIFF a0 x0 x1))).
Definition term56 (x0 : Prop) (x1 : Prop) := imp ((False /\ (~ x0)) -> ~ x1).
Definition term31 (x0 : Prop) (x1 : Prop) := imp ((True /\ (~ x0)) -> ~ x1).
Definition term99 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := or (x0 x1).
Definition term21 (x0 : Prop) (x1 : Prop) (x2 : Prop) := @eq Prop ((fun y0 : Prop => ((y0 /\ (~ x1)) -> ~ x0) -> (x0 /\ y0) -> x1) x2).
Definition term24 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => ((y0 /\ (~ x1)) -> ~ x0) -> (x0 /\ y0) -> x1) False.
Definition term41 (x0 : Prop) (x1 : Prop) := @eq Prop (((~ x1) -> ~ x0) -> x0 -> x1).
Definition term64 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @INFINITE a0 (@DIFF a0 x0 x1).
