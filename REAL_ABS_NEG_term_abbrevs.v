Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term60 (x0 : real) := forall y0 : real, ((real_le x0 y0) /\ (real_le y0 x0)) = (x0 = y0).
Definition term130 (x0 : real -> Prop) := ~ (all x0).
Definition term298 := (~ False) -> False.
Definition term46 := imp (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1)).
Definition term10 (x0 : real) := real_neg (real_neg x0).
Definition term86 (x0 : real) := True /\ ((real_le x0 (real_of_num (NUMERAL 0))) \/ (x0 = (real_neg x0))).
Definition term33 := fun y0 : real => (@COND real (real_le y0 (real_of_num (NUMERAL 0))) (real_neg y0) y0) = (@COND real (real_le (real_of_num (NUMERAL 0)) y0) y0 (real_neg y0)).
Definition term51 := ((real_neg (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1)) -> ~ (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)).
Definition term122 (x0 : real) := ~ ((real_le (real_of_num (NUMERAL 0)) x0) \/ ((real_le x0 (real_of_num (NUMERAL 0))) \/ (x0 = (real_neg x0)))).
Definition term303 (x0 : real) := (~ (real_le (real_of_num (NUMERAL 0)) x0)) -> real_le x0 (real_of_num (NUMERAL 0)).
Definition term233 := (~ ((real_neg (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0)))) -> (real_neg (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0)).
Definition term251 (x0 : Prop) := ~ (~ x0).
Definition term22 := real_of_num (NUMERAL 0).
Definition term26 (x0 : real) := @COND real (real_le x0 (real_of_num (NUMERAL 0))).
Definition term220 := and (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) \/ (~ (y0 = y1))).
Definition term79 (x0 : real) := (~ (real_le x0 (real_of_num (NUMERAL 0)))) \/ ((real_neg x0) = (@COND real (real_le (real_of_num (NUMERAL 0)) x0) x0 (real_neg x0))).
Definition term92 (x0 : real) := ((~ (real_le x0 (real_of_num (NUMERAL 0)))) \/ ((real_neg x0) = x0)) /\ True.
Definition term123 (x0 : real) := or (~ ((~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ ((~ (real_le x0 (real_of_num (NUMERAL 0)))) \/ ((real_neg x0) = x0)))).
Definition term198 (x0 : real) := and (forall y0 : real, ((real_le x0 y0) /\ (real_le y0 x0)) \/ (~ (x0 = y0))).
Definition term283 (x0 : real) (x1 : real) (x2 : real) := (~ (~ (x1 = x0))) /\ (~ (~ (x1 = x2))).
Definition term252 (x0 : real) (x1 : real) := ~ (~ (real_le x0 x1)).
Definition term82 (x0 : real) := and ((~ (real_le x0 (real_of_num (NUMERAL 0)))) \/ ((real_neg x0) = (@COND real (real_le (real_of_num (NUMERAL 0)) x0) x0 (real_neg x0)))).
Definition term210 (x0 : real) := and ((fun y0 : real => forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) \/ (~ (y0 = y1))) x0).
Definition term139 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term165 (x0 : real) (x1 : real) := ~ ((real_le x1 x0) /\ (real_le x0 x1)).
Definition term56 (x0 : real) := forall y0 : real, (real_le x0 y0) \/ (real_le y0 x0).
Definition term231 (x0 : real) (x1 : real) := (~ (x0 = x1)) \/ ((real_neg x0) = (real_neg x1)).
Definition term3 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0).
Definition term67 (x0 : real) := @COND real True (real_neg x0) x0.
Definition term219 := and (forall y0 : real, (fun y1 : real => forall y2 : real, ((real_le y1 y2) /\ (real_le y2 y1)) \/ (~ (y1 = y2))) y0).
Definition term197 (x0 : real) := and (forall y0 : real, (fun y1 : real => ((real_le x0 y1) /\ (real_le y1 x0)) \/ (~ (x0 = y1))) y0).
Definition term50 := ((real_neg (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False.
Definition term36 (x0 : Prop) := (~ x0) -> False.
Definition term287 (x0 : real) (x1 : real) (x2 : real) := imp (~ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term255 (x0 : real) (x1 : real) := imp (~ ((~ (real_le x1 x0)) \/ (~ (real_le x0 x1)))).
Definition term115 (x0 : real) := ~ ((~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ ((~ (real_le x0 (real_of_num (NUMERAL 0)))) \/ ((real_neg x0) = x0))).
Definition term100 := ~ (forall y0 : real, ((~ (real_le (real_of_num (NUMERAL 0)) y0)) \/ ((~ (real_le y0 (real_of_num (NUMERAL 0)))) \/ ((real_neg y0) = y0))) /\ ((real_le (real_of_num (NUMERAL 0)) y0) \/ ((real_le y0 (real_of_num (NUMERAL 0))) \/ (y0 = (real_neg y0))))).
Definition term38 := ~ (forall y0 : real, (@COND real (real_le y0 (real_of_num (NUMERAL 0))) (real_neg y0) y0) = (@COND real (real_le (real_of_num (NUMERAL 0)) y0) y0 (real_neg y0))).
Definition term75 (x0 : real) := @COND real (real_le (real_of_num (NUMERAL 0)) x0).
Definition term109 (x0 : real) := (real_le x0 (real_of_num (NUMERAL 0))) /\ (~ ((real_neg x0) = x0)).
Definition term174 (x0 : real) := fun y0 : real => (((real_le x0 y0) /\ (real_le y0 x0)) \/ (~ (x0 = y0))) /\ (((~ (real_le x0 y0)) \/ (~ (real_le y0 x0))) \/ (x0 = y0)).
Definition term203 := fun y0 : real => (forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) \/ (~ (y0 = y1))) /\ (forall y1 : real, ((~ (real_le y0 y1)) \/ (~ (real_le y1 y0))) \/ (y0 = y1)).
Definition term54 (x0 : real) (x1 : real) := (real_le x1 x0) \/ (real_le x0 x1).
Definition term84 (x0 : real) := (real_le x0 (real_of_num (NUMERAL 0))) \/ (x0 = (@COND real (real_le (real_of_num (NUMERAL 0)) x0) x0 (real_neg x0))).
Definition term90 (x0 : real) := and ((~ (real_le x0 (real_of_num (NUMERAL 0)))) \/ ((real_neg x0) = x0)).
Definition term126 (x0 : real) := ((real_le (real_of_num (NUMERAL 0)) x0) /\ ((real_le x0 (real_of_num (NUMERAL 0))) /\ (~ ((real_neg x0) = x0)))) \/ ((~ (real_le (real_of_num (NUMERAL 0)) x0)) /\ ((~ (real_le x0 (real_of_num (NUMERAL 0)))) /\ (~ (x0 = (real_neg x0))))).
Definition term164 := real_neg (real_of_num (NUMERAL 0)).
Definition term76 (x0 : real) := @COND real (real_le (real_of_num (NUMERAL 0)) x0) x0.
Definition term257 (x0 : real) (x1 : real) := ((real_le x0 x1) /\ (real_le x1 x0)) -> x0 = x1.
Definition term224 := (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) \/ (~ (y0 = y1))) /\ (forall y0 : real, forall y1 : real, ((~ (real_le y0 y1)) \/ (~ (real_le y1 y0))) \/ (y0 = y1)).
Definition term24 (x0 : real) := real_le x0 (real_of_num (NUMERAL 0)).
Definition term271 (x0 : real) := (~ ((real_neg (real_of_num (NUMERAL 0))) = (real_neg x0))) -> (real_neg (real_of_num (NUMERAL 0))) = (real_neg x0).
Definition term89 (x0 : real) := (~ (real_le x0 (real_of_num (NUMERAL 0)))) \/ ((real_neg x0) = x0).
Definition term245 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term206 := (forall y0 : real, (fun y1 : real => forall y2 : real, ((real_le y1 y2) /\ (real_le y2 y1)) \/ (~ (y1 = y2))) y0) /\ (forall y0 : real, (fun y1 : real => forall y2 : real, ((~ (real_le y1 y2)) \/ (~ (real_le y2 y1))) \/ (y1 = y2)) y0).
Definition term183 (x0 : real) := (forall y0 : real, (fun y1 : real => ((real_le x0 y1) /\ (real_le y1 x0)) \/ (~ (x0 = y1))) y0) /\ (forall y0 : real, (fun y1 : real => ((~ (real_le x0 y1)) \/ (~ (real_le y1 x0))) \/ (x0 = y1)) y0).
Definition term20 (x0 : real) := real_le (real_of_num (NUMERAL 0)) (real_neg x0).
Definition term73 (x0 : real) := ((~ (real_le x0 (real_of_num (NUMERAL 0)))) \/ ((real_neg x0) = (@COND real (real_le (real_of_num (NUMERAL 0)) x0) x0 (real_neg x0)))) /\ ((real_le x0 (real_of_num (NUMERAL 0))) \/ (x0 = (@COND real (real_le (real_of_num (NUMERAL 0)) x0) x0 (real_neg x0)))).
Definition term264 (x0 : real) (x1 : real) := @eq Prop ((~ (x0 = x1)) \/ ((real_neg x0) = (real_neg x1))).
Definition term170 (x0 : real) (x1 : real) := ((~ (real_le x0 x1)) \/ (~ (real_le x1 x0))) \/ (x0 = x1).
Definition term114 (x0 : real) := (real_le (real_of_num (NUMERAL 0)) x0) /\ ((real_le x0 (real_of_num (NUMERAL 0))) /\ (~ ((real_neg x0) = x0))).
Definition term167 (x0 : real) (x1 : real) := or (~ ((real_le x1 x0) /\ (real_le x0 x1))).
Definition term85 (x0 : real) := (real_le x0 (real_of_num (NUMERAL 0))) \/ (x0 = (real_neg x0)).
Definition term235 (x0 : Prop) := (~ x0) -> x0.
Definition term87 (x0 : real) := ((real_le (real_of_num (NUMERAL 0)) x0) = False) -> (((~ (real_le x0 (real_of_num (NUMERAL 0)))) \/ ((real_neg x0) = (@COND real (real_le (real_of_num (NUMERAL 0)) x0) x0 (real_neg x0)))) /\ ((real_le x0 (real_of_num (NUMERAL 0))) \/ (x0 = (@COND real (real_le (real_of_num (NUMERAL 0)) x0) x0 (real_neg x0))))) = ((real_le x0 (real_of_num (NUMERAL 0))) \/ (x0 = (real_neg x0))).
Definition term169 (x0 : real) (x1 : real) := (~ ((real_le x0 x1) /\ (real_le x1 x0))) \/ (x0 = x1).
Definition term34 := forall y0 : real, (real_abs (real_neg y0)) = (real_abs y0).
Definition term238 (x0 : real) (x1 : real) := (~ (real_le x1 x0)) \/ (x0 = x1).
Definition term119 (x0 : real) := and (~ (real_le (real_of_num (NUMERAL 0)) x0)).
Definition term281 (x0 : real) (x1 : real) (x2 : real) := (~ (x1 = x0)) \/ (~ (x1 = x2)).
Definition term221 := fun y0 : real => (fun y1 : real => forall y2 : real, ((~ (real_le y1 y2)) \/ (~ (real_le y2 y1))) \/ (y1 = y2)) y0.
Definition term216 := fun y0 : real => (fun y1 : real => forall y2 : real, ((real_le y1 y2) /\ (real_le y2 y1)) \/ (~ (y1 = y2))) y0.
Definition term248 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term116 (x0 : real) := ~ (real_le (real_of_num (NUMERAL 0)) x0).
Definition term91 (x0 : real) := (real_le x0 (real_of_num (NUMERAL 0))) \/ True.
Definition term278 (x0 : real) (x1 : real) (x2 : real) := @eq Prop ((~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2))).
Definition term113 (x0 : real) := (~ (~ (real_le (real_of_num (NUMERAL 0)) x0))) /\ (~ ((~ (real_le x0 (real_of_num (NUMERAL 0)))) \/ ((real_neg x0) = x0))).
Definition term93 (x0 : real) := ((real_le (real_of_num (NUMERAL 0)) x0) = True) -> (((~ (real_le x0 (real_of_num (NUMERAL 0)))) \/ ((real_neg x0) = (@COND real (real_le (real_of_num (NUMERAL 0)) x0) x0 (real_neg x0)))) /\ ((real_le x0 (real_of_num (NUMERAL 0))) \/ (x0 = (@COND real (real_le (real_of_num (NUMERAL 0)) x0) x0 (real_neg x0))))) = ((~ (real_le x0 (real_of_num (NUMERAL 0)))) \/ ((real_neg x0) = x0)).
Definition term229 (x0 : real) (x1 : real) := (x0 = x1) -> (real_neg x0) = (real_neg x1).
Definition term172 (x0 : real) (x1 : real) := (((real_le x0 x1) /\ (real_le x1 x0)) \/ (~ (x0 = x1))) /\ ((~ ((real_le x0 x1) /\ (real_le x1 x0))) \/ (x0 = x1)).
Definition term159 := exists y0 : real, (fun y1 : real => (~ (real_le (real_of_num (NUMERAL 0)) y1)) /\ ((~ (real_le y1 (real_of_num (NUMERAL 0)))) /\ (~ (y1 = (real_neg y1))))) y0.
Definition term154 := exists y0 : real, (fun y1 : real => (real_le (real_of_num (NUMERAL 0)) y1) /\ ((real_le y1 (real_of_num (NUMERAL 0))) /\ (~ ((real_neg y1) = y1)))) y0.
Definition term68 (x0 : real) := @eq real (real_neg x0).
Definition term223 := forall y0 : real, forall y1 : real, ((~ (real_le y0 y1)) \/ (~ (real_le y1 y0))) \/ (y0 = y1).
Definition term218 := forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) \/ (~ (y0 = y1)).
Definition term177 := forall y0 : real, forall y1 : real, (((real_le y0 y1) /\ (real_le y1 y0)) \/ (~ (y0 = y1))) /\ (((~ (real_le y0 y1)) \/ (~ (real_le y1 y0))) \/ (y0 = y1)).
Definition term62 := forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1).
Definition term45 := forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0).
Definition term279 (x0 : real) (x1 : real) (x2 : real) := @eq Prop ((x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term31 (x0 : real) := @eq real (@COND real (real_le x0 (real_of_num (NUMERAL 0))) (real_neg x0) x0).
Definition term175 (x0 : real) := forall y0 : real, (((real_le x0 y0) /\ (real_le y0 x0)) \/ (~ (x0 = y0))) /\ (((~ (real_le x0 y0)) \/ (~ (real_le y0 x0))) \/ (x0 = y0)).
Definition term30 (x0 : real) := @eq real (real_abs (real_neg x0)).
Definition term179 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term47 := (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False.
Definition term41 := (((~ (forall y0 : real, (@COND real (real_le y0 (real_of_num (NUMERAL 0))) (real_neg y0) y0) = (@COND real (real_le (real_of_num (NUMERAL 0)) y0) y0 (real_neg y0)))) -> ((real_neg (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False) -> (~ (forall y0 : real, (@COND real (real_le y0 (real_of_num (NUMERAL 0))) (real_neg y0) y0) = (@COND real (real_le (real_of_num (NUMERAL 0)) y0) y0 (real_neg y0)))) -> ((real_neg (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False) -> (~ (forall y0 : real, (@COND real (real_le y0 (real_of_num (NUMERAL 0))) (real_neg y0) y0) = (@COND real (real_le (real_of_num (NUMERAL 0)) y0) y0 (real_neg y0)))) -> ((real_neg (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False.
Definition term156 := or (exists y0 : real, (fun y1 : real => (real_le (real_of_num (NUMERAL 0)) y1) /\ ((real_le y1 (real_of_num (NUMERAL 0))) /\ (~ ((real_neg y1) = y1)))) y0).
Definition term121 (x0 : real) := (~ (real_le (real_of_num (NUMERAL 0)) x0)) /\ ((~ (real_le x0 (real_of_num (NUMERAL 0)))) /\ (~ (x0 = (real_neg x0)))).
Definition term5 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term246 (x0 : real) (x1 : real) := (~ ((~ (real_le x0 x1)) \/ (~ (real_le x1 x0)))) -> x0 = x1.
Definition term236 (x0 : real) := (~ (real_le (real_of_num (NUMERAL 0)) x0)) -> real_le (real_of_num (NUMERAL 0)) x0.
Definition term291 (x0 : real) := (((real_neg (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) /\ ((real_neg (real_of_num (NUMERAL 0))) = (real_neg x0))) -> (real_of_num (NUMERAL 0)) = (real_neg x0).
Definition term14 (x0 : real) (x1 : real) := real_le x0 (real_neg x1).
Definition term265 (x0 : real) (x1 : real) := @eq Prop (((real_neg x0) = (real_neg x1)) \/ (~ (x0 = x1))).
Definition term244 (x0 : real) (x1 : real) := @eq Prop ((x1 = x0) \/ ((~ (real_le x1 x0)) \/ (~ (real_le x0 x1)))).
Definition term132 := exists y0 : real, ~ ((fun y1 : real => ((~ (real_le (real_of_num (NUMERAL 0)) y1)) \/ ((~ (real_le y1 (real_of_num (NUMERAL 0)))) \/ ((real_neg y1) = y1))) /\ ((real_le (real_of_num (NUMERAL 0)) y1) \/ ((real_le y1 (real_of_num (NUMERAL 0))) \/ (y1 = (real_neg y1))))) y0).
Definition term83 (x0 : real) := or (real_le x0 (real_of_num (NUMERAL 0))).
Definition term69 (x0 : real) := ((real_le x0 (real_of_num (NUMERAL 0))) = True) -> ((@COND real (real_le x0 (real_of_num (NUMERAL 0))) (real_neg x0) x0) = (@COND real (real_le (real_of_num (NUMERAL 0)) x0) x0 (real_neg x0))) = ((real_neg x0) = (@COND real (real_le (real_of_num (NUMERAL 0)) x0) x0 (real_neg x0))).
Definition term98 := fun y0 : real => ((~ (real_le (real_of_num (NUMERAL 0)) y0)) \/ ((~ (real_le y0 (real_of_num (NUMERAL 0)))) \/ ((real_neg y0) = y0))) /\ ((real_le (real_of_num (NUMERAL 0)) y0) \/ ((real_le y0 (real_of_num (NUMERAL 0))) \/ (y0 = (real_neg y0)))).
Definition term215 := @eq Prop (forall y0 : real, (forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) \/ (~ (y0 = y1))) /\ (forall y1 : real, ((~ (real_le y0 y1)) \/ (~ (real_le y1 y0))) \/ (y0 = y1))).
Definition term214 := @eq Prop (forall y0 : real, ((fun y1 : real => forall y2 : real, ((real_le y1 y2) /\ (real_le y2 y1)) \/ (~ (y1 = y2))) y0) /\ ((fun y1 : real => forall y2 : real, ((~ (real_le y1 y2)) \/ (~ (real_le y2 y1))) \/ (y1 = y2)) y0)).
Definition term193 (x0 : real) := @eq Prop (forall y0 : real, (((real_le x0 y0) /\ (real_le y0 x0)) \/ (~ (x0 = y0))) /\ (((~ (real_le x0 y0)) \/ (~ (real_le y0 x0))) \/ (x0 = y0))).
Definition term192 (x0 : real) := @eq Prop (forall y0 : real, ((fun y1 : real => ((real_le x0 y1) /\ (real_le y1 x0)) \/ (~ (x0 = y1))) y0) /\ ((fun y1 : real => ((~ (real_le x0 y1)) \/ (~ (real_le y1 x0))) \/ (x0 = y1)) y0)).
Definition term112 (x0 : real) := and (real_le (real_of_num (NUMERAL 0)) x0).
Definition term232 (x0 : real) (x1 : real) (x2 : real) := (~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2)).
Definition term258 (x0 : real) := (real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le x0 (real_of_num (NUMERAL 0))).
Definition term173 (x0 : real) (x1 : real) := (((real_le x0 x1) /\ (real_le x1 x0)) \/ (~ (x0 = x1))) /\ (((~ (real_le x0 x1)) \/ (~ (real_le x1 x0))) \/ (x0 = x1)).
Definition term7 (x0 : real) := (fun y0 : real => (real_add (real_of_num (NUMERAL 0)) y0) = y0) x0.
Definition term166 (x0 : real) (x1 : real) := (~ (real_le x1 x0)) \/ (~ (real_le x0 x1)).
Definition term65 (x0 : real) := ((real_le x0 (real_of_num (NUMERAL 0))) = False) -> ((@COND real (real_le x0 (real_of_num (NUMERAL 0))) (real_neg x0) x0) = (@COND real (real_le (real_of_num (NUMERAL 0)) x0) x0 (real_neg x0))) = (x0 = (@COND real (real_le (real_of_num (NUMERAL 0)) x0) x0 (real_neg x0))).
Definition term304 (x0 : real) := (real_le x0 (real_of_num (NUMERAL 0))) -> False.
Definition term176 := fun y0 : real => forall y1 : real, (((real_le y0 y1) /\ (real_le y1 y0)) \/ (~ (y0 = y1))) /\ (((~ (real_le y0 y1)) \/ (~ (real_le y1 y0))) \/ (y0 = y1)).
Definition term43 := (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False.
Definition term104 (x0 : real) := ~ (~ (real_le x0 (real_of_num (NUMERAL 0)))).
Definition term58 (x0 : real) (x1 : real) := (real_le x1 x0) /\ (real_le x0 x1).
Definition term148 (x0 : real) := (fun y0 : real => (~ (real_le (real_of_num (NUMERAL 0)) y0)) /\ ((~ (real_le y0 (real_of_num (NUMERAL 0)))) /\ (~ (y0 = (real_neg y0))))) x0.
Definition term263 (x0 : real) (x1 : real) := ~ (x0 = x1).
Definition term42 := (((~ (forall y0 : real, (@COND real (real_le y0 (real_of_num (NUMERAL 0))) (real_neg y0) y0) = (@COND real (real_le (real_of_num (NUMERAL 0)) y0) y0 (real_neg y0)))) -> ((real_neg (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False) -> (~ (forall y0 : real, (@COND real (real_le y0 (real_of_num (NUMERAL 0))) (real_neg y0) y0) = (@COND real (real_le (real_of_num (NUMERAL 0)) y0) y0 (real_neg y0)))) -> ((real_neg (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False) -> ((~ (forall y0 : real, (@COND real (real_le y0 (real_of_num (NUMERAL 0))) (real_neg y0) y0) = (@COND real (real_le (real_of_num (NUMERAL 0)) y0) y0 (real_neg y0)))) -> ((real_neg (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False) -> (~ (forall y0 : real, (@COND real (real_le y0 (real_of_num (NUMERAL 0))) (real_neg y0) y0) = (@COND real (real_le (real_of_num (NUMERAL 0)) y0) y0 (real_neg y0)))) -> ((real_neg (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False.
Definition term140 (x0 : real -> Prop) (x1 : real -> Prop) := exists y0 : real, (x0 y0) \/ (x1 y0).
Definition term161 := (exists y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) /\ ((real_le y0 (real_of_num (NUMERAL 0))) /\ (~ ((real_neg y0) = y0)))) \/ (exists y0 : real, (~ (real_le (real_of_num (NUMERAL 0)) y0)) /\ ((~ (real_le y0 (real_of_num (NUMERAL 0)))) /\ (~ (y0 = (real_neg y0))))).
Definition term44 := ~ (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)).
Definition term185 (x0 : real) := fun y0 : real => ((~ (real_le x0 y0)) \/ (~ (real_le y0 x0))) \/ (x0 = y0).
Definition term0 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, (y0 \/ (y1 \/ y2)) = ((y0 \/ y1) \/ y2)) x0.
Definition term145 := fun y0 : real => (~ (real_le (real_of_num (NUMERAL 0)) y0)) /\ ((~ (real_le y0 (real_of_num (NUMERAL 0)))) /\ (~ (y0 = (real_neg y0)))).
Definition term274 (x0 : real) (x1 : real) (x2 : real) := (x0 = x2) \/ (~ (x1 = x2)).
Definition term141 (x0 : real -> Prop) (x1 : real -> Prop) := (exists y0 : real, x0 y0) \/ (exists y0 : real, x1 y0).
Definition term247 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term202 (x0 : real) := (forall y0 : real, ((real_le x0 y0) /\ (real_le y0 x0)) \/ (~ (x0 = y0))) /\ (forall y0 : real, ((~ (real_le x0 y0)) \/ (~ (real_le y0 x0))) \/ (x0 = y0)).
Definition term241 (x0 : real) (x1 : real) := (~ (real_le x1 x0)) \/ ((x1 = x0) \/ (~ (real_le x0 x1))).
Definition term78 (x0 : real) := or (~ (real_le x0 (real_of_num (NUMERAL 0)))).
Definition term96 (x0 : real) := ((~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ ((~ (real_le x0 (real_of_num (NUMERAL 0)))) \/ ((real_neg x0) = x0))) /\ ((real_le (real_of_num (NUMERAL 0)) x0) \/ ((real_le x0 (real_of_num (NUMERAL 0))) \/ (x0 = (real_neg x0)))).
Definition term77 (x0 : real) := @COND real False x0 (real_neg x0).
Definition term9 (x0 : real) := (fun y0 : real => (real_neg (real_neg y0)) = y0) x0.
Definition term184 (x0 : real) := fun y0 : real => ((real_le x0 y0) /\ (real_le y0 x0)) \/ (~ (x0 = y0)).
Definition term194 (x0 : real) := fun y0 : real => (fun y1 : real => ((real_le x0 y1) /\ (real_le y1 x0)) \/ (~ (x0 = y1))) y0.
Definition term120 (x0 : real) := (~ (real_le (real_of_num (NUMERAL 0)) x0)) /\ (~ ((real_le x0 (real_of_num (NUMERAL 0))) \/ (x0 = (real_neg x0)))).
Definition term171 (x0 : real) (x1 : real) := and (((real_le x0 x1) /\ (real_le x1 x0)) \/ (~ (x0 = x1))).
Definition term189 (x0 : real) (x1 : real) := (fun y0 : real => ((~ (real_le x0 y0)) \/ (~ (real_le y0 x0))) \/ (x0 = y0)) x1.
Definition term40 := ((~ (forall y0 : real, (@COND real (real_le y0 (real_of_num (NUMERAL 0))) (real_neg y0) y0) = (@COND real (real_le (real_of_num (NUMERAL 0)) y0) y0 (real_neg y0)))) -> ((real_neg (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False) -> (~ (forall y0 : real, (@COND real (real_le y0 (real_of_num (NUMERAL 0))) (real_neg y0) y0) = (@COND real (real_le (real_of_num (NUMERAL 0)) y0) y0 (real_neg y0)))) -> ((real_neg (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False.
Definition term133 (x0 : real) := (fun y0 : real => ((~ (real_le (real_of_num (NUMERAL 0)) y0)) \/ ((~ (real_le y0 (real_of_num (NUMERAL 0)))) \/ ((real_neg y0) = y0))) /\ ((real_le (real_of_num (NUMERAL 0)) y0) \/ ((real_le y0 (real_of_num (NUMERAL 0))) \/ (y0 = (real_neg y0))))) x0.
Definition term49 := imp ((real_neg (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))).
Definition term152 := @eq Prop (exists y0 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ ((real_le y0 (real_of_num (NUMERAL 0))) /\ (~ ((real_neg y0) = y0)))) \/ ((~ (real_le (real_of_num (NUMERAL 0)) y0)) /\ ((~ (real_le y0 (real_of_num (NUMERAL 0)))) /\ (~ (y0 = (real_neg y0)))))).
Definition term151 := @eq Prop (exists y0 : real, ((fun y1 : real => (real_le (real_of_num (NUMERAL 0)) y1) /\ ((real_le y1 (real_of_num (NUMERAL 0))) /\ (~ ((real_neg y1) = y1)))) y0) \/ ((fun y1 : real => (~ (real_le (real_of_num (NUMERAL 0)) y1)) /\ ((~ (real_le y1 (real_of_num (NUMERAL 0)))) /\ (~ (y1 = (real_neg y1))))) y0)).
Definition term208 := fun y0 : real => forall y1 : real, ((~ (real_le y0 y1)) \/ (~ (real_le y1 y0))) \/ (y0 = y1).
Definition term61 := fun y0 : real => forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1).
Definition term57 := fun y0 : real => forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0).
Definition term131 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term180 (x0 : real -> Prop) (x1 : real -> Prop) := forall y0 : real, (x0 y0) /\ (x1 y0).
Definition term117 (x0 : real) := ~ ((real_le x0 (real_of_num (NUMERAL 0))) \/ (x0 = (real_neg x0))).
Definition term6 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 \/ x1) \/ x2.
Definition term225 (x0 : real) := (fun y0 : real => forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) x0.
Definition term211 (x0 : real) := (fun y0 : real => forall y1 : real, ((~ (real_le y0 y1)) \/ (~ (real_le y1 y0))) \/ (y0 = y1)) x0.
Definition term209 (x0 : real) := (fun y0 : real => forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) \/ (~ (y0 = y1))) x0.
Definition term11 (x0 : real) := (fun y0 : real => forall y1 : real, (real_le y0 (real_neg y1)) = (real_le (real_add y0 y1) (real_of_num (NUMERAL 0)))) x0.
Definition term262 (x0 : real) (x1 : real) := ((real_neg x0) = (real_neg x1)) \/ (~ (x0 = x1)).
Definition term12 (x0 : real) := forall y0 : real, (real_le x0 (real_neg y0)) = (real_le (real_add x0 y0) (real_of_num (NUMERAL 0))).
Definition term27 (x0 : real) := @COND real (real_le (real_of_num (NUMERAL 0)) (real_neg x0)) (real_neg x0).
Definition term168 (x0 : real) (x1 : real) := or ((~ (real_le x1 x0)) \/ (~ (real_le x0 x1))).
Definition term74 (x0 : real) := real_le (real_of_num (NUMERAL 0)) x0.
Definition term16 (x0 : real) := (fun y0 : real => (real_abs y0) = (@COND real (real_le (real_of_num (NUMERAL 0)) y0) y0 (real_neg y0))) x0.
Definition term28 (x0 : real) := @COND real (real_le x0 (real_of_num (NUMERAL 0))) (real_neg x0).
Definition term37 := (~ (forall y0 : real, (@COND real (real_le y0 (real_of_num (NUMERAL 0))) (real_neg y0) y0) = (@COND real (real_le (real_of_num (NUMERAL 0)) y0) y0 (real_neg y0)))) -> False.
Definition term200 (x0 : real) := forall y0 : real, (fun y1 : real => ((~ (real_le x0 y1)) \/ (~ (real_le y1 x0))) \/ (x0 = y1)) y0.
Definition term195 (x0 : real) := forall y0 : real, (fun y1 : real => ((real_le x0 y1) /\ (real_le y1 x0)) \/ (~ (x0 = y1))) y0.
Definition term270 (x0 : real) := ((real_of_num (NUMERAL 0)) = x0) -> (real_neg (real_of_num (NUMERAL 0))) = (real_neg x0).
Definition term286 (x0 : real) (x1 : real) (x2 : real) := (x1 = x0) /\ (x1 = x2).
Definition term144 := fun y0 : real => (real_le (real_of_num (NUMERAL 0)) y0) /\ ((real_le y0 (real_of_num (NUMERAL 0))) /\ (~ ((real_neg y0) = y0))).
Definition term55 (x0 : real) := fun y0 : real => (real_le x0 y0) \/ (real_le y0 x0).
Definition term213 := fun y0 : real => ((fun y1 : real => forall y2 : real, ((real_le y1 y2) /\ (real_le y2 y1)) \/ (~ (y1 = y2))) y0) /\ ((fun y1 : real => forall y2 : real, ((~ (real_le y1 y2)) \/ (~ (real_le y2 y1))) \/ (y1 = y2)) y0).
Definition term301 (x0 : real) (x1 : real) := @eq Prop ((real_le x1 x0) \/ (real_le x0 x1)).
Definition term260 (x0 : real) := (~ ((real_of_num (NUMERAL 0)) = x0)) -> (real_of_num (NUMERAL 0)) = x0.
Definition term277 (x0 : real) (x1 : real) (x2 : real) := (x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term276 (x0 : real) (x1 : real) (x2 : real) := (~ (x1 = x0)) \/ ((x0 = x2) \/ (~ (x1 = x2))).
Definition term242 (x0 : real) (x1 : real) := (x1 = x0) \/ ((~ (real_le x1 x0)) \/ (~ (real_le x0 x1))).
Definition term59 (x0 : real) := fun y0 : real => ((real_le x0 y0) /\ (real_le y0 x0)) = (x0 = y0).
Definition term39 := (~ (forall y0 : real, (@COND real (real_le y0 (real_of_num (NUMERAL 0))) (real_neg y0) y0) = (@COND real (real_le (real_of_num (NUMERAL 0)) y0) y0 (real_neg y0)))) -> ((real_neg (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False.
Definition term227 (x0 : real) (x1 : real) := (~ (real_le x0 x1)) \/ ((~ (real_le x1 x0)) \/ (x0 = x1)).
Definition term17 (x0 : real) := @COND real (real_le (real_of_num (NUMERAL 0)) x0) x0 (real_neg x0).
Definition term108 (x0 : real) := (~ (~ (real_le x0 (real_of_num (NUMERAL 0))))) /\ (~ ((real_neg x0) = x0)).
Definition term240 (x0 : real) (x1 : real) := or (~ (real_le x0 x1)).
Definition term111 (x0 : real) := and (~ (~ (real_le (real_of_num (NUMERAL 0)) x0))).
Definition term1 (x0 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1).
Definition term190 (x0 : real) (x1 : real) := ((fun y0 : real => ((real_le x0 y0) /\ (real_le y0 x0)) \/ (~ (x0 = y0))) x1) /\ ((fun y0 : real => ((~ (real_le x0 y0)) \/ (~ (real_le y0 x0))) \/ (x0 = y0)) x1).
Definition term237 (x0 : real) := (~ (real_le x0 (real_of_num (NUMERAL 0)))) -> real_le x0 (real_of_num (NUMERAL 0)).
Definition term284 (x0 : real) (x1 : real) := and (~ (~ (x0 = x1))).
Definition term253 (x0 : real) (x1 : real) := and (~ (~ (real_le x0 x1))).
Definition term136 := fun y0 : real => ((real_le (real_of_num (NUMERAL 0)) y0) /\ ((real_le y0 (real_of_num (NUMERAL 0))) /\ (~ ((real_neg y0) = y0)))) \/ ((~ (real_le (real_of_num (NUMERAL 0)) y0)) /\ ((~ (real_le y0 (real_of_num (NUMERAL 0)))) /\ (~ (y0 = (real_neg y0))))).
Definition term239 (x0 : real) (x1 : real) := (x1 = x0) \/ (~ (real_le x0 x1)).
Definition term80 (x0 : real) := (~ (real_le x0 (real_of_num (NUMERAL 0)))) \/ True.
Definition term266 (x0 : real) (x1 : real) := (~ (~ (x0 = x1))) -> (real_neg x0) = (real_neg x1).
Definition term150 := fun y0 : real => ((fun y1 : real => (real_le (real_of_num (NUMERAL 0)) y1) /\ ((real_le y1 (real_of_num (NUMERAL 0))) /\ (~ ((real_neg y1) = y1)))) y0) \/ ((fun y1 : real => (~ (real_le (real_of_num (NUMERAL 0)) y1)) /\ ((~ (real_le y1 (real_of_num (NUMERAL 0)))) /\ (~ (y1 = (real_neg y1))))) y0).
Definition term292 (x0 : real) := (~ ((real_of_num (NUMERAL 0)) = (real_neg x0))) -> (real_of_num (NUMERAL 0)) = (real_neg x0).
Definition term64 (x0 : real) := @COND real False (real_neg x0) x0.
Definition term293 (x0 : real) := ~ ((real_of_num (NUMERAL 0)) = (real_neg x0)).
Definition term297 (x0 : real) := ((real_neg x0) = x0) -> False.
Definition term95 (x0 : real) := ((((real_le (real_of_num (NUMERAL 0)) x0) = False) -> (((~ (real_le x0 (real_of_num (NUMERAL 0)))) \/ ((real_neg x0) = (@COND real (real_le (real_of_num (NUMERAL 0)) x0) x0 (real_neg x0)))) /\ ((real_le x0 (real_of_num (NUMERAL 0))) \/ (x0 = (@COND real (real_le (real_of_num (NUMERAL 0)) x0) x0 (real_neg x0))))) = ((real_le x0 (real_of_num (NUMERAL 0))) \/ (x0 = (real_neg x0)))) /\ (((real_le (real_of_num (NUMERAL 0)) x0) = True) -> (((~ (real_le x0 (real_of_num (NUMERAL 0)))) \/ ((real_neg x0) = (@COND real (real_le (real_of_num (NUMERAL 0)) x0) x0 (real_neg x0)))) /\ ((real_le x0 (real_of_num (NUMERAL 0))) \/ (x0 = (@COND real (real_le (real_of_num (NUMERAL 0)) x0) x0 (real_neg x0))))) = ((~ (real_le x0 (real_of_num (NUMERAL 0)))) \/ ((real_neg x0) = x0)))) -> (((~ (real_le x0 (real_of_num (NUMERAL 0)))) \/ ((real_neg x0) = (@COND real (real_le (real_of_num (NUMERAL 0)) x0) x0 (real_neg x0)))) /\ ((real_le x0 (real_of_num (NUMERAL 0))) \/ (x0 = (@COND real (real_le (real_of_num (NUMERAL 0)) x0) x0 (real_neg x0))))) = (((~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ ((~ (real_le x0 (real_of_num (NUMERAL 0)))) \/ ((real_neg x0) = x0))) /\ ((real_le (real_of_num (NUMERAL 0)) x0) \/ ((real_le x0 (real_of_num (NUMERAL 0))) \/ (x0 = (real_neg x0))))).
Definition term72 (x0 : real) := ((((real_le x0 (real_of_num (NUMERAL 0))) = False) -> ((@COND real (real_le x0 (real_of_num (NUMERAL 0))) (real_neg x0) x0) = (@COND real (real_le (real_of_num (NUMERAL 0)) x0) x0 (real_neg x0))) = (x0 = (@COND real (real_le (real_of_num (NUMERAL 0)) x0) x0 (real_neg x0)))) /\ (((real_le x0 (real_of_num (NUMERAL 0))) = True) -> ((@COND real (real_le x0 (real_of_num (NUMERAL 0))) (real_neg x0) x0) = (@COND real (real_le (real_of_num (NUMERAL 0)) x0) x0 (real_neg x0))) = ((real_neg x0) = (@COND real (real_le (real_of_num (NUMERAL 0)) x0) x0 (real_neg x0))))) -> ((@COND real (real_le x0 (real_of_num (NUMERAL 0))) (real_neg x0) x0) = (@COND real (real_le (real_of_num (NUMERAL 0)) x0) x0 (real_neg x0))) = (((~ (real_le x0 (real_of_num (NUMERAL 0)))) \/ ((real_neg x0) = (@COND real (real_le (real_of_num (NUMERAL 0)) x0) x0 (real_neg x0)))) /\ ((real_le x0 (real_of_num (NUMERAL 0))) \/ (x0 = (@COND real (real_le (real_of_num (NUMERAL 0)) x0) x0 (real_neg x0))))).
Definition term142 := exists y0 : real, ((fun y1 : real => (real_le (real_of_num (NUMERAL 0)) y1) /\ ((real_le y1 (real_of_num (NUMERAL 0))) /\ (~ ((real_neg y1) = y1)))) y0) \/ ((fun y1 : real => (~ (real_le (real_of_num (NUMERAL 0)) y1)) /\ ((~ (real_le y1 (real_of_num (NUMERAL 0)))) /\ (~ (y1 = (real_neg y1))))) y0).
Definition term256 (x0 : real) (x1 : real) := imp ((real_le x1 x0) /\ (real_le x0 x1)).
Definition term71 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (((x2 = False) -> x0 = x3) /\ ((x2 = True) -> x0 = x1)) -> x0 = (((~ x2) \/ x1) /\ (x2 \/ x3)).
Definition term234 := ~ ((real_neg (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))).
Definition term149 (x0 : real) := ((fun y0 : real => (real_le (real_of_num (NUMERAL 0)) y0) /\ ((real_le y0 (real_of_num (NUMERAL 0))) /\ (~ ((real_neg y0) = y0)))) x0) \/ ((fun y0 : real => (~ (real_le (real_of_num (NUMERAL 0)) y0)) /\ ((~ (real_le y0 (real_of_num (NUMERAL 0)))) /\ (~ (y0 = (real_neg y0))))) x0).
Definition term146 (x0 : real) := (fun y0 : real => (real_le (real_of_num (NUMERAL 0)) y0) /\ ((real_le y0 (real_of_num (NUMERAL 0))) /\ (~ ((real_neg y0) = y0)))) x0.
Definition term125 (x0 : real) := (~ ((~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ ((~ (real_le x0 (real_of_num (NUMERAL 0)))) \/ ((real_neg x0) = x0)))) \/ (~ ((real_le (real_of_num (NUMERAL 0)) x0) \/ ((real_le x0 (real_of_num (NUMERAL 0))) \/ (x0 = (real_neg x0))))).
Definition term160 := exists y0 : real, (~ (real_le (real_of_num (NUMERAL 0)) y0)) /\ ((~ (real_le y0 (real_of_num (NUMERAL 0)))) /\ (~ (y0 = (real_neg y0)))).
Definition term118 (x0 : real) := (~ (real_le x0 (real_of_num (NUMERAL 0)))) /\ (~ (x0 = (real_neg x0))).
Definition term228 (x0 : real) (x1 : real) := ~ (real_le x0 x1).
Definition term290 (x0 : real) := ((real_neg (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) /\ ((real_neg (real_of_num (NUMERAL 0))) = (real_neg x0)).
Definition term21 (x0 : real) := real_le (real_add (real_of_num (NUMERAL 0)) x0) (real_of_num (NUMERAL 0)).
Definition term204 := forall y0 : real, (forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) \/ (~ (y0 = y1))) /\ (forall y1 : real, ((~ (real_le y0 y1)) \/ (~ (real_le y1 y0))) \/ (y0 = y1)).
Definition term155 := exists y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) /\ ((real_le y0 (real_of_num (NUMERAL 0))) /\ (~ ((real_neg y0) = y0))).
Definition term261 (x0 : real) := ~ ((real_of_num (NUMERAL 0)) = x0).
Definition term106 (x0 : real) := and (~ (~ (real_le x0 (real_of_num (NUMERAL 0))))).
Definition term8 (x0 : real) := real_add (real_of_num (NUMERAL 0)) x0.
Definition term289 (x0 : real) (x1 : real) (x2 : real) := ((x0 = x1) /\ (x0 = x2)) -> x1 = x2.
Definition term282 (x0 : real) (x1 : real) (x2 : real) := ~ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term249 (x0 : real) (x1 : real) := ~ ((~ (real_le x1 x0)) \/ (~ (real_le x0 x1))).
Definition term280 (x0 : real) (x1 : real) (x2 : real) := (~ ((~ (x0 = x1)) \/ (~ (x0 = x2)))) -> x1 = x2.
Definition term158 := fun y0 : real => (fun y1 : real => (~ (real_le (real_of_num (NUMERAL 0)) y1)) /\ ((~ (real_le y1 (real_of_num (NUMERAL 0)))) /\ (~ (y1 = (real_neg y1))))) y0.
Definition term153 := fun y0 : real => (fun y1 : real => (real_le (real_of_num (NUMERAL 0)) y1) /\ ((real_le y1 (real_of_num (NUMERAL 0))) /\ (~ ((real_neg y1) = y1)))) y0.
Definition term222 := forall y0 : real, (fun y1 : real => forall y2 : real, ((~ (real_le y1 y2)) \/ (~ (real_le y2 y1))) \/ (y1 = y2)) y0.
Definition term217 := forall y0 : real, (fun y1 : real => forall y2 : real, ((real_le y1 y2) /\ (real_le y2 y1)) \/ (~ (y1 = y2))) y0.
Definition term285 (x0 : real) (x1 : real) := and (x0 = x1).
Definition term212 (x0 : real) := ((fun y0 : real => forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) \/ (~ (y0 = y1))) x0) /\ ((fun y0 : real => forall y1 : real, ((~ (real_le y0 y1)) \/ (~ (real_le y1 y0))) \/ (y0 = y1)) x0).
Definition term48 := (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1)) -> ~ (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)).
Definition term272 (x0 : real) := ~ ((real_neg (real_of_num (NUMERAL 0))) = (real_neg x0)).
Definition term13 (x0 : real) (x1 : real) := (fun y0 : real => (real_le x0 (real_neg y0)) = (real_le (real_add x0 y0) (real_of_num (NUMERAL 0)))) x1.
Definition term254 (x0 : real) (x1 : real) := and (real_le x0 x1).
Definition term299 (x0 : real) := (real_le (real_of_num (NUMERAL 0)) x0) -> ~ (real_le (real_of_num (NUMERAL 0)) x0).
Definition term230 (x0 : Prop) (x1 : Prop) := (~ x0) \/ x1.
Definition term191 (x0 : real) := fun y0 : real => ((fun y1 : real => ((real_le x0 y1) /\ (real_le y1 x0)) \/ (~ (x0 = y1))) y0) /\ ((fun y1 : real => ((~ (real_le x0 y1)) \/ (~ (real_le y1 x0))) \/ (x0 = y1)) y0).
Definition term199 (x0 : real) := fun y0 : real => (fun y1 : real => ((~ (real_le x0 y1)) \/ (~ (real_le y1 x0))) \/ (x0 = y1)) y0.
Definition term29 (x0 : real) := @COND real (real_le x0 (real_of_num (NUMERAL 0))) (real_neg x0) x0.
Definition term99 := forall y0 : real, ((~ (real_le (real_of_num (NUMERAL 0)) y0)) \/ ((~ (real_le y0 (real_of_num (NUMERAL 0)))) \/ ((real_neg y0) = y0))) /\ ((real_le (real_of_num (NUMERAL 0)) y0) \/ ((real_le y0 (real_of_num (NUMERAL 0))) \/ (y0 = (real_neg y0)))).
Definition term294 (x0 : real) := ((real_of_num (NUMERAL 0)) = (real_neg x0)) /\ ((real_of_num (NUMERAL 0)) = x0).
Definition term2 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1)) x1.
Definition term134 (x0 : real) := ~ ((fun y0 : real => ((~ (real_le (real_of_num (NUMERAL 0)) y0)) \/ ((~ (real_le y0 (real_of_num (NUMERAL 0)))) \/ ((real_neg y0) = y0))) /\ ((real_le (real_of_num (NUMERAL 0)) y0) \/ ((real_le y0 (real_of_num (NUMERAL 0))) \/ (y0 = (real_neg y0))))) x0).
Definition term15 (x0 : real) (x1 : real) := real_le (real_add x0 x1) (real_of_num (NUMERAL 0)).
Definition term19 (x0 : real) := @COND real (real_le (real_of_num (NUMERAL 0)) (real_neg x0)) (real_neg x0) (real_neg (real_neg x0)).
Definition term135 := fun y0 : real => ~ ((fun y1 : real => ((~ (real_le (real_of_num (NUMERAL 0)) y1)) \/ ((~ (real_le y1 (real_of_num (NUMERAL 0)))) \/ ((real_neg y1) = y1))) /\ ((real_le (real_of_num (NUMERAL 0)) y1) \/ ((real_le y1 (real_of_num (NUMERAL 0))) \/ (y1 = (real_neg y1))))) y0).
Definition term128 (x0 : real) := (~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ ((~ (real_le x0 (real_of_num (NUMERAL 0)))) \/ ((real_neg x0) = x0)).
Definition term186 (x0 : real) (x1 : real) := (fun y0 : real => ((real_le x0 y0) /\ (real_le y0 x0)) \/ (~ (x0 = y0))) x1.
Definition term137 := exists y0 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ ((real_le y0 (real_of_num (NUMERAL 0))) /\ (~ ((real_neg y0) = y0)))) \/ ((~ (real_le (real_of_num (NUMERAL 0)) y0)) /\ ((~ (real_le y0 (real_of_num (NUMERAL 0)))) /\ (~ (y0 = (real_neg y0))))).
Definition term181 (x0 : real -> Prop) (x1 : real -> Prop) := (forall y0 : real, x0 y0) /\ (forall y0 : real, x1 y0).
Definition term107 (x0 : real) := and (real_le x0 (real_of_num (NUMERAL 0))).
Definition term243 (x0 : real) (x1 : real) := @eq Prop ((~ (real_le x0 x1)) \/ ((~ (real_le x1 x0)) \/ (x0 = x1))).
Definition term124 (x0 : real) := or ((real_le (real_of_num (NUMERAL 0)) x0) /\ ((real_le x0 (real_of_num (NUMERAL 0))) /\ (~ ((real_neg x0) = x0)))).
Definition term35 := forall y0 : real, (@COND real (real_le y0 (real_of_num (NUMERAL 0))) (real_neg y0) y0) = (@COND real (real_le (real_of_num (NUMERAL 0)) y0) y0 (real_neg y0)).
Definition term296 (x0 : real) := (~ ((real_neg x0) = x0)) -> (real_neg x0) = x0.
Definition term70 (x0 : real) := (((real_le x0 (real_of_num (NUMERAL 0))) = False) -> ((@COND real (real_le x0 (real_of_num (NUMERAL 0))) (real_neg x0) x0) = (@COND real (real_le (real_of_num (NUMERAL 0)) x0) x0 (real_neg x0))) = (x0 = (@COND real (real_le (real_of_num (NUMERAL 0)) x0) x0 (real_neg x0)))) /\ (((real_le x0 (real_of_num (NUMERAL 0))) = True) -> ((@COND real (real_le x0 (real_of_num (NUMERAL 0))) (real_neg x0) x0) = (@COND real (real_le (real_of_num (NUMERAL 0)) x0) x0 (real_neg x0))) = ((real_neg x0) = (@COND real (real_le (real_of_num (NUMERAL 0)) x0) x0 (real_neg x0)))).
Definition term288 (x0 : real) (x1 : real) (x2 : real) := imp ((x1 = x0) /\ (x1 = x2)).
Definition term178 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term147 (x0 : real) := or ((fun y0 : real => (real_le (real_of_num (NUMERAL 0)) y0) /\ ((real_le y0 (real_of_num (NUMERAL 0))) /\ (~ ((real_neg y0) = y0)))) x0).
Definition term18 (x0 : real) := real_abs (real_neg x0).
Definition term63 (x0 : real) := @COND real False (real_neg x0).
Definition term32 := fun y0 : real => (real_abs (real_neg y0)) = (real_abs y0).
Definition term129 (x0 : real) := (real_le (real_of_num (NUMERAL 0)) x0) \/ ((real_le x0 (real_of_num (NUMERAL 0))) \/ (x0 = (real_neg x0))).
Definition term25 (x0 : real) := @COND real (real_le (real_of_num (NUMERAL 0)) (real_neg x0)).
Definition term127 (x0 : real) := ~ (((~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ ((~ (real_le x0 (real_of_num (NUMERAL 0)))) \/ ((real_neg x0) = x0))) /\ ((real_le (real_of_num (NUMERAL 0)) x0) \/ ((real_le x0 (real_of_num (NUMERAL 0))) \/ (x0 = (real_neg x0))))).
Definition term110 (x0 : real) := ~ ((~ (real_le x0 (real_of_num (NUMERAL 0)))) \/ ((real_neg x0) = x0)).
Definition term4 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0)) x2.
Definition term105 (x0 : real) := ~ ((real_neg x0) = x0).
Definition term273 (x0 : real) (x1 : real) (x2 : real) := (~ (x0 = x2)) \/ (x1 = x2).
Definition term102 := (~ (forall y0 : real, ((~ (real_le (real_of_num (NUMERAL 0)) y0)) \/ ((~ (real_le y0 (real_of_num (NUMERAL 0)))) \/ ((real_neg y0) = y0))) /\ ((real_le (real_of_num (NUMERAL 0)) y0) \/ ((real_le y0 (real_of_num (NUMERAL 0))) \/ (y0 = (real_neg y0)))))) -> ((real_neg (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1)) -> ~ (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)).
Definition term53 := (~ (forall y0 : real, (@COND real (real_le y0 (real_of_num (NUMERAL 0))) (real_neg y0) y0) = (@COND real (real_le (real_of_num (NUMERAL 0)) y0) y0 (real_neg y0)))) -> ((real_neg (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1)) -> ~ (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)).
Definition term94 (x0 : real) := (((real_le (real_of_num (NUMERAL 0)) x0) = False) -> (((~ (real_le x0 (real_of_num (NUMERAL 0)))) \/ ((real_neg x0) = (@COND real (real_le (real_of_num (NUMERAL 0)) x0) x0 (real_neg x0)))) /\ ((real_le x0 (real_of_num (NUMERAL 0))) \/ (x0 = (@COND real (real_le (real_of_num (NUMERAL 0)) x0) x0 (real_neg x0))))) = ((real_le x0 (real_of_num (NUMERAL 0))) \/ (x0 = (real_neg x0)))) /\ (((real_le (real_of_num (NUMERAL 0)) x0) = True) -> (((~ (real_le x0 (real_of_num (NUMERAL 0)))) \/ ((real_neg x0) = (@COND real (real_le (real_of_num (NUMERAL 0)) x0) x0 (real_neg x0)))) /\ ((real_le x0 (real_of_num (NUMERAL 0))) \/ (x0 = (@COND real (real_le (real_of_num (NUMERAL 0)) x0) x0 (real_neg x0))))) = ((~ (real_le x0 (real_of_num (NUMERAL 0)))) \/ ((real_neg x0) = x0))).
Definition term267 (x0 : real) (x1 : real) := ~ (~ (x0 = x1)).
Definition term259 (x0 : real) := ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le x0 (real_of_num (NUMERAL 0)))) -> (real_of_num (NUMERAL 0)) = x0.
Definition term188 (x0 : real) (x1 : real) := and ((fun y0 : real => ((real_le x0 y0) /\ (real_le y0 x0)) \/ (~ (x0 = y0))) x1).
Definition term97 (x0 : real) := @eq Prop ((@COND real (real_le x0 (real_of_num (NUMERAL 0))) (real_neg x0) x0) = (@COND real (real_le (real_of_num (NUMERAL 0)) x0) x0 (real_neg x0))).
Definition term275 (x0 : real) (x1 : real) := or (~ (x0 = x1)).
Definition term66 (x0 : real) := @COND real True (real_neg x0).
Definition term81 (x0 : real) := ~ (real_le x0 (real_of_num (NUMERAL 0))).
Definition term157 := or (exists y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) /\ ((real_le y0 (real_of_num (NUMERAL 0))) /\ (~ ((real_neg y0) = y0)))).
Definition term295 (x0 : real) := (((real_of_num (NUMERAL 0)) = (real_neg x0)) /\ ((real_of_num (NUMERAL 0)) = x0)) -> (real_neg x0) = x0.
Definition term103 (x0 : real) := ~ (~ (real_le (real_of_num (NUMERAL 0)) x0)).
Definition term138 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term23 (x0 : real) := real_le (real_add (real_of_num (NUMERAL 0)) x0).
Definition term269 (x0 : real) (x1 : real) := imp (x0 = x1).
Definition term250 (x0 : real) (x1 : real) := (~ (~ (real_le x1 x0))) /\ (~ (~ (real_le x0 x1))).
Definition term196 (x0 : real) := forall y0 : real, ((real_le x0 y0) /\ (real_le y0 x0)) \/ (~ (x0 = y0)).
Definition term205 := forall y0 : real, ((fun y1 : real => forall y2 : real, ((real_le y1 y2) /\ (real_le y2 y1)) \/ (~ (y1 = y2))) y0) /\ ((fun y1 : real => forall y2 : real, ((~ (real_le y1 y2)) \/ (~ (real_le y2 y1))) \/ (y1 = y2)) y0).
Definition term182 (x0 : real) := forall y0 : real, ((fun y1 : real => ((real_le x0 y1) /\ (real_le y1 x0)) \/ (~ (x0 = y1))) y0) /\ ((fun y1 : real => ((~ (real_le x0 y1)) \/ (~ (real_le y1 x0))) \/ (x0 = y1)) y0).
Definition term302 (x0 : real) (x1 : real) := (~ (real_le x1 x0)) -> real_le x0 x1.
Definition term143 := (exists y0 : real, (fun y1 : real => (real_le (real_of_num (NUMERAL 0)) y1) /\ ((real_le y1 (real_of_num (NUMERAL 0))) /\ (~ ((real_neg y1) = y1)))) y0) \/ (exists y0 : real, (fun y1 : real => (~ (real_le (real_of_num (NUMERAL 0)) y1)) /\ ((~ (real_le y1 (real_of_num (NUMERAL 0)))) /\ (~ (y1 = (real_neg y1))))) y0).
Definition term226 (x0 : real) (x1 : real) := (fun y0 : real => (real_le x0 y0) \/ (real_le y0 x0)) x1.
Definition term101 := imp (~ (forall y0 : real, ((~ (real_le (real_of_num (NUMERAL 0)) y0)) \/ ((~ (real_le y0 (real_of_num (NUMERAL 0)))) \/ ((real_neg y0) = y0))) /\ ((real_le (real_of_num (NUMERAL 0)) y0) \/ ((real_le y0 (real_of_num (NUMERAL 0))) \/ (y0 = (real_neg y0)))))).
Definition term52 := imp (~ (forall y0 : real, (@COND real (real_le y0 (real_of_num (NUMERAL 0))) (real_neg y0) y0) = (@COND real (real_le (real_of_num (NUMERAL 0)) y0) y0 (real_neg y0)))).
Definition term300 (x0 : Prop) := x0 -> ~ x0.
Definition term207 := fun y0 : real => forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) \/ (~ (y0 = y1)).
Definition term187 (x0 : real) (x1 : real) := ((real_le x0 x1) /\ (real_le x1 x0)) \/ (~ (x0 = x1)).
Definition term201 (x0 : real) := forall y0 : real, ((~ (real_le x0 y0)) \/ (~ (real_le y0 x0))) \/ (x0 = y0).
Definition term88 (x0 : real) := @COND real True x0 (real_neg x0).
Definition term268 (x0 : real) (x1 : real) := imp (~ (~ (x0 = x1))).
Definition term163 := @eq Prop ((exists y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) /\ ((real_le y0 (real_of_num (NUMERAL 0))) /\ (~ ((real_neg y0) = y0)))) \/ (exists y0 : real, (~ (real_le (real_of_num (NUMERAL 0)) y0)) /\ ((~ (real_le y0 (real_of_num (NUMERAL 0)))) /\ (~ (y0 = (real_neg y0)))))).
Definition term162 := @eq Prop ((exists y0 : real, (fun y1 : real => (real_le (real_of_num (NUMERAL 0)) y1) /\ ((real_le y1 (real_of_num (NUMERAL 0))) /\ (~ ((real_neg y1) = y1)))) y0) \/ (exists y0 : real, (fun y1 : real => (~ (real_le (real_of_num (NUMERAL 0)) y1)) /\ ((~ (real_le y1 (real_of_num (NUMERAL 0)))) /\ (~ (y1 = (real_neg y1))))) y0)).
