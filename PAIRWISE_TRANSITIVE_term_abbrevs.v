Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term164 (a0 : Type') := forall y0 : a0, forall y1 : type1402 a0, forall y2 : a0, forall y3 : list a0, (forall y4 : a0, forall y5 : a0, forall y6 : a0, ((y1 y4 y5) /\ (y1 y5 y6)) -> y1 y4 y6) -> (y1 y0 y2) -> (@List.ForallOrdPairs a0 y1 y3) -> forall y4 : a0, (@List.In a0 y4 y3) -> (y1 y2 y4) -> y1 y0 y4.
Definition term163 (a0 : Type') := forall y0 : a0, forall y1 : type1402 a0, forall y2 : a0, forall y3 : list a0, (forall y4 : a0, forall y5 : a0, forall y6 : a0, ((y1 y4 y5) /\ (y1 y5 y6)) -> y1 y4 y6) -> (y1 y0 y2) -> (@List.ForallOrdPairs a0 y1 y3) -> (~ (forall y4 : a0, (@List.In a0 y4 y3) -> (y1 y2 y4) -> y1 y0 y4)) -> False.
Definition term66 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => ((y0 /\ (x1 /\ x0)) = (x1 /\ x0)) = (x0 -> x1 -> y0)) False.
Definition term195 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) := fun y0 : a0 => ((~ (@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x1 x2) x0)) \/ (~ (@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x1 x0) y0))) \/ (@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x1 x2) y0).
Definition term227 := (~ False) -> False.
Definition term8 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 -> x1 -> x2.
Definition term17 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := imp (forall y0 : a0, ((@List.In a0 y0 x0) /\ (x1 y0)) -> x2 y0).
Definition term36 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : list a0) := (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : list a0, (forall y3 : a0, (@List.In a0 y3 y2) -> (y0 y3) -> y1 y3) -> (@List.Forall a0 y0 y2) -> @List.Forall a0 y1 y2) -> (@List.Forall a0 x0 x2) -> @List.Forall a0 x1 x2.
Definition term188 (a0 : Type') (x0 : type1402 a0) (x1 : a0) (x2 : a0) := @I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x0 x1) x2.
Definition term88 (x0 : Prop) := @eq Prop (~ (False /\ x0)).
Definition term41 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (fun y0 : Prop => ((y0 /\ (x2 /\ (x1 /\ x0))) = (y0 /\ (x1 /\ x0))) = ((y0 /\ x0) -> x1 -> x2)) x3.
Definition term154 (a0 : Type') (x0 : type1402 a0) (x1 : a0) := fun y0 : a0 => forall y1 : list a0, (forall y2 : a0, forall y3 : a0, forall y4 : a0, ((x0 y2 y3) /\ (x0 y3 y4)) -> x0 y2 y4) -> (x0 x1 y0) -> (@List.ForallOrdPairs a0 x0 y1) -> forall y2 : a0, (@List.In a0 y2 y1) -> (x0 y0 y2) -> x0 x1 y2.
Definition term153 (a0 : Type') (x0 : type1402 a0) (x1 : a0) := fun y0 : a0 => forall y1 : list a0, (forall y2 : a0, forall y3 : a0, forall y4 : a0, ((x0 y2 y3) /\ (x0 y3 y4)) -> x0 y2 y4) -> (x0 x1 y0) -> (@List.ForallOrdPairs a0 x0 y1) -> (~ (forall y2 : a0, (@List.In a0 y2 y1) -> (x0 y0 y2) -> x0 x1 y2)) -> False.
Definition term113 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) (x3 : list a0) := (@List.Forall a0 (x1 x0) (@cons a0 x2 x3)) /\ (@List.ForallOrdPairs a0 x1 (@cons a0 x2 x3)).
Definition term143 (a0 : Type') (x0 : list a0) (x1 : a0) (x2 : type1402 a0) (x3 : a0) := (@List.ForallOrdPairs a0 x2 x0) -> forall y0 : a0, (@List.In a0 y0 x0) -> (x2 x1 y0) -> x2 x3 y0.
Definition term140 (x0 : Prop) := ~ (~ x0).
Definition term222 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) (x3 : a0) := (@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x1 x0) x2) /\ (@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x1 x2) x3).
Definition term12 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := ((@List.In a0 x3 x0) /\ (x1 x3)) -> x2 x3.
Definition term55 (x0 : Prop) (x1 : Prop) (x2 : Prop) := @eq Prop (True /\ (x0 /\ (x1 /\ x2))).
Definition term134 (a0 : Type') (x0 : list a0) (x1 : a0) (x2 : type1402 a0) (x3 : a0) := ~ (forall y0 : a0, (@List.In a0 y0 x0) -> (x2 x1 y0) -> x2 x3 y0).
Definition term73 (x0 : Prop) (x1 : Prop) := @eq Prop ((False /\ (x0 /\ x1)) = (x0 /\ x1)).
Definition term70 (x0 : Prop) (x1 : Prop) := @eq Prop ((True /\ (x0 /\ x1)) = (x0 /\ x1)).
Definition term78 (x0 : Prop) := (fun y0 : Prop => (~ (y0 /\ x0)) = (x0 -> ~ y0)) True.
Definition term9 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : list a0) := ((forall y0 : a0, ((@List.In a0 y0 x2) /\ (x0 y0)) -> x1 y0) /\ (@List.Forall a0 x0 x2)) -> @List.Forall a0 x1 x2.
Definition term24 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : list a0, (forall y1 : a0, (@List.In a0 y1 y0) -> (x0 y1) -> x1 y1) -> (@List.Forall a0 x0 y0) -> @List.Forall a0 x1 y0.
Definition term112 (a0 : Type') (x0 : type1402 a0) (x1 : a0) (x2 : a0) (x3 : list a0) := @List.ForallOrdPairs a0 x0 (@cons a0 x1 (@cons a0 x2 x3)).
Definition term202 (a0 : Type') (x0 : type1402 a0) (x1 : a0) (x2 : a0) := (fun y0 : a0 => forall y1 : a0, ((~ (@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x0 x1) y0)) \/ (~ (@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x0 y0) y1))) \/ (@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x0 x1) y1)) x2.
Definition term110 (a0 : Type') (x0 : type1402 a0) (x1 : a0) (x2 : list a0) := @List.ForallOrdPairs a0 x0 (@cons a0 x1 x2).
Definition term96 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, (x0 /\ (x1 /\ y0)) = ((x0 /\ x1) /\ y0).
Definition term3 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0).
Definition term32 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : list a0, (forall y3 : a0, (@List.In a0 y3 y2) -> (y0 y3) -> y1 y3) -> (@List.Forall a0 y0 y2) -> @List.Forall a0 y1 y2.
Definition term31 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : list a0, ((forall y3 : a0, ((@List.In a0 y3 y2) /\ (y0 y3)) -> y1 y3) /\ (@List.Forall a0 y0 y2)) -> @List.Forall a0 y1 y2.
Definition term190 (a0 : Type') (x0 : type1402 a0) (x1 : a0) (x2 : a0) := or (~ (x0 x1 x2)).
Definition term98 (x0 : Prop) := fun y0 : Prop => forall y1 : Prop, (x0 /\ (y0 /\ y1)) = ((x0 /\ y0) /\ y1).
Definition term131 (x0 : Prop) := (~ x0) -> False.
Definition term223 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) (x3 : a0) := imp (~ ((~ (@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x1 x0) x2)) \/ (~ (@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x1 x2) x3)))).
Definition term40 (x0 : Prop) (x1 : Prop) (x2 : Prop) := fun y0 : Prop => ((y0 /\ (x2 /\ (x1 /\ x0))) = (y0 /\ (x1 /\ x0))) = ((y0 /\ x0) -> x1 -> x2).
Definition term16 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := forall y0 : a0, (@List.In a0 y0 x0) -> (x1 y0) -> x2 y0.
Definition term119 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) (x3 : list a0) := and ((x1 x2 x0) /\ (@List.Forall a0 (x1 x2) x3)).
Definition term80 (x0 : Prop) := x0 -> ~ True.
Definition term18 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := imp (forall y0 : a0, (@List.In a0 y0 x0) -> (x1 y0) -> x2 y0).
Definition term230 (a0 : Type') (x0 : a0) (x1 : type1402 a0) := (fun y0 : type1402 a0 => forall y1 : a0, forall y2 : list a0, (forall y3 : a0, forall y4 : a0, forall y5 : a0, ((y0 y3 y4) /\ (y0 y4 y5)) -> y0 y3 y5) -> (y0 x0 y1) -> (@List.ForallOrdPairs a0 y0 y2) -> (~ (forall y3 : a0, (@List.In a0 y3 y2) -> (y0 y1 y3) -> y0 x0 y3)) -> False) x1.
Definition term22 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : list a0 => (forall y1 : a0, (@List.In a0 y1 y0) -> (x0 y1) -> x1 y1) -> (@List.Forall a0 x0 y0) -> @List.Forall a0 x1 y0.
Definition term75 (x0 : Prop) (x1 : Prop) := x0 -> ~ x1.
Definition term33 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, forall y2 : list a0, (forall y3 : a0, (@List.In a0 y3 y2) -> (y0 y3) -> y1 y3) -> (@List.Forall a0 y0 y2) -> @List.Forall a0 y1 y2) x0.
Definition term90 (x0 : Prop) (x1 : Prop) (x2 : Prop) := @eq Prop ((False /\ (x0 /\ (x1 /\ x2))) = (False /\ (x1 /\ x2))).
Definition term129 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : type1402 a0) (x3 : list a0) := (x2 x0 x1) /\ (@List.ForallOrdPairs a0 x2 x3).
Definition term91 (x0 : Prop) := imp (False /\ x0).
Definition term210 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) (x3 : a0) := (@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x1 x0) x3) \/ ((~ (@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x1 x0) x2)) \/ (~ (@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x1 x2) x3))).
Definition term173 (a0 : Type') (x0 : type1402 a0) (x1 : a0) (x2 : a0) := (~ (x0 x1 x2)) -> False.
Definition term47 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := x0 /\ (x1 /\ (x2 /\ x3)).
Definition term77 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => (~ (y0 /\ x0)) = (x0 -> ~ y0)) x1.
Definition term117 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) (x3 : list a0) := (x1 x2 x0) /\ (@List.Forall a0 (x1 x2) x3).
Definition term92 (x0 : Prop) (x1 : Prop) := False -> x0 -> x1.
Definition term170 (a0 : Type') (x0 : type1402 a0) (x1 : a0) := fun y0 : a0 => forall y1 : a0, ((x0 x1 y0) /\ (x0 y0 y1)) -> x0 x1 y1.
Definition term213 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term162 (a0 : Type') := fun y0 : a0 => forall y1 : type1402 a0, forall y2 : a0, forall y3 : list a0, (forall y4 : a0, forall y5 : a0, forall y6 : a0, ((y1 y4 y5) /\ (y1 y5 y6)) -> y1 y4 y6) -> (y1 y0 y2) -> (@List.ForallOrdPairs a0 y1 y3) -> forall y4 : a0, (@List.In a0 y4 y3) -> (y1 y2 y4) -> y1 y0 y4.
Definition term161 (a0 : Type') := fun y0 : a0 => forall y1 : type1402 a0, forall y2 : a0, forall y3 : list a0, (forall y4 : a0, forall y5 : a0, forall y6 : a0, ((y1 y4 y5) /\ (y1 y5 y6)) -> y1 y4 y6) -> (y1 y0 y2) -> (@List.ForallOrdPairs a0 y1 y3) -> (~ (forall y4 : a0, (@List.In a0 y4 y3) -> (y1 y2 y4) -> y1 y0 y4)) -> False.
Definition term62 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => ((y0 /\ (x1 /\ x0)) = (x1 /\ x0)) = (x0 -> x1 -> y0)) True.
Definition term44 (x0 : Prop) (x1 : Prop) := True /\ (x0 /\ x1).
Definition term60 (x0 : Prop) (x1 : Prop) := fun y0 : Prop => ((y0 /\ (x1 /\ x0)) = (x1 /\ x0)) = (x0 -> x1 -> y0).
Definition term69 (x0 : Prop) (x1 : Prop) := @eq Prop (x0 /\ x1).
Definition term168 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) := fun y0 : a0 => ((x1 x2 x0) /\ (x1 x0 y0)) -> x1 x2 y0.
Definition term37 (a0 : Type') := (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : list a0, (forall y3 : a0, (@List.In a0 y3 y2) -> (y0 y3) -> y1 y3) -> (@List.Forall a0 y0 y2) -> @List.Forall a0 y1 y2) -> forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : list a0, (forall y3 : a0, (@List.In a0 y3 y2) -> (y0 y3) -> y1 y3) -> (@List.Forall a0 y0 y2) -> @List.Forall a0 y1 y2.
Definition term59 (x0 : Prop) := imp (True /\ x0).
Definition term54 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (False /\ x0) -> x1 -> x2.
Definition term206 (x0 : Prop) := (~ x0) -> x0.
Definition term20 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : list a0) := (forall y0 : a0, (@List.In a0 y0 x2) -> (x0 y0) -> x1 y0) -> (@List.Forall a0 x0 x2) -> @List.Forall a0 x1 x2.
Definition term10 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : list a0) := (forall y0 : a0, ((@List.In a0 y0 x2) /\ (x0 y0)) -> x1 y0) -> (@List.Forall a0 x0 x2) -> @List.Forall a0 x1 x2.
Definition term181 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) (x3 : a0) := (x1 x0 x2) /\ (x1 x2 x3).
Definition term214 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) (x3 : a0) := (~ ((~ (@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x1 x2) x0)) \/ (~ (@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x1 x0) x3)))) -> @I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x1 x2) x3.
Definition term126 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) (x3 : list a0) := (x1 x0 x2) /\ (@List.ForallOrdPairs a0 x1 (@cons a0 x2 x3)).
Definition term189 (a0 : Type') (x0 : type1402 a0) (x1 : a0) (x2 : a0) := ~ (@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x0 x1) x2).
Definition term232 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) (x3 : list a0) := (fun y0 : list a0 => (forall y1 : a0, forall y2 : a0, forall y3 : a0, ((x1 y1 y2) /\ (x1 y2 y3)) -> x1 y1 y3) -> (x1 x2 x0) -> (@List.ForallOrdPairs a0 x1 y0) -> (~ (forall y1 : a0, (@List.In a0 y1 y0) -> (x1 x0 y1) -> x1 x2 y1)) -> False) x3.
Definition term86 (x0 : Prop) := @eq Prop (~ (True /\ x0)).
Definition term204 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) (x3 : a0) := (~ (@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x1 x2) x0)) \/ ((~ (@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x1 x0) x3)) \/ (@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x1 x2) x3)).
Definition term218 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) (x3 : a0) := (~ (~ (@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x1 x0) x2))) /\ (~ (~ (@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x1 x2) x3))).
Definition term35 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : list a0) := (fun y0 : list a0 => (forall y1 : a0, (@List.In a0 y1 y0) -> (x0 y1) -> x1 y1) -> (@List.Forall a0 x0 y0) -> @List.Forall a0 x1 y0) x2.
Definition term216 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term167 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) (x3 : a0) := ((x1 x2 x0) /\ (x1 x0 x3)) -> x1 x2 x3.
Definition term103 := fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, ((y0 /\ y1) /\ y2) = (y0 /\ (y1 /\ y2)).
Definition term102 := fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, (y0 /\ (y1 /\ y2)) = ((y0 /\ y1) /\ y2).
Definition term43 (x0 : Prop) (x1 : Prop) (x2 : Prop) := True /\ (x0 /\ (x1 /\ x2)).
Definition term115 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : list a0) := (x1 x0) /\ (@List.Forall a0 x1 x2).
Definition term42 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => ((y0 /\ (x2 /\ (x1 /\ x0))) = (y0 /\ (x1 /\ x0))) = ((y0 /\ x0) -> x1 -> x2)) True.
Definition term49 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 /\ x1) -> x2 -> x3.
Definition term72 (x0 : Prop) (x1 : Prop) := ~ (x0 /\ x1).
Definition term142 (a0 : Type') (x0 : list a0) (x1 : a0) (x2 : type1402 a0) (x3 : a0) := (@List.ForallOrdPairs a0 x2 x0) -> (~ (forall y0 : a0, (@List.In a0 y0 x0) -> (x2 x1 y0) -> x2 x3 y0)) -> False.
Definition term21 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : list a0 => ((forall y1 : a0, ((@List.In a0 y1 y0) /\ (x0 y1)) -> x1 y1) /\ (@List.Forall a0 x0 y0)) -> @List.Forall a0 x1 y0.
Definition term5 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term141 (a0 : Type') (x0 : type1402 a0) (x1 : list a0) := imp (@List.ForallOrdPairs a0 x0 x1).
Definition term34 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : list a0, (forall y2 : a0, (@List.In a0 y2 y1) -> (x0 y2) -> y0 y2) -> (@List.Forall a0 x0 y1) -> @List.Forall a0 y0 y1) x1.
Definition term207 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) (x3 : a0) := (~ (@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x1 x0) x3)) \/ (@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x1 x2) x3).
Definition term99 (x0 : Prop) := fun y0 : Prop => forall y1 : Prop, ((x0 /\ y0) /\ y1) = (x0 /\ (y0 /\ y1)).
Definition term13 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := (@List.In a0 x3 x0) -> (x1 x3) -> x2 x3.
Definition term111 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : list a0) := (@List.Forall a0 (x1 x0) x2) /\ (@List.ForallOrdPairs a0 x1 x2).
Definition term199 (a0 : Type') (x0 : type1402 a0) := fun y0 : a0 => forall y1 : a0, forall y2 : a0, ((~ (@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x0 y0) y1)) \/ (~ (@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x0 y1) y2))) \/ (@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x0 y0) y2).
Definition term186 (a0 : Type') (x0 : type1402 a0) := fun y0 : a0 => forall y1 : a0, forall y2 : a0, ((~ (x0 y0 y1)) \/ (~ (x0 y1 y2))) \/ (x0 y0 y2).
Definition term172 (a0 : Type') (x0 : type1402 a0) := fun y0 : a0 => forall y1 : a0, forall y2 : a0, ((x0 y0 y1) /\ (x0 y1 y2)) -> x0 y0 y2.
Definition term194 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) (x3 : a0) := ((~ (@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x1 x2) x0)) \/ (~ (@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x1 x0) x3))) \/ (@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x1 x2) x3).
Definition term26 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => forall y1 : list a0, (forall y2 : a0, (@List.In a0 y2 y1) -> (x0 y2) -> y0 y2) -> (@List.Forall a0 x0 y1) -> @List.Forall a0 y0 y1.
Definition term219 (a0 : Type') (x0 : type1402 a0) (x1 : a0) (x2 : a0) := ~ (~ (@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x0 x1) x2)).
Definition term48 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 /\ (x1 /\ x2).
Definition term118 (a0 : Type') (x0 : type1402 a0) (x1 : a0) (x2 : a0) (x3 : list a0) := and (@List.Forall a0 (x0 x1) (@cons a0 x2 x3)).
Definition term56 (x0 : Prop) (x1 : Prop) (x2 : Prop) := @eq Prop (x0 /\ (x1 /\ x2)).
Definition term74 (x0 : Prop) (x1 : Prop) := @eq Prop (~ (x0 /\ x1)).
Definition term108 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => ((x0 /\ x1) /\ y0) = (x0 /\ (x1 /\ y0))) x2.
Definition term97 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, ((x0 /\ x1) /\ y0) = (x0 /\ (x1 /\ y0)).
Definition term123 (a0 : Type') (x0 : type1402 a0) (x1 : a0) (x2 : a0) (x3 : list a0) := @eq Prop (@List.ForallOrdPairs a0 x0 (@cons a0 x1 (@cons a0 x2 x3))).
Definition term135 (a0 : Type') (x0 : list a0) (x1 : a0) (x2 : type1402 a0) (x3 : a0) := (forall y0 : a0, forall y1 : a0, forall y2 : a0, ((x2 y0 y1) /\ (x2 y1 y2)) -> x2 y0 y2) -> (x2 x3 x1) -> (@List.ForallOrdPairs a0 x2 x0) -> (~ (forall y0 : a0, (@List.In a0 y0 x0) -> (x2 x1 y0) -> x2 x3 y0)) -> False.
Definition term120 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : type1402 a0) (x3 : list a0) := ((x2 x0 x1) /\ (@List.Forall a0 (x2 x0) x3)) /\ ((@List.Forall a0 (x2 x1) x3) /\ (@List.ForallOrdPairs a0 x2 x3)).
Definition term63 (x0 : Prop) (x1 : Prop) := x0 -> x1 -> True.
Definition term211 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) (x3 : a0) := @eq Prop ((~ (@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x1 x2) x0)) \/ ((~ (@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x1 x0) x3)) \/ (@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x1 x2) x3))).
Definition term106 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, ((y0 /\ y1) /\ y2) = (y0 /\ (y1 /\ y2))) x0.
Definition term0 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, (y0 \/ (y1 \/ y2)) = ((y0 \/ y1) \/ y2)) x0.
Definition term182 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) := fun y0 : a0 => ((~ (x1 x2 x0)) \/ (~ (x1 x0 y0))) \/ (x1 x2 y0).
Definition term234 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) (x3 : list a0) := (forall y0 : a0, forall y1 : a0, forall y2 : a0, ((x1 y0 y1) /\ (x1 y1 y2)) -> x1 y0 y2) -> (@List.ForallOrdPairs a0 x1 (@cons a0 x0 (@cons a0 x2 x3))) = ((x1 x0 x2) /\ (@List.ForallOrdPairs a0 x1 (@cons a0 x2 x3))).
Definition term124 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : type1402 a0) (x3 : list a0) := @eq Prop ((x2 x0 x1) /\ ((@List.Forall a0 (x2 x0) x3) /\ ((@List.Forall a0 (x2 x1) x3) /\ (@List.ForallOrdPairs a0 x2 x3)))).
Definition term87 (x0 : Prop) := @eq Prop (~ x0).
Definition term215 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term93 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 /\ x1) /\ x2.
Definition term158 (a0 : Type') (x0 : a0) := fun y0 : type1402 a0 => forall y1 : a0, forall y2 : list a0, (forall y3 : a0, forall y4 : a0, forall y5 : a0, ((y0 y3 y4) /\ (y0 y4 y5)) -> y0 y3 y5) -> (y0 x0 y1) -> (@List.ForallOrdPairs a0 y0 y2) -> forall y3 : a0, (@List.In a0 y3 y2) -> (y0 y1 y3) -> y0 x0 y3.
Definition term157 (a0 : Type') (x0 : a0) := fun y0 : type1402 a0 => forall y1 : a0, forall y2 : list a0, (forall y3 : a0, forall y4 : a0, forall y5 : a0, ((y0 y3 y4) /\ (y0 y4 y5)) -> y0 y3 y5) -> (y0 x0 y1) -> (@List.ForallOrdPairs a0 y0 y2) -> (~ (forall y3 : a0, (@List.In a0 y3 y2) -> (y0 y1 y3) -> y0 x0 y3)) -> False.
Definition term15 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := fun y0 : a0 => (@List.In a0 y0 x0) -> (x1 y0) -> x2 y0.
Definition term209 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) (x3 : a0) := (~ (@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x1 x0) x2)) \/ ((@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x1 x0) x3) \/ (~ (@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x1 x2) x3))).
Definition term226 (a0 : Type') (x0 : type1402 a0) (x1 : a0) (x2 : a0) := (@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x0 x1) x2) -> False.
Definition term82 (x0 : Prop) (x1 : Prop) := @eq Prop ((~ (x1 /\ x0)) = (x0 -> ~ x1)).
Definition term228 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) (x3 : a0) := (x1 x0 x3) -> x1 x2 x3.
Definition term147 (a0 : Type') (x0 : type1402 a0) := imp (forall y0 : a0, forall y1 : a0, forall y2 : a0, ((x0 y0 y1) /\ (x0 y1 y2)) -> x0 y0 y2).
Definition term237 (a0 : Type') (x0 : type1402 a0) := forall y0 : a0, forall y1 : a0, forall y2 : list a0, (forall y3 : a0, forall y4 : a0, forall y5 : a0, ((x0 y3 y4) /\ (x0 y4 y5)) -> x0 y3 y5) -> (@List.ForallOrdPairs a0 x0 (@cons a0 y0 (@cons a0 y1 y2))) = ((x0 y0 y1) /\ (@List.ForallOrdPairs a0 x0 (@cons a0 y1 y2))).
Definition term200 (a0 : Type') (x0 : type1402 a0) := forall y0 : a0, forall y1 : a0, forall y2 : a0, ((~ (@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x0 y0) y1)) \/ (~ (@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x0 y1) y2))) \/ (@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x0 y0) y2).
Definition term187 (a0 : Type') (x0 : type1402 a0) := forall y0 : a0, forall y1 : a0, forall y2 : a0, ((~ (x0 y0 y1)) \/ (~ (x0 y1 y2))) \/ (x0 y0 y2).
Definition term109 (a0 : Type') (x0 : type1402 a0) := forall y0 : a0, forall y1 : a0, forall y2 : a0, ((x0 y0 y1) /\ (x0 y1 y2)) -> x0 y0 y2.
Definition term6 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 \/ x1) \/ x2.
Definition term51 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => ((y0 /\ (x2 /\ (x1 /\ x0))) = (y0 /\ (x1 /\ x0))) = ((y0 /\ x0) -> x1 -> x2)) False.
Definition term84 (x0 : Prop) := ~ (False /\ x0).
Definition term165 (a0 : Type') (x0 : list a0) (x1 : a0) (x2 : type1402 a0) (x3 : a0) (x4 : a0) := (@List.In a0 x4 x0) -> (x2 x1 x4) -> x2 x3 x4.
Definition term139 (a0 : Type') (x0 : list a0) (x1 : a0) (x2 : type1402 a0) (x3 : a0) := ~ (~ (forall y0 : a0, (@List.In a0 y0 x0) -> (x2 x1 y0) -> x2 x3 y0)).
Definition term81 (x0 : Prop) (x1 : Prop) := @eq Prop ((fun y0 : Prop => (~ (y0 /\ x0)) = (x0 -> ~ y0)) x1).
Definition term148 (a0 : Type') (x0 : list a0) (x1 : a0) (x2 : type1402 a0) (x3 : a0) := (forall y0 : a0, forall y1 : a0, forall y2 : a0, ((x2 y0 y1) /\ (x2 y1 y2)) -> x2 y0 y2) -> (x2 x3 x1) -> (@List.ForallOrdPairs a0 x2 x0) -> forall y0 : a0, (@List.In a0 y0 x0) -> (x2 x1 y0) -> x2 x3 y0.
Definition term193 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) (x3 : a0) := or ((~ (@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x1 x0) x2)) \/ (~ (@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x1 x2) x3))).
Definition term178 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) (x3 : a0) := or ((~ (x1 x0 x2)) \/ (~ (x1 x2 x3))).
Definition term133 (a0 : Type') (x0 : list a0) (x1 : a0) (x2 : type1402 a0) (x3 : a0) := (~ (forall y0 : a0, (@List.In a0 y0 x0) -> (x2 x1 y0) -> x2 x3 y0)) -> False.
Definition term221 (a0 : Type') (x0 : type1402 a0) (x1 : a0) (x2 : a0) := and (@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x0 x1) x2).
Definition term166 (a0 : Type') (x0 : list a0) (x1 : a0) (x2 : type1402 a0) (x3 : a0) := fun y0 : a0 => (@List.In a0 y0 x0) -> (x2 x1 y0) -> x2 x3 y0.
Definition term128 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) (x3 : list a0) := ((x1 x2 x0) /\ (@List.ForallOrdPairs a0 x1 x3)) -> (@List.Forall a0 (x1 x0) x3) -> @List.Forall a0 (x1 x2) x3.
Definition term203 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) (x3 : a0) := (fun y0 : a0 => ((~ (@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x1 x2) x0)) \/ (~ (@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x1 x0) y0))) \/ (@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x1 x2) y0)) x3.
Definition term205 (a0 : Type') (x0 : type1402 a0) (x1 : a0) (x2 : a0) := (~ (@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x0 x1) x2)) -> @I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x0 x1) x2.
Definition term130 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) (x3 : list a0) := (forall y0 : a0, (@List.In a0 y0 x3) -> (x1 x0 y0) -> x1 x2 y0) -> (@List.Forall a0 (x1 x0) x3) -> @List.Forall a0 (x1 x2) x3.
Definition term231 (a0 : Type') (x0 : type1402 a0) (x1 : a0) (x2 : a0) := (fun y0 : a0 => forall y1 : list a0, (forall y2 : a0, forall y3 : a0, forall y4 : a0, ((x0 y2 y3) /\ (x0 y3 y4)) -> x0 y2 y4) -> (x0 x1 y0) -> (@List.ForallOrdPairs a0 x0 y1) -> (~ (forall y2 : a0, (@List.In a0 y2 y1) -> (x0 y0 y2) -> x0 x1 y2)) -> False) x2.
Definition term19 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : list a0) := (@List.Forall a0 x0 x2) -> @List.Forall a0 x1 x2.
Definition term53 (x0 : Prop) (x1 : Prop) := False /\ (x0 /\ x1).
Definition term39 (x0 : Prop) := (x0 = True) \/ (x0 = False).
Definition term7 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 /\ x1) -> x2.
Definition term105 := forall y0 : Prop, forall y1 : Prop, forall y2 : Prop, ((y0 /\ y1) /\ y2) = (y0 /\ (y1 /\ y2)).
Definition term104 := forall y0 : Prop, forall y1 : Prop, forall y2 : Prop, (y0 /\ (y1 /\ y2)) = ((y0 /\ y1) /\ y2).
Definition term101 (x0 : Prop) := forall y0 : Prop, forall y1 : Prop, ((x0 /\ y0) /\ y1) = (x0 /\ (y0 /\ y1)).
Definition term100 (x0 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 /\ (y0 /\ y1)) = ((x0 /\ y0) /\ y1).
Definition term1 (x0 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1).
Definition term28 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, forall y1 : list a0, (forall y2 : a0, (@List.In a0 y2 y1) -> (x0 y2) -> y0 y2) -> (@List.Forall a0 x0 y1) -> @List.Forall a0 y0 y1.
Definition term27 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, forall y1 : list a0, ((forall y2 : a0, ((@List.In a0 y2 y1) /\ (x0 y2)) -> y0 y2) /\ (@List.Forall a0 x0 y1)) -> @List.Forall a0 y0 y1.
Definition term95 (x0 : Prop) (x1 : Prop) := fun y0 : Prop => ((x0 /\ x1) /\ y0) = (x0 /\ (x1 /\ y0)).
Definition term65 (x0 : Prop) (x1 : Prop) (x2 : Prop) := @eq Prop (((x2 /\ (x1 /\ x0)) = (x1 /\ x0)) = (x0 -> x1 -> x2)).
Definition term138 (a0 : Type') (x0 : list a0) (x1 : a0) (x2 : type1402 a0) (x3 : a0) := (((forall y0 : a0, forall y1 : a0, forall y2 : a0, ((x2 y0 y1) /\ (x2 y1 y2)) -> x2 y0 y2) -> (x2 x3 x1) -> (@List.ForallOrdPairs a0 x2 x0) -> (~ (forall y0 : a0, (@List.In a0 y0 x0) -> (x2 x1 y0) -> x2 x3 y0)) -> False) -> (forall y0 : a0, forall y1 : a0, forall y2 : a0, ((x2 y0 y1) /\ (x2 y1 y2)) -> x2 y0 y2) -> (x2 x3 x1) -> (@List.ForallOrdPairs a0 x2 x0) -> (~ (forall y0 : a0, (@List.In a0 y0 x0) -> (x2 x1 y0) -> x2 x3 y0)) -> False) -> ((forall y0 : a0, forall y1 : a0, forall y2 : a0, ((x2 y0 y1) /\ (x2 y1 y2)) -> x2 y0 y2) -> (x2 x3 x1) -> (@List.ForallOrdPairs a0 x2 x0) -> (~ (forall y0 : a0, (@List.In a0 y0 x0) -> (x2 x1 y0) -> x2 x3 y0)) -> False) -> (forall y0 : a0, forall y1 : a0, forall y2 : a0, ((x2 y0 y1) /\ (x2 y1 y2)) -> x2 y0 y2) -> (x2 x3 x1) -> (@List.ForallOrdPairs a0 x2 x0) -> (~ (forall y0 : a0, (@List.In a0 y0 x0) -> (x2 x1 y0) -> x2 x3 y0)) -> False.
Definition term57 (x0 : Prop) (x1 : Prop) (x2 : Prop) := @eq Prop ((True /\ (x0 /\ (x1 /\ x2))) = (True /\ (x1 /\ x2))).
Definition term85 (x0 : Prop) := x0 -> ~ False.
Definition term11 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := forall y0 : a0, ((@List.In a0 y0 x0) /\ (x1 y0)) -> x2 y0.
Definition term121 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : type1402 a0) (x3 : list a0) := (x2 x0 x1) /\ ((@List.Forall a0 (x2 x0) x3) /\ ((@List.Forall a0 (x2 x1) x3) /\ (@List.ForallOrdPairs a0 x2 x3))).
Definition term183 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) := forall y0 : a0, ((~ (x1 x2 x0)) \/ (~ (x1 x0 y0))) \/ (x1 x2 y0).
Definition term149 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) := fun y0 : list a0 => (forall y1 : a0, forall y2 : a0, forall y3 : a0, ((x1 y1 y2) /\ (x1 y2 y3)) -> x1 y1 y3) -> (x1 x2 x0) -> (@List.ForallOrdPairs a0 x1 y0) -> (~ (forall y1 : a0, (@List.In a0 y1 y0) -> (x1 x0 y1) -> x1 x2 y1)) -> False.
Definition term169 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) := forall y0 : a0, ((x1 x2 x0) /\ (x1 x0 y0)) -> x1 x2 y0.
Definition term212 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) (x3 : a0) := @eq Prop ((@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x1 x0) x3) \/ ((~ (@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x1 x0) x2)) \/ (~ (@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x1 x2) x3)))).
Definition term208 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) (x3 : a0) := (@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x1 x0) x3) \/ (~ (@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x1 x2) x3)).
Definition term127 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : type1402 a0) (x3 : list a0) := (x2 x0 x1) /\ ((@List.Forall a0 (x2 x1) x3) /\ (@List.ForallOrdPairs a0 x2 x3)).
Definition term46 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := @eq Prop ((fun y0 : Prop => ((y0 /\ (x2 /\ (x1 /\ x0))) = (y0 /\ (x1 /\ x0))) = ((y0 /\ x0) -> x1 -> x2)) x3).
Definition term23 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : list a0, ((forall y1 : a0, ((@List.In a0 y1 y0) /\ (x0 y1)) -> x1 y1) /\ (@List.Forall a0 x0 y0)) -> @List.Forall a0 x1 y0.
Definition term197 (a0 : Type') (x0 : type1402 a0) (x1 : a0) := fun y0 : a0 => forall y1 : a0, ((~ (@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x0 x1) y0)) \/ (~ (@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x0 y0) y1))) \/ (@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x0 x1) y1).
Definition term198 (a0 : Type') (x0 : type1402 a0) (x1 : a0) := forall y0 : a0, forall y1 : a0, ((~ (@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x0 x1) y0)) \/ (~ (@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x0 y0) y1))) \/ (@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x0 x1) y1).
Definition term185 (a0 : Type') (x0 : type1402 a0) (x1 : a0) := forall y0 : a0, forall y1 : a0, ((~ (x0 x1 y0)) \/ (~ (x0 y0 y1))) \/ (x0 x1 y1).
Definition term171 (a0 : Type') (x0 : type1402 a0) (x1 : a0) := forall y0 : a0, forall y1 : a0, ((x0 x1 y0) /\ (x0 y0 y1)) -> x0 x1 y1.
Definition term150 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) := fun y0 : list a0 => (forall y1 : a0, forall y2 : a0, forall y3 : a0, ((x1 y1 y2) /\ (x1 y2 y3)) -> x1 y1 y3) -> (x1 x2 x0) -> (@List.ForallOrdPairs a0 x1 y0) -> forall y1 : a0, (@List.In a0 y1 y0) -> (x1 x0 y1) -> x1 x2 y1.
Definition term83 (x0 : Prop) := (fun y0 : Prop => (~ (y0 /\ x0)) = (x0 -> ~ y0)) False.
Definition term136 (a0 : Type') (x0 : list a0) (x1 : a0) (x2 : type1402 a0) (x3 : a0) := ((forall y0 : a0, forall y1 : a0, forall y2 : a0, ((x2 y0 y1) /\ (x2 y1 y2)) -> x2 y0 y2) -> (x2 x3 x1) -> (@List.ForallOrdPairs a0 x2 x0) -> (~ (forall y0 : a0, (@List.In a0 y0 x0) -> (x2 x1 y0) -> x2 x3 y0)) -> False) -> (forall y0 : a0, forall y1 : a0, forall y2 : a0, ((x2 y0 y1) /\ (x2 y1 y2)) -> x2 y0 y2) -> (x2 x3 x1) -> (@List.ForallOrdPairs a0 x2 x0) -> (~ (forall y0 : a0, (@List.In a0 y0 x0) -> (x2 x1 y0) -> x2 x3 y0)) -> False.
Definition term217 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) (x3 : a0) := ~ ((~ (@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x1 x0) x2)) \/ (~ (@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x1 x2) x3))).
Definition term52 (x0 : Prop) (x1 : Prop) (x2 : Prop) := False /\ (x0 /\ (x1 /\ x2)).
Definition term50 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := @eq Prop (((x0 /\ (x3 /\ (x2 /\ x1))) = (x0 /\ (x2 /\ x1))) = ((x0 /\ x1) -> x2 -> x3)).
Definition term180 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) (x3 : a0) := ((~ (x1 x2 x0)) \/ (~ (x1 x0 x3))) \/ (x1 x2 x3).
Definition term89 (x0 : Prop) (x1 : Prop) (x2 : Prop) := @eq Prop (False /\ (x0 /\ (x1 /\ x2))).
Definition term122 (a0 : Type') (x0 : type1402 a0) (x1 : a0) (x2 : list a0) := @List.Forall a0 (x0 x1) x2.
Definition term137 (a0 : Type') (x0 : list a0) (x1 : a0) (x2 : type1402 a0) (x3 : a0) := (((forall y0 : a0, forall y1 : a0, forall y2 : a0, ((x2 y0 y1) /\ (x2 y1 y2)) -> x2 y0 y2) -> (x2 x3 x1) -> (@List.ForallOrdPairs a0 x2 x0) -> (~ (forall y0 : a0, (@List.In a0 y0 x0) -> (x2 x1 y0) -> x2 x3 y0)) -> False) -> (forall y0 : a0, forall y1 : a0, forall y2 : a0, ((x2 y0 y1) /\ (x2 y1 y2)) -> x2 y0 y2) -> (x2 x3 x1) -> (@List.ForallOrdPairs a0 x2 x0) -> (~ (forall y0 : a0, (@List.In a0 y0 x0) -> (x2 x1 y0) -> x2 x3 y0)) -> False) -> (forall y0 : a0, forall y1 : a0, forall y2 : a0, ((x2 y0 y1) /\ (x2 y1 y2)) -> x2 y0 y2) -> (x2 x3 x1) -> (@List.ForallOrdPairs a0 x2 x0) -> (~ (forall y0 : a0, (@List.In a0 y0 x0) -> (x2 x1 y0) -> x2 x3 y0)) -> False.
Definition term107 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((x0 /\ y0) /\ y1) = (x0 /\ (y0 /\ y1))) x1.
Definition term2 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1)) x1.
Definition term132 (a0 : Type') (x0 : list a0) (x1 : a0) (x2 : type1402 a0) (x3 : a0) := forall y0 : a0, (@List.In a0 y0 x0) -> (x2 x1 y0) -> x2 x3 y0.
Definition term201 (a0 : Type') (x0 : type1402 a0) (x1 : a0) := (fun y0 : a0 => forall y1 : a0, forall y2 : a0, ((~ (@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x0 y0) y1)) \/ (~ (@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x0 y1) y2))) \/ (@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x0 y0) y2)) x1.
Definition term174 (a0 : Type') (x0 : type1402 a0) (x1 : a0) (x2 : a0) := ~ (x0 x1 x2).
Definition term191 (a0 : Type') (x0 : type1402 a0) (x1 : a0) (x2 : a0) := or (~ (@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x0 x1) x2)).
Definition term196 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) := forall y0 : a0, ((~ (@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x1 x2) x0)) \/ (~ (@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x1 x0) y0))) \/ (@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x1 x2) y0).
Definition term67 (x0 : Prop) (x1 : Prop) := x0 -> x1 -> False.
Definition term25 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => forall y1 : list a0, ((forall y2 : a0, ((@List.In a0 y2 y1) /\ (x0 y2)) -> y0 y2) /\ (@List.Forall a0 x0 y1)) -> @List.Forall a0 y0 y1.
Definition term238 (a0 : Type') := forall y0 : type1402 a0, forall y1 : a0, forall y2 : a0, forall y3 : list a0, (forall y4 : a0, forall y5 : a0, forall y6 : a0, ((y0 y4 y5) /\ (y0 y5 y6)) -> y0 y4 y6) -> (@List.ForallOrdPairs a0 y0 (@cons a0 y1 (@cons a0 y2 y3))) = ((y0 y1 y2) /\ (@List.ForallOrdPairs a0 y0 (@cons a0 y2 y3))).
Definition term160 (a0 : Type') (x0 : a0) := forall y0 : type1402 a0, forall y1 : a0, forall y2 : list a0, (forall y3 : a0, forall y4 : a0, forall y5 : a0, ((y0 y3 y4) /\ (y0 y4 y5)) -> y0 y3 y5) -> (y0 x0 y1) -> (@List.ForallOrdPairs a0 y0 y2) -> forall y3 : a0, (@List.In a0 y3 y2) -> (y0 y1 y3) -> y0 x0 y3.
Definition term159 (a0 : Type') (x0 : a0) := forall y0 : type1402 a0, forall y1 : a0, forall y2 : list a0, (forall y3 : a0, forall y4 : a0, forall y5 : a0, ((y0 y3 y4) /\ (y0 y4 y5)) -> y0 y3 y5) -> (y0 x0 y1) -> (@List.ForallOrdPairs a0 y0 y2) -> (~ (forall y3 : a0, (@List.In a0 y3 y2) -> (y0 y1 y3) -> y0 x0 y3)) -> False.
Definition term71 (x0 : Prop) (x1 : Prop) := @eq Prop (False /\ (x0 /\ x1)).
Definition term192 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) (x3 : a0) := (~ (@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x1 x0) x2)) \/ (~ (@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x1 x2) x3)).
Definition term179 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) (x3 : a0) := (~ ((x1 x2 x0) /\ (x1 x0 x3))) \/ (x1 x2 x3).
Definition term30 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, forall y2 : list a0, (forall y3 : a0, (@List.In a0 y3 y2) -> (y0 y3) -> y1 y3) -> (@List.Forall a0 y0 y2) -> @List.Forall a0 y1 y2.
Definition term29 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, forall y2 : list a0, ((forall y3 : a0, ((@List.In a0 y3 y2) /\ (y0 y3)) -> y1 y3) /\ (@List.Forall a0 y0 y2)) -> @List.Forall a0 y1 y2.
Definition term175 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) (x3 : a0) := ~ ((x1 x0 x2) /\ (x1 x2 x3)).
Definition term45 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (True /\ x0) -> x1 -> x2.
Definition term61 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => ((y0 /\ (x1 /\ x0)) = (x1 /\ x0)) = (x0 -> x1 -> y0)) x2.
Definition term144 (a0 : Type') (x0 : type1402 a0) (x1 : a0) (x2 : a0) := imp (x0 x1 x2).
Definition term184 (a0 : Type') (x0 : type1402 a0) (x1 : a0) := fun y0 : a0 => forall y1 : a0, ((~ (x0 x1 y0)) \/ (~ (x0 y0 y1))) \/ (x0 x1 y1).
Definition term4 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0)) x2.
Definition term145 (a0 : Type') (x0 : list a0) (x1 : a0) (x2 : type1402 a0) (x3 : a0) := (x2 x3 x1) -> (@List.ForallOrdPairs a0 x2 x0) -> (~ (forall y0 : a0, (@List.In a0 y0 x0) -> (x2 x1 y0) -> x2 x3 y0)) -> False.
Definition term233 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) (x3 : list a0) := (@List.Forall a0 (x1 x0) x3) -> @List.Forall a0 (x1 x2) x3.
Definition term146 (a0 : Type') (x0 : list a0) (x1 : a0) (x2 : type1402 a0) (x3 : a0) := (x2 x3 x1) -> (@List.ForallOrdPairs a0 x2 x0) -> forall y0 : a0, (@List.In a0 y0 x0) -> (x2 x1 y0) -> x2 x3 y0.
Definition term235 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) := forall y0 : list a0, (forall y1 : a0, forall y2 : a0, forall y3 : a0, ((x1 y1 y2) /\ (x1 y2 y3)) -> x1 y1 y3) -> (@List.ForallOrdPairs a0 x1 (@cons a0 x0 (@cons a0 x2 y0))) = ((x1 x0 x2) /\ (@List.ForallOrdPairs a0 x1 (@cons a0 x2 y0))).
Definition term152 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) := forall y0 : list a0, (forall y1 : a0, forall y2 : a0, forall y3 : a0, ((x1 y1 y2) /\ (x1 y2 y3)) -> x1 y1 y3) -> (x1 x2 x0) -> (@List.ForallOrdPairs a0 x1 y0) -> forall y1 : a0, (@List.In a0 y1 y0) -> (x1 x0 y1) -> x1 x2 y1.
Definition term151 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) := forall y0 : list a0, (forall y1 : a0, forall y2 : a0, forall y3 : a0, ((x1 y1 y2) /\ (x1 y2 y3)) -> x1 y1 y3) -> (x1 x2 x0) -> (@List.ForallOrdPairs a0 x1 y0) -> (~ (forall y1 : a0, (@List.In a0 y1 y0) -> (x1 x0 y1) -> x1 x2 y1)) -> False.
Definition term76 (x0 : Prop) := fun y0 : Prop => (~ (y0 /\ x0)) = (x0 -> ~ y0).
Definition term38 (x0 : Prop) := (fun y0 : Prop => (y0 = True) \/ (y0 = False)) x0.
Definition term58 (x0 : Prop) (x1 : Prop) (x2 : Prop) := @eq Prop ((x0 /\ (x1 /\ x2)) = (x1 /\ x2)).
Definition term125 (a0 : Type') (x0 : type1402 a0) (x1 : a0) (x2 : a0) := and (x0 x1 x2).
Definition term116 (a0 : Type') (x0 : type1402 a0) (x1 : a0) (x2 : a0) (x3 : list a0) := @List.Forall a0 (x0 x1) (@cons a0 x2 x3).
Definition term236 (a0 : Type') (x0 : a0) (x1 : type1402 a0) := forall y0 : a0, forall y1 : list a0, (forall y2 : a0, forall y3 : a0, forall y4 : a0, ((x1 y2 y3) /\ (x1 y3 y4)) -> x1 y2 y4) -> (@List.ForallOrdPairs a0 x1 (@cons a0 x0 (@cons a0 y0 y1))) = ((x1 x0 y0) /\ (@List.ForallOrdPairs a0 x1 (@cons a0 y0 y1))).
Definition term156 (a0 : Type') (x0 : type1402 a0) (x1 : a0) := forall y0 : a0, forall y1 : list a0, (forall y2 : a0, forall y3 : a0, forall y4 : a0, ((x0 y2 y3) /\ (x0 y3 y4)) -> x0 y2 y4) -> (x0 x1 y0) -> (@List.ForallOrdPairs a0 x0 y1) -> forall y2 : a0, (@List.In a0 y2 y1) -> (x0 y0 y2) -> x0 x1 y2.
Definition term155 (a0 : Type') (x0 : type1402 a0) (x1 : a0) := forall y0 : a0, forall y1 : list a0, (forall y2 : a0, forall y3 : a0, forall y4 : a0, ((x0 y2 y3) /\ (x0 y3 y4)) -> x0 y2 y4) -> (x0 x1 y0) -> (@List.ForallOrdPairs a0 x0 y1) -> (~ (forall y2 : a0, (@List.In a0 y2 y1) -> (x0 y0 y2) -> x0 x1 y2)) -> False.
Definition term225 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) (x3 : a0) := ((@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x1 x2) x0) /\ (@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x1 x0) x3)) -> @I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x1 x2) x3.
Definition term229 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : type1402 a0, forall y2 : a0, forall y3 : list a0, (forall y4 : a0, forall y5 : a0, forall y6 : a0, ((y1 y4 y5) /\ (y1 y5 y6)) -> y1 y4 y6) -> (y1 y0 y2) -> (@List.ForallOrdPairs a0 y1 y3) -> (~ (forall y4 : a0, (@List.In a0 y4 y3) -> (y1 y2 y4) -> y1 y0 y4)) -> False) x0.
Definition term176 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) (x3 : a0) := (~ (x1 x0 x2)) \/ (~ (x1 x2 x3)).
Definition term114 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : list a0) := @List.Forall a0 x0 (@cons a0 x1 x2).
Definition term68 (x0 : Prop) (x1 : Prop) := @eq Prop (True /\ (x0 /\ x1)).
Definition term14 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := fun y0 : a0 => ((@List.In a0 y0 x0) /\ (x1 y0)) -> x2 y0.
Definition term220 (a0 : Type') (x0 : type1402 a0) (x1 : a0) (x2 : a0) := and (~ (~ (@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x0 x1) x2))).
Definition term177 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) (x3 : a0) := or (~ ((x1 x0 x2) /\ (x1 x2 x3))).
Definition term94 (x0 : Prop) (x1 : Prop) := fun y0 : Prop => (x0 /\ (x1 /\ y0)) = ((x0 /\ x1) /\ y0).
Definition term224 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) (x3 : a0) := imp ((@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x1 x0) x2) /\ (@I (a0 -> Prop) (@I (a0 -> a0 -> Prop) x1 x2) x3)).
Definition term64 (x0 : Prop) (x1 : Prop) (x2 : Prop) := @eq Prop ((fun y0 : Prop => ((y0 /\ (x1 /\ x0)) = (x1 /\ x0)) = (x0 -> x1 -> y0)) x2).
Definition term79 (x0 : Prop) := ~ (True /\ x0).
