Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term94 (a0 : Type') (x0 : list a0) := fun y0 : a0 -> Prop => forall y1 : a0, forall y2 : a0 -> Prop, (((forall y3 : a0, ((@List.In a0 y3 x0) /\ (y2 y3)) -> y0 y3) /\ (@List.Forall a0 y2 x0)) -> @List.Forall a0 y0 x0) -> ((forall y3 : a0, (((y3 = y1) \/ (@List.In a0 y3 x0)) /\ (y2 y3)) -> y0 y3) /\ ((y2 y1) /\ (@List.Forall a0 y2 x0))) -> (y0 y1) /\ (@List.Forall a0 y0 x0).
Definition term93 (a0 : Type') (x0 : list a0) := fun y0 : a0 -> Prop => forall y1 : a0, forall y2 : a0 -> Prop, (((forall y3 : a0, ((@List.In a0 y3 x0) /\ (y2 y3)) -> y0 y3) /\ (@List.Forall a0 y2 x0)) -> @List.Forall a0 y0 x0) -> (~ (((forall y3 : a0, (((y3 = y1) \/ (@List.In a0 y3 x0)) /\ (y2 y3)) -> y0 y3) /\ ((y2 y1) /\ (@List.Forall a0 y2 x0))) -> (y0 y1) /\ (@List.Forall a0 y0 x0))) -> False.
Definition term174 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0 -> Prop) (x3 : a0) := or (((~ (x3 = x0)) /\ (~ (@List.In a0 x3 x1))) \/ (~ (x2 x3))).
Definition term204 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : list a0) := ((((@List.In a0 x0 x3) /\ (@I (a0 -> Prop) x1 x0)) /\ (~ (@I (a0 -> Prop) x2 x0))) \/ (~ (@List.Forall a0 x1 x3))) \/ (@List.Forall a0 x2 x3).
Definition term161 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : list a0) := ((((@List.In a0 x0 x3) /\ (x1 x0)) /\ (~ (x2 x0))) \/ (~ (@List.Forall a0 x1 x3))) \/ (@List.Forall a0 x2 x3).
Definition term248 := (~ False) -> False.
Definition term218 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := (~ (x3 = x0)) \/ ((~ (@I (a0 -> Prop) x1 x3)) \/ (@I (a0 -> Prop) x2 x3)).
Definition term80 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) (x3 : list a0) := (((((forall y0 : a0, ((@List.In a0 y0 x3) /\ (x0 y0)) -> x2 y0) /\ (@List.Forall a0 x0 x3)) -> @List.Forall a0 x2 x3) -> (~ (((forall y0 : a0, (((y0 = x1) \/ (@List.In a0 y0 x3)) /\ (x0 y0)) -> x2 y0) /\ ((x0 x1) /\ (@List.Forall a0 x0 x3))) -> (x2 x1) /\ (@List.Forall a0 x2 x3))) -> False) -> (((forall y0 : a0, ((@List.In a0 y0 x3) /\ (x0 y0)) -> x2 y0) /\ (@List.Forall a0 x0 x3)) -> @List.Forall a0 x2 x3) -> (~ (((forall y0 : a0, (((y0 = x1) \/ (@List.In a0 y0 x3)) /\ (x0 y0)) -> x2 y0) /\ ((x0 x1) /\ (@List.Forall a0 x0 x3))) -> (x2 x1) /\ (@List.Forall a0 x2 x3))) -> False) -> (((forall y0 : a0, ((@List.In a0 y0 x3) /\ (x0 y0)) -> x2 y0) /\ (@List.Forall a0 x0 x3)) -> @List.Forall a0 x2 x3) -> (~ (((forall y0 : a0, (((y0 = x1) \/ (@List.In a0 y0 x3)) /\ (x0 y0)) -> x2 y0) /\ ((x0 x1) /\ (@List.Forall a0 x0 x3))) -> (x2 x1) /\ (@List.Forall a0 x2 x3))) -> False.
Definition term250 (a0 : Type') (x0 : a0 -> Prop) (x1 : list a0) (x2 : a0 -> Prop) (x3 : a0) := (~ (@I (a0 -> Prop) x0 x3)) \/ ((~ (@List.In a0 x3 x1)) \/ (@I (a0 -> Prop) x2 x3)).
Definition term193 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := or (~ (x0 x1)).
Definition term20 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) (x3 : list a0) := ((fun y0 : list a0 => ((forall y1 : a0, ((@List.In a0 y1 y0) /\ (x0 y1)) -> x1 y1) /\ (@List.Forall a0 x0 y0)) -> @List.Forall a0 x1 y0) x3) -> (fun y0 : list a0 => ((forall y1 : a0, ((@List.In a0 y1 y0) /\ (x0 y1)) -> x1 y1) /\ (@List.Forall a0 x0 y0)) -> @List.Forall a0 x1 y0) (@cons a0 x2 x3).
Definition term212 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0) := (~ (@List.In a0 x2 x0)) \/ (~ (@I (a0 -> Prop) x1 x2)).
Definition term27 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => forall y1 : list a0, (((forall y2 : a0, ((@List.In a0 y2 y1) /\ (x0 y2)) -> x1 y2) /\ (@List.Forall a0 x0 y1)) -> @List.Forall a0 x1 y1) -> ((forall y2 : a0, ((@List.In a0 y2 (@cons a0 y0 y1)) /\ (x0 y2)) -> x1 y2) /\ (@List.Forall a0 x0 (@cons a0 y0 y1))) -> @List.Forall a0 x1 (@cons a0 y0 y1).
Definition term260 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := (~ ((~ (@List.In a0 x3 x0)) \/ (~ (@I (a0 -> Prop) x1 x3)))) -> @I (a0 -> Prop) x2 x3.
Definition term232 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := (~ ((~ (x3 = x0)) \/ (~ (@I (a0 -> Prop) x1 x3)))) -> @I (a0 -> Prop) x2 x3.
Definition term83 (x0 : Prop) := ~ (~ x0).
Definition term164 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : list a0) := exists y0 : a0, ((((@List.In a0 y0 x2) /\ (x0 y0)) /\ (~ (x1 y0))) \/ (~ (@List.Forall a0 x0 x2))) \/ (@List.Forall a0 x1 x2).
Definition term101 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := ((@List.In a0 x3 x0) /\ (x1 x3)) -> x2 x3.
Definition term257 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : list a0) := (~ (@I (a0 -> Prop) x0 x1)) \/ (~ (@List.In a0 x1 x2)).
Definition term153 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : list a0) := fun y0 : a0 => (fun y1 : a0 => (((@List.In a0 y1 x2) /\ (x1 y1)) /\ (~ (x0 y1))) \/ (~ (@List.Forall a0 x1 x2))) y0.
Definition term15 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : list a0) := ((forall y0 : a0, ((@List.In a0 y0 x2) /\ (x0 y0)) -> x1 y0) /\ (@List.Forall a0 x0 x2)) -> @List.Forall a0 x1 x2.
Definition term160 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) (x3 : list a0) := ((fun y0 : a0 => (((@List.In a0 y0 x3) /\ (x0 y0)) /\ (~ (x2 y0))) \/ (~ (@List.Forall a0 x0 x3))) x1) \/ (@List.Forall a0 x2 x3).
Definition term109 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := ~ (((@List.In a0 x3 x0) /\ (x1 x3)) -> x2 x3).
Definition term32 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := imp (((fun y0 : list a0 => ((forall y1 : a0, ((@List.In a0 y1 y0) /\ (x0 y1)) -> x1 y1) /\ (@List.Forall a0 x0 y0)) -> @List.Forall a0 x1 y0) (@nil a0)) /\ (forall y0 : a0, forall y1 : list a0, ((fun y2 : list a0 => ((forall y3 : a0, ((@List.In a0 y3 y2) /\ (x0 y3)) -> x1 y3) /\ (@List.Forall a0 x0 y2)) -> @List.Forall a0 x1 y2) y1) -> (fun y2 : list a0 => ((forall y3 : a0, ((@List.In a0 y3 y2) /\ (x0 y3)) -> x1 y3) /\ (@List.Forall a0 x0 y2)) -> @List.Forall a0 x1 y2) (@cons a0 y0 y1))).
Definition term262 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0) := (~ (~ (@List.In a0 x2 x0))) /\ (~ (~ (@I (a0 -> Prop) x1 x2))).
Definition term236 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := (~ (~ (x2 = x0))) /\ (~ (~ (@I (a0 -> Prop) x1 x2))).
Definition term37 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((((forall y0 : a0, ((@List.In a0 y0 (@nil a0)) /\ (x0 y0)) -> x1 y0) /\ (@List.Forall a0 x0 (@nil a0))) -> @List.Forall a0 x1 (@nil a0)) /\ (forall y0 : a0, forall y1 : list a0, (((forall y2 : a0, ((@List.In a0 y2 y1) /\ (x0 y2)) -> x1 y2) /\ (@List.Forall a0 x0 y1)) -> @List.Forall a0 x1 y1) -> ((forall y2 : a0, ((@List.In a0 y2 (@cons a0 y0 y1)) /\ (x0 y2)) -> x1 y2) /\ (@List.Forall a0 x0 (@cons a0 y0 y1))) -> @List.Forall a0 x1 (@cons a0 y0 y1))) -> forall y0 : list a0, ((forall y1 : a0, ((@List.In a0 y1 y0) /\ (x0 y1)) -> x1 y1) /\ (@List.Forall a0 x0 y0)) -> @List.Forall a0 x1 y0.
Definition term48 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term120 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := exists y0 : a0, ((@List.In a0 y0 x0) /\ (x1 y0)) /\ (~ (x2 y0)).
Definition term167 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (x0 x1).
Definition term246 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ((x2 = x2) /\ (@I (a0 -> Prop) x0 x2)) -> @I (a0 -> Prop) x1 x2.
Definition term112 (a0 : Type') (x0 : a0 -> Prop) := ~ (all x0).
Definition term79 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) (x3 : list a0) := ((((forall y0 : a0, ((@List.In a0 y0 x3) /\ (x0 y0)) -> x2 y0) /\ (@List.Forall a0 x0 x3)) -> @List.Forall a0 x2 x3) -> (~ (((forall y0 : a0, (((y0 = x1) \/ (@List.In a0 y0 x3)) /\ (x0 y0)) -> x2 y0) /\ ((x0 x1) /\ (@List.Forall a0 x0 x3))) -> (x2 x1) /\ (@List.Forall a0 x2 x3))) -> False) -> (((forall y0 : a0, ((@List.In a0 y0 x3) /\ (x0 y0)) -> x2 y0) /\ (@List.Forall a0 x0 x3)) -> @List.Forall a0 x2 x3) -> (~ (((forall y0 : a0, (((y0 = x1) \/ (@List.In a0 y0 x3)) /\ (x0 y0)) -> x2 y0) /\ ((x0 x1) /\ (@List.Forall a0 x0 x3))) -> (x2 x1) /\ (@List.Forall a0 x2 x3))) -> False.
Definition term10 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : list a0 => ((forall y1 : a0, ((@List.In a0 y1 y0) /\ (x0 y1)) -> x1 y1) /\ (@List.Forall a0 x0 y0)) -> @List.Forall a0 x1 y0) (@nil a0).
Definition term3 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0).
Definition term275 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : list a0, ((forall y3 : a0, ((@List.In a0 y3 y2) /\ (y0 y3)) -> y1 y3) /\ (@List.Forall a0 y0 y2)) -> @List.Forall a0 y1 y2.
Definition term75 (x0 : Prop) := (~ x0) -> False.
Definition term8 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (((fun y0 : list a0 => ((forall y1 : a0, ((@List.In a0 y1 y0) /\ (x0 y1)) -> x1 y1) /\ (@List.Forall a0 x0 y0)) -> @List.Forall a0 x1 y0) (@nil a0)) /\ (forall y0 : a0, forall y1 : list a0, ((fun y2 : list a0 => ((forall y3 : a0, ((@List.In a0 y3 y2) /\ (x0 y3)) -> x1 y3) /\ (@List.Forall a0 x0 y2)) -> @List.Forall a0 x1 y2) y1) -> (fun y2 : list a0 => ((forall y3 : a0, ((@List.In a0 y3 y2) /\ (x0 y3)) -> x1 y3) /\ (@List.Forall a0 x0 y2)) -> @List.Forall a0 x1 y2) (@cons a0 y0 y1))) -> forall y0 : list a0, (fun y1 : list a0 => ((forall y2 : a0, ((@List.In a0 y2 y1) /\ (x0 y2)) -> x1 y2) /\ (@List.Forall a0 x0 y1)) -> @List.Forall a0 x1 y1) y0.
Definition term131 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) \/ x1.
Definition term265 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0) := imp (~ ((~ (@List.In a0 x2 x0)) \/ (~ (@I (a0 -> Prop) x1 x2)))).
Definition term242 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := imp (~ ((~ (x2 = x0)) \/ (~ (@I (a0 -> Prop) x1 x2)))).
Definition term7 (a0 : Type') (x0 : type1143 a0) := ((x0 (@nil a0)) /\ (forall y0 : a0, forall y1 : list a0, (x0 y1) -> x0 (@cons a0 y0 y1))) -> forall y0 : list a0, x0 y0.
Definition term270 (a0 : Type') (x0 : list a0) := (fun y0 : list a0 => forall y1 : a0 -> Prop, forall y2 : a0, forall y3 : a0 -> Prop, (((forall y4 : a0, ((@List.In a0 y4 y0) /\ (y3 y4)) -> y1 y4) /\ (@List.Forall a0 y3 y0)) -> @List.Forall a0 y1 y0) -> (~ (((forall y4 : a0, (((y4 = y2) \/ (@List.In a0 y4 y0)) /\ (y3 y4)) -> y1 y4) /\ ((y3 y2) /\ (@List.Forall a0 y3 y0))) -> (y1 y2) /\ (@List.Forall a0 y1 y0))) -> False) x0.
Definition term176 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0 -> Prop) (x3 : a0 -> Prop) (x4 : a0) := (((~ (x4 = x0)) /\ (~ (@List.In a0 x4 x1))) \/ (~ (x2 x4))) \/ (x3 x4).
Definition term76 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) (x3 : list a0) := (~ (((forall y0 : a0, (((y0 = x1) \/ (@List.In a0 y0 x3)) /\ (x0 y0)) -> x2 y0) /\ ((x0 x1) /\ (@List.Forall a0 x0 x3))) -> (x2 x1) /\ (@List.Forall a0 x2 x3))) -> False.
Definition term42 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ((@List.In a0 x2 (@nil a0)) /\ (x0 x2)) -> x1 x2.
Definition term217 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := ((~ (@List.In a0 x3 x0)) \/ (~ (@I (a0 -> Prop) x1 x3))) \/ (@I (a0 -> Prop) x2 x3).
Definition term216 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := ((~ (x3 = x0)) \/ (~ (@I (a0 -> Prop) x1 x3))) \/ (@I (a0 -> Prop) x2 x3).
Definition term271 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0, forall y2 : a0 -> Prop, (((forall y3 : a0, ((@List.In a0 y3 x0) /\ (y2 y3)) -> y0 y3) /\ (@List.Forall a0 y2 x0)) -> @List.Forall a0 y0 x0) -> (~ (((forall y3 : a0, (((y3 = y1) \/ (@List.In a0 y3 x0)) /\ (y2 y3)) -> y0 y3) /\ ((y2 y1) /\ (@List.Forall a0 y2 x0))) -> (y0 y1) /\ (@List.Forall a0 y0 x0))) -> False) x1.
Definition term100 (a0 : Type') := forall y0 : list a0, forall y1 : a0 -> Prop, forall y2 : a0, forall y3 : a0 -> Prop, (((forall y4 : a0, ((@List.In a0 y4 y0) /\ (y3 y4)) -> y1 y4) /\ (@List.Forall a0 y3 y0)) -> @List.Forall a0 y1 y0) -> ((forall y4 : a0, (((y4 = y2) \/ (@List.In a0 y4 y0)) /\ (y3 y4)) -> y1 y4) /\ ((y3 y2) /\ (@List.Forall a0 y3 y0))) -> (y1 y2) /\ (@List.Forall a0 y1 y0).
Definition term99 (a0 : Type') := forall y0 : list a0, forall y1 : a0 -> Prop, forall y2 : a0, forall y3 : a0 -> Prop, (((forall y4 : a0, ((@List.In a0 y4 y0) /\ (y3 y4)) -> y1 y4) /\ (@List.Forall a0 y3 y0)) -> @List.Forall a0 y1 y0) -> (~ (((forall y4 : a0, (((y4 = y2) \/ (@List.In a0 y4 y0)) /\ (y3 y4)) -> y1 y4) /\ ((y3 y2) /\ (@List.Forall a0 y3 y0))) -> (y1 y2) /\ (@List.Forall a0 y1 y0))) -> False.
Definition term85 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : list a0) := fun y0 : a0 -> Prop => (((forall y1 : a0, ((@List.In a0 y1 x2) /\ (y0 y1)) -> x1 y1) /\ (@List.Forall a0 y0 x2)) -> @List.Forall a0 x1 x2) -> (~ (((forall y1 : a0, (((y1 = x0) \/ (@List.In a0 y1 x2)) /\ (y0 y1)) -> x1 y1) /\ ((y0 x0) /\ (@List.Forall a0 y0 x2))) -> (x1 x0) /\ (@List.Forall a0 x1 x2))) -> False.
Definition term155 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : list a0) := or (exists y0 : a0, (fun y1 : a0 => (((@List.In a0 y1 x2) /\ (x1 y1)) /\ (~ (x0 y1))) \/ (~ (@List.Forall a0 x1 x2))) y0).
Definition term138 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := or (exists y0 : a0, (fun y1 : a0 => ((@List.In a0 y1 x0) /\ (x1 y1)) /\ (~ (x2 y1))) y0).
Definition term47 (a0 : Type') := forall y0 : a0, True.
Definition term81 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) (x3 : list a0) := (((((forall y0 : a0, ((@List.In a0 y0 x3) /\ (x0 y0)) -> x2 y0) /\ (@List.Forall a0 x0 x3)) -> @List.Forall a0 x2 x3) -> (~ (((forall y0 : a0, (((y0 = x1) \/ (@List.In a0 y0 x3)) /\ (x0 y0)) -> x2 y0) /\ ((x0 x1) /\ (@List.Forall a0 x0 x3))) -> (x2 x1) /\ (@List.Forall a0 x2 x3))) -> False) -> (((forall y0 : a0, ((@List.In a0 y0 x3) /\ (x0 y0)) -> x2 y0) /\ (@List.Forall a0 x0 x3)) -> @List.Forall a0 x2 x3) -> (~ (((forall y0 : a0, (((y0 = x1) \/ (@List.In a0 y0 x3)) /\ (x0 y0)) -> x2 y0) /\ ((x0 x1) /\ (@List.Forall a0 x0 x3))) -> (x2 x1) /\ (@List.Forall a0 x2 x3))) -> False) -> ((((forall y0 : a0, ((@List.In a0 y0 x3) /\ (x0 y0)) -> x2 y0) /\ (@List.Forall a0 x0 x3)) -> @List.Forall a0 x2 x3) -> (~ (((forall y0 : a0, (((y0 = x1) \/ (@List.In a0 y0 x3)) /\ (x0 y0)) -> x2 y0) /\ ((x0 x1) /\ (@List.Forall a0 x0 x3))) -> (x2 x1) /\ (@List.Forall a0 x2 x3))) -> False) -> (((forall y0 : a0, ((@List.In a0 y0 x3) /\ (x0 y0)) -> x2 y0) /\ (@List.Forall a0 x0 x3)) -> @List.Forall a0 x2 x3) -> (~ (((forall y0 : a0, (((y0 = x1) \/ (@List.In a0 y0 x3)) /\ (x0 y0)) -> x2 y0) /\ ((x0 x1) /\ (@List.Forall a0 x0 x3))) -> (x2 x1) /\ (@List.Forall a0 x2 x3))) -> False.
Definition term143 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) (x3 : list a0) := ((fun y0 : a0 => ((@List.In a0 y0 x3) /\ (x2 y0)) /\ (~ (x0 y0))) x1) \/ (~ (@List.Forall a0 x2 x3)).
Definition term13 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := and (((forall y0 : a0, ((@List.In a0 y0 (@nil a0)) /\ (x0 y0)) -> x1 y0) /\ (@List.Forall a0 x0 (@nil a0))) -> @List.Forall a0 x1 (@nil a0)).
Definition term22 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := fun y0 : list a0 => ((fun y1 : list a0 => ((forall y2 : a0, ((@List.In a0 y2 y1) /\ (x0 y2)) -> x1 y2) /\ (@List.Forall a0 x0 y1)) -> @List.Forall a0 x1 y1) y0) -> (fun y1 : list a0 => ((forall y2 : a0, ((@List.In a0 y2 y1) /\ (x0 y2)) -> x1 y2) /\ (@List.Forall a0 x0 y1)) -> @List.Forall a0 x1 y1) (@cons a0 x2 y0).
Definition term34 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : list a0 => (fun y1 : list a0 => ((forall y2 : a0, ((@List.In a0 y2 y1) /\ (x0 y2)) -> x1 y2) /\ (@List.Forall a0 x0 y1)) -> @List.Forall a0 x1 y1) y0.
Definition term58 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0 -> Prop) (x3 : a0) := imp ((@List.In a0 x3 (@cons a0 x0 x1)) /\ (x2 x3)).
Definition term231 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term59 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0 -> Prop) (x3 : a0) := imp (((x3 = x0) \/ (@List.In a0 x3 x1)) /\ (x2 x3)).
Definition term223 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (~ (@I (a0 -> Prop) x0 x1)) -> @I (a0 -> Prop) x0 x1.
Definition term135 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := (fun y0 : a0 => ((@List.In a0 y0 x0) /\ (x1 y0)) /\ (~ (x2 y0))) x3.
Definition term65 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0 -> Prop) (x3 : a0 -> Prop) := forall y0 : a0, (((y0 = x0) \/ (@List.In a0 y0 x1)) /\ (x2 y0)) -> x3 y0.
Definition term64 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0 -> Prop) (x3 : a0 -> Prop) := forall y0 : a0, ((@List.In a0 y0 (@cons a0 x0 x1)) /\ (x2 y0)) -> x3 y0.
Definition term263 (a0 : Type') (x0 : a0) (x1 : list a0) := ~ (~ (@List.In a0 x0 x1)).
Definition term222 (x0 : Prop) := (~ x0) -> x0.
Definition term267 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := ((@List.In a0 x3 x0) /\ (@I (a0 -> Prop) x1 x3)) -> @I (a0 -> Prop) x2 x3.
Definition term244 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := ((x3 = x0) /\ (@I (a0 -> Prop) x1 x3)) -> @I (a0 -> Prop) x2 x3.
Definition term269 (a0 : Type') (x0 : a0 -> Prop) (x1 : list a0) := (@List.Forall a0 x0 x1) -> False.
Definition term170 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0 -> Prop) (x3 : a0) := (~ ((x3 = x0) \/ (@List.In a0 x3 x1))) \/ (~ (x2 x3)).
Definition term98 (a0 : Type') := fun y0 : list a0 => forall y1 : a0 -> Prop, forall y2 : a0, forall y3 : a0 -> Prop, (((forall y4 : a0, ((@List.In a0 y4 y0) /\ (y3 y4)) -> y1 y4) /\ (@List.Forall a0 y3 y0)) -> @List.Forall a0 y1 y0) -> ((forall y4 : a0, (((y4 = y2) \/ (@List.In a0 y4 y0)) /\ (y3 y4)) -> y1 y4) /\ ((y3 y2) /\ (@List.Forall a0 y3 y0))) -> (y1 y2) /\ (@List.Forall a0 y1 y0).
Definition term97 (a0 : Type') := fun y0 : list a0 => forall y1 : a0 -> Prop, forall y2 : a0, forall y3 : a0 -> Prop, (((forall y4 : a0, ((@List.In a0 y4 y0) /\ (y3 y4)) -> y1 y4) /\ (@List.Forall a0 y3 y0)) -> @List.Forall a0 y1 y0) -> (~ (((forall y4 : a0, (((y4 = y2) \/ (@List.In a0 y4 y0)) /\ (y3 y4)) -> y1 y4) /\ ((y3 y2) /\ (@List.Forall a0 y3 y0))) -> (y1 y2) /\ (@List.Forall a0 y1 y0))) -> False.
Definition term26 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => forall y1 : list a0, ((fun y2 : list a0 => ((forall y3 : a0, ((@List.In a0 y3 y2) /\ (x0 y3)) -> x1 y3) /\ (@List.Forall a0 x0 y2)) -> @List.Forall a0 x1 y2) y1) -> (fun y2 : list a0 => ((forall y3 : a0, ((@List.In a0 y3 y2) /\ (x0 y3)) -> x1 y3) /\ (@List.Forall a0 x0 y2)) -> @List.Forall a0 x1 y2) (@cons a0 y0 y1).
Definition term54 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) := and (@List.In a0 x0 (@cons a0 x1 x2)).
Definition term234 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term88 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : list a0) := forall y0 : a0 -> Prop, (((forall y1 : a0, ((@List.In a0 y1 x2) /\ (y0 y1)) -> x1 y1) /\ (@List.Forall a0 y0 x2)) -> @List.Forall a0 x1 x2) -> ((forall y1 : a0, (((y1 = x0) \/ (@List.In a0 y1 x2)) /\ (y0 y1)) -> x1 y1) /\ ((y0 x0) /\ (@List.Forall a0 y0 x2))) -> (x1 x0) /\ (@List.Forall a0 x1 x2).
Definition term245 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (x1 = x1) /\ (@I (a0 -> Prop) x0 x1).
Definition term87 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : list a0) := forall y0 : a0 -> Prop, (((forall y1 : a0, ((@List.In a0 y1 x2) /\ (y0 y1)) -> x1 y1) /\ (@List.Forall a0 y0 x2)) -> @List.Forall a0 x1 x2) -> (~ (((forall y1 : a0, (((y1 = x0) \/ (@List.In a0 y1 x2)) /\ (y0 y1)) -> x1 y1) /\ ((y0 x0) /\ (@List.Forall a0 y0 x2))) -> (x1 x0) /\ (@List.Forall a0 x1 x2))) -> False.
Definition term69 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : list a0) := (x1 x0) /\ (@List.Forall a0 x1 x2).
Definition term142 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := or (((@List.In a0 x3 x0) /\ (x1 x3)) /\ (~ (x2 x3))).
Definition term226 (a0 : Type') (x0 : a0) (x1 : a0) := or (~ (x0 = x1)).
Definition term122 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := or (~ (forall y0 : a0, ((@List.In a0 y0 x0) /\ (x1 y0)) -> x2 y0)).
Definition term172 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0 -> Prop) (x3 : a0) := ~ (((x3 = x0) \/ (@List.In a0 x3 x1)) /\ (x2 x3)).
Definition term252 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : list a0) := (@I (a0 -> Prop) x0 x1) \/ (~ (@List.In a0 x1 x2)).
Definition term89 (a0 : Type') (x0 : a0 -> Prop) (x1 : list a0) := fun y0 : a0 => forall y1 : a0 -> Prop, (((forall y2 : a0, ((@List.In a0 y2 x1) /\ (y1 y2)) -> x0 y2) /\ (@List.Forall a0 y1 x1)) -> @List.Forall a0 x0 x1) -> (~ (((forall y2 : a0, (((y2 = y0) \/ (@List.In a0 y2 x1)) /\ (y1 y2)) -> x0 y2) /\ ((y1 y0) /\ (@List.Forall a0 y1 x1))) -> (x0 y0) /\ (@List.Forall a0 x0 x1))) -> False.
Definition term128 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : list a0) := or ((exists y0 : a0, ((@List.In a0 y0 x2) /\ (x1 y0)) /\ (~ (x0 y0))) \/ (~ (@List.Forall a0 x1 x2))).
Definition term9 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : list a0 => ((forall y1 : a0, ((@List.In a0 y1 y0) /\ (x0 y1)) -> x1 y1) /\ (@List.Forall a0 x0 y0)) -> @List.Forall a0 x1 y0.
Definition term255 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := @eq Prop ((~ (@List.In a0 x3 x0)) \/ ((~ (@I (a0 -> Prop) x1 x3)) \/ (@I (a0 -> Prop) x2 x3))).
Definition term229 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := @eq Prop ((~ (x3 = x0)) \/ ((~ (@I (a0 -> Prop) x1 x3)) \/ (@I (a0 -> Prop) x2 x3))).
Definition term157 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : list a0) := @eq Prop ((exists y0 : a0, (((@List.In a0 y0 x2) /\ (x0 y0)) /\ (~ (x1 y0))) \/ (~ (@List.Forall a0 x0 x2))) \/ (@List.Forall a0 x1 x2)).
Definition term156 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : list a0) := @eq Prop ((exists y0 : a0, (fun y1 : a0 => (((@List.In a0 y1 x2) /\ (x0 y1)) /\ (~ (x1 y1))) \/ (~ (@List.Forall a0 x0 x2))) y0) \/ (@List.Forall a0 x1 x2)).
Definition term272 (a0 : Type') (x0 : a0 -> Prop) (x1 : list a0) (x2 : a0) := (fun y0 : a0 => forall y1 : a0 -> Prop, (((forall y2 : a0, ((@List.In a0 y2 x1) /\ (y1 y2)) -> x0 y2) /\ (@List.Forall a0 y1 x1)) -> @List.Forall a0 x0 x1) -> (~ (((forall y2 : a0, (((y2 = y0) \/ (@List.In a0 y2 x1)) /\ (y1 y2)) -> x0 y2) /\ ((y1 y0) /\ (@List.Forall a0 y1 x1))) -> (x0 y0) /\ (@List.Forall a0 x0 x1))) -> False) x2.
Definition term5 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term33 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := imp ((((forall y0 : a0, ((@List.In a0 y0 (@nil a0)) /\ (x0 y0)) -> x1 y0) /\ (@List.Forall a0 x0 (@nil a0))) -> @List.Forall a0 x1 (@nil a0)) /\ (forall y0 : a0, forall y1 : list a0, (((forall y2 : a0, ((@List.In a0 y2 y1) /\ (x0 y2)) -> x1 y2) /\ (@List.Forall a0 x0 y1)) -> @List.Forall a0 x1 y1) -> ((forall y2 : a0, ((@List.In a0 y2 (@cons a0 y0 y1)) /\ (x0 y2)) -> x1 y2) /\ (@List.Forall a0 x0 (@cons a0 y0 y1))) -> @List.Forall a0 x1 (@cons a0 y0 y1))).
Definition term180 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) (x3 : list a0) := (forall y0 : a0, (((~ (y0 = x1)) /\ (~ (@List.In a0 y0 x3))) \/ (~ (x2 y0))) \/ (x0 y0)) /\ ((x2 x1) /\ (@List.Forall a0 x2 x3)).
Definition term71 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) (x3 : list a0) := (forall y0 : a0, (((y0 = x1) \/ (@List.In a0 y0 x3)) /\ (x2 y0)) -> x0 y0) /\ ((x2 x1) /\ (@List.Forall a0 x2 x3)).
Definition term127 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : list a0) := or (~ ((forall y0 : a0, ((@List.In a0 y0 x2) /\ (x1 y0)) -> x0 y0) /\ (@List.Forall a0 x1 x2))).
Definition term154 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : list a0) := exists y0 : a0, (fun y1 : a0 => (((@List.In a0 y1 x2) /\ (x1 y1)) /\ (~ (x0 y1))) \/ (~ (@List.Forall a0 x1 x2))) y0.
Definition term137 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := exists y0 : a0, (fun y1 : a0 => ((@List.In a0 y1 x0) /\ (x1 y1)) /\ (~ (x2 y1))) y0.
Definition term253 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) (x3 : list a0) := (~ (@I (a0 -> Prop) x0 x2)) \/ ((@I (a0 -> Prop) x1 x2) \/ (~ (@List.In a0 x2 x3))).
Definition term118 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := fun y0 : a0 => ~ ((fun y1 : a0 => ((@List.In a0 y1 x0) /\ (x1 y1)) -> x2 y1) y0).
Definition term38 (a0 : Type') (x0 : a0) := and (@List.In a0 x0 (@nil a0)).
Definition term219 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := (~ (@List.In a0 x3 x0)) \/ ((~ (@I (a0 -> Prop) x1 x3)) \/ (@I (a0 -> Prop) x2 x3)).
Definition term196 (a0 : Type') (x0 : a0) (x1 : list a0) := and (@List.In a0 x0 x1).
Definition term179 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0 -> Prop) (x3 : a0 -> Prop) := and (forall y0 : a0, (((~ (y0 = x0)) /\ (~ (@List.In a0 y0 x1))) \/ (~ (x2 y0))) \/ (x3 y0)).
Definition term104 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := and (forall y0 : a0, ((@List.In a0 y0 x0) /\ (x1 y0)) -> x2 y0).
Definition term67 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0 -> Prop) (x3 : a0 -> Prop) := and (forall y0 : a0, (((y0 = x0) \/ (@List.In a0 y0 x1)) /\ (x2 y0)) -> x3 y0).
Definition term66 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0 -> Prop) (x3 : a0 -> Prop) := and (forall y0 : a0, ((@List.In a0 y0 (@cons a0 x0 x1)) /\ (x2 y0)) -> x3 y0).
Definition term49 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := and (forall y0 : a0, ((@List.In a0 y0 (@nil a0)) /\ (x0 y0)) -> x1 y0).
Definition term110 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := ((@List.In a0 x3 x0) /\ (x1 x3)) /\ (~ (x2 x3)).
Definition term188 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0 -> Prop) (x3 : a0 -> Prop) (x4 : a0) := (((~ (x4 = x0)) /\ (~ (@List.In a0 x4 x1))) \/ (~ (@I (a0 -> Prop) x2 x4))) \/ (@I (a0 -> Prop) x3 x4).
Definition term211 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := (~ (x2 = x0)) \/ (~ (@I (a0 -> Prop) x1 x2)).
Definition term136 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := fun y0 : a0 => (fun y1 : a0 => ((@List.In a0 y1 x0) /\ (x1 y1)) /\ (~ (x2 y1))) y0.
Definition term208 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0 -> Prop) (x3 : a0) := or (((~ (x3 = x0)) \/ (~ (@I (a0 -> Prop) x2 x3))) /\ ((~ (@List.In a0 x3 x1)) \/ (~ (@I (a0 -> Prop) x2 x3)))).
Definition term190 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0 -> Prop) (x3 : a0 -> Prop) := forall y0 : a0, (((~ (y0 = x0)) /\ (~ (@List.In a0 y0 x1))) \/ (~ (@I (a0 -> Prop) x2 y0))) \/ (@I (a0 -> Prop) x3 y0).
Definition term221 (a0 : Type') (x0 : a0) := ~ (x0 = x0).
Definition term105 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : list a0) := (forall y0 : a0, ((@List.In a0 y0 x2) /\ (x1 y0)) -> x0 y0) /\ (@List.Forall a0 x1 x2).
Definition term254 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) (x3 : list a0) := (@I (a0 -> Prop) x0 x2) \/ ((~ (@I (a0 -> Prop) x1 x2)) \/ (~ (@List.In a0 x2 x3))).
Definition term214 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0 -> Prop) (x3 : a0 -> Prop) := forall y0 : a0, (((~ (y0 = x0)) \/ (~ (@I (a0 -> Prop) x2 y0))) \/ (@I (a0 -> Prop) x3 y0)) /\ (((~ (@List.In a0 y0 x1)) \/ (~ (@I (a0 -> Prop) x2 y0))) \/ (@I (a0 -> Prop) x3 y0)).
Definition term165 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) := ~ ((x1 = x0) \/ (@List.In a0 x1 x2)).
Definition term18 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) (x3 : list a0) := (fun y0 : list a0 => ((forall y1 : a0, ((@List.In a0 y1 y0) /\ (x0 y1)) -> x1 y1) /\ (@List.Forall a0 x0 y0)) -> @List.Forall a0 x1 y0) (@cons a0 x2 x3).
Definition term121 (a0 : Type') (x0 : a0 -> Prop) (x1 : list a0) := ~ (@List.Forall a0 x0 x1).
Definition term194 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := or (~ (@I (a0 -> Prop) x0 x1)).
Definition term125 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : list a0) := (exists y0 : a0, ((@List.In a0 y0 x2) /\ (x1 y0)) /\ (~ (x0 y0))) \/ (~ (@List.Forall a0 x1 x2)).
Definition term106 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : list a0) := imp ((forall y0 : a0, ((@List.In a0 y0 x2) /\ (x1 y0)) -> x0 y0) /\ (@List.Forall a0 x1 x2)).
Definition term0 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, (y0 \/ (y1 \/ y2)) = ((y0 \/ y1) \/ y2)) x0.
Definition term31 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (((forall y0 : a0, ((@List.In a0 y0 (@nil a0)) /\ (x0 y0)) -> x1 y0) /\ (@List.Forall a0 x0 (@nil a0))) -> @List.Forall a0 x1 (@nil a0)) /\ (forall y0 : a0, forall y1 : list a0, (((forall y2 : a0, ((@List.In a0 y2 y1) /\ (x0 y2)) -> x1 y2) /\ (@List.Forall a0 x0 y1)) -> @List.Forall a0 x1 y1) -> ((forall y2 : a0, ((@List.In a0 y2 (@cons a0 y0 y1)) /\ (x0 y2)) -> x1 y2) /\ (@List.Forall a0 x0 (@cons a0 y0 y1))) -> @List.Forall a0 x1 (@cons a0 y0 y1)).
Definition term46 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, ((@List.In a0 y0 (@nil a0)) /\ (x0 y0)) -> x1 y0.
Definition term240 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (~ (@I (a0 -> Prop) x0 x1)).
Definition term12 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := and ((fun y0 : list a0 => ((forall y1 : a0, ((@List.In a0 y1 y0) /\ (x0 y1)) -> x1 y1) /\ (@List.Forall a0 x0 y0)) -> @List.Forall a0 x1 y0) (@nil a0)).
Definition term145 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : list a0) := fun y0 : a0 => ((fun y1 : a0 => ((@List.In a0 y1 x2) /\ (x1 y1)) /\ (~ (x0 y1))) y0) \/ (~ (@List.Forall a0 x1 x2)).
Definition term168 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) := or (~ ((x1 = x0) \/ (@List.In a0 x1 x2))).
Definition term24 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := forall y0 : list a0, ((fun y1 : list a0 => ((forall y2 : a0, ((@List.In a0 y2 y1) /\ (x0 y2)) -> x1 y2) /\ (@List.Forall a0 x0 y1)) -> @List.Forall a0 x1 y1) y0) -> (fun y1 : list a0 => ((forall y2 : a0, ((@List.In a0 y2 y1) /\ (x0 y2)) -> x1 y2) /\ (@List.Forall a0 x0 y1)) -> @List.Forall a0 x1 y1) (@cons a0 x2 y0).
Definition term233 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term173 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0 -> Prop) (x3 : a0) := or (~ (((x3 = x0) \/ (@List.In a0 x3 x1)) /\ (x2 x3))).
Definition term113 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0, ~ (x0 y0).
Definition term17 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : list a0) := imp (((forall y0 : a0, ((@List.In a0 y0 x2) /\ (x0 y0)) -> x1 y0) /\ (@List.Forall a0 x0 x2)) -> @List.Forall a0 x1 x2).
Definition term126 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : list a0) := ~ ((forall y0 : a0, ((@List.In a0 y0 x2) /\ (x1 y0)) -> x0 y0) /\ (@List.Forall a0 x1 x2)).
Definition term215 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0 -> Prop) (x3 : a0 -> Prop) (x4 : a0) := (fun y0 : a0 => (((~ (y0 = x0)) \/ (~ (@I (a0 -> Prop) x2 y0))) \/ (@I (a0 -> Prop) x3 y0)) /\ (((~ (@List.In a0 y0 x1)) \/ (~ (@I (a0 -> Prop) x2 y0))) \/ (@I (a0 -> Prop) x3 y0))) x4.
Definition term251 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0) := (~ (@List.In a0 x2 x0)) \/ (@I (a0 -> Prop) x1 x2).
Definition term45 (a0 : Type') := fun y0 : a0 => True.
Definition term108 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : list a0) := ~ ((x1 x0) /\ (@List.Forall a0 x1 x2)).
Definition term201 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := or (((@List.In a0 x3 x0) /\ (@I (a0 -> Prop) x1 x3)) /\ (~ (@I (a0 -> Prop) x2 x3))).
Definition term182 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := and (x0 x1).
Definition term134 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : list a0) := exists y0 : a0, ((fun y1 : a0 => ((@List.In a0 y1 x2) /\ (x1 y1)) /\ (~ (x0 y1))) y0) \/ (~ (@List.Forall a0 x1 x2)).
Definition term61 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0 -> Prop) (x3 : a0 -> Prop) (x4 : a0) := (((x4 = x0) \/ (@List.In a0 x4 x1)) /\ (x2 x4)) -> x3 x4.
Definition term60 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0 -> Prop) (x3 : a0 -> Prop) (x4 : a0) := ((@List.In a0 x4 (@cons a0 x0 x1)) /\ (x2 x4)) -> x3 x4.
Definition term192 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) (x3 : list a0) := (forall y0 : a0, (((~ (y0 = x1)) /\ (~ (@List.In a0 y0 x3))) \/ (~ (@I (a0 -> Prop) x2 y0))) \/ (@I (a0 -> Prop) x0 y0)) /\ ((@I (a0 -> Prop) x2 x1) /\ (@List.Forall a0 x2 x3)).
Definition term175 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0 -> Prop) (x3 : a0 -> Prop) (x4 : a0) := (~ (((x4 = x0) \/ (@List.In a0 x4 x1)) /\ (x2 x4))) \/ (x3 x4).
Definition term57 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0 -> Prop) (x3 : a0) := ((x3 = x0) \/ (@List.In a0 x3 x1)) /\ (x2 x3).
Definition term19 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) (x3 : list a0) := ((forall y0 : a0, ((@List.In a0 y0 (@cons a0 x2 x3)) /\ (x0 y0)) -> x1 y0) /\ (@List.Forall a0 x0 (@cons a0 x2 x3))) -> @List.Forall a0 x1 (@cons a0 x2 x3).
Definition term63 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0 -> Prop) (x3 : a0 -> Prop) := fun y0 : a0 => (((y0 = x0) \/ (@List.In a0 y0 x1)) /\ (x2 y0)) -> x3 y0.
Definition term62 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0 -> Prop) (x3 : a0 -> Prop) := fun y0 : a0 => ((@List.In a0 y0 (@cons a0 x0 x1)) /\ (x2 y0)) -> x3 y0.
Definition term130 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : list a0) := ((exists y0 : a0, ((@List.In a0 y0 x2) /\ (x0 y0)) /\ (~ (x1 y0))) \/ (~ (@List.Forall a0 x0 x2))) \/ (@List.Forall a0 x1 x2).
Definition term202 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) (x3 : list a0) := (((@List.In a0 x1 x3) /\ (@I (a0 -> Prop) x2 x1)) /\ (~ (@I (a0 -> Prop) x0 x1))) \/ (~ (@List.Forall a0 x2 x3)).
Definition term51 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := imp ((forall y0 : a0, ((@List.In a0 y0 (@nil a0)) /\ (x1 y0)) -> x0 y0) /\ (@List.Forall a0 x1 (@nil a0))).
Definition term186 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0 -> Prop) (x3 : a0) := ((~ (x3 = x0)) /\ (~ (@List.In a0 x3 x1))) \/ (~ (@I (a0 -> Prop) x2 x3)).
Definition term25 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := forall y0 : list a0, (((forall y1 : a0, ((@List.In a0 y1 y0) /\ (x0 y1)) -> x1 y1) /\ (@List.Forall a0 x0 y0)) -> @List.Forall a0 x1 y0) -> ((forall y1 : a0, ((@List.In a0 y1 (@cons a0 x2 y0)) /\ (x0 y1)) -> x1 y1) /\ (@List.Forall a0 x0 (@cons a0 x2 y0))) -> @List.Forall a0 x1 (@cons a0 x2 y0).
Definition term268 (a0 : Type') (x0 : a0 -> Prop) (x1 : list a0) := (~ (@List.Forall a0 x0 x1)) -> @List.Forall a0 x0 x1.
Definition term6 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 \/ x1) \/ x2.
Definition term273 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : list a0) (x3 : a0 -> Prop) := (fun y0 : a0 -> Prop => (((forall y1 : a0, ((@List.In a0 y1 x2) /\ (y0 y1)) -> x1 y1) /\ (@List.Forall a0 y0 x2)) -> @List.Forall a0 x1 x2) -> (~ (((forall y1 : a0, (((y1 = x0) \/ (@List.In a0 y1 x2)) /\ (y0 y1)) -> x1 y1) /\ ((y0 x0) /\ (@List.Forall a0 y0 x2))) -> (x1 x0) /\ (@List.Forall a0 x1 x2))) -> False) x3.
Definition term205 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0 -> Prop) (x3 : a0) := ((~ (x3 = x0)) \/ (~ (@I (a0 -> Prop) x2 x3))) /\ ((~ (@List.In a0 x3 x1)) \/ (~ (@I (a0 -> Prop) x2 x3))).
Definition term258 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := or (@I (a0 -> Prop) x0 x1).
Definition term132 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) \/ x1.
Definition term53 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) := (x1 = x0) \/ (@List.In a0 x1 x2).
Definition term189 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0 -> Prop) (x3 : a0 -> Prop) := fun y0 : a0 => (((~ (y0 = x0)) /\ (~ (@List.In a0 y0 x1))) \/ (~ (@I (a0 -> Prop) x2 y0))) \/ (@I (a0 -> Prop) x3 y0).
Definition term50 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, ((@List.In a0 y0 (@nil a0)) /\ (x1 y0)) -> x0 y0) /\ (@List.Forall a0 x1 (@nil a0)).
Definition term90 (a0 : Type') (x0 : a0 -> Prop) (x1 : list a0) := fun y0 : a0 => forall y1 : a0 -> Prop, (((forall y2 : a0, ((@List.In a0 y2 x1) /\ (y1 y2)) -> x0 y2) /\ (@List.Forall a0 y1 x1)) -> @List.Forall a0 x0 x1) -> ((forall y2 : a0, (((y2 = y0) \/ (@List.In a0 y2 x1)) /\ (y1 y2)) -> x0 y2) /\ ((y1 y0) /\ (@List.Forall a0 y1 x1))) -> (x0 y0) /\ (@List.Forall a0 x0 x1).
Definition term213 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0 -> Prop) (x3 : a0 -> Prop) := fun y0 : a0 => (((~ (y0 = x0)) \/ (~ (@I (a0 -> Prop) x2 y0))) \/ (@I (a0 -> Prop) x3 y0)) /\ (((~ (@List.In a0 y0 x1)) \/ (~ (@I (a0 -> Prop) x2 y0))) \/ (@I (a0 -> Prop) x3 y0)).
Definition term266 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0) := imp ((@List.In a0 x2 x0) /\ (@I (a0 -> Prop) x1 x2)).
Definition term209 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0 -> Prop) (x3 : a0 -> Prop) (x4 : a0) := (((~ (x4 = x0)) \/ (~ (@I (a0 -> Prop) x2 x4))) /\ ((~ (@List.In a0 x4 x1)) \/ (~ (@I (a0 -> Prop) x2 x4)))) \/ (@I (a0 -> Prop) x3 x4).
Definition term256 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) (x3 : list a0) := @eq Prop ((@I (a0 -> Prop) x0 x2) \/ ((~ (@I (a0 -> Prop) x1 x2)) \/ (~ (@List.In a0 x2 x3)))).
Definition term78 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) (x3 : list a0) := (((forall y0 : a0, ((@List.In a0 y0 x3) /\ (x0 y0)) -> x2 y0) /\ (@List.Forall a0 x0 x3)) -> @List.Forall a0 x2 x3) -> (~ (((forall y0 : a0, (((y0 = x1) \/ (@List.In a0 y0 x3)) /\ (x0 y0)) -> x2 y0) /\ ((x0 x1) /\ (@List.Forall a0 x0 x3))) -> (x2 x1) /\ (@List.Forall a0 x2 x3))) -> False.
Definition term239 (a0 : Type') (x0 : a0) (x1 : a0) := and (x0 = x1).
Definition term158 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : list a0) (x3 : a0) := or ((fun y0 : a0 => (((@List.In a0 y0 x2) /\ (x1 y0)) /\ (~ (x0 y0))) \/ (~ (@List.Forall a0 x1 x2))) x3).
Definition term141 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := or ((fun y0 : a0 => ((@List.In a0 y0 x0) /\ (x1 y0)) /\ (~ (x2 y0))) x3).
Definition term140 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : list a0) := @eq Prop ((exists y0 : a0, ((@List.In a0 y0 x2) /\ (x1 y0)) /\ (~ (x0 y0))) \/ (~ (@List.Forall a0 x1 x2))).
Definition term139 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : list a0) := @eq Prop ((exists y0 : a0, (fun y1 : a0 => ((@List.In a0 y1 x2) /\ (x1 y1)) /\ (~ (x0 y1))) y0) \/ (~ (@List.Forall a0 x1 x2))).
Definition term1 (x0 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1).
Definition term264 (a0 : Type') (x0 : a0) (x1 : list a0) := and (~ (~ (@List.In a0 x0 x1))).
Definition term238 (a0 : Type') (x0 : a0) (x1 : a0) := and (~ (~ (x0 = x1))).
Definition term185 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (@I (a0 -> Prop) x0 x1).
Definition term206 (a0 : Type') (x0 : a0) (x1 : a0) := ~ (x0 = x1).
Definition term11 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((forall y0 : a0, ((@List.In a0 y0 (@nil a0)) /\ (x0 y0)) -> x1 y0) /\ (@List.Forall a0 x0 (@nil a0))) -> @List.Forall a0 x1 (@nil a0).
Definition term274 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, forall y1 : list a0, ((forall y2 : a0, ((@List.In a0 y2 y1) /\ (x0 y2)) -> y0 y2) /\ (@List.Forall a0 x0 y1)) -> @List.Forall a0 y0 y1.
Definition term147 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : list a0) := exists y0 : a0, (((@List.In a0 y0 x2) /\ (x1 y0)) /\ (~ (x0 y0))) \/ (~ (@List.Forall a0 x1 x2)).
Definition term227 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := (~ (x3 = x0)) \/ ((@I (a0 -> Prop) x1 x3) \/ (~ (@I (a0 -> Prop) x2 x3))).
Definition term146 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : list a0) := fun y0 : a0 => (((@List.In a0 y0 x2) /\ (x1 y0)) /\ (~ (x0 y0))) \/ (~ (@List.Forall a0 x1 x2)).
Definition term103 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := forall y0 : a0, ((@List.In a0 y0 x0) /\ (x1 y0)) -> x2 y0.
Definition term151 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : list a0) := exists y0 : a0, ((fun y1 : a0 => (((@List.In a0 y1 x2) /\ (x0 y1)) /\ (~ (x1 y1))) \/ (~ (@List.Forall a0 x0 x2))) y0) \/ (@List.Forall a0 x1 x2).
Definition term207 (a0 : Type') (x0 : a0) (x1 : list a0) := ~ (@List.In a0 x0 x1).
Definition term116 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := (fun y0 : a0 => ((@List.In a0 y0 x0) /\ (x1 y0)) -> x2 y0) x3.
Definition term52 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) := @List.In a0 x0 (@cons a0 x1 x2).
Definition term203 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) (x3 : list a0) := or ((((@List.In a0 x1 x3) /\ (@I (a0 -> Prop) x2 x1)) /\ (~ (@I (a0 -> Prop) x0 x1))) \/ (~ (@List.Forall a0 x2 x3))).
Definition term187 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0 -> Prop) (x3 : a0) := or (((~ (x3 = x0)) /\ (~ (@List.In a0 x3 x1))) \/ (~ (@I (a0 -> Prop) x2 x3))).
Definition term159 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) (x3 : list a0) := or ((((@List.In a0 x1 x3) /\ (x2 x1)) /\ (~ (x0 x1))) \/ (~ (@List.Forall a0 x2 x3))).
Definition term191 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0 -> Prop) (x3 : a0 -> Prop) := and (forall y0 : a0, (((~ (y0 = x0)) /\ (~ (@List.In a0 y0 x1))) \/ (~ (@I (a0 -> Prop) x2 y0))) \/ (@I (a0 -> Prop) x3 y0)).
Definition term183 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := and (@I (a0 -> Prop) x0 x1).
Definition term150 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : list a0) := (exists y0 : a0, (fun y1 : a0 => (((@List.In a0 y1 x2) /\ (x0 y1)) /\ (~ (x1 y1))) \/ (~ (@List.Forall a0 x0 x2))) y0) \/ (@List.Forall a0 x1 x2).
Definition term181 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : list a0) := (~ (x1 x0)) \/ (~ (@List.Forall a0 x1 x2)).
Definition term169 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) := or ((~ (x1 = x0)) /\ (~ (@List.In a0 x1 x2))).
Definition term166 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) := (~ (x1 = x0)) /\ (~ (@List.In a0 x1 x2)).
Definition term230 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) (x3 : a0) := @eq Prop ((@I (a0 -> Prop) x0 x3) \/ ((~ (x3 = x1)) \/ (~ (@I (a0 -> Prop) x2 x3)))).
Definition term119 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := fun y0 : a0 => ((@List.In a0 y0 x0) /\ (x1 y0)) /\ (~ (x2 y0)).
Definition term243 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := imp ((x2 = x0) /\ (@I (a0 -> Prop) x1 x2)).
Definition term115 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := exists y0 : a0, ~ ((fun y1 : a0 => ((@List.In a0 y1 x0) /\ (x1 y1)) -> x2 y1) y0).
Definition term16 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : list a0) := imp ((fun y0 : list a0 => ((forall y1 : a0, ((@List.In a0 y1 y0) /\ (x0 y1)) -> x1 y1) /\ (@List.Forall a0 x0 y0)) -> @List.Forall a0 x1 y0) x2).
Definition term224 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (~ (@I (a0 -> Prop) x0 x2)) \/ (@I (a0 -> Prop) x1 x2).
Definition term44 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => ((@List.In a0 y0 (@nil a0)) /\ (x0 y0)) -> x1 y0.
Definition term247 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (@I (a0 -> Prop) x0 x1) -> False.
Definition term74 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) (x3 : list a0) := ((forall y0 : a0, (((y0 = x1) \/ (@List.In a0 y0 x3)) /\ (x0 y0)) -> x2 y0) /\ ((x0 x1) /\ (@List.Forall a0 x0 x3))) -> (x2 x1) /\ (@List.Forall a0 x2 x3).
Definition term36 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : list a0, ((forall y1 : a0, ((@List.In a0 y1 y0) /\ (x0 y1)) -> x1 y1) /\ (@List.Forall a0 x0 y0)) -> @List.Forall a0 x1 y0.
Definition term117 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := ~ ((fun y0 : a0 => ((@List.In a0 y0 x0) /\ (x1 y0)) -> x2 y0) x3).
Definition term220 (a0 : Type') (x0 : a0) := (~ (x0 = x0)) -> x0 = x0.
Definition term149 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : list a0) := (exists y0 : a0, (((@List.In a0 y0 x2) /\ (x0 y0)) /\ (~ (x1 y0))) \/ (~ (@List.Forall a0 x0 x2))) \/ (@List.Forall a0 x1 x2).
Definition term84 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) (x3 : list a0) := (((forall y0 : a0, ((@List.In a0 y0 x3) /\ (x0 y0)) -> x2 y0) /\ (@List.Forall a0 x0 x3)) -> @List.Forall a0 x2 x3) -> ((forall y0 : a0, (((y0 = x1) \/ (@List.In a0 y0 x3)) /\ (x0 y0)) -> x2 y0) /\ ((x0 x1) /\ (@List.Forall a0 x0 x3))) -> (x2 x1) /\ (@List.Forall a0 x2 x3).
Definition term261 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0) := ~ ((~ (@List.In a0 x2 x0)) \/ (~ (@I (a0 -> Prop) x1 x2))).
Definition term235 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := ~ ((~ (x2 = x0)) \/ (~ (@I (a0 -> Prop) x1 x2))).
Definition term56 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0 -> Prop) (x3 : a0) := (@List.In a0 x3 (@cons a0 x0 x1)) /\ (x2 x3).
Definition term86 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : list a0) := fun y0 : a0 -> Prop => (((forall y1 : a0, ((@List.In a0 y1 x2) /\ (y0 y1)) -> x1 y1) /\ (@List.Forall a0 y0 x2)) -> @List.Forall a0 x1 x2) -> ((forall y1 : a0, (((y1 = x0) \/ (@List.In a0 y1 x2)) /\ (y0 y1)) -> x1 y1) /\ ((y0 x0) /\ (@List.Forall a0 y0 x2))) -> (x1 x0) /\ (@List.Forall a0 x1 x2).
Definition term40 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := False /\ (x0 x1).
Definition term198 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0) := and ((@List.In a0 x2 x0) /\ (x1 x2)).
Definition term178 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0 -> Prop) (x3 : a0 -> Prop) := forall y0 : a0, (((~ (y0 = x0)) /\ (~ (@List.In a0 y0 x1))) \/ (~ (x2 y0))) \/ (x3 y0).
Definition term43 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := False -> x0 x1.
Definition term82 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) (x3 : list a0) := ~ (~ (((forall y0 : a0, (((y0 = x1) \/ (@List.In a0 y0 x3)) /\ (x0 y0)) -> x2 y0) /\ ((x0 x1) /\ (@List.Forall a0 x0 x3))) -> (x2 x1) /\ (@List.Forall a0 x2 x3))).
Definition term41 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := imp ((@List.In a0 x1 (@nil a0)) /\ (x0 x1)).
Definition term184 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : list a0) := (@I (a0 -> Prop) x1 x0) /\ (@List.Forall a0 x1 x2).
Definition term225 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (@I (a0 -> Prop) x0 x2) \/ (~ (@I (a0 -> Prop) x1 x2)).
Definition term177 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0 -> Prop) (x3 : a0 -> Prop) := fun y0 : a0 => (((~ (y0 = x0)) /\ (~ (@List.In a0 y0 x1))) \/ (~ (x2 y0))) \/ (x3 y0).
Definition term171 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0 -> Prop) (x3 : a0) := ((~ (x3 = x0)) /\ (~ (@List.In a0 x3 x1))) \/ (~ (x2 x3)).
Definition term200 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := ((@List.In a0 x3 x0) /\ (@I (a0 -> Prop) x1 x3)) /\ (~ (@I (a0 -> Prop) x2 x3)).
Definition term162 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : list a0) := fun y0 : a0 => ((fun y1 : a0 => (((@List.In a0 y1 x2) /\ (x0 y1)) /\ (~ (x1 y1))) \/ (~ (@List.Forall a0 x0 x2))) y0) \/ (@List.Forall a0 x1 x2).
Definition term129 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : list a0) := (~ ((forall y0 : a0, ((@List.In a0 y0 x2) /\ (x0 y0)) -> x1 y0) /\ (@List.Forall a0 x0 x2))) \/ (@List.Forall a0 x1 x2).
Definition term2 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1)) x1.
Definition term144 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) (x3 : list a0) := (((@List.In a0 x1 x3) /\ (x2 x1)) /\ (~ (x0 x1))) \/ (~ (@List.Forall a0 x2 x3)).
Definition term133 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : list a0) := (exists y0 : a0, (fun y1 : a0 => ((@List.In a0 y1 x2) /\ (x1 y1)) /\ (~ (x0 y1))) y0) \/ (~ (@List.Forall a0 x1 x2)).
Definition term259 (a0 : Type') (x0 : a0 -> Prop) (x1 : list a0) (x2 : a0 -> Prop) (x3 : a0) := (@I (a0 -> Prop) x0 x3) \/ ((~ (@List.In a0 x3 x1)) \/ (~ (@I (a0 -> Prop) x2 x3))).
Definition term228 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) (x3 : a0) := (@I (a0 -> Prop) x0 x3) \/ ((~ (x3 = x1)) \/ (~ (@I (a0 -> Prop) x2 x3))).
Definition term96 (a0 : Type') (x0 : list a0) := forall y0 : a0 -> Prop, forall y1 : a0, forall y2 : a0 -> Prop, (((forall y3 : a0, ((@List.In a0 y3 x0) /\ (y2 y3)) -> y0 y3) /\ (@List.Forall a0 y2 x0)) -> @List.Forall a0 y0 x0) -> ((forall y3 : a0, (((y3 = y1) \/ (@List.In a0 y3 x0)) /\ (y2 y3)) -> y0 y3) /\ ((y2 y1) /\ (@List.Forall a0 y2 x0))) -> (y0 y1) /\ (@List.Forall a0 y0 x0).
Definition term95 (a0 : Type') (x0 : list a0) := forall y0 : a0 -> Prop, forall y1 : a0, forall y2 : a0 -> Prop, (((forall y3 : a0, ((@List.In a0 y3 x0) /\ (y2 y3)) -> y0 y3) /\ (@List.Forall a0 y2 x0)) -> @List.Forall a0 y0 x0) -> (~ (((forall y3 : a0, (((y3 = y1) \/ (@List.In a0 y3 x0)) /\ (y2 y3)) -> y0 y3) /\ ((y2 y1) /\ (@List.Forall a0 y2 x0))) -> (y0 y1) /\ (@List.Forall a0 y0 x0))) -> False.
Definition term111 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0) := (@List.In a0 x2 x0) /\ (x1 x2).
Definition term70 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) (x3 : list a0) := (forall y0 : a0, ((@List.In a0 y0 (@cons a0 x2 x3)) /\ (x1 y0)) -> x0 y0) /\ (@List.Forall a0 x1 (@cons a0 x2 x3)).
Definition term107 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : list a0) := (~ ((x1 x0) /\ (@List.Forall a0 x1 x2))) -> False.
Definition term55 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) := and ((x1 = x0) \/ (@List.In a0 x1 x2)).
Definition term21 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) (x3 : list a0) := (((forall y0 : a0, ((@List.In a0 y0 x3) /\ (x0 y0)) -> x1 y0) /\ (@List.Forall a0 x0 x3)) -> @List.Forall a0 x1 x3) -> ((forall y0 : a0, ((@List.In a0 y0 (@cons a0 x2 x3)) /\ (x0 y0)) -> x1 y0) /\ (@List.Forall a0 x0 (@cons a0 x2 x3))) -> @List.Forall a0 x1 (@cons a0 x2 x3).
Definition term4 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0)) x2.
Definition term195 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : list a0) := (~ (@I (a0 -> Prop) x1 x0)) \/ (~ (@List.Forall a0 x1 x2)).
Definition term163 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : list a0) := fun y0 : a0 => ((((@List.In a0 y0 x2) /\ (x0 y0)) /\ (~ (x1 y0))) \/ (~ (@List.Forall a0 x0 x2))) \/ (@List.Forall a0 x1 x2).
Definition term241 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := (x2 = x0) /\ (@I (a0 -> Prop) x1 x2).
Definition term35 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : list a0, (fun y1 : list a0 => ((forall y2 : a0, ((@List.In a0 y2 y1) /\ (x0 y2)) -> x1 y2) /\ (@List.Forall a0 x0 y1)) -> @List.Forall a0 x1 y1) y0.
Definition term92 (a0 : Type') (x0 : a0 -> Prop) (x1 : list a0) := forall y0 : a0, forall y1 : a0 -> Prop, (((forall y2 : a0, ((@List.In a0 y2 x1) /\ (y1 y2)) -> x0 y2) /\ (@List.Forall a0 y1 x1)) -> @List.Forall a0 x0 x1) -> ((forall y2 : a0, (((y2 = y0) \/ (@List.In a0 y2 x1)) /\ (y1 y2)) -> x0 y2) /\ ((y1 y0) /\ (@List.Forall a0 y1 x1))) -> (x0 y0) /\ (@List.Forall a0 x0 x1).
Definition term91 (a0 : Type') (x0 : a0 -> Prop) (x1 : list a0) := forall y0 : a0, forall y1 : a0 -> Prop, (((forall y2 : a0, ((@List.In a0 y2 x1) /\ (y1 y2)) -> x0 y2) /\ (@List.Forall a0 y1 x1)) -> @List.Forall a0 x0 x1) -> (~ (((forall y2 : a0, (((y2 = y0) \/ (@List.In a0 y2 x1)) /\ (y1 y2)) -> x0 y2) /\ ((y1 y0) /\ (@List.Forall a0 y1 x1))) -> (x0 y0) /\ (@List.Forall a0 x0 x1))) -> False.
Definition term29 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, forall y1 : list a0, (((forall y2 : a0, ((@List.In a0 y2 y1) /\ (x0 y2)) -> x1 y2) /\ (@List.Forall a0 x0 y1)) -> @List.Forall a0 x1 y1) -> ((forall y2 : a0, ((@List.In a0 y2 (@cons a0 y0 y1)) /\ (x0 y2)) -> x1 y2) /\ (@List.Forall a0 x0 (@cons a0 y0 y1))) -> @List.Forall a0 x1 (@cons a0 y0 y1).
Definition term28 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, forall y1 : list a0, ((fun y2 : list a0 => ((forall y3 : a0, ((@List.In a0 y3 y2) /\ (x0 y3)) -> x1 y3) /\ (@List.Forall a0 x0 y2)) -> @List.Forall a0 x1 y2) y1) -> (fun y2 : list a0 => ((forall y3 : a0, ((@List.In a0 y3 y2) /\ (x0 y3)) -> x1 y3) /\ (@List.Forall a0 x0 y2)) -> @List.Forall a0 x1 y2) (@cons a0 y0 y1).
Definition term210 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0 -> Prop) (x3 : a0 -> Prop) (x4 : a0) := (((~ (x4 = x0)) \/ (~ (@I (a0 -> Prop) x2 x4))) \/ (@I (a0 -> Prop) x3 x4)) /\ (((~ (@List.In a0 x4 x1)) \/ (~ (@I (a0 -> Prop) x2 x4))) \/ (@I (a0 -> Prop) x3 x4)).
Definition term249 (a0 : Type') (x0 : a0) (x1 : list a0) := (~ (@List.In a0 x0 x1)) -> @List.In a0 x0 x1.
Definition term114 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := ~ (forall y0 : a0, ((@List.In a0 y0 x0) /\ (x1 y0)) -> x2 y0).
Definition term23 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := fun y0 : list a0 => (((forall y1 : a0, ((@List.In a0 y1 y0) /\ (x0 y1)) -> x1 y1) /\ (@List.Forall a0 x0 y0)) -> @List.Forall a0 x1 y0) -> ((forall y1 : a0, ((@List.In a0 y1 (@cons a0 x2 y0)) /\ (x0 y1)) -> x1 y1) /\ (@List.Forall a0 x0 (@cons a0 x2 y0))) -> @List.Forall a0 x1 (@cons a0 x2 y0).
Definition term68 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : list a0) := @List.Forall a0 x0 (@cons a0 x1 x2).
Definition term73 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) (x3 : list a0) := imp ((forall y0 : a0, (((y0 = x1) \/ (@List.In a0 y0 x3)) /\ (x2 y0)) -> x0 y0) /\ ((x2 x1) /\ (@List.Forall a0 x2 x3))).
Definition term148 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : list a0) := or (exists y0 : a0, (((@List.In a0 y0 x2) /\ (x1 y0)) /\ (~ (x0 y0))) \/ (~ (@List.Forall a0 x1 x2))).
Definition term123 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := or (exists y0 : a0, ((@List.In a0 y0 x0) /\ (x1 y0)) /\ (~ (x2 y0))).
Definition term124 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : list a0) := (~ (forall y0 : a0, ((@List.In a0 y0 x2) /\ (x1 y0)) -> x0 y0)) \/ (~ (@List.Forall a0 x1 x2)).
Definition term102 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := fun y0 : a0 => ((@List.In a0 y0 x0) /\ (x1 y0)) -> x2 y0.
Definition term72 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) (x3 : list a0) := imp ((forall y0 : a0, ((@List.In a0 y0 (@cons a0 x2 x3)) /\ (x1 y0)) -> x0 y0) /\ (@List.Forall a0 x1 (@cons a0 x2 x3))).
Definition term237 (a0 : Type') (x0 : a0) (x1 : a0) := ~ (~ (x0 = x1)).
Definition term199 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0) := and ((@List.In a0 x2 x0) /\ (@I (a0 -> Prop) x1 x2)).
Definition term77 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) (x3 : list a0) := ~ (((forall y0 : a0, (((y0 = x1) \/ (@List.In a0 y0 x3)) /\ (x0 y0)) -> x2 y0) /\ ((x0 x1) /\ (@List.Forall a0 x0 x3))) -> (x2 x1) /\ (@List.Forall a0 x2 x3)).
Definition term14 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : list a0) := (fun y0 : list a0 => ((forall y1 : a0, ((@List.In a0 y1 y0) /\ (x0 y1)) -> x1 y1) /\ (@List.Forall a0 x0 y0)) -> @List.Forall a0 x1 y0) x2.
Definition term39 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (@List.In a0 x1 (@nil a0)) /\ (x0 x1).
Definition term30 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((fun y0 : list a0 => ((forall y1 : a0, ((@List.In a0 y1 y0) /\ (x0 y1)) -> x1 y1) /\ (@List.Forall a0 x0 y0)) -> @List.Forall a0 x1 y0) (@nil a0)) /\ (forall y0 : a0, forall y1 : list a0, ((fun y2 : list a0 => ((forall y3 : a0, ((@List.In a0 y3 y2) /\ (x0 y3)) -> x1 y3) /\ (@List.Forall a0 x0 y2)) -> @List.Forall a0 x1 y2) y1) -> (fun y2 : list a0 => ((forall y3 : a0, ((@List.In a0 y3 y2) /\ (x0 y3)) -> x1 y3) /\ (@List.Forall a0 x0 y2)) -> @List.Forall a0 x1 y2) (@cons a0 y0 y1)).
Definition term152 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : list a0) (x3 : a0) := (fun y0 : a0 => (((@List.In a0 y0 x2) /\ (x1 y0)) /\ (~ (x0 y0))) \/ (~ (@List.Forall a0 x1 x2))) x3.
Definition term197 (a0 : Type') (x0 : list a0) (x1 : a0 -> Prop) (x2 : a0) := (@List.In a0 x2 x0) /\ (@I (a0 -> Prop) x1 x2).
