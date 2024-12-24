Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term179 (a0 : Type') (x0 : list a0) (x1 : a0) (x2 : list a0) (x3 : list a0) := @eq Prop ((fun y0 : list a0 => ~ (y0 = (@List.app a0 x0 (@cons a0 x1 x2)))) x3).
Definition term88 (a0 : Type') (x0 : list a0) (x1 : list a0) (x2 : a0) (x3 : list a0) (x4 : Prop) (x5 : Prop) := ((x3 = (@List.app a0 x0 (@cons a0 x2 x1))) = x4) -> (x4 -> (@List.In a0 x2 x3) = x5) -> ((x3 = (@List.app a0 x0 (@cons a0 x2 x1))) -> @List.In a0 x2 x3) = (x4 -> x5).
Definition term186 := (~ False) -> False.
Definition term29 (x0 : Prop) := @eq Prop (False = x0).
Definition term140 (a0 : Type') (x0 : list a0) (x1 : list a0) (x2 : a0) := fun y0 : list a0 => (~ (@List.In a0 x2 x1)) /\ ((fun y1 : list a0 => x0 = (@List.app a0 x1 (@cons a0 x2 y1))) y0).
Definition term98 (a0 : Type') (x0 : a0) (x1 : list a0) := True \/ (@List.In a0 x0 x1).
Definition term102 (a0 : Type') (x0 : list a0) (x1 : list a0) (x2 : a0) (x3 : list a0) := ((x0 = (@List.app a0 x1 (@cons a0 x2 x3))) -> (@List.In a0 x2 x0) = True) -> ((x0 = (@List.app a0 x1 (@cons a0 x2 x3))) -> @List.In a0 x2 x0) = ((x0 = (@List.app a0 x1 (@cons a0 x2 x3))) -> True).
Definition term129 (x0 : Prop) := ~ (~ x0).
Definition term68 (a0 : Type') (x0 : list a0) (x1 : a0) (x2 : list a0) := @List.app a0 x0 (@cons a0 x1 x2).
Definition term171 (a0 : Type') (x0 : list a0) (x1 : a0) := fun y0 : list a0 => forall y1 : list a0, ~ (x0 = (@List.app a0 y0 (@cons a0 x1 y1))).
Definition term15 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := forall y0 : a0, (x0 y0) -> x1.
Definition term27 (x0 : Prop) := @eq Prop (True = x0).
Definition term8 (a0 : Type') (x0 : list a0) (x1 : a0) (x2 : list a0) := (fun y0 : list a0 => (@List.In a0 x1 (@List.app a0 x0 y0)) = ((@List.In a0 x1 x0) \/ (@List.In a0 x1 y0))) x2.
Definition term106 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term73 (a0 : Type') (x0 : list a0) (x1 : a0) (x2 : list a0) := @eq Prop ((exists y0 : list a0, x2 = (@List.app a0 x0 (@cons a0 x1 y0))) -> @List.In a0 x1 x2).
Definition term72 (a0 : Type') (x0 : list a0) (x1 : a0) (x2 : list a0) := @eq Prop ((exists y0 : list a0, (fun y1 : list a0 => x2 = (@List.app a0 x0 (@cons a0 x1 y1))) y0) -> @List.In a0 x1 x2).
Definition term160 (a0 : Type') (x0 : type1143 a0) := forall y0 : list a0, ~ (x0 y0).
Definition term167 (a0 : Type') (x0 : list a0) (x1 : list a0) (x2 : a0) := forall y0 : list a0, ~ (x0 = (@List.app a0 x1 (@cons a0 x2 y0))).
Definition term0 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : list a0, (@List.In a0 y0 y1) = (exists y2 : list a0, exists y3 : list a0, (~ (@List.In a0 y0 y2)) /\ (y1 = (@List.app a0 y2 (@cons a0 y0 y3))))) x0.
Definition term2 (a0 : Type') (x0 : a0) (x1 : list a0) := (fun y0 : list a0 => (@List.In a0 x0 y0) = (exists y1 : list a0, exists y2 : list a0, (~ (@List.In a0 x0 y1)) /\ (y0 = (@List.app a0 y1 (@cons a0 x0 y2))))) x1.
Definition term76 (a0 : Type') (x0 : list a0) (x1 : list a0) (x2 : a0) (x3 : list a0) := ((fun y0 : list a0 => x3 = (@List.app a0 x0 (@cons a0 x2 y0))) x1) -> @List.In a0 x2 x3.
Definition term91 (a0 : Type') (x0 : list a0) (x1 : a0) (x2 : list a0) := @List.In a0 x1 (@List.app a0 x0 (@cons a0 x1 x2)).
Definition term130 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 /\ (x1 y0).
Definition term122 (x0 : Prop) := (~ x0) -> False.
Definition term172 (a0 : Type') (x0 : list a0) (x1 : a0) := forall y0 : list a0, forall y1 : list a0, ~ (x0 = (@List.app a0 y0 (@cons a0 x1 y1))).
Definition term5 (a0 : Type') (x0 : a0) := forall y0 : list a0, forall y1 : list a0, (@List.In a0 x0 (@List.app a0 y0 y1)) = ((@List.In a0 x0 y0) \/ (@List.In a0 x0 y1)).
Definition term143 (a0 : Type') (x0 : list a0) (x1 : list a0) (x2 : a0) := @eq Prop (exists y0 : list a0, (~ (@List.In a0 x2 x1)) /\ ((fun y1 : list a0 => x0 = (@List.app a0 x1 (@cons a0 x2 y1))) y0)).
Definition term147 (a0 : Type') (x0 : list a0) (x1 : a0) := fun y0 : list a0 => (~ (@List.In a0 x1 y0)) /\ (exists y1 : list a0, x0 = (@List.app a0 y0 (@cons a0 x1 y1))).
Definition term185 (a0 : Type') (x0 : list a0) (x1 : a0) (x2 : list a0) := ((@List.app a0 x0 (@cons a0 x1 x2)) = (@List.app a0 x0 (@cons a0 x1 x2))) -> False.
Definition term184 (a0 : Type') (x0 : list a0) (x1 : list a0) (x2 : list a0) (x3 : a0) (x4 : list a0) := ((@List.app a0 x0 (@cons a0 x3 x1)) = (@List.app a0 x2 (@cons a0 x3 x4))) -> False.
Definition term34 (a0 : Type') (x0 : a0) (x1 : list a0) := ((@List.In a0 x0 x1) -> exists y0 : list a0, exists y1 : list a0, x1 = (@List.app a0 y0 (@cons a0 x0 y1))) /\ ((exists y0 : list a0, exists y1 : list a0, x1 = (@List.app a0 y0 (@cons a0 x0 y1))) -> @List.In a0 x0 x1).
Definition term38 (a0 : Type') (x0 : a0) := forall y0 : list a0, ((@List.In a0 x0 y0) -> exists y1 : list a0, exists y2 : list a0, y0 = (@List.app a0 y1 (@cons a0 x0 y2))) /\ ((exists y1 : list a0, exists y2 : list a0, y0 = (@List.app a0 y1 (@cons a0 x0 y2))) -> @List.In a0 x0 y0).
Definition term148 (a0 : Type') (x0 : list a0) (x1 : a0) := exists y0 : list a0, (~ (@List.In a0 x1 y0)) /\ (exists y1 : list a0, x0 = (@List.app a0 y0 (@cons a0 x1 y1))).
Definition term92 (a0 : Type') (x0 : list a0) (x1 : a0) (x2 : list a0) := (@List.In a0 x1 x0) \/ (@List.In a0 x1 (@cons a0 x1 x2)).
Definition term135 (a0 : Type') (x0 : list a0) (x1 : list a0) (x2 : a0) := (~ (@List.In a0 x2 x1)) /\ (exists y0 : list a0, (fun y1 : list a0 => x0 = (@List.app a0 x1 (@cons a0 x2 y1))) y0).
Definition term117 (a0 : Type') (x0 : list a0) (x1 : a0) := (exists y0 : list a0, exists y1 : list a0, (~ (@List.In a0 x1 y0)) /\ (x0 = (@List.app a0 y0 (@cons a0 x1 y1)))) -> exists y0 : list a0, exists y1 : list a0, x0 = (@List.app a0 y0 (@cons a0 x1 y1)).
Definition term66 (a0 : Type') (x0 : list a0) (x1 : list a0) (x2 : a0) := fun y0 : list a0 => x0 = (@List.app a0 x1 (@cons a0 x2 y0)).
Definition term31 (x0 : Prop) := and (False -> x0).
Definition term177 (a0 : Type') (x0 : list a0) (x1 : list a0) (x2 : list a0) (x3 : a0) (x4 : list a0) := (fun y0 : list a0 => ~ (y0 = (@List.app a0 x0 (@cons a0 x3 x1)))) (@List.app a0 x2 (@cons a0 x3 x4)).
Definition term131 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 /\ (exists y0 : a0, x1 y0).
Definition term183 (x0 : Prop) := (~ x0) -> x0.
Definition term65 (a0 : Type') (x0 : list a0) (x1 : a0) (x2 : list a0) := forall y0 : list a0, ((fun y1 : list a0 => x2 = (@List.app a0 x0 (@cons a0 x1 y1))) y0) -> @List.In a0 x1 x2.
Definition term173 (a0 : Type') (x0 : list a0) (x1 : a0) (x2 : list a0) := (fun y0 : list a0 => forall y1 : list a0, ~ (x0 = (@List.app a0 y0 (@cons a0 x1 y1)))) x2.
Definition term62 (a0 : Type') (x0 : a0) (x1 : list a0) := fun y0 : list a0 => (exists y1 : list a0, x1 = (@List.app a0 y0 (@cons a0 x0 y1))) -> @List.In a0 x0 x1.
Definition term23 (x0 : Prop) (x1 : Prop) := (x1 -> x0) /\ (x0 -> x1).
Definition term155 (a0 : Type') (x0 : list a0) (x1 : a0) := (~ (exists y0 : list a0, exists y1 : list a0, x0 = (@List.app a0 y0 (@cons a0 x1 y1)))) -> False.
Definition term19 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => (y0 = x0) = ((y0 -> x0) /\ (x0 -> y0))) x1.
Definition term44 (a0 : Type') (x0 : type1143 a0) (x1 : Prop) := forall y0 : list a0, (x0 y0) -> x1.
Definition term71 (a0 : Type') (x0 : list a0) (x1 : list a0) (x2 : a0) := imp (exists y0 : list a0, (fun y1 : list a0 => x0 = (@List.app a0 x1 (@cons a0 x2 y1))) y0).
Definition term52 (a0 : Type') (x0 : list a0) (x1 : a0) := imp (exists y0 : list a0, (fun y1 : list a0 => exists y2 : list a0, x0 = (@List.app a0 y1 (@cons a0 x1 y2))) y0).
Definition term180 (a0 : Type') (x0 : list a0) (x1 : list a0) (x2 : a0) (x3 : list a0) := @eq Prop (~ (x0 = (@List.app a0 x1 (@cons a0 x2 x3)))).
Definition term112 (a0 : Type') (x0 : a0) := forall y0 : list a0, (@List.In a0 x0 y0) -> exists y1 : list a0, exists y2 : list a0, y0 = (@List.app a0 y1 (@cons a0 x0 y2)).
Definition term158 (a0 : Type') (x0 : list a0) (x1 : list a0) (x2 : a0) := @eq Prop ((~ (@List.In a0 x2 x1)) /\ (exists y0 : list a0, x0 = (@List.app a0 x1 (@cons a0 x2 y0)))).
Definition term157 (a0 : Type') (x0 : list a0) (x1 : list a0) (x2 : a0) := @eq Prop ((~ (@List.In a0 x2 x1)) /\ (exists y0 : list a0, (fun y1 : list a0 => x0 = (@List.app a0 x1 (@cons a0 x2 y1))) y0)).
Definition term4 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : list a0, forall y2 : list a0, (@List.In a0 y0 (@List.app a0 y1 y2)) = ((@List.In a0 y0 y1) \/ (@List.In a0 y0 y2))) x0.
Definition term80 (a0 : Type') (x0 : list a0) (x1 : a0) (x2 : list a0) := forall y0 : list a0, (x2 = (@List.app a0 x0 (@cons a0 x1 y0))) -> @List.In a0 x1 x2.
Definition term144 (a0 : Type') (x0 : list a0) (x1 : list a0) (x2 : a0) := @eq Prop (exists y0 : list a0, (~ (@List.In a0 x2 x1)) /\ (x0 = (@List.app a0 x1 (@cons a0 x2 y0)))).
Definition term96 (a0 : Type') (x0 : a0) (x1 : list a0) := (x0 = x0) \/ (@List.In a0 x0 x1).
Definition term64 (a0 : Type') (x0 : list a0) (x1 : a0) (x2 : list a0) := (exists y0 : list a0, (fun y1 : list a0 => x2 = (@List.app a0 x0 (@cons a0 x1 y1))) y0) -> @List.In a0 x1 x2.
Definition term97 (a0 : Type') (x0 : a0) := or (x0 = x0).
Definition term56 (a0 : Type') (x0 : a0) (x1 : list a0) := @eq Prop ((exists y0 : list a0, exists y1 : list a0, x1 = (@List.app a0 y0 (@cons a0 x0 y1))) -> @List.In a0 x0 x1).
Definition term55 (a0 : Type') (x0 : a0) (x1 : list a0) := @eq Prop ((exists y0 : list a0, (fun y1 : list a0 => exists y2 : list a0, x1 = (@List.app a0 y1 (@cons a0 x0 y2))) y0) -> @List.In a0 x0 x1).
Definition term79 (a0 : Type') (x0 : list a0) (x1 : a0) (x2 : list a0) := fun y0 : list a0 => (x2 = (@List.app a0 x0 (@cons a0 x1 y0))) -> @List.In a0 x1 x2.
Definition term138 (a0 : Type') (x0 : list a0) (x1 : list a0) (x2 : a0) (x3 : list a0) := (~ (@List.In a0 x2 x1)) /\ ((fun y0 : list a0 => x0 = (@List.app a0 x1 (@cons a0 x2 y0))) x3).
Definition term105 (a0 : Type') := forall y0 : list a0, True.
Definition term63 (a0 : Type') (x0 : a0) (x1 : list a0) := forall y0 : list a0, (exists y1 : list a0, x1 = (@List.app a0 y0 (@cons a0 x0 y1))) -> @List.In a0 x0 x1.
Definition term24 (x0 : Prop) (x1 : Prop) := @eq Prop ((x1 = x0) = ((x1 -> x0) /\ (x0 -> x1))).
Definition term111 (a0 : Type') (x0 : a0) := fun y0 : list a0 => (@List.In a0 x0 y0) -> exists y1 : list a0, exists y2 : list a0, y0 = (@List.app a0 y1 (@cons a0 x0 y2)).
Definition term50 (a0 : Type') (x0 : list a0) (x1 : a0) := fun y0 : list a0 => (fun y1 : list a0 => exists y2 : list a0, x0 = (@List.app a0 y1 (@cons a0 x1 y2))) y0.
Definition term103 (a0 : Type') (x0 : list a0) (x1 : list a0) (x2 : a0) (x3 : list a0) := (x0 = (@List.app a0 x1 (@cons a0 x2 x3))) -> True.
Definition term81 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term18 (x0 : Prop) := fun y0 : Prop => (y0 = x0) = ((y0 -> x0) /\ (x0 -> y0)).
Definition term26 (x0 : Prop) := (False -> x0) /\ (x0 -> False).
Definition term39 (a0 : Type') := fun y0 : a0 => forall y1 : list a0, (@List.In a0 y0 y1) = (exists y2 : list a0, exists y3 : list a0, y1 = (@List.app a0 y2 (@cons a0 y0 y3))).
Definition term74 (a0 : Type') (x0 : list a0) (x1 : list a0) (x2 : a0) (x3 : list a0) := imp ((fun y0 : list a0 => x0 = (@List.app a0 x1 (@cons a0 x2 y0))) x3).
Definition term13 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (fun y0 : Prop => ((exists y1 : a0, x0 y1) -> y0) = (forall y1 : a0, (x0 y1) -> y0)) x1.
Definition term25 (x0 : Prop) := (fun y0 : Prop => (y0 = x0) = ((y0 -> x0) /\ (x0 -> y0))) False.
Definition term125 (a0 : Type') := ((~ (forall y0 : a0, forall y1 : list a0, (exists y2 : list a0, exists y3 : list a0, (~ (@List.In a0 y0 y2)) /\ (y1 = (@List.app a0 y2 (@cons a0 y0 y3)))) -> exists y2 : list a0, exists y3 : list a0, y1 = (@List.app a0 y2 (@cons a0 y0 y3)))) -> False) -> (~ (forall y0 : a0, forall y1 : list a0, (exists y2 : list a0, exists y3 : list a0, (~ (@List.In a0 y0 y2)) /\ (y1 = (@List.app a0 y2 (@cons a0 y0 y3)))) -> exists y2 : list a0, exists y3 : list a0, y1 = (@List.app a0 y2 (@cons a0 y0 y3)))) -> False.
Definition term116 (a0 : Type') (x0 : list a0) (x1 : a0) := imp (exists y0 : list a0, exists y1 : list a0, (~ (@List.In a0 x1 y0)) /\ (x0 = (@List.app a0 y0 (@cons a0 x1 y1)))).
Definition term53 (a0 : Type') (x0 : list a0) (x1 : a0) := imp (exists y0 : list a0, exists y1 : list a0, x0 = (@List.app a0 y0 (@cons a0 x1 y1))).
Definition term137 (a0 : Type') (x0 : a0) (x1 : list a0) := and (~ (@List.In a0 x0 x1)).
Definition term30 (x0 : Prop) := @eq Prop (~ x0).
Definition term36 (a0 : Type') (x0 : a0) := fun y0 : list a0 => ((@List.In a0 x0 y0) -> exists y1 : list a0, exists y2 : list a0, y0 = (@List.app a0 y1 (@cons a0 x0 y2))) /\ ((exists y1 : list a0, exists y2 : list a0, y0 = (@List.app a0 y1 (@cons a0 x0 y2))) -> @List.In a0 x0 y0).
Definition term159 (a0 : Type') (x0 : type1143 a0) := ~ (ex x0).
Definition term69 (a0 : Type') (x0 : list a0) (x1 : list a0) (x2 : a0) := fun y0 : list a0 => (fun y1 : list a0 => x0 = (@List.app a0 x1 (@cons a0 x2 y1))) y0.
Definition term89 (a0 : Type') (x0 : list a0) (x1 : list a0) (x2 : a0) (x3 : list a0) (x4 : Prop) := ((x0 = (@List.app a0 x1 (@cons a0 x2 x3))) = (x0 = (@List.app a0 x1 (@cons a0 x2 x3)))) -> ((x0 = (@List.app a0 x1 (@cons a0 x2 x3))) -> (@List.In a0 x2 x0) = x4) -> ((x0 = (@List.app a0 x1 (@cons a0 x2 x3))) -> @List.In a0 x2 x0) = ((x0 = (@List.app a0 x1 (@cons a0 x2 x3))) -> x4).
Definition term32 (x0 : Prop) := True /\ (~ x0).
Definition term161 (a0 : Type') (x0 : list a0) (x1 : list a0) (x2 : a0) := ~ (exists y0 : list a0, x0 = (@List.app a0 x1 (@cons a0 x2 y0))).
Definition term75 (a0 : Type') (x0 : list a0) (x1 : list a0) (x2 : a0) (x3 : list a0) := imp (x0 = (@List.app a0 x1 (@cons a0 x2 x3))).
Definition term101 (a0 : Type') (x0 : list a0) (x1 : list a0) (x2 : a0) (x3 : list a0) := (x3 = (@List.app a0 x0 (@cons a0 x2 x1))) -> (@List.In a0 x2 x3) = True.
Definition term51 (a0 : Type') (x0 : list a0) (x1 : a0) := exists y0 : list a0, (fun y1 : list a0 => exists y2 : list a0, x0 = (@List.app a0 y1 (@cons a0 x1 y2))) y0.
Definition term43 (a0 : Type') (x0 : type1143 a0) (x1 : Prop) := (exists y0 : list a0, x0 y0) -> x1.
Definition term57 (a0 : Type') (x0 : list a0) (x1 : a0) (x2 : list a0) := imp ((fun y0 : list a0 => exists y1 : list a0, x0 = (@List.app a0 y0 (@cons a0 x1 y1))) x2).
Definition term164 (a0 : Type') (x0 : list a0) (x1 : list a0) (x2 : a0) (x3 : list a0) := ~ (x0 = (@List.app a0 x1 (@cons a0 x2 x3))).
Definition term153 (a0 : Type') := fun y0 : a0 => forall y1 : list a0, (exists y2 : list a0, (~ (@List.In a0 y0 y2)) /\ (exists y3 : list a0, y1 = (@List.app a0 y2 (@cons a0 y0 y3)))) -> exists y2 : list a0, exists y3 : list a0, y1 = (@List.app a0 y2 (@cons a0 y0 y3)).
Definition term120 (a0 : Type') := fun y0 : a0 => forall y1 : list a0, (exists y2 : list a0, exists y3 : list a0, (~ (@List.In a0 y0 y2)) /\ (y1 = (@List.app a0 y2 (@cons a0 y0 y3)))) -> exists y2 : list a0, exists y3 : list a0, y1 = (@List.app a0 y2 (@cons a0 y0 y3)).
Definition term113 (a0 : Type') := fun y0 : a0 => forall y1 : list a0, (@List.In a0 y0 y1) -> exists y2 : list a0, exists y3 : list a0, y1 = (@List.app a0 y2 (@cons a0 y0 y3)).
Definition term169 (a0 : Type') (x0 : list a0) (x1 : a0) (x2 : list a0) := ~ ((fun y0 : list a0 => exists y1 : list a0, x0 = (@List.app a0 y0 (@cons a0 x1 y1))) x2).
Definition term141 (a0 : Type') (x0 : list a0) (x1 : list a0) (x2 : a0) := fun y0 : list a0 => (~ (@List.In a0 x2 x1)) /\ (x0 = (@List.app a0 x1 (@cons a0 x2 y0))).
Definition term94 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) := (x1 = x0) \/ (@List.In a0 x1 x2).
Definition term11 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : Prop, ((exists y2 : a0, y0 y2) -> y1) = (forall y2 : a0, (y0 y2) -> y1)) x0.
Definition term10 (a0 : Type') (x0 : list a0) (x1 : a0) (x2 : list a0) := (@List.In a0 x1 x0) \/ (@List.In a0 x1 x2).
Definition term132 (a0 : Type') (x0 : Prop) (x1 : type1143 a0) := exists y0 : list a0, x0 /\ (x1 y0).
Definition term128 (a0 : Type') := ~ (~ (forall y0 : a0, forall y1 : list a0, (exists y2 : list a0, exists y3 : list a0, (~ (@List.In a0 y0 y2)) /\ (y1 = (@List.app a0 y2 (@cons a0 y0 y3)))) -> exists y2 : list a0, exists y3 : list a0, y1 = (@List.app a0 y2 (@cons a0 y0 y3)))).
Definition term22 (x0 : Prop) (x1 : Prop) := @eq Prop ((fun y0 : Prop => (y0 = x0) = ((y0 -> x0) /\ (x0 -> y0))) x1).
Definition term145 (a0 : Type') (x0 : list a0) (x1 : list a0) (x2 : a0) := (~ (@List.In a0 x2 x1)) /\ (exists y0 : list a0, x0 = (@List.app a0 x1 (@cons a0 x2 y0))).
Definition term123 (a0 : Type') := (~ (forall y0 : a0, forall y1 : list a0, (exists y2 : list a0, exists y3 : list a0, (~ (@List.In a0 y0 y2)) /\ (y1 = (@List.app a0 y2 (@cons a0 y0 y3)))) -> exists y2 : list a0, exists y3 : list a0, y1 = (@List.app a0 y2 (@cons a0 y0 y3)))) -> False.
Definition term150 (a0 : Type') (x0 : list a0) (x1 : a0) := (exists y0 : list a0, (~ (@List.In a0 x1 y0)) /\ (exists y1 : list a0, x0 = (@List.app a0 y0 (@cons a0 x1 y1)))) -> exists y0 : list a0, exists y1 : list a0, x0 = (@List.app a0 y0 (@cons a0 x1 y1)).
Definition term6 (a0 : Type') (x0 : a0) (x1 : list a0) := (fun y0 : list a0 => forall y1 : list a0, (@List.In a0 x0 (@List.app a0 y0 y1)) = ((@List.In a0 x0 y0) \/ (@List.In a0 x0 y1))) x1.
Definition term21 (x0 : Prop) := (True -> x0) /\ (x0 -> True).
Definition term86 (a0 : Type') (x0 : list a0) (x1 : list a0) (x2 : a0) (x3 : list a0) (x4 : Prop) := forall y0 : Prop, ((x3 = (@List.app a0 x0 (@cons a0 x2 x1))) = x4) -> (x4 -> (@List.In a0 x2 x3) = y0) -> ((x3 = (@List.app a0 x0 (@cons a0 x2 x1))) -> @List.In a0 x2 x3) = (x4 -> y0).
Definition term82 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term178 (a0 : Type') (x0 : list a0) (x1 : list a0) (x2 : list a0) (x3 : a0) (x4 : list a0) := ~ ((@List.app a0 x0 (@cons a0 x3 x1)) = (@List.app a0 x2 (@cons a0 x3 x4))).
Definition term165 (a0 : Type') (x0 : list a0) (x1 : list a0) (x2 : a0) := fun y0 : list a0 => ~ ((fun y1 : list a0 => x0 = (@List.app a0 x1 (@cons a0 x2 y1))) y0).
Definition term45 (a0 : Type') (x0 : a0) (x1 : list a0) := (exists y0 : list a0, (fun y1 : list a0 => exists y2 : list a0, x1 = (@List.app a0 y1 (@cons a0 x0 y2))) y0) -> @List.In a0 x0 x1.
Definition term134 (a0 : Type') (x0 : list a0) (x1 : list a0) (x2 : a0) := exists y0 : list a0, (~ (@List.In a0 x2 x1)) /\ ((fun y1 : list a0 => x0 = (@List.app a0 x1 (@cons a0 x2 y1))) y0).
Definition term126 (a0 : Type') := (((~ (forall y0 : a0, forall y1 : list a0, (exists y2 : list a0, exists y3 : list a0, (~ (@List.In a0 y0 y2)) /\ (y1 = (@List.app a0 y2 (@cons a0 y0 y3)))) -> exists y2 : list a0, exists y3 : list a0, y1 = (@List.app a0 y2 (@cons a0 y0 y3)))) -> False) -> (~ (forall y0 : a0, forall y1 : list a0, (exists y2 : list a0, exists y3 : list a0, (~ (@List.In a0 y0 y2)) /\ (y1 = (@List.app a0 y2 (@cons a0 y0 y3)))) -> exists y2 : list a0, exists y3 : list a0, y1 = (@List.app a0 y2 (@cons a0 y0 y3)))) -> False) -> (~ (forall y0 : a0, forall y1 : list a0, (exists y2 : list a0, exists y3 : list a0, (~ (@List.In a0 y0 y2)) /\ (y1 = (@List.app a0 y2 (@cons a0 y0 y3)))) -> exists y2 : list a0, exists y3 : list a0, y1 = (@List.app a0 y2 (@cons a0 y0 y3)))) -> False.
Definition term17 (x0 : Prop) := (x0 = True) \/ (x0 = False).
Definition term84 (a0 : Type') (x0 : list a0) (x1 : list a0) (x2 : a0) (x3 : list a0) := forall y0 : Prop, forall y1 : Prop, ((x3 = (@List.app a0 x0 (@cons a0 x2 x1))) = y0) -> (y0 -> (@List.In a0 x2 x3) = y1) -> ((x3 = (@List.app a0 x0 (@cons a0 x2 x1))) -> @List.In a0 x2 x3) = (y0 -> y1).
Definition term83 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term60 (a0 : Type') (x0 : list a0) (x1 : a0) (x2 : list a0) := (exists y0 : list a0, x2 = (@List.app a0 x0 (@cons a0 x1 y0))) -> @List.In a0 x1 x2.
Definition term9 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : list a0) := @List.In a0 x0 (@List.app a0 x1 x2).
Definition term58 (a0 : Type') (x0 : list a0) (x1 : list a0) (x2 : a0) := imp (exists y0 : list a0, x0 = (@List.app a0 x1 (@cons a0 x2 y0))).
Definition term170 (a0 : Type') (x0 : list a0) (x1 : a0) := fun y0 : list a0 => ~ ((fun y1 : list a0 => exists y2 : list a0, x0 = (@List.app a0 y1 (@cons a0 x1 y2))) y0).
Definition term151 (a0 : Type') (x0 : a0) := fun y0 : list a0 => (exists y1 : list a0, (~ (@List.In a0 x0 y1)) /\ (exists y2 : list a0, y0 = (@List.app a0 y1 (@cons a0 x0 y2)))) -> exists y1 : list a0, exists y2 : list a0, y0 = (@List.app a0 y1 (@cons a0 x0 y2)).
Definition term118 (a0 : Type') (x0 : a0) := fun y0 : list a0 => (exists y1 : list a0, exists y2 : list a0, (~ (@List.In a0 x0 y1)) /\ (y0 = (@List.app a0 y1 (@cons a0 x0 y2)))) -> exists y1 : list a0, exists y2 : list a0, y0 = (@List.app a0 y1 (@cons a0 x0 y2)).
Definition term166 (a0 : Type') (x0 : list a0) (x1 : list a0) (x2 : a0) := fun y0 : list a0 => ~ (x0 = (@List.app a0 x1 (@cons a0 x2 y0))).
Definition term136 (a0 : Type') (x0 : a0) (x1 : list a0) := ~ (@List.In a0 x0 x1).
Definition term37 (a0 : Type') (x0 : a0) := forall y0 : list a0, (@List.In a0 x0 y0) = (exists y1 : list a0, exists y2 : list a0, y0 = (@List.app a0 y1 (@cons a0 x0 y2))).
Definition term1 (a0 : Type') (x0 : a0) := forall y0 : list a0, (@List.In a0 x0 y0) = (exists y1 : list a0, exists y2 : list a0, (~ (@List.In a0 x0 y1)) /\ (y0 = (@List.app a0 y1 (@cons a0 x0 y2)))).
Definition term146 (a0 : Type') (x0 : list a0) (x1 : a0) := fun y0 : list a0 => exists y1 : list a0, (~ (@List.In a0 x1 y0)) /\ (x0 = (@List.app a0 y0 (@cons a0 x1 y1))).
Definition term93 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) := @List.In a0 x0 (@cons a0 x1 x2).
Definition term87 (a0 : Type') (x0 : list a0) (x1 : list a0) (x2 : a0) (x3 : list a0) (x4 : Prop) (x5 : Prop) := (fun y0 : Prop => ((x3 = (@List.app a0 x0 (@cons a0 x2 x1))) = x4) -> (x4 -> (@List.In a0 x2 x3) = y0) -> ((x3 = (@List.app a0 x0 (@cons a0 x2 x1))) -> @List.In a0 x2 x3) = (x4 -> y0)) x5.
Definition term12 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : Prop, ((exists y1 : a0, x0 y1) -> y0) = (forall y1 : a0, (x0 y1) -> y0).
Definition term7 (a0 : Type') (x0 : list a0) (x1 : a0) := forall y0 : list a0, (@List.In a0 x1 (@List.app a0 x0 y0)) = ((@List.In a0 x1 x0) \/ (@List.In a0 x1 y0)).
Definition term133 (a0 : Type') (x0 : Prop) (x1 : type1143 a0) := x0 /\ (exists y0 : list a0, x1 y0).
Definition term152 (a0 : Type') (x0 : a0) := forall y0 : list a0, (exists y1 : list a0, (~ (@List.In a0 x0 y1)) /\ (exists y2 : list a0, y0 = (@List.app a0 y1 (@cons a0 x0 y2)))) -> exists y1 : list a0, exists y2 : list a0, y0 = (@List.app a0 y1 (@cons a0 x0 y2)).
Definition term119 (a0 : Type') (x0 : a0) := forall y0 : list a0, (exists y1 : list a0, exists y2 : list a0, (~ (@List.In a0 x0 y1)) /\ (y0 = (@List.app a0 y1 (@cons a0 x0 y2)))) -> exists y1 : list a0, exists y2 : list a0, y0 = (@List.app a0 y1 (@cons a0 x0 y2)).
Definition term108 (a0 : Type') (x0 : list a0) (x1 : a0) := and ((@List.In a0 x1 x0) -> exists y0 : list a0, exists y1 : list a0, x0 = (@List.app a0 y0 (@cons a0 x1 y1))).
Definition term109 (a0 : Type') (x0 : list a0) (x1 : a0) := ((@List.In a0 x1 x0) -> exists y0 : list a0, exists y1 : list a0, x0 = (@List.app a0 y0 (@cons a0 x1 y1))) /\ True.
Definition term46 (a0 : Type') (x0 : a0) (x1 : list a0) := forall y0 : list a0, ((fun y1 : list a0 => exists y2 : list a0, x1 = (@List.app a0 y1 (@cons a0 x0 y2))) y0) -> @List.In a0 x0 x1.
Definition term40 (a0 : Type') := fun y0 : a0 => forall y1 : list a0, ((@List.In a0 y0 y1) -> exists y2 : list a0, exists y3 : list a0, y1 = (@List.app a0 y2 (@cons a0 y0 y3))) /\ ((exists y2 : list a0, exists y3 : list a0, y1 = (@List.app a0 y2 (@cons a0 y0 y3))) -> @List.In a0 y0 y1).
Definition term28 (x0 : Prop) := and (True -> x0).
Definition term100 (a0 : Type') (x0 : a0) (x1 : list a0) := (@List.In a0 x0 x1) \/ True.
Definition term49 (a0 : Type') (x0 : list a0) (x1 : list a0) (x2 : a0) := exists y0 : list a0, x0 = (@List.app a0 x1 (@cons a0 x2 y0)).
Definition term70 (a0 : Type') (x0 : list a0) (x1 : list a0) (x2 : a0) := exists y0 : list a0, (fun y1 : list a0 => x0 = (@List.app a0 x1 (@cons a0 x2 y1))) y0.
Definition term14 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) -> x1.
Definition term77 (a0 : Type') (x0 : list a0) (x1 : list a0) (x2 : a0) (x3 : list a0) := (x3 = (@List.app a0 x0 (@cons a0 x2 x1))) -> @List.In a0 x2 x3.
Definition term33 (a0 : Type') (x0 : list a0) (x1 : a0) := exists y0 : list a0, exists y1 : list a0, x0 = (@List.app a0 y0 (@cons a0 x1 y1)).
Definition term3 (a0 : Type') (x0 : list a0) (x1 : a0) := exists y0 : list a0, exists y1 : list a0, (~ (@List.In a0 x1 y0)) /\ (x0 = (@List.app a0 y0 (@cons a0 x1 y1))).
Definition term163 (a0 : Type') (x0 : list a0) (x1 : list a0) (x2 : a0) (x3 : list a0) := ~ ((fun y0 : list a0 => x0 = (@List.app a0 x1 (@cons a0 x2 y0))) x3).
Definition term67 (a0 : Type') (x0 : list a0) (x1 : list a0) (x2 : a0) (x3 : list a0) := (fun y0 : list a0 => x0 = (@List.app a0 x1 (@cons a0 x2 y0))) x3.
Definition term175 (a0 : Type') (x0 : list a0) (x1 : a0) (x2 : list a0) := fun y0 : list a0 => ~ (y0 = (@List.app a0 x0 (@cons a0 x1 x2))).
Definition term142 (a0 : Type') (x0 : list a0) (x1 : list a0) (x2 : a0) := exists y0 : list a0, (~ (@List.In a0 x2 x1)) /\ (x0 = (@List.app a0 x1 (@cons a0 x2 y0))).
Definition term124 (a0 : Type') := ~ (forall y0 : a0, forall y1 : list a0, (exists y2 : list a0, exists y3 : list a0, (~ (@List.In a0 y0 y2)) /\ (y1 = (@List.app a0 y2 (@cons a0 y0 y3)))) -> exists y2 : list a0, exists y3 : list a0, y1 = (@List.app a0 y2 (@cons a0 y0 y3))).
Definition term47 (a0 : Type') (x0 : list a0) (x1 : a0) := fun y0 : list a0 => exists y1 : list a0, x0 = (@List.app a0 y0 (@cons a0 x1 y1)).
Definition term54 (a0 : Type') (x0 : a0) (x1 : list a0) := (exists y0 : list a0, exists y1 : list a0, x1 = (@List.app a0 y0 (@cons a0 x0 y1))) -> @List.In a0 x0 x1.
Definition term104 (a0 : Type') := fun y0 : list a0 => True.
Definition term127 (a0 : Type') := (((~ (forall y0 : a0, forall y1 : list a0, (exists y2 : list a0, exists y3 : list a0, (~ (@List.In a0 y0 y2)) /\ (y1 = (@List.app a0 y2 (@cons a0 y0 y3)))) -> exists y2 : list a0, exists y3 : list a0, y1 = (@List.app a0 y2 (@cons a0 y0 y3)))) -> False) -> (~ (forall y0 : a0, forall y1 : list a0, (exists y2 : list a0, exists y3 : list a0, (~ (@List.In a0 y0 y2)) /\ (y1 = (@List.app a0 y2 (@cons a0 y0 y3)))) -> exists y2 : list a0, exists y3 : list a0, y1 = (@List.app a0 y2 (@cons a0 y0 y3)))) -> False) -> ((~ (forall y0 : a0, forall y1 : list a0, (exists y2 : list a0, exists y3 : list a0, (~ (@List.In a0 y0 y2)) /\ (y1 = (@List.app a0 y2 (@cons a0 y0 y3)))) -> exists y2 : list a0, exists y3 : list a0, y1 = (@List.app a0 y2 (@cons a0 y0 y3)))) -> False) -> (~ (forall y0 : a0, forall y1 : list a0, (exists y2 : list a0, exists y3 : list a0, (~ (@List.In a0 y0 y2)) /\ (y1 = (@List.app a0 y2 (@cons a0 y0 y3)))) -> exists y2 : list a0, exists y3 : list a0, y1 = (@List.app a0 y2 (@cons a0 y0 y3)))) -> False.
Definition term110 (a0 : Type') (x0 : list a0) (x1 : a0) := (@List.In a0 x1 x0) -> exists y0 : list a0, exists y1 : list a0, x0 = (@List.app a0 y0 (@cons a0 x1 y1)).
Definition term168 (a0 : Type') (x0 : list a0) (x1 : a0) := forall y0 : list a0, ~ ((fun y1 : list a0 => exists y2 : list a0, x0 = (@List.app a0 y1 (@cons a0 x1 y2))) y0).
Definition term162 (a0 : Type') (x0 : list a0) (x1 : list a0) (x2 : a0) := forall y0 : list a0, ~ ((fun y1 : list a0 => x0 = (@List.app a0 x1 (@cons a0 x2 y1))) y0).
Definition term139 (a0 : Type') (x0 : list a0) (x1 : list a0) (x2 : a0) (x3 : list a0) := (~ (@List.In a0 x2 x1)) /\ (x0 = (@List.app a0 x1 (@cons a0 x2 x3))).
Definition term181 (a0 : Type') (x0 : list a0) (x1 : a0) (x2 : list a0) := (~ ((@List.app a0 x0 (@cons a0 x1 x2)) = (@List.app a0 x0 (@cons a0 x1 x2)))) -> (@List.app a0 x0 (@cons a0 x1 x2)) = (@List.app a0 x0 (@cons a0 x1 x2)).
Definition term149 (a0 : Type') (x0 : list a0) (x1 : a0) := imp (exists y0 : list a0, (~ (@List.In a0 x1 y0)) /\ (exists y1 : list a0, x0 = (@List.app a0 y0 (@cons a0 x1 y1)))).
Definition term48 (a0 : Type') (x0 : list a0) (x1 : a0) (x2 : list a0) := (fun y0 : list a0 => exists y1 : list a0, x0 = (@List.app a0 y0 (@cons a0 x1 y1))) x2.
Definition term182 (a0 : Type') (x0 : list a0) (x1 : a0) (x2 : list a0) := ~ ((@List.app a0 x0 (@cons a0 x1 x2)) = (@List.app a0 x0 (@cons a0 x1 x2))).
Definition term107 (a0 : Type') (x0 : Prop) := forall y0 : list a0, x0.
Definition term16 (x0 : Prop) := (fun y0 : Prop => (y0 = True) \/ (y0 = False)) x0.
Definition term85 (a0 : Type') (x0 : list a0) (x1 : list a0) (x2 : a0) (x3 : list a0) (x4 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((x3 = (@List.app a0 x0 (@cons a0 x2 x1))) = y0) -> (y0 -> (@List.In a0 x2 x3) = y1) -> ((x3 = (@List.app a0 x0 (@cons a0 x2 x1))) -> @List.In a0 x2 x3) = (y0 -> y1)) x4.
Definition term90 (a0 : Type') (x0 : list a0) (x1 : list a0) (x2 : a0) (x3 : list a0) (x4 : Prop) := ((x0 = (@List.app a0 x1 (@cons a0 x2 x3))) -> (@List.In a0 x2 x0) = x4) -> ((x0 = (@List.app a0 x1 (@cons a0 x2 x3))) -> @List.In a0 x2 x0) = ((x0 = (@List.app a0 x1 (@cons a0 x2 x3))) -> x4).
Definition term78 (a0 : Type') (x0 : list a0) (x1 : a0) (x2 : list a0) := fun y0 : list a0 => ((fun y1 : list a0 => x2 = (@List.app a0 x0 (@cons a0 x1 y1))) y0) -> @List.In a0 x1 x2.
Definition term154 (a0 : Type') := forall y0 : a0, forall y1 : list a0, (exists y2 : list a0, (~ (@List.In a0 y0 y2)) /\ (exists y3 : list a0, y1 = (@List.app a0 y2 (@cons a0 y0 y3)))) -> exists y2 : list a0, exists y3 : list a0, y1 = (@List.app a0 y2 (@cons a0 y0 y3)).
Definition term121 (a0 : Type') := forall y0 : a0, forall y1 : list a0, (exists y2 : list a0, exists y3 : list a0, (~ (@List.In a0 y0 y2)) /\ (y1 = (@List.app a0 y2 (@cons a0 y0 y3)))) -> exists y2 : list a0, exists y3 : list a0, y1 = (@List.app a0 y2 (@cons a0 y0 y3)).
Definition term114 (a0 : Type') := forall y0 : a0, forall y1 : list a0, (@List.In a0 y0 y1) -> exists y2 : list a0, exists y3 : list a0, y1 = (@List.app a0 y2 (@cons a0 y0 y3)).
Definition term42 (a0 : Type') := forall y0 : a0, forall y1 : list a0, ((@List.In a0 y0 y1) -> exists y2 : list a0, exists y3 : list a0, y1 = (@List.app a0 y2 (@cons a0 y0 y3))) /\ ((exists y2 : list a0, exists y3 : list a0, y1 = (@List.app a0 y2 (@cons a0 y0 y3))) -> @List.In a0 y0 y1).
Definition term41 (a0 : Type') := forall y0 : a0, forall y1 : list a0, (@List.In a0 y0 y1) = (exists y2 : list a0, exists y3 : list a0, y1 = (@List.app a0 y2 (@cons a0 y0 y3))).
Definition term95 (a0 : Type') (x0 : a0) (x1 : list a0) := @List.In a0 x0 (@cons a0 x0 x1).
Definition term176 (a0 : Type') (x0 : list a0) (x1 : a0) (x2 : list a0) (x3 : list a0) := (fun y0 : list a0 => ~ (y0 = (@List.app a0 x0 (@cons a0 x1 x2)))) x3.
Definition term174 (a0 : Type') (x0 : list a0) (x1 : list a0) (x2 : a0) (x3 : list a0) := (fun y0 : list a0 => ~ (x0 = (@List.app a0 x1 (@cons a0 x2 y0)))) x3.
Definition term20 (x0 : Prop) := (fun y0 : Prop => (y0 = x0) = ((y0 -> x0) /\ (x0 -> y0))) True.
Definition term59 (a0 : Type') (x0 : list a0) (x1 : a0) (x2 : list a0) := ((fun y0 : list a0 => exists y1 : list a0, x2 = (@List.app a0 y0 (@cons a0 x1 y1))) x0) -> @List.In a0 x1 x2.
Definition term156 (a0 : Type') (x0 : list a0) (x1 : a0) := ~ (exists y0 : list a0, exists y1 : list a0, x0 = (@List.app a0 y0 (@cons a0 x1 y1))).
Definition term99 (a0 : Type') (x0 : a0) (x1 : list a0) := or (@List.In a0 x0 x1).
Definition term35 (a0 : Type') (x0 : a0) := fun y0 : list a0 => (@List.In a0 x0 y0) = (exists y1 : list a0, exists y2 : list a0, y0 = (@List.app a0 y1 (@cons a0 x0 y2))).
Definition term61 (a0 : Type') (x0 : a0) (x1 : list a0) := fun y0 : list a0 => ((fun y1 : list a0 => exists y2 : list a0, x1 = (@List.app a0 y1 (@cons a0 x0 y2))) y0) -> @List.In a0 x0 x1.
Definition term115 (a0 : Type') (x0 : a0) (x1 : list a0) := imp (@List.In a0 x0 x1).
