Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term45 (a0 : Type') := forall y0 : list a0, ((fun y1 : list a0 => (@List.rev a0 (@nil a0)) = (@nil a0)) y0) /\ ((fun y1 : list a0 => forall y2 : a0, (@List.rev a0 (@cons a0 y2 y1)) = (@List.app a0 (@List.rev a0 y1) (@cons a0 y2 (@nil a0)))) y0).
Definition term55 (a0 : Type') := @eq Prop (forall y0 : list a0, ((@List.rev a0 (@nil a0)) = (@nil a0)) /\ (forall y1 : a0, (@List.rev a0 (@cons a0 y1 y0)) = (@List.app a0 (@List.rev a0 y0) (@cons a0 y1 (@nil a0))))).
Definition term49 (a0 : Type') (x0 : list a0) := (fun y0 : list a0 => (@List.rev a0 (@nil a0)) = (@nil a0)) x0.
Definition term141 (a0 : Type') (x0 : list a0) := (~ ((@List.rev a0 (@List.rev a0 x0)) = (@List.rev a0 x0))) -> (@List.rev a0 (@List.rev a0 x0)) = (@List.rev a0 x0).
Definition term166 (a0 : Type') (x0 : list a0) (x1 : list a0) (x2 : list a0) := ((x0 = x1) /\ (x0 = x2)) -> x1 = x2.
Definition term80 (a0 : Type') (x0 : type1143 a0) := ~ (all x0).
Definition term171 := (~ False) -> False.
Definition term34 (a0 : Type') (x0 : list a0) := fun y0 : a0 => (fun y1 : a0 => (@List.rev a0 (@cons a0 y1 x0)) = (@List.app a0 (@List.rev a0 x0) (@cons a0 y1 (@nil a0)))) y0.
Definition term70 (a0 : Type') := ~ (forall y0 : list a0, (@List.rev a0 (@List.rev a0 y0)) = y0).
Definition term3 (a0 : Type') := forall y0 : list a0, ((@List.rev a0 y0) = (@nil a0)) = (y0 = (@nil a0)).
Definition term132 (a0 : Type') (x0 : list a0) := (fun y0 : list a0 => ~ ((@List.rev a0 y0) = (@nil a0))) x0.
Definition term101 (a0 : Type') (x0 : list a0) := (~ ((@List.rev a0 x0) = (@nil a0))) /\ (x0 = (@nil a0)).
Definition term159 (x0 : Prop) := ~ (~ x0).
Definition term57 (a0 : Type') := forall y0 : list a0, (fun y1 : list a0 => (@List.rev a0 (@nil a0)) = (@nil a0)) y0.
Definition term36 (a0 : Type') (x0 : list a0) := forall y0 : a0, (@List.rev a0 (@cons a0 y0 x0)) = (@List.app a0 (@List.rev a0 x0) (@cons a0 y0 (@nil a0))).
Definition term29 (a0 : Type') := fun y0 : a0 => (fun y1 : a0 => (@List.rev a0 (@nil a0)) = (@nil a0)) y0.
Definition term158 (a0 : Type') (x0 : list a0) (x1 : list a0) (x2 : list a0) := (~ (~ (x1 = x0))) /\ (~ (~ (x1 = x2))).
Definition term106 (a0 : Type') := fun y0 : list a0 => (fun y1 : list a0 => ((@List.rev a0 y1) = (@nil a0)) /\ (~ (y1 = (@nil a0)))) y0.
Definition term38 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term89 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term130 (a0 : Type') (x0 : list a0) := @eq Prop (~ (x0 = (@nil a0))).
Definition term69 (a0 : Type') := (forall y0 : list a0, (@List.rev a0 (@List.rev a0 y0)) = y0) -> False.
Definition term119 (a0 : Type') (x0 : list a0) := ~ ((@List.rev a0 x0) = (@nil a0)).
Definition term28 (a0 : Type') (x0 : list a0) := @eq Prop (forall y0 : a0, ((@List.rev a0 (@nil a0)) = (@nil a0)) /\ ((@List.rev a0 (@cons a0 y0 x0)) = (@List.app a0 (@List.rev a0 x0) (@cons a0 y0 (@nil a0))))).
Definition term32 (a0 : Type') := and (forall y0 : a0, (fun y1 : a0 => (@List.rev a0 (@nil a0)) = (@nil a0)) y0).
Definition term167 (a0 : Type') (x0 : list a0) := ((@List.rev a0 (@List.rev a0 x0)) = x0) /\ ((@List.rev a0 (@List.rev a0 x0)) = (@List.rev a0 x0)).
Definition term2 (x0 : Prop) := (~ x0) -> False.
Definition term168 (a0 : Type') (x0 : list a0) := (((@List.rev a0 (@List.rev a0 x0)) = x0) /\ ((@List.rev a0 (@List.rev a0 x0)) = (@List.rev a0 x0))) -> x0 = (@List.rev a0 x0).
Definition term164 (a0 : Type') (x0 : list a0) (x1 : list a0) (x2 : list a0) := imp (~ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term39 (a0 : Type') (x0 : list a0) := ((@List.rev a0 (@nil a0)) = (@nil a0)) /\ (forall y0 : a0, (@List.rev a0 (@cons a0 y0 x0)) = (@List.app a0 (@List.rev a0 x0) (@cons a0 y0 (@nil a0)))).
Definition term41 (a0 : Type') := fun y0 : list a0 => ((@List.rev a0 (@nil a0)) = (@nil a0)) /\ (forall y1 : a0, (@List.rev a0 (@cons a0 y1 y0)) = (@List.app a0 (@List.rev a0 y0) (@cons a0 y1 (@nil a0)))).
Definition term78 (a0 : Type') (x0 : list a0) := ~ (((@List.rev a0 x0) = (@nil a0)) = (x0 = (@nil a0))).
Definition term6 (a0 : Type') := forall y0 : list a0, (@List.rev a0 (@List.rev a0 y0)) = y0.
Definition term63 (a0 : Type') := forall y0 : list a0, forall y1 : a0, (@List.rev a0 (@cons a0 y1 y0)) = (@List.app a0 (@List.rev a0 y0) (@cons a0 y1 (@nil a0))).
Definition term1 (a0 : Type') := forall y0 : list a0, forall y1 : a0, ((@List.rev a0 (@nil a0)) = (@nil a0)) /\ ((@List.rev a0 (@cons a0 y1 y0)) = (@List.app a0 (@List.rev a0 y0) (@cons a0 y1 (@nil a0)))).
Definition term94 (a0 : Type') := fun y0 : list a0 => ((@List.rev a0 y0) = (@nil a0)) /\ (~ (y0 = (@nil a0))).
Definition term104 (a0 : Type') := @eq Prop (exists y0 : list a0, ((fun y1 : list a0 => ((@List.rev a0 y1) = (@nil a0)) /\ (~ (y1 = (@nil a0)))) y0) \/ ((fun y1 : list a0 => (~ ((@List.rev a0 y1) = (@nil a0))) /\ (y1 = (@nil a0))) y0)).
Definition term52 (a0 : Type') (x0 : list a0) := ((fun y0 : list a0 => (@List.rev a0 (@nil a0)) = (@nil a0)) x0) /\ ((fun y0 : list a0 => forall y1 : a0, (@List.rev a0 (@cons a0 y1 y0)) = (@List.app a0 (@List.rev a0 y0) (@cons a0 y1 (@nil a0)))) x0).
Definition term108 (a0 : Type') := exists y0 : list a0, ((@List.rev a0 y0) = (@nil a0)) /\ (~ (y0 = (@nil a0))).
Definition term35 (a0 : Type') (x0 : list a0) := forall y0 : a0, (fun y1 : a0 => (@List.rev a0 (@cons a0 y1 x0)) = (@List.app a0 (@List.rev a0 x0) (@cons a0 y1 (@nil a0)))) y0.
Definition term152 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term129 (a0 : Type') (x0 : list a0) := @eq Prop ((fun y0 : list a0 => ~ (x0 = y0)) (@nil a0)).
Definition term48 (a0 : Type') := fun y0 : list a0 => forall y1 : a0, (@List.rev a0 (@cons a0 y1 y0)) = (@List.app a0 (@List.rev a0 y0) (@cons a0 y1 (@nil a0))).
Definition term40 (a0 : Type') := fun y0 : list a0 => forall y1 : a0, ((@List.rev a0 (@nil a0)) = (@nil a0)) /\ ((@List.rev a0 (@cons a0 y1 y0)) = (@List.app a0 (@List.rev a0 y0) (@cons a0 y1 (@nil a0)))).
Definition term162 (a0 : Type') (x0 : list a0) (x1 : list a0) := and (x0 = x1).
Definition term124 (a0 : Type') := @eq Prop ((@List.rev a0 (@nil a0)) = (@nil a0)).
Definition term20 (a0 : Type') (x0 : list a0) (x1 : a0) := (fun y0 : a0 => (@List.rev a0 (@cons a0 y0 x0)) = (@List.app a0 (@List.rev a0 x0) (@cons a0 y0 (@nil a0)))) x1.
Definition term25 (a0 : Type') (x0 : list a0) := fun y0 : a0 => ((fun y1 : a0 => (@List.rev a0 (@nil a0)) = (@nil a0)) y0) /\ ((fun y1 : a0 => (@List.rev a0 (@cons a0 y1 x0)) = (@List.app a0 (@List.rev a0 x0) (@cons a0 y1 (@nil a0)))) y0).
Definition term140 (x0 : Prop) := (~ x0) -> x0.
Definition term8 (a0 : Type') := ((~ (forall y0 : list a0, ((@List.rev a0 y0) = (@nil a0)) = (y0 = (@nil a0)))) -> (forall y0 : list a0, forall y1 : a0, ((@List.rev a0 (@nil a0)) = (@nil a0)) /\ ((@List.rev a0 (@cons a0 y1 y0)) = (@List.app a0 (@List.rev a0 y0) (@cons a0 y1 (@nil a0))))) -> (forall y0 : list a0, (@List.rev a0 (@List.rev a0 y0)) = y0) -> False) -> (~ (forall y0 : list a0, ((@List.rev a0 y0) = (@nil a0)) = (y0 = (@nil a0)))) -> (forall y0 : list a0, forall y1 : a0, ((@List.rev a0 (@nil a0)) = (@nil a0)) /\ ((@List.rev a0 (@cons a0 y1 y0)) = (@List.app a0 (@List.rev a0 y0) (@cons a0 y1 (@nil a0))))) -> (forall y0 : list a0, (@List.rev a0 (@List.rev a0 y0)) = y0) -> False.
Definition term154 (a0 : Type') (x0 : list a0) (x1 : list a0) (x2 : list a0) := (~ (x1 = x0)) \/ (~ (x1 = x2)).
Definition term156 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term74 (a0 : Type') := (~ (forall y0 : list a0, ((@List.rev a0 y0) = (@nil a0)) = (y0 = (@nil a0)))) -> (((@List.rev a0 (@nil a0)) = (@nil a0)) /\ (forall y0 : list a0, forall y1 : a0, (@List.rev a0 (@cons a0 y1 y0)) = (@List.app a0 (@List.rev a0 y0) (@cons a0 y1 (@nil a0))))) -> ~ (forall y0 : list a0, (@List.rev a0 (@List.rev a0 y0)) = y0).
Definition term150 (a0 : Type') (x0 : list a0) (x1 : list a0) (x2 : list a0) := @eq Prop ((~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2))).
Definition term134 (a0 : Type') := ~ ((@List.rev a0 (@nil a0)) = (@nil a0)).
Definition term44 (a0 : Type') (x0 : type1143 a0) (x1 : type1143 a0) := (forall y0 : list a0, x0 y0) /\ (forall y0 : list a0, x1 y0).
Definition term151 (a0 : Type') (x0 : list a0) (x1 : list a0) (x2 : list a0) := @eq Prop ((x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term30 (a0 : Type') := forall y0 : a0, (fun y1 : a0 => (@List.rev a0 (@nil a0)) = (@nil a0)) y0.
Definition term12 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term24 (a0 : Type') (x0 : list a0) (x1 : a0) := ((@List.rev a0 (@nil a0)) = (@nil a0)) /\ ((@List.rev a0 (@cons a0 x1 x0)) = (@List.app a0 (@List.rev a0 x0) (@cons a0 x1 (@nil a0)))).
Definition term71 (a0 : Type') := (forall y0 : list a0, forall y1 : a0, ((@List.rev a0 (@nil a0)) = (@nil a0)) /\ ((@List.rev a0 (@cons a0 y1 y0)) = (@List.app a0 (@List.rev a0 y0) (@cons a0 y1 (@nil a0))))) -> (forall y0 : list a0, (@List.rev a0 (@List.rev a0 y0)) = y0) -> False.
Definition term105 (a0 : Type') := @eq Prop (exists y0 : list a0, (((@List.rev a0 y0) = (@nil a0)) /\ (~ (y0 = (@nil a0)))) \/ ((~ ((@List.rev a0 y0) = (@nil a0))) /\ (y0 = (@nil a0)))).
Definition term60 (a0 : Type') := and (forall y0 : list a0, (@List.rev a0 (@nil a0)) = (@nil a0)).
Definition term148 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term43 (a0 : Type') (x0 : type1143 a0) (x1 : type1143 a0) := forall y0 : list a0, (x0 y0) /\ (x1 y0).
Definition term13 (a0 : Type') (x0 : list a0) := forall y0 : a0, ((fun y1 : a0 => (@List.rev a0 (@nil a0)) = (@nil a0)) y0) /\ ((fun y1 : a0 => (@List.rev a0 (@cons a0 y1 x0)) = (@List.app a0 (@List.rev a0 x0) (@cons a0 y1 (@nil a0)))) y0).
Definition term91 (a0 : Type') (x0 : type1143 a0) (x1 : type1143 a0) := (exists y0 : list a0, x0 y0) \/ (exists y0 : list a0, x1 y0).
Definition term5 (a0 : Type') := ~ (forall y0 : list a0, ((@List.rev a0 y0) = (@nil a0)) = (y0 = (@nil a0))).
Definition term66 (a0 : Type') := ((@List.rev a0 (@nil a0)) = (@nil a0)) /\ (forall y0 : list a0, forall y1 : a0, (@List.rev a0 (@cons a0 y1 y0)) = (@List.app a0 (@List.rev a0 y0) (@cons a0 y1 (@nil a0)))).
Definition term50 (a0 : Type') (x0 : list a0) := and ((fun y0 : list a0 => (@List.rev a0 (@nil a0)) = (@nil a0)) x0).
Definition term137 (a0 : Type') (x0 : list a0) (x1 : list a0) (x2 : list a0) := (~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2)).
Definition term172 (a0 : Type') := (~ ((@List.rev a0 (@nil a0)) = (@nil a0))) -> (@List.rev a0 (@nil a0)) = (@nil a0).
Definition term114 (a0 : Type') := (exists y0 : list a0, ((@List.rev a0 y0) = (@nil a0)) /\ (~ (y0 = (@nil a0)))) \/ (exists y0 : list a0, (~ ((@List.rev a0 y0) = (@nil a0))) /\ (y0 = (@nil a0))).
Definition term62 (a0 : Type') := forall y0 : list a0, (fun y1 : list a0 => forall y2 : a0, (@List.rev a0 (@cons a0 y2 y1)) = (@List.app a0 (@List.rev a0 y1) (@cons a0 y2 (@nil a0)))) y0.
Definition term103 (a0 : Type') := fun y0 : list a0 => ((fun y1 : list a0 => ((@List.rev a0 y1) = (@nil a0)) /\ (~ (y1 = (@nil a0)))) y0) \/ ((fun y1 : list a0 => (~ ((@List.rev a0 y1) = (@nil a0))) /\ (y1 = (@nil a0))) y0).
Definition term96 (a0 : Type') (x0 : list a0) := (fun y0 : list a0 => ((@List.rev a0 y0) = (@nil a0)) /\ (~ (y0 = (@nil a0)))) x0.
Definition term97 (a0 : Type') (x0 : list a0) := ((@List.rev a0 x0) = (@nil a0)) /\ (~ (x0 = (@nil a0))).
Definition term77 (a0 : Type') := fun y0 : list a0 => ((@List.rev a0 y0) = (@nil a0)) = (y0 = (@nil a0)).
Definition term149 (a0 : Type') (x0 : list a0) (x1 : list a0) (x2 : list a0) := (x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term86 (a0 : Type') := fun y0 : list a0 => (((@List.rev a0 y0) = (@nil a0)) /\ (~ (y0 = (@nil a0)))) \/ ((~ ((@List.rev a0 y0) = (@nil a0))) /\ (y0 = (@nil a0))).
Definition term131 (a0 : Type') := fun y0 : list a0 => ~ ((@List.rev a0 y0) = (@nil a0)).
Definition term31 (a0 : Type') := forall y0 : a0, (@List.rev a0 (@nil a0)) = (@nil a0).
Definition term109 (a0 : Type') := or (exists y0 : list a0, (fun y1 : list a0 => ((@List.rev a0 y1) = (@nil a0)) /\ (~ (y1 = (@nil a0)))) y0).
Definition term19 (a0 : Type') := and ((@List.rev a0 (@nil a0)) = (@nil a0)).
Definition term83 (a0 : Type') (x0 : list a0) := (fun y0 : list a0 => ((@List.rev a0 y0) = (@nil a0)) = (y0 = (@nil a0))) x0.
Definition term155 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term61 (a0 : Type') := fun y0 : list a0 => (fun y1 : list a0 => forall y2 : a0, (@List.rev a0 (@cons a0 y2 y1)) = (@List.app a0 (@List.rev a0 y1) (@cons a0 y2 (@nil a0)))) y0.
Definition term135 (a0 : Type') (x0 : list a0) := @eq Prop ((fun y0 : list a0 => ~ ((@List.rev a0 y0) = (@nil a0))) x0).
Definition term51 (a0 : Type') (x0 : list a0) := (fun y0 : list a0 => forall y1 : a0, (@List.rev a0 (@cons a0 y1 y0)) = (@List.app a0 (@List.rev a0 y0) (@cons a0 y1 (@nil a0)))) x0.
Definition term139 (a0 : Type') (x0 : list a0) := ~ ((@List.rev a0 (@List.rev a0 x0)) = x0).
Definition term136 (a0 : Type') (x0 : list a0) := @eq Prop (~ ((@List.rev a0 x0) = (@nil a0))).
Definition term75 (a0 : Type') (x0 : list a0) := @List.rev a0 (@List.rev a0 x0).
Definition term125 (a0 : Type') (x0 : list a0) := fun y0 : list a0 => ~ (x0 = y0).
Definition term42 (a0 : Type') := forall y0 : list a0, ((@List.rev a0 (@nil a0)) = (@nil a0)) /\ (forall y1 : a0, (@List.rev a0 (@cons a0 y1 y0)) = (@List.app a0 (@List.rev a0 y0) (@cons a0 y1 (@nil a0)))).
Definition term9 (a0 : Type') := (((~ (forall y0 : list a0, ((@List.rev a0 y0) = (@nil a0)) = (y0 = (@nil a0)))) -> (forall y0 : list a0, forall y1 : a0, ((@List.rev a0 (@nil a0)) = (@nil a0)) /\ ((@List.rev a0 (@cons a0 y1 y0)) = (@List.app a0 (@List.rev a0 y0) (@cons a0 y1 (@nil a0))))) -> (forall y0 : list a0, (@List.rev a0 (@List.rev a0 y0)) = y0) -> False) -> (~ (forall y0 : list a0, ((@List.rev a0 y0) = (@nil a0)) = (y0 = (@nil a0)))) -> (forall y0 : list a0, forall y1 : a0, ((@List.rev a0 (@nil a0)) = (@nil a0)) /\ ((@List.rev a0 (@cons a0 y1 y0)) = (@List.app a0 (@List.rev a0 y0) (@cons a0 y1 (@nil a0))))) -> (forall y0 : list a0, (@List.rev a0 (@List.rev a0 y0)) = y0) -> False) -> (~ (forall y0 : list a0, ((@List.rev a0 y0) = (@nil a0)) = (y0 = (@nil a0)))) -> (forall y0 : list a0, forall y1 : a0, ((@List.rev a0 (@nil a0)) = (@nil a0)) /\ ((@List.rev a0 (@cons a0 y1 y0)) = (@List.app a0 (@List.rev a0 y0) (@cons a0 y1 (@nil a0))))) -> (forall y0 : list a0, (@List.rev a0 (@List.rev a0 y0)) = y0) -> False.
Definition term90 (a0 : Type') (x0 : type1143 a0) (x1 : type1143 a0) := exists y0 : list a0, (x0 y0) \/ (x1 y0).
Definition term93 (a0 : Type') := (exists y0 : list a0, (fun y1 : list a0 => ((@List.rev a0 y1) = (@nil a0)) /\ (~ (y1 = (@nil a0)))) y0) \/ (exists y0 : list a0, (fun y1 : list a0 => (~ ((@List.rev a0 y1) = (@nil a0))) /\ (y1 = (@nil a0))) y0).
Definition term16 (a0 : Type') (x0 : list a0) := fun y0 : a0 => (@List.rev a0 (@cons a0 y0 x0)) = (@List.app a0 (@List.rev a0 x0) (@cons a0 y0 (@nil a0))).
Definition term142 (a0 : Type') (x0 : list a0) := ~ ((@List.rev a0 (@List.rev a0 x0)) = (@List.rev a0 x0)).
Definition term143 (a0 : Type') (x0 : list a0) (x1 : list a0) (x2 : list a0) := (~ (x0 = x2)) \/ (x1 = x2).
Definition term84 (a0 : Type') (x0 : list a0) := ~ ((fun y0 : list a0 => ((@List.rev a0 y0) = (@nil a0)) = (y0 = (@nil a0))) x0).
Definition term123 (a0 : Type') := @eq Prop ((fun y0 : list a0 => (@List.rev a0 y0) = y0) (@nil a0)).
Definition term0 (a0 : Type') (x0 : list a0) := forall y0 : a0, ((@List.rev a0 (@nil a0)) = (@nil a0)) /\ ((@List.rev a0 (@cons a0 y0 x0)) = (@List.app a0 (@List.rev a0 x0) (@cons a0 y0 (@nil a0)))).
Definition term76 (a0 : Type') := fun y0 : list a0 => (@List.rev a0 (@List.rev a0 y0)) = y0.
Definition term81 (a0 : Type') (x0 : type1143 a0) := exists y0 : list a0, ~ (x0 y0).
Definition term53 (a0 : Type') := fun y0 : list a0 => ((fun y1 : list a0 => (@List.rev a0 (@nil a0)) = (@nil a0)) y0) /\ ((fun y1 : list a0 => forall y2 : a0, (@List.rev a0 (@cons a0 y2 y1)) = (@List.app a0 (@List.rev a0 y1) (@cons a0 y2 (@nil a0)))) y0).
Definition term127 (a0 : Type') (x0 : list a0) := (fun y0 : list a0 => ~ (x0 = y0)) (@List.rev a0 x0).
Definition term173 (a0 : Type') := ((@List.rev a0 (@nil a0)) = (@nil a0)) -> False.
Definition term169 (a0 : Type') (x0 : list a0) := (~ (x0 = (@List.rev a0 x0))) -> x0 = (@List.rev a0 x0).
Definition term79 (a0 : Type') (x0 : list a0) := (((@List.rev a0 x0) = (@nil a0)) /\ (~ (x0 = (@nil a0)))) \/ ((~ ((@List.rev a0 x0) = (@nil a0))) /\ (x0 = (@nil a0))).
Definition term4 (a0 : Type') := (~ (forall y0 : list a0, ((@List.rev a0 y0) = (@nil a0)) = (y0 = (@nil a0)))) -> False.
Definition term22 (a0 : Type') (x0 : list a0) (x1 : a0) := @List.app a0 (@List.rev a0 x0) (@cons a0 x1 (@nil a0)).
Definition term138 (a0 : Type') (x0 : list a0) := (~ ((@List.rev a0 (@List.rev a0 x0)) = x0)) -> (@List.rev a0 (@List.rev a0 x0)) = x0.
Definition term85 (a0 : Type') := fun y0 : list a0 => ~ ((fun y1 : list a0 => ((@List.rev a0 y1) = (@nil a0)) = (y1 = (@nil a0))) y0).
Definition term147 (a0 : Type') (x0 : list a0) (x1 : list a0) (x2 : list a0) := (~ (x1 = x0)) \/ ((x0 = x2) \/ (~ (x1 = x2))).
Definition term87 (a0 : Type') := exists y0 : list a0, (((@List.rev a0 y0) = (@nil a0)) /\ (~ (y0 = (@nil a0)))) \/ ((~ ((@List.rev a0 y0) = (@nil a0))) /\ (y0 = (@nil a0))).
Definition term126 (a0 : Type') (x0 : list a0) := (fun y0 : list a0 => ~ (x0 = y0)) (@nil a0).
Definition term128 (a0 : Type') (x0 : list a0) := ~ (x0 = (@List.rev a0 x0)).
Definition term10 (a0 : Type') := (((~ (forall y0 : list a0, ((@List.rev a0 y0) = (@nil a0)) = (y0 = (@nil a0)))) -> (forall y0 : list a0, forall y1 : a0, ((@List.rev a0 (@nil a0)) = (@nil a0)) /\ ((@List.rev a0 (@cons a0 y1 y0)) = (@List.app a0 (@List.rev a0 y0) (@cons a0 y1 (@nil a0))))) -> (forall y0 : list a0, (@List.rev a0 (@List.rev a0 y0)) = y0) -> False) -> (~ (forall y0 : list a0, ((@List.rev a0 y0) = (@nil a0)) = (y0 = (@nil a0)))) -> (forall y0 : list a0, forall y1 : a0, ((@List.rev a0 (@nil a0)) = (@nil a0)) /\ ((@List.rev a0 (@cons a0 y1 y0)) = (@List.app a0 (@List.rev a0 y0) (@cons a0 y1 (@nil a0))))) -> (forall y0 : list a0, (@List.rev a0 (@List.rev a0 y0)) = y0) -> False) -> ((~ (forall y0 : list a0, ((@List.rev a0 y0) = (@nil a0)) = (y0 = (@nil a0)))) -> (forall y0 : list a0, forall y1 : a0, ((@List.rev a0 (@nil a0)) = (@nil a0)) /\ ((@List.rev a0 (@cons a0 y1 y0)) = (@List.app a0 (@List.rev a0 y0) (@cons a0 y1 (@nil a0))))) -> (forall y0 : list a0, (@List.rev a0 (@List.rev a0 y0)) = y0) -> False) -> (~ (forall y0 : list a0, ((@List.rev a0 y0) = (@nil a0)) = (y0 = (@nil a0)))) -> (forall y0 : list a0, forall y1 : a0, ((@List.rev a0 (@nil a0)) = (@nil a0)) /\ ((@List.rev a0 (@cons a0 y1 y0)) = (@List.app a0 (@List.rev a0 y0) (@cons a0 y1 (@nil a0))))) -> (forall y0 : list a0, (@List.rev a0 (@List.rev a0 y0)) = y0) -> False.
Definition term58 (a0 : Type') := forall y0 : list a0, (@List.rev a0 (@nil a0)) = (@nil a0).
Definition term161 (a0 : Type') (x0 : list a0) (x1 : list a0) := and (~ (~ (x0 = x1))).
Definition term56 (a0 : Type') := fun y0 : list a0 => (fun y1 : list a0 => (@List.rev a0 (@nil a0)) = (@nil a0)) y0.
Definition term133 (a0 : Type') := (fun y0 : list a0 => ~ ((@List.rev a0 y0) = (@nil a0))) (@nil a0).
Definition term118 (a0 : Type') (x0 : list a0) := ~ (x0 = (@nil a0)).
Definition term17 (a0 : Type') (x0 : a0) := (fun y0 : a0 => (@List.rev a0 (@nil a0)) = (@nil a0)) x0.
Definition term95 (a0 : Type') := fun y0 : list a0 => (~ ((@List.rev a0 y0) = (@nil a0))) /\ (y0 = (@nil a0)).
Definition term163 (a0 : Type') (x0 : list a0) (x1 : list a0) (x2 : list a0) := (x1 = x0) /\ (x1 = x2).
Definition term37 (a0 : Type') (x0 : list a0) := (forall y0 : a0, (@List.rev a0 (@nil a0)) = (@nil a0)) /\ (forall y0 : a0, (@List.rev a0 (@cons a0 y0 x0)) = (@List.app a0 (@List.rev a0 x0) (@cons a0 y0 (@nil a0)))).
Definition term54 (a0 : Type') := @eq Prop (forall y0 : list a0, ((fun y1 : list a0 => (@List.rev a0 (@nil a0)) = (@nil a0)) y0) /\ ((fun y1 : list a0 => forall y2 : a0, (@List.rev a0 (@cons a0 y2 y1)) = (@List.app a0 (@List.rev a0 y1) (@cons a0 y2 (@nil a0)))) y0)).
Definition term110 (a0 : Type') := or (exists y0 : list a0, ((@List.rev a0 y0) = (@nil a0)) /\ (~ (y0 = (@nil a0)))).
Definition term47 (a0 : Type') := fun y0 : list a0 => (@List.rev a0 (@nil a0)) = (@nil a0).
Definition term68 (a0 : Type') := imp (((@List.rev a0 (@nil a0)) = (@nil a0)) /\ (forall y0 : list a0, forall y1 : a0, (@List.rev a0 (@cons a0 y1 y0)) = (@List.app a0 (@List.rev a0 y0) (@cons a0 y1 (@nil a0))))).
Definition term153 (a0 : Type') (x0 : list a0) (x1 : list a0) (x2 : list a0) := (~ ((~ (x0 = x1)) \/ (~ (x0 = x2)))) -> x1 = x2.
Definition term113 (a0 : Type') := exists y0 : list a0, (~ ((@List.rev a0 y0) = (@nil a0))) /\ (y0 = (@nil a0)).
Definition term82 (a0 : Type') := exists y0 : list a0, ~ ((fun y1 : list a0 => ((@List.rev a0 y1) = (@nil a0)) = (y1 = (@nil a0))) y0).
Definition term72 (a0 : Type') := (((@List.rev a0 (@nil a0)) = (@nil a0)) /\ (forall y0 : list a0, forall y1 : a0, (@List.rev a0 (@cons a0 y1 y0)) = (@List.app a0 (@List.rev a0 y0) (@cons a0 y1 (@nil a0))))) -> ~ (forall y0 : list a0, (@List.rev a0 (@List.rev a0 y0)) = y0).
Definition term67 (a0 : Type') := imp (forall y0 : list a0, forall y1 : a0, ((@List.rev a0 (@nil a0)) = (@nil a0)) /\ ((@List.rev a0 (@cons a0 y1 y0)) = (@List.app a0 (@List.rev a0 y0) (@cons a0 y1 (@nil a0))))).
Definition term157 (a0 : Type') (x0 : list a0) (x1 : list a0) (x2 : list a0) := ~ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term112 (a0 : Type') := exists y0 : list a0, (fun y1 : list a0 => (~ ((@List.rev a0 y1) = (@nil a0))) /\ (y1 = (@nil a0))) y0.
Definition term107 (a0 : Type') := exists y0 : list a0, (fun y1 : list a0 => ((@List.rev a0 y1) = (@nil a0)) /\ (~ (y1 = (@nil a0)))) y0.
Definition term111 (a0 : Type') := fun y0 : list a0 => (fun y1 : list a0 => (~ ((@List.rev a0 y1) = (@nil a0))) /\ (y1 = (@nil a0))) y0.
Definition term121 (a0 : Type') := (fun y0 : list a0 => (@List.rev a0 y0) = y0) (@nil a0).
Definition term21 (a0 : Type') (x0 : a0) (x1 : list a0) := @List.rev a0 (@cons a0 x0 x1).
Definition term64 (a0 : Type') := (forall y0 : list a0, (@List.rev a0 (@nil a0)) = (@nil a0)) /\ (forall y0 : list a0, forall y1 : a0, (@List.rev a0 (@cons a0 y1 y0)) = (@List.app a0 (@List.rev a0 y0) (@cons a0 y1 (@nil a0)))).
Definition term23 (a0 : Type') (x0 : list a0) (x1 : a0) := ((fun y0 : a0 => (@List.rev a0 (@nil a0)) = (@nil a0)) x1) /\ ((fun y0 : a0 => (@List.rev a0 (@cons a0 y0 x0)) = (@List.app a0 (@List.rev a0 x0) (@cons a0 y0 (@nil a0)))) x1).
Definition term165 (a0 : Type') (x0 : list a0) (x1 : list a0) (x2 : list a0) := imp ((x1 = x0) /\ (x1 = x2)).
Definition term11 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term98 (a0 : Type') (x0 : list a0) := or ((fun y0 : list a0 => ((@List.rev a0 y0) = (@nil a0)) /\ (~ (y0 = (@nil a0)))) x0).
Definition term170 (a0 : Type') (x0 : list a0) := (x0 = (@List.rev a0 x0)) -> False.
Definition term117 (a0 : Type') (x0 : list a0) := (fun y0 : list a0 => (@List.rev a0 (@List.rev a0 y0)) = y0) x0.
Definition term18 (a0 : Type') (x0 : a0) := and ((fun y0 : a0 => (@List.rev a0 (@nil a0)) = (@nil a0)) x0).
Definition term59 (a0 : Type') := and (forall y0 : list a0, (fun y1 : list a0 => (@List.rev a0 (@nil a0)) = (@nil a0)) y0).
Definition term99 (a0 : Type') (x0 : list a0) := or (((@List.rev a0 x0) = (@nil a0)) /\ (~ (x0 = (@nil a0)))).
Definition term14 (a0 : Type') (x0 : list a0) := (forall y0 : a0, (fun y1 : a0 => (@List.rev a0 (@nil a0)) = (@nil a0)) y0) /\ (forall y0 : a0, (fun y1 : a0 => (@List.rev a0 (@cons a0 y1 x0)) = (@List.app a0 (@List.rev a0 x0) (@cons a0 y1 (@nil a0)))) y0).
Definition term120 (a0 : Type') := fun y0 : list a0 => (@List.rev a0 y0) = y0.
Definition term26 (a0 : Type') (x0 : list a0) := fun y0 : a0 => ((@List.rev a0 (@nil a0)) = (@nil a0)) /\ ((@List.rev a0 (@cons a0 y0 x0)) = (@List.app a0 (@List.rev a0 x0) (@cons a0 y0 (@nil a0)))).
Definition term27 (a0 : Type') (x0 : list a0) := @eq Prop (forall y0 : a0, ((fun y1 : a0 => (@List.rev a0 (@nil a0)) = (@nil a0)) y0) /\ ((fun y1 : a0 => (@List.rev a0 (@cons a0 y1 x0)) = (@List.app a0 (@List.rev a0 x0) (@cons a0 y1 (@nil a0)))) y0)).
Definition term102 (a0 : Type') (x0 : list a0) := ((fun y0 : list a0 => ((@List.rev a0 y0) = (@nil a0)) /\ (~ (y0 = (@nil a0)))) x0) \/ ((fun y0 : list a0 => (~ ((@List.rev a0 y0) = (@nil a0))) /\ (y0 = (@nil a0))) x0).
Definition term145 (a0 : Type') (x0 : list a0) (x1 : list a0) := ~ (x0 = x1).
Definition term160 (a0 : Type') (x0 : list a0) (x1 : list a0) := ~ (~ (x0 = x1)).
Definition term65 (a0 : Type') (x0 : Prop) := forall y0 : list a0, x0.
Definition term15 (a0 : Type') := fun y0 : a0 => (@List.rev a0 (@nil a0)) = (@nil a0).
Definition term46 (a0 : Type') := (forall y0 : list a0, (fun y1 : list a0 => (@List.rev a0 (@nil a0)) = (@nil a0)) y0) /\ (forall y0 : list a0, (fun y1 : list a0 => forall y2 : a0, (@List.rev a0 (@cons a0 y2 y1)) = (@List.app a0 (@List.rev a0 y1) (@cons a0 y2 (@nil a0)))) y0).
Definition term146 (a0 : Type') (x0 : list a0) (x1 : list a0) := or (~ (x0 = x1)).
Definition term144 (a0 : Type') (x0 : list a0) (x1 : list a0) (x2 : list a0) := (x0 = x2) \/ (~ (x1 = x2)).
Definition term92 (a0 : Type') := exists y0 : list a0, ((fun y1 : list a0 => ((@List.rev a0 y1) = (@nil a0)) /\ (~ (y1 = (@nil a0)))) y0) \/ ((fun y1 : list a0 => (~ ((@List.rev a0 y1) = (@nil a0))) /\ (y1 = (@nil a0))) y0).
Definition term88 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term7 (a0 : Type') := (~ (forall y0 : list a0, ((@List.rev a0 y0) = (@nil a0)) = (y0 = (@nil a0)))) -> (forall y0 : list a0, forall y1 : a0, ((@List.rev a0 (@nil a0)) = (@nil a0)) /\ ((@List.rev a0 (@cons a0 y1 y0)) = (@List.app a0 (@List.rev a0 y0) (@cons a0 y1 (@nil a0))))) -> (forall y0 : list a0, (@List.rev a0 (@List.rev a0 y0)) = y0) -> False.
Definition term33 (a0 : Type') := and (forall y0 : a0, (@List.rev a0 (@nil a0)) = (@nil a0)).
Definition term100 (a0 : Type') (x0 : list a0) := (fun y0 : list a0 => (~ ((@List.rev a0 y0) = (@nil a0))) /\ (y0 = (@nil a0))) x0.
Definition term122 (a0 : Type') (x0 : list a0) := (fun y0 : list a0 => (@List.rev a0 y0) = y0) (@List.rev a0 x0).
Definition term73 (a0 : Type') := imp (~ (forall y0 : list a0, ((@List.rev a0 y0) = (@nil a0)) = (y0 = (@nil a0)))).
Definition term116 (a0 : Type') := @eq Prop ((exists y0 : list a0, ((@List.rev a0 y0) = (@nil a0)) /\ (~ (y0 = (@nil a0)))) \/ (exists y0 : list a0, (~ ((@List.rev a0 y0) = (@nil a0))) /\ (y0 = (@nil a0)))).
Definition term115 (a0 : Type') := @eq Prop ((exists y0 : list a0, (fun y1 : list a0 => ((@List.rev a0 y1) = (@nil a0)) /\ (~ (y1 = (@nil a0)))) y0) \/ (exists y0 : list a0, (fun y1 : list a0 => (~ ((@List.rev a0 y1) = (@nil a0))) /\ (y1 = (@nil a0))) y0)).
