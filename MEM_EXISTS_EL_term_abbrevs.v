Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term163 (x0 : nat -> nat) := fun y0 : nat => (fun y1 : nat => fun y2 : nat => (y1 = (NUMERAL 0)) \/ (y1 = (S y2))) y0 (x0 y0).
Definition term327 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) (x3 : nat) := (fun y0 : nat => (Peano.lt y0 (S (@List.length a0 x2))) /\ (x0 = (@EL a0 y0 (@cons a0 x1 x2)))) (S x3).
Definition term187 (x0 : nat) (x1 : nat) := ~ (x0 = x1).
Definition term33 (x0 : nat -> Prop) := fun y0 : nat => x0 y0.
Definition term139 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) \/ (x0 = (S x1)).
Definition term218 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := ~ ((~ (x2 = x0)) \/ (~ (x1 x2))).
Definition term324 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) := (Peano.lt (NUMERAL 0) (S (@List.length a0 x2))) /\ (x0 = (@EL a0 (NUMERAL 0) (@cons a0 x1 x2))).
Definition term234 := (~ False) -> False.
Definition term41 (x0 : nat -> Prop) (x1 : nat) := ~ (x0 x1).
Definition term1 (x0 : nat) := Peano.lt (NUMERAL 0) (S x0).
Definition term115 (x0 : nat) (x1 : nat -> Prop) := (x1 x0) /\ ((~ (x1 (NUMERAL 0))) /\ (forall y0 : nat, ~ (x1 (S y0)))).
Definition term171 (x0 : nat -> nat) (x1 : nat) := (fun y0 : nat => (y0 = (NUMERAL 0)) \/ (y0 = (S (x0 y0)))) x1.
Definition term67 (x0 : nat -> Prop) := ((exists y0 : nat, x0 y0) /\ ((~ (x0 (NUMERAL 0))) /\ (forall y0 : nat, ~ (x0 (S y0))))) \/ ((forall y0 : nat, ~ (x0 y0)) /\ ((x0 (NUMERAL 0)) \/ (exists y0 : nat, x0 (S y0)))).
Definition term46 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => x0 (S y0)) x1.
Definition term61 (x0 : nat -> Prop) := and (exists y0 : nat, x0 y0).
Definition term124 (x0 : nat -> Prop) (x1 : nat) := or ((fun y0 : nat => (x0 y0) /\ ((~ (x0 (NUMERAL 0))) /\ (forall y1 : nat, ~ (x0 (S y1))))) x1).
Definition term308 (a0 : Type') (x0 : a0) (x1 : nat) (x2 : a0) (x3 : list a0) := (Peano.lt x1 (@List.length a0 (@cons a0 x2 x3))) /\ (x0 = (@EL a0 x1 (@cons a0 x2 x3))).
Definition term277 (a0 : Type') (x0 : a0) (x1 : nat) := (Peano.lt x1 (@List.length a0 (@nil a0))) /\ (x0 = (@EL a0 x1 (@nil a0))).
Definition term281 (a0 : Type') (x0 : a0) := exists y0 : nat, (Peano.lt y0 (@List.length a0 (@nil a0))) /\ (x0 = (@EL a0 y0 (@nil a0))).
Definition term295 (a0 : Type') (x0 : list a0) (x1 : a0) := (fun y0 : a0 => (@List.In a0 y0 x0) = (exists y1 : nat, (Peano.lt y1 (@List.length a0 x0)) /\ (y0 = (@EL a0 y1 x0)))) x1.
Definition term192 (x0 : Prop) := ~ (~ x0).
Definition term338 (a0 : Type') (x0 : a0) (x1 : list a0) := @hd a0 (@cons a0 x0 x1).
Definition term323 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) := (fun y0 : nat => (Peano.lt y0 (S (@List.length a0 x2))) /\ (x0 = (@EL a0 y0 (@cons a0 x1 x2)))) (NUMERAL 0).
Definition term293 (a0 : Type') (x0 : a0) (x1 : list a0) := @List.length a0 (@cons a0 x0 x1).
Definition term219 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (~ (~ (x2 = x0))) /\ (~ (~ (x1 x2))).
Definition term149 := forall y0 : nat, exists y1 : nat, (fun y2 : nat => fun y3 : nat => (y2 = (NUMERAL 0)) \/ (y2 = (S y3))) y0 y1.
Definition term147 (x0 : type1605) := forall y0 : nat, exists y1 : nat, x0 y0 y1.
Definition term144 := forall y0 : nat, exists y1 : nat, (y0 = (NUMERAL 0)) \/ (y0 = (S y1)).
Definition term239 (x0 : nat -> Prop) := (fun y0 : nat -> Prop => (~ ((exists y1 : nat, y0 y1) = ((y0 (NUMERAL 0)) \/ (exists y1 : nat, y0 (S y1))))) -> (forall y1 : nat, (y1 = (NUMERAL 0)) \/ (exists y2 : nat, y1 = (S y2))) -> False) x0.
Definition term156 (x0 : nat) := exists y0 : nat, (fun y1 : nat => fun y2 : nat => (y1 = (NUMERAL 0)) \/ (y1 = (S y2))) x0 y0.
Definition term143 := fun y0 : nat => exists y1 : nat, (y0 = (NUMERAL 0)) \/ (y0 = (S y1)).
Definition term342 (a0 : Type') (x0 : nat) (x1 : list a0) := and (Peano.lt (S x0) (S (@List.length a0 x1))).
Definition term57 (x0 : nat -> Prop) := and (~ (exists y0 : nat, x0 y0)).
Definition term73 (x0 : nat -> Prop) := or (exists y0 : nat, (x0 y0) /\ ((~ (x0 (NUMERAL 0))) /\ (forall y1 : nat, ~ (x0 (S y1))))).
Definition term198 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := ((~ (x0 x2)) /\ (x0 x1)) -> ~ (x1 = x2).
Definition term266 (a0 : Type') := imp (((fun y0 : list a0 => forall y1 : a0, (@List.In a0 y1 y0) = (exists y2 : nat, (Peano.lt y2 (@List.length a0 y0)) /\ (y1 = (@EL a0 y2 y0)))) (@nil a0)) /\ (forall y0 : a0, forall y1 : list a0, ((fun y2 : list a0 => forall y3 : a0, (@List.In a0 y3 y2) = (exists y4 : nat, (Peano.lt y4 (@List.length a0 y2)) /\ (y3 = (@EL a0 y4 y2)))) y1) -> (fun y2 : list a0 => forall y3 : a0, (@List.In a0 y3 y2) = (exists y4 : nat, (Peano.lt y4 (@List.length a0 y2)) /\ (y3 = (@EL a0 y4 y2)))) (@cons a0 y0 y1))).
Definition term212 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (~ (x0 x1)) \/ (~ (x1 = x2)).
Definition term173 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => ~ (x0 y0)) x1.
Definition term206 (x0 : nat -> nat) (x1 : nat) := (~ (x1 = (NUMERAL 0))) -> x1 = (S (x0 x1)).
Definition term288 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term107 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term106 (x0 : nat -> Prop) := (exists y0 : nat, (x0 y0) /\ ((~ (x0 (NUMERAL 0))) /\ (forall y1 : nat, ~ (x0 (S y1))))) \/ (exists y0 : nat, (forall y1 : nat, ~ (x0 y1)) /\ ((x0 (NUMERAL 0)) \/ (x0 (S y0)))).
Definition term13 (x0 : nat -> Prop) := (((~ ((exists y0 : nat, x0 y0) = ((x0 (NUMERAL 0)) \/ (exists y0 : nat, x0 (S y0))))) -> (forall y0 : nat, (y0 = (NUMERAL 0)) \/ (exists y1 : nat, y0 = (S y1))) -> False) -> (~ ((exists y0 : nat, x0 y0) = ((x0 (NUMERAL 0)) \/ (exists y0 : nat, x0 (S y0))))) -> (forall y0 : nat, (y0 = (NUMERAL 0)) \/ (exists y1 : nat, y0 = (S y1))) -> False) -> (~ ((exists y0 : nat, x0 y0) = ((x0 (NUMERAL 0)) \/ (exists y0 : nat, x0 (S y0))))) -> (forall y0 : nat, (y0 = (NUMERAL 0)) \/ (exists y1 : nat, y0 = (S y1))) -> False.
Definition term343 (a0 : Type') (x0 : nat) (x1 : list a0) := and (Peano.lt x0 (@List.length a0 x1)).
Definition term344 (a0 : Type') (x0 : nat) (x1 : list a0) := @EL a0 (S x0) x1.
Definition term91 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 /\ (x1 y0).
Definition term164 (x0 : nat -> nat) := fun y0 : nat => (y0 = (NUMERAL 0)) \/ (y0 = (S (x0 y0))).
Definition term246 (a0 : Type') := and ((fun y0 : list a0 => forall y1 : a0, (@List.In a0 y1 y0) = (exists y2 : nat, (Peano.lt y2 (@List.length a0 y0)) /\ (y1 = (@EL a0 y2 y0)))) (@nil a0)).
Definition term28 := fun y0 : nat => (y0 = (NUMERAL 0)) \/ (exists y1 : nat, y0 = (S y1)).
Definition term6 (x0 : Prop) := (~ x0) -> False.
Definition term242 (a0 : Type') := (((fun y0 : list a0 => forall y1 : a0, (@List.In a0 y1 y0) = (exists y2 : nat, (Peano.lt y2 (@List.length a0 y0)) /\ (y1 = (@EL a0 y2 y0)))) (@nil a0)) /\ (forall y0 : a0, forall y1 : list a0, ((fun y2 : list a0 => forall y3 : a0, (@List.In a0 y3 y2) = (exists y4 : nat, (Peano.lt y4 (@List.length a0 y2)) /\ (y3 = (@EL a0 y4 y2)))) y1) -> (fun y2 : list a0 => forall y3 : a0, (@List.In a0 y3 y2) = (exists y4 : nat, (Peano.lt y4 (@List.length a0 y2)) /\ (y3 = (@EL a0 y4 y2)))) (@cons a0 y0 y1))) -> forall y0 : list a0, (fun y1 : list a0 => forall y2 : a0, (@List.In a0 y2 y1) = (exists y3 : nat, (Peano.lt y3 (@List.length a0 y1)) /\ (y2 = (@EL a0 y3 y1)))) y0.
Definition term259 (a0 : Type') (x0 : a0) := forall y0 : list a0, (forall y1 : a0, (@List.In a0 y1 y0) = (exists y2 : nat, (Peano.lt y2 (@List.length a0 y0)) /\ (y1 = (@EL a0 y2 y0)))) -> forall y1 : a0, (@List.In a0 y1 (@cons a0 x0 y0)) = (exists y2 : nat, (Peano.lt y2 (@List.length a0 (@cons a0 x0 y0))) /\ (y1 = (@EL a0 y2 (@cons a0 x0 y0)))).
Definition term241 (a0 : Type') (x0 : type1143 a0) := ((x0 (@nil a0)) /\ (forall y0 : a0, forall y1 : list a0, (x0 y1) -> x0 (@cons a0 y0 y1))) -> forall y0 : list a0, x0 y0.
Definition term177 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (x2 = x0) -> (x1 x0) \/ (~ (x1 x2)).
Definition term9 (x0 : nat -> Prop) := (~ ((exists y0 : nat, x0 y0) = ((x0 (NUMERAL 0)) \/ (exists y0 : nat, x0 (S y0))))) -> False.
Definition term336 (a0 : Type') (x0 : list a0) := @EL a0 (NUMERAL 0) x0.
Definition term304 (a0 : Type') (x0 : nat) (x1 : list a0) := Peano.lt x0 (S (@List.length a0 x1)).
Definition term270 (a0 : Type') := forall y0 : list a0, forall y1 : a0, (@List.In a0 y1 y0) = (exists y2 : nat, (Peano.lt y2 (@List.length a0 y0)) /\ (y1 = (@EL a0 y2 y0))).
Definition term104 (x0 : nat -> Prop) := fun y0 : nat => (forall y1 : nat, ~ (x0 y1)) /\ ((x0 (NUMERAL 0)) \/ (x0 (S y0))).
Definition term291 (a0 : Type') (x0 : a0) := forall y0 : list a0, (@List.length a0 (@cons a0 x0 y0)) = (S (@List.length a0 y0)).
Definition term330 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) := fun y0 : nat => (Peano.lt (S y0) (S (@List.length a0 x2))) /\ (x0 = (@EL a0 (S y0) (@cons a0 x1 x2))).
Definition term152 (x0 : nat) := (fun y0 : nat => fun y1 : nat => (y0 = (NUMERAL 0)) \/ (y0 = (S y1))) x0.
Definition term3 (x0 : nat) := forall y0 : nat, (Peano.lt (S x0) (S y0)) = (Peano.lt x0 y0).
Definition term233 (x0 : nat -> Prop) (x1 : nat -> nat) (x2 : nat) := (x0 (S (x1 x2))) -> False.
Definition term287 (a0 : Type') := forall y0 : a0, True.
Definition term337 (a0 : Type') (x0 : a0) (x1 : list a0) := @EL a0 (NUMERAL 0) (@cons a0 x0 x1).
Definition term52 (x0 : nat -> Prop) := and (~ (x0 (NUMERAL 0))).
Definition term294 (a0 : Type') (x0 : list a0) := S (@List.length a0 x0).
Definition term153 (x0 : nat) (x1 : nat) := (fun y0 : nat => fun y1 : nat => (y0 = (NUMERAL 0)) \/ (y0 = (S y1))) x0 x1.
Definition term77 (x0 : Prop) (x1 : nat -> Prop) := exists y0 : nat, x0 \/ (x1 y0).
Definition term130 (x0 : nat -> Prop) := exists y0 : nat, ((x0 y0) /\ ((~ (x0 (NUMERAL 0))) /\ (forall y1 : nat, ~ (x0 (S y1))))) \/ ((forall y1 : nat, ~ (x0 y1)) /\ ((x0 (NUMERAL 0)) \/ (x0 (S y0)))).
Definition term185 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term84 (x0 : nat -> Prop) (x1 : nat) := (x0 (NUMERAL 0)) \/ ((fun y0 : nat => x0 (S y0)) x1).
Definition term222 (x0 : nat) (x1 : nat) := and (x0 = x1).
Definition term332 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) := exists y0 : nat, (Peano.lt (S y0) (S (@List.length a0 x2))) /\ (x0 = (@EL a0 (S y0) (@cons a0 x1 x2))).
Definition term313 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) := exists y0 : nat, (Peano.lt y0 (S (@List.length a0 x2))) /\ (x0 = (@EL a0 y0 (@cons a0 x1 x2))).
Definition term312 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) := exists y0 : nat, (Peano.lt y0 (@List.length a0 (@cons a0 x1 x2))) /\ (x0 = (@EL a0 y0 (@cons a0 x1 x2))).
Definition term18 (x0 : nat -> Prop) := imp (~ ((exists y0 : nat, x0 y0) = ((x0 (NUMERAL 0)) \/ (exists y0 : nat, x0 (S y0))))).
Definition term16 := ~ (forall y0 : nat, (y0 = (NUMERAL 0)) \/ (exists y1 : nat, y0 = (S y1))).
Definition term231 (x0 : nat -> Prop) (x1 : nat -> nat) (x2 : nat) := ~ (x0 (S (x1 x2))).
Definition term235 (x0 : nat -> Prop) := (~ (x0 (NUMERAL 0))) -> x0 (NUMERAL 0).
Definition term86 (x0 : nat -> Prop) := fun y0 : nat => (x0 (NUMERAL 0)) \/ ((fun y1 : nat => x0 (S y1)) y0).
Definition term90 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 /\ (exists y0 : a0, x1 y0).
Definition term58 (x0 : nat -> Prop) := and (forall y0 : nat, ~ (x0 y0)).
Definition term243 (a0 : Type') := fun y0 : list a0 => forall y1 : a0, (@List.In a0 y1 y0) = (exists y2 : nat, (Peano.lt y2 (@List.length a0 y0)) /\ (y1 = (@EL a0 y2 y0))).
Definition term62 (x0 : nat -> Prop) := (exists y0 : nat, x0 y0) /\ (~ ((x0 (NUMERAL 0)) \/ (exists y0 : nat, x0 (S y0)))).
Definition term230 (x0 : nat -> Prop) (x1 : nat -> nat) (x2 : nat) := (~ (x0 (S (x1 x2)))) -> x0 (S (x1 x2)).
Definition term141 (x0 : nat) := fun y0 : nat => (x0 = (NUMERAL 0)) \/ (x0 = (S y0)).
Definition term197 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := imp ((~ (x1 x0)) /\ (x1 x2)).
Definition term184 (x0 : Prop) := (~ x0) -> x0.
Definition term275 (a0 : Type') (x0 : nat) := Peano.lt x0 (@List.length a0 (@nil a0)).
Definition term151 := fun y0 : nat => fun y1 : nat => (y0 = (NUMERAL 0)) \/ (y0 = (S y1)).
Definition term331 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) := exists y0 : nat, (fun y1 : nat => (Peano.lt y1 (S (@List.length a0 x2))) /\ (x0 = (@EL a0 y1 (@cons a0 x1 x2)))) (S y0).
Definition term240 := forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False.
Definition term260 (a0 : Type') := fun y0 : a0 => forall y1 : list a0, ((fun y2 : list a0 => forall y3 : a0, (@List.In a0 y3 y2) = (exists y4 : nat, (Peano.lt y4 (@List.length a0 y2)) /\ (y3 = (@EL a0 y4 y2)))) y1) -> (fun y2 : list a0 => forall y3 : a0, (@List.In a0 y3 y2) = (exists y4 : nat, (Peano.lt y4 (@List.length a0 y2)) /\ (y3 = (@EL a0 y4 y2)))) (@cons a0 y0 y1).
Definition term24 (x0 : nat) := fun y0 : nat => x0 = (S y0).
Definition term72 (x0 : nat -> Prop) := exists y0 : nat, (x0 y0) /\ ((~ (x0 (NUMERAL 0))) /\ (forall y1 : nat, ~ (x0 (S y1)))).
Definition term237 (x0 : nat -> Prop) := (x0 (NUMERAL 0)) -> False.
Definition term189 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term265 (a0 : Type') := (forall y0 : a0, (@List.In a0 y0 (@nil a0)) = (exists y1 : nat, (Peano.lt y1 (@List.length a0 (@nil a0))) /\ (y0 = (@EL a0 y1 (@nil a0))))) /\ (forall y0 : a0, forall y1 : list a0, (forall y2 : a0, (@List.In a0 y2 y1) = (exists y3 : nat, (Peano.lt y3 (@List.length a0 y1)) /\ (y2 = (@EL a0 y3 y1)))) -> forall y2 : a0, (@List.In a0 y2 (@cons a0 y0 y1)) = (exists y3 : nat, (Peano.lt y3 (@List.length a0 (@cons a0 y0 y1))) /\ (y2 = (@EL a0 y3 (@cons a0 y0 y1))))).
Definition term335 (a0 : Type') (x0 : list a0) := and (Peano.lt (NUMERAL 0) (S (@List.length a0 x0))).
Definition term40 (x0 : nat -> Prop) (x1 : nat) := ~ ((fun y0 : nat => x0 y0) x1).
Definition term145 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := forall y0 : a0, exists y1 : a1, x0 y0 y1.
Definition term87 (x0 : nat -> Prop) := fun y0 : nat => (x0 (NUMERAL 0)) \/ (x0 (S y0)).
Definition term339 (a0 : Type') (x0 : a0) (x1 : a0) := True /\ (x0 = x1).
Definition term169 := exists y0 : nat -> nat, forall y1 : nat, (y1 = (NUMERAL 0)) \/ (y1 = (S (y0 y1))).
Definition term150 := exists y0 : nat -> nat, forall y1 : nat, (fun y2 : nat => fun y3 : nat => (y2 = (NUMERAL 0)) \/ (y2 = (S y3))) y1 (y0 y1).
Definition term148 (x0 : type1605) := exists y0 : nat -> nat, forall y1 : nat, x0 y1 (y0 y1).
Definition term345 (a0 : Type') (x0 : nat) (x1 : list a0) := @EL a0 x0 (@tl a0 x1).
Definition term8 (x0 : nat -> Prop) := (x0 (NUMERAL 0)) \/ (exists y0 : nat, x0 (S y0)).
Definition term97 (x0 : nat -> Prop) := fun y0 : nat => (fun y1 : nat => (x0 (NUMERAL 0)) \/ (x0 (S y1))) y0.
Definition term94 (x0 : nat -> Prop) := (forall y0 : nat, ~ (x0 y0)) /\ (exists y0 : nat, (fun y1 : nat => (x0 (NUMERAL 0)) \/ (x0 (S y1))) y0).
Definition term236 (x0 : nat -> Prop) (x1 : nat) := (x0 x1) -> False.
Definition term213 (x0 : nat -> Prop) (x1 : nat) := or (x0 x1).
Definition term209 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term244 (a0 : Type') := (fun y0 : list a0 => forall y1 : a0, (@List.In a0 y1 y0) = (exists y2 : nat, (Peano.lt y2 (@List.length a0 y0)) /\ (y1 = (@EL a0 y2 y0)))) (@nil a0).
Definition term348 (a0 : Type') (x0 : a0) (x1 : list a0) := @tl a0 (@cons a0 x0 x1).
Definition term85 (x0 : nat -> Prop) (x1 : nat) := (x0 (NUMERAL 0)) \/ (x0 (S x1)).
Definition term201 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term30 (x0 : nat -> Prop) := fun y0 : nat => x0 (S y0).
Definition term305 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : list a0) := and (Peano.lt x0 (@List.length a0 (@cons a0 x1 x2))).
Definition term96 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => (x0 (NUMERAL 0)) \/ (x0 (S y0))) x1.
Definition term53 (x0 : nat -> Prop) := (~ (x0 (NUMERAL 0))) /\ (~ (exists y0 : nat, x0 (S y0))).
Definition term334 (a0 : Type') (x0 : list a0) := Peano.lt (NUMERAL 0) (S (@List.length a0 x0)).
Definition term322 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) := @eq Prop (exists y0 : nat, (Peano.lt y0 (S (@List.length a0 x2))) /\ (x0 = (@EL a0 y0 (@cons a0 x1 x2)))).
Definition term165 (x0 : nat -> nat) := forall y0 : nat, (fun y1 : nat => fun y2 : nat => (y1 = (NUMERAL 0)) \/ (y1 = (S y2))) y0 (x0 y0).
Definition term257 (a0 : Type') (x0 : a0) := fun y0 : list a0 => (forall y1 : a0, (@List.In a0 y1 y0) = (exists y2 : nat, (Peano.lt y2 (@List.length a0 y0)) /\ (y1 = (@EL a0 y2 y0)))) -> forall y1 : a0, (@List.In a0 y1 (@cons a0 x0 y0)) = (exists y2 : nat, (Peano.lt y2 (@List.length a0 (@cons a0 x0 y0))) /\ (y1 = (@EL a0 y2 (@cons a0 x0 y0)))).
Definition term11 (x0 : nat -> Prop) := (~ ((exists y0 : nat, x0 y0) = ((x0 (NUMERAL 0)) \/ (exists y0 : nat, x0 (S y0))))) -> (forall y0 : nat, (y0 = (NUMERAL 0)) \/ (exists y1 : nat, y0 = (S y1))) -> False.
Definition term20 := fun y0 : nat -> Prop => (~ ((exists y1 : nat, y0 y1) = ((y0 (NUMERAL 0)) \/ (exists y1 : nat, y0 (S y1))))) -> (forall y1 : nat, (y1 = (NUMERAL 0)) \/ (exists y2 : nat, y1 = (S y2))) -> False.
Definition term93 (x0 : Prop) (x1 : nat -> Prop) := exists y0 : nat, x0 /\ (x1 y0).
Definition term7 (x0 : nat -> Prop) := exists y0 : nat, x0 y0.
Definition term224 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := imp (~ ((~ (x2 = x0)) \/ (~ (x1 x2)))).
Definition term23 := forall y0 : nat -> Prop, (~ ((exists y1 : nat, y0 y1) = ((y0 (NUMERAL 0)) \/ (exists y1 : nat, y0 (S y1))))) -> ~ (forall y1 : nat, (y1 = (NUMERAL 0)) \/ (exists y2 : nat, y1 = (S y2))).
Definition term44 (x0 : nat -> Prop) := ~ (exists y0 : nat, x0 (S y0)).
Definition term80 (x0 : nat -> Prop) := fun y0 : nat => (fun y1 : nat => x0 (S y1)) y0.
Definition term183 (x0 : nat -> Prop) (x1 : nat) := (~ (x0 x1)) -> x0 x1.
Definition term17 := forall y0 : nat, (y0 = (NUMERAL 0)) \/ (exists y1 : nat, y0 = (S y1)).
Definition term138 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) \/ ((fun y0 : nat => x0 = (S y0)) x1).
Definition term226 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := ((x0 = x2) /\ (x1 x0)) -> x1 x2.
Definition term269 (a0 : Type') := forall y0 : list a0, (fun y1 : list a0 => forall y2 : a0, (@List.In a0 y2 y1) = (exists y3 : nat, (Peano.lt y3 (@List.length a0 y1)) /\ (y2 = (@EL a0 y3 y1)))) y0.
Definition term92 (x0 : Prop) (x1 : nat -> Prop) := x0 /\ (exists y0 : nat, x1 y0).
Definition term22 := forall y0 : nat -> Prop, (~ ((exists y1 : nat, y0 y1) = ((y0 (NUMERAL 0)) \/ (exists y1 : nat, y0 (S y1))))) -> (forall y1 : nat, (y1 = (NUMERAL 0)) \/ (exists y2 : nat, y1 = (S y2))) -> False.
Definition term63 (x0 : nat -> Prop) := (exists y0 : nat, x0 y0) /\ ((~ (x0 (NUMERAL 0))) /\ (forall y0 : nat, ~ (x0 (S y0)))).
Definition term194 (x0 : nat -> Prop) (x1 : nat) := and (~ (x0 x1)).
Definition term19 (x0 : nat -> Prop) := (~ ((exists y0 : nat, x0 y0) = ((x0 (NUMERAL 0)) \/ (exists y0 : nat, x0 (S y0))))) -> ~ (forall y0 : nat, (y0 = (NUMERAL 0)) \/ (exists y1 : nat, y0 = (S y1))).
Definition term111 (x0 : nat -> Prop) := (exists y0 : nat, (fun y1 : nat => (x0 y1) /\ ((~ (x0 (NUMERAL 0))) /\ (forall y2 : nat, ~ (x0 (S y2))))) y0) \/ (exists y0 : nat, (fun y1 : nat => (forall y2 : nat, ~ (x0 y2)) /\ ((x0 (NUMERAL 0)) \/ (x0 (S y1)))) y0).
Definition term255 (a0 : Type') (x0 : a0) (x1 : list a0) := (forall y0 : a0, (@List.In a0 y0 x1) = (exists y1 : nat, (Peano.lt y1 (@List.length a0 x1)) /\ (y0 = (@EL a0 y1 x1)))) -> forall y0 : a0, (@List.In a0 y0 (@cons a0 x0 x1)) = (exists y1 : nat, (Peano.lt y1 (@List.length a0 (@cons a0 x0 x1))) /\ (y0 = (@EL a0 y1 (@cons a0 x0 x1)))).
Definition term249 (a0 : Type') (x0 : list a0) := forall y0 : a0, (@List.In a0 y0 x0) = (exists y1 : nat, (Peano.lt y1 (@List.length a0 x0)) /\ (y0 = (@EL a0 y1 x0))).
Definition term168 := fun y0 : nat -> nat => forall y1 : nat, (y1 = (NUMERAL 0)) \/ (y1 = (S (y0 y1))).
Definition term167 := fun y0 : nat -> nat => forall y1 : nat, (fun y2 : nat => fun y3 : nat => (y2 = (NUMERAL 0)) \/ (y2 = (S y3))) y1 (y0 y1).
Definition term272 (x0 : nat) := (fun y0 : nat => (Peano.lt y0 (NUMERAL 0)) = False) x0.
Definition term271 (a0 : Type') := ((forall y0 : a0, (@List.In a0 y0 (@nil a0)) = (exists y1 : nat, (Peano.lt y1 (@List.length a0 (@nil a0))) /\ (y0 = (@EL a0 y1 (@nil a0))))) /\ (forall y0 : a0, forall y1 : list a0, (forall y2 : a0, (@List.In a0 y2 y1) = (exists y3 : nat, (Peano.lt y3 (@List.length a0 y1)) /\ (y2 = (@EL a0 y3 y1)))) -> forall y2 : a0, (@List.In a0 y2 (@cons a0 y0 y1)) = (exists y3 : nat, (Peano.lt y3 (@List.length a0 (@cons a0 y0 y1))) /\ (y2 = (@EL a0 y3 (@cons a0 y0 y1)))))) -> forall y0 : list a0, forall y1 : a0, (@List.In a0 y1 y0) = (exists y2 : nat, (Peano.lt y2 (@List.length a0 y0)) /\ (y1 = (@EL a0 y2 y0))).
Definition term159 := @eq Prop (forall y0 : nat, exists y1 : nat, (y0 = (NUMERAL 0)) \/ (y0 = (S y1))).
Definition term158 := @eq Prop (forall y0 : nat, exists y1 : nat, (fun y2 : nat => fun y3 : nat => (y2 = (NUMERAL 0)) \/ (y2 = (S y3))) y0 y1).
Definition term333 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) := ((Peano.lt (NUMERAL 0) (S (@List.length a0 x2))) /\ (x0 = (@EL a0 (NUMERAL 0) (@cons a0 x1 x2)))) \/ (exists y0 : nat, (Peano.lt (S y0) (S (@List.length a0 x2))) /\ (x0 = (@EL a0 (S y0) (@cons a0 x1 x2)))).
Definition term284 (x0 : Prop) := exists y0 : nat, x0.
Definition term195 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (~ (x1 x0)) /\ (x1 x2).
Definition term48 (x0 : nat -> Prop) (x1 : nat) := ~ (x0 (S x1)).
Definition term267 (a0 : Type') := imp ((forall y0 : a0, (@List.In a0 y0 (@nil a0)) = (exists y1 : nat, (Peano.lt y1 (@List.length a0 (@nil a0))) /\ (y0 = (@EL a0 y1 (@nil a0))))) /\ (forall y0 : a0, forall y1 : list a0, (forall y2 : a0, (@List.In a0 y2 y1) = (exists y3 : nat, (Peano.lt y3 (@List.length a0 y1)) /\ (y2 = (@EL a0 y3 y1)))) -> forall y2 : a0, (@List.In a0 y2 (@cons a0 y0 y1)) = (exists y3 : nat, (Peano.lt y3 (@List.length a0 (@cons a0 y0 y1))) /\ (y2 = (@EL a0 y3 (@cons a0 y0 y1)))))).
Definition term75 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 \/ (x1 y0).
Definition term205 (x0 : nat -> nat) (x1 : nat) := @eq Prop ((x1 = (NUMERAL 0)) \/ (x1 = (S (x0 x1)))).
Definition term247 (a0 : Type') := and (forall y0 : a0, (@List.In a0 y0 (@nil a0)) = (exists y1 : nat, (Peano.lt y1 (@List.length a0 (@nil a0))) /\ (y0 = (@EL a0 y1 (@nil a0))))).
Definition term83 (x0 : nat -> Prop) := @eq Prop ((x0 (NUMERAL 0)) \/ (exists y0 : nat, x0 (S y0))).
Definition term82 (x0 : nat -> Prop) := @eq Prop ((x0 (NUMERAL 0)) \/ (exists y0 : nat, (fun y1 : nat => x0 (S y1)) y0)).
Definition term133 (x0 : nat) (x1 : nat) := (fun y0 : nat => x0 = (S y0)) x1.
Definition term26 (x0 : nat) := or (x0 = (NUMERAL 0)).
Definition term258 (a0 : Type') (x0 : a0) := forall y0 : list a0, ((fun y1 : list a0 => forall y2 : a0, (@List.In a0 y2 y1) = (exists y3 : nat, (Peano.lt y3 (@List.length a0 y1)) /\ (y2 = (@EL a0 y3 y1)))) y0) -> (fun y1 : list a0 => forall y2 : a0, (@List.In a0 y2 y1) = (exists y3 : nat, (Peano.lt y3 (@List.length a0 y1)) /\ (y2 = (@EL a0 y3 y1)))) (@cons a0 x0 y0).
Definition term59 (x0 : nat -> Prop) := (~ (exists y0 : nat, x0 y0)) /\ ((x0 (NUMERAL 0)) \/ (exists y0 : nat, x0 (S y0))).
Definition term290 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : list a0, (@List.length a0 (@cons a0 y0 y1)) = (S (@List.length a0 y1))) x0.
Definition term188 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term268 (a0 : Type') := fun y0 : list a0 => (fun y1 : list a0 => forall y2 : a0, (@List.In a0 y2 y1) = (exists y3 : nat, (Peano.lt y3 (@List.length a0 y1)) /\ (y2 = (@EL a0 y3 y1)))) y0.
Definition term248 (a0 : Type') (x0 : list a0) := (fun y0 : list a0 => forall y1 : a0, (@List.In a0 y1 y0) = (exists y2 : nat, (Peano.lt y2 (@List.length a0 y0)) /\ (y1 = (@EL a0 y2 y0)))) x0.
Definition term286 (a0 : Type') := fun y0 : a0 => True.
Definition term74 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 \/ (exists y0 : a0, x1 y0).
Definition term200 (x0 : nat -> Prop) (x1 : nat) := ((~ (x0 (NUMERAL 0))) /\ (x0 x1)) -> ~ (x1 = (NUMERAL 0)).
Definition term229 (x0 : nat -> Prop) (x1 : nat -> nat) (x2 : nat) := x0 (S (x1 x2)).
Definition term132 (x0 : nat) := exists y0 : nat, (x0 = (NUMERAL 0)) \/ ((fun y1 : nat => x0 = (S y1)) y0).
Definition term69 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) /\ x1.
Definition term119 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => (forall y1 : nat, ~ (x0 y1)) /\ ((x0 (NUMERAL 0)) \/ (x0 (S y0)))) x1.
Definition term250 (a0 : Type') (x0 : list a0) := imp ((fun y0 : list a0 => forall y1 : a0, (@List.In a0 y1 y0) = (exists y2 : nat, (Peano.lt y2 (@List.length a0 y0)) /\ (y1 = (@EL a0 y2 y0)))) x0).
Definition term35 (x0 : nat -> Prop) := ~ (ex x0).
Definition term112 (x0 : nat -> Prop) := exists y0 : nat, ((fun y1 : nat => (x0 y1) /\ ((~ (x0 (NUMERAL 0))) /\ (forall y2 : nat, ~ (x0 (S y2))))) y0) \/ ((fun y1 : nat => (forall y2 : nat, ~ (x0 y2)) /\ ((x0 (NUMERAL 0)) \/ (x0 (S y1)))) y0).
Definition term39 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => x0 y0) x1.
Definition term276 (a0 : Type') (x0 : nat) := and (Peano.lt x0 (@List.length a0 (@nil a0))).
Definition term176 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (x1 x0) \/ (~ (x1 x2)).
Definition term32 (x0 : nat -> Prop) := or (x0 (NUMERAL 0)).
Definition term215 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := @eq Prop ((~ (x2 = x0)) \/ ((x1 x0) \/ (~ (x1 x2)))).
Definition term214 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (x0 x2) \/ ((~ (x0 x1)) \/ (~ (x1 = x2))).
Definition term350 (a0 : Type') (x0 : a0) (x1 : list a0) := fun y0 : nat => (Peano.lt y0 (@List.length a0 x1)) /\ (x0 = (@EL a0 y0 x1)).
Definition term15 := (forall y0 : nat, (y0 = (NUMERAL 0)) \/ (exists y1 : nat, y0 = (S y1))) -> False.
Definition term36 (x0 : nat -> Prop) := forall y0 : nat, ~ (x0 y0).
Definition term261 (a0 : Type') := fun y0 : a0 => forall y1 : list a0, (forall y2 : a0, (@List.In a0 y2 y1) = (exists y3 : nat, (Peano.lt y3 (@List.length a0 y1)) /\ (y2 = (@EL a0 y3 y1)))) -> forall y2 : a0, (@List.In a0 y2 (@cons a0 y0 y1)) = (exists y3 : nat, (Peano.lt y3 (@List.length a0 (@cons a0 y0 y1))) /\ (y2 = (@EL a0 y3 (@cons a0 y0 y1)))).
Definition term329 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) := fun y0 : nat => (fun y1 : nat => (Peano.lt y1 (S (@List.length a0 x2))) /\ (x0 = (@EL a0 y1 (@cons a0 x1 x2)))) (S y0).
Definition term199 (x0 : nat -> Prop) (x1 : nat) := (~ (x0 (NUMERAL 0))) /\ (x0 x1).
Definition term311 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) := fun y0 : nat => (Peano.lt y0 (S (@List.length a0 x2))) /\ (x0 = (@EL a0 y0 (@cons a0 x1 x2))).
Definition term245 (a0 : Type') := forall y0 : a0, (@List.In a0 y0 (@nil a0)) = (exists y1 : nat, (Peano.lt y1 (@List.length a0 (@nil a0))) /\ (y0 = (@EL a0 y1 (@nil a0)))).
Definition term298 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) := (x1 = x0) \/ (@List.In a0 x1 x2).
Definition term306 (a0 : Type') (x0 : nat) (x1 : list a0) := and (Peano.lt x0 (S (@List.length a0 x1))).
Definition term179 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (~ (x2 = x0)) \/ ((x1 x0) \/ (~ (x1 x2))).
Definition term25 (x0 : nat) := exists y0 : nat, x0 = (S y0).
Definition term292 (a0 : Type') (x0 : a0) (x1 : list a0) := (fun y0 : list a0 => (@List.length a0 (@cons a0 x0 y0)) = (S (@List.length a0 y0))) x1.
Definition term71 (x0 : nat -> Prop) (x1 : Prop) := exists y0 : nat, (x0 y0) /\ x1.
Definition term217 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (~ ((~ (x0 = x2)) \/ (~ (x1 x0)))) -> x1 x2.
Definition term4 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt (S x0) (S y0)) = (Peano.lt x0 y0)) x1.
Definition term78 (x0 : nat -> Prop) := (x0 (NUMERAL 0)) \/ (exists y0 : nat, (fun y1 : nat => x0 (S y1)) y0).
Definition term193 (x0 : nat -> Prop) (x1 : nat) := ~ (~ (x0 x1)).
Definition term280 := fun y0 : nat => False.
Definition term264 (a0 : Type') := ((fun y0 : list a0 => forall y1 : a0, (@List.In a0 y1 y0) = (exists y2 : nat, (Peano.lt y2 (@List.length a0 y0)) /\ (y1 = (@EL a0 y2 y0)))) (@nil a0)) /\ (forall y0 : a0, forall y1 : list a0, ((fun y2 : list a0 => forall y3 : a0, (@List.In a0 y3 y2) = (exists y4 : nat, (Peano.lt y4 (@List.length a0 y2)) /\ (y3 = (@EL a0 y4 y2)))) y1) -> (fun y2 : list a0 => forall y3 : a0, (@List.In a0 y3 y2) = (exists y4 : nat, (Peano.lt y4 (@List.length a0 y2)) /\ (y3 = (@EL a0 y4 y2)))) (@cons a0 y0 y1)).
Definition term202 (x0 : nat) := (x0 = (NUMERAL 0)) -> ~ (x0 = (NUMERAL 0)).
Definition term228 (x0 : nat -> Prop) (x1 : nat -> nat) (x2 : nat) := ((x2 = (S (x1 x2))) /\ (x0 x2)) -> x0 (S (x1 x2)).
Definition term54 (x0 : nat -> Prop) := (~ (x0 (NUMERAL 0))) /\ (forall y0 : nat, ~ (x0 (S y0))).
Definition term89 (x0 : nat -> Prop) := (forall y0 : nat, ~ (x0 y0)) /\ (exists y0 : nat, (x0 (NUMERAL 0)) \/ (x0 (S y0))).
Definition term60 (x0 : nat -> Prop) := (forall y0 : nat, ~ (x0 y0)) /\ ((x0 (NUMERAL 0)) \/ (exists y0 : nat, x0 (S y0))).
Definition term316 (a0 : Type') (x0 : a0) (x1 : list a0) := forall y0 : a0, ((y0 = x0) \/ (exists y1 : nat, (Peano.lt y1 (@List.length a0 x1)) /\ (y0 = (@EL a0 y1 x1)))) = (exists y1 : nat, (Peano.lt y1 (S (@List.length a0 x1))) /\ (y0 = (@EL a0 y1 (@cons a0 x0 x1)))).
Definition term253 (a0 : Type') (x0 : a0) (x1 : list a0) := forall y0 : a0, (@List.In a0 y0 (@cons a0 x0 x1)) = (exists y1 : nat, (Peano.lt y1 (@List.length a0 (@cons a0 x0 x1))) /\ (y0 = (@EL a0 y1 (@cons a0 x0 x1)))).
Definition term210 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (x1 x0) \/ ((~ (x2 = x0)) \/ (~ (x1 x2))).
Definition term181 (x0 : nat -> Prop) := (x0 (NUMERAL 0)) -> ~ (x0 (NUMERAL 0)).
Definition term317 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) := exists y0 : nat, (fun y1 : nat => (Peano.lt y1 (S (@List.length a0 x2))) /\ (x0 = (@EL a0 y1 (@cons a0 x1 x2)))) y0.
Definition term135 (x0 : nat) := exists y0 : nat, (fun y1 : nat => x0 = (S y1)) y0.
Definition term121 (x0 : nat -> Prop) := exists y0 : nat, (fun y1 : nat => (forall y2 : nat, ~ (x0 y2)) /\ ((x0 (NUMERAL 0)) \/ (x0 (S y1)))) y0.
Definition term117 (x0 : nat -> Prop) := exists y0 : nat, (fun y1 : nat => (x0 y1) /\ ((~ (x0 (NUMERAL 0))) /\ (forall y2 : nat, ~ (x0 (S y2))))) y0.
Definition term98 (x0 : nat -> Prop) := exists y0 : nat, (fun y1 : nat => (x0 (NUMERAL 0)) \/ (x0 (S y1))) y0.
Definition term137 (x0 : nat) := @eq Prop ((x0 = (NUMERAL 0)) \/ (exists y0 : nat, x0 = (S y0))).
Definition term136 (x0 : nat) := @eq Prop ((x0 = (NUMERAL 0)) \/ (exists y0 : nat, (fun y1 : nat => x0 = (S y1)) y0)).
Definition term252 (a0 : Type') (x0 : a0) (x1 : list a0) := (fun y0 : list a0 => forall y1 : a0, (@List.In a0 y1 y0) = (exists y2 : nat, (Peano.lt y2 (@List.length a0 y0)) /\ (y1 = (@EL a0 y2 y0)))) (@cons a0 x0 x1).
Definition term221 (x0 : nat) (x1 : nat) := and (~ (~ (x0 = x1))).
Definition term283 (a0 : Type') (x0 : Prop) := exists y0 : a0, x0.
Definition term299 (a0 : Type') (x0 : a0) (x1 : a0) := or (x0 = x1).
Definition term319 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) (x3 : nat) := (fun y0 : nat => (Peano.lt y0 (S (@List.length a0 x2))) /\ (x0 = (@EL a0 y0 (@cons a0 x1 x2)))) x3.
Definition term303 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : list a0) := Peano.lt x0 (@List.length a0 (@cons a0 x1 x2)).
Definition term155 (x0 : nat) := fun y0 : nat => (fun y1 : nat => fun y2 : nat => (y1 = (NUMERAL 0)) \/ (y1 = (S y2))) x0 y0.
Definition term340 (a0 : Type') (x0 : nat) (x1 : list a0) := Peano.lt (S x0) (S (@List.length a0 x1)).
Definition term42 (x0 : nat -> Prop) := fun y0 : nat => ~ ((fun y1 : nat => x0 y1) y0).
Definition term161 (x0 : nat -> nat) (x1 : nat) := (fun y0 : nat => (x1 = (NUMERAL 0)) \/ (x1 = (S y0))) (x0 x1).
Definition term64 (x0 : nat -> Prop) := or ((exists y0 : nat, x0 y0) /\ (~ ((x0 (NUMERAL 0)) \/ (exists y0 : nat, x0 (S y0))))).
Definition term174 (x0 : Prop) (x1 : Prop) := (x1 = x0) -> x0 \/ (~ x1).
Definition term297 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) := @List.In a0 x0 (@cons a0 x1 x2).
Definition term326 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) := or ((Peano.lt (NUMERAL 0) (S (@List.length a0 x2))) /\ (x0 = (@EL a0 (NUMERAL 0) (@cons a0 x1 x2)))).
Definition term273 (x0 : nat) := Peano.lt x0 (NUMERAL 0).
Definition term204 (x0 : nat -> nat) (x1 : nat) := S (x0 x1).
Definition term216 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := @eq Prop ((x0 x2) \/ ((~ (x0 x1)) \/ (~ (x1 = x2)))).
Definition term274 (a0 : Type') (x0 : a0) := @eq Prop (@List.In a0 x0 (@nil a0)).
Definition term203 (x0 : nat -> nat) (x1 : nat) := (x1 = (S (x0 x1))) \/ (x1 = (NUMERAL 0)).
Definition term208 (x0 : nat -> nat) (x1 : nat) := ~ (x1 = (S (x0 x1))).
Definition term70 (x0 : nat -> Prop) (x1 : Prop) := (exists y0 : nat, x0 y0) /\ x1.
Definition term254 (a0 : Type') (x0 : a0) (x1 : list a0) := ((fun y0 : list a0 => forall y1 : a0, (@List.In a0 y1 y0) = (exists y2 : nat, (Peano.lt y2 (@List.length a0 y0)) /\ (y1 = (@EL a0 y2 y0)))) x1) -> (fun y0 : list a0 => forall y1 : a0, (@List.In a0 y1 y0) = (exists y2 : nat, (Peano.lt y2 (@List.length a0 y0)) /\ (y1 = (@EL a0 y2 y0)))) (@cons a0 x0 x1).
Definition term56 (x0 : nat -> Prop) := x0 (NUMERAL 0).
Definition term301 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) := @eq Prop (@List.In a0 x0 (@cons a0 x1 x2)).
Definition term45 (x0 : nat -> Prop) := forall y0 : nat, ~ ((fun y1 : nat => x0 (S y1)) y0).
Definition term38 (x0 : nat -> Prop) := forall y0 : nat, ~ ((fun y1 : nat => x0 y1) y0).
Definition term2 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt (S y0) (S y1)) = (Peano.lt y0 y1)) x0.
Definition term349 (a0 : Type') (x0 : a0) (x1 : nat) (x2 : list a0) := (Peano.lt x1 (@List.length a0 x2)) /\ (x0 = (@EL a0 x1 x2)).
Definition term310 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) := fun y0 : nat => (Peano.lt y0 (@List.length a0 (@cons a0 x1 x2))) /\ (x0 = (@EL a0 y0 (@cons a0 x1 x2))).
Definition term180 (x0 : nat -> Prop) := ~ (x0 (NUMERAL 0)).
Definition term12 (x0 : nat -> Prop) := ((~ ((exists y0 : nat, x0 y0) = ((x0 (NUMERAL 0)) \/ (exists y0 : nat, x0 (S y0))))) -> (forall y0 : nat, (y0 = (NUMERAL 0)) \/ (exists y1 : nat, y0 = (S y1))) -> False) -> (~ ((exists y0 : nat, x0 y0) = ((x0 (NUMERAL 0)) \/ (exists y0 : nat, x0 (S y0))))) -> (forall y0 : nat, (y0 = (NUMERAL 0)) \/ (exists y1 : nat, y0 = (S y1))) -> False.
Definition term227 (x0 : nat -> nat) (x1 : nat -> Prop) (x2 : nat) := (x2 = (S (x0 x2))) /\ (x1 x2).
Definition term103 (x0 : nat -> Prop) := fun y0 : nat => (forall y1 : nat, ~ (x0 y1)) /\ ((fun y1 : nat => (x0 (NUMERAL 0)) \/ (x0 (S y1))) y0).
Definition term51 (x0 : nat -> Prop) := forall y0 : nat, ~ (x0 (S y0)).
Definition term307 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : list a0) := @EL a0 x0 (@cons a0 x1 x2).
Definition term66 (x0 : nat -> Prop) := ((exists y0 : nat, x0 y0) /\ (~ ((x0 (NUMERAL 0)) \/ (exists y0 : nat, x0 (S y0))))) \/ ((~ (exists y0 : nat, x0 y0)) /\ ((x0 (NUMERAL 0)) \/ (exists y0 : nat, x0 (S y0)))).
Definition term31 (x0 : nat -> Prop) := exists y0 : nat, x0 (S y0).
Definition term162 (x0 : nat -> nat) (x1 : nat) := (x1 = (NUMERAL 0)) \/ (x1 = (S (x0 x1))).
Definition term172 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => ~ (x0 (S y0))) x1.
Definition term5 (x0 : nat) (x1 : nat) := Peano.lt (S x0) (S x1).
Definition term160 (x0 : nat -> nat) (x1 : nat) := (fun y0 : nat => fun y1 : nat => (y0 = (NUMERAL 0)) \/ (y0 = (S y1))) x1 (x0 x1).
Definition term278 (a0 : Type') (x0 : a0) (x1 : nat) := False /\ (x0 = (@EL a0 x1 (@nil a0))).
Definition term232 (x0 : nat -> Prop) (x1 : nat) := (x0 (S x1)) -> False.
Definition term154 (x0 : nat) (x1 : nat) := (fun y0 : nat => (x0 = (NUMERAL 0)) \/ (x0 = (S y0))) x1.
Definition term157 := fun y0 : nat => exists y1 : nat, (fun y2 : nat => fun y3 : nat => (y2 = (NUMERAL 0)) \/ (y2 = (S y3))) y0 y1.
Definition term328 (a0 : Type') (x0 : a0) (x1 : nat) (x2 : a0) (x3 : list a0) := (Peano.lt (S x1) (S (@List.length a0 x3))) /\ (x0 = (@EL a0 (S x1) (@cons a0 x2 x3))).
Definition term320 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) := fun y0 : nat => (fun y1 : nat => (Peano.lt y1 (S (@List.length a0 x2))) /\ (x0 = (@EL a0 y1 (@cons a0 x1 x2)))) y0.
Definition term120 (x0 : nat -> Prop) := fun y0 : nat => (fun y1 : nat => (forall y2 : nat, ~ (x0 y2)) /\ ((x0 (NUMERAL 0)) \/ (x0 (S y1)))) y0.
Definition term116 (x0 : nat -> Prop) := fun y0 : nat => (fun y1 : nat => (x0 y1) /\ ((~ (x0 (NUMERAL 0))) /\ (forall y2 : nat, ~ (x0 (S y2))))) y0.
Definition term131 (x0 : nat) := (x0 = (NUMERAL 0)) \/ (exists y0 : nat, (fun y1 : nat => x0 = (S y1)) y0).
Definition term178 (x0 : Prop) (x1 : Prop) := (~ x0) \/ x1.
Definition term347 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : list a0) := @EL a0 x0 (@tl a0 (@cons a0 x1 x2)).
Definition term47 (x0 : nat -> Prop) (x1 : nat) := ~ ((fun y0 : nat => x0 (S y0)) x1).
Definition term186 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (~ ((x0 x2) \/ (~ (x0 x1)))) -> ~ (x1 = x2).
Definition term105 (x0 : nat -> Prop) := exists y0 : nat, (forall y1 : nat, ~ (x0 y1)) /\ ((x0 (NUMERAL 0)) \/ (x0 (S y0))).
Definition term300 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) := (x1 = x0) \/ (exists y0 : nat, (Peano.lt y0 (@List.length a0 x2)) /\ (x1 = (@EL a0 y0 x2))).
Definition term166 (x0 : nat -> nat) := forall y0 : nat, (y0 = (NUMERAL 0)) \/ (y0 = (S (x0 y0))).
Definition term318 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) := ((fun y0 : nat => (Peano.lt y0 (S (@List.length a0 x2))) /\ (x0 = (@EL a0 y0 (@cons a0 x1 x2)))) (NUMERAL 0)) \/ (exists y0 : nat, (fun y1 : nat => (Peano.lt y1 (S (@List.length a0 x2))) /\ (x0 = (@EL a0 y1 (@cons a0 x1 x2)))) (S y0)).
Definition term27 (x0 : nat) := (x0 = (NUMERAL 0)) \/ (exists y0 : nat, x0 = (S y0)).
Definition term302 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) := @eq Prop ((x1 = x0) \/ (exists y0 : nat, (Peano.lt y0 (@List.length a0 x2)) /\ (x1 = (@EL a0 y0 x2)))).
Definition term315 (a0 : Type') (x0 : a0) (x1 : list a0) := fun y0 : a0 => ((y0 = x0) \/ (exists y1 : nat, (Peano.lt y1 (@List.length a0 x1)) /\ (y0 = (@EL a0 y1 x1)))) = (exists y1 : nat, (Peano.lt y1 (S (@List.length a0 x1))) /\ (y0 = (@EL a0 y1 (@cons a0 x0 x1)))).
Definition term29 (x0 : nat -> Prop) (x1 : nat) := x0 (S x1).
Definition term100 (x0 : nat -> Prop) := @eq Prop ((forall y0 : nat, ~ (x0 y0)) /\ (exists y0 : nat, (x0 (NUMERAL 0)) \/ (x0 (S y0)))).
Definition term99 (x0 : nat -> Prop) := @eq Prop ((forall y0 : nat, ~ (x0 y0)) /\ (exists y0 : nat, (fun y1 : nat => (x0 (NUMERAL 0)) \/ (x0 (S y1))) y0)).
Definition term101 (x0 : nat -> Prop) (x1 : nat) := (forall y0 : nat, ~ (x0 y0)) /\ ((fun y0 : nat => (x0 (NUMERAL 0)) \/ (x0 (S y0))) x1).
Definition term223 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (x2 = x0) /\ (x1 x2).
Definition term207 (x0 : nat -> nat) (x1 : nat) := (~ (x1 = (S (x0 x1)))) -> x1 = (S (x0 x1)).
Definition term37 (x0 : nat -> Prop) := ~ (exists y0 : nat, x0 y0).
Definition term142 (x0 : nat) := exists y0 : nat, (x0 = (NUMERAL 0)) \/ (x0 = (S y0)).
Definition term49 (x0 : nat -> Prop) := fun y0 : nat => ~ ((fun y1 : nat => x0 (S y1)) y0).
Definition term170 (x0 : nat -> Prop) (x1 : nat) := and (x0 x1).
Definition term110 (x0 : nat -> Prop) (x1 : nat -> Prop) := exists y0 : nat, (x0 y0) \/ (x1 y0).
Definition term125 (x0 : nat) (x1 : nat -> Prop) := or ((x1 x0) /\ ((~ (x1 (NUMERAL 0))) /\ (forall y0 : nat, ~ (x1 (S y0))))).
Definition term34 (x0 : nat -> Prop) := @eq Prop (exists y0 : nat, x0 y0).
Definition term191 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (~ (x1 x0)) /\ (~ (~ (x1 x2))).
Definition term346 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : list a0) := @EL a0 (S x0) (@cons a0 x1 x2).
Definition term113 (x0 : nat -> Prop) := fun y0 : nat => (x0 y0) /\ ((~ (x0 (NUMERAL 0))) /\ (forall y1 : nat, ~ (x0 (S y1)))).
Definition term196 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := imp (~ ((x1 x0) \/ (~ (x1 x2)))).
Definition term68 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) /\ x1.
Definition term341 (a0 : Type') (x0 : nat) (x1 : list a0) := Peano.lt x0 (@List.length a0 x1).
Definition term128 (x0 : nat -> Prop) := fun y0 : nat => ((fun y1 : nat => (x0 y1) /\ ((~ (x0 (NUMERAL 0))) /\ (forall y2 : nat, ~ (x0 (S y2))))) y0) \/ ((fun y1 : nat => (forall y2 : nat, ~ (x0 y2)) /\ ((x0 (NUMERAL 0)) \/ (x0 (S y1)))) y0).
Definition term88 (x0 : nat -> Prop) := exists y0 : nat, (x0 (NUMERAL 0)) \/ (x0 (S y0)).
Definition term118 (x0 : nat -> Prop) := or (exists y0 : nat, (fun y1 : nat => (x0 y1) /\ ((~ (x0 (NUMERAL 0))) /\ (forall y2 : nat, ~ (x0 (S y2))))) y0).
Definition term10 (x0 : nat -> Prop) := ~ ((exists y0 : nat, x0 y0) = ((x0 (NUMERAL 0)) \/ (exists y0 : nat, x0 (S y0)))).
Definition term211 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (~ (x2 = x0)) \/ (~ (x1 x2)).
Definition term65 (x0 : nat -> Prop) := or ((exists y0 : nat, x0 y0) /\ ((~ (x0 (NUMERAL 0))) /\ (forall y0 : nat, ~ (x0 (S y0))))).
Definition term102 (x0 : nat -> Prop) (x1 : nat) := (forall y0 : nat, ~ (x0 y0)) /\ ((x0 (NUMERAL 0)) \/ (x0 (S x1))).
Definition term220 (x0 : nat) (x1 : nat) := ~ (~ (x0 = x1)).
Definition term127 (x0 : nat -> Prop) (x1 : nat) := ((x0 x1) /\ ((~ (x0 (NUMERAL 0))) /\ (forall y0 : nat, ~ (x0 (S y0))))) \/ ((forall y0 : nat, ~ (x0 y0)) /\ ((x0 (NUMERAL 0)) \/ (x0 (S x1)))).
Definition term14 (x0 : nat -> Prop) := (((~ ((exists y0 : nat, x0 y0) = ((x0 (NUMERAL 0)) \/ (exists y0 : nat, x0 (S y0))))) -> (forall y0 : nat, (y0 = (NUMERAL 0)) \/ (exists y1 : nat, y0 = (S y1))) -> False) -> (~ ((exists y0 : nat, x0 y0) = ((x0 (NUMERAL 0)) \/ (exists y0 : nat, x0 (S y0))))) -> (forall y0 : nat, (y0 = (NUMERAL 0)) \/ (exists y1 : nat, y0 = (S y1))) -> False) -> ((~ ((exists y0 : nat, x0 y0) = ((x0 (NUMERAL 0)) \/ (exists y0 : nat, x0 (S y0))))) -> (forall y0 : nat, (y0 = (NUMERAL 0)) \/ (exists y1 : nat, y0 = (S y1))) -> False) -> (~ ((exists y0 : nat, x0 y0) = ((x0 (NUMERAL 0)) \/ (exists y0 : nat, x0 (S y0))))) -> (forall y0 : nat, (y0 = (NUMERAL 0)) \/ (exists y1 : nat, y0 = (S y1))) -> False.
Definition term140 (x0 : nat) := fun y0 : nat => (x0 = (NUMERAL 0)) \/ ((fun y1 : nat => x0 = (S y1)) y0).
Definition term126 (x0 : nat -> Prop) (x1 : nat) := ((fun y0 : nat => (x0 y0) /\ ((~ (x0 (NUMERAL 0))) /\ (forall y1 : nat, ~ (x0 (S y1))))) x1) \/ ((fun y0 : nat => (forall y1 : nat, ~ (x0 y1)) /\ ((x0 (NUMERAL 0)) \/ (x0 (S y0)))) x1).
Definition term251 (a0 : Type') (x0 : list a0) := imp (forall y0 : a0, (@List.In a0 y0 x0) = (exists y1 : nat, (Peano.lt y1 (@List.length a0 x0)) /\ (y0 = (@EL a0 y1 x0)))).
Definition term238 (x0 : nat -> Prop) (x1 : nat) := (~ (x0 (S x1))) -> x0 (S x1).
Definition term146 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := exists y0 : a0 -> a1, forall y1 : a0, x0 y1 (y0 y1).
Definition term114 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => (x0 y0) /\ ((~ (x0 (NUMERAL 0))) /\ (forall y1 : nat, ~ (x0 (S y1))))) x1.
Definition term279 (a0 : Type') (x0 : a0) := fun y0 : nat => (Peano.lt y0 (@List.length a0 (@nil a0))) /\ (x0 = (@EL a0 y0 (@nil a0))).
Definition term289 (a0 : Type') := forall y0 : a0, forall y1 : list a0, (@List.length a0 (@cons a0 y0 y1)) = (S (@List.length a0 y1)).
Definition term263 (a0 : Type') := forall y0 : a0, forall y1 : list a0, (forall y2 : a0, (@List.In a0 y2 y1) = (exists y3 : nat, (Peano.lt y3 (@List.length a0 y1)) /\ (y2 = (@EL a0 y3 y1)))) -> forall y2 : a0, (@List.In a0 y2 (@cons a0 y0 y1)) = (exists y3 : nat, (Peano.lt y3 (@List.length a0 (@cons a0 y0 y1))) /\ (y2 = (@EL a0 y3 (@cons a0 y0 y1)))).
Definition term262 (a0 : Type') := forall y0 : a0, forall y1 : list a0, ((fun y2 : list a0 => forall y3 : a0, (@List.In a0 y3 y2) = (exists y4 : nat, (Peano.lt y4 (@List.length a0 y2)) /\ (y3 = (@EL a0 y4 y2)))) y1) -> (fun y2 : list a0 => forall y3 : a0, (@List.In a0 y3 y2) = (exists y4 : nat, (Peano.lt y4 (@List.length a0 y2)) /\ (y3 = (@EL a0 y4 y2)))) (@cons a0 y0 y1).
Definition term21 := fun y0 : nat -> Prop => (~ ((exists y1 : nat, y0 y1) = ((y0 (NUMERAL 0)) \/ (exists y1 : nat, y0 (S y1))))) -> ~ (forall y1 : nat, (y1 = (NUMERAL 0)) \/ (exists y2 : nat, y1 = (S y2))).
Definition term108 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term225 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := imp ((x2 = x0) /\ (x1 x2)).
Definition term325 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) := or ((fun y0 : nat => (Peano.lt y0 (S (@List.length a0 x2))) /\ (x0 = (@EL a0 y0 (@cons a0 x1 x2)))) (NUMERAL 0)).
Definition term309 (a0 : Type') (x0 : a0) (x1 : nat) (x2 : a0) (x3 : list a0) := (Peano.lt x1 (S (@List.length a0 x3))) /\ (x0 = (@EL a0 x1 (@cons a0 x2 x3))).
Definition term282 := exists y0 : nat, False.
Definition term76 (x0 : Prop) (x1 : nat -> Prop) := x0 \/ (exists y0 : nat, x1 y0).
Definition term81 (x0 : nat -> Prop) := exists y0 : nat, (fun y1 : nat => x0 (S y1)) y0.
Definition term50 (x0 : nat -> Prop) := fun y0 : nat => ~ (x0 (S y0)).
Definition term134 (x0 : nat) := fun y0 : nat => (fun y1 : nat => x0 = (S y1)) y0.
Definition term314 (a0 : Type') (x0 : a0) (x1 : list a0) := fun y0 : a0 => (@List.In a0 y0 (@cons a0 x0 x1)) = (exists y1 : nat, (Peano.lt y1 (@List.length a0 (@cons a0 x0 x1))) /\ (y0 = (@EL a0 y1 (@cons a0 x0 x1)))).
Definition term190 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := ~ ((x1 x0) \/ (~ (x1 x2))).
Definition term321 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) := @eq Prop (exists y0 : nat, (fun y1 : nat => (Peano.lt y1 (S (@List.length a0 x2))) /\ (x0 = (@EL a0 y1 (@cons a0 x1 x2)))) y0).
Definition term285 (a0 : Type') := fun y0 : a0 => (@List.In a0 y0 (@nil a0)) = (exists y1 : nat, (Peano.lt y1 (@List.length a0 (@nil a0))) /\ (y0 = (@EL a0 y1 (@nil a0)))).
Definition term109 (x0 : nat -> Prop) (x1 : nat -> Prop) := (exists y0 : nat, x0 y0) \/ (exists y0 : nat, x1 y0).
Definition term175 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := ((x1 x2) = (x1 x0)) -> (x1 x0) \/ (~ (x1 x2)).
Definition term182 (x0 : Prop) := x0 -> ~ x0.
Definition term43 (x0 : nat -> Prop) := fun y0 : nat => ~ (x0 y0).
Definition term55 (x0 : nat -> Prop) := ~ ((x0 (NUMERAL 0)) \/ (exists y0 : nat, x0 (S y0))).
Definition term256 (a0 : Type') (x0 : a0) := fun y0 : list a0 => ((fun y1 : list a0 => forall y2 : a0, (@List.In a0 y2 y1) = (exists y3 : nat, (Peano.lt y3 (@List.length a0 y1)) /\ (y2 = (@EL a0 y3 y1)))) y0) -> (fun y1 : list a0 => forall y2 : a0, (@List.In a0 y2 y1) = (exists y3 : nat, (Peano.lt y3 (@List.length a0 y1)) /\ (y2 = (@EL a0 y3 y1)))) (@cons a0 x0 y0).
Definition term129 (x0 : nat -> Prop) := fun y0 : nat => ((x0 y0) /\ ((~ (x0 (NUMERAL 0))) /\ (forall y1 : nat, ~ (x0 (S y1))))) \/ ((forall y1 : nat, ~ (x0 y1)) /\ ((x0 (NUMERAL 0)) \/ (x0 (S y0)))).
Definition term0 (x0 : nat) := (fun y0 : nat => Peano.lt (NUMERAL 0) (S y0)) x0.
Definition term79 (x0 : nat -> Prop) := exists y0 : nat, (x0 (NUMERAL 0)) \/ ((fun y1 : nat => x0 (S y1)) y0).
Definition term95 (x0 : nat -> Prop) := exists y0 : nat, (forall y1 : nat, ~ (x0 y1)) /\ ((fun y1 : nat => (x0 (NUMERAL 0)) \/ (x0 (S y1))) y0).
Definition term296 (a0 : Type') (x0 : a0) (x1 : list a0) := exists y0 : nat, (Peano.lt y0 (@List.length a0 x1)) /\ (x0 = (@EL a0 y0 x1)).
Definition term123 (x0 : nat -> Prop) := @eq Prop ((exists y0 : nat, (x0 y0) /\ ((~ (x0 (NUMERAL 0))) /\ (forall y1 : nat, ~ (x0 (S y1))))) \/ (exists y0 : nat, (forall y1 : nat, ~ (x0 y1)) /\ ((x0 (NUMERAL 0)) \/ (x0 (S y0))))).
Definition term122 (x0 : nat -> Prop) := @eq Prop ((exists y0 : nat, (fun y1 : nat => (x0 y1) /\ ((~ (x0 (NUMERAL 0))) /\ (forall y2 : nat, ~ (x0 (S y2))))) y0) \/ (exists y0 : nat, (fun y1 : nat => (forall y2 : nat, ~ (x0 y2)) /\ ((x0 (NUMERAL 0)) \/ (x0 (S y1)))) y0)).
