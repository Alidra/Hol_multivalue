Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term69 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := fun y0 : a1 => fun y1 : a0 => x0 y0 y1.
Definition term31 := @eq Prop (~ False).
Definition term33 (x0 : Prop) := imp (~ x0).
Definition term41 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := forall y0 : prod a1 a0, ~ (x0 y0).
Definition term86 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := fun y0 : prod a1 a0 => x0 (@ε ((prod a1 a0) -> a1) (fun y1 : type1222 a0 a1 => forall y2 : a1, forall y3 : a0, (y1 (@pair a1 a0 y2 y3)) = y2) y0) (@ε ((prod a1 a0) -> a0) (fun y1 : type1221 a0 a1 => forall y2 : a1, forall y3 : a0, (y1 (@pair a1 a0 y2 y3)) = y3) y0).
Definition term20 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => ((~ y0) = (~ x0)) -> y0 = x0) x1.
Definition term29 (x0 : Prop) := ~ (~ x0).
Definition term16 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (~ (ex y0)) = (forall y1 : a0, ~ (y0 y1))) x0.
Definition term1 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := fun y0 : a0 => x0 y0.
Definition term14 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := forall y0 : prod a1 a0, x0 y0.
Definition term6 (a0 : Type') (x0 : a0 -> Prop) := @eq Prop (~ (exists y0 : a0, x0 y0)).
Definition term60 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := fun y0 : a1 => forall y1 : a0, ~ (@GABS ((prod a1 a0) -> Prop) (fun y2 : type1223 a0 a1 => forall y3 : a1, forall y4 : a0, @GEQ Prop (y2 (@pair a1 a0 y3 y4)) (x0 y3 y4)) (@pair a1 a0 y0 y1)).
Definition term44 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := @GABS ((prod a1 a0) -> Prop) (fun y0 : type1223 a0 a1 => forall y1 : a1, forall y2 : a0, @GEQ Prop (y0 (@pair a1 a0 y1 y2)) (x0 y1 y2)).
Definition term2 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => x0 y0.
Definition term135 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := fun y0 : a1 => ~ ((fun y1 : a1 => exists y2 : a0, x0 y1 y2) y0).
Definition term102 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := (fun y0 : type1223 a0 a1 => forall y1 : a1, forall y2 : a0, @GEQ Prop (y0 (@pair a1 a0 y1 y2)) (x0 y1 y2)) (@GABS ((prod a1 a0) -> Prop) (fun y0 : type1223 a0 a1 => forall y1 : a1, forall y2 : a0, @GEQ Prop (y0 (@pair a1 a0 y1 y2)) (x0 y1 y2))).
Definition term5 (a0 : Type') (x0 : a0 -> Prop) := ~ (ex x0).
Definition term71 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) (x2 : a0) := (fun y0 : a1 => fun y1 : a0 => x0 y0 y1) (@ε ((prod a1 a0) -> a1) (fun y0 : type1222 a0 a1 => forall y1 : a1, forall y2 : a0, (y0 (@pair a1 a0 y1 y2)) = y1) (@pair a1 a0 x1 x2)).
Definition term87 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : a1) (x2 : a0) := x0 (@pair a1 a0 x1 x2).
Definition term113 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := forall y0 : a1, forall y1 : a0, ~ (x0 y0 y1).
Definition term61 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := forall y0 : a1, forall y1 : a0, ~ (@GABS ((prod a1 a0) -> Prop) (fun y2 : type1223 a0 a1 => forall y3 : a1, forall y4 : a0, @GEQ Prop (y2 (@pair a1 a0 y3 y4)) (x0 y3 y4)) (@pair a1 a0 y0 y1)).
Definition term124 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := fun y0 : a1 => (fun y1 : a1 => exists y2 : a0, x0 y1 y2) y0.
Definition term0 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := (fun y0 : a0 -> a1 => (fun y1 : a0 => y0 y1) = y0) x0.
Definition term125 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) := @eq Prop ((fun y0 : a1 => (fun y1 : a1 => exists y2 : a0, x0 y1 y2) y0) x1).
Definition term3 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0, x0 y0.
Definition term94 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : type1470 a0 a1) := fun y0 : a1 => forall y1 : a0, @GEQ Prop (x0 (@pair a1 a0 y0 y1)) (x1 y0 y1).
Definition term98 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := exists y0 : type1223 a0 a1, forall y1 : a1, forall y2 : a0, @GEQ Prop (y0 (@pair a1 a0 y1 y2)) (x0 y1 y2).
Definition term84 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := exists y0 : type1223 a0 a1, forall y1 : a1, forall y2 : a0, (y0 (@pair a1 a0 y1 y2)) = (x0 y1 y2).
Definition term67 (a0 : Type') (x0 : a0) := @eq a0 ((fun y0 : a0 => y0) x0).
Definition term133 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) (x2 : a0) := ~ ((fun y0 : a0 => x0 x1 y0) x2).
Definition term114 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := @eq Prop (~ (ex (@GABS ((prod a1 a0) -> Prop) (fun y0 : type1223 a0 a1 => forall y1 : a1, forall y2 : a0, @GEQ Prop (y0 (@pair a1 a0 y1 y2)) (x0 y1 y2))))).
Definition term128 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) := ~ (exists y0 : a0, x0 x1 y0).
Definition term51 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := @eq Prop (forall y0 : prod a1 a0, (fun y1 : prod a1 a0 => ~ (@GABS ((prod a1 a0) -> Prop) (fun y2 : type1223 a0 a1 => forall y3 : a1, forall y4 : a0, @GEQ Prop (y2 (@pair a1 a0 y3 y4)) (x0 y3 y4)) y1)) y0).
Definition term35 (x0 : Prop) (x1 : Prop) := (((~ x0) = (~ x1)) -> x0 = x1) -> x0 = x1.
Definition term57 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) := forall y0 : a0, (fun y1 : prod a1 a0 => ~ (@GABS ((prod a1 a0) -> Prop) (fun y2 : type1223 a0 a1 => forall y3 : a1, forall y4 : a0, @GEQ Prop (y2 (@pair a1 a0 y3 y4)) (x0 y3 y4)) y1)) (@pair a1 a0 x1 y0).
Definition term25 (x0 : Prop) (x1 : Prop) := @eq Prop (((~ x0) = (~ x1)) -> x0 = x1).
Definition term108 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) (x2 : a0) := @GABS ((prod a1 a0) -> Prop) (fun y0 : type1223 a0 a1 => forall y1 : a1, forall y2 : a0, @GEQ Prop (y0 (@pair a1 a0 y1 y2)) (x0 y1 y2)) (@pair a1 a0 x1 x2).
Definition term48 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : prod a1 a0) := (fun y0 : prod a1 a0 => ~ (@GABS ((prod a1 a0) -> Prop) (fun y1 : type1223 a0 a1 => forall y2 : a1, forall y3 : a0, @GEQ Prop (y1 (@pair a1 a0 y2 y3)) (x0 y2 y3)) y0)) x1.
Definition term9 (a0 : Type') := fun y0 : a0 -> Prop => (~ (exists y1 : a0, y0 y1)) = (forall y1 : a0, ~ (y0 y1)).
Definition term121 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) := (fun y0 : a1 => (fun y1 : a1 => exists y2 : a0, x0 y1 y2) y0) x1.
Definition term106 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) (x2 : a0) := (fun y0 : a0 => @GEQ Prop (@GABS ((prod a1 a0) -> Prop) (fun y1 : type1223 a0 a1 => forall y2 : a1, forall y3 : a0, @GEQ Prop (y1 (@pair a1 a0 y2 y3)) (x0 y2 y3)) (@pair a1 a0 x1 y0)) (x0 x1 y0)) x2.
Definition term78 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) (x2 : a0) := x0 (@ε ((prod a1 a0) -> a1) (fun y0 : type1222 a0 a1 => forall y1 : a1, forall y2 : a0, (y0 (@pair a1 a0 y1 y2)) = y1) (@pair a1 a0 x1 x2)) (@ε ((prod a1 a0) -> a0) (fun y0 : type1221 a0 a1 => forall y1 : a1, forall y2 : a0, (y0 (@pair a1 a0 y1 y2)) = y2) (@pair a1 a0 x1 x2)).
Definition term126 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) := @eq Prop ((fun y0 : a1 => exists y1 : a0, x0 y0 y1) x1).
Definition term123 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) := exists y0 : a0, x0 x1 y0.
Definition term89 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : type1470 a0 a1) (x2 : a1) := fun y0 : a0 => (x0 (@pair a1 a0 x2 y0)) = (x1 x2 y0).
Definition term138 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := @eq Prop (((forall y0 : a1, forall y1 : a0, ~ (x0 y0 y1)) = (forall y0 : a1, forall y1 : a0, ~ (x0 y0 y1))) = True).
Definition term112 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := fun y0 : a1 => forall y1 : a0, ~ (x0 y0 y1).
Definition term131 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) := fun y0 : a0 => (fun y1 : a0 => x0 x1 y1) y0.
Definition term7 (a0 : Type') (x0 : a0 -> Prop) := @eq Prop (~ (ex x0)).
Definition term105 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) := forall y0 : a0, @GEQ Prop (@GABS ((prod a1 a0) -> Prop) (fun y1 : type1223 a0 a1 => forall y2 : a1, forall y3 : a0, @GEQ Prop (y1 (@pair a1 a0 y2 y3)) (x0 y2 y3)) (@pair a1 a0 x1 y0)) (x0 x1 y0).
Definition term73 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) := @eq (a0 -> Prop) ((fun y0 : a1 => fun y1 : a0 => x0 y0 y1) x1).
Definition term56 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) := fun y0 : a0 => ~ (@GABS ((prod a1 a0) -> Prop) (fun y1 : type1223 a0 a1 => forall y2 : a1, forall y3 : a0, @GEQ Prop (y1 (@pair a1 a0 y2 y3)) (x0 y2 y3)) (@pair a1 a0 x1 y0)).
Definition term8 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, ~ (x0 y0).
Definition term76 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) (x2 : a0) := (fun y0 : a0 => x0 x1 y0) x2.
Definition term119 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term93 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : type1470 a0 a1) := fun y0 : a1 => forall y1 : a0, (x0 (@pair a1 a0 y0 y1)) = (x1 y0 y1).
Definition term104 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) := (fun y0 : a1 => forall y1 : a0, @GEQ Prop (@GABS ((prod a1 a0) -> Prop) (fun y2 : type1223 a0 a1 => forall y3 : a1, forall y4 : a0, @GEQ Prop (y2 (@pair a1 a0 y3 y4)) (x0 y3 y4)) (@pair a1 a0 y0 y1)) (x0 y0 y1)) x1.
Definition term82 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) := forall y0 : a0, ((fun y1 : prod a1 a0 => x0 (@ε ((prod a1 a0) -> a1) (fun y2 : type1222 a0 a1 => forall y3 : a1, forall y4 : a0, (y2 (@pair a1 a0 y3 y4)) = y3) y1) (@ε ((prod a1 a0) -> a0) (fun y2 : type1221 a0 a1 => forall y3 : a1, forall y4 : a0, (y2 (@pair a1 a0 y3 y4)) = y4) y1)) (@pair a1 a0 x1 y0)) = (x0 x1 y0).
Definition term127 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) := ~ ((fun y0 : a1 => exists y1 : a0, x0 y0 y1) x1).
Definition term137 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := @eq Prop ((fun y0 : Prop => y0 = True) ((forall y0 : a1, forall y1 : a0, ~ (x0 y0 y1)) = (forall y0 : a1, forall y1 : a0, ~ (x0 y0 y1)))).
Definition term120 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term49 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : prod a1 a0) := ~ (@GABS ((prod a1 a0) -> Prop) (fun y0 : type1223 a0 a1 => forall y1 : a1, forall y2 : a0, @GEQ Prop (y0 (@pair a1 a0 y1 y2)) (x0 y1 y2)) x1).
Definition term68 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0) := (fun y0 : a0 => y0) (@ε ((prod a1 a0) -> a0) (fun y0 : type1221 a0 a1 => forall y1 : a1, forall y2 : a0, (y0 (@pair a1 a0 y1 y2)) = y2) (@pair a1 a0 x0 x1)).
Definition term66 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0) := (fun y0 : a1 => y0) (@ε ((prod a1 a0) -> a1) (fun y0 : type1222 a0 a1 => forall y1 : a1, forall y2 : a0, (y0 (@pair a1 a0 y1 y2)) = y1) (@pair a1 a0 x0 x1)).
Definition term80 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) (x2 : a0) := @eq Prop (x0 x1 x2).
Definition term40 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := ~ (ex x0).
Definition term53 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) (x2 : a0) := (fun y0 : prod a1 a0 => ~ (@GABS ((prod a1 a0) -> Prop) (fun y1 : type1223 a0 a1 => forall y2 : a1, forall y3 : a0, @GEQ Prop (y1 (@pair a1 a0 y2 y3)) (x0 y2 y3)) y0)) (@pair a1 a0 x1 x2).
Definition term38 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := ex (@GABS ((prod a1 a0) -> Prop) (fun y0 : type1223 a0 a1 => forall y1 : a1, forall y2 : a0, @GEQ Prop (y0 (@pair a1 a0 y1 y2)) (x0 y1 y2))).
Definition term65 (a0 : Type') (x0 : a0) := (fun y0 : a0 => y0) x0.
Definition term42 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := ~ (ex (@GABS ((prod a1 a0) -> Prop) (fun y0 : type1223 a0 a1 => forall y1 : a1, forall y2 : a0, @GEQ Prop (y0 (@pair a1 a0 y1 y2)) (x0 y1 y2)))).
Definition term47 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := fun y0 : prod a1 a0 => ~ (@GABS ((prod a1 a0) -> Prop) (fun y1 : type1223 a0 a1 => forall y2 : a1, forall y3 : a0, @GEQ Prop (y1 (@pair a1 a0 y2 y3)) (x0 y2 y3)) y0).
Definition term101 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := (exists y0 : type1223 a0 a1, forall y1 : a1, forall y2 : a0, @GEQ Prop (y0 (@pair a1 a0 y1 y2)) (x0 y1 y2)) -> (fun y0 : type1223 a0 a1 => forall y1 : a1, forall y2 : a0, @GEQ Prop (y0 (@pair a1 a0 y1 y2)) (x0 y1 y2)) (@GABS ((prod a1 a0) -> Prop) (fun y0 : type1223 a0 a1 => forall y1 : a1, forall y2 : a0, @GEQ Prop (y0 (@pair a1 a0 y1 y2)) (x0 y1 y2))).
Definition term43 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := forall y0 : prod a1 a0, ~ (@GABS ((prod a1 a0) -> Prop) (fun y1 : type1223 a0 a1 => forall y2 : a1, forall y3 : a0, @GEQ Prop (y1 (@pair a1 a0 y2 y3)) (x0 y2 y3)) y0).
Definition term77 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) (x2 : a0) := (fun y0 : a0 => x0 (@ε ((prod a1 a0) -> a1) (fun y1 : type1222 a0 a1 => forall y2 : a1, forall y3 : a0, (y1 (@pair a1 a0 y2 y3)) = y2) (@pair a1 a0 x1 x2)) y0) (@ε ((prod a1 a0) -> a0) (fun y0 : type1221 a0 a1 => forall y1 : a1, forall y2 : a0, (y0 (@pair a1 a0 y1 y2)) = y2) (@pair a1 a0 x1 x2)).
Definition term4 (a0 : Type') (x0 : a0 -> Prop) := ~ (exists y0 : a0, x0 y0).
Definition term22 (x0 : Prop) := ((~ True) = (~ x0)) -> True = x0.
Definition term23 (x0 : Prop) (x1 : Prop) := @eq Prop ((fun y0 : Prop => ((~ y0) = (~ x0)) -> y0 = x0) x1).
Definition term132 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) (x2 : a0) := @eq Prop ((fun y0 : a0 => (fun y1 : a0 => x0 x1 y1) y0) x2).
Definition term64 (a0 : Type') := fun y0 : a0 => y0.
Definition term139 (a0 : Type') (a1 : Type') := forall y0 : type1470 a0 a1, (ex (@GABS ((prod a1 a0) -> Prop) (fun y1 : type1223 a0 a1 => forall y2 : a1, forall y3 : a0, @GEQ Prop (y1 (@pair a1 a0 y2 y3)) (y0 y2 y3)))) = (exists y1 : a1, exists y2 : a0, y0 y1 y2).
Definition term90 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : type1470 a0 a1) (x2 : a1) := fun y0 : a0 => @GEQ Prop (x0 (@pair a1 a0 x2 y0)) (x1 x2 y0).
Definition term28 := @eq Prop (~ True).
Definition term34 (x0 : Prop) := (~ x0) -> ~ x0.
Definition term115 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := @eq Prop (forall y0 : a1, forall y1 : a0, ~ (x0 y0 y1)).
Definition term26 (x0 : Prop) := (fun y0 : Prop => ((~ y0) = (~ x0)) -> y0 = x0) False.
Definition term18 (x0 : Prop) := (x0 = True) \/ (x0 = False).
Definition term72 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) (x2 : a0) := fun y0 : a0 => x0 (@ε ((prod a1 a0) -> a1) (fun y1 : type1222 a0 a1 => forall y2 : a1, forall y3 : a0, (y1 (@pair a1 a0 y2 y3)) = y2) (@pair a1 a0 x1 x2)) y0.
Definition term122 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) := (fun y0 : a1 => exists y1 : a0, x0 y0 y1) x1.
Definition term15 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := forall y0 : a1, forall y1 : a0, x0 (@pair a1 a0 y0 y1).
Definition term12 (a0 : Type') := forall y0 : a0 -> Prop, (~ (ex y0)) = (forall y1 : a0, ~ (y0 y1)).
Definition term11 (a0 : Type') := forall y0 : a0 -> Prop, (~ (exists y1 : a0, y0 y1)) = (forall y1 : a0, ~ (y0 y1)).
Definition term21 (x0 : Prop) := (fun y0 : Prop => ((~ y0) = (~ x0)) -> y0 = x0) True.
Definition term134 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) := fun y0 : a0 => ~ ((fun y1 : a0 => x0 x1 y1) y0).
Definition term110 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) := fun y0 : a0 => ~ (x0 x1 y0).
Definition term111 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) := forall y0 : a0, ~ (x0 x1 y0).
Definition term107 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) (x2 : a0) := @GEQ Prop (@GABS ((prod a1 a0) -> Prop) (fun y0 : type1223 a0 a1 => forall y1 : a1, forall y2 : a0, @GEQ Prop (y0 (@pair a1 a0 y1 y2)) (x0 y1 y2)) (@pair a1 a0 x1 x2)) (x0 x1 x2).
Definition term91 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : type1470 a0 a1) (x2 : a1) := forall y0 : a0, (x0 (@pair a1 a0 x2 y0)) = (x1 x2 y0).
Definition term55 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) := fun y0 : a0 => (fun y1 : prod a1 a0 => ~ (@GABS ((prod a1 a0) -> Prop) (fun y2 : type1223 a0 a1 => forall y3 : a1, forall y4 : a0, @GEQ Prop (y2 (@pair a1 a0 y3 y4)) (x0 y3 y4)) y1)) (@pair a1 a0 x1 y0).
Definition term45 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := forall y0 : prod a1 a0, (fun y1 : prod a1 a0 => ~ (@GABS ((prod a1 a0) -> Prop) (fun y2 : type1223 a0 a1 => forall y3 : a1, forall y4 : a0, @GEQ Prop (y2 (@pair a1 a0 y3 y4)) (x0 y3 y4)) y1)) y0.
Definition term92 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : type1470 a0 a1) (x2 : a1) := forall y0 : a0, @GEQ Prop (x0 (@pair a1 a0 x2 y0)) (x1 x2 y0).
Definition term103 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := forall y0 : a1, forall y1 : a0, @GEQ Prop (@GABS ((prod a1 a0) -> Prop) (fun y2 : type1223 a0 a1 => forall y3 : a1, forall y4 : a0, @GEQ Prop (y2 (@pair a1 a0 y3 y4)) (x0 y3 y4)) (@pair a1 a0 y0 y1)) (x0 y0 y1).
Definition term96 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : type1470 a0 a1) := forall y0 : a1, forall y1 : a0, @GEQ Prop (x0 (@pair a1 a0 y0 y1)) (x1 y0 y1).
Definition term95 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : type1470 a0 a1) := forall y0 : a1, forall y1 : a0, (x0 (@pair a1 a0 y0 y1)) = (x1 y0 y1).
Definition term83 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := forall y0 : a1, forall y1 : a0, ((fun y2 : prod a1 a0 => x0 (@ε ((prod a1 a0) -> a1) (fun y3 : type1222 a0 a1 => forall y4 : a1, forall y5 : a0, (y3 (@pair a1 a0 y4 y5)) = y4) y2) (@ε ((prod a1 a0) -> a0) (fun y3 : type1221 a0 a1 => forall y4 : a1, forall y5 : a0, (y3 (@pair a1 a0 y4 y5)) = y5) y2)) (@pair a1 a0 y0 y1)) = (x0 y0 y1).
Definition term37 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := ((~ (ex (@GABS ((prod a1 a0) -> Prop) (fun y0 : type1223 a0 a1 => forall y1 : a1, forall y2 : a0, @GEQ Prop (y0 (@pair a1 a0 y1 y2)) (x0 y1 y2))))) = (~ (exists y0 : a1, exists y1 : a0, x0 y0 y1))) -> (ex (@GABS ((prod a1 a0) -> Prop) (fun y0 : type1223 a0 a1 => forall y1 : a1, forall y2 : a0, @GEQ Prop (y0 (@pair a1 a0 y1 y2)) (x0 y1 y2)))) = (exists y0 : a1, exists y1 : a0, x0 y0 y1).
Definition term24 (x0 : Prop) (x1 : Prop) := ((~ x0) = (~ x1)) -> x0 = x1.
Definition term58 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) := forall y0 : a0, ~ (@GABS ((prod a1 a0) -> Prop) (fun y1 : type1223 a0 a1 => forall y2 : a1, forall y3 : a0, @GEQ Prop (y1 (@pair a1 a0 y2 y3)) (x0 y2 y3)) (@pair a1 a0 x1 y0)).
Definition term109 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) (x2 : a0) := ~ (x0 x1 x2).
Definition term75 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) := @eq (a0 -> Prop) (fun y0 : a0 => x0 x1 y0).
Definition term32 (x0 : Prop) := imp ((~ False) = (~ x0)).
Definition term30 (x0 : Prop) := imp ((~ True) = (~ x0)).
Definition term52 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := @eq Prop (forall y0 : prod a1 a0, ~ (@GABS ((prod a1 a0) -> Prop) (fun y1 : type1223 a0 a1 => forall y2 : a1, forall y3 : a0, @GEQ Prop (y1 (@pair a1 a0 y2 y3)) (x0 y2 y3)) y0)).
Definition term97 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := fun y0 : type1223 a0 a1 => forall y1 : a1, forall y2 : a0, @GEQ Prop (y0 (@pair a1 a0 y1 y2)) (x0 y1 y2).
Definition term85 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := fun y0 : type1223 a0 a1 => forall y1 : a1, forall y2 : a0, (y0 (@pair a1 a0 y1 y2)) = (x0 y1 y2).
Definition term81 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) (x2 : a0) := (fun y0 : prod a1 a0 => x0 (@ε ((prod a1 a0) -> a1) (fun y1 : type1222 a0 a1 => forall y2 : a1, forall y3 : a0, (y1 (@pair a1 a0 y2 y3)) = y2) y0) (@ε ((prod a1 a0) -> a0) (fun y1 : type1221 a0 a1 => forall y2 : a1, forall y3 : a0, (y1 (@pair a1 a0 y2 y3)) = y3) y0)) (@pair a1 a0 x1 x2).
Definition term10 (a0 : Type') := fun y0 : a0 -> Prop => (~ (ex y0)) = (forall y1 : a0, ~ (y0 y1)).
Definition term118 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := fun y0 : a1 => exists y1 : a0, x0 y0 y1.
Definition term19 (x0 : Prop) := fun y0 : Prop => ((~ y0) = (~ x0)) -> y0 = x0.
Definition term136 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := (fun y0 : Prop => y0 = True) ((forall y0 : a1, forall y1 : a0, ~ (x0 y0 y1)) = (forall y0 : a1, forall y1 : a0, ~ (x0 y0 y1))).
Definition term63 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0) := @ε ((prod a1 a0) -> a0) (fun y0 : type1221 a0 a1 => forall y1 : a1, forall y2 : a0, (y0 (@pair a1 a0 y1 y2)) = y2) (@pair a1 a0 x0 x1).
Definition term62 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0) := @ε ((prod a1 a0) -> a1) (fun y0 : type1222 a0 a1 => forall y1 : a1, forall y2 : a0, (y0 (@pair a1 a0 y1 y2)) = y1) (@pair a1 a0 x0 x1).
Definition term117 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := forall y0 : a1, ~ ((fun y1 : a1 => exists y2 : a0, x0 y1 y2) y0).
Definition term74 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) := fun y0 : a0 => x0 x1 y0.
Definition term116 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := ~ (exists y0 : a1, exists y1 : a0, x0 y0 y1).
Definition term70 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) := (fun y0 : a1 => fun y1 : a0 => x0 y0 y1) x1.
Definition term39 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := exists y0 : a1, exists y1 : a0, x0 y0 y1.
Definition term79 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) (x2 : a0) := @eq Prop ((fun y0 : a0 => x0 x1 y0) x2).
Definition term17 (x0 : Prop) := (fun y0 : Prop => (y0 = True) \/ (y0 = False)) x0.
Definition term50 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := fun y0 : prod a1 a0 => (fun y1 : prod a1 a0 => ~ (@GABS ((prod a1 a0) -> Prop) (fun y2 : type1223 a0 a1 => forall y3 : a1, forall y4 : a0, @GEQ Prop (y2 (@pair a1 a0 y3 y4)) (x0 y3 y4)) y1)) y0.
Definition term129 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) := forall y0 : a0, ~ ((fun y1 : a0 => x0 x1 y1) y0).
Definition term46 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := forall y0 : a1, forall y1 : a0, (fun y2 : prod a1 a0 => ~ (@GABS ((prod a1 a0) -> Prop) (fun y3 : type1223 a0 a1 => forall y4 : a1, forall y5 : a0, @GEQ Prop (y3 (@pair a1 a0 y4 y5)) (x0 y4 y5)) y2)) (@pair a1 a0 y0 y1).
Definition term54 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) (x2 : a0) := ~ (@GABS ((prod a1 a0) -> Prop) (fun y0 : type1223 a0 a1 => forall y1 : a1, forall y2 : a0, @GEQ Prop (y0 (@pair a1 a0 y1 y2)) (x0 y1 y2)) (@pair a1 a0 x1 x2)).
Definition term130 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) (x2 : a0) := (fun y0 : a0 => (fun y1 : a0 => x0 x1 y1) y0) x2.
Definition term13 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := (fun y0 : type1223 a0 a1 => (forall y1 : prod a1 a0, y0 y1) = (forall y1 : a1, forall y2 : a0, y0 (@pair a1 a0 y1 y2))) x0.
Definition term88 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : type1470 a0 a1) (x2 : a1) (x3 : a0) := @GEQ Prop (x0 (@pair a1 a0 x2 x3)) (x1 x2 x3).
Definition term59 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := fun y0 : a1 => forall y1 : a0, (fun y2 : prod a1 a0 => ~ (@GABS ((prod a1 a0) -> Prop) (fun y3 : type1223 a0 a1 => forall y4 : a1, forall y5 : a0, @GEQ Prop (y3 (@pair a1 a0 y4 y5)) (x0 y4 y5)) y2)) (@pair a1 a0 y0 y1).
Definition term27 (x0 : Prop) := ((~ False) = (~ x0)) -> False = x0.
Definition term36 (x0 : Prop) (x1 : Prop) := (((~ x0) = (~ x1)) -> x0 = x1) -> ((~ x0) = (~ x1)) -> x0 = x1.
Definition term100 (a0 : Type') (a1 : Type') (x0 : type330 a0 a1) := (ex x0) -> x0 (@GABS ((prod a1 a0) -> Prop) x0).
Definition term99 (a0 : Type') (x0 : a0 -> Prop) := (ex x0) -> x0 (@GABS a0 x0).
