Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := (fun y0 : a0 -> a1 => forall y1 : a0, ((fun y2 : a0 => y0 y2) y1) = (y0 y1)) x0.
Definition term123 (a0 : Type') := fun y0 : type1244 a0 => forall y1 : type1669, (forall y2 : type1402 a0, (y0 y1 y2 (@nil a0)) = True) /\ (forall y2 : a0, forall y3 : type1402 a0, forall y4 : list a0, (y0 y1 y3 (@cons a0 y2 y4)) = ((@List.Forall a0 (y3 y2) y4) /\ (y0 y1 y3 y4))).
Definition term114 (a0 : Type') := @eq Prop (forall y0 : type1669, exists y1 : type416 a0, (forall y2 : type1402 a0, (y1 y2 (@nil a0)) = True) /\ (forall y2 : a0, forall y3 : type1402 a0, forall y4 : list a0, (y1 y3 (@cons a0 y2 y4)) = ((@List.Forall a0 (y3 y2) y4) /\ (y1 y3 y4)))).
Definition term113 (a0 : Type') := @eq Prop (forall y0 : type1669, exists y1 : type416 a0, (fun y2 : type1669 => fun y3 : type416 a0 => (forall y4 : type1402 a0, (y3 y4 (@nil a0)) = True) /\ (forall y4 : a0, forall y5 : type1402 a0, forall y6 : list a0, (y3 y5 (@cons a0 y4 y6)) = ((@List.Forall a0 (y5 y4) y6) /\ (y3 y5 y6)))) y0 y1).
Definition term52 (a0 : Type') (x0 : type1127 a0) := forall y0 : a0, forall y1 : type1402 a0, forall y2 : list a0, (x0 (@cons a0 y0 y2) y1) = ((@List.Forall a0 (y1 y0) y2) /\ (x0 y2 y1)).
Definition term51 (a0 : Type') (x0 : type416 a0) := forall y0 : a0, forall y1 : type1402 a0, forall y2 : list a0, (x0 y1 (@cons a0 y0 y2)) = ((@List.Forall a0 (y1 y0) y2) /\ (x0 y1 y2)).
Definition term122 (a0 : Type') := fun y0 : type1244 a0 => forall y1 : type1669, (fun y2 : type1669 => fun y3 : type416 a0 => (forall y4 : type1402 a0, (y3 y4 (@nil a0)) = True) /\ (forall y4 : a0, forall y5 : type1402 a0, forall y6 : list a0, (y3 y5 (@cons a0 y4 y6)) = ((@List.Forall a0 (y5 y4) y6) /\ (y3 y5 y6)))) y1 (y0 y1).
Definition term5 (a0 : Type') (x0 : type1127 a0) (x1 : type1402 a0) := (fun y0 : type1402 a0 => fun y1 : list a0 => x0 y1 y0) x1.
Definition term65 (a0 : Type') (a1 : Type') (x0 : a1) := (fun y0 : a1 => forall y1 : type1394 a0 a1, exists y2 : type1142 a0 a1, ((y2 (@nil a0)) = y0) /\ (forall y3 : a0, forall y4 : list a0, (y2 (@cons a0 y3 y4)) = (y1 y3 y4 (y2 y4)))) x0.
Definition term8 (a0 : Type') (x0 : type1127 a0) (x1 : type1402 a0) := fun y0 : list a0 => x0 y0 x1.
Definition term60 (a0 : Type') (x0 : a0) (x1 : type1127 a0) (x2 : list a0) := (fun y0 : list a0 => (x1 (@cons a0 x0 y0)) = (fun y1 : type1402 a0 => (@List.Forall a0 (y1 x0) y0) /\ (x1 y0 y1))) x2.
Definition term71 (a0 : Type') := fun y0 : a0 => fun y1 : list a0 => fun y2 : type421 a0 => fun y3 : type1402 a0 => (@List.Forall a0 (y3 y0) y1) /\ (y2 y3).
Definition term83 (a0 : Type') (x0 : type1127 a0) := fun y0 : a0 => forall y1 : list a0, (x0 (@cons a0 y0 y1)) = ((fun y2 : a0 => fun y3 : list a0 => fun y4 : type421 a0 => fun y5 : type1402 a0 => (@List.Forall a0 (y5 y2) y3) /\ (y4 y5)) y0 y1 (x0 y1)).
Definition term75 (a0 : Type') (x0 : a0) (x1 : list a0) := (fun y0 : list a0 => fun y1 : type421 a0 => fun y2 : type1402 a0 => (@List.Forall a0 (y2 x0) y0) /\ (y1 y2)) x1.
Definition term39 (a0 : Type') (x0 : a0) (x1 : type416 a0) (x2 : type1402 a0) (x3 : list a0) := (@List.Forall a0 (x2 x0) x3) /\ (x1 x2 x3).
Definition term107 (a0 : Type') (x0 : type1669) (x1 : type416 a0) := (fun y0 : type1669 => fun y1 : type416 a0 => (forall y2 : type1402 a0, (y1 y2 (@nil a0)) = True) /\ (forall y2 : a0, forall y3 : type1402 a0, forall y4 : list a0, (y1 y3 (@cons a0 y2 y4)) = ((@List.Forall a0 (y3 y2) y4) /\ (y1 y3 y4)))) x0 x1.
Definition term105 (a0 : Type') := fun y0 : type1669 => fun y1 : type416 a0 => (forall y2 : type1402 a0, (y1 y2 (@nil a0)) = True) /\ (forall y2 : a0, forall y3 : type1402 a0, forall y4 : list a0, (y1 y3 (@cons a0 y2 y4)) = ((@List.Forall a0 (y3 y2) y4) /\ (y1 y3 y4))).
Definition term78 (a0 : Type') (x0 : a0) (x1 : type1127 a0) (x2 : list a0) := (fun y0 : type421 a0 => fun y1 : type1402 a0 => (@List.Forall a0 (y1 x0) x2) /\ (y0 y1)) (x1 x2).
Definition term1 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := forall y0 : a0, ((fun y1 : a0 => x0 y1) y0) = (x0 y0).
Definition term23 (a0 : Type') (x0 : type416 a0) := forall y0 : type1402 a0, (x0 y0 (@nil a0)) = True.
Definition term56 (a0 : Type') (x0 : type1402 a0) := (fun y0 : type1402 a0 => True) x0.
Definition term7 (a0 : Type') (x0 : type1127 a0) (x1 : type1402 a0) := (fun y0 : type1402 a0 => (fun y1 : type1402 a0 => fun y2 : list a0 => x0 y2 y1) y0) x1.
Definition term67 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : type1394 a0 a1) := (fun y0 : type1394 a0 a1 => exists y1 : type1142 a0 a1, ((y1 (@nil a0)) = x0) /\ (forall y2 : a0, forall y3 : list a0, (y1 (@cons a0 y2 y3)) = (y0 y2 y3 (y1 y3)))) x1.
Definition term6 (a0 : Type') (x0 : type416 a0) (x1 : type1402 a0) := (fun y0 : type1402 a0 => x0 y0) x1.
Definition term36 (a0 : Type') (x0 : type1127 a0) (x1 : type1402 a0) (x2 : list a0) := @eq Prop ((fun y0 : list a0 => (fun y1 : list a0 => x0 y1 x1) y0) x2).
Definition term12 (a0 : Type') (x0 : type1127 a0) (x1 : type1402 a0) := (fun y0 : list a0 => x0 y0 x1) (@nil a0).
Definition term92 (a0 : Type') := fun y0 : type1127 a0 => (forall y1 : type1402 a0, (y0 (@nil a0) y1) = True) /\ (forall y1 : a0, forall y2 : type1402 a0, forall y3 : list a0, (y0 (@cons a0 y1 y3) y2) = ((@List.Forall a0 (y2 y1) y3) /\ (y0 y3 y2))).
Definition term35 (a0 : Type') (x0 : type1127 a0) (x1 : type1402 a0) (x2 : list a0) := (fun y0 : list a0 => (fun y1 : list a0 => x0 y1 x1) y0) x2.
Definition term59 (a0 : Type') (x0 : a0) (x1 : type1127 a0) := forall y0 : list a0, (x1 (@cons a0 x0 y0)) = (fun y1 : type1402 a0 => (@List.Forall a0 (y1 x0) y0) /\ (x1 y0 y1)).
Definition term109 (a0 : Type') (x0 : type1669) := fun y0 : type416 a0 => (fun y1 : type1669 => fun y2 : type416 a0 => (forall y3 : type1402 a0, (y2 y3 (@nil a0)) = True) /\ (forall y3 : a0, forall y4 : type1402 a0, forall y5 : list a0, (y2 y4 (@cons a0 y3 y5)) = ((@List.Forall a0 (y4 y3) y5) /\ (y2 y4 y5)))) x0 y0.
Definition term128 (a0 : Type') := (fun y0 : type1244 a0 => forall y1 : type1669, (forall y2 : type1402 a0, (y0 y1 y2 (@nil a0)) = True) /\ (forall y2 : a0, forall y3 : type1402 a0, forall y4 : list a0, (y0 y1 y3 (@cons a0 y2 y4)) = ((@List.Forall a0 (y3 y2) y4) /\ (y0 y1 y3 y4)))) (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) -> (a0 -> a0 -> Prop) -> (list a0) -> Prop) (fun y0 : type1244 a0 => forall y1 : type1669, (forall y2 : type1402 a0, (y0 y1 y2 (@nil a0)) = True) /\ (forall y2 : a0, forall y3 : type1402 a0, forall y4 : list a0, (y0 y1 y3 (@cons a0 y2 y4)) = ((@List.Forall a0 (y3 y2) y4) /\ (y0 y1 y3 y4))))).
Definition term50 (a0 : Type') (x0 : type1127 a0) := fun y0 : a0 => forall y1 : type1402 a0, forall y2 : list a0, (x0 (@cons a0 y0 y2) y1) = ((@List.Forall a0 (y1 y0) y2) /\ (x0 y2 y1)).
Definition term49 (a0 : Type') (x0 : type416 a0) := fun y0 : a0 => forall y1 : type1402 a0, forall y2 : list a0, (x0 y1 (@cons a0 y0 y2)) = ((@List.Forall a0 (y1 y0) y2) /\ (x0 y1 y2)).
Definition term121 (a0 : Type') (x0 : type1244 a0) := forall y0 : type1669, (forall y1 : type1402 a0, (x0 y0 y1 (@nil a0)) = True) /\ (forall y1 : a0, forall y2 : type1402 a0, forall y3 : list a0, (x0 y0 y2 (@cons a0 y1 y3)) = ((@List.Forall a0 (y2 y1) y3) /\ (x0 y0 y2 y3))).
Definition term93 (a0 : Type') := exists y0 : type416 a0, (forall y1 : type1402 a0, (y0 y1 (@nil a0)) = True) /\ (forall y1 : a0, forall y2 : type1402 a0, forall y3 : list a0, (y0 y2 (@cons a0 y1 y3)) = ((@List.Forall a0 (y2 y1) y3) /\ (y0 y2 y3))).
Definition term91 (a0 : Type') := exists y0 : type1127 a0, (forall y1 : type1402 a0, (y0 (@nil a0) y1) = True) /\ (forall y1 : a0, forall y2 : type1402 a0, forall y3 : list a0, (y0 (@cons a0 y1 y3) y2) = ((@List.Forall a0 (y2 y1) y3) /\ (y0 y3 y2))).
Definition term61 (a0 : Type') (x0 : type1127 a0) (x1 : a0) (x2 : list a0) := x0 (@cons a0 x1 x2).
Definition term117 (a0 : Type') (x0 : type1244 a0) (x1 : type1669) := (forall y0 : type1402 a0, (x0 x1 y0 (@nil a0)) = True) /\ (forall y0 : a0, forall y1 : type1402 a0, forall y2 : list a0, (x0 x1 y1 (@cons a0 y0 y2)) = ((@List.Forall a0 (y1 y0) y2) /\ (x0 x1 y1 y2))).
Definition term54 (a0 : Type') (x0 : type1127 a0) := (forall y0 : type1402 a0, (x0 (@nil a0) y0) = True) /\ (forall y0 : a0, forall y1 : type1402 a0, forall y2 : list a0, (x0 (@cons a0 y0 y2) y1) = ((@List.Forall a0 (y1 y0) y2) /\ (x0 y2 y1))).
Definition term53 (a0 : Type') (x0 : type416 a0) := (forall y0 : type1402 a0, (x0 y0 (@nil a0)) = True) /\ (forall y0 : a0, forall y1 : type1402 a0, forall y2 : list a0, (x0 y1 (@cons a0 y0 y2)) = ((@List.Forall a0 (y1 y0) y2) /\ (x0 y1 y2))).
Definition term40 (a0 : Type') (x0 : a0) (x1 : type1127 a0) (x2 : list a0) (x3 : type1402 a0) := (@List.Forall a0 (x3 x0) x2) /\ (x1 x2 x3).
Definition term99 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := forall y0 : a0, exists y1 : a1, x0 y0 y1.
Definition term18 (a0 : Type') (x0 : type1127 a0) (x1 : type1402 a0) := @eq Prop ((fun y0 : list a0 => x0 y0 x1) (@nil a0)).
Definition term124 (a0 : Type') := exists y0 : type1244 a0, forall y1 : type1669, (forall y2 : type1402 a0, (y0 y1 y2 (@nil a0)) = True) /\ (forall y2 : a0, forall y3 : type1402 a0, forall y4 : list a0, (y0 y1 y3 (@cons a0 y2 y4)) = ((@List.Forall a0 (y3 y2) y4) /\ (y0 y1 y3 y4))).
Definition term104 (a0 : Type') := exists y0 : type1244 a0, forall y1 : type1669, (fun y2 : type1669 => fun y3 : type416 a0 => (forall y4 : type1402 a0, (y3 y4 (@nil a0)) = True) /\ (forall y4 : a0, forall y5 : type1402 a0, forall y6 : list a0, (y3 y5 (@cons a0 y4 y6)) = ((@List.Forall a0 (y5 y4) y6) /\ (y3 y5 y6)))) y1 (y0 y1).
Definition term102 (a0 : Type') (x0 : type1241 a0) := exists y0 : type1244 a0, forall y1 : type1669, x0 y1 (y0 y1).
Definition term120 (a0 : Type') (x0 : type1244 a0) := forall y0 : type1669, (fun y1 : type1669 => fun y2 : type416 a0 => (forall y3 : type1402 a0, (y2 y3 (@nil a0)) = True) /\ (forall y3 : a0, forall y4 : type1402 a0, forall y5 : list a0, (y2 y4 (@cons a0 y3 y5)) = ((@List.Forall a0 (y4 y3) y5) /\ (y2 y4 y5)))) y0 (x0 y0).
Definition term74 (a0 : Type') (x0 : a0) (x1 : list a0) := (fun y0 : a0 => fun y1 : list a0 => fun y2 : type421 a0 => fun y3 : type1402 a0 => (@List.Forall a0 (y3 y0) y1) /\ (y2 y3)) x0 x1.
Definition term116 (a0 : Type') (x0 : type1244 a0) (x1 : type1669) := (fun y0 : type416 a0 => (forall y1 : type1402 a0, (y0 y1 (@nil a0)) = True) /\ (forall y1 : a0, forall y2 : type1402 a0, forall y3 : list a0, (y0 y2 (@cons a0 y1 y3)) = ((@List.Forall a0 (y2 y1) y3) /\ (y0 y2 y3)))) (x0 x1).
Definition term73 (a0 : Type') (x0 : a0) := fun y0 : list a0 => fun y1 : type421 a0 => fun y2 : type1402 a0 => (@List.Forall a0 (y2 x0) y0) /\ (y1 y2).
Definition term126 (a0 : Type') := fun y0 : type338 a0 => y0 (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) -> (a0 -> a0 -> Prop) -> (list a0) -> Prop) y0).
Definition term9 (a0 : Type') (x0 : type1127 a0) := fun y0 : type1402 a0 => (fun y1 : type1402 a0 => fun y2 : list a0 => x0 y2 y1) y0.
Definition term37 (a0 : Type') (x0 : type1127 a0) (x1 : type1402 a0) (x2 : list a0) := @eq Prop ((fun y0 : list a0 => x0 y0 x1) x2).
Definition term42 (a0 : Type') (x0 : a0) (x1 : type1127 a0) (x2 : type1402 a0) := fun y0 : list a0 => (x1 (@cons a0 x0 y0) x2) = ((@List.Forall a0 (x2 x0) y0) /\ (x1 y0 x2)).
Definition term2 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => ((fun y1 : a0 => x0 y1) y0) = (x0 y0)) x1.
Definition term82 (a0 : Type') (x0 : a0) (x1 : type1127 a0) := forall y0 : list a0, (x1 (@cons a0 x0 y0)) = ((fun y1 : a0 => fun y2 : list a0 => fun y3 : type421 a0 => fun y4 : type1402 a0 => (@List.Forall a0 (y4 y1) y2) /\ (y3 y4)) x0 y0 (x1 y0)).
Definition term86 (a0 : Type') (x0 : type1127 a0) := and ((x0 (@nil a0)) = (fun y0 : type1402 a0 => True)).
Definition term38 (a0 : Type') (x0 : type1402 a0) (x1 : a0) (x2 : list a0) := and (@List.Forall a0 (x0 x1) x2).
Definition term16 (a0 : Type') (x0 : type1127 a0) (x1 : type1402 a0) := fun y0 : list a0 => (fun y1 : list a0 => x0 y1 x1) y0.
Definition term112 (a0 : Type') := fun y0 : type1669 => exists y1 : type416 a0, (forall y2 : type1402 a0, (y1 y2 (@nil a0)) = True) /\ (forall y2 : a0, forall y3 : type1402 a0, forall y4 : list a0, (y1 y3 (@cons a0 y2 y4)) = ((@List.Forall a0 (y3 y2) y4) /\ (y1 y3 y4))).
Definition term80 (a0 : Type') (x0 : a0) (x1 : type1127 a0) := fun y0 : list a0 => (x1 (@cons a0 x0 y0)) = ((fun y1 : a0 => fun y2 : list a0 => fun y3 : type421 a0 => fun y4 : type1402 a0 => (@List.Forall a0 (y4 y1) y2) /\ (y3 y4)) x0 y0 (x1 y0)).
Definition term90 (a0 : Type') := exists y0 : type1127 a0, ((y0 (@nil a0)) = (fun y1 : type1402 a0 => True)) /\ (forall y1 : a0, forall y2 : list a0, (y0 (@cons a0 y1 y2)) = (fun y3 : type1402 a0 => (@List.Forall a0 (y3 y1) y2) /\ (y0 y2 y3))).
Definition term70 (a0 : Type') := exists y0 : type1127 a0, ((y0 (@nil a0)) = (fun y1 : type1402 a0 => True)) /\ (forall y1 : a0, forall y2 : list a0, (y0 (@cons a0 y1 y2)) = ((fun y3 : a0 => fun y4 : list a0 => fun y5 : type421 a0 => fun y6 : type1402 a0 => (@List.Forall a0 (y6 y3) y4) /\ (y5 y6)) y1 y2 (y0 y2))).
Definition term125 (a0 : Type') := fun y0 : a0 -> Prop => y0 (@ε a0 y0).
Definition term15 (a0 : Type') (x0 : type1127 a0) (x1 : type1402 a0) (x2 : list a0) := (fun y0 : list a0 => x0 y0 x1) x2.
Definition term115 (a0 : Type') (x0 : type1244 a0) (x1 : type1669) := (fun y0 : type1669 => fun y1 : type416 a0 => (forall y2 : type1402 a0, (y1 y2 (@nil a0)) = True) /\ (forall y2 : a0, forall y3 : type1402 a0, forall y4 : list a0, (y1 y3 (@cons a0 y2 y4)) = ((@List.Forall a0 (y3 y2) y4) /\ (y1 y3 y4)))) x1 (x0 x1).
Definition term3 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term81 (a0 : Type') (x0 : a0) (x1 : type1127 a0) := fun y0 : list a0 => (x1 (@cons a0 x0 y0)) = (fun y1 : type1402 a0 => (@List.Forall a0 (y1 x0) y0) /\ (x1 y0 y1)).
Definition term127 (a0 : Type') := (fun y0 : type338 a0 => y0 (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) -> (a0 -> a0 -> Prop) -> (list a0) -> Prop) y0)) (fun y0 : type1244 a0 => forall y1 : type1669, (forall y2 : type1402 a0, (y0 y1 y2 (@nil a0)) = True) /\ (forall y2 : a0, forall y3 : type1402 a0, forall y4 : list a0, (y0 y1 y3 (@cons a0 y2 y4)) = ((@List.Forall a0 (y3 y2) y4) /\ (y0 y1 y3 y4)))).
Definition term13 (a0 : Type') (x0 : type1143 a0) (x1 : list a0) := (fun y0 : list a0 => x0 y0) x1.
Definition term119 (a0 : Type') (x0 : type1244 a0) := fun y0 : type1669 => (forall y1 : type1402 a0, (x0 y0 y1 (@nil a0)) = True) /\ (forall y1 : a0, forall y2 : type1402 a0, forall y3 : list a0, (x0 y0 y2 (@cons a0 y1 y3)) = ((@List.Forall a0 (y2 y1) y3) /\ (x0 y0 y2 y3))).
Definition term21 (a0 : Type') (x0 : type416 a0) := fun y0 : type1402 a0 => (x0 y0 (@nil a0)) = True.
Definition term44 (a0 : Type') (x0 : a0) (x1 : type1127 a0) (x2 : type1402 a0) := forall y0 : list a0, (x1 (@cons a0 x0 y0) x2) = ((@List.Forall a0 (x2 x0) y0) /\ (x1 y0 x2)).
Definition term110 (a0 : Type') (x0 : type1669) := exists y0 : type416 a0, (fun y1 : type1669 => fun y2 : type416 a0 => (forall y3 : type1402 a0, (y2 y3 (@nil a0)) = True) /\ (forall y3 : a0, forall y4 : type1402 a0, forall y5 : list a0, (y2 y4 (@cons a0 y3 y5)) = ((@List.Forall a0 (y4 y3) y5) /\ (y2 y4 y5)))) x0 y0.
Definition term31 (a0 : Type') (x0 : type1127 a0) (x1 : type1402 a0) (x2 : a0) (x3 : list a0) := @eq Prop ((fun y0 : list a0 => x0 y0 x1) (@cons a0 x2 x3)).
Definition term32 (a0 : Type') (x0 : type1127 a0) (x1 : a0) (x2 : list a0) (x3 : type1402 a0) := x0 (@cons a0 x1 x2) x3.
Definition term26 (a0 : Type') (x0 : type1127 a0) := and (forall y0 : type1402 a0, (x0 (@nil a0) y0) = True).
Definition term25 (a0 : Type') (x0 : type416 a0) := and (forall y0 : type1402 a0, (x0 y0 (@nil a0)) = True).
Definition term84 (a0 : Type') (x0 : type1127 a0) := fun y0 : a0 => forall y1 : list a0, (x0 (@cons a0 y0 y1)) = (fun y2 : type1402 a0 => (@List.Forall a0 (y2 y0) y1) /\ (x0 y1 y2)).
Definition term89 (a0 : Type') := fun y0 : type1127 a0 => ((y0 (@nil a0)) = (fun y1 : type1402 a0 => True)) /\ (forall y1 : a0, forall y2 : list a0, (y0 (@cons a0 y1 y2)) = (fun y3 : type1402 a0 => (@List.Forall a0 (y3 y1) y2) /\ (y0 y2 y3))).
Definition term88 (a0 : Type') := fun y0 : type1127 a0 => ((y0 (@nil a0)) = (fun y1 : type1402 a0 => True)) /\ (forall y1 : a0, forall y2 : list a0, (y0 (@cons a0 y1 y2)) = ((fun y3 : a0 => fun y4 : list a0 => fun y5 : type421 a0 => fun y6 : type1402 a0 => (@List.Forall a0 (y6 y3) y4) /\ (y5 y6)) y1 y2 (y0 y2))).
Definition term58 (a0 : Type') (x0 : type1127 a0) (x1 : a0) := (fun y0 : a0 => forall y1 : list a0, (x0 (@cons a0 y0 y1)) = (fun y2 : type1402 a0 => (@List.Forall a0 (y2 y0) y1) /\ (x0 y1 y2))) x1.
Definition term57 (a0 : Type') (x0 : type1127 a0) := forall y0 : a0, forall y1 : list a0, (x0 (@cons a0 y0 y1)) = (fun y2 : type1402 a0 => (@List.Forall a0 (y2 y0) y1) /\ (x0 y1 y2)).
Definition term48 (a0 : Type') (x0 : a0) (x1 : type1127 a0) := forall y0 : type1402 a0, forall y1 : list a0, (x1 (@cons a0 x0 y1) y0) = ((@List.Forall a0 (y0 x0) y1) /\ (x1 y1 y0)).
Definition term47 (a0 : Type') (x0 : a0) (x1 : type416 a0) := forall y0 : type1402 a0, forall y1 : list a0, (x1 y0 (@cons a0 x0 y1)) = ((@List.Forall a0 (y0 x0) y1) /\ (x1 y0 y1)).
Definition term118 (a0 : Type') (x0 : type1244 a0) := fun y0 : type1669 => (fun y1 : type1669 => fun y2 : type416 a0 => (forall y3 : type1402 a0, (y2 y3 (@nil a0)) = True) /\ (forall y3 : a0, forall y4 : type1402 a0, forall y5 : list a0, (y2 y4 (@cons a0 y3 y5)) = ((@List.Forall a0 (y4 y3) y5) /\ (y2 y4 y5)))) y0 (x0 y0).
Definition term76 (a0 : Type') (x0 : a0) (x1 : list a0) := fun y0 : type421 a0 => fun y1 : type1402 a0 => (@List.Forall a0 (y1 x0) x1) /\ (y0 y1).
Definition term41 (a0 : Type') (x0 : a0) (x1 : type416 a0) (x2 : type1402 a0) := fun y0 : list a0 => (x1 x2 (@cons a0 x0 y0)) = ((@List.Forall a0 (x2 x0) y0) /\ (x1 x2 y0)).
Definition term27 (a0 : Type') (x0 : type416 a0) (x1 : type1402 a0) (x2 : a0) (x3 : list a0) := x0 x1 (@cons a0 x2 x3).
Definition term20 (a0 : Type') (x0 : type1127 a0) (x1 : type1402 a0) := @eq Prop (x0 (@nil a0) x1).
Definition term43 (a0 : Type') (x0 : a0) (x1 : type416 a0) (x2 : type1402 a0) := forall y0 : list a0, (x1 x2 (@cons a0 x0 y0)) = ((@List.Forall a0 (x2 x0) y0) /\ (x1 x2 y0)).
Definition term72 (a0 : Type') (x0 : a0) := (fun y0 : a0 => fun y1 : list a0 => fun y2 : type421 a0 => fun y3 : type1402 a0 => (@List.Forall a0 (y3 y0) y1) /\ (y2 y3)) x0.
Definition term62 (a0 : Type') (x0 : a0) (x1 : type1127 a0) (x2 : list a0) := fun y0 : type1402 a0 => (@List.Forall a0 (y0 x0) x2) /\ (x1 x2 y0).
Definition term63 (a0 : Type') (x0 : a0) (x1 : type1127 a0) (x2 : list a0) (x3 : type1402 a0) := (fun y0 : type1402 a0 => (@List.Forall a0 (y0 x0) x2) /\ (x1 x2 y0)) x3.
Definition term95 (a0 : Type') (x0 : type416 a0) (x1 : type1127 a0) := (x0 = (fun y0 : type1402 a0 => fun y1 : list a0 => x1 y1 y0)) -> exists y0 : type416 a0, (forall y1 : type1402 a0, (y0 y1 (@nil a0)) = True) /\ (forall y1 : a0, forall y2 : type1402 a0, forall y3 : list a0, (y0 y2 (@cons a0 y1 y3)) = ((@List.Forall a0 (y2 y1) y3) /\ (y0 y2 y3))).
Definition term33 (a0 : Type') (x0 : type416 a0) (x1 : type1402 a0) (x2 : a0) (x3 : list a0) := @eq Prop (x0 x1 (@cons a0 x2 x3)).
Definition term22 (a0 : Type') (x0 : type1127 a0) := fun y0 : type1402 a0 => (x0 (@nil a0) y0) = True.
Definition term14 (a0 : Type') (x0 : type1127 a0) (x1 : type1402 a0) := (fun y0 : list a0 => (fun y1 : list a0 => x0 y1 x1) y0) (@nil a0).
Definition term10 (a0 : Type') (x0 : type1127 a0) (x1 : type1402 a0) := @eq ((list a0) -> Prop) ((fun y0 : type1402 a0 => (fun y1 : type1402 a0 => fun y2 : list a0 => x0 y2 y1) y0) x1).
Definition term87 (a0 : Type') (x0 : type1127 a0) := ((x0 (@nil a0)) = (fun y0 : type1402 a0 => True)) /\ (forall y0 : a0, forall y1 : list a0, (x0 (@cons a0 y0 y1)) = ((fun y2 : a0 => fun y3 : list a0 => fun y4 : type421 a0 => fun y5 : type1402 a0 => (@List.Forall a0 (y5 y2) y3) /\ (y4 y5)) y0 y1 (x0 y1))).
Definition term64 (a0 : Type') (x0 : type1127 a0) := ((x0 (@nil a0)) = (fun y0 : type1402 a0 => True)) /\ (forall y0 : a0, forall y1 : list a0, (x0 (@cons a0 y0 y1)) = (fun y2 : type1402 a0 => (@List.Forall a0 (y2 y0) y1) /\ (x0 y1 y2))).
Definition term17 (a0 : Type') (x0 : type1127 a0) (x1 : type1402 a0) := @eq Prop ((fun y0 : list a0 => (fun y1 : list a0 => x0 y1 x1) y0) (@nil a0)).
Definition term11 (a0 : Type') (x0 : type1127 a0) (x1 : type1402 a0) := @eq ((list a0) -> Prop) ((fun y0 : type1402 a0 => fun y1 : list a0 => x0 y1 y0) x1).
Definition term46 (a0 : Type') (x0 : a0) (x1 : type1127 a0) := fun y0 : type1402 a0 => forall y1 : list a0, (x1 (@cons a0 x0 y1) y0) = ((@List.Forall a0 (y0 x0) y1) /\ (x1 y1 y0)).
Definition term45 (a0 : Type') (x0 : a0) (x1 : type416 a0) := fun y0 : type1402 a0 => forall y1 : list a0, (x1 y0 (@cons a0 x0 y1)) = ((@List.Forall a0 (y0 x0) y1) /\ (x1 y0 y1)).
Definition term108 (a0 : Type') (x0 : type416 a0) := (fun y0 : type416 a0 => (forall y1 : type1402 a0, (y0 y1 (@nil a0)) = True) /\ (forall y1 : a0, forall y2 : type1402 a0, forall y3 : list a0, (y0 y2 (@cons a0 y1 y3)) = ((@List.Forall a0 (y2 y1) y3) /\ (y0 y2 y3)))) x0.
Definition term28 (a0 : Type') (x0 : type1127 a0) (x1 : type1402 a0) (x2 : a0) (x3 : list a0) := (fun y0 : list a0 => x0 y0 x1) (@cons a0 x2 x3).
Definition term19 (a0 : Type') (x0 : type416 a0) (x1 : type1402 a0) := @eq Prop (x0 x1 (@nil a0)).
Definition term66 (a0 : Type') (a1 : Type') (x0 : a1) := forall y0 : type1394 a0 a1, exists y1 : type1142 a0 a1, ((y1 (@nil a0)) = x0) /\ (forall y2 : a0, forall y3 : list a0, (y1 (@cons a0 y2 y3)) = (y0 y2 y3 (y1 y3))).
Definition term98 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := (fun y0 : type1413 a0 a1 => (forall y1 : a0, exists y2 : a1, y0 y1 y2) = (exists y1 : a0 -> a1, forall y2 : a0, y0 y2 (y1 y2))) x0.
Definition term29 (a0 : Type') (x0 : type1127 a0) (x1 : type1402 a0) (x2 : a0) (x3 : list a0) := (fun y0 : list a0 => (fun y1 : list a0 => x0 y1 x1) y0) (@cons a0 x2 x3).
Definition term106 (a0 : Type') (x0 : type1669) := (fun y0 : type1669 => fun y1 : type416 a0 => (forall y2 : type1402 a0, (y1 y2 (@nil a0)) = True) /\ (forall y2 : a0, forall y3 : type1402 a0, forall y4 : list a0, (y1 y3 (@cons a0 y2 y4)) = ((@List.Forall a0 (y3 y2) y4) /\ (y1 y3 y4)))) x0.
Definition term34 (a0 : Type') (x0 : type1127 a0) (x1 : a0) (x2 : list a0) (x3 : type1402 a0) := @eq Prop (x0 (@cons a0 x1 x2) x3).
Definition term24 (a0 : Type') (x0 : type1127 a0) := forall y0 : type1402 a0, (x0 (@nil a0) y0) = True.
Definition term77 (a0 : Type') (x0 : a0) (x1 : type1127 a0) (x2 : list a0) := (fun y0 : a0 => fun y1 : list a0 => fun y2 : type421 a0 => fun y3 : type1402 a0 => (@List.Forall a0 (y3 y0) y1) /\ (y2 y3)) x0 x2 (x1 x2).
Definition term100 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := exists y0 : a0 -> a1, forall y1 : a0, x0 y1 (y0 y1).
Definition term69 (a0 : Type') (x0 : type421 a0) (x1 : type1383 a0) := exists y0 : type1127 a0, ((y0 (@nil a0)) = x0) /\ (forall y1 : a0, forall y2 : list a0, (y0 (@cons a0 y1 y2)) = (x1 y1 y2 (y0 y2))).
Definition term68 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : type1394 a0 a1) := exists y0 : type1142 a0 a1, ((y0 (@nil a0)) = x0) /\ (forall y1 : a0, forall y2 : list a0, (y0 (@cons a0 y1 y2)) = (x1 y1 y2 (y0 y2))).
Definition term103 (a0 : Type') := forall y0 : type1669, exists y1 : type416 a0, (fun y2 : type1669 => fun y3 : type416 a0 => (forall y4 : type1402 a0, (y3 y4 (@nil a0)) = True) /\ (forall y4 : a0, forall y5 : type1402 a0, forall y6 : list a0, (y3 y5 (@cons a0 y4 y6)) = ((@List.Forall a0 (y5 y4) y6) /\ (y3 y5 y6)))) y0 y1.
Definition term101 (a0 : Type') (x0 : type1241 a0) := forall y0 : type1669, exists y1 : type416 a0, x0 y0 y1.
Definition term85 (a0 : Type') (x0 : type1127 a0) := forall y0 : a0, forall y1 : list a0, (x0 (@cons a0 y0 y1)) = ((fun y2 : a0 => fun y3 : list a0 => fun y4 : type421 a0 => fun y5 : type1402 a0 => (@List.Forall a0 (y5 y2) y3) /\ (y4 y5)) y0 y1 (x0 y1)).
Definition term55 (a0 : Type') := fun y0 : type1402 a0 => True.
Definition term96 (a0 : Type') (x0 : type1127 a0) := ((fun y0 : type1402 a0 => fun y1 : list a0 => x0 y1 y0) = (fun y0 : type1402 a0 => fun y1 : list a0 => x0 y1 y0)) -> exists y0 : type416 a0, (forall y1 : type1402 a0, (y0 y1 (@nil a0)) = True) /\ (forall y1 : a0, forall y2 : type1402 a0, forall y3 : list a0, (y0 y2 (@cons a0 y1 y3)) = ((@List.Forall a0 (y2 y1) y3) /\ (y0 y2 y3))).
Definition term97 (a0 : Type') := forall y0 : type1669, exists y1 : type416 a0, (forall y2 : type1402 a0, (y1 y2 (@nil a0)) = True) /\ (forall y2 : a0, forall y3 : type1402 a0, forall y4 : list a0, (y1 y3 (@cons a0 y2 y4)) = ((@List.Forall a0 (y3 y2) y4) /\ (y1 y3 y4))).
Definition term94 (a0 : Type') := fun y0 : type416 a0 => (forall y1 : type1402 a0, (y0 y1 (@nil a0)) = True) /\ (forall y1 : a0, forall y2 : type1402 a0, forall y3 : list a0, (y0 y2 (@cons a0 y1 y3)) = ((@List.Forall a0 (y2 y1) y3) /\ (y0 y2 y3))).
Definition term4 (a0 : Type') (x0 : type1127 a0) := fun y0 : type1402 a0 => fun y1 : list a0 => x0 y1 y0.
Definition term79 (a0 : Type') (x0 : type1127 a0) (x1 : a0) (x2 : list a0) := @eq ((a0 -> a0 -> Prop) -> Prop) (x0 (@cons a0 x1 x2)).
Definition term30 (a0 : Type') (x0 : type1127 a0) (x1 : type1402 a0) (x2 : a0) (x3 : list a0) := @eq Prop ((fun y0 : list a0 => (fun y1 : list a0 => x0 y1 x1) y0) (@cons a0 x2 x3)).
Definition term111 (a0 : Type') := fun y0 : type1669 => exists y1 : type416 a0, (fun y2 : type1669 => fun y3 : type416 a0 => (forall y4 : type1402 a0, (y3 y4 (@nil a0)) = True) /\ (forall y4 : a0, forall y5 : type1402 a0, forall y6 : list a0, (y3 y5 (@cons a0 y4 y6)) = ((@List.Forall a0 (y5 y4) y6) /\ (y3 y5 y6)))) y0 y1.
