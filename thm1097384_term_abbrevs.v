Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term30 (a0 : Type') (a1 : Type') (x0 : type1129 a0 a1) (x1 : a0 -> a1) (x2 : a0) (x3 : list a0) := @eq (list a1) ((fun y0 : list a0 => (fun y1 : list a0 => x0 y1 x1) y0) (@cons a0 x2 x3)).
Definition term0 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := (fun y0 : a0 -> a1 => forall y1 : a0, ((fun y2 : a0 => y0 y2) y1) = (y0 y1)) x0.
Definition term123 (a0 : Type') (a1 : Type') := fun y0 : type1297 a0 a1 => forall y1 : type1674, (forall y2 : a0 -> a1, (y0 y1 y2 (@nil a0)) = (@nil a1)) /\ (forall y2 : a0 -> a1, forall y3 : a0, forall y4 : list a0, (y0 y1 y2 (@cons a0 y3 y4)) = (@cons a1 (y2 y3) (y0 y1 y2 y4))).
Definition term114 (a0 : Type') (a1 : Type') := @eq Prop (forall y0 : type1674, exists y1 : type540 a0 a1, (forall y2 : a0 -> a1, (y1 y2 (@nil a0)) = (@nil a1)) /\ (forall y2 : a0 -> a1, forall y3 : a0, forall y4 : list a0, (y1 y2 (@cons a0 y3 y4)) = (@cons a1 (y2 y3) (y1 y2 y4)))).
Definition term113 (a0 : Type') (a1 : Type') := @eq Prop (forall y0 : type1674, exists y1 : type540 a0 a1, (fun y2 : type1674 => fun y3 : type540 a0 a1 => (forall y4 : a0 -> a1, (y3 y4 (@nil a0)) = (@nil a1)) /\ (forall y4 : a0 -> a1, forall y5 : a0, forall y6 : list a0, (y3 y4 (@cons a0 y5 y6)) = (@cons a1 (y4 y5) (y3 y4 y6)))) y0 y1).
Definition term122 (a0 : Type') (a1 : Type') := fun y0 : type1297 a0 a1 => forall y1 : type1674, (fun y2 : type1674 => fun y3 : type540 a0 a1 => (forall y4 : a0 -> a1, (y3 y4 (@nil a0)) = (@nil a1)) /\ (forall y4 : a0 -> a1, forall y5 : a0, forall y6 : list a0, (y3 y4 (@cons a0 y5 y6)) = (@cons a1 (y4 y5) (y3 y4 y6)))) y1 (y0 y1).
Definition term87 (a0 : Type') (a1 : Type') (x0 : type1129 a0 a1) := ((x0 (@nil a0)) = (fun y0 : a0 -> a1 => @nil a1)) /\ (forall y0 : a0, forall y1 : list a0, (x0 (@cons a0 y0 y1)) = ((fun y2 : a0 => fun y3 : list a0 => fun y4 : type568 a0 a1 => fun y5 : a0 -> a1 => @cons a1 (y5 y2) (y4 y5)) y0 y1 (x0 y1))).
Definition term64 (a0 : Type') (a1 : Type') (x0 : type1129 a0 a1) := ((x0 (@nil a0)) = (fun y0 : a0 -> a1 => @nil a1)) /\ (forall y0 : a0, forall y1 : list a0, (x0 (@cons a0 y0 y1)) = (fun y2 : a0 -> a1 => @cons a1 (y2 y0) (x0 y1 y2))).
Definition term117 (a0 : Type') (a1 : Type') (x0 : type1297 a0 a1) (x1 : type1674) := (forall y0 : a0 -> a1, (x0 x1 y0 (@nil a0)) = (@nil a1)) /\ (forall y0 : a0 -> a1, forall y1 : a0, forall y2 : list a0, (x0 x1 y0 (@cons a0 y1 y2)) = (@cons a1 (y0 y1) (x0 x1 y0 y2))).
Definition term54 (a0 : Type') (a1 : Type') (x0 : type1129 a0 a1) := (forall y0 : a0 -> a1, (x0 (@nil a0) y0) = (@nil a1)) /\ (forall y0 : a0 -> a1, forall y1 : a0, forall y2 : list a0, (x0 (@cons a0 y1 y2) y0) = (@cons a1 (y0 y1) (x0 y2 y0))).
Definition term53 (a0 : Type') (a1 : Type') (x0 : type540 a0 a1) := (forall y0 : a0 -> a1, (x0 y0 (@nil a0)) = (@nil a1)) /\ (forall y0 : a0 -> a1, forall y1 : a0, forall y2 : list a0, (x0 y0 (@cons a0 y1 y2)) = (@cons a1 (y0 y1) (x0 y0 y2))).
Definition term39 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : type540 a0 a1) (x2 : a0 -> a1) (x3 : list a0) := @cons a1 (x2 x0) (x1 x2 x3).
Definition term65 (a0 : Type') (a1 : Type') (x0 : a1) := (fun y0 : a1 => forall y1 : type1394 a0 a1, exists y2 : type1142 a0 a1, ((y2 (@nil a0)) = y0) /\ (forall y3 : a0, forall y4 : list a0, (y2 (@cons a0 y3 y4)) = (y1 y3 y4 (y2 y4)))) x0.
Definition term8 (a0 : Type') (a1 : Type') (x0 : type1129 a0 a1) (x1 : a0 -> a1) := fun y0 : list a0 => x0 y0 x1.
Definition term60 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : type1129 a0 a1) (x2 : list a0) := (fun y0 : list a0 => (x1 (@cons a0 x0 y0)) = (fun y1 : a0 -> a1 => @cons a1 (y1 x0) (x1 y0 y1))) x2.
Definition term71 (a0 : Type') (a1 : Type') := fun y0 : a0 => fun y1 : list a0 => fun y2 : type568 a0 a1 => fun y3 : a0 -> a1 => @cons a1 (y3 y0) (y2 y3).
Definition term83 (a0 : Type') (a1 : Type') (x0 : type1129 a0 a1) := fun y0 : a0 => forall y1 : list a0, (x0 (@cons a0 y0 y1)) = ((fun y2 : a0 => fun y3 : list a0 => fun y4 : type568 a0 a1 => fun y5 : a0 -> a1 => @cons a1 (y5 y2) (y4 y5)) y0 y1 (x0 y1)).
Definition term46 (a0 : Type') (a1 : Type') (x0 : type1129 a0 a1) (x1 : a0 -> a1) := fun y0 : a0 => forall y1 : list a0, (x0 (@cons a0 y0 y1) x1) = (@cons a1 (x1 y0) (x0 y1 x1)).
Definition term45 (a0 : Type') (a1 : Type') (x0 : type540 a0 a1) (x1 : a0 -> a1) := fun y0 : a0 => forall y1 : list a0, (x0 x1 (@cons a0 y0 y1)) = (@cons a1 (x1 y0) (x0 x1 y1)).
Definition term75 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : list a0) := (fun y0 : list a0 => fun y1 : type568 a0 a1 => fun y2 : a0 -> a1 => @cons a1 (y2 x0) (y1 y2)) x1.
Definition term50 (a0 : Type') (a1 : Type') (x0 : type1129 a0 a1) := fun y0 : a0 -> a1 => forall y1 : a0, forall y2 : list a0, (x0 (@cons a0 y1 y2) y0) = (@cons a1 (y0 y1) (x0 y2 y0)).
Definition term49 (a0 : Type') (a1 : Type') (x0 : type540 a0 a1) := fun y0 : a0 -> a1 => forall y1 : a0, forall y2 : list a0, (x0 y0 (@cons a0 y1 y2)) = (@cons a1 (y0 y1) (x0 y0 y2)).
Definition term107 (a0 : Type') (a1 : Type') (x0 : type1674) (x1 : type540 a0 a1) := (fun y0 : type1674 => fun y1 : type540 a0 a1 => (forall y2 : a0 -> a1, (y1 y2 (@nil a0)) = (@nil a1)) /\ (forall y2 : a0 -> a1, forall y3 : a0, forall y4 : list a0, (y1 y2 (@cons a0 y3 y4)) = (@cons a1 (y2 y3) (y1 y2 y4)))) x0 x1.
Definition term105 (a0 : Type') (a1 : Type') := fun y0 : type1674 => fun y1 : type540 a0 a1 => (forall y2 : a0 -> a1, (y1 y2 (@nil a0)) = (@nil a1)) /\ (forall y2 : a0 -> a1, forall y3 : a0, forall y4 : list a0, (y1 y2 (@cons a0 y3 y4)) = (@cons a1 (y2 y3) (y1 y2 y4))).
Definition term78 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : type1129 a0 a1) (x2 : list a0) := (fun y0 : type568 a0 a1 => fun y1 : a0 -> a1 => @cons a1 (y1 x0) (y0 y1)) (x1 x2).
Definition term1 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := forall y0 : a0, ((fun y1 : a0 => x0 y1) y0) = (x0 y0).
Definition term67 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : type1394 a0 a1) := (fun y0 : type1394 a0 a1 => exists y1 : type1142 a0 a1, ((y1 (@nil a0)) = x0) /\ (forall y2 : a0, forall y3 : list a0, (y1 (@cons a0 y2 y3)) = (y0 y2 y3 (y1 y3)))) x1.
Definition term21 (a0 : Type') (a1 : Type') (x0 : type540 a0 a1) := fun y0 : a0 -> a1 => (x0 y0 (@nil a0)) = (@nil a1).
Definition term12 (a0 : Type') (a1 : Type') (x0 : type1129 a0 a1) (x1 : a0 -> a1) := (fun y0 : list a0 => x0 y0 x1) (@nil a0).
Definition term92 (a0 : Type') (a1 : Type') := fun y0 : type1129 a0 a1 => (forall y1 : a0 -> a1, (y0 (@nil a0) y1) = (@nil a1)) /\ (forall y1 : a0 -> a1, forall y2 : a0, forall y3 : list a0, (y0 (@cons a0 y2 y3) y1) = (@cons a1 (y1 y2) (y0 y3 y1))).
Definition term35 (a0 : Type') (a1 : Type') (x0 : type1129 a0 a1) (x1 : a0 -> a1) (x2 : list a0) := (fun y0 : list a0 => (fun y1 : list a0 => x0 y1 x1) y0) x2.
Definition term6 (a0 : Type') (a1 : Type') (x0 : type540 a0 a1) (x1 : a0 -> a1) := (fun y0 : a0 -> a1 => x0 y0) x1.
Definition term59 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : type1129 a0 a1) := forall y0 : list a0, (x1 (@cons a0 x0 y0)) = (fun y1 : a0 -> a1 => @cons a1 (y1 x0) (x1 y0 y1)).
Definition term109 (a0 : Type') (a1 : Type') (x0 : type1674) := fun y0 : type540 a0 a1 => (fun y1 : type1674 => fun y2 : type540 a0 a1 => (forall y3 : a0 -> a1, (y2 y3 (@nil a0)) = (@nil a1)) /\ (forall y3 : a0 -> a1, forall y4 : a0, forall y5 : list a0, (y2 y3 (@cons a0 y4 y5)) = (@cons a1 (y3 y4) (y2 y3 y5)))) x0 y0.
Definition term128 (a0 : Type') (a1 : Type') := (fun y0 : type1297 a0 a1 => forall y1 : type1674, (forall y2 : a0 -> a1, (y0 y1 y2 (@nil a0)) = (@nil a1)) /\ (forall y2 : a0 -> a1, forall y3 : a0, forall y4 : list a0, (y0 y1 y2 (@cons a0 y3 y4)) = (@cons a1 (y2 y3) (y0 y1 y2 y4)))) (@ε ((prod nat (prod nat nat)) -> (a0 -> a1) -> (list a0) -> list a1) (fun y0 : type1297 a0 a1 => forall y1 : type1674, (forall y2 : a0 -> a1, (y0 y1 y2 (@nil a0)) = (@nil a1)) /\ (forall y2 : a0 -> a1, forall y3 : a0, forall y4 : list a0, (y0 y1 y2 (@cons a0 y3 y4)) = (@cons a1 (y2 y3) (y0 y1 y2 y4))))).
Definition term121 (a0 : Type') (a1 : Type') (x0 : type1297 a0 a1) := forall y0 : type1674, (forall y1 : a0 -> a1, (x0 y0 y1 (@nil a0)) = (@nil a1)) /\ (forall y1 : a0 -> a1, forall y2 : a0, forall y3 : list a0, (x0 y0 y1 (@cons a0 y2 y3)) = (@cons a1 (y1 y2) (x0 y0 y1 y3))).
Definition term93 (a0 : Type') (a1 : Type') := exists y0 : type540 a0 a1, (forall y1 : a0 -> a1, (y0 y1 (@nil a0)) = (@nil a1)) /\ (forall y1 : a0 -> a1, forall y2 : a0, forall y3 : list a0, (y0 y1 (@cons a0 y2 y3)) = (@cons a1 (y1 y2) (y0 y1 y3))).
Definition term91 (a0 : Type') (a1 : Type') := exists y0 : type1129 a0 a1, (forall y1 : a0 -> a1, (y0 (@nil a0) y1) = (@nil a1)) /\ (forall y1 : a0 -> a1, forall y2 : a0, forall y3 : list a0, (y0 (@cons a0 y2 y3) y1) = (@cons a1 (y1 y2) (y0 y3 y1))).
Definition term34 (a0 : Type') (a1 : Type') (x0 : type1129 a0 a1) (x1 : a0) (x2 : list a0) (x3 : a0 -> a1) := @eq (list a1) (x0 (@cons a0 x1 x2) x3).
Definition term61 (a0 : Type') (a1 : Type') (x0 : type1129 a0 a1) (x1 : a0) (x2 : list a0) := x0 (@cons a0 x1 x2).
Definition term99 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := forall y0 : a0, exists y1 : a1, x0 y0 y1.
Definition term5 (a0 : Type') (a1 : Type') (x0 : type1129 a0 a1) (x1 : a0 -> a1) := (fun y0 : a0 -> a1 => fun y1 : list a0 => x0 y1 y0) x1.
Definition term124 (a0 : Type') (a1 : Type') := exists y0 : type1297 a0 a1, forall y1 : type1674, (forall y2 : a0 -> a1, (y0 y1 y2 (@nil a0)) = (@nil a1)) /\ (forall y2 : a0 -> a1, forall y3 : a0, forall y4 : list a0, (y0 y1 y2 (@cons a0 y3 y4)) = (@cons a1 (y2 y3) (y0 y1 y2 y4))).
Definition term104 (a0 : Type') (a1 : Type') := exists y0 : type1297 a0 a1, forall y1 : type1674, (fun y2 : type1674 => fun y3 : type540 a0 a1 => (forall y4 : a0 -> a1, (y3 y4 (@nil a0)) = (@nil a1)) /\ (forall y4 : a0 -> a1, forall y5 : a0, forall y6 : list a0, (y3 y4 (@cons a0 y5 y6)) = (@cons a1 (y4 y5) (y3 y4 y6)))) y1 (y0 y1).
Definition term102 (a0 : Type') (a1 : Type') (x0 : type1293 a0 a1) := exists y0 : type1297 a0 a1, forall y1 : type1674, x0 y1 (y0 y1).
Definition term120 (a0 : Type') (a1 : Type') (x0 : type1297 a0 a1) := forall y0 : type1674, (fun y1 : type1674 => fun y2 : type540 a0 a1 => (forall y3 : a0 -> a1, (y2 y3 (@nil a0)) = (@nil a1)) /\ (forall y3 : a0 -> a1, forall y4 : a0, forall y5 : list a0, (y2 y3 (@cons a0 y4 y5)) = (@cons a1 (y3 y4) (y2 y3 y5)))) y0 (x0 y0).
Definition term74 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : list a0) := (fun y0 : a0 => fun y1 : list a0 => fun y2 : type568 a0 a1 => fun y3 : a0 -> a1 => @cons a1 (y3 y0) (y2 y3)) x0 x1.
Definition term116 (a0 : Type') (a1 : Type') (x0 : type1297 a0 a1) (x1 : type1674) := (fun y0 : type540 a0 a1 => (forall y1 : a0 -> a1, (y0 y1 (@nil a0)) = (@nil a1)) /\ (forall y1 : a0 -> a1, forall y2 : a0, forall y3 : list a0, (y0 y1 (@cons a0 y2 y3)) = (@cons a1 (y1 y2) (y0 y1 y3)))) (x0 x1).
Definition term73 (a0 : Type') (a1 : Type') (x0 : a0) := fun y0 : list a0 => fun y1 : type568 a0 a1 => fun y2 : a0 -> a1 => @cons a1 (y2 x0) (y1 y2).
Definition term126 (a0 : Type') (a1 : Type') := fun y0 : type364 a0 a1 => y0 (@ε ((prod nat (prod nat nat)) -> (a0 -> a1) -> (list a0) -> list a1) y0).
Definition term26 (a0 : Type') (a1 : Type') (x0 : type1129 a0 a1) := and (forall y0 : a0 -> a1, (x0 (@nil a0) y0) = (@nil a1)).
Definition term25 (a0 : Type') (a1 : Type') (x0 : type540 a0 a1) := and (forall y0 : a0 -> a1, (x0 y0 (@nil a0)) = (@nil a1)).
Definition term33 (a0 : Type') (a1 : Type') (x0 : type540 a0 a1) (x1 : a0 -> a1) (x2 : a0) (x3 : list a0) := @eq (list a1) (x0 x1 (@cons a0 x2 x3)).
Definition term2 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => ((fun y1 : a0 => x0 y1) y0) = (x0 y0)) x1.
Definition term24 (a0 : Type') (a1 : Type') (x0 : type1129 a0 a1) := forall y0 : a0 -> a1, (x0 (@nil a0) y0) = (@nil a1).
Definition term82 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : type1129 a0 a1) := forall y0 : list a0, (x1 (@cons a0 x0 y0)) = ((fun y1 : a0 => fun y2 : list a0 => fun y3 : type568 a0 a1 => fun y4 : a0 -> a1 => @cons a1 (y4 y1) (y3 y4)) x0 y0 (x1 y0)).
Definition term38 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := @cons a1 (x0 x1).
Definition term16 (a0 : Type') (a1 : Type') (x0 : type1129 a0 a1) (x1 : a0 -> a1) := fun y0 : list a0 => (fun y1 : list a0 => x0 y1 x1) y0.
Definition term112 (a0 : Type') (a1 : Type') := fun y0 : type1674 => exists y1 : type540 a0 a1, (forall y2 : a0 -> a1, (y1 y2 (@nil a0)) = (@nil a1)) /\ (forall y2 : a0 -> a1, forall y3 : a0, forall y4 : list a0, (y1 y2 (@cons a0 y3 y4)) = (@cons a1 (y2 y3) (y1 y2 y4))).
Definition term80 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : type1129 a0 a1) := fun y0 : list a0 => (x1 (@cons a0 x0 y0)) = ((fun y1 : a0 => fun y2 : list a0 => fun y3 : type568 a0 a1 => fun y4 : a0 -> a1 => @cons a1 (y4 y1) (y3 y4)) x0 y0 (x1 y0)).
Definition term90 (a0 : Type') (a1 : Type') := exists y0 : type1129 a0 a1, ((y0 (@nil a0)) = (fun y1 : a0 -> a1 => @nil a1)) /\ (forall y1 : a0, forall y2 : list a0, (y0 (@cons a0 y1 y2)) = (fun y3 : a0 -> a1 => @cons a1 (y3 y1) (y0 y2 y3))).
Definition term70 (a0 : Type') (a1 : Type') := exists y0 : type1129 a0 a1, ((y0 (@nil a0)) = (fun y1 : a0 -> a1 => @nil a1)) /\ (forall y1 : a0, forall y2 : list a0, (y0 (@cons a0 y1 y2)) = ((fun y3 : a0 => fun y4 : list a0 => fun y5 : type568 a0 a1 => fun y6 : a0 -> a1 => @cons a1 (y6 y3) (y5 y6)) y1 y2 (y0 y2))).
Definition term125 (a0 : Type') := fun y0 : a0 -> Prop => y0 (@ε a0 y0).
Definition term15 (a0 : Type') (a1 : Type') (x0 : type1129 a0 a1) (x1 : a0 -> a1) (x2 : list a0) := (fun y0 : list a0 => x0 y0 x1) x2.
Definition term115 (a0 : Type') (a1 : Type') (x0 : type1297 a0 a1) (x1 : type1674) := (fun y0 : type1674 => fun y1 : type540 a0 a1 => (forall y2 : a0 -> a1, (y1 y2 (@nil a0)) = (@nil a1)) /\ (forall y2 : a0 -> a1, forall y3 : a0, forall y4 : list a0, (y1 y2 (@cons a0 y3 y4)) = (@cons a1 (y2 y3) (y1 y2 y4)))) x1 (x0 x1).
Definition term3 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term22 (a0 : Type') (a1 : Type') (x0 : type1129 a0 a1) := fun y0 : a0 -> a1 => (x0 (@nil a0) y0) = (@nil a1).
Definition term81 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : type1129 a0 a1) := fun y0 : list a0 => (x1 (@cons a0 x0 y0)) = (fun y1 : a0 -> a1 => @cons a1 (y1 x0) (x1 y0 y1)).
Definition term127 (a0 : Type') (a1 : Type') := (fun y0 : type364 a0 a1 => y0 (@ε ((prod nat (prod nat nat)) -> (a0 -> a1) -> (list a0) -> list a1) y0)) (fun y0 : type1297 a0 a1 => forall y1 : type1674, (forall y2 : a0 -> a1, (y0 y1 y2 (@nil a0)) = (@nil a1)) /\ (forall y2 : a0 -> a1, forall y3 : a0, forall y4 : list a0, (y0 y1 y2 (@cons a0 y3 y4)) = (@cons a1 (y2 y3) (y0 y1 y2 y4)))).
Definition term13 (a0 : Type') (a1 : Type') (x0 : type1139 a0 a1) (x1 : list a0) := (fun y0 : list a0 => x0 y0) x1.
Definition term119 (a0 : Type') (a1 : Type') (x0 : type1297 a0 a1) := fun y0 : type1674 => (forall y1 : a0 -> a1, (x0 y0 y1 (@nil a0)) = (@nil a1)) /\ (forall y1 : a0 -> a1, forall y2 : a0, forall y3 : list a0, (x0 y0 y1 (@cons a0 y2 y3)) = (@cons a1 (y1 y2) (x0 y0 y1 y3))).
Definition term20 (a0 : Type') (a1 : Type') (x0 : type1129 a0 a1) (x1 : a0 -> a1) := @eq (list a1) (x0 (@nil a0) x1).
Definition term44 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : type1129 a0 a1) (x2 : a0 -> a1) := forall y0 : list a0, (x1 (@cons a0 x0 y0) x2) = (@cons a1 (x2 x0) (x1 y0 x2)).
Definition term19 (a0 : Type') (a1 : Type') (x0 : type540 a0 a1) (x1 : a0 -> a1) := @eq (list a1) (x0 x1 (@nil a0)).
Definition term62 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : type1129 a0 a1) (x2 : list a0) := fun y0 : a0 -> a1 => @cons a1 (y0 x0) (x1 x2 y0).
Definition term110 (a0 : Type') (a1 : Type') (x0 : type1674) := exists y0 : type540 a0 a1, (fun y1 : type1674 => fun y2 : type540 a0 a1 => (forall y3 : a0 -> a1, (y2 y3 (@nil a0)) = (@nil a1)) /\ (forall y3 : a0 -> a1, forall y4 : a0, forall y5 : list a0, (y2 y3 (@cons a0 y4 y5)) = (@cons a1 (y3 y4) (y2 y3 y5)))) x0 y0.
Definition term18 (a0 : Type') (a1 : Type') (x0 : type1129 a0 a1) (x1 : a0 -> a1) := @eq (list a1) ((fun y0 : list a0 => x0 y0 x1) (@nil a0)).
Definition term40 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : type1129 a0 a1) (x2 : list a0) (x3 : a0 -> a1) := @cons a1 (x3 x0) (x1 x2 x3).
Definition term84 (a0 : Type') (a1 : Type') (x0 : type1129 a0 a1) := fun y0 : a0 => forall y1 : list a0, (x0 (@cons a0 y0 y1)) = (fun y2 : a0 -> a1 => @cons a1 (y2 y0) (x0 y1 y2)).
Definition term37 (a0 : Type') (a1 : Type') (x0 : type1129 a0 a1) (x1 : a0 -> a1) (x2 : list a0) := @eq (list a1) ((fun y0 : list a0 => x0 y0 x1) x2).
Definition term55 (a0 : Type') (a1 : Type') := fun y0 : a0 -> a1 => @nil a1.
Definition term89 (a0 : Type') (a1 : Type') := fun y0 : type1129 a0 a1 => ((y0 (@nil a0)) = (fun y1 : a0 -> a1 => @nil a1)) /\ (forall y1 : a0, forall y2 : list a0, (y0 (@cons a0 y1 y2)) = (fun y3 : a0 -> a1 => @cons a1 (y3 y1) (y0 y2 y3))).
Definition term88 (a0 : Type') (a1 : Type') := fun y0 : type1129 a0 a1 => ((y0 (@nil a0)) = (fun y1 : a0 -> a1 => @nil a1)) /\ (forall y1 : a0, forall y2 : list a0, (y0 (@cons a0 y1 y2)) = ((fun y3 : a0 => fun y4 : list a0 => fun y5 : type568 a0 a1 => fun y6 : a0 -> a1 => @cons a1 (y6 y3) (y5 y6)) y1 y2 (y0 y2))).
Definition term58 (a0 : Type') (a1 : Type') (x0 : type1129 a0 a1) (x1 : a0) := (fun y0 : a0 => forall y1 : list a0, (x0 (@cons a0 y0 y1)) = (fun y2 : a0 -> a1 => @cons a1 (y2 y0) (x0 y1 y2))) x1.
Definition term23 (a0 : Type') (a1 : Type') (x0 : type540 a0 a1) := forall y0 : a0 -> a1, (x0 y0 (@nil a0)) = (@nil a1).
Definition term57 (a0 : Type') (a1 : Type') (x0 : type1129 a0 a1) := forall y0 : a0, forall y1 : list a0, (x0 (@cons a0 y0 y1)) = (fun y2 : a0 -> a1 => @cons a1 (y2 y0) (x0 y1 y2)).
Definition term56 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := (fun y0 : a0 -> a1 => @nil a1) x0.
Definition term118 (a0 : Type') (a1 : Type') (x0 : type1297 a0 a1) := fun y0 : type1674 => (fun y1 : type1674 => fun y2 : type540 a0 a1 => (forall y3 : a0 -> a1, (y2 y3 (@nil a0)) = (@nil a1)) /\ (forall y3 : a0 -> a1, forall y4 : a0, forall y5 : list a0, (y2 y3 (@cons a0 y4 y5)) = (@cons a1 (y3 y4) (y2 y3 y5)))) y0 (x0 y0).
Definition term76 (a0 : Type') (a1 : Type') (x0 : a0) := fun y0 : type568 a0 a1 => fun y1 : a0 -> a1 => @cons a1 (y1 x0) (y0 y1).
Definition term86 (a0 : Type') (a1 : Type') (x0 : type1129 a0 a1) := and ((x0 (@nil a0)) = (fun y0 : a0 -> a1 => @nil a1)).
Definition term27 (a0 : Type') (a1 : Type') (x0 : type540 a0 a1) (x1 : a0 -> a1) (x2 : a0) (x3 : list a0) := x0 x1 (@cons a0 x2 x3).
Definition term43 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : type540 a0 a1) (x2 : a0 -> a1) := forall y0 : list a0, (x1 x2 (@cons a0 x0 y0)) = (@cons a1 (x2 x0) (x1 x2 y0)).
Definition term72 (a0 : Type') (a1 : Type') (x0 : a0) := (fun y0 : a0 => fun y1 : list a0 => fun y2 : type568 a0 a1 => fun y3 : a0 -> a1 => @cons a1 (y3 y0) (y2 y3)) x0.
Definition term32 (a0 : Type') (a1 : Type') (x0 : type1129 a0 a1) (x1 : a0) (x2 : list a0) (x3 : a0 -> a1) := x0 (@cons a0 x1 x2) x3.
Definition term95 (a0 : Type') (a1 : Type') (x0 : type540 a0 a1) (x1 : type1129 a0 a1) := (x0 = (fun y0 : a0 -> a1 => fun y1 : list a0 => x1 y1 y0)) -> exists y0 : type540 a0 a1, (forall y1 : a0 -> a1, (y0 y1 (@nil a0)) = (@nil a1)) /\ (forall y1 : a0 -> a1, forall y2 : a0, forall y3 : list a0, (y0 y1 (@cons a0 y2 y3)) = (@cons a1 (y1 y2) (y0 y1 y3))).
Definition term42 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : type1129 a0 a1) (x2 : a0 -> a1) := fun y0 : list a0 => (x1 (@cons a0 x0 y0) x2) = (@cons a1 (x2 x0) (x1 y0 x2)).
Definition term36 (a0 : Type') (a1 : Type') (x0 : type1129 a0 a1) (x1 : a0 -> a1) (x2 : list a0) := @eq (list a1) ((fun y0 : list a0 => (fun y1 : list a0 => x0 y1 x1) y0) x2).
Definition term14 (a0 : Type') (a1 : Type') (x0 : type1129 a0 a1) (x1 : a0 -> a1) := (fun y0 : list a0 => (fun y1 : list a0 => x0 y1 x1) y0) (@nil a0).
Definition term10 (a0 : Type') (a1 : Type') (x0 : type1129 a0 a1) (x1 : a0 -> a1) := @eq ((list a0) -> list a1) ((fun y0 : a0 -> a1 => (fun y1 : a0 -> a1 => fun y2 : list a0 => x0 y2 y1) y0) x1).
Definition term31 (a0 : Type') (a1 : Type') (x0 : type1129 a0 a1) (x1 : a0 -> a1) (x2 : a0) (x3 : list a0) := @eq (list a1) ((fun y0 : list a0 => x0 y0 x1) (@cons a0 x2 x3)).
Definition term63 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : type1129 a0 a1) (x2 : list a0) (x3 : a0 -> a1) := (fun y0 : a0 -> a1 => @cons a1 (y0 x0) (x1 x2 y0)) x3.
Definition term11 (a0 : Type') (a1 : Type') (x0 : type1129 a0 a1) (x1 : a0 -> a1) := @eq ((list a0) -> list a1) ((fun y0 : a0 -> a1 => fun y1 : list a0 => x0 y1 y0) x1).
Definition term108 (a0 : Type') (a1 : Type') (x0 : type540 a0 a1) := (fun y0 : type540 a0 a1 => (forall y1 : a0 -> a1, (y0 y1 (@nil a0)) = (@nil a1)) /\ (forall y1 : a0 -> a1, forall y2 : a0, forall y3 : list a0, (y0 y1 (@cons a0 y2 y3)) = (@cons a1 (y1 y2) (y0 y1 y3)))) x0.
Definition term4 (a0 : Type') (a1 : Type') (x0 : type1129 a0 a1) := fun y0 : a0 -> a1 => fun y1 : list a0 => x0 y1 y0.
Definition term28 (a0 : Type') (a1 : Type') (x0 : type1129 a0 a1) (x1 : a0 -> a1) (x2 : a0) (x3 : list a0) := (fun y0 : list a0 => x0 y0 x1) (@cons a0 x2 x3).
Definition term41 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : type540 a0 a1) (x2 : a0 -> a1) := fun y0 : list a0 => (x1 x2 (@cons a0 x0 y0)) = (@cons a1 (x2 x0) (x1 x2 y0)).
Definition term52 (a0 : Type') (a1 : Type') (x0 : type1129 a0 a1) := forall y0 : a0 -> a1, forall y1 : a0, forall y2 : list a0, (x0 (@cons a0 y1 y2) y0) = (@cons a1 (y0 y1) (x0 y2 y0)).
Definition term51 (a0 : Type') (a1 : Type') (x0 : type540 a0 a1) := forall y0 : a0 -> a1, forall y1 : a0, forall y2 : list a0, (x0 y0 (@cons a0 y1 y2)) = (@cons a1 (y0 y1) (x0 y0 y2)).
Definition term66 (a0 : Type') (a1 : Type') (x0 : a1) := forall y0 : type1394 a0 a1, exists y1 : type1142 a0 a1, ((y1 (@nil a0)) = x0) /\ (forall y2 : a0, forall y3 : list a0, (y1 (@cons a0 y2 y3)) = (y0 y2 y3 (y1 y3))).
Definition term98 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := (fun y0 : type1413 a0 a1 => (forall y1 : a0, exists y2 : a1, y0 y1 y2) = (exists y1 : a0 -> a1, forall y2 : a0, y0 y2 (y1 y2))) x0.
Definition term17 (a0 : Type') (a1 : Type') (x0 : type1129 a0 a1) (x1 : a0 -> a1) := @eq (list a1) ((fun y0 : list a0 => (fun y1 : list a0 => x0 y1 x1) y0) (@nil a0)).
Definition term29 (a0 : Type') (a1 : Type') (x0 : type1129 a0 a1) (x1 : a0 -> a1) (x2 : a0) (x3 : list a0) := (fun y0 : list a0 => (fun y1 : list a0 => x0 y1 x1) y0) (@cons a0 x2 x3).
Definition term106 (a0 : Type') (a1 : Type') (x0 : type1674) := (fun y0 : type1674 => fun y1 : type540 a0 a1 => (forall y2 : a0 -> a1, (y1 y2 (@nil a0)) = (@nil a1)) /\ (forall y2 : a0 -> a1, forall y3 : a0, forall y4 : list a0, (y1 y2 (@cons a0 y3 y4)) = (@cons a1 (y2 y3) (y1 y2 y4)))) x0.
Definition term77 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : type1129 a0 a1) (x2 : list a0) := (fun y0 : a0 => fun y1 : list a0 => fun y2 : type568 a0 a1 => fun y3 : a0 -> a1 => @cons a1 (y3 y0) (y2 y3)) x0 x2 (x1 x2).
Definition term100 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := exists y0 : a0 -> a1, forall y1 : a0, x0 y1 (y0 y1).
Definition term69 (a0 : Type') (a1 : Type') (x0 : type568 a0 a1) (x1 : type1385 a0 a1) := exists y0 : type1129 a0 a1, ((y0 (@nil a0)) = x0) /\ (forall y1 : a0, forall y2 : list a0, (y0 (@cons a0 y1 y2)) = (x1 y1 y2 (y0 y2))).
Definition term68 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : type1394 a0 a1) := exists y0 : type1142 a0 a1, ((y0 (@nil a0)) = x0) /\ (forall y1 : a0, forall y2 : list a0, (y0 (@cons a0 y1 y2)) = (x1 y1 y2 (y0 y2))).
Definition term103 (a0 : Type') (a1 : Type') := forall y0 : type1674, exists y1 : type540 a0 a1, (fun y2 : type1674 => fun y3 : type540 a0 a1 => (forall y4 : a0 -> a1, (y3 y4 (@nil a0)) = (@nil a1)) /\ (forall y4 : a0 -> a1, forall y5 : a0, forall y6 : list a0, (y3 y4 (@cons a0 y5 y6)) = (@cons a1 (y4 y5) (y3 y4 y6)))) y0 y1.
Definition term101 (a0 : Type') (a1 : Type') (x0 : type1293 a0 a1) := forall y0 : type1674, exists y1 : type540 a0 a1, x0 y0 y1.
Definition term85 (a0 : Type') (a1 : Type') (x0 : type1129 a0 a1) := forall y0 : a0, forall y1 : list a0, (x0 (@cons a0 y0 y1)) = ((fun y2 : a0 => fun y3 : list a0 => fun y4 : type568 a0 a1 => fun y5 : a0 -> a1 => @cons a1 (y5 y2) (y4 y5)) y0 y1 (x0 y1)).
Definition term48 (a0 : Type') (a1 : Type') (x0 : type1129 a0 a1) (x1 : a0 -> a1) := forall y0 : a0, forall y1 : list a0, (x0 (@cons a0 y0 y1) x1) = (@cons a1 (x1 y0) (x0 y1 x1)).
Definition term47 (a0 : Type') (a1 : Type') (x0 : type540 a0 a1) (x1 : a0 -> a1) := forall y0 : a0, forall y1 : list a0, (x0 x1 (@cons a0 y0 y1)) = (@cons a1 (x1 y0) (x0 x1 y1)).
Definition term7 (a0 : Type') (a1 : Type') (x0 : type1129 a0 a1) (x1 : a0 -> a1) := (fun y0 : a0 -> a1 => (fun y1 : a0 -> a1 => fun y2 : list a0 => x0 y2 y1) y0) x1.
Definition term9 (a0 : Type') (a1 : Type') (x0 : type1129 a0 a1) := fun y0 : a0 -> a1 => (fun y1 : a0 -> a1 => fun y2 : list a0 => x0 y2 y1) y0.
Definition term96 (a0 : Type') (a1 : Type') (x0 : type1129 a0 a1) := ((fun y0 : a0 -> a1 => fun y1 : list a0 => x0 y1 y0) = (fun y0 : a0 -> a1 => fun y1 : list a0 => x0 y1 y0)) -> exists y0 : type540 a0 a1, (forall y1 : a0 -> a1, (y0 y1 (@nil a0)) = (@nil a1)) /\ (forall y1 : a0 -> a1, forall y2 : a0, forall y3 : list a0, (y0 y1 (@cons a0 y2 y3)) = (@cons a1 (y1 y2) (y0 y1 y3))).
Definition term97 (a0 : Type') (a1 : Type') := forall y0 : type1674, exists y1 : type540 a0 a1, (forall y2 : a0 -> a1, (y1 y2 (@nil a0)) = (@nil a1)) /\ (forall y2 : a0 -> a1, forall y3 : a0, forall y4 : list a0, (y1 y2 (@cons a0 y3 y4)) = (@cons a1 (y2 y3) (y1 y2 y4))).
Definition term94 (a0 : Type') (a1 : Type') := fun y0 : type540 a0 a1 => (forall y1 : a0 -> a1, (y0 y1 (@nil a0)) = (@nil a1)) /\ (forall y1 : a0 -> a1, forall y2 : a0, forall y3 : list a0, (y0 y1 (@cons a0 y2 y3)) = (@cons a1 (y1 y2) (y0 y1 y3))).
Definition term79 (a0 : Type') (a1 : Type') (x0 : type1129 a0 a1) (x1 : a0) (x2 : list a0) := @eq ((a0 -> a1) -> list a1) (x0 (@cons a0 x1 x2)).
Definition term111 (a0 : Type') (a1 : Type') := fun y0 : type1674 => exists y1 : type540 a0 a1, (fun y2 : type1674 => fun y3 : type540 a0 a1 => (forall y4 : a0 -> a1, (y3 y4 (@nil a0)) = (@nil a1)) /\ (forall y4 : a0 -> a1, forall y5 : a0, forall y6 : list a0, (y3 y4 (@cons a0 y5 y6)) = (@cons a1 (y4 y5) (y3 y4 y6)))) y0 y1.
