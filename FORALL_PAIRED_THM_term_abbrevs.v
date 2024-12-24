Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term50 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := fun y0 : a1 => fun y1 : a0 => x0 y0 y1.
Definition term29 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) := (fun y0 : prod a1 a0 => True) x0.
Definition term36 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) := fun y0 : a0 => (fun y1 : prod a1 a0 => (@GABS ((prod a1 a0) -> Prop) (fun y2 : type1223 a0 a1 => forall y3 : a1, forall y4 : a0, @GEQ Prop (y2 (@pair a1 a0 y3 y4)) (x0 y3 y4)) y1) = ((fun y2 : prod a1 a0 => True) y1)) (@pair a1 a0 x1 y0).
Definition term11 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := (fun y0 : type1223 a0 a1 => y0 = (fun y1 : prod a1 a0 => True)) (@GABS ((prod a1 a0) -> Prop) (fun y0 : type1223 a0 a1 => forall y1 : a1, forall y2 : a0, @GEQ Prop (y0 (@pair a1 a0 y1 y2)) (x0 y1 y2))).
Definition term26 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := fun y0 : prod a1 a0 => (@GABS ((prod a1 a0) -> Prop) (fun y1 : type1223 a0 a1 => forall y2 : a1, forall y3 : a0, @GEQ Prop (y1 (@pair a1 a0 y2 y3)) (x0 y2 y3)) y0) = ((fun y1 : prod a1 a0 => True) y0).
Definition term67 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := fun y0 : prod a1 a0 => x0 (@ε ((prod a1 a0) -> a1) (fun y1 : type1222 a0 a1 => forall y2 : a1, forall y3 : a0, (y1 (@pair a1 a0 y2 y3)) = y2) y0) (@ε ((prod a1 a0) -> a0) (fun y1 : type1221 a0 a1 => forall y2 : a1, forall y3 : a0, (y1 (@pair a1 a0 y2 y3)) = y3) y0).
Definition term23 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := forall y0 : prod a1 a0, (@GABS ((prod a1 a0) -> Prop) (fun y1 : type1223 a0 a1 => forall y2 : a1, forall y3 : a0, @GEQ Prop (y1 (@pair a1 a0 y2 y3)) (x0 y2 y3)) y0) = ((fun y1 : prod a1 a0 => True) y0).
Definition term1 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := forall y0 : prod a1 a0, x0 y0.
Definition term20 (a0 : Type') (a1 : Type') := fun y0 : type1223 a0 a1 => (fun y1 : type1223 a0 a1 => y1 = (fun y2 : prod a1 a0 => True)) y0.
Definition term41 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := fun y0 : a1 => forall y1 : a0, (@GABS ((prod a1 a0) -> Prop) (fun y2 : type1223 a0 a1 => forall y3 : a1, forall y4 : a0, @GEQ Prop (y2 (@pair a1 a0 y3 y4)) (x0 y3 y4)) (@pair a1 a0 y0 y1)) = ((fun y2 : prod a1 a0 => True) (@pair a1 a0 y0 y1)).
Definition term9 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := @GABS ((prod a1 a0) -> Prop) (fun y0 : type1223 a0 a1 => forall y1 : a1, forall y2 : a0, @GEQ Prop (y0 (@pair a1 a0 y1 y2)) (x0 y1 y2)).
Definition term83 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := (fun y0 : type1223 a0 a1 => forall y1 : a1, forall y2 : a0, @GEQ Prop (y0 (@pair a1 a0 y1 y2)) (x0 y1 y2)) (@GABS ((prod a1 a0) -> Prop) (fun y0 : type1223 a0 a1 => forall y1 : a1, forall y2 : a0, @GEQ Prop (y0 (@pair a1 a0 y1 y2)) (x0 y1 y2))).
Definition term52 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) (x2 : a0) := (fun y0 : a1 => fun y1 : a0 => x0 y0 y1) (@ε ((prod a1 a0) -> a1) (fun y0 : type1222 a0 a1 => forall y1 : a1, forall y2 : a0, (y0 (@pair a1 a0 y1 y2)) = y1) (@pair a1 a0 x1 x2)).
Definition term68 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : a1) (x2 : a0) := x0 (@pair a1 a0 x1 x2).
Definition term92 (a0 : Type') (a1 : Type') := fun y0 : prod a1 a0 => (fun y1 : prod a1 a0 => True) y0.
Definition term91 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0) := (fun y0 : prod a1 a0 => (fun y1 : prod a1 a0 => True) y0) (@pair a1 a0 x0 x1).
Definition term75 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : type1470 a0 a1) := fun y0 : a1 => forall y1 : a0, @GEQ Prop (x0 (@pair a1 a0 y0 y1)) (x1 y0 y1).
Definition term79 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := exists y0 : type1223 a0 a1, forall y1 : a1, forall y2 : a0, @GEQ Prop (y0 (@pair a1 a0 y1 y2)) (x0 y1 y2).
Definition term65 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := exists y0 : type1223 a0 a1, forall y1 : a1, forall y2 : a0, (y0 (@pair a1 a0 y1 y2)) = (x0 y1 y2).
Definition term48 (a0 : Type') (x0 : a0) := @eq a0 ((fun y0 : a0 => y0) x0).
Definition term22 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : type1223 a0 a1) := forall y0 : prod a1 a0, (x0 y0) = (x1 y0).
Definition term90 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : prod a1 a0) := (fun y0 : prod a1 a0 => x0 y0) x1.
Definition term31 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := @eq Prop (forall y0 : prod a1 a0, (fun y1 : prod a1 a0 => (@GABS ((prod a1 a0) -> Prop) (fun y2 : type1223 a0 a1 => forall y3 : a1, forall y4 : a0, @GEQ Prop (y2 (@pair a1 a0 y3 y4)) (x0 y3 y4)) y1) = ((fun y2 : prod a1 a0 => True) y1)) y0).
Definition term30 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := fun y0 : prod a1 a0 => (fun y1 : prod a1 a0 => (@GABS ((prod a1 a0) -> Prop) (fun y2 : type1223 a0 a1 => forall y3 : a1, forall y4 : a0, @GEQ Prop (y2 (@pair a1 a0 y3 y4)) (x0 y3 y4)) y1) = ((fun y2 : prod a1 a0 => True) y1)) y0.
Definition term16 (a0 : Type') (a1 : Type') (x0 : type330 a0 a1) (x1 : type1223 a0 a1) := (fun y0 : type1223 a0 a1 => x0 y0) x1.
Definition term34 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) (x2 : a0) := @GABS ((prod a1 a0) -> Prop) (fun y0 : type1223 a0 a1 => forall y1 : a1, forall y2 : a0, @GEQ Prop (y0 (@pair a1 a0 y1 y2)) (x0 y1 y2)) (@pair a1 a0 x1 x2).
Definition term39 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) := forall y0 : a0, (@GABS ((prod a1 a0) -> Prop) (fun y1 : type1223 a0 a1 => forall y2 : a1, forall y3 : a0, @GEQ Prop (y1 (@pair a1 a0 y2 y3)) (x0 y2 y3)) (@pair a1 a0 x1 y0)) = ((fun y1 : prod a1 a0 => True) (@pair a1 a0 x1 y0)).
Definition term35 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0) := (fun y0 : prod a1 a0 => True) (@pair a1 a0 x0 x1).
Definition term7 (a0 : Type') := fun y0 : a0 -> Prop => y0 = (fun y1 : a0 => True).
Definition term19 (a0 : Type') (a1 : Type') := fun y0 : prod a1 a0 => True.
Definition term87 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) (x2 : a0) := (fun y0 : a0 => @GEQ Prop (@GABS ((prod a1 a0) -> Prop) (fun y1 : type1223 a0 a1 => forall y2 : a1, forall y3 : a0, @GEQ Prop (y1 (@pair a1 a0 y2 y3)) (x0 y2 y3)) (@pair a1 a0 x1 y0)) (x0 x1 y0)) x2.
Definition term59 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) (x2 : a0) := x0 (@ε ((prod a1 a0) -> a1) (fun y0 : type1222 a0 a1 => forall y1 : a1, forall y2 : a0, (y0 (@pair a1 a0 y1 y2)) = y1) (@pair a1 a0 x1 x2)) (@ε ((prod a1 a0) -> a0) (fun y0 : type1221 a0 a1 => forall y1 : a1, forall y2 : a0, (y0 (@pair a1 a0 y1 y2)) = y2) (@pair a1 a0 x1 x2)).
Definition term70 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : type1470 a0 a1) (x2 : a1) := fun y0 : a0 => (x0 (@pair a1 a0 x2 y0)) = (x1 x2 y0).
Definition term100 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := @eq Prop (((forall y0 : a1, forall y1 : a0, x0 y0 y1) = (forall y0 : a1, forall y1 : a0, x0 y0 y1)) = True).
Definition term21 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := @eq Prop ((fun y0 : type1223 a0 a1 => (fun y1 : type1223 a0 a1 => y1 = (fun y2 : prod a1 a0 => True)) y0) (@GABS ((prod a1 a0) -> Prop) (fun y0 : type1223 a0 a1 => forall y1 : a1, forall y2 : a0, @GEQ Prop (y0 (@pair a1 a0 y1 y2)) (x0 y1 y2)))).
Definition term86 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) := forall y0 : a0, @GEQ Prop (@GABS ((prod a1 a0) -> Prop) (fun y1 : type1223 a0 a1 => forall y2 : a1, forall y3 : a0, @GEQ Prop (y1 (@pair a1 a0 y2 y3)) (x0 y2 y3)) (@pair a1 a0 x1 y0)) (x0 x1 y0).
Definition term27 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : prod a1 a0) := (fun y0 : prod a1 a0 => (@GABS ((prod a1 a0) -> Prop) (fun y1 : type1223 a0 a1 => forall y2 : a1, forall y3 : a0, @GEQ Prop (y1 (@pair a1 a0 y2 y3)) (x0 y2 y3)) y0) = ((fun y1 : prod a1 a0 => True) y0)) x1.
Definition term32 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := @eq Prop (forall y0 : prod a1 a0, (@GABS ((prod a1 a0) -> Prop) (fun y1 : type1223 a0 a1 => forall y2 : a1, forall y3 : a0, @GEQ Prop (y1 (@pair a1 a0 y2 y3)) (x0 y2 y3)) y0) = ((fun y1 : prod a1 a0 => True) y0)).
Definition term54 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) := @eq (a0 -> Prop) ((fun y0 : a1 => fun y1 : a0 => x0 y0 y1) x1).
Definition term18 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := (fun y0 : type1223 a0 a1 => y0 = (fun y1 : prod a1 a0 => True)) x0.
Definition term13 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := @eq Prop ((fun y0 : type1223 a0 a1 => y0 = (fun y1 : prod a1 a0 => True)) (@GABS ((prod a1 a0) -> Prop) (fun y0 : type1223 a0 a1 => forall y1 : a1, forall y2 : a0, @GEQ Prop (y0 (@pair a1 a0 y1 y2)) (x0 y1 y2)))).
Definition term57 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) (x2 : a0) := (fun y0 : a0 => x0 x1 y0) x2.
Definition term15 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term74 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : type1470 a0 a1) := fun y0 : a1 => forall y1 : a0, (x0 (@pair a1 a0 y0 y1)) = (x1 y0 y1).
Definition term12 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := @eq Prop (all (@GABS ((prod a1 a0) -> Prop) (fun y0 : type1223 a0 a1 => forall y1 : a1, forall y2 : a0, @GEQ Prop (y0 (@pair a1 a0 y1 y2)) (x0 y1 y2)))).
Definition term85 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) := (fun y0 : a1 => forall y1 : a0, @GEQ Prop (@GABS ((prod a1 a0) -> Prop) (fun y2 : type1223 a0 a1 => forall y3 : a1, forall y4 : a0, @GEQ Prop (y2 (@pair a1 a0 y3 y4)) (x0 y3 y4)) (@pair a1 a0 y0 y1)) (x0 y0 y1)) x1.
Definition term63 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) := forall y0 : a0, ((fun y1 : prod a1 a0 => x0 (@ε ((prod a1 a0) -> a1) (fun y2 : type1222 a0 a1 => forall y3 : a1, forall y4 : a0, (y2 (@pair a1 a0 y3 y4)) = y3) y1) (@ε ((prod a1 a0) -> a0) (fun y2 : type1221 a0 a1 => forall y3 : a1, forall y4 : a0, (y2 (@pair a1 a0 y3 y4)) = y4) y1)) (@pair a1 a0 x1 y0)) = (x0 x1 y0).
Definition term99 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := @eq Prop ((fun y0 : Prop => y0 = True) ((forall y0 : a1, forall y1 : a0, x0 y0 y1) = (forall y0 : a1, forall y1 : a0, x0 y0 y1))).
Definition term38 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) := forall y0 : a0, (fun y1 : prod a1 a0 => (@GABS ((prod a1 a0) -> Prop) (fun y2 : type1223 a0 a1 => forall y3 : a1, forall y4 : a0, @GEQ Prop (y2 (@pair a1 a0 y3 y4)) (x0 y3 y4)) y1) = ((fun y2 : prod a1 a0 => True) y1)) (@pair a1 a0 x1 y0).
Definition term49 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0) := (fun y0 : a0 => y0) (@ε ((prod a1 a0) -> a0) (fun y0 : type1221 a0 a1 => forall y1 : a1, forall y2 : a0, (y0 (@pair a1 a0 y1 y2)) = y2) (@pair a1 a0 x0 x1)).
Definition term47 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0) := (fun y0 : a1 => y0) (@ε ((prod a1 a0) -> a1) (fun y0 : type1222 a0 a1 => forall y1 : a1, forall y2 : a0, (y0 (@pair a1 a0 y1 y2)) = y1) (@pair a1 a0 x0 x1)).
Definition term61 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) (x2 : a0) := @eq Prop (x0 x1 x2).
Definition term14 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := forall y0 : a1, forall y1 : a0, x0 y0 y1.
Definition term46 (a0 : Type') (x0 : a0) := (fun y0 : a0 => y0) x0.
Definition term82 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := (exists y0 : type1223 a0 a1, forall y1 : a1, forall y2 : a0, @GEQ Prop (y0 (@pair a1 a0 y1 y2)) (x0 y1 y2)) -> (fun y0 : type1223 a0 a1 => forall y1 : a1, forall y2 : a0, @GEQ Prop (y0 (@pair a1 a0 y1 y2)) (x0 y1 y2)) (@GABS ((prod a1 a0) -> Prop) (fun y0 : type1223 a0 a1 => forall y1 : a1, forall y2 : a0, @GEQ Prop (y0 (@pair a1 a0 y1 y2)) (x0 y1 y2))).
Definition term17 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := (fun y0 : type1223 a0 a1 => (fun y1 : type1223 a0 a1 => y1 = (fun y2 : prod a1 a0 => True)) y0) (@GABS ((prod a1 a0) -> Prop) (fun y0 : type1223 a0 a1 => forall y1 : a1, forall y2 : a0, @GEQ Prop (y0 (@pair a1 a0 y1 y2)) (x0 y1 y2))).
Definition term58 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) (x2 : a0) := (fun y0 : a0 => x0 (@ε ((prod a1 a0) -> a1) (fun y1 : type1222 a0 a1 => forall y2 : a1, forall y3 : a0, (y1 (@pair a1 a0 y2 y3)) = y2) (@pair a1 a0 x1 x2)) y0) (@ε ((prod a1 a0) -> a0) (fun y0 : type1221 a0 a1 => forall y1 : a1, forall y2 : a0, (y0 (@pair a1 a0 y1 y2)) = y2) (@pair a1 a0 x1 x2)).
Definition term24 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := forall y0 : prod a1 a0, (fun y1 : prod a1 a0 => (@GABS ((prod a1 a0) -> Prop) (fun y2 : type1223 a0 a1 => forall y3 : a1, forall y4 : a0, @GEQ Prop (y2 (@pair a1 a0 y3 y4)) (x0 y3 y4)) y1) = ((fun y2 : prod a1 a0 => True) y1)) y0.
Definition term37 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) := fun y0 : a0 => (@GABS ((prod a1 a0) -> Prop) (fun y1 : type1223 a0 a1 => forall y2 : a1, forall y3 : a0, @GEQ Prop (y1 (@pair a1 a0 y2 y3)) (x0 y2 y3)) (@pair a1 a0 x1 y0)) = ((fun y1 : prod a1 a0 => True) (@pair a1 a0 x1 y0)).
Definition term45 (a0 : Type') := fun y0 : a0 => y0.
Definition term33 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) (x2 : a0) := (fun y0 : prod a1 a0 => (@GABS ((prod a1 a0) -> Prop) (fun y1 : type1223 a0 a1 => forall y2 : a1, forall y3 : a0, @GEQ Prop (y1 (@pair a1 a0 y2 y3)) (x0 y2 y3)) y0) = ((fun y1 : prod a1 a0 => True) y0)) (@pair a1 a0 x1 x2).
Definition term94 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0) := @eq Prop ((fun y0 : prod a1 a0 => True) (@pair a1 a0 x0 x1)).
Definition term71 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : type1470 a0 a1) (x2 : a1) := fun y0 : a0 => @GEQ Prop (x0 (@pair a1 a0 x2 y0)) (x1 x2 y0).
Definition term97 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := @eq Prop (forall y0 : a1, forall y1 : a0, x0 y0 y1).
Definition term53 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) (x2 : a0) := fun y0 : a0 => x0 (@ε ((prod a1 a0) -> a1) (fun y1 : type1222 a0 a1 => forall y2 : a1, forall y3 : a0, (y1 (@pair a1 a0 y2 y3)) = y2) (@pair a1 a0 x1 x2)) y0.
Definition term2 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := forall y0 : a1, forall y1 : a0, x0 (@pair a1 a0 y0 y1).
Definition term101 (a0 : Type') (a1 : Type') := forall y0 : type1470 a0 a1, (all (@GABS ((prod a1 a0) -> Prop) (fun y1 : type1223 a0 a1 => forall y2 : a1, forall y3 : a0, @GEQ Prop (y1 (@pair a1 a0 y2 y3)) (y0 y2 y3)))) = (forall y1 : a1, forall y2 : a0, y0 y1 y2).
Definition term88 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) (x2 : a0) := @GEQ Prop (@GABS ((prod a1 a0) -> Prop) (fun y0 : type1223 a0 a1 => forall y1 : a1, forall y2 : a0, @GEQ Prop (y0 (@pair a1 a0 y1 y2)) (x0 y1 y2)) (@pair a1 a0 x1 x2)) (x0 x1 x2).
Definition term72 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : type1470 a0 a1) (x2 : a1) := forall y0 : a0, (x0 (@pair a1 a0 x2 y0)) = (x1 x2 y0).
Definition term73 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : type1470 a0 a1) (x2 : a1) := forall y0 : a0, @GEQ Prop (x0 (@pair a1 a0 x2 y0)) (x1 x2 y0).
Definition term84 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := forall y0 : a1, forall y1 : a0, @GEQ Prop (@GABS ((prod a1 a0) -> Prop) (fun y2 : type1223 a0 a1 => forall y3 : a1, forall y4 : a0, @GEQ Prop (y2 (@pair a1 a0 y3 y4)) (x0 y3 y4)) (@pair a1 a0 y0 y1)) (x0 y0 y1).
Definition term77 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : type1470 a0 a1) := forall y0 : a1, forall y1 : a0, @GEQ Prop (x0 (@pair a1 a0 y0 y1)) (x1 y0 y1).
Definition term76 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : type1470 a0 a1) := forall y0 : a1, forall y1 : a0, (x0 (@pair a1 a0 y0 y1)) = (x1 y0 y1).
Definition term64 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := forall y0 : a1, forall y1 : a0, ((fun y2 : prod a1 a0 => x0 (@ε ((prod a1 a0) -> a1) (fun y3 : type1222 a0 a1 => forall y4 : a1, forall y5 : a0, (y3 (@pair a1 a0 y4 y5)) = y4) y2) (@ε ((prod a1 a0) -> a0) (fun y3 : type1221 a0 a1 => forall y4 : a1, forall y5 : a0, (y3 (@pair a1 a0 y4 y5)) = y5) y2)) (@pair a1 a0 y0 y1)) = (x0 y0 y1).
Definition term42 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := forall y0 : a1, forall y1 : a0, (@GABS ((prod a1 a0) -> Prop) (fun y2 : type1223 a0 a1 => forall y3 : a1, forall y4 : a0, @GEQ Prop (y2 (@pair a1 a0 y3 y4)) (x0 y3 y4)) (@pair a1 a0 y0 y1)) = ((fun y2 : prod a1 a0 => True) (@pair a1 a0 y0 y1)).
Definition term89 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) (x2 : a0) := @eq Prop (@GABS ((prod a1 a0) -> Prop) (fun y0 : type1223 a0 a1 => forall y1 : a1, forall y2 : a0, @GEQ Prop (y0 (@pair a1 a0 y1 y2)) (x0 y1 y2)) (@pair a1 a0 x1 x2)).
Definition term96 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := fun y0 : a1 => forall y1 : a0, x0 y0 y1.
Definition term8 (a0 : Type') (a1 : Type') := fun y0 : type1223 a0 a1 => y0 = (fun y1 : prod a1 a0 => True).
Definition term28 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : prod a1 a0) := @GABS ((prod a1 a0) -> Prop) (fun y0 : type1223 a0 a1 => forall y1 : a1, forall y2 : a0, @GEQ Prop (y0 (@pair a1 a0 y1 y2)) (x0 y1 y2)) x1.
Definition term40 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := fun y0 : a1 => forall y1 : a0, (fun y2 : prod a1 a0 => (@GABS ((prod a1 a0) -> Prop) (fun y3 : type1223 a0 a1 => forall y4 : a1, forall y5 : a0, @GEQ Prop (y3 (@pair a1 a0 y4 y5)) (x0 y4 y5)) y2) = ((fun y3 : prod a1 a0 => True) y2)) (@pair a1 a0 y0 y1).
Definition term56 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) := @eq (a0 -> Prop) (fun y0 : a0 => x0 x1 y0).
Definition term78 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := fun y0 : type1223 a0 a1 => forall y1 : a1, forall y2 : a0, @GEQ Prop (y0 (@pair a1 a0 y1 y2)) (x0 y1 y2).
Definition term66 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := fun y0 : type1223 a0 a1 => forall y1 : a1, forall y2 : a0, (y0 (@pair a1 a0 y1 y2)) = (x0 y1 y2).
Definition term62 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) (x2 : a0) := (fun y0 : prod a1 a0 => x0 (@ε ((prod a1 a0) -> a1) (fun y1 : type1222 a0 a1 => forall y2 : a1, forall y3 : a0, (y1 (@pair a1 a0 y2 y3)) = y2) y0) (@ε ((prod a1 a0) -> a0) (fun y1 : type1221 a0 a1 => forall y2 : a1, forall y3 : a0, (y1 (@pair a1 a0 y2 y3)) = y3) y0)) (@pair a1 a0 x1 x2).
Definition term98 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := (fun y0 : Prop => y0 = True) ((forall y0 : a1, forall y1 : a0, x0 y0 y1) = (forall y0 : a1, forall y1 : a0, x0 y0 y1)).
Definition term44 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0) := @ε ((prod a1 a0) -> a0) (fun y0 : type1221 a0 a1 => forall y1 : a1, forall y2 : a0, (y0 (@pair a1 a0 y1 y2)) = y2) (@pair a1 a0 x0 x1).
Definition term43 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0) := @ε ((prod a1 a0) -> a1) (fun y0 : type1222 a0 a1 => forall y1 : a1, forall y2 : a0, (y0 (@pair a1 a0 y1 y2)) = y1) (@pair a1 a0 x0 x1).
Definition term6 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> a1) := forall y0 : a0, (x0 y0) = (x1 y0).
Definition term55 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) := fun y0 : a0 => x0 x1 y0.
Definition term51 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) := (fun y0 : a1 => fun y1 : a0 => x0 y0 y1) x1.
Definition term60 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) (x2 : a0) := @eq Prop ((fun y0 : a0 => x0 x1 y0) x2).
Definition term93 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0) := @eq Prop ((fun y0 : prod a1 a0 => (fun y1 : prod a1 a0 => True) y0) (@pair a1 a0 x0 x1)).
Definition term3 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := (fun y0 : a0 -> a1 => forall y1 : a0 -> a1, (y0 = y1) = (forall y2 : a0, (y0 y2) = (y1 y2))) x0.
Definition term25 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := forall y0 : a1, forall y1 : a0, (fun y2 : prod a1 a0 => (@GABS ((prod a1 a0) -> Prop) (fun y3 : type1223 a0 a1 => forall y4 : a1, forall y5 : a0, @GEQ Prop (y3 (@pair a1 a0 y4 y5)) (x0 y4 y5)) y2) = ((fun y3 : prod a1 a0 => True) y2)) (@pair a1 a0 y0 y1).
Definition term95 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) := forall y0 : a0, x0 x1 y0.
Definition term5 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> a1) := (fun y0 : a0 -> a1 => (x0 = y0) = (forall y1 : a0, (x0 y1) = (y0 y1))) x1.
Definition term0 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := (fun y0 : type1223 a0 a1 => (forall y1 : prod a1 a0, y0 y1) = (forall y1 : a1, forall y2 : a0, y0 (@pair a1 a0 y1 y2))) x0.
Definition term4 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := forall y0 : a0 -> a1, (x0 = y0) = (forall y1 : a0, (x0 y1) = (y0 y1)).
Definition term69 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : type1470 a0 a1) (x2 : a1) (x3 : a0) := @GEQ Prop (x0 (@pair a1 a0 x2 x3)) (x1 x2 x3).
Definition term10 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := all (@GABS ((prod a1 a0) -> Prop) (fun y0 : type1223 a0 a1 => forall y1 : a1, forall y2 : a0, @GEQ Prop (y0 (@pair a1 a0 y1 y2)) (x0 y1 y2))).
Definition term81 (a0 : Type') (a1 : Type') (x0 : type330 a0 a1) := (ex x0) -> x0 (@GABS ((prod a1 a0) -> Prop) x0).
Definition term80 (a0 : Type') (x0 : a0 -> Prop) := (ex x0) -> x0 (@GABS a0 x0).
