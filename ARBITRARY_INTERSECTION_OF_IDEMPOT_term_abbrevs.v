Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term6 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := forall y0 : a0 -> a1, (forall y1 : a0, (x0 y1) = (y0 y1)) = (x0 = y0).
Definition term48 (a0 : Type') := @eq (((a0 -> Prop) -> Prop) -> (a0 -> Prop) -> Prop) (@INTERSECTION_OF a0 (@ARBITRARY a0)).
Definition term45 (a0 : Type') := @eq Prop (forall y0 : type686 a0, (@INTERSECTION_OF a0 (@ARBITRARY a0) y0) = (fun y1 : a0 -> Prop => @UNION_OF a0 (@ARBITRARY a0) (fun y2 : a0 -> Prop => y0 (@DIFF a0 (@UNIV a0) y2)) (@DIFF a0 (@UNIV a0) y1))).
Definition term12 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := fun y0 : a0 => x0 y0.
Definition term32 (a0 : Type') := fun y0 : type686 a0 => forall y1 : a0 -> Prop, (@INTERSECTION_OF a0 (@ARBITRARY a0) y0 y1) = (@UNION_OF a0 (@ARBITRARY a0) (fun y2 : a0 -> Prop => y0 (@DIFF a0 (@UNIV a0) y2)) (@DIFF a0 (@UNIV a0) y1)).
Definition term81 (a0 : Type') := fun y0 : type686 a0 => (@INTERSECTION_OF a0 (@ARBITRARY a0) (@INTERSECTION_OF a0 (@ARBITRARY a0) y0)) = (@INTERSECTION_OF a0 (@ARBITRARY a0) y0).
Definition term4 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := fun y0 : a0 -> a1 => (forall y1 : a0, (x0 y1) = (y0 y1)) = (x0 = y0).
Definition term3 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := fun y0 : a0 -> a1 => (x0 = y0) = (forall y1 : a0, (x0 y1) = (y0 y1)).
Definition term89 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term73 (a0 : Type') (x0 : type686 a0) := fun y0 : a0 -> Prop => @UNION_OF a0 (@ARBITRARY a0) (fun y1 : a0 -> Prop => x0 (@DIFF a0 (@UNIV a0) y1)) y0.
Definition term0 (a0 : Type') (x0 : type686 a0) := (fun y0 : type686 a0 => (@UNION_OF a0 (@ARBITRARY a0) (@UNION_OF a0 (@ARBITRARY a0) y0)) = (@UNION_OF a0 (@ARBITRARY a0) y0)) x0.
Definition term60 (a0 : Type') (x0 : type686 a0) := @eq ((a0 -> Prop) -> Prop) ((fun y0 : type686 a0 => (fun y1 : type686 a0 => fun y2 : a0 -> Prop => @UNION_OF a0 (@ARBITRARY a0) (fun y3 : a0 -> Prop => y1 (@DIFF a0 (@UNIV a0) y3)) (@DIFF a0 (@UNIV a0) y2)) y0) (fun y0 : a0 -> Prop => @UNION_OF a0 (@ARBITRARY a0) (fun y1 : a0 -> Prop => x0 (@DIFF a0 (@UNIV a0) y1)) (@DIFF a0 (@UNIV a0) y0))).
Definition term46 (a0 : Type') (x0 : type174 a0) := fun y0 : type686 a0 => x0 y0.
Definition term30 (a0 : Type') (x0 : type686 a0) := @eq ((a0 -> Prop) -> Prop) (fun y0 : a0 -> Prop => @INTERSECTION_OF a0 (@ARBITRARY a0) x0 y0).
Definition term63 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => x0 y0) x1.
Definition term25 (a0 : Type') (x0 : type686 a0) := fun y0 : a0 -> Prop => (@INTERSECTION_OF a0 (@ARBITRARY a0) x0 y0) = (@UNION_OF a0 (@ARBITRARY a0) (fun y1 : a0 -> Prop => x0 (@DIFF a0 (@UNIV a0) y1)) (@DIFF a0 (@UNIV a0) y0)).
Definition term67 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := @eq Prop ((fun y0 : a0 -> Prop => (fun y1 : a0 -> Prop => @UNION_OF a0 (@ARBITRARY a0) (fun y2 : a0 -> Prop => x0 (@DIFF a0 (@UNIV a0) y2)) (@DIFF a0 (@UNIV a0) y1)) y0) (@DIFF a0 (@UNIV a0) x1)).
Definition term14 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> a1) := (fun y0 : a0 -> a1 => (forall y1 : a0, (x0 y1) = (y0 y1)) = (x0 = y0)) x1.
Definition term11 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := (fun y0 : a0 -> a1 => (fun y1 : a0 => y0 y1) = y0) x0.
Definition term36 (a0 : Type') (x0 : type174 a0) (x1 : type174 a0) := forall y0 : type686 a0, (x0 y0) = (x1 y0).
Definition term28 (a0 : Type') (x0 : type686 a0) := @eq Prop (forall y0 : a0 -> Prop, (@INTERSECTION_OF a0 (@ARBITRARY a0) x0 y0) = (@UNION_OF a0 (@ARBITRARY a0) (fun y1 : a0 -> Prop => x0 (@DIFF a0 (@UNIV a0) y1)) (@DIFF a0 (@UNIV a0) y0))).
Definition term86 (a0 : Type') (x0 : type686 a0) := @eq ((a0 -> Prop) -> Prop) (fun y0 : a0 -> Prop => @UNION_OF a0 (@ARBITRARY a0) (fun y1 : a0 -> Prop => x0 (@DIFF a0 (@UNIV a0) y1)) (@DIFF a0 (@UNIV a0) y0)).
Definition term33 (a0 : Type') := fun y0 : type686 a0 => (@INTERSECTION_OF a0 (@ARBITRARY a0) y0) = (fun y1 : a0 -> Prop => @UNION_OF a0 (@ARBITRARY a0) (fun y2 : a0 -> Prop => y0 (@DIFF a0 (@UNIV a0) y2)) (@DIFF a0 (@UNIV a0) y1)).
Definition term39 (a0 : Type') := fun y0 : type686 a0 => fun y1 : a0 -> Prop => @UNION_OF a0 (@ARBITRARY a0) (fun y2 : a0 -> Prop => y0 (@DIFF a0 (@UNIV a0) y2)) (@DIFF a0 (@UNIV a0) y1).
Definition term16 (a0 : Type') (x0 : type686 a0) := forall y0 : a0 -> Prop, ((fun y1 : a0 -> Prop => @INTERSECTION_OF a0 (@ARBITRARY a0) x0 y1) y0) = ((fun y1 : a0 -> Prop => @UNION_OF a0 (@ARBITRARY a0) (fun y2 : a0 -> Prop => x0 (@DIFF a0 (@UNIV a0) y2)) (@DIFF a0 (@UNIV a0) y1)) y0).
Definition term70 (a0 : Type') (x0 : type686 a0) := @UNION_OF a0 (@ARBITRARY a0) (fun y0 : a0 -> Prop => x0 (@DIFF a0 (@UNIV a0) y0)).
Definition term38 (a0 : Type') := fun y0 : type686 a0 => @INTERSECTION_OF a0 (@ARBITRARY a0) y0.
Definition term21 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := @eq Prop (@INTERSECTION_OF a0 (@ARBITRARY a0) x0 x1).
Definition term65 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => @UNION_OF a0 (@ARBITRARY a0) (fun y1 : a0 -> Prop => x0 (@DIFF a0 (@UNIV a0) y1)) (@DIFF a0 (@UNIV a0) y0)) (@DIFF a0 (@UNIV a0) x1).
Definition term76 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := @UNION_OF a0 (@ARBITRARY a0) (fun y0 : a0 -> Prop => (fun y1 : a0 -> Prop => @UNION_OF a0 (@ARBITRARY a0) (fun y2 : a0 -> Prop => x0 (@DIFF a0 (@UNIV a0) y2)) (@DIFF a0 (@UNIV a0) y1)) (@DIFF a0 (@UNIV a0) y0)) (@DIFF a0 (@UNIV a0) x1).
Definition term72 (a0 : Type') (x0 : type686 a0) := fun y0 : a0 -> Prop => (fun y1 : a0 -> Prop => @UNION_OF a0 (@ARBITRARY a0) (fun y2 : a0 -> Prop => x0 (@DIFF a0 (@UNIV a0) y2)) (@DIFF a0 (@UNIV a0) y1)) (@DIFF a0 (@UNIV a0) y0).
Definition term19 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => @INTERSECTION_OF a0 (@ARBITRARY a0) x0 y0) x1.
Definition term31 (a0 : Type') (x0 : type686 a0) := @eq ((a0 -> Prop) -> Prop) (@INTERSECTION_OF a0 (@ARBITRARY a0) x0).
Definition term55 (a0 : Type') (x0 : type686 a0) := @eq ((a0 -> Prop) -> Prop) ((fun y0 : type686 a0 => (fun y1 : type686 a0 => fun y2 : a0 -> Prop => @UNION_OF a0 (@ARBITRARY a0) (fun y3 : a0 -> Prop => y1 (@DIFF a0 (@UNIV a0) y3)) (@DIFF a0 (@UNIV a0) y2)) y0) x0).
Definition term74 (a0 : Type') (x0 : type686 a0) := @UNION_OF a0 (@ARBITRARY a0) (fun y0 : a0 -> Prop => (fun y1 : a0 -> Prop => @UNION_OF a0 (@ARBITRARY a0) (fun y2 : a0 -> Prop => x0 (@DIFF a0 (@UNIV a0) y2)) (@DIFF a0 (@UNIV a0) y1)) (@DIFF a0 (@UNIV a0) y0)).
Definition term62 (a0 : Type') (x0 : type686 a0) := fun y0 : a0 -> Prop => @UNION_OF a0 (@ARBITRARY a0) (fun y1 : a0 -> Prop => (fun y2 : a0 -> Prop => @UNION_OF a0 (@ARBITRARY a0) (fun y3 : a0 -> Prop => x0 (@DIFF a0 (@UNIV a0) y3)) (@DIFF a0 (@UNIV a0) y2)) (@DIFF a0 (@UNIV a0) y1)) (@DIFF a0 (@UNIV a0) y0).
Definition term49 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@DIFF a0 (@UNIV a0) (@DIFF a0 (@UNIV a0) y0)) = y0) x0.
Definition term40 (a0 : Type') (x0 : type686 a0) := (fun y0 : type686 a0 => @INTERSECTION_OF a0 (@ARBITRARY a0) y0) x0.
Definition term78 (a0 : Type') (x0 : type686 a0) := fun y0 : a0 -> Prop => @UNION_OF a0 (@ARBITRARY a0) (@UNION_OF a0 (@ARBITRARY a0) (fun y1 : a0 -> Prop => x0 (@DIFF a0 (@UNIV a0) y1))) (@DIFF a0 (@UNIV a0) y0).
Definition term75 (a0 : Type') (x0 : type686 a0) := @UNION_OF a0 (@ARBITRARY a0) (@UNION_OF a0 (@ARBITRARY a0) (fun y0 : a0 -> Prop => x0 (@DIFF a0 (@UNIV a0) y0))).
Definition term51 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term88 (a0 : Type') := forall y0 : type686 a0, True.
Definition term17 (a0 : Type') (x0 : type686 a0) := fun y0 : a0 -> Prop => @INTERSECTION_OF a0 (@ARBITRARY a0) x0 y0.
Definition term66 (a0 : Type') (x0 : type686 a0) := fun y0 : a0 -> Prop => (fun y1 : a0 -> Prop => @UNION_OF a0 (@ARBITRARY a0) (fun y2 : a0 -> Prop => x0 (@DIFF a0 (@UNIV a0) y2)) (@DIFF a0 (@UNIV a0) y1)) y0.
Definition term57 (a0 : Type') (x0 : type686 a0) := @INTERSECTION_OF a0 (@ARBITRARY a0) (@INTERSECTION_OF a0 (@ARBITRARY a0) x0).
Definition term35 (a0 : Type') := forall y0 : type686 a0, (@INTERSECTION_OF a0 (@ARBITRARY a0) y0) = (fun y1 : a0 -> Prop => @UNION_OF a0 (@ARBITRARY a0) (fun y2 : a0 -> Prop => y0 (@DIFF a0 (@UNIV a0) y2)) (@DIFF a0 (@UNIV a0) y1)).
Definition term53 (a0 : Type') (x0 : type686 a0) := (fun y0 : type686 a0 => (fun y1 : type686 a0 => fun y2 : a0 -> Prop => @UNION_OF a0 (@ARBITRARY a0) (fun y3 : a0 -> Prop => y1 (@DIFF a0 (@UNIV a0) y3)) (@DIFF a0 (@UNIV a0) y2)) y0) x0.
Definition term29 (a0 : Type') (x0 : type686 a0) := fun y0 : a0 -> Prop => x0 y0.
Definition term52 (a0 : Type') (x0 : type174 a0) (x1 : type686 a0) := (fun y0 : type686 a0 => x0 y0) x1.
Definition term61 (a0 : Type') (x0 : type686 a0) := @eq ((a0 -> Prop) -> Prop) ((fun y0 : type686 a0 => fun y1 : a0 -> Prop => @UNION_OF a0 (@ARBITRARY a0) (fun y2 : a0 -> Prop => y0 (@DIFF a0 (@UNIV a0) y2)) (@DIFF a0 (@UNIV a0) y1)) (fun y0 : a0 -> Prop => @UNION_OF a0 (@ARBITRARY a0) (fun y1 : a0 -> Prop => x0 (@DIFF a0 (@UNIV a0) y1)) (@DIFF a0 (@UNIV a0) y0))).
Definition term24 (a0 : Type') (x0 : type686 a0) := fun y0 : a0 -> Prop => ((fun y1 : a0 -> Prop => @INTERSECTION_OF a0 (@ARBITRARY a0) x0 y1) y0) = ((fun y1 : a0 -> Prop => @UNION_OF a0 (@ARBITRARY a0) (fun y2 : a0 -> Prop => x0 (@DIFF a0 (@UNIV a0) y2)) (@DIFF a0 (@UNIV a0) y1)) y0).
Definition term87 (a0 : Type') := fun y0 : type686 a0 => True.
Definition term56 (a0 : Type') (x0 : type686 a0) := @eq ((a0 -> Prop) -> Prop) ((fun y0 : type686 a0 => fun y1 : a0 -> Prop => @UNION_OF a0 (@ARBITRARY a0) (fun y2 : a0 -> Prop => y0 (@DIFF a0 (@UNIV a0) y2)) (@DIFF a0 (@UNIV a0) y1)) x0).
Definition term85 (a0 : Type') (x0 : type686 a0) := fun y0 : a0 -> Prop => x0 (@DIFF a0 (@UNIV a0) y0).
Definition term82 (a0 : Type') := fun y0 : type686 a0 => (fun y1 : a0 -> Prop => @UNION_OF a0 (@ARBITRARY a0) (@UNION_OF a0 (@ARBITRARY a0) (fun y2 : a0 -> Prop => y0 (@DIFF a0 (@UNIV a0) y2))) (@DIFF a0 (@UNIV a0) y1)) = (fun y1 : a0 -> Prop => @UNION_OF a0 (@ARBITRARY a0) (fun y2 : a0 -> Prop => y0 (@DIFF a0 (@UNIV a0) y2)) (@DIFF a0 (@UNIV a0) y1)).
Definition term59 (a0 : Type') (x0 : type686 a0) := (fun y0 : type686 a0 => (fun y1 : type686 a0 => fun y2 : a0 -> Prop => @UNION_OF a0 (@ARBITRARY a0) (fun y3 : a0 -> Prop => y1 (@DIFF a0 (@UNIV a0) y3)) (@DIFF a0 (@UNIV a0) y2)) y0) (fun y0 : a0 -> Prop => @UNION_OF a0 (@ARBITRARY a0) (fun y1 : a0 -> Prop => x0 (@DIFF a0 (@UNIV a0) y1)) (@DIFF a0 (@UNIV a0) y0)).
Definition term50 (a0 : Type') (x0 : a0 -> Prop) := @DIFF a0 (@UNIV a0) (@DIFF a0 (@UNIV a0) x0).
Definition term47 (a0 : Type') := @eq (((a0 -> Prop) -> Prop) -> (a0 -> Prop) -> Prop) (fun y0 : type686 a0 => @INTERSECTION_OF a0 (@ARBITRARY a0) y0).
Definition term44 (a0 : Type') := @eq Prop (forall y0 : type686 a0, ((fun y1 : type686 a0 => @INTERSECTION_OF a0 (@ARBITRARY a0) y1) y0) = ((fun y1 : type686 a0 => fun y2 : a0 -> Prop => @UNION_OF a0 (@ARBITRARY a0) (fun y3 : a0 -> Prop => y1 (@DIFF a0 (@UNIV a0) y3)) (@DIFF a0 (@UNIV a0) y2)) y0)).
Definition term27 (a0 : Type') (x0 : type686 a0) := @eq Prop (forall y0 : a0 -> Prop, ((fun y1 : a0 -> Prop => @INTERSECTION_OF a0 (@ARBITRARY a0) x0 y1) y0) = ((fun y1 : a0 -> Prop => @UNION_OF a0 (@ARBITRARY a0) (fun y2 : a0 -> Prop => x0 (@DIFF a0 (@UNIV a0) y2)) (@DIFF a0 (@UNIV a0) y1)) y0)).
Definition term37 (a0 : Type') := forall y0 : type686 a0, ((fun y1 : type686 a0 => @INTERSECTION_OF a0 (@ARBITRARY a0) y1) y0) = ((fun y1 : type686 a0 => fun y2 : a0 -> Prop => @UNION_OF a0 (@ARBITRARY a0) (fun y3 : a0 -> Prop => y1 (@DIFF a0 (@UNIV a0) y3)) (@DIFF a0 (@UNIV a0) y2)) y0).
Definition term83 (a0 : Type') := forall y0 : type686 a0, (@INTERSECTION_OF a0 (@ARBITRARY a0) (@INTERSECTION_OF a0 (@ARBITRARY a0) y0)) = (@INTERSECTION_OF a0 (@ARBITRARY a0) y0).
Definition term10 (a0 : Type') (a1 : Type') := forall y0 : a0 -> a1, forall y1 : a0 -> a1, (forall y2 : a0, (y0 y2) = (y1 y2)) = (y0 = y1).
Definition term9 (a0 : Type') (a1 : Type') := forall y0 : a0 -> a1, forall y1 : a0 -> a1, (y0 = y1) = (forall y2 : a0, (y0 y2) = (y1 y2)).
Definition term84 (a0 : Type') := forall y0 : type686 a0, (fun y1 : a0 -> Prop => @UNION_OF a0 (@ARBITRARY a0) (@UNION_OF a0 (@ARBITRARY a0) (fun y2 : a0 -> Prop => y0 (@DIFF a0 (@UNIV a0) y2))) (@DIFF a0 (@UNIV a0) y1)) = (fun y1 : a0 -> Prop => @UNION_OF a0 (@ARBITRARY a0) (fun y2 : a0 -> Prop => y0 (@DIFF a0 (@UNIV a0) y2)) (@DIFF a0 (@UNIV a0) y1)).
Definition term68 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := @eq Prop ((fun y0 : a0 -> Prop => @UNION_OF a0 (@ARBITRARY a0) (fun y1 : a0 -> Prop => x0 (@DIFF a0 (@UNIV a0) y1)) (@DIFF a0 (@UNIV a0) y0)) (@DIFF a0 (@UNIV a0) x1)).
Definition term34 (a0 : Type') := forall y0 : type686 a0, forall y1 : a0 -> Prop, (@INTERSECTION_OF a0 (@ARBITRARY a0) y0 y1) = (@UNION_OF a0 (@ARBITRARY a0) (fun y2 : a0 -> Prop => y0 (@DIFF a0 (@UNIV a0) y2)) (@DIFF a0 (@UNIV a0) y1)).
Definition term79 (a0 : Type') (x0 : type686 a0) := @eq ((a0 -> Prop) -> Prop) (@INTERSECTION_OF a0 (@ARBITRARY a0) (@INTERSECTION_OF a0 (@ARBITRARY a0) x0)).
Definition term58 (a0 : Type') (x0 : type686 a0) := (fun y0 : type686 a0 => fun y1 : a0 -> Prop => @UNION_OF a0 (@ARBITRARY a0) (fun y2 : a0 -> Prop => y0 (@DIFF a0 (@UNIV a0) y2)) (@DIFF a0 (@UNIV a0) y1)) (fun y0 : a0 -> Prop => @UNION_OF a0 (@ARBITRARY a0) (fun y1 : a0 -> Prop => x0 (@DIFF a0 (@UNIV a0) y1)) (@DIFF a0 (@UNIV a0) y0)).
Definition term41 (a0 : Type') (x0 : type686 a0) := @eq ((a0 -> Prop) -> Prop) ((fun y0 : type686 a0 => @INTERSECTION_OF a0 (@ARBITRARY a0) y0) x0).
Definition term54 (a0 : Type') := fun y0 : type686 a0 => (fun y1 : type686 a0 => fun y2 : a0 -> Prop => @UNION_OF a0 (@ARBITRARY a0) (fun y3 : a0 -> Prop => y1 (@DIFF a0 (@UNIV a0) y3)) (@DIFF a0 (@UNIV a0) y2)) y0.
Definition term20 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := @eq Prop ((fun y0 : a0 -> Prop => @INTERSECTION_OF a0 (@ARBITRARY a0) x0 y0) x1).
Definition term22 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => @UNION_OF a0 (@ARBITRARY a0) (fun y1 : a0 -> Prop => x0 (@DIFF a0 (@UNIV a0) y1)) (@DIFF a0 (@UNIV a0) y0)) x1.
Definition term90 (a0 : Type') (x0 : Prop) := forall y0 : type686 a0, x0.
Definition term77 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := @UNION_OF a0 (@ARBITRARY a0) (@UNION_OF a0 (@ARBITRARY a0) (fun y0 : a0 -> Prop => x0 (@DIFF a0 (@UNIV a0) y0))) (@DIFF a0 (@UNIV a0) x1).
Definition term26 (a0 : Type') (x0 : type686 a0) := forall y0 : a0 -> Prop, (@INTERSECTION_OF a0 (@ARBITRARY a0) x0 y0) = (@UNION_OF a0 (@ARBITRARY a0) (fun y1 : a0 -> Prop => x0 (@DIFF a0 (@UNIV a0) y1)) (@DIFF a0 (@UNIV a0) y0)).
Definition term80 (a0 : Type') (x0 : type686 a0) := @eq ((a0 -> Prop) -> Prop) (fun y0 : a0 -> Prop => @UNION_OF a0 (@ARBITRARY a0) (@UNION_OF a0 (@ARBITRARY a0) (fun y1 : a0 -> Prop => x0 (@DIFF a0 (@UNIV a0) y1))) (@DIFF a0 (@UNIV a0) y0)).
Definition term1 (a0 : Type') (x0 : type686 a0) := @UNION_OF a0 (@ARBITRARY a0) (@UNION_OF a0 (@ARBITRARY a0) x0).
Definition term71 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := @UNION_OF a0 (@ARBITRARY a0) (fun y0 : a0 -> Prop => x0 (@DIFF a0 (@UNIV a0) y0)) x1.
Definition term8 (a0 : Type') (a1 : Type') := fun y0 : a0 -> a1 => forall y1 : a0 -> a1, (forall y2 : a0, (y0 y2) = (y1 y2)) = (y0 = y1).
Definition term64 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (fun y1 : a0 -> Prop => @UNION_OF a0 (@ARBITRARY a0) (fun y2 : a0 -> Prop => x0 (@DIFF a0 (@UNIV a0) y2)) (@DIFF a0 (@UNIV a0) y1)) y0) (@DIFF a0 (@UNIV a0) x1).
Definition term69 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := @UNION_OF a0 (@ARBITRARY a0) (fun y0 : a0 -> Prop => x0 (@DIFF a0 (@UNIV a0) y0)) (@DIFF a0 (@UNIV a0) (@DIFF a0 (@UNIV a0) x1)).
Definition term2 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> a1) := forall y0 : a0, (x0 y0) = (x1 y0).
Definition term15 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) := forall y0 : a0 -> Prop, (x0 y0) = (x1 y0).
Definition term13 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := (fun y0 : a0 -> a1 => forall y1 : a0 -> a1, (forall y2 : a0, (y0 y2) = (y1 y2)) = (y0 = y1)) x0.
Definition term18 (a0 : Type') (x0 : type686 a0) := fun y0 : a0 -> Prop => @UNION_OF a0 (@ARBITRARY a0) (fun y1 : a0 -> Prop => x0 (@DIFF a0 (@UNIV a0) y1)) (@DIFF a0 (@UNIV a0) y0).
Definition term42 (a0 : Type') (x0 : type686 a0) := (fun y0 : type686 a0 => fun y1 : a0 -> Prop => @UNION_OF a0 (@ARBITRARY a0) (fun y2 : a0 -> Prop => y0 (@DIFF a0 (@UNIV a0) y2)) (@DIFF a0 (@UNIV a0) y1)) x0.
Definition term7 (a0 : Type') (a1 : Type') := fun y0 : a0 -> a1 => forall y1 : a0 -> a1, (y0 = y1) = (forall y2 : a0, (y0 y2) = (y1 y2)).
Definition term43 (a0 : Type') := fun y0 : type686 a0 => ((fun y1 : type686 a0 => @INTERSECTION_OF a0 (@ARBITRARY a0) y1) y0) = ((fun y1 : type686 a0 => fun y2 : a0 -> Prop => @UNION_OF a0 (@ARBITRARY a0) (fun y3 : a0 -> Prop => y1 (@DIFF a0 (@UNIV a0) y3)) (@DIFF a0 (@UNIV a0) y2)) y0).
Definition term5 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := forall y0 : a0 -> a1, (x0 = y0) = (forall y1 : a0, (x0 y1) = (y0 y1)).
Definition term23 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := @UNION_OF a0 (@ARBITRARY a0) (fun y0 : a0 -> Prop => x0 (@DIFF a0 (@UNIV a0) y0)) (@DIFF a0 (@UNIV a0) x1).
