Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term32 (a0 : Type') := forall y0 : a0, forall y1 : list a0, forall y2 : list a0, (@List.app a0 (@cons a0 y0 y1) y2) = (@cons a0 y0 (@List.app a0 y1 y2)).
Definition term51 (a0 : Type') (x0 : a0) := @List.rev a0 (@cons a0 x0 (@nil a0)).
Definition term10 (a0 : Type') (x0 : list a0) := imp ((@List.rev a0 (@List.rev a0 x0)) = x0).
Definition term20 (a0 : Type') := fun y0 : a0 => forall y1 : list a0, ((@List.rev a0 (@List.rev a0 y1)) = y1) -> (@List.rev a0 (@List.rev a0 (@cons a0 y0 y1))) = (@cons a0 y0 y1).
Definition term55 (a0 : Type') (x0 : a0) := @List.app a0 (@List.rev a0 (@cons a0 x0 (@nil a0))).
Definition term38 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : list a0) := @List.app a0 (@cons a0 x0 x1) x2.
Definition term15 (a0 : Type') (x0 : a0) := fun y0 : list a0 => ((fun y1 : list a0 => (@List.rev a0 (@List.rev a0 y1)) = y1) y0) -> (fun y1 : list a0 => (@List.rev a0 (@List.rev a0 y1)) = y1) (@cons a0 x0 y0).
Definition term36 (a0 : Type') (x0 : a0) (x1 : list a0) := forall y0 : list a0, (@List.app a0 (@cons a0 x0 x1) y0) = (@cons a0 x0 (@List.app a0 x1 y0)).
Definition term25 (a0 : Type') := imp (((fun y0 : list a0 => (@List.rev a0 (@List.rev a0 y0)) = y0) (@nil a0)) /\ (forall y0 : a0, forall y1 : list a0, ((fun y2 : list a0 => (@List.rev a0 (@List.rev a0 y2)) = y2) y1) -> (fun y2 : list a0 => (@List.rev a0 (@List.rev a0 y2)) = y2) (@cons a0 y0 y1))).
Definition term52 (a0 : Type') (x0 : a0) := @List.app a0 (@List.rev a0 (@nil a0)) (@cons a0 x0 (@nil a0)).
Definition term1 (a0 : Type') := (((fun y0 : list a0 => (@List.rev a0 (@List.rev a0 y0)) = y0) (@nil a0)) /\ (forall y0 : a0, forall y1 : list a0, ((fun y2 : list a0 => (@List.rev a0 (@List.rev a0 y2)) = y2) y1) -> (fun y2 : list a0 => (@List.rev a0 (@List.rev a0 y2)) = y2) (@cons a0 y0 y1))) -> forall y0 : list a0, (fun y1 : list a0 => (@List.rev a0 (@List.rev a0 y1)) = y1) y0.
Definition term0 (a0 : Type') (x0 : type1143 a0) := ((x0 (@nil a0)) /\ (forall y0 : a0, forall y1 : list a0, (x0 y1) -> x0 (@cons a0 y0 y1))) -> forall y0 : list a0, x0 y0.
Definition term50 (a0 : Type') (x0 : a0) (x1 : list a0) := @List.app a0 (@List.rev a0 (@cons a0 x0 (@nil a0))) (@List.rev a0 (@List.rev a0 x1)).
Definition term29 (a0 : Type') := forall y0 : list a0, (@List.rev a0 (@List.rev a0 y0)) = y0.
Definition term34 (a0 : Type') (x0 : a0) := forall y0 : list a0, forall y1 : list a0, (@List.app a0 (@cons a0 x0 y0) y1) = (@cons a0 x0 (@List.app a0 y0 y1)).
Definition term5 (a0 : Type') := and ((fun y0 : list a0 => (@List.rev a0 (@List.rev a0 y0)) = y0) (@nil a0)).
Definition term54 (a0 : Type') (x0 : a0) := @List.app a0 (@nil a0) (@cons a0 x0 (@nil a0)).
Definition term13 (a0 : Type') (x0 : a0) (x1 : list a0) := ((fun y0 : list a0 => (@List.rev a0 (@List.rev a0 y0)) = y0) x1) -> (fun y0 : list a0 => (@List.rev a0 (@List.rev a0 y0)) = y0) (@cons a0 x0 x1).
Definition term19 (a0 : Type') := fun y0 : a0 => forall y1 : list a0, ((fun y2 : list a0 => (@List.rev a0 (@List.rev a0 y2)) = y2) y1) -> (fun y2 : list a0 => (@List.rev a0 (@List.rev a0 y2)) = y2) (@cons a0 y0 y1).
Definition term6 (a0 : Type') := and ((@List.rev a0 (@List.rev a0 (@nil a0))) = (@nil a0)).
Definition term33 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : list a0, forall y2 : list a0, (@List.app a0 (@cons a0 y0 y1) y2) = (@cons a0 y0 (@List.app a0 y1 y2))) x0.
Definition term42 (a0 : Type') (x0 : list a0) := (fun y0 : list a0 => forall y1 : list a0, (@List.rev a0 (@List.app a0 y0 y1)) = (@List.app a0 (@List.rev a0 y1) (@List.rev a0 y0))) x0.
Definition term16 (a0 : Type') (x0 : a0) := fun y0 : list a0 => ((@List.rev a0 (@List.rev a0 y0)) = y0) -> (@List.rev a0 (@List.rev a0 (@cons a0 x0 y0))) = (@cons a0 x0 y0).
Definition term4 (a0 : Type') := @List.rev a0 (@List.rev a0 (@nil a0)).
Definition term41 (a0 : Type') (x0 : list a0) := (fun y0 : list a0 => (@List.app a0 (@nil a0) y0) = y0) x0.
Definition term59 (a0 : Type') (x0 : a0) (x1 : list a0) := @eq (list a0) (@List.rev a0 (@List.rev a0 (@cons a0 x0 x1))).
Definition term56 (a0 : Type') (x0 : a0) := @List.app a0 (@cons a0 x0 (@nil a0)).
Definition term46 (a0 : Type') (x0 : list a0) (x1 : list a0) := @List.app a0 (@List.rev a0 x0) (@List.rev a0 x1).
Definition term17 (a0 : Type') (x0 : a0) := forall y0 : list a0, ((fun y1 : list a0 => (@List.rev a0 (@List.rev a0 y1)) = y1) y0) -> (fun y1 : list a0 => (@List.rev a0 (@List.rev a0 y1)) = y1) (@cons a0 x0 y0).
Definition term18 (a0 : Type') (x0 : a0) := forall y0 : list a0, ((@List.rev a0 (@List.rev a0 y0)) = y0) -> (@List.rev a0 (@List.rev a0 (@cons a0 x0 y0))) = (@cons a0 x0 y0).
Definition term8 (a0 : Type') (x0 : list a0) := @List.rev a0 (@List.rev a0 x0).
Definition term40 (a0 : Type') := forall y0 : list a0, (@List.app a0 (@nil a0) y0) = y0.
Definition term14 (a0 : Type') (x0 : a0) (x1 : list a0) := ((@List.rev a0 (@List.rev a0 x1)) = x1) -> (@List.rev a0 (@List.rev a0 (@cons a0 x0 x1))) = (@cons a0 x0 x1).
Definition term49 (a0 : Type') (x0 : list a0) (x1 : a0) := @List.rev a0 (@List.app a0 (@List.rev a0 x0) (@cons a0 x1 (@nil a0))).
Definition term57 (a0 : Type') (x0 : a0) (x1 : list a0) := @List.app a0 (@cons a0 x0 (@nil a0)) x1.
Definition term24 (a0 : Type') := ((@List.rev a0 (@List.rev a0 (@nil a0))) = (@nil a0)) /\ (forall y0 : a0, forall y1 : list a0, ((@List.rev a0 (@List.rev a0 y1)) = y1) -> (@List.rev a0 (@List.rev a0 (@cons a0 y0 y1))) = (@cons a0 y0 y1)).
Definition term53 (a0 : Type') := @List.app a0 (@List.rev a0 (@nil a0)).
Definition term11 (a0 : Type') (x0 : a0) (x1 : list a0) := (fun y0 : list a0 => (@List.rev a0 (@List.rev a0 y0)) = y0) (@cons a0 x0 x1).
Definition term45 (a0 : Type') (x0 : list a0) (x1 : list a0) := @List.rev a0 (@List.app a0 x0 x1).
Definition term39 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : list a0) := @cons a0 x0 (@List.app a0 x1 x2).
Definition term2 (a0 : Type') := fun y0 : list a0 => (@List.rev a0 (@List.rev a0 y0)) = y0.
Definition term48 (a0 : Type') (x0 : list a0) (x1 : a0) := @List.app a0 (@List.rev a0 x0) (@cons a0 x1 (@nil a0)).
Definition term35 (a0 : Type') (x0 : a0) (x1 : list a0) := (fun y0 : list a0 => forall y1 : list a0, (@List.app a0 (@cons a0 x0 y0) y1) = (@cons a0 x0 (@List.app a0 y0 y1))) x1.
Definition term27 (a0 : Type') := fun y0 : list a0 => (fun y1 : list a0 => (@List.rev a0 (@List.rev a0 y1)) = y1) y0.
Definition term28 (a0 : Type') := forall y0 : list a0, (fun y1 : list a0 => (@List.rev a0 (@List.rev a0 y1)) = y1) y0.
Definition term26 (a0 : Type') := imp (((@List.rev a0 (@List.rev a0 (@nil a0))) = (@nil a0)) /\ (forall y0 : a0, forall y1 : list a0, ((@List.rev a0 (@List.rev a0 y1)) = y1) -> (@List.rev a0 (@List.rev a0 (@cons a0 y0 y1))) = (@cons a0 y0 y1))).
Definition term31 (a0 : Type') := @eq (list a0) (@List.rev a0 (@List.rev a0 (@nil a0))).
Definition term47 (a0 : Type') (x0 : a0) (x1 : list a0) := @List.rev a0 (@cons a0 x0 x1).
Definition term44 (a0 : Type') (x0 : list a0) (x1 : list a0) := (fun y0 : list a0 => (@List.rev a0 (@List.app a0 x0 y0)) = (@List.app a0 (@List.rev a0 y0) (@List.rev a0 x0))) x1.
Definition term58 (a0 : Type') (x0 : a0) (x1 : list a0) := @cons a0 x0 (@List.app a0 (@nil a0) x1).
Definition term7 (a0 : Type') (x0 : list a0) := (fun y0 : list a0 => (@List.rev a0 (@List.rev a0 y0)) = y0) x0.
Definition term23 (a0 : Type') := ((fun y0 : list a0 => (@List.rev a0 (@List.rev a0 y0)) = y0) (@nil a0)) /\ (forall y0 : a0, forall y1 : list a0, ((fun y2 : list a0 => (@List.rev a0 (@List.rev a0 y2)) = y2) y1) -> (fun y2 : list a0 => (@List.rev a0 (@List.rev a0 y2)) = y2) (@cons a0 y0 y1)).
Definition term30 (a0 : Type') := (((@List.rev a0 (@List.rev a0 (@nil a0))) = (@nil a0)) /\ (forall y0 : a0, forall y1 : list a0, ((@List.rev a0 (@List.rev a0 y1)) = y1) -> (@List.rev a0 (@List.rev a0 (@cons a0 y0 y1))) = (@cons a0 y0 y1))) -> forall y0 : list a0, (@List.rev a0 (@List.rev a0 y0)) = y0.
Definition term43 (a0 : Type') (x0 : list a0) := forall y0 : list a0, (@List.rev a0 (@List.app a0 x0 y0)) = (@List.app a0 (@List.rev a0 y0) (@List.rev a0 x0)).
Definition term37 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : list a0) := (fun y0 : list a0 => (@List.app a0 (@cons a0 x0 x1) y0) = (@cons a0 x0 (@List.app a0 x1 y0))) x2.
Definition term3 (a0 : Type') := (fun y0 : list a0 => (@List.rev a0 (@List.rev a0 y0)) = y0) (@nil a0).
Definition term22 (a0 : Type') := forall y0 : a0, forall y1 : list a0, ((@List.rev a0 (@List.rev a0 y1)) = y1) -> (@List.rev a0 (@List.rev a0 (@cons a0 y0 y1))) = (@cons a0 y0 y1).
Definition term21 (a0 : Type') := forall y0 : a0, forall y1 : list a0, ((fun y2 : list a0 => (@List.rev a0 (@List.rev a0 y2)) = y2) y1) -> (fun y2 : list a0 => (@List.rev a0 (@List.rev a0 y2)) = y2) (@cons a0 y0 y1).
Definition term12 (a0 : Type') (x0 : a0) (x1 : list a0) := @List.rev a0 (@List.rev a0 (@cons a0 x0 x1)).
Definition term9 (a0 : Type') (x0 : list a0) := imp ((fun y0 : list a0 => (@List.rev a0 (@List.rev a0 y0)) = y0) x0).
Definition term60 (a0 : Type') (x0 : a0) (x1 : list a0) := @eq (list a0) (@cons a0 x0 x1).