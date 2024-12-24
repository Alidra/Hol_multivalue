Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term3 (a0 : Type') (x0 : type180 a0) (x1 : type686 a0) := (fun y0 : type686 a0 => (x0 (@EMPTY (a0 -> Prop))) -> @UNION_OF a0 x0 y0 (@EMPTY a0)) x1.
Definition term5 (a0 : Type') (x0 : type180 a0) (x1 : type686 a0) := (x0 (@EMPTY (a0 -> Prop))) -> (@UNION_OF a0 x0 x1 (@EMPTY a0)) = True.
Definition term11 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term0 (a0 : Type') (x0 : type686 a0) := (fun y0 : type686 a0 => (@ARBITRARY a0 y0) = True) x0.
Definition term2 (a0 : Type') (x0 : type180 a0) := forall y0 : type686 a0, (x0 (@EMPTY (a0 -> Prop))) -> @UNION_OF a0 x0 y0 (@EMPTY a0).
Definition term6 (a0 : Type') (x0 : type686 a0) := (@ARBITRARY a0 (@EMPTY (a0 -> Prop))) -> (@UNION_OF a0 (@ARBITRARY a0) x0 (@EMPTY a0)) = True.
Definition term10 (a0 : Type') := forall y0 : type686 a0, True.
Definition term7 (a0 : Type') := fun y0 : type686 a0 => @UNION_OF a0 (@ARBITRARY a0) y0 (@EMPTY a0).
Definition term8 (a0 : Type') := fun y0 : type686 a0 => True.
Definition term1 (a0 : Type') (x0 : type180 a0) := (fun y0 : type180 a0 => forall y1 : type686 a0, (y0 (@EMPTY (a0 -> Prop))) -> @UNION_OF a0 y0 y1 (@EMPTY a0)) x0.
Definition term9 (a0 : Type') := forall y0 : type686 a0, @UNION_OF a0 (@ARBITRARY a0) y0 (@EMPTY a0).
Definition term12 (a0 : Type') (x0 : Prop) := forall y0 : type686 a0, x0.
Definition term4 (a0 : Type') (x0 : type180 a0) (x1 : type686 a0) := (x0 (@EMPTY (a0 -> Prop))) -> @UNION_OF a0 x0 x1 (@EMPTY a0).
