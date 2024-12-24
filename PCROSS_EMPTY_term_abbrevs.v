Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term5 (a0 : Type') (a1 : Type') (x0 : type24 a0 a1) := or (x0 = (@EMPTY (cart a0 a1))).
Definition term11 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term6 (a0 : Type') (a1 : Type') (x0 : type24 a0 a1) := (x0 = (@EMPTY (cart a0 a1))) \/ True.
Definition term18 (a0 : Type') (a1 : Type') (a2 : Type') := forall y0 : type24 a0 a2, (@PCROSS a0 a1 a2 (@EMPTY (cart a0 a1)) y0) = (@EMPTY (cart a0 (finite_sum a1 a2))).
Definition term4 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type24 a0 a1) := (x0 = (@EMPTY (cart a0 a1))) \/ ((@EMPTY (cart a0 a2)) = (@EMPTY (cart a0 a2))).
Definition term13 (a0 : Type') (a1 : Type') (a2 : Type') := and (forall y0 : type24 a0 a1, (@PCROSS a0 a1 a2 y0 (@EMPTY (cart a0 a2))) = (@EMPTY (cart a0 (finite_sum a1 a2)))).
Definition term8 (a0 : Type') (a1 : Type') := fun y0 : type24 a0 a1 => True.
Definition term9 (a0 : Type') (a1 : Type') (a2 : Type') := forall y0 : type24 a0 a1, (@PCROSS a0 a1 a2 y0 (@EMPTY (cart a0 a2))) = (@EMPTY (cart a0 (finite_sum a1 a2))).
Definition term17 (a0 : Type') (a1 : Type') (a2 : Type') := fun y0 : type24 a0 a2 => (@PCROSS a0 a1 a2 (@EMPTY (cart a0 a1)) y0) = (@EMPTY (cart a0 (finite_sum a1 a2))).
Definition term2 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type24 a0 a1) (x1 : type24 a0 a2) := (fun y0 : type24 a0 a2 => ((@PCROSS a0 a1 a2 x0 y0) = (@EMPTY (cart a0 (finite_sum a1 a2)))) = ((x0 = (@EMPTY (cart a0 a1))) \/ (y0 = (@EMPTY (cart a0 a2))))) x1.
Definition term10 (a0 : Type') (a1 : Type') := forall y0 : type24 a0 a1, True.
Definition term16 (a0 : Type') (a1 : Type') (x0 : type24 a0 a1) := True \/ (x0 = (@EMPTY (cart a0 a1))).
Definition term1 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type24 a0 a1) := forall y0 : type24 a0 a2, ((@PCROSS a0 a1 a2 x0 y0) = (@EMPTY (cart a0 (finite_sum a1 a2)))) = ((x0 = (@EMPTY (cart a0 a1))) \/ (y0 = (@EMPTY (cart a0 a2)))).
Definition term0 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type24 a0 a1) := (fun y0 : type24 a0 a1 => forall y1 : type24 a0 a2, ((@PCROSS a0 a1 a2 y0 y1) = (@EMPTY (cart a0 (finite_sum a1 a2)))) = ((y0 = (@EMPTY (cart a0 a1))) \/ (y1 = (@EMPTY (cart a0 a2))))) x0.
Definition term15 (a0 : Type') (a1 : Type') := or ((@EMPTY (cart a0 a1)) = (@EMPTY (cart a0 a1))).
Definition term12 (a0 : Type') (a1 : Type') (x0 : Prop) := forall y0 : type24 a0 a1, x0.
Definition term19 (a0 : Type') (a1 : Type') (a2 : Type') (a3 : Type') (a4 : Type') (a5 : Type') := (forall y0 : type24 a0 a1, (@PCROSS a0 a1 a2 y0 (@EMPTY (cart a0 a2))) = (@EMPTY (cart a0 (finite_sum a1 a2)))) /\ (forall y0 : type24 a3 a5, (@PCROSS a3 a4 a5 (@EMPTY (cart a3 a4)) y0) = (@EMPTY (cart a3 (finite_sum a4 a5)))).
Definition term7 (a0 : Type') (a1 : Type') (a2 : Type') := fun y0 : type24 a0 a1 => (@PCROSS a0 a1 a2 y0 (@EMPTY (cart a0 a2))) = (@EMPTY (cart a0 (finite_sum a1 a2))).
Definition term3 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type24 a0 a1) (x1 : type24 a0 a2) := (x0 = (@EMPTY (cart a0 a1))) \/ (x1 = (@EMPTY (cart a0 a2))).
Definition term14 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type24 a0 a2) := ((@EMPTY (cart a0 a1)) = (@EMPTY (cart a0 a1))) \/ (x0 = (@EMPTY (cart a0 a2))).
