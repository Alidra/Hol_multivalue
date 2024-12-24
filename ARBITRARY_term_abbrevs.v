Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term3 (a0 : Type') (x0 : type686 a0) := (fun y0 : type686 a0 => (@ARBITRARY a0 y0) = True) x0.
Definition term2 (a0 : Type') := forall y0 : type686 a0, (@ARBITRARY a0 y0) = True.
Definition term1 (a0 : Type') (x0 : type686 a0) := (fun y0 : type686 a0 => True) x0.
Definition term0 (a0 : Type') := fun y0 : type686 a0 => True.
