Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') := @INJP a0 (@INJN a0 (NUMERAL 0)) (@ε (nat -> a0 -> Prop) (fun y0 : type1597 a0 => True)).
