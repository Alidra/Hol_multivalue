Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : int) := (fun y0 : int => forall y1 : int, (int_coprime (@pair int int y0 y1)) = (exists y2 : int, exists y3 : int, (int_add (int_mul y0 y2) (int_mul y1 y3)) = (int_of_num (NUMERAL (BIT1 0))))) x0.
Definition term2 (x0 : int) (x1 : int) := (fun y0 : int => (int_coprime (@pair int int x0 y0)) = (exists y1 : int, exists y2 : int, (int_add (int_mul x0 y1) (int_mul y0 y2)) = (int_of_num (NUMERAL (BIT1 0))))) x1.
Definition term1 (x0 : int) := forall y0 : int, (int_coprime (@pair int int x0 y0)) = (exists y1 : int, exists y2 : int, (int_add (int_mul x0 y1) (int_mul y0 y2)) = (int_of_num (NUMERAL (BIT1 0)))).
