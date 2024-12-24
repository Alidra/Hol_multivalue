Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2447313 : forall (a : int) (b : int), ((fun b' : int => (int_coprime (@pair int int a b')) = (exists x : int, exists y : int, (int_add (int_mul a x) (int_mul b' y)) = (int_of_num (NUMERAL (BIT1 0))))) b) = ((int_coprime (@pair int int a b)) = (exists x : int, exists y : int, (int_add (int_mul a x) (int_mul b y)) = (int_of_num (NUMERAL (BIT1 0))))).
