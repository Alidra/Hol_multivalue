Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1902884 : forall x : real, (sqrt (real_pow x (NUMERAL (BIT0 (BIT1 0))))) = (real_abs x).
