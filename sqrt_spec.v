Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1868831 : forall x : real, (sqrt x) = (@ε real (fun y : real => ((real_sgn y) = (real_sgn x)) /\ ((real_pow y (NUMERAL (BIT0 (BIT1 0)))) = (real_abs x)))).
