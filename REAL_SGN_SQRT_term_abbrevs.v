Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term9 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term6 := fun y0 : real => True.
Definition term3 (x0 : real) := @eq real (real_sgn (sqrt x0)).
Definition term8 := forall y0 : real, True.
Definition term10 (x0 : Prop) := forall y0 : real, x0.
Definition term5 := fun y0 : real => (real_sgn (sqrt y0)) = (real_sgn y0).
Definition term1 (x0 : real) := ((real_sgn (sqrt x0)) = (real_sgn x0)) /\ ((real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))) = (real_abs x0)).
Definition term7 := forall y0 : real, (real_sgn (sqrt y0)) = (real_sgn y0).
Definition term0 (x0 : real) := (fun y0 : real => ((real_sgn (sqrt y0)) = (real_sgn y0)) /\ ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = (real_abs y0))) x0.
Definition term4 (x0 : real) := @eq real (real_sgn x0).
Definition term2 (x0 : real) := real_sgn (sqrt x0).
