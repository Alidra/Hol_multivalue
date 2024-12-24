Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term4 (x0 : real) := (fun y0 : real => (sqrt y0) = (@ε real (fun y1 : real => ((real_sgn y1) = (real_sgn y0)) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = (real_abs y0))))) x0.
Definition term0 := fun y0 : real => @ε real (fun y1 : real => ((real_sgn y1) = (real_sgn y0)) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = (real_abs y0))).
Definition term3 := forall y0 : real, (sqrt y0) = (@ε real (fun y1 : real => ((real_sgn y1) = (real_sgn y0)) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = (real_abs y0)))).
Definition term2 (x0 : real) := @ε real (fun y0 : real => ((real_sgn y0) = (real_sgn x0)) /\ ((real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_abs x0))).
Definition term1 (x0 : real) := (fun y0 : real => @ε real (fun y1 : real => ((real_sgn y1) = (real_sgn y0)) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = (real_abs y0)))) x0.
