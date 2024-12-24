Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term3 (x0 : real) := (fun y0 : real => (real_sgn y0) = (@COND real (real_lt (real_of_num (NUMERAL 0)) y0) (real_of_num (NUMERAL (BIT1 0))) (@COND real (real_lt y0 (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))))) x0.
Definition term56 := @eq real (real_inv (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term44 := real_inv (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term31 (x0 : real) := ((real_lt (real_of_num (NUMERAL 0)) x0) -> (real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))) /\ ((~ (real_lt (real_of_num (NUMERAL 0)) x0)) -> (real_inv (@COND real (real_lt x0 (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))) = (@COND real (real_lt x0 (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))).
Definition term43 := (fun y0 : real => (real_inv y0) = y0) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term21 (x0 : real) := imp (~ (real_lt (real_of_num (NUMERAL 0)) x0)).
Definition term58 := @eq real (real_inv (real_of_num (NUMERAL 0))).
Definition term14 (x0 : real) := (fun y0 : real => (real_inv y0) = y0) (@COND real (real_lt (real_of_num (NUMERAL 0)) x0) (real_of_num (NUMERAL (BIT1 0))) (@COND real (real_lt x0 (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))).
Definition term37 := real_of_num (NUMERAL 0).
Definition term32 (x0 : real) := @eq Prop ((fun y0 : real => (real_inv y0) = y0) (@COND real (real_lt (real_of_num (NUMERAL 0)) x0) (real_of_num (NUMERAL (BIT1 0))) (@COND real (real_lt x0 (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))))).
Definition term48 (x0 : real) := and ((real_lt x0 (real_of_num (NUMERAL 0))) -> (fun y0 : real => (real_inv y0) = y0) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term45 (x0 : real) := imp (real_lt x0 (real_of_num (NUMERAL 0))).
Definition term7 (x0 : real) := @eq real (real_inv (real_sgn x0)).
Definition term0 (x0 : real) := (fun y0 : real => (real_inv (real_neg y0)) = (real_neg (real_inv y0))) x0.
Definition term36 (x0 : real) := real_lt x0 (real_of_num (NUMERAL 0)).
Definition term57 := @eq real (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term49 (x0 : real) := and ((real_lt x0 (real_of_num (NUMERAL 0))) -> (real_inv (real_neg (real_of_num (NUMERAL (BIT1 0))))) = (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term39 := real_inv (real_of_num (NUMERAL 0)).
Definition term20 (x0 : real) := real_inv (@COND real (real_lt x0 (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term4 (x0 : real) := @COND real (real_lt (real_of_num (NUMERAL 0)) x0) (real_of_num (NUMERAL (BIT1 0))) (@COND real (real_lt x0 (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term18 (x0 : real) := @COND real (real_lt x0 (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term23 (x0 : real) := (~ (real_lt (real_of_num (NUMERAL 0)) x0)) -> (real_inv (@COND real (real_lt x0 (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))) = (@COND real (real_lt x0 (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term1 (x0 : real) := real_inv (real_neg x0).
Definition term19 (x0 : real) := (fun y0 : real => (real_inv y0) = y0) (@COND real (real_lt x0 (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term30 (x0 : real) := and ((real_lt (real_of_num (NUMERAL 0)) x0) -> (real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term29 (x0 : real) := and ((real_lt (real_of_num (NUMERAL 0)) x0) -> (fun y0 : real => (real_inv y0) = y0) (real_of_num (NUMERAL (BIT1 0)))).
Definition term33 (x0 : real) := @eq Prop ((real_inv (@COND real (real_lt (real_of_num (NUMERAL 0)) x0) (real_of_num (NUMERAL (BIT1 0))) (@COND real (real_lt x0 (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))))) = (@COND real (real_lt (real_of_num (NUMERAL 0)) x0) (real_of_num (NUMERAL (BIT1 0))) (@COND real (real_lt x0 (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))))).
Definition term61 (x0 : real) := ~ (real_lt (real_of_num (NUMERAL 0)) x0).
Definition term2 (x0 : real) := real_neg (real_inv x0).
Definition term10 (x0 : real) (x1 : Prop) (x2 : real -> Prop) (x3 : real) := (x1 -> x2 x0) /\ ((~ x1) -> x2 x3).
Definition term34 (x0 : real) := ((real_lt x0 (real_of_num (NUMERAL 0))) -> (fun y0 : real => (real_inv y0) = y0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) /\ ((~ (real_lt x0 (real_of_num (NUMERAL 0)))) -> (fun y0 : real => (real_inv y0) = y0) (real_of_num (NUMERAL 0))).
Definition term24 := (fun y0 : real => (real_inv y0) = y0) (real_of_num (NUMERAL (BIT1 0))).
Definition term47 (x0 : real) := (real_lt x0 (real_of_num (NUMERAL 0))) -> (real_inv (real_neg (real_of_num (NUMERAL (BIT1 0))))) = (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term40 (x0 : real) := imp (~ (real_lt x0 (real_of_num (NUMERAL 0)))).
Definition term15 (x0 : real) := ((real_lt (real_of_num (NUMERAL 0)) x0) -> (fun y0 : real => (real_inv y0) = y0) (real_of_num (NUMERAL (BIT1 0)))) /\ ((~ (real_lt (real_of_num (NUMERAL 0)) x0)) -> (fun y0 : real => (real_inv y0) = y0) (@COND real (real_lt x0 (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))).
Definition term62 := forall y0 : real, (real_inv (real_sgn y0)) = (real_sgn y0).
Definition term51 (x0 : real) := @eq Prop ((fun y0 : real => (real_inv y0) = y0) (@COND real (real_lt x0 (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))).
Definition term60 (x0 : real) := ~ (real_lt x0 (real_of_num (NUMERAL 0))).
Definition term59 := @eq real (real_of_num (NUMERAL 0)).
Definition term26 (x0 : real) := imp (real_lt (real_of_num (NUMERAL 0)) x0).
Definition term41 (x0 : real) := (~ (real_lt x0 (real_of_num (NUMERAL 0)))) -> (fun y0 : real => (real_inv y0) = y0) (real_of_num (NUMERAL 0)).
Definition term38 := (fun y0 : real => (real_inv y0) = y0) (real_of_num (NUMERAL 0)).
Definition term5 (x0 : real) := real_inv (real_sgn x0).
Definition term42 (x0 : real) := (~ (real_lt x0 (real_of_num (NUMERAL 0)))) -> (real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0)).
Definition term35 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term55 := real_neg (real_inv (real_of_num (NUMERAL (BIT1 0)))).
Definition term8 (x0 : real) := @eq real (real_inv (@COND real (real_lt (real_of_num (NUMERAL 0)) x0) (real_of_num (NUMERAL (BIT1 0))) (@COND real (real_lt x0 (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))))).
Definition term12 (x0 : real) (x1 : Prop) (x2 : real) := (x1 -> (fun y0 : real => (real_inv y0) = y0) x0) /\ ((~ x1) -> (fun y0 : real => (real_inv y0) = y0) x2).
Definition term17 (x0 : real) := real_lt (real_of_num (NUMERAL 0)) x0.
Definition term28 (x0 : real) := (real_lt (real_of_num (NUMERAL 0)) x0) -> (real_inv (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0))).
Definition term52 (x0 : real) := @eq Prop ((real_inv (@COND real (real_lt x0 (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))) = (@COND real (real_lt x0 (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))).
Definition term6 (x0 : real) := real_inv (@COND real (real_lt (real_of_num (NUMERAL 0)) x0) (real_of_num (NUMERAL (BIT1 0))) (@COND real (real_lt x0 (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))).
Definition term16 := real_of_num (NUMERAL (BIT1 0)).
Definition term25 := real_inv (real_of_num (NUMERAL (BIT1 0))).
Definition term9 (x0 : real -> Prop) (x1 : Prop) (x2 : real) (x3 : real) := x0 (@COND real x1 x2 x3).
Definition term46 (x0 : real) := (real_lt x0 (real_of_num (NUMERAL 0))) -> (fun y0 : real => (real_inv y0) = y0) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term54 := @eq real (real_of_num (NUMERAL (BIT1 0))).
Definition term50 (x0 : real) := ((real_lt x0 (real_of_num (NUMERAL 0))) -> (real_inv (real_neg (real_of_num (NUMERAL (BIT1 0))))) = (real_neg (real_of_num (NUMERAL (BIT1 0))))) /\ ((~ (real_lt x0 (real_of_num (NUMERAL 0)))) -> (real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))).
Definition term22 (x0 : real) := (~ (real_lt (real_of_num (NUMERAL 0)) x0)) -> (fun y0 : real => (real_inv y0) = y0) (@COND real (real_lt x0 (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term27 (x0 : real) := (real_lt (real_of_num (NUMERAL 0)) x0) -> (fun y0 : real => (real_inv y0) = y0) (real_of_num (NUMERAL (BIT1 0))).
Definition term13 := fun y0 : real => (real_inv y0) = y0.
Definition term53 := @eq real (real_inv (real_of_num (NUMERAL (BIT1 0)))).
Definition term11 (x0 : Prop) (x1 : real) (x2 : real) := (fun y0 : real => (real_inv y0) = y0) (@COND real x0 x1 x2).
