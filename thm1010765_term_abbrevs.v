Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term9 (x0 : nat) := ~ (~ (Peano.lt (NUMERAL x0) (NUMERAL x0))).
Definition term28 := (~ False) -> False.
Definition term14 := ~ (forall y0 : nat, ~ (Peano.lt y0 y0)).
Definition term24 (x0 : nat) := (~ (Peano.lt (NUMERAL x0) (NUMERAL x0))) -> Peano.lt (NUMERAL x0) (NUMERAL x0).
Definition term10 (x0 : Prop) := ~ (~ x0).
Definition term26 (x0 : nat) := (Peano.lt x0 x0) -> False.
Definition term0 (x0 : Prop) := (~ x0) -> False.
Definition term4 (x0 : nat) := (~ ((Peano.lt (NUMERAL x0) (NUMERAL x0)) = False)) -> (forall y0 : nat, ~ (Peano.lt y0 y0)) -> False.
Definition term18 := fun y0 : nat => (Peano.lt (NUMERAL y0) (NUMERAL y0)) -> ~ (forall y1 : nat, ~ (Peano.lt y1 y1)).
Definition term25 (x0 : Prop) := (~ x0) -> x0.
Definition term16 (x0 : nat) := (Peano.lt (NUMERAL x0) (NUMERAL x0)) -> ~ (forall y0 : nat, ~ (Peano.lt y0 y0)).
Definition term8 (x0 : nat) := ~ (Peano.lt (NUMERAL x0) (NUMERAL x0)).
Definition term20 := forall y0 : nat, (Peano.lt (NUMERAL y0) (NUMERAL y0)) -> ~ (forall y1 : nat, ~ (Peano.lt y1 y1)).
Definition term12 (x0 : nat) := imp (Peano.lt (NUMERAL x0) (NUMERAL x0)).
Definition term11 (x0 : nat) := imp (~ ((Peano.lt (NUMERAL x0) (NUMERAL x0)) = False)).
Definition term5 (x0 : nat) := ((~ ((Peano.lt (NUMERAL x0) (NUMERAL x0)) = False)) -> (forall y0 : nat, ~ (Peano.lt y0 y0)) -> False) -> (~ ((Peano.lt (NUMERAL x0) (NUMERAL x0)) = False)) -> (forall y0 : nat, ~ (Peano.lt y0 y0)) -> False.
Definition term21 (x0 : nat) := ~ (Peano.lt x0 x0).
Definition term15 := forall y0 : nat, ~ (Peano.lt y0 y0).
Definition term19 := forall y0 : nat, (~ ((Peano.lt (NUMERAL y0) (NUMERAL y0)) = False)) -> (forall y1 : nat, ~ (Peano.lt y1 y1)) -> False.
Definition term13 := (forall y0 : nat, ~ (Peano.lt y0 y0)) -> False.
Definition term22 := fun y0 : nat => ~ (Peano.lt y0 y0).
Definition term6 (x0 : nat) := (((~ ((Peano.lt (NUMERAL x0) (NUMERAL x0)) = False)) -> (forall y0 : nat, ~ (Peano.lt y0 y0)) -> False) -> (~ ((Peano.lt (NUMERAL x0) (NUMERAL x0)) = False)) -> (forall y0 : nat, ~ (Peano.lt y0 y0)) -> False) -> (~ ((Peano.lt (NUMERAL x0) (NUMERAL x0)) = False)) -> (forall y0 : nat, ~ (Peano.lt y0 y0)) -> False.
Definition term29 (x0 : nat) := (fun y0 : nat => (~ ((Peano.lt (NUMERAL y0) (NUMERAL y0)) = False)) -> (forall y1 : nat, ~ (Peano.lt y1 y1)) -> False) x0.
Definition term23 (x0 : nat) := (fun y0 : nat => ~ (Peano.lt y0 y0)) x0.
Definition term27 (x0 : nat) := (Peano.lt (NUMERAL x0) (NUMERAL x0)) -> False.
Definition term2 (x0 : nat) := (~ ((Peano.lt (NUMERAL x0) (NUMERAL x0)) = False)) -> False.
Definition term7 (x0 : nat) := (((~ ((Peano.lt (NUMERAL x0) (NUMERAL x0)) = False)) -> (forall y0 : nat, ~ (Peano.lt y0 y0)) -> False) -> (~ ((Peano.lt (NUMERAL x0) (NUMERAL x0)) = False)) -> (forall y0 : nat, ~ (Peano.lt y0 y0)) -> False) -> ((~ ((Peano.lt (NUMERAL x0) (NUMERAL x0)) = False)) -> (forall y0 : nat, ~ (Peano.lt y0 y0)) -> False) -> (~ ((Peano.lt (NUMERAL x0) (NUMERAL x0)) = False)) -> (forall y0 : nat, ~ (Peano.lt y0 y0)) -> False.
Definition term1 (x0 : nat) := Peano.lt (NUMERAL x0) (NUMERAL x0).
Definition term17 := fun y0 : nat => (~ ((Peano.lt (NUMERAL y0) (NUMERAL y0)) = False)) -> (forall y1 : nat, ~ (Peano.lt y1 y1)) -> False.
Definition term3 (x0 : nat) := ~ ((Peano.lt (NUMERAL x0) (NUMERAL x0)) = False).
