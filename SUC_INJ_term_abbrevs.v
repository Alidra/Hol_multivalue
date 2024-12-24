Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term10 (x0 : nat) (x1 : nat) := @eq Prop ((S x0) = (S x1)).
Definition term41 (x0 : nat) (x1 : nat) := imp ((mk_num (dest_num x0)) = (mk_num (dest_num x1))).
Definition term44 (x0 : nat) (x1 : nat) := (x0 = x1) -> x0 = x1.
Definition term13 (x0 : nat) := dest_num (mk_num (IND_SUC (dest_num x0))).
Definition term28 (x0 : nat) (x1 : nat) := ((dest_num (mk_num (IND_SUC (dest_num x0)))) = (dest_num (mk_num (IND_SUC (dest_num x1))))) -> x0 = x1.
Definition term24 := fun y0 : nat => (dest_num (mk_num (IND_SUC (dest_num y0)))) = (IND_SUC (dest_num y0)).
Definition term48 (x0 : nat) := forall y0 : nat, ((S x0) = (S y0)) = (x0 = y0).
Definition term43 (x0 : nat) (x1 : nat) := ((mk_num (dest_num x0)) = (mk_num (dest_num x1))) -> x0 = x1.
Definition term33 (x0 : ind) (x1 : ind) := (fun y0 : ind => ((IND_SUC x0) = (IND_SUC y0)) = (x0 = y0)) x1.
Definition term5 := (forall y0 : ind, (NUM_REP y0) -> NUM_REP (IND_SUC y0)) -> forall y0 : ind, (NUM_REP y0) -> NUM_REP (IND_SUC y0).
Definition term38 (x0 : nat) (x1 : nat) := imp ((dest_num x0) = (dest_num x1)).
Definition term2 (x0 : ind) := (NUM_REP x0) -> NUM_REP (IND_SUC x0).
Definition term15 (x0 : nat) := (NUM_REP (dest_num x0)) -> NUM_REP (IND_SUC (dest_num x0)).
Definition term18 (x0 : nat) := dest_num (mk_num (dest_num x0)).
Definition term14 := forall y0 : nat, NUM_REP (IND_SUC (dest_num y0)).
Definition term4 (x0 : ind) := (forall y0 : ind, (NUM_REP y0) -> NUM_REP (IND_SUC y0)) -> NUM_REP (IND_SUC x0).
Definition term47 (x0 : nat) (x1 : nat) := (((mk_num (IND_SUC (dest_num x0))) = (mk_num (IND_SUC (dest_num x1)))) -> x0 = x1) /\ ((x0 = x1) -> (mk_num (IND_SUC (dest_num x0))) = (mk_num (IND_SUC (dest_num x1)))).
Definition term27 := imp (forall y0 : nat, (dest_num (mk_num (IND_SUC (dest_num y0)))) = (IND_SUC (dest_num y0))).
Definition term26 := imp (forall y0 : nat, NUM_REP (IND_SUC (dest_num y0))).
Definition term34 (x0 : nat) := (fun y0 : nat => (dest_num (mk_num (IND_SUC (dest_num y0)))) = (IND_SUC (dest_num y0))) x0.
Definition term42 (x0 : nat) (x1 : nat) := imp (x0 = x1).
Definition term32 (x0 : ind) := forall y0 : ind, ((IND_SUC x0) = (IND_SUC y0)) = (x0 = y0).
Definition term49 := forall y0 : nat, forall y1 : nat, ((S y0) = (S y1)) = (y0 = y1).
Definition term25 := forall y0 : nat, (dest_num (mk_num (IND_SUC (dest_num y0)))) = (IND_SUC (dest_num y0)).
Definition term36 (x0 : nat) := @eq ind (IND_SUC (dest_num x0)).
Definition term6 (x0 : nat) := (fun y0 : nat => (S y0) = (mk_num (IND_SUC (dest_num y0)))) x0.
Definition term1 (x0 : ind) := (fun y0 : ind => (NUM_REP y0) -> NUM_REP (IND_SUC y0)) x0.
Definition term46 (x0 : nat) (x1 : nat) := ((mk_num (IND_SUC (dest_num x0))) = (mk_num (IND_SUC (dest_num x1)))) -> x0 = x1.
Definition term8 (x0 : nat) := @eq nat (S x0).
Definition term40 (x0 : nat) := @eq nat (mk_num (dest_num x0)).
Definition term16 (x0 : ind) := dest_num (mk_num x0).
Definition term9 (x0 : nat) := @eq nat (mk_num (IND_SUC (dest_num x0))).
Definition term7 (x0 : nat) := mk_num (IND_SUC (dest_num x0)).
Definition term3 (x0 : ind) := NUM_REP (IND_SUC x0).
Definition term11 (x0 : nat) (x1 : nat) := @eq Prop ((mk_num (IND_SUC (dest_num x0))) = (mk_num (IND_SUC (dest_num x1)))).
Definition term31 (x0 : ind) := (fun y0 : ind => forall y1 : ind, ((IND_SUC y0) = (IND_SUC y1)) = (y0 = y1)) x0.
Definition term30 (x0 : nat) (x1 : nat) := (forall y0 : nat, (dest_num (mk_num (IND_SUC (dest_num y0)))) = (IND_SUC (dest_num y0))) -> ((dest_num (mk_num (IND_SUC (dest_num x0)))) = (dest_num (mk_num (IND_SUC (dest_num x1))))) -> x0 = x1.
Definition term20 (x0 : nat) := @eq ind (dest_num (mk_num (dest_num x0))).
Definition term22 (x0 : nat) := NUM_REP (IND_SUC (dest_num x0)).
Definition term37 (x0 : nat) (x1 : nat) := imp ((dest_num (mk_num (IND_SUC (dest_num x0)))) = (dest_num (mk_num (IND_SUC (dest_num x1))))).
Definition term39 (x0 : nat) (x1 : nat) := ((dest_num x0) = (dest_num x1)) -> x0 = x1.
Definition term17 (x0 : nat) := NUM_REP (dest_num x0).
Definition term35 (x0 : nat) := @eq ind (dest_num (mk_num (IND_SUC (dest_num x0)))).
Definition term0 := forall y0 : ind, (NUM_REP y0) -> NUM_REP (IND_SUC y0).
Definition term45 (x0 : nat) (x1 : nat) := (x0 = x1) -> (mk_num (IND_SUC (dest_num x0))) = (mk_num (IND_SUC (dest_num x1))).
Definition term19 (x0 : nat) := mk_num (dest_num x0).
Definition term12 (x0 : nat) := IND_SUC (dest_num x0).
Definition term29 (x0 : nat) (x1 : nat) := (forall y0 : nat, NUM_REP (IND_SUC (dest_num y0))) -> ((dest_num (mk_num (IND_SUC (dest_num x0)))) = (dest_num (mk_num (IND_SUC (dest_num x1))))) -> x0 = x1.
Definition term23 := fun y0 : nat => NUM_REP (IND_SUC (dest_num y0)).
Definition term21 (x0 : nat) := @eq ind (dest_num x0).
