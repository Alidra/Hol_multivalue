Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term42 (x0 : nat -> Prop) := forall y0 : ind, ((NUM_REP y0) /\ (x0 (mk_num y0))) -> (NUM_REP (IND_SUC y0)) /\ (x0 (mk_num (IND_SUC y0))).
Definition term70 (x0 : nat -> Prop) := fun y0 : nat => x0 y0.
Definition term24 := and (NUM_REP IND_0).
Definition term30 (x0 : nat -> Prop) (x1 : ind) := imp ((fun y0 : ind => (NUM_REP y0) /\ (x0 (mk_num y0))) x1).
Definition term73 (x0 : nat -> Prop) (x1 : ind) := x0 (S (mk_num x1)).
Definition term35 (x0 : nat -> Prop) (x1 : ind) := @eq Prop ((fun y0 : ind => (NUM_REP y0) /\ (x0 (mk_num y0))) (IND_SUC x1)).
Definition term77 (x0 : ind) := mk_num (IND_SUC (dest_num (mk_num x0))).
Definition term63 (x0 : Prop) := forall y0 : ind, x0.
Definition term31 (x0 : nat -> Prop) (x1 : ind) := imp ((NUM_REP x1) /\ (x0 (mk_num x1))).
Definition term68 (x0 : ind) := mk_num (IND_SUC x0).
Definition term71 (x0 : nat -> Prop) (x1 : ind) := (fun y0 : nat => x0 y0) (mk_num (IND_SUC x1)).
Definition term72 (x0 : nat -> Prop) (x1 : ind) := (fun y0 : nat => x0 y0) (S (mk_num x1)).
Definition term62 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term34 (x0 : nat -> Prop) (x1 : ind) := @eq Prop ((fun y0 : ind => (fun y1 : ind => (NUM_REP y1) /\ (x0 (mk_num y1))) y0) (IND_SUC x1)).
Definition term86 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : ind => (NUM_REP y0) -> (NUM_REP y0) /\ (x0 (mk_num y0))) (dest_num x1).
Definition term102 (x0 : nat -> Prop) (x1 : nat) := (x0 x1) -> x0 x1.
Definition term95 (x0 : nat -> Prop) (x1 : nat) := x0 (mk_num (dest_num x1)).
Definition term100 (x0 : nat -> Prop) (x1 : nat) := imp (x0 x1).
Definition term67 (x0 : nat -> Prop) (x1 : ind) := x0 (mk_num x1).
Definition term38 (x0 : nat -> Prop) (x1 : ind) := ((NUM_REP x1) /\ (x0 (mk_num x1))) -> (NUM_REP (IND_SUC x1)) /\ (x0 (mk_num (IND_SUC x1))).
Definition term66 (x0 : nat -> Prop) (x1 : nat) := (forall y0 : ind, (NUM_REP y0) -> (NUM_REP y0) /\ (x0 (mk_num y0))) -> x0 x1.
Definition term47 (x0 : ind) := imp (NUM_REP x0).
Definition term19 (x0 : nat -> Prop) (x1 : ind) := (NUM_REP x1) /\ (x0 (mk_num x1)).
Definition term54 (x0 : nat -> Prop) := (forall y0 : ind, ((NUM_REP y0) /\ (x0 (mk_num y0))) -> (NUM_REP (IND_SUC y0)) /\ (x0 (mk_num (IND_SUC y0)))) -> forall y0 : ind, (NUM_REP y0) -> (NUM_REP y0) /\ (x0 (mk_num y0)).
Definition term8 := (forall y0 : ind, (NUM_REP y0) -> NUM_REP (IND_SUC y0)) -> forall y0 : ind, (NUM_REP y0) -> NUM_REP (IND_SUC y0).
Definition term5 (x0 : ind) := (NUM_REP x0) -> NUM_REP (IND_SUC x0).
Definition term9 (x0 : nat -> Prop) := (fun y0 : ind -> Prop => ((y0 IND_0) /\ (forall y1 : ind, (y0 y1) -> y0 (IND_SUC y1))) -> forall y1 : ind, (NUM_REP y1) -> y0 y1) (fun y0 : ind => (NUM_REP y0) /\ (x0 (mk_num y0))).
Definition term81 (x0 : nat -> Prop) (x1 : nat) := (x0 x1) -> x0 (S x1).
Definition term53 (x0 : nat -> Prop) := forall y0 : ind, (NUM_REP y0) -> (NUM_REP y0) /\ (x0 (mk_num y0)).
Definition term83 (x0 : nat -> Prop) (x1 : nat) := (forall y0 : nat, (x0 y0) -> x0 (S y0)) -> x0 (S x1).
Definition term18 (x0 : nat -> Prop) (x1 : ind) := (fun y0 : ind => (NUM_REP y0) /\ (x0 (mk_num y0))) x1.
Definition term43 (x0 : nat -> Prop) := ((fun y0 : ind => (NUM_REP y0) /\ (x0 (mk_num y0))) IND_0) /\ (forall y0 : ind, ((fun y1 : ind => (NUM_REP y1) /\ (x0 (mk_num y1))) y0) -> (fun y1 : ind => (NUM_REP y1) /\ (x0 (mk_num y1))) (IND_SUC y0)).
Definition term57 (x0 : nat -> Prop) (x1 : nat) := ((((fun y0 : ind => (NUM_REP y0) /\ (x0 (mk_num y0))) IND_0) /\ (forall y0 : ind, ((fun y1 : ind => (NUM_REP y1) /\ (x0 (mk_num y1))) y0) -> (fun y1 : ind => (NUM_REP y1) /\ (x0 (mk_num y1))) (IND_SUC y0))) -> forall y0 : ind, (NUM_REP y0) -> (fun y1 : ind => (NUM_REP y1) /\ (x0 (mk_num y1))) y0) -> x0 x1.
Definition term89 (x0 : nat) := dest_num (mk_num (dest_num x0)).
Definition term7 (x0 : ind) := (forall y0 : ind, (NUM_REP y0) -> NUM_REP (IND_SUC y0)) -> NUM_REP (IND_SUC x0).
Definition term69 (x0 : ind) := S (mk_num x0).
Definition term87 (x0 : nat -> Prop) (x1 : nat) := (NUM_REP (dest_num x1)) -> (NUM_REP (dest_num x1)) /\ (x0 (mk_num (dest_num x1))).
Definition term55 (x0 : nat -> Prop) := imp ((((fun y0 : ind => (NUM_REP y0) /\ (x0 (mk_num y0))) IND_0) /\ (forall y0 : ind, ((fun y1 : ind => (NUM_REP y1) /\ (x0 (mk_num y1))) y0) -> (fun y1 : ind => (NUM_REP y1) /\ (x0 (mk_num y1))) (IND_SUC y0))) -> forall y0 : ind, (NUM_REP y0) -> (fun y1 : ind => (NUM_REP y1) /\ (x0 (mk_num y1))) y0).
Definition term74 (x0 : nat -> Prop) (x1 : ind) := @eq Prop ((fun y0 : nat => x0 y0) (mk_num (IND_SUC x1))).
Definition term10 (x0 : nat -> Prop) := fun y0 : ind => (NUM_REP y0) /\ (x0 (mk_num y0)).
Definition term16 (x0 : nat -> Prop) := (fun y0 : ind => (fun y1 : ind => (NUM_REP y1) /\ (x0 (mk_num y1))) y0) IND_0.
Definition term14 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term22 (x0 : nat -> Prop) := @eq Prop ((fun y0 : ind => (NUM_REP y0) /\ (x0 (mk_num y0))) IND_0).
Definition term85 (x0 : nat -> Prop) (x1 : ind) := (x0 (mk_num x1)) -> x0 (S (mk_num x1)).
Definition term39 (x0 : nat -> Prop) := fun y0 : ind => ((fun y1 : ind => (NUM_REP y1) /\ (x0 (mk_num y1))) y0) -> (fun y1 : ind => (NUM_REP y1) /\ (x0 (mk_num y1))) (IND_SUC y0).
Definition term104 (x0 : nat -> Prop) := ((x0 0) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term65 (x0 : nat -> Prop) := imp (forall y0 : ind, (NUM_REP y0) -> (NUM_REP y0) /\ (x0 (mk_num y0))).
Definition term46 (x0 : nat -> Prop) := imp (forall y0 : ind, ((NUM_REP y0) /\ (x0 (mk_num y0))) -> (NUM_REP (IND_SUC y0)) /\ (x0 (mk_num (IND_SUC y0)))).
Definition term1 (x0 : nat) := (fun y0 : nat => (S y0) = (mk_num (IND_SUC (dest_num y0)))) x0.
Definition term4 (x0 : ind) := (fun y0 : ind => (NUM_REP y0) -> NUM_REP (IND_SUC y0)) x0.
Definition term75 (x0 : nat -> Prop) (x1 : ind) := x0 (mk_num (IND_SUC x1)).
Definition term12 (x0 : nat -> Prop) := (x0 0) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0)).
Definition term41 (x0 : nat -> Prop) := forall y0 : ind, ((fun y1 : ind => (NUM_REP y1) /\ (x0 (mk_num y1))) y0) -> (fun y1 : ind => (NUM_REP y1) /\ (x0 (mk_num y1))) (IND_SUC y0).
Definition term28 (x0 : nat -> Prop) (x1 : ind) := @eq Prop ((fun y0 : ind => (fun y1 : ind => (NUM_REP y1) /\ (x0 (mk_num y1))) y0) x1).
Definition term45 (x0 : nat -> Prop) := imp (((fun y0 : ind => (NUM_REP y0) /\ (x0 (mk_num y0))) IND_0) /\ (forall y0 : ind, ((fun y1 : ind => (NUM_REP y1) /\ (x0 (mk_num y1))) y0) -> (fun y1 : ind => (NUM_REP y1) /\ (x0 (mk_num y1))) (IND_SUC y0))).
Definition term96 (x0 : nat -> Prop) (x1 : nat) := (NUM_REP (dest_num x1)) /\ (x0 (mk_num (dest_num x1))).
Definition term36 (x0 : nat -> Prop) (x1 : ind) := (NUM_REP (IND_SUC x1)) /\ (x0 (mk_num (IND_SUC x1))).
Definition term97 (x0 : nat -> Prop) (x1 : nat) := True /\ (x0 x1).
Definition term56 (x0 : nat -> Prop) := imp ((forall y0 : ind, ((NUM_REP y0) /\ (x0 (mk_num y0))) -> (NUM_REP (IND_SUC y0)) /\ (x0 (mk_num (IND_SUC y0)))) -> forall y0 : ind, (NUM_REP y0) -> (NUM_REP y0) /\ (x0 (mk_num y0))).
Definition term51 (x0 : nat -> Prop) := fun y0 : ind => (NUM_REP y0) -> (NUM_REP y0) /\ (x0 (mk_num y0)).
Definition term105 := forall y0 : nat -> Prop, ((y0 0) /\ (forall y1 : nat, (y0 y1) -> y0 (S y1))) -> forall y1 : nat, y0 y1.
Definition term25 (x0 : nat -> Prop) := x0 (mk_num IND_0).
Definition term101 (x0 : nat -> Prop) (x1 : nat) := ((NUM_REP (dest_num x1)) -> (NUM_REP (dest_num x1)) /\ (x0 (mk_num (dest_num x1)))) -> x0 x1.
Definition term79 (x0 : ind) := IND_SUC (dest_num (mk_num x0)).
Definition term40 (x0 : nat -> Prop) := fun y0 : ind => ((NUM_REP y0) /\ (x0 (mk_num y0))) -> (NUM_REP (IND_SUC y0)) /\ (x0 (mk_num (IND_SUC y0))).
Definition term76 (x0 : nat -> Prop) (x1 : ind) := @eq Prop (x0 (mk_num (IND_SUC x1))).
Definition term61 := forall y0 : ind, True.
Definition term0 (x0 : ind) := dest_num (mk_num x0).
Definition term98 (x0 : nat -> Prop) (x1 : nat) := True -> x0 x1.
Definition term27 (x0 : nat -> Prop) (x1 : ind) := (fun y0 : ind => (fun y1 : ind => (NUM_REP y1) /\ (x0 (mk_num y1))) y0) x1.
Definition term23 (x0 : nat -> Prop) := (NUM_REP IND_0) /\ (x0 (mk_num IND_0)).
Definition term2 (x0 : nat) := mk_num (IND_SUC (dest_num x0)).
Definition term33 (x0 : nat -> Prop) (x1 : ind) := (fun y0 : ind => (NUM_REP y0) /\ (x0 (mk_num y0))) (IND_SUC x1).
Definition term6 (x0 : ind) := NUM_REP (IND_SUC x0).
Definition term80 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => (x0 y0) -> x0 (S y0)) x1.
Definition term99 (x0 : nat -> Prop) (x1 : nat) := imp ((NUM_REP (dest_num x1)) -> (NUM_REP (dest_num x1)) /\ (x0 (mk_num (dest_num x1)))).
Definition term59 (x0 : nat -> Prop) (x1 : ind) := (fun y0 : ind => ((NUM_REP y0) /\ (x0 (mk_num y0))) -> (NUM_REP (IND_SUC y0)) /\ (x0 (mk_num (IND_SUC y0)))) x1.
Definition term17 (x0 : nat -> Prop) := (fun y0 : ind => (NUM_REP y0) /\ (x0 (mk_num y0))) IND_0.
Definition term94 (x0 : nat) := and (NUM_REP (dest_num x0)).
Definition term91 (x0 : nat) := @eq ind (dest_num (mk_num (dest_num x0))).
Definition term26 (x0 : nat -> Prop) := and ((fun y0 : ind => (NUM_REP y0) /\ (x0 (mk_num y0))) IND_0).
Definition term49 (x0 : nat -> Prop) (x1 : ind) := (NUM_REP x1) -> (NUM_REP x1) /\ (x0 (mk_num x1)).
Definition term44 (x0 : nat -> Prop) := True /\ (forall y0 : ind, ((NUM_REP y0) /\ (x0 (mk_num y0))) -> (NUM_REP (IND_SUC y0)) /\ (x0 (mk_num (IND_SUC y0)))).
Definition term78 (x0 : ind) := @eq nat (mk_num (IND_SUC x0)).
Definition term58 (x0 : nat -> Prop) (x1 : nat) := ((forall y0 : ind, ((NUM_REP y0) /\ (x0 (mk_num y0))) -> (NUM_REP (IND_SUC y0)) /\ (x0 (mk_num (IND_SUC y0)))) -> forall y0 : ind, (NUM_REP y0) -> (NUM_REP y0) /\ (x0 (mk_num y0))) -> x0 x1.
Definition term82 (x0 : nat -> Prop) (x1 : nat) := x0 (S x1).
Definition term52 (x0 : nat -> Prop) := forall y0 : ind, (NUM_REP y0) -> (fun y1 : ind => (NUM_REP y1) /\ (x0 (mk_num y1))) y0.
Definition term29 (x0 : nat -> Prop) (x1 : ind) := @eq Prop ((fun y0 : ind => (NUM_REP y0) /\ (x0 (mk_num y0))) x1).
Definition term60 := fun y0 : ind => True.
Definition term88 (x0 : nat) := NUM_REP (dest_num x0).
Definition term20 (x0 : nat -> Prop) := fun y0 : ind => (fun y1 : ind => (NUM_REP y1) /\ (x0 (mk_num y1))) y0.
Definition term50 (x0 : nat -> Prop) := fun y0 : ind => (NUM_REP y0) -> (fun y1 : ind => (NUM_REP y1) /\ (x0 (mk_num y1))) y0.
Definition term3 := forall y0 : ind, (NUM_REP y0) -> NUM_REP (IND_SUC y0).
Definition term93 (x0 : nat) := imp (NUM_REP (dest_num x0)).
Definition term37 (x0 : nat -> Prop) (x1 : ind) := ((fun y0 : ind => (NUM_REP y0) /\ (x0 (mk_num y0))) x1) -> (fun y0 : ind => (NUM_REP y0) /\ (x0 (mk_num y0))) (IND_SUC x1).
Definition term11 (x0 : nat -> Prop) := (((fun y0 : ind => (NUM_REP y0) /\ (x0 (mk_num y0))) IND_0) /\ (forall y0 : ind, ((fun y1 : ind => (NUM_REP y1) /\ (x0 (mk_num y1))) y0) -> (fun y1 : ind => (NUM_REP y1) /\ (x0 (mk_num y1))) (IND_SUC y0))) -> forall y0 : ind, (NUM_REP y0) -> (fun y1 : ind => (NUM_REP y1) /\ (x0 (mk_num y1))) y0.
Definition term13 (x0 : nat -> Prop) := forall y0 : nat, (x0 y0) -> x0 (S y0).
Definition term32 (x0 : nat -> Prop) (x1 : ind) := (fun y0 : ind => (fun y1 : ind => (NUM_REP y1) /\ (x0 (mk_num y1))) y0) (IND_SUC x1).
Definition term21 (x0 : nat -> Prop) := @eq Prop ((fun y0 : ind => (fun y1 : ind => (NUM_REP y1) /\ (x0 (mk_num y1))) y0) IND_0).
Definition term90 (x0 : nat) := mk_num (dest_num x0).
Definition term15 (x0 : ind -> Prop) (x1 : ind) := (fun y0 : ind => x0 y0) x1.
Definition term64 (x0 : nat -> Prop) := True -> forall y0 : ind, (NUM_REP y0) -> (NUM_REP y0) /\ (x0 (mk_num y0)).
Definition term48 (x0 : nat -> Prop) (x1 : ind) := (NUM_REP x1) -> (fun y0 : ind => (NUM_REP y0) /\ (x0 (mk_num y0))) x1.
Definition term103 (x0 : nat -> Prop) := forall y0 : nat, x0 y0.
Definition term84 (x0 : nat -> Prop) := (forall y0 : nat, (x0 y0) -> x0 (S y0)) -> forall y0 : nat, (x0 y0) -> x0 (S y0).
Definition term92 (x0 : nat) := @eq ind (dest_num x0).
