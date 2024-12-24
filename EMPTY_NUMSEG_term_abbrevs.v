Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term10 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term8 (x0 : nat) := forall y0 : nat, (Peano.lt y0 x0) -> (dotdot x0 y0) = (@EMPTY nat).
Definition term13 := forall y0 : nat, forall y1 : nat, (Peano.lt y1 y0) -> (dotdot y0 y1) = (@EMPTY nat).
Definition term5 (x0 : nat) (x1 : nat) := (Peano.lt x0 x1) -> Peano.lt x0 x1.
Definition term9 := forall y0 : nat, True.
Definition term7 := fun y0 : nat => True.
Definition term6 (x0 : nat) := fun y0 : nat => (Peano.lt y0 x0) -> (dotdot x0 y0) = (@EMPTY nat).
Definition term3 (x0 : nat) (x1 : nat) := imp (Peano.lt x0 x1).
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((dotdot y0 y1) = (@EMPTY nat)) = (Peano.lt y1 y0)) x0.
Definition term1 (x0 : nat) := forall y0 : nat, ((dotdot x0 y0) = (@EMPTY nat)) = (Peano.lt y0 x0).
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((dotdot x0 y0) = (@EMPTY nat)) = (Peano.lt y0 x0)) x1.
Definition term11 (x0 : Prop) := forall y0 : nat, x0.
Definition term4 (x0 : nat) (x1 : nat) := (Peano.lt x1 x0) -> (dotdot x0 x1) = (@EMPTY nat).
Definition term12 := fun y0 : nat => forall y1 : nat, (Peano.lt y1 y0) -> (dotdot y0 y1) = (@EMPTY nat).
