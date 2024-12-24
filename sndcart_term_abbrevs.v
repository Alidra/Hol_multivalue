Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type2 a0 a1 a2) := @lambda a0 a2 (fun y0 : nat => @dollar a0 (finite_sum a1 a2) x0 (Nat.add y0 (@dimindex a1 (@UNIV a1)))).
Definition term4 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type2 a0 a1 a2) := (fun y0 : type2 a0 a1 a2 => (@sndcart a0 a1 a2 y0) = (@lambda a0 a2 (fun y1 : nat => @dollar a0 (finite_sum a1 a2) y0 (Nat.add y1 (@dimindex a1 (@UNIV a1)))))) x0.
Definition term1 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type2 a0 a1 a2) := (fun y0 : type2 a0 a1 a2 => @lambda a0 a2 (fun y1 : nat => @dollar a0 (finite_sum a1 a2) y0 (Nat.add y1 (@dimindex a1 (@UNIV a1))))) x0.
Definition term0 (a0 : Type') (a1 : Type') (a2 : Type') := fun y0 : type2 a0 a1 a2 => @lambda a0 a2 (fun y1 : nat => @dollar a0 (finite_sum a1 a2) y0 (Nat.add y1 (@dimindex a1 (@UNIV a1)))).
Definition term3 (a0 : Type') (a1 : Type') (a2 : Type') := forall y0 : type2 a0 a1 a2, (@sndcart a0 a1 a2 y0) = (@lambda a0 a2 (fun y1 : nat => @dollar a0 (finite_sum a1 a2) y0 (Nat.add y1 (@dimindex a1 (@UNIV a1))))).
