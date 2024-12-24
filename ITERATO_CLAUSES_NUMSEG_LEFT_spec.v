Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6897351 : forall {A : Type'}, forall dom : A -> Prop, forall neut : A, forall op : A -> A -> A, forall f : nat -> A, forall m : nat, forall n : nat, (@iterato A nat dom neut op Peano.le (dotdot m n) f) = (@COND A (Peano.le m n) (@COND A ((@IN A (f m) dom) -> (f m) = neut) (@iterato A nat dom neut op Peano.le (dotdot (Nat.add m (NUMERAL (BIT1 0))) n) f) (op (f m) (@iterato A nat dom neut op Peano.le (dotdot (Nat.add m (NUMERAL (BIT1 0))) n) f))) neut).
