Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem155635 : (fun r : (prod nat (prod nat nat)) -> nat -> nat -> nat => forall _3087 : prod nat (prod nat nat), forall m : nat, forall n : nat, @COND Prop (n = (NUMERAL 0)) (((Nat.div m n) = (NUMERAL 0)) /\ ((r _3087 m n) = m)) ((m = (Nat.add (Nat.mul (Nat.div m n) n) (r _3087 m n))) /\ (Peano.lt (r _3087 m n) n))) (@ε ((prod nat (prod nat nat)) -> nat -> nat -> nat) (fun r : (prod nat (prod nat nat)) -> nat -> nat -> nat => forall _3087 : prod nat (prod nat nat), forall m : nat, forall n : nat, @COND Prop (n = (NUMERAL 0)) (((Nat.div m n) = (NUMERAL 0)) /\ ((r _3087 m n) = m)) ((m = (Nat.add (Nat.mul (Nat.div m n) n) (r _3087 m n))) /\ (Peano.lt (r _3087 m n) n)))).
