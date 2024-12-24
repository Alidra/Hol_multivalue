Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem302783 : forall (m : nat) (n : nat), (m = n) = ((S (Nat.add m m)) = (Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) n) (NUMERAL (BIT1 0)))).
