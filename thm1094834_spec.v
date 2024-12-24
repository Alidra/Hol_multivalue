Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1094834 : forall {A : Type'}, (@hd A) = (@ε ((prod nat nat) -> (list A) -> A) (fun HD' : (prod nat nat) -> (list A) -> A => forall _17927 : prod nat nat, forall t : list A, forall h : A, (HD' _17927 (@cons A h t)) = h) (@pair nat nat (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))))).
