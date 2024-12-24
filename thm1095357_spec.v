Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1095357 : forall {A : Type'}, (@tl A) = (@ε ((prod nat nat) -> (list A) -> list A) (fun TL' : (prod nat nat) -> (list A) -> list A => forall _17931 : prod nat nat, forall h : A, forall t : list A, (TL' _17931 (@cons A h t)) = t) (@pair nat nat (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))))).
