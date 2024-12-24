Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1100049 : forall {_25287 : Type'}, (@NULL _25287) = (@ε ((prod nat (prod nat (prod nat nat))) -> (list _25287) -> Prop) (fun NULL' : (prod nat (prod nat (prod nat nat))) -> (list _25287) -> Prop => forall _17966 : prod nat (prod nat (prod nat nat)), ((NULL' _17966 (@nil _25287)) = True) /\ (forall h : _25287, forall t : list _25287, (NULL' _17966 (@cons _25287 h t)) = False)) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))))))).
