Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1099685 : forall {_25287 : Type'}, (fun NULL' : (prod nat (prod nat (prod nat nat))) -> (list _25287) -> Prop => forall _17966 : prod nat (prod nat (prod nat nat)), ((NULL' _17966 (@nil _25287)) = True) /\ (forall h : _25287, forall t : list _25287, (NULL' _17966 (@cons _25287 h t)) = False)) (@ε ((prod nat (prod nat (prod nat nat))) -> (list _25287) -> Prop) (fun NULL' : (prod nat (prod nat (prod nat nat))) -> (list _25287) -> Prop => forall _17966 : prod nat (prod nat (prod nat nat)), ((NULL' _17966 (@nil _25287)) = True) /\ (forall h : _25287, forall t : list _25287, (NULL' _17966 (@cons _25287 h t)) = False))).
