Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1100408 : forall {_25307 : Type'}, (fun ALL' : (prod nat (prod nat nat)) -> (_25307 -> Prop) -> (list _25307) -> Prop => forall _17973 : prod nat (prod nat nat), (forall P : _25307 -> Prop, (ALL' _17973 P (@nil _25307)) = True) /\ (forall h : _25307, forall P : _25307 -> Prop, forall t : list _25307, (ALL' _17973 P (@cons _25307 h t)) = ((P h) /\ (ALL' _17973 P t)))) (@ε ((prod nat (prod nat nat)) -> (_25307 -> Prop) -> (list _25307) -> Prop) (fun ALL' : (prod nat (prod nat nat)) -> (_25307 -> Prop) -> (list _25307) -> Prop => forall _17973 : prod nat (prod nat nat), (forall P : _25307 -> Prop, (ALL' _17973 P (@nil _25307)) = True) /\ (forall h : _25307, forall P : _25307 -> Prop, forall t : list _25307, (ALL' _17973 P (@cons _25307 h t)) = ((P h) /\ (ALL' _17973 P t))))).
