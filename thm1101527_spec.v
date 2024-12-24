Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1101527 : forall {_25328 : Type'}, (@EX _25328) = (@ε ((prod nat nat) -> (_25328 -> Prop) -> (list _25328) -> Prop) (fun EX' : (prod nat nat) -> (_25328 -> Prop) -> (list _25328) -> Prop => forall _17980 : prod nat nat, (forall P : _25328 -> Prop, (EX' _17980 P (@nil _25328)) = False) /\ (forall h : _25328, forall P : _25328 -> Prop, forall t : list _25328, (EX' _17980 P (@cons _25328 h t)) = ((P h) \/ (EX' _17980 P t)))) (@pair nat nat (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))))).
