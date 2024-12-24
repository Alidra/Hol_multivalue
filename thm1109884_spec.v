Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1109884 : forall {_25786 _25787 : Type'} (h : _25787) (f : _25787 -> _25786 -> Prop) (t : list _25787) (l : list _25786), (fun l' : list _25786 => (@ALLPAIRS _25786 _25787 f (@cons _25787 h t) l') = ((@List.Forall _25786 (f h) l') /\ (@ALLPAIRS _25786 _25787 f t l'))) l.
