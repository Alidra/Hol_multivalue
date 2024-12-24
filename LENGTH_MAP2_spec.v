Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1189023 : forall {_27740 _27742 _27753 : Type'}, forall f : _27740 -> _27742 -> _27753, forall l : list _27740, forall m : list _27742, ((@List.length _27740 l) = (@List.length _27742 m)) -> (@List.length _27753 (@MAP2 _27753 _27740 _27742 f l m)) = (@List.length _27742 m).
