Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1148178 : forall {_27039 _27046 : Type'}, forall P : _27039 -> Prop, forall f : _27046 -> _27039, forall l : list _27046, (@FILTER _27039 P (@List.map _27046 _27039 f l)) = (@List.map _27046 _27039 f (@FILTER _27046 (@o _27046 _27039 Prop P f) l)).
