Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem8002422 : forall {_141774 _141775 _141776 : Type'}, forall P : (cart _141774 _141775) -> (cart _141774 _141776) -> Prop, forall a : cart _141774 _141775, forall b : cart _141774 _141776, (@IN (cart _141774 (finite_sum _141775 _141776)) (@pastecart _141774 _141775 _141776 a b) (@GSPEC (cart _141774 (finite_sum _141775 _141776)) (fun GEN_PVAR_360 : cart _141774 (finite_sum _141775 _141776) => exists x : cart _141774 _141775, exists y : cart _141774 _141776, @SETSPEC (cart _141774 (finite_sum _141775 _141776)) GEN_PVAR_360 (P x y) (@pastecart _141774 _141775 _141776 x y)))) = (P a b).
