Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3464394 : forall {_89769 _89788 _89789 : Type'}, forall P : _89789 -> _89788 -> Prop, forall f : _89789 -> _89788 -> _89769 -> Prop, (@INTERS _89769 (@GSPEC (_89769 -> Prop) (fun GEN_PVAR_57 : _89769 -> Prop => exists x : _89789, exists y : _89788, @SETSPEC (_89769 -> Prop) GEN_PVAR_57 (P x y) (f x y)))) = (@GSPEC _89769 (fun GEN_PVAR_58 : _89769 => exists a : _89769, @SETSPEC _89769 GEN_PVAR_58 (forall x : _89789, forall y : _89788, (P x y) -> @IN _89769 a (f x y)) a)).
