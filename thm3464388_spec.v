Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3464388 : forall {_89837 _89861 _89862 _89863 : Type'}, forall P : _89863 -> _89862 -> _89861 -> Prop, forall f : _89863 -> _89862 -> _89861 -> _89837 -> Prop, (@INTERS _89837 (@GSPEC (_89837 -> Prop) (fun GEN_PVAR_59 : _89837 -> Prop => exists x : _89863, exists y : _89862, exists z : _89861, @SETSPEC (_89837 -> Prop) GEN_PVAR_59 (P x y z) (f x y z)))) = (@GSPEC _89837 (fun GEN_PVAR_60 : _89837 => exists a : _89837, @SETSPEC _89837 GEN_PVAR_60 (forall x : _89863, forall y : _89862, forall z : _89861, (P x y z) -> @IN _89837 a (f x y z)) a)).
