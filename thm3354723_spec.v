Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3354723 : forall {_87240 : Type'} (s : _87240 -> Prop), (forall x : _87240, (@IN _87240 x (@INTERS _87240 (@INSERT (_87240 -> Prop) s (@EMPTY (_87240 -> Prop))))) = (@IN _87240 x s)) = ((@INTERS _87240 (@INSERT (_87240 -> Prop) s (@EMPTY (_87240 -> Prop)))) = s).
