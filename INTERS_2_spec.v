Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3356566 : forall {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop), (@INTERS _87260 (@INSERT (_87260 -> Prop) s (@INSERT (_87260 -> Prop) t (@EMPTY (_87260 -> Prop))))) = (@INTER _87260 s t).
