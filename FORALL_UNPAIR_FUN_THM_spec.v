Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem54977 : forall {_5621 _5630 _5631 : Type'}, forall P : (_5621 -> _5630) -> (_5621 -> _5631) -> Prop, (forall f : _5621 -> _5630, forall g : _5621 -> _5631, P f g) = (forall h : _5621 -> prod _5630 _5631, P (@o _5621 (prod _5630 _5631) _5630 (@fst _5630 _5631) h) (@o _5621 (prod _5630 _5631) _5631 (@snd _5630 _5631) h)).
