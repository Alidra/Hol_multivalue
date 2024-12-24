Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem55166 : forall {_5658 _5667 _5668 : Type'}, forall P : (_5658 -> _5667) -> (_5658 -> _5668) -> Prop, (exists f : _5658 -> _5667, exists g : _5658 -> _5668, P f g) = (exists h : _5658 -> prod _5667 _5668, P (@o _5658 (prod _5667 _5668) _5667 (@fst _5667 _5668) h) (@o _5658 (prod _5667 _5668) _5668 (@snd _5667 _5668) h)).
