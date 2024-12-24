Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem8099922 : forall {_143642 _143649 : Type'} (r : _143649 -> _143642 -> Prop) (s : _143649 -> _143642 -> Prop) (x : _143649), (@COND _143642 (@ex1 _143642 (@COND (_143642 -> Prop) (exists y : _143642, r x y) (r x) (s x))) (@ε _143642 (@COND (_143642 -> Prop) (exists y : _143642, r x y) (r x) (s x))) (@ε _143642 (fun z : _143642 => False))) = (@COND _143642 (exists y : _143642, r x y) (@COND _143642 (@ex1 _143642 (r x)) (@ε _143642 (r x)) (@ε _143642 (fun z : _143642 => False))) (@COND _143642 (@ex1 _143642 (s x)) (@ε _143642 (s x)) (@ε _143642 (fun z : _143642 => False)))).
