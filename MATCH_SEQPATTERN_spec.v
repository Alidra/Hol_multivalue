Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem8099923 : forall {_143642 _143649 : Type'} (r : _143649 -> _143642 -> Prop) (x : _143649) (s : _143649 -> _143642 -> Prop), (@_MATCH _143649 _143642 x (@_SEQPATTERN _143642 _143649 r s)) = (@COND _143642 (exists y : _143642, r x y) (@_MATCH _143649 _143642 x r) (@_MATCH _143649 _143642 x s)).
