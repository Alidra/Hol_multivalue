Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6970340 : forall {_127848 : Type'}, forall f : _127848 -> nat, forall s : _127848 -> Prop, (@FINITE _127848 s) -> (@nsum _127848 s (fun x : _127848 => @COND nat (@IN _127848 x s) (f x) (NUMERAL 0))) = (@nsum _127848 s f).
