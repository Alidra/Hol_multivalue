Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7085323 : forall {_132484 : Type'}, forall c : real, forall s : _132484 -> Prop, (@FINITE _132484 s) -> (@sum _132484 s (fun n : _132484 => c)) = (real_mul (real_of_num (@CARD _132484 s)) c).
