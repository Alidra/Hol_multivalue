Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7659572 : forall {_140390 _140392 _140395 : Type'}, forall z : cart _140395 (finite_sum _140392 _140390), (@pastecart _140395 _140392 _140390 (@fstcart _140395 _140392 _140390 z) (@sndcart _140395 _140392 _140390 z)) = z.
