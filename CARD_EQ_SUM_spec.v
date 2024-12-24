Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7158078 : forall {_134012 : Type'}, forall s : _134012 -> Prop, (@FINITE _134012 s) -> (real_of_num (@CARD _134012 s)) = (@sum _134012 s (fun x : _134012 => real_of_num (NUMERAL (BIT1 0)))).
