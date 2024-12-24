Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4907451 : forall {_112866 : Type'}, forall l : list _112866, (@HAS_SIZE _112866 (@set_of_list _112866 l) (@List.length _112866 l)) = (@List.ForallOrdPairs _112866 (fun x : _112866 => fun y : _112866 => ~ (x = y)) l).
