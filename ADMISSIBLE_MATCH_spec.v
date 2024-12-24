Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem8150397 : forall {_144104 _144105 _144106 _144138 _144141 P : Type'}, forall lt2 : _144105 -> _144104 -> Prop, forall p : (_144105 -> _144106) -> P -> Prop, forall s : P -> _144104, forall e : (_144105 -> _144106) -> P -> _144141, forall c : (_144105 -> _144106) -> P -> _144141 -> _144138 -> Prop, ((@admissible _144104 _144106 _144105 _144141 P lt2 p s e) /\ (@admissible _144104 _144106 _144105 (_144138 -> Prop) P lt2 p s (fun f : _144105 -> _144106 => fun x : P => c f x (e f x)))) -> @admissible _144104 _144106 _144105 _144138 P lt2 p s (fun f : _144105 -> _144106 => fun x : P => @_MATCH _144141 _144138 (e f x) (c f x)).
