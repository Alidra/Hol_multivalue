Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem8058954 : forall {_143118 _143154 _143158 _143159 : Type'} (f : _143159) (x : _143158), (@CASEWISE _143118 _143154 _143158 _143159 (@nil (prod (_143154 -> _143158) (_143159 -> _143154 -> _143118))) f x) = (@ε _143118 (fun y : _143118 => True)).