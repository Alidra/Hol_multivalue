Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem8059078 : forall {_143170 _143178 _143179 _143218 _143219 _143221 : Type'} (t : _143219 -> _143221 -> _143179) (s : _143221 -> _143218) (clauses : list (prod (_143221 -> _143218) (_143219 -> _143221 -> _143179))) (f : _143219) (x : _143218), ((@CASEWISE _143178 _143170 _143218 _143219 (@nil (prod (_143170 -> _143218) (_143219 -> _143170 -> _143178))) f x) = (@ε _143178 (fun y : _143178 => True))) /\ ((@CASEWISE _143179 _143221 _143218 _143219 (@cons (prod (_143221 -> _143218) (_143219 -> _143221 -> _143179)) (@pair (_143221 -> _143218) (_143219 -> _143221 -> _143179) s t) clauses) f x) = (@COND _143179 (exists y : _143221, (s y) = x) (t f (@ε _143221 (fun y : _143221 => (s y) = x))) (@CASEWISE _143179 _143221 _143218 _143219 clauses f x))).