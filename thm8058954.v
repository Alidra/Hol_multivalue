Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm8058954_term_abbrevs.
Require Import thm8058952_spec.
Require Import thm8058953_spec.
Lemma lem8058954 {_143118 _143154 _143158 _143159 : Type'} (f : _143159) (x : _143158) : (@CASEWISE _143118 _143154 _143158 _143159 (@nil (prod (_143154 -> _143158) (_143159 -> _143154 -> _143118))) f x) = (term0 _143118).
Proof. exact (EQ_MP (@lem8058953 _143118 _143154 _143158 _143159 f x) (@lem8058952 _143118 _143154 _143158 _143159 f x)). Qed.
