Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm8058953_term_abbrevs.
Lemma lem8058953 {_143118 _143154 _143158 _143159 : Type'} (f : _143159) (x : _143158) : (term0 _143118 _143154 _143158 _143159 f x) = ((@CASEWISE _143118 _143154 _143158 _143159 (@nil (prod (_143154 -> _143158) (_143159 -> _143154 -> _143118))) f x) = (term1 _143118)).
Proof. exact (eq_refl (term0 _143118 _143154 _143158 _143159 f x)). Qed.
