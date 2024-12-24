Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm8058965_term_abbrevs.
Lemma lem8058965 {_143118 _143154 _143158 _143159 : Type'} (h : type1644 _143118 _143154 _143158 _143159) (t : type1633 _143118 _143154 _143158 _143159) (f : _143159) (x : _143158) : (term0 _143118 _143154 _143158 _143159 h t f x) = ((term1 _143118 _143154 _143158 _143159 h t f x) = (term2 _143118 _143154 _143158 _143159 h t f x)).
Proof. exact (eq_refl (term0 _143118 _143154 _143158 _143159 h t f x)). Qed.
