Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CASEWISE_DEF_term_abbrevs.
Require Import thm8058954_spec.
Require Import thm8058964_spec.
Require Import thm8058965_spec.
Lemma lem8058966 {_143118 _143154 _143158 _143159 : Type'} (h : type1644 _143118 _143154 _143158 _143159) (t : type1633 _143118 _143154 _143158 _143159) (f : _143159) (x : _143158) : (term0 _143118 _143154 _143158 _143159 h t f x) = (term1 _143118 _143154 _143158 _143159 h t f x).
Proof. exact (EQ_MP (@lem8058965 _143118 _143154 _143158 _143159 h t f x) (@lem8058964 _143118 _143154 _143158 _143159 h t f x)). Qed.
Lemma lem8058967 {_143118 _143154 _143158 _143159 : Type'} (h : type1644 _143118 _143154 _143158 _143159) (t : type1633 _143118 _143154 _143158 _143159) (f : _143159) (x : _143158) : term2 _143118 _143154 _143158 _143159 h t f x.
Proof. exact (conj (@lem8058954 _143118 _143154 _143158 _143159 f x) (@lem8058966 _143118 _143154 _143158 _143159 h t f x)). Qed.
