Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm8058952_term_abbrevs.
Require Import thm8058946_spec.
Lemma lem8058948 {_143118 _143154 _143158 _143159 : Type'} : term0 _143118 _143154 _143158 _143159.
Proof. exact (proj1 (@lem8058946 _143118 _143154 _143158 _143159)). Qed.
Lemma lem8058949 {_143118 _143154 _143158 _143159 : Type'} (f : _143159) : term1 _143118 _143154 _143158 _143159 f.
Proof. exact (@lem8058948 _143118 _143154 _143158 _143159 f). Qed.
Lemma lem8058950 {_143118 _143154 _143158 _143159 : Type'} (f : _143159) : (term1 _143118 _143154 _143158 _143159 f) = (term2 _143118 _143154 _143158 _143159 f).
Proof. exact (eq_refl (term1 _143118 _143154 _143158 _143159 f)). Qed.
Lemma lem8058951 {_143118 _143154 _143158 _143159 : Type'} (f : _143159) : term2 _143118 _143154 _143158 _143159 f.
Proof. exact (EQ_MP (@lem8058950 _143118 _143154 _143158 _143159 f) (@lem8058949 _143118 _143154 _143158 _143159 f)). Qed.
Lemma lem8058952 {_143118 _143154 _143158 _143159 : Type'} (f : _143159) (x : _143158) : term3 _143118 _143154 _143158 _143159 f x.
Proof. exact (@lem8058951 _143118 _143154 _143158 _143159 f x). Qed.
