Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import PCROSS_INTERS_term_abbrevs.
Require Import thm8057189_spec.
Require Import thm8057199_spec.
Lemma lem8057212 {_143007 _143008 _143009 _143061 _143062 _143063 : Type'} : term0 _143007 _143008 _143009 _143061 _143062 _143063.
Proof. exact (conj (@lem8057199 _143007 _143008 _143009) (@lem8057189 _143061 _143062 _143063)). Qed.
