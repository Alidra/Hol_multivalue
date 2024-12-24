Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FORALL_UNION_OF_term_abbrevs.
Require Import thm4845732_spec.
Require Import thm4848608_spec.
Lemma lem4848609 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term0 _111301 P Q R) = (term1 _111301 P Q R).
Proof. exact (EQ_MP (@lem4845732 _111301 P Q R) (@lem4848608 _111301 P Q R)). Qed.
