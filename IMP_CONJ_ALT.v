Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import IMP_CONJ_ALT_term_abbrevs.
Require Import thm951_spec.
Require Import thm952_spec.
Lemma lem953 (q : Prop) (p : Prop) (r : Prop) : (term0 p q r) = (term1 q p r).
Proof. exact (EQ_MP (@lem952 q p r) (@lem951 p q r)). Qed.
