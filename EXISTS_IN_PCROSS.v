Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EXISTS_IN_PCROSS_term_abbrevs.
Require Import thm0_spec.
Require Import thm8004099_spec.
Lemma lem8004100 {_141895 _141896 _141897 : Type'} (s : type24 _141895 _141896) (t : type24 _141895 _141897) (P : type16 _141895 _141896 _141897) : (term0 _141895 _141896 _141897 s t P) = (term1 _141895 _141896 _141897 s t P).
Proof. exact (EQ_MP (@lem8004099 _141895 _141896 _141897 s t P) (@lem0)). Qed.
