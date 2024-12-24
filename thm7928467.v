Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7928467_term_abbrevs.
Require Import thm7928136_spec.
Lemma lem7928456 {A : Type'} : (term0 A) = (term0 A).
Proof. exact (eq_refl (term0 A)). Qed.
Lemma lem7928457 {A : Type'} (_103802' : type39 A) (h1 : _103802' = (term1 A)) : (term2 A _103802') = (term3 A).
Proof. exact (MK_COMB (@lem7928456 A) (@lem7928136 A _103802' h1)). Qed.
Lemma lem7928458 {A : Type'} : (term3 A) = (term4 A).
Proof. exact (eq_refl (term3 A)). Qed.
Lemma lem7928459 {A : Type'} (_103802' : type39 A) : (term5 A _103802') = (term5 A _103802').
Proof. exact (eq_refl (term5 A _103802')). Qed.
Lemma lem7928460 {A : Type'} (_103802' : type39 A) : ((term2 A _103802') = (term3 A)) = ((term2 A _103802') = (term4 A)).
Proof. exact (MK_COMB (@lem7928459 A _103802') (@lem7928458 A)). Qed.
Lemma lem7928461 {A : Type'} (_103802' : type39 A) : (term2 A _103802') = (term6 A _103802').
Proof. exact (eq_refl (term2 A _103802')). Qed.
Lemma lem7928462 {A : Type'} : (@eq ((finite_sum (finite_sum A A) unit) -> tybit1 A)) = (@eq ((finite_sum (finite_sum A A) unit) -> tybit1 A)).
Proof. exact (eq_refl (@eq ((finite_sum (finite_sum A A) unit) -> tybit1 A))). Qed.
Lemma lem7928463 {A : Type'} (_103802' : type39 A) : (term5 A _103802') = (term7 A _103802').
Proof. exact (MK_COMB (@lem7928462 A) (@lem7928461 A _103802')). Qed.
Lemma lem7928464 {A : Type'} : (term4 A) = (term4 A).
Proof. exact (eq_refl (term4 A)). Qed.
Lemma lem7928465 {A : Type'} (_103802' : type39 A) : ((term2 A _103802') = (term4 A)) = ((term6 A _103802') = (term4 A)).
Proof. exact (MK_COMB (@lem7928463 A _103802') (@lem7928464 A)). Qed.
Lemma lem7928466 {A : Type'} (_103802' : type39 A) : ((term2 A _103802') = (term3 A)) = ((term6 A _103802') = (term4 A)).
Proof. exact (TRANS (@lem7928460 A _103802') (@lem7928465 A _103802')). Qed.
Lemma lem7928467 {A : Type'} (_103802' : type39 A) (h1 : _103802' = (term1 A)) : (term6 A _103802') = (term4 A).
Proof. exact (EQ_MP (@lem7928466 A _103802') (@lem7928457 A _103802' h1)). Qed.
