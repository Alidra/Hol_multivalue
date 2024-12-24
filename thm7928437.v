Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7928437_term_abbrevs.
Require Import thm7928136_spec.
Lemma lem7928424 {A : Type'} (tybit1' : type1329 A) (_103802' : type39 A) (h1 : tybit1' = (term0 A _103802')) : tybit1' = (term0 A _103802').
Proof. exact (h1). Qed.
Lemma lem7928425 {A : Type'} : (term1 A) = (term1 A).
Proof. exact (eq_refl (term1 A)). Qed.
Lemma lem7928426 {A : Type'} (_103802' : type39 A) (h1 : _103802' = (term2 A)) : (term3 A _103802') = (term4 A).
Proof. exact (MK_COMB (@lem7928425 A) (@lem7928136 A _103802' h1)). Qed.
Lemma lem7928427 {A : Type'} : (term4 A) = (term5 A).
Proof. exact (eq_refl (term4 A)). Qed.
Lemma lem7928428 {A : Type'} (_103802' : type39 A) : (term6 A _103802') = (term6 A _103802').
Proof. exact (eq_refl (term6 A _103802')). Qed.
Lemma lem7928429 {A : Type'} (_103802' : type39 A) : ((term3 A _103802') = (term4 A)) = ((term3 A _103802') = (term5 A)).
Proof. exact (MK_COMB (@lem7928428 A _103802') (@lem7928427 A)). Qed.
Lemma lem7928430 {A : Type'} (_103802' : type39 A) : (term3 A _103802') = (term0 A _103802').
Proof. exact (eq_refl (term3 A _103802')). Qed.
Lemma lem7928431 {A : Type'} : (@eq ((recspace (finite_sum (finite_sum A A) unit)) -> Prop)) = (@eq ((recspace (finite_sum (finite_sum A A) unit)) -> Prop)).
Proof. exact (eq_refl (@eq ((recspace (finite_sum (finite_sum A A) unit)) -> Prop))). Qed.
Lemma lem7928432 {A : Type'} (_103802' : type39 A) : (term6 A _103802') = (term7 A _103802').
Proof. exact (MK_COMB (@lem7928431 A) (@lem7928430 A _103802')). Qed.
Lemma lem7928433 {A : Type'} : (term5 A) = (term5 A).
Proof. exact (eq_refl (term5 A)). Qed.
Lemma lem7928434 {A : Type'} (_103802' : type39 A) : ((term3 A _103802') = (term5 A)) = ((term0 A _103802') = (term5 A)).
Proof. exact (MK_COMB (@lem7928432 A _103802') (@lem7928433 A)). Qed.
Lemma lem7928435 {A : Type'} (_103802' : type39 A) : ((term3 A _103802') = (term4 A)) = ((term0 A _103802') = (term5 A)).
Proof. exact (TRANS (@lem7928429 A _103802') (@lem7928434 A _103802')). Qed.
Lemma lem7928436 {A : Type'} (_103802' : type39 A) (h1 : _103802' = (term2 A)) : (term0 A _103802') = (term5 A).
Proof. exact (EQ_MP (@lem7928435 A _103802') (@lem7928426 A _103802' h1)). Qed.
Lemma lem7928437 {A : Type'} (tybit1' : type1329 A) (_103802' : type39 A) (h1 : _103802' = (term2 A)) (h2 : tybit1' = (term0 A _103802')) : tybit1' = (term5 A).
Proof. exact (TRANS (@lem7928424 A tybit1' _103802' h2) (@lem7928436 A _103802' h1)). Qed.
