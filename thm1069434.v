Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1069434_term_abbrevs.
Require Import thm1069015_spec.
Lemma lem1069423 {A : Type'} : (term0 A) = (term0 A).
Proof. exact (eq_refl (term0 A)). Qed.
Lemma lem1069424 {A : Type'} (NONE' : recspace A) (h1 : NONE' = (term1 A)) : (term2 A NONE') = (term3 A).
Proof. exact (MK_COMB (@lem1069423 A) (@lem1069015 A NONE' h1)). Qed.
Lemma lem1069425 {A : Type'} : (term3 A) = (term4 A).
Proof. exact (eq_refl (term3 A)). Qed.
Lemma lem1069426 {A : Type'} (NONE' : recspace A) : (term5 A NONE') = (term5 A NONE').
Proof. exact (eq_refl (term5 A NONE')). Qed.
Lemma lem1069427 {A : Type'} (NONE' : recspace A) : ((term2 A NONE') = (term3 A)) = ((term2 A NONE') = (term4 A)).
Proof. exact (MK_COMB (@lem1069426 A NONE') (@lem1069425 A)). Qed.
Lemma lem1069428 {A : Type'} (NONE' : recspace A) : (term2 A NONE') = (@_mk_option A NONE').
Proof. exact (eq_refl (term2 A NONE')). Qed.
Lemma lem1069429 {A : Type'} : (@eq (option A)) = (@eq (option A)).
Proof. exact (eq_refl (@eq (option A))). Qed.
Lemma lem1069430 {A : Type'} (NONE' : recspace A) : (term5 A NONE') = (term6 A NONE').
Proof. exact (MK_COMB (@lem1069429 A) (@lem1069428 A NONE')). Qed.
Lemma lem1069431 {A : Type'} : (term4 A) = (term4 A).
Proof. exact (eq_refl (term4 A)). Qed.
Lemma lem1069432 {A : Type'} (NONE' : recspace A) : ((term2 A NONE') = (term4 A)) = ((@_mk_option A NONE') = (term4 A)).
Proof. exact (MK_COMB (@lem1069430 A NONE') (@lem1069431 A)). Qed.
Lemma lem1069433 {A : Type'} (NONE' : recspace A) : ((term2 A NONE') = (term3 A)) = ((@_mk_option A NONE') = (term4 A)).
Proof. exact (TRANS (@lem1069427 A NONE') (@lem1069432 A NONE')). Qed.
Lemma lem1069434 {A : Type'} (NONE' : recspace A) (h1 : NONE' = (term1 A)) : (@_mk_option A NONE') = (term4 A).
Proof. exact (EQ_MP (@lem1069433 A NONE') (@lem1069424 A NONE' h1)). Qed.
