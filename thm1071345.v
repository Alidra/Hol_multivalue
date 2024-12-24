Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1071345_term_abbrevs.
Require Import thm1070451_spec.
Lemma lem1071334 {A : Type'} : (term0 A) = (term0 A).
Proof. exact (eq_refl (term0 A)). Qed.
Lemma lem1071335 {A : Type'} (CONS' : type1399 A) (h1 : CONS' = (term1 A)) : (term2 A CONS') = (term3 A).
Proof. exact (MK_COMB (@lem1071334 A) (@lem1070451 A CONS' h1)). Qed.
Lemma lem1071336 {A : Type'} : (term3 A) = (term4 A).
Proof. exact (eq_refl (term3 A)). Qed.
Lemma lem1071337 {A : Type'} (CONS' : type1399 A) : (term5 A CONS') = (term5 A CONS').
Proof. exact (eq_refl (term5 A CONS')). Qed.
Lemma lem1071338 {A : Type'} (CONS' : type1399 A) : ((term2 A CONS') = (term3 A)) = ((term2 A CONS') = (term4 A)).
Proof. exact (MK_COMB (@lem1071337 A CONS') (@lem1071336 A)). Qed.
Lemma lem1071339 {A : Type'} (CONS' : type1399 A) : (term2 A CONS') = (term6 A CONS').
Proof. exact (eq_refl (term2 A CONS')). Qed.
Lemma lem1071340 {A : Type'} : (@eq (A -> (list A) -> list A)) = (@eq (A -> (list A) -> list A)).
Proof. exact (eq_refl (@eq (A -> (list A) -> list A))). Qed.
Lemma lem1071341 {A : Type'} (CONS' : type1399 A) : (term5 A CONS') = (term7 A CONS').
Proof. exact (MK_COMB (@lem1071340 A) (@lem1071339 A CONS')). Qed.
Lemma lem1071342 {A : Type'} : (term4 A) = (term4 A).
Proof. exact (eq_refl (term4 A)). Qed.
Lemma lem1071343 {A : Type'} (CONS' : type1399 A) : ((term2 A CONS') = (term4 A)) = ((term6 A CONS') = (term4 A)).
Proof. exact (MK_COMB (@lem1071341 A CONS') (@lem1071342 A)). Qed.
Lemma lem1071344 {A : Type'} (CONS' : type1399 A) : ((term2 A CONS') = (term3 A)) = ((term6 A CONS') = (term4 A)).
Proof. exact (TRANS (@lem1071338 A CONS') (@lem1071343 A CONS')). Qed.
Lemma lem1071345 {A : Type'} (CONS' : type1399 A) (h1 : CONS' = (term1 A)) : (term6 A CONS') = (term4 A).
Proof. exact (EQ_MP (@lem1071344 A CONS') (@lem1071335 A CONS' h1)). Qed.
