Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INFINITE_UNIV_PAIR_term_abbrevs.
Require Import thm0_spec.
Require Import thm1834_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4333782_spec.
Require Import thm4334154_spec.
Lemma lem4334183 {A B : Type'} : (@INFINITE (prod A B) (@UNIV (prod A B))) = (term0 A B).
Proof. exact (EQ_MP (@lem4333782 A B) (@lem4334154 A B)). Qed.
Lemma lem4334184 {A : Type'} : (@INFINITE (prod A A) (@UNIV (prod A A))) = (term1 A).
Proof. exact (@lem4334183 A A). Qed.
Lemma lem4334186 (t : Prop) : (t \/ t) = t.
Proof. exact (proj2 (@lem1834 t)). Qed.
Lemma lem4334187 {A : Type'} : (term1 A) = (@INFINITE A (@UNIV A)).
Proof. exact (@lem4334186 (@INFINITE A (@UNIV A))). Qed.
Lemma lem4334190 {A : Type'} : (@INFINITE (prod A A) (@UNIV (prod A A))) = (@INFINITE A (@UNIV A)).
Proof. exact (TRANS (@lem4334184 A) (@lem4334187 A)). Qed.
Lemma lem4334191 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4334192 {A : Type'} : (term2 A) = (term3 A).
Proof. exact (MK_COMB (@lem4334191) (@lem4334190 A)). Qed.
Lemma lem4334195 {A : Type'} : (@INFINITE A (@UNIV A)) = (@INFINITE A (@UNIV A)).
Proof. exact (eq_refl (@INFINITE A (@UNIV A))). Qed.
Lemma lem4334196 {A : Type'} : ((@INFINITE (prod A A) (@UNIV (prod A A))) = (@INFINITE A (@UNIV A))) = ((@INFINITE A (@UNIV A)) = (@INFINITE A (@UNIV A))).
Proof. exact (MK_COMB (@lem4334192 A) (@lem4334195 A)). Qed.
Lemma lem4334198 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4334199 (x : Prop) : (x = x) = True.
Proof. exact (@lem4334198 Prop x). Qed.
Lemma lem4334200 {A : Type'} : ((@INFINITE A (@UNIV A)) = (@INFINITE A (@UNIV A))) = True.
Proof. exact (@lem4334199 (@INFINITE A (@UNIV A))). Qed.
Lemma lem4334201 {A : Type'} : ((@INFINITE (prod A A) (@UNIV (prod A A))) = (@INFINITE A (@UNIV A))) = True.
Proof. exact (TRANS (@lem4334196 A) (@lem4334200 A)). Qed.
Lemma lem4334202 {A : Type'} : True = ((@INFINITE (prod A A) (@UNIV (prod A A))) = (@INFINITE A (@UNIV A))).
Proof. exact (SYM (@lem4334201 A)). Qed.
Lemma lem4334203 {A : Type'} : (@INFINITE (prod A A) (@UNIV (prod A A))) = (@INFINITE A (@UNIV A)).
Proof. exact (EQ_MP (@lem4334202 A) (@lem0)). Qed.
