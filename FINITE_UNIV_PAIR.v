Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_UNIV_PAIR_term_abbrevs.
Require Import thm0_spec.
Require Import thm1845_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4333669_spec.
Lemma lem4334159 {A B : Type'} : (@FINITE (prod A B) (@UNIV (prod A B))) = (term0 A B).
Proof. exact (EQ_MP (@lem4333669 A B) (@lem0)). Qed.
Lemma lem4334160 {A : Type'} : (@FINITE (prod A A) (@UNIV (prod A A))) = (term1 A).
Proof. exact (@lem4334159 A A). Qed.
Lemma lem4334162 (t : Prop) : (t /\ t) = t.
Proof. exact (proj2 (@lem1845 t)). Qed.
Lemma lem4334163 {A : Type'} : (term1 A) = (@FINITE A (@UNIV A)).
Proof. exact (@lem4334162 (@FINITE A (@UNIV A))). Qed.
Lemma lem4334166 {A : Type'} : (@FINITE (prod A A) (@UNIV (prod A A))) = (@FINITE A (@UNIV A)).
Proof. exact (TRANS (@lem4334160 A) (@lem4334163 A)). Qed.
Lemma lem4334167 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4334168 {A : Type'} : (term2 A) = (term3 A).
Proof. exact (MK_COMB (@lem4334167) (@lem4334166 A)). Qed.
Lemma lem4334171 {A : Type'} : (@FINITE A (@UNIV A)) = (@FINITE A (@UNIV A)).
Proof. exact (eq_refl (@FINITE A (@UNIV A))). Qed.
Lemma lem4334172 {A : Type'} : ((@FINITE (prod A A) (@UNIV (prod A A))) = (@FINITE A (@UNIV A))) = ((@FINITE A (@UNIV A)) = (@FINITE A (@UNIV A))).
Proof. exact (MK_COMB (@lem4334168 A) (@lem4334171 A)). Qed.
Lemma lem4334174 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4334175 (x : Prop) : (x = x) = True.
Proof. exact (@lem4334174 Prop x). Qed.
Lemma lem4334176 {A : Type'} : ((@FINITE A (@UNIV A)) = (@FINITE A (@UNIV A))) = True.
Proof. exact (@lem4334175 (@FINITE A (@UNIV A))). Qed.
Lemma lem4334177 {A : Type'} : ((@FINITE (prod A A) (@UNIV (prod A A))) = (@FINITE A (@UNIV A))) = True.
Proof. exact (TRANS (@lem4334172 A) (@lem4334176 A)). Qed.
Lemma lem4334178 {A : Type'} : True = ((@FINITE (prod A A) (@UNIV (prod A A))) = (@FINITE A (@UNIV A))).
Proof. exact (SYM (@lem4334177 A)). Qed.
Lemma lem4334179 {A : Type'} : (@FINITE (prod A A) (@UNIV (prod A A))) = (@FINITE A (@UNIV A)).
Proof. exact (EQ_MP (@lem4334178 A) (@lem0)). Qed.
