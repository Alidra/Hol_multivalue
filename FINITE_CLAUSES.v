Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_CLAUSES_term_abbrevs.
Require Import FINITE_1_spec.
Require Import FINITE_TYBIT0_spec.
Require Import FINITE_TYBIT1_spec.
Require Import thm0_spec.
Require Import thm1842_spec.
Require Import thm7_spec.
Lemma lem7936823 {A : Type'} : (@FINITE (tybit1 A) (@UNIV (tybit1 A))) = ((@FINITE (tybit1 A) (@UNIV (tybit1 A))) = True).
Proof. exact (@lem7 (@FINITE (tybit1 A) (@UNIV (tybit1 A)))). Qed.
Lemma lem7936825 {A : Type'} : (@FINITE (tybit0 A) (@UNIV (tybit0 A))) = ((@FINITE (tybit0 A) (@UNIV (tybit0 A))) = True).
Proof. exact (@lem7 (@FINITE (tybit0 A) (@UNIV (tybit0 A)))). Qed.
Lemma lem7936827 : (@FINITE unit (@UNIV unit)) = ((@FINITE unit (@UNIV unit)) = True).
Proof. exact (@lem7 (@FINITE unit (@UNIV unit))). Qed.
Lemma lem7936836 : (@FINITE unit (@UNIV unit)) = True.
Proof. exact (EQ_MP (@lem7936827) (@lem7933973)). Qed.
Lemma lem7936837 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7936838 : term0 = (and True).
Proof. exact (MK_COMB (@lem7936837) (@lem7936836)). Qed.
Lemma lem7936844 {A : Type'} : (@FINITE (tybit0 A) (@UNIV (tybit0 A))) = True.
Proof. exact (EQ_MP (@lem7936825 A) (@lem7935382 A)). Qed.
Lemma lem7936845 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7936846 {A : Type'} : (term1 A) = (and True).
Proof. exact (MK_COMB (@lem7936845) (@lem7936844 A)). Qed.
Lemma lem7936848 {A : Type'} : (@FINITE (tybit1 A) (@UNIV (tybit1 A))) = True.
Proof. exact (EQ_MP (@lem7936823 A) (@lem7936822 A)). Qed.
Lemma lem7936849 {A : Type'} : (term2 A) = (True /\ True).
Proof. exact (MK_COMB (@lem7936846 A) (@lem7936848 A)). Qed.
Lemma lem7936851 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7936852 : (True /\ True) = True.
Proof. exact (@lem7936851 True). Qed.
Lemma lem7936853 {A : Type'} : (term2 A) = True.
Proof. exact (TRANS (@lem7936849 A) (@lem7936852)). Qed.
Lemma lem7936854 {A : Type'} : (term3 A) = (True /\ True).
Proof. exact (MK_COMB (@lem7936838) (@lem7936853 A)). Qed.
Lemma lem7936856 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7936857 : (True /\ True) = True.
Proof. exact (@lem7936856 True). Qed.
Lemma lem7936858 {A : Type'} : (term3 A) = True.
Proof. exact (TRANS (@lem7936854 A) (@lem7936857)). Qed.
Lemma lem7936859 {A : Type'} : True = (term3 A).
Proof. exact (SYM (@lem7936858 A)). Qed.
Lemma lem7936860 {A : Type'} : term3 A.
Proof. exact (EQ_MP (@lem7936859 A) (@lem0)). Qed.
