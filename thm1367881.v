Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1367881_term_abbrevs.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1367847 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1367848 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1367847 real t2 t1). Qed.
Lemma lem1367849 (y : real) (x : real) : (@COND real True x y) = x.
Proof. exact (@lem1367848 y x). Qed.
Lemma lem1367850 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1367851 (y : real) (x : real) : (term0 x y) = (@eq real x).
Proof. exact (MK_COMB (@lem1367850) (@lem1367849 y x)). Qed.
Lemma lem1367852 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1367853 (y : real) (x : real) : ((@COND real True x y) = x) = (x = x).
Proof. exact (MK_COMB (@lem1367851 y x) (@lem1367852 x)). Qed.
Lemma lem1367855 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1367856 (x : real) : (x = x) = True.
Proof. exact (@lem1367855 real x). Qed.
Lemma lem1367857 (y : real) (x : real) : ((@COND real True x y) = x) = True.
Proof. exact (TRANS (@lem1367853 y x) (@lem1367856 x)). Qed.
Lemma lem1367858 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1367859 (y : real) (x : real) : (term1 y x) = (and True).
Proof. exact (MK_COMB (@lem1367858) (@lem1367857 y x)). Qed.
Lemma lem1367863 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1367864 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1367863 real t1 t2). Qed.
Lemma lem1367865 (x : real) (y : real) : (@COND real False x y) = y.
Proof. exact (@lem1367864 x y). Qed.
Lemma lem1367866 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1367867 (x : real) (y : real) : (term2 x y) = (@eq real y).
Proof. exact (MK_COMB (@lem1367866) (@lem1367865 x y)). Qed.
Lemma lem1367868 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1367869 (x : real) (y : real) : ((@COND real False x y) = y) = (y = y).
Proof. exact (MK_COMB (@lem1367867 x y) (@lem1367868 y)). Qed.
Lemma lem1367871 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1367872 (x : real) : (x = x) = True.
Proof. exact (@lem1367871 real x). Qed.
Lemma lem1367873 (y : real) : (y = y) = True.
Proof. exact (@lem1367872 y). Qed.
Lemma lem1367874 (x : real) (y : real) : ((@COND real False x y) = y) = True.
Proof. exact (TRANS (@lem1367869 x y) (@lem1367873 y)). Qed.
Lemma lem1367875 (x : real) (y : real) : (term3 x y) = (True /\ True).
Proof. exact (MK_COMB (@lem1367859 y x) (@lem1367874 x y)). Qed.
Lemma lem1367877 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1367878 : (True /\ True) = True.
Proof. exact (@lem1367877 True). Qed.
Lemma lem1367879 (x : real) (y : real) : (term3 x y) = True.
Proof. exact (TRANS (@lem1367875 x y) (@lem1367878)). Qed.
Lemma lem1367880 (x : real) (y : real) : True = (term3 x y).
Proof. exact (SYM (@lem1367879 x y)). Qed.
Lemma lem1367881 (x : real) (y : real) : term3 x y.
Proof. exact (EQ_MP (@lem1367880 x y) (@lem0)). Qed.
