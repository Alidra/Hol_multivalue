Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_ABS_NUM_term_abbrevs.
Require Import LE_0_spec.
Require Import real_abs_spec.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm1340282_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Lemma lem1362864 (n : nat) : term0 n.
Proof. exact (@lem91499 n). Qed.
Lemma lem1362865 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem1362866 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem1362865 n) (@lem1362864 n)). Qed.
Lemma lem1362867 (n : nat) : (term1 n) = ((term1 n) = True).
Proof. exact (@lem7 (term1 n)). Qed.
Lemma lem1362869 (m : nat) : term2 m.
Proof. exact (@lem1340282 m). Qed.
Lemma lem1362870 (m : nat) : (term2 m) = (term3 m).
Proof. exact (eq_refl (term2 m)). Qed.
Lemma lem1362871 (m : nat) : term3 m.
Proof. exact (EQ_MP (@lem1362870 m) (@lem1362869 m)). Qed.
Lemma lem1362872 (m : nat) (n : nat) : term4 m n.
Proof. exact (@lem1362871 m n). Qed.
Lemma lem1362873 (m : nat) (n : nat) : (term4 m n) = ((term5 m n) = (Peano.le m n)).
Proof. exact (eq_refl (term4 m n)). Qed.
Lemma lem1362875 (x : real) : term6 x.
Proof. exact (@lem1343359 x). Qed.
Lemma lem1362876 (x : real) : (term6 x) = ((real_abs x) = (term7 x)).
Proof. exact (eq_refl (term6 x)). Qed.
Lemma lem1362885 (x : real) : (real_abs x) = (term7 x).
Proof. exact (EQ_MP (@lem1362876 x) (@lem1362875 x)). Qed.
Lemma lem1362886 (n : nat) : (term8 n) = (term9 n).
Proof. exact (@lem1362885 (real_of_num n)). Qed.
Lemma lem1362888 (m : nat) (n : nat) : (term5 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem1362873 m n) (@lem1362872 m n)). Qed.
Lemma lem1362889 (n : nat) : (term10 n) = (term1 n).
Proof. exact (@lem1362888 (NUMERAL 0) n). Qed.
Lemma lem1362891 (n : nat) : (term1 n) = True.
Proof. exact (EQ_MP (@lem1362867 n) (@lem1362866 n)). Qed.
Lemma lem1362892 (n : nat) : (term10 n) = True.
Proof. exact (TRANS (@lem1362889 n) (@lem1362891 n)). Qed.
Lemma lem1362893 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1362894 (n : nat) : (term11 n) = (@COND real True).
Proof. exact (MK_COMB (@lem1362893) (@lem1362892 n)). Qed.
Lemma lem1362895 (n : nat) : (real_of_num n) = (real_of_num n).
Proof. exact (eq_refl (real_of_num n)). Qed.
Lemma lem1362896 (n : nat) : (term12 n) = (term13 n).
Proof. exact (MK_COMB (@lem1362894 n) (@lem1362895 n)). Qed.
Lemma lem1362897 (n : nat) : (term14 n) = (term14 n).
Proof. exact (eq_refl (term14 n)). Qed.
Lemma lem1362898 (n : nat) : (term9 n) = (term15 n).
Proof. exact (MK_COMB (@lem1362896 n) (@lem1362897 n)). Qed.
Lemma lem1362900 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1362901 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1362900 real t2 t1). Qed.
Lemma lem1362902 (n : nat) : (term15 n) = (real_of_num n).
Proof. exact (@lem1362901 (term14 n) (real_of_num n)). Qed.
Lemma lem1362903 (n : nat) : (term9 n) = (real_of_num n).
Proof. exact (TRANS (@lem1362898 n) (@lem1362902 n)). Qed.
Lemma lem1362904 (n : nat) : (term8 n) = (real_of_num n).
Proof. exact (TRANS (@lem1362886 n) (@lem1362903 n)). Qed.
Lemma lem1362905 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1362906 (n : nat) : (term16 n) = (term17 n).
Proof. exact (MK_COMB (@lem1362905) (@lem1362904 n)). Qed.
Lemma lem1362907 (n : nat) : (real_of_num n) = (real_of_num n).
Proof. exact (eq_refl (real_of_num n)). Qed.
Lemma lem1362908 (n : nat) : ((term8 n) = (real_of_num n)) = ((real_of_num n) = (real_of_num n)).
Proof. exact (MK_COMB (@lem1362906 n) (@lem1362907 n)). Qed.
Lemma lem1362910 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1362911 (x : real) : (x = x) = True.
Proof. exact (@lem1362910 real x). Qed.
Lemma lem1362912 (n : nat) : ((real_of_num n) = (real_of_num n)) = True.
Proof. exact (@lem1362911 (real_of_num n)). Qed.
Lemma lem1362913 (n : nat) : ((term8 n) = (real_of_num n)) = True.
Proof. exact (TRANS (@lem1362908 n) (@lem1362912 n)). Qed.
Lemma lem1362914 : term18 = term19.
Proof. exact (fun_ext (fun n : nat => @lem1362913 n)). Qed.
Lemma lem1362915 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1362916 : term20 = term21.
Proof. exact (MK_COMB (@lem1362915) (@lem1362914)). Qed.
Lemma lem1362918 {A : Type'} (t : Prop) : (term22 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1362919 (t : Prop) : (term23 t) = t.
Proof. exact (@lem1362918 nat t). Qed.
Lemma lem1362920 : term21 = True.
Proof. exact (@lem1362919 True). Qed.
Lemma lem1362921 : term20 = True.
Proof. exact (TRANS (@lem1362916) (@lem1362920)). Qed.
Lemma lem1362922 : True = term20.
Proof. exact (SYM (@lem1362921)). Qed.
Lemma lem1362923 : term20.
Proof. exact (EQ_MP (@lem1362922) (@lem0)). Qed.
