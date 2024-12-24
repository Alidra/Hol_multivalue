Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_OF_NUM_MAX_term_abbrevs.
Require Import COND_RAND_spec.
Require Import MAX_spec.
Require Import real_max_spec.
Require Import thm0_spec.
Require Import thm1340282_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1483798 {A B : Type'} (b : Prop) (x : A) (f : A -> B) (y : A) (h1 : (term0 A B f b x y) = (term1 A B b x f y)) : (term0 A B f b x y) = (term1 A B b x f y).
Proof. exact (h1). Qed.
Lemma lem1483799 {A B : Type'} (b : Prop) (x : A) (f : A -> B) (y : A) (h1 : (term0 A B f b x y) = (term1 A B b x f y)) : (term1 A B b x f y) = (term0 A B f b x y).
Proof. exact (SYM (@lem1483798 A B b x f y h1)). Qed.
Lemma lem1483800 {A B : Type'} (f : A -> B) (b : Prop) (x : A) (y : A) (h1 : (term1 A B b x f y) = (term0 A B f b x y)) : (term1 A B b x f y) = (term0 A B f b x y).
Proof. exact (h1). Qed.
Lemma lem1483801 {A B : Type'} (f : A -> B) (b : Prop) (x : A) (y : A) (h1 : (term1 A B b x f y) = (term0 A B f b x y)) : (term0 A B f b x y) = (term1 A B b x f y).
Proof. exact (SYM (@lem1483800 A B f b x y h1)). Qed.
Lemma lem1483802 {A B : Type'} (f : A -> B) (b : Prop) (x : A) (y : A) : ((term0 A B f b x y) = (term1 A B b x f y)) = ((term1 A B b x f y) = (term0 A B f b x y)).
Proof. exact (prop_ext (fun h1 : (term0 A B f b x y) = (term1 A B b x f y) => @lem1483799 A B b x f y h1) (fun h1 : (term1 A B b x f y) = (term0 A B f b x y) => @lem1483801 A B f b x y h1)). Qed.
Lemma lem1483803 {A B : Type'} (f : A -> B) (b : Prop) (x : A) : (term2 A B b x f) = (term3 A B f b x).
Proof. exact (fun_ext (fun y : A => @lem1483802 A B f b x y)). Qed.
Lemma lem1483804 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1483805 {A B : Type'} (f : A -> B) (b : Prop) (x : A) : (term4 A B b x f) = (term5 A B f b x).
Proof. exact (MK_COMB (@lem1483804 A) (@lem1483803 A B f b x)). Qed.
Lemma lem1483806 {A B : Type'} (f : A -> B) (b : Prop) : (term6 A B b f) = (term7 A B f b).
Proof. exact (fun_ext (fun x : A => @lem1483805 A B f b x)). Qed.
Lemma lem1483807 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1483808 {A B : Type'} (f : A -> B) (b : Prop) : (term8 A B b f) = (term9 A B f b).
Proof. exact (MK_COMB (@lem1483807 A) (@lem1483806 A B f b)). Qed.
Lemma lem1483809 {A B : Type'} (b : Prop) : (term10 A B b) = (term11 A B b).
Proof. exact (fun_ext (fun f : A -> B => @lem1483808 A B f b)). Qed.
Lemma lem1483810 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem1483811 {A B : Type'} (b : Prop) : (term12 A B b) = (term13 A B b).
Proof. exact (MK_COMB (@lem1483810 A B) (@lem1483809 A B b)). Qed.
Lemma lem1483812 {A B : Type'} : (term14 A B) = (term15 A B).
Proof. exact (fun_ext (fun b : Prop => @lem1483811 A B b)). Qed.
Lemma lem1483813 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem1483814 {A B : Type'} : (term16 A B) = (term17 A B).
Proof. exact (MK_COMB (@lem1483813) (@lem1483812 A B)). Qed.
Lemma lem1483815 {A B : Type'} : term17 A B.
Proof. exact (EQ_MP (@lem1483814 A B) (@lem12958 A B)). Qed.
Lemma lem1483816 {A B : Type'} (b : Prop) : term18 A B b.
Proof. exact (@lem1483815 A B b). Qed.
Lemma lem1483817 {A B : Type'} (b : Prop) : (term18 A B b) = (term13 A B b).
Proof. exact (eq_refl (term18 A B b)). Qed.
Lemma lem1483818 {A B : Type'} (b : Prop) : term13 A B b.
Proof. exact (EQ_MP (@lem1483817 A B b) (@lem1483816 A B b)). Qed.
Lemma lem1483819 {A B : Type'} (b : Prop) (f : A -> B) : term19 A B b f.
Proof. exact (@lem1483818 A B b f). Qed.
Lemma lem1483820 {A B : Type'} (f : A -> B) (b : Prop) : (term19 A B b f) = (term9 A B f b).
Proof. exact (eq_refl (term19 A B b f)). Qed.
Lemma lem1483821 {A B : Type'} (f : A -> B) (b : Prop) : term9 A B f b.
Proof. exact (EQ_MP (@lem1483820 A B f b) (@lem1483819 A B b f)). Qed.
Lemma lem1483822 {A B : Type'} (f : A -> B) (b : Prop) (x : A) : term20 A B f b x.
Proof. exact (@lem1483821 A B f b x). Qed.
Lemma lem1483823 {A B : Type'} (f : A -> B) (b : Prop) (x : A) : (term20 A B f b x) = (term5 A B f b x).
Proof. exact (eq_refl (term20 A B f b x)). Qed.
Lemma lem1483824 {A B : Type'} (f : A -> B) (b : Prop) (x : A) : term5 A B f b x.
Proof. exact (EQ_MP (@lem1483823 A B f b x) (@lem1483822 A B f b x)). Qed.
Lemma lem1483825 {A B : Type'} (f : A -> B) (b : Prop) (x : A) (y : A) : term21 A B f b x y.
Proof. exact (@lem1483824 A B f b x y). Qed.
Lemma lem1483826 {A B : Type'} (f : A -> B) (b : Prop) (x : A) (y : A) : (term21 A B f b x y) = ((term1 A B b x f y) = (term0 A B f b x y)).
Proof. exact (eq_refl (term21 A B f b x y)). Qed.
Lemma lem1483828 (n : real) : term22 n.
Proof. exact (@lem1345564 n). Qed.
Lemma lem1483829 (n : real) : (term22 n) = (term23 n).
Proof. exact (eq_refl (term22 n)). Qed.
Lemma lem1483830 (n : real) : term23 n.
Proof. exact (EQ_MP (@lem1483829 n) (@lem1483828 n)). Qed.
Lemma lem1483831 (n : real) (m : real) : term24 n m.
Proof. exact (@lem1483830 n m). Qed.
Lemma lem1483832 (n : real) (m : real) : (term24 n m) = ((real_max m n) = (term25 n m)).
Proof. exact (eq_refl (term24 n m)). Qed.
Lemma lem1483834 (m : nat) : term26 m.
Proof. exact (@lem90708 m). Qed.
Lemma lem1483835 (m : nat) : (term26 m) = (term27 m).
Proof. exact (eq_refl (term26 m)). Qed.
Lemma lem1483836 (m : nat) : term27 m.
Proof. exact (EQ_MP (@lem1483835 m) (@lem1483834 m)). Qed.
Lemma lem1483837 (m : nat) (n : nat) : term28 m n.
Proof. exact (@lem1483836 m n). Qed.
Lemma lem1483838 (n : nat) (m : nat) : (term28 m n) = ((Nat.max m n) = (term29 n m)).
Proof. exact (eq_refl (term28 m n)). Qed.
Lemma lem1483840 (m : nat) : term30 m.
Proof. exact (@lem1340282 m). Qed.
Lemma lem1483841 (m : nat) : (term30 m) = (term31 m).
Proof. exact (eq_refl (term30 m)). Qed.
Lemma lem1483842 (m : nat) : term31 m.
Proof. exact (EQ_MP (@lem1483841 m) (@lem1483840 m)). Qed.
Lemma lem1483843 (m : nat) (n : nat) : term32 m n.
Proof. exact (@lem1483842 m n). Qed.
Lemma lem1483844 (m : nat) (n : nat) : (term32 m n) = ((term33 m n) = (Peano.le m n)).
Proof. exact (eq_refl (term32 m n)). Qed.
Lemma lem1483857 (n : real) (m : real) : (real_max m n) = (term25 n m).
Proof. exact (EQ_MP (@lem1483832 n m) (@lem1483831 n m)). Qed.
Lemma lem1483858 (n : nat) (m : nat) : (term34 m n) = (term35 n m).
Proof. exact (@lem1483857 (real_of_num n) (real_of_num m)). Qed.
Lemma lem1483860 {A B : Type'} (f : A -> B) (b : Prop) (x : A) (y : A) : (term1 A B b x f y) = (term0 A B f b x y).
Proof. exact (EQ_MP (@lem1483826 A B f b x y) (@lem1483825 A B f b x y)). Qed.
Lemma lem1483861 (f : nat -> real) (b : Prop) (x : nat) (y : nat) : (term36 b x f y) = (term37 f b x y).
Proof. exact (@lem1483860 nat real f b x y). Qed.
Lemma lem1483862 (n : nat) (m : nat) : (term35 n m) = (term38 n m).
Proof. exact (@lem1483861 real_of_num (term33 m n) n m). Qed.
Lemma lem1483863 (n : nat) (m : nat) : (term34 m n) = (term38 n m).
Proof. exact (TRANS (@lem1483858 n m) (@lem1483862 n m)). Qed.
Lemma lem1483867 (m : nat) (n : nat) : (term33 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem1483844 m n) (@lem1483843 m n)). Qed.
Lemma lem1483868 : (@COND nat) = (@COND nat).
Proof. exact (eq_refl (@COND nat)). Qed.
Lemma lem1483869 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (MK_COMB (@lem1483868) (@lem1483867 m n)). Qed.
Lemma lem1483870 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1483871 (m : nat) (n : nat) : (term41 m n) = (term42 m n).
Proof. exact (MK_COMB (@lem1483869 m n) (@lem1483870 n)). Qed.
Lemma lem1483872 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem1483873 (n : nat) (m : nat) : (term43 n m) = (term29 n m).
Proof. exact (MK_COMB (@lem1483871 m n) (@lem1483872 m)). Qed.
Lemma lem1483876 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1483877 (n : nat) (m : nat) : (term38 n m) = (term44 n m).
Proof. exact (MK_COMB (@lem1483876) (@lem1483873 n m)). Qed.
Lemma lem1483878 (n : nat) (m : nat) : (term34 m n) = (term44 n m).
Proof. exact (TRANS (@lem1483863 n m) (@lem1483877 n m)). Qed.
Lemma lem1483879 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1483880 (n : nat) (m : nat) : (term45 m n) = (term46 n m).
Proof. exact (MK_COMB (@lem1483879) (@lem1483878 n m)). Qed.
Lemma lem1483882 (n : nat) (m : nat) : (Nat.max m n) = (term29 n m).
Proof. exact (EQ_MP (@lem1483838 n m) (@lem1483837 m n)). Qed.
Lemma lem1483885 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1483886 (n : nat) (m : nat) : (term47 m n) = (term44 n m).
Proof. exact (MK_COMB (@lem1483885) (@lem1483882 n m)). Qed.
Lemma lem1483887 (n : nat) (m : nat) : ((term34 m n) = (term47 m n)) = ((term44 n m) = (term44 n m)).
Proof. exact (MK_COMB (@lem1483880 n m) (@lem1483886 n m)). Qed.
Lemma lem1483889 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1483890 (x : real) : (x = x) = True.
Proof. exact (@lem1483889 real x). Qed.
Lemma lem1483891 (n : nat) (m : nat) : ((term44 n m) = (term44 n m)) = True.
Proof. exact (@lem1483890 (term44 n m)). Qed.
Lemma lem1483892 (m : nat) (n : nat) : ((term34 m n) = (term47 m n)) = True.
Proof. exact (TRANS (@lem1483887 n m) (@lem1483891 n m)). Qed.
Lemma lem1483893 (m : nat) : (term48 m) = term49.
Proof. exact (fun_ext (fun n : nat => @lem1483892 m n)). Qed.
Lemma lem1483894 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1483895 (m : nat) : (term50 m) = term51.
Proof. exact (MK_COMB (@lem1483894) (@lem1483893 m)). Qed.
Lemma lem1483897 {A : Type'} (t : Prop) : (term52 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1483898 (t : Prop) : (term53 t) = t.
Proof. exact (@lem1483897 nat t). Qed.
Lemma lem1483899 : term51 = True.
Proof. exact (@lem1483898 True). Qed.
Lemma lem1483900 (m : nat) : (term50 m) = True.
Proof. exact (TRANS (@lem1483895 m) (@lem1483899)). Qed.
Lemma lem1483901 : term54 = term49.
Proof. exact (fun_ext (fun m : nat => @lem1483900 m)). Qed.
Lemma lem1483902 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1483903 : term55 = term51.
Proof. exact (MK_COMB (@lem1483902) (@lem1483901)). Qed.
Lemma lem1483905 {A : Type'} (t : Prop) : (term52 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1483906 (t : Prop) : (term53 t) = t.
Proof. exact (@lem1483905 nat t). Qed.
Lemma lem1483907 : term51 = True.
Proof. exact (@lem1483906 True). Qed.
Lemma lem1483908 : term55 = True.
Proof. exact (TRANS (@lem1483903) (@lem1483907)). Qed.
Lemma lem1483909 : True = term55.
Proof. exact (SYM (@lem1483908)). Qed.
Lemma lem1483910 : term55.
Proof. exact (EQ_MP (@lem1483909) (@lem0)). Qed.
