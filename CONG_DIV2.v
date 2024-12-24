Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CONG_DIV2_term_abbrevs.
Require Import CONG_spec.
Require Import DIV_MOD_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Lemma lem3070800 (m : nat) : term0 m.
Proof. exact (@lem227406 m). Qed.
Lemma lem3070801 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem3070802 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem3070801 m) (@lem3070800 m)). Qed.
Lemma lem3070803 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem3070802 m n). Qed.
Lemma lem3070804 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem3070805 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem3070804 m n) (@lem3070803 m n)). Qed.
Lemma lem3070806 (m : nat) (n : nat) (p : nat) : term4 m n p.
Proof. exact (@lem3070805 m n p). Qed.
Lemma lem3070807 (m : nat) (p : nat) (n : nat) : (term4 m n p) = ((term5 m n p) = (term6 m p n)).
Proof. exact (eq_refl (term4 m n p)). Qed.
Lemma lem3070809 (x : nat) : term7 x.
Proof. exact (@lem3070637 x). Qed.
Lemma lem3070810 (x : nat) : (term7 x) = (term8 x).
Proof. exact (eq_refl (term7 x)). Qed.
Lemma lem3070811 (x : nat) : term8 x.
Proof. exact (EQ_MP (@lem3070810 x) (@lem3070809 x)). Qed.
Lemma lem3070812 (x : nat) (y : nat) : term9 x y.
Proof. exact (@lem3070811 x y). Qed.
Lemma lem3070813 (x : nat) (y : nat) : (term9 x y) = (term10 x y).
Proof. exact (eq_refl (term9 x y)). Qed.
Lemma lem3070814 (x : nat) (y : nat) : term10 x y.
Proof. exact (EQ_MP (@lem3070813 x y) (@lem3070812 x y)). Qed.
Lemma lem3070815 (x : nat) (y : nat) (n : nat) : term11 x y n.
Proof. exact (@lem3070814 x y n). Qed.
Lemma lem3070816 (x : nat) (y : nat) (n : nat) : (term11 x y n) = ((term12 x y n) = ((Nat.modulo x n) = (Nat.modulo y n))).
Proof. exact (eq_refl (term11 x y n)). Qed.
Lemma lem3070837 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term13 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem3070838 (p : Prop) (q : Prop) (p' : Prop) : term14 p q p'.
Proof. exact (fun q' : Prop => @lem3070837 p q p' q'). Qed.
Lemma lem3070839 (p : Prop) (q : Prop) : term15 p q.
Proof. exact (fun p' : Prop => @lem3070838 p q p'). Qed.
Lemma lem3070840 (a : nat) (b : nat) (m : nat) (n : nat) : term16 a b m n.
Proof. exact (@lem3070839 (term17 a b m n) (term18 a b m n)). Qed.
Lemma lem3070841 (a : nat) (b : nat) (m : nat) (n : nat) (p' : Prop) : term19 a b m n p'.
Proof. exact (@lem3070840 a b m n p'). Qed.
Lemma lem3070842 (a : nat) (b : nat) (m : nat) (n : nat) (p' : Prop) : (term19 a b m n p') = (term20 a b m n p').
Proof. exact (eq_refl (term19 a b m n p')). Qed.
Lemma lem3070843 (a : nat) (b : nat) (m : nat) (n : nat) (p' : Prop) : term20 a b m n p'.
Proof. exact (EQ_MP (@lem3070842 a b m n p') (@lem3070841 a b m n p')). Qed.
Lemma lem3070844 (a : nat) (b : nat) (m : nat) (n : nat) (p' : Prop) (q' : Prop) : term21 a b m n p' q'.
Proof. exact (@lem3070843 a b m n p' q'). Qed.
Lemma lem3070845 (a : nat) (b : nat) (m : nat) (n : nat) (p' : Prop) (q' : Prop) : (term21 a b m n p' q') = (term22 a b m n p' q').
Proof. exact (eq_refl (term21 a b m n p' q')). Qed.
Lemma lem3070846 (a : nat) (b : nat) (m : nat) (n : nat) (p' : Prop) (q' : Prop) : term22 a b m n p' q'.
Proof. exact (EQ_MP (@lem3070845 a b m n p' q') (@lem3070844 a b m n p' q')). Qed.
Lemma lem3070848 (x : nat) (y : nat) (n : nat) : (term12 x y n) = ((Nat.modulo x n) = (Nat.modulo y n)).
Proof. exact (EQ_MP (@lem3070816 x y n) (@lem3070815 x y n)). Qed.
Lemma lem3070849 (a : nat) (b : nat) (m : nat) (n : nat) : (term17 a b m n) = ((term23 a m n) = (term23 b m n)).
Proof. exact (@lem3070848 a b (Nat.mul m n)). Qed.
Lemma lem3070852 (a : nat) (b : nat) (m : nat) (n : nat) (q' : Prop) : term24 a b m n q'.
Proof. exact (@lem3070846 a b m n ((term23 a m n) = (term23 b m n)) q'). Qed.
Lemma lem3070853 (a : nat) (b : nat) (m : nat) (n : nat) (q' : Prop) : term25 a b m n q'.
Proof. exact (@lem3070852 a b m n q' (@lem3070849 a b m n)). Qed.
Lemma lem3070856 (x : nat) (y : nat) (n : nat) : (term12 x y n) = ((Nat.modulo x n) = (Nat.modulo y n)).
Proof. exact (EQ_MP (@lem3070816 x y n) (@lem3070815 x y n)). Qed.
Lemma lem3070857 (a : nat) (b : nat) (m : nat) (n : nat) : (term18 a b m n) = ((term5 a m n) = (term5 b m n)).
Proof. exact (@lem3070856 (Nat.div a m) (Nat.div b m) n). Qed.
Lemma lem3070861 (m : nat) (p : nat) (n : nat) : (term5 m n p) = (term6 m p n).
Proof. exact (EQ_MP (@lem3070807 m p n) (@lem3070806 m n p)). Qed.
Lemma lem3070862 (a : nat) (n : nat) (m : nat) : (term5 a m n) = (term6 a n m).
Proof. exact (@lem3070861 a n m). Qed.
Lemma lem3070864 (a : nat) (b : nat) (m : nat) (n : nat) (h1 : (term23 a m n) = (term23 b m n)) : (term23 a m n) = (term23 b m n).
Proof. exact (h1). Qed.
Lemma lem3070865 : Nat.div = Nat.div.
Proof. exact (eq_refl Nat.div). Qed.
Lemma lem3070866 (a : nat) (b : nat) (m : nat) (n : nat) (h1 : (term23 a m n) = (term23 b m n)) : (term26 a m n) = (term26 b m n).
Proof. exact (MK_COMB (@lem3070865) (@lem3070864 a b m n h1)). Qed.
Lemma lem3070867 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem3070868 (a : nat) (b : nat) (m : nat) (n : nat) (h1 : (term23 a m n) = (term23 b m n)) : (term6 a n m) = (term6 b n m).
Proof. exact (MK_COMB (@lem3070866 a b m n h1) (@lem3070867 m)). Qed.
Lemma lem3070869 (a : nat) (b : nat) (m : nat) (n : nat) (h1 : (term23 a m n) = (term23 b m n)) : (term5 a m n) = (term6 b n m).
Proof. exact (TRANS (@lem3070862 a n m) (@lem3070868 a b m n h1)). Qed.
Lemma lem3070870 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem3070871 (a : nat) (b : nat) (m : nat) (n : nat) (h1 : (term23 a m n) = (term23 b m n)) : (term27 a m n) = (term28 b n m).
Proof. exact (MK_COMB (@lem3070870) (@lem3070869 a b m n h1)). Qed.
Lemma lem3070873 (m : nat) (p : nat) (n : nat) : (term5 m n p) = (term6 m p n).
Proof. exact (EQ_MP (@lem3070807 m p n) (@lem3070806 m n p)). Qed.
Lemma lem3070874 (b : nat) (n : nat) (m : nat) : (term5 b m n) = (term6 b n m).
Proof. exact (@lem3070873 b n m). Qed.
Lemma lem3070875 (a : nat) (b : nat) (m : nat) (n : nat) (h1 : (term23 a m n) = (term23 b m n)) : ((term5 a m n) = (term5 b m n)) = ((term6 b n m) = (term6 b n m)).
Proof. exact (MK_COMB (@lem3070871 a b m n h1) (@lem3070874 b n m)). Qed.
Lemma lem3070877 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3070878 (x : nat) : (x = x) = True.
Proof. exact (@lem3070877 nat x). Qed.
Lemma lem3070879 (b : nat) (n : nat) (m : nat) : ((term6 b n m) = (term6 b n m)) = True.
Proof. exact (@lem3070878 (term6 b n m)). Qed.
Lemma lem3070880 (a : nat) (b : nat) (m : nat) (n : nat) (h1 : (term23 a m n) = (term23 b m n)) : ((term5 a m n) = (term5 b m n)) = True.
Proof. exact (TRANS (@lem3070875 a b m n h1) (@lem3070879 b n m)). Qed.
Lemma lem3070881 (a : nat) (b : nat) (m : nat) (n : nat) (h1 : (term23 a m n) = (term23 b m n)) : (term18 a b m n) = True.
Proof. exact (TRANS (@lem3070857 a b m n) (@lem3070880 a b m n h1)). Qed.
Lemma lem3070882 (a : nat) (b : nat) (m : nat) (n : nat) : term29 a b m n.
Proof. exact (fun h0 : (term23 a m n) = (term23 b m n) => @lem3070881 a b m n h0). Qed.
Lemma lem3070883 (a : nat) (b : nat) (m : nat) (n : nat) : term30 a b m n.
Proof. exact (@lem3070853 a b m n True). Qed.
Lemma lem3070884 (a : nat) (b : nat) (m : nat) (n : nat) : (term31 a b m n) = (term32 a b m n).
Proof. exact (@lem3070883 a b m n (@lem3070882 a b m n)). Qed.
Lemma lem3070888 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem3070889 (a : nat) (b : nat) (m : nat) (n : nat) : (term32 a b m n) = True.
Proof. exact (@lem3070888 ((term23 a m n) = (term23 b m n))). Qed.
Lemma lem3070890 (a : nat) (b : nat) (m : nat) (n : nat) : (term31 a b m n) = True.
Proof. exact (TRANS (@lem3070884 a b m n) (@lem3070889 a b m n)). Qed.
Lemma lem3070891 (a : nat) (b : nat) (m : nat) : (term33 a b m) = term34.
Proof. exact (fun_ext (fun n : nat => @lem3070890 a b m n)). Qed.
Lemma lem3070892 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3070893 (a : nat) (b : nat) (m : nat) : (term35 a b m) = term36.
Proof. exact (MK_COMB (@lem3070892) (@lem3070891 a b m)). Qed.
Lemma lem3070895 {A : Type'} (t : Prop) : (term37 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3070896 (t : Prop) : (term38 t) = t.
Proof. exact (@lem3070895 nat t). Qed.
Lemma lem3070897 : term36 = True.
Proof. exact (@lem3070896 True). Qed.
Lemma lem3070898 (a : nat) (b : nat) (m : nat) : (term35 a b m) = True.
Proof. exact (TRANS (@lem3070893 a b m) (@lem3070897)). Qed.
Lemma lem3070899 (a : nat) (b : nat) : (term39 a b) = term34.
Proof. exact (fun_ext (fun m : nat => @lem3070898 a b m)). Qed.
Lemma lem3070900 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3070901 (a : nat) (b : nat) : (term40 a b) = term36.
Proof. exact (MK_COMB (@lem3070900) (@lem3070899 a b)). Qed.
Lemma lem3070903 {A : Type'} (t : Prop) : (term37 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3070904 (t : Prop) : (term38 t) = t.
Proof. exact (@lem3070903 nat t). Qed.
Lemma lem3070905 : term36 = True.
Proof. exact (@lem3070904 True). Qed.
Lemma lem3070906 (a : nat) (b : nat) : (term40 a b) = True.
Proof. exact (TRANS (@lem3070901 a b) (@lem3070905)). Qed.
Lemma lem3070907 (a : nat) : (term41 a) = term34.
Proof. exact (fun_ext (fun b : nat => @lem3070906 a b)). Qed.
Lemma lem3070908 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3070909 (a : nat) : (term42 a) = term36.
Proof. exact (MK_COMB (@lem3070908) (@lem3070907 a)). Qed.
Lemma lem3070911 {A : Type'} (t : Prop) : (term37 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3070912 (t : Prop) : (term38 t) = t.
Proof. exact (@lem3070911 nat t). Qed.
Lemma lem3070913 : term36 = True.
Proof. exact (@lem3070912 True). Qed.
Lemma lem3070914 (a : nat) : (term42 a) = True.
Proof. exact (TRANS (@lem3070909 a) (@lem3070913)). Qed.
Lemma lem3070915 : term43 = term34.
Proof. exact (fun_ext (fun a : nat => @lem3070914 a)). Qed.
Lemma lem3070916 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3070917 : term44 = term36.
Proof. exact (MK_COMB (@lem3070916) (@lem3070915)). Qed.
Lemma lem3070919 {A : Type'} (t : Prop) : (term37 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3070920 (t : Prop) : (term38 t) = t.
Proof. exact (@lem3070919 nat t). Qed.
Lemma lem3070921 : term36 = True.
Proof. exact (@lem3070920 True). Qed.
Lemma lem3070922 : term44 = True.
Proof. exact (TRANS (@lem3070917) (@lem3070921)). Qed.
Lemma lem3070923 : True = term44.
Proof. exact (SYM (@lem3070922)). Qed.
Lemma lem3070924 : term44.
Proof. exact (EQ_MP (@lem3070923) (@lem0)). Qed.
