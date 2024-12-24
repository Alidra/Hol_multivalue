Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import RDIV_LT_EQ_term_abbrevs.
Require Import LE_RDIV_EQ_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_LE_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm82_spec.
Lemma lem188845 (n : nat) (m : nat) (h1 : (term0 m n) = (Peano.lt n m)) : (term0 m n) = (Peano.lt n m).
Proof. exact (h1). Qed.
Lemma lem188846 (n : nat) (m : nat) (h1 : (term0 m n) = (Peano.lt n m)) : (Peano.lt n m) = (term0 m n).
Proof. exact (SYM (@lem188845 n m h1)). Qed.
Lemma lem188847 (m : nat) (n : nat) (h1 : (Peano.lt n m) = (term0 m n)) : (Peano.lt n m) = (term0 m n).
Proof. exact (h1). Qed.
Lemma lem188848 (m : nat) (n : nat) (h1 : (Peano.lt n m) = (term0 m n)) : (term0 m n) = (Peano.lt n m).
Proof. exact (SYM (@lem188847 m n h1)). Qed.
Lemma lem188849 (m : nat) (n : nat) : ((term0 m n) = (Peano.lt n m)) = ((Peano.lt n m) = (term0 m n)).
Proof. exact (prop_ext (fun h1 : (term0 m n) = (Peano.lt n m) => @lem188846 n m h1) (fun h1 : (Peano.lt n m) = (term0 m n) => @lem188848 m n h1)). Qed.
Lemma lem188850 (m : nat) : (term1 m) = (term2 m).
Proof. exact (fun_ext (fun n : nat => @lem188849 m n)). Qed.
Lemma lem188851 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem188852 (m : nat) : (term3 m) = (term4 m).
Proof. exact (MK_COMB (@lem188851) (@lem188850 m)). Qed.
Lemma lem188853 : term5 = term6.
Proof. exact (fun_ext (fun m : nat => @lem188852 m)). Qed.
Lemma lem188854 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem188855 : term7 = term8.
Proof. exact (MK_COMB (@lem188854) (@lem188853)). Qed.
Lemma lem188856 : term8.
Proof. exact (EQ_MP (@lem188855) (@lem97961)). Qed.
Lemma lem188857 (a : nat) : term9 a.
Proof. exact (@lem188842 a). Qed.
Lemma lem188858 (a : nat) : (term9 a) = (term10 a).
Proof. exact (eq_refl (term9 a)). Qed.
Lemma lem188859 (a : nat) : term10 a.
Proof. exact (EQ_MP (@lem188858 a) (@lem188857 a)). Qed.
Lemma lem188860 (a : nat) (b : nat) : term11 a b.
Proof. exact (@lem188859 a b). Qed.
Lemma lem188861 (a : nat) (b : nat) : (term11 a b) = (term12 a b).
Proof. exact (eq_refl (term11 a b)). Qed.
Lemma lem188862 (a : nat) (b : nat) : term12 a b.
Proof. exact (EQ_MP (@lem188861 a b) (@lem188860 a b)). Qed.
Lemma lem188863 (a : nat) (b : nat) (n : nat) : term13 a b n.
Proof. exact (@lem188862 a b n). Qed.
Lemma lem188864 (a : nat) (n : nat) (b : nat) : (term13 a b n) = (term14 a n b).
Proof. exact (eq_refl (term13 a b n)). Qed.
Lemma lem188865 (a : nat) (n : nat) (b : nat) : term14 a n b.
Proof. exact (EQ_MP (@lem188864 a n b) (@lem188863 a b n)). Qed.
Lemma lem188866 (a : nat) (h1 : term15 a) : term15 a.
Proof. exact (h1). Qed.
Lemma lem188867 (n : nat) (b : nat) (a : nat) (h1 : term15 a) : (term16 n b a) = (term17 a n b).
Proof. exact (@lem188865 a n b (@lem188866 a h1)). Qed.
Lemma lem188873 (m : nat) : term18 m.
Proof. exact (@lem188856 m). Qed.
Lemma lem188874 (m : nat) : (term18 m) = (term4 m).
Proof. exact (eq_refl (term18 m)). Qed.
Lemma lem188875 (m : nat) : term4 m.
Proof. exact (EQ_MP (@lem188874 m) (@lem188873 m)). Qed.
Lemma lem188876 (m : nat) (n : nat) : term19 m n.
Proof. exact (@lem188875 m n). Qed.
Lemma lem188877 (m : nat) (n : nat) : (term19 m n) = ((Peano.lt n m) = (term0 m n)).
Proof. exact (eq_refl (term19 m n)). Qed.
Lemma lem188894 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term20 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem188895 (p : Prop) (q : Prop) (p' : Prop) : term21 p q p'.
Proof. exact (fun q' : Prop => @lem188894 p q p' q'). Qed.
Lemma lem188896 (p : Prop) (q : Prop) : term22 p q.
Proof. exact (fun p' : Prop => @lem188895 p q p'). Qed.
Lemma lem188897 (b : nat) (a : nat) (n : nat) : term23 b a n.
Proof. exact (@lem188896 (term15 a) ((term24 b a n) = (term25 b a n))). Qed.
Lemma lem188898 (b : nat) (a : nat) (n : nat) (p' : Prop) : term26 b a n p'.
Proof. exact (@lem188897 b a n p'). Qed.
Lemma lem188899 (b : nat) (a : nat) (n : nat) (p' : Prop) : (term26 b a n p') = (term27 b a n p').
Proof. exact (eq_refl (term26 b a n p')). Qed.
Lemma lem188900 (b : nat) (a : nat) (n : nat) (p' : Prop) : term27 b a n p'.
Proof. exact (EQ_MP (@lem188899 b a n p') (@lem188898 b a n p')). Qed.
Lemma lem188901 (b : nat) (a : nat) (n : nat) (p' : Prop) (q' : Prop) : term28 b a n p' q'.
Proof. exact (@lem188900 b a n p' q'). Qed.
Lemma lem188902 (b : nat) (a : nat) (n : nat) (p' : Prop) (q' : Prop) : (term28 b a n p' q') = (term29 b a n p' q').
Proof. exact (eq_refl (term28 b a n p' q')). Qed.
Lemma lem188903 (b : nat) (a : nat) (n : nat) (p' : Prop) (q' : Prop) : term29 b a n p' q'.
Proof. exact (EQ_MP (@lem188902 b a n p' q') (@lem188901 b a n p' q')). Qed.
Lemma lem188906 (a : nat) : (term15 a) = (term15 a).
Proof. exact (eq_refl (term15 a)). Qed.
Lemma lem188907 (b : nat) (n : nat) (a : nat) (q' : Prop) : term30 b n a q'.
Proof. exact (@lem188903 b a n (term15 a) q'). Qed.
Lemma lem188908 (b : nat) (n : nat) (a : nat) (q' : Prop) : term31 b n a q'.
Proof. exact (@lem188907 b n a q' (@lem188906 a)). Qed.
Lemma lem188909 (a : nat) (h1 : term15 a) : term15 a.
Proof. exact (h1). Qed.
Lemma lem188910 (a : nat) : term32 a.
Proof. exact (@lem82 (a = (NUMERAL 0))). Qed.
Lemma lem188926 (m : nat) (n : nat) : (Peano.lt n m) = (term0 m n).
Proof. exact (EQ_MP (@lem188877 m n) (@lem188876 m n)). Qed.
Lemma lem188927 (n : nat) (b : nat) (a : nat) : (term24 b a n) = (term33 n b a).
Proof. exact (@lem188926 n (Nat.div b a)). Qed.
Lemma lem188929 (a : nat) (n : nat) (b : nat) : term14 a n b.
Proof. exact (fun h0 : term15 a => @lem188867 n b a h0). Qed.
Lemma lem188931 (a : nat) (h1 : term15 a) : (a = (NUMERAL 0)) = False.
Proof. exact (@lem188910 a (@lem188909 a h1)). Qed.
Lemma lem188932 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem188933 (a : nat) (h1 : term15 a) : (term15 a) = (~ False).
Proof. exact (MK_COMB (@lem188932) (@lem188931 a h1)). Qed.
Lemma lem188935 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem188936 (a : nat) (h1 : term15 a) : (term15 a) = True.
Proof. exact (TRANS (@lem188933 a h1) (@lem188935)). Qed.
Lemma lem188937 (a : nat) (h1 : term15 a) : True = (term15 a).
Proof. exact (SYM (@lem188936 a h1)). Qed.
Lemma lem188938 (a : nat) (h1 : term15 a) : term15 a.
Proof. exact (EQ_MP (@lem188937 a h1) (@lem0)). Qed.
Lemma lem188939 (n : nat) (b : nat) (a : nat) (h1 : term15 a) : (term16 n b a) = (term17 a n b).
Proof. exact (@lem188929 a n b (@lem188938 a h1)). Qed.
Lemma lem188940 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem188941 (n : nat) (b : nat) (a : nat) (h1 : term15 a) : (term33 n b a) = (term34 a n b).
Proof. exact (MK_COMB (@lem188940) (@lem188939 n b a h1)). Qed.
Lemma lem188942 (n : nat) (b : nat) (a : nat) (h1 : term15 a) : (term24 b a n) = (term34 a n b).
Proof. exact (TRANS (@lem188927 n b a) (@lem188941 n b a h1)). Qed.
Lemma lem188943 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem188944 (n : nat) (b : nat) (a : nat) (h1 : term15 a) : (term35 b a n) = (term36 a n b).
Proof. exact (MK_COMB (@lem188943) (@lem188942 n b a h1)). Qed.
Lemma lem188946 (m : nat) (n : nat) : (Peano.lt n m) = (term0 m n).
Proof. exact (EQ_MP (@lem188877 m n) (@lem188876 m n)). Qed.
Lemma lem188947 (a : nat) (n : nat) (b : nat) : (term25 b a n) = (term34 a n b).
Proof. exact (@lem188946 (Nat.mul a n) b). Qed.
Lemma lem188948 (n : nat) (b : nat) (a : nat) (h1 : term15 a) : ((term24 b a n) = (term25 b a n)) = ((term34 a n b) = (term34 a n b)).
Proof. exact (MK_COMB (@lem188944 n b a h1) (@lem188947 a n b)). Qed.
Lemma lem188950 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem188951 (x : Prop) : (x = x) = True.
Proof. exact (@lem188950 Prop x). Qed.
Lemma lem188952 (a : nat) (n : nat) (b : nat) : ((term34 a n b) = (term34 a n b)) = True.
Proof. exact (@lem188951 (term34 a n b)). Qed.
Lemma lem188953 (b : nat) (n : nat) (a : nat) (h1 : term15 a) : ((term24 b a n) = (term25 b a n)) = True.
Proof. exact (TRANS (@lem188948 n b a h1) (@lem188952 a n b)). Qed.
Lemma lem188954 (b : nat) (a : nat) (n : nat) : term37 b a n.
Proof. exact (fun h0 : term15 a => @lem188953 b n a h0). Qed.
Lemma lem188955 (b : nat) (n : nat) (a : nat) : term38 b n a.
Proof. exact (@lem188908 b n a True). Qed.
Lemma lem188956 (b : nat) (n : nat) (a : nat) : (term39 b a n) = (term40 a).
Proof. exact (@lem188955 b n a (@lem188954 b a n)). Qed.
Lemma lem188958 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem188959 (a : nat) : (term40 a) = True.
Proof. exact (@lem188958 (term15 a)). Qed.
Lemma lem188960 (b : nat) (a : nat) (n : nat) : (term39 b a n) = True.
Proof. exact (TRANS (@lem188956 b n a) (@lem188959 a)). Qed.
Lemma lem188961 (b : nat) (a : nat) : (term41 b a) = term42.
Proof. exact (fun_ext (fun n : nat => @lem188960 b a n)). Qed.
Lemma lem188962 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem188963 (b : nat) (a : nat) : (term43 b a) = term44.
Proof. exact (MK_COMB (@lem188962) (@lem188961 b a)). Qed.
Lemma lem188965 {A : Type'} (t : Prop) : (term45 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem188966 (t : Prop) : (term46 t) = t.
Proof. exact (@lem188965 nat t). Qed.
Lemma lem188967 : term44 = True.
Proof. exact (@lem188966 True). Qed.
Lemma lem188968 (b : nat) (a : nat) : (term43 b a) = True.
Proof. exact (TRANS (@lem188963 b a) (@lem188967)). Qed.
Lemma lem188969 (a : nat) : (term47 a) = term42.
Proof. exact (fun_ext (fun b : nat => @lem188968 b a)). Qed.
Lemma lem188970 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem188971 (a : nat) : (term48 a) = term44.
Proof. exact (MK_COMB (@lem188970) (@lem188969 a)). Qed.
Lemma lem188973 {A : Type'} (t : Prop) : (term45 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem188974 (t : Prop) : (term46 t) = t.
Proof. exact (@lem188973 nat t). Qed.
Lemma lem188975 : term44 = True.
Proof. exact (@lem188974 True). Qed.
Lemma lem188976 (a : nat) : (term48 a) = True.
Proof. exact (TRANS (@lem188971 a) (@lem188975)). Qed.
Lemma lem188977 : term49 = term42.
Proof. exact (fun_ext (fun a : nat => @lem188976 a)). Qed.
Lemma lem188978 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem188979 : term50 = term44.
Proof. exact (MK_COMB (@lem188978) (@lem188977)). Qed.
Lemma lem188981 {A : Type'} (t : Prop) : (term45 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem188982 (t : Prop) : (term46 t) = t.
Proof. exact (@lem188981 nat t). Qed.
Lemma lem188983 : term44 = True.
Proof. exact (@lem188982 True). Qed.
Lemma lem188984 : term50 = True.
Proof. exact (TRANS (@lem188979) (@lem188983)). Qed.
Lemma lem188985 : True = term50.
Proof. exact (SYM (@lem188984)). Qed.
Lemma lem188986 : term50.
Proof. exact (EQ_MP (@lem188985) (@lem0)). Qed.
