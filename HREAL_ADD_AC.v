Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import HREAL_ADD_AC_term_abbrevs.
Require Import thm1320004_spec.
Require Import thm1320203_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Lemma lem1321910 (x : hreal) : term0 x.
Proof. exact (@lem1320004 x). Qed.
Lemma lem1321911 (x : hreal) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1321912 (x : hreal) : term1 x.
Proof. exact (EQ_MP (@lem1321911 x) (@lem1321910 x)). Qed.
Lemma lem1321913 (x : hreal) (y : hreal) : term2 x y.
Proof. exact (@lem1321912 x y). Qed.
Lemma lem1321914 (y : hreal) (x : hreal) : (term2 x y) = ((hreal_add x y) = (hreal_add y x)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem1321915 (y : hreal) (x : hreal) : (hreal_add x y) = (hreal_add y x).
Proof. exact (EQ_MP (@lem1321914 y x) (@lem1321913 x y)). Qed.
Lemma lem1321916 (y : hreal) (x : hreal) : ((hreal_add x y) = (hreal_add y x)) = (((hreal_add x y) = (hreal_add y x)) = True).
Proof. exact (@lem7 ((hreal_add x y) = (hreal_add y x))). Qed.
Lemma lem1321918 (x : hreal) : term3 x.
Proof. exact (@lem1320203 x). Qed.
Lemma lem1321919 (x : hreal) : (term3 x) = (term4 x).
Proof. exact (eq_refl (term3 x)). Qed.
Lemma lem1321920 (x : hreal) : term4 x.
Proof. exact (EQ_MP (@lem1321919 x) (@lem1321918 x)). Qed.
Lemma lem1321921 (x : hreal) (y : hreal) : term5 x y.
Proof. exact (@lem1321920 x y). Qed.
Lemma lem1321922 (x : hreal) (y : hreal) : (term5 x y) = (term6 x y).
Proof. exact (eq_refl (term5 x y)). Qed.
Lemma lem1321923 (x : hreal) (y : hreal) : term6 x y.
Proof. exact (EQ_MP (@lem1321922 x y) (@lem1321921 x y)). Qed.
Lemma lem1321924 (x : hreal) (y : hreal) (z : hreal) : term7 x y z.
Proof. exact (@lem1321923 x y z). Qed.
Lemma lem1321925 (x : hreal) (y : hreal) (z : hreal) : (term7 x y z) = ((term8 x y z) = (term9 x y z)).
Proof. exact (eq_refl (term7 x y z)). Qed.
Lemma lem1321930 (y : hreal) (x : hreal) : ((hreal_add x y) = (hreal_add y x)) = True.
Proof. exact (EQ_MP (@lem1321916 y x) (@lem1321915 y x)). Qed.
Lemma lem1321931 (n : hreal) (m : hreal) : ((hreal_add m n) = (hreal_add n m)) = True.
Proof. exact (@lem1321930 n m). Qed.
Lemma lem1321932 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1321933 (n : hreal) (m : hreal) : (term10 n m) = (and True).
Proof. exact (MK_COMB (@lem1321932) (@lem1321931 n m)). Qed.
Lemma lem1321941 (x : hreal) (y : hreal) (z : hreal) : (term8 x y z) = (term9 x y z).
Proof. exact (EQ_MP (@lem1321925 x y z) (@lem1321924 x y z)). Qed.
Lemma lem1321942 (m : hreal) (n : hreal) (p : hreal) : (term8 m n p) = (term9 m n p).
Proof. exact (@lem1321941 m n p). Qed.
Lemma lem1321943 (m : hreal) (n : hreal) (p : hreal) : (term11 m n p) = (term11 m n p).
Proof. exact (eq_refl (term11 m n p)). Qed.
Lemma lem1321944 (m : hreal) (n : hreal) (p : hreal) : ((term9 m n p) = (term8 m n p)) = ((term9 m n p) = (term9 m n p)).
Proof. exact (MK_COMB (@lem1321943 m n p) (@lem1321942 m n p)). Qed.
Lemma lem1321948 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1321949 (x : hreal) : (x = x) = True.
Proof. exact (@lem1321948 hreal x). Qed.
Lemma lem1321950 (m : hreal) (n : hreal) (p : hreal) : ((term9 m n p) = (term9 m n p)) = True.
Proof. exact (@lem1321949 (term9 m n p)). Qed.
Lemma lem1321951 (m : hreal) (n : hreal) (p : hreal) : ((term9 m n p) = (term8 m n p)) = True.
Proof. exact (TRANS (@lem1321944 m n p) (@lem1321950 m n p)). Qed.
Lemma lem1321952 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1321953 (m : hreal) (n : hreal) (p : hreal) : (term12 m n p) = (and True).
Proof. exact (MK_COMB (@lem1321952) (@lem1321951 m n p)). Qed.
Lemma lem1321959 (x : hreal) (y : hreal) (z : hreal) : (term8 x y z) = (term9 x y z).
Proof. exact (EQ_MP (@lem1321925 x y z) (@lem1321924 x y z)). Qed.
Lemma lem1321960 (m : hreal) (n : hreal) (p : hreal) : (term8 m n p) = (term9 m n p).
Proof. exact (@lem1321959 m n p). Qed.
Lemma lem1321961 : (@eq hreal) = (@eq hreal).
Proof. exact (eq_refl (@eq hreal)). Qed.
Lemma lem1321962 (m : hreal) (n : hreal) (p : hreal) : (term13 m n p) = (term11 m n p).
Proof. exact (MK_COMB (@lem1321961) (@lem1321960 m n p)). Qed.
Lemma lem1321964 (x : hreal) (y : hreal) (z : hreal) : (term8 x y z) = (term9 x y z).
Proof. exact (EQ_MP (@lem1321925 x y z) (@lem1321924 x y z)). Qed.
Lemma lem1321965 (n : hreal) (m : hreal) (p : hreal) : (term8 n m p) = (term9 n m p).
Proof. exact (@lem1321964 n m p). Qed.
Lemma lem1321966 (n : hreal) (m : hreal) (p : hreal) : ((term8 m n p) = (term8 n m p)) = ((term9 m n p) = (term9 n m p)).
Proof. exact (MK_COMB (@lem1321962 m n p) (@lem1321965 n m p)). Qed.
Lemma lem1321971 (n : hreal) (m : hreal) (p : hreal) : (term14 n m p) = (term15 n m p).
Proof. exact (MK_COMB (@lem1321953 m n p) (@lem1321966 n m p)). Qed.
Lemma lem1321973 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1321974 (n : hreal) (m : hreal) (p : hreal) : (term15 n m p) = ((term9 m n p) = (term9 n m p)).
Proof. exact (@lem1321973 ((term9 m n p) = (term9 n m p))). Qed.
Lemma lem1321979 (n : hreal) (m : hreal) (p : hreal) : (term14 n m p) = ((term9 m n p) = (term9 n m p)).
Proof. exact (TRANS (@lem1321971 n m p) (@lem1321974 n m p)). Qed.
Lemma lem1321980 (n : hreal) (m : hreal) (p : hreal) : (term16 n m p) = (term15 n m p).
Proof. exact (MK_COMB (@lem1321933 n m) (@lem1321979 n m p)). Qed.
Lemma lem1321982 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1321983 (n : hreal) (m : hreal) (p : hreal) : (term15 n m p) = ((term9 m n p) = (term9 n m p)).
Proof. exact (@lem1321982 ((term9 m n p) = (term9 n m p))). Qed.
Lemma lem1321988 (n : hreal) (m : hreal) (p : hreal) : (term16 n m p) = ((term9 m n p) = (term9 n m p)).
Proof. exact (TRANS (@lem1321980 n m p) (@lem1321983 n m p)). Qed.
Lemma lem1321989 (n : hreal) (m : hreal) (p : hreal) : ((term9 m n p) = (term9 n m p)) = (term16 n m p).
Proof. exact (SYM (@lem1321988 n m p)). Qed.
Lemma lem1321990 (p : hreal) : p = p.
Proof. exact (eq_refl p). Qed.
Lemma lem1321991 : hreal_add = hreal_add.
Proof. exact (eq_refl hreal_add). Qed.
Lemma lem1321992 (x : hreal) : term0 x.
Proof. exact (@lem1320004 x). Qed.
Lemma lem1321993 (x : hreal) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1321994 (x : hreal) : term1 x.
Proof. exact (EQ_MP (@lem1321993 x) (@lem1321992 x)). Qed.
Lemma lem1321995 (x : hreal) (y : hreal) : term2 x y.
Proof. exact (@lem1321994 x y). Qed.
Lemma lem1321996 (y : hreal) (x : hreal) : (term2 x y) = ((hreal_add x y) = (hreal_add y x)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem1321999 (y : hreal) (x : hreal) : (hreal_add x y) = (hreal_add y x).
Proof. exact (EQ_MP (@lem1321996 y x) (@lem1321995 x y)). Qed.
Lemma lem1322000 (n : hreal) (m : hreal) : (hreal_add m n) = (hreal_add n m).
Proof. exact (@lem1321999 n m). Qed.
Lemma lem1322001 (n : hreal) (m : hreal) : (term17 m n) = (term17 n m).
Proof. exact (MK_COMB (@lem1321991) (@lem1322000 n m)). Qed.
Lemma lem1322002 (n : hreal) (m : hreal) (p : hreal) : (term9 m n p) = (term9 n m p).
Proof. exact (MK_COMB (@lem1322001 n m) (@lem1321990 p)). Qed.
Lemma lem1322003 (n : hreal) (m : hreal) (p : hreal) : term16 n m p.
Proof. exact (EQ_MP (@lem1321989 n m p) (@lem1322002 n m p)). Qed.
