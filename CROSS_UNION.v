Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CROSS_UNION_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import EXTENSION_spec.
Require Import FORALL_PAIR_THM_spec.
Require Import IN_CROSS_spec.
Require Import IN_UNION_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1831_spec.
Require Import thm1833_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1845_spec.
Require Import thm1855_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem4360795 {_103718 _103721 : Type'} (x : _103718) : term0 _103718 _103721 x.
Proof. exact (@lem4325365 _103718 _103721 x). Qed.
Lemma lem4360796 {_103718 _103721 : Type'} (x : _103718) : (term0 _103718 _103721 x) = (term1 _103718 _103721 x).
Proof. exact (eq_refl (term0 _103718 _103721 x)). Qed.
Lemma lem4360797 {_103718 _103721 : Type'} (x : _103718) : term1 _103718 _103721 x.
Proof. exact (EQ_MP (@lem4360796 _103718 _103721 x) (@lem4360795 _103718 _103721 x)). Qed.
Lemma lem4360798 {_103718 _103721 : Type'} (x : _103718) (y : _103721) : term2 _103718 _103721 x y.
Proof. exact (@lem4360797 _103718 _103721 x y). Qed.
Lemma lem4360799 {_103718 _103721 : Type'} (x : _103718) (y : _103721) : (term2 _103718 _103721 x y) = (term3 _103718 _103721 x y).
Proof. exact (eq_refl (term2 _103718 _103721 x y)). Qed.
Lemma lem4360800 {_103718 _103721 : Type'} (x : _103718) (y : _103721) : term3 _103718 _103721 x y.
Proof. exact (EQ_MP (@lem4360799 _103718 _103721 x y) (@lem4360798 _103718 _103721 x y)). Qed.
Lemma lem4360801 {_103718 _103721 : Type'} (x : _103718) (y : _103721) (s : _103718 -> Prop) : term4 _103718 _103721 x y s.
Proof. exact (@lem4360800 _103718 _103721 x y s). Qed.
Lemma lem4360802 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) : (term4 _103718 _103721 x y s) = (term5 _103718 _103721 x s y).
Proof. exact (eq_refl (term4 _103718 _103721 x y s)). Qed.
Lemma lem4360803 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) : term5 _103718 _103721 x s y.
Proof. exact (EQ_MP (@lem4360802 _103718 _103721 x s y) (@lem4360801 _103718 _103721 x y s)). Qed.
Lemma lem4360804 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : term6 _103718 _103721 x s y t.
Proof. exact (@lem4360803 _103718 _103721 x s y t). Qed.
Lemma lem4360805 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term6 _103718 _103721 x s y t) = ((term7 _103718 _103721 x y s t) = (term8 _103718 _103721 x s y t)).
Proof. exact (eq_refl (term6 _103718 _103721 x s y t)). Qed.
Lemma lem4360807 {A : Type'} (s : A -> Prop) : term9 A s.
Proof. exact (@lem3204949 A s). Qed.
Lemma lem4360808 {A : Type'} (s : A -> Prop) : (term9 A s) = (term10 A s).
Proof. exact (eq_refl (term9 A s)). Qed.
Lemma lem4360809 {A : Type'} (s : A -> Prop) : term10 A s.
Proof. exact (EQ_MP (@lem4360808 A s) (@lem4360807 A s)). Qed.
Lemma lem4360810 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term11 A s t.
Proof. exact (@lem4360809 A s t). Qed.
Lemma lem4360811 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term11 A s t) = (term12 A s t).
Proof. exact (eq_refl (term11 A s t)). Qed.
Lemma lem4360812 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term12 A s t.
Proof. exact (EQ_MP (@lem4360811 A s t) (@lem4360810 A s t)). Qed.
Lemma lem4360813 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : term13 A s t x.
Proof. exact (@lem4360812 A s t x). Qed.
Lemma lem4360814 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term13 A s t x) = ((term14 A x s t) = (term15 A s x t)).
Proof. exact (eq_refl (term13 A s t x)). Qed.
Lemma lem4360816 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : term16 _5106 _5107 P.
Proof. exact (@lem49909 _5106 _5107 P). Qed.
Lemma lem4360817 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term16 _5106 _5107 P) = ((term17 _5106 _5107 P) = (term18 _5106 _5107 P)).
Proof. exact (eq_refl (term16 _5106 _5107 P)). Qed.
Lemma lem4360819 {A : Type'} (s : A -> Prop) : term19 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem4360820 {A : Type'} (s : A -> Prop) : (term19 A s) = (term20 A s).
Proof. exact (eq_refl (term19 A s)). Qed.
Lemma lem4360821 {A : Type'} (s : A -> Prop) : term20 A s.
Proof. exact (EQ_MP (@lem4360820 A s) (@lem4360819 A s)). Qed.
Lemma lem4360822 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term21 A s t.
Proof. exact (@lem4360821 A s t). Qed.
Lemma lem4360823 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term21 A s t) = ((s = t) = (term22 A s t)).
Proof. exact (eq_refl (term21 A s t)). Qed.
Lemma lem4360848 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term22 A s t).
Proof. exact (EQ_MP (@lem4360823 A s t) (@lem4360822 A s t)). Qed.
Lemma lem4360849 {_104522 _104523 : Type'} (s : type1210 _104522 _104523) (t : type1210 _104522 _104523) : (s = t) = (term23 _104522 _104523 s t).
Proof. exact (@lem4360848 (prod _104522 _104523) s t). Qed.
Lemma lem4360850 {_104522 _104523 : Type'} (t : _104523 -> Prop) (s : _104522 -> Prop) (u : _104523 -> Prop) : ((term24 _104522 _104523 s t u) = (term25 _104522 _104523 t s u)) = (term26 _104522 _104523 t s u).
Proof. exact (@lem4360849 _104522 _104523 (term24 _104522 _104523 s t u) (term25 _104522 _104523 t s u)). Qed.
Lemma lem4360856 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term17 _5106 _5107 P) = (term18 _5106 _5107 P).
Proof. exact (EQ_MP (@lem4360817 _5106 _5107 P) (@lem4360816 _5106 _5107 P)). Qed.
Lemma lem4360857 {_104522 _104523 : Type'} (P : type1210 _104522 _104523) : (term27 _104522 _104523 P) = (term28 _104522 _104523 P).
Proof. exact (@lem4360856 _104523 _104522 P). Qed.
Lemma lem4360858 {_104522 _104523 : Type'} (t : _104523 -> Prop) (s : _104522 -> Prop) (u : _104523 -> Prop) : (term29 _104522 _104523 t s u) = (term30 _104522 _104523 t s u).
Proof. exact (@lem4360857 _104522 _104523 (term31 _104522 _104523 t s u)). Qed.
Lemma lem4360859 {_104522 _104523 : Type'} (x : prod _104522 _104523) (t : _104523 -> Prop) (s : _104522 -> Prop) (u : _104523 -> Prop) : (term32 _104522 _104523 t s u x) = ((term33 _104522 _104523 x s t u) = (term34 _104522 _104523 x t s u)).
Proof. exact (eq_refl (term32 _104522 _104523 t s u x)). Qed.
Lemma lem4360860 {_104522 _104523 : Type'} (t : _104523 -> Prop) (s : _104522 -> Prop) (u : _104523 -> Prop) : (term35 _104522 _104523 t s u) = (term31 _104522 _104523 t s u).
Proof. exact (fun_ext (fun x : prod _104522 _104523 => @lem4360859 _104522 _104523 x t s u)). Qed.
Lemma lem4360861 {_104522 _104523 : Type'} : (@all (prod _104522 _104523)) = (@all (prod _104522 _104523)).
Proof. exact (eq_refl (@all (prod _104522 _104523))). Qed.
Lemma lem4360862 {_104522 _104523 : Type'} (t : _104523 -> Prop) (s : _104522 -> Prop) (u : _104523 -> Prop) : (term29 _104522 _104523 t s u) = (term26 _104522 _104523 t s u).
Proof. exact (MK_COMB (@lem4360861 _104522 _104523) (@lem4360860 _104522 _104523 t s u)). Qed.
Lemma lem4360863 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4360864 {_104522 _104523 : Type'} (t : _104523 -> Prop) (s : _104522 -> Prop) (u : _104523 -> Prop) : (term36 _104522 _104523 t s u) = (term37 _104522 _104523 t s u).
Proof. exact (MK_COMB (@lem4360863) (@lem4360862 _104522 _104523 t s u)). Qed.
Lemma lem4360865 {_104522 _104523 : Type'} (p1 : _104522) (p2 : _104523) (t : _104523 -> Prop) (s : _104522 -> Prop) (u : _104523 -> Prop) : (term38 _104522 _104523 t s u p1 p2) = ((term39 _104522 _104523 p1 p2 s t u) = (term40 _104522 _104523 p1 p2 t s u)).
Proof. exact (eq_refl (term38 _104522 _104523 t s u p1 p2)). Qed.
Lemma lem4360866 {_104522 _104523 : Type'} (p1 : _104522) (t : _104523 -> Prop) (s : _104522 -> Prop) (u : _104523 -> Prop) : (term41 _104522 _104523 t s u p1) = (term42 _104522 _104523 p1 t s u).
Proof. exact (fun_ext (fun p2 : _104523 => @lem4360865 _104522 _104523 p1 p2 t s u)). Qed.
Lemma lem4360867 {_104523 : Type'} : (@all _104523) = (@all _104523).
Proof. exact (eq_refl (@all _104523)). Qed.
Lemma lem4360868 {_104522 _104523 : Type'} (p1 : _104522) (t : _104523 -> Prop) (s : _104522 -> Prop) (u : _104523 -> Prop) : (term43 _104522 _104523 t s u p1) = (term44 _104522 _104523 p1 t s u).
Proof. exact (MK_COMB (@lem4360867 _104523) (@lem4360866 _104522 _104523 p1 t s u)). Qed.
Lemma lem4360869 {_104522 _104523 : Type'} (t : _104523 -> Prop) (s : _104522 -> Prop) (u : _104523 -> Prop) : (term45 _104522 _104523 t s u) = (term46 _104522 _104523 t s u).
Proof. exact (fun_ext (fun p1 : _104522 => @lem4360868 _104522 _104523 p1 t s u)). Qed.
Lemma lem4360870 {_104522 : Type'} : (@all _104522) = (@all _104522).
Proof. exact (eq_refl (@all _104522)). Qed.
Lemma lem4360871 {_104522 _104523 : Type'} (t : _104523 -> Prop) (s : _104522 -> Prop) (u : _104523 -> Prop) : (term30 _104522 _104523 t s u) = (term47 _104522 _104523 t s u).
Proof. exact (MK_COMB (@lem4360870 _104522) (@lem4360869 _104522 _104523 t s u)). Qed.
Lemma lem4360872 {_104522 _104523 : Type'} (t : _104523 -> Prop) (s : _104522 -> Prop) (u : _104523 -> Prop) : ((term29 _104522 _104523 t s u) = (term30 _104522 _104523 t s u)) = ((term26 _104522 _104523 t s u) = (term47 _104522 _104523 t s u)).
Proof. exact (MK_COMB (@lem4360864 _104522 _104523 t s u) (@lem4360871 _104522 _104523 t s u)). Qed.
Lemma lem4360873 {_104522 _104523 : Type'} (t : _104523 -> Prop) (s : _104522 -> Prop) (u : _104523 -> Prop) : (term26 _104522 _104523 t s u) = (term47 _104522 _104523 t s u).
Proof. exact (EQ_MP (@lem4360872 _104522 _104523 t s u) (@lem4360858 _104522 _104523 t s u)). Qed.
Lemma lem4360880 {_104522 _104523 : Type'} (t : _104523 -> Prop) (s : _104522 -> Prop) (u : _104523 -> Prop) : ((term24 _104522 _104523 s t u) = (term25 _104522 _104523 t s u)) = (term47 _104522 _104523 t s u).
Proof. exact (TRANS (@lem4360850 _104522 _104523 t s u) (@lem4360873 _104522 _104523 t s u)). Qed.
Lemma lem4360892 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term7 _103718 _103721 x y s t) = (term8 _103718 _103721 x s y t).
Proof. exact (EQ_MP (@lem4360805 _103718 _103721 x s y t) (@lem4360804 _103718 _103721 x s y t)). Qed.
Lemma lem4360893 {_104522 _104523 : Type'} (x : _104522) (s : _104522 -> Prop) (y : _104523) (t : _104523 -> Prop) : (term7 _104522 _104523 x y s t) = (term8 _104522 _104523 x s y t).
Proof. exact (@lem4360892 _104522 _104523 x s y t). Qed.
Lemma lem4360894 {_104522 _104523 : Type'} (p1 : _104522) (s : _104522 -> Prop) (p2 : _104523) (t : _104523 -> Prop) (u : _104523 -> Prop) : (term39 _104522 _104523 p1 p2 s t u) = (term48 _104522 _104523 p1 s p2 t u).
Proof. exact (@lem4360893 _104522 _104523 p1 s p2 (@UNION _104523 t u)). Qed.
Lemma lem4360898 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term14 A x s t) = (term15 A s x t).
Proof. exact (EQ_MP (@lem4360814 A s x t) (@lem4360813 A s t x)). Qed.
Lemma lem4360899 {_104523 : Type'} (s : _104523 -> Prop) (x : _104523) (t : _104523 -> Prop) : (term14 _104523 x s t) = (term15 _104523 s x t).
Proof. exact (@lem4360898 _104523 s x t). Qed.
Lemma lem4360900 {_104523 : Type'} (t : _104523 -> Prop) (p2 : _104523) (u : _104523 -> Prop) : (term14 _104523 p2 t u) = (term15 _104523 t p2 u).
Proof. exact (@lem4360899 _104523 t p2 u). Qed.
Lemma lem4360903 {_104522 : Type'} (p1 : _104522) (s : _104522 -> Prop) : (term49 _104522 p1 s) = (term49 _104522 p1 s).
Proof. exact (eq_refl (term49 _104522 p1 s)). Qed.
Lemma lem4360904 {_104522 _104523 : Type'} (p1 : _104522) (s : _104522 -> Prop) (t : _104523 -> Prop) (p2 : _104523) (u : _104523 -> Prop) : (term48 _104522 _104523 p1 s p2 t u) = (term50 _104522 _104523 p1 s t p2 u).
Proof. exact (MK_COMB (@lem4360903 _104522 p1 s) (@lem4360900 _104523 t p2 u)). Qed.
Lemma lem4360907 {_104522 _104523 : Type'} (p1 : _104522) (s : _104522 -> Prop) (t : _104523 -> Prop) (p2 : _104523) (u : _104523 -> Prop) : (term39 _104522 _104523 p1 p2 s t u) = (term50 _104522 _104523 p1 s t p2 u).
Proof. exact (TRANS (@lem4360894 _104522 _104523 p1 s p2 t u) (@lem4360904 _104522 _104523 p1 s t p2 u)). Qed.
Lemma lem4360908 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4360909 {_104522 _104523 : Type'} (p1 : _104522) (s : _104522 -> Prop) (t : _104523 -> Prop) (p2 : _104523) (u : _104523 -> Prop) : (term51 _104522 _104523 p1 p2 s t u) = (term52 _104522 _104523 p1 s t p2 u).
Proof. exact (MK_COMB (@lem4360908) (@lem4360907 _104522 _104523 p1 s t p2 u)). Qed.
Lemma lem4360911 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term14 A x s t) = (term15 A s x t).
Proof. exact (EQ_MP (@lem4360814 A s x t) (@lem4360813 A s t x)). Qed.
Lemma lem4360912 {_104522 _104523 : Type'} (s : type1210 _104522 _104523) (x : prod _104522 _104523) (t : type1210 _104522 _104523) : (term53 _104522 _104523 x s t) = (term54 _104522 _104523 s x t).
Proof. exact (@lem4360911 (prod _104522 _104523) s x t). Qed.
Lemma lem4360913 {_104522 _104523 : Type'} (t : _104523 -> Prop) (p1 : _104522) (p2 : _104523) (s : _104522 -> Prop) (u : _104523 -> Prop) : (term40 _104522 _104523 p1 p2 t s u) = (term55 _104522 _104523 t p1 p2 s u).
Proof. exact (@lem4360912 _104522 _104523 (@CROSS _104523 _104522 s t) (@pair _104522 _104523 p1 p2) (@CROSS _104523 _104522 s u)). Qed.
Lemma lem4360917 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term7 _103718 _103721 x y s t) = (term8 _103718 _103721 x s y t).
Proof. exact (EQ_MP (@lem4360805 _103718 _103721 x s y t) (@lem4360804 _103718 _103721 x s y t)). Qed.
Lemma lem4360918 {_104522 _104523 : Type'} (x : _104522) (s : _104522 -> Prop) (y : _104523) (t : _104523 -> Prop) : (term7 _104522 _104523 x y s t) = (term8 _104522 _104523 x s y t).
Proof. exact (@lem4360917 _104522 _104523 x s y t). Qed.
Lemma lem4360919 {_104522 _104523 : Type'} (p1 : _104522) (s : _104522 -> Prop) (p2 : _104523) (t : _104523 -> Prop) : (term7 _104522 _104523 p1 p2 s t) = (term8 _104522 _104523 p1 s p2 t).
Proof. exact (@lem4360918 _104522 _104523 p1 s p2 t). Qed.
Lemma lem4360922 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4360923 {_104522 _104523 : Type'} (p1 : _104522) (s : _104522 -> Prop) (p2 : _104523) (t : _104523 -> Prop) : (term56 _104522 _104523 p1 p2 s t) = (term57 _104522 _104523 p1 s p2 t).
Proof. exact (MK_COMB (@lem4360922) (@lem4360919 _104522 _104523 p1 s p2 t)). Qed.
Lemma lem4360925 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term7 _103718 _103721 x y s t) = (term8 _103718 _103721 x s y t).
Proof. exact (EQ_MP (@lem4360805 _103718 _103721 x s y t) (@lem4360804 _103718 _103721 x s y t)). Qed.
Lemma lem4360926 {_104522 _104523 : Type'} (x : _104522) (s : _104522 -> Prop) (y : _104523) (t : _104523 -> Prop) : (term7 _104522 _104523 x y s t) = (term8 _104522 _104523 x s y t).
Proof. exact (@lem4360925 _104522 _104523 x s y t). Qed.
Lemma lem4360927 {_104522 _104523 : Type'} (p1 : _104522) (s : _104522 -> Prop) (p2 : _104523) (u : _104523 -> Prop) : (term7 _104522 _104523 p1 p2 s u) = (term8 _104522 _104523 p1 s p2 u).
Proof. exact (@lem4360926 _104522 _104523 p1 s p2 u). Qed.
Lemma lem4360930 {_104522 _104523 : Type'} (t : _104523 -> Prop) (p1 : _104522) (s : _104522 -> Prop) (p2 : _104523) (u : _104523 -> Prop) : (term55 _104522 _104523 t p1 p2 s u) = (term58 _104522 _104523 t p1 s p2 u).
Proof. exact (MK_COMB (@lem4360923 _104522 _104523 p1 s p2 t) (@lem4360927 _104522 _104523 p1 s p2 u)). Qed.
Lemma lem4360933 {_104522 _104523 : Type'} (t : _104523 -> Prop) (p1 : _104522) (s : _104522 -> Prop) (p2 : _104523) (u : _104523 -> Prop) : (term40 _104522 _104523 p1 p2 t s u) = (term58 _104522 _104523 t p1 s p2 u).
Proof. exact (TRANS (@lem4360913 _104522 _104523 t p1 p2 s u) (@lem4360930 _104522 _104523 t p1 s p2 u)). Qed.
Lemma lem4360934 {_104522 _104523 : Type'} (t : _104523 -> Prop) (p1 : _104522) (s : _104522 -> Prop) (p2 : _104523) (u : _104523 -> Prop) : ((term39 _104522 _104523 p1 p2 s t u) = (term40 _104522 _104523 p1 p2 t s u)) = ((term50 _104522 _104523 p1 s t p2 u) = (term58 _104522 _104523 t p1 s p2 u)).
Proof. exact (MK_COMB (@lem4360909 _104522 _104523 p1 s t p2 u) (@lem4360933 _104522 _104523 t p1 s p2 u)). Qed.
Lemma lem4360939 {_104522 _104523 : Type'} (t : _104523 -> Prop) (p1 : _104522) (s : _104522 -> Prop) (u : _104523 -> Prop) : (term42 _104522 _104523 p1 t s u) = (term59 _104522 _104523 t p1 s u).
Proof. exact (fun_ext (fun p2 : _104523 => @lem4360934 _104522 _104523 t p1 s p2 u)). Qed.
Lemma lem4360940 {_104523 : Type'} : (@all _104523) = (@all _104523).
Proof. exact (eq_refl (@all _104523)). Qed.
Lemma lem4360941 {_104522 _104523 : Type'} (t : _104523 -> Prop) (p1 : _104522) (s : _104522 -> Prop) (u : _104523 -> Prop) : (term44 _104522 _104523 p1 t s u) = (term60 _104522 _104523 t p1 s u).
Proof. exact (MK_COMB (@lem4360940 _104523) (@lem4360939 _104522 _104523 t p1 s u)). Qed.
Lemma lem4360948 {_104522 _104523 : Type'} (t : _104523 -> Prop) (s : _104522 -> Prop) (u : _104523 -> Prop) : (term46 _104522 _104523 t s u) = (term61 _104522 _104523 t s u).
Proof. exact (fun_ext (fun p1 : _104522 => @lem4360941 _104522 _104523 t p1 s u)). Qed.
Lemma lem4360949 {_104522 : Type'} : (@all _104522) = (@all _104522).
Proof. exact (eq_refl (@all _104522)). Qed.
Lemma lem4360950 {_104522 _104523 : Type'} (t : _104523 -> Prop) (s : _104522 -> Prop) (u : _104523 -> Prop) : (term47 _104522 _104523 t s u) = (term62 _104522 _104523 t s u).
Proof. exact (MK_COMB (@lem4360949 _104522) (@lem4360948 _104522 _104523 t s u)). Qed.
Lemma lem4360957 {_104522 _104523 : Type'} (t : _104523 -> Prop) (s : _104522 -> Prop) (u : _104523 -> Prop) : ((term24 _104522 _104523 s t u) = (term25 _104522 _104523 t s u)) = (term62 _104522 _104523 t s u).
Proof. exact (TRANS (@lem4360880 _104522 _104523 t s u) (@lem4360950 _104522 _104523 t s u)). Qed.
Lemma lem4360958 {_104522 _104523 : Type'} (t : _104523 -> Prop) (s : _104522 -> Prop) : (term63 _104522 _104523 t s) = (term64 _104522 _104523 t s).
Proof. exact (fun_ext (fun u : _104523 -> Prop => @lem4360957 _104522 _104523 t s u)). Qed.
Lemma lem4360959 {_104523 : Type'} : (@all (_104523 -> Prop)) = (@all (_104523 -> Prop)).
Proof. exact (eq_refl (@all (_104523 -> Prop))). Qed.
Lemma lem4360960 {_104522 _104523 : Type'} (t : _104523 -> Prop) (s : _104522 -> Prop) : (term65 _104522 _104523 t s) = (term66 _104522 _104523 t s).
Proof. exact (MK_COMB (@lem4360959 _104523) (@lem4360958 _104522 _104523 t s)). Qed.
Lemma lem4360967 {_104522 _104523 : Type'} (s : _104522 -> Prop) : (term67 _104522 _104523 s) = (term68 _104522 _104523 s).
Proof. exact (fun_ext (fun t : _104523 -> Prop => @lem4360960 _104522 _104523 t s)). Qed.
Lemma lem4360968 {_104523 : Type'} : (@all (_104523 -> Prop)) = (@all (_104523 -> Prop)).
Proof. exact (eq_refl (@all (_104523 -> Prop))). Qed.
Lemma lem4360969 {_104522 _104523 : Type'} (s : _104522 -> Prop) : (term69 _104522 _104523 s) = (term70 _104522 _104523 s).
Proof. exact (MK_COMB (@lem4360968 _104523) (@lem4360967 _104522 _104523 s)). Qed.
Lemma lem4360976 {_104522 _104523 : Type'} : (term71 _104522 _104523) = (term72 _104522 _104523).
Proof. exact (fun_ext (fun s : _104522 -> Prop => @lem4360969 _104522 _104523 s)). Qed.
Lemma lem4360977 {_104522 : Type'} : (@all (_104522 -> Prop)) = (@all (_104522 -> Prop)).
Proof. exact (eq_refl (@all (_104522 -> Prop))). Qed.
Lemma lem4360978 {_104522 _104523 : Type'} : (term73 _104522 _104523) = (term74 _104522 _104523).
Proof. exact (MK_COMB (@lem4360977 _104522) (@lem4360976 _104522 _104523)). Qed.
Lemma lem4360985 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4360986 {_104522 _104523 : Type'} : (term75 _104522 _104523) = (term76 _104522 _104523).
Proof. exact (MK_COMB (@lem4360985) (@lem4360978 _104522 _104523)). Qed.
Lemma lem4361008 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term22 A s t).
Proof. exact (EQ_MP (@lem4360823 A s t) (@lem4360822 A s t)). Qed.
Lemma lem4361009 {_104555 _104556 : Type'} (s : type1210 _104555 _104556) (t : type1210 _104555 _104556) : (s = t) = (term23 _104555 _104556 s t).
Proof. exact (@lem4361008 (prod _104555 _104556) s t). Qed.
Lemma lem4361010 {_104555 _104556 : Type'} (s : _104555 -> Prop) (t : _104555 -> Prop) (u : _104556 -> Prop) : ((term77 _104555 _104556 s t u) = (term78 _104555 _104556 s t u)) = (term79 _104555 _104556 s t u).
Proof. exact (@lem4361009 _104555 _104556 (term77 _104555 _104556 s t u) (term78 _104555 _104556 s t u)). Qed.
Lemma lem4361016 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term17 _5106 _5107 P) = (term18 _5106 _5107 P).
Proof. exact (EQ_MP (@lem4360817 _5106 _5107 P) (@lem4360816 _5106 _5107 P)). Qed.
Lemma lem4361017 {_104555 _104556 : Type'} (P : type1210 _104555 _104556) : (term27 _104555 _104556 P) = (term28 _104555 _104556 P).
Proof. exact (@lem4361016 _104556 _104555 P). Qed.
Lemma lem4361018 {_104555 _104556 : Type'} (s : _104555 -> Prop) (t : _104555 -> Prop) (u : _104556 -> Prop) : (term80 _104555 _104556 s t u) = (term81 _104555 _104556 s t u).
Proof. exact (@lem4361017 _104555 _104556 (term82 _104555 _104556 s t u)). Qed.
Lemma lem4361019 {_104555 _104556 : Type'} (x : prod _104555 _104556) (s : _104555 -> Prop) (t : _104555 -> Prop) (u : _104556 -> Prop) : (term83 _104555 _104556 s t u x) = ((term84 _104555 _104556 x s t u) = (term85 _104555 _104556 x s t u)).
Proof. exact (eq_refl (term83 _104555 _104556 s t u x)). Qed.
Lemma lem4361020 {_104555 _104556 : Type'} (s : _104555 -> Prop) (t : _104555 -> Prop) (u : _104556 -> Prop) : (term86 _104555 _104556 s t u) = (term82 _104555 _104556 s t u).
Proof. exact (fun_ext (fun x : prod _104555 _104556 => @lem4361019 _104555 _104556 x s t u)). Qed.
Lemma lem4361021 {_104555 _104556 : Type'} : (@all (prod _104555 _104556)) = (@all (prod _104555 _104556)).
Proof. exact (eq_refl (@all (prod _104555 _104556))). Qed.
Lemma lem4361022 {_104555 _104556 : Type'} (s : _104555 -> Prop) (t : _104555 -> Prop) (u : _104556 -> Prop) : (term80 _104555 _104556 s t u) = (term79 _104555 _104556 s t u).
Proof. exact (MK_COMB (@lem4361021 _104555 _104556) (@lem4361020 _104555 _104556 s t u)). Qed.
Lemma lem4361023 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4361024 {_104555 _104556 : Type'} (s : _104555 -> Prop) (t : _104555 -> Prop) (u : _104556 -> Prop) : (term87 _104555 _104556 s t u) = (term88 _104555 _104556 s t u).
Proof. exact (MK_COMB (@lem4361023) (@lem4361022 _104555 _104556 s t u)). Qed.
Lemma lem4361025 {_104555 _104556 : Type'} (p1 : _104555) (p2 : _104556) (s : _104555 -> Prop) (t : _104555 -> Prop) (u : _104556 -> Prop) : (term89 _104555 _104556 s t u p1 p2) = ((term90 _104555 _104556 p1 p2 s t u) = (term91 _104555 _104556 p1 p2 s t u)).
Proof. exact (eq_refl (term89 _104555 _104556 s t u p1 p2)). Qed.
Lemma lem4361026 {_104555 _104556 : Type'} (p1 : _104555) (s : _104555 -> Prop) (t : _104555 -> Prop) (u : _104556 -> Prop) : (term92 _104555 _104556 s t u p1) = (term93 _104555 _104556 p1 s t u).
Proof. exact (fun_ext (fun p2 : _104556 => @lem4361025 _104555 _104556 p1 p2 s t u)). Qed.
Lemma lem4361027 {_104556 : Type'} : (@all _104556) = (@all _104556).
Proof. exact (eq_refl (@all _104556)). Qed.
Lemma lem4361028 {_104555 _104556 : Type'} (p1 : _104555) (s : _104555 -> Prop) (t : _104555 -> Prop) (u : _104556 -> Prop) : (term94 _104555 _104556 s t u p1) = (term95 _104555 _104556 p1 s t u).
Proof. exact (MK_COMB (@lem4361027 _104556) (@lem4361026 _104555 _104556 p1 s t u)). Qed.
Lemma lem4361029 {_104555 _104556 : Type'} (s : _104555 -> Prop) (t : _104555 -> Prop) (u : _104556 -> Prop) : (term96 _104555 _104556 s t u) = (term97 _104555 _104556 s t u).
Proof. exact (fun_ext (fun p1 : _104555 => @lem4361028 _104555 _104556 p1 s t u)). Qed.
Lemma lem4361030 {_104555 : Type'} : (@all _104555) = (@all _104555).
Proof. exact (eq_refl (@all _104555)). Qed.
Lemma lem4361031 {_104555 _104556 : Type'} (s : _104555 -> Prop) (t : _104555 -> Prop) (u : _104556 -> Prop) : (term81 _104555 _104556 s t u) = (term98 _104555 _104556 s t u).
Proof. exact (MK_COMB (@lem4361030 _104555) (@lem4361029 _104555 _104556 s t u)). Qed.
Lemma lem4361032 {_104555 _104556 : Type'} (s : _104555 -> Prop) (t : _104555 -> Prop) (u : _104556 -> Prop) : ((term80 _104555 _104556 s t u) = (term81 _104555 _104556 s t u)) = ((term79 _104555 _104556 s t u) = (term98 _104555 _104556 s t u)).
Proof. exact (MK_COMB (@lem4361024 _104555 _104556 s t u) (@lem4361031 _104555 _104556 s t u)). Qed.
Lemma lem4361033 {_104555 _104556 : Type'} (s : _104555 -> Prop) (t : _104555 -> Prop) (u : _104556 -> Prop) : (term79 _104555 _104556 s t u) = (term98 _104555 _104556 s t u).
Proof. exact (EQ_MP (@lem4361032 _104555 _104556 s t u) (@lem4361018 _104555 _104556 s t u)). Qed.
Lemma lem4361040 {_104555 _104556 : Type'} (s : _104555 -> Prop) (t : _104555 -> Prop) (u : _104556 -> Prop) : ((term77 _104555 _104556 s t u) = (term78 _104555 _104556 s t u)) = (term98 _104555 _104556 s t u).
Proof. exact (TRANS (@lem4361010 _104555 _104556 s t u) (@lem4361033 _104555 _104556 s t u)). Qed.
Lemma lem4361052 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term7 _103718 _103721 x y s t) = (term8 _103718 _103721 x s y t).
Proof. exact (EQ_MP (@lem4360805 _103718 _103721 x s y t) (@lem4360804 _103718 _103721 x s y t)). Qed.
Lemma lem4361053 {_104555 _104556 : Type'} (x : _104555) (s : _104555 -> Prop) (y : _104556) (t : _104556 -> Prop) : (term7 _104555 _104556 x y s t) = (term8 _104555 _104556 x s y t).
Proof. exact (@lem4361052 _104555 _104556 x s y t). Qed.
Lemma lem4361054 {_104555 _104556 : Type'} (p1 : _104555) (s : _104555 -> Prop) (t : _104555 -> Prop) (p2 : _104556) (u : _104556 -> Prop) : (term90 _104555 _104556 p1 p2 s t u) = (term99 _104555 _104556 p1 s t p2 u).
Proof. exact (@lem4361053 _104555 _104556 p1 (@UNION _104555 s t) p2 u). Qed.
Lemma lem4361058 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term14 A x s t) = (term15 A s x t).
Proof. exact (EQ_MP (@lem4360814 A s x t) (@lem4360813 A s t x)). Qed.
Lemma lem4361059 {_104555 : Type'} (s : _104555 -> Prop) (x : _104555) (t : _104555 -> Prop) : (term14 _104555 x s t) = (term15 _104555 s x t).
Proof. exact (@lem4361058 _104555 s x t). Qed.
Lemma lem4361060 {_104555 : Type'} (s : _104555 -> Prop) (p1 : _104555) (t : _104555 -> Prop) : (term14 _104555 p1 s t) = (term15 _104555 s p1 t).
Proof. exact (@lem4361059 _104555 s p1 t). Qed.
Lemma lem4361063 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4361064 {_104555 : Type'} (s : _104555 -> Prop) (p1 : _104555) (t : _104555 -> Prop) : (term100 _104555 p1 s t) = (term101 _104555 s p1 t).
Proof. exact (MK_COMB (@lem4361063) (@lem4361060 _104555 s p1 t)). Qed.
Lemma lem4361065 {_104556 : Type'} (p2 : _104556) (u : _104556 -> Prop) : (@IN _104556 p2 u) = (@IN _104556 p2 u).
Proof. exact (eq_refl (@IN _104556 p2 u)). Qed.
Lemma lem4361066 {_104555 _104556 : Type'} (s : _104555 -> Prop) (p1 : _104555) (t : _104555 -> Prop) (p2 : _104556) (u : _104556 -> Prop) : (term99 _104555 _104556 p1 s t p2 u) = (term102 _104555 _104556 s p1 t p2 u).
Proof. exact (MK_COMB (@lem4361064 _104555 s p1 t) (@lem4361065 _104556 p2 u)). Qed.
Lemma lem4361069 {_104555 _104556 : Type'} (s : _104555 -> Prop) (p1 : _104555) (t : _104555 -> Prop) (p2 : _104556) (u : _104556 -> Prop) : (term90 _104555 _104556 p1 p2 s t u) = (term102 _104555 _104556 s p1 t p2 u).
Proof. exact (TRANS (@lem4361054 _104555 _104556 p1 s t p2 u) (@lem4361066 _104555 _104556 s p1 t p2 u)). Qed.
Lemma lem4361070 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4361071 {_104555 _104556 : Type'} (s : _104555 -> Prop) (p1 : _104555) (t : _104555 -> Prop) (p2 : _104556) (u : _104556 -> Prop) : (term103 _104555 _104556 p1 p2 s t u) = (term104 _104555 _104556 s p1 t p2 u).
Proof. exact (MK_COMB (@lem4361070) (@lem4361069 _104555 _104556 s p1 t p2 u)). Qed.
Lemma lem4361073 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term14 A x s t) = (term15 A s x t).
Proof. exact (EQ_MP (@lem4360814 A s x t) (@lem4360813 A s t x)). Qed.
Lemma lem4361074 {_104555 _104556 : Type'} (s : type1210 _104555 _104556) (x : prod _104555 _104556) (t : type1210 _104555 _104556) : (term53 _104555 _104556 x s t) = (term54 _104555 _104556 s x t).
Proof. exact (@lem4361073 (prod _104555 _104556) s x t). Qed.
Lemma lem4361075 {_104555 _104556 : Type'} (s : _104555 -> Prop) (p1 : _104555) (p2 : _104556) (t : _104555 -> Prop) (u : _104556 -> Prop) : (term91 _104555 _104556 p1 p2 s t u) = (term105 _104555 _104556 s p1 p2 t u).
Proof. exact (@lem4361074 _104555 _104556 (@CROSS _104556 _104555 s u) (@pair _104555 _104556 p1 p2) (@CROSS _104556 _104555 t u)). Qed.
Lemma lem4361079 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term7 _103718 _103721 x y s t) = (term8 _103718 _103721 x s y t).
Proof. exact (EQ_MP (@lem4360805 _103718 _103721 x s y t) (@lem4360804 _103718 _103721 x s y t)). Qed.
Lemma lem4361080 {_104555 _104556 : Type'} (x : _104555) (s : _104555 -> Prop) (y : _104556) (t : _104556 -> Prop) : (term7 _104555 _104556 x y s t) = (term8 _104555 _104556 x s y t).
Proof. exact (@lem4361079 _104555 _104556 x s y t). Qed.
Lemma lem4361081 {_104555 _104556 : Type'} (p1 : _104555) (s : _104555 -> Prop) (p2 : _104556) (u : _104556 -> Prop) : (term7 _104555 _104556 p1 p2 s u) = (term8 _104555 _104556 p1 s p2 u).
Proof. exact (@lem4361080 _104555 _104556 p1 s p2 u). Qed.
Lemma lem4361084 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4361085 {_104555 _104556 : Type'} (p1 : _104555) (s : _104555 -> Prop) (p2 : _104556) (u : _104556 -> Prop) : (term56 _104555 _104556 p1 p2 s u) = (term57 _104555 _104556 p1 s p2 u).
Proof. exact (MK_COMB (@lem4361084) (@lem4361081 _104555 _104556 p1 s p2 u)). Qed.
Lemma lem4361087 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term7 _103718 _103721 x y s t) = (term8 _103718 _103721 x s y t).
Proof. exact (EQ_MP (@lem4360805 _103718 _103721 x s y t) (@lem4360804 _103718 _103721 x s y t)). Qed.
Lemma lem4361088 {_104555 _104556 : Type'} (x : _104555) (s : _104555 -> Prop) (y : _104556) (t : _104556 -> Prop) : (term7 _104555 _104556 x y s t) = (term8 _104555 _104556 x s y t).
Proof. exact (@lem4361087 _104555 _104556 x s y t). Qed.
Lemma lem4361089 {_104555 _104556 : Type'} (p1 : _104555) (t : _104555 -> Prop) (p2 : _104556) (u : _104556 -> Prop) : (term7 _104555 _104556 p1 p2 t u) = (term8 _104555 _104556 p1 t p2 u).
Proof. exact (@lem4361088 _104555 _104556 p1 t p2 u). Qed.
Lemma lem4361092 {_104555 _104556 : Type'} (s : _104555 -> Prop) (p1 : _104555) (t : _104555 -> Prop) (p2 : _104556) (u : _104556 -> Prop) : (term105 _104555 _104556 s p1 p2 t u) = (term106 _104555 _104556 s p1 t p2 u).
Proof. exact (MK_COMB (@lem4361085 _104555 _104556 p1 s p2 u) (@lem4361089 _104555 _104556 p1 t p2 u)). Qed.
Lemma lem4361095 {_104555 _104556 : Type'} (s : _104555 -> Prop) (p1 : _104555) (t : _104555 -> Prop) (p2 : _104556) (u : _104556 -> Prop) : (term91 _104555 _104556 p1 p2 s t u) = (term106 _104555 _104556 s p1 t p2 u).
Proof. exact (TRANS (@lem4361075 _104555 _104556 s p1 p2 t u) (@lem4361092 _104555 _104556 s p1 t p2 u)). Qed.
Lemma lem4361096 {_104555 _104556 : Type'} (s : _104555 -> Prop) (p1 : _104555) (t : _104555 -> Prop) (p2 : _104556) (u : _104556 -> Prop) : ((term90 _104555 _104556 p1 p2 s t u) = (term91 _104555 _104556 p1 p2 s t u)) = ((term102 _104555 _104556 s p1 t p2 u) = (term106 _104555 _104556 s p1 t p2 u)).
Proof. exact (MK_COMB (@lem4361071 _104555 _104556 s p1 t p2 u) (@lem4361095 _104555 _104556 s p1 t p2 u)). Qed.
Lemma lem4361101 {_104555 _104556 : Type'} (s : _104555 -> Prop) (p1 : _104555) (t : _104555 -> Prop) (u : _104556 -> Prop) : (term93 _104555 _104556 p1 s t u) = (term107 _104555 _104556 s p1 t u).
Proof. exact (fun_ext (fun p2 : _104556 => @lem4361096 _104555 _104556 s p1 t p2 u)). Qed.
Lemma lem4361102 {_104556 : Type'} : (@all _104556) = (@all _104556).
Proof. exact (eq_refl (@all _104556)). Qed.
Lemma lem4361103 {_104555 _104556 : Type'} (s : _104555 -> Prop) (p1 : _104555) (t : _104555 -> Prop) (u : _104556 -> Prop) : (term95 _104555 _104556 p1 s t u) = (term108 _104555 _104556 s p1 t u).
Proof. exact (MK_COMB (@lem4361102 _104556) (@lem4361101 _104555 _104556 s p1 t u)). Qed.
Lemma lem4361110 {_104555 _104556 : Type'} (s : _104555 -> Prop) (t : _104555 -> Prop) (u : _104556 -> Prop) : (term97 _104555 _104556 s t u) = (term109 _104555 _104556 s t u).
Proof. exact (fun_ext (fun p1 : _104555 => @lem4361103 _104555 _104556 s p1 t u)). Qed.
Lemma lem4361111 {_104555 : Type'} : (@all _104555) = (@all _104555).
Proof. exact (eq_refl (@all _104555)). Qed.
Lemma lem4361112 {_104555 _104556 : Type'} (s : _104555 -> Prop) (t : _104555 -> Prop) (u : _104556 -> Prop) : (term98 _104555 _104556 s t u) = (term110 _104555 _104556 s t u).
Proof. exact (MK_COMB (@lem4361111 _104555) (@lem4361110 _104555 _104556 s t u)). Qed.
Lemma lem4361119 {_104555 _104556 : Type'} (s : _104555 -> Prop) (t : _104555 -> Prop) (u : _104556 -> Prop) : ((term77 _104555 _104556 s t u) = (term78 _104555 _104556 s t u)) = (term110 _104555 _104556 s t u).
Proof. exact (TRANS (@lem4361040 _104555 _104556 s t u) (@lem4361112 _104555 _104556 s t u)). Qed.
Lemma lem4361120 {_104555 _104556 : Type'} (s : _104555 -> Prop) (t : _104555 -> Prop) : (term111 _104555 _104556 s t) = (term112 _104555 _104556 s t).
Proof. exact (fun_ext (fun u : _104556 -> Prop => @lem4361119 _104555 _104556 s t u)). Qed.
Lemma lem4361121 {_104556 : Type'} : (@all (_104556 -> Prop)) = (@all (_104556 -> Prop)).
Proof. exact (eq_refl (@all (_104556 -> Prop))). Qed.
Lemma lem4361122 {_104555 _104556 : Type'} (s : _104555 -> Prop) (t : _104555 -> Prop) : (term113 _104555 _104556 s t) = (term114 _104555 _104556 s t).
Proof. exact (MK_COMB (@lem4361121 _104556) (@lem4361120 _104555 _104556 s t)). Qed.
Lemma lem4361129 {_104555 _104556 : Type'} (s : _104555 -> Prop) : (term115 _104555 _104556 s) = (term116 _104555 _104556 s).
Proof. exact (fun_ext (fun t : _104555 -> Prop => @lem4361122 _104555 _104556 s t)). Qed.
Lemma lem4361130 {_104555 : Type'} : (@all (_104555 -> Prop)) = (@all (_104555 -> Prop)).
Proof. exact (eq_refl (@all (_104555 -> Prop))). Qed.
Lemma lem4361131 {_104555 _104556 : Type'} (s : _104555 -> Prop) : (term117 _104555 _104556 s) = (term118 _104555 _104556 s).
Proof. exact (MK_COMB (@lem4361130 _104555) (@lem4361129 _104555 _104556 s)). Qed.
Lemma lem4361138 {_104555 _104556 : Type'} : (term119 _104555 _104556) = (term120 _104555 _104556).
Proof. exact (fun_ext (fun s : _104555 -> Prop => @lem4361131 _104555 _104556 s)). Qed.
Lemma lem4361139 {_104555 : Type'} : (@all (_104555 -> Prop)) = (@all (_104555 -> Prop)).
Proof. exact (eq_refl (@all (_104555 -> Prop))). Qed.
Lemma lem4361140 {_104555 _104556 : Type'} : (term121 _104555 _104556) = (term122 _104555 _104556).
Proof. exact (MK_COMB (@lem4361139 _104555) (@lem4361138 _104555 _104556)). Qed.
Lemma lem4361147 {_104522 _104523 _104555 _104556 : Type'} : (term123 _104522 _104523 _104555 _104556) = (term124 _104522 _104523 _104555 _104556).
Proof. exact (MK_COMB (@lem4360986 _104522 _104523) (@lem4361140 _104555 _104556)). Qed.
Lemma lem4361150 {_104522 _104523 _104555 _104556 : Type'} : (term124 _104522 _104523 _104555 _104556) = (term123 _104522 _104523 _104555 _104556).
Proof. exact (SYM (@lem4361147 _104522 _104523 _104555 _104556)). Qed.
Lemma lem4361165 {_104522 : Type'} (p1 : _104522) (s : _104522 -> Prop) : term125 _104522 p1 s.
Proof. exact (@lem9851 (@IN _104522 p1 s)). Qed.
Lemma lem4361166 {_104522 : Type'} (p1 : _104522) (s : _104522 -> Prop) : (term125 _104522 p1 s) = (term126 _104522 p1 s).
Proof. exact (eq_refl (term125 _104522 p1 s)). Qed.
Lemma lem4361167 {_104522 : Type'} (p1 : _104522) (s : _104522 -> Prop) : term126 _104522 p1 s.
Proof. exact (EQ_MP (@lem4361166 _104522 p1 s) (@lem4361165 _104522 p1 s)). Qed.
Lemma lem4361168 {_104522 : Type'} (p1 : _104522) (s : _104522 -> Prop) (h1 : (@IN _104522 p1 s) = True) : (@IN _104522 p1 s) = True.
Proof. exact (h1). Qed.
Lemma lem4361169 {_104522 : Type'} (p1 : _104522) (s : _104522 -> Prop) (h1 : (@IN _104522 p1 s) = False) : (@IN _104522 p1 s) = False.
Proof. exact (h1). Qed.
Lemma lem4361184 {_104523 : Type'} (t : _104523 -> Prop) (p2 : _104523) (u : _104523 -> Prop) : (term127 _104523 t p2 u) = (term127 _104523 t p2 u).
Proof. exact (eq_refl (term127 _104523 t p2 u)). Qed.
Lemma lem4361185 {_104522 _104523 : Type'} (t : _104523 -> Prop) (p2 : _104523) (u : _104523 -> Prop) (p1 : _104522) (s : _104522 -> Prop) (h1 : (@IN _104522 p1 s) = True) : (term128 _104522 _104523 t p2 u p1 s) = (term129 _104523 t p2 u).
Proof. exact (MK_COMB (@lem4361184 _104523 t p2 u) (@lem4361168 _104522 p1 s h1)). Qed.
Lemma lem4361186 {_104523 : Type'} (t : _104523 -> Prop) (p2 : _104523) (u : _104523 -> Prop) : (term129 _104523 t p2 u) = ((term130 _104523 t p2 u) = (term131 _104523 t p2 u)).
Proof. exact (eq_refl (term129 _104523 t p2 u)). Qed.
Lemma lem4361187 {_104522 _104523 : Type'} (t : _104523 -> Prop) (p2 : _104523) (u : _104523 -> Prop) (p1 : _104522) (s : _104522 -> Prop) : (term132 _104522 _104523 t p2 u p1 s) = (term132 _104522 _104523 t p2 u p1 s).
Proof. exact (eq_refl (term132 _104522 _104523 t p2 u p1 s)). Qed.
Lemma lem4361188 {_104522 _104523 : Type'} (p1 : _104522) (s : _104522 -> Prop) (t : _104523 -> Prop) (p2 : _104523) (u : _104523 -> Prop) : ((term128 _104522 _104523 t p2 u p1 s) = (term129 _104523 t p2 u)) = ((term128 _104522 _104523 t p2 u p1 s) = ((term130 _104523 t p2 u) = (term131 _104523 t p2 u))).
Proof. exact (MK_COMB (@lem4361187 _104522 _104523 t p2 u p1 s) (@lem4361186 _104523 t p2 u)). Qed.
Lemma lem4361189 {_104522 _104523 : Type'} (t : _104523 -> Prop) (p1 : _104522) (s : _104522 -> Prop) (p2 : _104523) (u : _104523 -> Prop) : (term128 _104522 _104523 t p2 u p1 s) = ((term50 _104522 _104523 p1 s t p2 u) = (term58 _104522 _104523 t p1 s p2 u)).
Proof. exact (eq_refl (term128 _104522 _104523 t p2 u p1 s)). Qed.
Lemma lem4361190 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4361191 {_104522 _104523 : Type'} (t : _104523 -> Prop) (p1 : _104522) (s : _104522 -> Prop) (p2 : _104523) (u : _104523 -> Prop) : (term132 _104522 _104523 t p2 u p1 s) = (term133 _104522 _104523 t p1 s p2 u).
Proof. exact (MK_COMB (@lem4361190) (@lem4361189 _104522 _104523 t p1 s p2 u)). Qed.
Lemma lem4361192 {_104523 : Type'} (t : _104523 -> Prop) (p2 : _104523) (u : _104523 -> Prop) : ((term130 _104523 t p2 u) = (term131 _104523 t p2 u)) = ((term130 _104523 t p2 u) = (term131 _104523 t p2 u)).
Proof. exact (eq_refl ((term130 _104523 t p2 u) = (term131 _104523 t p2 u))). Qed.
Lemma lem4361193 {_104522 _104523 : Type'} (p1 : _104522) (s : _104522 -> Prop) (t : _104523 -> Prop) (p2 : _104523) (u : _104523 -> Prop) : ((term128 _104522 _104523 t p2 u p1 s) = ((term130 _104523 t p2 u) = (term131 _104523 t p2 u))) = (((term50 _104522 _104523 p1 s t p2 u) = (term58 _104522 _104523 t p1 s p2 u)) = ((term130 _104523 t p2 u) = (term131 _104523 t p2 u))).
Proof. exact (MK_COMB (@lem4361191 _104522 _104523 t p1 s p2 u) (@lem4361192 _104523 t p2 u)). Qed.
Lemma lem4361194 {_104522 _104523 : Type'} (p1 : _104522) (s : _104522 -> Prop) (t : _104523 -> Prop) (p2 : _104523) (u : _104523 -> Prop) : ((term128 _104522 _104523 t p2 u p1 s) = (term129 _104523 t p2 u)) = (((term50 _104522 _104523 p1 s t p2 u) = (term58 _104522 _104523 t p1 s p2 u)) = ((term130 _104523 t p2 u) = (term131 _104523 t p2 u))).
Proof. exact (TRANS (@lem4361188 _104522 _104523 p1 s t p2 u) (@lem4361193 _104522 _104523 p1 s t p2 u)). Qed.
Lemma lem4361195 {_104522 _104523 : Type'} (t : _104523 -> Prop) (p2 : _104523) (u : _104523 -> Prop) (p1 : _104522) (s : _104522 -> Prop) (h1 : (@IN _104522 p1 s) = True) : ((term50 _104522 _104523 p1 s t p2 u) = (term58 _104522 _104523 t p1 s p2 u)) = ((term130 _104523 t p2 u) = (term131 _104523 t p2 u)).
Proof. exact (EQ_MP (@lem4361194 _104522 _104523 p1 s t p2 u) (@lem4361185 _104522 _104523 t p2 u p1 s h1)). Qed.
Lemma lem4361196 {_104522 _104523 : Type'} (t : _104523 -> Prop) (p2 : _104523) (u : _104523 -> Prop) (p1 : _104522) (s : _104522 -> Prop) (h1 : (@IN _104522 p1 s) = True) : ((term130 _104523 t p2 u) = (term131 _104523 t p2 u)) = ((term50 _104522 _104523 p1 s t p2 u) = (term58 _104522 _104523 t p1 s p2 u)).
Proof. exact (SYM (@lem4361195 _104522 _104523 t p2 u p1 s h1)). Qed.
Lemma lem4361197 {_104523 : Type'} (t : _104523 -> Prop) (p2 : _104523) (u : _104523 -> Prop) : (term127 _104523 t p2 u) = (term127 _104523 t p2 u).
Proof. exact (eq_refl (term127 _104523 t p2 u)). Qed.
Lemma lem4361198 {_104522 _104523 : Type'} (t : _104523 -> Prop) (p2 : _104523) (u : _104523 -> Prop) (p1 : _104522) (s : _104522 -> Prop) (h1 : (@IN _104522 p1 s) = False) : (term128 _104522 _104523 t p2 u p1 s) = (term134 _104523 t p2 u).
Proof. exact (MK_COMB (@lem4361197 _104523 t p2 u) (@lem4361169 _104522 p1 s h1)). Qed.
Lemma lem4361199 {_104523 : Type'} (t : _104523 -> Prop) (p2 : _104523) (u : _104523 -> Prop) : (term134 _104523 t p2 u) = ((term135 _104523 t p2 u) = (term136 _104523 t p2 u)).
Proof. exact (eq_refl (term134 _104523 t p2 u)). Qed.
Lemma lem4361200 {_104522 _104523 : Type'} (t : _104523 -> Prop) (p2 : _104523) (u : _104523 -> Prop) (p1 : _104522) (s : _104522 -> Prop) : (term132 _104522 _104523 t p2 u p1 s) = (term132 _104522 _104523 t p2 u p1 s).
Proof. exact (eq_refl (term132 _104522 _104523 t p2 u p1 s)). Qed.
Lemma lem4361201 {_104522 _104523 : Type'} (p1 : _104522) (s : _104522 -> Prop) (t : _104523 -> Prop) (p2 : _104523) (u : _104523 -> Prop) : ((term128 _104522 _104523 t p2 u p1 s) = (term134 _104523 t p2 u)) = ((term128 _104522 _104523 t p2 u p1 s) = ((term135 _104523 t p2 u) = (term136 _104523 t p2 u))).
Proof. exact (MK_COMB (@lem4361200 _104522 _104523 t p2 u p1 s) (@lem4361199 _104523 t p2 u)). Qed.
Lemma lem4361202 {_104522 _104523 : Type'} (t : _104523 -> Prop) (p1 : _104522) (s : _104522 -> Prop) (p2 : _104523) (u : _104523 -> Prop) : (term128 _104522 _104523 t p2 u p1 s) = ((term50 _104522 _104523 p1 s t p2 u) = (term58 _104522 _104523 t p1 s p2 u)).
Proof. exact (eq_refl (term128 _104522 _104523 t p2 u p1 s)). Qed.
Lemma lem4361203 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4361204 {_104522 _104523 : Type'} (t : _104523 -> Prop) (p1 : _104522) (s : _104522 -> Prop) (p2 : _104523) (u : _104523 -> Prop) : (term132 _104522 _104523 t p2 u p1 s) = (term133 _104522 _104523 t p1 s p2 u).
Proof. exact (MK_COMB (@lem4361203) (@lem4361202 _104522 _104523 t p1 s p2 u)). Qed.
Lemma lem4361205 {_104523 : Type'} (t : _104523 -> Prop) (p2 : _104523) (u : _104523 -> Prop) : ((term135 _104523 t p2 u) = (term136 _104523 t p2 u)) = ((term135 _104523 t p2 u) = (term136 _104523 t p2 u)).
Proof. exact (eq_refl ((term135 _104523 t p2 u) = (term136 _104523 t p2 u))). Qed.
Lemma lem4361206 {_104522 _104523 : Type'} (p1 : _104522) (s : _104522 -> Prop) (t : _104523 -> Prop) (p2 : _104523) (u : _104523 -> Prop) : ((term128 _104522 _104523 t p2 u p1 s) = ((term135 _104523 t p2 u) = (term136 _104523 t p2 u))) = (((term50 _104522 _104523 p1 s t p2 u) = (term58 _104522 _104523 t p1 s p2 u)) = ((term135 _104523 t p2 u) = (term136 _104523 t p2 u))).
Proof. exact (MK_COMB (@lem4361204 _104522 _104523 t p1 s p2 u) (@lem4361205 _104523 t p2 u)). Qed.
Lemma lem4361207 {_104522 _104523 : Type'} (p1 : _104522) (s : _104522 -> Prop) (t : _104523 -> Prop) (p2 : _104523) (u : _104523 -> Prop) : ((term128 _104522 _104523 t p2 u p1 s) = (term134 _104523 t p2 u)) = (((term50 _104522 _104523 p1 s t p2 u) = (term58 _104522 _104523 t p1 s p2 u)) = ((term135 _104523 t p2 u) = (term136 _104523 t p2 u))).
Proof. exact (TRANS (@lem4361201 _104522 _104523 p1 s t p2 u) (@lem4361206 _104522 _104523 p1 s t p2 u)). Qed.
Lemma lem4361208 {_104522 _104523 : Type'} (t : _104523 -> Prop) (p2 : _104523) (u : _104523 -> Prop) (p1 : _104522) (s : _104522 -> Prop) (h1 : (@IN _104522 p1 s) = False) : ((term50 _104522 _104523 p1 s t p2 u) = (term58 _104522 _104523 t p1 s p2 u)) = ((term135 _104523 t p2 u) = (term136 _104523 t p2 u)).
Proof. exact (EQ_MP (@lem4361207 _104522 _104523 p1 s t p2 u) (@lem4361198 _104522 _104523 t p2 u p1 s h1)). Qed.
Lemma lem4361209 {_104522 _104523 : Type'} (t : _104523 -> Prop) (p2 : _104523) (u : _104523 -> Prop) (p1 : _104522) (s : _104522 -> Prop) (h1 : (@IN _104522 p1 s) = False) : ((term135 _104523 t p2 u) = (term136 _104523 t p2 u)) = ((term50 _104522 _104523 p1 s t p2 u) = (term58 _104522 _104523 t p1 s p2 u)).
Proof. exact (SYM (@lem4361208 _104522 _104523 t p2 u p1 s h1)). Qed.
Lemma lem4361213 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4361214 {_104523 : Type'} (t : _104523 -> Prop) (p2 : _104523) (u : _104523 -> Prop) : (term130 _104523 t p2 u) = (term15 _104523 t p2 u).
Proof. exact (@lem4361213 (term15 _104523 t p2 u)). Qed.
Lemma lem4361217 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4361218 {_104523 : Type'} (t : _104523 -> Prop) (p2 : _104523) (u : _104523 -> Prop) : (term137 _104523 t p2 u) = (term138 _104523 t p2 u).
Proof. exact (MK_COMB (@lem4361217) (@lem4361214 _104523 t p2 u)). Qed.
Lemma lem4361222 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4361223 {_104523 : Type'} (p2 : _104523) (t : _104523 -> Prop) : (term139 _104523 p2 t) = (@IN _104523 p2 t).
Proof. exact (@lem4361222 (@IN _104523 p2 t)). Qed.
Lemma lem4361224 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4361225 {_104523 : Type'} (p2 : _104523) (t : _104523 -> Prop) : (term140 _104523 p2 t) = (term141 _104523 p2 t).
Proof. exact (MK_COMB (@lem4361224) (@lem4361223 _104523 p2 t)). Qed.
Lemma lem4361227 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4361228 {_104523 : Type'} (p2 : _104523) (u : _104523 -> Prop) : (term139 _104523 p2 u) = (@IN _104523 p2 u).
Proof. exact (@lem4361227 (@IN _104523 p2 u)). Qed.
Lemma lem4361229 {_104523 : Type'} (t : _104523 -> Prop) (p2 : _104523) (u : _104523 -> Prop) : (term131 _104523 t p2 u) = (term15 _104523 t p2 u).
Proof. exact (MK_COMB (@lem4361225 _104523 p2 t) (@lem4361228 _104523 p2 u)). Qed.
Lemma lem4361232 {_104523 : Type'} (t : _104523 -> Prop) (p2 : _104523) (u : _104523 -> Prop) : ((term130 _104523 t p2 u) = (term131 _104523 t p2 u)) = ((term15 _104523 t p2 u) = (term15 _104523 t p2 u)).
Proof. exact (MK_COMB (@lem4361218 _104523 t p2 u) (@lem4361229 _104523 t p2 u)). Qed.
Lemma lem4361234 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4361235 (x : Prop) : (x = x) = True.
Proof. exact (@lem4361234 Prop x). Qed.
Lemma lem4361236 {_104523 : Type'} (t : _104523 -> Prop) (p2 : _104523) (u : _104523 -> Prop) : ((term15 _104523 t p2 u) = (term15 _104523 t p2 u)) = True.
Proof. exact (@lem4361235 (term15 _104523 t p2 u)). Qed.
Lemma lem4361237 {_104523 : Type'} (t : _104523 -> Prop) (p2 : _104523) (u : _104523 -> Prop) : ((term130 _104523 t p2 u) = (term131 _104523 t p2 u)) = True.
Proof. exact (TRANS (@lem4361232 _104523 t p2 u) (@lem4361236 _104523 t p2 u)). Qed.
Lemma lem4361238 {_104523 : Type'} (t : _104523 -> Prop) (p2 : _104523) (u : _104523 -> Prop) : True = ((term130 _104523 t p2 u) = (term131 _104523 t p2 u)).
Proof. exact (SYM (@lem4361237 _104523 t p2 u)). Qed.
Lemma lem4361239 {_104523 : Type'} (t : _104523 -> Prop) (p2 : _104523) (u : _104523 -> Prop) : (term130 _104523 t p2 u) = (term131 _104523 t p2 u).
Proof. exact (EQ_MP (@lem4361238 _104523 t p2 u) (@lem0)). Qed.
Lemma lem4361243 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem4361244 {_104523 : Type'} (t : _104523 -> Prop) (p2 : _104523) (u : _104523 -> Prop) : (term135 _104523 t p2 u) = False.
Proof. exact (@lem4361243 (term15 _104523 t p2 u)). Qed.
Lemma lem4361245 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4361246 {_104523 : Type'} (t : _104523 -> Prop) (p2 : _104523) (u : _104523 -> Prop) : (term142 _104523 t p2 u) = (@eq Prop False).
Proof. exact (MK_COMB (@lem4361245) (@lem4361244 _104523 t p2 u)). Qed.
Lemma lem4361250 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem4361251 {_104523 : Type'} (p2 : _104523) (t : _104523 -> Prop) : (term143 _104523 p2 t) = False.
Proof. exact (@lem4361250 (@IN _104523 p2 t)). Qed.
Lemma lem4361252 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4361253 {_104523 : Type'} (p2 : _104523) (t : _104523 -> Prop) : (term144 _104523 p2 t) = (or False).
Proof. exact (MK_COMB (@lem4361252) (@lem4361251 _104523 p2 t)). Qed.
Lemma lem4361255 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem4361256 {_104523 : Type'} (p2 : _104523) (u : _104523 -> Prop) : (term143 _104523 p2 u) = False.
Proof. exact (@lem4361255 (@IN _104523 p2 u)). Qed.
Lemma lem4361257 {_104523 : Type'} (t : _104523 -> Prop) (p2 : _104523) (u : _104523 -> Prop) : (term136 _104523 t p2 u) = (False \/ False).
Proof. exact (MK_COMB (@lem4361253 _104523 p2 t) (@lem4361256 _104523 p2 u)). Qed.
Lemma lem4361259 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem4361260 : (False \/ False) = False.
Proof. exact (@lem4361259 False). Qed.
Lemma lem4361261 {_104523 : Type'} (t : _104523 -> Prop) (p2 : _104523) (u : _104523 -> Prop) : (term136 _104523 t p2 u) = False.
Proof. exact (TRANS (@lem4361257 _104523 t p2 u) (@lem4361260)). Qed.
Lemma lem4361262 {_104523 : Type'} (t : _104523 -> Prop) (p2 : _104523) (u : _104523 -> Prop) : ((term135 _104523 t p2 u) = (term136 _104523 t p2 u)) = (False = False).
Proof. exact (MK_COMB (@lem4361246 _104523 t p2 u) (@lem4361261 _104523 t p2 u)). Qed.
Lemma lem4361264 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem4361265 : (False = False) = (~ False).
Proof. exact (@lem4361264 False). Qed.
Lemma lem4361267 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem4361268 : (False = False) = True.
Proof. exact (TRANS (@lem4361265) (@lem4361267)). Qed.
Lemma lem4361269 {_104523 : Type'} (t : _104523 -> Prop) (p2 : _104523) (u : _104523 -> Prop) : ((term135 _104523 t p2 u) = (term136 _104523 t p2 u)) = True.
Proof. exact (TRANS (@lem4361262 _104523 t p2 u) (@lem4361268)). Qed.
Lemma lem4361270 {_104523 : Type'} (t : _104523 -> Prop) (p2 : _104523) (u : _104523 -> Prop) : True = ((term135 _104523 t p2 u) = (term136 _104523 t p2 u)).
Proof. exact (SYM (@lem4361269 _104523 t p2 u)). Qed.
Lemma lem4361271 {_104523 : Type'} (t : _104523 -> Prop) (p2 : _104523) (u : _104523 -> Prop) : (term135 _104523 t p2 u) = (term136 _104523 t p2 u).
Proof. exact (EQ_MP (@lem4361270 _104523 t p2 u) (@lem0)). Qed.
Lemma lem4361272 {_104522 _104523 : Type'} (t : _104523 -> Prop) (p2 : _104523) (u : _104523 -> Prop) (p1 : _104522) (s : _104522 -> Prop) (h1 : (@IN _104522 p1 s) = False) : (term50 _104522 _104523 p1 s t p2 u) = (term58 _104522 _104523 t p1 s p2 u).
Proof. exact (EQ_MP (@lem4361209 _104522 _104523 t p2 u p1 s h1) (@lem4361271 _104523 t p2 u)). Qed.
Lemma lem4361273 {_104522 _104523 : Type'} (t : _104523 -> Prop) (p2 : _104523) (u : _104523 -> Prop) (p1 : _104522) (s : _104522 -> Prop) (h1 : (@IN _104522 p1 s) = True) : (term50 _104522 _104523 p1 s t p2 u) = (term58 _104522 _104523 t p1 s p2 u).
Proof. exact (EQ_MP (@lem4361196 _104522 _104523 t p2 u p1 s h1) (@lem4361239 _104523 t p2 u)). Qed.
Lemma lem4361276 {_104522 _104523 : Type'} (t : _104523 -> Prop) (p1 : _104522) (s : _104522 -> Prop) (p2 : _104523) (u : _104523 -> Prop) : (term50 _104522 _104523 p1 s t p2 u) = (term58 _104522 _104523 t p1 s p2 u).
Proof. exact (or_elim (@lem4361167 _104522 p1 s) (fun h0 : (@IN _104522 p1 s) = True => @lem4361273 _104522 _104523 t p2 u p1 s h0) (fun h0 : (@IN _104522 p1 s) = False => @lem4361272 _104522 _104523 t p2 u p1 s h0)). Qed.
Lemma lem4361291 {_104555 : Type'} (p1 : _104555) (s : _104555 -> Prop) : term125 _104555 p1 s.
Proof. exact (@lem9851 (@IN _104555 p1 s)). Qed.
Lemma lem4361292 {_104555 : Type'} (p1 : _104555) (s : _104555 -> Prop) : (term125 _104555 p1 s) = (term126 _104555 p1 s).
Proof. exact (eq_refl (term125 _104555 p1 s)). Qed.
Lemma lem4361293 {_104555 : Type'} (p1 : _104555) (s : _104555 -> Prop) : term126 _104555 p1 s.
Proof. exact (EQ_MP (@lem4361292 _104555 p1 s) (@lem4361291 _104555 p1 s)). Qed.
Lemma lem4361294 {_104555 : Type'} (p1 : _104555) (s : _104555 -> Prop) (h1 : (@IN _104555 p1 s) = True) : (@IN _104555 p1 s) = True.
Proof. exact (h1). Qed.
Lemma lem4361295 {_104555 : Type'} (p1 : _104555) (s : _104555 -> Prop) (h1 : (@IN _104555 p1 s) = False) : (@IN _104555 p1 s) = False.
Proof. exact (h1). Qed.
Lemma lem4361310 {_104555 _104556 : Type'} (p1 : _104555) (t : _104555 -> Prop) (p2 : _104556) (u : _104556 -> Prop) : (term145 _104555 _104556 p1 t p2 u) = (term145 _104555 _104556 p1 t p2 u).
Proof. exact (eq_refl (term145 _104555 _104556 p1 t p2 u)). Qed.
Lemma lem4361311 {_104555 _104556 : Type'} (t : _104555 -> Prop) (p2 : _104556) (u : _104556 -> Prop) (p1 : _104555) (s : _104555 -> Prop) (h1 : (@IN _104555 p1 s) = True) : (term146 _104555 _104556 t p2 u p1 s) = (term147 _104555 _104556 p1 t p2 u).
Proof. exact (MK_COMB (@lem4361310 _104555 _104556 p1 t p2 u) (@lem4361294 _104555 p1 s h1)). Qed.
Lemma lem4361312 {_104555 _104556 : Type'} (p1 : _104555) (t : _104555 -> Prop) (p2 : _104556) (u : _104556 -> Prop) : (term147 _104555 _104556 p1 t p2 u) = ((term148 _104555 _104556 p1 t p2 u) = (term149 _104555 _104556 p1 t p2 u)).
Proof. exact (eq_refl (term147 _104555 _104556 p1 t p2 u)). Qed.
Lemma lem4361313 {_104555 _104556 : Type'} (t : _104555 -> Prop) (p2 : _104556) (u : _104556 -> Prop) (p1 : _104555) (s : _104555 -> Prop) : (term150 _104555 _104556 t p2 u p1 s) = (term150 _104555 _104556 t p2 u p1 s).
Proof. exact (eq_refl (term150 _104555 _104556 t p2 u p1 s)). Qed.
Lemma lem4361314 {_104555 _104556 : Type'} (s : _104555 -> Prop) (p1 : _104555) (t : _104555 -> Prop) (p2 : _104556) (u : _104556 -> Prop) : ((term146 _104555 _104556 t p2 u p1 s) = (term147 _104555 _104556 p1 t p2 u)) = ((term146 _104555 _104556 t p2 u p1 s) = ((term148 _104555 _104556 p1 t p2 u) = (term149 _104555 _104556 p1 t p2 u))).
Proof. exact (MK_COMB (@lem4361313 _104555 _104556 t p2 u p1 s) (@lem4361312 _104555 _104556 p1 t p2 u)). Qed.
Lemma lem4361315 {_104555 _104556 : Type'} (s : _104555 -> Prop) (p1 : _104555) (t : _104555 -> Prop) (p2 : _104556) (u : _104556 -> Prop) : (term146 _104555 _104556 t p2 u p1 s) = ((term102 _104555 _104556 s p1 t p2 u) = (term106 _104555 _104556 s p1 t p2 u)).
Proof. exact (eq_refl (term146 _104555 _104556 t p2 u p1 s)). Qed.
Lemma lem4361316 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4361317 {_104555 _104556 : Type'} (s : _104555 -> Prop) (p1 : _104555) (t : _104555 -> Prop) (p2 : _104556) (u : _104556 -> Prop) : (term150 _104555 _104556 t p2 u p1 s) = (term151 _104555 _104556 s p1 t p2 u).
Proof. exact (MK_COMB (@lem4361316) (@lem4361315 _104555 _104556 s p1 t p2 u)). Qed.
Lemma lem4361318 {_104555 _104556 : Type'} (p1 : _104555) (t : _104555 -> Prop) (p2 : _104556) (u : _104556 -> Prop) : ((term148 _104555 _104556 p1 t p2 u) = (term149 _104555 _104556 p1 t p2 u)) = ((term148 _104555 _104556 p1 t p2 u) = (term149 _104555 _104556 p1 t p2 u)).
Proof. exact (eq_refl ((term148 _104555 _104556 p1 t p2 u) = (term149 _104555 _104556 p1 t p2 u))). Qed.
Lemma lem4361319 {_104555 _104556 : Type'} (s : _104555 -> Prop) (p1 : _104555) (t : _104555 -> Prop) (p2 : _104556) (u : _104556 -> Prop) : ((term146 _104555 _104556 t p2 u p1 s) = ((term148 _104555 _104556 p1 t p2 u) = (term149 _104555 _104556 p1 t p2 u))) = (((term102 _104555 _104556 s p1 t p2 u) = (term106 _104555 _104556 s p1 t p2 u)) = ((term148 _104555 _104556 p1 t p2 u) = (term149 _104555 _104556 p1 t p2 u))).
Proof. exact (MK_COMB (@lem4361317 _104555 _104556 s p1 t p2 u) (@lem4361318 _104555 _104556 p1 t p2 u)). Qed.
Lemma lem4361320 {_104555 _104556 : Type'} (s : _104555 -> Prop) (p1 : _104555) (t : _104555 -> Prop) (p2 : _104556) (u : _104556 -> Prop) : ((term146 _104555 _104556 t p2 u p1 s) = (term147 _104555 _104556 p1 t p2 u)) = (((term102 _104555 _104556 s p1 t p2 u) = (term106 _104555 _104556 s p1 t p2 u)) = ((term148 _104555 _104556 p1 t p2 u) = (term149 _104555 _104556 p1 t p2 u))).
Proof. exact (TRANS (@lem4361314 _104555 _104556 s p1 t p2 u) (@lem4361319 _104555 _104556 s p1 t p2 u)). Qed.
Lemma lem4361321 {_104555 _104556 : Type'} (t : _104555 -> Prop) (p2 : _104556) (u : _104556 -> Prop) (p1 : _104555) (s : _104555 -> Prop) (h1 : (@IN _104555 p1 s) = True) : ((term102 _104555 _104556 s p1 t p2 u) = (term106 _104555 _104556 s p1 t p2 u)) = ((term148 _104555 _104556 p1 t p2 u) = (term149 _104555 _104556 p1 t p2 u)).
Proof. exact (EQ_MP (@lem4361320 _104555 _104556 s p1 t p2 u) (@lem4361311 _104555 _104556 t p2 u p1 s h1)). Qed.
Lemma lem4361322 {_104555 _104556 : Type'} (t : _104555 -> Prop) (p2 : _104556) (u : _104556 -> Prop) (p1 : _104555) (s : _104555 -> Prop) (h1 : (@IN _104555 p1 s) = True) : ((term148 _104555 _104556 p1 t p2 u) = (term149 _104555 _104556 p1 t p2 u)) = ((term102 _104555 _104556 s p1 t p2 u) = (term106 _104555 _104556 s p1 t p2 u)).
Proof. exact (SYM (@lem4361321 _104555 _104556 t p2 u p1 s h1)). Qed.
Lemma lem4361323 {_104555 _104556 : Type'} (p1 : _104555) (t : _104555 -> Prop) (p2 : _104556) (u : _104556 -> Prop) : (term145 _104555 _104556 p1 t p2 u) = (term145 _104555 _104556 p1 t p2 u).
Proof. exact (eq_refl (term145 _104555 _104556 p1 t p2 u)). Qed.
Lemma lem4361324 {_104555 _104556 : Type'} (t : _104555 -> Prop) (p2 : _104556) (u : _104556 -> Prop) (p1 : _104555) (s : _104555 -> Prop) (h1 : (@IN _104555 p1 s) = False) : (term146 _104555 _104556 t p2 u p1 s) = (term152 _104555 _104556 p1 t p2 u).
Proof. exact (MK_COMB (@lem4361323 _104555 _104556 p1 t p2 u) (@lem4361295 _104555 p1 s h1)). Qed.
Lemma lem4361325 {_104555 _104556 : Type'} (p1 : _104555) (t : _104555 -> Prop) (p2 : _104556) (u : _104556 -> Prop) : (term152 _104555 _104556 p1 t p2 u) = ((term153 _104555 _104556 p1 t p2 u) = (term154 _104555 _104556 p1 t p2 u)).
Proof. exact (eq_refl (term152 _104555 _104556 p1 t p2 u)). Qed.
Lemma lem4361326 {_104555 _104556 : Type'} (t : _104555 -> Prop) (p2 : _104556) (u : _104556 -> Prop) (p1 : _104555) (s : _104555 -> Prop) : (term150 _104555 _104556 t p2 u p1 s) = (term150 _104555 _104556 t p2 u p1 s).
Proof. exact (eq_refl (term150 _104555 _104556 t p2 u p1 s)). Qed.
Lemma lem4361327 {_104555 _104556 : Type'} (s : _104555 -> Prop) (p1 : _104555) (t : _104555 -> Prop) (p2 : _104556) (u : _104556 -> Prop) : ((term146 _104555 _104556 t p2 u p1 s) = (term152 _104555 _104556 p1 t p2 u)) = ((term146 _104555 _104556 t p2 u p1 s) = ((term153 _104555 _104556 p1 t p2 u) = (term154 _104555 _104556 p1 t p2 u))).
Proof. exact (MK_COMB (@lem4361326 _104555 _104556 t p2 u p1 s) (@lem4361325 _104555 _104556 p1 t p2 u)). Qed.
Lemma lem4361328 {_104555 _104556 : Type'} (s : _104555 -> Prop) (p1 : _104555) (t : _104555 -> Prop) (p2 : _104556) (u : _104556 -> Prop) : (term146 _104555 _104556 t p2 u p1 s) = ((term102 _104555 _104556 s p1 t p2 u) = (term106 _104555 _104556 s p1 t p2 u)).
Proof. exact (eq_refl (term146 _104555 _104556 t p2 u p1 s)). Qed.
Lemma lem4361329 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4361330 {_104555 _104556 : Type'} (s : _104555 -> Prop) (p1 : _104555) (t : _104555 -> Prop) (p2 : _104556) (u : _104556 -> Prop) : (term150 _104555 _104556 t p2 u p1 s) = (term151 _104555 _104556 s p1 t p2 u).
Proof. exact (MK_COMB (@lem4361329) (@lem4361328 _104555 _104556 s p1 t p2 u)). Qed.
Lemma lem4361331 {_104555 _104556 : Type'} (p1 : _104555) (t : _104555 -> Prop) (p2 : _104556) (u : _104556 -> Prop) : ((term153 _104555 _104556 p1 t p2 u) = (term154 _104555 _104556 p1 t p2 u)) = ((term153 _104555 _104556 p1 t p2 u) = (term154 _104555 _104556 p1 t p2 u)).
Proof. exact (eq_refl ((term153 _104555 _104556 p1 t p2 u) = (term154 _104555 _104556 p1 t p2 u))). Qed.
Lemma lem4361332 {_104555 _104556 : Type'} (s : _104555 -> Prop) (p1 : _104555) (t : _104555 -> Prop) (p2 : _104556) (u : _104556 -> Prop) : ((term146 _104555 _104556 t p2 u p1 s) = ((term153 _104555 _104556 p1 t p2 u) = (term154 _104555 _104556 p1 t p2 u))) = (((term102 _104555 _104556 s p1 t p2 u) = (term106 _104555 _104556 s p1 t p2 u)) = ((term153 _104555 _104556 p1 t p2 u) = (term154 _104555 _104556 p1 t p2 u))).
Proof. exact (MK_COMB (@lem4361330 _104555 _104556 s p1 t p2 u) (@lem4361331 _104555 _104556 p1 t p2 u)). Qed.
Lemma lem4361333 {_104555 _104556 : Type'} (s : _104555 -> Prop) (p1 : _104555) (t : _104555 -> Prop) (p2 : _104556) (u : _104556 -> Prop) : ((term146 _104555 _104556 t p2 u p1 s) = (term152 _104555 _104556 p1 t p2 u)) = (((term102 _104555 _104556 s p1 t p2 u) = (term106 _104555 _104556 s p1 t p2 u)) = ((term153 _104555 _104556 p1 t p2 u) = (term154 _104555 _104556 p1 t p2 u))).
Proof. exact (TRANS (@lem4361327 _104555 _104556 s p1 t p2 u) (@lem4361332 _104555 _104556 s p1 t p2 u)). Qed.
Lemma lem4361334 {_104555 _104556 : Type'} (t : _104555 -> Prop) (p2 : _104556) (u : _104556 -> Prop) (p1 : _104555) (s : _104555 -> Prop) (h1 : (@IN _104555 p1 s) = False) : ((term102 _104555 _104556 s p1 t p2 u) = (term106 _104555 _104556 s p1 t p2 u)) = ((term153 _104555 _104556 p1 t p2 u) = (term154 _104555 _104556 p1 t p2 u)).
Proof. exact (EQ_MP (@lem4361333 _104555 _104556 s p1 t p2 u) (@lem4361324 _104555 _104556 t p2 u p1 s h1)). Qed.
Lemma lem4361335 {_104555 _104556 : Type'} (t : _104555 -> Prop) (p2 : _104556) (u : _104556 -> Prop) (p1 : _104555) (s : _104555 -> Prop) (h1 : (@IN _104555 p1 s) = False) : ((term153 _104555 _104556 p1 t p2 u) = (term154 _104555 _104556 p1 t p2 u)) = ((term102 _104555 _104556 s p1 t p2 u) = (term106 _104555 _104556 s p1 t p2 u)).
Proof. exact (SYM (@lem4361334 _104555 _104556 t p2 u p1 s h1)). Qed.
Lemma lem4361341 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem4361342 {_104555 : Type'} (p1 : _104555) (t : _104555 -> Prop) : (term155 _104555 p1 t) = True.
Proof. exact (@lem4361341 (@IN _104555 p1 t)). Qed.
Lemma lem4361343 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4361344 {_104555 : Type'} (p1 : _104555) (t : _104555 -> Prop) : (term156 _104555 p1 t) = (and True).
Proof. exact (MK_COMB (@lem4361343) (@lem4361342 _104555 p1 t)). Qed.
Lemma lem4361345 {_104556 : Type'} (p2 : _104556) (u : _104556 -> Prop) : (@IN _104556 p2 u) = (@IN _104556 p2 u).
Proof. exact (eq_refl (@IN _104556 p2 u)). Qed.
Lemma lem4361346 {_104555 _104556 : Type'} (p1 : _104555) (t : _104555 -> Prop) (p2 : _104556) (u : _104556 -> Prop) : (term148 _104555 _104556 p1 t p2 u) = (term139 _104556 p2 u).
Proof. exact (MK_COMB (@lem4361344 _104555 p1 t) (@lem4361345 _104556 p2 u)). Qed.
Lemma lem4361348 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4361349 {_104556 : Type'} (p2 : _104556) (u : _104556 -> Prop) : (term139 _104556 p2 u) = (@IN _104556 p2 u).
Proof. exact (@lem4361348 (@IN _104556 p2 u)). Qed.
Lemma lem4361350 {_104555 _104556 : Type'} (p1 : _104555) (t : _104555 -> Prop) (p2 : _104556) (u : _104556 -> Prop) : (term148 _104555 _104556 p1 t p2 u) = (@IN _104556 p2 u).
Proof. exact (TRANS (@lem4361346 _104555 _104556 p1 t p2 u) (@lem4361349 _104556 p2 u)). Qed.
Lemma lem4361351 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4361352 {_104555 _104556 : Type'} (p1 : _104555) (t : _104555 -> Prop) (p2 : _104556) (u : _104556 -> Prop) : (term157 _104555 _104556 p1 t p2 u) = (term158 _104556 p2 u).
Proof. exact (MK_COMB (@lem4361351) (@lem4361350 _104555 _104556 p1 t p2 u)). Qed.
Lemma lem4361356 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4361357 {_104556 : Type'} (p2 : _104556) (u : _104556 -> Prop) : (term139 _104556 p2 u) = (@IN _104556 p2 u).
Proof. exact (@lem4361356 (@IN _104556 p2 u)). Qed.
Lemma lem4361358 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4361359 {_104556 : Type'} (p2 : _104556) (u : _104556 -> Prop) : (term140 _104556 p2 u) = (term141 _104556 p2 u).
Proof. exact (MK_COMB (@lem4361358) (@lem4361357 _104556 p2 u)). Qed.
Lemma lem4361362 {_104555 _104556 : Type'} (p1 : _104555) (t : _104555 -> Prop) (p2 : _104556) (u : _104556 -> Prop) : (term8 _104555 _104556 p1 t p2 u) = (term8 _104555 _104556 p1 t p2 u).
Proof. exact (eq_refl (term8 _104555 _104556 p1 t p2 u)). Qed.
Lemma lem4361363 {_104555 _104556 : Type'} (p1 : _104555) (t : _104555 -> Prop) (p2 : _104556) (u : _104556 -> Prop) : (term149 _104555 _104556 p1 t p2 u) = (term159 _104555 _104556 p1 t p2 u).
Proof. exact (MK_COMB (@lem4361359 _104556 p2 u) (@lem4361362 _104555 _104556 p1 t p2 u)). Qed.
Lemma lem4361366 {_104555 _104556 : Type'} (p1 : _104555) (t : _104555 -> Prop) (p2 : _104556) (u : _104556 -> Prop) : ((term148 _104555 _104556 p1 t p2 u) = (term149 _104555 _104556 p1 t p2 u)) = ((@IN _104556 p2 u) = (term159 _104555 _104556 p1 t p2 u)).
Proof. exact (MK_COMB (@lem4361352 _104555 _104556 p1 t p2 u) (@lem4361363 _104555 _104556 p1 t p2 u)). Qed.
Lemma lem4361369 {_104555 _104556 : Type'} (p1 : _104555) (t : _104555 -> Prop) (p2 : _104556) (u : _104556 -> Prop) : ((@IN _104556 p2 u) = (term159 _104555 _104556 p1 t p2 u)) = ((term148 _104555 _104556 p1 t p2 u) = (term149 _104555 _104556 p1 t p2 u)).
Proof. exact (SYM (@lem4361366 _104555 _104556 p1 t p2 u)). Qed.
Lemma lem4361370 {_104556 : Type'} (p2 : _104556) (u : _104556 -> Prop) : term125 _104556 p2 u.
Proof. exact (@lem9851 (@IN _104556 p2 u)). Qed.
Lemma lem4361371 {_104556 : Type'} (p2 : _104556) (u : _104556 -> Prop) : (term125 _104556 p2 u) = (term126 _104556 p2 u).
Proof. exact (eq_refl (term125 _104556 p2 u)). Qed.
Lemma lem4361372 {_104556 : Type'} (p2 : _104556) (u : _104556 -> Prop) : term126 _104556 p2 u.
Proof. exact (EQ_MP (@lem4361371 _104556 p2 u) (@lem4361370 _104556 p2 u)). Qed.
Lemma lem4361373 {_104556 : Type'} (p2 : _104556) (u : _104556 -> Prop) (h1 : (@IN _104556 p2 u) = True) : (@IN _104556 p2 u) = True.
Proof. exact (h1). Qed.
Lemma lem4361374 {_104556 : Type'} (p2 : _104556) (u : _104556 -> Prop) (h1 : (@IN _104556 p2 u) = False) : (@IN _104556 p2 u) = False.
Proof. exact (h1). Qed.
Lemma lem4361383 {_104555 : Type'} (p1 : _104555) (t : _104555 -> Prop) : (term160 _104555 p1 t) = (term160 _104555 p1 t).
Proof. exact (eq_refl (term160 _104555 p1 t)). Qed.
Lemma lem4361384 {_104555 _104556 : Type'} (p1 : _104555) (t : _104555 -> Prop) (p2 : _104556) (u : _104556 -> Prop) (h1 : (@IN _104556 p2 u) = True) : (term161 _104555 _104556 p1 t p2 u) = (term162 _104555 p1 t).
Proof. exact (MK_COMB (@lem4361383 _104555 p1 t) (@lem4361373 _104556 p2 u h1)). Qed.
Lemma lem4361385 {_104555 : Type'} (p1 : _104555) (t : _104555 -> Prop) : (term162 _104555 p1 t) = (True = (term163 _104555 p1 t)).
Proof. exact (eq_refl (term162 _104555 p1 t)). Qed.
Lemma lem4361386 {_104555 _104556 : Type'} (p1 : _104555) (t : _104555 -> Prop) (p2 : _104556) (u : _104556 -> Prop) : (term164 _104555 _104556 p1 t p2 u) = (term164 _104555 _104556 p1 t p2 u).
Proof. exact (eq_refl (term164 _104555 _104556 p1 t p2 u)). Qed.
Lemma lem4361387 {_104555 _104556 : Type'} (p2 : _104556) (u : _104556 -> Prop) (p1 : _104555) (t : _104555 -> Prop) : ((term161 _104555 _104556 p1 t p2 u) = (term162 _104555 p1 t)) = ((term161 _104555 _104556 p1 t p2 u) = (True = (term163 _104555 p1 t))).
Proof. exact (MK_COMB (@lem4361386 _104555 _104556 p1 t p2 u) (@lem4361385 _104555 p1 t)). Qed.
Lemma lem4361388 {_104555 _104556 : Type'} (p1 : _104555) (t : _104555 -> Prop) (p2 : _104556) (u : _104556 -> Prop) : (term161 _104555 _104556 p1 t p2 u) = ((@IN _104556 p2 u) = (term159 _104555 _104556 p1 t p2 u)).
Proof. exact (eq_refl (term161 _104555 _104556 p1 t p2 u)). Qed.
Lemma lem4361389 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4361390 {_104555 _104556 : Type'} (p1 : _104555) (t : _104555 -> Prop) (p2 : _104556) (u : _104556 -> Prop) : (term164 _104555 _104556 p1 t p2 u) = (term165 _104555 _104556 p1 t p2 u).
Proof. exact (MK_COMB (@lem4361389) (@lem4361388 _104555 _104556 p1 t p2 u)). Qed.
Lemma lem4361391 {_104555 : Type'} (p1 : _104555) (t : _104555 -> Prop) : (True = (term163 _104555 p1 t)) = (True = (term163 _104555 p1 t)).
Proof. exact (eq_refl (True = (term163 _104555 p1 t))). Qed.
Lemma lem4361392 {_104555 _104556 : Type'} (p2 : _104556) (u : _104556 -> Prop) (p1 : _104555) (t : _104555 -> Prop) : ((term161 _104555 _104556 p1 t p2 u) = (True = (term163 _104555 p1 t))) = (((@IN _104556 p2 u) = (term159 _104555 _104556 p1 t p2 u)) = (True = (term163 _104555 p1 t))).
Proof. exact (MK_COMB (@lem4361390 _104555 _104556 p1 t p2 u) (@lem4361391 _104555 p1 t)). Qed.
Lemma lem4361393 {_104555 _104556 : Type'} (p2 : _104556) (u : _104556 -> Prop) (p1 : _104555) (t : _104555 -> Prop) : ((term161 _104555 _104556 p1 t p2 u) = (term162 _104555 p1 t)) = (((@IN _104556 p2 u) = (term159 _104555 _104556 p1 t p2 u)) = (True = (term163 _104555 p1 t))).
Proof. exact (TRANS (@lem4361387 _104555 _104556 p2 u p1 t) (@lem4361392 _104555 _104556 p2 u p1 t)). Qed.
Lemma lem4361394 {_104555 _104556 : Type'} (p1 : _104555) (t : _104555 -> Prop) (p2 : _104556) (u : _104556 -> Prop) (h1 : (@IN _104556 p2 u) = True) : ((@IN _104556 p2 u) = (term159 _104555 _104556 p1 t p2 u)) = (True = (term163 _104555 p1 t)).
Proof. exact (EQ_MP (@lem4361393 _104555 _104556 p2 u p1 t) (@lem4361384 _104555 _104556 p1 t p2 u h1)). Qed.
Lemma lem4361395 {_104555 _104556 : Type'} (p1 : _104555) (t : _104555 -> Prop) (p2 : _104556) (u : _104556 -> Prop) (h1 : (@IN _104556 p2 u) = True) : (True = (term163 _104555 p1 t)) = ((@IN _104556 p2 u) = (term159 _104555 _104556 p1 t p2 u)).
Proof. exact (SYM (@lem4361394 _104555 _104556 p1 t p2 u h1)). Qed.
Lemma lem4361396 {_104555 : Type'} (p1 : _104555) (t : _104555 -> Prop) : (term160 _104555 p1 t) = (term160 _104555 p1 t).
Proof. exact (eq_refl (term160 _104555 p1 t)). Qed.
Lemma lem4361397 {_104555 _104556 : Type'} (p1 : _104555) (t : _104555 -> Prop) (p2 : _104556) (u : _104556 -> Prop) (h1 : (@IN _104556 p2 u) = False) : (term161 _104555 _104556 p1 t p2 u) = (term166 _104555 p1 t).
Proof. exact (MK_COMB (@lem4361396 _104555 p1 t) (@lem4361374 _104556 p2 u h1)). Qed.
Lemma lem4361398 {_104555 : Type'} (p1 : _104555) (t : _104555 -> Prop) : (term166 _104555 p1 t) = (False = (term167 _104555 p1 t)).
Proof. exact (eq_refl (term166 _104555 p1 t)). Qed.
Lemma lem4361399 {_104555 _104556 : Type'} (p1 : _104555) (t : _104555 -> Prop) (p2 : _104556) (u : _104556 -> Prop) : (term164 _104555 _104556 p1 t p2 u) = (term164 _104555 _104556 p1 t p2 u).
Proof. exact (eq_refl (term164 _104555 _104556 p1 t p2 u)). Qed.
Lemma lem4361400 {_104555 _104556 : Type'} (p2 : _104556) (u : _104556 -> Prop) (p1 : _104555) (t : _104555 -> Prop) : ((term161 _104555 _104556 p1 t p2 u) = (term166 _104555 p1 t)) = ((term161 _104555 _104556 p1 t p2 u) = (False = (term167 _104555 p1 t))).
Proof. exact (MK_COMB (@lem4361399 _104555 _104556 p1 t p2 u) (@lem4361398 _104555 p1 t)). Qed.
Lemma lem4361401 {_104555 _104556 : Type'} (p1 : _104555) (t : _104555 -> Prop) (p2 : _104556) (u : _104556 -> Prop) : (term161 _104555 _104556 p1 t p2 u) = ((@IN _104556 p2 u) = (term159 _104555 _104556 p1 t p2 u)).
Proof. exact (eq_refl (term161 _104555 _104556 p1 t p2 u)). Qed.
Lemma lem4361402 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4361403 {_104555 _104556 : Type'} (p1 : _104555) (t : _104555 -> Prop) (p2 : _104556) (u : _104556 -> Prop) : (term164 _104555 _104556 p1 t p2 u) = (term165 _104555 _104556 p1 t p2 u).
Proof. exact (MK_COMB (@lem4361402) (@lem4361401 _104555 _104556 p1 t p2 u)). Qed.
Lemma lem4361404 {_104555 : Type'} (p1 : _104555) (t : _104555 -> Prop) : (False = (term167 _104555 p1 t)) = (False = (term167 _104555 p1 t)).
Proof. exact (eq_refl (False = (term167 _104555 p1 t))). Qed.
Lemma lem4361405 {_104555 _104556 : Type'} (p2 : _104556) (u : _104556 -> Prop) (p1 : _104555) (t : _104555 -> Prop) : ((term161 _104555 _104556 p1 t p2 u) = (False = (term167 _104555 p1 t))) = (((@IN _104556 p2 u) = (term159 _104555 _104556 p1 t p2 u)) = (False = (term167 _104555 p1 t))).
Proof. exact (MK_COMB (@lem4361403 _104555 _104556 p1 t p2 u) (@lem4361404 _104555 p1 t)). Qed.
Lemma lem4361406 {_104555 _104556 : Type'} (p2 : _104556) (u : _104556 -> Prop) (p1 : _104555) (t : _104555 -> Prop) : ((term161 _104555 _104556 p1 t p2 u) = (term166 _104555 p1 t)) = (((@IN _104556 p2 u) = (term159 _104555 _104556 p1 t p2 u)) = (False = (term167 _104555 p1 t))).
Proof. exact (TRANS (@lem4361400 _104555 _104556 p2 u p1 t) (@lem4361405 _104555 _104556 p2 u p1 t)). Qed.
Lemma lem4361407 {_104555 _104556 : Type'} (p1 : _104555) (t : _104555 -> Prop) (p2 : _104556) (u : _104556 -> Prop) (h1 : (@IN _104556 p2 u) = False) : ((@IN _104556 p2 u) = (term159 _104555 _104556 p1 t p2 u)) = (False = (term167 _104555 p1 t)).
Proof. exact (EQ_MP (@lem4361406 _104555 _104556 p2 u p1 t) (@lem4361397 _104555 _104556 p1 t p2 u h1)). Qed.
Lemma lem4361408 {_104555 _104556 : Type'} (p1 : _104555) (t : _104555 -> Prop) (p2 : _104556) (u : _104556 -> Prop) (h1 : (@IN _104556 p2 u) = False) : (False = (term167 _104555 p1 t)) = ((@IN _104556 p2 u) = (term159 _104555 _104556 p1 t p2 u)).
Proof. exact (SYM (@lem4361407 _104555 _104556 p1 t p2 u h1)). Qed.
Lemma lem4361410 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem4361411 {_104555 : Type'} (p1 : _104555) (t : _104555 -> Prop) : (True = (term163 _104555 p1 t)) = (term163 _104555 p1 t).
Proof. exact (@lem4361410 (term163 _104555 p1 t)). Qed.
Lemma lem4361413 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem4361414 {_104555 : Type'} (p1 : _104555) (t : _104555 -> Prop) : (term163 _104555 p1 t) = True.
Proof. exact (@lem4361413 (term168 _104555 p1 t)). Qed.
Lemma lem4361415 {_104555 : Type'} (p1 : _104555) (t : _104555 -> Prop) : (True = (term163 _104555 p1 t)) = True.
Proof. exact (TRANS (@lem4361411 _104555 p1 t) (@lem4361414 _104555 p1 t)). Qed.
Lemma lem4361416 {_104555 : Type'} (p1 : _104555) (t : _104555 -> Prop) : True = (True = (term163 _104555 p1 t)).
Proof. exact (SYM (@lem4361415 _104555 p1 t)). Qed.
Lemma lem4361417 {_104555 : Type'} (p1 : _104555) (t : _104555 -> Prop) : True = (term163 _104555 p1 t).
Proof. exact (EQ_MP (@lem4361416 _104555 p1 t) (@lem0)). Qed.
Lemma lem4361419 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem4361420 {_104555 : Type'} (p1 : _104555) (t : _104555 -> Prop) : (False = (term167 _104555 p1 t)) = (term169 _104555 p1 t).
Proof. exact (@lem4361419 (term167 _104555 p1 t)). Qed.
Lemma lem4361422 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem4361423 {_104555 : Type'} (p1 : _104555) (t : _104555 -> Prop) : (term167 _104555 p1 t) = (term170 _104555 p1 t).
Proof. exact (@lem4361422 (term170 _104555 p1 t)). Qed.
Lemma lem4361425 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem4361426 {_104555 : Type'} (p1 : _104555) (t : _104555 -> Prop) : (term170 _104555 p1 t) = False.
Proof. exact (@lem4361425 (@IN _104555 p1 t)). Qed.
Lemma lem4361427 {_104555 : Type'} (p1 : _104555) (t : _104555 -> Prop) : (term167 _104555 p1 t) = False.
Proof. exact (TRANS (@lem4361423 _104555 p1 t) (@lem4361426 _104555 p1 t)). Qed.
Lemma lem4361428 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4361429 {_104555 : Type'} (p1 : _104555) (t : _104555 -> Prop) : (term169 _104555 p1 t) = (~ False).
Proof. exact (MK_COMB (@lem4361428) (@lem4361427 _104555 p1 t)). Qed.
Lemma lem4361431 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem4361432 {_104555 : Type'} (p1 : _104555) (t : _104555 -> Prop) : (term169 _104555 p1 t) = True.
Proof. exact (TRANS (@lem4361429 _104555 p1 t) (@lem4361431)). Qed.
Lemma lem4361433 {_104555 : Type'} (p1 : _104555) (t : _104555 -> Prop) : (False = (term167 _104555 p1 t)) = True.
Proof. exact (TRANS (@lem4361420 _104555 p1 t) (@lem4361432 _104555 p1 t)). Qed.
Lemma lem4361434 {_104555 : Type'} (p1 : _104555) (t : _104555 -> Prop) : True = (False = (term167 _104555 p1 t)).
Proof. exact (SYM (@lem4361433 _104555 p1 t)). Qed.
Lemma lem4361435 {_104555 : Type'} (p1 : _104555) (t : _104555 -> Prop) : False = (term167 _104555 p1 t).
Proof. exact (EQ_MP (@lem4361434 _104555 p1 t) (@lem0)). Qed.
Lemma lem4361436 {_104555 _104556 : Type'} (p1 : _104555) (t : _104555 -> Prop) (p2 : _104556) (u : _104556 -> Prop) (h1 : (@IN _104556 p2 u) = False) : (@IN _104556 p2 u) = (term159 _104555 _104556 p1 t p2 u).
Proof. exact (EQ_MP (@lem4361408 _104555 _104556 p1 t p2 u h1) (@lem4361435 _104555 p1 t)). Qed.
Lemma lem4361437 {_104555 _104556 : Type'} (p1 : _104555) (t : _104555 -> Prop) (p2 : _104556) (u : _104556 -> Prop) (h1 : (@IN _104556 p2 u) = True) : (@IN _104556 p2 u) = (term159 _104555 _104556 p1 t p2 u).
Proof. exact (EQ_MP (@lem4361395 _104555 _104556 p1 t p2 u h1) (@lem4361417 _104555 p1 t)). Qed.
Lemma lem4361439 {_104555 _104556 : Type'} (p1 : _104555) (t : _104555 -> Prop) (p2 : _104556) (u : _104556 -> Prop) : (@IN _104556 p2 u) = (term159 _104555 _104556 p1 t p2 u).
Proof. exact (or_elim (@lem4361372 _104556 p2 u) (fun h0 : (@IN _104556 p2 u) = True => @lem4361437 _104555 _104556 p1 t p2 u h0) (fun h0 : (@IN _104556 p2 u) = False => @lem4361436 _104555 _104556 p1 t p2 u h0)). Qed.
Lemma lem4361440 {_104555 _104556 : Type'} (p1 : _104555) (t : _104555 -> Prop) (p2 : _104556) (u : _104556 -> Prop) : (term148 _104555 _104556 p1 t p2 u) = (term149 _104555 _104556 p1 t p2 u).
Proof. exact (EQ_MP (@lem4361369 _104555 _104556 p1 t p2 u) (@lem4361439 _104555 _104556 p1 t p2 u)). Qed.
Lemma lem4361446 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem4361447 {_104555 : Type'} (p1 : _104555) (t : _104555 -> Prop) : (term171 _104555 p1 t) = (@IN _104555 p1 t).
Proof. exact (@lem4361446 (@IN _104555 p1 t)). Qed.
Lemma lem4361448 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4361449 {_104555 : Type'} (p1 : _104555) (t : _104555 -> Prop) : (term172 _104555 p1 t) = (term49 _104555 p1 t).
Proof. exact (MK_COMB (@lem4361448) (@lem4361447 _104555 p1 t)). Qed.
Lemma lem4361450 {_104556 : Type'} (p2 : _104556) (u : _104556 -> Prop) : (@IN _104556 p2 u) = (@IN _104556 p2 u).
Proof. exact (eq_refl (@IN _104556 p2 u)). Qed.
Lemma lem4361451 {_104555 _104556 : Type'} (p1 : _104555) (t : _104555 -> Prop) (p2 : _104556) (u : _104556 -> Prop) : (term153 _104555 _104556 p1 t p2 u) = (term8 _104555 _104556 p1 t p2 u).
Proof. exact (MK_COMB (@lem4361449 _104555 p1 t) (@lem4361450 _104556 p2 u)). Qed.
Lemma lem4361454 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4361455 {_104555 _104556 : Type'} (p1 : _104555) (t : _104555 -> Prop) (p2 : _104556) (u : _104556 -> Prop) : (term173 _104555 _104556 p1 t p2 u) = (term174 _104555 _104556 p1 t p2 u).
Proof. exact (MK_COMB (@lem4361454) (@lem4361451 _104555 _104556 p1 t p2 u)). Qed.
Lemma lem4361459 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem4361460 {_104556 : Type'} (p2 : _104556) (u : _104556 -> Prop) : (term143 _104556 p2 u) = False.
Proof. exact (@lem4361459 (@IN _104556 p2 u)). Qed.
Lemma lem4361461 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4361462 {_104556 : Type'} (p2 : _104556) (u : _104556 -> Prop) : (term144 _104556 p2 u) = (or False).
Proof. exact (MK_COMB (@lem4361461) (@lem4361460 _104556 p2 u)). Qed.
Lemma lem4361465 {_104555 _104556 : Type'} (p1 : _104555) (t : _104555 -> Prop) (p2 : _104556) (u : _104556 -> Prop) : (term8 _104555 _104556 p1 t p2 u) = (term8 _104555 _104556 p1 t p2 u).
Proof. exact (eq_refl (term8 _104555 _104556 p1 t p2 u)). Qed.
Lemma lem4361466 {_104555 _104556 : Type'} (p1 : _104555) (t : _104555 -> Prop) (p2 : _104556) (u : _104556 -> Prop) : (term154 _104555 _104556 p1 t p2 u) = (term175 _104555 _104556 p1 t p2 u).
Proof. exact (MK_COMB (@lem4361462 _104556 p2 u) (@lem4361465 _104555 _104556 p1 t p2 u)). Qed.
Lemma lem4361468 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem4361469 {_104555 _104556 : Type'} (p1 : _104555) (t : _104555 -> Prop) (p2 : _104556) (u : _104556 -> Prop) : (term175 _104555 _104556 p1 t p2 u) = (term8 _104555 _104556 p1 t p2 u).
Proof. exact (@lem4361468 (term8 _104555 _104556 p1 t p2 u)). Qed.
Lemma lem4361472 {_104555 _104556 : Type'} (p1 : _104555) (t : _104555 -> Prop) (p2 : _104556) (u : _104556 -> Prop) : (term154 _104555 _104556 p1 t p2 u) = (term8 _104555 _104556 p1 t p2 u).
Proof. exact (TRANS (@lem4361466 _104555 _104556 p1 t p2 u) (@lem4361469 _104555 _104556 p1 t p2 u)). Qed.
Lemma lem4361473 {_104555 _104556 : Type'} (p1 : _104555) (t : _104555 -> Prop) (p2 : _104556) (u : _104556 -> Prop) : ((term153 _104555 _104556 p1 t p2 u) = (term154 _104555 _104556 p1 t p2 u)) = ((term8 _104555 _104556 p1 t p2 u) = (term8 _104555 _104556 p1 t p2 u)).
Proof. exact (MK_COMB (@lem4361455 _104555 _104556 p1 t p2 u) (@lem4361472 _104555 _104556 p1 t p2 u)). Qed.
Lemma lem4361475 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4361476 (x : Prop) : (x = x) = True.
Proof. exact (@lem4361475 Prop x). Qed.
Lemma lem4361477 {_104555 _104556 : Type'} (p1 : _104555) (t : _104555 -> Prop) (p2 : _104556) (u : _104556 -> Prop) : ((term8 _104555 _104556 p1 t p2 u) = (term8 _104555 _104556 p1 t p2 u)) = True.
Proof. exact (@lem4361476 (term8 _104555 _104556 p1 t p2 u)). Qed.
Lemma lem4361478 {_104555 _104556 : Type'} (p1 : _104555) (t : _104555 -> Prop) (p2 : _104556) (u : _104556 -> Prop) : ((term153 _104555 _104556 p1 t p2 u) = (term154 _104555 _104556 p1 t p2 u)) = True.
Proof. exact (TRANS (@lem4361473 _104555 _104556 p1 t p2 u) (@lem4361477 _104555 _104556 p1 t p2 u)). Qed.
Lemma lem4361479 {_104555 _104556 : Type'} (p1 : _104555) (t : _104555 -> Prop) (p2 : _104556) (u : _104556 -> Prop) : True = ((term153 _104555 _104556 p1 t p2 u) = (term154 _104555 _104556 p1 t p2 u)).
Proof. exact (SYM (@lem4361478 _104555 _104556 p1 t p2 u)). Qed.
Lemma lem4361480 {_104555 _104556 : Type'} (p1 : _104555) (t : _104555 -> Prop) (p2 : _104556) (u : _104556 -> Prop) : (term153 _104555 _104556 p1 t p2 u) = (term154 _104555 _104556 p1 t p2 u).
Proof. exact (EQ_MP (@lem4361479 _104555 _104556 p1 t p2 u) (@lem0)). Qed.
Lemma lem4361481 {_104555 _104556 : Type'} (t : _104555 -> Prop) (p2 : _104556) (u : _104556 -> Prop) (p1 : _104555) (s : _104555 -> Prop) (h1 : (@IN _104555 p1 s) = False) : (term102 _104555 _104556 s p1 t p2 u) = (term106 _104555 _104556 s p1 t p2 u).
Proof. exact (EQ_MP (@lem4361335 _104555 _104556 t p2 u p1 s h1) (@lem4361480 _104555 _104556 p1 t p2 u)). Qed.
Lemma lem4361482 {_104555 _104556 : Type'} (t : _104555 -> Prop) (p2 : _104556) (u : _104556 -> Prop) (p1 : _104555) (s : _104555 -> Prop) (h1 : (@IN _104555 p1 s) = True) : (term102 _104555 _104556 s p1 t p2 u) = (term106 _104555 _104556 s p1 t p2 u).
Proof. exact (EQ_MP (@lem4361322 _104555 _104556 t p2 u p1 s h1) (@lem4361440 _104555 _104556 p1 t p2 u)). Qed.
Lemma lem4361485 {_104555 _104556 : Type'} (s : _104555 -> Prop) (p1 : _104555) (t : _104555 -> Prop) (p2 : _104556) (u : _104556 -> Prop) : (term102 _104555 _104556 s p1 t p2 u) = (term106 _104555 _104556 s p1 t p2 u).
Proof. exact (or_elim (@lem4361293 _104555 p1 s) (fun h0 : (@IN _104555 p1 s) = True => @lem4361482 _104555 _104556 t p2 u p1 s h0) (fun h0 : (@IN _104555 p1 s) = False => @lem4361481 _104555 _104556 t p2 u p1 s h0)). Qed.
Lemma lem4361490 {_104555 _104556 : Type'} (s : _104555 -> Prop) (p1 : _104555) (t : _104555 -> Prop) (u : _104556 -> Prop) : term108 _104555 _104556 s p1 t u.
Proof. exact (fun p2 : _104556 => @lem4361485 _104555 _104556 s p1 t p2 u). Qed.
Lemma lem4361495 {_104555 _104556 : Type'} (s : _104555 -> Prop) (t : _104555 -> Prop) (u : _104556 -> Prop) : term110 _104555 _104556 s t u.
Proof. exact (fun p1 : _104555 => @lem4361490 _104555 _104556 s p1 t u). Qed.
Lemma lem4361500 {_104555 _104556 : Type'} (s : _104555 -> Prop) (t : _104555 -> Prop) : term114 _104555 _104556 s t.
Proof. exact (fun u : _104556 -> Prop => @lem4361495 _104555 _104556 s t u). Qed.
Lemma lem4361505 {_104555 _104556 : Type'} (s : _104555 -> Prop) : term118 _104555 _104556 s.
Proof. exact (fun t : _104555 -> Prop => @lem4361500 _104555 _104556 s t). Qed.
Lemma lem4361510 {_104555 _104556 : Type'} : term122 _104555 _104556.
Proof. exact (fun s : _104555 -> Prop => @lem4361505 _104555 _104556 s). Qed.
Lemma lem4361515 {_104522 _104523 : Type'} (t : _104523 -> Prop) (p1 : _104522) (s : _104522 -> Prop) (u : _104523 -> Prop) : term60 _104522 _104523 t p1 s u.
Proof. exact (fun p2 : _104523 => @lem4361276 _104522 _104523 t p1 s p2 u). Qed.
Lemma lem4361520 {_104522 _104523 : Type'} (t : _104523 -> Prop) (s : _104522 -> Prop) (u : _104523 -> Prop) : term62 _104522 _104523 t s u.
Proof. exact (fun p1 : _104522 => @lem4361515 _104522 _104523 t p1 s u). Qed.
Lemma lem4361525 {_104522 _104523 : Type'} (t : _104523 -> Prop) (s : _104522 -> Prop) : term66 _104522 _104523 t s.
Proof. exact (fun u : _104523 -> Prop => @lem4361520 _104522 _104523 t s u). Qed.
Lemma lem4361530 {_104522 _104523 : Type'} (s : _104522 -> Prop) : term70 _104522 _104523 s.
Proof. exact (fun t : _104523 -> Prop => @lem4361525 _104522 _104523 t s). Qed.
Lemma lem4361535 {_104522 _104523 : Type'} : term74 _104522 _104523.
Proof. exact (fun s : _104522 -> Prop => @lem4361530 _104522 _104523 s). Qed.
Lemma lem4361536 {_104522 _104523 _104555 _104556 : Type'} : term124 _104522 _104523 _104555 _104556.
Proof. exact (conj (@lem4361535 _104522 _104523) (@lem4361510 _104555 _104556)). Qed.
Lemma lem4361537 {_104522 _104523 _104555 _104556 : Type'} : term123 _104522 _104523 _104555 _104556.
Proof. exact (EQ_MP (@lem4361150 _104522 _104523 _104555 _104556) (@lem4361536 _104522 _104523 _104555 _104556)). Qed.
