Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import IMAGE_ID_term_abbrevs.
Require Import EXTENSION_spec.
Require Import IN_IMAGE_spec.
Require Import UNWIND_THM1_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem3368784 {A : Type'} (P : A -> Prop) : term0 A P.
Proof. exact (@lem4524 A P). Qed.
Lemma lem3368785 {A : Type'} (P : A -> Prop) : (term0 A P) = (term1 A P).
Proof. exact (eq_refl (term0 A P)). Qed.
Lemma lem3368786 {A : Type'} (P : A -> Prop) : term1 A P.
Proof. exact (EQ_MP (@lem3368785 A P) (@lem3368784 A P)). Qed.
Lemma lem3368787 {A : Type'} (P : A -> Prop) (a : A) : term2 A P a.
Proof. exact (@lem3368786 A P a). Qed.
Lemma lem3368788 {A : Type'} (P : A -> Prop) (a : A) : (term2 A P a) = ((term3 A a P) = (P a)).
Proof. exact (eq_refl (term2 A P a)). Qed.
Lemma lem3368790 {A B : Type'} (y : B) : term4 A B y.
Proof. exact (@lem3206070 A B y). Qed.
Lemma lem3368791 {A B : Type'} (y : B) : (term4 A B y) = (term5 A B y).
Proof. exact (eq_refl (term4 A B y)). Qed.
Lemma lem3368792 {A B : Type'} (y : B) : term5 A B y.
Proof. exact (EQ_MP (@lem3368791 A B y) (@lem3368790 A B y)). Qed.
Lemma lem3368793 {A B : Type'} (y : B) (s : A -> Prop) : term6 A B y s.
Proof. exact (@lem3368792 A B y s). Qed.
Lemma lem3368794 {A B : Type'} (y : B) (s : A -> Prop) : (term6 A B y s) = (term7 A B y s).
Proof. exact (eq_refl (term6 A B y s)). Qed.
Lemma lem3368795 {A B : Type'} (y : B) (s : A -> Prop) : term7 A B y s.
Proof. exact (EQ_MP (@lem3368794 A B y s) (@lem3368793 A B y s)). Qed.
Lemma lem3368796 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) : term8 A B y s f.
Proof. exact (@lem3368795 A B y s f). Qed.
Lemma lem3368797 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term8 A B y s f) = ((term9 A B y f s) = (term10 A B y f s)).
Proof. exact (eq_refl (term8 A B y s f)). Qed.
Lemma lem3368799 {A : Type'} (s : A -> Prop) : term11 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem3368800 {A : Type'} (s : A -> Prop) : (term11 A s) = (term12 A s).
Proof. exact (eq_refl (term11 A s)). Qed.
Lemma lem3368801 {A : Type'} (s : A -> Prop) : term12 A s.
Proof. exact (EQ_MP (@lem3368800 A s) (@lem3368799 A s)). Qed.
Lemma lem3368802 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term13 A s t.
Proof. exact (@lem3368801 A s t). Qed.
Lemma lem3368803 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term13 A s t) = ((s = t) = (term14 A s t)).
Proof. exact (eq_refl (term13 A s t)). Qed.
Lemma lem3368812 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term14 A s t).
Proof. exact (EQ_MP (@lem3368803 A s t) (@lem3368802 A s t)). Qed.
Lemma lem3368813 {_87528 : Type'} (s : _87528 -> Prop) (t : _87528 -> Prop) : (s = t) = (term14 _87528 s t).
Proof. exact (@lem3368812 _87528 s t). Qed.
Lemma lem3368814 {_87528 : Type'} (s : _87528 -> Prop) : ((term15 _87528 s) = s) = (term16 _87528 s).
Proof. exact (@lem3368813 _87528 (term15 _87528 s) s). Qed.
Lemma lem3368824 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term9 A B y f s) = (term10 A B y f s).
Proof. exact (EQ_MP (@lem3368797 A B y f s) (@lem3368796 A B y s f)). Qed.
Lemma lem3368825 {_87528 : Type'} (y : _87528) (f : _87528 -> _87528) (s : _87528 -> Prop) : (term17 _87528 y f s) = (term18 _87528 y f s).
Proof. exact (@lem3368824 _87528 _87528 y f s). Qed.
Lemma lem3368826 {_87528 : Type'} (x : _87528) (s : _87528 -> Prop) : (term19 _87528 x s) = (term20 _87528 x s).
Proof. exact (@lem3368825 _87528 x (term21 _87528) s). Qed.
Lemma lem3368840 {A B : Type'} (f : A -> B) (y : A) : (term22 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3368841 {_87528 : Type'} (f : _87528 -> _87528) (y : _87528) : (term23 _87528 f y) = (f y).
Proof. exact (@lem3368840 _87528 _87528 f y). Qed.
Lemma lem3368842 {_87528 : Type'} (x' : _87528) : (term24 _87528 x') = (term25 _87528 x').
Proof. exact (@lem3368841 _87528 (term21 _87528) x'). Qed.
Lemma lem3368843 {_87528 : Type'} (x : _87528) : (term25 _87528 x) = x.
Proof. exact (eq_refl (term25 _87528 x)). Qed.
Lemma lem3368844 {_87528 : Type'} : (term26 _87528) = (term21 _87528).
Proof. exact (fun_ext (fun x : _87528 => @lem3368843 _87528 x)). Qed.
Lemma lem3368845 {_87528 : Type'} (x' : _87528) : x' = x'.
Proof. exact (eq_refl x'). Qed.
Lemma lem3368846 {_87528 : Type'} (x' : _87528) : (term24 _87528 x') = (term25 _87528 x').
Proof. exact (MK_COMB (@lem3368844 _87528) (@lem3368845 _87528 x')). Qed.
Lemma lem3368847 {_87528 : Type'} : (@eq _87528) = (@eq _87528).
Proof. exact (eq_refl (@eq _87528)). Qed.
Lemma lem3368848 {_87528 : Type'} (x' : _87528) : (term27 _87528 x') = (term28 _87528 x').
Proof. exact (MK_COMB (@lem3368847 _87528) (@lem3368846 _87528 x')). Qed.
Lemma lem3368849 {_87528 : Type'} (x' : _87528) : (term25 _87528 x') = x'.
Proof. exact (eq_refl (term25 _87528 x')). Qed.
Lemma lem3368850 {_87528 : Type'} (x' : _87528) : ((term24 _87528 x') = (term25 _87528 x')) = ((term25 _87528 x') = x').
Proof. exact (MK_COMB (@lem3368848 _87528 x') (@lem3368849 _87528 x')). Qed.
Lemma lem3368851 {_87528 : Type'} (x' : _87528) : (term25 _87528 x') = x'.
Proof. exact (EQ_MP (@lem3368850 _87528 x') (@lem3368842 _87528 x')). Qed.
Lemma lem3368852 {_87528 : Type'} (x : _87528) : (@eq _87528 x) = (@eq _87528 x).
Proof. exact (eq_refl (@eq _87528 x)). Qed.
Lemma lem3368853 {_87528 : Type'} (x : _87528) (x' : _87528) : (x = (term25 _87528 x')) = (x = x').
Proof. exact (MK_COMB (@lem3368852 _87528 x) (@lem3368851 _87528 x')). Qed.
Lemma lem3368858 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3368859 {_87528 : Type'} (x : _87528) (x' : _87528) : (term29 _87528 x x') = (term30 _87528 x x').
Proof. exact (MK_COMB (@lem3368858) (@lem3368853 _87528 x x')). Qed.
Lemma lem3368860 {_87528 : Type'} (x' : _87528) (s : _87528 -> Prop) : (@IN _87528 x' s) = (@IN _87528 x' s).
Proof. exact (eq_refl (@IN _87528 x' s)). Qed.
Lemma lem3368861 {_87528 : Type'} (x : _87528) (x' : _87528) (s : _87528 -> Prop) : (term31 _87528 x x' s) = (term32 _87528 x x' s).
Proof. exact (MK_COMB (@lem3368859 _87528 x x') (@lem3368860 _87528 x' s)). Qed.
Lemma lem3368864 {_87528 : Type'} (x : _87528) (s : _87528 -> Prop) : (term33 _87528 x s) = (term34 _87528 x s).
Proof. exact (fun_ext (fun x' : _87528 => @lem3368861 _87528 x x' s)). Qed.
Lemma lem3368865 {_87528 : Type'} : (@ex _87528) = (@ex _87528).
Proof. exact (eq_refl (@ex _87528)). Qed.
Lemma lem3368866 {_87528 : Type'} (x : _87528) (s : _87528 -> Prop) : (term20 _87528 x s) = (term35 _87528 x s).
Proof. exact (MK_COMB (@lem3368865 _87528) (@lem3368864 _87528 x s)). Qed.
Lemma lem3368868 {A : Type'} (P : A -> Prop) (a : A) : (term3 A a P) = (P a).
Proof. exact (EQ_MP (@lem3368788 A P a) (@lem3368787 A P a)). Qed.
Lemma lem3368869 {_87528 : Type'} (P : _87528 -> Prop) (a : _87528) : (term3 _87528 a P) = (P a).
Proof. exact (@lem3368868 _87528 P a). Qed.
Lemma lem3368870 {_87528 : Type'} (s : _87528 -> Prop) (x : _87528) : (term36 _87528 x s) = (term37 _87528 s x).
Proof. exact (@lem3368869 _87528 (term38 _87528 s) x). Qed.
Lemma lem3368871 {_87528 : Type'} (x' : _87528) (s : _87528 -> Prop) : (term37 _87528 s x') = (@IN _87528 x' s).
Proof. exact (eq_refl (term37 _87528 s x')). Qed.
Lemma lem3368872 {_87528 : Type'} (x : _87528) (x' : _87528) : (term30 _87528 x x') = (term30 _87528 x x').
Proof. exact (eq_refl (term30 _87528 x x')). Qed.
Lemma lem3368873 {_87528 : Type'} (x : _87528) (x' : _87528) (s : _87528 -> Prop) : (term39 _87528 x s x') = (term32 _87528 x x' s).
Proof. exact (MK_COMB (@lem3368872 _87528 x x') (@lem3368871 _87528 x' s)). Qed.
Lemma lem3368874 {_87528 : Type'} (x : _87528) (s : _87528 -> Prop) : (term40 _87528 x s) = (term34 _87528 x s).
Proof. exact (fun_ext (fun x' : _87528 => @lem3368873 _87528 x x' s)). Qed.
Lemma lem3368875 {_87528 : Type'} : (@ex _87528) = (@ex _87528).
Proof. exact (eq_refl (@ex _87528)). Qed.
Lemma lem3368876 {_87528 : Type'} (x : _87528) (s : _87528 -> Prop) : (term36 _87528 x s) = (term35 _87528 x s).
Proof. exact (MK_COMB (@lem3368875 _87528) (@lem3368874 _87528 x s)). Qed.
Lemma lem3368877 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3368878 {_87528 : Type'} (x : _87528) (s : _87528 -> Prop) : (term41 _87528 x s) = (term42 _87528 x s).
Proof. exact (MK_COMB (@lem3368877) (@lem3368876 _87528 x s)). Qed.
Lemma lem3368879 {_87528 : Type'} (x : _87528) (s : _87528 -> Prop) : (term37 _87528 s x) = (@IN _87528 x s).
Proof. exact (eq_refl (term37 _87528 s x)). Qed.
Lemma lem3368880 {_87528 : Type'} (x : _87528) (s : _87528 -> Prop) : ((term36 _87528 x s) = (term37 _87528 s x)) = ((term35 _87528 x s) = (@IN _87528 x s)).
Proof. exact (MK_COMB (@lem3368878 _87528 x s) (@lem3368879 _87528 x s)). Qed.
Lemma lem3368881 {_87528 : Type'} (x : _87528) (s : _87528 -> Prop) : (term35 _87528 x s) = (@IN _87528 x s).
Proof. exact (EQ_MP (@lem3368880 _87528 x s) (@lem3368870 _87528 s x)). Qed.
Lemma lem3368882 {_87528 : Type'} (x : _87528) (s : _87528 -> Prop) : (term20 _87528 x s) = (@IN _87528 x s).
Proof. exact (TRANS (@lem3368866 _87528 x s) (@lem3368881 _87528 x s)). Qed.
Lemma lem3368883 {_87528 : Type'} (x : _87528) (s : _87528 -> Prop) : (term19 _87528 x s) = (@IN _87528 x s).
Proof. exact (TRANS (@lem3368826 _87528 x s) (@lem3368882 _87528 x s)). Qed.
Lemma lem3368884 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3368885 {_87528 : Type'} (x : _87528) (s : _87528 -> Prop) : (term43 _87528 x s) = (term44 _87528 x s).
Proof. exact (MK_COMB (@lem3368884) (@lem3368883 _87528 x s)). Qed.
Lemma lem3368886 {_87528 : Type'} (x : _87528) (s : _87528 -> Prop) : (@IN _87528 x s) = (@IN _87528 x s).
Proof. exact (eq_refl (@IN _87528 x s)). Qed.
Lemma lem3368887 {_87528 : Type'} (x : _87528) (s : _87528 -> Prop) : ((term19 _87528 x s) = (@IN _87528 x s)) = ((@IN _87528 x s) = (@IN _87528 x s)).
Proof. exact (MK_COMB (@lem3368885 _87528 x s) (@lem3368886 _87528 x s)). Qed.
Lemma lem3368889 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3368890 (x : Prop) : (x = x) = True.
Proof. exact (@lem3368889 Prop x). Qed.
Lemma lem3368891 {_87528 : Type'} (x : _87528) (s : _87528 -> Prop) : ((@IN _87528 x s) = (@IN _87528 x s)) = True.
Proof. exact (@lem3368890 (@IN _87528 x s)). Qed.
Lemma lem3368892 {_87528 : Type'} (x : _87528) (s : _87528 -> Prop) : ((term19 _87528 x s) = (@IN _87528 x s)) = True.
Proof. exact (TRANS (@lem3368887 _87528 x s) (@lem3368891 _87528 x s)). Qed.
Lemma lem3368893 {_87528 : Type'} (s : _87528 -> Prop) : (term45 _87528 s) = (term46 _87528).
Proof. exact (fun_ext (fun x : _87528 => @lem3368892 _87528 x s)). Qed.
Lemma lem3368894 {_87528 : Type'} : (@all _87528) = (@all _87528).
Proof. exact (eq_refl (@all _87528)). Qed.
Lemma lem3368895 {_87528 : Type'} (s : _87528 -> Prop) : (term16 _87528 s) = (term47 _87528).
Proof. exact (MK_COMB (@lem3368894 _87528) (@lem3368893 _87528 s)). Qed.
Lemma lem3368897 {A : Type'} (t : Prop) : (term48 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3368898 {_87528 : Type'} (t : Prop) : (term48 _87528 t) = t.
Proof. exact (@lem3368897 _87528 t). Qed.
Lemma lem3368899 {_87528 : Type'} : (term47 _87528) = True.
Proof. exact (@lem3368898 _87528 True). Qed.
Lemma lem3368900 {_87528 : Type'} (s : _87528 -> Prop) : (term16 _87528 s) = True.
Proof. exact (TRANS (@lem3368895 _87528 s) (@lem3368899 _87528)). Qed.
Lemma lem3368901 {_87528 : Type'} (s : _87528 -> Prop) : ((term15 _87528 s) = s) = True.
Proof. exact (TRANS (@lem3368814 _87528 s) (@lem3368900 _87528 s)). Qed.
Lemma lem3368902 {_87528 : Type'} : (term49 _87528) = (term50 _87528).
Proof. exact (fun_ext (fun s : _87528 -> Prop => @lem3368901 _87528 s)). Qed.
Lemma lem3368903 {_87528 : Type'} : (@all (_87528 -> Prop)) = (@all (_87528 -> Prop)).
Proof. exact (eq_refl (@all (_87528 -> Prop))). Qed.
Lemma lem3368904 {_87528 : Type'} : (term51 _87528) = (term52 _87528).
Proof. exact (MK_COMB (@lem3368903 _87528) (@lem3368902 _87528)). Qed.
Lemma lem3368906 {A : Type'} (t : Prop) : (term48 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3368907 {_87528 : Type'} (t : Prop) : (term53 _87528 t) = t.
Proof. exact (@lem3368906 (_87528 -> Prop) t). Qed.
Lemma lem3368908 {_87528 : Type'} : (term52 _87528) = True.
Proof. exact (@lem3368907 _87528 True). Qed.
Lemma lem3368909 {_87528 : Type'} : (term51 _87528) = True.
Proof. exact (TRANS (@lem3368904 _87528) (@lem3368908 _87528)). Qed.
Lemma lem3368910 {_87528 : Type'} : True = (term51 _87528).
Proof. exact (SYM (@lem3368909 _87528)). Qed.
Lemma lem3368911 {_87528 : Type'} : term51 _87528.
Proof. exact (EQ_MP (@lem3368910 _87528) (@lem0)). Qed.
