Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm8054010_term_abbrevs.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm1843_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211668_spec.
Require Import thm3211669_spec.
Require Import thm3211724_spec.
Require Import thm3211725_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm8049006_spec.
Lemma lem8053839 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem8053840 {_143007 _143009 : Type'} (s : type56 _143007 _143009) (t : type56 _143007 _143009) : (s = t) = (term1 _143007 _143009 s t).
Proof. exact (@lem8053839 (type24 _143007 _143009) s t). Qed.
Lemma lem8053841 {_143007 _143009 : Type'} (f : type56 _143007 _143009) : (f = (@EMPTY ((cart _143007 _143009) -> Prop))) = (term2 _143007 _143009 f).
Proof. exact (@lem8053840 _143007 _143009 f (@EMPTY ((cart _143007 _143009) -> Prop))). Qed.
Lemma lem8053850 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8053851 {_143007 _143009 : Type'} (f : type56 _143007 _143009) : (term3 _143007 _143009 f) = (term4 _143007 _143009 f).
Proof. exact (MK_COMB (@lem8053850) (@lem8053841 _143007 _143009 f)). Qed.
Lemma lem8053868 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) : (term5 _143007 _143008 _143009 s) = (term5 _143007 _143008 _143009 s).
Proof. exact (eq_refl (term5 _143007 _143008 _143009 s)). Qed.
Lemma lem8053869 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : (term6 _143007 _143008 _143009 f s) = (term7 _143007 _143008 _143009 f s).
Proof. exact (MK_COMB (@lem8053851 _143007 _143009 f) (@lem8053868 _143007 _143008 _143009 s)). Qed.
Lemma lem8053872 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : (term7 _143007 _143008 _143009 f s) = (term6 _143007 _143008 _143009 f s).
Proof. exact (SYM (@lem8053869 _143007 _143008 _143009 f s)). Qed.
Lemma lem8053882 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem8053883 {_143007 _143009 : Type'} (P : type56 _143007 _143009) (x : type24 _143007 _143009) : (@IN ((cart _143007 _143009) -> Prop) x P) = (P x).
Proof. exact (@lem8053882 (type24 _143007 _143009) P x). Qed.
Lemma lem8053884 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (x : type24 _143007 _143009) : (@IN ((cart _143007 _143009) -> Prop) x f) = (f x).
Proof. exact (@lem8053883 _143007 _143009 f x). Qed.
Lemma lem8053885 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8053886 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (x : type24 _143007 _143009) : (term8 _143007 _143009 x f) = (term9 _143007 _143009 f x).
Proof. exact (MK_COMB (@lem8053885) (@lem8053884 _143007 _143009 f x)). Qed.
Lemma lem8053888 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem8053889 {_143007 _143009 : Type'} (x : type24 _143007 _143009) : (@IN ((cart _143007 _143009) -> Prop) x (@EMPTY ((cart _143007 _143009) -> Prop))) = False.
Proof. exact (@lem8053888 (type24 _143007 _143009) x). Qed.
Lemma lem8053890 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (x : type24 _143007 _143009) : ((@IN ((cart _143007 _143009) -> Prop) x f) = (@IN ((cart _143007 _143009) -> Prop) x (@EMPTY ((cart _143007 _143009) -> Prop)))) = ((f x) = False).
Proof. exact (MK_COMB (@lem8053886 _143007 _143009 f x) (@lem8053889 _143007 _143009 x)). Qed.
Lemma lem8053892 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem8053893 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (x : type24 _143007 _143009) : ((f x) = False) = (term10 _143007 _143009 f x).
Proof. exact (@lem8053892 (f x)). Qed.
Lemma lem8053894 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (x : type24 _143007 _143009) : ((@IN ((cart _143007 _143009) -> Prop) x f) = (@IN ((cart _143007 _143009) -> Prop) x (@EMPTY ((cart _143007 _143009) -> Prop)))) = (term10 _143007 _143009 f x).
Proof. exact (TRANS (@lem8053890 _143007 _143009 f x) (@lem8053893 _143007 _143009 f x)). Qed.
Lemma lem8053895 {_143007 _143009 : Type'} (f : type56 _143007 _143009) : (term11 _143007 _143009 f) = (term12 _143007 _143009 f).
Proof. exact (fun_ext (fun x : type24 _143007 _143009 => @lem8053894 _143007 _143009 f x)). Qed.
Lemma lem8053896 {_143007 _143009 : Type'} : (@all ((cart _143007 _143009) -> Prop)) = (@all ((cart _143007 _143009) -> Prop)).
Proof. exact (eq_refl (@all ((cart _143007 _143009) -> Prop))). Qed.
Lemma lem8053897 {_143007 _143009 : Type'} (f : type56 _143007 _143009) : (term2 _143007 _143009 f) = (term13 _143007 _143009 f).
Proof. exact (MK_COMB (@lem8053896 _143007 _143009) (@lem8053895 _143007 _143009 f)). Qed.
Lemma lem8053902 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8053903 {_143007 _143009 : Type'} (f : type56 _143007 _143009) : (term4 _143007 _143009 f) = (term14 _143007 _143009 f).
Proof. exact (MK_COMB (@lem8053902) (@lem8053897 _143007 _143009 f)). Qed.
Lemma lem8053917 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem8053918 {_143007 _143008 : Type'} (P : type24 _143007 _143008) (x : cart _143007 _143008) : (@IN (cart _143007 _143008) x P) = (P x).
Proof. exact (@lem8053917 (cart _143007 _143008) P x). Qed.
Lemma lem8053919 {_143007 _143008 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) : (@IN (cart _143007 _143008) x s) = (s x).
Proof. exact (@lem8053918 _143007 _143008 s x). Qed.
Lemma lem8053920 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8053921 {_143007 _143008 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) : (term15 _143007 _143008 x s) = (term16 _143007 _143008 s x).
Proof. exact (MK_COMB (@lem8053920) (@lem8053919 _143007 _143008 s x)). Qed.
Lemma lem8053923 {A : Type'} (s : type686 A) (x : A) : (term17 A x s) = (term18 A s x).
Proof. exact (EQ_MP (@lem3211669 A s x) (@lem3211668 A s x)). Qed.
Lemma lem8053924 {_143007 _143009 : Type'} (s : type56 _143007 _143009) (x : cart _143007 _143009) : (term19 _143007 _143009 x s) = (term20 _143007 _143009 s x).
Proof. exact (@lem8053923 (cart _143007 _143009) s x). Qed.
Lemma lem8053925 {_143007 _143009 : Type'} (y : cart _143007 _143009) : (term21 _143007 _143009 y) = (term22 _143007 _143009 y).
Proof. exact (@lem8053924 _143007 _143009 (@EMPTY ((cart _143007 _143009) -> Prop)) y). Qed.
Lemma lem8053933 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem8053934 {_143007 _143009 : Type'} (x : type24 _143007 _143009) : (@IN ((cart _143007 _143009) -> Prop) x (@EMPTY ((cart _143007 _143009) -> Prop))) = False.
Proof. exact (@lem8053933 (type24 _143007 _143009) x). Qed.
Lemma lem8053935 {_143007 _143009 : Type'} (t : type24 _143007 _143009) : (@IN ((cart _143007 _143009) -> Prop) t (@EMPTY ((cart _143007 _143009) -> Prop))) = False.
Proof. exact (@lem8053934 _143007 _143009 t). Qed.
Lemma lem8053936 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8053937 {_143007 _143009 : Type'} (t : type24 _143007 _143009) : (term23 _143007 _143009 t) = (imp False).
Proof. exact (MK_COMB (@lem8053936) (@lem8053935 _143007 _143009 t)). Qed.
Lemma lem8053939 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem8053940 {_143007 _143009 : Type'} (P : type24 _143007 _143009) (x : cart _143007 _143009) : (@IN (cart _143007 _143009) x P) = (P x).
Proof. exact (@lem8053939 (cart _143007 _143009) P x). Qed.
Lemma lem8053941 {_143007 _143009 : Type'} (t : type24 _143007 _143009) (y : cart _143007 _143009) : (@IN (cart _143007 _143009) y t) = (t y).
Proof. exact (@lem8053940 _143007 _143009 t y). Qed.
Lemma lem8053942 {_143007 _143009 : Type'} (t : type24 _143007 _143009) (y : cart _143007 _143009) : (term24 _143007 _143009 y t) = (term25 _143007 _143009 t y).
Proof. exact (MK_COMB (@lem8053937 _143007 _143009 t) (@lem8053941 _143007 _143009 t y)). Qed.
Lemma lem8053944 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem8053945 {_143007 _143009 : Type'} (t : type24 _143007 _143009) (y : cart _143007 _143009) : (term25 _143007 _143009 t y) = True.
Proof. exact (@lem8053944 (t y)). Qed.
Lemma lem8053946 {_143007 _143009 : Type'} (y : cart _143007 _143009) (t : type24 _143007 _143009) : (term24 _143007 _143009 y t) = True.
Proof. exact (TRANS (@lem8053942 _143007 _143009 t y) (@lem8053945 _143007 _143009 t y)). Qed.
Lemma lem8053947 {_143007 _143009 : Type'} (y : cart _143007 _143009) : (term26 _143007 _143009 y) = (term27 _143007 _143009).
Proof. exact (fun_ext (fun t : type24 _143007 _143009 => @lem8053946 _143007 _143009 y t)). Qed.
Lemma lem8053948 {_143007 _143009 : Type'} : (@all ((cart _143007 _143009) -> Prop)) = (@all ((cart _143007 _143009) -> Prop)).
Proof. exact (eq_refl (@all ((cart _143007 _143009) -> Prop))). Qed.
Lemma lem8053949 {_143007 _143009 : Type'} (y : cart _143007 _143009) : (term22 _143007 _143009 y) = (term28 _143007 _143009).
Proof. exact (MK_COMB (@lem8053948 _143007 _143009) (@lem8053947 _143007 _143009 y)). Qed.
Lemma lem8053951 {A : Type'} (t : Prop) : (term29 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem8053952 {_143007 _143009 : Type'} (t : Prop) : (term30 _143007 _143009 t) = t.
Proof. exact (@lem8053951 (type24 _143007 _143009) t). Qed.
Lemma lem8053953 {_143007 _143009 : Type'} : (term28 _143007 _143009) = True.
Proof. exact (@lem8053952 _143007 _143009 True). Qed.
Lemma lem8053954 {_143007 _143009 : Type'} (y : cart _143007 _143009) : (term22 _143007 _143009 y) = True.
Proof. exact (TRANS (@lem8053949 _143007 _143009 y) (@lem8053953 _143007 _143009)). Qed.
Lemma lem8053955 {_143007 _143009 : Type'} (y : cart _143007 _143009) : (term21 _143007 _143009 y) = True.
Proof. exact (TRANS (@lem8053925 _143007 _143009 y) (@lem8053954 _143007 _143009 y)). Qed.
Lemma lem8053956 {_143007 _143008 _143009 : Type'} (y : cart _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) : (term31 _143007 _143008 _143009 x s y) = (term32 _143007 _143008 s x).
Proof. exact (MK_COMB (@lem8053921 _143007 _143008 s x) (@lem8053955 _143007 _143009 y)). Qed.
Lemma lem8053958 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem8053959 {_143007 _143008 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) : (term32 _143007 _143008 s x) = (s x).
Proof. exact (@lem8053958 (s x)). Qed.
Lemma lem8053960 {_143007 _143008 _143009 : Type'} (y : cart _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) : (term31 _143007 _143008 _143009 x s y) = (s x).
Proof. exact (TRANS (@lem8053956 _143007 _143008 _143009 y s x) (@lem8053959 _143007 _143008 s x)). Qed.
Lemma lem8053961 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8053962 {_143007 _143008 _143009 : Type'} (y : cart _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) : (term33 _143007 _143008 _143009 x s y) = (term34 _143007 _143008 s x).
Proof. exact (MK_COMB (@lem8053961) (@lem8053960 _143007 _143008 _143009 y s x)). Qed.
Lemma lem8053966 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem8053967 {_143007 _143008 : Type'} (P : type24 _143007 _143008) (x : cart _143007 _143008) : (@IN (cart _143007 _143008) x P) = (P x).
Proof. exact (@lem8053966 (cart _143007 _143008) P x). Qed.
Lemma lem8053968 {_143007 _143008 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) : (@IN (cart _143007 _143008) x s) = (s x).
Proof. exact (@lem8053967 _143007 _143008 s x). Qed.
Lemma lem8053969 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8053970 {_143007 _143008 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) : (term15 _143007 _143008 x s) = (term16 _143007 _143008 s x).
Proof. exact (MK_COMB (@lem8053969) (@lem8053968 _143007 _143008 s x)). Qed.
Lemma lem8053972 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3211725 A x) (@lem3211724 A x)). Qed.
Lemma lem8053973 {_143007 _143009 : Type'} (x : cart _143007 _143009) : (@IN (cart _143007 _143009) x (@UNIV (cart _143007 _143009))) = True.
Proof. exact (@lem8053972 (cart _143007 _143009) x). Qed.
Lemma lem8053974 {_143007 _143009 : Type'} (y : cart _143007 _143009) : (@IN (cart _143007 _143009) y (@UNIV (cart _143007 _143009))) = True.
Proof. exact (@lem8053973 _143007 _143009 y). Qed.
Lemma lem8053975 {_143007 _143008 _143009 : Type'} (y : cart _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) : (term35 _143007 _143008 _143009 x s y) = (term32 _143007 _143008 s x).
Proof. exact (MK_COMB (@lem8053970 _143007 _143008 s x) (@lem8053974 _143007 _143009 y)). Qed.
Lemma lem8053977 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem8053978 {_143007 _143008 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) : (term32 _143007 _143008 s x) = (s x).
Proof. exact (@lem8053977 (s x)). Qed.
Lemma lem8053979 {_143007 _143008 _143009 : Type'} (y : cart _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) : (term35 _143007 _143008 _143009 x s y) = (s x).
Proof. exact (TRANS (@lem8053975 _143007 _143008 _143009 y s x) (@lem8053978 _143007 _143008 s x)). Qed.
Lemma lem8053980 {_143007 _143008 _143009 : Type'} (y : cart _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) : ((term31 _143007 _143008 _143009 x s y) = (term35 _143007 _143008 _143009 x s y)) = ((s x) = (s x)).
Proof. exact (MK_COMB (@lem8053962 _143007 _143008 _143009 y s x) (@lem8053979 _143007 _143008 _143009 y s x)). Qed.
Lemma lem8053982 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem8053983 (x : Prop) : (x = x) = True.
Proof. exact (@lem8053982 Prop x). Qed.
Lemma lem8053984 {_143007 _143008 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) : ((s x) = (s x)) = True.
Proof. exact (@lem8053983 (s x)). Qed.
Lemma lem8053985 {_143007 _143008 _143009 : Type'} (x : cart _143007 _143008) (s : type24 _143007 _143008) (y : cart _143007 _143009) : ((term31 _143007 _143008 _143009 x s y) = (term35 _143007 _143008 _143009 x s y)) = True.
Proof. exact (TRANS (@lem8053980 _143007 _143008 _143009 y s x) (@lem8053984 _143007 _143008 s x)). Qed.
Lemma lem8053986 {_143007 _143008 _143009 : Type'} (x : cart _143007 _143008) (s : type24 _143007 _143008) : (term36 _143007 _143008 _143009 x s) = (term37 _143007 _143009).
Proof. exact (fun_ext (fun y : cart _143007 _143009 => @lem8053985 _143007 _143008 _143009 x s y)). Qed.
Lemma lem8053987 {_143007 _143009 : Type'} : (@all (cart _143007 _143009)) = (@all (cart _143007 _143009)).
Proof. exact (eq_refl (@all (cart _143007 _143009))). Qed.
Lemma lem8053988 {_143007 _143008 _143009 : Type'} (x : cart _143007 _143008) (s : type24 _143007 _143008) : (term38 _143007 _143008 _143009 x s) = (term39 _143007 _143009).
Proof. exact (MK_COMB (@lem8053987 _143007 _143009) (@lem8053986 _143007 _143008 _143009 x s)). Qed.
Lemma lem8053990 {A : Type'} (t : Prop) : (term29 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem8053991 {_143007 _143009 : Type'} (t : Prop) : (term40 _143007 _143009 t) = t.
Proof. exact (@lem8053990 (cart _143007 _143009) t). Qed.
Lemma lem8053992 {_143007 _143009 : Type'} : (term39 _143007 _143009) = True.
Proof. exact (@lem8053991 _143007 _143009 True). Qed.
Lemma lem8053993 {_143007 _143008 _143009 : Type'} (x : cart _143007 _143008) (s : type24 _143007 _143008) : (term38 _143007 _143008 _143009 x s) = True.
Proof. exact (TRANS (@lem8053988 _143007 _143008 _143009 x s) (@lem8053992 _143007 _143009)). Qed.
Lemma lem8053994 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) : (term41 _143007 _143008 _143009 s) = (term37 _143007 _143008).
Proof. exact (fun_ext (fun x : cart _143007 _143008 => @lem8053993 _143007 _143008 _143009 x s)). Qed.
Lemma lem8053995 {_143007 _143008 : Type'} : (@all (cart _143007 _143008)) = (@all (cart _143007 _143008)).
Proof. exact (eq_refl (@all (cart _143007 _143008))). Qed.
Lemma lem8053996 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) : (term5 _143007 _143008 _143009 s) = (term39 _143007 _143008).
Proof. exact (MK_COMB (@lem8053995 _143007 _143008) (@lem8053994 _143007 _143008 _143009 s)). Qed.
Lemma lem8053998 {A : Type'} (t : Prop) : (term29 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem8053999 {_143007 _143008 : Type'} (t : Prop) : (term40 _143007 _143008 t) = t.
Proof. exact (@lem8053998 (cart _143007 _143008) t). Qed.
Lemma lem8054000 {_143007 _143008 : Type'} : (term39 _143007 _143008) = True.
Proof. exact (@lem8053999 _143007 _143008 True). Qed.
Lemma lem8054001 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) : (term5 _143007 _143008 _143009 s) = True.
Proof. exact (TRANS (@lem8053996 _143007 _143008 _143009 s) (@lem8054000 _143007 _143008)). Qed.
Lemma lem8054002 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) (f : type56 _143007 _143009) : (term7 _143007 _143008 _143009 f s) = (term42 _143007 _143009 f).
Proof. exact (MK_COMB (@lem8053903 _143007 _143009 f) (@lem8054001 _143007 _143008 _143009 s)). Qed.
Lemma lem8054004 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem8054005 {_143007 _143009 : Type'} (f : type56 _143007 _143009) : (term42 _143007 _143009 f) = True.
Proof. exact (@lem8054004 (term13 _143007 _143009 f)). Qed.
Lemma lem8054006 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : (term7 _143007 _143008 _143009 f s) = True.
Proof. exact (TRANS (@lem8054002 _143007 _143008 _143009 s f) (@lem8054005 _143007 _143009 f)). Qed.
Lemma lem8054007 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : True = (term7 _143007 _143008 _143009 f s).
Proof. exact (SYM (@lem8054006 _143007 _143008 _143009 f s)). Qed.
Lemma lem8054008 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : term7 _143007 _143008 _143009 f s.
Proof. exact (EQ_MP (@lem8054007 _143007 _143008 _143009 f s) (@lem0)). Qed.
Lemma lem8054009 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : term6 _143007 _143008 _143009 f s.
Proof. exact (EQ_MP (@lem8053872 _143007 _143008 _143009 f s) (@lem8054008 _143007 _143008 _143009 f s)). Qed.
Lemma lem8054010 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) (f : type56 _143007 _143009) (h1 : f = (@EMPTY ((cart _143007 _143009) -> Prop))) : term5 _143007 _143008 _143009 s.
Proof. exact (@lem8054009 _143007 _143008 _143009 f s (@lem8049006 _143007 _143009 f h1)). Qed.
