Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INJECTIVE_ON_PREIMAGE_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import SUBSET_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1822_spec.
Require Import thm1834_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm1845_spec.
Require Import thm1857_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19490_spec.
Require Import thm19699_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm32_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211640_spec.
Require Import thm3211641_spec.
Require Import thm3211656_spec.
Require Import thm3211657_spec.
Require Import thm3211692_spec.
Require Import thm3211693_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem5042895 {A : Type'} (s : A -> Prop) : term0 A s.
Proof. exact (@lem3194148 A s). Qed.
Lemma lem5042896 {A : Type'} (s : A -> Prop) : (term0 A s) = (term1 A s).
Proof. exact (eq_refl (term0 A s)). Qed.
Lemma lem5042897 {A : Type'} (s : A -> Prop) : term1 A s.
Proof. exact (EQ_MP (@lem5042896 A s) (@lem5042895 A s)). Qed.
Lemma lem5042898 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term2 A s t.
Proof. exact (@lem5042897 A s t). Qed.
Lemma lem5042899 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term2 A s t) = ((@SUBSET A s t) = (term3 A s t)).
Proof. exact (eq_refl (term2 A s t)). Qed.
Lemma lem5042901 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term4 A B u s f) : term4 A B u s f.
Proof. exact (h1). Qed.
Lemma lem5042902 {A B : Type'} (u : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term5 A B u f s) : term5 A B u f s.
Proof. exact (h1). Qed.
Lemma lem5042903 (t1 : Prop) : term6 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem5042904 (t1 : Prop) : (term6 t1) = (term7 t1).
Proof. exact (eq_refl (term6 t1)). Qed.
Lemma lem5042905 (t1 : Prop) : term7 t1.
Proof. exact (EQ_MP (@lem5042904 t1) (@lem5042903 t1)). Qed.
Lemma lem5042906 (t1 : Prop) (t2 : Prop) : term8 t1 t2.
Proof. exact (@lem5042905 t1 t2). Qed.
Lemma lem5042907 (t1 : Prop) (t2 : Prop) : (term8 t1 t2) = (term9 t1 t2).
Proof. exact (eq_refl (term8 t1 t2)). Qed.
Lemma lem5042908 (t1 : Prop) (t2 : Prop) : term9 t1 t2.
Proof. exact (EQ_MP (@lem5042907 t1 t2) (@lem5042906 t1 t2)). Qed.
Lemma lem5042909 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term10 t1 t2 t3.
Proof. exact (@lem5042908 t1 t2 t3). Qed.
Lemma lem5042910 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term10 t1 t2 t3) = ((term11 t1 t2 t3) = (term12 t1 t2 t3)).
Proof. exact (eq_refl (term10 t1 t2 t3)). Qed.
Lemma lem5042911 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term11 t1 t2 t3) = (term12 t1 t2 t3).
Proof. exact (EQ_MP (@lem5042910 t1 t2 t3) (@lem5042909 t1 t2 t3)). Qed.
Lemma lem5042912 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term12 t1 t2 t3) = (term11 t1 t2 t3).
Proof. exact (SYM (@lem5042911 t1 t2 t3)). Qed.
Lemma lem5042916 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term3 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem5042917 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (@SUBSET B s t) = (term3 B s t).
Proof. exact (@lem5042916 B s t). Qed.
Lemma lem5042918 {A B : Type'} (u : B -> Prop) (f : A -> B) (s : A -> Prop) : (term5 A B u f s) = (term13 A B u f s).
Proof. exact (@lem5042917 B u (@IMAGE A B f s)). Qed.
Lemma lem5042925 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5042926 {A B : Type'} (u : B -> Prop) (f : A -> B) (s : A -> Prop) : (term14 A B u f s) = (term15 A B u f s).
Proof. exact (MK_COMB (@lem5042925) (@lem5042918 A B u f s)). Qed.
Lemma lem5042940 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term3 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem5042941 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (@SUBSET B s t) = (term3 B s t).
Proof. exact (@lem5042940 B s t). Qed.
Lemma lem5042942 {B : Type'} (t : B -> Prop) (u : B -> Prop) : (@SUBSET B t u) = (term3 B t u).
Proof. exact (@lem5042941 B t u). Qed.
Lemma lem5042949 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5042950 {B : Type'} (t : B -> Prop) (u : B -> Prop) : (term16 B t u) = (term17 B t u).
Proof. exact (MK_COMB (@lem5042949) (@lem5042942 B t u)). Qed.
Lemma lem5042954 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term3 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem5042955 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (@SUBSET B s t) = (term3 B s t).
Proof. exact (@lem5042954 B s t). Qed.
Lemma lem5042956 {B : Type'} (t' : B -> Prop) (u : B -> Prop) : (@SUBSET B t' u) = (term3 B t' u).
Proof. exact (@lem5042955 B t' u). Qed.
Lemma lem5042963 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5042964 {B : Type'} (t' : B -> Prop) (u : B -> Prop) : (term16 B t' u) = (term17 B t' u).
Proof. exact (MK_COMB (@lem5042963) (@lem5042956 B t' u)). Qed.
Lemma lem5042968 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term18 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem5042969 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term18 A s t).
Proof. exact (@lem5042968 A s t). Qed.
Lemma lem5042970 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (t' : B -> Prop) : ((term19 A B s f t) = (term19 A B s f t')) = (term20 A B t s f t').
Proof. exact (@lem5042969 A (term19 A B s f t) (term19 A B s f t')). Qed.
Lemma lem5042991 {A B : Type'} (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (t' : B -> Prop) : (term21 A B u t s f t') = (term22 A B u t s f t').
Proof. exact (MK_COMB (@lem5042964 B t' u) (@lem5042970 A B t s f t')). Qed.
Lemma lem5042994 {A B : Type'} (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (t' : B -> Prop) : (term23 A B u t s f t') = (term24 A B u t s f t').
Proof. exact (MK_COMB (@lem5042950 B t u) (@lem5042991 A B u t s f t')). Qed.
Lemma lem5042997 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5042998 {A B : Type'} (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (t' : B -> Prop) : (term25 A B u t s f t') = (term26 A B u t s f t').
Proof. exact (MK_COMB (@lem5042997) (@lem5042994 A B u t s f t')). Qed.
Lemma lem5043002 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term18 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem5043003 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (s = t) = (term18 B s t).
Proof. exact (@lem5043002 B s t). Qed.
Lemma lem5043004 {B : Type'} (t : B -> Prop) (t' : B -> Prop) : (t = t') = (term18 B t t').
Proof. exact (@lem5043003 B t t'). Qed.
Lemma lem5043013 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) : (term27 A B u s f t t') = (term28 A B u s f t t').
Proof. exact (MK_COMB (@lem5042998 A B u t s f t') (@lem5043004 B t t')). Qed.
Lemma lem5043016 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term29 A B u s f t) = (term30 A B u s f t).
Proof. exact (fun_ext (fun t' : B -> Prop => @lem5043013 A B u s f t t')). Qed.
Lemma lem5043017 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5043018 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term31 A B u s f t) = (term32 A B u s f t).
Proof. exact (MK_COMB (@lem5043017 B) (@lem5043016 A B u s f t)). Qed.
Lemma lem5043023 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) : (term33 A B u s f) = (term34 A B u s f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5043018 A B u s f t)). Qed.
Lemma lem5043024 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5043025 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) : (term4 A B u s f) = (term35 A B u s f).
Proof. exact (MK_COMB (@lem5043024 B) (@lem5043023 A B u s f)). Qed.
Lemma lem5043030 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) : (term36 A B u s f) = (term37 A B u s f).
Proof. exact (MK_COMB (@lem5042926 A B u f s) (@lem5043025 A B u s f)). Qed.
Lemma lem5043033 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) : (term37 A B u s f) = (term36 A B u s f).
Proof. exact (SYM (@lem5043030 A B u s f)). Qed.
Lemma lem5043043 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5043044 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem5043043 B P x). Qed.
Lemma lem5043045 {B : Type'} (u : B -> Prop) (x : B) : (@IN B x u) = (u x).
Proof. exact (@lem5043044 B u x). Qed.
Lemma lem5043046 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5043047 {B : Type'} (u : B -> Prop) (x : B) : (term38 B x u) = (term39 B u x).
Proof. exact (MK_COMB (@lem5043046) (@lem5043045 B u x)). Qed.
Lemma lem5043049 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term40 A B y f s) = (term41 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem5043050 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term40 A B y f s) = (term41 A B y f s).
Proof. exact (@lem5043049 A B y f s). Qed.
Lemma lem5043051 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term40 A B x f s) = (term41 A B x f s).
Proof. exact (@lem5043050 A B x f s). Qed.
Lemma lem5043061 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5043062 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5043061 A P x). Qed.
Lemma lem5043063 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem5043062 A s x). Qed.
Lemma lem5043064 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term42 A B x f x') = (term42 A B x f x').
Proof. exact (eq_refl (term42 A B x f x')). Qed.
Lemma lem5043065 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term43 A B x f x' s) = (term44 A B x f s x').
Proof. exact (MK_COMB (@lem5043064 A B x f x') (@lem5043063 A s x')). Qed.
Lemma lem5043068 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term45 A B x f s) = (term46 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem5043065 A B x f s x')). Qed.
Lemma lem5043069 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5043070 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term41 A B x f s) = (term47 A B x f s).
Proof. exact (MK_COMB (@lem5043069 A) (@lem5043068 A B x f s)). Qed.
Lemma lem5043075 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term40 A B x f s) = (term47 A B x f s).
Proof. exact (TRANS (@lem5043051 A B x f s) (@lem5043070 A B x f s)). Qed.
Lemma lem5043076 {A B : Type'} (u : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term48 A B u x f s) = (term49 A B u x f s).
Proof. exact (MK_COMB (@lem5043047 B u x) (@lem5043075 A B x f s)). Qed.
Lemma lem5043079 {A B : Type'} (u : B -> Prop) (f : A -> B) (s : A -> Prop) : (term50 A B u f s) = (term51 A B u f s).
Proof. exact (fun_ext (fun x : B => @lem5043076 A B u x f s)). Qed.
Lemma lem5043080 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5043081 {A B : Type'} (u : B -> Prop) (f : A -> B) (s : A -> Prop) : (term13 A B u f s) = (term52 A B u f s).
Proof. exact (MK_COMB (@lem5043080 B) (@lem5043079 A B u f s)). Qed.
Lemma lem5043086 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5043087 {A B : Type'} (u : B -> Prop) (f : A -> B) (s : A -> Prop) : (term15 A B u f s) = (term53 A B u f s).
Proof. exact (MK_COMB (@lem5043086) (@lem5043081 A B u f s)). Qed.
Lemma lem5043107 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5043108 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem5043107 B P x). Qed.
Lemma lem5043109 {B : Type'} (t : B -> Prop) (x : B) : (@IN B x t) = (t x).
Proof. exact (@lem5043108 B t x). Qed.
Lemma lem5043110 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5043111 {B : Type'} (t : B -> Prop) (x : B) : (term38 B x t) = (term39 B t x).
Proof. exact (MK_COMB (@lem5043110) (@lem5043109 B t x)). Qed.
Lemma lem5043113 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5043114 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem5043113 B P x). Qed.
Lemma lem5043115 {B : Type'} (u : B -> Prop) (x : B) : (@IN B x u) = (u x).
Proof. exact (@lem5043114 B u x). Qed.
Lemma lem5043116 {B : Type'} (t : B -> Prop) (u : B -> Prop) (x : B) : (term54 B t x u) = (term55 B t u x).
Proof. exact (MK_COMB (@lem5043111 B t x) (@lem5043115 B u x)). Qed.
Lemma lem5043119 {B : Type'} (t : B -> Prop) (u : B -> Prop) : (term56 B t u) = (term57 B t u).
Proof. exact (fun_ext (fun x : B => @lem5043116 B t u x)). Qed.
Lemma lem5043120 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5043121 {B : Type'} (t : B -> Prop) (u : B -> Prop) : (term3 B t u) = (term58 B t u).
Proof. exact (MK_COMB (@lem5043120 B) (@lem5043119 B t u)). Qed.
Lemma lem5043126 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5043127 {B : Type'} (t : B -> Prop) (u : B -> Prop) : (term17 B t u) = (term59 B t u).
Proof. exact (MK_COMB (@lem5043126) (@lem5043121 B t u)). Qed.
Lemma lem5043137 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5043138 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem5043137 B P x). Qed.
Lemma lem5043139 {B : Type'} (t' : B -> Prop) (x : B) : (@IN B x t') = (t' x).
Proof. exact (@lem5043138 B t' x). Qed.
Lemma lem5043140 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5043141 {B : Type'} (t' : B -> Prop) (x : B) : (term38 B x t') = (term39 B t' x).
Proof. exact (MK_COMB (@lem5043140) (@lem5043139 B t' x)). Qed.
Lemma lem5043143 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5043144 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem5043143 B P x). Qed.
Lemma lem5043145 {B : Type'} (u : B -> Prop) (x : B) : (@IN B x u) = (u x).
Proof. exact (@lem5043144 B u x). Qed.
Lemma lem5043146 {B : Type'} (t' : B -> Prop) (u : B -> Prop) (x : B) : (term54 B t' x u) = (term55 B t' u x).
Proof. exact (MK_COMB (@lem5043141 B t' x) (@lem5043145 B u x)). Qed.
Lemma lem5043149 {B : Type'} (t' : B -> Prop) (u : B -> Prop) : (term56 B t' u) = (term57 B t' u).
Proof. exact (fun_ext (fun x : B => @lem5043146 B t' u x)). Qed.
Lemma lem5043150 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5043151 {B : Type'} (t' : B -> Prop) (u : B -> Prop) : (term3 B t' u) = (term58 B t' u).
Proof. exact (MK_COMB (@lem5043150 B) (@lem5043149 B t' u)). Qed.
Lemma lem5043156 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5043157 {B : Type'} (t' : B -> Prop) (u : B -> Prop) : (term17 B t' u) = (term59 B t' u).
Proof. exact (MK_COMB (@lem5043156) (@lem5043151 B t' u)). Qed.
Lemma lem5043165 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term60 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem5043166 {A : Type'} (p : A -> Prop) (x : A) : (term60 A x p) = (p x).
Proof. exact (@lem5043165 A p x). Qed.
Lemma lem5043167 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) (x : A) : (term61 A B x s f t) = (term62 A B s f t x).
Proof. exact (@lem5043166 A (term63 A B s f t) x). Qed.
Lemma lem5043168 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (t : B -> Prop) : (term62 A B s f t x) = (term64 A B s f x t).
Proof. exact (eq_refl (term62 A B s f t x)). Qed.
Lemma lem5043169 {A : Type'} (GEN_PVAR_220 : A) : (@SETSPEC A GEN_PVAR_220) = (@SETSPEC A GEN_PVAR_220).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_220)). Qed.
Lemma lem5043170 {A B : Type'} (GEN_PVAR_220 : A) (s : A -> Prop) (f : A -> B) (x : A) (t : B -> Prop) : (term65 A B GEN_PVAR_220 s f t x) = (term66 A B GEN_PVAR_220 s f x t).
Proof. exact (MK_COMB (@lem5043169 A GEN_PVAR_220) (@lem5043168 A B s f x t)). Qed.
Lemma lem5043171 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5043172 {A B : Type'} (GEN_PVAR_220 : A) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (x : A) : (term67 A B GEN_PVAR_220 s f t x) = (term68 A B GEN_PVAR_220 s f t x).
Proof. exact (MK_COMB (@lem5043170 A B GEN_PVAR_220 s f x t) (@lem5043171 A x)). Qed.
Lemma lem5043173 {A B : Type'} (GEN_PVAR_220 : A) (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term69 A B GEN_PVAR_220 s f t) = (term70 A B GEN_PVAR_220 s f t).
Proof. exact (fun_ext (fun x : A => @lem5043172 A B GEN_PVAR_220 s f t x)). Qed.
Lemma lem5043174 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5043175 {A B : Type'} (GEN_PVAR_220 : A) (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term71 A B GEN_PVAR_220 s f t) = (term72 A B GEN_PVAR_220 s f t).
Proof. exact (MK_COMB (@lem5043174 A) (@lem5043173 A B GEN_PVAR_220 s f t)). Qed.
Lemma lem5043176 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term73 A B s f t) = (term74 A B s f t).
Proof. exact (fun_ext (fun GEN_PVAR_220 : A => @lem5043175 A B GEN_PVAR_220 s f t)). Qed.
Lemma lem5043177 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem5043178 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term75 A B s f t) = (term19 A B s f t).
Proof. exact (MK_COMB (@lem5043177 A) (@lem5043176 A B s f t)). Qed.
Lemma lem5043179 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem5043180 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term61 A B x s f t) = (term76 A B x s f t).
Proof. exact (MK_COMB (@lem5043179 A x) (@lem5043178 A B s f t)). Qed.
Lemma lem5043181 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5043182 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term77 A B x s f t) = (term78 A B x s f t).
Proof. exact (MK_COMB (@lem5043181) (@lem5043180 A B x s f t)). Qed.
Lemma lem5043183 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (t : B -> Prop) : (term62 A B s f t x) = (term64 A B s f x t).
Proof. exact (eq_refl (term62 A B s f t x)). Qed.
Lemma lem5043184 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (t : B -> Prop) : ((term61 A B x s f t) = (term62 A B s f t x)) = ((term76 A B x s f t) = (term64 A B s f x t)).
Proof. exact (MK_COMB (@lem5043182 A B x s f t) (@lem5043183 A B s f x t)). Qed.
Lemma lem5043185 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (t : B -> Prop) : (term76 A B x s f t) = (term64 A B s f x t).
Proof. exact (EQ_MP (@lem5043184 A B s f x t) (@lem5043167 A B s f t x)). Qed.
Lemma lem5043189 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5043190 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5043189 A P x). Qed.
Lemma lem5043191 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem5043190 A s x). Qed.
Lemma lem5043192 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5043193 {A : Type'} (s : A -> Prop) (x : A) : (term79 A x s) = (term80 A s x).
Proof. exact (MK_COMB (@lem5043192) (@lem5043191 A s x)). Qed.
Lemma lem5043195 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5043196 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem5043195 B P x). Qed.
Lemma lem5043197 {A B : Type'} (t : B -> Prop) (f : A -> B) (x : A) : (term81 A B f x t) = (term82 A B t f x).
Proof. exact (@lem5043196 B t (f x)). Qed.
Lemma lem5043198 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term64 A B s f x t) = (term83 A B s t f x).
Proof. exact (MK_COMB (@lem5043193 A s x) (@lem5043197 A B t f x)). Qed.
Lemma lem5043201 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term76 A B x s f t) = (term83 A B s t f x).
Proof. exact (TRANS (@lem5043185 A B s f x t) (@lem5043198 A B s t f x)). Qed.
Lemma lem5043202 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5043203 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term78 A B x s f t) = (term84 A B s t f x).
Proof. exact (MK_COMB (@lem5043202) (@lem5043201 A B s t f x)). Qed.
Lemma lem5043205 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term60 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem5043206 {A : Type'} (p : A -> Prop) (x : A) : (term60 A x p) = (p x).
Proof. exact (@lem5043205 A p x). Qed.
Lemma lem5043207 {A B : Type'} (s : A -> Prop) (f : A -> B) (t' : B -> Prop) (x : A) : (term61 A B x s f t') = (term62 A B s f t' x).
Proof. exact (@lem5043206 A (term63 A B s f t') x). Qed.
Lemma lem5043208 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (t' : B -> Prop) : (term62 A B s f t' x) = (term64 A B s f x t').
Proof. exact (eq_refl (term62 A B s f t' x)). Qed.
Lemma lem5043209 {A : Type'} (GEN_PVAR_221 : A) : (@SETSPEC A GEN_PVAR_221) = (@SETSPEC A GEN_PVAR_221).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_221)). Qed.
Lemma lem5043210 {A B : Type'} (GEN_PVAR_221 : A) (s : A -> Prop) (f : A -> B) (x : A) (t' : B -> Prop) : (term65 A B GEN_PVAR_221 s f t' x) = (term66 A B GEN_PVAR_221 s f x t').
Proof. exact (MK_COMB (@lem5043209 A GEN_PVAR_221) (@lem5043208 A B s f x t')). Qed.
Lemma lem5043211 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5043212 {A B : Type'} (GEN_PVAR_221 : A) (s : A -> Prop) (f : A -> B) (t' : B -> Prop) (x : A) : (term67 A B GEN_PVAR_221 s f t' x) = (term68 A B GEN_PVAR_221 s f t' x).
Proof. exact (MK_COMB (@lem5043210 A B GEN_PVAR_221 s f x t') (@lem5043211 A x)). Qed.
Lemma lem5043213 {A B : Type'} (GEN_PVAR_221 : A) (s : A -> Prop) (f : A -> B) (t' : B -> Prop) : (term69 A B GEN_PVAR_221 s f t') = (term70 A B GEN_PVAR_221 s f t').
Proof. exact (fun_ext (fun x : A => @lem5043212 A B GEN_PVAR_221 s f t' x)). Qed.
Lemma lem5043214 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5043215 {A B : Type'} (GEN_PVAR_221 : A) (s : A -> Prop) (f : A -> B) (t' : B -> Prop) : (term71 A B GEN_PVAR_221 s f t') = (term72 A B GEN_PVAR_221 s f t').
Proof. exact (MK_COMB (@lem5043214 A) (@lem5043213 A B GEN_PVAR_221 s f t')). Qed.
Lemma lem5043216 {A B : Type'} (s : A -> Prop) (f : A -> B) (t' : B -> Prop) : (term73 A B s f t') = (term74 A B s f t').
Proof. exact (fun_ext (fun GEN_PVAR_221 : A => @lem5043215 A B GEN_PVAR_221 s f t')). Qed.
Lemma lem5043217 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem5043218 {A B : Type'} (s : A -> Prop) (f : A -> B) (t' : B -> Prop) : (term75 A B s f t') = (term19 A B s f t').
Proof. exact (MK_COMB (@lem5043217 A) (@lem5043216 A B s f t')). Qed.
Lemma lem5043219 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem5043220 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (t' : B -> Prop) : (term61 A B x s f t') = (term76 A B x s f t').
Proof. exact (MK_COMB (@lem5043219 A x) (@lem5043218 A B s f t')). Qed.
Lemma lem5043221 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5043222 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (t' : B -> Prop) : (term77 A B x s f t') = (term78 A B x s f t').
Proof. exact (MK_COMB (@lem5043221) (@lem5043220 A B x s f t')). Qed.
Lemma lem5043223 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (t' : B -> Prop) : (term62 A B s f t' x) = (term64 A B s f x t').
Proof. exact (eq_refl (term62 A B s f t' x)). Qed.
Lemma lem5043224 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (t' : B -> Prop) : ((term61 A B x s f t') = (term62 A B s f t' x)) = ((term76 A B x s f t') = (term64 A B s f x t')).
Proof. exact (MK_COMB (@lem5043222 A B x s f t') (@lem5043223 A B s f x t')). Qed.
Lemma lem5043225 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (t' : B -> Prop) : (term76 A B x s f t') = (term64 A B s f x t').
Proof. exact (EQ_MP (@lem5043224 A B s f x t') (@lem5043207 A B s f t' x)). Qed.
Lemma lem5043229 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5043230 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5043229 A P x). Qed.
Lemma lem5043231 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem5043230 A s x). Qed.
Lemma lem5043232 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5043233 {A : Type'} (s : A -> Prop) (x : A) : (term79 A x s) = (term80 A s x).
Proof. exact (MK_COMB (@lem5043232) (@lem5043231 A s x)). Qed.
Lemma lem5043235 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5043236 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem5043235 B P x). Qed.
Lemma lem5043237 {A B : Type'} (t' : B -> Prop) (f : A -> B) (x : A) : (term81 A B f x t') = (term82 A B t' f x).
Proof. exact (@lem5043236 B t' (f x)). Qed.
Lemma lem5043238 {A B : Type'} (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (x : A) : (term64 A B s f x t') = (term83 A B s t' f x).
Proof. exact (MK_COMB (@lem5043233 A s x) (@lem5043237 A B t' f x)). Qed.
Lemma lem5043241 {A B : Type'} (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (x : A) : (term76 A B x s f t') = (term83 A B s t' f x).
Proof. exact (TRANS (@lem5043225 A B s f x t') (@lem5043238 A B s t' f x)). Qed.
Lemma lem5043242 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (x : A) : ((term76 A B x s f t) = (term76 A B x s f t')) = ((term83 A B s t f x) = (term83 A B s t' f x)).
Proof. exact (MK_COMB (@lem5043203 A B s t f x) (@lem5043241 A B s t' f x)). Qed.
Lemma lem5043245 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) : (term85 A B t s f t') = (term86 A B t s t' f).
Proof. exact (fun_ext (fun x : A => @lem5043242 A B t s t' f x)). Qed.
Lemma lem5043246 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5043247 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) : (term20 A B t s f t') = (term87 A B t s t' f).
Proof. exact (MK_COMB (@lem5043246 A) (@lem5043245 A B t s t' f)). Qed.
Lemma lem5043252 {A B : Type'} (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) : (term22 A B u t s f t') = (term88 A B u t s t' f).
Proof. exact (MK_COMB (@lem5043157 B t' u) (@lem5043247 A B t s t' f)). Qed.
Lemma lem5043255 {A B : Type'} (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) : (term24 A B u t s f t') = (term89 A B u t s t' f).
Proof. exact (MK_COMB (@lem5043127 B t u) (@lem5043252 A B u t s t' f)). Qed.
Lemma lem5043258 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5043259 {A B : Type'} (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) : (term26 A B u t s f t') = (term90 A B u t s t' f).
Proof. exact (MK_COMB (@lem5043258) (@lem5043255 A B u t s t' f)). Qed.
Lemma lem5043267 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5043268 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem5043267 B P x). Qed.
Lemma lem5043269 {B : Type'} (t : B -> Prop) (x : B) : (@IN B x t) = (t x).
Proof. exact (@lem5043268 B t x). Qed.
Lemma lem5043270 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5043271 {B : Type'} (t : B -> Prop) (x : B) : (term91 B x t) = (term92 B t x).
Proof. exact (MK_COMB (@lem5043270) (@lem5043269 B t x)). Qed.
Lemma lem5043273 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5043274 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem5043273 B P x). Qed.
Lemma lem5043275 {B : Type'} (t' : B -> Prop) (x : B) : (@IN B x t') = (t' x).
Proof. exact (@lem5043274 B t' x). Qed.
Lemma lem5043276 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x : B) : ((@IN B x t) = (@IN B x t')) = ((t x) = (t' x)).
Proof. exact (MK_COMB (@lem5043271 B t x) (@lem5043275 B t' x)). Qed.
Lemma lem5043279 {B : Type'} (t : B -> Prop) (t' : B -> Prop) : (term93 B t t') = (term94 B t t').
Proof. exact (fun_ext (fun x : B => @lem5043276 B t t' x)). Qed.
Lemma lem5043280 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5043281 {B : Type'} (t : B -> Prop) (t' : B -> Prop) : (term18 B t t') = (term95 B t t').
Proof. exact (MK_COMB (@lem5043280 B) (@lem5043279 B t t')). Qed.
Lemma lem5043286 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) : (term28 A B u s f t t') = (term96 A B u s f t t').
Proof. exact (MK_COMB (@lem5043259 A B u t s t' f) (@lem5043281 B t t')). Qed.
Lemma lem5043289 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term30 A B u s f t) = (term97 A B u s f t).
Proof. exact (fun_ext (fun t' : B -> Prop => @lem5043286 A B u s f t t')). Qed.
Lemma lem5043290 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5043291 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term32 A B u s f t) = (term98 A B u s f t).
Proof. exact (MK_COMB (@lem5043290 B) (@lem5043289 A B u s f t)). Qed.
Lemma lem5043296 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) : (term34 A B u s f) = (term99 A B u s f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5043291 A B u s f t)). Qed.
Lemma lem5043297 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5043298 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) : (term35 A B u s f) = (term100 A B u s f).
Proof. exact (MK_COMB (@lem5043297 B) (@lem5043296 A B u s f)). Qed.
Lemma lem5043303 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) : (term37 A B u s f) = (term101 A B u s f).
Proof. exact (MK_COMB (@lem5043087 A B u f s) (@lem5043298 A B u s f)). Qed.
Lemma lem5043306 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) : (term101 A B u s f) = (term37 A B u s f).
Proof. exact (SYM (@lem5043303 A B u s f)). Qed.
Lemma lem5043308 (p : Prop) : p = (term102 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5043309 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) : (term101 A B u s f) = (term103 A B u s f).
Proof. exact (@lem5043308 (term101 A B u s f)). Qed.
Lemma lem5043310 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) : (term103 A B u s f) = (term101 A B u s f).
Proof. exact (SYM (@lem5043309 A B u s f)). Qed.
Lemma lem5043311 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term104 A B u s f) : term104 A B u s f.
Proof. exact (h1). Qed.
Lemma lem5043314 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term103 A B u s f) : term103 A B u s f.
Proof. exact (h1). Qed.
Lemma lem5043315 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) : term105 A B u s f.
Proof. exact (fun h0 : term103 A B u s f => @lem5043314 A B u s f h0). Qed.
Lemma lem5043316 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term105 A B u s f) : term105 A B u s f.
Proof. exact (h1). Qed.
Lemma lem5043317 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term103 A B u s f) : term103 A B u s f.
Proof. exact (h1). Qed.
Lemma lem5043318 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term103 A B u s f) (h2 : term105 A B u s f) : term103 A B u s f.
Proof. exact (@lem5043316 A B u s f h2 (@lem5043317 A B u s f h1)). Qed.
Lemma lem5043319 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term103 A B u s f) : term106 A B u s f.
Proof. exact (fun h0 : term105 A B u s f => @lem5043318 A B u s f h1 h0). Qed.
Lemma lem5043320 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term105 A B u s f) : term105 A B u s f.
Proof. exact (h1). Qed.
Lemma lem5043321 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term103 A B u s f) (h2 : term105 A B u s f) : term103 A B u s f.
Proof. exact (@lem5043319 A B u s f h1 (@lem5043320 A B u s f h2)). Qed.
Lemma lem5043322 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term105 A B u s f) : term105 A B u s f.
Proof. exact (fun h0 : term103 A B u s f => @lem5043321 A B u s f h0 h1). Qed.
Lemma lem5043323 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) : term107 A B u s f.
Proof. exact (fun h0 : term105 A B u s f => @lem5043322 A B u s f h0). Qed.
Lemma lem5043326 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) : term105 A B u s f.
Proof. exact (@lem5043323 A B u s f (@lem5043315 A B u s f)). Qed.
Lemma lem5043327 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) : term105 A B u s f.
Proof. exact (@lem5043326 A B u s f). Qed.
Lemma lem5043341 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5043342 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) : (term103 A B u s f) = (term108 A B u s f).
Proof. exact (@lem5043341 (term104 A B u s f)). Qed.
Lemma lem5043344 (t : Prop) : (term109 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5043345 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) : (term108 A B u s f) = (term101 A B u s f).
Proof. exact (@lem5043344 (term101 A B u s f)). Qed.
Lemma lem5043348 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) : (term103 A B u s f) = (term101 A B u s f).
Proof. exact (TRANS (@lem5043342 A B u s f) (@lem5043345 A B u s f)). Qed.
Lemma lem5043427 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term110 A B s f) = (term111 A B s f).
Proof. exact (fun_ext (fun u : B -> Prop => @lem5043348 A B u s f)). Qed.
Lemma lem5043428 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5043429 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term112 A B s f) = (term113 A B s f).
Proof. exact (MK_COMB (@lem5043428 B) (@lem5043427 A B s f)). Qed.
Lemma lem5043434 {A B : Type'} (f : A -> B) : (term114 A B f) = (term115 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5043429 A B s f)). Qed.
Lemma lem5043435 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5043436 {A B : Type'} (f : A -> B) : (term116 A B f) = (term117 A B f).
Proof. exact (MK_COMB (@lem5043435 A) (@lem5043434 A B f)). Qed.
Lemma lem5043441 {A B : Type'} : (term118 A B) = (term119 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem5043436 A B f)). Qed.
Lemma lem5043442 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5043451 {A B : Type'} : (term120 A B) = (term121 A B).
Proof. exact (MK_COMB (@lem5043442 A B) (@lem5043441 A B)). Qed.
Lemma lem5043456 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x : B) : ((t x) = (t' x)) = ((t x) = (t' x)).
Proof. exact (eq_refl ((t x) = (t' x))). Qed.
Lemma lem5043457 {B : Type'} (t : B -> Prop) (t' : B -> Prop) : (term94 B t t') = (term94 B t t').
Proof. exact (fun_ext (fun x : B => @lem5043456 B t t' x)). Qed.
Lemma lem5043458 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5043459 {B : Type'} (t : B -> Prop) (t' : B -> Prop) : (term95 B t t') = (term95 B t t').
Proof. exact (MK_COMB (@lem5043458 B) (@lem5043457 B t t')). Qed.
Lemma lem5043472 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (x : A) : ((term83 A B s t f x) = (term83 A B s t' f x)) = ((term83 A B s t f x) = (term83 A B s t' f x)).
Proof. exact (eq_refl ((term83 A B s t f x) = (term83 A B s t' f x))). Qed.
Lemma lem5043473 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) : (term86 A B t s t' f) = (term86 A B t s t' f).
Proof. exact (fun_ext (fun x : A => @lem5043472 A B t s t' f x)). Qed.
Lemma lem5043474 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5043475 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) : (term87 A B t s t' f) = (term87 A B t s t' f).
Proof. exact (MK_COMB (@lem5043474 A) (@lem5043473 A B t s t' f)). Qed.
Lemma lem5043480 {B : Type'} (t' : B -> Prop) (u : B -> Prop) (x : B) : (term55 B t' u x) = (term55 B t' u x).
Proof. exact (eq_refl (term55 B t' u x)). Qed.
Lemma lem5043481 {B : Type'} (t' : B -> Prop) (u : B -> Prop) : (term57 B t' u) = (term57 B t' u).
Proof. exact (fun_ext (fun x : B => @lem5043480 B t' u x)). Qed.
Lemma lem5043482 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5043483 {B : Type'} (t' : B -> Prop) (u : B -> Prop) : (term58 B t' u) = (term58 B t' u).
Proof. exact (MK_COMB (@lem5043482 B) (@lem5043481 B t' u)). Qed.
Lemma lem5043484 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5043485 {B : Type'} (t' : B -> Prop) (u : B -> Prop) : (term59 B t' u) = (term59 B t' u).
Proof. exact (MK_COMB (@lem5043484) (@lem5043483 B t' u)). Qed.
Lemma lem5043486 {A B : Type'} (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) : (term88 A B u t s t' f) = (term88 A B u t s t' f).
Proof. exact (MK_COMB (@lem5043485 B t' u) (@lem5043475 A B t s t' f)). Qed.
Lemma lem5043491 {B : Type'} (t : B -> Prop) (u : B -> Prop) (x : B) : (term55 B t u x) = (term55 B t u x).
Proof. exact (eq_refl (term55 B t u x)). Qed.
Lemma lem5043492 {B : Type'} (t : B -> Prop) (u : B -> Prop) : (term57 B t u) = (term57 B t u).
Proof. exact (fun_ext (fun x : B => @lem5043491 B t u x)). Qed.
Lemma lem5043493 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5043494 {B : Type'} (t : B -> Prop) (u : B -> Prop) : (term58 B t u) = (term58 B t u).
Proof. exact (MK_COMB (@lem5043493 B) (@lem5043492 B t u)). Qed.
Lemma lem5043495 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5043496 {B : Type'} (t : B -> Prop) (u : B -> Prop) : (term59 B t u) = (term59 B t u).
Proof. exact (MK_COMB (@lem5043495) (@lem5043494 B t u)). Qed.
Lemma lem5043497 {A B : Type'} (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) : (term89 A B u t s t' f) = (term89 A B u t s t' f).
Proof. exact (MK_COMB (@lem5043496 B t u) (@lem5043486 A B u t s t' f)). Qed.
Lemma lem5043498 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5043499 {A B : Type'} (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) : (term90 A B u t s t' f) = (term90 A B u t s t' f).
Proof. exact (MK_COMB (@lem5043498) (@lem5043497 A B u t s t' f)). Qed.
Lemma lem5043500 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) : (term96 A B u s f t t') = (term96 A B u s f t t').
Proof. exact (MK_COMB (@lem5043499 A B u t s t' f) (@lem5043459 B t t')). Qed.
Lemma lem5043501 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term97 A B u s f t) = (term97 A B u s f t).
Proof. exact (fun_ext (fun t' : B -> Prop => @lem5043500 A B u s f t t')). Qed.
Lemma lem5043502 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5043503 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term98 A B u s f t) = (term98 A B u s f t).
Proof. exact (MK_COMB (@lem5043502 B) (@lem5043501 A B u s f t)). Qed.
Lemma lem5043504 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) : (term99 A B u s f) = (term99 A B u s f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5043503 A B u s f t)). Qed.
Lemma lem5043505 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5043506 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) : (term100 A B u s f) = (term100 A B u s f).
Proof. exact (MK_COMB (@lem5043505 B) (@lem5043504 A B u s f)). Qed.
Lemma lem5043511 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term44 A B x f s x') = (term44 A B x f s x').
Proof. exact (eq_refl (term44 A B x f s x')). Qed.
Lemma lem5043512 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term46 A B x f s) = (term46 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem5043511 A B x f s x')). Qed.
Lemma lem5043513 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5043514 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term47 A B x f s) = (term47 A B x f s).
Proof. exact (MK_COMB (@lem5043513 A) (@lem5043512 A B x f s)). Qed.
Lemma lem5043517 {B : Type'} (u : B -> Prop) (x : B) : (term39 B u x) = (term39 B u x).
Proof. exact (eq_refl (term39 B u x)). Qed.
Lemma lem5043518 {A B : Type'} (u : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term49 A B u x f s) = (term49 A B u x f s).
Proof. exact (MK_COMB (@lem5043517 B u x) (@lem5043514 A B x f s)). Qed.
Lemma lem5043519 {A B : Type'} (u : B -> Prop) (f : A -> B) (s : A -> Prop) : (term51 A B u f s) = (term51 A B u f s).
Proof. exact (fun_ext (fun x : B => @lem5043518 A B u x f s)). Qed.
Lemma lem5043520 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5043521 {A B : Type'} (u : B -> Prop) (f : A -> B) (s : A -> Prop) : (term52 A B u f s) = (term52 A B u f s).
Proof. exact (MK_COMB (@lem5043520 B) (@lem5043519 A B u f s)). Qed.
Lemma lem5043522 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5043523 {A B : Type'} (u : B -> Prop) (f : A -> B) (s : A -> Prop) : (term53 A B u f s) = (term53 A B u f s).
Proof. exact (MK_COMB (@lem5043522) (@lem5043521 A B u f s)). Qed.
Lemma lem5043524 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) : (term101 A B u s f) = (term101 A B u s f).
Proof. exact (MK_COMB (@lem5043523 A B u f s) (@lem5043506 A B u s f)). Qed.
Lemma lem5043525 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term111 A B s f) = (term111 A B s f).
Proof. exact (fun_ext (fun u : B -> Prop => @lem5043524 A B u s f)). Qed.
Lemma lem5043526 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5043527 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term113 A B s f) = (term113 A B s f).
Proof. exact (MK_COMB (@lem5043526 B) (@lem5043525 A B s f)). Qed.
Lemma lem5043528 {A B : Type'} (f : A -> B) : (term115 A B f) = (term115 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5043527 A B s f)). Qed.
Lemma lem5043529 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5043530 {A B : Type'} (f : A -> B) : (term117 A B f) = (term117 A B f).
Proof. exact (MK_COMB (@lem5043529 A) (@lem5043528 A B f)). Qed.
Lemma lem5043531 {A B : Type'} : (term119 A B) = (term119 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem5043530 A B f)). Qed.
Lemma lem5043532 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5043533 {A B : Type'} : (term121 A B) = (term121 A B).
Proof. exact (MK_COMB (@lem5043532 A B) (@lem5043531 A B)). Qed.
Lemma lem5043622 {A B : Type'} : (term120 A B) = (term121 A B).
Proof. exact (TRANS (@lem5043451 A B) (@lem5043533 A B)). Qed.
Lemma lem5043623 {A B : Type'} : (term121 A B) = (term120 A B).
Proof. exact (SYM (@lem5043622 A B)). Qed.
Lemma lem5043624 {A B : Type'} (u : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term52 A B u f s) : term52 A B u f s.
Proof. exact (h1). Qed.
Lemma lem5043625 {A B : Type'} (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (h1 : term89 A B u t s t' f) : term89 A B u t s t' f.
Proof. exact (h1). Qed.
Lemma lem5043627 (p : Prop) : p = (term102 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5043628 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x : B) : ((t x) = (t' x)) = (term122 B t t' x).
Proof. exact (@lem5043627 ((t x) = (t' x))). Qed.
Lemma lem5043629 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x : B) : (term122 B t t' x) = ((t x) = (t' x)).
Proof. exact (SYM (@lem5043628 B t t' x)). Qed.
Lemma lem5043630 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term123 B t t' x) : term123 B t t' x.
Proof. exact (h1). Qed.
Lemma lem5043636 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term44 A B x f s x') = (term44 A B x f s x').
Proof. exact (eq_refl (term44 A B x f s x')). Qed.
Lemma lem5043637 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term46 A B x f s) = (term46 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem5043636 A B x f s x')). Qed.
Lemma lem5043638 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5043639 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term47 A B x f s) = (term47 A B x f s).
Proof. exact (MK_COMB (@lem5043638 A) (@lem5043637 A B x f s)). Qed.
Lemma lem5043641 {B : Type'} (u : B -> Prop) (x : B) : (term124 B u x) = (term124 B u x).
Proof. exact (eq_refl (term124 B u x)). Qed.
Lemma lem5043642 {A B : Type'} (u : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term125 A B u x f s) = (term125 A B u x f s).
Proof. exact (MK_COMB (@lem5043641 B u x) (@lem5043639 A B x f s)). Qed.
Lemma lem5043643 {A B : Type'} (u : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term49 A B u x f s) = (term125 A B u x f s).
Proof. exact (@lem17265 (u x) (term47 A B x f s)). Qed.
Lemma lem5043644 {A B : Type'} (u : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term49 A B u x f s) = (term125 A B u x f s).
Proof. exact (TRANS (@lem5043643 A B u x f s) (@lem5043642 A B u x f s)). Qed.
Lemma lem5043645 {A B : Type'} (u : B -> Prop) (f : A -> B) (s : A -> Prop) : (term51 A B u f s) = (term126 A B u f s).
Proof. exact (fun_ext (fun x : B => @lem5043644 A B u x f s)). Qed.
Lemma lem5043646 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5043647 {A B : Type'} (u : B -> Prop) (f : A -> B) (s : A -> Prop) : (term52 A B u f s) = (term127 A B u f s).
Proof. exact (MK_COMB (@lem5043646 B) (@lem5043645 A B u f s)). Qed.
Lemma lem5043730 {A : Type'} (P : Prop) (Q : A -> Prop) : (term128 A P Q) = (term129 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5043731 {A : Type'} (P : Prop) (Q : A -> Prop) : (term128 A P Q) = (term129 A P Q).
Proof. exact (@lem5043730 A P Q). Qed.
Lemma lem5043732 {A B : Type'} (u : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term130 A B u x f s) = (term131 A B u x f s).
Proof. exact (@lem5043731 A (term132 B u x) (term46 A B x f s)). Qed.
Lemma lem5043733 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term133 A B x f s x') = (term44 A B x f s x').
Proof. exact (eq_refl (term133 A B x f s x')). Qed.
Lemma lem5043734 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term134 A B x f s) = (term46 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem5043733 A B x f s x')). Qed.
Lemma lem5043735 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5043736 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term135 A B x f s) = (term47 A B x f s).
Proof. exact (MK_COMB (@lem5043735 A) (@lem5043734 A B x f s)). Qed.
Lemma lem5043737 {B : Type'} (u : B -> Prop) (x : B) : (term124 B u x) = (term124 B u x).
Proof. exact (eq_refl (term124 B u x)). Qed.
Lemma lem5043738 {A B : Type'} (u : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term130 A B u x f s) = (term125 A B u x f s).
Proof. exact (MK_COMB (@lem5043737 B u x) (@lem5043736 A B x f s)). Qed.
Lemma lem5043739 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5043740 {A B : Type'} (u : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term136 A B u x f s) = (term137 A B u x f s).
Proof. exact (MK_COMB (@lem5043739) (@lem5043738 A B u x f s)). Qed.
Lemma lem5043741 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term133 A B x f s x') = (term44 A B x f s x').
Proof. exact (eq_refl (term133 A B x f s x')). Qed.
Lemma lem5043742 {B : Type'} (u : B -> Prop) (x : B) : (term124 B u x) = (term124 B u x).
Proof. exact (eq_refl (term124 B u x)). Qed.
Lemma lem5043743 {A B : Type'} (u : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term138 A B u x f s x') = (term139 A B u x f s x').
Proof. exact (MK_COMB (@lem5043742 B u x) (@lem5043741 A B x f s x')). Qed.
Lemma lem5043744 {A B : Type'} (u : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term140 A B u x f s) = (term141 A B u x f s).
Proof. exact (fun_ext (fun x' : A => @lem5043743 A B u x f s x')). Qed.
Lemma lem5043745 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5043746 {A B : Type'} (u : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term131 A B u x f s) = (term142 A B u x f s).
Proof. exact (MK_COMB (@lem5043745 A) (@lem5043744 A B u x f s)). Qed.
Lemma lem5043747 {A B : Type'} (u : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : ((term130 A B u x f s) = (term131 A B u x f s)) = ((term125 A B u x f s) = (term142 A B u x f s)).
Proof. exact (MK_COMB (@lem5043740 A B u x f s) (@lem5043746 A B u x f s)). Qed.
Lemma lem5043748 {A B : Type'} (u : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term125 A B u x f s) = (term142 A B u x f s).
Proof. exact (EQ_MP (@lem5043747 A B u x f s) (@lem5043732 A B u x f s)). Qed.
Lemma lem5043749 {A B : Type'} (u : B -> Prop) (f : A -> B) (s : A -> Prop) : (term126 A B u f s) = (term143 A B u f s).
Proof. exact (fun_ext (fun x : B => @lem5043748 A B u x f s)). Qed.
Lemma lem5043750 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5043751 {A B : Type'} (u : B -> Prop) (f : A -> B) (s : A -> Prop) : (term127 A B u f s) = (term144 A B u f s).
Proof. exact (MK_COMB (@lem5043750 B) (@lem5043749 A B u f s)). Qed.
Lemma lem5043753 {A B : Type'} (P : type1413 A B) : (term145 A B P) = (term146 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5043754 {A B : Type'} (P : type1470 A B) : (term147 A B P) = (term148 A B P).
Proof. exact (@lem5043753 B A P). Qed.
Lemma lem5043755 {A B : Type'} (u : B -> Prop) (f : A -> B) (s : A -> Prop) : (term149 A B u f s) = (term150 A B u f s).
Proof. exact (@lem5043754 A B (term151 A B u f s)). Qed.
Lemma lem5043756 {A B : Type'} (u : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term152 A B u f s x) = (term141 A B u x f s).
Proof. exact (eq_refl (term152 A B u f s x)). Qed.
Lemma lem5043757 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5043758 {A B : Type'} (u : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term153 A B u f s x x') = (term154 A B u x f s x').
Proof. exact (MK_COMB (@lem5043756 A B u x f s) (@lem5043757 A x')). Qed.
Lemma lem5043759 {A B : Type'} (u : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term154 A B u x f s x') = (term139 A B u x f s x').
Proof. exact (eq_refl (term154 A B u x f s x')). Qed.
Lemma lem5043760 {A B : Type'} (u : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term153 A B u f s x x') = (term139 A B u x f s x').
Proof. exact (TRANS (@lem5043758 A B u x f s x') (@lem5043759 A B u x f s x')). Qed.
Lemma lem5043761 {A B : Type'} (u : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term155 A B u f s x) = (term141 A B u x f s).
Proof. exact (fun_ext (fun x' : A => @lem5043760 A B u x f s x')). Qed.
Lemma lem5043762 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5043763 {A B : Type'} (u : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term156 A B u f s x) = (term142 A B u x f s).
Proof. exact (MK_COMB (@lem5043762 A) (@lem5043761 A B u x f s)). Qed.
Lemma lem5043764 {A B : Type'} (u : B -> Prop) (f : A -> B) (s : A -> Prop) : (term157 A B u f s) = (term143 A B u f s).
Proof. exact (fun_ext (fun x : B => @lem5043763 A B u x f s)). Qed.
Lemma lem5043765 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5043766 {A B : Type'} (u : B -> Prop) (f : A -> B) (s : A -> Prop) : (term149 A B u f s) = (term144 A B u f s).
Proof. exact (MK_COMB (@lem5043765 B) (@lem5043764 A B u f s)). Qed.
Lemma lem5043767 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5043768 {A B : Type'} (u : B -> Prop) (f : A -> B) (s : A -> Prop) : (term158 A B u f s) = (term159 A B u f s).
Proof. exact (MK_COMB (@lem5043767) (@lem5043766 A B u f s)). Qed.
Lemma lem5043769 {A B : Type'} (u : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term152 A B u f s x) = (term141 A B u x f s).
Proof. exact (eq_refl (term152 A B u f s x)). Qed.
Lemma lem5043770 {A B : Type'} (x : B -> A) (x' : B) : (x x') = (x x').
Proof. exact (eq_refl (x x')). Qed.
Lemma lem5043771 {A B : Type'} (u : B -> Prop) (f : A -> B) (s : A -> Prop) (x : B -> A) (x' : B) : (term160 A B u f s x x') = (term161 A B u f s x x').
Proof. exact (MK_COMB (@lem5043769 A B u x' f s) (@lem5043770 A B x x')). Qed.
Lemma lem5043772 {A B : Type'} (u : B -> Prop) (f : A -> B) (s : A -> Prop) (x : B -> A) (x' : B) : (term161 A B u f s x x') = (term162 A B u f s x x').
Proof. exact (eq_refl (term161 A B u f s x x')). Qed.
Lemma lem5043773 {A B : Type'} (u : B -> Prop) (f : A -> B) (s : A -> Prop) (x : B -> A) (x' : B) : (term160 A B u f s x x') = (term162 A B u f s x x').
Proof. exact (TRANS (@lem5043771 A B u f s x x') (@lem5043772 A B u f s x x')). Qed.
Lemma lem5043774 {A B : Type'} (u : B -> Prop) (f : A -> B) (s : A -> Prop) (x : B -> A) : (term163 A B u f s x) = (term164 A B u f s x).
Proof. exact (fun_ext (fun x' : B => @lem5043773 A B u f s x x')). Qed.
Lemma lem5043775 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5043776 {A B : Type'} (u : B -> Prop) (f : A -> B) (s : A -> Prop) (x : B -> A) : (term165 A B u f s x) = (term166 A B u f s x).
Proof. exact (MK_COMB (@lem5043775 B) (@lem5043774 A B u f s x)). Qed.
Lemma lem5043777 {A B : Type'} (u : B -> Prop) (f : A -> B) (s : A -> Prop) : (term167 A B u f s) = (term168 A B u f s).
Proof. exact (fun_ext (fun x : B -> A => @lem5043776 A B u f s x)). Qed.
Lemma lem5043778 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem5043779 {A B : Type'} (u : B -> Prop) (f : A -> B) (s : A -> Prop) : (term150 A B u f s) = (term169 A B u f s).
Proof. exact (MK_COMB (@lem5043778 A B) (@lem5043777 A B u f s)). Qed.
Lemma lem5043780 {A B : Type'} (u : B -> Prop) (f : A -> B) (s : A -> Prop) : ((term149 A B u f s) = (term150 A B u f s)) = ((term144 A B u f s) = (term169 A B u f s)).
Proof. exact (MK_COMB (@lem5043768 A B u f s) (@lem5043779 A B u f s)). Qed.
Lemma lem5043781 {A B : Type'} (u : B -> Prop) (f : A -> B) (s : A -> Prop) : (term144 A B u f s) = (term169 A B u f s).
Proof. exact (EQ_MP (@lem5043780 A B u f s) (@lem5043755 A B u f s)). Qed.
Lemma lem5043783 {A B : Type'} (u : B -> Prop) (f : A -> B) (s : A -> Prop) : (term127 A B u f s) = (term169 A B u f s).
Proof. exact (TRANS (@lem5043751 A B u f s) (@lem5043781 A B u f s)). Qed.
Lemma lem5043784 {A B : Type'} (u : B -> Prop) (f : A -> B) (s : A -> Prop) : (term52 A B u f s) = (term169 A B u f s).
Proof. exact (TRANS (@lem5043647 A B u f s) (@lem5043783 A B u f s)). Qed.
Lemma lem5043785 {A B : Type'} (u : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term52 A B u f s) : term169 A B u f s.
Proof. exact (EQ_MP (@lem5043784 A B u f s) (@lem5043624 A B u f s h1)). Qed.
Lemma lem5043792 {B : Type'} (t : B -> Prop) (u : B -> Prop) (x : B) : (term55 B t u x) = (term170 B t u x).
Proof. exact (@lem17265 (t x) (u x)). Qed.
Lemma lem5043793 {B : Type'} (t : B -> Prop) (u : B -> Prop) : (term57 B t u) = (term171 B t u).
Proof. exact (fun_ext (fun x : B => @lem5043792 B t u x)). Qed.
Lemma lem5043794 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5043795 {B : Type'} (t : B -> Prop) (u : B -> Prop) : (term58 B t u) = (term172 B t u).
Proof. exact (MK_COMB (@lem5043794 B) (@lem5043793 B t u)). Qed.
Lemma lem5043802 {B : Type'} (t' : B -> Prop) (u : B -> Prop) (x : B) : (term55 B t' u x) = (term170 B t' u x).
Proof. exact (@lem17265 (t' x) (u x)). Qed.
Lemma lem5043803 {B : Type'} (t' : B -> Prop) (u : B -> Prop) : (term57 B t' u) = (term171 B t' u).
Proof. exact (fun_ext (fun x : B => @lem5043802 B t' u x)). Qed.
Lemma lem5043804 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5043805 {B : Type'} (t' : B -> Prop) (u : B -> Prop) : (term58 B t' u) = (term172 B t' u).
Proof. exact (MK_COMB (@lem5043804 B) (@lem5043803 B t' u)). Qed.
Lemma lem5043814 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term173 A B s t f x) = (term174 A B s t f x).
Proof. exact (@lem17045 (s x) (term82 A B t f x)). Qed.
Lemma lem5043826 {A B : Type'} (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (x : A) : (term173 A B s t' f x) = (term174 A B s t' f x).
Proof. exact (@lem17045 (s x) (term82 A B t' f x)). Qed.
Lemma lem5043829 {A B : Type'} (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (x : A) : (term83 A B s t' f x) = (term83 A B s t' f x).
Proof. exact (eq_refl (term83 A B s t' f x)). Qed.
Lemma lem5043830 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5043831 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term175 A B s t f x) = (term176 A B s t f x).
Proof. exact (MK_COMB (@lem5043830) (@lem5043814 A B s t f x)). Qed.
Lemma lem5043832 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (x : A) : (term177 A B t s t' f x) = (term178 A B t s t' f x).
Proof. exact (MK_COMB (@lem5043831 A B s t f x) (@lem5043829 A B s t' f x)). Qed.
Lemma lem5043834 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term179 A B s t f x) = (term179 A B s t f x).
Proof. exact (eq_refl (term179 A B s t f x)). Qed.
Lemma lem5043835 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (x : A) : (term180 A B t s t' f x) = (term181 A B t s t' f x).
Proof. exact (MK_COMB (@lem5043834 A B s t f x) (@lem5043826 A B s t' f x)). Qed.
Lemma lem5043836 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5043837 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (x : A) : (term182 A B t s t' f x) = (term183 A B t s t' f x).
Proof. exact (MK_COMB (@lem5043836) (@lem5043835 A B t s t' f x)). Qed.
Lemma lem5043838 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (x : A) : (term184 A B t s t' f x) = (term185 A B t s t' f x).
Proof. exact (MK_COMB (@lem5043837 A B t s t' f x) (@lem5043832 A B t s t' f x)). Qed.
Lemma lem5043839 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (x : A) : ((term83 A B s t f x) = (term83 A B s t' f x)) = (term184 A B t s t' f x).
Proof. exact (@lem17784 (term83 A B s t f x) (term83 A B s t' f x)). Qed.
Lemma lem5043840 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (x : A) : ((term83 A B s t f x) = (term83 A B s t' f x)) = (term185 A B t s t' f x).
Proof. exact (TRANS (@lem5043839 A B t s t' f x) (@lem5043838 A B t s t' f x)). Qed.
Lemma lem5043841 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) : (term86 A B t s t' f) = (term186 A B t s t' f).
Proof. exact (fun_ext (fun x : A => @lem5043840 A B t s t' f x)). Qed.
Lemma lem5043842 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5043843 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) : (term87 A B t s t' f) = (term187 A B t s t' f).
Proof. exact (MK_COMB (@lem5043842 A) (@lem5043841 A B t s t' f)). Qed.
Lemma lem5043844 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5043845 {B : Type'} (t' : B -> Prop) (u : B -> Prop) : (term59 B t' u) = (term188 B t' u).
Proof. exact (MK_COMB (@lem5043844) (@lem5043805 B t' u)). Qed.
Lemma lem5043846 {A B : Type'} (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) : (term88 A B u t s t' f) = (term189 A B u t s t' f).
Proof. exact (MK_COMB (@lem5043845 B t' u) (@lem5043843 A B t s t' f)). Qed.
Lemma lem5043847 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5043848 {B : Type'} (t : B -> Prop) (u : B -> Prop) : (term59 B t u) = (term188 B t u).
Proof. exact (MK_COMB (@lem5043847) (@lem5043795 B t u)). Qed.
Lemma lem5043849 {A B : Type'} (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) : (term89 A B u t s t' f) = (term190 A B u t s t' f).
Proof. exact (MK_COMB (@lem5043848 B t u) (@lem5043846 A B u t s t' f)). Qed.
Lemma lem5043915 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term191 A P Q) = (term192 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5043916 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term191 A P Q) = (term192 A P Q).
Proof. exact (@lem5043915 A P Q). Qed.
Lemma lem5043917 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) : (term193 A B t s t' f) = (term194 A B t s t' f).
Proof. exact (@lem5043916 A (term195 A B t s t' f) (term196 A B t s t' f)). Qed.
Lemma lem5043918 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (x : A) : (term197 A B t s t' f x) = (term181 A B t s t' f x).
Proof. exact (eq_refl (term197 A B t s t' f x)). Qed.
Lemma lem5043919 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5043920 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (x : A) : (term198 A B t s t' f x) = (term183 A B t s t' f x).
Proof. exact (MK_COMB (@lem5043919) (@lem5043918 A B t s t' f x)). Qed.
Lemma lem5043921 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (x : A) : (term199 A B t s t' f x) = (term178 A B t s t' f x).
Proof. exact (eq_refl (term199 A B t s t' f x)). Qed.
Lemma lem5043922 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (x : A) : (term200 A B t s t' f x) = (term185 A B t s t' f x).
Proof. exact (MK_COMB (@lem5043920 A B t s t' f x) (@lem5043921 A B t s t' f x)). Qed.
Lemma lem5043923 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) : (term201 A B t s t' f) = (term186 A B t s t' f).
Proof. exact (fun_ext (fun x : A => @lem5043922 A B t s t' f x)). Qed.
Lemma lem5043924 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5043925 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) : (term193 A B t s t' f) = (term187 A B t s t' f).
Proof. exact (MK_COMB (@lem5043924 A) (@lem5043923 A B t s t' f)). Qed.
Lemma lem5043926 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5043927 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) : (term202 A B t s t' f) = (term203 A B t s t' f).
Proof. exact (MK_COMB (@lem5043926) (@lem5043925 A B t s t' f)). Qed.
Lemma lem5043928 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (x : A) : (term197 A B t s t' f x) = (term181 A B t s t' f x).
Proof. exact (eq_refl (term197 A B t s t' f x)). Qed.
Lemma lem5043929 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) : (term204 A B t s t' f) = (term195 A B t s t' f).
Proof. exact (fun_ext (fun x : A => @lem5043928 A B t s t' f x)). Qed.
Lemma lem5043930 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5043931 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) : (term205 A B t s t' f) = (term206 A B t s t' f).
Proof. exact (MK_COMB (@lem5043930 A) (@lem5043929 A B t s t' f)). Qed.
Lemma lem5043932 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5043933 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) : (term207 A B t s t' f) = (term208 A B t s t' f).
Proof. exact (MK_COMB (@lem5043932) (@lem5043931 A B t s t' f)). Qed.
Lemma lem5043934 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (x : A) : (term199 A B t s t' f x) = (term178 A B t s t' f x).
Proof. exact (eq_refl (term199 A B t s t' f x)). Qed.
Lemma lem5043935 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) : (term209 A B t s t' f) = (term196 A B t s t' f).
Proof. exact (fun_ext (fun x : A => @lem5043934 A B t s t' f x)). Qed.
Lemma lem5043936 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5043937 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) : (term210 A B t s t' f) = (term211 A B t s t' f).
Proof. exact (MK_COMB (@lem5043936 A) (@lem5043935 A B t s t' f)). Qed.
Lemma lem5043938 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) : (term194 A B t s t' f) = (term212 A B t s t' f).
Proof. exact (MK_COMB (@lem5043933 A B t s t' f) (@lem5043937 A B t s t' f)). Qed.
Lemma lem5043939 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) : ((term193 A B t s t' f) = (term194 A B t s t' f)) = ((term187 A B t s t' f) = (term212 A B t s t' f)).
Proof. exact (MK_COMB (@lem5043927 A B t s t' f) (@lem5043938 A B t s t' f)). Qed.
Lemma lem5043940 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) : (term187 A B t s t' f) = (term212 A B t s t' f).
Proof. exact (EQ_MP (@lem5043939 A B t s t' f) (@lem5043917 A B t s t' f)). Qed.
Lemma lem5044037 {B : Type'} (t' : B -> Prop) (u : B -> Prop) : (term188 B t' u) = (term188 B t' u).
Proof. exact (eq_refl (term188 B t' u)). Qed.
Lemma lem5044038 {A B : Type'} (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) : (term189 A B u t s t' f) = (term213 A B u t s t' f).
Proof. exact (MK_COMB (@lem5044037 B t' u) (@lem5043940 A B t s t' f)). Qed.
Lemma lem5044039 {B : Type'} (t : B -> Prop) (u : B -> Prop) : (term188 B t u) = (term188 B t u).
Proof. exact (eq_refl (term188 B t u)). Qed.
Lemma lem5044042 {A B : Type'} (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) : (term190 A B u t s t' f) = (term214 A B u t s t' f).
Proof. exact (MK_COMB (@lem5044039 B t u) (@lem5044038 A B u t s t' f)). Qed.
Lemma lem5044043 {A B : Type'} (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) : (term89 A B u t s t' f) = (term214 A B u t s t' f).
Proof. exact (TRANS (@lem5043849 A B u t s t' f) (@lem5044042 A B u t s t' f)). Qed.
Lemma lem5044044 {A B : Type'} (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (h1 : term89 A B u t s t' f) : term214 A B u t s t' f.
Proof. exact (EQ_MP (@lem5044043 A B u t s t' f) (@lem5043625 A B u t s t' f h1)). Qed.
Lemma lem5044063 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x : B) : (term123 B t t' x) = (term215 B t t' x).
Proof. exact (@lem17646 (t x) (t' x)). Qed.
Lemma lem5044065 {A B : Type'} (u : B -> Prop) (f : A -> B) (s : A -> Prop) (x' : B -> A) (h1 : term166 A B u f s x') : term166 A B u f s x'.
Proof. exact (h1). Qed.
Lemma lem5044094 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (x : A) : (term178 A B t s t' f x) = (term178 A B t s t' f x).
Proof. exact (eq_refl (term178 A B t s t' f x)). Qed.
Lemma lem5044095 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) : (term196 A B t s t' f) = (term196 A B t s t' f).
Proof. exact (fun_ext (fun x : A => @lem5044094 A B t s t' f x)). Qed.
Lemma lem5044096 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5044097 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) : (term211 A B t s t' f) = (term211 A B t s t' f).
Proof. exact (MK_COMB (@lem5044096 A) (@lem5044095 A B t s t' f)). Qed.
Lemma lem5044126 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (x : A) : (term181 A B t s t' f x) = (term181 A B t s t' f x).
Proof. exact (eq_refl (term181 A B t s t' f x)). Qed.
Lemma lem5044127 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) : (term195 A B t s t' f) = (term195 A B t s t' f).
Proof. exact (fun_ext (fun x : A => @lem5044126 A B t s t' f x)). Qed.
Lemma lem5044128 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5044129 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) : (term206 A B t s t' f) = (term206 A B t s t' f).
Proof. exact (MK_COMB (@lem5044128 A) (@lem5044127 A B t s t' f)). Qed.
Lemma lem5044130 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5044131 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) : (term208 A B t s t' f) = (term208 A B t s t' f).
Proof. exact (MK_COMB (@lem5044130) (@lem5044129 A B t s t' f)). Qed.
Lemma lem5044132 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) : (term212 A B t s t' f) = (term212 A B t s t' f).
Proof. exact (MK_COMB (@lem5044131 A B t s t' f) (@lem5044097 A B t s t' f)). Qed.
Lemma lem5044143 {B : Type'} (t' : B -> Prop) (u : B -> Prop) (x : B) : (term170 B t' u x) = (term170 B t' u x).
Proof. exact (eq_refl (term170 B t' u x)). Qed.
Lemma lem5044144 {B : Type'} (t' : B -> Prop) (u : B -> Prop) : (term171 B t' u) = (term171 B t' u).
Proof. exact (fun_ext (fun x : B => @lem5044143 B t' u x)). Qed.
Lemma lem5044145 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5044146 {B : Type'} (t' : B -> Prop) (u : B -> Prop) : (term172 B t' u) = (term172 B t' u).
Proof. exact (MK_COMB (@lem5044145 B) (@lem5044144 B t' u)). Qed.
Lemma lem5044147 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5044148 {B : Type'} (t' : B -> Prop) (u : B -> Prop) : (term188 B t' u) = (term188 B t' u).
Proof. exact (MK_COMB (@lem5044147) (@lem5044146 B t' u)). Qed.
Lemma lem5044149 {A B : Type'} (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) : (term213 A B u t s t' f) = (term213 A B u t s t' f).
Proof. exact (MK_COMB (@lem5044148 B t' u) (@lem5044132 A B t s t' f)). Qed.
Lemma lem5044160 {B : Type'} (t : B -> Prop) (u : B -> Prop) (x : B) : (term170 B t u x) = (term170 B t u x).
Proof. exact (eq_refl (term170 B t u x)). Qed.
Lemma lem5044161 {B : Type'} (t : B -> Prop) (u : B -> Prop) : (term171 B t u) = (term171 B t u).
Proof. exact (fun_ext (fun x : B => @lem5044160 B t u x)). Qed.
Lemma lem5044162 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5044163 {B : Type'} (t : B -> Prop) (u : B -> Prop) : (term172 B t u) = (term172 B t u).
Proof. exact (MK_COMB (@lem5044162 B) (@lem5044161 B t u)). Qed.
Lemma lem5044164 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5044165 {B : Type'} (t : B -> Prop) (u : B -> Prop) : (term188 B t u) = (term188 B t u).
Proof. exact (MK_COMB (@lem5044164) (@lem5044163 B t u)). Qed.
Lemma lem5044166 {A B : Type'} (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) : (term214 A B u t s t' f) = (term214 A B u t s t' f).
Proof. exact (MK_COMB (@lem5044165 B t u) (@lem5044149 A B u t s t' f)). Qed.
Lemma lem5044167 {A B : Type'} (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (h1 : term89 A B u t s t' f) : term214 A B u t s t' f.
Proof. exact (EQ_MP (@lem5044166 A B u t s t' f) (@lem5044044 A B u t s t' f h1)). Qed.
Lemma lem5044193 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term123 B t t' x) : term215 B t t' x.
Proof. exact (EQ_MP (@lem5044063 B t t' x) (@lem5043630 B t t' x h1)). Qed.
Lemma lem5044218 {A B : Type'} (u : B -> Prop) (f : A -> B) (s : A -> Prop) (x' : B -> A) (x : B) : (term162 A B u f s x' x) = (term162 A B u f s x' x).
Proof. exact (eq_refl (term162 A B u f s x' x)). Qed.
Lemma lem5044219 {A B : Type'} (u : B -> Prop) (f : A -> B) (s : A -> Prop) (x' : B -> A) : (term164 A B u f s x') = (term164 A B u f s x').
Proof. exact (fun_ext (fun x : B => @lem5044218 A B u f s x' x)). Qed.
Lemma lem5044220 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5044221 {A B : Type'} (u : B -> Prop) (f : A -> B) (s : A -> Prop) (x' : B -> A) : (term166 A B u f s x') = (term166 A B u f s x').
Proof. exact (MK_COMB (@lem5044220 B) (@lem5044219 A B u f s x')). Qed.
Lemma lem5044222 {A B : Type'} (u : B -> Prop) (f : A -> B) (s : A -> Prop) (x' : B -> A) (h1 : term166 A B u f s x') : term166 A B u f s x'.
Proof. exact (EQ_MP (@lem5044221 A B u f s x') (@lem5044065 A B u f s x' h1)). Qed.
Lemma lem5044223 {A B : Type'} (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (h1 : term89 A B u t s t' f) : term213 A B u t s t' f.
Proof. exact (proj2 (@lem5044167 A B u t s t' f h1)). Qed.
Lemma lem5044224 {A B : Type'} (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (h1 : term89 A B u t s t' f) : term172 B t u.
Proof. exact (proj1 (@lem5044167 A B u t s t' f h1)). Qed.
Lemma lem5044225 {A B : Type'} (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (h1 : term89 A B u t s t' f) : term212 A B t s t' f.
Proof. exact (proj2 (@lem5044223 A B u t s t' f h1)). Qed.
Lemma lem5044226 {A B : Type'} (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (h1 : term89 A B u t s t' f) : term172 B t' u.
Proof. exact (proj1 (@lem5044223 A B u t s t' f h1)). Qed.
Lemma lem5044227 {A B : Type'} (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (h1 : term89 A B u t s t' f) : term211 A B t s t' f.
Proof. exact (proj2 (@lem5044225 A B u t s t' f h1)). Qed.
Lemma lem5044228 {A B : Type'} (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (h1 : term89 A B u t s t' f) : term206 A B t s t' f.
Proof. exact (proj1 (@lem5044225 A B u t s t' f h1)). Qed.
Lemma lem5044229 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term216 B t t' x) : term216 B t t' x.
Proof. exact (h1). Qed.
Lemma lem5044230 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term217 B t t' x) : term217 B t t' x.
Proof. exact (h1). Qed.
Lemma lem5044252 {A B : Type'} (f : A -> B) (u : B -> Prop) (s : A -> Prop) (x' : B -> A) (x : B) : (term162 A B u f s x' x) = (term218 A B f u s x' x).
Proof. exact (@lem19490 (x = (term219 A B f x' x)) (term132 B u x) (term220 A B s x' x)). Qed.
Lemma lem5044253 {A B : Type'} (f : A -> B) (u : B -> Prop) (s : A -> Prop) (x' : B -> A) : (term164 A B u f s x') = (term221 A B f u s x').
Proof. exact (fun_ext (fun x : B => @lem5044252 A B f u s x' x)). Qed.
Lemma lem5044254 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5044256 {A B : Type'} (f : A -> B) (u : B -> Prop) (s : A -> Prop) (x' : B -> A) : (term166 A B u f s x') = (term222 A B f u s x').
Proof. exact (MK_COMB (@lem5044254 B) (@lem5044253 A B f u s x')). Qed.
Lemma lem5044257 {A B : Type'} (u : B -> Prop) (f : A -> B) (s : A -> Prop) (x' : B -> A) (h1 : term166 A B u f s x') : term222 A B f u s x'.
Proof. exact (EQ_MP (@lem5044256 A B f u s x') (@lem5044222 A B u f s x' h1)). Qed.
Lemma lem5044265 {B : Type'} (t : B -> Prop) (u : B -> Prop) (x : B) : (term170 B t u x) = (term170 B t u x).
Proof. exact (eq_refl (term170 B t u x)). Qed.
Lemma lem5044266 {B : Type'} (t : B -> Prop) (u : B -> Prop) : (term171 B t u) = (term171 B t u).
Proof. exact (fun_ext (fun x : B => @lem5044265 B t u x)). Qed.
Lemma lem5044267 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5044269 {B : Type'} (t : B -> Prop) (u : B -> Prop) : (term172 B t u) = (term172 B t u).
Proof. exact (MK_COMB (@lem5044267 B) (@lem5044266 B t u)). Qed.
Lemma lem5044270 {A B : Type'} (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (h1 : term89 A B u t s t' f) : term172 B t u.
Proof. exact (EQ_MP (@lem5044269 B t u) (@lem5044224 A B u t s t' f h1)). Qed.
Lemma lem5044336 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (f : A -> B) (x : A) : (term178 A B t s t' f x) = (term223 A B s t t' f x).
Proof. exact (@lem19490 (s x) (term174 A B s t f x) (term82 A B t' f x)). Qed.
Lemma lem5044337 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (f : A -> B) : (term196 A B t s t' f) = (term224 A B s t t' f).
Proof. exact (fun_ext (fun x : A => @lem5044336 A B s t t' f x)). Qed.
Lemma lem5044338 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5044340 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (f : A -> B) : (term211 A B t s t' f) = (term225 A B s t t' f).
Proof. exact (MK_COMB (@lem5044338 A) (@lem5044337 A B s t t' f)). Qed.
Lemma lem5044341 {A B : Type'} (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (h1 : term89 A B u t s t' f) : term225 A B s t t' f.
Proof. exact (EQ_MP (@lem5044340 A B s t t' f) (@lem5044227 A B u t s t' f h1)). Qed.
Lemma lem5044367 {A B : Type'} (f : A -> B) (u : B -> Prop) (s : A -> Prop) (x' : B -> A) (x : B) : (term162 A B u f s x' x) = (term218 A B f u s x' x).
Proof. exact (@lem19490 (x = (term219 A B f x' x)) (term132 B u x) (term220 A B s x' x)). Qed.
Lemma lem5044368 {A B : Type'} (f : A -> B) (u : B -> Prop) (s : A -> Prop) (x' : B -> A) : (term164 A B u f s x') = (term221 A B f u s x').
Proof. exact (fun_ext (fun x : B => @lem5044367 A B f u s x' x)). Qed.
Lemma lem5044369 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5044371 {A B : Type'} (f : A -> B) (u : B -> Prop) (s : A -> Prop) (x' : B -> A) : (term166 A B u f s x') = (term222 A B f u s x').
Proof. exact (MK_COMB (@lem5044369 B) (@lem5044368 A B f u s x')). Qed.
Lemma lem5044372 {A B : Type'} (u : B -> Prop) (f : A -> B) (s : A -> Prop) (x' : B -> A) (h1 : term166 A B u f s x') : term222 A B f u s x'.
Proof. exact (EQ_MP (@lem5044371 A B f u s x') (@lem5044222 A B u f s x' h1)). Qed.
Lemma lem5044393 {B : Type'} (t' : B -> Prop) (u : B -> Prop) (x : B) : (term170 B t' u x) = (term170 B t' u x).
Proof. exact (eq_refl (term170 B t' u x)). Qed.
Lemma lem5044394 {B : Type'} (t' : B -> Prop) (u : B -> Prop) : (term171 B t' u) = (term171 B t' u).
Proof. exact (fun_ext (fun x : B => @lem5044393 B t' u x)). Qed.
Lemma lem5044395 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5044397 {B : Type'} (t' : B -> Prop) (u : B -> Prop) : (term172 B t' u) = (term172 B t' u).
Proof. exact (MK_COMB (@lem5044395 B) (@lem5044394 B t' u)). Qed.
Lemma lem5044398 {A B : Type'} (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (h1 : term89 A B u t s t' f) : term172 B t' u.
Proof. exact (EQ_MP (@lem5044397 B t' u) (@lem5044226 A B u t s t' f h1)). Qed.
Lemma lem5044422 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (x : A) : (term181 A B t s t' f x) = (term226 A B t s t' f x).
Proof. exact (@lem19699 (s x) (term82 A B t f x) (term174 A B s t' f x)). Qed.
Lemma lem5044423 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) : (term195 A B t s t' f) = (term227 A B t s t' f).
Proof. exact (fun_ext (fun x : A => @lem5044422 A B t s t' f x)). Qed.
Lemma lem5044424 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5044426 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) : (term206 A B t s t' f) = (term228 A B t s t' f).
Proof. exact (MK_COMB (@lem5044424 A) (@lem5044423 A B t s t' f)). Qed.
Lemma lem5044427 {A B : Type'} (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (h1 : term89 A B u t s t' f) : term228 A B t s t' f.
Proof. exact (EQ_MP (@lem5044426 A B t s t' f) (@lem5044228 A B u t s t' f h1)). Qed.
Lemma lem5044465 {A B : Type'} (_64815 : B) (u : B -> Prop) (f : A -> B) (s : A -> Prop) (x' : B -> A) (h1 : term166 A B u f s x') : term229 A B f u s x' _64815.
Proof. exact (@lem5044257 A B u f s x' h1 _64815). Qed.
Lemma lem5044466 {A B : Type'} (f : A -> B) (u : B -> Prop) (s : A -> Prop) (x' : B -> A) (_64815 : B) : (term229 A B f u s x' _64815) = (term218 A B f u s x' _64815).
Proof. exact (eq_refl (term229 A B f u s x' _64815)). Qed.
Lemma lem5044467 {A B : Type'} (_64815 : B) (u : B -> Prop) (f : A -> B) (s : A -> Prop) (x' : B -> A) (h1 : term166 A B u f s x') : term218 A B f u s x' _64815.
Proof. exact (EQ_MP (@lem5044466 A B f u s x' _64815) (@lem5044465 A B _64815 u f s x' h1)). Qed.
Lemma lem5044468 {A B : Type'} (_64816 : B) (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (h1 : term89 A B u t s t' f) : term230 B t u _64816.
Proof. exact (@lem5044270 A B u t s t' f h1 _64816). Qed.
Lemma lem5044469 {B : Type'} (t : B -> Prop) (u : B -> Prop) (_64816 : B) : (term230 B t u _64816) = (term170 B t u _64816).
Proof. exact (eq_refl (term230 B t u _64816)). Qed.
Lemma lem5044477 {A B : Type'} (_64819 : A) (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (h1 : term89 A B u t s t' f) : term231 A B s t t' f _64819.
Proof. exact (@lem5044341 A B u t s t' f h1 _64819). Qed.
Lemma lem5044478 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (f : A -> B) (_64819 : A) : (term231 A B s t t' f _64819) = (term223 A B s t t' f _64819).
Proof. exact (eq_refl (term231 A B s t t' f _64819)). Qed.
Lemma lem5044479 {A B : Type'} (_64819 : A) (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (h1 : term89 A B u t s t' f) : term223 A B s t t' f _64819.
Proof. exact (EQ_MP (@lem5044478 A B s t t' f _64819) (@lem5044477 A B _64819 u t s t' f h1)). Qed.
Lemma lem5044480 {A B : Type'} (_64820 : B) (u : B -> Prop) (f : A -> B) (s : A -> Prop) (x' : B -> A) (h1 : term166 A B u f s x') : term229 A B f u s x' _64820.
Proof. exact (@lem5044372 A B u f s x' h1 _64820). Qed.
Lemma lem5044481 {A B : Type'} (f : A -> B) (u : B -> Prop) (s : A -> Prop) (x' : B -> A) (_64820 : B) : (term229 A B f u s x' _64820) = (term218 A B f u s x' _64820).
Proof. exact (eq_refl (term229 A B f u s x' _64820)). Qed.
Lemma lem5044482 {A B : Type'} (_64820 : B) (u : B -> Prop) (f : A -> B) (s : A -> Prop) (x' : B -> A) (h1 : term166 A B u f s x') : term218 A B f u s x' _64820.
Proof. exact (EQ_MP (@lem5044481 A B f u s x' _64820) (@lem5044480 A B _64820 u f s x' h1)). Qed.
Lemma lem5044486 {A B : Type'} (_64822 : B) (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (h1 : term89 A B u t s t' f) : term230 B t' u _64822.
Proof. exact (@lem5044398 A B u t s t' f h1 _64822). Qed.
Lemma lem5044487 {B : Type'} (t' : B -> Prop) (u : B -> Prop) (_64822 : B) : (term230 B t' u _64822) = (term170 B t' u _64822).
Proof. exact (eq_refl (term230 B t' u _64822)). Qed.
Lemma lem5044489 {A B : Type'} (_64823 : A) (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (h1 : term89 A B u t s t' f) : term232 A B t s t' f _64823.
Proof. exact (@lem5044427 A B u t s t' f h1 _64823). Qed.
Lemma lem5044490 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (_64823 : A) : (term232 A B t s t' f _64823) = (term226 A B t s t' f _64823).
Proof. exact (eq_refl (term232 A B t s t' f _64823)). Qed.
Lemma lem5044491 {A B : Type'} (_64823 : A) (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (h1 : term89 A B u t s t' f) : term226 A B t s t' f _64823.
Proof. exact (EQ_MP (@lem5044490 A B t s t' f _64823) (@lem5044489 A B _64823 u t s t' f h1)). Qed.
Lemma lem5044495 {A B : Type'} (_64819 : A) (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (h1 : term89 A B u t s t' f) : term233 A B s t t' f _64819.
Proof. exact (proj2 (@lem5044479 A B _64819 u t s t' f h1)). Qed.
Lemma lem5044512 {A B : Type'} (_64816 : B) (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (h1 : term89 A B u t s t' f) : term170 B t u _64816.
Proof. exact (EQ_MP (@lem5044469 B t u _64816) (@lem5044468 A B _64816 u t s t' f h1)). Qed.
Lemma lem5044522 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term216 B t t' x) : term132 B t' x.
Proof. exact (proj2 (@lem5044229 B t t' x h1)). Qed.
Lemma lem5044545 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (f : A -> B) (_64819 : A) : (term233 A B s t t' f _64819) = (term234 A B s t t' f _64819).
Proof. exact (@lem5042912 (term132 A s _64819) (term235 A B t f _64819) (term82 A B t' f _64819)). Qed.
Lemma lem5044546 {A B : Type'} (_64819 : A) (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (h1 : term89 A B u t s t' f) : term234 A B s t t' f _64819.
Proof. exact (EQ_MP (@lem5044545 A B s t t' f _64819) (@lem5044495 A B _64819 u t s t' f h1)). Qed.
Lemma lem5044572 {A B : Type'} (_64815 : B) (u : B -> Prop) (f : A -> B) (s : A -> Prop) (x' : B -> A) (h1 : term166 A B u f s x') : term236 A B u f x' _64815.
Proof. exact (proj1 (@lem5044467 A B _64815 u f s x' h1)). Qed.
Lemma lem5044578 {A B : Type'} (_64815 : B) (u : B -> Prop) (f : A -> B) (s : A -> Prop) (x' : B -> A) (h1 : term166 A B u f s x') : term237 A B u s x' _64815.
Proof. exact (proj2 (@lem5044467 A B _64815 u f s x' h1)). Qed.
Lemma lem5044590 {A B : Type'} (_64822 : B) (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (h1 : term89 A B u t s t' f) : term170 B t' u _64822.
Proof. exact (EQ_MP (@lem5044487 B t' u _64822) (@lem5044486 A B _64822 u t s t' f h1)). Qed.
Lemma lem5044592 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term217 B t t' x) : term132 B t x.
Proof. exact (proj1 (@lem5044230 B t t' x h1)). Qed.
Lemma lem5044638 {A B : Type'} (_64823 : A) (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (h1 : term89 A B u t s t' f) : term238 A B t s t' f _64823.
Proof. exact (proj2 (@lem5044491 A B _64823 u t s t' f h1)). Qed.
Lemma lem5044644 {A B : Type'} (_64820 : B) (u : B -> Prop) (f : A -> B) (s : A -> Prop) (x' : B -> A) (h1 : term166 A B u f s x') : term236 A B u f x' _64820.
Proof. exact (proj1 (@lem5044482 A B _64820 u f s x' h1)). Qed.
Lemma lem5044650 {A B : Type'} (_64820 : B) (u : B -> Prop) (f : A -> B) (s : A -> Prop) (x' : B -> A) (h1 : term166 A B u f s x') : term237 A B u s x' _64820.
Proof. exact (proj2 (@lem5044482 A B _64820 u f s x' h1)). Qed.
Lemma lem5044663 {B : Type'} (t' : B -> Prop) : t' = t'.
Proof. exact (eq_refl t'). Qed.
Lemma lem5044664 {B : Type'} (_64827 : B) (_64828 : B) (h1 : _64827 = _64828) : _64827 = _64828.
Proof. exact (h1). Qed.
Lemma lem5044665 {B : Type'} (t' : B -> Prop) (_64827 : B) (_64828 : B) (h1 : _64827 = _64828) : (t' _64827) = (t' _64828).
Proof. exact (MK_COMB (@lem5044663 B t') (@lem5044664 B _64827 _64828 h1)). Qed.
Lemma lem5044667 (b : Prop) (a : Prop) : term239 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem5044668 {B : Type'} (_64828 : B) (t' : B -> Prop) (_64827 : B) : term240 B _64828 t' _64827.
Proof. exact (@lem5044667 (t' _64828) (t' _64827)). Qed.
Lemma lem5044669 {B : Type'} (t' : B -> Prop) (_64827 : B) (_64828 : B) (h1 : _64827 = _64828) : term241 B _64828 t' _64827.
Proof. exact (@lem5044668 B _64828 t' _64827 (@lem5044665 B t' _64827 _64828 h1)). Qed.
Lemma lem5044670 {B : Type'} (_64828 : B) (t' : B -> Prop) (_64827 : B) : term242 B _64828 t' _64827.
Proof. exact (fun h0 : _64827 = _64828 => @lem5044669 B t' _64827 _64828 h0). Qed.
Lemma lem5044672 (a : Prop) (b : Prop) : (a -> b) = (term243 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem5044673 {B : Type'} (_64828 : B) (t' : B -> Prop) (_64827 : B) : (term242 B _64828 t' _64827) = (term244 B _64828 t' _64827).
Proof. exact (@lem5044672 (_64827 = _64828) (term241 B _64828 t' _64827)). Qed.
Lemma lem5044674 {B : Type'} (_64828 : B) (t' : B -> Prop) (_64827 : B) : term244 B _64828 t' _64827.
Proof. exact (EQ_MP (@lem5044673 B _64828 t' _64827) (@lem5044670 B _64828 t' _64827)). Qed.
Lemma lem5044675 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5044676 {B : Type'} (_64829 : B) (_64830 : B) (h1 : _64829 = _64830) : _64829 = _64830.
Proof. exact (h1). Qed.
Lemma lem5044677 {B : Type'} (t : B -> Prop) (_64829 : B) (_64830 : B) (h1 : _64829 = _64830) : (t _64829) = (t _64830).
Proof. exact (MK_COMB (@lem5044675 B t) (@lem5044676 B _64829 _64830 h1)). Qed.
Lemma lem5044679 (b : Prop) (a : Prop) : term239 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem5044680 {B : Type'} (_64830 : B) (t : B -> Prop) (_64829 : B) : term240 B _64830 t _64829.
Proof. exact (@lem5044679 (t _64830) (t _64829)). Qed.
Lemma lem5044681 {B : Type'} (t : B -> Prop) (_64829 : B) (_64830 : B) (h1 : _64829 = _64830) : term241 B _64830 t _64829.
Proof. exact (@lem5044680 B _64830 t _64829 (@lem5044677 B t _64829 _64830 h1)). Qed.
Lemma lem5044682 {B : Type'} (_64830 : B) (t : B -> Prop) (_64829 : B) : term242 B _64830 t _64829.
Proof. exact (fun h0 : _64829 = _64830 => @lem5044681 B t _64829 _64830 h0). Qed.
Lemma lem5044684 (a : Prop) (b : Prop) : (a -> b) = (term243 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem5044685 {B : Type'} (_64830 : B) (t : B -> Prop) (_64829 : B) : (term242 B _64830 t _64829) = (term244 B _64830 t _64829).
Proof. exact (@lem5044684 (_64829 = _64830) (term241 B _64830 t _64829)). Qed.
Lemma lem5044686 {B : Type'} (_64830 : B) (t : B -> Prop) (_64829 : B) : term244 B _64830 t _64829.
Proof. exact (EQ_MP (@lem5044685 B _64830 t _64829) (@lem5044682 B _64830 t _64829)). Qed.
Lemma lem5044716 {B : Type'} (x : B) (y : B) (z : B) : term245 B x y z.
Proof. exact (@lem21385 B x y z). Qed.
Lemma lem5044720 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term216 B t t' x) : t x.
Proof. exact (proj1 (@lem5044229 B t t' x h1)). Qed.
Lemma lem5044721 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term216 B t t' x) : term246 B t x.
Proof. exact (fun h0 : term132 B t x => @lem5044720 B t t' x h1). Qed.
Lemma lem5044723 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5044724 {B : Type'} (t : B -> Prop) (x : B) : (term246 B t x) = (t x).
Proof. exact (@lem5044723 (t x)). Qed.
Lemma lem5044725 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term216 B t t' x) : t x.
Proof. exact (EQ_MP (@lem5044724 B t x) (@lem5044721 B t t' x h1)). Qed.
Lemma lem5044731 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5044732 {B : Type'} (u : B -> Prop) (t : B -> Prop) (_64816 : B) : (term170 B t u _64816) = (term248 B u t _64816).
Proof. exact (@lem5044731 (u _64816) (term132 B t _64816)). Qed.
Lemma lem5044738 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5044739 {B : Type'} (u : B -> Prop) (t : B -> Prop) (_64816 : B) : (term249 B t u _64816) = (term250 B u t _64816).
Proof. exact (MK_COMB (@lem5044738) (@lem5044732 B u t _64816)). Qed.
Lemma lem5044745 {B : Type'} (u : B -> Prop) (t : B -> Prop) (_64816 : B) : (term248 B u t _64816) = (term248 B u t _64816).
Proof. exact (eq_refl (term248 B u t _64816)). Qed.
Lemma lem5044746 {B : Type'} (u : B -> Prop) (t : B -> Prop) (_64816 : B) : ((term170 B t u _64816) = (term248 B u t _64816)) = ((term248 B u t _64816) = (term248 B u t _64816)).
Proof. exact (MK_COMB (@lem5044739 B u t _64816) (@lem5044745 B u t _64816)). Qed.
Lemma lem5044748 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5044749 (x : Prop) : (x = x) = True.
Proof. exact (@lem5044748 Prop x). Qed.
Lemma lem5044750 {B : Type'} (u : B -> Prop) (t : B -> Prop) (_64816 : B) : ((term248 B u t _64816) = (term248 B u t _64816)) = True.
Proof. exact (@lem5044749 (term248 B u t _64816)). Qed.
Lemma lem5044751 {B : Type'} (u : B -> Prop) (t : B -> Prop) (_64816 : B) : ((term170 B t u _64816) = (term248 B u t _64816)) = True.
Proof. exact (TRANS (@lem5044746 B u t _64816) (@lem5044750 B u t _64816)). Qed.
Lemma lem5044752 {B : Type'} (u : B -> Prop) (t : B -> Prop) (_64816 : B) : True = ((term170 B t u _64816) = (term248 B u t _64816)).
Proof. exact (SYM (@lem5044751 B u t _64816)). Qed.
Lemma lem5044753 {B : Type'} (u : B -> Prop) (t : B -> Prop) (_64816 : B) : (term170 B t u _64816) = (term248 B u t _64816).
Proof. exact (EQ_MP (@lem5044752 B u t _64816) (@lem0)). Qed.
Lemma lem5044754 {A B : Type'} (_64816 : B) (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (h1 : term89 A B u t s t' f) : term248 B u t _64816.
Proof. exact (EQ_MP (@lem5044753 B u t _64816) (@lem5044512 A B _64816 u t s t' f h1)). Qed.
Lemma lem5044756 (b : Prop) (a : Prop) : (a \/ b) = (term251 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5044757 {B : Type'} (t : B -> Prop) (u : B -> Prop) (_64816 : B) : (term248 B u t _64816) = (term252 B t u _64816).
Proof. exact (@lem5044756 (term132 B t _64816) (u _64816)). Qed.
Lemma lem5044759 (a : Prop) : (term109 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5044760 {B : Type'} (t : B -> Prop) (_64816 : B) : (term253 B t _64816) = (t _64816).
Proof. exact (@lem5044759 (t _64816)). Qed.
Lemma lem5044761 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5044762 {B : Type'} (t : B -> Prop) (_64816 : B) : (term254 B t _64816) = (term39 B t _64816).
Proof. exact (MK_COMB (@lem5044761) (@lem5044760 B t _64816)). Qed.
Lemma lem5044763 {B : Type'} (u : B -> Prop) (_64816 : B) : (u _64816) = (u _64816).
Proof. exact (eq_refl (u _64816)). Qed.
Lemma lem5044764 {B : Type'} (t : B -> Prop) (u : B -> Prop) (_64816 : B) : (term252 B t u _64816) = (term55 B t u _64816).
Proof. exact (MK_COMB (@lem5044762 B t _64816) (@lem5044763 B u _64816)). Qed.
Lemma lem5044765 {B : Type'} (t : B -> Prop) (u : B -> Prop) (_64816 : B) : (term248 B u t _64816) = (term55 B t u _64816).
Proof. exact (TRANS (@lem5044757 B t u _64816) (@lem5044764 B t u _64816)). Qed.
Lemma lem5044768 {A B : Type'} (_64816 : B) (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (h1 : term89 A B u t s t' f) : term55 B t u _64816.
Proof. exact (EQ_MP (@lem5044765 B t u _64816) (@lem5044754 A B _64816 u t s t' f h1)). Qed.
Lemma lem5044769 {A B : Type'} (_64816 : B) (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (h1 : term89 A B u t s t' f) : term55 B t u _64816.
Proof. exact (@lem5044768 A B _64816 u t s t' f h1). Qed.
Lemma lem5044770 {A B : Type'} (x : B) (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (h1 : term89 A B u t s t' f) : term55 B t u x.
Proof. exact (@lem5044769 A B x u t s t' f h1). Qed.
Lemma lem5044773 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term89 A B u t s t' f) (h2 : term216 B t t' x) : u x.
Proof. exact (@lem5044770 A B x u t s t' f h1 (@lem5044725 B t t' x h2)). Qed.
Lemma lem5044774 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term89 A B u t s t' f) (h2 : term216 B t t' x) : term246 B u x.
Proof. exact (fun h0 : term132 B u x => @lem5044773 A B u s f t t' x h1 h2). Qed.
Lemma lem5044776 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5044777 {B : Type'} (u : B -> Prop) (x : B) : (term246 B u x) = (u x).
Proof. exact (@lem5044776 (u x)). Qed.
Lemma lem5044778 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term89 A B u t s t' f) (h2 : term216 B t t' x) : u x.
Proof. exact (EQ_MP (@lem5044777 B u x) (@lem5044774 A B u s f t t' x h1 h2)). Qed.
Lemma lem5044784 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5044785 {A B : Type'} (f : A -> B) (x' : B -> A) (u : B -> Prop) (_64815 : B) : (term236 A B u f x' _64815) = (term255 A B f x' u _64815).
Proof. exact (@lem5044784 (_64815 = (term219 A B f x' _64815)) (term132 B u _64815)). Qed.
Lemma lem5044793 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5044794 {A B : Type'} (f : A -> B) (x' : B -> A) (u : B -> Prop) (_64815 : B) : (term256 A B u f x' _64815) = (term257 A B f x' u _64815).
Proof. exact (MK_COMB (@lem5044793) (@lem5044785 A B f x' u _64815)). Qed.
Lemma lem5044802 {A B : Type'} (f : A -> B) (x' : B -> A) (u : B -> Prop) (_64815 : B) : (term255 A B f x' u _64815) = (term255 A B f x' u _64815).
Proof. exact (eq_refl (term255 A B f x' u _64815)). Qed.
Lemma lem5044803 {A B : Type'} (f : A -> B) (x' : B -> A) (u : B -> Prop) (_64815 : B) : ((term236 A B u f x' _64815) = (term255 A B f x' u _64815)) = ((term255 A B f x' u _64815) = (term255 A B f x' u _64815)).
Proof. exact (MK_COMB (@lem5044794 A B f x' u _64815) (@lem5044802 A B f x' u _64815)). Qed.
Lemma lem5044805 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5044806 (x : Prop) : (x = x) = True.
Proof. exact (@lem5044805 Prop x). Qed.
Lemma lem5044807 {A B : Type'} (f : A -> B) (x' : B -> A) (u : B -> Prop) (_64815 : B) : ((term255 A B f x' u _64815) = (term255 A B f x' u _64815)) = True.
Proof. exact (@lem5044806 (term255 A B f x' u _64815)). Qed.
Lemma lem5044808 {A B : Type'} (f : A -> B) (x' : B -> A) (u : B -> Prop) (_64815 : B) : ((term236 A B u f x' _64815) = (term255 A B f x' u _64815)) = True.
Proof. exact (TRANS (@lem5044803 A B f x' u _64815) (@lem5044807 A B f x' u _64815)). Qed.
Lemma lem5044809 {A B : Type'} (f : A -> B) (x' : B -> A) (u : B -> Prop) (_64815 : B) : True = ((term236 A B u f x' _64815) = (term255 A B f x' u _64815)).
Proof. exact (SYM (@lem5044808 A B f x' u _64815)). Qed.
Lemma lem5044810 {A B : Type'} (f : A -> B) (x' : B -> A) (u : B -> Prop) (_64815 : B) : (term236 A B u f x' _64815) = (term255 A B f x' u _64815).
Proof. exact (EQ_MP (@lem5044809 A B f x' u _64815) (@lem0)). Qed.
Lemma lem5044811 {A B : Type'} (_64815 : B) (u : B -> Prop) (f : A -> B) (s : A -> Prop) (x' : B -> A) (h1 : term166 A B u f s x') : term255 A B f x' u _64815.
Proof. exact (EQ_MP (@lem5044810 A B f x' u _64815) (@lem5044572 A B _64815 u f s x' h1)). Qed.
Lemma lem5044813 (b : Prop) (a : Prop) : (a \/ b) = (term251 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5044814 {A B : Type'} (u : B -> Prop) (f : A -> B) (x' : B -> A) (_64815 : B) : (term255 A B f x' u _64815) = (term258 A B u f x' _64815).
Proof. exact (@lem5044813 (term132 B u _64815) (_64815 = (term219 A B f x' _64815))). Qed.
Lemma lem5044816 (a : Prop) : (term109 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5044817 {B : Type'} (u : B -> Prop) (_64815 : B) : (term253 B u _64815) = (u _64815).
Proof. exact (@lem5044816 (u _64815)). Qed.
Lemma lem5044818 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5044819 {B : Type'} (u : B -> Prop) (_64815 : B) : (term254 B u _64815) = (term39 B u _64815).
Proof. exact (MK_COMB (@lem5044818) (@lem5044817 B u _64815)). Qed.
Lemma lem5044820 {A B : Type'} (f : A -> B) (x' : B -> A) (_64815 : B) : (_64815 = (term219 A B f x' _64815)) = (_64815 = (term219 A B f x' _64815)).
Proof. exact (eq_refl (_64815 = (term219 A B f x' _64815))). Qed.
Lemma lem5044821 {A B : Type'} (u : B -> Prop) (f : A -> B) (x' : B -> A) (_64815 : B) : (term258 A B u f x' _64815) = (term259 A B u f x' _64815).
Proof. exact (MK_COMB (@lem5044819 B u _64815) (@lem5044820 A B f x' _64815)). Qed.
Lemma lem5044822 {A B : Type'} (u : B -> Prop) (f : A -> B) (x' : B -> A) (_64815 : B) : (term255 A B f x' u _64815) = (term259 A B u f x' _64815).
Proof. exact (TRANS (@lem5044814 A B u f x' _64815) (@lem5044821 A B u f x' _64815)). Qed.
Lemma lem5044825 {A B : Type'} (_64815 : B) (u : B -> Prop) (f : A -> B) (s : A -> Prop) (x' : B -> A) (h1 : term166 A B u f s x') : term259 A B u f x' _64815.
Proof. exact (EQ_MP (@lem5044822 A B u f x' _64815) (@lem5044811 A B _64815 u f s x' h1)). Qed.
Lemma lem5044826 {A B : Type'} (_64815 : B) (u : B -> Prop) (f : A -> B) (s : A -> Prop) (x' : B -> A) (h1 : term166 A B u f s x') : term259 A B u f x' _64815.
Proof. exact (@lem5044825 A B _64815 u f s x' h1). Qed.
Lemma lem5044827 {A B : Type'} (x : B) (u : B -> Prop) (f : A -> B) (s : A -> Prop) (x' : B -> A) (h1 : term166 A B u f s x') : term259 A B u f x' x.
Proof. exact (@lem5044826 A B x u f s x' h1). Qed.
Lemma lem5044830 {A B : Type'} (x' : B -> A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term166 A B u f s x') (h2 : term89 A B u t s t' f) (h3 : term216 B t t' x) : x = (term219 A B f x' x).
Proof. exact (@lem5044827 A B x u f s x' h1 (@lem5044778 A B u s f t t' x h2 h3)). Qed.
Lemma lem5044831 {A B : Type'} (x' : B -> A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term166 A B u f s x') (h2 : term89 A B u t s t' f) (h3 : term216 B t t' x) : term260 A B f x' x.
Proof. exact (fun h0 : term261 A B f x' x => @lem5044830 A B x' u s f t t' x h1 h2 h3). Qed.
Lemma lem5044833 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5044834 {A B : Type'} (f : A -> B) (x' : B -> A) (x : B) : (term260 A B f x' x) = (x = (term219 A B f x' x)).
Proof. exact (@lem5044833 (x = (term219 A B f x' x))). Qed.
Lemma lem5044835 {A B : Type'} (x' : B -> A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term166 A B u f s x') (h2 : term89 A B u t s t' f) (h3 : term216 B t t' x) : x = (term219 A B f x' x).
Proof. exact (EQ_MP (@lem5044834 A B f x' x) (@lem5044831 A B x' u s f t t' x h1 h2 h3)). Qed.
Lemma lem5044837 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem5044838 {B : Type'} (x : B) : x = x.
Proof. exact (@lem5044837 B x). Qed.
Lemma lem5044839 {B : Type'} (x : B) : term262 B x.
Proof. exact (fun h0 : term263 B x => @lem5044838 B x). Qed.
Lemma lem5044841 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5044842 {B : Type'} (x : B) : (term262 B x) = (x = x).
Proof. exact (@lem5044841 (x = x)). Qed.
Lemma lem5044843 {B : Type'} (x : B) : x = x.
Proof. exact (EQ_MP (@lem5044842 B x) (@lem5044839 B x)). Qed.
Lemma lem5044861 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5044862 {B : Type'} (y : B) (x : B) (z : B) : (term264 B x y z) = (term265 B y x z).
Proof. exact (@lem5044861 (y = z) (term266 B x z)). Qed.
Lemma lem5044872 {B : Type'} (x : B) (y : B) : (term267 B x y) = (term267 B x y).
Proof. exact (eq_refl (term267 B x y)). Qed.
Lemma lem5044873 {B : Type'} (y : B) (x : B) (z : B) : (term245 B x y z) = (term268 B y x z).
Proof. exact (MK_COMB (@lem5044872 B x y) (@lem5044862 B y x z)). Qed.
Lemma lem5044877 (q : Prop) (p : Prop) (r : Prop) : (term11 p q r) = (term11 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5044878 {B : Type'} (y : B) (x : B) (z : B) : (term268 B y x z) = (term269 B y x z).
Proof. exact (@lem5044877 (y = z) (term266 B x y) (term266 B x z)). Qed.
Lemma lem5044900 {B : Type'} (y : B) (x : B) (z : B) : (term245 B x y z) = (term269 B y x z).
Proof. exact (TRANS (@lem5044873 B y x z) (@lem5044878 B y x z)). Qed.
Lemma lem5044901 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5044902 {B : Type'} (y : B) (x : B) (z : B) : (term270 B x y z) = (term271 B y x z).
Proof. exact (MK_COMB (@lem5044901) (@lem5044900 B y x z)). Qed.
Lemma lem5044924 {B : Type'} (y : B) (x : B) (z : B) : (term269 B y x z) = (term269 B y x z).
Proof. exact (eq_refl (term269 B y x z)). Qed.
Lemma lem5044925 {B : Type'} (y : B) (x : B) (z : B) : ((term245 B x y z) = (term269 B y x z)) = ((term269 B y x z) = (term269 B y x z)).
Proof. exact (MK_COMB (@lem5044902 B y x z) (@lem5044924 B y x z)). Qed.
Lemma lem5044927 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5044928 (x : Prop) : (x = x) = True.
Proof. exact (@lem5044927 Prop x). Qed.
Lemma lem5044929 {B : Type'} (y : B) (x : B) (z : B) : ((term269 B y x z) = (term269 B y x z)) = True.
Proof. exact (@lem5044928 (term269 B y x z)). Qed.
Lemma lem5044930 {B : Type'} (y : B) (x : B) (z : B) : ((term245 B x y z) = (term269 B y x z)) = True.
Proof. exact (TRANS (@lem5044925 B y x z) (@lem5044929 B y x z)). Qed.
Lemma lem5044931 {B : Type'} (y : B) (x : B) (z : B) : True = ((term245 B x y z) = (term269 B y x z)).
Proof. exact (SYM (@lem5044930 B y x z)). Qed.
Lemma lem5044932 {B : Type'} (y : B) (x : B) (z : B) : (term245 B x y z) = (term269 B y x z).
Proof. exact (EQ_MP (@lem5044931 B y x z) (@lem0)). Qed.
Lemma lem5044933 {B : Type'} (y : B) (x : B) (z : B) : term269 B y x z.
Proof. exact (EQ_MP (@lem5044932 B y x z) (@lem5044716 B x y z)). Qed.
Lemma lem5044935 (b : Prop) (a : Prop) : (a \/ b) = (term251 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5044936 {B : Type'} (x : B) (y : B) (z : B) : (term269 B y x z) = (term272 B x y z).
Proof. exact (@lem5044935 (term273 B y x z) (y = z)). Qed.
Lemma lem5044938 (a : Prop) (b : Prop) : (term274 a b) = (term275 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5044939 {B : Type'} (y : B) (x : B) (z : B) : (term276 B y x z) = (term277 B y x z).
Proof. exact (@lem5044938 (term266 B x y) (term266 B x z)). Qed.
Lemma lem5044941 (a : Prop) : (term109 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5044942 {B : Type'} (x : B) (y : B) : (term278 B x y) = (x = y).
Proof. exact (@lem5044941 (x = y)). Qed.
Lemma lem5044943 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5044944 {B : Type'} (x : B) (y : B) : (term279 B x y) = (term280 B x y).
Proof. exact (MK_COMB (@lem5044943) (@lem5044942 B x y)). Qed.
Lemma lem5044946 (a : Prop) : (term109 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5044947 {B : Type'} (x : B) (z : B) : (term278 B x z) = (x = z).
Proof. exact (@lem5044946 (x = z)). Qed.
Lemma lem5044948 {B : Type'} (y : B) (x : B) (z : B) : (term277 B y x z) = (term281 B y x z).
Proof. exact (MK_COMB (@lem5044944 B x y) (@lem5044947 B x z)). Qed.
Lemma lem5044949 {B : Type'} (y : B) (x : B) (z : B) : (term276 B y x z) = (term281 B y x z).
Proof. exact (TRANS (@lem5044939 B y x z) (@lem5044948 B y x z)). Qed.
Lemma lem5044950 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5044951 {B : Type'} (y : B) (x : B) (z : B) : (term282 B y x z) = (term283 B y x z).
Proof. exact (MK_COMB (@lem5044950) (@lem5044949 B y x z)). Qed.
Lemma lem5044952 {B : Type'} (y : B) (z : B) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem5044953 {B : Type'} (x : B) (y : B) (z : B) : (term272 B x y z) = (term284 B x y z).
Proof. exact (MK_COMB (@lem5044951 B y x z) (@lem5044952 B y z)). Qed.
Lemma lem5044954 {B : Type'} (x : B) (y : B) (z : B) : (term269 B y x z) = (term284 B x y z).
Proof. exact (TRANS (@lem5044936 B x y z) (@lem5044953 B x y z)). Qed.
Lemma lem5044956 {A B : Type'} (x' : B -> A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term166 A B u f s x') (h2 : term89 A B u t s t' f) (h3 : term216 B t t' x) : term285 A B f x' x.
Proof. exact (conj (@lem5044835 A B x' u s f t t' x h1 h2 h3) (@lem5044843 B x)). Qed.
Lemma lem5044958 {B : Type'} (x : B) (y : B) (z : B) : term284 B x y z.
Proof. exact (EQ_MP (@lem5044954 B x y z) (@lem5044933 B y x z)). Qed.
Lemma lem5044959 {B : Type'} (x : B) (y : B) (z : B) : term284 B x y z.
Proof. exact (@lem5044958 B x y z). Qed.
Lemma lem5044960 {A B : Type'} (f : A -> B) (x' : B -> A) (x : B) : term286 A B f x' x.
Proof. exact (@lem5044959 B x (term219 A B f x' x) x). Qed.
Lemma lem5044963 {A B : Type'} (x' : B -> A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term166 A B u f s x') (h2 : term89 A B u t s t' f) (h3 : term216 B t t' x) : (term219 A B f x' x) = x.
Proof. exact (@lem5044960 A B f x' x (@lem5044956 A B x' u s f t t' x h1 h2 h3)). Qed.
Lemma lem5044964 {A B : Type'} (x' : B -> A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term166 A B u f s x') (h2 : term89 A B u t s t' f) (h3 : term216 B t t' x) : term287 A B f x' x.
Proof. exact (fun h0 : term288 A B f x' x => @lem5044963 A B x' u s f t t' x h1 h2 h3). Qed.
Lemma lem5044966 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5044967 {A B : Type'} (f : A -> B) (x' : B -> A) (x : B) : (term287 A B f x' x) = ((term219 A B f x' x) = x).
Proof. exact (@lem5044966 ((term219 A B f x' x) = x)). Qed.
Lemma lem5044968 {A B : Type'} (x' : B -> A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term166 A B u f s x') (h2 : term89 A B u t s t' f) (h3 : term216 B t t' x) : (term219 A B f x' x) = x.
Proof. exact (EQ_MP (@lem5044967 A B f x' x) (@lem5044964 A B x' u s f t t' x h1 h2 h3)). Qed.
Lemma lem5044970 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term216 B t t' x) : t x.
Proof. exact (proj1 (@lem5044229 B t t' x h1)). Qed.
Lemma lem5044971 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term216 B t t' x) : term246 B t x.
Proof. exact (fun h0 : term132 B t x => @lem5044970 B t t' x h1). Qed.
Lemma lem5044973 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5044974 {B : Type'} (t : B -> Prop) (x : B) : (term246 B t x) = (t x).
Proof. exact (@lem5044973 (t x)). Qed.
Lemma lem5044975 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term216 B t t' x) : t x.
Proof. exact (EQ_MP (@lem5044974 B t x) (@lem5044971 B t t' x h1)). Qed.
Lemma lem5044977 {A B : Type'} (_64816 : B) (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (h1 : term89 A B u t s t' f) : term55 B t u _64816.
Proof. exact (EQ_MP (@lem5044765 B t u _64816) (@lem5044754 A B _64816 u t s t' f h1)). Qed.
Lemma lem5044978 {A B : Type'} (_64816 : B) (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (h1 : term89 A B u t s t' f) : term55 B t u _64816.
Proof. exact (@lem5044977 A B _64816 u t s t' f h1). Qed.
Lemma lem5044979 {A B : Type'} (x : B) (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (h1 : term89 A B u t s t' f) : term55 B t u x.
Proof. exact (@lem5044978 A B x u t s t' f h1). Qed.
Lemma lem5044982 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term89 A B u t s t' f) (h2 : term216 B t t' x) : u x.
Proof. exact (@lem5044979 A B x u t s t' f h1 (@lem5044975 B t t' x h2)). Qed.
Lemma lem5044983 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term89 A B u t s t' f) (h2 : term216 B t t' x) : term246 B u x.
Proof. exact (fun h0 : term132 B u x => @lem5044982 A B u s f t t' x h1 h2). Qed.
Lemma lem5044985 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5044986 {B : Type'} (u : B -> Prop) (x : B) : (term246 B u x) = (u x).
Proof. exact (@lem5044985 (u x)). Qed.
Lemma lem5044987 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term89 A B u t s t' f) (h2 : term216 B t t' x) : u x.
Proof. exact (EQ_MP (@lem5044986 B u x) (@lem5044983 A B u s f t t' x h1 h2)). Qed.
Lemma lem5044993 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5044994 {A B : Type'} (s : A -> Prop) (x' : B -> A) (u : B -> Prop) (_64815 : B) : (term237 A B u s x' _64815) = (term289 A B s x' u _64815).
Proof. exact (@lem5044993 (term220 A B s x' _64815) (term132 B u _64815)). Qed.
Lemma lem5045000 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5045001 {A B : Type'} (s : A -> Prop) (x' : B -> A) (u : B -> Prop) (_64815 : B) : (term290 A B u s x' _64815) = (term291 A B s x' u _64815).
Proof. exact (MK_COMB (@lem5045000) (@lem5044994 A B s x' u _64815)). Qed.
Lemma lem5045007 {A B : Type'} (s : A -> Prop) (x' : B -> A) (u : B -> Prop) (_64815 : B) : (term289 A B s x' u _64815) = (term289 A B s x' u _64815).
Proof. exact (eq_refl (term289 A B s x' u _64815)). Qed.
Lemma lem5045008 {A B : Type'} (s : A -> Prop) (x' : B -> A) (u : B -> Prop) (_64815 : B) : ((term237 A B u s x' _64815) = (term289 A B s x' u _64815)) = ((term289 A B s x' u _64815) = (term289 A B s x' u _64815)).
Proof. exact (MK_COMB (@lem5045001 A B s x' u _64815) (@lem5045007 A B s x' u _64815)). Qed.
Lemma lem5045010 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5045011 (x : Prop) : (x = x) = True.
Proof. exact (@lem5045010 Prop x). Qed.
Lemma lem5045012 {A B : Type'} (s : A -> Prop) (x' : B -> A) (u : B -> Prop) (_64815 : B) : ((term289 A B s x' u _64815) = (term289 A B s x' u _64815)) = True.
Proof. exact (@lem5045011 (term289 A B s x' u _64815)). Qed.
Lemma lem5045013 {A B : Type'} (s : A -> Prop) (x' : B -> A) (u : B -> Prop) (_64815 : B) : ((term237 A B u s x' _64815) = (term289 A B s x' u _64815)) = True.
Proof. exact (TRANS (@lem5045008 A B s x' u _64815) (@lem5045012 A B s x' u _64815)). Qed.
Lemma lem5045014 {A B : Type'} (s : A -> Prop) (x' : B -> A) (u : B -> Prop) (_64815 : B) : True = ((term237 A B u s x' _64815) = (term289 A B s x' u _64815)).
Proof. exact (SYM (@lem5045013 A B s x' u _64815)). Qed.
Lemma lem5045015 {A B : Type'} (s : A -> Prop) (x' : B -> A) (u : B -> Prop) (_64815 : B) : (term237 A B u s x' _64815) = (term289 A B s x' u _64815).
Proof. exact (EQ_MP (@lem5045014 A B s x' u _64815) (@lem0)). Qed.
Lemma lem5045016 {A B : Type'} (_64815 : B) (u : B -> Prop) (f : A -> B) (s : A -> Prop) (x' : B -> A) (h1 : term166 A B u f s x') : term289 A B s x' u _64815.
Proof. exact (EQ_MP (@lem5045015 A B s x' u _64815) (@lem5044578 A B _64815 u f s x' h1)). Qed.
Lemma lem5045018 (b : Prop) (a : Prop) : (a \/ b) = (term251 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5045019 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (x' : B -> A) (_64815 : B) : (term289 A B s x' u _64815) = (term292 A B u s x' _64815).
Proof. exact (@lem5045018 (term132 B u _64815) (term220 A B s x' _64815)). Qed.
Lemma lem5045021 (a : Prop) : (term109 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5045022 {B : Type'} (u : B -> Prop) (_64815 : B) : (term253 B u _64815) = (u _64815).
Proof. exact (@lem5045021 (u _64815)). Qed.
Lemma lem5045023 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5045024 {B : Type'} (u : B -> Prop) (_64815 : B) : (term254 B u _64815) = (term39 B u _64815).
Proof. exact (MK_COMB (@lem5045023) (@lem5045022 B u _64815)). Qed.
Lemma lem5045025 {A B : Type'} (s : A -> Prop) (x' : B -> A) (_64815 : B) : (term220 A B s x' _64815) = (term220 A B s x' _64815).
Proof. exact (eq_refl (term220 A B s x' _64815)). Qed.
Lemma lem5045026 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (x' : B -> A) (_64815 : B) : (term292 A B u s x' _64815) = (term293 A B u s x' _64815).
Proof. exact (MK_COMB (@lem5045024 B u _64815) (@lem5045025 A B s x' _64815)). Qed.
Lemma lem5045027 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (x' : B -> A) (_64815 : B) : (term289 A B s x' u _64815) = (term293 A B u s x' _64815).
Proof. exact (TRANS (@lem5045019 A B u s x' _64815) (@lem5045026 A B u s x' _64815)). Qed.
Lemma lem5045030 {A B : Type'} (_64815 : B) (u : B -> Prop) (f : A -> B) (s : A -> Prop) (x' : B -> A) (h1 : term166 A B u f s x') : term293 A B u s x' _64815.
Proof. exact (EQ_MP (@lem5045027 A B u s x' _64815) (@lem5045016 A B _64815 u f s x' h1)). Qed.
Lemma lem5045031 {A B : Type'} (_64815 : B) (u : B -> Prop) (f : A -> B) (s : A -> Prop) (x' : B -> A) (h1 : term166 A B u f s x') : term293 A B u s x' _64815.
Proof. exact (@lem5045030 A B _64815 u f s x' h1). Qed.
Lemma lem5045032 {A B : Type'} (x : B) (u : B -> Prop) (f : A -> B) (s : A -> Prop) (x' : B -> A) (h1 : term166 A B u f s x') : term293 A B u s x' x.
Proof. exact (@lem5045031 A B x u f s x' h1). Qed.
Lemma lem5045035 {A B : Type'} (x' : B -> A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term166 A B u f s x') (h2 : term89 A B u t s t' f) (h3 : term216 B t t' x) : term220 A B s x' x.
Proof. exact (@lem5045032 A B x u f s x' h1 (@lem5044987 A B u s f t t' x h2 h3)). Qed.
Lemma lem5045036 {A B : Type'} (x' : B -> A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term166 A B u f s x') (h2 : term89 A B u t s t' f) (h3 : term216 B t t' x) : term294 A B s x' x.
Proof. exact (fun h0 : term295 A B s x' x => @lem5045035 A B x' u s f t t' x h1 h2 h3). Qed.
Lemma lem5045038 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5045039 {A B : Type'} (s : A -> Prop) (x' : B -> A) (x : B) : (term294 A B s x' x) = (term220 A B s x' x).
Proof. exact (@lem5045038 (term220 A B s x' x)). Qed.
Lemma lem5045040 {A B : Type'} (x' : B -> A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term166 A B u f s x') (h2 : term89 A B u t s t' f) (h3 : term216 B t t' x) : term220 A B s x' x.
Proof. exact (EQ_MP (@lem5045039 A B s x' x) (@lem5045036 A B x' u s f t t' x h1 h2 h3)). Qed.
Lemma lem5045042 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term216 B t t' x) : t x.
Proof. exact (proj1 (@lem5044229 B t t' x h1)). Qed.
Lemma lem5045043 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term216 B t t' x) : term246 B t x.
Proof. exact (fun h0 : term132 B t x => @lem5045042 B t t' x h1). Qed.
Lemma lem5045045 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5045046 {B : Type'} (t : B -> Prop) (x : B) : (term246 B t x) = (t x).
Proof. exact (@lem5045045 (t x)). Qed.
Lemma lem5045047 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term216 B t t' x) : t x.
Proof. exact (EQ_MP (@lem5045046 B t x) (@lem5045043 B t t' x h1)). Qed.
Lemma lem5045049 {A B : Type'} (_64816 : B) (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (h1 : term89 A B u t s t' f) : term55 B t u _64816.
Proof. exact (EQ_MP (@lem5044765 B t u _64816) (@lem5044754 A B _64816 u t s t' f h1)). Qed.
Lemma lem5045050 {A B : Type'} (_64816 : B) (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (h1 : term89 A B u t s t' f) : term55 B t u _64816.
Proof. exact (@lem5045049 A B _64816 u t s t' f h1). Qed.
Lemma lem5045051 {A B : Type'} (x : B) (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (h1 : term89 A B u t s t' f) : term55 B t u x.
Proof. exact (@lem5045050 A B x u t s t' f h1). Qed.
Lemma lem5045054 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term89 A B u t s t' f) (h2 : term216 B t t' x) : u x.
Proof. exact (@lem5045051 A B x u t s t' f h1 (@lem5045047 B t t' x h2)). Qed.
Lemma lem5045055 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term89 A B u t s t' f) (h2 : term216 B t t' x) : term246 B u x.
Proof. exact (fun h0 : term132 B u x => @lem5045054 A B u s f t t' x h1 h2). Qed.
Lemma lem5045057 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5045058 {B : Type'} (u : B -> Prop) (x : B) : (term246 B u x) = (u x).
Proof. exact (@lem5045057 (u x)). Qed.
Lemma lem5045059 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term89 A B u t s t' f) (h2 : term216 B t t' x) : u x.
Proof. exact (EQ_MP (@lem5045058 B u x) (@lem5045055 A B u s f t t' x h1 h2)). Qed.
Lemma lem5045061 {A B : Type'} (_64815 : B) (u : B -> Prop) (f : A -> B) (s : A -> Prop) (x' : B -> A) (h1 : term166 A B u f s x') : term259 A B u f x' _64815.
Proof. exact (EQ_MP (@lem5044822 A B u f x' _64815) (@lem5044811 A B _64815 u f s x' h1)). Qed.
Lemma lem5045062 {A B : Type'} (_64815 : B) (u : B -> Prop) (f : A -> B) (s : A -> Prop) (x' : B -> A) (h1 : term166 A B u f s x') : term259 A B u f x' _64815.
Proof. exact (@lem5045061 A B _64815 u f s x' h1). Qed.
Lemma lem5045063 {A B : Type'} (x : B) (u : B -> Prop) (f : A -> B) (s : A -> Prop) (x' : B -> A) (h1 : term166 A B u f s x') : term259 A B u f x' x.
Proof. exact (@lem5045062 A B x u f s x' h1). Qed.
Lemma lem5045066 {A B : Type'} (x' : B -> A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term166 A B u f s x') (h2 : term89 A B u t s t' f) (h3 : term216 B t t' x) : x = (term219 A B f x' x).
Proof. exact (@lem5045063 A B x u f s x' h1 (@lem5045059 A B u s f t t' x h2 h3)). Qed.
Lemma lem5045067 {A B : Type'} (x' : B -> A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term166 A B u f s x') (h2 : term89 A B u t s t' f) (h3 : term216 B t t' x) : term260 A B f x' x.
Proof. exact (fun h0 : term261 A B f x' x => @lem5045066 A B x' u s f t t' x h1 h2 h3). Qed.
Lemma lem5045069 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5045070 {A B : Type'} (f : A -> B) (x' : B -> A) (x : B) : (term260 A B f x' x) = (x = (term219 A B f x' x)).
Proof. exact (@lem5045069 (x = (term219 A B f x' x))). Qed.
Lemma lem5045071 {A B : Type'} (x' : B -> A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term166 A B u f s x') (h2 : term89 A B u t s t' f) (h3 : term216 B t t' x) : x = (term219 A B f x' x).
Proof. exact (EQ_MP (@lem5045070 A B f x' x) (@lem5045067 A B x' u s f t t' x h1 h2 h3)). Qed.
Lemma lem5045073 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term216 B t t' x) : t x.
Proof. exact (proj1 (@lem5044229 B t t' x h1)). Qed.
Lemma lem5045074 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term216 B t t' x) : term246 B t x.
Proof. exact (fun h0 : term132 B t x => @lem5045073 B t t' x h1). Qed.
Lemma lem5045076 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5045077 {B : Type'} (t : B -> Prop) (x : B) : (term246 B t x) = (t x).
Proof. exact (@lem5045076 (t x)). Qed.
Lemma lem5045078 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term216 B t t' x) : t x.
Proof. exact (EQ_MP (@lem5045077 B t x) (@lem5045074 B t t' x h1)). Qed.
Lemma lem5045084 (q : Prop) (p : Prop) (r : Prop) : (term11 p q r) = (term11 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5045085 {B : Type'} (_64830 : B) (t : B -> Prop) (_64829 : B) : (term244 B _64830 t _64829) = (term296 B _64830 t _64829).
Proof. exact (@lem5045084 (t _64830) (term266 B _64829 _64830) (term132 B t _64829)). Qed.
Lemma lem5045099 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5045100 {B : Type'} (t : B -> Prop) (_64829 : B) (_64830 : B) : (term297 B _64830 t _64829) = (term298 B t _64829 _64830).
Proof. exact (@lem5045099 (term132 B t _64829) (term266 B _64829 _64830)). Qed.
Lemma lem5045108 {B : Type'} (t : B -> Prop) (_64830 : B) : (term299 B t _64830) = (term299 B t _64830).
Proof. exact (eq_refl (term299 B t _64830)). Qed.
Lemma lem5045109 {B : Type'} (t : B -> Prop) (_64829 : B) (_64830 : B) : (term296 B _64830 t _64829) = (term300 B t _64829 _64830).
Proof. exact (MK_COMB (@lem5045108 B t _64830) (@lem5045100 B t _64829 _64830)). Qed.
Lemma lem5045120 {B : Type'} (t : B -> Prop) (_64829 : B) (_64830 : B) : (term244 B _64830 t _64829) = (term300 B t _64829 _64830).
Proof. exact (TRANS (@lem5045085 B _64830 t _64829) (@lem5045109 B t _64829 _64830)). Qed.
Lemma lem5045121 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5045122 {B : Type'} (t : B -> Prop) (_64829 : B) (_64830 : B) : (term301 B _64830 t _64829) = (term302 B t _64829 _64830).
Proof. exact (MK_COMB (@lem5045121) (@lem5045120 B t _64829 _64830)). Qed.
Lemma lem5045136 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5045137 {B : Type'} (t : B -> Prop) (_64829 : B) (_64830 : B) : (term297 B _64830 t _64829) = (term298 B t _64829 _64830).
Proof. exact (@lem5045136 (term132 B t _64829) (term266 B _64829 _64830)). Qed.
Lemma lem5045145 {B : Type'} (t : B -> Prop) (_64830 : B) : (term299 B t _64830) = (term299 B t _64830).
Proof. exact (eq_refl (term299 B t _64830)). Qed.
Lemma lem5045146 {B : Type'} (t : B -> Prop) (_64829 : B) (_64830 : B) : (term296 B _64830 t _64829) = (term300 B t _64829 _64830).
Proof. exact (MK_COMB (@lem5045145 B t _64830) (@lem5045137 B t _64829 _64830)). Qed.
Lemma lem5045157 {B : Type'} (t : B -> Prop) (_64829 : B) (_64830 : B) : ((term244 B _64830 t _64829) = (term296 B _64830 t _64829)) = ((term300 B t _64829 _64830) = (term300 B t _64829 _64830)).
Proof. exact (MK_COMB (@lem5045122 B t _64829 _64830) (@lem5045146 B t _64829 _64830)). Qed.
Lemma lem5045159 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5045160 (x : Prop) : (x = x) = True.
Proof. exact (@lem5045159 Prop x). Qed.
Lemma lem5045161 {B : Type'} (t : B -> Prop) (_64829 : B) (_64830 : B) : ((term300 B t _64829 _64830) = (term300 B t _64829 _64830)) = True.
Proof. exact (@lem5045160 (term300 B t _64829 _64830)). Qed.
Lemma lem5045162 {B : Type'} (_64830 : B) (t : B -> Prop) (_64829 : B) : ((term244 B _64830 t _64829) = (term296 B _64830 t _64829)) = True.
Proof. exact (TRANS (@lem5045157 B t _64829 _64830) (@lem5045161 B t _64829 _64830)). Qed.
Lemma lem5045163 {B : Type'} (_64830 : B) (t : B -> Prop) (_64829 : B) : True = ((term244 B _64830 t _64829) = (term296 B _64830 t _64829)).
Proof. exact (SYM (@lem5045162 B _64830 t _64829)). Qed.
Lemma lem5045164 {B : Type'} (_64830 : B) (t : B -> Prop) (_64829 : B) : (term244 B _64830 t _64829) = (term296 B _64830 t _64829).
Proof. exact (EQ_MP (@lem5045163 B _64830 t _64829) (@lem0)). Qed.
Lemma lem5045165 {B : Type'} (_64830 : B) (t : B -> Prop) (_64829 : B) : term296 B _64830 t _64829.
Proof. exact (EQ_MP (@lem5045164 B _64830 t _64829) (@lem5044686 B _64830 t _64829)). Qed.
Lemma lem5045167 (b : Prop) (a : Prop) : (a \/ b) = (term251 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5045168 {B : Type'} (_64829 : B) (t : B -> Prop) (_64830 : B) : (term296 B _64830 t _64829) = (term303 B _64829 t _64830).
Proof. exact (@lem5045167 (term297 B _64830 t _64829) (t _64830)). Qed.
Lemma lem5045170 (a : Prop) (b : Prop) : (term274 a b) = (term275 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5045171 {B : Type'} (_64830 : B) (t : B -> Prop) (_64829 : B) : (term304 B _64830 t _64829) = (term305 B _64830 t _64829).
Proof. exact (@lem5045170 (term266 B _64829 _64830) (term132 B t _64829)). Qed.
Lemma lem5045173 (a : Prop) : (term109 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5045174 {B : Type'} (_64829 : B) (_64830 : B) : (term278 B _64829 _64830) = (_64829 = _64830).
Proof. exact (@lem5045173 (_64829 = _64830)). Qed.
Lemma lem5045175 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5045176 {B : Type'} (_64829 : B) (_64830 : B) : (term279 B _64829 _64830) = (term280 B _64829 _64830).
Proof. exact (MK_COMB (@lem5045175) (@lem5045174 B _64829 _64830)). Qed.
Lemma lem5045178 (a : Prop) : (term109 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5045179 {B : Type'} (t : B -> Prop) (_64829 : B) : (term253 B t _64829) = (t _64829).
Proof. exact (@lem5045178 (t _64829)). Qed.
Lemma lem5045180 {B : Type'} (_64830 : B) (t : B -> Prop) (_64829 : B) : (term305 B _64830 t _64829) = (term306 B _64830 t _64829).
Proof. exact (MK_COMB (@lem5045176 B _64829 _64830) (@lem5045179 B t _64829)). Qed.
Lemma lem5045181 {B : Type'} (_64830 : B) (t : B -> Prop) (_64829 : B) : (term304 B _64830 t _64829) = (term306 B _64830 t _64829).
Proof. exact (TRANS (@lem5045171 B _64830 t _64829) (@lem5045180 B _64830 t _64829)). Qed.
Lemma lem5045182 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5045183 {B : Type'} (_64830 : B) (t : B -> Prop) (_64829 : B) : (term307 B _64830 t _64829) = (term308 B _64830 t _64829).
Proof. exact (MK_COMB (@lem5045182) (@lem5045181 B _64830 t _64829)). Qed.
Lemma lem5045184 {B : Type'} (t : B -> Prop) (_64830 : B) : (t _64830) = (t _64830).
Proof. exact (eq_refl (t _64830)). Qed.
Lemma lem5045185 {B : Type'} (_64829 : B) (t : B -> Prop) (_64830 : B) : (term303 B _64829 t _64830) = (term309 B _64829 t _64830).
Proof. exact (MK_COMB (@lem5045183 B _64830 t _64829) (@lem5045184 B t _64830)). Qed.
Lemma lem5045186 {B : Type'} (_64829 : B) (t : B -> Prop) (_64830 : B) : (term296 B _64830 t _64829) = (term309 B _64829 t _64830).
Proof. exact (TRANS (@lem5045168 B _64829 t _64830) (@lem5045185 B _64829 t _64830)). Qed.
Lemma lem5045188 {A B : Type'} (x' : B -> A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term166 A B u f s x') (h2 : term89 A B u t s t' f) (h3 : term216 B t t' x) : term310 A B f x' t x.
Proof. exact (conj (@lem5045071 A B x' u s f t t' x h1 h2 h3) (@lem5045078 B t t' x h3)). Qed.
Lemma lem5045190 {B : Type'} (_64829 : B) (t : B -> Prop) (_64830 : B) : term309 B _64829 t _64830.
Proof. exact (EQ_MP (@lem5045186 B _64829 t _64830) (@lem5045165 B _64830 t _64829)). Qed.
Lemma lem5045191 {B : Type'} (_64829 : B) (t : B -> Prop) (_64830 : B) : term309 B _64829 t _64830.
Proof. exact (@lem5045190 B _64829 t _64830). Qed.
Lemma lem5045192 {A B : Type'} (t : B -> Prop) (f : A -> B) (x' : B -> A) (x : B) : term311 A B t f x' x.
Proof. exact (@lem5045191 B x t (term219 A B f x' x)). Qed.
Lemma lem5045195 {A B : Type'} (x' : B -> A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term166 A B u f s x') (h2 : term89 A B u t s t' f) (h3 : term216 B t t' x) : term312 A B t f x' x.
Proof. exact (@lem5045192 A B t f x' x (@lem5045188 A B x' u s f t t' x h1 h2 h3)). Qed.
Lemma lem5045196 {A B : Type'} (x' : B -> A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term166 A B u f s x') (h2 : term89 A B u t s t' f) (h3 : term216 B t t' x) : term313 A B t f x' x.
Proof. exact (fun h0 : term314 A B t f x' x => @lem5045195 A B x' u s f t t' x h1 h2 h3). Qed.
Lemma lem5045198 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5045199 {A B : Type'} (t : B -> Prop) (f : A -> B) (x' : B -> A) (x : B) : (term313 A B t f x' x) = (term312 A B t f x' x).
Proof. exact (@lem5045198 (term312 A B t f x' x)). Qed.
Lemma lem5045200 {A B : Type'} (x' : B -> A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term166 A B u f s x') (h2 : term89 A B u t s t' f) (h3 : term216 B t t' x) : term312 A B t f x' x.
Proof. exact (EQ_MP (@lem5045199 A B t f x' x) (@lem5045196 A B x' u s f t t' x h1 h2 h3)). Qed.
Lemma lem5045216 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5045217 {A B : Type'} (t' : B -> Prop) (t : B -> Prop) (f : A -> B) (_64819 : A) : (term315 A B t t' f _64819) = (term316 A B t' t f _64819).
Proof. exact (@lem5045216 (term82 A B t' f _64819) (term235 A B t f _64819)). Qed.
Lemma lem5045223 {A : Type'} (s : A -> Prop) (_64819 : A) : (term124 A s _64819) = (term124 A s _64819).
Proof. exact (eq_refl (term124 A s _64819)). Qed.
Lemma lem5045224 {A B : Type'} (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (f : A -> B) (_64819 : A) : (term234 A B s t t' f _64819) = (term317 A B s t' t f _64819).
Proof. exact (MK_COMB (@lem5045223 A s _64819) (@lem5045217 A B t' t f _64819)). Qed.
Lemma lem5045228 (q : Prop) (p : Prop) (r : Prop) : (term11 p q r) = (term11 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5045229 {A B : Type'} (t' : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (_64819 : A) : (term317 A B s t' t f _64819) = (term238 A B t' s t f _64819).
Proof. exact (@lem5045228 (term82 A B t' f _64819) (term132 A s _64819) (term235 A B t f _64819)). Qed.
Lemma lem5045245 {A B : Type'} (t' : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (_64819 : A) : (term234 A B s t t' f _64819) = (term238 A B t' s t f _64819).
Proof. exact (TRANS (@lem5045224 A B s t' t f _64819) (@lem5045229 A B t' s t f _64819)). Qed.
Lemma lem5045246 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5045247 {A B : Type'} (t' : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (_64819 : A) : (term318 A B s t t' f _64819) = (term319 A B t' s t f _64819).
Proof. exact (MK_COMB (@lem5045246) (@lem5045245 A B t' s t f _64819)). Qed.
Lemma lem5045263 {A B : Type'} (t' : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (_64819 : A) : (term238 A B t' s t f _64819) = (term238 A B t' s t f _64819).
Proof. exact (eq_refl (term238 A B t' s t f _64819)). Qed.
Lemma lem5045264 {A B : Type'} (t' : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (_64819 : A) : ((term234 A B s t t' f _64819) = (term238 A B t' s t f _64819)) = ((term238 A B t' s t f _64819) = (term238 A B t' s t f _64819)).
Proof. exact (MK_COMB (@lem5045247 A B t' s t f _64819) (@lem5045263 A B t' s t f _64819)). Qed.
Lemma lem5045266 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5045267 (x : Prop) : (x = x) = True.
Proof. exact (@lem5045266 Prop x). Qed.
Lemma lem5045268 {A B : Type'} (t' : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (_64819 : A) : ((term238 A B t' s t f _64819) = (term238 A B t' s t f _64819)) = True.
Proof. exact (@lem5045267 (term238 A B t' s t f _64819)). Qed.
Lemma lem5045269 {A B : Type'} (t' : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (_64819 : A) : ((term234 A B s t t' f _64819) = (term238 A B t' s t f _64819)) = True.
Proof. exact (TRANS (@lem5045264 A B t' s t f _64819) (@lem5045268 A B t' s t f _64819)). Qed.
Lemma lem5045270 {A B : Type'} (t' : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (_64819 : A) : True = ((term234 A B s t t' f _64819) = (term238 A B t' s t f _64819)).
Proof. exact (SYM (@lem5045269 A B t' s t f _64819)). Qed.
Lemma lem5045271 {A B : Type'} (t' : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (_64819 : A) : (term234 A B s t t' f _64819) = (term238 A B t' s t f _64819).
Proof. exact (EQ_MP (@lem5045270 A B t' s t f _64819) (@lem0)). Qed.
Lemma lem5045272 {A B : Type'} (_64819 : A) (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (h1 : term89 A B u t s t' f) : term238 A B t' s t f _64819.
Proof. exact (EQ_MP (@lem5045271 A B t' s t f _64819) (@lem5044546 A B _64819 u t s t' f h1)). Qed.
Lemma lem5045274 (b : Prop) (a : Prop) : (a \/ b) = (term251 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5045275 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (f : A -> B) (_64819 : A) : (term238 A B t' s t f _64819) = (term320 A B s t t' f _64819).
Proof. exact (@lem5045274 (term174 A B s t f _64819) (term82 A B t' f _64819)). Qed.
Lemma lem5045277 (a : Prop) (b : Prop) : (term274 a b) = (term275 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5045278 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (_64819 : A) : (term321 A B s t f _64819) = (term322 A B s t f _64819).
Proof. exact (@lem5045277 (term132 A s _64819) (term235 A B t f _64819)). Qed.
Lemma lem5045280 (a : Prop) : (term109 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5045281 {A : Type'} (s : A -> Prop) (_64819 : A) : (term253 A s _64819) = (s _64819).
Proof. exact (@lem5045280 (s _64819)). Qed.
Lemma lem5045282 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5045283 {A : Type'} (s : A -> Prop) (_64819 : A) : (term323 A s _64819) = (term80 A s _64819).
Proof. exact (MK_COMB (@lem5045282) (@lem5045281 A s _64819)). Qed.
Lemma lem5045285 (a : Prop) : (term109 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5045286 {A B : Type'} (t : B -> Prop) (f : A -> B) (_64819 : A) : (term324 A B t f _64819) = (term82 A B t f _64819).
Proof. exact (@lem5045285 (term82 A B t f _64819)). Qed.
Lemma lem5045287 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (_64819 : A) : (term322 A B s t f _64819) = (term83 A B s t f _64819).
Proof. exact (MK_COMB (@lem5045283 A s _64819) (@lem5045286 A B t f _64819)). Qed.
Lemma lem5045288 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (_64819 : A) : (term321 A B s t f _64819) = (term83 A B s t f _64819).
Proof. exact (TRANS (@lem5045278 A B s t f _64819) (@lem5045287 A B s t f _64819)). Qed.
Lemma lem5045289 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5045290 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (_64819 : A) : (term325 A B s t f _64819) = (term326 A B s t f _64819).
Proof. exact (MK_COMB (@lem5045289) (@lem5045288 A B s t f _64819)). Qed.
Lemma lem5045291 {A B : Type'} (t' : B -> Prop) (f : A -> B) (_64819 : A) : (term82 A B t' f _64819) = (term82 A B t' f _64819).
Proof. exact (eq_refl (term82 A B t' f _64819)). Qed.
Lemma lem5045292 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (f : A -> B) (_64819 : A) : (term320 A B s t t' f _64819) = (term327 A B s t t' f _64819).
Proof. exact (MK_COMB (@lem5045290 A B s t f _64819) (@lem5045291 A B t' f _64819)). Qed.
Lemma lem5045293 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (f : A -> B) (_64819 : A) : (term238 A B t' s t f _64819) = (term327 A B s t t' f _64819).
Proof. exact (TRANS (@lem5045275 A B s t t' f _64819) (@lem5045292 A B s t t' f _64819)). Qed.
Lemma lem5045295 {A B : Type'} (x' : B -> A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term166 A B u f s x') (h2 : term89 A B u t s t' f) (h3 : term216 B t t' x) : term328 A B s t f x' x.
Proof. exact (conj (@lem5045040 A B x' u s f t t' x h1 h2 h3) (@lem5045200 A B x' u s f t t' x h1 h2 h3)). Qed.
Lemma lem5045297 {A B : Type'} (_64819 : A) (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (h1 : term89 A B u t s t' f) : term327 A B s t t' f _64819.
Proof. exact (EQ_MP (@lem5045293 A B s t t' f _64819) (@lem5045272 A B _64819 u t s t' f h1)). Qed.
Lemma lem5045298 {A B : Type'} (_64819 : A) (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (h1 : term89 A B u t s t' f) : term327 A B s t t' f _64819.
Proof. exact (@lem5045297 A B _64819 u t s t' f h1). Qed.
Lemma lem5045299 {A B : Type'} (x' : B -> A) (x : B) (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (h1 : term89 A B u t s t' f) : term329 A B s t t' f x' x.
Proof. exact (@lem5045298 A B (x' x) u t s t' f h1). Qed.
Lemma lem5045302 {A B : Type'} (x' : B -> A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term166 A B u f s x') (h2 : term89 A B u t s t' f) (h3 : term216 B t t' x) : term312 A B t' f x' x.
Proof. exact (@lem5045299 A B x' x u t s t' f h2 (@lem5045295 A B x' u s f t t' x h1 h2 h3)). Qed.
Lemma lem5045303 {A B : Type'} (x' : B -> A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term166 A B u f s x') (h2 : term89 A B u t s t' f) (h3 : term216 B t t' x) : term313 A B t' f x' x.
Proof. exact (fun h0 : term314 A B t' f x' x => @lem5045302 A B x' u s f t t' x h1 h2 h3). Qed.
Lemma lem5045305 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5045306 {A B : Type'} (t' : B -> Prop) (f : A -> B) (x' : B -> A) (x : B) : (term313 A B t' f x' x) = (term312 A B t' f x' x).
Proof. exact (@lem5045305 (term312 A B t' f x' x)). Qed.
Lemma lem5045307 {A B : Type'} (x' : B -> A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term166 A B u f s x') (h2 : term89 A B u t s t' f) (h3 : term216 B t t' x) : term312 A B t' f x' x.
Proof. exact (EQ_MP (@lem5045306 A B t' f x' x) (@lem5045303 A B x' u s f t t' x h1 h2 h3)). Qed.
Lemma lem5045313 (q : Prop) (p : Prop) (r : Prop) : (term11 p q r) = (term11 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5045314 {B : Type'} (_64828 : B) (t' : B -> Prop) (_64827 : B) : (term244 B _64828 t' _64827) = (term296 B _64828 t' _64827).
Proof. exact (@lem5045313 (t' _64828) (term266 B _64827 _64828) (term132 B t' _64827)). Qed.
Lemma lem5045328 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5045329 {B : Type'} (t' : B -> Prop) (_64827 : B) (_64828 : B) : (term297 B _64828 t' _64827) = (term298 B t' _64827 _64828).
Proof. exact (@lem5045328 (term132 B t' _64827) (term266 B _64827 _64828)). Qed.
Lemma lem5045337 {B : Type'} (t' : B -> Prop) (_64828 : B) : (term299 B t' _64828) = (term299 B t' _64828).
Proof. exact (eq_refl (term299 B t' _64828)). Qed.
Lemma lem5045338 {B : Type'} (t' : B -> Prop) (_64827 : B) (_64828 : B) : (term296 B _64828 t' _64827) = (term300 B t' _64827 _64828).
Proof. exact (MK_COMB (@lem5045337 B t' _64828) (@lem5045329 B t' _64827 _64828)). Qed.
Lemma lem5045349 {B : Type'} (t' : B -> Prop) (_64827 : B) (_64828 : B) : (term244 B _64828 t' _64827) = (term300 B t' _64827 _64828).
Proof. exact (TRANS (@lem5045314 B _64828 t' _64827) (@lem5045338 B t' _64827 _64828)). Qed.
Lemma lem5045350 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5045351 {B : Type'} (t' : B -> Prop) (_64827 : B) (_64828 : B) : (term301 B _64828 t' _64827) = (term302 B t' _64827 _64828).
Proof. exact (MK_COMB (@lem5045350) (@lem5045349 B t' _64827 _64828)). Qed.
Lemma lem5045365 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5045366 {B : Type'} (t' : B -> Prop) (_64827 : B) (_64828 : B) : (term297 B _64828 t' _64827) = (term298 B t' _64827 _64828).
Proof. exact (@lem5045365 (term132 B t' _64827) (term266 B _64827 _64828)). Qed.
Lemma lem5045374 {B : Type'} (t' : B -> Prop) (_64828 : B) : (term299 B t' _64828) = (term299 B t' _64828).
Proof. exact (eq_refl (term299 B t' _64828)). Qed.
Lemma lem5045375 {B : Type'} (t' : B -> Prop) (_64827 : B) (_64828 : B) : (term296 B _64828 t' _64827) = (term300 B t' _64827 _64828).
Proof. exact (MK_COMB (@lem5045374 B t' _64828) (@lem5045366 B t' _64827 _64828)). Qed.
Lemma lem5045386 {B : Type'} (t' : B -> Prop) (_64827 : B) (_64828 : B) : ((term244 B _64828 t' _64827) = (term296 B _64828 t' _64827)) = ((term300 B t' _64827 _64828) = (term300 B t' _64827 _64828)).
Proof. exact (MK_COMB (@lem5045351 B t' _64827 _64828) (@lem5045375 B t' _64827 _64828)). Qed.
Lemma lem5045388 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5045389 (x : Prop) : (x = x) = True.
Proof. exact (@lem5045388 Prop x). Qed.
Lemma lem5045390 {B : Type'} (t' : B -> Prop) (_64827 : B) (_64828 : B) : ((term300 B t' _64827 _64828) = (term300 B t' _64827 _64828)) = True.
Proof. exact (@lem5045389 (term300 B t' _64827 _64828)). Qed.
Lemma lem5045391 {B : Type'} (_64828 : B) (t' : B -> Prop) (_64827 : B) : ((term244 B _64828 t' _64827) = (term296 B _64828 t' _64827)) = True.
Proof. exact (TRANS (@lem5045386 B t' _64827 _64828) (@lem5045390 B t' _64827 _64828)). Qed.
Lemma lem5045392 {B : Type'} (_64828 : B) (t' : B -> Prop) (_64827 : B) : True = ((term244 B _64828 t' _64827) = (term296 B _64828 t' _64827)).
Proof. exact (SYM (@lem5045391 B _64828 t' _64827)). Qed.
Lemma lem5045393 {B : Type'} (_64828 : B) (t' : B -> Prop) (_64827 : B) : (term244 B _64828 t' _64827) = (term296 B _64828 t' _64827).
Proof. exact (EQ_MP (@lem5045392 B _64828 t' _64827) (@lem0)). Qed.
Lemma lem5045394 {B : Type'} (_64828 : B) (t' : B -> Prop) (_64827 : B) : term296 B _64828 t' _64827.
Proof. exact (EQ_MP (@lem5045393 B _64828 t' _64827) (@lem5044674 B _64828 t' _64827)). Qed.
Lemma lem5045396 (b : Prop) (a : Prop) : (a \/ b) = (term251 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5045397 {B : Type'} (_64827 : B) (t' : B -> Prop) (_64828 : B) : (term296 B _64828 t' _64827) = (term303 B _64827 t' _64828).
Proof. exact (@lem5045396 (term297 B _64828 t' _64827) (t' _64828)). Qed.
Lemma lem5045399 (a : Prop) (b : Prop) : (term274 a b) = (term275 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5045400 {B : Type'} (_64828 : B) (t' : B -> Prop) (_64827 : B) : (term304 B _64828 t' _64827) = (term305 B _64828 t' _64827).
Proof. exact (@lem5045399 (term266 B _64827 _64828) (term132 B t' _64827)). Qed.
Lemma lem5045402 (a : Prop) : (term109 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5045403 {B : Type'} (_64827 : B) (_64828 : B) : (term278 B _64827 _64828) = (_64827 = _64828).
Proof. exact (@lem5045402 (_64827 = _64828)). Qed.
Lemma lem5045404 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5045405 {B : Type'} (_64827 : B) (_64828 : B) : (term279 B _64827 _64828) = (term280 B _64827 _64828).
Proof. exact (MK_COMB (@lem5045404) (@lem5045403 B _64827 _64828)). Qed.
Lemma lem5045407 (a : Prop) : (term109 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5045408 {B : Type'} (t' : B -> Prop) (_64827 : B) : (term253 B t' _64827) = (t' _64827).
Proof. exact (@lem5045407 (t' _64827)). Qed.
Lemma lem5045409 {B : Type'} (_64828 : B) (t' : B -> Prop) (_64827 : B) : (term305 B _64828 t' _64827) = (term306 B _64828 t' _64827).
Proof. exact (MK_COMB (@lem5045405 B _64827 _64828) (@lem5045408 B t' _64827)). Qed.
Lemma lem5045410 {B : Type'} (_64828 : B) (t' : B -> Prop) (_64827 : B) : (term304 B _64828 t' _64827) = (term306 B _64828 t' _64827).
Proof. exact (TRANS (@lem5045400 B _64828 t' _64827) (@lem5045409 B _64828 t' _64827)). Qed.
Lemma lem5045411 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5045412 {B : Type'} (_64828 : B) (t' : B -> Prop) (_64827 : B) : (term307 B _64828 t' _64827) = (term308 B _64828 t' _64827).
Proof. exact (MK_COMB (@lem5045411) (@lem5045410 B _64828 t' _64827)). Qed.
Lemma lem5045413 {B : Type'} (t' : B -> Prop) (_64828 : B) : (t' _64828) = (t' _64828).
Proof. exact (eq_refl (t' _64828)). Qed.
Lemma lem5045414 {B : Type'} (_64827 : B) (t' : B -> Prop) (_64828 : B) : (term303 B _64827 t' _64828) = (term309 B _64827 t' _64828).
Proof. exact (MK_COMB (@lem5045412 B _64828 t' _64827) (@lem5045413 B t' _64828)). Qed.
Lemma lem5045415 {B : Type'} (_64827 : B) (t' : B -> Prop) (_64828 : B) : (term296 B _64828 t' _64827) = (term309 B _64827 t' _64828).
Proof. exact (TRANS (@lem5045397 B _64827 t' _64828) (@lem5045414 B _64827 t' _64828)). Qed.
Lemma lem5045417 {A B : Type'} (x' : B -> A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term166 A B u f s x') (h2 : term89 A B u t s t' f) (h3 : term216 B t t' x) : term330 A B t' f x' x.
Proof. exact (conj (@lem5044968 A B x' u s f t t' x h1 h2 h3) (@lem5045307 A B x' u s f t t' x h1 h2 h3)). Qed.
Lemma lem5045419 {B : Type'} (_64827 : B) (t' : B -> Prop) (_64828 : B) : term309 B _64827 t' _64828.
Proof. exact (EQ_MP (@lem5045415 B _64827 t' _64828) (@lem5045394 B _64828 t' _64827)). Qed.
Lemma lem5045420 {B : Type'} (_64827 : B) (t' : B -> Prop) (_64828 : B) : term309 B _64827 t' _64828.
Proof. exact (@lem5045419 B _64827 t' _64828). Qed.
Lemma lem5045421 {A B : Type'} (f : A -> B) (x' : B -> A) (t' : B -> Prop) (x : B) : term331 A B f x' t' x.
Proof. exact (@lem5045420 B (term219 A B f x' x) t' x). Qed.
Lemma lem5045424 {A B : Type'} (x' : B -> A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term166 A B u f s x') (h2 : term89 A B u t s t' f) (h3 : term216 B t t' x) : t' x.
Proof. exact (@lem5045421 A B f x' t' x (@lem5045417 A B x' u s f t t' x h1 h2 h3)). Qed.
Lemma lem5045425 {A B : Type'} (x' : B -> A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term166 A B u f s x') (h2 : term89 A B u t s t' f) (h3 : term216 B t t' x) : term246 B t' x.
Proof. exact (fun h0 : term132 B t' x => @lem5045424 A B x' u s f t t' x h1 h2 h3). Qed.
Lemma lem5045427 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5045428 {B : Type'} (t' : B -> Prop) (x : B) : (term246 B t' x) = (t' x).
Proof. exact (@lem5045427 (t' x)). Qed.
Lemma lem5045429 {A B : Type'} (x' : B -> A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term166 A B u f s x') (h2 : term89 A B u t s t' f) (h3 : term216 B t t' x) : t' x.
Proof. exact (EQ_MP (@lem5045428 B t' x) (@lem5045425 A B x' u s f t t' x h1 h2 h3)). Qed.
Lemma lem5045432 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5045434 {B : Type'} (t' : B -> Prop) (x : B) : (term132 B t' x) = (term332 B t' x).
Proof. exact (@lem5045432 (t' x)). Qed.
Lemma lem5045437 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term216 B t t' x) : term332 B t' x.
Proof. exact (EQ_MP (@lem5045434 B t' x) (@lem5044522 B t t' x h1)). Qed.
Lemma lem5045440 {A B : Type'} (x' : B -> A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term166 A B u f s x') (h2 : term89 A B u t s t' f) (h3 : term216 B t t' x) : False.
Proof. exact (@lem5045437 B t t' x h3 (@lem5045429 A B x' u s f t t' x h1 h2 h3)). Qed.
Lemma lem5045441 {A B : Type'} (x' : B -> A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term166 A B u f s x') (h2 : term89 A B u t s t' f) (h3 : term216 B t t' x) : term333.
Proof. exact (fun h0 : ~ False => @lem5045440 A B x' u s f t t' x h1 h2 h3). Qed.
Lemma lem5045443 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5045444 : term333 = False.
Proof. exact (@lem5045443 False). Qed.
Lemma lem5045445 {A B : Type'} (x' : B -> A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term166 A B u f s x') (h2 : term89 A B u t s t' f) (h3 : term216 B t t' x) : False.
Proof. exact (EQ_MP (@lem5045444) (@lem5045441 A B x' u s f t t' x h1 h2 h3)). Qed.
Lemma lem5045458 {B : Type'} (t' : B -> Prop) : t' = t'.
Proof. exact (eq_refl t'). Qed.
Lemma lem5045459 {B : Type'} (_64839 : B) (_64840 : B) (h1 : _64839 = _64840) : _64839 = _64840.
Proof. exact (h1). Qed.
Lemma lem5045460 {B : Type'} (t' : B -> Prop) (_64839 : B) (_64840 : B) (h1 : _64839 = _64840) : (t' _64839) = (t' _64840).
Proof. exact (MK_COMB (@lem5045458 B t') (@lem5045459 B _64839 _64840 h1)). Qed.
Lemma lem5045462 (b : Prop) (a : Prop) : term239 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem5045463 {B : Type'} (_64840 : B) (t' : B -> Prop) (_64839 : B) : term240 B _64840 t' _64839.
Proof. exact (@lem5045462 (t' _64840) (t' _64839)). Qed.
Lemma lem5045464 {B : Type'} (t' : B -> Prop) (_64839 : B) (_64840 : B) (h1 : _64839 = _64840) : term241 B _64840 t' _64839.
Proof. exact (@lem5045463 B _64840 t' _64839 (@lem5045460 B t' _64839 _64840 h1)). Qed.
Lemma lem5045465 {B : Type'} (_64840 : B) (t' : B -> Prop) (_64839 : B) : term242 B _64840 t' _64839.
Proof. exact (fun h0 : _64839 = _64840 => @lem5045464 B t' _64839 _64840 h0). Qed.
Lemma lem5045467 (a : Prop) (b : Prop) : (a -> b) = (term243 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem5045468 {B : Type'} (_64840 : B) (t' : B -> Prop) (_64839 : B) : (term242 B _64840 t' _64839) = (term244 B _64840 t' _64839).
Proof. exact (@lem5045467 (_64839 = _64840) (term241 B _64840 t' _64839)). Qed.
Lemma lem5045469 {B : Type'} (_64840 : B) (t' : B -> Prop) (_64839 : B) : term244 B _64840 t' _64839.
Proof. exact (EQ_MP (@lem5045468 B _64840 t' _64839) (@lem5045465 B _64840 t' _64839)). Qed.
Lemma lem5045470 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5045471 {B : Type'} (_64841 : B) (_64842 : B) (h1 : _64841 = _64842) : _64841 = _64842.
Proof. exact (h1). Qed.
Lemma lem5045472 {B : Type'} (t : B -> Prop) (_64841 : B) (_64842 : B) (h1 : _64841 = _64842) : (t _64841) = (t _64842).
Proof. exact (MK_COMB (@lem5045470 B t) (@lem5045471 B _64841 _64842 h1)). Qed.
Lemma lem5045474 (b : Prop) (a : Prop) : term239 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem5045475 {B : Type'} (_64842 : B) (t : B -> Prop) (_64841 : B) : term240 B _64842 t _64841.
Proof. exact (@lem5045474 (t _64842) (t _64841)). Qed.
Lemma lem5045476 {B : Type'} (t : B -> Prop) (_64841 : B) (_64842 : B) (h1 : _64841 = _64842) : term241 B _64842 t _64841.
Proof. exact (@lem5045475 B _64842 t _64841 (@lem5045472 B t _64841 _64842 h1)). Qed.
Lemma lem5045477 {B : Type'} (_64842 : B) (t : B -> Prop) (_64841 : B) : term242 B _64842 t _64841.
Proof. exact (fun h0 : _64841 = _64842 => @lem5045476 B t _64841 _64842 h0). Qed.
Lemma lem5045479 (a : Prop) (b : Prop) : (a -> b) = (term243 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem5045480 {B : Type'} (_64842 : B) (t : B -> Prop) (_64841 : B) : (term242 B _64842 t _64841) = (term244 B _64842 t _64841).
Proof. exact (@lem5045479 (_64841 = _64842) (term241 B _64842 t _64841)). Qed.
Lemma lem5045481 {B : Type'} (_64842 : B) (t : B -> Prop) (_64841 : B) : term244 B _64842 t _64841.
Proof. exact (EQ_MP (@lem5045480 B _64842 t _64841) (@lem5045477 B _64842 t _64841)). Qed.
Lemma lem5045511 {B : Type'} (x : B) (y : B) (z : B) : term245 B x y z.
Proof. exact (@lem21385 B x y z). Qed.
Lemma lem5045515 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term217 B t t' x) : t' x.
Proof. exact (proj2 (@lem5044230 B t t' x h1)). Qed.
Lemma lem5045516 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term217 B t t' x) : term246 B t' x.
Proof. exact (fun h0 : term132 B t' x => @lem5045515 B t t' x h1). Qed.
Lemma lem5045518 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5045519 {B : Type'} (t' : B -> Prop) (x : B) : (term246 B t' x) = (t' x).
Proof. exact (@lem5045518 (t' x)). Qed.
Lemma lem5045520 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term217 B t t' x) : t' x.
Proof. exact (EQ_MP (@lem5045519 B t' x) (@lem5045516 B t t' x h1)). Qed.
Lemma lem5045526 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5045527 {B : Type'} (u : B -> Prop) (t' : B -> Prop) (_64822 : B) : (term170 B t' u _64822) = (term248 B u t' _64822).
Proof. exact (@lem5045526 (u _64822) (term132 B t' _64822)). Qed.
Lemma lem5045533 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5045534 {B : Type'} (u : B -> Prop) (t' : B -> Prop) (_64822 : B) : (term249 B t' u _64822) = (term250 B u t' _64822).
Proof. exact (MK_COMB (@lem5045533) (@lem5045527 B u t' _64822)). Qed.
Lemma lem5045540 {B : Type'} (u : B -> Prop) (t' : B -> Prop) (_64822 : B) : (term248 B u t' _64822) = (term248 B u t' _64822).
Proof. exact (eq_refl (term248 B u t' _64822)). Qed.
Lemma lem5045541 {B : Type'} (u : B -> Prop) (t' : B -> Prop) (_64822 : B) : ((term170 B t' u _64822) = (term248 B u t' _64822)) = ((term248 B u t' _64822) = (term248 B u t' _64822)).
Proof. exact (MK_COMB (@lem5045534 B u t' _64822) (@lem5045540 B u t' _64822)). Qed.
Lemma lem5045543 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5045544 (x : Prop) : (x = x) = True.
Proof. exact (@lem5045543 Prop x). Qed.
Lemma lem5045545 {B : Type'} (u : B -> Prop) (t' : B -> Prop) (_64822 : B) : ((term248 B u t' _64822) = (term248 B u t' _64822)) = True.
Proof. exact (@lem5045544 (term248 B u t' _64822)). Qed.
Lemma lem5045546 {B : Type'} (u : B -> Prop) (t' : B -> Prop) (_64822 : B) : ((term170 B t' u _64822) = (term248 B u t' _64822)) = True.
Proof. exact (TRANS (@lem5045541 B u t' _64822) (@lem5045545 B u t' _64822)). Qed.
Lemma lem5045547 {B : Type'} (u : B -> Prop) (t' : B -> Prop) (_64822 : B) : True = ((term170 B t' u _64822) = (term248 B u t' _64822)).
Proof. exact (SYM (@lem5045546 B u t' _64822)). Qed.
Lemma lem5045548 {B : Type'} (u : B -> Prop) (t' : B -> Prop) (_64822 : B) : (term170 B t' u _64822) = (term248 B u t' _64822).
Proof. exact (EQ_MP (@lem5045547 B u t' _64822) (@lem0)). Qed.
Lemma lem5045549 {A B : Type'} (_64822 : B) (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (h1 : term89 A B u t s t' f) : term248 B u t' _64822.
Proof. exact (EQ_MP (@lem5045548 B u t' _64822) (@lem5044590 A B _64822 u t s t' f h1)). Qed.
Lemma lem5045551 (b : Prop) (a : Prop) : (a \/ b) = (term251 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5045552 {B : Type'} (t' : B -> Prop) (u : B -> Prop) (_64822 : B) : (term248 B u t' _64822) = (term252 B t' u _64822).
Proof. exact (@lem5045551 (term132 B t' _64822) (u _64822)). Qed.
Lemma lem5045554 (a : Prop) : (term109 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5045555 {B : Type'} (t' : B -> Prop) (_64822 : B) : (term253 B t' _64822) = (t' _64822).
Proof. exact (@lem5045554 (t' _64822)). Qed.
Lemma lem5045556 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5045557 {B : Type'} (t' : B -> Prop) (_64822 : B) : (term254 B t' _64822) = (term39 B t' _64822).
Proof. exact (MK_COMB (@lem5045556) (@lem5045555 B t' _64822)). Qed.
Lemma lem5045558 {B : Type'} (u : B -> Prop) (_64822 : B) : (u _64822) = (u _64822).
Proof. exact (eq_refl (u _64822)). Qed.
Lemma lem5045559 {B : Type'} (t' : B -> Prop) (u : B -> Prop) (_64822 : B) : (term252 B t' u _64822) = (term55 B t' u _64822).
Proof. exact (MK_COMB (@lem5045557 B t' _64822) (@lem5045558 B u _64822)). Qed.
Lemma lem5045560 {B : Type'} (t' : B -> Prop) (u : B -> Prop) (_64822 : B) : (term248 B u t' _64822) = (term55 B t' u _64822).
Proof. exact (TRANS (@lem5045552 B t' u _64822) (@lem5045559 B t' u _64822)). Qed.
Lemma lem5045563 {A B : Type'} (_64822 : B) (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (h1 : term89 A B u t s t' f) : term55 B t' u _64822.
Proof. exact (EQ_MP (@lem5045560 B t' u _64822) (@lem5045549 A B _64822 u t s t' f h1)). Qed.
Lemma lem5045564 {A B : Type'} (_64822 : B) (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (h1 : term89 A B u t s t' f) : term55 B t' u _64822.
Proof. exact (@lem5045563 A B _64822 u t s t' f h1). Qed.
Lemma lem5045565 {A B : Type'} (x : B) (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (h1 : term89 A B u t s t' f) : term55 B t' u x.
Proof. exact (@lem5045564 A B x u t s t' f h1). Qed.
Lemma lem5045568 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term89 A B u t s t' f) (h2 : term217 B t t' x) : u x.
Proof. exact (@lem5045565 A B x u t s t' f h1 (@lem5045520 B t t' x h2)). Qed.
Lemma lem5045569 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term89 A B u t s t' f) (h2 : term217 B t t' x) : term246 B u x.
Proof. exact (fun h0 : term132 B u x => @lem5045568 A B u s f t t' x h1 h2). Qed.
Lemma lem5045571 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5045572 {B : Type'} (u : B -> Prop) (x : B) : (term246 B u x) = (u x).
Proof. exact (@lem5045571 (u x)). Qed.
Lemma lem5045573 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term89 A B u t s t' f) (h2 : term217 B t t' x) : u x.
Proof. exact (EQ_MP (@lem5045572 B u x) (@lem5045569 A B u s f t t' x h1 h2)). Qed.
Lemma lem5045579 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5045580 {A B : Type'} (f : A -> B) (x' : B -> A) (u : B -> Prop) (_64820 : B) : (term236 A B u f x' _64820) = (term255 A B f x' u _64820).
Proof. exact (@lem5045579 (_64820 = (term219 A B f x' _64820)) (term132 B u _64820)). Qed.
Lemma lem5045588 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5045589 {A B : Type'} (f : A -> B) (x' : B -> A) (u : B -> Prop) (_64820 : B) : (term256 A B u f x' _64820) = (term257 A B f x' u _64820).
Proof. exact (MK_COMB (@lem5045588) (@lem5045580 A B f x' u _64820)). Qed.
Lemma lem5045597 {A B : Type'} (f : A -> B) (x' : B -> A) (u : B -> Prop) (_64820 : B) : (term255 A B f x' u _64820) = (term255 A B f x' u _64820).
Proof. exact (eq_refl (term255 A B f x' u _64820)). Qed.
Lemma lem5045598 {A B : Type'} (f : A -> B) (x' : B -> A) (u : B -> Prop) (_64820 : B) : ((term236 A B u f x' _64820) = (term255 A B f x' u _64820)) = ((term255 A B f x' u _64820) = (term255 A B f x' u _64820)).
Proof. exact (MK_COMB (@lem5045589 A B f x' u _64820) (@lem5045597 A B f x' u _64820)). Qed.
Lemma lem5045600 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5045601 (x : Prop) : (x = x) = True.
Proof. exact (@lem5045600 Prop x). Qed.
Lemma lem5045602 {A B : Type'} (f : A -> B) (x' : B -> A) (u : B -> Prop) (_64820 : B) : ((term255 A B f x' u _64820) = (term255 A B f x' u _64820)) = True.
Proof. exact (@lem5045601 (term255 A B f x' u _64820)). Qed.
Lemma lem5045603 {A B : Type'} (f : A -> B) (x' : B -> A) (u : B -> Prop) (_64820 : B) : ((term236 A B u f x' _64820) = (term255 A B f x' u _64820)) = True.
Proof. exact (TRANS (@lem5045598 A B f x' u _64820) (@lem5045602 A B f x' u _64820)). Qed.
Lemma lem5045604 {A B : Type'} (f : A -> B) (x' : B -> A) (u : B -> Prop) (_64820 : B) : True = ((term236 A B u f x' _64820) = (term255 A B f x' u _64820)).
Proof. exact (SYM (@lem5045603 A B f x' u _64820)). Qed.
Lemma lem5045605 {A B : Type'} (f : A -> B) (x' : B -> A) (u : B -> Prop) (_64820 : B) : (term236 A B u f x' _64820) = (term255 A B f x' u _64820).
Proof. exact (EQ_MP (@lem5045604 A B f x' u _64820) (@lem0)). Qed.
Lemma lem5045606 {A B : Type'} (_64820 : B) (u : B -> Prop) (f : A -> B) (s : A -> Prop) (x' : B -> A) (h1 : term166 A B u f s x') : term255 A B f x' u _64820.
Proof. exact (EQ_MP (@lem5045605 A B f x' u _64820) (@lem5044644 A B _64820 u f s x' h1)). Qed.
Lemma lem5045608 (b : Prop) (a : Prop) : (a \/ b) = (term251 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5045609 {A B : Type'} (u : B -> Prop) (f : A -> B) (x' : B -> A) (_64820 : B) : (term255 A B f x' u _64820) = (term258 A B u f x' _64820).
Proof. exact (@lem5045608 (term132 B u _64820) (_64820 = (term219 A B f x' _64820))). Qed.
Lemma lem5045611 (a : Prop) : (term109 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5045612 {B : Type'} (u : B -> Prop) (_64820 : B) : (term253 B u _64820) = (u _64820).
Proof. exact (@lem5045611 (u _64820)). Qed.
Lemma lem5045613 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5045614 {B : Type'} (u : B -> Prop) (_64820 : B) : (term254 B u _64820) = (term39 B u _64820).
Proof. exact (MK_COMB (@lem5045613) (@lem5045612 B u _64820)). Qed.
Lemma lem5045615 {A B : Type'} (f : A -> B) (x' : B -> A) (_64820 : B) : (_64820 = (term219 A B f x' _64820)) = (_64820 = (term219 A B f x' _64820)).
Proof. exact (eq_refl (_64820 = (term219 A B f x' _64820))). Qed.
Lemma lem5045616 {A B : Type'} (u : B -> Prop) (f : A -> B) (x' : B -> A) (_64820 : B) : (term258 A B u f x' _64820) = (term259 A B u f x' _64820).
Proof. exact (MK_COMB (@lem5045614 B u _64820) (@lem5045615 A B f x' _64820)). Qed.
Lemma lem5045617 {A B : Type'} (u : B -> Prop) (f : A -> B) (x' : B -> A) (_64820 : B) : (term255 A B f x' u _64820) = (term259 A B u f x' _64820).
Proof. exact (TRANS (@lem5045609 A B u f x' _64820) (@lem5045616 A B u f x' _64820)). Qed.
Lemma lem5045620 {A B : Type'} (_64820 : B) (u : B -> Prop) (f : A -> B) (s : A -> Prop) (x' : B -> A) (h1 : term166 A B u f s x') : term259 A B u f x' _64820.
Proof. exact (EQ_MP (@lem5045617 A B u f x' _64820) (@lem5045606 A B _64820 u f s x' h1)). Qed.
Lemma lem5045621 {A B : Type'} (_64820 : B) (u : B -> Prop) (f : A -> B) (s : A -> Prop) (x' : B -> A) (h1 : term166 A B u f s x') : term259 A B u f x' _64820.
Proof. exact (@lem5045620 A B _64820 u f s x' h1). Qed.
Lemma lem5045622 {A B : Type'} (x : B) (u : B -> Prop) (f : A -> B) (s : A -> Prop) (x' : B -> A) (h1 : term166 A B u f s x') : term259 A B u f x' x.
Proof. exact (@lem5045621 A B x u f s x' h1). Qed.
Lemma lem5045625 {A B : Type'} (x' : B -> A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term166 A B u f s x') (h2 : term89 A B u t s t' f) (h3 : term217 B t t' x) : x = (term219 A B f x' x).
Proof. exact (@lem5045622 A B x u f s x' h1 (@lem5045573 A B u s f t t' x h2 h3)). Qed.
Lemma lem5045626 {A B : Type'} (x' : B -> A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term166 A B u f s x') (h2 : term89 A B u t s t' f) (h3 : term217 B t t' x) : term260 A B f x' x.
Proof. exact (fun h0 : term261 A B f x' x => @lem5045625 A B x' u s f t t' x h1 h2 h3). Qed.
Lemma lem5045628 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5045629 {A B : Type'} (f : A -> B) (x' : B -> A) (x : B) : (term260 A B f x' x) = (x = (term219 A B f x' x)).
Proof. exact (@lem5045628 (x = (term219 A B f x' x))). Qed.
Lemma lem5045630 {A B : Type'} (x' : B -> A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term166 A B u f s x') (h2 : term89 A B u t s t' f) (h3 : term217 B t t' x) : x = (term219 A B f x' x).
Proof. exact (EQ_MP (@lem5045629 A B f x' x) (@lem5045626 A B x' u s f t t' x h1 h2 h3)). Qed.
Lemma lem5045632 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem5045633 {B : Type'} (x : B) : x = x.
Proof. exact (@lem5045632 B x). Qed.
Lemma lem5045634 {B : Type'} (x : B) : term262 B x.
Proof. exact (fun h0 : term263 B x => @lem5045633 B x). Qed.
Lemma lem5045636 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5045637 {B : Type'} (x : B) : (term262 B x) = (x = x).
Proof. exact (@lem5045636 (x = x)). Qed.
Lemma lem5045638 {B : Type'} (x : B) : x = x.
Proof. exact (EQ_MP (@lem5045637 B x) (@lem5045634 B x)). Qed.
Lemma lem5045656 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5045657 {B : Type'} (y : B) (x : B) (z : B) : (term264 B x y z) = (term265 B y x z).
Proof. exact (@lem5045656 (y = z) (term266 B x z)). Qed.
Lemma lem5045667 {B : Type'} (x : B) (y : B) : (term267 B x y) = (term267 B x y).
Proof. exact (eq_refl (term267 B x y)). Qed.
Lemma lem5045668 {B : Type'} (y : B) (x : B) (z : B) : (term245 B x y z) = (term268 B y x z).
Proof. exact (MK_COMB (@lem5045667 B x y) (@lem5045657 B y x z)). Qed.
Lemma lem5045672 (q : Prop) (p : Prop) (r : Prop) : (term11 p q r) = (term11 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5045673 {B : Type'} (y : B) (x : B) (z : B) : (term268 B y x z) = (term269 B y x z).
Proof. exact (@lem5045672 (y = z) (term266 B x y) (term266 B x z)). Qed.
Lemma lem5045695 {B : Type'} (y : B) (x : B) (z : B) : (term245 B x y z) = (term269 B y x z).
Proof. exact (TRANS (@lem5045668 B y x z) (@lem5045673 B y x z)). Qed.
Lemma lem5045696 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5045697 {B : Type'} (y : B) (x : B) (z : B) : (term270 B x y z) = (term271 B y x z).
Proof. exact (MK_COMB (@lem5045696) (@lem5045695 B y x z)). Qed.
Lemma lem5045719 {B : Type'} (y : B) (x : B) (z : B) : (term269 B y x z) = (term269 B y x z).
Proof. exact (eq_refl (term269 B y x z)). Qed.
Lemma lem5045720 {B : Type'} (y : B) (x : B) (z : B) : ((term245 B x y z) = (term269 B y x z)) = ((term269 B y x z) = (term269 B y x z)).
Proof. exact (MK_COMB (@lem5045697 B y x z) (@lem5045719 B y x z)). Qed.
Lemma lem5045722 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5045723 (x : Prop) : (x = x) = True.
Proof. exact (@lem5045722 Prop x). Qed.
Lemma lem5045724 {B : Type'} (y : B) (x : B) (z : B) : ((term269 B y x z) = (term269 B y x z)) = True.
Proof. exact (@lem5045723 (term269 B y x z)). Qed.
Lemma lem5045725 {B : Type'} (y : B) (x : B) (z : B) : ((term245 B x y z) = (term269 B y x z)) = True.
Proof. exact (TRANS (@lem5045720 B y x z) (@lem5045724 B y x z)). Qed.
Lemma lem5045726 {B : Type'} (y : B) (x : B) (z : B) : True = ((term245 B x y z) = (term269 B y x z)).
Proof. exact (SYM (@lem5045725 B y x z)). Qed.
Lemma lem5045727 {B : Type'} (y : B) (x : B) (z : B) : (term245 B x y z) = (term269 B y x z).
Proof. exact (EQ_MP (@lem5045726 B y x z) (@lem0)). Qed.
Lemma lem5045728 {B : Type'} (y : B) (x : B) (z : B) : term269 B y x z.
Proof. exact (EQ_MP (@lem5045727 B y x z) (@lem5045511 B x y z)). Qed.
Lemma lem5045730 (b : Prop) (a : Prop) : (a \/ b) = (term251 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5045731 {B : Type'} (x : B) (y : B) (z : B) : (term269 B y x z) = (term272 B x y z).
Proof. exact (@lem5045730 (term273 B y x z) (y = z)). Qed.
Lemma lem5045733 (a : Prop) (b : Prop) : (term274 a b) = (term275 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5045734 {B : Type'} (y : B) (x : B) (z : B) : (term276 B y x z) = (term277 B y x z).
Proof. exact (@lem5045733 (term266 B x y) (term266 B x z)). Qed.
Lemma lem5045736 (a : Prop) : (term109 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5045737 {B : Type'} (x : B) (y : B) : (term278 B x y) = (x = y).
Proof. exact (@lem5045736 (x = y)). Qed.
Lemma lem5045738 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5045739 {B : Type'} (x : B) (y : B) : (term279 B x y) = (term280 B x y).
Proof. exact (MK_COMB (@lem5045738) (@lem5045737 B x y)). Qed.
Lemma lem5045741 (a : Prop) : (term109 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5045742 {B : Type'} (x : B) (z : B) : (term278 B x z) = (x = z).
Proof. exact (@lem5045741 (x = z)). Qed.
Lemma lem5045743 {B : Type'} (y : B) (x : B) (z : B) : (term277 B y x z) = (term281 B y x z).
Proof. exact (MK_COMB (@lem5045739 B x y) (@lem5045742 B x z)). Qed.
Lemma lem5045744 {B : Type'} (y : B) (x : B) (z : B) : (term276 B y x z) = (term281 B y x z).
Proof. exact (TRANS (@lem5045734 B y x z) (@lem5045743 B y x z)). Qed.
Lemma lem5045745 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5045746 {B : Type'} (y : B) (x : B) (z : B) : (term282 B y x z) = (term283 B y x z).
Proof. exact (MK_COMB (@lem5045745) (@lem5045744 B y x z)). Qed.
Lemma lem5045747 {B : Type'} (y : B) (z : B) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem5045748 {B : Type'} (x : B) (y : B) (z : B) : (term272 B x y z) = (term284 B x y z).
Proof. exact (MK_COMB (@lem5045746 B y x z) (@lem5045747 B y z)). Qed.
Lemma lem5045749 {B : Type'} (x : B) (y : B) (z : B) : (term269 B y x z) = (term284 B x y z).
Proof. exact (TRANS (@lem5045731 B x y z) (@lem5045748 B x y z)). Qed.
Lemma lem5045751 {A B : Type'} (x' : B -> A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term166 A B u f s x') (h2 : term89 A B u t s t' f) (h3 : term217 B t t' x) : term285 A B f x' x.
Proof. exact (conj (@lem5045630 A B x' u s f t t' x h1 h2 h3) (@lem5045638 B x)). Qed.
Lemma lem5045753 {B : Type'} (x : B) (y : B) (z : B) : term284 B x y z.
Proof. exact (EQ_MP (@lem5045749 B x y z) (@lem5045728 B y x z)). Qed.
Lemma lem5045754 {B : Type'} (x : B) (y : B) (z : B) : term284 B x y z.
Proof. exact (@lem5045753 B x y z). Qed.
Lemma lem5045755 {A B : Type'} (f : A -> B) (x' : B -> A) (x : B) : term286 A B f x' x.
Proof. exact (@lem5045754 B x (term219 A B f x' x) x). Qed.
Lemma lem5045758 {A B : Type'} (x' : B -> A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term166 A B u f s x') (h2 : term89 A B u t s t' f) (h3 : term217 B t t' x) : (term219 A B f x' x) = x.
Proof. exact (@lem5045755 A B f x' x (@lem5045751 A B x' u s f t t' x h1 h2 h3)). Qed.
Lemma lem5045759 {A B : Type'} (x' : B -> A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term166 A B u f s x') (h2 : term89 A B u t s t' f) (h3 : term217 B t t' x) : term287 A B f x' x.
Proof. exact (fun h0 : term288 A B f x' x => @lem5045758 A B x' u s f t t' x h1 h2 h3). Qed.
Lemma lem5045761 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5045762 {A B : Type'} (f : A -> B) (x' : B -> A) (x : B) : (term287 A B f x' x) = ((term219 A B f x' x) = x).
Proof. exact (@lem5045761 ((term219 A B f x' x) = x)). Qed.
Lemma lem5045763 {A B : Type'} (x' : B -> A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term166 A B u f s x') (h2 : term89 A B u t s t' f) (h3 : term217 B t t' x) : (term219 A B f x' x) = x.
Proof. exact (EQ_MP (@lem5045762 A B f x' x) (@lem5045759 A B x' u s f t t' x h1 h2 h3)). Qed.
Lemma lem5045765 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term217 B t t' x) : t' x.
Proof. exact (proj2 (@lem5044230 B t t' x h1)). Qed.
Lemma lem5045766 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term217 B t t' x) : term246 B t' x.
Proof. exact (fun h0 : term132 B t' x => @lem5045765 B t t' x h1). Qed.
Lemma lem5045768 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5045769 {B : Type'} (t' : B -> Prop) (x : B) : (term246 B t' x) = (t' x).
Proof. exact (@lem5045768 (t' x)). Qed.
Lemma lem5045770 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term217 B t t' x) : t' x.
Proof. exact (EQ_MP (@lem5045769 B t' x) (@lem5045766 B t t' x h1)). Qed.
Lemma lem5045772 {A B : Type'} (_64822 : B) (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (h1 : term89 A B u t s t' f) : term55 B t' u _64822.
Proof. exact (EQ_MP (@lem5045560 B t' u _64822) (@lem5045549 A B _64822 u t s t' f h1)). Qed.
Lemma lem5045773 {A B : Type'} (_64822 : B) (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (h1 : term89 A B u t s t' f) : term55 B t' u _64822.
Proof. exact (@lem5045772 A B _64822 u t s t' f h1). Qed.
Lemma lem5045774 {A B : Type'} (x : B) (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (h1 : term89 A B u t s t' f) : term55 B t' u x.
Proof. exact (@lem5045773 A B x u t s t' f h1). Qed.
Lemma lem5045777 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term89 A B u t s t' f) (h2 : term217 B t t' x) : u x.
Proof. exact (@lem5045774 A B x u t s t' f h1 (@lem5045770 B t t' x h2)). Qed.
Lemma lem5045778 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term89 A B u t s t' f) (h2 : term217 B t t' x) : term246 B u x.
Proof. exact (fun h0 : term132 B u x => @lem5045777 A B u s f t t' x h1 h2). Qed.
Lemma lem5045780 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5045781 {B : Type'} (u : B -> Prop) (x : B) : (term246 B u x) = (u x).
Proof. exact (@lem5045780 (u x)). Qed.
Lemma lem5045782 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term89 A B u t s t' f) (h2 : term217 B t t' x) : u x.
Proof. exact (EQ_MP (@lem5045781 B u x) (@lem5045778 A B u s f t t' x h1 h2)). Qed.
Lemma lem5045788 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5045789 {A B : Type'} (s : A -> Prop) (x' : B -> A) (u : B -> Prop) (_64820 : B) : (term237 A B u s x' _64820) = (term289 A B s x' u _64820).
Proof. exact (@lem5045788 (term220 A B s x' _64820) (term132 B u _64820)). Qed.
Lemma lem5045795 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5045796 {A B : Type'} (s : A -> Prop) (x' : B -> A) (u : B -> Prop) (_64820 : B) : (term290 A B u s x' _64820) = (term291 A B s x' u _64820).
Proof. exact (MK_COMB (@lem5045795) (@lem5045789 A B s x' u _64820)). Qed.
Lemma lem5045802 {A B : Type'} (s : A -> Prop) (x' : B -> A) (u : B -> Prop) (_64820 : B) : (term289 A B s x' u _64820) = (term289 A B s x' u _64820).
Proof. exact (eq_refl (term289 A B s x' u _64820)). Qed.
Lemma lem5045803 {A B : Type'} (s : A -> Prop) (x' : B -> A) (u : B -> Prop) (_64820 : B) : ((term237 A B u s x' _64820) = (term289 A B s x' u _64820)) = ((term289 A B s x' u _64820) = (term289 A B s x' u _64820)).
Proof. exact (MK_COMB (@lem5045796 A B s x' u _64820) (@lem5045802 A B s x' u _64820)). Qed.
Lemma lem5045805 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5045806 (x : Prop) : (x = x) = True.
Proof. exact (@lem5045805 Prop x). Qed.
Lemma lem5045807 {A B : Type'} (s : A -> Prop) (x' : B -> A) (u : B -> Prop) (_64820 : B) : ((term289 A B s x' u _64820) = (term289 A B s x' u _64820)) = True.
Proof. exact (@lem5045806 (term289 A B s x' u _64820)). Qed.
Lemma lem5045808 {A B : Type'} (s : A -> Prop) (x' : B -> A) (u : B -> Prop) (_64820 : B) : ((term237 A B u s x' _64820) = (term289 A B s x' u _64820)) = True.
Proof. exact (TRANS (@lem5045803 A B s x' u _64820) (@lem5045807 A B s x' u _64820)). Qed.
Lemma lem5045809 {A B : Type'} (s : A -> Prop) (x' : B -> A) (u : B -> Prop) (_64820 : B) : True = ((term237 A B u s x' _64820) = (term289 A B s x' u _64820)).
Proof. exact (SYM (@lem5045808 A B s x' u _64820)). Qed.
Lemma lem5045810 {A B : Type'} (s : A -> Prop) (x' : B -> A) (u : B -> Prop) (_64820 : B) : (term237 A B u s x' _64820) = (term289 A B s x' u _64820).
Proof. exact (EQ_MP (@lem5045809 A B s x' u _64820) (@lem0)). Qed.
Lemma lem5045811 {A B : Type'} (_64820 : B) (u : B -> Prop) (f : A -> B) (s : A -> Prop) (x' : B -> A) (h1 : term166 A B u f s x') : term289 A B s x' u _64820.
Proof. exact (EQ_MP (@lem5045810 A B s x' u _64820) (@lem5044650 A B _64820 u f s x' h1)). Qed.
Lemma lem5045813 (b : Prop) (a : Prop) : (a \/ b) = (term251 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5045814 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (x' : B -> A) (_64820 : B) : (term289 A B s x' u _64820) = (term292 A B u s x' _64820).
Proof. exact (@lem5045813 (term132 B u _64820) (term220 A B s x' _64820)). Qed.
Lemma lem5045816 (a : Prop) : (term109 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5045817 {B : Type'} (u : B -> Prop) (_64820 : B) : (term253 B u _64820) = (u _64820).
Proof. exact (@lem5045816 (u _64820)). Qed.
Lemma lem5045818 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5045819 {B : Type'} (u : B -> Prop) (_64820 : B) : (term254 B u _64820) = (term39 B u _64820).
Proof. exact (MK_COMB (@lem5045818) (@lem5045817 B u _64820)). Qed.
Lemma lem5045820 {A B : Type'} (s : A -> Prop) (x' : B -> A) (_64820 : B) : (term220 A B s x' _64820) = (term220 A B s x' _64820).
Proof. exact (eq_refl (term220 A B s x' _64820)). Qed.
Lemma lem5045821 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (x' : B -> A) (_64820 : B) : (term292 A B u s x' _64820) = (term293 A B u s x' _64820).
Proof. exact (MK_COMB (@lem5045819 B u _64820) (@lem5045820 A B s x' _64820)). Qed.
Lemma lem5045822 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (x' : B -> A) (_64820 : B) : (term289 A B s x' u _64820) = (term293 A B u s x' _64820).
Proof. exact (TRANS (@lem5045814 A B u s x' _64820) (@lem5045821 A B u s x' _64820)). Qed.
Lemma lem5045825 {A B : Type'} (_64820 : B) (u : B -> Prop) (f : A -> B) (s : A -> Prop) (x' : B -> A) (h1 : term166 A B u f s x') : term293 A B u s x' _64820.
Proof. exact (EQ_MP (@lem5045822 A B u s x' _64820) (@lem5045811 A B _64820 u f s x' h1)). Qed.
Lemma lem5045826 {A B : Type'} (_64820 : B) (u : B -> Prop) (f : A -> B) (s : A -> Prop) (x' : B -> A) (h1 : term166 A B u f s x') : term293 A B u s x' _64820.
Proof. exact (@lem5045825 A B _64820 u f s x' h1). Qed.
Lemma lem5045827 {A B : Type'} (x : B) (u : B -> Prop) (f : A -> B) (s : A -> Prop) (x' : B -> A) (h1 : term166 A B u f s x') : term293 A B u s x' x.
Proof. exact (@lem5045826 A B x u f s x' h1). Qed.
Lemma lem5045830 {A B : Type'} (x' : B -> A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term166 A B u f s x') (h2 : term89 A B u t s t' f) (h3 : term217 B t t' x) : term220 A B s x' x.
Proof. exact (@lem5045827 A B x u f s x' h1 (@lem5045782 A B u s f t t' x h2 h3)). Qed.
Lemma lem5045831 {A B : Type'} (x' : B -> A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term166 A B u f s x') (h2 : term89 A B u t s t' f) (h3 : term217 B t t' x) : term294 A B s x' x.
Proof. exact (fun h0 : term295 A B s x' x => @lem5045830 A B x' u s f t t' x h1 h2 h3). Qed.
Lemma lem5045833 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5045834 {A B : Type'} (s : A -> Prop) (x' : B -> A) (x : B) : (term294 A B s x' x) = (term220 A B s x' x).
Proof. exact (@lem5045833 (term220 A B s x' x)). Qed.
Lemma lem5045835 {A B : Type'} (x' : B -> A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term166 A B u f s x') (h2 : term89 A B u t s t' f) (h3 : term217 B t t' x) : term220 A B s x' x.
Proof. exact (EQ_MP (@lem5045834 A B s x' x) (@lem5045831 A B x' u s f t t' x h1 h2 h3)). Qed.
Lemma lem5045837 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term217 B t t' x) : t' x.
Proof. exact (proj2 (@lem5044230 B t t' x h1)). Qed.
Lemma lem5045838 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term217 B t t' x) : term246 B t' x.
Proof. exact (fun h0 : term132 B t' x => @lem5045837 B t t' x h1). Qed.
Lemma lem5045840 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5045841 {B : Type'} (t' : B -> Prop) (x : B) : (term246 B t' x) = (t' x).
Proof. exact (@lem5045840 (t' x)). Qed.
Lemma lem5045842 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term217 B t t' x) : t' x.
Proof. exact (EQ_MP (@lem5045841 B t' x) (@lem5045838 B t t' x h1)). Qed.
Lemma lem5045844 {A B : Type'} (_64822 : B) (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (h1 : term89 A B u t s t' f) : term55 B t' u _64822.
Proof. exact (EQ_MP (@lem5045560 B t' u _64822) (@lem5045549 A B _64822 u t s t' f h1)). Qed.
Lemma lem5045845 {A B : Type'} (_64822 : B) (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (h1 : term89 A B u t s t' f) : term55 B t' u _64822.
Proof. exact (@lem5045844 A B _64822 u t s t' f h1). Qed.
Lemma lem5045846 {A B : Type'} (x : B) (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (h1 : term89 A B u t s t' f) : term55 B t' u x.
Proof. exact (@lem5045845 A B x u t s t' f h1). Qed.
Lemma lem5045849 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term89 A B u t s t' f) (h2 : term217 B t t' x) : u x.
Proof. exact (@lem5045846 A B x u t s t' f h1 (@lem5045842 B t t' x h2)). Qed.
Lemma lem5045850 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term89 A B u t s t' f) (h2 : term217 B t t' x) : term246 B u x.
Proof. exact (fun h0 : term132 B u x => @lem5045849 A B u s f t t' x h1 h2). Qed.
Lemma lem5045852 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5045853 {B : Type'} (u : B -> Prop) (x : B) : (term246 B u x) = (u x).
Proof. exact (@lem5045852 (u x)). Qed.
Lemma lem5045854 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term89 A B u t s t' f) (h2 : term217 B t t' x) : u x.
Proof. exact (EQ_MP (@lem5045853 B u x) (@lem5045850 A B u s f t t' x h1 h2)). Qed.
Lemma lem5045856 {A B : Type'} (_64820 : B) (u : B -> Prop) (f : A -> B) (s : A -> Prop) (x' : B -> A) (h1 : term166 A B u f s x') : term259 A B u f x' _64820.
Proof. exact (EQ_MP (@lem5045617 A B u f x' _64820) (@lem5045606 A B _64820 u f s x' h1)). Qed.
Lemma lem5045857 {A B : Type'} (_64820 : B) (u : B -> Prop) (f : A -> B) (s : A -> Prop) (x' : B -> A) (h1 : term166 A B u f s x') : term259 A B u f x' _64820.
Proof. exact (@lem5045856 A B _64820 u f s x' h1). Qed.
Lemma lem5045858 {A B : Type'} (x : B) (u : B -> Prop) (f : A -> B) (s : A -> Prop) (x' : B -> A) (h1 : term166 A B u f s x') : term259 A B u f x' x.
Proof. exact (@lem5045857 A B x u f s x' h1). Qed.
Lemma lem5045861 {A B : Type'} (x' : B -> A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term166 A B u f s x') (h2 : term89 A B u t s t' f) (h3 : term217 B t t' x) : x = (term219 A B f x' x).
Proof. exact (@lem5045858 A B x u f s x' h1 (@lem5045854 A B u s f t t' x h2 h3)). Qed.
Lemma lem5045862 {A B : Type'} (x' : B -> A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term166 A B u f s x') (h2 : term89 A B u t s t' f) (h3 : term217 B t t' x) : term260 A B f x' x.
Proof. exact (fun h0 : term261 A B f x' x => @lem5045861 A B x' u s f t t' x h1 h2 h3). Qed.
Lemma lem5045864 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5045865 {A B : Type'} (f : A -> B) (x' : B -> A) (x : B) : (term260 A B f x' x) = (x = (term219 A B f x' x)).
Proof. exact (@lem5045864 (x = (term219 A B f x' x))). Qed.
Lemma lem5045866 {A B : Type'} (x' : B -> A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term166 A B u f s x') (h2 : term89 A B u t s t' f) (h3 : term217 B t t' x) : x = (term219 A B f x' x).
Proof. exact (EQ_MP (@lem5045865 A B f x' x) (@lem5045862 A B x' u s f t t' x h1 h2 h3)). Qed.
Lemma lem5045868 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term217 B t t' x) : t' x.
Proof. exact (proj2 (@lem5044230 B t t' x h1)). Qed.
Lemma lem5045869 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term217 B t t' x) : term246 B t' x.
Proof. exact (fun h0 : term132 B t' x => @lem5045868 B t t' x h1). Qed.
Lemma lem5045871 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5045872 {B : Type'} (t' : B -> Prop) (x : B) : (term246 B t' x) = (t' x).
Proof. exact (@lem5045871 (t' x)). Qed.
Lemma lem5045873 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term217 B t t' x) : t' x.
Proof. exact (EQ_MP (@lem5045872 B t' x) (@lem5045869 B t t' x h1)). Qed.
Lemma lem5045879 (q : Prop) (p : Prop) (r : Prop) : (term11 p q r) = (term11 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5045880 {B : Type'} (_64840 : B) (t' : B -> Prop) (_64839 : B) : (term244 B _64840 t' _64839) = (term296 B _64840 t' _64839).
Proof. exact (@lem5045879 (t' _64840) (term266 B _64839 _64840) (term132 B t' _64839)). Qed.
Lemma lem5045894 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5045895 {B : Type'} (t' : B -> Prop) (_64839 : B) (_64840 : B) : (term297 B _64840 t' _64839) = (term298 B t' _64839 _64840).
Proof. exact (@lem5045894 (term132 B t' _64839) (term266 B _64839 _64840)). Qed.
Lemma lem5045903 {B : Type'} (t' : B -> Prop) (_64840 : B) : (term299 B t' _64840) = (term299 B t' _64840).
Proof. exact (eq_refl (term299 B t' _64840)). Qed.
Lemma lem5045904 {B : Type'} (t' : B -> Prop) (_64839 : B) (_64840 : B) : (term296 B _64840 t' _64839) = (term300 B t' _64839 _64840).
Proof. exact (MK_COMB (@lem5045903 B t' _64840) (@lem5045895 B t' _64839 _64840)). Qed.
Lemma lem5045915 {B : Type'} (t' : B -> Prop) (_64839 : B) (_64840 : B) : (term244 B _64840 t' _64839) = (term300 B t' _64839 _64840).
Proof. exact (TRANS (@lem5045880 B _64840 t' _64839) (@lem5045904 B t' _64839 _64840)). Qed.
Lemma lem5045916 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5045917 {B : Type'} (t' : B -> Prop) (_64839 : B) (_64840 : B) : (term301 B _64840 t' _64839) = (term302 B t' _64839 _64840).
Proof. exact (MK_COMB (@lem5045916) (@lem5045915 B t' _64839 _64840)). Qed.
Lemma lem5045931 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5045932 {B : Type'} (t' : B -> Prop) (_64839 : B) (_64840 : B) : (term297 B _64840 t' _64839) = (term298 B t' _64839 _64840).
Proof. exact (@lem5045931 (term132 B t' _64839) (term266 B _64839 _64840)). Qed.
Lemma lem5045940 {B : Type'} (t' : B -> Prop) (_64840 : B) : (term299 B t' _64840) = (term299 B t' _64840).
Proof. exact (eq_refl (term299 B t' _64840)). Qed.
Lemma lem5045941 {B : Type'} (t' : B -> Prop) (_64839 : B) (_64840 : B) : (term296 B _64840 t' _64839) = (term300 B t' _64839 _64840).
Proof. exact (MK_COMB (@lem5045940 B t' _64840) (@lem5045932 B t' _64839 _64840)). Qed.
Lemma lem5045952 {B : Type'} (t' : B -> Prop) (_64839 : B) (_64840 : B) : ((term244 B _64840 t' _64839) = (term296 B _64840 t' _64839)) = ((term300 B t' _64839 _64840) = (term300 B t' _64839 _64840)).
Proof. exact (MK_COMB (@lem5045917 B t' _64839 _64840) (@lem5045941 B t' _64839 _64840)). Qed.
Lemma lem5045954 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5045955 (x : Prop) : (x = x) = True.
Proof. exact (@lem5045954 Prop x). Qed.
Lemma lem5045956 {B : Type'} (t' : B -> Prop) (_64839 : B) (_64840 : B) : ((term300 B t' _64839 _64840) = (term300 B t' _64839 _64840)) = True.
Proof. exact (@lem5045955 (term300 B t' _64839 _64840)). Qed.
Lemma lem5045957 {B : Type'} (_64840 : B) (t' : B -> Prop) (_64839 : B) : ((term244 B _64840 t' _64839) = (term296 B _64840 t' _64839)) = True.
Proof. exact (TRANS (@lem5045952 B t' _64839 _64840) (@lem5045956 B t' _64839 _64840)). Qed.
Lemma lem5045958 {B : Type'} (_64840 : B) (t' : B -> Prop) (_64839 : B) : True = ((term244 B _64840 t' _64839) = (term296 B _64840 t' _64839)).
Proof. exact (SYM (@lem5045957 B _64840 t' _64839)). Qed.
Lemma lem5045959 {B : Type'} (_64840 : B) (t' : B -> Prop) (_64839 : B) : (term244 B _64840 t' _64839) = (term296 B _64840 t' _64839).
Proof. exact (EQ_MP (@lem5045958 B _64840 t' _64839) (@lem0)). Qed.
Lemma lem5045960 {B : Type'} (_64840 : B) (t' : B -> Prop) (_64839 : B) : term296 B _64840 t' _64839.
Proof. exact (EQ_MP (@lem5045959 B _64840 t' _64839) (@lem5045469 B _64840 t' _64839)). Qed.
Lemma lem5045962 (b : Prop) (a : Prop) : (a \/ b) = (term251 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5045963 {B : Type'} (_64839 : B) (t' : B -> Prop) (_64840 : B) : (term296 B _64840 t' _64839) = (term303 B _64839 t' _64840).
Proof. exact (@lem5045962 (term297 B _64840 t' _64839) (t' _64840)). Qed.
Lemma lem5045965 (a : Prop) (b : Prop) : (term274 a b) = (term275 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5045966 {B : Type'} (_64840 : B) (t' : B -> Prop) (_64839 : B) : (term304 B _64840 t' _64839) = (term305 B _64840 t' _64839).
Proof. exact (@lem5045965 (term266 B _64839 _64840) (term132 B t' _64839)). Qed.
Lemma lem5045968 (a : Prop) : (term109 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5045969 {B : Type'} (_64839 : B) (_64840 : B) : (term278 B _64839 _64840) = (_64839 = _64840).
Proof. exact (@lem5045968 (_64839 = _64840)). Qed.
Lemma lem5045970 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5045971 {B : Type'} (_64839 : B) (_64840 : B) : (term279 B _64839 _64840) = (term280 B _64839 _64840).
Proof. exact (MK_COMB (@lem5045970) (@lem5045969 B _64839 _64840)). Qed.
Lemma lem5045973 (a : Prop) : (term109 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5045974 {B : Type'} (t' : B -> Prop) (_64839 : B) : (term253 B t' _64839) = (t' _64839).
Proof. exact (@lem5045973 (t' _64839)). Qed.
Lemma lem5045975 {B : Type'} (_64840 : B) (t' : B -> Prop) (_64839 : B) : (term305 B _64840 t' _64839) = (term306 B _64840 t' _64839).
Proof. exact (MK_COMB (@lem5045971 B _64839 _64840) (@lem5045974 B t' _64839)). Qed.
Lemma lem5045976 {B : Type'} (_64840 : B) (t' : B -> Prop) (_64839 : B) : (term304 B _64840 t' _64839) = (term306 B _64840 t' _64839).
Proof. exact (TRANS (@lem5045966 B _64840 t' _64839) (@lem5045975 B _64840 t' _64839)). Qed.
Lemma lem5045977 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5045978 {B : Type'} (_64840 : B) (t' : B -> Prop) (_64839 : B) : (term307 B _64840 t' _64839) = (term308 B _64840 t' _64839).
Proof. exact (MK_COMB (@lem5045977) (@lem5045976 B _64840 t' _64839)). Qed.
Lemma lem5045979 {B : Type'} (t' : B -> Prop) (_64840 : B) : (t' _64840) = (t' _64840).
Proof. exact (eq_refl (t' _64840)). Qed.
Lemma lem5045980 {B : Type'} (_64839 : B) (t' : B -> Prop) (_64840 : B) : (term303 B _64839 t' _64840) = (term309 B _64839 t' _64840).
Proof. exact (MK_COMB (@lem5045978 B _64840 t' _64839) (@lem5045979 B t' _64840)). Qed.
Lemma lem5045981 {B : Type'} (_64839 : B) (t' : B -> Prop) (_64840 : B) : (term296 B _64840 t' _64839) = (term309 B _64839 t' _64840).
Proof. exact (TRANS (@lem5045963 B _64839 t' _64840) (@lem5045980 B _64839 t' _64840)). Qed.
Lemma lem5045983 {A B : Type'} (x' : B -> A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term166 A B u f s x') (h2 : term89 A B u t s t' f) (h3 : term217 B t t' x) : term310 A B f x' t' x.
Proof. exact (conj (@lem5045866 A B x' u s f t t' x h1 h2 h3) (@lem5045873 B t t' x h3)). Qed.
Lemma lem5045985 {B : Type'} (_64839 : B) (t' : B -> Prop) (_64840 : B) : term309 B _64839 t' _64840.
Proof. exact (EQ_MP (@lem5045981 B _64839 t' _64840) (@lem5045960 B _64840 t' _64839)). Qed.
Lemma lem5045986 {B : Type'} (_64839 : B) (t' : B -> Prop) (_64840 : B) : term309 B _64839 t' _64840.
Proof. exact (@lem5045985 B _64839 t' _64840). Qed.
Lemma lem5045987 {A B : Type'} (t' : B -> Prop) (f : A -> B) (x' : B -> A) (x : B) : term311 A B t' f x' x.
Proof. exact (@lem5045986 B x t' (term219 A B f x' x)). Qed.
Lemma lem5045990 {A B : Type'} (x' : B -> A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term166 A B u f s x') (h2 : term89 A B u t s t' f) (h3 : term217 B t t' x) : term312 A B t' f x' x.
Proof. exact (@lem5045987 A B t' f x' x (@lem5045983 A B x' u s f t t' x h1 h2 h3)). Qed.
Lemma lem5045991 {A B : Type'} (x' : B -> A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term166 A B u f s x') (h2 : term89 A B u t s t' f) (h3 : term217 B t t' x) : term313 A B t' f x' x.
Proof. exact (fun h0 : term314 A B t' f x' x => @lem5045990 A B x' u s f t t' x h1 h2 h3). Qed.
Lemma lem5045993 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5045994 {A B : Type'} (t' : B -> Prop) (f : A -> B) (x' : B -> A) (x : B) : (term313 A B t' f x' x) = (term312 A B t' f x' x).
Proof. exact (@lem5045993 (term312 A B t' f x' x)). Qed.
Lemma lem5045995 {A B : Type'} (x' : B -> A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term166 A B u f s x') (h2 : term89 A B u t s t' f) (h3 : term217 B t t' x) : term312 A B t' f x' x.
Proof. exact (EQ_MP (@lem5045994 A B t' f x' x) (@lem5045991 A B x' u s f t t' x h1 h2 h3)). Qed.
Lemma lem5045997 (b : Prop) (a : Prop) : (a \/ b) = (term251 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5045998 {A B : Type'} (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (f : A -> B) (_64823 : A) : (term238 A B t s t' f _64823) = (term320 A B s t' t f _64823).
Proof. exact (@lem5045997 (term174 A B s t' f _64823) (term82 A B t f _64823)). Qed.
Lemma lem5046000 (a : Prop) (b : Prop) : (term274 a b) = (term275 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5046001 {A B : Type'} (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (_64823 : A) : (term321 A B s t' f _64823) = (term322 A B s t' f _64823).
Proof. exact (@lem5046000 (term132 A s _64823) (term235 A B t' f _64823)). Qed.
Lemma lem5046003 (a : Prop) : (term109 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5046004 {A : Type'} (s : A -> Prop) (_64823 : A) : (term253 A s _64823) = (s _64823).
Proof. exact (@lem5046003 (s _64823)). Qed.
Lemma lem5046005 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5046006 {A : Type'} (s : A -> Prop) (_64823 : A) : (term323 A s _64823) = (term80 A s _64823).
Proof. exact (MK_COMB (@lem5046005) (@lem5046004 A s _64823)). Qed.
Lemma lem5046008 (a : Prop) : (term109 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5046009 {A B : Type'} (t' : B -> Prop) (f : A -> B) (_64823 : A) : (term324 A B t' f _64823) = (term82 A B t' f _64823).
Proof. exact (@lem5046008 (term82 A B t' f _64823)). Qed.
Lemma lem5046010 {A B : Type'} (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (_64823 : A) : (term322 A B s t' f _64823) = (term83 A B s t' f _64823).
Proof. exact (MK_COMB (@lem5046006 A s _64823) (@lem5046009 A B t' f _64823)). Qed.
Lemma lem5046011 {A B : Type'} (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (_64823 : A) : (term321 A B s t' f _64823) = (term83 A B s t' f _64823).
Proof. exact (TRANS (@lem5046001 A B s t' f _64823) (@lem5046010 A B s t' f _64823)). Qed.
Lemma lem5046012 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5046013 {A B : Type'} (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (_64823 : A) : (term325 A B s t' f _64823) = (term326 A B s t' f _64823).
Proof. exact (MK_COMB (@lem5046012) (@lem5046011 A B s t' f _64823)). Qed.
Lemma lem5046014 {A B : Type'} (t : B -> Prop) (f : A -> B) (_64823 : A) : (term82 A B t f _64823) = (term82 A B t f _64823).
Proof. exact (eq_refl (term82 A B t f _64823)). Qed.
Lemma lem5046015 {A B : Type'} (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (f : A -> B) (_64823 : A) : (term320 A B s t' t f _64823) = (term327 A B s t' t f _64823).
Proof. exact (MK_COMB (@lem5046013 A B s t' f _64823) (@lem5046014 A B t f _64823)). Qed.
Lemma lem5046016 {A B : Type'} (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (f : A -> B) (_64823 : A) : (term238 A B t s t' f _64823) = (term327 A B s t' t f _64823).
Proof. exact (TRANS (@lem5045998 A B s t' t f _64823) (@lem5046015 A B s t' t f _64823)). Qed.
Lemma lem5046018 {A B : Type'} (x' : B -> A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term166 A B u f s x') (h2 : term89 A B u t s t' f) (h3 : term217 B t t' x) : term328 A B s t' f x' x.
Proof. exact (conj (@lem5045835 A B x' u s f t t' x h1 h2 h3) (@lem5045995 A B x' u s f t t' x h1 h2 h3)). Qed.
Lemma lem5046020 {A B : Type'} (_64823 : A) (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (h1 : term89 A B u t s t' f) : term327 A B s t' t f _64823.
Proof. exact (EQ_MP (@lem5046016 A B s t' t f _64823) (@lem5044638 A B _64823 u t s t' f h1)). Qed.
Lemma lem5046021 {A B : Type'} (_64823 : A) (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (h1 : term89 A B u t s t' f) : term327 A B s t' t f _64823.
Proof. exact (@lem5046020 A B _64823 u t s t' f h1). Qed.
Lemma lem5046022 {A B : Type'} (x' : B -> A) (x : B) (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (h1 : term89 A B u t s t' f) : term329 A B s t' t f x' x.
Proof. exact (@lem5046021 A B (x' x) u t s t' f h1). Qed.
Lemma lem5046025 {A B : Type'} (x' : B -> A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term166 A B u f s x') (h2 : term89 A B u t s t' f) (h3 : term217 B t t' x) : term312 A B t f x' x.
Proof. exact (@lem5046022 A B x' x u t s t' f h2 (@lem5046018 A B x' u s f t t' x h1 h2 h3)). Qed.
Lemma lem5046026 {A B : Type'} (x' : B -> A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term166 A B u f s x') (h2 : term89 A B u t s t' f) (h3 : term217 B t t' x) : term313 A B t f x' x.
Proof. exact (fun h0 : term314 A B t f x' x => @lem5046025 A B x' u s f t t' x h1 h2 h3). Qed.
Lemma lem5046028 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5046029 {A B : Type'} (t : B -> Prop) (f : A -> B) (x' : B -> A) (x : B) : (term313 A B t f x' x) = (term312 A B t f x' x).
Proof. exact (@lem5046028 (term312 A B t f x' x)). Qed.
Lemma lem5046030 {A B : Type'} (x' : B -> A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term166 A B u f s x') (h2 : term89 A B u t s t' f) (h3 : term217 B t t' x) : term312 A B t f x' x.
Proof. exact (EQ_MP (@lem5046029 A B t f x' x) (@lem5046026 A B x' u s f t t' x h1 h2 h3)). Qed.
Lemma lem5046036 (q : Prop) (p : Prop) (r : Prop) : (term11 p q r) = (term11 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5046037 {B : Type'} (_64842 : B) (t : B -> Prop) (_64841 : B) : (term244 B _64842 t _64841) = (term296 B _64842 t _64841).
Proof. exact (@lem5046036 (t _64842) (term266 B _64841 _64842) (term132 B t _64841)). Qed.
Lemma lem5046051 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5046052 {B : Type'} (t : B -> Prop) (_64841 : B) (_64842 : B) : (term297 B _64842 t _64841) = (term298 B t _64841 _64842).
Proof. exact (@lem5046051 (term132 B t _64841) (term266 B _64841 _64842)). Qed.
Lemma lem5046060 {B : Type'} (t : B -> Prop) (_64842 : B) : (term299 B t _64842) = (term299 B t _64842).
Proof. exact (eq_refl (term299 B t _64842)). Qed.
Lemma lem5046061 {B : Type'} (t : B -> Prop) (_64841 : B) (_64842 : B) : (term296 B _64842 t _64841) = (term300 B t _64841 _64842).
Proof. exact (MK_COMB (@lem5046060 B t _64842) (@lem5046052 B t _64841 _64842)). Qed.
Lemma lem5046072 {B : Type'} (t : B -> Prop) (_64841 : B) (_64842 : B) : (term244 B _64842 t _64841) = (term300 B t _64841 _64842).
Proof. exact (TRANS (@lem5046037 B _64842 t _64841) (@lem5046061 B t _64841 _64842)). Qed.
Lemma lem5046073 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5046074 {B : Type'} (t : B -> Prop) (_64841 : B) (_64842 : B) : (term301 B _64842 t _64841) = (term302 B t _64841 _64842).
Proof. exact (MK_COMB (@lem5046073) (@lem5046072 B t _64841 _64842)). Qed.
Lemma lem5046088 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5046089 {B : Type'} (t : B -> Prop) (_64841 : B) (_64842 : B) : (term297 B _64842 t _64841) = (term298 B t _64841 _64842).
Proof. exact (@lem5046088 (term132 B t _64841) (term266 B _64841 _64842)). Qed.
Lemma lem5046097 {B : Type'} (t : B -> Prop) (_64842 : B) : (term299 B t _64842) = (term299 B t _64842).
Proof. exact (eq_refl (term299 B t _64842)). Qed.
Lemma lem5046098 {B : Type'} (t : B -> Prop) (_64841 : B) (_64842 : B) : (term296 B _64842 t _64841) = (term300 B t _64841 _64842).
Proof. exact (MK_COMB (@lem5046097 B t _64842) (@lem5046089 B t _64841 _64842)). Qed.
Lemma lem5046109 {B : Type'} (t : B -> Prop) (_64841 : B) (_64842 : B) : ((term244 B _64842 t _64841) = (term296 B _64842 t _64841)) = ((term300 B t _64841 _64842) = (term300 B t _64841 _64842)).
Proof. exact (MK_COMB (@lem5046074 B t _64841 _64842) (@lem5046098 B t _64841 _64842)). Qed.
Lemma lem5046111 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5046112 (x : Prop) : (x = x) = True.
Proof. exact (@lem5046111 Prop x). Qed.
Lemma lem5046113 {B : Type'} (t : B -> Prop) (_64841 : B) (_64842 : B) : ((term300 B t _64841 _64842) = (term300 B t _64841 _64842)) = True.
Proof. exact (@lem5046112 (term300 B t _64841 _64842)). Qed.
Lemma lem5046114 {B : Type'} (_64842 : B) (t : B -> Prop) (_64841 : B) : ((term244 B _64842 t _64841) = (term296 B _64842 t _64841)) = True.
Proof. exact (TRANS (@lem5046109 B t _64841 _64842) (@lem5046113 B t _64841 _64842)). Qed.
Lemma lem5046115 {B : Type'} (_64842 : B) (t : B -> Prop) (_64841 : B) : True = ((term244 B _64842 t _64841) = (term296 B _64842 t _64841)).
Proof. exact (SYM (@lem5046114 B _64842 t _64841)). Qed.
Lemma lem5046116 {B : Type'} (_64842 : B) (t : B -> Prop) (_64841 : B) : (term244 B _64842 t _64841) = (term296 B _64842 t _64841).
Proof. exact (EQ_MP (@lem5046115 B _64842 t _64841) (@lem0)). Qed.
Lemma lem5046117 {B : Type'} (_64842 : B) (t : B -> Prop) (_64841 : B) : term296 B _64842 t _64841.
Proof. exact (EQ_MP (@lem5046116 B _64842 t _64841) (@lem5045481 B _64842 t _64841)). Qed.
Lemma lem5046119 (b : Prop) (a : Prop) : (a \/ b) = (term251 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5046120 {B : Type'} (_64841 : B) (t : B -> Prop) (_64842 : B) : (term296 B _64842 t _64841) = (term303 B _64841 t _64842).
Proof. exact (@lem5046119 (term297 B _64842 t _64841) (t _64842)). Qed.
Lemma lem5046122 (a : Prop) (b : Prop) : (term274 a b) = (term275 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5046123 {B : Type'} (_64842 : B) (t : B -> Prop) (_64841 : B) : (term304 B _64842 t _64841) = (term305 B _64842 t _64841).
Proof. exact (@lem5046122 (term266 B _64841 _64842) (term132 B t _64841)). Qed.
Lemma lem5046125 (a : Prop) : (term109 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5046126 {B : Type'} (_64841 : B) (_64842 : B) : (term278 B _64841 _64842) = (_64841 = _64842).
Proof. exact (@lem5046125 (_64841 = _64842)). Qed.
Lemma lem5046127 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5046128 {B : Type'} (_64841 : B) (_64842 : B) : (term279 B _64841 _64842) = (term280 B _64841 _64842).
Proof. exact (MK_COMB (@lem5046127) (@lem5046126 B _64841 _64842)). Qed.
Lemma lem5046130 (a : Prop) : (term109 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5046131 {B : Type'} (t : B -> Prop) (_64841 : B) : (term253 B t _64841) = (t _64841).
Proof. exact (@lem5046130 (t _64841)). Qed.
Lemma lem5046132 {B : Type'} (_64842 : B) (t : B -> Prop) (_64841 : B) : (term305 B _64842 t _64841) = (term306 B _64842 t _64841).
Proof. exact (MK_COMB (@lem5046128 B _64841 _64842) (@lem5046131 B t _64841)). Qed.
Lemma lem5046133 {B : Type'} (_64842 : B) (t : B -> Prop) (_64841 : B) : (term304 B _64842 t _64841) = (term306 B _64842 t _64841).
Proof. exact (TRANS (@lem5046123 B _64842 t _64841) (@lem5046132 B _64842 t _64841)). Qed.
Lemma lem5046134 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5046135 {B : Type'} (_64842 : B) (t : B -> Prop) (_64841 : B) : (term307 B _64842 t _64841) = (term308 B _64842 t _64841).
Proof. exact (MK_COMB (@lem5046134) (@lem5046133 B _64842 t _64841)). Qed.
Lemma lem5046136 {B : Type'} (t : B -> Prop) (_64842 : B) : (t _64842) = (t _64842).
Proof. exact (eq_refl (t _64842)). Qed.
Lemma lem5046137 {B : Type'} (_64841 : B) (t : B -> Prop) (_64842 : B) : (term303 B _64841 t _64842) = (term309 B _64841 t _64842).
Proof. exact (MK_COMB (@lem5046135 B _64842 t _64841) (@lem5046136 B t _64842)). Qed.
Lemma lem5046138 {B : Type'} (_64841 : B) (t : B -> Prop) (_64842 : B) : (term296 B _64842 t _64841) = (term309 B _64841 t _64842).
Proof. exact (TRANS (@lem5046120 B _64841 t _64842) (@lem5046137 B _64841 t _64842)). Qed.
Lemma lem5046140 {A B : Type'} (x' : B -> A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term166 A B u f s x') (h2 : term89 A B u t s t' f) (h3 : term217 B t t' x) : term330 A B t f x' x.
Proof. exact (conj (@lem5045763 A B x' u s f t t' x h1 h2 h3) (@lem5046030 A B x' u s f t t' x h1 h2 h3)). Qed.
Lemma lem5046142 {B : Type'} (_64841 : B) (t : B -> Prop) (_64842 : B) : term309 B _64841 t _64842.
Proof. exact (EQ_MP (@lem5046138 B _64841 t _64842) (@lem5046117 B _64842 t _64841)). Qed.
Lemma lem5046143 {B : Type'} (_64841 : B) (t : B -> Prop) (_64842 : B) : term309 B _64841 t _64842.
Proof. exact (@lem5046142 B _64841 t _64842). Qed.
Lemma lem5046144 {A B : Type'} (f : A -> B) (x' : B -> A) (t : B -> Prop) (x : B) : term331 A B f x' t x.
Proof. exact (@lem5046143 B (term219 A B f x' x) t x). Qed.
Lemma lem5046147 {A B : Type'} (x' : B -> A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term166 A B u f s x') (h2 : term89 A B u t s t' f) (h3 : term217 B t t' x) : t x.
Proof. exact (@lem5046144 A B f x' t x (@lem5046140 A B x' u s f t t' x h1 h2 h3)). Qed.
Lemma lem5046148 {A B : Type'} (x' : B -> A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term166 A B u f s x') (h2 : term89 A B u t s t' f) (h3 : term217 B t t' x) : term246 B t x.
Proof. exact (fun h0 : term132 B t x => @lem5046147 A B x' u s f t t' x h1 h2 h3). Qed.
Lemma lem5046150 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5046151 {B : Type'} (t : B -> Prop) (x : B) : (term246 B t x) = (t x).
Proof. exact (@lem5046150 (t x)). Qed.
Lemma lem5046152 {A B : Type'} (x' : B -> A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term166 A B u f s x') (h2 : term89 A B u t s t' f) (h3 : term217 B t t' x) : t x.
Proof. exact (EQ_MP (@lem5046151 B t x) (@lem5046148 A B x' u s f t t' x h1 h2 h3)). Qed.
Lemma lem5046155 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5046157 {B : Type'} (t : B -> Prop) (x : B) : (term132 B t x) = (term332 B t x).
Proof. exact (@lem5046155 (t x)). Qed.
Lemma lem5046160 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term217 B t t' x) : term332 B t x.
Proof. exact (EQ_MP (@lem5046157 B t x) (@lem5044592 B t t' x h1)). Qed.
Lemma lem5046163 {A B : Type'} (x' : B -> A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term166 A B u f s x') (h2 : term89 A B u t s t' f) (h3 : term217 B t t' x) : False.
Proof. exact (@lem5046160 B t t' x h3 (@lem5046152 A B x' u s f t t' x h1 h2 h3)). Qed.
Lemma lem5046164 {A B : Type'} (x' : B -> A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term166 A B u f s x') (h2 : term89 A B u t s t' f) (h3 : term217 B t t' x) : term333.
Proof. exact (fun h0 : ~ False => @lem5046163 A B x' u s f t t' x h1 h2 h3). Qed.
Lemma lem5046166 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5046167 : term333 = False.
Proof. exact (@lem5046166 False). Qed.
Lemma lem5046168 {A B : Type'} (x' : B -> A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (t' : B -> Prop) (x : B) (h1 : term166 A B u f s x') (h2 : term89 A B u t s t' f) (h3 : term217 B t t' x) : False.
Proof. exact (EQ_MP (@lem5046167) (@lem5046164 A B x' u s f t t' x h1 h2 h3)). Qed.
Lemma lem5046169 {A B : Type'} (x' : B -> A) (x : B) (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (h1 : term166 A B u f s x') (h2 : term123 B t t' x) (h3 : term89 A B u t s t' f) : False.
Proof. exact (or_elim (@lem5044193 B t t' x h2) (fun h0 : term216 B t t' x => @lem5045445 A B x' u s f t t' x h1 h3 h0) (fun h0 : term217 B t t' x => @lem5046168 A B x' u s f t t' x h1 h3 h0)). Qed.
Lemma lem5046170 {A B : Type'} (x' : B -> A) (x : B) (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (h1 : term166 A B u f s x') (h2 : term123 B t t' x) (h3 : term89 A B u t s t' f) : (term166 A B u f s x') = False.
Proof. exact (prop_ext (fun h4 : term166 A B u f s x' => @lem5046169 A B x' x u t s t' f h1 h2 h3) (fun h4 : False => @lem5044222 A B u f s x' h1)). Qed.
Lemma lem5046171 {A B : Type'} (x' : B -> A) (x : B) (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (h1 : term166 A B u f s x') (h2 : term123 B t t' x) (h3 : term89 A B u t s t' f) : False.
Proof. exact (EQ_MP (@lem5046170 A B x' x u t s t' f h1 h2 h3) (@lem5044222 A B u f s x' h1)). Qed.
Lemma lem5046172 {A B : Type'} (x : B) (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (h1 : term52 A B u f s) (h2 : term123 B t t' x) (h3 : term89 A B u t s t' f) : False.
Proof. exact (ex_elim (@lem5043785 A B u f s h1) (fun x' : B -> A => fun h0 : term168 A B u f s x' => @lem5046171 A B x' x u t s t' f h0 h2 h3)). Qed.
Lemma lem5046173 {A B : Type'} (x : B) (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (h1 : term52 A B u f s) (h2 : term123 B t t' x) (h3 : term89 A B u t s t' f) : (term123 B t t' x) = False.
Proof. exact (prop_ext (fun h4 : term123 B t t' x => @lem5046172 A B x u t s t' f h1 h2 h3) (fun h4 : False => @lem5043630 B t t' x h2)). Qed.
Lemma lem5046174 {A B : Type'} (x : B) (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (h1 : term52 A B u f s) (h2 : term123 B t t' x) (h3 : term89 A B u t s t' f) : False.
Proof. exact (EQ_MP (@lem5046173 A B x u t s t' f h1 h2 h3) (@lem5043630 B t t' x h2)). Qed.
Lemma lem5046175 {A B : Type'} (x : B) (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (h1 : term52 A B u f s) (h2 : term89 A B u t s t' f) : term122 B t t' x.
Proof. exact (fun h0 : term123 B t t' x => @lem5046174 A B x u t s t' f h1 h0 h2). Qed.
Lemma lem5046176 {A B : Type'} (x : B) (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (h1 : term52 A B u f s) (h2 : term89 A B u t s t' f) : (t x) = (t' x).
Proof. exact (EQ_MP (@lem5043629 B t t' x) (@lem5046175 A B x u t s t' f h1 h2)). Qed.
Lemma lem5046181 {A B : Type'} (u : B -> Prop) (t : B -> Prop) (s : A -> Prop) (t' : B -> Prop) (f : A -> B) (h1 : term52 A B u f s) (h2 : term89 A B u t s t' f) : term95 B t t'.
Proof. exact (fun x : B => @lem5046176 A B x u t s t' f h1 h2). Qed.
Lemma lem5046182 {A B : Type'} (t : B -> Prop) (t' : B -> Prop) (u : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term52 A B u f s) : term96 A B u s f t t'.
Proof. exact (fun h0 : term89 A B u t s t' f => @lem5046181 A B u t s t' f h1 h0). Qed.
Lemma lem5046187 {A B : Type'} (t : B -> Prop) (u : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term52 A B u f s) : term98 A B u s f t.
Proof. exact (fun t' : B -> Prop => @lem5046182 A B t t' u f s h1). Qed.
Lemma lem5046192 {A B : Type'} (u : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term52 A B u f s) : term100 A B u s f.
Proof. exact (fun t : B -> Prop => @lem5046187 A B t u f s h1). Qed.
Lemma lem5046193 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) : term101 A B u s f.
Proof. exact (fun h0 : term52 A B u f s => @lem5046192 A B u f s h0). Qed.
Lemma lem5046198 {A B : Type'} (s : A -> Prop) (f : A -> B) : term113 A B s f.
Proof. exact (fun u : B -> Prop => @lem5046193 A B u s f). Qed.
Lemma lem5046203 {A B : Type'} (f : A -> B) : term117 A B f.
Proof. exact (fun s : A -> Prop => @lem5046198 A B s f). Qed.
Lemma lem5046208 {A B : Type'} : term121 A B.
Proof. exact (fun f : A -> B => @lem5046203 A B f). Qed.
Lemma lem5046209 {A B : Type'} : term120 A B.
Proof. exact (EQ_MP (@lem5043623 A B) (@lem5046208 A B)). Qed.
Lemma lem5046210 {A B : Type'} (f : A -> B) : term334 A B f.
Proof. exact (@lem5046209 A B f). Qed.
Lemma lem5046211 {A B : Type'} (f : A -> B) : (term334 A B f) = (term116 A B f).
Proof. exact (eq_refl (term334 A B f)). Qed.
Lemma lem5046212 {A B : Type'} (f : A -> B) : term116 A B f.
Proof. exact (EQ_MP (@lem5046211 A B f) (@lem5046210 A B f)). Qed.
Lemma lem5046213 {A B : Type'} (f : A -> B) (s : A -> Prop) : term335 A B f s.
Proof. exact (@lem5046212 A B f s). Qed.
Lemma lem5046214 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term335 A B f s) = (term112 A B s f).
Proof. exact (eq_refl (term335 A B f s)). Qed.
Lemma lem5046215 {A B : Type'} (s : A -> Prop) (f : A -> B) : term112 A B s f.
Proof. exact (EQ_MP (@lem5046214 A B s f) (@lem5046213 A B f s)). Qed.
Lemma lem5046216 {A B : Type'} (s : A -> Prop) (f : A -> B) (u : B -> Prop) : term336 A B s f u.
Proof. exact (@lem5046215 A B s f u). Qed.
Lemma lem5046217 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) : (term336 A B s f u) = (term103 A B u s f).
Proof. exact (eq_refl (term336 A B s f u)). Qed.
Lemma lem5046218 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) : term103 A B u s f.
Proof. exact (EQ_MP (@lem5046217 A B u s f) (@lem5046216 A B s f u)). Qed.
Lemma lem5046220 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) : term103 A B u s f.
Proof. exact (@lem5043327 A B u s f (@lem5046218 A B u s f)). Qed.
Lemma lem5046221 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term104 A B u s f) : False.
Proof. exact (@lem5046220 A B u s f (@lem5043311 A B u s f h1)). Qed.
Lemma lem5046222 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term104 A B u s f) : (term104 A B u s f) = False.
Proof. exact (prop_ext (fun h2 : term104 A B u s f => @lem5046221 A B u s f h1) (fun h2 : False => @lem5043311 A B u s f h1)). Qed.
Lemma lem5046223 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term104 A B u s f) : False.
Proof. exact (EQ_MP (@lem5046222 A B u s f h1) (@lem5043311 A B u s f h1)). Qed.
Lemma lem5046224 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) : term103 A B u s f.
Proof. exact (fun h0 : term104 A B u s f => @lem5046223 A B u s f h0). Qed.
Lemma lem5046225 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) : term101 A B u s f.
Proof. exact (EQ_MP (@lem5043310 A B u s f) (@lem5046224 A B u s f)). Qed.
Lemma lem5046226 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) : term37 A B u s f.
Proof. exact (EQ_MP (@lem5043306 A B u s f) (@lem5046225 A B u s f)). Qed.
Lemma lem5046227 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) : term36 A B u s f.
Proof. exact (EQ_MP (@lem5043033 A B u s f) (@lem5046226 A B u s f)). Qed.
Lemma lem5046228 {A B : Type'} (u : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term5 A B u f s) : term4 A B u s f.
Proof. exact (@lem5046227 A B u s f (@lem5042902 A B u f s h1)). Qed.
Lemma lem5046230 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term3 A s t).
Proof. exact (EQ_MP (@lem5042899 A s t) (@lem5042898 A s t)). Qed.
Lemma lem5046231 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (@SUBSET B s t) = (term3 B s t).
Proof. exact (@lem5046230 B s t). Qed.
Lemma lem5046232 {A B : Type'} (u : B -> Prop) (f : A -> B) (s : A -> Prop) : (term5 A B u f s) = (term13 A B u f s).
Proof. exact (@lem5046231 B u (@IMAGE A B f s)). Qed.
Lemma lem5046239 {A B : Type'} (u : B -> Prop) (f : A -> B) (s : A -> Prop) : (term13 A B u f s) = (term5 A B u f s).
Proof. exact (SYM (@lem5046232 A B u f s)). Qed.
Lemma lem5046240 {A B : Type'} (y : B) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term4 A B u s f) : term337 A B u s f y.
Proof. exact (@lem5042901 A B u s f h1 (@INSERT B y (@EMPTY B))). Qed.
Lemma lem5046241 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term337 A B u s f y) = (term338 A B u s f y).
Proof. exact (eq_refl (term337 A B u s f y)). Qed.
Lemma lem5046242 {A B : Type'} (y : B) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term4 A B u s f) : term338 A B u s f y.
Proof. exact (EQ_MP (@lem5046241 A B u s f y) (@lem5046240 A B y u s f h1)). Qed.
Lemma lem5046243 {A B : Type'} (y : B) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term4 A B u s f) : term339 A B u s f y.
Proof. exact (@lem5046242 A B y u s f h1 (@EMPTY B)). Qed.
Lemma lem5046244 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term339 A B u s f y) = (term340 A B u s f y).
Proof. exact (eq_refl (term339 A B u s f y)). Qed.
Lemma lem5046245 {A B : Type'} (y : B) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term4 A B u s f) : term340 A B u s f y.
Proof. exact (EQ_MP (@lem5046244 A B u s f y) (@lem5046243 A B y u s f h1)). Qed.
Lemma lem5046263 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term3 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem5046264 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (@SUBSET B s t) = (term3 B s t).
Proof. exact (@lem5046263 B s t). Qed.
Lemma lem5046265 {B : Type'} (y : B) (u : B -> Prop) : (term341 B y u) = (term342 B y u).
Proof. exact (@lem5046264 B (@INSERT B y (@EMPTY B)) u). Qed.
Lemma lem5046272 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5046273 {B : Type'} (y : B) (u : B -> Prop) : (term343 B y u) = (term344 B y u).
Proof. exact (MK_COMB (@lem5046272) (@lem5046265 B y u)). Qed.
Lemma lem5046277 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term3 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem5046278 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (@SUBSET B s t) = (term3 B s t).
Proof. exact (@lem5046277 B s t). Qed.
Lemma lem5046279 {B : Type'} (u : B -> Prop) : (@SUBSET B (@EMPTY B) u) = (term345 B u).
Proof. exact (@lem5046278 B (@EMPTY B) u). Qed.
Lemma lem5046286 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5046287 {B : Type'} (u : B -> Prop) : (term346 B u) = (term347 B u).
Proof. exact (MK_COMB (@lem5046286) (@lem5046279 B u)). Qed.
Lemma lem5046291 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term18 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem5046292 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term18 A s t).
Proof. exact (@lem5046291 A s t). Qed.
Lemma lem5046293 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) : ((term348 A B s f y) = (term349 A B s f)) = (term350 A B y s f).
Proof. exact (@lem5046292 A (term348 A B s f y) (term349 A B s f)). Qed.
Lemma lem5046314 {A B : Type'} (u : B -> Prop) (y : B) (s : A -> Prop) (f : A -> B) : (term351 A B u y s f) = (term352 A B u y s f).
Proof. exact (MK_COMB (@lem5046287 B u) (@lem5046293 A B y s f)). Qed.
Lemma lem5046317 {A B : Type'} (u : B -> Prop) (y : B) (s : A -> Prop) (f : A -> B) : (term353 A B u y s f) = (term354 A B u y s f).
Proof. exact (MK_COMB (@lem5046273 B y u) (@lem5046314 A B u y s f)). Qed.
Lemma lem5046320 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5046321 {A B : Type'} (u : B -> Prop) (y : B) (s : A -> Prop) (f : A -> B) : (term355 A B u y s f) = (term356 A B u y s f).
Proof. exact (MK_COMB (@lem5046320) (@lem5046317 A B u y s f)). Qed.
Lemma lem5046325 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term18 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem5046326 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (s = t) = (term18 B s t).
Proof. exact (@lem5046325 B s t). Qed.
Lemma lem5046327 {B : Type'} (y : B) : ((@INSERT B y (@EMPTY B)) = (@EMPTY B)) = (term357 B y).
Proof. exact (@lem5046326 B (@INSERT B y (@EMPTY B)) (@EMPTY B)). Qed.
Lemma lem5046336 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term340 A B u s f y) = (term358 A B u s f y).
Proof. exact (MK_COMB (@lem5046321 A B u y s f) (@lem5046327 B y)). Qed.
Lemma lem5046339 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5046340 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term359 A B u s f y) = (term360 A B u s f y).
Proof. exact (MK_COMB (@lem5046339) (@lem5046336 A B u s f y)). Qed.
Lemma lem5046343 {A B : Type'} (u : B -> Prop) (y : B) (f : A -> B) (s : A -> Prop) : (term48 A B u y f s) = (term48 A B u y f s).
Proof. exact (eq_refl (term48 A B u y f s)). Qed.
Lemma lem5046344 {A B : Type'} (u : B -> Prop) (y : B) (f : A -> B) (s : A -> Prop) : (term361 A B u y f s) = (term362 A B u y f s).
Proof. exact (MK_COMB (@lem5046340 A B u s f y) (@lem5046343 A B u y f s)). Qed.
Lemma lem5046347 {A B : Type'} (u : B -> Prop) (y : B) (f : A -> B) (s : A -> Prop) : (term362 A B u y f s) = (term361 A B u y f s).
Proof. exact (SYM (@lem5046344 A B u y f s)). Qed.
Lemma lem5046361 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term363 A x y s) = (term364 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem5046362 {B : Type'} (y : B) (x : B) (s : B -> Prop) : (term363 B x y s) = (term364 B y x s).
Proof. exact (@lem5046361 B y x s). Qed.
Lemma lem5046363 {B : Type'} (y : B) (x : B) : (term365 B x y) = (term366 B y x).
Proof. exact (@lem5046362 B y x (@EMPTY B)). Qed.
Lemma lem5046369 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem5046370 {B : Type'} (x : B) : (@IN B x (@EMPTY B)) = False.
Proof. exact (@lem5046369 B x). Qed.
Lemma lem5046371 {B : Type'} (x : B) (y : B) : (term367 B x y) = (term367 B x y).
Proof. exact (eq_refl (term367 B x y)). Qed.
Lemma lem5046372 {B : Type'} (x : B) (y : B) : (term366 B y x) = (term368 B x y).
Proof. exact (MK_COMB (@lem5046371 B x y) (@lem5046370 B x)). Qed.
Lemma lem5046374 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem5046375 {B : Type'} (x : B) (y : B) : (term368 B x y) = (x = y).
Proof. exact (@lem5046374 (x = y)). Qed.
Lemma lem5046378 {B : Type'} (x : B) (y : B) : (term366 B y x) = (x = y).
Proof. exact (TRANS (@lem5046372 B x y) (@lem5046375 B x y)). Qed.
Lemma lem5046379 {B : Type'} (x : B) (y : B) : (term365 B x y) = (x = y).
Proof. exact (TRANS (@lem5046363 B y x) (@lem5046378 B x y)). Qed.
Lemma lem5046380 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5046381 {B : Type'} (x : B) (y : B) : (term369 B x y) = (term370 B x y).
Proof. exact (MK_COMB (@lem5046380) (@lem5046379 B x y)). Qed.
Lemma lem5046383 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5046384 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem5046383 B P x). Qed.
Lemma lem5046385 {B : Type'} (u : B -> Prop) (x : B) : (@IN B x u) = (u x).
Proof. exact (@lem5046384 B u x). Qed.
Lemma lem5046386 {B : Type'} (y : B) (u : B -> Prop) (x : B) : (term371 B y x u) = (term372 B y u x).
Proof. exact (MK_COMB (@lem5046381 B x y) (@lem5046385 B u x)). Qed.
Lemma lem5046391 {B : Type'} (y : B) (u : B -> Prop) : (term373 B y u) = (term374 B y u).
Proof. exact (fun_ext (fun x : B => @lem5046386 B y u x)). Qed.
Lemma lem5046392 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5046393 {B : Type'} (y : B) (u : B -> Prop) : (term342 B y u) = (term375 B y u).
Proof. exact (MK_COMB (@lem5046392 B) (@lem5046391 B y u)). Qed.
Lemma lem5046398 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5046399 {B : Type'} (y : B) (u : B -> Prop) : (term344 B y u) = (term376 B y u).
Proof. exact (MK_COMB (@lem5046398) (@lem5046393 B y u)). Qed.
Lemma lem5046409 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem5046410 {B : Type'} (x : B) : (@IN B x (@EMPTY B)) = False.
Proof. exact (@lem5046409 B x). Qed.
Lemma lem5046411 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5046412 {B : Type'} (x : B) : (term377 B x) = (imp False).
Proof. exact (MK_COMB (@lem5046411) (@lem5046410 B x)). Qed.
Lemma lem5046414 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5046415 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem5046414 B P x). Qed.
Lemma lem5046416 {B : Type'} (u : B -> Prop) (x : B) : (@IN B x u) = (u x).
Proof. exact (@lem5046415 B u x). Qed.
Lemma lem5046417 {B : Type'} (u : B -> Prop) (x : B) : (term378 B x u) = (term379 B u x).
Proof. exact (MK_COMB (@lem5046412 B x) (@lem5046416 B u x)). Qed.
Lemma lem5046419 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem5046420 {B : Type'} (u : B -> Prop) (x : B) : (term379 B u x) = True.
Proof. exact (@lem5046419 (u x)). Qed.
Lemma lem5046421 {B : Type'} (x : B) (u : B -> Prop) : (term378 B x u) = True.
Proof. exact (TRANS (@lem5046417 B u x) (@lem5046420 B u x)). Qed.
Lemma lem5046422 {B : Type'} (u : B -> Prop) : (term380 B u) = (term381 B).
Proof. exact (fun_ext (fun x : B => @lem5046421 B x u)). Qed.
Lemma lem5046423 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5046424 {B : Type'} (u : B -> Prop) : (term345 B u) = (term382 B).
Proof. exact (MK_COMB (@lem5046423 B) (@lem5046422 B u)). Qed.
Lemma lem5046426 {A : Type'} (t : Prop) : (term383 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5046427 {B : Type'} (t : Prop) : (term383 B t) = t.
Proof. exact (@lem5046426 B t). Qed.
Lemma lem5046428 {B : Type'} : (term382 B) = True.
Proof. exact (@lem5046427 B True). Qed.
Lemma lem5046429 {B : Type'} (u : B -> Prop) : (term345 B u) = True.
Proof. exact (TRANS (@lem5046424 B u) (@lem5046428 B)). Qed.
Lemma lem5046430 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5046431 {B : Type'} (u : B -> Prop) : (term347 B u) = (and True).
Proof. exact (MK_COMB (@lem5046430) (@lem5046429 B u)). Qed.
Lemma lem5046439 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term60 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem5046440 {A : Type'} (p : A -> Prop) (x : A) : (term60 A x p) = (p x).
Proof. exact (@lem5046439 A p x). Qed.
Lemma lem5046441 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term384 A B x s f y) = (term385 A B s f y x).
Proof. exact (@lem5046440 A (term386 A B s f y) x). Qed.
Lemma lem5046442 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term385 A B s f y x) = (term387 A B s f x y).
Proof. exact (eq_refl (term385 A B s f y x)). Qed.
Lemma lem5046443 {A : Type'} (GEN_PVAR_220 : A) : (@SETSPEC A GEN_PVAR_220) = (@SETSPEC A GEN_PVAR_220).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_220)). Qed.
Lemma lem5046444 {A B : Type'} (GEN_PVAR_220 : A) (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term388 A B GEN_PVAR_220 s f y x) = (term389 A B GEN_PVAR_220 s f x y).
Proof. exact (MK_COMB (@lem5046443 A GEN_PVAR_220) (@lem5046442 A B s f x y)). Qed.
Lemma lem5046445 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5046446 {A B : Type'} (GEN_PVAR_220 : A) (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term390 A B GEN_PVAR_220 s f y x) = (term391 A B GEN_PVAR_220 s f y x).
Proof. exact (MK_COMB (@lem5046444 A B GEN_PVAR_220 s f x y) (@lem5046445 A x)). Qed.
Lemma lem5046447 {A B : Type'} (GEN_PVAR_220 : A) (s : A -> Prop) (f : A -> B) (y : B) : (term392 A B GEN_PVAR_220 s f y) = (term393 A B GEN_PVAR_220 s f y).
Proof. exact (fun_ext (fun x : A => @lem5046446 A B GEN_PVAR_220 s f y x)). Qed.
Lemma lem5046448 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5046449 {A B : Type'} (GEN_PVAR_220 : A) (s : A -> Prop) (f : A -> B) (y : B) : (term394 A B GEN_PVAR_220 s f y) = (term395 A B GEN_PVAR_220 s f y).
Proof. exact (MK_COMB (@lem5046448 A) (@lem5046447 A B GEN_PVAR_220 s f y)). Qed.
Lemma lem5046450 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term396 A B s f y) = (term397 A B s f y).
Proof. exact (fun_ext (fun GEN_PVAR_220 : A => @lem5046449 A B GEN_PVAR_220 s f y)). Qed.
Lemma lem5046451 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem5046452 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term398 A B s f y) = (term348 A B s f y).
Proof. exact (MK_COMB (@lem5046451 A) (@lem5046450 A B s f y)). Qed.
Lemma lem5046453 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem5046454 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (y : B) : (term384 A B x s f y) = (term399 A B x s f y).
Proof. exact (MK_COMB (@lem5046453 A x) (@lem5046452 A B s f y)). Qed.
Lemma lem5046455 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5046456 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (y : B) : (term400 A B x s f y) = (term401 A B x s f y).
Proof. exact (MK_COMB (@lem5046455) (@lem5046454 A B x s f y)). Qed.
Lemma lem5046457 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term385 A B s f y x) = (term387 A B s f x y).
Proof. exact (eq_refl (term385 A B s f y x)). Qed.
Lemma lem5046458 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : ((term384 A B x s f y) = (term385 A B s f y x)) = ((term399 A B x s f y) = (term387 A B s f x y)).
Proof. exact (MK_COMB (@lem5046456 A B x s f y) (@lem5046457 A B s f x y)). Qed.
Lemma lem5046459 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term399 A B x s f y) = (term387 A B s f x y).
Proof. exact (EQ_MP (@lem5046458 A B s f x y) (@lem5046441 A B s f y x)). Qed.
Lemma lem5046463 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5046464 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5046463 A P x). Qed.
Lemma lem5046465 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem5046464 A s x). Qed.
Lemma lem5046466 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5046467 {A : Type'} (s : A -> Prop) (x : A) : (term79 A x s) = (term80 A s x).
Proof. exact (MK_COMB (@lem5046466) (@lem5046465 A s x)). Qed.
Lemma lem5046469 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term363 A x y s) = (term364 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem5046470 {B : Type'} (y : B) (x : B) (s : B -> Prop) : (term363 B x y s) = (term364 B y x s).
Proof. exact (@lem5046469 B y x s). Qed.
Lemma lem5046471 {A B : Type'} (y : B) (f : A -> B) (x : A) : (term402 A B f x y) = (term403 A B y f x).
Proof. exact (@lem5046470 B y (f x) (@EMPTY B)). Qed.
Lemma lem5046477 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem5046478 {B : Type'} (x : B) : (@IN B x (@EMPTY B)) = False.
Proof. exact (@lem5046477 B x). Qed.
Lemma lem5046479 {A B : Type'} (f : A -> B) (x : A) : (term404 A B f x) = False.
Proof. exact (@lem5046478 B (f x)). Qed.
Lemma lem5046480 {A B : Type'} (f : A -> B) (x : A) (y : B) : (term405 A B f x y) = (term405 A B f x y).
Proof. exact (eq_refl (term405 A B f x y)). Qed.
Lemma lem5046481 {A B : Type'} (f : A -> B) (x : A) (y : B) : (term403 A B y f x) = (term406 A B f x y).
Proof. exact (MK_COMB (@lem5046480 A B f x y) (@lem5046479 A B f x)). Qed.
Lemma lem5046483 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem5046484 {A B : Type'} (f : A -> B) (x : A) (y : B) : (term406 A B f x y) = ((f x) = y).
Proof. exact (@lem5046483 ((f x) = y)). Qed.
Lemma lem5046487 {A B : Type'} (f : A -> B) (x : A) (y : B) : (term403 A B y f x) = ((f x) = y).
Proof. exact (TRANS (@lem5046481 A B f x y) (@lem5046484 A B f x y)). Qed.
Lemma lem5046488 {A B : Type'} (f : A -> B) (x : A) (y : B) : (term402 A B f x y) = ((f x) = y).
Proof. exact (TRANS (@lem5046471 A B y f x) (@lem5046487 A B f x y)). Qed.
Lemma lem5046489 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term387 A B s f x y) = (term407 A B s f x y).
Proof. exact (MK_COMB (@lem5046467 A s x) (@lem5046488 A B f x y)). Qed.
Lemma lem5046492 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term399 A B x s f y) = (term407 A B s f x y).
Proof. exact (TRANS (@lem5046459 A B s f x y) (@lem5046489 A B s f x y)). Qed.
Lemma lem5046493 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5046494 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term401 A B x s f y) = (term408 A B s f x y).
Proof. exact (MK_COMB (@lem5046493) (@lem5046492 A B s f x y)). Qed.
Lemma lem5046496 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term60 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem5046497 {A : Type'} (p : A -> Prop) (x : A) : (term60 A x p) = (p x).
Proof. exact (@lem5046496 A p x). Qed.
Lemma lem5046498 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term409 A B x s f) = (term410 A B s f x).
Proof. exact (@lem5046497 A (term411 A B s f) x). Qed.
Lemma lem5046499 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term410 A B s f x) = (term412 A B s f x).
Proof. exact (eq_refl (term410 A B s f x)). Qed.
Lemma lem5046500 {A : Type'} (GEN_PVAR_221 : A) : (@SETSPEC A GEN_PVAR_221) = (@SETSPEC A GEN_PVAR_221).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_221)). Qed.
Lemma lem5046501 {A B : Type'} (GEN_PVAR_221 : A) (s : A -> Prop) (f : A -> B) (x : A) : (term413 A B GEN_PVAR_221 s f x) = (term414 A B GEN_PVAR_221 s f x).
Proof. exact (MK_COMB (@lem5046500 A GEN_PVAR_221) (@lem5046499 A B s f x)). Qed.
Lemma lem5046502 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5046503 {A B : Type'} (GEN_PVAR_221 : A) (s : A -> Prop) (f : A -> B) (x : A) : (term415 A B GEN_PVAR_221 s f x) = (term416 A B GEN_PVAR_221 s f x).
Proof. exact (MK_COMB (@lem5046501 A B GEN_PVAR_221 s f x) (@lem5046502 A x)). Qed.
Lemma lem5046504 {A B : Type'} (GEN_PVAR_221 : A) (s : A -> Prop) (f : A -> B) : (term417 A B GEN_PVAR_221 s f) = (term418 A B GEN_PVAR_221 s f).
Proof. exact (fun_ext (fun x : A => @lem5046503 A B GEN_PVAR_221 s f x)). Qed.
Lemma lem5046505 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5046506 {A B : Type'} (GEN_PVAR_221 : A) (s : A -> Prop) (f : A -> B) : (term419 A B GEN_PVAR_221 s f) = (term420 A B GEN_PVAR_221 s f).
Proof. exact (MK_COMB (@lem5046505 A) (@lem5046504 A B GEN_PVAR_221 s f)). Qed.
Lemma lem5046507 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term421 A B s f) = (term422 A B s f).
Proof. exact (fun_ext (fun GEN_PVAR_221 : A => @lem5046506 A B GEN_PVAR_221 s f)). Qed.
Lemma lem5046508 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem5046509 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term423 A B s f) = (term349 A B s f).
Proof. exact (MK_COMB (@lem5046508 A) (@lem5046507 A B s f)). Qed.
Lemma lem5046510 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem5046511 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) : (term409 A B x s f) = (term424 A B x s f).
Proof. exact (MK_COMB (@lem5046510 A x) (@lem5046509 A B s f)). Qed.
Lemma lem5046512 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5046513 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) : (term425 A B x s f) = (term426 A B x s f).
Proof. exact (MK_COMB (@lem5046512) (@lem5046511 A B x s f)). Qed.
Lemma lem5046514 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term410 A B s f x) = (term412 A B s f x).
Proof. exact (eq_refl (term410 A B s f x)). Qed.
Lemma lem5046515 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : ((term409 A B x s f) = (term410 A B s f x)) = ((term424 A B x s f) = (term412 A B s f x)).
Proof. exact (MK_COMB (@lem5046513 A B x s f) (@lem5046514 A B s f x)). Qed.
Lemma lem5046516 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term424 A B x s f) = (term412 A B s f x).
Proof. exact (EQ_MP (@lem5046515 A B s f x) (@lem5046498 A B s f x)). Qed.
Lemma lem5046520 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5046521 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5046520 A P x). Qed.
Lemma lem5046522 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem5046521 A s x). Qed.
Lemma lem5046523 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5046524 {A : Type'} (s : A -> Prop) (x : A) : (term79 A x s) = (term80 A s x).
Proof. exact (MK_COMB (@lem5046523) (@lem5046522 A s x)). Qed.
Lemma lem5046526 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem5046527 {B : Type'} (x : B) : (@IN B x (@EMPTY B)) = False.
Proof. exact (@lem5046526 B x). Qed.
Lemma lem5046528 {A B : Type'} (f : A -> B) (x : A) : (term404 A B f x) = False.
Proof. exact (@lem5046527 B (f x)). Qed.
Lemma lem5046529 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term412 A B s f x) = (term427 A s x).
Proof. exact (MK_COMB (@lem5046524 A s x) (@lem5046528 A B f x)). Qed.
Lemma lem5046531 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem5046532 {A : Type'} (s : A -> Prop) (x : A) : (term427 A s x) = False.
Proof. exact (@lem5046531 (s x)). Qed.
Lemma lem5046533 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term412 A B s f x) = False.
Proof. exact (TRANS (@lem5046529 A B f s x) (@lem5046532 A s x)). Qed.
Lemma lem5046534 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) : (term424 A B x s f) = False.
Proof. exact (TRANS (@lem5046516 A B s f x) (@lem5046533 A B s f x)). Qed.
Lemma lem5046535 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : ((term399 A B x s f y) = (term424 A B x s f)) = ((term407 A B s f x y) = False).
Proof. exact (MK_COMB (@lem5046494 A B s f x y) (@lem5046534 A B x s f)). Qed.
Lemma lem5046537 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem5046538 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : ((term407 A B s f x y) = False) = (term428 A B s f x y).
Proof. exact (@lem5046537 (term407 A B s f x y)). Qed.
Lemma lem5046543 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : ((term399 A B x s f y) = (term424 A B x s f)) = (term428 A B s f x y).
Proof. exact (TRANS (@lem5046535 A B s f x y) (@lem5046538 A B s f x y)). Qed.
Lemma lem5046544 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term429 A B y s f) = (term430 A B s f y).
Proof. exact (fun_ext (fun x : A => @lem5046543 A B s f x y)). Qed.
Lemma lem5046545 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5046546 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term350 A B y s f) = (term431 A B s f y).
Proof. exact (MK_COMB (@lem5046545 A) (@lem5046544 A B s f y)). Qed.
Lemma lem5046551 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term352 A B u y s f) = (term432 A B s f y).
Proof. exact (MK_COMB (@lem5046431 B u) (@lem5046546 A B s f y)). Qed.
Lemma lem5046553 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5046554 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term432 A B s f y) = (term431 A B s f y).
Proof. exact (@lem5046553 (term431 A B s f y)). Qed.
Lemma lem5046563 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term352 A B u y s f) = (term431 A B s f y).
Proof. exact (TRANS (@lem5046551 A B u s f y) (@lem5046554 A B s f y)). Qed.
Lemma lem5046564 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term354 A B u y s f) = (term433 A B u s f y).
Proof. exact (MK_COMB (@lem5046399 B y u) (@lem5046563 A B u s f y)). Qed.
Lemma lem5046567 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5046568 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term356 A B u y s f) = (term434 A B u s f y).
Proof. exact (MK_COMB (@lem5046567) (@lem5046564 A B u s f y)). Qed.
Lemma lem5046576 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term363 A x y s) = (term364 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem5046577 {B : Type'} (y : B) (x : B) (s : B -> Prop) : (term363 B x y s) = (term364 B y x s).
Proof. exact (@lem5046576 B y x s). Qed.
Lemma lem5046578 {B : Type'} (y : B) (x : B) : (term365 B x y) = (term366 B y x).
Proof. exact (@lem5046577 B y x (@EMPTY B)). Qed.
Lemma lem5046584 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem5046585 {B : Type'} (x : B) : (@IN B x (@EMPTY B)) = False.
Proof. exact (@lem5046584 B x). Qed.
Lemma lem5046586 {B : Type'} (x : B) (y : B) : (term367 B x y) = (term367 B x y).
Proof. exact (eq_refl (term367 B x y)). Qed.
Lemma lem5046587 {B : Type'} (x : B) (y : B) : (term366 B y x) = (term368 B x y).
Proof. exact (MK_COMB (@lem5046586 B x y) (@lem5046585 B x)). Qed.
Lemma lem5046589 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem5046590 {B : Type'} (x : B) (y : B) : (term368 B x y) = (x = y).
Proof. exact (@lem5046589 (x = y)). Qed.
Lemma lem5046593 {B : Type'} (x : B) (y : B) : (term366 B y x) = (x = y).
Proof. exact (TRANS (@lem5046587 B x y) (@lem5046590 B x y)). Qed.
Lemma lem5046594 {B : Type'} (x : B) (y : B) : (term365 B x y) = (x = y).
Proof. exact (TRANS (@lem5046578 B y x) (@lem5046593 B x y)). Qed.
Lemma lem5046595 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5046596 {B : Type'} (x : B) (y : B) : (term435 B x y) = (term436 B x y).
Proof. exact (MK_COMB (@lem5046595) (@lem5046594 B x y)). Qed.
Lemma lem5046598 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem5046599 {B : Type'} (x : B) : (@IN B x (@EMPTY B)) = False.
Proof. exact (@lem5046598 B x). Qed.
Lemma lem5046600 {B : Type'} (x : B) (y : B) : ((term365 B x y) = (@IN B x (@EMPTY B))) = ((x = y) = False).
Proof. exact (MK_COMB (@lem5046596 B x y) (@lem5046599 B x)). Qed.
Lemma lem5046602 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem5046603 {B : Type'} (x : B) (y : B) : ((x = y) = False) = (term266 B x y).
Proof. exact (@lem5046602 (x = y)). Qed.
Lemma lem5046606 {B : Type'} (x : B) (y : B) : ((term365 B x y) = (@IN B x (@EMPTY B))) = (term266 B x y).
Proof. exact (TRANS (@lem5046600 B x y) (@lem5046603 B x y)). Qed.
Lemma lem5046607 {B : Type'} (y : B) : (term437 B y) = (term438 B y).
Proof. exact (fun_ext (fun x : B => @lem5046606 B x y)). Qed.
Lemma lem5046608 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5046609 {B : Type'} (y : B) : (term357 B y) = (term439 B y).
Proof. exact (MK_COMB (@lem5046608 B) (@lem5046607 B y)). Qed.
Lemma lem5046614 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term358 A B u s f y) = (term440 A B u s f y).
Proof. exact (MK_COMB (@lem5046568 A B u s f y) (@lem5046609 B y)). Qed.
Lemma lem5046617 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5046618 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term360 A B u s f y) = (term441 A B u s f y).
Proof. exact (MK_COMB (@lem5046617) (@lem5046614 A B u s f y)). Qed.
Lemma lem5046622 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5046623 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem5046622 B P x). Qed.
Lemma lem5046624 {B : Type'} (u : B -> Prop) (y : B) : (@IN B y u) = (u y).
Proof. exact (@lem5046623 B u y). Qed.
Lemma lem5046625 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5046626 {B : Type'} (u : B -> Prop) (y : B) : (term38 B y u) = (term39 B u y).
Proof. exact (MK_COMB (@lem5046625) (@lem5046624 B u y)). Qed.
Lemma lem5046628 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term40 A B y f s) = (term41 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem5046629 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term40 A B y f s) = (term41 A B y f s).
Proof. exact (@lem5046628 A B y f s). Qed.
Lemma lem5046639 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5046640 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5046639 A P x). Qed.
Lemma lem5046641 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem5046640 A s x). Qed.
Lemma lem5046642 {A B : Type'} (y : B) (f : A -> B) (x : A) : (term42 A B y f x) = (term42 A B y f x).
Proof. exact (eq_refl (term42 A B y f x)). Qed.
Lemma lem5046643 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (x : A) : (term43 A B y f x s) = (term44 A B y f s x).
Proof. exact (MK_COMB (@lem5046642 A B y f x) (@lem5046641 A s x)). Qed.
Lemma lem5046646 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term45 A B y f s) = (term46 A B y f s).
Proof. exact (fun_ext (fun x : A => @lem5046643 A B y f s x)). Qed.
Lemma lem5046647 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5046648 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term41 A B y f s) = (term47 A B y f s).
Proof. exact (MK_COMB (@lem5046647 A) (@lem5046646 A B y f s)). Qed.
Lemma lem5046653 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term40 A B y f s) = (term47 A B y f s).
Proof. exact (TRANS (@lem5046629 A B y f s) (@lem5046648 A B y f s)). Qed.
Lemma lem5046654 {A B : Type'} (u : B -> Prop) (y : B) (f : A -> B) (s : A -> Prop) : (term48 A B u y f s) = (term49 A B u y f s).
Proof. exact (MK_COMB (@lem5046626 B u y) (@lem5046653 A B y f s)). Qed.
Lemma lem5046657 {A B : Type'} (u : B -> Prop) (y : B) (f : A -> B) (s : A -> Prop) : (term362 A B u y f s) = (term442 A B u y f s).
Proof. exact (MK_COMB (@lem5046618 A B u s f y) (@lem5046654 A B u y f s)). Qed.
Lemma lem5046660 {A B : Type'} (u : B -> Prop) (y : B) (f : A -> B) (s : A -> Prop) : (term442 A B u y f s) = (term362 A B u y f s).
Proof. exact (SYM (@lem5046657 A B u y f s)). Qed.
Lemma lem5046662 (p : Prop) : p = (term102 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5046663 {A B : Type'} (u : B -> Prop) (y : B) (f : A -> B) (s : A -> Prop) : (term442 A B u y f s) = (term443 A B u y f s).
Proof. exact (@lem5046662 (term442 A B u y f s)). Qed.
Lemma lem5046664 {A B : Type'} (u : B -> Prop) (y : B) (f : A -> B) (s : A -> Prop) : (term443 A B u y f s) = (term442 A B u y f s).
Proof. exact (SYM (@lem5046663 A B u y f s)). Qed.
Lemma lem5046665 {A B : Type'} (u : B -> Prop) (y : B) (f : A -> B) (s : A -> Prop) (h1 : term444 A B u y f s) : term444 A B u y f s.
Proof. exact (h1). Qed.
Lemma lem5046668 {A B : Type'} (u : B -> Prop) (y : B) (f : A -> B) (s : A -> Prop) (h1 : term443 A B u y f s) : term443 A B u y f s.
Proof. exact (h1). Qed.
Lemma lem5046669 {A B : Type'} (u : B -> Prop) (y : B) (f : A -> B) (s : A -> Prop) : term445 A B u y f s.
Proof. exact (fun h0 : term443 A B u y f s => @lem5046668 A B u y f s h0). Qed.
Lemma lem5046670 {A B : Type'} (u : B -> Prop) (y : B) (f : A -> B) (s : A -> Prop) (h1 : term445 A B u y f s) : term445 A B u y f s.
Proof. exact (h1). Qed.
Lemma lem5046671 {A B : Type'} (u : B -> Prop) (y : B) (f : A -> B) (s : A -> Prop) (h1 : term443 A B u y f s) : term443 A B u y f s.
Proof. exact (h1). Qed.
Lemma lem5046672 {A B : Type'} (u : B -> Prop) (y : B) (f : A -> B) (s : A -> Prop) (h1 : term443 A B u y f s) (h2 : term445 A B u y f s) : term443 A B u y f s.
Proof. exact (@lem5046670 A B u y f s h2 (@lem5046671 A B u y f s h1)). Qed.
Lemma lem5046673 {A B : Type'} (u : B -> Prop) (y : B) (f : A -> B) (s : A -> Prop) (h1 : term443 A B u y f s) : term446 A B u y f s.
Proof. exact (fun h0 : term445 A B u y f s => @lem5046672 A B u y f s h1 h0). Qed.
Lemma lem5046674 {A B : Type'} (u : B -> Prop) (y : B) (f : A -> B) (s : A -> Prop) (h1 : term445 A B u y f s) : term445 A B u y f s.
Proof. exact (h1). Qed.
Lemma lem5046675 {A B : Type'} (u : B -> Prop) (y : B) (f : A -> B) (s : A -> Prop) (h1 : term443 A B u y f s) (h2 : term445 A B u y f s) : term443 A B u y f s.
Proof. exact (@lem5046673 A B u y f s h1 (@lem5046674 A B u y f s h2)). Qed.
Lemma lem5046676 {A B : Type'} (u : B -> Prop) (y : B) (f : A -> B) (s : A -> Prop) (h1 : term445 A B u y f s) : term445 A B u y f s.
Proof. exact (fun h0 : term443 A B u y f s => @lem5046675 A B u y f s h0 h1). Qed.
Lemma lem5046677 {A B : Type'} (u : B -> Prop) (y : B) (f : A -> B) (s : A -> Prop) : term447 A B u y f s.
Proof. exact (fun h0 : term445 A B u y f s => @lem5046676 A B u y f s h0). Qed.
Lemma lem5046680 {A B : Type'} (u : B -> Prop) (y : B) (f : A -> B) (s : A -> Prop) : term445 A B u y f s.
Proof. exact (@lem5046677 A B u y f s (@lem5046669 A B u y f s)). Qed.
Lemma lem5046681 {A B : Type'} (u : B -> Prop) (y : B) (f : A -> B) (s : A -> Prop) : term445 A B u y f s.
Proof. exact (@lem5046680 A B u y f s). Qed.
Lemma lem5046699 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5046700 {A B : Type'} (u : B -> Prop) (y : B) (f : A -> B) (s : A -> Prop) : (term443 A B u y f s) = (term448 A B u y f s).
Proof. exact (@lem5046699 (term444 A B u y f s)). Qed.
Lemma lem5046702 (t : Prop) : (term109 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5046703 {A B : Type'} (u : B -> Prop) (y : B) (f : A -> B) (s : A -> Prop) : (term448 A B u y f s) = (term442 A B u y f s).
Proof. exact (@lem5046702 (term442 A B u y f s)). Qed.
Lemma lem5046706 {A B : Type'} (u : B -> Prop) (y : B) (f : A -> B) (s : A -> Prop) : (term443 A B u y f s) = (term442 A B u y f s).
Proof. exact (TRANS (@lem5046700 A B u y f s) (@lem5046703 A B u y f s)). Qed.
Lemma lem5046763 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term449 A B y f s) = (term450 A B y f s).
Proof. exact (fun_ext (fun u : B -> Prop => @lem5046706 A B u y f s)). Qed.
Lemma lem5046764 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5046765 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term451 A B y f s) = (term452 A B y f s).
Proof. exact (MK_COMB (@lem5046764 B) (@lem5046763 A B y f s)). Qed.
Lemma lem5046770 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term453 A B f s) = (term454 A B f s).
Proof. exact (fun_ext (fun y : B => @lem5046765 A B y f s)). Qed.
Lemma lem5046771 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5046772 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term455 A B f s) = (term456 A B f s).
Proof. exact (MK_COMB (@lem5046771 B) (@lem5046770 A B f s)). Qed.
Lemma lem5046777 {A B : Type'} (s : A -> Prop) : (term457 A B s) = (term458 A B s).
Proof. exact (fun_ext (fun f : A -> B => @lem5046772 A B f s)). Qed.
Lemma lem5046778 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5046779 {A B : Type'} (s : A -> Prop) : (term459 A B s) = (term460 A B s).
Proof. exact (MK_COMB (@lem5046778 A B) (@lem5046777 A B s)). Qed.
Lemma lem5046784 {A B : Type'} : (term461 A B) = (term462 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5046779 A B s)). Qed.
Lemma lem5046785 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5046794 {A B : Type'} : (term463 A B) = (term464 A B).
Proof. exact (MK_COMB (@lem5046785 A) (@lem5046784 A B)). Qed.
Lemma lem5046799 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (x : A) : (term44 A B y f s x) = (term44 A B y f s x).
Proof. exact (eq_refl (term44 A B y f s x)). Qed.
Lemma lem5046800 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term46 A B y f s) = (term46 A B y f s).
Proof. exact (fun_ext (fun x : A => @lem5046799 A B y f s x)). Qed.
Lemma lem5046801 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5046802 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term47 A B y f s) = (term47 A B y f s).
Proof. exact (MK_COMB (@lem5046801 A) (@lem5046800 A B y f s)). Qed.
Lemma lem5046805 {B : Type'} (u : B -> Prop) (y : B) : (term39 B u y) = (term39 B u y).
Proof. exact (eq_refl (term39 B u y)). Qed.
Lemma lem5046806 {A B : Type'} (u : B -> Prop) (y : B) (f : A -> B) (s : A -> Prop) : (term49 A B u y f s) = (term49 A B u y f s).
Proof. exact (MK_COMB (@lem5046805 B u y) (@lem5046802 A B y f s)). Qed.
Lemma lem5046809 {B : Type'} (x : B) (y : B) : (term266 B x y) = (term266 B x y).
Proof. exact (eq_refl (term266 B x y)). Qed.
Lemma lem5046810 {B : Type'} (y : B) : (term438 B y) = (term438 B y).
Proof. exact (fun_ext (fun x : B => @lem5046809 B x y)). Qed.
Lemma lem5046811 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5046812 {B : Type'} (y : B) : (term439 B y) = (term439 B y).
Proof. exact (MK_COMB (@lem5046811 B) (@lem5046810 B y)). Qed.
Lemma lem5046819 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term428 A B s f x y) = (term428 A B s f x y).
Proof. exact (eq_refl (term428 A B s f x y)). Qed.
Lemma lem5046820 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term430 A B s f y) = (term430 A B s f y).
Proof. exact (fun_ext (fun x : A => @lem5046819 A B s f x y)). Qed.
Lemma lem5046821 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5046822 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term431 A B s f y) = (term431 A B s f y).
Proof. exact (MK_COMB (@lem5046821 A) (@lem5046820 A B s f y)). Qed.
Lemma lem5046827 {B : Type'} (y : B) (u : B -> Prop) (x : B) : (term372 B y u x) = (term372 B y u x).
Proof. exact (eq_refl (term372 B y u x)). Qed.
Lemma lem5046828 {B : Type'} (y : B) (u : B -> Prop) : (term374 B y u) = (term374 B y u).
Proof. exact (fun_ext (fun x : B => @lem5046827 B y u x)). Qed.
Lemma lem5046829 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5046830 {B : Type'} (y : B) (u : B -> Prop) : (term375 B y u) = (term375 B y u).
Proof. exact (MK_COMB (@lem5046829 B) (@lem5046828 B y u)). Qed.
Lemma lem5046831 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5046832 {B : Type'} (y : B) (u : B -> Prop) : (term376 B y u) = (term376 B y u).
Proof. exact (MK_COMB (@lem5046831) (@lem5046830 B y u)). Qed.
Lemma lem5046833 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term433 A B u s f y) = (term433 A B u s f y).
Proof. exact (MK_COMB (@lem5046832 B y u) (@lem5046822 A B s f y)). Qed.
Lemma lem5046834 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5046835 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term434 A B u s f y) = (term434 A B u s f y).
Proof. exact (MK_COMB (@lem5046834) (@lem5046833 A B u s f y)). Qed.
Lemma lem5046836 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term440 A B u s f y) = (term440 A B u s f y).
Proof. exact (MK_COMB (@lem5046835 A B u s f y) (@lem5046812 B y)). Qed.
Lemma lem5046837 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5046838 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term441 A B u s f y) = (term441 A B u s f y).
Proof. exact (MK_COMB (@lem5046837) (@lem5046836 A B u s f y)). Qed.
Lemma lem5046839 {A B : Type'} (u : B -> Prop) (y : B) (f : A -> B) (s : A -> Prop) : (term442 A B u y f s) = (term442 A B u y f s).
Proof. exact (MK_COMB (@lem5046838 A B u s f y) (@lem5046806 A B u y f s)). Qed.
Lemma lem5046840 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term450 A B y f s) = (term450 A B y f s).
Proof. exact (fun_ext (fun u : B -> Prop => @lem5046839 A B u y f s)). Qed.
Lemma lem5046841 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5046842 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term452 A B y f s) = (term452 A B y f s).
Proof. exact (MK_COMB (@lem5046841 B) (@lem5046840 A B y f s)). Qed.
Lemma lem5046843 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term454 A B f s) = (term454 A B f s).
Proof. exact (fun_ext (fun y : B => @lem5046842 A B y f s)). Qed.
Lemma lem5046844 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5046845 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term456 A B f s) = (term456 A B f s).
Proof. exact (MK_COMB (@lem5046844 B) (@lem5046843 A B f s)). Qed.
Lemma lem5046846 {A B : Type'} (s : A -> Prop) : (term458 A B s) = (term458 A B s).
Proof. exact (fun_ext (fun f : A -> B => @lem5046845 A B f s)). Qed.
Lemma lem5046847 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5046848 {A B : Type'} (s : A -> Prop) : (term460 A B s) = (term460 A B s).
Proof. exact (MK_COMB (@lem5046847 A B) (@lem5046846 A B s)). Qed.
Lemma lem5046849 {A B : Type'} : (term462 A B) = (term462 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5046848 A B s)). Qed.
Lemma lem5046850 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5046851 {A B : Type'} : (term464 A B) = (term464 A B).
Proof. exact (MK_COMB (@lem5046850 A) (@lem5046849 A B)). Qed.
Lemma lem5046916 {A B : Type'} : (term463 A B) = (term464 A B).
Proof. exact (TRANS (@lem5046794 A B) (@lem5046851 A B)). Qed.
Lemma lem5046917 {A B : Type'} : (term464 A B) = (term463 A B).
Proof. exact (SYM (@lem5046916 A B)). Qed.
Lemma lem5046918 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) (h1 : term440 A B u s f y) : term440 A B u s f y.
Proof. exact (h1). Qed.
Lemma lem5046921 (p : Prop) : p = (term102 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5046922 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term47 A B y f s) = (term465 A B y f s).
Proof. exact (@lem5046921 (term47 A B y f s)). Qed.
Lemma lem5046923 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term465 A B y f s) = (term47 A B y f s).
Proof. exact (SYM (@lem5046922 A B y f s)). Qed.
Lemma lem5046924 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (h1 : term466 A B y f s) : term466 A B y f s.
Proof. exact (h1). Qed.
Lemma lem5046931 {B : Type'} (y : B) (u : B -> Prop) (x : B) : (term467 B y u x) = (term468 B y u x).
Proof. exact (@lem17362 (x = y) (u x)). Qed.
Lemma lem5046932 {B : Type'} (P : B -> Prop) : (term469 B P) = (term470 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem5046933 {B : Type'} (y : B) (u : B -> Prop) : (term471 B y u) = (term472 B y u).
Proof. exact (@lem5046932 B (term374 B y u)). Qed.
Lemma lem5046934 {B : Type'} (y : B) (u : B -> Prop) (x : B) : (term473 B y u x) = (term372 B y u x).
Proof. exact (eq_refl (term473 B y u x)). Qed.
Lemma lem5046935 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5046936 {B : Type'} (y : B) (u : B -> Prop) (x : B) : (term474 B y u x) = (term467 B y u x).
Proof. exact (MK_COMB (@lem5046935) (@lem5046934 B y u x)). Qed.
Lemma lem5046937 {B : Type'} (y : B) (u : B -> Prop) (x : B) : (term474 B y u x) = (term468 B y u x).
Proof. exact (TRANS (@lem5046936 B y u x) (@lem5046931 B y u x)). Qed.
Lemma lem5046938 {B : Type'} (y : B) (u : B -> Prop) : (term475 B y u) = (term476 B y u).
Proof. exact (fun_ext (fun x : B => @lem5046937 B y u x)). Qed.
Lemma lem5046939 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5046940 {B : Type'} (y : B) (u : B -> Prop) : (term472 B y u) = (term477 B y u).
Proof. exact (MK_COMB (@lem5046939 B) (@lem5046938 B y u)). Qed.
Lemma lem5046941 {B : Type'} (y : B) (u : B -> Prop) : (term471 B y u) = (term477 B y u).
Proof. exact (TRANS (@lem5046933 B y u) (@lem5046940 B y u)). Qed.
Lemma lem5046948 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term478 A B s f x y) = (term407 A B s f x y).
Proof. exact (@lem16933 (term407 A B s f x y)). Qed.
Lemma lem5046949 {A : Type'} (P : A -> Prop) : (term469 A P) = (term470 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem5046950 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term479 A B s f y) = (term480 A B s f y).
Proof. exact (@lem5046949 A (term430 A B s f y)). Qed.
Lemma lem5046951 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term481 A B s f y x) = (term428 A B s f x y).
Proof. exact (eq_refl (term481 A B s f y x)). Qed.
Lemma lem5046952 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5046953 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term482 A B s f y x) = (term478 A B s f x y).
Proof. exact (MK_COMB (@lem5046952) (@lem5046951 A B s f x y)). Qed.
Lemma lem5046954 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term482 A B s f y x) = (term407 A B s f x y).
Proof. exact (TRANS (@lem5046953 A B s f x y) (@lem5046948 A B s f x y)). Qed.
Lemma lem5046955 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term483 A B s f y) = (term484 A B s f y).
Proof. exact (fun_ext (fun x : A => @lem5046954 A B s f x y)). Qed.
Lemma lem5046956 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5046957 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term480 A B s f y) = (term485 A B s f y).
Proof. exact (MK_COMB (@lem5046956 A) (@lem5046955 A B s f y)). Qed.
Lemma lem5046958 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term479 A B s f y) = (term485 A B s f y).
Proof. exact (TRANS (@lem5046950 A B s f y) (@lem5046957 A B s f y)). Qed.
Lemma lem5046959 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5046960 {B : Type'} (y : B) (u : B -> Prop) : (term486 B y u) = (term487 B y u).
Proof. exact (MK_COMB (@lem5046959) (@lem5046941 B y u)). Qed.
Lemma lem5046961 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term488 A B u s f y) = (term489 A B u s f y).
Proof. exact (MK_COMB (@lem5046960 B y u) (@lem5046958 A B s f y)). Qed.
Lemma lem5046962 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term490 A B u s f y) = (term488 A B u s f y).
Proof. exact (@lem17045 (term375 B y u) (term431 A B s f y)). Qed.
Lemma lem5046963 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term490 A B u s f y) = (term489 A B u s f y).
Proof. exact (TRANS (@lem5046962 A B u s f y) (@lem5046961 A B u s f y)). Qed.
Lemma lem5046964 {B : Type'} (x : B) (y : B) : (term266 B x y) = (term266 B x y).
Proof. exact (eq_refl (term266 B x y)). Qed.
Lemma lem5046965 {B : Type'} (y : B) : (term438 B y) = (term438 B y).
Proof. exact (fun_ext (fun x : B => @lem5046964 B x y)). Qed.
Lemma lem5046966 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5046967 {B : Type'} (y : B) : (term439 B y) = (term439 B y).
Proof. exact (MK_COMB (@lem5046966 B) (@lem5046965 B y)). Qed.
Lemma lem5046968 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5046969 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term491 A B u s f y) = (term492 A B u s f y).
Proof. exact (MK_COMB (@lem5046968) (@lem5046963 A B u s f y)). Qed.
Lemma lem5046970 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term493 A B u s f y) = (term494 A B u s f y).
Proof. exact (MK_COMB (@lem5046969 A B u s f y) (@lem5046967 B y)). Qed.
Lemma lem5046971 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term440 A B u s f y) = (term493 A B u s f y).
Proof. exact (@lem17265 (term433 A B u s f y) (term439 B y)). Qed.
Lemma lem5046972 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term440 A B u s f y) = (term494 A B u s f y).
Proof. exact (TRANS (@lem5046971 A B u s f y) (@lem5046970 A B u s f y)). Qed.
Lemma lem5047057 {A : Type'} (P : A -> Prop) (Q : Prop) : (term495 A P Q) = (term496 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5047058 {B : Type'} (P : B -> Prop) (Q : Prop) : (term495 B P Q) = (term496 B P Q).
Proof. exact (@lem5047057 B P Q). Qed.
Lemma lem5047059 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term497 A B u s f y) = (term498 A B u s f y).
Proof. exact (@lem5047058 B (term476 B y u) (term485 A B s f y)). Qed.
Lemma lem5047060 {B : Type'} (y : B) (u : B -> Prop) (x : B) : (term499 B y u x) = (term468 B y u x).
Proof. exact (eq_refl (term499 B y u x)). Qed.
Lemma lem5047061 {B : Type'} (y : B) (u : B -> Prop) : (term500 B y u) = (term476 B y u).
Proof. exact (fun_ext (fun x : B => @lem5047060 B y u x)). Qed.
Lemma lem5047062 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5047063 {B : Type'} (y : B) (u : B -> Prop) : (term501 B y u) = (term477 B y u).
Proof. exact (MK_COMB (@lem5047062 B) (@lem5047061 B y u)). Qed.
Lemma lem5047064 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5047065 {B : Type'} (y : B) (u : B -> Prop) : (term502 B y u) = (term487 B y u).
Proof. exact (MK_COMB (@lem5047064) (@lem5047063 B y u)). Qed.
Lemma lem5047066 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term485 A B s f y) = (term485 A B s f y).
Proof. exact (eq_refl (term485 A B s f y)). Qed.
Lemma lem5047067 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term497 A B u s f y) = (term489 A B u s f y).
Proof. exact (MK_COMB (@lem5047065 B y u) (@lem5047066 A B s f y)). Qed.
Lemma lem5047068 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5047069 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term503 A B u s f y) = (term504 A B u s f y).
Proof. exact (MK_COMB (@lem5047068) (@lem5047067 A B u s f y)). Qed.
Lemma lem5047070 {B : Type'} (y : B) (u : B -> Prop) (x : B) : (term499 B y u x) = (term468 B y u x).
Proof. exact (eq_refl (term499 B y u x)). Qed.
Lemma lem5047071 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5047072 {B : Type'} (y : B) (u : B -> Prop) (x : B) : (term505 B y u x) = (term506 B y u x).
Proof. exact (MK_COMB (@lem5047071) (@lem5047070 B y u x)). Qed.
Lemma lem5047073 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term485 A B s f y) = (term485 A B s f y).
Proof. exact (eq_refl (term485 A B s f y)). Qed.
Lemma lem5047074 {A B : Type'} (u : B -> Prop) (x : B) (s : A -> Prop) (f : A -> B) (y : B) : (term507 A B u x s f y) = (term508 A B u x s f y).
Proof. exact (MK_COMB (@lem5047072 B y u x) (@lem5047073 A B s f y)). Qed.
Lemma lem5047075 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term509 A B u s f y) = (term510 A B u s f y).
Proof. exact (fun_ext (fun x : B => @lem5047074 A B u x s f y)). Qed.
Lemma lem5047076 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5047077 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term498 A B u s f y) = (term511 A B u s f y).
Proof. exact (MK_COMB (@lem5047076 B) (@lem5047075 A B u s f y)). Qed.
Lemma lem5047078 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : ((term497 A B u s f y) = (term498 A B u s f y)) = ((term489 A B u s f y) = (term511 A B u s f y)).
Proof. exact (MK_COMB (@lem5047069 A B u s f y) (@lem5047077 A B u s f y)). Qed.
Lemma lem5047079 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term489 A B u s f y) = (term511 A B u s f y).
Proof. exact (EQ_MP (@lem5047078 A B u s f y) (@lem5047059 A B u s f y)). Qed.
Lemma lem5047081 {A : Type'} (P : Prop) (Q : A -> Prop) : (term128 A P Q) = (term129 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5047082 {A : Type'} (P : Prop) (Q : A -> Prop) : (term128 A P Q) = (term129 A P Q).
Proof. exact (@lem5047081 A P Q). Qed.
Lemma lem5047083 {A B : Type'} (u : B -> Prop) (x : B) (s : A -> Prop) (f : A -> B) (y : B) : (term512 A B u x s f y) = (term513 A B u x s f y).
Proof. exact (@lem5047082 A (term468 B y u x) (term484 A B s f y)). Qed.
Lemma lem5047084 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term514 A B s f y x) = (term407 A B s f x y).
Proof. exact (eq_refl (term514 A B s f y x)). Qed.
Lemma lem5047085 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term515 A B s f y) = (term484 A B s f y).
Proof. exact (fun_ext (fun x : A => @lem5047084 A B s f x y)). Qed.
Lemma lem5047086 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5047087 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term516 A B s f y) = (term485 A B s f y).
Proof. exact (MK_COMB (@lem5047086 A) (@lem5047085 A B s f y)). Qed.
Lemma lem5047088 {B : Type'} (y : B) (u : B -> Prop) (x : B) : (term506 B y u x) = (term506 B y u x).
Proof. exact (eq_refl (term506 B y u x)). Qed.
Lemma lem5047089 {A B : Type'} (u : B -> Prop) (x : B) (s : A -> Prop) (f : A -> B) (y : B) : (term512 A B u x s f y) = (term508 A B u x s f y).
Proof. exact (MK_COMB (@lem5047088 B y u x) (@lem5047087 A B s f y)). Qed.
Lemma lem5047090 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5047091 {A B : Type'} (u : B -> Prop) (x : B) (s : A -> Prop) (f : A -> B) (y : B) : (term517 A B u x s f y) = (term518 A B u x s f y).
Proof. exact (MK_COMB (@lem5047090) (@lem5047089 A B u x s f y)). Qed.
Lemma lem5047092 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term514 A B s f y x) = (term407 A B s f x y).
Proof. exact (eq_refl (term514 A B s f y x)). Qed.
Lemma lem5047093 {B : Type'} (y : B) (u : B -> Prop) (x : B) : (term506 B y u x) = (term506 B y u x).
Proof. exact (eq_refl (term506 B y u x)). Qed.
Lemma lem5047094 {A B : Type'} (u : B -> Prop) (x : B) (s : A -> Prop) (f : A -> B) (x' : A) (y : B) : (term519 A B u x s f y x') = (term520 A B u x s f x' y).
Proof. exact (MK_COMB (@lem5047093 B y u x) (@lem5047092 A B s f x' y)). Qed.
Lemma lem5047095 {A B : Type'} (u : B -> Prop) (x : B) (s : A -> Prop) (f : A -> B) (y : B) : (term521 A B u x s f y) = (term522 A B u x s f y).
Proof. exact (fun_ext (fun x' : A => @lem5047094 A B u x s f x' y)). Qed.
Lemma lem5047096 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5047097 {A B : Type'} (u : B -> Prop) (x : B) (s : A -> Prop) (f : A -> B) (y : B) : (term513 A B u x s f y) = (term523 A B u x s f y).
Proof. exact (MK_COMB (@lem5047096 A) (@lem5047095 A B u x s f y)). Qed.
Lemma lem5047098 {A B : Type'} (u : B -> Prop) (x : B) (s : A -> Prop) (f : A -> B) (y : B) : ((term512 A B u x s f y) = (term513 A B u x s f y)) = ((term508 A B u x s f y) = (term523 A B u x s f y)).
Proof. exact (MK_COMB (@lem5047091 A B u x s f y) (@lem5047097 A B u x s f y)). Qed.
Lemma lem5047099 {A B : Type'} (u : B -> Prop) (x : B) (s : A -> Prop) (f : A -> B) (y : B) : (term508 A B u x s f y) = (term523 A B u x s f y).
Proof. exact (EQ_MP (@lem5047098 A B u x s f y) (@lem5047083 A B u x s f y)). Qed.
Lemma lem5047100 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term510 A B u s f y) = (term524 A B u s f y).
Proof. exact (fun_ext (fun x : B => @lem5047099 A B u x s f y)). Qed.
Lemma lem5047101 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5047102 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term511 A B u s f y) = (term525 A B u s f y).
Proof. exact (MK_COMB (@lem5047101 B) (@lem5047100 A B u s f y)). Qed.
Lemma lem5047103 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term489 A B u s f y) = (term525 A B u s f y).
Proof. exact (TRANS (@lem5047079 A B u s f y) (@lem5047102 A B u s f y)). Qed.
Lemma lem5047104 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5047105 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term492 A B u s f y) = (term526 A B u s f y).
Proof. exact (MK_COMB (@lem5047104) (@lem5047103 A B u s f y)). Qed.
Lemma lem5047106 {B : Type'} (y : B) : (term439 B y) = (term439 B y).
Proof. exact (eq_refl (term439 B y)). Qed.
Lemma lem5047107 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term494 A B u s f y) = (term527 A B u s f y).
Proof. exact (MK_COMB (@lem5047105 A B u s f y) (@lem5047106 B y)). Qed.
Lemma lem5047109 {A : Type'} (P : A -> Prop) (Q : Prop) : (term495 A P Q) = (term496 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5047110 {B : Type'} (P : B -> Prop) (Q : Prop) : (term495 B P Q) = (term496 B P Q).
Proof. exact (@lem5047109 B P Q). Qed.
Lemma lem5047111 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term528 A B u s f y) = (term529 A B u s f y).
Proof. exact (@lem5047110 B (term524 A B u s f y) (term439 B y)). Qed.
Lemma lem5047112 {A B : Type'} (u : B -> Prop) (x : B) (s : A -> Prop) (f : A -> B) (y : B) : (term530 A B u s f y x) = (term523 A B u x s f y).
Proof. exact (eq_refl (term530 A B u s f y x)). Qed.
Lemma lem5047113 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term531 A B u s f y) = (term524 A B u s f y).
Proof. exact (fun_ext (fun x : B => @lem5047112 A B u x s f y)). Qed.
Lemma lem5047114 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5047115 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term532 A B u s f y) = (term525 A B u s f y).
Proof. exact (MK_COMB (@lem5047114 B) (@lem5047113 A B u s f y)). Qed.
Lemma lem5047116 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5047117 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term533 A B u s f y) = (term526 A B u s f y).
Proof. exact (MK_COMB (@lem5047116) (@lem5047115 A B u s f y)). Qed.
Lemma lem5047118 {B : Type'} (y : B) : (term439 B y) = (term439 B y).
Proof. exact (eq_refl (term439 B y)). Qed.
Lemma lem5047119 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term528 A B u s f y) = (term527 A B u s f y).
Proof. exact (MK_COMB (@lem5047117 A B u s f y) (@lem5047118 B y)). Qed.
Lemma lem5047120 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5047121 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term534 A B u s f y) = (term535 A B u s f y).
Proof. exact (MK_COMB (@lem5047120) (@lem5047119 A B u s f y)). Qed.
Lemma lem5047122 {A B : Type'} (u : B -> Prop) (x : B) (s : A -> Prop) (f : A -> B) (y : B) : (term530 A B u s f y x) = (term523 A B u x s f y).
Proof. exact (eq_refl (term530 A B u s f y x)). Qed.
Lemma lem5047123 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5047124 {A B : Type'} (u : B -> Prop) (x : B) (s : A -> Prop) (f : A -> B) (y : B) : (term536 A B u s f y x) = (term537 A B u x s f y).
Proof. exact (MK_COMB (@lem5047123) (@lem5047122 A B u x s f y)). Qed.
Lemma lem5047125 {B : Type'} (y : B) : (term439 B y) = (term439 B y).
Proof. exact (eq_refl (term439 B y)). Qed.
Lemma lem5047126 {A B : Type'} (u : B -> Prop) (x : B) (s : A -> Prop) (f : A -> B) (y : B) : (term538 A B u s f x y) = (term539 A B u x s f y).
Proof. exact (MK_COMB (@lem5047124 A B u x s f y) (@lem5047125 B y)). Qed.
Lemma lem5047127 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term540 A B u s f y) = (term541 A B u s f y).
Proof. exact (fun_ext (fun x : B => @lem5047126 A B u x s f y)). Qed.
Lemma lem5047128 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5047129 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term529 A B u s f y) = (term542 A B u s f y).
Proof. exact (MK_COMB (@lem5047128 B) (@lem5047127 A B u s f y)). Qed.
Lemma lem5047130 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : ((term528 A B u s f y) = (term529 A B u s f y)) = ((term527 A B u s f y) = (term542 A B u s f y)).
Proof. exact (MK_COMB (@lem5047121 A B u s f y) (@lem5047129 A B u s f y)). Qed.
Lemma lem5047131 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term527 A B u s f y) = (term542 A B u s f y).
Proof. exact (EQ_MP (@lem5047130 A B u s f y) (@lem5047111 A B u s f y)). Qed.
Lemma lem5047133 {A : Type'} (P : A -> Prop) (Q : Prop) : (term495 A P Q) = (term496 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5047134 {A : Type'} (P : A -> Prop) (Q : Prop) : (term495 A P Q) = (term496 A P Q).
Proof. exact (@lem5047133 A P Q). Qed.
Lemma lem5047135 {A B : Type'} (u : B -> Prop) (x : B) (s : A -> Prop) (f : A -> B) (y : B) : (term543 A B u x s f y) = (term544 A B u x s f y).
Proof. exact (@lem5047134 A (term522 A B u x s f y) (term439 B y)). Qed.
Lemma lem5047136 {A B : Type'} (u : B -> Prop) (x : B) (s : A -> Prop) (f : A -> B) (x' : A) (y : B) : (term545 A B u x s f y x') = (term520 A B u x s f x' y).
Proof. exact (eq_refl (term545 A B u x s f y x')). Qed.
Lemma lem5047137 {A B : Type'} (u : B -> Prop) (x : B) (s : A -> Prop) (f : A -> B) (y : B) : (term546 A B u x s f y) = (term522 A B u x s f y).
Proof. exact (fun_ext (fun x' : A => @lem5047136 A B u x s f x' y)). Qed.
Lemma lem5047138 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5047139 {A B : Type'} (u : B -> Prop) (x : B) (s : A -> Prop) (f : A -> B) (y : B) : (term547 A B u x s f y) = (term523 A B u x s f y).
Proof. exact (MK_COMB (@lem5047138 A) (@lem5047137 A B u x s f y)). Qed.
Lemma lem5047140 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5047141 {A B : Type'} (u : B -> Prop) (x : B) (s : A -> Prop) (f : A -> B) (y : B) : (term548 A B u x s f y) = (term537 A B u x s f y).
Proof. exact (MK_COMB (@lem5047140) (@lem5047139 A B u x s f y)). Qed.
Lemma lem5047142 {B : Type'} (y : B) : (term439 B y) = (term439 B y).
Proof. exact (eq_refl (term439 B y)). Qed.
Lemma lem5047143 {A B : Type'} (u : B -> Prop) (x : B) (s : A -> Prop) (f : A -> B) (y : B) : (term543 A B u x s f y) = (term539 A B u x s f y).
Proof. exact (MK_COMB (@lem5047141 A B u x s f y) (@lem5047142 B y)). Qed.
Lemma lem5047144 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5047145 {A B : Type'} (u : B -> Prop) (x : B) (s : A -> Prop) (f : A -> B) (y : B) : (term549 A B u x s f y) = (term550 A B u x s f y).
Proof. exact (MK_COMB (@lem5047144) (@lem5047143 A B u x s f y)). Qed.
Lemma lem5047146 {A B : Type'} (u : B -> Prop) (x : B) (s : A -> Prop) (f : A -> B) (x' : A) (y : B) : (term545 A B u x s f y x') = (term520 A B u x s f x' y).
Proof. exact (eq_refl (term545 A B u x s f y x')). Qed.
Lemma lem5047147 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5047148 {A B : Type'} (u : B -> Prop) (x : B) (s : A -> Prop) (f : A -> B) (x' : A) (y : B) : (term551 A B u x s f y x') = (term552 A B u x s f x' y).
Proof. exact (MK_COMB (@lem5047147) (@lem5047146 A B u x s f x' y)). Qed.
Lemma lem5047149 {B : Type'} (y : B) : (term439 B y) = (term439 B y).
Proof. exact (eq_refl (term439 B y)). Qed.
Lemma lem5047150 {A B : Type'} (u : B -> Prop) (x : B) (s : A -> Prop) (f : A -> B) (x' : A) (y : B) : (term553 A B u x s f x' y) = (term554 A B u x s f x' y).
Proof. exact (MK_COMB (@lem5047148 A B u x s f x' y) (@lem5047149 B y)). Qed.
Lemma lem5047151 {A B : Type'} (u : B -> Prop) (x : B) (s : A -> Prop) (f : A -> B) (y : B) : (term555 A B u x s f y) = (term556 A B u x s f y).
Proof. exact (fun_ext (fun x' : A => @lem5047150 A B u x s f x' y)). Qed.
Lemma lem5047152 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5047153 {A B : Type'} (u : B -> Prop) (x : B) (s : A -> Prop) (f : A -> B) (y : B) : (term544 A B u x s f y) = (term557 A B u x s f y).
Proof. exact (MK_COMB (@lem5047152 A) (@lem5047151 A B u x s f y)). Qed.
Lemma lem5047154 {A B : Type'} (u : B -> Prop) (x : B) (s : A -> Prop) (f : A -> B) (y : B) : ((term543 A B u x s f y) = (term544 A B u x s f y)) = ((term539 A B u x s f y) = (term557 A B u x s f y)).
Proof. exact (MK_COMB (@lem5047145 A B u x s f y) (@lem5047153 A B u x s f y)). Qed.
Lemma lem5047155 {A B : Type'} (u : B -> Prop) (x : B) (s : A -> Prop) (f : A -> B) (y : B) : (term539 A B u x s f y) = (term557 A B u x s f y).
Proof. exact (EQ_MP (@lem5047154 A B u x s f y) (@lem5047135 A B u x s f y)). Qed.
Lemma lem5047156 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term541 A B u s f y) = (term558 A B u s f y).
Proof. exact (fun_ext (fun x : B => @lem5047155 A B u x s f y)). Qed.
Lemma lem5047157 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5047158 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term542 A B u s f y) = (term559 A B u s f y).
Proof. exact (MK_COMB (@lem5047157 B) (@lem5047156 A B u s f y)). Qed.
Lemma lem5047159 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term527 A B u s f y) = (term559 A B u s f y).
Proof. exact (TRANS (@lem5047131 A B u s f y) (@lem5047158 A B u s f y)). Qed.
Lemma lem5047161 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term494 A B u s f y) = (term559 A B u s f y).
Proof. exact (TRANS (@lem5047107 A B u s f y) (@lem5047159 A B u s f y)). Qed.
Lemma lem5047162 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term440 A B u s f y) = (term559 A B u s f y).
Proof. exact (TRANS (@lem5046972 A B u s f y) (@lem5047161 A B u s f y)). Qed.
Lemma lem5047163 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) (h1 : term440 A B u s f y) : term559 A B u s f y.
Proof. exact (EQ_MP (@lem5047162 A B u s f y) (@lem5046918 A B u s f y h1)). Qed.
Lemma lem5047169 {B : Type'} (u : B -> Prop) (y : B) (h1 : u y) : u y.
Proof. exact (h1). Qed.
Lemma lem5047176 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (x : A) : (term560 A B y f s x) = (term561 A B y f s x).
Proof. exact (@lem17045 (y = (f x)) (s x)). Qed.
Lemma lem5047177 {A : Type'} (P : A -> Prop) : (term562 A P) = (term563 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem5047178 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term466 A B y f s) = (term564 A B y f s).
Proof. exact (@lem5047177 A (term46 A B y f s)). Qed.
Lemma lem5047179 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (x : A) : (term133 A B y f s x) = (term44 A B y f s x).
Proof. exact (eq_refl (term133 A B y f s x)). Qed.
Lemma lem5047180 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5047181 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (x : A) : (term565 A B y f s x) = (term560 A B y f s x).
Proof. exact (MK_COMB (@lem5047180) (@lem5047179 A B y f s x)). Qed.
Lemma lem5047182 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (x : A) : (term565 A B y f s x) = (term561 A B y f s x).
Proof. exact (TRANS (@lem5047181 A B y f s x) (@lem5047176 A B y f s x)). Qed.
Lemma lem5047183 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term566 A B y f s) = (term567 A B y f s).
Proof. exact (fun_ext (fun x : A => @lem5047182 A B y f s x)). Qed.
Lemma lem5047184 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5047185 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term564 A B y f s) = (term568 A B y f s).
Proof. exact (MK_COMB (@lem5047184 A) (@lem5047183 A B y f s)). Qed.
Lemma lem5047238 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term466 A B y f s) = (term568 A B y f s).
Proof. exact (TRANS (@lem5047178 A B y f s) (@lem5047185 A B y f s)). Qed.
Lemma lem5047239 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (h1 : term466 A B y f s) : term568 A B y f s.
Proof. exact (EQ_MP (@lem5047238 A B y f s) (@lem5046924 A B y f s h1)). Qed.
Lemma lem5047240 {A B : Type'} (u : B -> Prop) (x : B) (s : A -> Prop) (f : A -> B) (y : B) (h1 : term557 A B u x s f y) : term557 A B u x s f y.
Proof. exact (h1). Qed.
Lemma lem5047241 {A B : Type'} (u : B -> Prop) (x : B) (s : A -> Prop) (f : A -> B) (x' : A) (y : B) (h1 : term554 A B u x s f x' y) : term554 A B u x s f x' y.
Proof. exact (h1). Qed.
Lemma lem5047245 {B : Type'} (u : B -> Prop) (y : B) (h1 : u y) : u y.
Proof. exact (h1). Qed.
Lemma lem5047262 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (x : A) : (term561 A B y f s x) = (term561 A B y f s x).
Proof. exact (eq_refl (term561 A B y f s x)). Qed.
Lemma lem5047263 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term567 A B y f s) = (term567 A B y f s).
Proof. exact (fun_ext (fun x : A => @lem5047262 A B y f s x)). Qed.
Lemma lem5047264 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5047265 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term568 A B y f s) = (term568 A B y f s).
Proof. exact (MK_COMB (@lem5047264 A) (@lem5047263 A B y f s)). Qed.
Lemma lem5047266 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (h1 : term466 A B y f s) : term568 A B y f s.
Proof. exact (EQ_MP (@lem5047265 A B y f s) (@lem5047239 A B y f s h1)). Qed.
Lemma lem5047273 {B : Type'} (x : B) (y : B) : (term266 B x y) = (term266 B x y).
Proof. exact (eq_refl (term266 B x y)). Qed.
Lemma lem5047274 {B : Type'} (y : B) : (term438 B y) = (term438 B y).
Proof. exact (fun_ext (fun x : B => @lem5047273 B x y)). Qed.
Lemma lem5047275 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5047276 {B : Type'} (y : B) : (term439 B y) = (term439 B y).
Proof. exact (MK_COMB (@lem5047275 B) (@lem5047274 B y)). Qed.
Lemma lem5047307 {A B : Type'} (u : B -> Prop) (x : B) (s : A -> Prop) (f : A -> B) (x' : A) (y : B) : (term552 A B u x s f x' y) = (term552 A B u x s f x' y).
Proof. exact (eq_refl (term552 A B u x s f x' y)). Qed.
Lemma lem5047308 {A B : Type'} (u : B -> Prop) (x : B) (s : A -> Prop) (f : A -> B) (x' : A) (y : B) : (term554 A B u x s f x' y) = (term554 A B u x s f x' y).
Proof. exact (MK_COMB (@lem5047307 A B u x s f x' y) (@lem5047276 B y)). Qed.
Lemma lem5047309 {A B : Type'} (u : B -> Prop) (x : B) (s : A -> Prop) (f : A -> B) (x' : A) (y : B) (h1 : term554 A B u x s f x' y) : term554 A B u x s f x' y.
Proof. exact (EQ_MP (@lem5047308 A B u x s f x' y) (@lem5047241 A B u x s f x' y h1)). Qed.
Lemma lem5047310 {A B : Type'} (u : B -> Prop) (x : B) (s : A -> Prop) (f : A -> B) (x' : A) (y : B) (h1 : term520 A B u x s f x' y) : term520 A B u x s f x' y.
Proof. exact (h1). Qed.
Lemma lem5047311 {B : Type'} (y : B) (h1 : term439 B y) : term439 B y.
Proof. exact (h1). Qed.
Lemma lem5047312 {B : Type'} (y : B) (u : B -> Prop) (x : B) (h1 : term468 B y u x) : term468 B y u x.
Proof. exact (h1). Qed.
Lemma lem5047313 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (y : B) (h1 : term407 A B s f x' y) : term407 A B s f x' y.
Proof. exact (h1). Qed.
Lemma lem5047321 {B : Type'} (u : B -> Prop) (y : B) (h1 : u y) : u y.
Proof. exact (h1). Qed.
Lemma lem5047354 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (x : A) : (term561 A B y f s x) = (term561 A B y f s x).
Proof. exact (eq_refl (term561 A B y f s x)). Qed.
Lemma lem5047355 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term567 A B y f s) = (term567 A B y f s).
Proof. exact (fun_ext (fun x : A => @lem5047354 A B y f s x)). Qed.
Lemma lem5047356 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5047358 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term568 A B y f s) = (term568 A B y f s).
Proof. exact (MK_COMB (@lem5047356 A) (@lem5047355 A B y f s)). Qed.
Lemma lem5047359 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (h1 : term466 A B y f s) : term568 A B y f s.
Proof. exact (EQ_MP (@lem5047358 A B y f s) (@lem5047266 A B y f s h1)). Qed.
Lemma lem5047386 {B : Type'} (x : B) (y : B) : (term266 B x y) = (term266 B x y).
Proof. exact (eq_refl (term266 B x y)). Qed.
Lemma lem5047387 {B : Type'} (y : B) : (term438 B y) = (term438 B y).
Proof. exact (fun_ext (fun x : B => @lem5047386 B x y)). Qed.
Lemma lem5047388 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5047390 {B : Type'} (y : B) : (term439 B y) = (term439 B y).
Proof. exact (MK_COMB (@lem5047388 B) (@lem5047387 B y)). Qed.
Lemma lem5047391 {B : Type'} (y : B) (h1 : term439 B y) : term439 B y.
Proof. exact (EQ_MP (@lem5047390 B y) (@lem5047311 B y h1)). Qed.
Lemma lem5047395 {A B : Type'} (_64850 : A) (y : B) (f : A -> B) (s : A -> Prop) (h1 : term466 A B y f s) : term569 A B y f s _64850.
Proof. exact (@lem5047359 A B y f s h1 _64850). Qed.
Lemma lem5047396 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (_64850 : A) : (term569 A B y f s _64850) = (term561 A B y f s _64850).
Proof. exact (eq_refl (term569 A B y f s _64850)). Qed.
Lemma lem5047401 {B : Type'} (_64852 : B) (y : B) (h1 : term439 B y) : term570 B y _64852.
Proof. exact (@lem5047391 B y h1 _64852). Qed.
Lemma lem5047402 {B : Type'} (_64852 : B) (y : B) : (term570 B y _64852) = (term266 B _64852 y).
Proof. exact (eq_refl (term570 B y _64852)). Qed.
Lemma lem5047405 {B : Type'} (u : B -> Prop) (y : B) (h1 : u y) : u y.
Proof. exact (h1). Qed.
Lemma lem5047413 {B : Type'} (y : B) (u : B -> Prop) (x : B) (h1 : term468 B y u x) : x = y.
Proof. exact (proj1 (@lem5047312 B y u x h1)). Qed.
Lemma lem5047415 {B : Type'} (y : B) (u : B -> Prop) (x : B) (h1 : term468 B y u x) : term132 B u x.
Proof. exact (proj2 (@lem5047312 B y u x h1)). Qed.
Lemma lem5047423 {A B : Type'} (_64850 : A) (y : B) (f : A -> B) (s : A -> Prop) (h1 : term466 A B y f s) : term561 A B y f s _64850.
Proof. exact (EQ_MP (@lem5047396 A B y f s _64850) (@lem5047395 A B _64850 y f s h1)). Qed.
Lemma lem5047427 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (y : B) (h1 : term407 A B s f x' y) : (f x') = y.
Proof. exact (proj2 (@lem5047313 A B s f x' y h1)). Qed.
Lemma lem5047437 {B : Type'} (_64852 : B) (y : B) (h1 : term439 B y) : term266 B _64852 y.
Proof. exact (EQ_MP (@lem5047402 B _64852 y) (@lem5047401 B _64852 y h1)). Qed.
Lemma lem5047465 {B : Type'} (u : B -> Prop) (y : B) (h1 : u y) : u y.
Proof. exact (h1). Qed.
Lemma lem5047480 {B : Type'} (u : B -> Prop) : (term571 B u) = (term571 B u).
Proof. exact (eq_refl (term571 B u)). Qed.
Lemma lem5047481 {B : Type'} (y : B) (u : B -> Prop) (x : B) (h1 : term468 B y u x) : (term572 B u x) = (term572 B u y).
Proof. exact (MK_COMB (@lem5047480 B u) (@lem5047413 B y u x h1)). Qed.
Lemma lem5047482 {B : Type'} (u : B -> Prop) (y : B) : (term572 B u y) = (term132 B u y).
Proof. exact (eq_refl (term572 B u y)). Qed.
Lemma lem5047483 {B : Type'} (u : B -> Prop) (x : B) : (term573 B u x) = (term573 B u x).
Proof. exact (eq_refl (term573 B u x)). Qed.
Lemma lem5047484 {B : Type'} (x : B) (u : B -> Prop) (y : B) : ((term572 B u x) = (term572 B u y)) = ((term572 B u x) = (term132 B u y)).
Proof. exact (MK_COMB (@lem5047483 B u x) (@lem5047482 B u y)). Qed.
Lemma lem5047485 {B : Type'} (u : B -> Prop) (x : B) : (term572 B u x) = (term132 B u x).
Proof. exact (eq_refl (term572 B u x)). Qed.
Lemma lem5047486 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5047487 {B : Type'} (u : B -> Prop) (x : B) : (term573 B u x) = (term574 B u x).
Proof. exact (MK_COMB (@lem5047486) (@lem5047485 B u x)). Qed.
Lemma lem5047488 {B : Type'} (u : B -> Prop) (y : B) : (term132 B u y) = (term132 B u y).
Proof. exact (eq_refl (term132 B u y)). Qed.
Lemma lem5047489 {B : Type'} (x : B) (u : B -> Prop) (y : B) : ((term572 B u x) = (term132 B u y)) = ((term132 B u x) = (term132 B u y)).
Proof. exact (MK_COMB (@lem5047487 B u x) (@lem5047488 B u y)). Qed.
Lemma lem5047490 {B : Type'} (x : B) (u : B -> Prop) (y : B) : ((term572 B u x) = (term572 B u y)) = ((term132 B u x) = (term132 B u y)).
Proof. exact (TRANS (@lem5047484 B x u y) (@lem5047489 B x u y)). Qed.
Lemma lem5047491 {B : Type'} (y : B) (u : B -> Prop) (x : B) (h1 : term468 B y u x) : (term132 B u x) = (term132 B u y).
Proof. exact (EQ_MP (@lem5047490 B x u y) (@lem5047481 B y u x h1)). Qed.
Lemma lem5047492 {B : Type'} (y : B) (u : B -> Prop) (x : B) (h1 : term468 B y u x) : term132 B u y.
Proof. exact (EQ_MP (@lem5047491 B y u x h1) (@lem5047415 B y u x h1)). Qed.
Lemma lem5047493 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (y : B) (h1 : term407 A B s f x' y) : y = (f x').
Proof. exact (SYM (@lem5047427 A B s f x' y h1)). Qed.
Lemma lem5047521 {A B : Type'} (f : A -> B) (s : A -> Prop) (_64850 : A) : (term575 A B f s _64850) = (term575 A B f s _64850).
Proof. exact (eq_refl (term575 A B f s _64850)). Qed.
Lemma lem5047522 {A B : Type'} (_64850 : A) (s : A -> Prop) (f : A -> B) (x' : A) (y : B) (h1 : term407 A B s f x' y) : (term576 A B f s _64850 y) = (term577 A B s _64850 f x').
Proof. exact (MK_COMB (@lem5047521 A B f s _64850) (@lem5047493 A B s f x' y h1)). Qed.
Lemma lem5047523 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_64850 : A) : (term577 A B s _64850 f x') = (term578 A B x' f s _64850).
Proof. exact (eq_refl (term577 A B s _64850 f x')). Qed.
Lemma lem5047524 {A B : Type'} (f : A -> B) (s : A -> Prop) (_64850 : A) (y : B) : (term579 A B f s _64850 y) = (term579 A B f s _64850 y).
Proof. exact (eq_refl (term579 A B f s _64850 y)). Qed.
Lemma lem5047525 {A B : Type'} (y : B) (x' : A) (f : A -> B) (s : A -> Prop) (_64850 : A) : ((term576 A B f s _64850 y) = (term577 A B s _64850 f x')) = ((term576 A B f s _64850 y) = (term578 A B x' f s _64850)).
Proof. exact (MK_COMB (@lem5047524 A B f s _64850 y) (@lem5047523 A B x' f s _64850)). Qed.
Lemma lem5047526 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (_64850 : A) : (term576 A B f s _64850 y) = (term561 A B y f s _64850).
Proof. exact (eq_refl (term576 A B f s _64850 y)). Qed.
Lemma lem5047527 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5047528 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (_64850 : A) : (term579 A B f s _64850 y) = (term580 A B y f s _64850).
Proof. exact (MK_COMB (@lem5047527) (@lem5047526 A B y f s _64850)). Qed.
Lemma lem5047529 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_64850 : A) : (term578 A B x' f s _64850) = (term578 A B x' f s _64850).
Proof. exact (eq_refl (term578 A B x' f s _64850)). Qed.
Lemma lem5047530 {A B : Type'} (y : B) (x' : A) (f : A -> B) (s : A -> Prop) (_64850 : A) : ((term576 A B f s _64850 y) = (term578 A B x' f s _64850)) = ((term561 A B y f s _64850) = (term578 A B x' f s _64850)).
Proof. exact (MK_COMB (@lem5047528 A B y f s _64850) (@lem5047529 A B x' f s _64850)). Qed.
Lemma lem5047531 {A B : Type'} (y : B) (x' : A) (f : A -> B) (s : A -> Prop) (_64850 : A) : ((term576 A B f s _64850 y) = (term577 A B s _64850 f x')) = ((term561 A B y f s _64850) = (term578 A B x' f s _64850)).
Proof. exact (TRANS (@lem5047525 A B y x' f s _64850) (@lem5047530 A B y x' f s _64850)). Qed.
Lemma lem5047532 {A B : Type'} (_64850 : A) (s : A -> Prop) (f : A -> B) (x' : A) (y : B) (h1 : term407 A B s f x' y) : (term561 A B y f s _64850) = (term578 A B x' f s _64850).
Proof. exact (EQ_MP (@lem5047531 A B y x' f s _64850) (@lem5047522 A B _64850 s f x' y h1)). Qed.
Lemma lem5047533 {A B : Type'} (_64850 : A) (s : A -> Prop) (f : A -> B) (x' : A) (y : B) (h1 : term466 A B y f s) (h2 : term407 A B s f x' y) : term578 A B x' f s _64850.
Proof. exact (EQ_MP (@lem5047532 A B _64850 s f x' y h2) (@lem5047423 A B _64850 y f s h1)). Qed.
Lemma lem5047585 {B : Type'} (u : B -> Prop) (y : B) (h1 : u y) : u y.
Proof. exact (h1). Qed.
Lemma lem5047586 {B : Type'} (u : B -> Prop) (y : B) (h1 : u y) : term246 B u y.
Proof. exact (fun h0 : term132 B u y => @lem5047585 B u y h1). Qed.
Lemma lem5047588 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5047589 {B : Type'} (u : B -> Prop) (y : B) : (term246 B u y) = (u y).
Proof. exact (@lem5047588 (u y)). Qed.
Lemma lem5047590 {B : Type'} (u : B -> Prop) (y : B) (h1 : u y) : u y.
Proof. exact (EQ_MP (@lem5047589 B u y) (@lem5047586 B u y h1)). Qed.
Lemma lem5047593 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5047595 {B : Type'} (u : B -> Prop) (y : B) : (term132 B u y) = (term332 B u y).
Proof. exact (@lem5047593 (u y)). Qed.
Lemma lem5047598 {B : Type'} (y : B) (u : B -> Prop) (x : B) (h1 : term468 B y u x) : term332 B u y.
Proof. exact (EQ_MP (@lem5047595 B u y) (@lem5047492 B y u x h1)). Qed.
Lemma lem5047601 {B : Type'} (y : B) (u : B -> Prop) (x : B) (h1 : u y) (h2 : term468 B y u x) : False.
Proof. exact (@lem5047598 B y u x h2 (@lem5047590 B u y h1)). Qed.
Lemma lem5047602 {B : Type'} (y : B) (u : B -> Prop) (x : B) (h1 : u y) (h2 : term468 B y u x) : term333.
Proof. exact (fun h0 : ~ False => @lem5047601 B y u x h1 h2). Qed.
Lemma lem5047604 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5047605 : term333 = False.
Proof. exact (@lem5047604 False). Qed.
Lemma lem5047606 {B : Type'} (y : B) (u : B -> Prop) (x : B) (h1 : u y) (h2 : term468 B y u x) : False.
Proof. exact (EQ_MP (@lem5047605) (@lem5047602 B y u x h1 h2)). Qed.
Lemma lem5047644 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem5047645 {B : Type'} (x : B) : x = x.
Proof. exact (@lem5047644 B x). Qed.
Lemma lem5047646 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (f x').
Proof. exact (@lem5047645 B (f x')). Qed.
Lemma lem5047647 {A B : Type'} (f : A -> B) (x' : A) : term581 A B f x'.
Proof. exact (fun h0 : term582 A B f x' => @lem5047646 A B f x'). Qed.
Lemma lem5047649 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5047650 {A B : Type'} (f : A -> B) (x' : A) : (term581 A B f x') = ((f x') = (f x')).
Proof. exact (@lem5047649 ((f x') = (f x'))). Qed.
Lemma lem5047651 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (f x').
Proof. exact (EQ_MP (@lem5047650 A B f x') (@lem5047647 A B f x')). Qed.
Lemma lem5047653 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (y : B) (h1 : term407 A B s f x' y) : s x'.
Proof. exact (proj1 (@lem5047313 A B s f x' y h1)). Qed.
Lemma lem5047654 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (y : B) (h1 : term407 A B s f x' y) : term246 A s x'.
Proof. exact (fun h0 : term132 A s x' => @lem5047653 A B s f x' y h1). Qed.
Lemma lem5047656 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5047657 {A : Type'} (s : A -> Prop) (x' : A) : (term246 A s x') = (s x').
Proof. exact (@lem5047656 (s x')). Qed.
Lemma lem5047658 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (y : B) (h1 : term407 A B s f x' y) : s x'.
Proof. exact (EQ_MP (@lem5047657 A s x') (@lem5047654 A B s f x' y h1)). Qed.
Lemma lem5047660 (a : Prop) (b : Prop) : (term583 a b) = (term584 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem5047661 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_64850 : A) : (term578 A B x' f s _64850) = (term585 A B x' f s _64850).
Proof. exact (@lem5047660 ((f x') = (f _64850)) (s _64850)). Qed.
Lemma lem5047663 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5047664 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_64850 : A) : (term585 A B x' f s _64850) = (term586 A B x' f s _64850).
Proof. exact (@lem5047663 (term587 A B x' f s _64850)). Qed.
Lemma lem5047665 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_64850 : A) : (term578 A B x' f s _64850) = (term586 A B x' f s _64850).
Proof. exact (TRANS (@lem5047661 A B x' f s _64850) (@lem5047664 A B x' f s _64850)). Qed.
Lemma lem5047667 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (y : B) (h1 : term407 A B s f x' y) : term588 A B f s x'.
Proof. exact (conj (@lem5047651 A B f x') (@lem5047658 A B s f x' y h1)). Qed.
Lemma lem5047669 {A B : Type'} (_64850 : A) (s : A -> Prop) (f : A -> B) (x' : A) (y : B) (h1 : term466 A B y f s) (h2 : term407 A B s f x' y) : term586 A B x' f s _64850.
Proof. exact (EQ_MP (@lem5047665 A B x' f s _64850) (@lem5047533 A B _64850 s f x' y h1 h2)). Qed.
Lemma lem5047670 {A B : Type'} (_64850 : A) (s : A -> Prop) (f : A -> B) (x' : A) (y : B) (h1 : term466 A B y f s) (h2 : term407 A B s f x' y) : term586 A B x' f s _64850.
Proof. exact (@lem5047669 A B _64850 s f x' y h1 h2). Qed.
Lemma lem5047671 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (y : B) (h1 : term466 A B y f s) (h2 : term407 A B s f x' y) : term589 A B f s x'.
Proof. exact (@lem5047670 A B x' s f x' y h1 h2). Qed.
Lemma lem5047674 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (y : B) (h1 : term466 A B y f s) (h2 : term407 A B s f x' y) : False.
Proof. exact (@lem5047671 A B s f x' y h1 h2 (@lem5047667 A B s f x' y h2)). Qed.
Lemma lem5047675 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (y : B) (h1 : term466 A B y f s) (h2 : term407 A B s f x' y) : term333.
Proof. exact (fun h0 : ~ False => @lem5047674 A B s f x' y h1 h2). Qed.
Lemma lem5047677 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5047678 : term333 = False.
Proof. exact (@lem5047677 False). Qed.
Lemma lem5047717 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem5047718 {B : Type'} (x : B) : x = x.
Proof. exact (@lem5047717 B x). Qed.
Lemma lem5047719 {B : Type'} (y : B) : y = y.
Proof. exact (@lem5047718 B y). Qed.
Lemma lem5047720 {B : Type'} (y : B) : term262 B y.
Proof. exact (fun h0 : term263 B y => @lem5047719 B y). Qed.
Lemma lem5047722 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5047723 {B : Type'} (y : B) : (term262 B y) = (y = y).
Proof. exact (@lem5047722 (y = y)). Qed.
Lemma lem5047724 {B : Type'} (y : B) : y = y.
Proof. exact (EQ_MP (@lem5047723 B y) (@lem5047720 B y)). Qed.
Lemma lem5047727 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5047729 {B : Type'} (_64852 : B) (y : B) : (term266 B _64852 y) = (term590 B _64852 y).
Proof. exact (@lem5047727 (_64852 = y)). Qed.
Lemma lem5047732 {B : Type'} (_64852 : B) (y : B) (h1 : term439 B y) : term590 B _64852 y.
Proof. exact (EQ_MP (@lem5047729 B _64852 y) (@lem5047437 B _64852 y h1)). Qed.
Lemma lem5047733 {B : Type'} (_64852 : B) (y : B) (h1 : term439 B y) : term590 B _64852 y.
Proof. exact (@lem5047732 B _64852 y h1). Qed.
Lemma lem5047734 {B : Type'} (y : B) (h1 : term439 B y) : term591 B y.
Proof. exact (@lem5047733 B y y h1). Qed.
Lemma lem5047737 {B : Type'} (y : B) (h1 : term439 B y) : False.
Proof. exact (@lem5047734 B y h1 (@lem5047724 B y)). Qed.
Lemma lem5047738 {B : Type'} (y : B) (h1 : term439 B y) : term333.
Proof. exact (fun h0 : ~ False => @lem5047737 B y h1). Qed.
Lemma lem5047740 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5047741 : term333 = False.
Proof. exact (@lem5047740 False). Qed.
Lemma lem5047742 {B : Type'} (y : B) (h1 : term439 B y) : False.
Proof. exact (EQ_MP (@lem5047741) (@lem5047738 B y h1)). Qed.
Lemma lem5047743 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (y : B) (h1 : term466 A B y f s) (h2 : term407 A B s f x' y) : False.
Proof. exact (EQ_MP (@lem5047678) (@lem5047675 A B s f x' y h1 h2)). Qed.
Lemma lem5047744 {B : Type'} (y : B) (u : B -> Prop) (x : B) (h1 : u y) (h2 : term468 B y u x) : (u y) = False.
Proof. exact (prop_ext (fun h3 : u y => @lem5047606 B y u x h1 h2) (fun h3 : False => @lem5047465 B u y h1)). Qed.
Lemma lem5047746 {B : Type'} (y : B) (u : B -> Prop) (x : B) (h1 : u y) (h2 : term468 B y u x) : False.
Proof. exact (EQ_MP (@lem5047744 B y u x h1 h2) (@lem5047465 B u y h1)). Qed.
Lemma lem5047747 {B : Type'} (y : B) (u : B -> Prop) (x : B) (h1 : u y) (h2 : term468 B y u x) : (u y) = False.
Proof. exact (prop_ext (fun h3 : u y => @lem5047746 B y u x h1 h2) (fun h3 : False => @lem5047405 B u y h1)). Qed.
Lemma lem5047748 {B : Type'} (y : B) (u : B -> Prop) (x : B) (h1 : u y) (h2 : term468 B y u x) : False.
Proof. exact (EQ_MP (@lem5047747 B y u x h1 h2) (@lem5047405 B u y h1)). Qed.
Lemma lem5047749 {B : Type'} (y : B) (u : B -> Prop) (x : B) (h1 : u y) (h2 : term468 B y u x) : (u y) = False.
Proof. exact (prop_ext (fun h3 : u y => @lem5047748 B y u x h1 h2) (fun h3 : False => @lem5047321 B u y h1)). Qed.
Lemma lem5047750 {B : Type'} (y : B) (u : B -> Prop) (x : B) (h1 : u y) (h2 : term468 B y u x) : False.
Proof. exact (EQ_MP (@lem5047749 B y u x h1 h2) (@lem5047321 B u y h1)). Qed.
Lemma lem5047751 {B : Type'} (y : B) (h1 : term439 B y) : (term439 B y) = False.
Proof. exact (prop_ext (fun h2 : term439 B y => @lem5047742 B y h1) (fun h2 : False => @lem5047391 B y h1)). Qed.
Lemma lem5047752 {B : Type'} (y : B) (h1 : term439 B y) : False.
Proof. exact (EQ_MP (@lem5047751 B y h1) (@lem5047391 B y h1)). Qed.
Lemma lem5047753 {B : Type'} (y : B) (u : B -> Prop) (x : B) (h1 : u y) (h2 : term468 B y u x) : (u y) = False.
Proof. exact (prop_ext (fun h3 : u y => @lem5047750 B y u x h1 h2) (fun h3 : False => @lem5047321 B u y h1)). Qed.
Lemma lem5047754 {B : Type'} (y : B) (u : B -> Prop) (x : B) (h1 : u y) (h2 : term468 B y u x) : False.
Proof. exact (EQ_MP (@lem5047753 B y u x h1 h2) (@lem5047321 B u y h1)). Qed.
Lemma lem5047755 {A B : Type'} (u : B -> Prop) (x : B) (s : A -> Prop) (f : A -> B) (x' : A) (y : B) (h1 : term466 A B y f s) (h2 : u y) (h3 : term520 A B u x s f x' y) : False.
Proof. exact (or_elim (@lem5047310 A B u x s f x' y h3) (fun h0 : term468 B y u x => @lem5047754 B y u x h2 h0) (fun h0 : term407 A B s f x' y => @lem5047743 A B s f x' y h1 h0)). Qed.
Lemma lem5047756 {A B : Type'} (u : B -> Prop) (x : B) (s : A -> Prop) (f : A -> B) (x' : A) (y : B) (h1 : term466 A B y f s) (h2 : u y) (h3 : term554 A B u x s f x' y) : False.
Proof. exact (or_elim (@lem5047309 A B u x s f x' y h3) (fun h0 : term520 A B u x s f x' y => @lem5047755 A B u x s f x' y h1 h2 h0) (fun h0 : term439 B y => @lem5047752 B y h0)). Qed.
Lemma lem5047757 {A B : Type'} (u : B -> Prop) (x : B) (s : A -> Prop) (f : A -> B) (x' : A) (y : B) (h1 : term466 A B y f s) (h2 : u y) (h3 : term554 A B u x s f x' y) : (term554 A B u x s f x' y) = False.
Proof. exact (prop_ext (fun h4 : term554 A B u x s f x' y => @lem5047756 A B u x s f x' y h1 h2 h3) (fun h4 : False => @lem5047309 A B u x s f x' y h3)). Qed.
Lemma lem5047758 {A B : Type'} (u : B -> Prop) (x : B) (s : A -> Prop) (f : A -> B) (x' : A) (y : B) (h1 : term466 A B y f s) (h2 : u y) (h3 : term554 A B u x s f x' y) : False.
Proof. exact (EQ_MP (@lem5047757 A B u x s f x' y h1 h2 h3) (@lem5047309 A B u x s f x' y h3)). Qed.
Lemma lem5047759 {A B : Type'} (u : B -> Prop) (x : B) (s : A -> Prop) (f : A -> B) (x' : A) (y : B) (h1 : term466 A B y f s) (h2 : u y) (h3 : term554 A B u x s f x' y) : (u y) = False.
Proof. exact (prop_ext (fun h4 : u y => @lem5047758 A B u x s f x' y h1 h2 h3) (fun h4 : False => @lem5047245 B u y h2)). Qed.
Lemma lem5047760 {A B : Type'} (u : B -> Prop) (x : B) (s : A -> Prop) (f : A -> B) (x' : A) (y : B) (h1 : term466 A B y f s) (h2 : u y) (h3 : term554 A B u x s f x' y) : False.
Proof. exact (EQ_MP (@lem5047759 A B u x s f x' y h1 h2 h3) (@lem5047245 B u y h2)). Qed.
Lemma lem5047761 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (u : B -> Prop) (y : B) (h1 : term557 A B u x s f y) (h2 : term466 A B y f s) (h3 : u y) : False.
Proof. exact (ex_elim (@lem5047240 A B u x s f y h1) (fun x' : A => fun h0 : term556 A B u x s f y x' => @lem5047760 A B u x s f x' y h2 h3 h0)). Qed.
Lemma lem5047762 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) (h1 : term466 A B y f s) (h2 : u y) (h3 : term440 A B u s f y) : False.
Proof. exact (ex_elim (@lem5047163 A B u s f y h3) (fun x : B => fun h0 : term558 A B u s f y x => @lem5047761 A B x f s u y h0 h1 h2)). Qed.
Lemma lem5047763 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) (h1 : term466 A B y f s) (h2 : u y) (h3 : term440 A B u s f y) : (u y) = False.
Proof. exact (prop_ext (fun h4 : u y => @lem5047762 A B u s f y h1 h2 h3) (fun h4 : False => @lem5047169 B u y h2)). Qed.
Lemma lem5047764 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) (h1 : term466 A B y f s) (h2 : u y) (h3 : term440 A B u s f y) : False.
Proof. exact (EQ_MP (@lem5047763 A B u s f y h1 h2 h3) (@lem5047169 B u y h2)). Qed.
Lemma lem5047765 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) (h1 : term466 A B y f s) (h2 : u y) (h3 : term440 A B u s f y) : (term466 A B y f s) = False.
Proof. exact (prop_ext (fun h4 : term466 A B y f s => @lem5047764 A B u s f y h1 h2 h3) (fun h4 : False => @lem5046924 A B y f s h1)). Qed.
Lemma lem5047766 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) (h1 : term466 A B y f s) (h2 : u y) (h3 : term440 A B u s f y) : False.
Proof. exact (EQ_MP (@lem5047765 A B u s f y h1 h2 h3) (@lem5046924 A B y f s h1)). Qed.
Lemma lem5047767 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) (h1 : u y) (h2 : term440 A B u s f y) : term465 A B y f s.
Proof. exact (fun h0 : term466 A B y f s => @lem5047766 A B u s f y h0 h1 h2). Qed.
Lemma lem5047768 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) (h1 : u y) (h2 : term440 A B u s f y) : term47 A B y f s.
Proof. exact (EQ_MP (@lem5046923 A B y f s) (@lem5047767 A B u s f y h1 h2)). Qed.
Lemma lem5047769 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) (h1 : term440 A B u s f y) : term49 A B u y f s.
Proof. exact (fun h0 : u y => @lem5047768 A B u s f y h0 h1). Qed.
Lemma lem5047770 {A B : Type'} (u : B -> Prop) (y : B) (f : A -> B) (s : A -> Prop) : term442 A B u y f s.
Proof. exact (fun h0 : term440 A B u s f y => @lem5047769 A B u s f y h0). Qed.
Lemma lem5047775 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : term452 A B y f s.
Proof. exact (fun u : B -> Prop => @lem5047770 A B u y f s). Qed.
Lemma lem5047780 {A B : Type'} (f : A -> B) (s : A -> Prop) : term456 A B f s.
Proof. exact (fun y : B => @lem5047775 A B y f s). Qed.
Lemma lem5047785 {A B : Type'} (s : A -> Prop) : term460 A B s.
Proof. exact (fun f : A -> B => @lem5047780 A B f s). Qed.
Lemma lem5047790 {A B : Type'} : term464 A B.
Proof. exact (fun s : A -> Prop => @lem5047785 A B s). Qed.
Lemma lem5047791 {A B : Type'} : term463 A B.
Proof. exact (EQ_MP (@lem5046917 A B) (@lem5047790 A B)). Qed.
Lemma lem5047792 {A B : Type'} (s : A -> Prop) : term592 A B s.
Proof. exact (@lem5047791 A B s). Qed.
Lemma lem5047793 {A B : Type'} (s : A -> Prop) : (term592 A B s) = (term459 A B s).
Proof. exact (eq_refl (term592 A B s)). Qed.
Lemma lem5047794 {A B : Type'} (s : A -> Prop) : term459 A B s.
Proof. exact (EQ_MP (@lem5047793 A B s) (@lem5047792 A B s)). Qed.
Lemma lem5047795 {A B : Type'} (s : A -> Prop) (f : A -> B) : term593 A B s f.
Proof. exact (@lem5047794 A B s f). Qed.
Lemma lem5047796 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term593 A B s f) = (term455 A B f s).
Proof. exact (eq_refl (term593 A B s f)). Qed.
Lemma lem5047797 {A B : Type'} (f : A -> B) (s : A -> Prop) : term455 A B f s.
Proof. exact (EQ_MP (@lem5047796 A B f s) (@lem5047795 A B s f)). Qed.
Lemma lem5047798 {A B : Type'} (f : A -> B) (s : A -> Prop) (y : B) : term594 A B f s y.
Proof. exact (@lem5047797 A B f s y). Qed.
Lemma lem5047799 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term594 A B f s y) = (term451 A B y f s).
Proof. exact (eq_refl (term594 A B f s y)). Qed.
Lemma lem5047800 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : term451 A B y f s.
Proof. exact (EQ_MP (@lem5047799 A B y f s) (@lem5047798 A B f s y)). Qed.
Lemma lem5047801 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (u : B -> Prop) : term595 A B y f s u.
Proof. exact (@lem5047800 A B y f s u). Qed.
Lemma lem5047802 {A B : Type'} (u : B -> Prop) (y : B) (f : A -> B) (s : A -> Prop) : (term595 A B y f s u) = (term443 A B u y f s).
Proof. exact (eq_refl (term595 A B y f s u)). Qed.
Lemma lem5047803 {A B : Type'} (u : B -> Prop) (y : B) (f : A -> B) (s : A -> Prop) : term443 A B u y f s.
Proof. exact (EQ_MP (@lem5047802 A B u y f s) (@lem5047801 A B y f s u)). Qed.
Lemma lem5047805 {A B : Type'} (u : B -> Prop) (y : B) (f : A -> B) (s : A -> Prop) : term443 A B u y f s.
Proof. exact (@lem5046681 A B u y f s (@lem5047803 A B u y f s)). Qed.
Lemma lem5047806 {A B : Type'} (u : B -> Prop) (y : B) (f : A -> B) (s : A -> Prop) (h1 : term444 A B u y f s) : False.
Proof. exact (@lem5047805 A B u y f s (@lem5046665 A B u y f s h1)). Qed.
Lemma lem5047807 {A B : Type'} (u : B -> Prop) (y : B) (f : A -> B) (s : A -> Prop) (h1 : term444 A B u y f s) : (term444 A B u y f s) = False.
Proof. exact (prop_ext (fun h2 : term444 A B u y f s => @lem5047806 A B u y f s h1) (fun h2 : False => @lem5046665 A B u y f s h1)). Qed.
Lemma lem5047808 {A B : Type'} (u : B -> Prop) (y : B) (f : A -> B) (s : A -> Prop) (h1 : term444 A B u y f s) : False.
Proof. exact (EQ_MP (@lem5047807 A B u y f s h1) (@lem5046665 A B u y f s h1)). Qed.
Lemma lem5047809 {A B : Type'} (u : B -> Prop) (y : B) (f : A -> B) (s : A -> Prop) : term443 A B u y f s.
Proof. exact (fun h0 : term444 A B u y f s => @lem5047808 A B u y f s h0). Qed.
Lemma lem5047810 {A B : Type'} (u : B -> Prop) (y : B) (f : A -> B) (s : A -> Prop) : term442 A B u y f s.
Proof. exact (EQ_MP (@lem5046664 A B u y f s) (@lem5047809 A B u y f s)). Qed.
Lemma lem5047811 {A B : Type'} (u : B -> Prop) (y : B) (f : A -> B) (s : A -> Prop) : term362 A B u y f s.
Proof. exact (EQ_MP (@lem5046660 A B u y f s) (@lem5047810 A B u y f s)). Qed.
Lemma lem5047812 {A B : Type'} (u : B -> Prop) (y : B) (f : A -> B) (s : A -> Prop) : term361 A B u y f s.
Proof. exact (EQ_MP (@lem5046347 A B u y f s) (@lem5047811 A B u y f s)). Qed.
Lemma lem5047813 {A B : Type'} (y : B) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term4 A B u s f) : term48 A B u y f s.
Proof. exact (@lem5047812 A B u y f s (@lem5046245 A B y u s f h1)). Qed.
Lemma lem5047818 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term4 A B u s f) : term13 A B u f s.
Proof. exact (fun y : B => @lem5047813 A B y u s f h1). Qed.
Lemma lem5047819 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term4 A B u s f) : term5 A B u f s.
Proof. exact (EQ_MP (@lem5046239 A B u f s) (@lem5047818 A B u s f h1)). Qed.
Lemma lem5047820 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) : term36 A B u s f.
Proof. exact (fun h0 : term5 A B u f s => @lem5046228 A B u f s h0). Qed.
Lemma lem5047821 {A B : Type'} (u : B -> Prop) (f : A -> B) (s : A -> Prop) : term596 A B u f s.
Proof. exact (fun h0 : term4 A B u s f => @lem5047819 A B u s f h0). Qed.
Lemma lem5047822 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) : term597 A B u s f.
Proof. exact (conj (@lem5047821 A B u f s) (@lem5047820 A B u s f)). Qed.
Lemma lem5047823 {A B : Type'} (u : B -> Prop) (f : A -> B) (s : A -> Prop) : (term597 A B u s f) = ((term4 A B u s f) = (term5 A B u f s)).
Proof. exact (@lem32 (term4 A B u s f) (term5 A B u f s)). Qed.
Lemma lem5047824 {A B : Type'} (u : B -> Prop) (f : A -> B) (s : A -> Prop) : (term4 A B u s f) = (term5 A B u f s).
Proof. exact (EQ_MP (@lem5047823 A B u f s) (@lem5047822 A B u s f)). Qed.
Lemma lem5047829 {A B : Type'} (f : A -> B) (s : A -> Prop) : term598 A B f s.
Proof. exact (fun u : B -> Prop => @lem5047824 A B u f s). Qed.
Lemma lem5047834 {A B : Type'} (f : A -> B) : term599 A B f.
Proof. exact (fun s : A -> Prop => @lem5047829 A B f s). Qed.
Lemma lem5047839 {A B : Type'} : term600 A B.
Proof. exact (fun f : A -> B => @lem5047834 A B f). Qed.
