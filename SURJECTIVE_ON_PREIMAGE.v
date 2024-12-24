Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SURJECTIVE_ON_PREIMAGE_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import FORALL_IN_IMAGE_spec.
Require Import SUBSET_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm1834_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
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
Lemma lem5047840 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : term0 _87967 _87968 P f.
Proof. exact (@lem3386920 _87967 _87968 P f). Qed.
Lemma lem5047841 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : (term0 _87967 _87968 P f) = (term1 _87967 _87968 P f).
Proof. exact (eq_refl (term0 _87967 _87968 P f)). Qed.
Lemma lem5047842 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : term1 _87967 _87968 P f.
Proof. exact (EQ_MP (@lem5047841 _87967 _87968 P f) (@lem5047840 _87967 _87968 P f)). Qed.
Lemma lem5047843 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) (s : _87968 -> Prop) : term2 _87967 _87968 P f s.
Proof. exact (@lem5047842 _87967 _87968 P f s). Qed.
Lemma lem5047844 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term2 _87967 _87968 P f s) = ((term3 _87967 _87968 f s P) = (term4 _87967 _87968 s P f)).
Proof. exact (eq_refl (term2 _87967 _87968 P f s)). Qed.
Lemma lem5047846 {A : Type'} (s : A -> Prop) : term5 A s.
Proof. exact (@lem3194148 A s). Qed.
Lemma lem5047847 {A : Type'} (s : A -> Prop) : (term5 A s) = (term6 A s).
Proof. exact (eq_refl (term5 A s)). Qed.
Lemma lem5047848 {A : Type'} (s : A -> Prop) : term6 A s.
Proof. exact (EQ_MP (@lem5047847 A s) (@lem5047846 A s)). Qed.
Lemma lem5047849 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term7 A s t.
Proof. exact (@lem5047848 A s t). Qed.
Lemma lem5047850 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term7 A s t) = ((@SUBSET A s t) = (term8 A s t)).
Proof. exact (eq_refl (term7 A s t)). Qed.
Lemma lem5047852 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term9 A B u s f) : term9 A B u s f.
Proof. exact (h1). Qed.
Lemma lem5047853 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term10 A B u s f) : term10 A B u s f.
Proof. exact (h1). Qed.
Lemma lem5047855 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term8 A s t).
Proof. exact (EQ_MP (@lem5047850 A s t) (@lem5047849 A s t)). Qed.
Lemma lem5047856 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (@SUBSET B s t) = (term8 B s t).
Proof. exact (@lem5047855 B s t). Qed.
Lemma lem5047857 {A B : Type'} (f : A -> B) (s : A -> Prop) (u : B -> Prop) : (term11 A B f s u) = (term12 A B f s u).
Proof. exact (@lem5047856 B (@IMAGE A B f s) u). Qed.
Lemma lem5047859 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term3 _87967 _87968 f s P) = (term4 _87967 _87968 s P f).
Proof. exact (EQ_MP (@lem5047844 _87967 _87968 s P f) (@lem5047843 _87967 _87968 P f s)). Qed.
Lemma lem5047860 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term13 A B f s P) = (term14 A B s P f).
Proof. exact (@lem5047859 B A s P f). Qed.
Lemma lem5047861 {A B : Type'} (s : A -> Prop) (u : B -> Prop) (f : A -> B) : (term15 A B f s u) = (term16 A B s u f).
Proof. exact (@lem5047860 A B s (term17 B u) f). Qed.
Lemma lem5047862 {B : Type'} (x : B) (u : B -> Prop) : (term18 B u x) = (@IN B x u).
Proof. exact (eq_refl (term18 B u x)). Qed.
Lemma lem5047863 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term19 A B x f s) = (term19 A B x f s).
Proof. exact (eq_refl (term19 A B x f s)). Qed.
Lemma lem5047864 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : B) (u : B -> Prop) : (term20 A B f s u x) = (term21 A B f s x u).
Proof. exact (MK_COMB (@lem5047863 A B x f s) (@lem5047862 B x u)). Qed.
Lemma lem5047865 {A B : Type'} (f : A -> B) (s : A -> Prop) (u : B -> Prop) : (term22 A B f s u) = (term23 A B f s u).
Proof. exact (fun_ext (fun x : B => @lem5047864 A B f s x u)). Qed.
Lemma lem5047866 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5047867 {A B : Type'} (f : A -> B) (s : A -> Prop) (u : B -> Prop) : (term15 A B f s u) = (term12 A B f s u).
Proof. exact (MK_COMB (@lem5047866 B) (@lem5047865 A B f s u)). Qed.
Lemma lem5047868 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5047869 {A B : Type'} (f : A -> B) (s : A -> Prop) (u : B -> Prop) : (term24 A B f s u) = (term25 A B f s u).
Proof. exact (MK_COMB (@lem5047868) (@lem5047867 A B f s u)). Qed.
Lemma lem5047870 {A B : Type'} (f : A -> B) (x : A) (u : B -> Prop) : (term26 A B u f x) = (term27 A B f x u).
Proof. exact (eq_refl (term26 A B u f x)). Qed.
Lemma lem5047871 {A : Type'} (x : A) (s : A -> Prop) : (term28 A x s) = (term28 A x s).
Proof. exact (eq_refl (term28 A x s)). Qed.
Lemma lem5047872 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (u : B -> Prop) : (term29 A B s u f x) = (term30 A B s f x u).
Proof. exact (MK_COMB (@lem5047871 A x s) (@lem5047870 A B f x u)). Qed.
Lemma lem5047873 {A B : Type'} (s : A -> Prop) (f : A -> B) (u : B -> Prop) : (term31 A B s u f) = (term32 A B s f u).
Proof. exact (fun_ext (fun x : A => @lem5047872 A B s f x u)). Qed.
Lemma lem5047874 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5047875 {A B : Type'} (s : A -> Prop) (f : A -> B) (u : B -> Prop) : (term16 A B s u f) = (term33 A B s f u).
Proof. exact (MK_COMB (@lem5047874 A) (@lem5047873 A B s f u)). Qed.
Lemma lem5047876 {A B : Type'} (s : A -> Prop) (f : A -> B) (u : B -> Prop) : ((term15 A B f s u) = (term16 A B s u f)) = ((term12 A B f s u) = (term33 A B s f u)).
Proof. exact (MK_COMB (@lem5047869 A B f s u) (@lem5047875 A B s f u)). Qed.
Lemma lem5047877 {A B : Type'} (s : A -> Prop) (f : A -> B) (u : B -> Prop) : (term12 A B f s u) = (term33 A B s f u).
Proof. exact (EQ_MP (@lem5047876 A B s f u) (@lem5047861 A B s u f)). Qed.
Lemma lem5047882 {A B : Type'} (s : A -> Prop) (f : A -> B) (u : B -> Prop) : (term11 A B f s u) = (term33 A B s f u).
Proof. exact (TRANS (@lem5047857 A B f s u) (@lem5047877 A B s f u)). Qed.
Lemma lem5047885 {A B : Type'} (f : A -> B) (s : A -> Prop) (u : B -> Prop) : (term33 A B s f u) = (term11 A B f s u).
Proof. exact (SYM (@lem5047882 A B s f u)). Qed.
Lemma lem5047886 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem5047887 {A B : Type'} (x : A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term9 A B u s f) : term34 A B u s f x.
Proof. exact (@lem5047852 A B u s f h1 (@INSERT A x (@EMPTY A))). Qed.
Lemma lem5047888 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term34 A B u s f x) = (term35 A B u s f x).
Proof. exact (eq_refl (term34 A B u s f x)). Qed.
Lemma lem5047889 {A B : Type'} (x : A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term9 A B u s f) : term35 A B u s f x.
Proof. exact (EQ_MP (@lem5047888 A B u s f x) (@lem5047887 A B x u s f h1)). Qed.
Lemma lem5047907 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term8 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem5047908 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term8 A s t).
Proof. exact (@lem5047907 A s t). Qed.
Lemma lem5047909 {A : Type'} (x : A) (s : A -> Prop) : (term36 A x s) = (term37 A x s).
Proof. exact (@lem5047908 A (@INSERT A x (@EMPTY A)) s). Qed.
Lemma lem5047916 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5047917 {A : Type'} (x : A) (s : A -> Prop) : (term38 A x s) = (term39 A x s).
Proof. exact (MK_COMB (@lem5047916) (@lem5047909 A x s)). Qed.
Lemma lem5047925 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term8 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem5047926 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (@SUBSET B s t) = (term8 B s t).
Proof. exact (@lem5047925 B s t). Qed.
Lemma lem5047927 {B : Type'} (t : B -> Prop) (u : B -> Prop) : (@SUBSET B t u) = (term8 B t u).
Proof. exact (@lem5047926 B t u). Qed.
Lemma lem5047934 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5047935 {B : Type'} (t : B -> Prop) (u : B -> Prop) : (term40 B t u) = (term41 B t u).
Proof. exact (MK_COMB (@lem5047934) (@lem5047927 B t u)). Qed.
Lemma lem5047939 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term42 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem5047940 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term42 A s t).
Proof. exact (@lem5047939 A s t). Qed.
Lemma lem5047941 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) (x : A) : ((term43 A B s f t) = (@INSERT A x (@EMPTY A))) = (term44 A B s f t x).
Proof. exact (@lem5047940 A (term43 A B s f t) (@INSERT A x (@EMPTY A))). Qed.
Lemma lem5047956 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (x : A) : (term45 A B u s f t x) = (term46 A B u s f t x).
Proof. exact (MK_COMB (@lem5047935 B t u) (@lem5047941 A B s f t x)). Qed.
Lemma lem5047959 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term47 A B u s f x) = (term48 A B u s f x).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5047956 A B u s f t x)). Qed.
Lemma lem5047960 {B : Type'} : (@ex (B -> Prop)) = (@ex (B -> Prop)).
Proof. exact (eq_refl (@ex (B -> Prop))). Qed.
Lemma lem5047961 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term49 A B u s f x) = (term50 A B u s f x).
Proof. exact (MK_COMB (@lem5047960 B) (@lem5047959 A B u s f x)). Qed.
Lemma lem5047966 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term35 A B u s f x) = (term51 A B u s f x).
Proof. exact (MK_COMB (@lem5047917 A x s) (@lem5047961 A B u s f x)). Qed.
Lemma lem5047969 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5047970 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term52 A B u s f x) = (term53 A B u s f x).
Proof. exact (MK_COMB (@lem5047969) (@lem5047966 A B u s f x)). Qed.
Lemma lem5047971 {A B : Type'} (f : A -> B) (x : A) (u : B -> Prop) : (term27 A B f x u) = (term27 A B f x u).
Proof. exact (eq_refl (term27 A B f x u)). Qed.
Lemma lem5047972 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (u : B -> Prop) : (term54 A B s f x u) = (term55 A B s f x u).
Proof. exact (MK_COMB (@lem5047970 A B u s f x) (@lem5047971 A B f x u)). Qed.
Lemma lem5047975 {A : Type'} (x : A) (s : A -> Prop) : (term28 A x s) = (term28 A x s).
Proof. exact (eq_refl (term28 A x s)). Qed.
Lemma lem5047976 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (u : B -> Prop) : (term56 A B s f x u) = (term57 A B s f x u).
Proof. exact (MK_COMB (@lem5047975 A x s) (@lem5047972 A B s f x u)). Qed.
Lemma lem5047979 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (u : B -> Prop) : (term57 A B s f x u) = (term56 A B s f x u).
Proof. exact (SYM (@lem5047976 A B s f x u)). Qed.
Lemma lem5047983 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5047984 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5047983 A P x). Qed.
Lemma lem5047985 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem5047984 A s x). Qed.
Lemma lem5047986 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5047987 {A : Type'} (s : A -> Prop) (x : A) : (term28 A x s) = (term58 A s x).
Proof. exact (MK_COMB (@lem5047986) (@lem5047985 A s x)). Qed.
Lemma lem5047999 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term59 A x y s) = (term60 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem5048000 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term59 A x y s) = (term60 A y x s).
Proof. exact (@lem5047999 A y x s). Qed.
Lemma lem5048001 {A : Type'} (x : A) (x' : A) : (term61 A x' x) = (term62 A x x').
Proof. exact (@lem5048000 A x x' (@EMPTY A)). Qed.
Lemma lem5048007 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem5048008 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem5048007 A x). Qed.
Lemma lem5048009 {A : Type'} (x' : A) : (@IN A x' (@EMPTY A)) = False.
Proof. exact (@lem5048008 A x'). Qed.
Lemma lem5048010 {A : Type'} (x' : A) (x : A) : (term63 A x' x) = (term63 A x' x).
Proof. exact (eq_refl (term63 A x' x)). Qed.
Lemma lem5048011 {A : Type'} (x' : A) (x : A) : (term62 A x x') = (term64 A x' x).
Proof. exact (MK_COMB (@lem5048010 A x' x) (@lem5048009 A x')). Qed.
Lemma lem5048013 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem5048014 {A : Type'} (x' : A) (x : A) : (term64 A x' x) = (x' = x).
Proof. exact (@lem5048013 (x' = x)). Qed.
Lemma lem5048017 {A : Type'} (x' : A) (x : A) : (term62 A x x') = (x' = x).
Proof. exact (TRANS (@lem5048011 A x' x) (@lem5048014 A x' x)). Qed.
Lemma lem5048018 {A : Type'} (x' : A) (x : A) : (term61 A x' x) = (x' = x).
Proof. exact (TRANS (@lem5048001 A x x') (@lem5048017 A x' x)). Qed.
Lemma lem5048019 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5048020 {A : Type'} (x' : A) (x : A) : (term65 A x' x) = (term66 A x' x).
Proof. exact (MK_COMB (@lem5048019) (@lem5048018 A x' x)). Qed.
Lemma lem5048022 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5048023 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5048022 A P x). Qed.
Lemma lem5048024 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem5048023 A s x'). Qed.
Lemma lem5048025 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term67 A x x' s) = (term68 A x s x').
Proof. exact (MK_COMB (@lem5048020 A x' x) (@lem5048024 A s x')). Qed.
Lemma lem5048030 {A : Type'} (x : A) (s : A -> Prop) : (term69 A x s) = (term70 A x s).
Proof. exact (fun_ext (fun x' : A => @lem5048025 A x s x')). Qed.
Lemma lem5048031 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5048032 {A : Type'} (x : A) (s : A -> Prop) : (term37 A x s) = (term71 A x s).
Proof. exact (MK_COMB (@lem5048031 A) (@lem5048030 A x s)). Qed.
Lemma lem5048037 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5048038 {A : Type'} (x : A) (s : A -> Prop) : (term39 A x s) = (term72 A x s).
Proof. exact (MK_COMB (@lem5048037) (@lem5048032 A x s)). Qed.
Lemma lem5048052 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5048053 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem5048052 B P x). Qed.
Lemma lem5048054 {B : Type'} (t : B -> Prop) (x : B) : (@IN B x t) = (t x).
Proof. exact (@lem5048053 B t x). Qed.
Lemma lem5048055 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5048056 {B : Type'} (t : B -> Prop) (x : B) : (term28 B x t) = (term58 B t x).
Proof. exact (MK_COMB (@lem5048055) (@lem5048054 B t x)). Qed.
Lemma lem5048058 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5048059 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem5048058 B P x). Qed.
Lemma lem5048060 {B : Type'} (u : B -> Prop) (x : B) : (@IN B x u) = (u x).
Proof. exact (@lem5048059 B u x). Qed.
Lemma lem5048061 {B : Type'} (t : B -> Prop) (u : B -> Prop) (x : B) : (term73 B t x u) = (term74 B t u x).
Proof. exact (MK_COMB (@lem5048056 B t x) (@lem5048060 B u x)). Qed.
Lemma lem5048064 {B : Type'} (t : B -> Prop) (u : B -> Prop) : (term75 B t u) = (term76 B t u).
Proof. exact (fun_ext (fun x : B => @lem5048061 B t u x)). Qed.
Lemma lem5048065 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5048066 {B : Type'} (t : B -> Prop) (u : B -> Prop) : (term8 B t u) = (term77 B t u).
Proof. exact (MK_COMB (@lem5048065 B) (@lem5048064 B t u)). Qed.
Lemma lem5048071 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5048072 {B : Type'} (t : B -> Prop) (u : B -> Prop) : (term41 B t u) = (term78 B t u).
Proof. exact (MK_COMB (@lem5048071) (@lem5048066 B t u)). Qed.
Lemma lem5048080 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term79 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem5048081 {A : Type'} (p : A -> Prop) (x : A) : (term79 A x p) = (p x).
Proof. exact (@lem5048080 A p x). Qed.
Lemma lem5048082 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) (x' : A) : (term80 A B x' s f t) = (term81 A B s f t x').
Proof. exact (@lem5048081 A (term82 A B s f t) x'). Qed.
Lemma lem5048083 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (t : B -> Prop) : (term81 A B s f t x) = (term83 A B s f x t).
Proof. exact (eq_refl (term81 A B s f t x)). Qed.
Lemma lem5048084 {A : Type'} (GEN_PVAR_222 : A) : (@SETSPEC A GEN_PVAR_222) = (@SETSPEC A GEN_PVAR_222).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_222)). Qed.
Lemma lem5048085 {A B : Type'} (GEN_PVAR_222 : A) (s : A -> Prop) (f : A -> B) (x : A) (t : B -> Prop) : (term84 A B GEN_PVAR_222 s f t x) = (term85 A B GEN_PVAR_222 s f x t).
Proof. exact (MK_COMB (@lem5048084 A GEN_PVAR_222) (@lem5048083 A B s f x t)). Qed.
Lemma lem5048086 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5048087 {A B : Type'} (GEN_PVAR_222 : A) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (x : A) : (term86 A B GEN_PVAR_222 s f t x) = (term87 A B GEN_PVAR_222 s f t x).
Proof. exact (MK_COMB (@lem5048085 A B GEN_PVAR_222 s f x t) (@lem5048086 A x)). Qed.
Lemma lem5048088 {A B : Type'} (GEN_PVAR_222 : A) (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term88 A B GEN_PVAR_222 s f t) = (term89 A B GEN_PVAR_222 s f t).
Proof. exact (fun_ext (fun x : A => @lem5048087 A B GEN_PVAR_222 s f t x)). Qed.
Lemma lem5048089 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5048090 {A B : Type'} (GEN_PVAR_222 : A) (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term90 A B GEN_PVAR_222 s f t) = (term91 A B GEN_PVAR_222 s f t).
Proof. exact (MK_COMB (@lem5048089 A) (@lem5048088 A B GEN_PVAR_222 s f t)). Qed.
Lemma lem5048091 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term92 A B s f t) = (term93 A B s f t).
Proof. exact (fun_ext (fun GEN_PVAR_222 : A => @lem5048090 A B GEN_PVAR_222 s f t)). Qed.
Lemma lem5048092 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem5048093 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term94 A B s f t) = (term43 A B s f t).
Proof. exact (MK_COMB (@lem5048092 A) (@lem5048091 A B s f t)). Qed.
Lemma lem5048094 {A : Type'} (x' : A) : (@IN A x') = (@IN A x').
Proof. exact (eq_refl (@IN A x')). Qed.
Lemma lem5048095 {A B : Type'} (x' : A) (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term80 A B x' s f t) = (term95 A B x' s f t).
Proof. exact (MK_COMB (@lem5048094 A x') (@lem5048093 A B s f t)). Qed.
Lemma lem5048096 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5048097 {A B : Type'} (x' : A) (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term96 A B x' s f t) = (term97 A B x' s f t).
Proof. exact (MK_COMB (@lem5048096) (@lem5048095 A B x' s f t)). Qed.
Lemma lem5048098 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (t : B -> Prop) : (term81 A B s f t x') = (term83 A B s f x' t).
Proof. exact (eq_refl (term81 A B s f t x')). Qed.
Lemma lem5048099 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (t : B -> Prop) : ((term80 A B x' s f t) = (term81 A B s f t x')) = ((term95 A B x' s f t) = (term83 A B s f x' t)).
Proof. exact (MK_COMB (@lem5048097 A B x' s f t) (@lem5048098 A B s f x' t)). Qed.
Lemma lem5048100 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (t : B -> Prop) : (term95 A B x' s f t) = (term83 A B s f x' t).
Proof. exact (EQ_MP (@lem5048099 A B s f x' t) (@lem5048082 A B s f t x')). Qed.
Lemma lem5048104 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5048105 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5048104 A P x). Qed.
Lemma lem5048106 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem5048105 A s x'). Qed.
Lemma lem5048107 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5048108 {A : Type'} (s : A -> Prop) (x' : A) : (term98 A x' s) = (term99 A s x').
Proof. exact (MK_COMB (@lem5048107) (@lem5048106 A s x')). Qed.
Lemma lem5048110 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5048111 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem5048110 B P x). Qed.
Lemma lem5048112 {A B : Type'} (t : B -> Prop) (f : A -> B) (x' : A) : (term27 A B f x' t) = (term100 A B t f x').
Proof. exact (@lem5048111 B t (f x')). Qed.
Lemma lem5048113 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x' : A) : (term83 A B s f x' t) = (term101 A B s t f x').
Proof. exact (MK_COMB (@lem5048108 A s x') (@lem5048112 A B t f x')). Qed.
Lemma lem5048116 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x' : A) : (term95 A B x' s f t) = (term101 A B s t f x').
Proof. exact (TRANS (@lem5048100 A B s f x' t) (@lem5048113 A B s t f x')). Qed.
Lemma lem5048117 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5048118 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x' : A) : (term97 A B x' s f t) = (term102 A B s t f x').
Proof. exact (MK_COMB (@lem5048117) (@lem5048116 A B s t f x')). Qed.
Lemma lem5048120 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term59 A x y s) = (term60 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem5048121 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term59 A x y s) = (term60 A y x s).
Proof. exact (@lem5048120 A y x s). Qed.
Lemma lem5048122 {A : Type'} (x : A) (x' : A) : (term61 A x' x) = (term62 A x x').
Proof. exact (@lem5048121 A x x' (@EMPTY A)). Qed.
Lemma lem5048128 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem5048129 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem5048128 A x). Qed.
Lemma lem5048130 {A : Type'} (x' : A) : (@IN A x' (@EMPTY A)) = False.
Proof. exact (@lem5048129 A x'). Qed.
Lemma lem5048131 {A : Type'} (x' : A) (x : A) : (term63 A x' x) = (term63 A x' x).
Proof. exact (eq_refl (term63 A x' x)). Qed.
Lemma lem5048132 {A : Type'} (x' : A) (x : A) : (term62 A x x') = (term64 A x' x).
Proof. exact (MK_COMB (@lem5048131 A x' x) (@lem5048130 A x')). Qed.
Lemma lem5048134 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem5048135 {A : Type'} (x' : A) (x : A) : (term64 A x' x) = (x' = x).
Proof. exact (@lem5048134 (x' = x)). Qed.
Lemma lem5048138 {A : Type'} (x' : A) (x : A) : (term62 A x x') = (x' = x).
Proof. exact (TRANS (@lem5048132 A x' x) (@lem5048135 A x' x)). Qed.
Lemma lem5048139 {A : Type'} (x' : A) (x : A) : (term61 A x' x) = (x' = x).
Proof. exact (TRANS (@lem5048122 A x x') (@lem5048138 A x' x)). Qed.
Lemma lem5048140 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x' : A) (x : A) : ((term95 A B x' s f t) = (term61 A x' x)) = ((term101 A B s t f x') = (x' = x)).
Proof. exact (MK_COMB (@lem5048118 A B s t f x') (@lem5048139 A x' x)). Qed.
Lemma lem5048143 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term103 A B s f t x) = (term104 A B s t f x).
Proof. exact (fun_ext (fun x' : A => @lem5048140 A B s t f x' x)). Qed.
Lemma lem5048144 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5048145 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term44 A B s f t x) = (term105 A B s t f x).
Proof. exact (MK_COMB (@lem5048144 A) (@lem5048143 A B s t f x)). Qed.
Lemma lem5048150 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term46 A B u s f t x) = (term106 A B u s t f x).
Proof. exact (MK_COMB (@lem5048072 B t u) (@lem5048145 A B s t f x)). Qed.
Lemma lem5048153 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term48 A B u s f x) = (term107 A B u s f x).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5048150 A B u s t f x)). Qed.
Lemma lem5048154 {B : Type'} : (@ex (B -> Prop)) = (@ex (B -> Prop)).
Proof. exact (eq_refl (@ex (B -> Prop))). Qed.
Lemma lem5048155 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term50 A B u s f x) = (term108 A B u s f x).
Proof. exact (MK_COMB (@lem5048154 B) (@lem5048153 A B u s f x)). Qed.
Lemma lem5048160 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term51 A B u s f x) = (term109 A B u s f x).
Proof. exact (MK_COMB (@lem5048038 A x s) (@lem5048155 A B u s f x)). Qed.
Lemma lem5048163 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5048164 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term53 A B u s f x) = (term110 A B u s f x).
Proof. exact (MK_COMB (@lem5048163) (@lem5048160 A B u s f x)). Qed.
Lemma lem5048166 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5048167 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem5048166 B P x). Qed.
Lemma lem5048168 {A B : Type'} (u : B -> Prop) (f : A -> B) (x : A) : (term27 A B f x u) = (term100 A B u f x).
Proof. exact (@lem5048167 B u (f x)). Qed.
Lemma lem5048169 {A B : Type'} (s : A -> Prop) (u : B -> Prop) (f : A -> B) (x : A) : (term55 A B s f x u) = (term111 A B s u f x).
Proof. exact (MK_COMB (@lem5048164 A B u s f x) (@lem5048168 A B u f x)). Qed.
Lemma lem5048172 {A B : Type'} (s : A -> Prop) (u : B -> Prop) (f : A -> B) (x : A) : (term57 A B s f x u) = (term112 A B s u f x).
Proof. exact (MK_COMB (@lem5047987 A s x) (@lem5048169 A B s u f x)). Qed.
Lemma lem5048175 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (u : B -> Prop) : (term112 A B s u f x) = (term57 A B s f x u).
Proof. exact (SYM (@lem5048172 A B s u f x)). Qed.
Lemma lem5048177 (p : Prop) : p = (term113 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5048178 {A B : Type'} (s : A -> Prop) (u : B -> Prop) (f : A -> B) (x : A) : (term112 A B s u f x) = (term114 A B s u f x).
Proof. exact (@lem5048177 (term112 A B s u f x)). Qed.
Lemma lem5048179 {A B : Type'} (s : A -> Prop) (u : B -> Prop) (f : A -> B) (x : A) : (term114 A B s u f x) = (term112 A B s u f x).
Proof. exact (SYM (@lem5048178 A B s u f x)). Qed.
Lemma lem5048180 {A B : Type'} (s : A -> Prop) (u : B -> Prop) (f : A -> B) (x : A) (h1 : term115 A B s u f x) : term115 A B s u f x.
Proof. exact (h1). Qed.
Lemma lem5048183 {A B : Type'} (s : A -> Prop) (u : B -> Prop) (f : A -> B) (x : A) (h1 : term114 A B s u f x) : term114 A B s u f x.
Proof. exact (h1). Qed.
Lemma lem5048184 {A B : Type'} (s : A -> Prop) (u : B -> Prop) (f : A -> B) (x : A) : term116 A B s u f x.
Proof. exact (fun h0 : term114 A B s u f x => @lem5048183 A B s u f x h0). Qed.
Lemma lem5048185 {A B : Type'} (s : A -> Prop) (u : B -> Prop) (f : A -> B) (x : A) (h1 : term116 A B s u f x) : term116 A B s u f x.
Proof. exact (h1). Qed.
Lemma lem5048186 {A B : Type'} (s : A -> Prop) (u : B -> Prop) (f : A -> B) (x : A) (h1 : term114 A B s u f x) : term114 A B s u f x.
Proof. exact (h1). Qed.
Lemma lem5048187 {A B : Type'} (s : A -> Prop) (u : B -> Prop) (f : A -> B) (x : A) (h1 : term114 A B s u f x) (h2 : term116 A B s u f x) : term114 A B s u f x.
Proof. exact (@lem5048185 A B s u f x h2 (@lem5048186 A B s u f x h1)). Qed.
Lemma lem5048188 {A B : Type'} (s : A -> Prop) (u : B -> Prop) (f : A -> B) (x : A) (h1 : term114 A B s u f x) : term117 A B s u f x.
Proof. exact (fun h0 : term116 A B s u f x => @lem5048187 A B s u f x h1 h0). Qed.
Lemma lem5048189 {A B : Type'} (s : A -> Prop) (u : B -> Prop) (f : A -> B) (x : A) (h1 : term116 A B s u f x) : term116 A B s u f x.
Proof. exact (h1). Qed.
Lemma lem5048190 {A B : Type'} (s : A -> Prop) (u : B -> Prop) (f : A -> B) (x : A) (h1 : term114 A B s u f x) (h2 : term116 A B s u f x) : term114 A B s u f x.
Proof. exact (@lem5048188 A B s u f x h1 (@lem5048189 A B s u f x h2)). Qed.
Lemma lem5048191 {A B : Type'} (s : A -> Prop) (u : B -> Prop) (f : A -> B) (x : A) (h1 : term116 A B s u f x) : term116 A B s u f x.
Proof. exact (fun h0 : term114 A B s u f x => @lem5048190 A B s u f x h0 h1). Qed.
Lemma lem5048192 {A B : Type'} (s : A -> Prop) (u : B -> Prop) (f : A -> B) (x : A) : term118 A B s u f x.
Proof. exact (fun h0 : term116 A B s u f x => @lem5048191 A B s u f x h0). Qed.
Lemma lem5048195 {A B : Type'} (s : A -> Prop) (u : B -> Prop) (f : A -> B) (x : A) : term116 A B s u f x.
Proof. exact (@lem5048192 A B s u f x (@lem5048184 A B s u f x)). Qed.
Lemma lem5048196 {A B : Type'} (s : A -> Prop) (u : B -> Prop) (f : A -> B) (x : A) : term116 A B s u f x.
Proof. exact (@lem5048195 A B s u f x). Qed.
Lemma lem5048214 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5048215 {A B : Type'} (s : A -> Prop) (u : B -> Prop) (f : A -> B) (x : A) : (term114 A B s u f x) = (term119 A B s u f x).
Proof. exact (@lem5048214 (term115 A B s u f x)). Qed.
Lemma lem5048217 (t : Prop) : (term120 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5048218 {A B : Type'} (s : A -> Prop) (u : B -> Prop) (f : A -> B) (x : A) : (term119 A B s u f x) = (term112 A B s u f x).
Proof. exact (@lem5048217 (term112 A B s u f x)). Qed.
Lemma lem5048221 {A B : Type'} (s : A -> Prop) (u : B -> Prop) (f : A -> B) (x : A) : (term114 A B s u f x) = (term112 A B s u f x).
Proof. exact (TRANS (@lem5048215 A B s u f x) (@lem5048218 A B s u f x)). Qed.
Lemma lem5048294 {A B : Type'} (u : B -> Prop) (f : A -> B) (x : A) : (term121 A B u f x) = (term122 A B u f x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5048221 A B s u f x)). Qed.
Lemma lem5048295 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5048296 {A B : Type'} (u : B -> Prop) (f : A -> B) (x : A) : (term123 A B u f x) = (term124 A B u f x).
Proof. exact (MK_COMB (@lem5048295 A) (@lem5048294 A B u f x)). Qed.
Lemma lem5048301 {A B : Type'} (f : A -> B) (x : A) : (term125 A B f x) = (term126 A B f x).
Proof. exact (fun_ext (fun u : B -> Prop => @lem5048296 A B u f x)). Qed.
Lemma lem5048302 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5048303 {A B : Type'} (f : A -> B) (x : A) : (term127 A B f x) = (term128 A B f x).
Proof. exact (MK_COMB (@lem5048302 B) (@lem5048301 A B f x)). Qed.
Lemma lem5048308 {A B : Type'} (x : A) : (term129 A B x) = (term130 A B x).
Proof. exact (fun_ext (fun f : A -> B => @lem5048303 A B f x)). Qed.
Lemma lem5048309 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5048310 {A B : Type'} (x : A) : (term131 A B x) = (term132 A B x).
Proof. exact (MK_COMB (@lem5048309 A B) (@lem5048308 A B x)). Qed.
Lemma lem5048315 {A B : Type'} : (term133 A B) = (term134 A B).
Proof. exact (fun_ext (fun x : A => @lem5048310 A B x)). Qed.
Lemma lem5048316 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5048325 {A B : Type'} : (term135 A B) = (term136 A B).
Proof. exact (MK_COMB (@lem5048316 A) (@lem5048315 A B)). Qed.
Lemma lem5048326 {A B : Type'} (u : B -> Prop) (f : A -> B) (x : A) : (term100 A B u f x) = (term100 A B u f x).
Proof. exact (eq_refl (term100 A B u f x)). Qed.
Lemma lem5048335 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x' : A) (x : A) : ((term101 A B s t f x') = (x' = x)) = ((term101 A B s t f x') = (x' = x)).
Proof. exact (eq_refl ((term101 A B s t f x') = (x' = x))). Qed.
Lemma lem5048336 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term104 A B s t f x) = (term104 A B s t f x).
Proof. exact (fun_ext (fun x' : A => @lem5048335 A B s t f x' x)). Qed.
Lemma lem5048337 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5048338 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term105 A B s t f x) = (term105 A B s t f x).
Proof. exact (MK_COMB (@lem5048337 A) (@lem5048336 A B s t f x)). Qed.
Lemma lem5048343 {B : Type'} (t : B -> Prop) (u : B -> Prop) (x : B) : (term74 B t u x) = (term74 B t u x).
Proof. exact (eq_refl (term74 B t u x)). Qed.
Lemma lem5048344 {B : Type'} (t : B -> Prop) (u : B -> Prop) : (term76 B t u) = (term76 B t u).
Proof. exact (fun_ext (fun x : B => @lem5048343 B t u x)). Qed.
Lemma lem5048345 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5048346 {B : Type'} (t : B -> Prop) (u : B -> Prop) : (term77 B t u) = (term77 B t u).
Proof. exact (MK_COMB (@lem5048345 B) (@lem5048344 B t u)). Qed.
Lemma lem5048347 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5048348 {B : Type'} (t : B -> Prop) (u : B -> Prop) : (term78 B t u) = (term78 B t u).
Proof. exact (MK_COMB (@lem5048347) (@lem5048346 B t u)). Qed.
Lemma lem5048349 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term106 A B u s t f x) = (term106 A B u s t f x).
Proof. exact (MK_COMB (@lem5048348 B t u) (@lem5048338 A B s t f x)). Qed.
Lemma lem5048350 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term107 A B u s f x) = (term107 A B u s f x).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5048349 A B u s t f x)). Qed.
Lemma lem5048351 {B : Type'} : (@ex (B -> Prop)) = (@ex (B -> Prop)).
Proof. exact (eq_refl (@ex (B -> Prop))). Qed.
Lemma lem5048352 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term108 A B u s f x) = (term108 A B u s f x).
Proof. exact (MK_COMB (@lem5048351 B) (@lem5048350 A B u s f x)). Qed.
Lemma lem5048357 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term68 A x s x') = (term68 A x s x').
Proof. exact (eq_refl (term68 A x s x')). Qed.
Lemma lem5048358 {A : Type'} (x : A) (s : A -> Prop) : (term70 A x s) = (term70 A x s).
Proof. exact (fun_ext (fun x' : A => @lem5048357 A x s x')). Qed.
Lemma lem5048359 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5048360 {A : Type'} (x : A) (s : A -> Prop) : (term71 A x s) = (term71 A x s).
Proof. exact (MK_COMB (@lem5048359 A) (@lem5048358 A x s)). Qed.
Lemma lem5048361 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5048362 {A : Type'} (x : A) (s : A -> Prop) : (term72 A x s) = (term72 A x s).
Proof. exact (MK_COMB (@lem5048361) (@lem5048360 A x s)). Qed.
Lemma lem5048363 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term109 A B u s f x) = (term109 A B u s f x).
Proof. exact (MK_COMB (@lem5048362 A x s) (@lem5048352 A B u s f x)). Qed.
Lemma lem5048364 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5048365 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term110 A B u s f x) = (term110 A B u s f x).
Proof. exact (MK_COMB (@lem5048364) (@lem5048363 A B u s f x)). Qed.
Lemma lem5048366 {A B : Type'} (s : A -> Prop) (u : B -> Prop) (f : A -> B) (x : A) : (term111 A B s u f x) = (term111 A B s u f x).
Proof. exact (MK_COMB (@lem5048365 A B u s f x) (@lem5048326 A B u f x)). Qed.
Lemma lem5048369 {A : Type'} (s : A -> Prop) (x : A) : (term58 A s x) = (term58 A s x).
Proof. exact (eq_refl (term58 A s x)). Qed.
Lemma lem5048370 {A B : Type'} (s : A -> Prop) (u : B -> Prop) (f : A -> B) (x : A) : (term112 A B s u f x) = (term112 A B s u f x).
Proof. exact (MK_COMB (@lem5048369 A s x) (@lem5048366 A B s u f x)). Qed.
Lemma lem5048371 {A B : Type'} (u : B -> Prop) (f : A -> B) (x : A) : (term122 A B u f x) = (term122 A B u f x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5048370 A B s u f x)). Qed.
Lemma lem5048372 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5048373 {A B : Type'} (u : B -> Prop) (f : A -> B) (x : A) : (term124 A B u f x) = (term124 A B u f x).
Proof. exact (MK_COMB (@lem5048372 A) (@lem5048371 A B u f x)). Qed.
Lemma lem5048374 {A B : Type'} (f : A -> B) (x : A) : (term126 A B f x) = (term126 A B f x).
Proof. exact (fun_ext (fun u : B -> Prop => @lem5048373 A B u f x)). Qed.
Lemma lem5048375 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5048376 {A B : Type'} (f : A -> B) (x : A) : (term128 A B f x) = (term128 A B f x).
Proof. exact (MK_COMB (@lem5048375 B) (@lem5048374 A B f x)). Qed.
Lemma lem5048377 {A B : Type'} (x : A) : (term130 A B x) = (term130 A B x).
Proof. exact (fun_ext (fun f : A -> B => @lem5048376 A B f x)). Qed.
Lemma lem5048378 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5048379 {A B : Type'} (x : A) : (term132 A B x) = (term132 A B x).
Proof. exact (MK_COMB (@lem5048378 A B) (@lem5048377 A B x)). Qed.
Lemma lem5048380 {A B : Type'} : (term134 A B) = (term134 A B).
Proof. exact (fun_ext (fun x : A => @lem5048379 A B x)). Qed.
Lemma lem5048381 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5048382 {A B : Type'} : (term136 A B) = (term136 A B).
Proof. exact (MK_COMB (@lem5048381 A) (@lem5048380 A B)). Qed.
Lemma lem5048447 {A B : Type'} : (term135 A B) = (term136 A B).
Proof. exact (TRANS (@lem5048325 A B) (@lem5048382 A B)). Qed.
Lemma lem5048448 {A B : Type'} : (term136 A B) = (term135 A B).
Proof. exact (SYM (@lem5048447 A B)). Qed.
Lemma lem5048450 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term109 A B u s f x) : term109 A B u s f x.
Proof. exact (h1). Qed.
Lemma lem5048452 (p : Prop) : p = (term113 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5048453 {A B : Type'} (u : B -> Prop) (f : A -> B) (x : A) : (term100 A B u f x) = (term137 A B u f x).
Proof. exact (@lem5048452 (term100 A B u f x)). Qed.
Lemma lem5048454 {A B : Type'} (u : B -> Prop) (f : A -> B) (x : A) : (term137 A B u f x) = (term100 A B u f x).
Proof. exact (SYM (@lem5048453 A B u f x)). Qed.
Lemma lem5048455 {A B : Type'} (u : B -> Prop) (f : A -> B) (x : A) (h1 : term138 A B u f x) : term138 A B u f x.
Proof. exact (h1). Qed.
Lemma lem5048461 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem5048468 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term139 A x s x') = (term140 A x s x').
Proof. exact (@lem17362 (x' = x) (s x')). Qed.
Lemma lem5048469 {A : Type'} (P : A -> Prop) : (term141 A P) = (term142 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem5048470 {A : Type'} (x : A) (s : A -> Prop) : (term143 A x s) = (term144 A x s).
Proof. exact (@lem5048469 A (term70 A x s)). Qed.
Lemma lem5048471 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term145 A x s x') = (term68 A x s x').
Proof. exact (eq_refl (term145 A x s x')). Qed.
Lemma lem5048472 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5048473 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term146 A x s x') = (term139 A x s x').
Proof. exact (MK_COMB (@lem5048472) (@lem5048471 A x s x')). Qed.
Lemma lem5048474 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term146 A x s x') = (term140 A x s x').
Proof. exact (TRANS (@lem5048473 A x s x') (@lem5048468 A x s x')). Qed.
Lemma lem5048475 {A : Type'} (x : A) (s : A -> Prop) : (term147 A x s) = (term148 A x s).
Proof. exact (fun_ext (fun x' : A => @lem5048474 A x s x')). Qed.
Lemma lem5048476 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5048477 {A : Type'} (x : A) (s : A -> Prop) : (term144 A x s) = (term149 A x s).
Proof. exact (MK_COMB (@lem5048476 A) (@lem5048475 A x s)). Qed.
Lemma lem5048478 {A : Type'} (x : A) (s : A -> Prop) : (term143 A x s) = (term149 A x s).
Proof. exact (TRANS (@lem5048470 A x s) (@lem5048477 A x s)). Qed.
Lemma lem5048485 {B : Type'} (t : B -> Prop) (u : B -> Prop) (x : B) : (term74 B t u x) = (term150 B t u x).
Proof. exact (@lem17265 (t x) (u x)). Qed.
Lemma lem5048486 {B : Type'} (t : B -> Prop) (u : B -> Prop) : (term76 B t u) = (term151 B t u).
Proof. exact (fun_ext (fun x : B => @lem5048485 B t u x)). Qed.
Lemma lem5048487 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5048488 {B : Type'} (t : B -> Prop) (u : B -> Prop) : (term77 B t u) = (term152 B t u).
Proof. exact (MK_COMB (@lem5048487 B) (@lem5048486 B t u)). Qed.
Lemma lem5048497 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x' : A) : (term153 A B s t f x') = (term154 A B s t f x').
Proof. exact (@lem17045 (s x') (term100 A B t f x')). Qed.
Lemma lem5048502 {A : Type'} (x' : A) (x : A) : (x' = x) = (x' = x).
Proof. exact (eq_refl (x' = x)). Qed.
Lemma lem5048503 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5048504 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x' : A) : (term155 A B s t f x') = (term156 A B s t f x').
Proof. exact (MK_COMB (@lem5048503) (@lem5048497 A B s t f x')). Qed.
Lemma lem5048505 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x' : A) (x : A) : (term157 A B s t f x' x) = (term158 A B s t f x' x).
Proof. exact (MK_COMB (@lem5048504 A B s t f x') (@lem5048502 A x' x)). Qed.
Lemma lem5048510 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x' : A) (x : A) : (term159 A B s t f x' x) = (term159 A B s t f x' x).
Proof. exact (eq_refl (term159 A B s t f x' x)). Qed.
Lemma lem5048511 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x' : A) (x : A) : (term160 A B s t f x' x) = (term161 A B s t f x' x).
Proof. exact (MK_COMB (@lem5048510 A B s t f x' x) (@lem5048505 A B s t f x' x)). Qed.
Lemma lem5048512 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x' : A) (x : A) : ((term101 A B s t f x') = (x' = x)) = (term160 A B s t f x' x).
Proof. exact (@lem17784 (term101 A B s t f x') (x' = x)). Qed.
Lemma lem5048513 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x' : A) (x : A) : ((term101 A B s t f x') = (x' = x)) = (term161 A B s t f x' x).
Proof. exact (TRANS (@lem5048512 A B s t f x' x) (@lem5048511 A B s t f x' x)). Qed.
Lemma lem5048514 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term104 A B s t f x) = (term162 A B s t f x).
Proof. exact (fun_ext (fun x' : A => @lem5048513 A B s t f x' x)). Qed.
Lemma lem5048515 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5048516 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term105 A B s t f x) = (term163 A B s t f x).
Proof. exact (MK_COMB (@lem5048515 A) (@lem5048514 A B s t f x)). Qed.
Lemma lem5048517 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5048518 {B : Type'} (t : B -> Prop) (u : B -> Prop) : (term78 B t u) = (term164 B t u).
Proof. exact (MK_COMB (@lem5048517) (@lem5048488 B t u)). Qed.
Lemma lem5048519 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term106 A B u s t f x) = (term165 A B u s t f x).
Proof. exact (MK_COMB (@lem5048518 B t u) (@lem5048516 A B s t f x)). Qed.
Lemma lem5048520 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term107 A B u s f x) = (term166 A B u s f x).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5048519 A B u s t f x)). Qed.
Lemma lem5048521 {B : Type'} : (@ex (B -> Prop)) = (@ex (B -> Prop)).
Proof. exact (eq_refl (@ex (B -> Prop))). Qed.
Lemma lem5048522 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term108 A B u s f x) = (term167 A B u s f x).
Proof. exact (MK_COMB (@lem5048521 B) (@lem5048520 A B u s f x)). Qed.
Lemma lem5048523 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5048524 {A : Type'} (x : A) (s : A -> Prop) : (term168 A x s) = (term169 A x s).
Proof. exact (MK_COMB (@lem5048523) (@lem5048478 A x s)). Qed.
Lemma lem5048525 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term170 A B u s f x) = (term171 A B u s f x).
Proof. exact (MK_COMB (@lem5048524 A x s) (@lem5048522 A B u s f x)). Qed.
Lemma lem5048526 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term109 A B u s f x) = (term170 A B u s f x).
Proof. exact (@lem17265 (term71 A x s) (term108 A B u s f x)). Qed.
Lemma lem5048527 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term109 A B u s f x) = (term171 A B u s f x).
Proof. exact (TRANS (@lem5048526 A B u s f x) (@lem5048525 A B u s f x)). Qed.
Lemma lem5048657 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term172 A P Q) = (term173 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5048658 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term172 A P Q) = (term173 A P Q).
Proof. exact (@lem5048657 A P Q). Qed.
Lemma lem5048659 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term174 A B s t f x) = (term175 A B s t f x).
Proof. exact (@lem5048658 A (term176 A B s t f x) (term177 A B s t f x)). Qed.
Lemma lem5048660 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x' : A) (x : A) : (term178 A B s t f x x') = (term179 A B s t f x' x).
Proof. exact (eq_refl (term178 A B s t f x x')). Qed.
Lemma lem5048661 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5048662 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x' : A) (x : A) : (term180 A B s t f x x') = (term159 A B s t f x' x).
Proof. exact (MK_COMB (@lem5048661) (@lem5048660 A B s t f x' x)). Qed.
Lemma lem5048663 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x' : A) (x : A) : (term181 A B s t f x x') = (term158 A B s t f x' x).
Proof. exact (eq_refl (term181 A B s t f x x')). Qed.
Lemma lem5048664 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x' : A) (x : A) : (term182 A B s t f x x') = (term161 A B s t f x' x).
Proof. exact (MK_COMB (@lem5048662 A B s t f x' x) (@lem5048663 A B s t f x' x)). Qed.
Lemma lem5048665 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term183 A B s t f x) = (term162 A B s t f x).
Proof. exact (fun_ext (fun x' : A => @lem5048664 A B s t f x' x)). Qed.
Lemma lem5048666 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5048667 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term174 A B s t f x) = (term163 A B s t f x).
Proof. exact (MK_COMB (@lem5048666 A) (@lem5048665 A B s t f x)). Qed.
Lemma lem5048668 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5048669 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term184 A B s t f x) = (term185 A B s t f x).
Proof. exact (MK_COMB (@lem5048668) (@lem5048667 A B s t f x)). Qed.
Lemma lem5048670 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x' : A) (x : A) : (term178 A B s t f x x') = (term179 A B s t f x' x).
Proof. exact (eq_refl (term178 A B s t f x x')). Qed.
Lemma lem5048671 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term186 A B s t f x) = (term176 A B s t f x).
Proof. exact (fun_ext (fun x' : A => @lem5048670 A B s t f x' x)). Qed.
Lemma lem5048672 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5048673 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term187 A B s t f x) = (term188 A B s t f x).
Proof. exact (MK_COMB (@lem5048672 A) (@lem5048671 A B s t f x)). Qed.
Lemma lem5048674 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5048675 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term189 A B s t f x) = (term190 A B s t f x).
Proof. exact (MK_COMB (@lem5048674) (@lem5048673 A B s t f x)). Qed.
Lemma lem5048676 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x' : A) (x : A) : (term181 A B s t f x x') = (term158 A B s t f x' x).
Proof. exact (eq_refl (term181 A B s t f x x')). Qed.
Lemma lem5048677 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term191 A B s t f x) = (term177 A B s t f x).
Proof. exact (fun_ext (fun x' : A => @lem5048676 A B s t f x' x)). Qed.
Lemma lem5048678 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5048679 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term192 A B s t f x) = (term193 A B s t f x).
Proof. exact (MK_COMB (@lem5048678 A) (@lem5048677 A B s t f x)). Qed.
Lemma lem5048680 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term175 A B s t f x) = (term194 A B s t f x).
Proof. exact (MK_COMB (@lem5048675 A B s t f x) (@lem5048679 A B s t f x)). Qed.
Lemma lem5048681 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : ((term174 A B s t f x) = (term175 A B s t f x)) = ((term163 A B s t f x) = (term194 A B s t f x)).
Proof. exact (MK_COMB (@lem5048669 A B s t f x) (@lem5048680 A B s t f x)). Qed.
Lemma lem5048682 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term163 A B s t f x) = (term194 A B s t f x).
Proof. exact (EQ_MP (@lem5048681 A B s t f x) (@lem5048659 A B s t f x)). Qed.
Lemma lem5048779 {B : Type'} (t : B -> Prop) (u : B -> Prop) : (term164 B t u) = (term164 B t u).
Proof. exact (eq_refl (term164 B t u)). Qed.
Lemma lem5048780 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term165 A B u s t f x) = (term195 A B u s t f x).
Proof. exact (MK_COMB (@lem5048779 B t u) (@lem5048682 A B s t f x)). Qed.
Lemma lem5048781 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term166 A B u s f x) = (term196 A B u s f x).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5048780 A B u s t f x)). Qed.
Lemma lem5048782 {B : Type'} : (@ex (B -> Prop)) = (@ex (B -> Prop)).
Proof. exact (eq_refl (@ex (B -> Prop))). Qed.
Lemma lem5048783 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term167 A B u s f x) = (term197 A B u s f x).
Proof. exact (MK_COMB (@lem5048782 B) (@lem5048781 A B u s f x)). Qed.
Lemma lem5048832 {A : Type'} (x : A) (s : A -> Prop) : (term169 A x s) = (term169 A x s).
Proof. exact (eq_refl (term169 A x s)). Qed.
Lemma lem5048833 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term171 A B u s f x) = (term198 A B u s f x).
Proof. exact (MK_COMB (@lem5048832 A x s) (@lem5048783 A B u s f x)). Qed.
Lemma lem5048837 {A : Type'} (P : A -> Prop) (Q : Prop) : (term199 A P Q) = (term200 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5048838 {A : Type'} (P : A -> Prop) (Q : Prop) : (term199 A P Q) = (term200 A P Q).
Proof. exact (@lem5048837 A P Q). Qed.
Lemma lem5048839 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term201 A B u s f x) = (term202 A B u s f x).
Proof. exact (@lem5048838 A (term148 A x s) (term197 A B u s f x)). Qed.
Lemma lem5048840 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term203 A x s x') = (term140 A x s x').
Proof. exact (eq_refl (term203 A x s x')). Qed.
Lemma lem5048841 {A : Type'} (x : A) (s : A -> Prop) : (term204 A x s) = (term148 A x s).
Proof. exact (fun_ext (fun x' : A => @lem5048840 A x s x')). Qed.
Lemma lem5048842 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5048843 {A : Type'} (x : A) (s : A -> Prop) : (term205 A x s) = (term149 A x s).
Proof. exact (MK_COMB (@lem5048842 A) (@lem5048841 A x s)). Qed.
Lemma lem5048844 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5048845 {A : Type'} (x : A) (s : A -> Prop) : (term206 A x s) = (term169 A x s).
Proof. exact (MK_COMB (@lem5048844) (@lem5048843 A x s)). Qed.
Lemma lem5048846 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term197 A B u s f x) = (term197 A B u s f x).
Proof. exact (eq_refl (term197 A B u s f x)). Qed.
Lemma lem5048847 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term201 A B u s f x) = (term198 A B u s f x).
Proof. exact (MK_COMB (@lem5048845 A x s) (@lem5048846 A B u s f x)). Qed.
Lemma lem5048848 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5048849 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term207 A B u s f x) = (term208 A B u s f x).
Proof. exact (MK_COMB (@lem5048848) (@lem5048847 A B u s f x)). Qed.
Lemma lem5048850 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term203 A x s x') = (term140 A x s x').
Proof. exact (eq_refl (term203 A x s x')). Qed.
Lemma lem5048851 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5048852 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term209 A x s x') = (term210 A x s x').
Proof. exact (MK_COMB (@lem5048851) (@lem5048850 A x s x')). Qed.
Lemma lem5048853 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term197 A B u s f x) = (term197 A B u s f x).
Proof. exact (eq_refl (term197 A B u s f x)). Qed.
Lemma lem5048854 {A B : Type'} (x' : A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term211 A B x' u s f x) = (term212 A B x' u s f x).
Proof. exact (MK_COMB (@lem5048852 A x s x') (@lem5048853 A B u s f x)). Qed.
Lemma lem5048855 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term213 A B u s f x) = (term214 A B u s f x).
Proof. exact (fun_ext (fun x' : A => @lem5048854 A B x' u s f x)). Qed.
Lemma lem5048856 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5048857 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term202 A B u s f x) = (term215 A B u s f x).
Proof. exact (MK_COMB (@lem5048856 A) (@lem5048855 A B u s f x)). Qed.
Lemma lem5048858 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : ((term201 A B u s f x) = (term202 A B u s f x)) = ((term198 A B u s f x) = (term215 A B u s f x)).
Proof. exact (MK_COMB (@lem5048849 A B u s f x) (@lem5048857 A B u s f x)). Qed.
Lemma lem5048859 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term198 A B u s f x) = (term215 A B u s f x).
Proof. exact (EQ_MP (@lem5048858 A B u s f x) (@lem5048839 A B u s f x)). Qed.
Lemma lem5048861 {A : Type'} (P : Prop) (Q : A -> Prop) : (term216 A P Q) = (term217 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5048862 {B : Type'} (P : Prop) (Q : type686 B) : (term218 B P Q) = (term219 B P Q).
Proof. exact (@lem5048861 (B -> Prop) P Q). Qed.
Lemma lem5048863 {A B : Type'} (x' : A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term220 A B x' u s f x) = (term221 A B x' u s f x).
Proof. exact (@lem5048862 B (term140 A x s x') (term196 A B u s f x)). Qed.
Lemma lem5048864 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term222 A B u s f x t) = (term195 A B u s t f x).
Proof. exact (eq_refl (term222 A B u s f x t)). Qed.
Lemma lem5048865 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term223 A B u s f x) = (term196 A B u s f x).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5048864 A B u s t f x)). Qed.
Lemma lem5048866 {B : Type'} : (@ex (B -> Prop)) = (@ex (B -> Prop)).
Proof. exact (eq_refl (@ex (B -> Prop))). Qed.
Lemma lem5048867 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term224 A B u s f x) = (term197 A B u s f x).
Proof. exact (MK_COMB (@lem5048866 B) (@lem5048865 A B u s f x)). Qed.
Lemma lem5048868 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term210 A x s x') = (term210 A x s x').
Proof. exact (eq_refl (term210 A x s x')). Qed.
Lemma lem5048869 {A B : Type'} (x' : A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term220 A B x' u s f x) = (term212 A B x' u s f x).
Proof. exact (MK_COMB (@lem5048868 A x s x') (@lem5048867 A B u s f x)). Qed.
Lemma lem5048870 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5048871 {A B : Type'} (x' : A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term225 A B x' u s f x) = (term226 A B x' u s f x).
Proof. exact (MK_COMB (@lem5048870) (@lem5048869 A B x' u s f x)). Qed.
Lemma lem5048872 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term222 A B u s f x t) = (term195 A B u s t f x).
Proof. exact (eq_refl (term222 A B u s f x t)). Qed.
Lemma lem5048873 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term210 A x s x') = (term210 A x s x').
Proof. exact (eq_refl (term210 A x s x')). Qed.
Lemma lem5048874 {A B : Type'} (x' : A) (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term227 A B x' u s f x t) = (term228 A B x' u s t f x).
Proof. exact (MK_COMB (@lem5048873 A x s x') (@lem5048872 A B u s t f x)). Qed.
Lemma lem5048875 {A B : Type'} (x' : A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term229 A B x' u s f x) = (term230 A B x' u s f x).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5048874 A B x' u s t f x)). Qed.
Lemma lem5048876 {B : Type'} : (@ex (B -> Prop)) = (@ex (B -> Prop)).
Proof. exact (eq_refl (@ex (B -> Prop))). Qed.
Lemma lem5048877 {A B : Type'} (x' : A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term221 A B x' u s f x) = (term231 A B x' u s f x).
Proof. exact (MK_COMB (@lem5048876 B) (@lem5048875 A B x' u s f x)). Qed.
Lemma lem5048878 {A B : Type'} (x' : A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : ((term220 A B x' u s f x) = (term221 A B x' u s f x)) = ((term212 A B x' u s f x) = (term231 A B x' u s f x)).
Proof. exact (MK_COMB (@lem5048871 A B x' u s f x) (@lem5048877 A B x' u s f x)). Qed.
Lemma lem5048879 {A B : Type'} (x' : A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term212 A B x' u s f x) = (term231 A B x' u s f x).
Proof. exact (EQ_MP (@lem5048878 A B x' u s f x) (@lem5048863 A B x' u s f x)). Qed.
Lemma lem5048880 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term214 A B u s f x) = (term232 A B u s f x).
Proof. exact (fun_ext (fun x' : A => @lem5048879 A B x' u s f x)). Qed.
Lemma lem5048881 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5048882 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term215 A B u s f x) = (term233 A B u s f x).
Proof. exact (MK_COMB (@lem5048881 A) (@lem5048880 A B u s f x)). Qed.
Lemma lem5048883 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term198 A B u s f x) = (term233 A B u s f x).
Proof. exact (TRANS (@lem5048859 A B u s f x) (@lem5048882 A B u s f x)). Qed.
Lemma lem5048884 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term171 A B u s f x) = (term233 A B u s f x).
Proof. exact (TRANS (@lem5048833 A B u s f x) (@lem5048883 A B u s f x)). Qed.
Lemma lem5048885 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term109 A B u s f x) = (term233 A B u s f x).
Proof. exact (TRANS (@lem5048527 A B u s f x) (@lem5048884 A B u s f x)). Qed.
Lemma lem5048886 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term109 A B u s f x) : term233 A B u s f x.
Proof. exact (EQ_MP (@lem5048885 A B u s f x) (@lem5048450 A B u s f x h1)). Qed.
Lemma lem5048892 {A B : Type'} (u : B -> Prop) (f : A -> B) (x : A) (h1 : term138 A B u f x) : term138 A B u f x.
Proof. exact (h1). Qed.
Lemma lem5048893 {A B : Type'} (x' : A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term231 A B x' u s f x) : term231 A B x' u s f x.
Proof. exact (h1). Qed.
Lemma lem5048894 {A B : Type'} (x' : A) (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term228 A B x' u s t f x) : term228 A B x' u s t f x.
Proof. exact (h1). Qed.
Lemma lem5048898 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem5048906 {A B : Type'} (u : B -> Prop) (f : A -> B) (x : A) (h1 : term138 A B u f x) : term138 A B u f x.
Proof. exact (h1). Qed.
Lemma lem5048929 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x' : A) (x : A) : (term158 A B s t f x' x) = (term158 A B s t f x' x).
Proof. exact (eq_refl (term158 A B s t f x' x)). Qed.
Lemma lem5048930 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term177 A B s t f x) = (term177 A B s t f x).
Proof. exact (fun_ext (fun x' : A => @lem5048929 A B s t f x' x)). Qed.
Lemma lem5048931 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5048932 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term193 A B s t f x) = (term193 A B s t f x).
Proof. exact (MK_COMB (@lem5048931 A) (@lem5048930 A B s t f x)). Qed.
Lemma lem5048953 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x' : A) (x : A) : (term179 A B s t f x' x) = (term179 A B s t f x' x).
Proof. exact (eq_refl (term179 A B s t f x' x)). Qed.
Lemma lem5048954 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term176 A B s t f x) = (term176 A B s t f x).
Proof. exact (fun_ext (fun x' : A => @lem5048953 A B s t f x' x)). Qed.
Lemma lem5048955 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5048956 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term188 A B s t f x) = (term188 A B s t f x).
Proof. exact (MK_COMB (@lem5048955 A) (@lem5048954 A B s t f x)). Qed.
Lemma lem5048957 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5048958 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term190 A B s t f x) = (term190 A B s t f x).
Proof. exact (MK_COMB (@lem5048957) (@lem5048956 A B s t f x)). Qed.
Lemma lem5048959 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term194 A B s t f x) = (term194 A B s t f x).
Proof. exact (MK_COMB (@lem5048958 A B s t f x) (@lem5048932 A B s t f x)). Qed.
Lemma lem5048970 {B : Type'} (t : B -> Prop) (u : B -> Prop) (x : B) : (term150 B t u x) = (term150 B t u x).
Proof. exact (eq_refl (term150 B t u x)). Qed.
Lemma lem5048971 {B : Type'} (t : B -> Prop) (u : B -> Prop) : (term151 B t u) = (term151 B t u).
Proof. exact (fun_ext (fun x : B => @lem5048970 B t u x)). Qed.
Lemma lem5048972 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5048973 {B : Type'} (t : B -> Prop) (u : B -> Prop) : (term152 B t u) = (term152 B t u).
Proof. exact (MK_COMB (@lem5048972 B) (@lem5048971 B t u)). Qed.
Lemma lem5048974 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5048975 {B : Type'} (t : B -> Prop) (u : B -> Prop) : (term164 B t u) = (term164 B t u).
Proof. exact (MK_COMB (@lem5048974) (@lem5048973 B t u)). Qed.
Lemma lem5048976 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term195 A B u s t f x) = (term195 A B u s t f x).
Proof. exact (MK_COMB (@lem5048975 B t u) (@lem5048959 A B s t f x)). Qed.
Lemma lem5048991 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term210 A x s x') = (term210 A x s x').
Proof. exact (eq_refl (term210 A x s x')). Qed.
Lemma lem5048992 {A B : Type'} (x' : A) (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term228 A B x' u s t f x) = (term228 A B x' u s t f x).
Proof. exact (MK_COMB (@lem5048991 A x s x') (@lem5048976 A B u s t f x)). Qed.
Lemma lem5048993 {A B : Type'} (x' : A) (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term228 A B x' u s t f x) : term228 A B x' u s t f x.
Proof. exact (EQ_MP (@lem5048992 A B x' u s t f x) (@lem5048894 A B x' u s t f x h1)). Qed.
Lemma lem5048994 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term140 A x s x') : term140 A x s x'.
Proof. exact (h1). Qed.
Lemma lem5048995 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term195 A B u s t f x) : term195 A B u s t f x.
Proof. exact (h1). Qed.
Lemma lem5048998 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term195 A B u s t f x) : term194 A B s t f x.
Proof. exact (proj2 (@lem5048995 A B u s t f x h1)). Qed.
Lemma lem5048999 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term195 A B u s t f x) : term152 B t u.
Proof. exact (proj1 (@lem5048995 A B u s t f x h1)). Qed.
Lemma lem5049001 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term195 A B u s t f x) : term188 A B s t f x.
Proof. exact (proj1 (@lem5048998 A B u s t f x h1)). Qed.
Lemma lem5049005 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem5049025 {A B : Type'} (u : B -> Prop) (f : A -> B) (x : A) (h1 : term138 A B u f x) : term138 A B u f x.
Proof. exact (h1). Qed.
Lemma lem5049033 {B : Type'} (t : B -> Prop) (u : B -> Prop) (x : B) : (term150 B t u x) = (term150 B t u x).
Proof. exact (eq_refl (term150 B t u x)). Qed.
Lemma lem5049034 {B : Type'} (t : B -> Prop) (u : B -> Prop) : (term151 B t u) = (term151 B t u).
Proof. exact (fun_ext (fun x : B => @lem5049033 B t u x)). Qed.
Lemma lem5049035 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5049037 {B : Type'} (t : B -> Prop) (u : B -> Prop) : (term152 B t u) = (term152 B t u).
Proof. exact (MK_COMB (@lem5049035 B) (@lem5049034 B t u)). Qed.
Lemma lem5049038 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term195 A B u s t f x) : term152 B t u.
Proof. exact (EQ_MP (@lem5049037 B t u) (@lem5048999 A B u s t f x h1)). Qed.
Lemma lem5049056 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x' : A) (x : A) : (term179 A B s t f x' x) = (term234 A B s t f x' x).
Proof. exact (@lem19699 (s x') (term100 A B t f x') (term235 A x' x)). Qed.
Lemma lem5049057 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term176 A B s t f x) = (term236 A B s t f x).
Proof. exact (fun_ext (fun x' : A => @lem5049056 A B s t f x' x)). Qed.
Lemma lem5049058 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5049060 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term188 A B s t f x) = (term237 A B s t f x).
Proof. exact (MK_COMB (@lem5049058 A) (@lem5049057 A B s t f x)). Qed.
Lemma lem5049061 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term195 A B u s t f x) : term237 A B s t f x.
Proof. exact (EQ_MP (@lem5049060 A B s t f x) (@lem5049001 A B u s t f x h1)). Qed.
Lemma lem5049081 {A B : Type'} (_64887 : B) (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term195 A B u s t f x) : term238 B t u _64887.
Proof. exact (@lem5049038 A B u s t f x h1 _64887). Qed.
Lemma lem5049082 {B : Type'} (t : B -> Prop) (u : B -> Prop) (_64887 : B) : (term238 B t u _64887) = (term150 B t u _64887).
Proof. exact (eq_refl (term238 B t u _64887)). Qed.
Lemma lem5049084 {A B : Type'} (_64888 : A) (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term195 A B u s t f x) : term239 A B s t f x _64888.
Proof. exact (@lem5049061 A B u s t f x h1 _64888). Qed.
Lemma lem5049085 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (_64888 : A) (x : A) : (term239 A B s t f x _64888) = (term234 A B s t f _64888 x).
Proof. exact (eq_refl (term239 A B s t f x _64888)). Qed.
Lemma lem5049086 {A B : Type'} (_64888 : A) (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term195 A B u s t f x) : term234 A B s t f _64888 x.
Proof. exact (EQ_MP (@lem5049085 A B s t f _64888 x) (@lem5049084 A B _64888 u s t f x h1)). Qed.
Lemma lem5049093 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem5049097 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term140 A x s x') : x' = x.
Proof. exact (proj1 (@lem5048994 A x s x' h1)). Qed.
Lemma lem5049099 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term140 A x s x') : term240 A s x'.
Proof. exact (proj2 (@lem5048994 A x s x' h1)). Qed.
Lemma lem5049103 {A B : Type'} (u : B -> Prop) (f : A -> B) (x : A) (h1 : term138 A B u f x) : term138 A B u f x.
Proof. exact (h1). Qed.
Lemma lem5049109 {A B : Type'} (_64887 : B) (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term195 A B u s t f x) : term150 B t u _64887.
Proof. exact (EQ_MP (@lem5049082 B t u _64887) (@lem5049081 A B _64887 u s t f x h1)). Qed.
Lemma lem5049133 {A B : Type'} (_64888 : A) (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term195 A B u s t f x) : term241 A B t f _64888 x.
Proof. exact (proj2 (@lem5049086 A B _64888 u s t f x h1)). Qed.
Lemma lem5049161 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem5049176 {A : Type'} (s : A -> Prop) : (term242 A s) = (term242 A s).
Proof. exact (eq_refl (term242 A s)). Qed.
Lemma lem5049177 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term140 A x s x') : (term243 A s x') = (term243 A s x).
Proof. exact (MK_COMB (@lem5049176 A s) (@lem5049097 A x s x' h1)). Qed.
Lemma lem5049178 {A : Type'} (s : A -> Prop) (x : A) : (term243 A s x) = (term240 A s x).
Proof. exact (eq_refl (term243 A s x)). Qed.
Lemma lem5049179 {A : Type'} (s : A -> Prop) (x' : A) : (term244 A s x') = (term244 A s x').
Proof. exact (eq_refl (term244 A s x')). Qed.
Lemma lem5049180 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : ((term243 A s x') = (term243 A s x)) = ((term243 A s x') = (term240 A s x)).
Proof. exact (MK_COMB (@lem5049179 A s x') (@lem5049178 A s x)). Qed.
Lemma lem5049181 {A : Type'} (s : A -> Prop) (x' : A) : (term243 A s x') = (term240 A s x').
Proof. exact (eq_refl (term243 A s x')). Qed.
Lemma lem5049182 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5049183 {A : Type'} (s : A -> Prop) (x' : A) : (term244 A s x') = (term245 A s x').
Proof. exact (MK_COMB (@lem5049182) (@lem5049181 A s x')). Qed.
Lemma lem5049184 {A : Type'} (s : A -> Prop) (x : A) : (term240 A s x) = (term240 A s x).
Proof. exact (eq_refl (term240 A s x)). Qed.
Lemma lem5049185 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : ((term243 A s x') = (term240 A s x)) = ((term240 A s x') = (term240 A s x)).
Proof. exact (MK_COMB (@lem5049183 A s x') (@lem5049184 A s x)). Qed.
Lemma lem5049186 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : ((term243 A s x') = (term243 A s x)) = ((term240 A s x') = (term240 A s x)).
Proof. exact (TRANS (@lem5049180 A x' s x) (@lem5049185 A x' s x)). Qed.
Lemma lem5049187 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term140 A x s x') : (term240 A s x') = (term240 A s x).
Proof. exact (EQ_MP (@lem5049186 A x' s x) (@lem5049177 A x s x' h1)). Qed.
Lemma lem5049188 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term140 A x s x') : term240 A s x.
Proof. exact (EQ_MP (@lem5049187 A x s x' h1) (@lem5049099 A x s x' h1)). Qed.
Lemma lem5049190 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem5049191 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : term246 A s x.
Proof. exact (fun h0 : term240 A s x => @lem5049190 A s x h1). Qed.
Lemma lem5049193 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5049194 {A : Type'} (s : A -> Prop) (x : A) : (term246 A s x) = (s x).
Proof. exact (@lem5049193 (s x)). Qed.
Lemma lem5049195 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (EQ_MP (@lem5049194 A s x) (@lem5049191 A s x h1)). Qed.
Lemma lem5049198 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5049200 {A : Type'} (s : A -> Prop) (x : A) : (term240 A s x) = (term248 A s x).
Proof. exact (@lem5049198 (s x)). Qed.
Lemma lem5049203 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term140 A x s x') : term248 A s x.
Proof. exact (EQ_MP (@lem5049200 A s x) (@lem5049188 A x s x' h1)). Qed.
Lemma lem5049206 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x) (h2 : term140 A x s x') : False.
Proof. exact (@lem5049203 A x s x' h2 (@lem5049195 A s x h1)). Qed.
Lemma lem5049207 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x) (h2 : term140 A x s x') : term249.
Proof. exact (fun h0 : ~ False => @lem5049206 A x s x' h1 h2). Qed.
Lemma lem5049209 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5049210 : term249 = False.
Proof. exact (@lem5049209 False). Qed.
Lemma lem5049211 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x) (h2 : term140 A x s x') : False.
Proof. exact (EQ_MP (@lem5049210) (@lem5049207 A x s x' h1 h2)). Qed.
Lemma lem5049261 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem5049262 {A : Type'} (x : A) : x = x.
Proof. exact (@lem5049261 A x). Qed.
Lemma lem5049263 {A : Type'} (x : A) : term250 A x.
Proof. exact (fun h0 : term251 A x => @lem5049262 A x). Qed.
Lemma lem5049265 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5049266 {A : Type'} (x : A) : (term250 A x) = (x = x).
Proof. exact (@lem5049265 (x = x)). Qed.
Lemma lem5049267 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem5049266 A x) (@lem5049263 A x)). Qed.
Lemma lem5049269 (b : Prop) (a : Prop) : (a \/ b) = (term252 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5049270 {A B : Type'} (x : A) (t : B -> Prop) (f : A -> B) (_64888 : A) : (term241 A B t f _64888 x) = (term253 A B x t f _64888).
Proof. exact (@lem5049269 (term235 A _64888 x) (term100 A B t f _64888)). Qed.
Lemma lem5049272 (a : Prop) : (term120 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5049273 {A : Type'} (_64888 : A) (x : A) : (term254 A _64888 x) = (_64888 = x).
Proof. exact (@lem5049272 (_64888 = x)). Qed.
Lemma lem5049274 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5049275 {A : Type'} (_64888 : A) (x : A) : (term255 A _64888 x) = (term66 A _64888 x).
Proof. exact (MK_COMB (@lem5049274) (@lem5049273 A _64888 x)). Qed.
Lemma lem5049276 {A B : Type'} (t : B -> Prop) (f : A -> B) (_64888 : A) : (term100 A B t f _64888) = (term100 A B t f _64888).
Proof. exact (eq_refl (term100 A B t f _64888)). Qed.
Lemma lem5049277 {A B : Type'} (x : A) (t : B -> Prop) (f : A -> B) (_64888 : A) : (term253 A B x t f _64888) = (term256 A B x t f _64888).
Proof. exact (MK_COMB (@lem5049275 A _64888 x) (@lem5049276 A B t f _64888)). Qed.
Lemma lem5049278 {A B : Type'} (x : A) (t : B -> Prop) (f : A -> B) (_64888 : A) : (term241 A B t f _64888 x) = (term256 A B x t f _64888).
Proof. exact (TRANS (@lem5049270 A B x t f _64888) (@lem5049277 A B x t f _64888)). Qed.
Lemma lem5049281 {A B : Type'} (_64888 : A) (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term195 A B u s t f x) : term256 A B x t f _64888.
Proof. exact (EQ_MP (@lem5049278 A B x t f _64888) (@lem5049133 A B _64888 u s t f x h1)). Qed.
Lemma lem5049282 {A B : Type'} (_64888 : A) (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term195 A B u s t f x) : term256 A B x t f _64888.
Proof. exact (@lem5049281 A B _64888 u s t f x h1). Qed.
Lemma lem5049283 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term195 A B u s t f x) : term257 A B t f x.
Proof. exact (@lem5049282 A B x u s t f x h1). Qed.
Lemma lem5049286 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term195 A B u s t f x) : term100 A B t f x.
Proof. exact (@lem5049283 A B u s t f x h1 (@lem5049267 A x)). Qed.
Lemma lem5049287 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term195 A B u s t f x) : term258 A B t f x.
Proof. exact (fun h0 : term138 A B t f x => @lem5049286 A B u s t f x h1). Qed.
Lemma lem5049289 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5049290 {A B : Type'} (t : B -> Prop) (f : A -> B) (x : A) : (term258 A B t f x) = (term100 A B t f x).
Proof. exact (@lem5049289 (term100 A B t f x)). Qed.
Lemma lem5049291 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term195 A B u s t f x) : term100 A B t f x.
Proof. exact (EQ_MP (@lem5049290 A B t f x) (@lem5049287 A B u s t f x h1)). Qed.
Lemma lem5049297 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5049298 {B : Type'} (u : B -> Prop) (t : B -> Prop) (_64887 : B) : (term150 B t u _64887) = (term259 B u t _64887).
Proof. exact (@lem5049297 (u _64887) (term240 B t _64887)). Qed.
Lemma lem5049304 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5049305 {B : Type'} (u : B -> Prop) (t : B -> Prop) (_64887 : B) : (term260 B t u _64887) = (term261 B u t _64887).
Proof. exact (MK_COMB (@lem5049304) (@lem5049298 B u t _64887)). Qed.
Lemma lem5049311 {B : Type'} (u : B -> Prop) (t : B -> Prop) (_64887 : B) : (term259 B u t _64887) = (term259 B u t _64887).
Proof. exact (eq_refl (term259 B u t _64887)). Qed.
Lemma lem5049312 {B : Type'} (u : B -> Prop) (t : B -> Prop) (_64887 : B) : ((term150 B t u _64887) = (term259 B u t _64887)) = ((term259 B u t _64887) = (term259 B u t _64887)).
Proof. exact (MK_COMB (@lem5049305 B u t _64887) (@lem5049311 B u t _64887)). Qed.
Lemma lem5049314 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5049315 (x : Prop) : (x = x) = True.
Proof. exact (@lem5049314 Prop x). Qed.
Lemma lem5049316 {B : Type'} (u : B -> Prop) (t : B -> Prop) (_64887 : B) : ((term259 B u t _64887) = (term259 B u t _64887)) = True.
Proof. exact (@lem5049315 (term259 B u t _64887)). Qed.
Lemma lem5049317 {B : Type'} (u : B -> Prop) (t : B -> Prop) (_64887 : B) : ((term150 B t u _64887) = (term259 B u t _64887)) = True.
Proof. exact (TRANS (@lem5049312 B u t _64887) (@lem5049316 B u t _64887)). Qed.
Lemma lem5049318 {B : Type'} (u : B -> Prop) (t : B -> Prop) (_64887 : B) : True = ((term150 B t u _64887) = (term259 B u t _64887)).
Proof. exact (SYM (@lem5049317 B u t _64887)). Qed.
Lemma lem5049319 {B : Type'} (u : B -> Prop) (t : B -> Prop) (_64887 : B) : (term150 B t u _64887) = (term259 B u t _64887).
Proof. exact (EQ_MP (@lem5049318 B u t _64887) (@lem0)). Qed.
Lemma lem5049320 {A B : Type'} (_64887 : B) (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term195 A B u s t f x) : term259 B u t _64887.
Proof. exact (EQ_MP (@lem5049319 B u t _64887) (@lem5049109 A B _64887 u s t f x h1)). Qed.
Lemma lem5049322 (b : Prop) (a : Prop) : (a \/ b) = (term252 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5049323 {B : Type'} (t : B -> Prop) (u : B -> Prop) (_64887 : B) : (term259 B u t _64887) = (term262 B t u _64887).
Proof. exact (@lem5049322 (term240 B t _64887) (u _64887)). Qed.
Lemma lem5049325 (a : Prop) : (term120 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5049326 {B : Type'} (t : B -> Prop) (_64887 : B) : (term263 B t _64887) = (t _64887).
Proof. exact (@lem5049325 (t _64887)). Qed.
Lemma lem5049327 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5049328 {B : Type'} (t : B -> Prop) (_64887 : B) : (term264 B t _64887) = (term58 B t _64887).
Proof. exact (MK_COMB (@lem5049327) (@lem5049326 B t _64887)). Qed.
Lemma lem5049329 {B : Type'} (u : B -> Prop) (_64887 : B) : (u _64887) = (u _64887).
Proof. exact (eq_refl (u _64887)). Qed.
Lemma lem5049330 {B : Type'} (t : B -> Prop) (u : B -> Prop) (_64887 : B) : (term262 B t u _64887) = (term74 B t u _64887).
Proof. exact (MK_COMB (@lem5049328 B t _64887) (@lem5049329 B u _64887)). Qed.
Lemma lem5049331 {B : Type'} (t : B -> Prop) (u : B -> Prop) (_64887 : B) : (term259 B u t _64887) = (term74 B t u _64887).
Proof. exact (TRANS (@lem5049323 B t u _64887) (@lem5049330 B t u _64887)). Qed.
Lemma lem5049334 {A B : Type'} (_64887 : B) (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term195 A B u s t f x) : term74 B t u _64887.
Proof. exact (EQ_MP (@lem5049331 B t u _64887) (@lem5049320 A B _64887 u s t f x h1)). Qed.
Lemma lem5049335 {A B : Type'} (_64887 : B) (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term195 A B u s t f x) : term74 B t u _64887.
Proof. exact (@lem5049334 A B _64887 u s t f x h1). Qed.
Lemma lem5049336 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term195 A B u s t f x) : term265 A B t u f x.
Proof. exact (@lem5049335 A B (f x) u s t f x h1). Qed.
Lemma lem5049339 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term195 A B u s t f x) : term100 A B u f x.
Proof. exact (@lem5049336 A B u s t f x h1 (@lem5049291 A B u s t f x h1)). Qed.
Lemma lem5049340 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term195 A B u s t f x) : term258 A B u f x.
Proof. exact (fun h0 : term138 A B u f x => @lem5049339 A B u s t f x h1). Qed.
Lemma lem5049342 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5049343 {A B : Type'} (u : B -> Prop) (f : A -> B) (x : A) : (term258 A B u f x) = (term100 A B u f x).
Proof. exact (@lem5049342 (term100 A B u f x)). Qed.
Lemma lem5049344 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term195 A B u s t f x) : term100 A B u f x.
Proof. exact (EQ_MP (@lem5049343 A B u f x) (@lem5049340 A B u s t f x h1)). Qed.
Lemma lem5049347 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5049349 {A B : Type'} (u : B -> Prop) (f : A -> B) (x : A) : (term138 A B u f x) = (term266 A B u f x).
Proof. exact (@lem5049347 (term100 A B u f x)). Qed.
Lemma lem5049352 {A B : Type'} (u : B -> Prop) (f : A -> B) (x : A) (h1 : term138 A B u f x) : term266 A B u f x.
Proof. exact (EQ_MP (@lem5049349 A B u f x) (@lem5049103 A B u f x h1)). Qed.
Lemma lem5049355 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term138 A B u f x) (h2 : term195 A B u s t f x) : False.
Proof. exact (@lem5049352 A B u f x h1 (@lem5049344 A B u s t f x h2)). Qed.
Lemma lem5049356 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term138 A B u f x) (h2 : term195 A B u s t f x) : term249.
Proof. exact (fun h0 : ~ False => @lem5049355 A B u s t f x h1 h2). Qed.
Lemma lem5049358 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5049359 : term249 = False.
Proof. exact (@lem5049358 False). Qed.
Lemma lem5049360 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term138 A B u f x) (h2 : term195 A B u s t f x) : False.
Proof. exact (EQ_MP (@lem5049359) (@lem5049356 A B u s t f x h1 h2)). Qed.
Lemma lem5049361 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x) (h2 : term140 A x s x') : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem5049211 A x s x' h1 h2) (fun h3 : False => @lem5049161 A s x h1)). Qed.
Lemma lem5049363 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x) (h2 : term140 A x s x') : False.
Proof. exact (EQ_MP (@lem5049361 A x s x' h1 h2) (@lem5049161 A s x h1)). Qed.
Lemma lem5049364 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term138 A B u f x) (h2 : term195 A B u s t f x) : (term138 A B u f x) = False.
Proof. exact (prop_ext (fun h3 : term138 A B u f x => @lem5049360 A B u s t f x h1 h2) (fun h3 : False => @lem5049103 A B u f x h1)). Qed.
Lemma lem5049365 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term138 A B u f x) (h2 : term195 A B u s t f x) : False.
Proof. exact (EQ_MP (@lem5049364 A B u s t f x h1 h2) (@lem5049103 A B u f x h1)). Qed.
Lemma lem5049366 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x) (h2 : term140 A x s x') : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem5049363 A x s x' h1 h2) (fun h3 : False => @lem5049093 A s x h1)). Qed.
Lemma lem5049367 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x) (h2 : term140 A x s x') : False.
Proof. exact (EQ_MP (@lem5049366 A x s x' h1 h2) (@lem5049093 A s x h1)). Qed.
Lemma lem5049368 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term138 A B u f x) (h2 : term195 A B u s t f x) : (term138 A B u f x) = False.
Proof. exact (prop_ext (fun h3 : term138 A B u f x => @lem5049365 A B u s t f x h1 h2) (fun h3 : False => @lem5049025 A B u f x h1)). Qed.
Lemma lem5049369 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term138 A B u f x) (h2 : term195 A B u s t f x) : False.
Proof. exact (EQ_MP (@lem5049368 A B u s t f x h1 h2) (@lem5049025 A B u f x h1)). Qed.
Lemma lem5049370 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x) (h2 : term140 A x s x') : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem5049367 A x s x' h1 h2) (fun h3 : False => @lem5049005 A s x h1)). Qed.
Lemma lem5049371 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x) (h2 : term140 A x s x') : False.
Proof. exact (EQ_MP (@lem5049370 A x s x' h1 h2) (@lem5049005 A s x h1)). Qed.
Lemma lem5049372 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term138 A B u f x) (h2 : term195 A B u s t f x) : (term138 A B u f x) = False.
Proof. exact (prop_ext (fun h3 : term138 A B u f x => @lem5049369 A B u s t f x h1 h2) (fun h3 : False => @lem5049025 A B u f x h1)). Qed.
Lemma lem5049373 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term138 A B u f x) (h2 : term195 A B u s t f x) : False.
Proof. exact (EQ_MP (@lem5049372 A B u s t f x h1 h2) (@lem5049025 A B u f x h1)). Qed.
Lemma lem5049374 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x) (h2 : term140 A x s x') : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem5049371 A x s x' h1 h2) (fun h3 : False => @lem5049005 A s x h1)). Qed.
Lemma lem5049375 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x) (h2 : term140 A x s x') : False.
Proof. exact (EQ_MP (@lem5049374 A x s x' h1 h2) (@lem5049005 A s x h1)). Qed.
Lemma lem5049376 {A B : Type'} (x' : A) (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term138 A B u f x) (h2 : s x) (h3 : term228 A B x' u s t f x) : False.
Proof. exact (or_elim (@lem5048993 A B x' u s t f x h3) (fun h0 : term140 A x s x' => @lem5049375 A x s x' h2 h0) (fun h0 : term195 A B u s t f x => @lem5049373 A B u s t f x h1 h0)). Qed.
Lemma lem5049377 {A B : Type'} (x' : A) (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term138 A B u f x) (h2 : s x) (h3 : term228 A B x' u s t f x) : (term228 A B x' u s t f x) = False.
Proof. exact (prop_ext (fun h4 : term228 A B x' u s t f x => @lem5049376 A B x' u s t f x h1 h2 h3) (fun h4 : False => @lem5048993 A B x' u s t f x h3)). Qed.
Lemma lem5049378 {A B : Type'} (x' : A) (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term138 A B u f x) (h2 : s x) (h3 : term228 A B x' u s t f x) : False.
Proof. exact (EQ_MP (@lem5049377 A B x' u s t f x h1 h2 h3) (@lem5048993 A B x' u s t f x h3)). Qed.
Lemma lem5049379 {A B : Type'} (x' : A) (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term138 A B u f x) (h2 : s x) (h3 : term228 A B x' u s t f x) : (term138 A B u f x) = False.
Proof. exact (prop_ext (fun h4 : term138 A B u f x => @lem5049378 A B x' u s t f x h1 h2 h3) (fun h4 : False => @lem5048906 A B u f x h1)). Qed.
Lemma lem5049380 {A B : Type'} (x' : A) (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term138 A B u f x) (h2 : s x) (h3 : term228 A B x' u s t f x) : False.
Proof. exact (EQ_MP (@lem5049379 A B x' u s t f x h1 h2 h3) (@lem5048906 A B u f x h1)). Qed.
Lemma lem5049381 {A B : Type'} (x' : A) (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term138 A B u f x) (h2 : s x) (h3 : term228 A B x' u s t f x) : (s x) = False.
Proof. exact (prop_ext (fun h4 : s x => @lem5049380 A B x' u s t f x h1 h2 h3) (fun h4 : False => @lem5048898 A s x h2)). Qed.
Lemma lem5049382 {A B : Type'} (x' : A) (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term138 A B u f x) (h2 : s x) (h3 : term228 A B x' u s t f x) : False.
Proof. exact (EQ_MP (@lem5049381 A B x' u s t f x h1 h2 h3) (@lem5048898 A s x h2)). Qed.
Lemma lem5049383 {A B : Type'} (x' : A) (u : B -> Prop) (f : A -> B) (s : A -> Prop) (x : A) (h1 : term231 A B x' u s f x) (h2 : term138 A B u f x) (h3 : s x) : False.
Proof. exact (ex_elim (@lem5048893 A B x' u s f x h1) (fun t : B -> Prop => fun h0 : term230 A B x' u s f x t => @lem5049382 A B x' u s t f x h2 h3 h0)). Qed.
Lemma lem5049384 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term138 A B u f x) (h2 : s x) (h3 : term109 A B u s f x) : False.
Proof. exact (ex_elim (@lem5048886 A B u s f x h3) (fun x' : A => fun h0 : term232 A B u s f x x' => @lem5049383 A B x' u f s x h0 h1 h2)). Qed.
Lemma lem5049385 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term138 A B u f x) (h2 : s x) (h3 : term109 A B u s f x) : (term138 A B u f x) = False.
Proof. exact (prop_ext (fun h4 : term138 A B u f x => @lem5049384 A B u s f x h1 h2 h3) (fun h4 : False => @lem5048892 A B u f x h1)). Qed.
Lemma lem5049386 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term138 A B u f x) (h2 : s x) (h3 : term109 A B u s f x) : False.
Proof. exact (EQ_MP (@lem5049385 A B u s f x h1 h2 h3) (@lem5048892 A B u f x h1)). Qed.
Lemma lem5049387 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term138 A B u f x) (h2 : s x) (h3 : term109 A B u s f x) : (s x) = False.
Proof. exact (prop_ext (fun h4 : s x => @lem5049386 A B u s f x h1 h2 h3) (fun h4 : False => @lem5048461 A s x h2)). Qed.
Lemma lem5049388 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term138 A B u f x) (h2 : s x) (h3 : term109 A B u s f x) : False.
Proof. exact (EQ_MP (@lem5049387 A B u s f x h1 h2 h3) (@lem5048461 A s x h2)). Qed.
Lemma lem5049389 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term138 A B u f x) (h2 : s x) (h3 : term109 A B u s f x) : (term138 A B u f x) = False.
Proof. exact (prop_ext (fun h4 : term138 A B u f x => @lem5049388 A B u s f x h1 h2 h3) (fun h4 : False => @lem5048455 A B u f x h1)). Qed.
Lemma lem5049390 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term138 A B u f x) (h2 : s x) (h3 : term109 A B u s f x) : False.
Proof. exact (EQ_MP (@lem5049389 A B u s f x h1 h2 h3) (@lem5048455 A B u f x h1)). Qed.
Lemma lem5049391 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (h1 : s x) (h2 : term109 A B u s f x) : term137 A B u f x.
Proof. exact (fun h0 : term138 A B u f x => @lem5049390 A B u s f x h0 h1 h2). Qed.
Lemma lem5049392 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (h1 : s x) (h2 : term109 A B u s f x) : term100 A B u f x.
Proof. exact (EQ_MP (@lem5048454 A B u f x) (@lem5049391 A B u s f x h1 h2)). Qed.
Lemma lem5049393 {A B : Type'} (u : B -> Prop) (f : A -> B) (s : A -> Prop) (x : A) (h1 : s x) : term111 A B s u f x.
Proof. exact (fun h0 : term109 A B u s f x => @lem5049392 A B u s f x h1 h0). Qed.
Lemma lem5049394 {A B : Type'} (s : A -> Prop) (u : B -> Prop) (f : A -> B) (x : A) : term112 A B s u f x.
Proof. exact (fun h0 : s x => @lem5049393 A B u f s x h0). Qed.
Lemma lem5049399 {A B : Type'} (u : B -> Prop) (f : A -> B) (x : A) : term124 A B u f x.
Proof. exact (fun s : A -> Prop => @lem5049394 A B s u f x). Qed.
Lemma lem5049404 {A B : Type'} (f : A -> B) (x : A) : term128 A B f x.
Proof. exact (fun u : B -> Prop => @lem5049399 A B u f x). Qed.
Lemma lem5049409 {A B : Type'} (x : A) : term132 A B x.
Proof. exact (fun f : A -> B => @lem5049404 A B f x). Qed.
Lemma lem5049414 {A B : Type'} : term136 A B.
Proof. exact (fun x : A => @lem5049409 A B x). Qed.
Lemma lem5049415 {A B : Type'} : term135 A B.
Proof. exact (EQ_MP (@lem5048448 A B) (@lem5049414 A B)). Qed.
Lemma lem5049416 {A B : Type'} (x : A) : term267 A B x.
Proof. exact (@lem5049415 A B x). Qed.
Lemma lem5049417 {A B : Type'} (x : A) : (term267 A B x) = (term131 A B x).
Proof. exact (eq_refl (term267 A B x)). Qed.
Lemma lem5049418 {A B : Type'} (x : A) : term131 A B x.
Proof. exact (EQ_MP (@lem5049417 A B x) (@lem5049416 A B x)). Qed.
Lemma lem5049419 {A B : Type'} (x : A) (f : A -> B) : term268 A B x f.
Proof. exact (@lem5049418 A B x f). Qed.
Lemma lem5049420 {A B : Type'} (f : A -> B) (x : A) : (term268 A B x f) = (term127 A B f x).
Proof. exact (eq_refl (term268 A B x f)). Qed.
Lemma lem5049421 {A B : Type'} (f : A -> B) (x : A) : term127 A B f x.
Proof. exact (EQ_MP (@lem5049420 A B f x) (@lem5049419 A B x f)). Qed.
Lemma lem5049422 {A B : Type'} (f : A -> B) (x : A) (u : B -> Prop) : term269 A B f x u.
Proof. exact (@lem5049421 A B f x u). Qed.
Lemma lem5049423 {A B : Type'} (u : B -> Prop) (f : A -> B) (x : A) : (term269 A B f x u) = (term123 A B u f x).
Proof. exact (eq_refl (term269 A B f x u)). Qed.
Lemma lem5049424 {A B : Type'} (u : B -> Prop) (f : A -> B) (x : A) : term123 A B u f x.
Proof. exact (EQ_MP (@lem5049423 A B u f x) (@lem5049422 A B f x u)). Qed.
Lemma lem5049425 {A B : Type'} (u : B -> Prop) (f : A -> B) (x : A) (s : A -> Prop) : term270 A B u f x s.
Proof. exact (@lem5049424 A B u f x s). Qed.
Lemma lem5049426 {A B : Type'} (s : A -> Prop) (u : B -> Prop) (f : A -> B) (x : A) : (term270 A B u f x s) = (term114 A B s u f x).
Proof. exact (eq_refl (term270 A B u f x s)). Qed.
Lemma lem5049427 {A B : Type'} (s : A -> Prop) (u : B -> Prop) (f : A -> B) (x : A) : term114 A B s u f x.
Proof. exact (EQ_MP (@lem5049426 A B s u f x) (@lem5049425 A B u f x s)). Qed.
Lemma lem5049429 {A B : Type'} (s : A -> Prop) (u : B -> Prop) (f : A -> B) (x : A) : term114 A B s u f x.
Proof. exact (@lem5048196 A B s u f x (@lem5049427 A B s u f x)). Qed.
Lemma lem5049430 {A B : Type'} (s : A -> Prop) (u : B -> Prop) (f : A -> B) (x : A) (h1 : term115 A B s u f x) : False.
Proof. exact (@lem5049429 A B s u f x (@lem5048180 A B s u f x h1)). Qed.
Lemma lem5049431 {A B : Type'} (s : A -> Prop) (u : B -> Prop) (f : A -> B) (x : A) (h1 : term115 A B s u f x) : (term115 A B s u f x) = False.
Proof. exact (prop_ext (fun h2 : term115 A B s u f x => @lem5049430 A B s u f x h1) (fun h2 : False => @lem5048180 A B s u f x h1)). Qed.
Lemma lem5049432 {A B : Type'} (s : A -> Prop) (u : B -> Prop) (f : A -> B) (x : A) (h1 : term115 A B s u f x) : False.
Proof. exact (EQ_MP (@lem5049431 A B s u f x h1) (@lem5048180 A B s u f x h1)). Qed.
Lemma lem5049433 {A B : Type'} (s : A -> Prop) (u : B -> Prop) (f : A -> B) (x : A) : term114 A B s u f x.
Proof. exact (fun h0 : term115 A B s u f x => @lem5049432 A B s u f x h0). Qed.
Lemma lem5049434 {A B : Type'} (s : A -> Prop) (u : B -> Prop) (f : A -> B) (x : A) : term112 A B s u f x.
Proof. exact (EQ_MP (@lem5048179 A B s u f x) (@lem5049433 A B s u f x)). Qed.
Lemma lem5049435 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (u : B -> Prop) : term57 A B s f x u.
Proof. exact (EQ_MP (@lem5048175 A B s f x u) (@lem5049434 A B s u f x)). Qed.
Lemma lem5049436 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (u : B -> Prop) : term56 A B s f x u.
Proof. exact (EQ_MP (@lem5047979 A B s f x u) (@lem5049435 A B s f x u)). Qed.
Lemma lem5049437 {A B : Type'} (f : A -> B) (u : B -> Prop) (x : A) (s : A -> Prop) (h1 : @IN A x s) : term54 A B s f x u.
Proof. exact (@lem5049436 A B s f x u (@lem5047886 A x s h1)). Qed.
Lemma lem5049438 {A B : Type'} (u : B -> Prop) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term9 A B u s f) (h2 : @IN A x s) : term27 A B f x u.
Proof. exact (@lem5049437 A B f u x s h2 (@lem5047889 A B x u s f h1)). Qed.
Lemma lem5049439 {A B : Type'} (x : A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term9 A B u s f) : term30 A B s f x u.
Proof. exact (fun h0 : @IN A x s => @lem5049438 A B u f x s h1 h0). Qed.
Lemma lem5049444 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term9 A B u s f) : term33 A B s f u.
Proof. exact (fun x : A => @lem5049439 A B x u s f h1). Qed.
Lemma lem5049445 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term9 A B u s f) : term11 A B f s u.
Proof. exact (EQ_MP (@lem5047885 A B f s u) (@lem5049444 A B u s f h1)). Qed.
Lemma lem5049446 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) (h1 : term271 A B s x f y) : term271 A B s x f y.
Proof. exact (h1). Qed.
Lemma lem5049447 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) (h1 : term272 A B s x f y) : term272 A B s x f y.
Proof. exact (h1). Qed.
Lemma lem5049448 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem5049449 {A B : Type'} (x : A) (f : A -> B) (y : A) (h1 : (f x) = (f y)) : (f x) = (f y).
Proof. exact (h1). Qed.
Lemma lem5049450 {A : Type'} (y : A) (s : A -> Prop) (h1 : @IN A y s) : @IN A y s.
Proof. exact (h1). Qed.
Lemma lem5049451 {A B : Type'} (x : A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term9 A B u s f) : term34 A B u s f x.
Proof. exact (@lem5047852 A B u s f h1 (@INSERT A x (@EMPTY A))). Qed.
Lemma lem5049452 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term34 A B u s f x) = (term35 A B u s f x).
Proof. exact (eq_refl (term34 A B u s f x)). Qed.
Lemma lem5049453 {A B : Type'} (x : A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term9 A B u s f) : term35 A B u s f x.
Proof. exact (EQ_MP (@lem5049452 A B u s f x) (@lem5049451 A B x u s f h1)). Qed.
Lemma lem5049454 (t1 : Prop) : term273 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem5049455 (t1 : Prop) : (term273 t1) = (term274 t1).
Proof. exact (eq_refl (term273 t1)). Qed.
Lemma lem5049456 (t1 : Prop) : term274 t1.
Proof. exact (EQ_MP (@lem5049455 t1) (@lem5049454 t1)). Qed.
Lemma lem5049457 (t1 : Prop) (t2 : Prop) : term275 t1 t2.
Proof. exact (@lem5049456 t1 t2). Qed.
Lemma lem5049458 (t1 : Prop) (t2 : Prop) : (term275 t1 t2) = (term276 t1 t2).
Proof. exact (eq_refl (term275 t1 t2)). Qed.
Lemma lem5049459 (t1 : Prop) (t2 : Prop) : term276 t1 t2.
Proof. exact (EQ_MP (@lem5049458 t1 t2) (@lem5049457 t1 t2)). Qed.
Lemma lem5049460 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term277 t1 t2 t3.
Proof. exact (@lem5049459 t1 t2 t3). Qed.
Lemma lem5049461 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term277 t1 t2 t3) = ((term278 t1 t2 t3) = (term279 t1 t2 t3)).
Proof. exact (eq_refl (term277 t1 t2 t3)). Qed.
Lemma lem5049462 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term278 t1 t2 t3) = (term279 t1 t2 t3).
Proof. exact (EQ_MP (@lem5049461 t1 t2 t3) (@lem5049460 t1 t2 t3)). Qed.
Lemma lem5049463 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term279 t1 t2 t3) = (term278 t1 t2 t3).
Proof. exact (SYM (@lem5049462 t1 t2 t3)). Qed.
Lemma lem5049464 {A : Type'} (x : A) (y : A) (s : A -> Prop) (h1 : @IN A x s) (h2 : @IN A y s) : term280 A y x s.
Proof. exact (conj (@lem5049450 A y s h2) (@lem5049448 A x s h1)). Qed.
Lemma lem5049465 {A B : Type'} (f : A -> B) (x : A) (y : A) (s : A -> Prop) (h1 : (f x) = (f y)) (h2 : @IN A x s) (h3 : @IN A y s) : term281 A B f y x s.
Proof. exact (conj (@lem5049449 A B x f y h1) (@lem5049464 A x y s h2 h3)). Qed.
Lemma lem5049481 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term8 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem5049482 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term8 A s t).
Proof. exact (@lem5049481 A s t). Qed.
Lemma lem5049483 {A : Type'} (x : A) (s : A -> Prop) : (term36 A x s) = (term37 A x s).
Proof. exact (@lem5049482 A (@INSERT A x (@EMPTY A)) s). Qed.
Lemma lem5049490 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5049491 {A : Type'} (x : A) (s : A -> Prop) : (term38 A x s) = (term39 A x s).
Proof. exact (MK_COMB (@lem5049490) (@lem5049483 A x s)). Qed.
Lemma lem5049499 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term8 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem5049500 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (@SUBSET B s t) = (term8 B s t).
Proof. exact (@lem5049499 B s t). Qed.
Lemma lem5049501 {B : Type'} (t : B -> Prop) (u : B -> Prop) : (@SUBSET B t u) = (term8 B t u).
Proof. exact (@lem5049500 B t u). Qed.
Lemma lem5049508 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5049509 {B : Type'} (t : B -> Prop) (u : B -> Prop) : (term40 B t u) = (term41 B t u).
Proof. exact (MK_COMB (@lem5049508) (@lem5049501 B t u)). Qed.
Lemma lem5049513 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term42 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem5049514 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term42 A s t).
Proof. exact (@lem5049513 A s t). Qed.
Lemma lem5049515 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) (x : A) : ((term43 A B s f t) = (@INSERT A x (@EMPTY A))) = (term44 A B s f t x).
Proof. exact (@lem5049514 A (term43 A B s f t) (@INSERT A x (@EMPTY A))). Qed.
Lemma lem5049530 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (x : A) : (term45 A B u s f t x) = (term46 A B u s f t x).
Proof. exact (MK_COMB (@lem5049509 B t u) (@lem5049515 A B s f t x)). Qed.
Lemma lem5049533 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term47 A B u s f x) = (term48 A B u s f x).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5049530 A B u s f t x)). Qed.
Lemma lem5049534 {B : Type'} : (@ex (B -> Prop)) = (@ex (B -> Prop)).
Proof. exact (eq_refl (@ex (B -> Prop))). Qed.
Lemma lem5049535 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term49 A B u s f x) = (term50 A B u s f x).
Proof. exact (MK_COMB (@lem5049534 B) (@lem5049533 A B u s f x)). Qed.
Lemma lem5049540 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term35 A B u s f x) = (term51 A B u s f x).
Proof. exact (MK_COMB (@lem5049491 A x s) (@lem5049535 A B u s f x)). Qed.
Lemma lem5049543 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5049544 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term52 A B u s f x) = (term53 A B u s f x).
Proof. exact (MK_COMB (@lem5049543) (@lem5049540 A B u s f x)). Qed.
Lemma lem5049549 {A : Type'} (x : A) (y : A) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem5049550 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term282 A B u s f x y) = (term283 A B u s f x y).
Proof. exact (MK_COMB (@lem5049544 A B u s f x) (@lem5049549 A x y)). Qed.
Lemma lem5049553 {A B : Type'} (f : A -> B) (y : A) (x : A) (s : A -> Prop) : (term284 A B f y x s) = (term284 A B f y x s).
Proof. exact (eq_refl (term284 A B f y x s)). Qed.
Lemma lem5049554 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term285 A B u s f x y) = (term286 A B u s f x y).
Proof. exact (MK_COMB (@lem5049553 A B f y x s) (@lem5049550 A B u s f x y)). Qed.
Lemma lem5049557 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term286 A B u s f x y) = (term285 A B u s f x y).
Proof. exact (SYM (@lem5049554 A B u s f x y)). Qed.
Lemma lem5049567 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5049568 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5049567 A P x). Qed.
Lemma lem5049569 {A : Type'} (s : A -> Prop) (y : A) : (@IN A y s) = (s y).
Proof. exact (@lem5049568 A s y). Qed.
Lemma lem5049570 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5049571 {A : Type'} (s : A -> Prop) (y : A) : (term98 A y s) = (term99 A s y).
Proof. exact (MK_COMB (@lem5049570) (@lem5049569 A s y)). Qed.
Lemma lem5049573 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5049574 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5049573 A P x). Qed.
Lemma lem5049575 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem5049574 A s x). Qed.
Lemma lem5049576 {A : Type'} (y : A) (s : A -> Prop) (x : A) : (term280 A y x s) = (term287 A y s x).
Proof. exact (MK_COMB (@lem5049571 A s y) (@lem5049575 A s x)). Qed.
Lemma lem5049579 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term288 A B x f y) = (term288 A B x f y).
Proof. exact (eq_refl (term288 A B x f y)). Qed.
Lemma lem5049580 {A B : Type'} (f : A -> B) (y : A) (s : A -> Prop) (x : A) : (term281 A B f y x s) = (term289 A B f y s x).
Proof. exact (MK_COMB (@lem5049579 A B x f y) (@lem5049576 A y s x)). Qed.
Lemma lem5049583 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5049584 {A B : Type'} (f : A -> B) (y : A) (s : A -> Prop) (x : A) : (term284 A B f y x s) = (term290 A B f y s x).
Proof. exact (MK_COMB (@lem5049583) (@lem5049580 A B f y s x)). Qed.
Lemma lem5049596 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term59 A x y s) = (term60 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem5049597 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term59 A x y s) = (term60 A y x s).
Proof. exact (@lem5049596 A y x s). Qed.
Lemma lem5049598 {A : Type'} (x : A) (x' : A) : (term61 A x' x) = (term62 A x x').
Proof. exact (@lem5049597 A x x' (@EMPTY A)). Qed.
Lemma lem5049604 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem5049605 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem5049604 A x). Qed.
Lemma lem5049606 {A : Type'} (x' : A) : (@IN A x' (@EMPTY A)) = False.
Proof. exact (@lem5049605 A x'). Qed.
Lemma lem5049607 {A : Type'} (x' : A) (x : A) : (term63 A x' x) = (term63 A x' x).
Proof. exact (eq_refl (term63 A x' x)). Qed.
Lemma lem5049608 {A : Type'} (x' : A) (x : A) : (term62 A x x') = (term64 A x' x).
Proof. exact (MK_COMB (@lem5049607 A x' x) (@lem5049606 A x')). Qed.
Lemma lem5049610 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem5049611 {A : Type'} (x' : A) (x : A) : (term64 A x' x) = (x' = x).
Proof. exact (@lem5049610 (x' = x)). Qed.
Lemma lem5049614 {A : Type'} (x' : A) (x : A) : (term62 A x x') = (x' = x).
Proof. exact (TRANS (@lem5049608 A x' x) (@lem5049611 A x' x)). Qed.
Lemma lem5049615 {A : Type'} (x' : A) (x : A) : (term61 A x' x) = (x' = x).
Proof. exact (TRANS (@lem5049598 A x x') (@lem5049614 A x' x)). Qed.
Lemma lem5049616 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5049617 {A : Type'} (x' : A) (x : A) : (term65 A x' x) = (term66 A x' x).
Proof. exact (MK_COMB (@lem5049616) (@lem5049615 A x' x)). Qed.
Lemma lem5049619 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5049620 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5049619 A P x). Qed.
Lemma lem5049621 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem5049620 A s x'). Qed.
Lemma lem5049622 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term67 A x x' s) = (term68 A x s x').
Proof. exact (MK_COMB (@lem5049617 A x' x) (@lem5049621 A s x')). Qed.
Lemma lem5049627 {A : Type'} (x : A) (s : A -> Prop) : (term69 A x s) = (term70 A x s).
Proof. exact (fun_ext (fun x' : A => @lem5049622 A x s x')). Qed.
Lemma lem5049628 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5049629 {A : Type'} (x : A) (s : A -> Prop) : (term37 A x s) = (term71 A x s).
Proof. exact (MK_COMB (@lem5049628 A) (@lem5049627 A x s)). Qed.
Lemma lem5049634 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5049635 {A : Type'} (x : A) (s : A -> Prop) : (term39 A x s) = (term72 A x s).
Proof. exact (MK_COMB (@lem5049634) (@lem5049629 A x s)). Qed.
Lemma lem5049649 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5049650 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem5049649 B P x). Qed.
Lemma lem5049651 {B : Type'} (t : B -> Prop) (x : B) : (@IN B x t) = (t x).
Proof. exact (@lem5049650 B t x). Qed.
Lemma lem5049652 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5049653 {B : Type'} (t : B -> Prop) (x : B) : (term28 B x t) = (term58 B t x).
Proof. exact (MK_COMB (@lem5049652) (@lem5049651 B t x)). Qed.
Lemma lem5049655 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5049656 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem5049655 B P x). Qed.
Lemma lem5049657 {B : Type'} (u : B -> Prop) (x : B) : (@IN B x u) = (u x).
Proof. exact (@lem5049656 B u x). Qed.
Lemma lem5049658 {B : Type'} (t : B -> Prop) (u : B -> Prop) (x : B) : (term73 B t x u) = (term74 B t u x).
Proof. exact (MK_COMB (@lem5049653 B t x) (@lem5049657 B u x)). Qed.
Lemma lem5049661 {B : Type'} (t : B -> Prop) (u : B -> Prop) : (term75 B t u) = (term76 B t u).
Proof. exact (fun_ext (fun x : B => @lem5049658 B t u x)). Qed.
Lemma lem5049662 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5049663 {B : Type'} (t : B -> Prop) (u : B -> Prop) : (term8 B t u) = (term77 B t u).
Proof. exact (MK_COMB (@lem5049662 B) (@lem5049661 B t u)). Qed.
Lemma lem5049668 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5049669 {B : Type'} (t : B -> Prop) (u : B -> Prop) : (term41 B t u) = (term78 B t u).
Proof. exact (MK_COMB (@lem5049668) (@lem5049663 B t u)). Qed.
Lemma lem5049677 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term79 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem5049678 {A : Type'} (p : A -> Prop) (x : A) : (term79 A x p) = (p x).
Proof. exact (@lem5049677 A p x). Qed.
Lemma lem5049679 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) (x' : A) : (term80 A B x' s f t) = (term81 A B s f t x').
Proof. exact (@lem5049678 A (term82 A B s f t) x'). Qed.
Lemma lem5049680 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (t : B -> Prop) : (term81 A B s f t x) = (term83 A B s f x t).
Proof. exact (eq_refl (term81 A B s f t x)). Qed.
Lemma lem5049681 {A : Type'} (GEN_PVAR_222 : A) : (@SETSPEC A GEN_PVAR_222) = (@SETSPEC A GEN_PVAR_222).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_222)). Qed.
Lemma lem5049682 {A B : Type'} (GEN_PVAR_222 : A) (s : A -> Prop) (f : A -> B) (x : A) (t : B -> Prop) : (term84 A B GEN_PVAR_222 s f t x) = (term85 A B GEN_PVAR_222 s f x t).
Proof. exact (MK_COMB (@lem5049681 A GEN_PVAR_222) (@lem5049680 A B s f x t)). Qed.
Lemma lem5049683 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5049684 {A B : Type'} (GEN_PVAR_222 : A) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (x : A) : (term86 A B GEN_PVAR_222 s f t x) = (term87 A B GEN_PVAR_222 s f t x).
Proof. exact (MK_COMB (@lem5049682 A B GEN_PVAR_222 s f x t) (@lem5049683 A x)). Qed.
Lemma lem5049685 {A B : Type'} (GEN_PVAR_222 : A) (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term88 A B GEN_PVAR_222 s f t) = (term89 A B GEN_PVAR_222 s f t).
Proof. exact (fun_ext (fun x : A => @lem5049684 A B GEN_PVAR_222 s f t x)). Qed.
Lemma lem5049686 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5049687 {A B : Type'} (GEN_PVAR_222 : A) (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term90 A B GEN_PVAR_222 s f t) = (term91 A B GEN_PVAR_222 s f t).
Proof. exact (MK_COMB (@lem5049686 A) (@lem5049685 A B GEN_PVAR_222 s f t)). Qed.
Lemma lem5049688 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term92 A B s f t) = (term93 A B s f t).
Proof. exact (fun_ext (fun GEN_PVAR_222 : A => @lem5049687 A B GEN_PVAR_222 s f t)). Qed.
Lemma lem5049689 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem5049690 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term94 A B s f t) = (term43 A B s f t).
Proof. exact (MK_COMB (@lem5049689 A) (@lem5049688 A B s f t)). Qed.
Lemma lem5049691 {A : Type'} (x' : A) : (@IN A x') = (@IN A x').
Proof. exact (eq_refl (@IN A x')). Qed.
Lemma lem5049692 {A B : Type'} (x' : A) (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term80 A B x' s f t) = (term95 A B x' s f t).
Proof. exact (MK_COMB (@lem5049691 A x') (@lem5049690 A B s f t)). Qed.
Lemma lem5049693 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5049694 {A B : Type'} (x' : A) (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term96 A B x' s f t) = (term97 A B x' s f t).
Proof. exact (MK_COMB (@lem5049693) (@lem5049692 A B x' s f t)). Qed.
Lemma lem5049695 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (t : B -> Prop) : (term81 A B s f t x') = (term83 A B s f x' t).
Proof. exact (eq_refl (term81 A B s f t x')). Qed.
Lemma lem5049696 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (t : B -> Prop) : ((term80 A B x' s f t) = (term81 A B s f t x')) = ((term95 A B x' s f t) = (term83 A B s f x' t)).
Proof. exact (MK_COMB (@lem5049694 A B x' s f t) (@lem5049695 A B s f x' t)). Qed.
Lemma lem5049697 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (t : B -> Prop) : (term95 A B x' s f t) = (term83 A B s f x' t).
Proof. exact (EQ_MP (@lem5049696 A B s f x' t) (@lem5049679 A B s f t x')). Qed.
Lemma lem5049701 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5049702 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5049701 A P x). Qed.
Lemma lem5049703 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem5049702 A s x'). Qed.
Lemma lem5049704 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5049705 {A : Type'} (s : A -> Prop) (x' : A) : (term98 A x' s) = (term99 A s x').
Proof. exact (MK_COMB (@lem5049704) (@lem5049703 A s x')). Qed.
Lemma lem5049707 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5049708 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem5049707 B P x). Qed.
Lemma lem5049709 {A B : Type'} (t : B -> Prop) (f : A -> B) (x' : A) : (term27 A B f x' t) = (term100 A B t f x').
Proof. exact (@lem5049708 B t (f x')). Qed.
Lemma lem5049710 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x' : A) : (term83 A B s f x' t) = (term101 A B s t f x').
Proof. exact (MK_COMB (@lem5049705 A s x') (@lem5049709 A B t f x')). Qed.
Lemma lem5049713 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x' : A) : (term95 A B x' s f t) = (term101 A B s t f x').
Proof. exact (TRANS (@lem5049697 A B s f x' t) (@lem5049710 A B s t f x')). Qed.
Lemma lem5049714 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5049715 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x' : A) : (term97 A B x' s f t) = (term102 A B s t f x').
Proof. exact (MK_COMB (@lem5049714) (@lem5049713 A B s t f x')). Qed.
Lemma lem5049717 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term59 A x y s) = (term60 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem5049718 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term59 A x y s) = (term60 A y x s).
Proof. exact (@lem5049717 A y x s). Qed.
Lemma lem5049719 {A : Type'} (x : A) (x' : A) : (term61 A x' x) = (term62 A x x').
Proof. exact (@lem5049718 A x x' (@EMPTY A)). Qed.
Lemma lem5049725 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem5049726 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem5049725 A x). Qed.
Lemma lem5049727 {A : Type'} (x' : A) : (@IN A x' (@EMPTY A)) = False.
Proof. exact (@lem5049726 A x'). Qed.
Lemma lem5049728 {A : Type'} (x' : A) (x : A) : (term63 A x' x) = (term63 A x' x).
Proof. exact (eq_refl (term63 A x' x)). Qed.
Lemma lem5049729 {A : Type'} (x' : A) (x : A) : (term62 A x x') = (term64 A x' x).
Proof. exact (MK_COMB (@lem5049728 A x' x) (@lem5049727 A x')). Qed.
Lemma lem5049731 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem5049732 {A : Type'} (x' : A) (x : A) : (term64 A x' x) = (x' = x).
Proof. exact (@lem5049731 (x' = x)). Qed.
Lemma lem5049735 {A : Type'} (x' : A) (x : A) : (term62 A x x') = (x' = x).
Proof. exact (TRANS (@lem5049729 A x' x) (@lem5049732 A x' x)). Qed.
Lemma lem5049736 {A : Type'} (x' : A) (x : A) : (term61 A x' x) = (x' = x).
Proof. exact (TRANS (@lem5049719 A x x') (@lem5049735 A x' x)). Qed.
Lemma lem5049737 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x' : A) (x : A) : ((term95 A B x' s f t) = (term61 A x' x)) = ((term101 A B s t f x') = (x' = x)).
Proof. exact (MK_COMB (@lem5049715 A B s t f x') (@lem5049736 A x' x)). Qed.
Lemma lem5049740 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term103 A B s f t x) = (term104 A B s t f x).
Proof. exact (fun_ext (fun x' : A => @lem5049737 A B s t f x' x)). Qed.
Lemma lem5049741 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5049742 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term44 A B s f t x) = (term105 A B s t f x).
Proof. exact (MK_COMB (@lem5049741 A) (@lem5049740 A B s t f x)). Qed.
Lemma lem5049747 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term46 A B u s f t x) = (term106 A B u s t f x).
Proof. exact (MK_COMB (@lem5049669 B t u) (@lem5049742 A B s t f x)). Qed.
Lemma lem5049750 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term48 A B u s f x) = (term107 A B u s f x).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5049747 A B u s t f x)). Qed.
Lemma lem5049751 {B : Type'} : (@ex (B -> Prop)) = (@ex (B -> Prop)).
Proof. exact (eq_refl (@ex (B -> Prop))). Qed.
Lemma lem5049752 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term50 A B u s f x) = (term108 A B u s f x).
Proof. exact (MK_COMB (@lem5049751 B) (@lem5049750 A B u s f x)). Qed.
Lemma lem5049757 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term51 A B u s f x) = (term109 A B u s f x).
Proof. exact (MK_COMB (@lem5049635 A x s) (@lem5049752 A B u s f x)). Qed.
Lemma lem5049760 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5049761 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term53 A B u s f x) = (term110 A B u s f x).
Proof. exact (MK_COMB (@lem5049760) (@lem5049757 A B u s f x)). Qed.
Lemma lem5049764 {A : Type'} (x : A) (y : A) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem5049765 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term283 A B u s f x y) = (term291 A B u s f x y).
Proof. exact (MK_COMB (@lem5049761 A B u s f x) (@lem5049764 A x y)). Qed.
Lemma lem5049768 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term286 A B u s f x y) = (term292 A B u s f x y).
Proof. exact (MK_COMB (@lem5049584 A B f y s x) (@lem5049765 A B u s f x y)). Qed.
Lemma lem5049771 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term292 A B u s f x y) = (term286 A B u s f x y).
Proof. exact (SYM (@lem5049768 A B u s f x y)). Qed.
Lemma lem5049773 (p : Prop) : p = (term113 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5049774 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term292 A B u s f x y) = (term293 A B u s f x y).
Proof. exact (@lem5049773 (term292 A B u s f x y)). Qed.
Lemma lem5049775 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term293 A B u s f x y) = (term292 A B u s f x y).
Proof. exact (SYM (@lem5049774 A B u s f x y)). Qed.
Lemma lem5049776 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term294 A B u s f x y) : term294 A B u s f x y.
Proof. exact (h1). Qed.
Lemma lem5049779 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term293 A B u s f x y) : term293 A B u s f x y.
Proof. exact (h1). Qed.
Lemma lem5049780 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (y : A) : term295 A B u s f x y.
Proof. exact (fun h0 : term293 A B u s f x y => @lem5049779 A B u s f x y h0). Qed.
Lemma lem5049781 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term295 A B u s f x y) : term295 A B u s f x y.
Proof. exact (h1). Qed.
Lemma lem5049782 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term293 A B u s f x y) : term293 A B u s f x y.
Proof. exact (h1). Qed.
Lemma lem5049783 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term293 A B u s f x y) (h2 : term295 A B u s f x y) : term293 A B u s f x y.
Proof. exact (@lem5049781 A B u s f x y h2 (@lem5049782 A B u s f x y h1)). Qed.
Lemma lem5049784 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term293 A B u s f x y) : term296 A B u s f x y.
Proof. exact (fun h0 : term295 A B u s f x y => @lem5049783 A B u s f x y h1 h0). Qed.
Lemma lem5049785 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term295 A B u s f x y) : term295 A B u s f x y.
Proof. exact (h1). Qed.
Lemma lem5049786 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term293 A B u s f x y) (h2 : term295 A B u s f x y) : term293 A B u s f x y.
Proof. exact (@lem5049784 A B u s f x y h1 (@lem5049785 A B u s f x y h2)). Qed.
Lemma lem5049787 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term295 A B u s f x y) : term295 A B u s f x y.
Proof. exact (fun h0 : term293 A B u s f x y => @lem5049786 A B u s f x y h0 h1). Qed.
Lemma lem5049788 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (y : A) : term297 A B u s f x y.
Proof. exact (fun h0 : term295 A B u s f x y => @lem5049787 A B u s f x y h0). Qed.
Lemma lem5049791 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (y : A) : term295 A B u s f x y.
Proof. exact (@lem5049788 A B u s f x y (@lem5049780 A B u s f x y)). Qed.
Lemma lem5049792 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (y : A) : term295 A B u s f x y.
Proof. exact (@lem5049791 A B u s f x y). Qed.
Lemma lem5049814 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5049815 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term293 A B u s f x y) = (term298 A B u s f x y).
Proof. exact (@lem5049814 (term294 A B u s f x y)). Qed.
Lemma lem5049817 (t : Prop) : (term120 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5049818 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term298 A B u s f x y) = (term292 A B u s f x y).
Proof. exact (@lem5049817 (term292 A B u s f x y)). Qed.
Lemma lem5049821 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term293 A B u s f x y) = (term292 A B u s f x y).
Proof. exact (TRANS (@lem5049815 A B u s f x y) (@lem5049818 A B u s f x y)). Qed.
Lemma lem5049898 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term299 A B s f x y) = (term300 A B s f x y).
Proof. exact (fun_ext (fun u : B -> Prop => @lem5049821 A B u s f x y)). Qed.
Lemma lem5049899 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5049900 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term301 A B s f x y) = (term302 A B s f x y).
Proof. exact (MK_COMB (@lem5049899 B) (@lem5049898 A B s f x y)). Qed.
Lemma lem5049905 {A B : Type'} (f : A -> B) (x : A) (y : A) : (term303 A B f x y) = (term304 A B f x y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5049900 A B s f x y)). Qed.
Lemma lem5049906 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5049907 {A B : Type'} (f : A -> B) (x : A) (y : A) : (term305 A B f x y) = (term306 A B f x y).
Proof. exact (MK_COMB (@lem5049906 A) (@lem5049905 A B f x y)). Qed.
Lemma lem5049912 {A B : Type'} (x : A) (y : A) : (term307 A B x y) = (term308 A B x y).
Proof. exact (fun_ext (fun f : A -> B => @lem5049907 A B f x y)). Qed.
Lemma lem5049913 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5049914 {A B : Type'} (x : A) (y : A) : (term309 A B x y) = (term310 A B x y).
Proof. exact (MK_COMB (@lem5049913 A B) (@lem5049912 A B x y)). Qed.
Lemma lem5049919 {A B : Type'} (y : A) : (term311 A B y) = (term312 A B y).
Proof. exact (fun_ext (fun x : A => @lem5049914 A B x y)). Qed.
Lemma lem5049920 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5049921 {A B : Type'} (y : A) : (term313 A B y) = (term314 A B y).
Proof. exact (MK_COMB (@lem5049920 A) (@lem5049919 A B y)). Qed.
Lemma lem5049926 {A B : Type'} : (term315 A B) = (term316 A B).
Proof. exact (fun_ext (fun y : A => @lem5049921 A B y)). Qed.
Lemma lem5049927 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5049936 {A B : Type'} : (term317 A B) = (term318 A B).
Proof. exact (MK_COMB (@lem5049927 A) (@lem5049926 A B)). Qed.
Lemma lem5049937 {A : Type'} (x : A) (y : A) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem5049946 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x' : A) (x : A) : ((term101 A B s t f x') = (x' = x)) = ((term101 A B s t f x') = (x' = x)).
Proof. exact (eq_refl ((term101 A B s t f x') = (x' = x))). Qed.
Lemma lem5049947 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term104 A B s t f x) = (term104 A B s t f x).
Proof. exact (fun_ext (fun x' : A => @lem5049946 A B s t f x' x)). Qed.
Lemma lem5049948 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5049949 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term105 A B s t f x) = (term105 A B s t f x).
Proof. exact (MK_COMB (@lem5049948 A) (@lem5049947 A B s t f x)). Qed.
Lemma lem5049954 {B : Type'} (t : B -> Prop) (u : B -> Prop) (x : B) : (term74 B t u x) = (term74 B t u x).
Proof. exact (eq_refl (term74 B t u x)). Qed.
Lemma lem5049955 {B : Type'} (t : B -> Prop) (u : B -> Prop) : (term76 B t u) = (term76 B t u).
Proof. exact (fun_ext (fun x : B => @lem5049954 B t u x)). Qed.
Lemma lem5049956 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5049957 {B : Type'} (t : B -> Prop) (u : B -> Prop) : (term77 B t u) = (term77 B t u).
Proof. exact (MK_COMB (@lem5049956 B) (@lem5049955 B t u)). Qed.
Lemma lem5049958 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5049959 {B : Type'} (t : B -> Prop) (u : B -> Prop) : (term78 B t u) = (term78 B t u).
Proof. exact (MK_COMB (@lem5049958) (@lem5049957 B t u)). Qed.
Lemma lem5049960 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term106 A B u s t f x) = (term106 A B u s t f x).
Proof. exact (MK_COMB (@lem5049959 B t u) (@lem5049949 A B s t f x)). Qed.
Lemma lem5049961 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term107 A B u s f x) = (term107 A B u s f x).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5049960 A B u s t f x)). Qed.
Lemma lem5049962 {B : Type'} : (@ex (B -> Prop)) = (@ex (B -> Prop)).
Proof. exact (eq_refl (@ex (B -> Prop))). Qed.
Lemma lem5049963 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term108 A B u s f x) = (term108 A B u s f x).
Proof. exact (MK_COMB (@lem5049962 B) (@lem5049961 A B u s f x)). Qed.
Lemma lem5049968 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term68 A x s x') = (term68 A x s x').
Proof. exact (eq_refl (term68 A x s x')). Qed.
Lemma lem5049969 {A : Type'} (x : A) (s : A -> Prop) : (term70 A x s) = (term70 A x s).
Proof. exact (fun_ext (fun x' : A => @lem5049968 A x s x')). Qed.
Lemma lem5049970 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5049971 {A : Type'} (x : A) (s : A -> Prop) : (term71 A x s) = (term71 A x s).
Proof. exact (MK_COMB (@lem5049970 A) (@lem5049969 A x s)). Qed.
Lemma lem5049972 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5049973 {A : Type'} (x : A) (s : A -> Prop) : (term72 A x s) = (term72 A x s).
Proof. exact (MK_COMB (@lem5049972) (@lem5049971 A x s)). Qed.
Lemma lem5049974 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term109 A B u s f x) = (term109 A B u s f x).
Proof. exact (MK_COMB (@lem5049973 A x s) (@lem5049963 A B u s f x)). Qed.
Lemma lem5049975 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5049976 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term110 A B u s f x) = (term110 A B u s f x).
Proof. exact (MK_COMB (@lem5049975) (@lem5049974 A B u s f x)). Qed.
Lemma lem5049977 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term291 A B u s f x y) = (term291 A B u s f x y).
Proof. exact (MK_COMB (@lem5049976 A B u s f x) (@lem5049937 A x y)). Qed.
Lemma lem5049988 {A B : Type'} (f : A -> B) (y : A) (s : A -> Prop) (x : A) : (term290 A B f y s x) = (term290 A B f y s x).
Proof. exact (eq_refl (term290 A B f y s x)). Qed.
Lemma lem5049989 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term292 A B u s f x y) = (term292 A B u s f x y).
Proof. exact (MK_COMB (@lem5049988 A B f y s x) (@lem5049977 A B u s f x y)). Qed.
Lemma lem5049990 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term300 A B s f x y) = (term300 A B s f x y).
Proof. exact (fun_ext (fun u : B -> Prop => @lem5049989 A B u s f x y)). Qed.
Lemma lem5049991 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5049992 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term302 A B s f x y) = (term302 A B s f x y).
Proof. exact (MK_COMB (@lem5049991 B) (@lem5049990 A B s f x y)). Qed.
Lemma lem5049993 {A B : Type'} (f : A -> B) (x : A) (y : A) : (term304 A B f x y) = (term304 A B f x y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5049992 A B s f x y)). Qed.
Lemma lem5049994 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5049995 {A B : Type'} (f : A -> B) (x : A) (y : A) : (term306 A B f x y) = (term306 A B f x y).
Proof. exact (MK_COMB (@lem5049994 A) (@lem5049993 A B f x y)). Qed.
Lemma lem5049996 {A B : Type'} (x : A) (y : A) : (term308 A B x y) = (term308 A B x y).
Proof. exact (fun_ext (fun f : A -> B => @lem5049995 A B f x y)). Qed.
Lemma lem5049997 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5049998 {A B : Type'} (x : A) (y : A) : (term310 A B x y) = (term310 A B x y).
Proof. exact (MK_COMB (@lem5049997 A B) (@lem5049996 A B x y)). Qed.
Lemma lem5049999 {A B : Type'} (y : A) : (term312 A B y) = (term312 A B y).
Proof. exact (fun_ext (fun x : A => @lem5049998 A B x y)). Qed.
Lemma lem5050000 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5050001 {A B : Type'} (y : A) : (term314 A B y) = (term314 A B y).
Proof. exact (MK_COMB (@lem5050000 A) (@lem5049999 A B y)). Qed.
Lemma lem5050002 {A B : Type'} : (term316 A B) = (term316 A B).
Proof. exact (fun_ext (fun y : A => @lem5050001 A B y)). Qed.
Lemma lem5050003 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5050004 {A B : Type'} : (term318 A B) = (term318 A B).
Proof. exact (MK_COMB (@lem5050003 A) (@lem5050002 A B)). Qed.
Lemma lem5050079 {A B : Type'} : (term317 A B) = (term318 A B).
Proof. exact (TRANS (@lem5049936 A B) (@lem5050004 A B)). Qed.
Lemma lem5050080 {A B : Type'} : (term318 A B) = (term317 A B).
Proof. exact (SYM (@lem5050079 A B)). Qed.
Lemma lem5050082 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term109 A B u s f x) : term109 A B u s f x.
Proof. exact (h1). Qed.
Lemma lem5050084 (p : Prop) : p = (term113 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5050085 {A : Type'} (x : A) (y : A) : (x = y) = (term319 A x y).
Proof. exact (@lem5050084 (x = y)). Qed.
Lemma lem5050086 {A : Type'} (x : A) (y : A) : (term319 A x y) = (x = y).
Proof. exact (SYM (@lem5050085 A x y)). Qed.
Lemma lem5050087 {A : Type'} (x : A) (y : A) (h1 : term235 A x y) : term235 A x y.
Proof. exact (h1). Qed.
Lemma lem5050101 {A B : Type'} (f : A -> B) (y : A) (s : A -> Prop) (x : A) (h1 : term289 A B f y s x) : term289 A B f y s x.
Proof. exact (h1). Qed.
Lemma lem5050108 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term139 A x s x') = (term140 A x s x').
Proof. exact (@lem17362 (x' = x) (s x')). Qed.
Lemma lem5050109 {A : Type'} (P : A -> Prop) : (term141 A P) = (term142 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem5050110 {A : Type'} (x : A) (s : A -> Prop) : (term143 A x s) = (term144 A x s).
Proof. exact (@lem5050109 A (term70 A x s)). Qed.
Lemma lem5050111 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term145 A x s x') = (term68 A x s x').
Proof. exact (eq_refl (term145 A x s x')). Qed.
Lemma lem5050112 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5050113 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term146 A x s x') = (term139 A x s x').
Proof. exact (MK_COMB (@lem5050112) (@lem5050111 A x s x')). Qed.
Lemma lem5050114 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term146 A x s x') = (term140 A x s x').
Proof. exact (TRANS (@lem5050113 A x s x') (@lem5050108 A x s x')). Qed.
Lemma lem5050115 {A : Type'} (x : A) (s : A -> Prop) : (term147 A x s) = (term148 A x s).
Proof. exact (fun_ext (fun x' : A => @lem5050114 A x s x')). Qed.
Lemma lem5050116 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5050117 {A : Type'} (x : A) (s : A -> Prop) : (term144 A x s) = (term149 A x s).
Proof. exact (MK_COMB (@lem5050116 A) (@lem5050115 A x s)). Qed.
Lemma lem5050118 {A : Type'} (x : A) (s : A -> Prop) : (term143 A x s) = (term149 A x s).
Proof. exact (TRANS (@lem5050110 A x s) (@lem5050117 A x s)). Qed.
Lemma lem5050125 {B : Type'} (t : B -> Prop) (u : B -> Prop) (x : B) : (term74 B t u x) = (term150 B t u x).
Proof. exact (@lem17265 (t x) (u x)). Qed.
Lemma lem5050126 {B : Type'} (t : B -> Prop) (u : B -> Prop) : (term76 B t u) = (term151 B t u).
Proof. exact (fun_ext (fun x : B => @lem5050125 B t u x)). Qed.
Lemma lem5050127 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5050128 {B : Type'} (t : B -> Prop) (u : B -> Prop) : (term77 B t u) = (term152 B t u).
Proof. exact (MK_COMB (@lem5050127 B) (@lem5050126 B t u)). Qed.
Lemma lem5050137 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x' : A) : (term153 A B s t f x') = (term154 A B s t f x').
Proof. exact (@lem17045 (s x') (term100 A B t f x')). Qed.
Lemma lem5050142 {A : Type'} (x' : A) (x : A) : (x' = x) = (x' = x).
Proof. exact (eq_refl (x' = x)). Qed.
Lemma lem5050143 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5050144 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x' : A) : (term155 A B s t f x') = (term156 A B s t f x').
Proof. exact (MK_COMB (@lem5050143) (@lem5050137 A B s t f x')). Qed.
Lemma lem5050145 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x' : A) (x : A) : (term157 A B s t f x' x) = (term158 A B s t f x' x).
Proof. exact (MK_COMB (@lem5050144 A B s t f x') (@lem5050142 A x' x)). Qed.
Lemma lem5050150 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x' : A) (x : A) : (term159 A B s t f x' x) = (term159 A B s t f x' x).
Proof. exact (eq_refl (term159 A B s t f x' x)). Qed.
Lemma lem5050151 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x' : A) (x : A) : (term160 A B s t f x' x) = (term161 A B s t f x' x).
Proof. exact (MK_COMB (@lem5050150 A B s t f x' x) (@lem5050145 A B s t f x' x)). Qed.
Lemma lem5050152 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x' : A) (x : A) : ((term101 A B s t f x') = (x' = x)) = (term160 A B s t f x' x).
Proof. exact (@lem17784 (term101 A B s t f x') (x' = x)). Qed.
Lemma lem5050153 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x' : A) (x : A) : ((term101 A B s t f x') = (x' = x)) = (term161 A B s t f x' x).
Proof. exact (TRANS (@lem5050152 A B s t f x' x) (@lem5050151 A B s t f x' x)). Qed.
Lemma lem5050154 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term104 A B s t f x) = (term162 A B s t f x).
Proof. exact (fun_ext (fun x' : A => @lem5050153 A B s t f x' x)). Qed.
Lemma lem5050155 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5050156 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term105 A B s t f x) = (term163 A B s t f x).
Proof. exact (MK_COMB (@lem5050155 A) (@lem5050154 A B s t f x)). Qed.
Lemma lem5050157 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5050158 {B : Type'} (t : B -> Prop) (u : B -> Prop) : (term78 B t u) = (term164 B t u).
Proof. exact (MK_COMB (@lem5050157) (@lem5050128 B t u)). Qed.
Lemma lem5050159 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term106 A B u s t f x) = (term165 A B u s t f x).
Proof. exact (MK_COMB (@lem5050158 B t u) (@lem5050156 A B s t f x)). Qed.
Lemma lem5050160 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term107 A B u s f x) = (term166 A B u s f x).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5050159 A B u s t f x)). Qed.
Lemma lem5050161 {B : Type'} : (@ex (B -> Prop)) = (@ex (B -> Prop)).
Proof. exact (eq_refl (@ex (B -> Prop))). Qed.
Lemma lem5050162 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term108 A B u s f x) = (term167 A B u s f x).
Proof. exact (MK_COMB (@lem5050161 B) (@lem5050160 A B u s f x)). Qed.
Lemma lem5050163 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5050164 {A : Type'} (x : A) (s : A -> Prop) : (term168 A x s) = (term169 A x s).
Proof. exact (MK_COMB (@lem5050163) (@lem5050118 A x s)). Qed.
Lemma lem5050165 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term170 A B u s f x) = (term171 A B u s f x).
Proof. exact (MK_COMB (@lem5050164 A x s) (@lem5050162 A B u s f x)). Qed.
Lemma lem5050166 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term109 A B u s f x) = (term170 A B u s f x).
Proof. exact (@lem17265 (term71 A x s) (term108 A B u s f x)). Qed.
Lemma lem5050167 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term109 A B u s f x) = (term171 A B u s f x).
Proof. exact (TRANS (@lem5050166 A B u s f x) (@lem5050165 A B u s f x)). Qed.
Lemma lem5050297 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term172 A P Q) = (term173 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5050298 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term172 A P Q) = (term173 A P Q).
Proof. exact (@lem5050297 A P Q). Qed.
Lemma lem5050299 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term174 A B s t f x) = (term175 A B s t f x).
Proof. exact (@lem5050298 A (term176 A B s t f x) (term177 A B s t f x)). Qed.
Lemma lem5050300 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x' : A) (x : A) : (term178 A B s t f x x') = (term179 A B s t f x' x).
Proof. exact (eq_refl (term178 A B s t f x x')). Qed.
Lemma lem5050301 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5050302 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x' : A) (x : A) : (term180 A B s t f x x') = (term159 A B s t f x' x).
Proof. exact (MK_COMB (@lem5050301) (@lem5050300 A B s t f x' x)). Qed.
Lemma lem5050303 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x' : A) (x : A) : (term181 A B s t f x x') = (term158 A B s t f x' x).
Proof. exact (eq_refl (term181 A B s t f x x')). Qed.
Lemma lem5050304 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x' : A) (x : A) : (term182 A B s t f x x') = (term161 A B s t f x' x).
Proof. exact (MK_COMB (@lem5050302 A B s t f x' x) (@lem5050303 A B s t f x' x)). Qed.
Lemma lem5050305 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term183 A B s t f x) = (term162 A B s t f x).
Proof. exact (fun_ext (fun x' : A => @lem5050304 A B s t f x' x)). Qed.
Lemma lem5050306 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5050307 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term174 A B s t f x) = (term163 A B s t f x).
Proof. exact (MK_COMB (@lem5050306 A) (@lem5050305 A B s t f x)). Qed.
Lemma lem5050308 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5050309 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term184 A B s t f x) = (term185 A B s t f x).
Proof. exact (MK_COMB (@lem5050308) (@lem5050307 A B s t f x)). Qed.
Lemma lem5050310 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x' : A) (x : A) : (term178 A B s t f x x') = (term179 A B s t f x' x).
Proof. exact (eq_refl (term178 A B s t f x x')). Qed.
Lemma lem5050311 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term186 A B s t f x) = (term176 A B s t f x).
Proof. exact (fun_ext (fun x' : A => @lem5050310 A B s t f x' x)). Qed.
Lemma lem5050312 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5050313 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term187 A B s t f x) = (term188 A B s t f x).
Proof. exact (MK_COMB (@lem5050312 A) (@lem5050311 A B s t f x)). Qed.
Lemma lem5050314 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5050315 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term189 A B s t f x) = (term190 A B s t f x).
Proof. exact (MK_COMB (@lem5050314) (@lem5050313 A B s t f x)). Qed.
Lemma lem5050316 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x' : A) (x : A) : (term181 A B s t f x x') = (term158 A B s t f x' x).
Proof. exact (eq_refl (term181 A B s t f x x')). Qed.
Lemma lem5050317 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term191 A B s t f x) = (term177 A B s t f x).
Proof. exact (fun_ext (fun x' : A => @lem5050316 A B s t f x' x)). Qed.
Lemma lem5050318 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5050319 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term192 A B s t f x) = (term193 A B s t f x).
Proof. exact (MK_COMB (@lem5050318 A) (@lem5050317 A B s t f x)). Qed.
Lemma lem5050320 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term175 A B s t f x) = (term194 A B s t f x).
Proof. exact (MK_COMB (@lem5050315 A B s t f x) (@lem5050319 A B s t f x)). Qed.
Lemma lem5050321 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : ((term174 A B s t f x) = (term175 A B s t f x)) = ((term163 A B s t f x) = (term194 A B s t f x)).
Proof. exact (MK_COMB (@lem5050309 A B s t f x) (@lem5050320 A B s t f x)). Qed.
Lemma lem5050322 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term163 A B s t f x) = (term194 A B s t f x).
Proof. exact (EQ_MP (@lem5050321 A B s t f x) (@lem5050299 A B s t f x)). Qed.
Lemma lem5050419 {B : Type'} (t : B -> Prop) (u : B -> Prop) : (term164 B t u) = (term164 B t u).
Proof. exact (eq_refl (term164 B t u)). Qed.
Lemma lem5050420 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term165 A B u s t f x) = (term195 A B u s t f x).
Proof. exact (MK_COMB (@lem5050419 B t u) (@lem5050322 A B s t f x)). Qed.
Lemma lem5050421 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term166 A B u s f x) = (term196 A B u s f x).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5050420 A B u s t f x)). Qed.
Lemma lem5050422 {B : Type'} : (@ex (B -> Prop)) = (@ex (B -> Prop)).
Proof. exact (eq_refl (@ex (B -> Prop))). Qed.
Lemma lem5050423 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term167 A B u s f x) = (term197 A B u s f x).
Proof. exact (MK_COMB (@lem5050422 B) (@lem5050421 A B u s f x)). Qed.
Lemma lem5050472 {A : Type'} (x : A) (s : A -> Prop) : (term169 A x s) = (term169 A x s).
Proof. exact (eq_refl (term169 A x s)). Qed.
Lemma lem5050473 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term171 A B u s f x) = (term198 A B u s f x).
Proof. exact (MK_COMB (@lem5050472 A x s) (@lem5050423 A B u s f x)). Qed.
Lemma lem5050477 {A : Type'} (P : A -> Prop) (Q : Prop) : (term199 A P Q) = (term200 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5050478 {A : Type'} (P : A -> Prop) (Q : Prop) : (term199 A P Q) = (term200 A P Q).
Proof. exact (@lem5050477 A P Q). Qed.
Lemma lem5050479 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term201 A B u s f x) = (term202 A B u s f x).
Proof. exact (@lem5050478 A (term148 A x s) (term197 A B u s f x)). Qed.
Lemma lem5050480 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term203 A x s x') = (term140 A x s x').
Proof. exact (eq_refl (term203 A x s x')). Qed.
Lemma lem5050481 {A : Type'} (x : A) (s : A -> Prop) : (term204 A x s) = (term148 A x s).
Proof. exact (fun_ext (fun x' : A => @lem5050480 A x s x')). Qed.
Lemma lem5050482 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5050483 {A : Type'} (x : A) (s : A -> Prop) : (term205 A x s) = (term149 A x s).
Proof. exact (MK_COMB (@lem5050482 A) (@lem5050481 A x s)). Qed.
Lemma lem5050484 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5050485 {A : Type'} (x : A) (s : A -> Prop) : (term206 A x s) = (term169 A x s).
Proof. exact (MK_COMB (@lem5050484) (@lem5050483 A x s)). Qed.
Lemma lem5050486 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term197 A B u s f x) = (term197 A B u s f x).
Proof. exact (eq_refl (term197 A B u s f x)). Qed.
Lemma lem5050487 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term201 A B u s f x) = (term198 A B u s f x).
Proof. exact (MK_COMB (@lem5050485 A x s) (@lem5050486 A B u s f x)). Qed.
Lemma lem5050488 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5050489 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term207 A B u s f x) = (term208 A B u s f x).
Proof. exact (MK_COMB (@lem5050488) (@lem5050487 A B u s f x)). Qed.
Lemma lem5050490 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term203 A x s x') = (term140 A x s x').
Proof. exact (eq_refl (term203 A x s x')). Qed.
Lemma lem5050491 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5050492 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term209 A x s x') = (term210 A x s x').
Proof. exact (MK_COMB (@lem5050491) (@lem5050490 A x s x')). Qed.
Lemma lem5050493 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term197 A B u s f x) = (term197 A B u s f x).
Proof. exact (eq_refl (term197 A B u s f x)). Qed.
Lemma lem5050494 {A B : Type'} (x' : A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term211 A B x' u s f x) = (term212 A B x' u s f x).
Proof. exact (MK_COMB (@lem5050492 A x s x') (@lem5050493 A B u s f x)). Qed.
Lemma lem5050495 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term213 A B u s f x) = (term214 A B u s f x).
Proof. exact (fun_ext (fun x' : A => @lem5050494 A B x' u s f x)). Qed.
Lemma lem5050496 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5050497 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term202 A B u s f x) = (term215 A B u s f x).
Proof. exact (MK_COMB (@lem5050496 A) (@lem5050495 A B u s f x)). Qed.
Lemma lem5050498 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : ((term201 A B u s f x) = (term202 A B u s f x)) = ((term198 A B u s f x) = (term215 A B u s f x)).
Proof. exact (MK_COMB (@lem5050489 A B u s f x) (@lem5050497 A B u s f x)). Qed.
Lemma lem5050499 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term198 A B u s f x) = (term215 A B u s f x).
Proof. exact (EQ_MP (@lem5050498 A B u s f x) (@lem5050479 A B u s f x)). Qed.
Lemma lem5050501 {A : Type'} (P : Prop) (Q : A -> Prop) : (term216 A P Q) = (term217 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5050502 {B : Type'} (P : Prop) (Q : type686 B) : (term218 B P Q) = (term219 B P Q).
Proof. exact (@lem5050501 (B -> Prop) P Q). Qed.
Lemma lem5050503 {A B : Type'} (x' : A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term220 A B x' u s f x) = (term221 A B x' u s f x).
Proof. exact (@lem5050502 B (term140 A x s x') (term196 A B u s f x)). Qed.
Lemma lem5050504 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term222 A B u s f x t) = (term195 A B u s t f x).
Proof. exact (eq_refl (term222 A B u s f x t)). Qed.
Lemma lem5050505 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term223 A B u s f x) = (term196 A B u s f x).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5050504 A B u s t f x)). Qed.
Lemma lem5050506 {B : Type'} : (@ex (B -> Prop)) = (@ex (B -> Prop)).
Proof. exact (eq_refl (@ex (B -> Prop))). Qed.
Lemma lem5050507 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term224 A B u s f x) = (term197 A B u s f x).
Proof. exact (MK_COMB (@lem5050506 B) (@lem5050505 A B u s f x)). Qed.
Lemma lem5050508 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term210 A x s x') = (term210 A x s x').
Proof. exact (eq_refl (term210 A x s x')). Qed.
Lemma lem5050509 {A B : Type'} (x' : A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term220 A B x' u s f x) = (term212 A B x' u s f x).
Proof. exact (MK_COMB (@lem5050508 A x s x') (@lem5050507 A B u s f x)). Qed.
Lemma lem5050510 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5050511 {A B : Type'} (x' : A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term225 A B x' u s f x) = (term226 A B x' u s f x).
Proof. exact (MK_COMB (@lem5050510) (@lem5050509 A B x' u s f x)). Qed.
Lemma lem5050512 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term222 A B u s f x t) = (term195 A B u s t f x).
Proof. exact (eq_refl (term222 A B u s f x t)). Qed.
Lemma lem5050513 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term210 A x s x') = (term210 A x s x').
Proof. exact (eq_refl (term210 A x s x')). Qed.
Lemma lem5050514 {A B : Type'} (x' : A) (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term227 A B x' u s f x t) = (term228 A B x' u s t f x).
Proof. exact (MK_COMB (@lem5050513 A x s x') (@lem5050512 A B u s t f x)). Qed.
Lemma lem5050515 {A B : Type'} (x' : A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term229 A B x' u s f x) = (term230 A B x' u s f x).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5050514 A B x' u s t f x)). Qed.
Lemma lem5050516 {B : Type'} : (@ex (B -> Prop)) = (@ex (B -> Prop)).
Proof. exact (eq_refl (@ex (B -> Prop))). Qed.
Lemma lem5050517 {A B : Type'} (x' : A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term221 A B x' u s f x) = (term231 A B x' u s f x).
Proof. exact (MK_COMB (@lem5050516 B) (@lem5050515 A B x' u s f x)). Qed.
Lemma lem5050518 {A B : Type'} (x' : A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : ((term220 A B x' u s f x) = (term221 A B x' u s f x)) = ((term212 A B x' u s f x) = (term231 A B x' u s f x)).
Proof. exact (MK_COMB (@lem5050511 A B x' u s f x) (@lem5050517 A B x' u s f x)). Qed.
Lemma lem5050519 {A B : Type'} (x' : A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term212 A B x' u s f x) = (term231 A B x' u s f x).
Proof. exact (EQ_MP (@lem5050518 A B x' u s f x) (@lem5050503 A B x' u s f x)). Qed.
Lemma lem5050520 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term214 A B u s f x) = (term232 A B u s f x).
Proof. exact (fun_ext (fun x' : A => @lem5050519 A B x' u s f x)). Qed.
Lemma lem5050521 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5050522 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term215 A B u s f x) = (term233 A B u s f x).
Proof. exact (MK_COMB (@lem5050521 A) (@lem5050520 A B u s f x)). Qed.
Lemma lem5050523 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term198 A B u s f x) = (term233 A B u s f x).
Proof. exact (TRANS (@lem5050499 A B u s f x) (@lem5050522 A B u s f x)). Qed.
Lemma lem5050524 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term171 A B u s f x) = (term233 A B u s f x).
Proof. exact (TRANS (@lem5050473 A B u s f x) (@lem5050523 A B u s f x)). Qed.
Lemma lem5050525 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term109 A B u s f x) = (term233 A B u s f x).
Proof. exact (TRANS (@lem5050167 A B u s f x) (@lem5050524 A B u s f x)). Qed.
Lemma lem5050526 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term109 A B u s f x) : term233 A B u s f x.
Proof. exact (EQ_MP (@lem5050525 A B u s f x) (@lem5050082 A B u s f x h1)). Qed.
Lemma lem5050532 {A : Type'} (x : A) (y : A) (h1 : term235 A x y) : term235 A x y.
Proof. exact (h1). Qed.
Lemma lem5050533 {A B : Type'} (x' : A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term231 A B x' u s f x) : term231 A B x' u s f x.
Proof. exact (h1). Qed.
Lemma lem5050534 {A B : Type'} (x' : A) (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term228 A B x' u s t f x) : term228 A B x' u s t f x.
Proof. exact (h1). Qed.
Lemma lem5050556 {A B : Type'} (f : A -> B) (y : A) (s : A -> Prop) (x : A) (h1 : term289 A B f y s x) : term289 A B f y s x.
Proof. exact (h1). Qed.
Lemma lem5050564 {A : Type'} (x : A) (y : A) (h1 : term235 A x y) : term235 A x y.
Proof. exact (h1). Qed.
Lemma lem5050587 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x' : A) (x : A) : (term158 A B s t f x' x) = (term158 A B s t f x' x).
Proof. exact (eq_refl (term158 A B s t f x' x)). Qed.
Lemma lem5050588 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term177 A B s t f x) = (term177 A B s t f x).
Proof. exact (fun_ext (fun x' : A => @lem5050587 A B s t f x' x)). Qed.
Lemma lem5050589 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5050590 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term193 A B s t f x) = (term193 A B s t f x).
Proof. exact (MK_COMB (@lem5050589 A) (@lem5050588 A B s t f x)). Qed.
Lemma lem5050611 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x' : A) (x : A) : (term179 A B s t f x' x) = (term179 A B s t f x' x).
Proof. exact (eq_refl (term179 A B s t f x' x)). Qed.
Lemma lem5050612 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term176 A B s t f x) = (term176 A B s t f x).
Proof. exact (fun_ext (fun x' : A => @lem5050611 A B s t f x' x)). Qed.
Lemma lem5050613 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5050614 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term188 A B s t f x) = (term188 A B s t f x).
Proof. exact (MK_COMB (@lem5050613 A) (@lem5050612 A B s t f x)). Qed.
Lemma lem5050615 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5050616 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term190 A B s t f x) = (term190 A B s t f x).
Proof. exact (MK_COMB (@lem5050615) (@lem5050614 A B s t f x)). Qed.
Lemma lem5050617 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term194 A B s t f x) = (term194 A B s t f x).
Proof. exact (MK_COMB (@lem5050616 A B s t f x) (@lem5050590 A B s t f x)). Qed.
Lemma lem5050628 {B : Type'} (t : B -> Prop) (u : B -> Prop) (x : B) : (term150 B t u x) = (term150 B t u x).
Proof. exact (eq_refl (term150 B t u x)). Qed.
Lemma lem5050629 {B : Type'} (t : B -> Prop) (u : B -> Prop) : (term151 B t u) = (term151 B t u).
Proof. exact (fun_ext (fun x : B => @lem5050628 B t u x)). Qed.
Lemma lem5050630 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5050631 {B : Type'} (t : B -> Prop) (u : B -> Prop) : (term152 B t u) = (term152 B t u).
Proof. exact (MK_COMB (@lem5050630 B) (@lem5050629 B t u)). Qed.
Lemma lem5050632 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5050633 {B : Type'} (t : B -> Prop) (u : B -> Prop) : (term164 B t u) = (term164 B t u).
Proof. exact (MK_COMB (@lem5050632) (@lem5050631 B t u)). Qed.
Lemma lem5050634 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term195 A B u s t f x) = (term195 A B u s t f x).
Proof. exact (MK_COMB (@lem5050633 B t u) (@lem5050617 A B s t f x)). Qed.
Lemma lem5050649 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term210 A x s x') = (term210 A x s x').
Proof. exact (eq_refl (term210 A x s x')). Qed.
Lemma lem5050650 {A B : Type'} (x' : A) (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term228 A B x' u s t f x) = (term228 A B x' u s t f x).
Proof. exact (MK_COMB (@lem5050649 A x s x') (@lem5050634 A B u s t f x)). Qed.
Lemma lem5050651 {A B : Type'} (x' : A) (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term228 A B x' u s t f x) : term228 A B x' u s t f x.
Proof. exact (EQ_MP (@lem5050650 A B x' u s t f x) (@lem5050534 A B x' u s t f x h1)). Qed.
Lemma lem5050652 {A B : Type'} (f : A -> B) (y : A) (s : A -> Prop) (x : A) (h1 : term289 A B f y s x) : term287 A y s x.
Proof. exact (proj2 (@lem5050556 A B f y s x h1)). Qed.
Lemma lem5050656 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term140 A x s x') : term140 A x s x'.
Proof. exact (h1). Qed.
Lemma lem5050657 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term195 A B u s t f x) : term195 A B u s t f x.
Proof. exact (h1). Qed.
Lemma lem5050660 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term195 A B u s t f x) : term194 A B s t f x.
Proof. exact (proj2 (@lem5050657 A B u s t f x h1)). Qed.
Lemma lem5050662 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term195 A B u s t f x) : term193 A B s t f x.
Proof. exact (proj2 (@lem5050660 A B u s t f x h1)). Qed.
Lemma lem5050663 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term195 A B u s t f x) : term188 A B s t f x.
Proof. exact (proj1 (@lem5050660 A B u s t f x h1)). Qed.
Lemma lem5050691 {A : Type'} (x : A) (y : A) (h1 : term235 A x y) : term235 A x y.
Proof. exact (h1). Qed.
Lemma lem5050734 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x' : A) (x : A) : (term179 A B s t f x' x) = (term234 A B s t f x' x).
Proof. exact (@lem19699 (s x') (term100 A B t f x') (term235 A x' x)). Qed.
Lemma lem5050735 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term176 A B s t f x) = (term236 A B s t f x).
Proof. exact (fun_ext (fun x' : A => @lem5050734 A B s t f x' x)). Qed.
Lemma lem5050736 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5050738 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term188 A B s t f x) = (term237 A B s t f x).
Proof. exact (MK_COMB (@lem5050736 A) (@lem5050735 A B s t f x)). Qed.
Lemma lem5050739 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term195 A B u s t f x) : term237 A B s t f x.
Proof. exact (EQ_MP (@lem5050738 A B s t f x) (@lem5050663 A B u s t f x h1)). Qed.
Lemma lem5050753 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x' : A) (x : A) : (term158 A B s t f x' x) = (term158 A B s t f x' x).
Proof. exact (eq_refl (term158 A B s t f x' x)). Qed.
Lemma lem5050754 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term177 A B s t f x) = (term177 A B s t f x).
Proof. exact (fun_ext (fun x' : A => @lem5050753 A B s t f x' x)). Qed.
Lemma lem5050755 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5050757 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term193 A B s t f x) = (term193 A B s t f x).
Proof. exact (MK_COMB (@lem5050755 A) (@lem5050754 A B s t f x)). Qed.
Lemma lem5050758 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term195 A B u s t f x) : term193 A B s t f x.
Proof. exact (EQ_MP (@lem5050757 A B s t f x) (@lem5050662 A B u s t f x h1)). Qed.
Lemma lem5050762 {A B : Type'} (_64907 : A) (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term195 A B u s t f x) : term239 A B s t f x _64907.
Proof. exact (@lem5050739 A B u s t f x h1 _64907). Qed.
Lemma lem5050763 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (_64907 : A) (x : A) : (term239 A B s t f x _64907) = (term234 A B s t f _64907 x).
Proof. exact (eq_refl (term239 A B s t f x _64907)). Qed.
Lemma lem5050764 {A B : Type'} (_64907 : A) (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term195 A B u s t f x) : term234 A B s t f _64907 x.
Proof. exact (EQ_MP (@lem5050763 A B s t f _64907 x) (@lem5050762 A B _64907 u s t f x h1)). Qed.
Lemma lem5050765 {A B : Type'} (_64908 : A) (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term195 A B u s t f x) : term181 A B s t f x _64908.
Proof. exact (@lem5050758 A B u s t f x h1 _64908). Qed.
Lemma lem5050766 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (_64908 : A) (x : A) : (term181 A B s t f x _64908) = (term158 A B s t f _64908 x).
Proof. exact (eq_refl (term181 A B s t f x _64908)). Qed.
Lemma lem5050767 {A B : Type'} (_64908 : A) (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term195 A B u s t f x) : term158 A B s t f _64908 x.
Proof. exact (EQ_MP (@lem5050766 A B s t f _64908 x) (@lem5050765 A B _64908 u s t f x h1)). Qed.
Lemma lem5050779 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term140 A x s x') : x' = x.
Proof. exact (proj1 (@lem5050656 A x s x' h1)). Qed.
Lemma lem5050781 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term140 A x s x') : term240 A s x'.
Proof. exact (proj2 (@lem5050656 A x s x' h1)). Qed.
Lemma lem5050783 {A : Type'} (x : A) (y : A) (h1 : term235 A x y) : term235 A x y.
Proof. exact (h1). Qed.
Lemma lem5050806 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (_64908 : A) (x : A) : (term158 A B s t f _64908 x) = (term320 A B s t f _64908 x).
Proof. exact (@lem5049463 (term240 A s _64908) (term138 A B t f _64908) (_64908 = x)). Qed.
Lemma lem5050807 {A B : Type'} (_64908 : A) (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term195 A B u s t f x) : term320 A B s t f _64908 x.
Proof. exact (EQ_MP (@lem5050806 A B s t f _64908 x) (@lem5050767 A B _64908 u s t f x h1)). Qed.
Lemma lem5050819 {A B : Type'} (_64907 : A) (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term195 A B u s t f x) : term241 A B t f _64907 x.
Proof. exact (proj2 (@lem5050764 A B _64907 u s t f x h1)). Qed.
Lemma lem5050890 {A : Type'} (s : A -> Prop) : (term242 A s) = (term242 A s).
Proof. exact (eq_refl (term242 A s)). Qed.
Lemma lem5050891 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term140 A x s x') : (term243 A s x') = (term243 A s x).
Proof. exact (MK_COMB (@lem5050890 A s) (@lem5050779 A x s x' h1)). Qed.
Lemma lem5050892 {A : Type'} (s : A -> Prop) (x : A) : (term243 A s x) = (term240 A s x).
Proof. exact (eq_refl (term243 A s x)). Qed.
Lemma lem5050893 {A : Type'} (s : A -> Prop) (x' : A) : (term244 A s x') = (term244 A s x').
Proof. exact (eq_refl (term244 A s x')). Qed.
Lemma lem5050894 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : ((term243 A s x') = (term243 A s x)) = ((term243 A s x') = (term240 A s x)).
Proof. exact (MK_COMB (@lem5050893 A s x') (@lem5050892 A s x)). Qed.
Lemma lem5050895 {A : Type'} (s : A -> Prop) (x' : A) : (term243 A s x') = (term240 A s x').
Proof. exact (eq_refl (term243 A s x')). Qed.
Lemma lem5050896 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5050897 {A : Type'} (s : A -> Prop) (x' : A) : (term244 A s x') = (term245 A s x').
Proof. exact (MK_COMB (@lem5050896) (@lem5050895 A s x')). Qed.
Lemma lem5050898 {A : Type'} (s : A -> Prop) (x : A) : (term240 A s x) = (term240 A s x).
Proof. exact (eq_refl (term240 A s x)). Qed.
Lemma lem5050899 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : ((term243 A s x') = (term240 A s x)) = ((term240 A s x') = (term240 A s x)).
Proof. exact (MK_COMB (@lem5050897 A s x') (@lem5050898 A s x)). Qed.
Lemma lem5050900 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : ((term243 A s x') = (term243 A s x)) = ((term240 A s x') = (term240 A s x)).
Proof. exact (TRANS (@lem5050894 A x' s x) (@lem5050899 A x' s x)). Qed.
Lemma lem5050901 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term140 A x s x') : (term240 A s x') = (term240 A s x).
Proof. exact (EQ_MP (@lem5050900 A x' s x) (@lem5050891 A x s x' h1)). Qed.
Lemma lem5050902 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term140 A x s x') : term240 A s x.
Proof. exact (EQ_MP (@lem5050901 A x s x' h1) (@lem5050781 A x s x' h1)). Qed.
Lemma lem5050928 {A B : Type'} (f : A -> B) (y : A) (s : A -> Prop) (x : A) (h1 : term289 A B f y s x) : s x.
Proof. exact (proj2 (@lem5050652 A B f y s x h1)). Qed.
Lemma lem5050929 {A B : Type'} (f : A -> B) (y : A) (s : A -> Prop) (x : A) (h1 : term289 A B f y s x) : term246 A s x.
Proof. exact (fun h0 : term240 A s x => @lem5050928 A B f y s x h1). Qed.
Lemma lem5050931 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5050932 {A : Type'} (s : A -> Prop) (x : A) : (term246 A s x) = (s x).
Proof. exact (@lem5050931 (s x)). Qed.
Lemma lem5050933 {A B : Type'} (f : A -> B) (y : A) (s : A -> Prop) (x : A) (h1 : term289 A B f y s x) : s x.
Proof. exact (EQ_MP (@lem5050932 A s x) (@lem5050929 A B f y s x h1)). Qed.
Lemma lem5050936 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5050938 {A : Type'} (s : A -> Prop) (x : A) : (term240 A s x) = (term248 A s x).
Proof. exact (@lem5050936 (s x)). Qed.
Lemma lem5050941 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term140 A x s x') : term248 A s x.
Proof. exact (EQ_MP (@lem5050938 A s x) (@lem5050902 A x s x' h1)). Qed.
Lemma lem5050944 {A B : Type'} (x' : A) (f : A -> B) (y : A) (s : A -> Prop) (x : A) (h1 : term140 A x s x') (h2 : term289 A B f y s x) : False.
Proof. exact (@lem5050941 A x s x' h1 (@lem5050933 A B f y s x h2)). Qed.
Lemma lem5050945 {A B : Type'} (x' : A) (f : A -> B) (y : A) (s : A -> Prop) (x : A) (h1 : term140 A x s x') (h2 : term289 A B f y s x) : term249.
Proof. exact (fun h0 : ~ False => @lem5050944 A B x' f y s x h1 h2). Qed.
Lemma lem5050947 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5050948 : term249 = False.
Proof. exact (@lem5050947 False). Qed.
Lemma lem5050950 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5050951 {B : Type'} (_64925 : B) (_64926 : B) (h1 : _64925 = _64926) : _64925 = _64926.
Proof. exact (h1). Qed.
Lemma lem5050952 {B : Type'} (t : B -> Prop) (_64925 : B) (_64926 : B) (h1 : _64925 = _64926) : (t _64925) = (t _64926).
Proof. exact (MK_COMB (@lem5050950 B t) (@lem5050951 B _64925 _64926 h1)). Qed.
Lemma lem5050954 (b : Prop) (a : Prop) : term321 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem5050955 {B : Type'} (_64926 : B) (t : B -> Prop) (_64925 : B) : term322 B _64926 t _64925.
Proof. exact (@lem5050954 (t _64926) (t _64925)). Qed.
Lemma lem5050956 {B : Type'} (t : B -> Prop) (_64925 : B) (_64926 : B) (h1 : _64925 = _64926) : term323 B _64926 t _64925.
Proof. exact (@lem5050955 B _64926 t _64925 (@lem5050952 B t _64925 _64926 h1)). Qed.
Lemma lem5050957 {B : Type'} (_64926 : B) (t : B -> Prop) (_64925 : B) : term324 B _64926 t _64925.
Proof. exact (fun h0 : _64925 = _64926 => @lem5050956 B t _64925 _64926 h0). Qed.
Lemma lem5050959 (a : Prop) (b : Prop) : (a -> b) = (term325 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem5050960 {B : Type'} (_64926 : B) (t : B -> Prop) (_64925 : B) : (term324 B _64926 t _64925) = (term326 B _64926 t _64925).
Proof. exact (@lem5050959 (_64925 = _64926) (term323 B _64926 t _64925)). Qed.
Lemma lem5050961 {B : Type'} (_64926 : B) (t : B -> Prop) (_64925 : B) : term326 B _64926 t _64925.
Proof. exact (EQ_MP (@lem5050960 B _64926 t _64925) (@lem5050957 B _64926 t _64925)). Qed.
Lemma lem5050997 {A : Type'} (x : A) (y : A) (z : A) : term327 A x y z.
Proof. exact (@lem21385 A x y z). Qed.
Lemma lem5050999 {A B : Type'} (f : A -> B) (y : A) (s : A -> Prop) (x : A) (h1 : term289 A B f y s x) : s y.
Proof. exact (proj1 (@lem5050652 A B f y s x h1)). Qed.
Lemma lem5051000 {A B : Type'} (f : A -> B) (y : A) (s : A -> Prop) (x : A) (h1 : term289 A B f y s x) : term246 A s y.
Proof. exact (fun h0 : term240 A s y => @lem5050999 A B f y s x h1). Qed.
Lemma lem5051002 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5051003 {A : Type'} (s : A -> Prop) (y : A) : (term246 A s y) = (s y).
Proof. exact (@lem5051002 (s y)). Qed.
Lemma lem5051004 {A B : Type'} (f : A -> B) (y : A) (s : A -> Prop) (x : A) (h1 : term289 A B f y s x) : s y.
Proof. exact (EQ_MP (@lem5051003 A s y) (@lem5051000 A B f y s x h1)). Qed.
Lemma lem5051006 {A B : Type'} (f : A -> B) (y : A) (s : A -> Prop) (x : A) (h1 : term289 A B f y s x) : (f x) = (f y).
Proof. exact (proj1 (@lem5050556 A B f y s x h1)). Qed.
Lemma lem5051007 {A B : Type'} (f : A -> B) (y : A) (s : A -> Prop) (x : A) (h1 : term289 A B f y s x) : term328 A B x f y.
Proof. exact (fun h0 : term329 A B x f y => @lem5051006 A B f y s x h1). Qed.
Lemma lem5051009 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5051010 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term328 A B x f y) = ((f x) = (f y)).
Proof. exact (@lem5051009 ((f x) = (f y))). Qed.
Lemma lem5051011 {A B : Type'} (f : A -> B) (y : A) (s : A -> Prop) (x : A) (h1 : term289 A B f y s x) : (f x) = (f y).
Proof. exact (EQ_MP (@lem5051010 A B x f y) (@lem5051007 A B f y s x h1)). Qed.
Lemma lem5051013 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem5051014 {A : Type'} (x : A) : x = x.
Proof. exact (@lem5051013 A x). Qed.
Lemma lem5051015 {A : Type'} (x : A) : term250 A x.
Proof. exact (fun h0 : term251 A x => @lem5051014 A x). Qed.
Lemma lem5051017 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5051018 {A : Type'} (x : A) : (term250 A x) = (x = x).
Proof. exact (@lem5051017 (x = x)). Qed.
Lemma lem5051019 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem5051018 A x) (@lem5051015 A x)). Qed.
Lemma lem5051021 (b : Prop) (a : Prop) : (a \/ b) = (term252 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5051022 {A B : Type'} (x : A) (t : B -> Prop) (f : A -> B) (_64907 : A) : (term241 A B t f _64907 x) = (term253 A B x t f _64907).
Proof. exact (@lem5051021 (term235 A _64907 x) (term100 A B t f _64907)). Qed.
Lemma lem5051024 (a : Prop) : (term120 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5051025 {A : Type'} (_64907 : A) (x : A) : (term254 A _64907 x) = (_64907 = x).
Proof. exact (@lem5051024 (_64907 = x)). Qed.
Lemma lem5051026 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5051027 {A : Type'} (_64907 : A) (x : A) : (term255 A _64907 x) = (term66 A _64907 x).
Proof. exact (MK_COMB (@lem5051026) (@lem5051025 A _64907 x)). Qed.
Lemma lem5051028 {A B : Type'} (t : B -> Prop) (f : A -> B) (_64907 : A) : (term100 A B t f _64907) = (term100 A B t f _64907).
Proof. exact (eq_refl (term100 A B t f _64907)). Qed.
Lemma lem5051029 {A B : Type'} (x : A) (t : B -> Prop) (f : A -> B) (_64907 : A) : (term253 A B x t f _64907) = (term256 A B x t f _64907).
Proof. exact (MK_COMB (@lem5051027 A _64907 x) (@lem5051028 A B t f _64907)). Qed.
Lemma lem5051030 {A B : Type'} (x : A) (t : B -> Prop) (f : A -> B) (_64907 : A) : (term241 A B t f _64907 x) = (term256 A B x t f _64907).
Proof. exact (TRANS (@lem5051022 A B x t f _64907) (@lem5051029 A B x t f _64907)). Qed.
Lemma lem5051033 {A B : Type'} (_64907 : A) (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term195 A B u s t f x) : term256 A B x t f _64907.
Proof. exact (EQ_MP (@lem5051030 A B x t f _64907) (@lem5050819 A B _64907 u s t f x h1)). Qed.
Lemma lem5051034 {A B : Type'} (_64907 : A) (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term195 A B u s t f x) : term256 A B x t f _64907.
Proof. exact (@lem5051033 A B _64907 u s t f x h1). Qed.
Lemma lem5051035 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term195 A B u s t f x) : term257 A B t f x.
Proof. exact (@lem5051034 A B x u s t f x h1). Qed.
Lemma lem5051038 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term195 A B u s t f x) : term100 A B t f x.
Proof. exact (@lem5051035 A B u s t f x h1 (@lem5051019 A x)). Qed.
Lemma lem5051039 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term195 A B u s t f x) : term258 A B t f x.
Proof. exact (fun h0 : term138 A B t f x => @lem5051038 A B u s t f x h1). Qed.
Lemma lem5051041 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5051042 {A B : Type'} (t : B -> Prop) (f : A -> B) (x : A) : (term258 A B t f x) = (term100 A B t f x).
Proof. exact (@lem5051041 (term100 A B t f x)). Qed.
Lemma lem5051043 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term195 A B u s t f x) : term100 A B t f x.
Proof. exact (EQ_MP (@lem5051042 A B t f x) (@lem5051039 A B u s t f x h1)). Qed.
Lemma lem5051049 (q : Prop) (p : Prop) (r : Prop) : (term278 p q r) = (term278 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5051050 {B : Type'} (_64926 : B) (t : B -> Prop) (_64925 : B) : (term326 B _64926 t _64925) = (term330 B _64926 t _64925).
Proof. exact (@lem5051049 (t _64926) (term235 B _64925 _64926) (term240 B t _64925)). Qed.
Lemma lem5051064 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5051065 {B : Type'} (t : B -> Prop) (_64925 : B) (_64926 : B) : (term331 B _64926 t _64925) = (term332 B t _64925 _64926).
Proof. exact (@lem5051064 (term240 B t _64925) (term235 B _64925 _64926)). Qed.
Lemma lem5051073 {B : Type'} (t : B -> Prop) (_64926 : B) : (term333 B t _64926) = (term333 B t _64926).
Proof. exact (eq_refl (term333 B t _64926)). Qed.
Lemma lem5051074 {B : Type'} (t : B -> Prop) (_64925 : B) (_64926 : B) : (term330 B _64926 t _64925) = (term334 B t _64925 _64926).
Proof. exact (MK_COMB (@lem5051073 B t _64926) (@lem5051065 B t _64925 _64926)). Qed.
Lemma lem5051085 {B : Type'} (t : B -> Prop) (_64925 : B) (_64926 : B) : (term326 B _64926 t _64925) = (term334 B t _64925 _64926).
Proof. exact (TRANS (@lem5051050 B _64926 t _64925) (@lem5051074 B t _64925 _64926)). Qed.
Lemma lem5051086 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5051087 {B : Type'} (t : B -> Prop) (_64925 : B) (_64926 : B) : (term335 B _64926 t _64925) = (term336 B t _64925 _64926).
Proof. exact (MK_COMB (@lem5051086) (@lem5051085 B t _64925 _64926)). Qed.
Lemma lem5051101 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5051102 {B : Type'} (t : B -> Prop) (_64925 : B) (_64926 : B) : (term331 B _64926 t _64925) = (term332 B t _64925 _64926).
Proof. exact (@lem5051101 (term240 B t _64925) (term235 B _64925 _64926)). Qed.
Lemma lem5051110 {B : Type'} (t : B -> Prop) (_64926 : B) : (term333 B t _64926) = (term333 B t _64926).
Proof. exact (eq_refl (term333 B t _64926)). Qed.
Lemma lem5051111 {B : Type'} (t : B -> Prop) (_64925 : B) (_64926 : B) : (term330 B _64926 t _64925) = (term334 B t _64925 _64926).
Proof. exact (MK_COMB (@lem5051110 B t _64926) (@lem5051102 B t _64925 _64926)). Qed.
Lemma lem5051122 {B : Type'} (t : B -> Prop) (_64925 : B) (_64926 : B) : ((term326 B _64926 t _64925) = (term330 B _64926 t _64925)) = ((term334 B t _64925 _64926) = (term334 B t _64925 _64926)).
Proof. exact (MK_COMB (@lem5051087 B t _64925 _64926) (@lem5051111 B t _64925 _64926)). Qed.
Lemma lem5051124 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5051125 (x : Prop) : (x = x) = True.
Proof. exact (@lem5051124 Prop x). Qed.
Lemma lem5051126 {B : Type'} (t : B -> Prop) (_64925 : B) (_64926 : B) : ((term334 B t _64925 _64926) = (term334 B t _64925 _64926)) = True.
Proof. exact (@lem5051125 (term334 B t _64925 _64926)). Qed.
Lemma lem5051127 {B : Type'} (_64926 : B) (t : B -> Prop) (_64925 : B) : ((term326 B _64926 t _64925) = (term330 B _64926 t _64925)) = True.
Proof. exact (TRANS (@lem5051122 B t _64925 _64926) (@lem5051126 B t _64925 _64926)). Qed.
Lemma lem5051128 {B : Type'} (_64926 : B) (t : B -> Prop) (_64925 : B) : True = ((term326 B _64926 t _64925) = (term330 B _64926 t _64925)).
Proof. exact (SYM (@lem5051127 B _64926 t _64925)). Qed.
Lemma lem5051129 {B : Type'} (_64926 : B) (t : B -> Prop) (_64925 : B) : (term326 B _64926 t _64925) = (term330 B _64926 t _64925).
Proof. exact (EQ_MP (@lem5051128 B _64926 t _64925) (@lem0)). Qed.
Lemma lem5051130 {B : Type'} (_64926 : B) (t : B -> Prop) (_64925 : B) : term330 B _64926 t _64925.
Proof. exact (EQ_MP (@lem5051129 B _64926 t _64925) (@lem5050961 B _64926 t _64925)). Qed.
Lemma lem5051132 (b : Prop) (a : Prop) : (a \/ b) = (term252 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5051133 {B : Type'} (_64925 : B) (t : B -> Prop) (_64926 : B) : (term330 B _64926 t _64925) = (term337 B _64925 t _64926).
Proof. exact (@lem5051132 (term331 B _64926 t _64925) (t _64926)). Qed.
Lemma lem5051135 (a : Prop) (b : Prop) : (term338 a b) = (term339 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5051136 {B : Type'} (_64926 : B) (t : B -> Prop) (_64925 : B) : (term340 B _64926 t _64925) = (term341 B _64926 t _64925).
Proof. exact (@lem5051135 (term235 B _64925 _64926) (term240 B t _64925)). Qed.
Lemma lem5051138 (a : Prop) : (term120 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5051139 {B : Type'} (_64925 : B) (_64926 : B) : (term254 B _64925 _64926) = (_64925 = _64926).
Proof. exact (@lem5051138 (_64925 = _64926)). Qed.
Lemma lem5051140 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5051141 {B : Type'} (_64925 : B) (_64926 : B) : (term342 B _64925 _64926) = (term343 B _64925 _64926).
Proof. exact (MK_COMB (@lem5051140) (@lem5051139 B _64925 _64926)). Qed.
Lemma lem5051143 (a : Prop) : (term120 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5051144 {B : Type'} (t : B -> Prop) (_64925 : B) : (term263 B t _64925) = (t _64925).
Proof. exact (@lem5051143 (t _64925)). Qed.
Lemma lem5051145 {B : Type'} (_64926 : B) (t : B -> Prop) (_64925 : B) : (term341 B _64926 t _64925) = (term344 B _64926 t _64925).
Proof. exact (MK_COMB (@lem5051141 B _64925 _64926) (@lem5051144 B t _64925)). Qed.
Lemma lem5051146 {B : Type'} (_64926 : B) (t : B -> Prop) (_64925 : B) : (term340 B _64926 t _64925) = (term344 B _64926 t _64925).
Proof. exact (TRANS (@lem5051136 B _64926 t _64925) (@lem5051145 B _64926 t _64925)). Qed.
Lemma lem5051147 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5051148 {B : Type'} (_64926 : B) (t : B -> Prop) (_64925 : B) : (term345 B _64926 t _64925) = (term346 B _64926 t _64925).
Proof. exact (MK_COMB (@lem5051147) (@lem5051146 B _64926 t _64925)). Qed.
Lemma lem5051149 {B : Type'} (t : B -> Prop) (_64926 : B) : (t _64926) = (t _64926).
Proof. exact (eq_refl (t _64926)). Qed.
Lemma lem5051150 {B : Type'} (_64925 : B) (t : B -> Prop) (_64926 : B) : (term337 B _64925 t _64926) = (term347 B _64925 t _64926).
Proof. exact (MK_COMB (@lem5051148 B _64926 t _64925) (@lem5051149 B t _64926)). Qed.
Lemma lem5051151 {B : Type'} (_64925 : B) (t : B -> Prop) (_64926 : B) : (term330 B _64926 t _64925) = (term347 B _64925 t _64926).
Proof. exact (TRANS (@lem5051133 B _64925 t _64926) (@lem5051150 B _64925 t _64926)). Qed.
Lemma lem5051153 {A B : Type'} (u : B -> Prop) (t : B -> Prop) (f : A -> B) (y : A) (s : A -> Prop) (x : A) (h1 : term195 A B u s t f x) (h2 : term289 A B f y s x) : term348 A B y t f x.
Proof. exact (conj (@lem5051011 A B f y s x h2) (@lem5051043 A B u s t f x h1)). Qed.
Lemma lem5051155 {B : Type'} (_64925 : B) (t : B -> Prop) (_64926 : B) : term347 B _64925 t _64926.
Proof. exact (EQ_MP (@lem5051151 B _64925 t _64926) (@lem5051130 B _64926 t _64925)). Qed.
Lemma lem5051156 {B : Type'} (_64925 : B) (t : B -> Prop) (_64926 : B) : term347 B _64925 t _64926.
Proof. exact (@lem5051155 B _64925 t _64926). Qed.
Lemma lem5051157 {A B : Type'} (x : A) (t : B -> Prop) (f : A -> B) (y : A) : term349 A B x t f y.
Proof. exact (@lem5051156 B (f x) t (f y)). Qed.
Lemma lem5051160 {A B : Type'} (u : B -> Prop) (t : B -> Prop) (f : A -> B) (y : A) (s : A -> Prop) (x : A) (h1 : term195 A B u s t f x) (h2 : term289 A B f y s x) : term100 A B t f y.
Proof. exact (@lem5051157 A B x t f y (@lem5051153 A B u t f y s x h1 h2)). Qed.
Lemma lem5051161 {A B : Type'} (u : B -> Prop) (t : B -> Prop) (f : A -> B) (y : A) (s : A -> Prop) (x : A) (h1 : term195 A B u s t f x) (h2 : term289 A B f y s x) : term258 A B t f y.
Proof. exact (fun h0 : term138 A B t f y => @lem5051160 A B u t f y s x h1 h2). Qed.
Lemma lem5051163 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5051164 {A B : Type'} (t : B -> Prop) (f : A -> B) (y : A) : (term258 A B t f y) = (term100 A B t f y).
Proof. exact (@lem5051163 (term100 A B t f y)). Qed.
Lemma lem5051165 {A B : Type'} (u : B -> Prop) (t : B -> Prop) (f : A -> B) (y : A) (s : A -> Prop) (x : A) (h1 : term195 A B u s t f x) (h2 : term289 A B f y s x) : term100 A B t f y.
Proof. exact (EQ_MP (@lem5051164 A B t f y) (@lem5051161 A B u t f y s x h1 h2)). Qed.
Lemma lem5051181 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5051182 {A B : Type'} (x : A) (t : B -> Prop) (f : A -> B) (_64908 : A) : (term350 A B t f _64908 x) = (term351 A B x t f _64908).
Proof. exact (@lem5051181 (_64908 = x) (term138 A B t f _64908)). Qed.
Lemma lem5051190 {A : Type'} (s : A -> Prop) (_64908 : A) : (term352 A s _64908) = (term352 A s _64908).
Proof. exact (eq_refl (term352 A s _64908)). Qed.
Lemma lem5051191 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (f : A -> B) (_64908 : A) : (term320 A B s t f _64908 x) = (term353 A B s x t f _64908).
Proof. exact (MK_COMB (@lem5051190 A s _64908) (@lem5051182 A B x t f _64908)). Qed.
Lemma lem5051195 (q : Prop) (p : Prop) (r : Prop) : (term278 p q r) = (term278 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5051196 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (_64908 : A) : (term353 A B s x t f _64908) = (term354 A B x s t f _64908).
Proof. exact (@lem5051195 (_64908 = x) (term240 A s _64908) (term138 A B t f _64908)). Qed.
Lemma lem5051214 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (_64908 : A) : (term320 A B s t f _64908 x) = (term354 A B x s t f _64908).
Proof. exact (TRANS (@lem5051191 A B s x t f _64908) (@lem5051196 A B x s t f _64908)). Qed.
Lemma lem5051215 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5051216 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (_64908 : A) : (term355 A B s t f _64908 x) = (term356 A B x s t f _64908).
Proof. exact (MK_COMB (@lem5051215) (@lem5051214 A B x s t f _64908)). Qed.
Lemma lem5051234 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (_64908 : A) : (term354 A B x s t f _64908) = (term354 A B x s t f _64908).
Proof. exact (eq_refl (term354 A B x s t f _64908)). Qed.
Lemma lem5051235 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (_64908 : A) : ((term320 A B s t f _64908 x) = (term354 A B x s t f _64908)) = ((term354 A B x s t f _64908) = (term354 A B x s t f _64908)).
Proof. exact (MK_COMB (@lem5051216 A B x s t f _64908) (@lem5051234 A B x s t f _64908)). Qed.
Lemma lem5051237 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5051238 (x : Prop) : (x = x) = True.
Proof. exact (@lem5051237 Prop x). Qed.
Lemma lem5051239 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (_64908 : A) : ((term354 A B x s t f _64908) = (term354 A B x s t f _64908)) = True.
Proof. exact (@lem5051238 (term354 A B x s t f _64908)). Qed.
Lemma lem5051240 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (_64908 : A) : ((term320 A B s t f _64908 x) = (term354 A B x s t f _64908)) = True.
Proof. exact (TRANS (@lem5051235 A B x s t f _64908) (@lem5051239 A B x s t f _64908)). Qed.
Lemma lem5051241 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (_64908 : A) : True = ((term320 A B s t f _64908 x) = (term354 A B x s t f _64908)).
Proof. exact (SYM (@lem5051240 A B x s t f _64908)). Qed.
Lemma lem5051242 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (_64908 : A) : (term320 A B s t f _64908 x) = (term354 A B x s t f _64908).
Proof. exact (EQ_MP (@lem5051241 A B x s t f _64908) (@lem0)). Qed.
Lemma lem5051243 {A B : Type'} (_64908 : A) (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term195 A B u s t f x) : term354 A B x s t f _64908.
Proof. exact (EQ_MP (@lem5051242 A B x s t f _64908) (@lem5050807 A B _64908 u s t f x h1)). Qed.
Lemma lem5051245 (b : Prop) (a : Prop) : (a \/ b) = (term252 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5051246 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (_64908 : A) (x : A) : (term354 A B x s t f _64908) = (term357 A B s t f _64908 x).
Proof. exact (@lem5051245 (term154 A B s t f _64908) (_64908 = x)). Qed.
Lemma lem5051248 (a : Prop) (b : Prop) : (term338 a b) = (term339 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5051249 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (_64908 : A) : (term358 A B s t f _64908) = (term359 A B s t f _64908).
Proof. exact (@lem5051248 (term240 A s _64908) (term138 A B t f _64908)). Qed.
Lemma lem5051251 (a : Prop) : (term120 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5051252 {A : Type'} (s : A -> Prop) (_64908 : A) : (term263 A s _64908) = (s _64908).
Proof. exact (@lem5051251 (s _64908)). Qed.
Lemma lem5051253 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5051254 {A : Type'} (s : A -> Prop) (_64908 : A) : (term360 A s _64908) = (term99 A s _64908).
Proof. exact (MK_COMB (@lem5051253) (@lem5051252 A s _64908)). Qed.
Lemma lem5051256 (a : Prop) : (term120 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5051257 {A B : Type'} (t : B -> Prop) (f : A -> B) (_64908 : A) : (term361 A B t f _64908) = (term100 A B t f _64908).
Proof. exact (@lem5051256 (term100 A B t f _64908)). Qed.
Lemma lem5051258 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (_64908 : A) : (term359 A B s t f _64908) = (term101 A B s t f _64908).
Proof. exact (MK_COMB (@lem5051254 A s _64908) (@lem5051257 A B t f _64908)). Qed.
Lemma lem5051259 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (_64908 : A) : (term358 A B s t f _64908) = (term101 A B s t f _64908).
Proof. exact (TRANS (@lem5051249 A B s t f _64908) (@lem5051258 A B s t f _64908)). Qed.
Lemma lem5051260 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5051261 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (_64908 : A) : (term362 A B s t f _64908) = (term363 A B s t f _64908).
Proof. exact (MK_COMB (@lem5051260) (@lem5051259 A B s t f _64908)). Qed.
Lemma lem5051262 {A : Type'} (_64908 : A) (x : A) : (_64908 = x) = (_64908 = x).
Proof. exact (eq_refl (_64908 = x)). Qed.
Lemma lem5051263 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (_64908 : A) (x : A) : (term357 A B s t f _64908 x) = (term364 A B s t f _64908 x).
Proof. exact (MK_COMB (@lem5051261 A B s t f _64908) (@lem5051262 A _64908 x)). Qed.
Lemma lem5051264 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (_64908 : A) (x : A) : (term354 A B x s t f _64908) = (term364 A B s t f _64908 x).
Proof. exact (TRANS (@lem5051246 A B s t f _64908 x) (@lem5051263 A B s t f _64908 x)). Qed.
Lemma lem5051266 {A B : Type'} (u : B -> Prop) (t : B -> Prop) (f : A -> B) (y : A) (s : A -> Prop) (x : A) (h1 : term195 A B u s t f x) (h2 : term289 A B f y s x) : term101 A B s t f y.
Proof. exact (conj (@lem5051004 A B f y s x h2) (@lem5051165 A B u t f y s x h1 h2)). Qed.
Lemma lem5051268 {A B : Type'} (_64908 : A) (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term195 A B u s t f x) : term364 A B s t f _64908 x.
Proof. exact (EQ_MP (@lem5051264 A B s t f _64908 x) (@lem5051243 A B _64908 u s t f x h1)). Qed.
Lemma lem5051269 {A B : Type'} (_64908 : A) (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term195 A B u s t f x) : term364 A B s t f _64908 x.
Proof. exact (@lem5051268 A B _64908 u s t f x h1). Qed.
Lemma lem5051270 {A B : Type'} (y : A) (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term195 A B u s t f x) : term364 A B s t f y x.
Proof. exact (@lem5051269 A B y u s t f x h1). Qed.
Lemma lem5051273 {A B : Type'} (u : B -> Prop) (t : B -> Prop) (f : A -> B) (y : A) (s : A -> Prop) (x : A) (h1 : term195 A B u s t f x) (h2 : term289 A B f y s x) : y = x.
Proof. exact (@lem5051270 A B y u s t f x h1 (@lem5051266 A B u t f y s x h1 h2)). Qed.
Lemma lem5051274 {A B : Type'} (u : B -> Prop) (t : B -> Prop) (f : A -> B) (y : A) (s : A -> Prop) (x : A) (h1 : term195 A B u s t f x) (h2 : term289 A B f y s x) : term365 A y x.
Proof. exact (fun h0 : term235 A y x => @lem5051273 A B u t f y s x h1 h2). Qed.
Lemma lem5051276 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5051277 {A : Type'} (y : A) (x : A) : (term365 A y x) = (y = x).
Proof. exact (@lem5051276 (y = x)). Qed.
Lemma lem5051278 {A B : Type'} (u : B -> Prop) (t : B -> Prop) (f : A -> B) (y : A) (s : A -> Prop) (x : A) (h1 : term195 A B u s t f x) (h2 : term289 A B f y s x) : y = x.
Proof. exact (EQ_MP (@lem5051277 A y x) (@lem5051274 A B u t f y s x h1 h2)). Qed.
Lemma lem5051280 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem5051281 {A : Type'} (x : A) : x = x.
Proof. exact (@lem5051280 A x). Qed.
Lemma lem5051282 {A : Type'} (y : A) : y = y.
Proof. exact (@lem5051281 A y). Qed.
Lemma lem5051283 {A : Type'} (y : A) : term250 A y.
Proof. exact (fun h0 : term251 A y => @lem5051282 A y). Qed.
Lemma lem5051285 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5051286 {A : Type'} (y : A) : (term250 A y) = (y = y).
Proof. exact (@lem5051285 (y = y)). Qed.
Lemma lem5051287 {A : Type'} (y : A) : y = y.
Proof. exact (EQ_MP (@lem5051286 A y) (@lem5051283 A y)). Qed.
Lemma lem5051305 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5051306 {A : Type'} (y : A) (x : A) (z : A) : (term366 A x y z) = (term367 A y x z).
Proof. exact (@lem5051305 (y = z) (term235 A x z)). Qed.
Lemma lem5051316 {A : Type'} (x : A) (y : A) : (term368 A x y) = (term368 A x y).
Proof. exact (eq_refl (term368 A x y)). Qed.
Lemma lem5051317 {A : Type'} (y : A) (x : A) (z : A) : (term327 A x y z) = (term369 A y x z).
Proof. exact (MK_COMB (@lem5051316 A x y) (@lem5051306 A y x z)). Qed.
Lemma lem5051321 (q : Prop) (p : Prop) (r : Prop) : (term278 p q r) = (term278 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5051322 {A : Type'} (y : A) (x : A) (z : A) : (term369 A y x z) = (term370 A y x z).
Proof. exact (@lem5051321 (y = z) (term235 A x y) (term235 A x z)). Qed.
Lemma lem5051344 {A : Type'} (y : A) (x : A) (z : A) : (term327 A x y z) = (term370 A y x z).
Proof. exact (TRANS (@lem5051317 A y x z) (@lem5051322 A y x z)). Qed.
Lemma lem5051345 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5051346 {A : Type'} (y : A) (x : A) (z : A) : (term371 A x y z) = (term372 A y x z).
Proof. exact (MK_COMB (@lem5051345) (@lem5051344 A y x z)). Qed.
Lemma lem5051368 {A : Type'} (y : A) (x : A) (z : A) : (term370 A y x z) = (term370 A y x z).
Proof. exact (eq_refl (term370 A y x z)). Qed.
Lemma lem5051369 {A : Type'} (y : A) (x : A) (z : A) : ((term327 A x y z) = (term370 A y x z)) = ((term370 A y x z) = (term370 A y x z)).
Proof. exact (MK_COMB (@lem5051346 A y x z) (@lem5051368 A y x z)). Qed.
Lemma lem5051371 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5051372 (x : Prop) : (x = x) = True.
Proof. exact (@lem5051371 Prop x). Qed.
Lemma lem5051373 {A : Type'} (y : A) (x : A) (z : A) : ((term370 A y x z) = (term370 A y x z)) = True.
Proof. exact (@lem5051372 (term370 A y x z)). Qed.
Lemma lem5051374 {A : Type'} (y : A) (x : A) (z : A) : ((term327 A x y z) = (term370 A y x z)) = True.
Proof. exact (TRANS (@lem5051369 A y x z) (@lem5051373 A y x z)). Qed.
Lemma lem5051375 {A : Type'} (y : A) (x : A) (z : A) : True = ((term327 A x y z) = (term370 A y x z)).
Proof. exact (SYM (@lem5051374 A y x z)). Qed.
Lemma lem5051376 {A : Type'} (y : A) (x : A) (z : A) : (term327 A x y z) = (term370 A y x z).
Proof. exact (EQ_MP (@lem5051375 A y x z) (@lem0)). Qed.
Lemma lem5051377 {A : Type'} (y : A) (x : A) (z : A) : term370 A y x z.
Proof. exact (EQ_MP (@lem5051376 A y x z) (@lem5050997 A x y z)). Qed.
Lemma lem5051379 (b : Prop) (a : Prop) : (a \/ b) = (term252 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5051380 {A : Type'} (x : A) (y : A) (z : A) : (term370 A y x z) = (term373 A x y z).
Proof. exact (@lem5051379 (term374 A y x z) (y = z)). Qed.
Lemma lem5051382 (a : Prop) (b : Prop) : (term338 a b) = (term339 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5051383 {A : Type'} (y : A) (x : A) (z : A) : (term375 A y x z) = (term376 A y x z).
Proof. exact (@lem5051382 (term235 A x y) (term235 A x z)). Qed.
Lemma lem5051385 (a : Prop) : (term120 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5051386 {A : Type'} (x : A) (y : A) : (term254 A x y) = (x = y).
Proof. exact (@lem5051385 (x = y)). Qed.
Lemma lem5051387 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5051388 {A : Type'} (x : A) (y : A) : (term342 A x y) = (term343 A x y).
Proof. exact (MK_COMB (@lem5051387) (@lem5051386 A x y)). Qed.
Lemma lem5051390 (a : Prop) : (term120 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5051391 {A : Type'} (x : A) (z : A) : (term254 A x z) = (x = z).
Proof. exact (@lem5051390 (x = z)). Qed.
Lemma lem5051392 {A : Type'} (y : A) (x : A) (z : A) : (term376 A y x z) = (term377 A y x z).
Proof. exact (MK_COMB (@lem5051388 A x y) (@lem5051391 A x z)). Qed.
Lemma lem5051393 {A : Type'} (y : A) (x : A) (z : A) : (term375 A y x z) = (term377 A y x z).
Proof. exact (TRANS (@lem5051383 A y x z) (@lem5051392 A y x z)). Qed.
Lemma lem5051394 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5051395 {A : Type'} (y : A) (x : A) (z : A) : (term378 A y x z) = (term379 A y x z).
Proof. exact (MK_COMB (@lem5051394) (@lem5051393 A y x z)). Qed.
Lemma lem5051396 {A : Type'} (y : A) (z : A) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem5051397 {A : Type'} (x : A) (y : A) (z : A) : (term373 A x y z) = (term380 A x y z).
Proof. exact (MK_COMB (@lem5051395 A y x z) (@lem5051396 A y z)). Qed.
Lemma lem5051398 {A : Type'} (x : A) (y : A) (z : A) : (term370 A y x z) = (term380 A x y z).
Proof. exact (TRANS (@lem5051380 A x y z) (@lem5051397 A x y z)). Qed.
Lemma lem5051400 {A B : Type'} (u : B -> Prop) (t : B -> Prop) (f : A -> B) (y : A) (s : A -> Prop) (x : A) (h1 : term195 A B u s t f x) (h2 : term289 A B f y s x) : term381 A x y.
Proof. exact (conj (@lem5051278 A B u t f y s x h1 h2) (@lem5051287 A y)). Qed.
Lemma lem5051402 {A : Type'} (x : A) (y : A) (z : A) : term380 A x y z.
Proof. exact (EQ_MP (@lem5051398 A x y z) (@lem5051377 A y x z)). Qed.
Lemma lem5051403 {A : Type'} (x : A) (y : A) (z : A) : term380 A x y z.
Proof. exact (@lem5051402 A x y z). Qed.
Lemma lem5051404 {A : Type'} (x : A) (y : A) : term382 A x y.
Proof. exact (@lem5051403 A y x y). Qed.
Lemma lem5051407 {A B : Type'} (u : B -> Prop) (t : B -> Prop) (f : A -> B) (y : A) (s : A -> Prop) (x : A) (h1 : term195 A B u s t f x) (h2 : term289 A B f y s x) : x = y.
Proof. exact (@lem5051404 A x y (@lem5051400 A B u t f y s x h1 h2)). Qed.
Lemma lem5051408 {A B : Type'} (u : B -> Prop) (t : B -> Prop) (f : A -> B) (y : A) (s : A -> Prop) (x : A) (h1 : term195 A B u s t f x) (h2 : term289 A B f y s x) : term365 A x y.
Proof. exact (fun h0 : term235 A x y => @lem5051407 A B u t f y s x h1 h2). Qed.
Lemma lem5051410 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5051411 {A : Type'} (x : A) (y : A) : (term365 A x y) = (x = y).
Proof. exact (@lem5051410 (x = y)). Qed.
Lemma lem5051412 {A B : Type'} (u : B -> Prop) (t : B -> Prop) (f : A -> B) (y : A) (s : A -> Prop) (x : A) (h1 : term195 A B u s t f x) (h2 : term289 A B f y s x) : x = y.
Proof. exact (EQ_MP (@lem5051411 A x y) (@lem5051408 A B u t f y s x h1 h2)). Qed.
Lemma lem5051415 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5051417 {A : Type'} (x : A) (y : A) : (term235 A x y) = (term383 A x y).
Proof. exact (@lem5051415 (x = y)). Qed.
Lemma lem5051420 {A : Type'} (x : A) (y : A) (h1 : term235 A x y) : term383 A x y.
Proof. exact (EQ_MP (@lem5051417 A x y) (@lem5050783 A x y h1)). Qed.
Lemma lem5051423 {A B : Type'} (u : B -> Prop) (t : B -> Prop) (f : A -> B) (y : A) (s : A -> Prop) (x : A) (h1 : term235 A x y) (h2 : term195 A B u s t f x) (h3 : term289 A B f y s x) : False.
Proof. exact (@lem5051420 A x y h1 (@lem5051412 A B u t f y s x h2 h3)). Qed.
Lemma lem5051424 {A B : Type'} (u : B -> Prop) (t : B -> Prop) (f : A -> B) (y : A) (s : A -> Prop) (x : A) (h1 : term235 A x y) (h2 : term195 A B u s t f x) (h3 : term289 A B f y s x) : term249.
Proof. exact (fun h0 : ~ False => @lem5051423 A B u t f y s x h1 h2 h3). Qed.
Lemma lem5051426 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5051427 : term249 = False.
Proof. exact (@lem5051426 False). Qed.
Lemma lem5051428 {A B : Type'} (u : B -> Prop) (t : B -> Prop) (f : A -> B) (y : A) (s : A -> Prop) (x : A) (h1 : term235 A x y) (h2 : term195 A B u s t f x) (h3 : term289 A B f y s x) : False.
Proof. exact (EQ_MP (@lem5051427) (@lem5051424 A B u t f y s x h1 h2 h3)). Qed.
Lemma lem5051429 {A B : Type'} (x' : A) (f : A -> B) (y : A) (s : A -> Prop) (x : A) (h1 : term140 A x s x') (h2 : term289 A B f y s x) : False.
Proof. exact (EQ_MP (@lem5050948) (@lem5050945 A B x' f y s x h1 h2)). Qed.
Lemma lem5051430 {A B : Type'} (u : B -> Prop) (t : B -> Prop) (f : A -> B) (y : A) (s : A -> Prop) (x : A) (h1 : term235 A x y) (h2 : term195 A B u s t f x) (h3 : term289 A B f y s x) : (term235 A x y) = False.
Proof. exact (prop_ext (fun h4 : term235 A x y => @lem5051428 A B u t f y s x h1 h2 h3) (fun h4 : False => @lem5050783 A x y h1)). Qed.
Lemma lem5051431 {A B : Type'} (u : B -> Prop) (t : B -> Prop) (f : A -> B) (y : A) (s : A -> Prop) (x : A) (h1 : term235 A x y) (h2 : term195 A B u s t f x) (h3 : term289 A B f y s x) : False.
Proof. exact (EQ_MP (@lem5051430 A B u t f y s x h1 h2 h3) (@lem5050783 A x y h1)). Qed.
Lemma lem5051432 {A B : Type'} (u : B -> Prop) (t : B -> Prop) (f : A -> B) (y : A) (s : A -> Prop) (x : A) (h1 : term235 A x y) (h2 : term195 A B u s t f x) (h3 : term289 A B f y s x) : (term235 A x y) = False.
Proof. exact (prop_ext (fun h4 : term235 A x y => @lem5051431 A B u t f y s x h1 h2 h3) (fun h4 : False => @lem5050691 A x y h1)). Qed.
Lemma lem5051433 {A B : Type'} (u : B -> Prop) (t : B -> Prop) (f : A -> B) (y : A) (s : A -> Prop) (x : A) (h1 : term235 A x y) (h2 : term195 A B u s t f x) (h3 : term289 A B f y s x) : False.
Proof. exact (EQ_MP (@lem5051432 A B u t f y s x h1 h2 h3) (@lem5050691 A x y h1)). Qed.
Lemma lem5051434 {A B : Type'} (u : B -> Prop) (t : B -> Prop) (f : A -> B) (y : A) (s : A -> Prop) (x : A) (h1 : term235 A x y) (h2 : term195 A B u s t f x) (h3 : term289 A B f y s x) : (term235 A x y) = False.
Proof. exact (prop_ext (fun h4 : term235 A x y => @lem5051433 A B u t f y s x h1 h2 h3) (fun h4 : False => @lem5050691 A x y h1)). Qed.
Lemma lem5051435 {A B : Type'} (u : B -> Prop) (t : B -> Prop) (f : A -> B) (y : A) (s : A -> Prop) (x : A) (h1 : term235 A x y) (h2 : term195 A B u s t f x) (h3 : term289 A B f y s x) : False.
Proof. exact (EQ_MP (@lem5051434 A B u t f y s x h1 h2 h3) (@lem5050691 A x y h1)). Qed.
Lemma lem5051436 {A B : Type'} (y : A) (x' : A) (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term235 A x y) (h2 : term289 A B f y s x) (h3 : term228 A B x' u s t f x) : False.
Proof. exact (or_elim (@lem5050651 A B x' u s t f x h3) (fun h0 : term140 A x s x' => @lem5051429 A B x' f y s x h0 h2) (fun h0 : term195 A B u s t f x => @lem5051435 A B u t f y s x h1 h0 h2)). Qed.
Lemma lem5051437 {A B : Type'} (y : A) (x' : A) (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term235 A x y) (h2 : term289 A B f y s x) (h3 : term228 A B x' u s t f x) : (term228 A B x' u s t f x) = False.
Proof. exact (prop_ext (fun h4 : term228 A B x' u s t f x => @lem5051436 A B y x' u s t f x h1 h2 h3) (fun h4 : False => @lem5050651 A B x' u s t f x h3)). Qed.
Lemma lem5051438 {A B : Type'} (y : A) (x' : A) (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term235 A x y) (h2 : term289 A B f y s x) (h3 : term228 A B x' u s t f x) : False.
Proof. exact (EQ_MP (@lem5051437 A B y x' u s t f x h1 h2 h3) (@lem5050651 A B x' u s t f x h3)). Qed.
Lemma lem5051439 {A B : Type'} (y : A) (x' : A) (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term235 A x y) (h2 : term289 A B f y s x) (h3 : term228 A B x' u s t f x) : (term235 A x y) = False.
Proof. exact (prop_ext (fun h4 : term235 A x y => @lem5051438 A B y x' u s t f x h1 h2 h3) (fun h4 : False => @lem5050564 A x y h1)). Qed.
Lemma lem5051440 {A B : Type'} (y : A) (x' : A) (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term235 A x y) (h2 : term289 A B f y s x) (h3 : term228 A B x' u s t f x) : False.
Proof. exact (EQ_MP (@lem5051439 A B y x' u s t f x h1 h2 h3) (@lem5050564 A x y h1)). Qed.
Lemma lem5051441 {A B : Type'} (y : A) (x' : A) (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term235 A x y) (h2 : term289 A B f y s x) (h3 : term228 A B x' u s t f x) : (term289 A B f y s x) = False.
Proof. exact (prop_ext (fun h4 : term289 A B f y s x => @lem5051440 A B y x' u s t f x h1 h2 h3) (fun h4 : False => @lem5050556 A B f y s x h2)). Qed.
Lemma lem5051442 {A B : Type'} (y : A) (x' : A) (u : B -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term235 A x y) (h2 : term289 A B f y s x) (h3 : term228 A B x' u s t f x) : False.
Proof. exact (EQ_MP (@lem5051441 A B y x' u s t f x h1 h2 h3) (@lem5050556 A B f y s x h2)). Qed.
Lemma lem5051443 {A B : Type'} (x' : A) (u : B -> Prop) (f : A -> B) (y : A) (s : A -> Prop) (x : A) (h1 : term231 A B x' u s f x) (h2 : term235 A x y) (h3 : term289 A B f y s x) : False.
Proof. exact (ex_elim (@lem5050533 A B x' u s f x h1) (fun t : B -> Prop => fun h0 : term230 A B x' u s f x t => @lem5051442 A B y x' u s t f x h2 h3 h0)). Qed.
Lemma lem5051444 {A B : Type'} (y : A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term235 A x y) (h2 : term289 A B f y s x) (h3 : term109 A B u s f x) : False.
Proof. exact (ex_elim (@lem5050526 A B u s f x h3) (fun x' : A => fun h0 : term232 A B u s f x x' => @lem5051443 A B x' u f y s x h0 h1 h2)). Qed.
Lemma lem5051445 {A B : Type'} (y : A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term235 A x y) (h2 : term289 A B f y s x) (h3 : term109 A B u s f x) : (term235 A x y) = False.
Proof. exact (prop_ext (fun h4 : term235 A x y => @lem5051444 A B y u s f x h1 h2 h3) (fun h4 : False => @lem5050532 A x y h1)). Qed.
Lemma lem5051446 {A B : Type'} (y : A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term235 A x y) (h2 : term289 A B f y s x) (h3 : term109 A B u s f x) : False.
Proof. exact (EQ_MP (@lem5051445 A B y u s f x h1 h2 h3) (@lem5050532 A x y h1)). Qed.
Lemma lem5051447 {A B : Type'} (y : A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term235 A x y) (h2 : term289 A B f y s x) (h3 : term109 A B u s f x) : (term289 A B f y s x) = False.
Proof. exact (prop_ext (fun h4 : term289 A B f y s x => @lem5051446 A B y u s f x h1 h2 h3) (fun h4 : False => @lem5050101 A B f y s x h2)). Qed.
Lemma lem5051448 {A B : Type'} (y : A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term235 A x y) (h2 : term289 A B f y s x) (h3 : term109 A B u s f x) : False.
Proof. exact (EQ_MP (@lem5051447 A B y u s f x h1 h2 h3) (@lem5050101 A B f y s x h2)). Qed.
Lemma lem5051449 {A B : Type'} (y : A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term235 A x y) (h2 : term289 A B f y s x) (h3 : term109 A B u s f x) : (term235 A x y) = False.
Proof. exact (prop_ext (fun h4 : term235 A x y => @lem5051448 A B y u s f x h1 h2 h3) (fun h4 : False => @lem5050087 A x y h1)). Qed.
Lemma lem5051450 {A B : Type'} (y : A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term235 A x y) (h2 : term289 A B f y s x) (h3 : term109 A B u s f x) : False.
Proof. exact (EQ_MP (@lem5051449 A B y u s f x h1 h2 h3) (@lem5050087 A x y h1)). Qed.
Lemma lem5051451 {A B : Type'} (y : A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term289 A B f y s x) (h2 : term109 A B u s f x) : term319 A x y.
Proof. exact (fun h0 : term235 A x y => @lem5051450 A B y u s f x h0 h1 h2). Qed.
Lemma lem5051452 {A B : Type'} (y : A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term289 A B f y s x) (h2 : term109 A B u s f x) : x = y.
Proof. exact (EQ_MP (@lem5050086 A x y) (@lem5051451 A B y u s f x h1 h2)). Qed.
Lemma lem5051453 {A B : Type'} (u : B -> Prop) (f : A -> B) (y : A) (s : A -> Prop) (x : A) (h1 : term289 A B f y s x) : term291 A B u s f x y.
Proof. exact (fun h0 : term109 A B u s f x => @lem5051452 A B y u s f x h1 h0). Qed.
Lemma lem5051454 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (y : A) : term292 A B u s f x y.
Proof. exact (fun h0 : term289 A B f y s x => @lem5051453 A B u f y s x h0). Qed.
Lemma lem5051459 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : term302 A B s f x y.
Proof. exact (fun u : B -> Prop => @lem5051454 A B u s f x y). Qed.
Lemma lem5051464 {A B : Type'} (f : A -> B) (x : A) (y : A) : term306 A B f x y.
Proof. exact (fun s : A -> Prop => @lem5051459 A B s f x y). Qed.
Lemma lem5051469 {A B : Type'} (x : A) (y : A) : term310 A B x y.
Proof. exact (fun f : A -> B => @lem5051464 A B f x y). Qed.
Lemma lem5051474 {A B : Type'} (y : A) : term314 A B y.
Proof. exact (fun x : A => @lem5051469 A B x y). Qed.
Lemma lem5051479 {A B : Type'} : term318 A B.
Proof. exact (fun y : A => @lem5051474 A B y). Qed.
Lemma lem5051480 {A B : Type'} : term317 A B.
Proof. exact (EQ_MP (@lem5050080 A B) (@lem5051479 A B)). Qed.
Lemma lem5051481 {A B : Type'} (y : A) : term384 A B y.
Proof. exact (@lem5051480 A B y). Qed.
Lemma lem5051482 {A B : Type'} (y : A) : (term384 A B y) = (term313 A B y).
Proof. exact (eq_refl (term384 A B y)). Qed.
Lemma lem5051483 {A B : Type'} (y : A) : term313 A B y.
Proof. exact (EQ_MP (@lem5051482 A B y) (@lem5051481 A B y)). Qed.
Lemma lem5051484 {A B : Type'} (y : A) (x : A) : term385 A B y x.
Proof. exact (@lem5051483 A B y x). Qed.
Lemma lem5051485 {A B : Type'} (x : A) (y : A) : (term385 A B y x) = (term309 A B x y).
Proof. exact (eq_refl (term385 A B y x)). Qed.
Lemma lem5051486 {A B : Type'} (x : A) (y : A) : term309 A B x y.
Proof. exact (EQ_MP (@lem5051485 A B x y) (@lem5051484 A B y x)). Qed.
Lemma lem5051487 {A B : Type'} (x : A) (y : A) (f : A -> B) : term386 A B x y f.
Proof. exact (@lem5051486 A B x y f). Qed.
Lemma lem5051488 {A B : Type'} (f : A -> B) (x : A) (y : A) : (term386 A B x y f) = (term305 A B f x y).
Proof. exact (eq_refl (term386 A B x y f)). Qed.
Lemma lem5051489 {A B : Type'} (f : A -> B) (x : A) (y : A) : term305 A B f x y.
Proof. exact (EQ_MP (@lem5051488 A B f x y) (@lem5051487 A B x y f)). Qed.
Lemma lem5051490 {A B : Type'} (f : A -> B) (x : A) (y : A) (s : A -> Prop) : term387 A B f x y s.
Proof. exact (@lem5051489 A B f x y s). Qed.
Lemma lem5051491 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term387 A B f x y s) = (term301 A B s f x y).
Proof. exact (eq_refl (term387 A B f x y s)). Qed.
Lemma lem5051492 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : term301 A B s f x y.
Proof. exact (EQ_MP (@lem5051491 A B s f x y) (@lem5051490 A B f x y s)). Qed.
Lemma lem5051493 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) (u : B -> Prop) : term388 A B s f x y u.
Proof. exact (@lem5051492 A B s f x y u). Qed.
Lemma lem5051494 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term388 A B s f x y u) = (term293 A B u s f x y).
Proof. exact (eq_refl (term388 A B s f x y u)). Qed.
Lemma lem5051495 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (y : A) : term293 A B u s f x y.
Proof. exact (EQ_MP (@lem5051494 A B u s f x y) (@lem5051493 A B s f x y u)). Qed.
Lemma lem5051497 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (y : A) : term293 A B u s f x y.
Proof. exact (@lem5049792 A B u s f x y (@lem5051495 A B u s f x y)). Qed.
Lemma lem5051498 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term294 A B u s f x y) : False.
Proof. exact (@lem5051497 A B u s f x y (@lem5049776 A B u s f x y h1)). Qed.
Lemma lem5051499 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term294 A B u s f x y) : (term294 A B u s f x y) = False.
Proof. exact (prop_ext (fun h2 : term294 A B u s f x y => @lem5051498 A B u s f x y h1) (fun h2 : False => @lem5049776 A B u s f x y h1)). Qed.
Lemma lem5051500 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term294 A B u s f x y) : False.
Proof. exact (EQ_MP (@lem5051499 A B u s f x y h1) (@lem5049776 A B u s f x y h1)). Qed.
Lemma lem5051501 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (y : A) : term293 A B u s f x y.
Proof. exact (fun h0 : term294 A B u s f x y => @lem5051500 A B u s f x y h0). Qed.
Lemma lem5051502 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (y : A) : term292 A B u s f x y.
Proof. exact (EQ_MP (@lem5049775 A B u s f x y) (@lem5051501 A B u s f x y)). Qed.
Lemma lem5051503 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (y : A) : term286 A B u s f x y.
Proof. exact (EQ_MP (@lem5049771 A B u s f x y) (@lem5051502 A B u s f x y)). Qed.
Lemma lem5051504 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (y : A) : term285 A B u s f x y.
Proof. exact (EQ_MP (@lem5049557 A B u s f x y) (@lem5051503 A B u s f x y)). Qed.
Lemma lem5051505 {A B : Type'} (u : B -> Prop) (f : A -> B) (x : A) (y : A) (s : A -> Prop) (h1 : (f x) = (f y)) (h2 : @IN A x s) (h3 : @IN A y s) : term282 A B u s f x y.
Proof. exact (@lem5051504 A B u s f x y (@lem5049465 A B f x y s h1 h2 h3)). Qed.
Lemma lem5051506 {A B : Type'} (u : B -> Prop) (f : A -> B) (x : A) (y : A) (s : A -> Prop) (h1 : term9 A B u s f) (h2 : (f x) = (f y)) (h3 : @IN A x s) (h4 : @IN A y s) : x = y.
Proof. exact (@lem5051505 A B u f x y s h2 h3 h4 (@lem5049453 A B x u s f h1)). Qed.
Lemma lem5051507 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) (h1 : term271 A B s x f y) : term272 A B s x f y.
Proof. exact (proj2 (@lem5049446 A B s x f y h1)). Qed.
Lemma lem5051508 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) (h1 : term271 A B s x f y) : @IN A x s.
Proof. exact (proj1 (@lem5049446 A B s x f y h1)). Qed.
Lemma lem5051509 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) (h1 : term272 A B s x f y) : (f x) = (f y).
Proof. exact (proj2 (@lem5049447 A B s x f y h1)). Qed.
Lemma lem5051510 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) (h1 : term272 A B s x f y) : @IN A y s.
Proof. exact (proj1 (@lem5049447 A B s x f y h1)). Qed.
Lemma lem5051511 {A B : Type'} (u : B -> Prop) (f : A -> B) (x : A) (y : A) (s : A -> Prop) (h1 : term9 A B u s f) (h2 : (f x) = (f y)) (h3 : @IN A x s) (h4 : @IN A y s) : ((f x) = (f y)) = (x = y).
Proof. exact (prop_ext (fun h5 : (f x) = (f y) => @lem5051506 A B u f x y s h1 h2 h3 h4) (fun h5 : x = y => @lem5049449 A B x f y h2)). Qed.
Lemma lem5051512 {A B : Type'} (u : B -> Prop) (f : A -> B) (x : A) (y : A) (s : A -> Prop) (h1 : term9 A B u s f) (h2 : (f x) = (f y)) (h3 : @IN A x s) (h4 : @IN A y s) : x = y.
Proof. exact (EQ_MP (@lem5051511 A B u f x y s h1 h2 h3 h4) (@lem5049449 A B x f y h2)). Qed.
Lemma lem5051513 {A B : Type'} (u : B -> Prop) (f : A -> B) (x : A) (y : A) (s : A -> Prop) (h1 : term9 A B u s f) (h2 : (f x) = (f y)) (h3 : @IN A x s) (h4 : @IN A y s) : (@IN A y s) = (x = y).
Proof. exact (prop_ext (fun h5 : @IN A y s => @lem5051512 A B u f x y s h1 h2 h3 h4) (fun h5 : x = y => @lem5049450 A y s h4)). Qed.
Lemma lem5051514 {A B : Type'} (u : B -> Prop) (f : A -> B) (x : A) (y : A) (s : A -> Prop) (h1 : term9 A B u s f) (h2 : (f x) = (f y)) (h3 : @IN A x s) (h4 : @IN A y s) : x = y.
Proof. exact (EQ_MP (@lem5051513 A B u f x y s h1 h2 h3 h4) (@lem5049450 A y s h4)). Qed.
Lemma lem5051515 {A B : Type'} (u : B -> Prop) (f : A -> B) (x : A) (y : A) (s : A -> Prop) (h1 : term9 A B u s f) (h2 : term272 A B s x f y) (h3 : @IN A x s) (h4 : @IN A y s) : ((f x) = (f y)) = (x = y).
Proof. exact (prop_ext (fun h5 : (f x) = (f y) => @lem5051514 A B u f x y s h1 h5 h3 h4) (fun h5 : x = y => @lem5051509 A B s x f y h2)). Qed.
Lemma lem5051516 {A B : Type'} (u : B -> Prop) (f : A -> B) (x : A) (y : A) (s : A -> Prop) (h1 : term9 A B u s f) (h2 : term272 A B s x f y) (h3 : @IN A x s) (h4 : @IN A y s) : x = y.
Proof. exact (EQ_MP (@lem5051515 A B u f x y s h1 h2 h3 h4) (@lem5051509 A B s x f y h2)). Qed.
Lemma lem5051517 {A B : Type'} (u : B -> Prop) (f : A -> B) (y : A) (x : A) (s : A -> Prop) (h1 : term9 A B u s f) (h2 : term272 A B s x f y) (h3 : @IN A x s) : (@IN A y s) = (x = y).
Proof. exact (prop_ext (fun h4 : @IN A y s => @lem5051516 A B u f x y s h1 h2 h3 h4) (fun h4 : x = y => @lem5051510 A B s x f y h2)). Qed.
Lemma lem5051518 {A B : Type'} (u : B -> Prop) (f : A -> B) (y : A) (x : A) (s : A -> Prop) (h1 : term9 A B u s f) (h2 : term272 A B s x f y) (h3 : @IN A x s) : x = y.
Proof. exact (EQ_MP (@lem5051517 A B u f y x s h1 h2 h3) (@lem5051510 A B s x f y h2)). Qed.
Lemma lem5051519 {A B : Type'} (u : B -> Prop) (f : A -> B) (y : A) (x : A) (s : A -> Prop) (h1 : term9 A B u s f) (h2 : term272 A B s x f y) (h3 : @IN A x s) : (@IN A x s) = (x = y).
Proof. exact (prop_ext (fun h4 : @IN A x s => @lem5051518 A B u f y x s h1 h2 h3) (fun h4 : x = y => @lem5049448 A x s h3)). Qed.
Lemma lem5051520 {A B : Type'} (u : B -> Prop) (f : A -> B) (y : A) (x : A) (s : A -> Prop) (h1 : term9 A B u s f) (h2 : term272 A B s x f y) (h3 : @IN A x s) : x = y.
Proof. exact (EQ_MP (@lem5051519 A B u f y x s h1 h2 h3) (@lem5049448 A x s h3)). Qed.
Lemma lem5051521 {A B : Type'} (u : B -> Prop) (f : A -> B) (y : A) (x : A) (s : A -> Prop) (h1 : term9 A B u s f) (h2 : term271 A B s x f y) (h3 : @IN A x s) : (term272 A B s x f y) = (x = y).
Proof. exact (prop_ext (fun h4 : term272 A B s x f y => @lem5051520 A B u f y x s h1 h4 h3) (fun h4 : x = y => @lem5051507 A B s x f y h2)). Qed.
Lemma lem5051522 {A B : Type'} (u : B -> Prop) (f : A -> B) (y : A) (x : A) (s : A -> Prop) (h1 : term9 A B u s f) (h2 : term271 A B s x f y) (h3 : @IN A x s) : x = y.
Proof. exact (EQ_MP (@lem5051521 A B u f y x s h1 h2 h3) (@lem5051507 A B s x f y h2)). Qed.
Lemma lem5051523 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (x : A) (f : A -> B) (y : A) (h1 : term9 A B u s f) (h2 : term271 A B s x f y) : (@IN A x s) = (x = y).
Proof. exact (prop_ext (fun h3 : @IN A x s => @lem5051522 A B u f y x s h1 h2 h3) (fun h3 : x = y => @lem5051508 A B s x f y h2)). Qed.
Lemma lem5051524 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (x : A) (f : A -> B) (y : A) (h1 : term9 A B u s f) (h2 : term271 A B s x f y) : x = y.
Proof. exact (EQ_MP (@lem5051523 A B u s x f y h1 h2) (@lem5051508 A B s x f y h2)). Qed.
Lemma lem5051525 {A B : Type'} (x : A) (y : A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term9 A B u s f) : term389 A B s f x y.
Proof. exact (fun h0 : term271 A B s x f y => @lem5051524 A B u s x f y h1 h0). Qed.
Lemma lem5051530 {A B : Type'} (x : A) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term9 A B u s f) : term390 A B s f x.
Proof. exact (fun y : A => @lem5051525 A B x y u s f h1). Qed.
Lemma lem5051535 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term9 A B u s f) : term391 A B s f.
Proof. exact (fun x : A => @lem5051530 A B x u s f h1). Qed.
Lemma lem5051536 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term9 A B u s f) : term10 A B u s f.
Proof. exact (conj (@lem5049445 A B u s f h1) (@lem5051535 A B u s f h1)). Qed.
Lemma lem5051537 {A : Type'} (k : A -> Prop) (s : A -> Prop) (h1 : @SUBSET A k s) : @SUBSET A k s.
Proof. exact (h1). Qed.
Lemma lem5051538 (t1 : Prop) : term273 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem5051539 (t1 : Prop) : (term273 t1) = (term274 t1).
Proof. exact (eq_refl (term273 t1)). Qed.
Lemma lem5051540 (t1 : Prop) : term274 t1.
Proof. exact (EQ_MP (@lem5051539 t1) (@lem5051538 t1)). Qed.
Lemma lem5051541 (t1 : Prop) (t2 : Prop) : term275 t1 t2.
Proof. exact (@lem5051540 t1 t2). Qed.
Lemma lem5051542 (t1 : Prop) (t2 : Prop) : (term275 t1 t2) = (term276 t1 t2).
Proof. exact (eq_refl (term275 t1 t2)). Qed.
Lemma lem5051543 (t1 : Prop) (t2 : Prop) : term276 t1 t2.
Proof. exact (EQ_MP (@lem5051542 t1 t2) (@lem5051541 t1 t2)). Qed.
Lemma lem5051544 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term277 t1 t2 t3.
Proof. exact (@lem5051543 t1 t2 t3). Qed.
Lemma lem5051545 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term277 t1 t2 t3) = ((term278 t1 t2 t3) = (term279 t1 t2 t3)).
Proof. exact (eq_refl (term277 t1 t2 t3)). Qed.
Lemma lem5051546 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term278 t1 t2 t3) = (term279 t1 t2 t3).
Proof. exact (EQ_MP (@lem5051545 t1 t2 t3) (@lem5051544 t1 t2 t3)). Qed.
Lemma lem5051547 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term279 t1 t2 t3) = (term278 t1 t2 t3).
Proof. exact (SYM (@lem5051546 t1 t2 t3)). Qed.
Lemma lem5051548 {A B : Type'} (u : B -> Prop) (f : A -> B) (k : A -> Prop) (s : A -> Prop) (h1 : term10 A B u s f) (h2 : @SUBSET A k s) : term392 A B k u s f.
Proof. exact (conj (@lem5051537 A k s h2) (@lem5047853 A B u s f h1)). Qed.
Lemma lem5051554 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term8 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem5051555 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term8 A s t).
Proof. exact (@lem5051554 A s t). Qed.
Lemma lem5051556 {A : Type'} (k : A -> Prop) (s : A -> Prop) : (@SUBSET A k s) = (term8 A k s).
Proof. exact (@lem5051555 A k s). Qed.
Lemma lem5051563 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5051564 {A : Type'} (k : A -> Prop) (s : A -> Prop) : (term40 A k s) = (term41 A k s).
Proof. exact (MK_COMB (@lem5051563) (@lem5051556 A k s)). Qed.
Lemma lem5051568 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term8 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem5051569 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (@SUBSET B s t) = (term8 B s t).
Proof. exact (@lem5051568 B s t). Qed.
Lemma lem5051570 {A B : Type'} (f : A -> B) (s : A -> Prop) (u : B -> Prop) : (term11 A B f s u) = (term12 A B f s u).
Proof. exact (@lem5051569 B (@IMAGE A B f s) u). Qed.
Lemma lem5051577 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5051578 {A B : Type'} (f : A -> B) (s : A -> Prop) (u : B -> Prop) : (term393 A B f s u) = (term394 A B f s u).
Proof. exact (MK_COMB (@lem5051577) (@lem5051570 A B f s u)). Qed.
Lemma lem5051601 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term391 A B s f) = (term391 A B s f).
Proof. exact (eq_refl (term391 A B s f)). Qed.
Lemma lem5051602 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) : (term10 A B u s f) = (term395 A B u s f).
Proof. exact (MK_COMB (@lem5051578 A B f s u) (@lem5051601 A B s f)). Qed.
Lemma lem5051605 {A B : Type'} (k : A -> Prop) (u : B -> Prop) (s : A -> Prop) (f : A -> B) : (term392 A B k u s f) = (term396 A B k u s f).
Proof. exact (MK_COMB (@lem5051564 A k s) (@lem5051602 A B u s f)). Qed.
Lemma lem5051608 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5051609 {A B : Type'} (k : A -> Prop) (u : B -> Prop) (s : A -> Prop) (f : A -> B) : (term397 A B k u s f) = (term398 A B k u s f).
Proof. exact (MK_COMB (@lem5051608) (@lem5051605 A B k u s f)). Qed.
Lemma lem5051613 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term8 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem5051614 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (@SUBSET B s t) = (term8 B s t).
Proof. exact (@lem5051613 B s t). Qed.
Lemma lem5051615 {A B : Type'} (f : A -> B) (k : A -> Prop) (u : B -> Prop) : (term11 A B f k u) = (term12 A B f k u).
Proof. exact (@lem5051614 B (@IMAGE A B f k) u). Qed.
Lemma lem5051622 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5051623 {A B : Type'} (f : A -> B) (k : A -> Prop) (u : B -> Prop) : (term393 A B f k u) = (term394 A B f k u).
Proof. exact (MK_COMB (@lem5051622) (@lem5051615 A B f k u)). Qed.
Lemma lem5051627 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term42 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem5051628 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term42 A s t).
Proof. exact (@lem5051627 A s t). Qed.
Lemma lem5051629 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) : ((term399 A B s f k) = k) = (term400 A B s f k).
Proof. exact (@lem5051628 A (term399 A B s f k) k). Qed.
Lemma lem5051644 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term401 A B u s f k) = (term402 A B u s f k).
Proof. exact (MK_COMB (@lem5051623 A B f k u) (@lem5051629 A B s f k)). Qed.
Lemma lem5051647 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term403 A B u s f k) = (term404 A B u s f k).
Proof. exact (MK_COMB (@lem5051609 A B k u s f) (@lem5051644 A B u s f k)). Qed.
Lemma lem5051650 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term404 A B u s f k) = (term403 A B u s f k).
Proof. exact (SYM (@lem5051647 A B u s f k)). Qed.
Lemma lem5051662 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5051663 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5051662 A P x). Qed.
Lemma lem5051664 {A : Type'} (k : A -> Prop) (x : A) : (@IN A x k) = (k x).
Proof. exact (@lem5051663 A k x). Qed.
Lemma lem5051665 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5051666 {A : Type'} (k : A -> Prop) (x : A) : (term28 A x k) = (term58 A k x).
Proof. exact (MK_COMB (@lem5051665) (@lem5051664 A k x)). Qed.
Lemma lem5051668 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5051669 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5051668 A P x). Qed.
Lemma lem5051670 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem5051669 A s x). Qed.
Lemma lem5051671 {A : Type'} (k : A -> Prop) (s : A -> Prop) (x : A) : (term73 A k x s) = (term74 A k s x).
Proof. exact (MK_COMB (@lem5051666 A k x) (@lem5051670 A s x)). Qed.
Lemma lem5051674 {A : Type'} (k : A -> Prop) (s : A -> Prop) : (term75 A k s) = (term76 A k s).
Proof. exact (fun_ext (fun x : A => @lem5051671 A k s x)). Qed.
Lemma lem5051675 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5051676 {A : Type'} (k : A -> Prop) (s : A -> Prop) : (term8 A k s) = (term77 A k s).
Proof. exact (MK_COMB (@lem5051675 A) (@lem5051674 A k s)). Qed.
Lemma lem5051681 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5051682 {A : Type'} (k : A -> Prop) (s : A -> Prop) : (term41 A k s) = (term78 A k s).
Proof. exact (MK_COMB (@lem5051681) (@lem5051676 A k s)). Qed.
Lemma lem5051692 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term405 A B y f s) = (term406 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem5051693 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term405 A B y f s) = (term406 A B y f s).
Proof. exact (@lem5051692 A B y f s). Qed.
Lemma lem5051694 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term405 A B x f s) = (term406 A B x f s).
Proof. exact (@lem5051693 A B x f s). Qed.
Lemma lem5051704 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5051705 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5051704 A P x). Qed.
Lemma lem5051706 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem5051705 A s x). Qed.
Lemma lem5051707 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term407 A B x f x') = (term407 A B x f x').
Proof. exact (eq_refl (term407 A B x f x')). Qed.
Lemma lem5051708 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term408 A B x f x' s) = (term409 A B x f s x').
Proof. exact (MK_COMB (@lem5051707 A B x f x') (@lem5051706 A s x')). Qed.
Lemma lem5051711 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term410 A B x f s) = (term411 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem5051708 A B x f s x')). Qed.
Lemma lem5051712 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5051713 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term406 A B x f s) = (term412 A B x f s).
Proof. exact (MK_COMB (@lem5051712 A) (@lem5051711 A B x f s)). Qed.
Lemma lem5051718 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term405 A B x f s) = (term412 A B x f s).
Proof. exact (TRANS (@lem5051694 A B x f s) (@lem5051713 A B x f s)). Qed.
Lemma lem5051719 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5051720 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term19 A B x f s) = (term413 A B x f s).
Proof. exact (MK_COMB (@lem5051719) (@lem5051718 A B x f s)). Qed.
Lemma lem5051722 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5051723 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem5051722 B P x). Qed.
Lemma lem5051724 {B : Type'} (u : B -> Prop) (x : B) : (@IN B x u) = (u x).
Proof. exact (@lem5051723 B u x). Qed.
Lemma lem5051725 {A B : Type'} (f : A -> B) (s : A -> Prop) (u : B -> Prop) (x : B) : (term21 A B f s x u) = (term414 A B f s u x).
Proof. exact (MK_COMB (@lem5051720 A B x f s) (@lem5051724 B u x)). Qed.
Lemma lem5051728 {A B : Type'} (f : A -> B) (s : A -> Prop) (u : B -> Prop) : (term23 A B f s u) = (term415 A B f s u).
Proof. exact (fun_ext (fun x : B => @lem5051725 A B f s u x)). Qed.
Lemma lem5051729 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5051730 {A B : Type'} (f : A -> B) (s : A -> Prop) (u : B -> Prop) : (term12 A B f s u) = (term416 A B f s u).
Proof. exact (MK_COMB (@lem5051729 B) (@lem5051728 A B f s u)). Qed.
Lemma lem5051735 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5051736 {A B : Type'} (f : A -> B) (s : A -> Prop) (u : B -> Prop) : (term394 A B f s u) = (term417 A B f s u).
Proof. exact (MK_COMB (@lem5051735) (@lem5051730 A B f s u)). Qed.
Lemma lem5051750 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5051751 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5051750 A P x). Qed.
Lemma lem5051752 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem5051751 A s x). Qed.
Lemma lem5051753 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5051754 {A : Type'} (s : A -> Prop) (x : A) : (term98 A x s) = (term99 A s x).
Proof. exact (MK_COMB (@lem5051753) (@lem5051752 A s x)). Qed.
Lemma lem5051758 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5051759 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5051758 A P x). Qed.
Lemma lem5051760 {A : Type'} (s : A -> Prop) (y : A) : (@IN A y s) = (s y).
Proof. exact (@lem5051759 A s y). Qed.
Lemma lem5051761 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5051762 {A : Type'} (s : A -> Prop) (y : A) : (term98 A y s) = (term99 A s y).
Proof. exact (MK_COMB (@lem5051761) (@lem5051760 A s y)). Qed.
Lemma lem5051765 {A B : Type'} (x : A) (f : A -> B) (y : A) : ((f x) = (f y)) = ((f x) = (f y)).
Proof. exact (eq_refl ((f x) = (f y))). Qed.
Lemma lem5051766 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term272 A B s x f y) = (term418 A B s x f y).
Proof. exact (MK_COMB (@lem5051762 A s y) (@lem5051765 A B x f y)). Qed.
Lemma lem5051769 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term271 A B s x f y) = (term419 A B s x f y).
Proof. exact (MK_COMB (@lem5051754 A s x) (@lem5051766 A B s x f y)). Qed.
Lemma lem5051772 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5051773 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term420 A B s x f y) = (term421 A B s x f y).
Proof. exact (MK_COMB (@lem5051772) (@lem5051769 A B s x f y)). Qed.
Lemma lem5051776 {A : Type'} (x : A) (y : A) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem5051777 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term389 A B s f x y) = (term422 A B s f x y).
Proof. exact (MK_COMB (@lem5051773 A B s x f y) (@lem5051776 A x y)). Qed.
Lemma lem5051780 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term423 A B s f x) = (term424 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem5051777 A B s f x y)). Qed.
Lemma lem5051781 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5051782 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term390 A B s f x) = (term425 A B s f x).
Proof. exact (MK_COMB (@lem5051781 A) (@lem5051780 A B s f x)). Qed.
Lemma lem5051787 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term426 A B s f) = (term427 A B s f).
Proof. exact (fun_ext (fun x : A => @lem5051782 A B s f x)). Qed.
Lemma lem5051788 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5051789 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term391 A B s f) = (term428 A B s f).
Proof. exact (MK_COMB (@lem5051788 A) (@lem5051787 A B s f)). Qed.
Lemma lem5051794 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) : (term395 A B u s f) = (term429 A B u s f).
Proof. exact (MK_COMB (@lem5051736 A B f s u) (@lem5051789 A B s f)). Qed.
Lemma lem5051797 {A B : Type'} (k : A -> Prop) (u : B -> Prop) (s : A -> Prop) (f : A -> B) : (term396 A B k u s f) = (term430 A B k u s f).
Proof. exact (MK_COMB (@lem5051682 A k s) (@lem5051794 A B u s f)). Qed.
Lemma lem5051800 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5051801 {A B : Type'} (k : A -> Prop) (u : B -> Prop) (s : A -> Prop) (f : A -> B) : (term398 A B k u s f) = (term431 A B k u s f).
Proof. exact (MK_COMB (@lem5051800) (@lem5051797 A B k u s f)). Qed.
Lemma lem5051811 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term405 A B y f s) = (term406 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem5051812 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term405 A B y f s) = (term406 A B y f s).
Proof. exact (@lem5051811 A B y f s). Qed.
Lemma lem5051813 {A B : Type'} (x : B) (f : A -> B) (k : A -> Prop) : (term405 A B x f k) = (term406 A B x f k).
Proof. exact (@lem5051812 A B x f k). Qed.
Lemma lem5051823 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5051824 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5051823 A P x). Qed.
Lemma lem5051825 {A : Type'} (k : A -> Prop) (x : A) : (@IN A x k) = (k x).
Proof. exact (@lem5051824 A k x). Qed.
Lemma lem5051826 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term407 A B x f x') = (term407 A B x f x').
Proof. exact (eq_refl (term407 A B x f x')). Qed.
Lemma lem5051827 {A B : Type'} (x : B) (f : A -> B) (k : A -> Prop) (x' : A) : (term408 A B x f x' k) = (term409 A B x f k x').
Proof. exact (MK_COMB (@lem5051826 A B x f x') (@lem5051825 A k x')). Qed.
Lemma lem5051830 {A B : Type'} (x : B) (f : A -> B) (k : A -> Prop) : (term410 A B x f k) = (term411 A B x f k).
Proof. exact (fun_ext (fun x' : A => @lem5051827 A B x f k x')). Qed.
Lemma lem5051831 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5051832 {A B : Type'} (x : B) (f : A -> B) (k : A -> Prop) : (term406 A B x f k) = (term412 A B x f k).
Proof. exact (MK_COMB (@lem5051831 A) (@lem5051830 A B x f k)). Qed.
Lemma lem5051837 {A B : Type'} (x : B) (f : A -> B) (k : A -> Prop) : (term405 A B x f k) = (term412 A B x f k).
Proof. exact (TRANS (@lem5051813 A B x f k) (@lem5051832 A B x f k)). Qed.
Lemma lem5051838 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5051839 {A B : Type'} (x : B) (f : A -> B) (k : A -> Prop) : (term19 A B x f k) = (term413 A B x f k).
Proof. exact (MK_COMB (@lem5051838) (@lem5051837 A B x f k)). Qed.
Lemma lem5051841 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5051842 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem5051841 B P x). Qed.
Lemma lem5051843 {B : Type'} (u : B -> Prop) (x : B) : (@IN B x u) = (u x).
Proof. exact (@lem5051842 B u x). Qed.
Lemma lem5051844 {A B : Type'} (f : A -> B) (k : A -> Prop) (u : B -> Prop) (x : B) : (term21 A B f k x u) = (term414 A B f k u x).
Proof. exact (MK_COMB (@lem5051839 A B x f k) (@lem5051843 B u x)). Qed.
Lemma lem5051847 {A B : Type'} (f : A -> B) (k : A -> Prop) (u : B -> Prop) : (term23 A B f k u) = (term415 A B f k u).
Proof. exact (fun_ext (fun x : B => @lem5051844 A B f k u x)). Qed.
Lemma lem5051848 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5051849 {A B : Type'} (f : A -> B) (k : A -> Prop) (u : B -> Prop) : (term12 A B f k u) = (term416 A B f k u).
Proof. exact (MK_COMB (@lem5051848 B) (@lem5051847 A B f k u)). Qed.
Lemma lem5051854 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5051855 {A B : Type'} (f : A -> B) (k : A -> Prop) (u : B -> Prop) : (term394 A B f k u) = (term417 A B f k u).
Proof. exact (MK_COMB (@lem5051854) (@lem5051849 A B f k u)). Qed.
Lemma lem5051863 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term79 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem5051864 {A : Type'} (p : A -> Prop) (x : A) : (term79 A x p) = (p x).
Proof. exact (@lem5051863 A p x). Qed.
Lemma lem5051865 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x : A) : (term432 A B x s f k) = (term433 A B s f k x).
Proof. exact (@lem5051864 A (term434 A B s f k) x). Qed.
Lemma lem5051866 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (k : A -> Prop) : (term433 A B s f k x) = (term435 A B s x f k).
Proof. exact (eq_refl (term433 A B s f k x)). Qed.
Lemma lem5051867 {A : Type'} (GEN_PVAR_222 : A) : (@SETSPEC A GEN_PVAR_222) = (@SETSPEC A GEN_PVAR_222).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_222)). Qed.
Lemma lem5051868 {A B : Type'} (GEN_PVAR_222 : A) (s : A -> Prop) (x : A) (f : A -> B) (k : A -> Prop) : (term436 A B GEN_PVAR_222 s f k x) = (term437 A B GEN_PVAR_222 s x f k).
Proof. exact (MK_COMB (@lem5051867 A GEN_PVAR_222) (@lem5051866 A B s x f k)). Qed.
Lemma lem5051869 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5051870 {A B : Type'} (GEN_PVAR_222 : A) (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x : A) : (term438 A B GEN_PVAR_222 s f k x) = (term439 A B GEN_PVAR_222 s f k x).
Proof. exact (MK_COMB (@lem5051868 A B GEN_PVAR_222 s x f k) (@lem5051869 A x)). Qed.
Lemma lem5051871 {A B : Type'} (GEN_PVAR_222 : A) (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term440 A B GEN_PVAR_222 s f k) = (term441 A B GEN_PVAR_222 s f k).
Proof. exact (fun_ext (fun x : A => @lem5051870 A B GEN_PVAR_222 s f k x)). Qed.
Lemma lem5051872 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5051873 {A B : Type'} (GEN_PVAR_222 : A) (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term442 A B GEN_PVAR_222 s f k) = (term443 A B GEN_PVAR_222 s f k).
Proof. exact (MK_COMB (@lem5051872 A) (@lem5051871 A B GEN_PVAR_222 s f k)). Qed.
Lemma lem5051874 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term444 A B s f k) = (term445 A B s f k).
Proof. exact (fun_ext (fun GEN_PVAR_222 : A => @lem5051873 A B GEN_PVAR_222 s f k)). Qed.
Lemma lem5051875 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem5051876 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term446 A B s f k) = (term399 A B s f k).
Proof. exact (MK_COMB (@lem5051875 A) (@lem5051874 A B s f k)). Qed.
Lemma lem5051877 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem5051878 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term432 A B x s f k) = (term447 A B x s f k).
Proof. exact (MK_COMB (@lem5051877 A x) (@lem5051876 A B s f k)). Qed.
Lemma lem5051879 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5051880 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term448 A B x s f k) = (term449 A B x s f k).
Proof. exact (MK_COMB (@lem5051879) (@lem5051878 A B x s f k)). Qed.
Lemma lem5051881 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (k : A -> Prop) : (term433 A B s f k x) = (term435 A B s x f k).
Proof. exact (eq_refl (term433 A B s f k x)). Qed.
Lemma lem5051882 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (k : A -> Prop) : ((term432 A B x s f k) = (term433 A B s f k x)) = ((term447 A B x s f k) = (term435 A B s x f k)).
Proof. exact (MK_COMB (@lem5051880 A B x s f k) (@lem5051881 A B s x f k)). Qed.
Lemma lem5051883 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (k : A -> Prop) : (term447 A B x s f k) = (term435 A B s x f k).
Proof. exact (EQ_MP (@lem5051882 A B s x f k) (@lem5051865 A B s f k x)). Qed.
Lemma lem5051887 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5051888 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5051887 A P x). Qed.
Lemma lem5051889 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem5051888 A s x). Qed.
Lemma lem5051890 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5051891 {A : Type'} (s : A -> Prop) (x : A) : (term98 A x s) = (term99 A s x).
Proof. exact (MK_COMB (@lem5051890) (@lem5051889 A s x)). Qed.
Lemma lem5051893 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term405 A B y f s) = (term406 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem5051894 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term405 A B y f s) = (term406 A B y f s).
Proof. exact (@lem5051893 A B y f s). Qed.
Lemma lem5051895 {A B : Type'} (x : A) (f : A -> B) (k : A -> Prop) : (term450 A B x f k) = (term451 A B x f k).
Proof. exact (@lem5051894 A B (f x) f k). Qed.
Lemma lem5051905 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5051906 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5051905 A P x). Qed.
Lemma lem5051907 {A : Type'} (k : A -> Prop) (x' : A) : (@IN A x' k) = (k x').
Proof. exact (@lem5051906 A k x'). Qed.
Lemma lem5051908 {A B : Type'} (x : A) (f : A -> B) (x' : A) : (term288 A B x f x') = (term288 A B x f x').
Proof. exact (eq_refl (term288 A B x f x')). Qed.
Lemma lem5051909 {A B : Type'} (x : A) (f : A -> B) (k : A -> Prop) (x' : A) : (term452 A B x f x' k) = (term453 A B x f k x').
Proof. exact (MK_COMB (@lem5051908 A B x f x') (@lem5051907 A k x')). Qed.
Lemma lem5051912 {A B : Type'} (x : A) (f : A -> B) (k : A -> Prop) : (term454 A B x f k) = (term455 A B x f k).
Proof. exact (fun_ext (fun x' : A => @lem5051909 A B x f k x')). Qed.
Lemma lem5051913 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5051914 {A B : Type'} (x : A) (f : A -> B) (k : A -> Prop) : (term451 A B x f k) = (term456 A B x f k).
Proof. exact (MK_COMB (@lem5051913 A) (@lem5051912 A B x f k)). Qed.
Lemma lem5051919 {A B : Type'} (x : A) (f : A -> B) (k : A -> Prop) : (term450 A B x f k) = (term456 A B x f k).
Proof. exact (TRANS (@lem5051895 A B x f k) (@lem5051914 A B x f k)). Qed.
Lemma lem5051920 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (k : A -> Prop) : (term435 A B s x f k) = (term457 A B s x f k).
Proof. exact (MK_COMB (@lem5051891 A s x) (@lem5051919 A B x f k)). Qed.
Lemma lem5051923 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (k : A -> Prop) : (term447 A B x s f k) = (term457 A B s x f k).
Proof. exact (TRANS (@lem5051883 A B s x f k) (@lem5051920 A B s x f k)). Qed.
Lemma lem5051924 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5051925 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (k : A -> Prop) : (term449 A B x s f k) = (term458 A B s x f k).
Proof. exact (MK_COMB (@lem5051924) (@lem5051923 A B s x f k)). Qed.
Lemma lem5051927 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5051928 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5051927 A P x). Qed.
Lemma lem5051929 {A : Type'} (k : A -> Prop) (x : A) : (@IN A x k) = (k x).
Proof. exact (@lem5051928 A k x). Qed.
Lemma lem5051930 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x : A) : ((term447 A B x s f k) = (@IN A x k)) = ((term457 A B s x f k) = (k x)).
Proof. exact (MK_COMB (@lem5051925 A B s x f k) (@lem5051929 A k x)). Qed.
Lemma lem5051933 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term459 A B s f k) = (term460 A B s f k).
Proof. exact (fun_ext (fun x : A => @lem5051930 A B s f k x)). Qed.
Lemma lem5051934 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5051935 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term400 A B s f k) = (term461 A B s f k).
Proof. exact (MK_COMB (@lem5051934 A) (@lem5051933 A B s f k)). Qed.
Lemma lem5051940 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term402 A B u s f k) = (term462 A B u s f k).
Proof. exact (MK_COMB (@lem5051855 A B f k u) (@lem5051935 A B s f k)). Qed.
Lemma lem5051943 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term404 A B u s f k) = (term463 A B u s f k).
Proof. exact (MK_COMB (@lem5051801 A B k u s f) (@lem5051940 A B u s f k)). Qed.
Lemma lem5051946 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term463 A B u s f k) = (term404 A B u s f k).
Proof. exact (SYM (@lem5051943 A B u s f k)). Qed.
Lemma lem5051948 (p : Prop) : p = (term113 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5051949 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term463 A B u s f k) = (term464 A B u s f k).
Proof. exact (@lem5051948 (term463 A B u s f k)). Qed.
Lemma lem5051950 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term464 A B u s f k) = (term463 A B u s f k).
Proof. exact (SYM (@lem5051949 A B u s f k)). Qed.
Lemma lem5051951 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) (h1 : term465 A B u s f k) : term465 A B u s f k.
Proof. exact (h1). Qed.
Lemma lem5051954 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) (h1 : term464 A B u s f k) : term464 A B u s f k.
Proof. exact (h1). Qed.
Lemma lem5051955 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) : term466 A B u s f k.
Proof. exact (fun h0 : term464 A B u s f k => @lem5051954 A B u s f k h0). Qed.
Lemma lem5051956 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) (h1 : term466 A B u s f k) : term466 A B u s f k.
Proof. exact (h1). Qed.
Lemma lem5051957 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) (h1 : term464 A B u s f k) : term464 A B u s f k.
Proof. exact (h1). Qed.
Lemma lem5051958 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) (h1 : term464 A B u s f k) (h2 : term466 A B u s f k) : term464 A B u s f k.
Proof. exact (@lem5051956 A B u s f k h2 (@lem5051957 A B u s f k h1)). Qed.
Lemma lem5051959 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) (h1 : term464 A B u s f k) : term467 A B u s f k.
Proof. exact (fun h0 : term466 A B u s f k => @lem5051958 A B u s f k h1 h0). Qed.
Lemma lem5051960 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) (h1 : term466 A B u s f k) : term466 A B u s f k.
Proof. exact (h1). Qed.
Lemma lem5051961 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) (h1 : term464 A B u s f k) (h2 : term466 A B u s f k) : term464 A B u s f k.
Proof. exact (@lem5051959 A B u s f k h1 (@lem5051960 A B u s f k h2)). Qed.
Lemma lem5051962 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) (h1 : term466 A B u s f k) : term466 A B u s f k.
Proof. exact (fun h0 : term464 A B u s f k => @lem5051961 A B u s f k h0 h1). Qed.
Lemma lem5051963 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) : term468 A B u s f k.
Proof. exact (fun h0 : term466 A B u s f k => @lem5051962 A B u s f k h0). Qed.
Lemma lem5051966 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) : term466 A B u s f k.
Proof. exact (@lem5051963 A B u s f k (@lem5051955 A B u s f k)). Qed.
Lemma lem5051967 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) : term466 A B u s f k.
Proof. exact (@lem5051966 A B u s f k). Qed.
Lemma lem5051985 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5051986 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term464 A B u s f k) = (term469 A B u s f k).
Proof. exact (@lem5051985 (term465 A B u s f k)). Qed.
Lemma lem5051988 (t : Prop) : (term120 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5051989 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term469 A B u s f k) = (term463 A B u s f k).
Proof. exact (@lem5051988 (term463 A B u s f k)). Qed.
Lemma lem5051992 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term464 A B u s f k) = (term463 A B u s f k).
Proof. exact (TRANS (@lem5051986 A B u s f k) (@lem5051989 A B u s f k)). Qed.
Lemma lem5052139 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term470 A B s f k) = (term471 A B s f k).
Proof. exact (fun_ext (fun u : B -> Prop => @lem5051992 A B u s f k)). Qed.
Lemma lem5052140 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5052141 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term472 A B s f k) = (term473 A B s f k).
Proof. exact (MK_COMB (@lem5052140 B) (@lem5052139 A B s f k)). Qed.
Lemma lem5052146 {A B : Type'} (f : A -> B) (k : A -> Prop) : (term474 A B f k) = (term475 A B f k).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5052141 A B s f k)). Qed.
Lemma lem5052147 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5052148 {A B : Type'} (f : A -> B) (k : A -> Prop) : (term476 A B f k) = (term477 A B f k).
Proof. exact (MK_COMB (@lem5052147 A) (@lem5052146 A B f k)). Qed.
Lemma lem5052153 {A B : Type'} (k : A -> Prop) : (term478 A B k) = (term479 A B k).
Proof. exact (fun_ext (fun f : A -> B => @lem5052148 A B f k)). Qed.
Lemma lem5052154 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5052155 {A B : Type'} (k : A -> Prop) : (term480 A B k) = (term481 A B k).
Proof. exact (MK_COMB (@lem5052154 A B) (@lem5052153 A B k)). Qed.
Lemma lem5052160 {A B : Type'} : (term482 A B) = (term483 A B).
Proof. exact (fun_ext (fun k : A -> Prop => @lem5052155 A B k)). Qed.
Lemma lem5052161 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5052170 {A B : Type'} : (term484 A B) = (term485 A B).
Proof. exact (MK_COMB (@lem5052161 A) (@lem5052160 A B)). Qed.
Lemma lem5052171 {A : Type'} (k : A -> Prop) (x : A) : (k x) = (k x).
Proof. exact (eq_refl (k x)). Qed.
Lemma lem5052176 {A B : Type'} (x : A) (f : A -> B) (k : A -> Prop) (x' : A) : (term453 A B x f k x') = (term453 A B x f k x').
Proof. exact (eq_refl (term453 A B x f k x')). Qed.
Lemma lem5052177 {A B : Type'} (x : A) (f : A -> B) (k : A -> Prop) : (term455 A B x f k) = (term455 A B x f k).
Proof. exact (fun_ext (fun x' : A => @lem5052176 A B x f k x')). Qed.
Lemma lem5052178 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5052179 {A B : Type'} (x : A) (f : A -> B) (k : A -> Prop) : (term456 A B x f k) = (term456 A B x f k).
Proof. exact (MK_COMB (@lem5052178 A) (@lem5052177 A B x f k)). Qed.
Lemma lem5052182 {A : Type'} (s : A -> Prop) (x : A) : (term99 A s x) = (term99 A s x).
Proof. exact (eq_refl (term99 A s x)). Qed.
Lemma lem5052183 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (k : A -> Prop) : (term457 A B s x f k) = (term457 A B s x f k).
Proof. exact (MK_COMB (@lem5052182 A s x) (@lem5052179 A B x f k)). Qed.
Lemma lem5052184 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5052185 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (k : A -> Prop) : (term458 A B s x f k) = (term458 A B s x f k).
Proof. exact (MK_COMB (@lem5052184) (@lem5052183 A B s x f k)). Qed.
Lemma lem5052186 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x : A) : ((term457 A B s x f k) = (k x)) = ((term457 A B s x f k) = (k x)).
Proof. exact (MK_COMB (@lem5052185 A B s x f k) (@lem5052171 A k x)). Qed.
Lemma lem5052187 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term460 A B s f k) = (term460 A B s f k).
Proof. exact (fun_ext (fun x : A => @lem5052186 A B s f k x)). Qed.
Lemma lem5052188 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5052189 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term461 A B s f k) = (term461 A B s f k).
Proof. exact (MK_COMB (@lem5052188 A) (@lem5052187 A B s f k)). Qed.
Lemma lem5052190 {B : Type'} (u : B -> Prop) (x : B) : (u x) = (u x).
Proof. exact (eq_refl (u x)). Qed.
Lemma lem5052195 {A B : Type'} (x : B) (f : A -> B) (k : A -> Prop) (x' : A) : (term409 A B x f k x') = (term409 A B x f k x').
Proof. exact (eq_refl (term409 A B x f k x')). Qed.
Lemma lem5052196 {A B : Type'} (x : B) (f : A -> B) (k : A -> Prop) : (term411 A B x f k) = (term411 A B x f k).
Proof. exact (fun_ext (fun x' : A => @lem5052195 A B x f k x')). Qed.
Lemma lem5052197 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5052198 {A B : Type'} (x : B) (f : A -> B) (k : A -> Prop) : (term412 A B x f k) = (term412 A B x f k).
Proof. exact (MK_COMB (@lem5052197 A) (@lem5052196 A B x f k)). Qed.
Lemma lem5052199 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5052200 {A B : Type'} (x : B) (f : A -> B) (k : A -> Prop) : (term413 A B x f k) = (term413 A B x f k).
Proof. exact (MK_COMB (@lem5052199) (@lem5052198 A B x f k)). Qed.
Lemma lem5052201 {A B : Type'} (f : A -> B) (k : A -> Prop) (u : B -> Prop) (x : B) : (term414 A B f k u x) = (term414 A B f k u x).
Proof. exact (MK_COMB (@lem5052200 A B x f k) (@lem5052190 B u x)). Qed.
Lemma lem5052202 {A B : Type'} (f : A -> B) (k : A -> Prop) (u : B -> Prop) : (term415 A B f k u) = (term415 A B f k u).
Proof. exact (fun_ext (fun x : B => @lem5052201 A B f k u x)). Qed.
Lemma lem5052203 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5052204 {A B : Type'} (f : A -> B) (k : A -> Prop) (u : B -> Prop) : (term416 A B f k u) = (term416 A B f k u).
Proof. exact (MK_COMB (@lem5052203 B) (@lem5052202 A B f k u)). Qed.
Lemma lem5052205 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5052206 {A B : Type'} (f : A -> B) (k : A -> Prop) (u : B -> Prop) : (term417 A B f k u) = (term417 A B f k u).
Proof. exact (MK_COMB (@lem5052205) (@lem5052204 A B f k u)). Qed.
Lemma lem5052207 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term462 A B u s f k) = (term462 A B u s f k).
Proof. exact (MK_COMB (@lem5052206 A B f k u) (@lem5052189 A B s f k)). Qed.
Lemma lem5052220 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term422 A B s f x y) = (term422 A B s f x y).
Proof. exact (eq_refl (term422 A B s f x y)). Qed.
Lemma lem5052221 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term424 A B s f x) = (term424 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem5052220 A B s f x y)). Qed.
Lemma lem5052222 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5052223 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term425 A B s f x) = (term425 A B s f x).
Proof. exact (MK_COMB (@lem5052222 A) (@lem5052221 A B s f x)). Qed.
Lemma lem5052224 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term427 A B s f) = (term427 A B s f).
Proof. exact (fun_ext (fun x : A => @lem5052223 A B s f x)). Qed.
Lemma lem5052225 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5052226 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term428 A B s f) = (term428 A B s f).
Proof. exact (MK_COMB (@lem5052225 A) (@lem5052224 A B s f)). Qed.
Lemma lem5052227 {B : Type'} (u : B -> Prop) (x : B) : (u x) = (u x).
Proof. exact (eq_refl (u x)). Qed.
Lemma lem5052232 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term409 A B x f s x') = (term409 A B x f s x').
Proof. exact (eq_refl (term409 A B x f s x')). Qed.
Lemma lem5052233 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term411 A B x f s) = (term411 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem5052232 A B x f s x')). Qed.
Lemma lem5052234 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5052235 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term412 A B x f s) = (term412 A B x f s).
Proof. exact (MK_COMB (@lem5052234 A) (@lem5052233 A B x f s)). Qed.
Lemma lem5052236 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5052237 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term413 A B x f s) = (term413 A B x f s).
Proof. exact (MK_COMB (@lem5052236) (@lem5052235 A B x f s)). Qed.
Lemma lem5052238 {A B : Type'} (f : A -> B) (s : A -> Prop) (u : B -> Prop) (x : B) : (term414 A B f s u x) = (term414 A B f s u x).
Proof. exact (MK_COMB (@lem5052237 A B x f s) (@lem5052227 B u x)). Qed.
Lemma lem5052239 {A B : Type'} (f : A -> B) (s : A -> Prop) (u : B -> Prop) : (term415 A B f s u) = (term415 A B f s u).
Proof. exact (fun_ext (fun x : B => @lem5052238 A B f s u x)). Qed.
Lemma lem5052240 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5052241 {A B : Type'} (f : A -> B) (s : A -> Prop) (u : B -> Prop) : (term416 A B f s u) = (term416 A B f s u).
Proof. exact (MK_COMB (@lem5052240 B) (@lem5052239 A B f s u)). Qed.
Lemma lem5052242 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5052243 {A B : Type'} (f : A -> B) (s : A -> Prop) (u : B -> Prop) : (term417 A B f s u) = (term417 A B f s u).
Proof. exact (MK_COMB (@lem5052242) (@lem5052241 A B f s u)). Qed.
Lemma lem5052244 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) : (term429 A B u s f) = (term429 A B u s f).
Proof. exact (MK_COMB (@lem5052243 A B f s u) (@lem5052226 A B s f)). Qed.
Lemma lem5052249 {A : Type'} (k : A -> Prop) (s : A -> Prop) (x : A) : (term74 A k s x) = (term74 A k s x).
Proof. exact (eq_refl (term74 A k s x)). Qed.
Lemma lem5052250 {A : Type'} (k : A -> Prop) (s : A -> Prop) : (term76 A k s) = (term76 A k s).
Proof. exact (fun_ext (fun x : A => @lem5052249 A k s x)). Qed.
Lemma lem5052251 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5052252 {A : Type'} (k : A -> Prop) (s : A -> Prop) : (term77 A k s) = (term77 A k s).
Proof. exact (MK_COMB (@lem5052251 A) (@lem5052250 A k s)). Qed.
Lemma lem5052253 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5052254 {A : Type'} (k : A -> Prop) (s : A -> Prop) : (term78 A k s) = (term78 A k s).
Proof. exact (MK_COMB (@lem5052253) (@lem5052252 A k s)). Qed.
Lemma lem5052255 {A B : Type'} (k : A -> Prop) (u : B -> Prop) (s : A -> Prop) (f : A -> B) : (term430 A B k u s f) = (term430 A B k u s f).
Proof. exact (MK_COMB (@lem5052254 A k s) (@lem5052244 A B u s f)). Qed.
Lemma lem5052256 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5052257 {A B : Type'} (k : A -> Prop) (u : B -> Prop) (s : A -> Prop) (f : A -> B) : (term431 A B k u s f) = (term431 A B k u s f).
Proof. exact (MK_COMB (@lem5052256) (@lem5052255 A B k u s f)). Qed.
Lemma lem5052258 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term463 A B u s f k) = (term463 A B u s f k).
Proof. exact (MK_COMB (@lem5052257 A B k u s f) (@lem5052207 A B u s f k)). Qed.
Lemma lem5052259 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term471 A B s f k) = (term471 A B s f k).
Proof. exact (fun_ext (fun u : B -> Prop => @lem5052258 A B u s f k)). Qed.
Lemma lem5052260 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5052261 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term473 A B s f k) = (term473 A B s f k).
Proof. exact (MK_COMB (@lem5052260 B) (@lem5052259 A B s f k)). Qed.
Lemma lem5052262 {A B : Type'} (f : A -> B) (k : A -> Prop) : (term475 A B f k) = (term475 A B f k).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5052261 A B s f k)). Qed.
Lemma lem5052263 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5052264 {A B : Type'} (f : A -> B) (k : A -> Prop) : (term477 A B f k) = (term477 A B f k).
Proof. exact (MK_COMB (@lem5052263 A) (@lem5052262 A B f k)). Qed.
Lemma lem5052265 {A B : Type'} (k : A -> Prop) : (term479 A B k) = (term479 A B k).
Proof. exact (fun_ext (fun f : A -> B => @lem5052264 A B f k)). Qed.
Lemma lem5052266 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5052267 {A B : Type'} (k : A -> Prop) : (term481 A B k) = (term481 A B k).
Proof. exact (MK_COMB (@lem5052266 A B) (@lem5052265 A B k)). Qed.
Lemma lem5052268 {A B : Type'} : (term483 A B) = (term483 A B).
Proof. exact (fun_ext (fun k : A -> Prop => @lem5052267 A B k)). Qed.
Lemma lem5052269 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5052270 {A B : Type'} : (term485 A B) = (term485 A B).
Proof. exact (MK_COMB (@lem5052269 A) (@lem5052268 A B)). Qed.
Lemma lem5052379 {A B : Type'} : (term484 A B) = (term485 A B).
Proof. exact (TRANS (@lem5052170 A B) (@lem5052270 A B)). Qed.
Lemma lem5052380 {A B : Type'} : (term485 A B) = (term484 A B).
Proof. exact (SYM (@lem5052379 A B)). Qed.
Lemma lem5052381 {A B : Type'} (k : A -> Prop) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term430 A B k u s f) : term430 A B k u s f.
Proof. exact (h1). Qed.
Lemma lem5052383 (p : Prop) : p = (term113 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5052384 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term462 A B u s f k) = (term486 A B u s f k).
Proof. exact (@lem5052383 (term462 A B u s f k)). Qed.
Lemma lem5052385 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term486 A B u s f k) = (term462 A B u s f k).
Proof. exact (SYM (@lem5052384 A B u s f k)). Qed.
Lemma lem5052386 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) (h1 : term487 A B u s f k) : term487 A B u s f k.
Proof. exact (h1). Qed.
Lemma lem5052393 {A : Type'} (k : A -> Prop) (s : A -> Prop) (x : A) : (term74 A k s x) = (term150 A k s x).
Proof. exact (@lem17265 (k x) (s x)). Qed.
Lemma lem5052394 {A : Type'} (k : A -> Prop) (s : A -> Prop) : (term76 A k s) = (term151 A k s).
Proof. exact (fun_ext (fun x : A => @lem5052393 A k s x)). Qed.
Lemma lem5052395 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5052396 {A : Type'} (k : A -> Prop) (s : A -> Prop) : (term77 A k s) = (term152 A k s).
Proof. exact (MK_COMB (@lem5052395 A) (@lem5052394 A k s)). Qed.
Lemma lem5052403 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term488 A B x f s x') = (term489 A B x f s x').
Proof. exact (@lem17045 (x = (f x')) (s x')). Qed.
Lemma lem5052404 {A : Type'} (P : A -> Prop) : (term490 A P) = (term491 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem5052405 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term492 A B x f s) = (term493 A B x f s).
Proof. exact (@lem5052404 A (term411 A B x f s)). Qed.
Lemma lem5052406 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term494 A B x f s x') = (term409 A B x f s x').
Proof. exact (eq_refl (term494 A B x f s x')). Qed.
Lemma lem5052407 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5052408 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term495 A B x f s x') = (term488 A B x f s x').
Proof. exact (MK_COMB (@lem5052407) (@lem5052406 A B x f s x')). Qed.
Lemma lem5052409 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term495 A B x f s x') = (term489 A B x f s x').
Proof. exact (TRANS (@lem5052408 A B x f s x') (@lem5052403 A B x f s x')). Qed.
Lemma lem5052410 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term496 A B x f s) = (term497 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem5052409 A B x f s x')). Qed.
Lemma lem5052411 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5052412 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term493 A B x f s) = (term498 A B x f s).
Proof. exact (MK_COMB (@lem5052411 A) (@lem5052410 A B x f s)). Qed.
Lemma lem5052413 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term492 A B x f s) = (term498 A B x f s).
Proof. exact (TRANS (@lem5052405 A B x f s) (@lem5052412 A B x f s)). Qed.
Lemma lem5052414 {B : Type'} (u : B -> Prop) (x : B) : (u x) = (u x).
Proof. exact (eq_refl (u x)). Qed.
Lemma lem5052415 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5052416 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term499 A B x f s) = (term500 A B x f s).
Proof. exact (MK_COMB (@lem5052415) (@lem5052413 A B x f s)). Qed.
Lemma lem5052417 {A B : Type'} (f : A -> B) (s : A -> Prop) (u : B -> Prop) (x : B) : (term501 A B f s u x) = (term502 A B f s u x).
Proof. exact (MK_COMB (@lem5052416 A B x f s) (@lem5052414 B u x)). Qed.
Lemma lem5052418 {A B : Type'} (f : A -> B) (s : A -> Prop) (u : B -> Prop) (x : B) : (term414 A B f s u x) = (term501 A B f s u x).
Proof. exact (@lem17265 (term412 A B x f s) (u x)). Qed.
Lemma lem5052419 {A B : Type'} (f : A -> B) (s : A -> Prop) (u : B -> Prop) (x : B) : (term414 A B f s u x) = (term502 A B f s u x).
Proof. exact (TRANS (@lem5052418 A B f s u x) (@lem5052417 A B f s u x)). Qed.
Lemma lem5052420 {A B : Type'} (f : A -> B) (s : A -> Prop) (u : B -> Prop) : (term415 A B f s u) = (term503 A B f s u).
Proof. exact (fun_ext (fun x : B => @lem5052419 A B f s u x)). Qed.
Lemma lem5052421 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5052422 {A B : Type'} (f : A -> B) (s : A -> Prop) (u : B -> Prop) : (term416 A B f s u) = (term504 A B f s u).
Proof. exact (MK_COMB (@lem5052421 B) (@lem5052420 A B f s u)). Qed.
Lemma lem5052430 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term505 A B s x f y) = (term506 A B s x f y).
Proof. exact (@lem17045 (s y) ((f x) = (f y))). Qed.
Lemma lem5052432 {A : Type'} (s : A -> Prop) (x : A) : (term352 A s x) = (term352 A s x).
Proof. exact (eq_refl (term352 A s x)). Qed.
Lemma lem5052433 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term507 A B s x f y) = (term508 A B s x f y).
Proof. exact (MK_COMB (@lem5052432 A s x) (@lem5052430 A B s x f y)). Qed.
Lemma lem5052434 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term509 A B s x f y) = (term507 A B s x f y).
Proof. exact (@lem17045 (s x) (term418 A B s x f y)). Qed.
Lemma lem5052435 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term509 A B s x f y) = (term508 A B s x f y).
Proof. exact (TRANS (@lem5052434 A B s x f y) (@lem5052433 A B s x f y)). Qed.
Lemma lem5052436 {A : Type'} (x : A) (y : A) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem5052437 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5052438 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term510 A B s x f y) = (term511 A B s x f y).
Proof. exact (MK_COMB (@lem5052437) (@lem5052435 A B s x f y)). Qed.
Lemma lem5052439 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term512 A B s f x y) = (term513 A B s f x y).
Proof. exact (MK_COMB (@lem5052438 A B s x f y) (@lem5052436 A x y)). Qed.
Lemma lem5052440 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term422 A B s f x y) = (term512 A B s f x y).
Proof. exact (@lem17265 (term419 A B s x f y) (x = y)). Qed.
Lemma lem5052441 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term422 A B s f x y) = (term513 A B s f x y).
Proof. exact (TRANS (@lem5052440 A B s f x y) (@lem5052439 A B s f x y)). Qed.
Lemma lem5052442 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term424 A B s f x) = (term514 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem5052441 A B s f x y)). Qed.
Lemma lem5052443 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5052444 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term425 A B s f x) = (term515 A B s f x).
Proof. exact (MK_COMB (@lem5052443 A) (@lem5052442 A B s f x)). Qed.
Lemma lem5052445 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term427 A B s f) = (term516 A B s f).
Proof. exact (fun_ext (fun x : A => @lem5052444 A B s f x)). Qed.
Lemma lem5052446 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5052447 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term428 A B s f) = (term517 A B s f).
Proof. exact (MK_COMB (@lem5052446 A) (@lem5052445 A B s f)). Qed.
Lemma lem5052448 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5052449 {A B : Type'} (f : A -> B) (s : A -> Prop) (u : B -> Prop) : (term417 A B f s u) = (term518 A B f s u).
Proof. exact (MK_COMB (@lem5052448) (@lem5052422 A B f s u)). Qed.
Lemma lem5052450 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) : (term429 A B u s f) = (term519 A B u s f).
Proof. exact (MK_COMB (@lem5052449 A B f s u) (@lem5052447 A B s f)). Qed.
Lemma lem5052451 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5052452 {A : Type'} (k : A -> Prop) (s : A -> Prop) : (term78 A k s) = (term164 A k s).
Proof. exact (MK_COMB (@lem5052451) (@lem5052396 A k s)). Qed.
Lemma lem5052621 {A B : Type'} (k : A -> Prop) (u : B -> Prop) (s : A -> Prop) (f : A -> B) : (term430 A B k u s f) = (term520 A B k u s f).
Proof. exact (MK_COMB (@lem5052452 A k s) (@lem5052450 A B u s f)). Qed.
Lemma lem5052622 {A B : Type'} (k : A -> Prop) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term430 A B k u s f) : term520 A B k u s f.
Proof. exact (EQ_MP (@lem5052621 A B k u s f) (@lem5052381 A B k u s f h1)). Qed.
Lemma lem5052627 {A B : Type'} (x : B) (f : A -> B) (k : A -> Prop) (x' : A) : (term409 A B x f k x') = (term409 A B x f k x').
Proof. exact (eq_refl (term409 A B x f k x')). Qed.
Lemma lem5052628 {A B : Type'} (x : B) (f : A -> B) (k : A -> Prop) : (term411 A B x f k) = (term411 A B x f k).
Proof. exact (fun_ext (fun x' : A => @lem5052627 A B x f k x')). Qed.
Lemma lem5052629 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5052630 {A B : Type'} (x : B) (f : A -> B) (k : A -> Prop) : (term412 A B x f k) = (term412 A B x f k).
Proof. exact (MK_COMB (@lem5052629 A) (@lem5052628 A B x f k)). Qed.
Lemma lem5052631 {B : Type'} (u : B -> Prop) (x : B) : (term240 B u x) = (term240 B u x).
Proof. exact (eq_refl (term240 B u x)). Qed.
Lemma lem5052632 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5052633 {A B : Type'} (x : B) (f : A -> B) (k : A -> Prop) : (term521 A B x f k) = (term521 A B x f k).
Proof. exact (MK_COMB (@lem5052632) (@lem5052630 A B x f k)). Qed.
Lemma lem5052634 {A B : Type'} (f : A -> B) (k : A -> Prop) (u : B -> Prop) (x : B) : (term522 A B f k u x) = (term522 A B f k u x).
Proof. exact (MK_COMB (@lem5052633 A B x f k) (@lem5052631 B u x)). Qed.
Lemma lem5052635 {A B : Type'} (f : A -> B) (k : A -> Prop) (u : B -> Prop) (x : B) : (term523 A B f k u x) = (term522 A B f k u x).
Proof. exact (@lem17362 (term412 A B x f k) (u x)). Qed.
Lemma lem5052636 {A B : Type'} (f : A -> B) (k : A -> Prop) (u : B -> Prop) (x : B) : (term523 A B f k u x) = (term522 A B f k u x).
Proof. exact (TRANS (@lem5052635 A B f k u x) (@lem5052634 A B f k u x)). Qed.
Lemma lem5052637 {B : Type'} (P : B -> Prop) : (term141 B P) = (term142 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem5052638 {A B : Type'} (f : A -> B) (k : A -> Prop) (u : B -> Prop) : (term524 A B f k u) = (term525 A B f k u).
Proof. exact (@lem5052637 B (term415 A B f k u)). Qed.
Lemma lem5052639 {A B : Type'} (f : A -> B) (k : A -> Prop) (u : B -> Prop) (x : B) : (term526 A B f k u x) = (term414 A B f k u x).
Proof. exact (eq_refl (term526 A B f k u x)). Qed.
Lemma lem5052640 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5052641 {A B : Type'} (f : A -> B) (k : A -> Prop) (u : B -> Prop) (x : B) : (term527 A B f k u x) = (term523 A B f k u x).
Proof. exact (MK_COMB (@lem5052640) (@lem5052639 A B f k u x)). Qed.
Lemma lem5052642 {A B : Type'} (f : A -> B) (k : A -> Prop) (u : B -> Prop) (x : B) : (term527 A B f k u x) = (term522 A B f k u x).
Proof. exact (TRANS (@lem5052641 A B f k u x) (@lem5052636 A B f k u x)). Qed.
Lemma lem5052643 {A B : Type'} (f : A -> B) (k : A -> Prop) (u : B -> Prop) : (term528 A B f k u) = (term529 A B f k u).
Proof. exact (fun_ext (fun x : B => @lem5052642 A B f k u x)). Qed.
Lemma lem5052644 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5052645 {A B : Type'} (f : A -> B) (k : A -> Prop) (u : B -> Prop) : (term525 A B f k u) = (term530 A B f k u).
Proof. exact (MK_COMB (@lem5052644 B) (@lem5052643 A B f k u)). Qed.
Lemma lem5052646 {A B : Type'} (f : A -> B) (k : A -> Prop) (u : B -> Prop) : (term524 A B f k u) = (term530 A B f k u).
Proof. exact (TRANS (@lem5052638 A B f k u) (@lem5052645 A B f k u)). Qed.
Lemma lem5052657 {A B : Type'} (x : A) (f : A -> B) (k : A -> Prop) (x' : A) : (term531 A B x f k x') = (term532 A B x f k x').
Proof. exact (@lem17045 ((f x) = (f x')) (k x')). Qed.
Lemma lem5052660 {A B : Type'} (x : A) (f : A -> B) (k : A -> Prop) (x' : A) : (term453 A B x f k x') = (term453 A B x f k x').
Proof. exact (eq_refl (term453 A B x f k x')). Qed.
Lemma lem5052661 {A : Type'} (P : A -> Prop) : (term490 A P) = (term491 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem5052662 {A B : Type'} (x : A) (f : A -> B) (k : A -> Prop) : (term533 A B x f k) = (term534 A B x f k).
Proof. exact (@lem5052661 A (term455 A B x f k)). Qed.
Lemma lem5052663 {A B : Type'} (x : A) (f : A -> B) (k : A -> Prop) (x' : A) : (term535 A B x f k x') = (term453 A B x f k x').
Proof. exact (eq_refl (term535 A B x f k x')). Qed.
Lemma lem5052664 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5052665 {A B : Type'} (x : A) (f : A -> B) (k : A -> Prop) (x' : A) : (term536 A B x f k x') = (term531 A B x f k x').
Proof. exact (MK_COMB (@lem5052664) (@lem5052663 A B x f k x')). Qed.
Lemma lem5052666 {A B : Type'} (x : A) (f : A -> B) (k : A -> Prop) (x' : A) : (term536 A B x f k x') = (term532 A B x f k x').
Proof. exact (TRANS (@lem5052665 A B x f k x') (@lem5052657 A B x f k x')). Qed.
Lemma lem5052667 {A B : Type'} (x : A) (f : A -> B) (k : A -> Prop) : (term537 A B x f k) = (term538 A B x f k).
Proof. exact (fun_ext (fun x' : A => @lem5052666 A B x f k x')). Qed.
Lemma lem5052668 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5052669 {A B : Type'} (x : A) (f : A -> B) (k : A -> Prop) : (term534 A B x f k) = (term539 A B x f k).
Proof. exact (MK_COMB (@lem5052668 A) (@lem5052667 A B x f k)). Qed.
Lemma lem5052670 {A B : Type'} (x : A) (f : A -> B) (k : A -> Prop) : (term533 A B x f k) = (term539 A B x f k).
Proof. exact (TRANS (@lem5052662 A B x f k) (@lem5052669 A B x f k)). Qed.
Lemma lem5052671 {A B : Type'} (x : A) (f : A -> B) (k : A -> Prop) : (term455 A B x f k) = (term455 A B x f k).
Proof. exact (fun_ext (fun x' : A => @lem5052660 A B x f k x')). Qed.
Lemma lem5052672 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5052673 {A B : Type'} (x : A) (f : A -> B) (k : A -> Prop) : (term456 A B x f k) = (term456 A B x f k).
Proof. exact (MK_COMB (@lem5052672 A) (@lem5052671 A B x f k)). Qed.
Lemma lem5052675 {A : Type'} (s : A -> Prop) (x : A) : (term352 A s x) = (term352 A s x).
Proof. exact (eq_refl (term352 A s x)). Qed.
Lemma lem5052676 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (k : A -> Prop) : (term540 A B s x f k) = (term541 A B s x f k).
Proof. exact (MK_COMB (@lem5052675 A s x) (@lem5052670 A B x f k)). Qed.
Lemma lem5052677 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (k : A -> Prop) : (term542 A B s x f k) = (term540 A B s x f k).
Proof. exact (@lem17045 (s x) (term456 A B x f k)). Qed.
Lemma lem5052678 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (k : A -> Prop) : (term542 A B s x f k) = (term541 A B s x f k).
Proof. exact (TRANS (@lem5052677 A B s x f k) (@lem5052676 A B s x f k)). Qed.
Lemma lem5052680 {A : Type'} (s : A -> Prop) (x : A) : (term99 A s x) = (term99 A s x).
Proof. exact (eq_refl (term99 A s x)). Qed.
Lemma lem5052681 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (k : A -> Prop) : (term457 A B s x f k) = (term457 A B s x f k).
Proof. exact (MK_COMB (@lem5052680 A s x) (@lem5052673 A B x f k)). Qed.
Lemma lem5052682 {A : Type'} (k : A -> Prop) (x : A) : (term240 A k x) = (term240 A k x).
Proof. exact (eq_refl (term240 A k x)). Qed.
Lemma lem5052683 {A : Type'} (k : A -> Prop) (x : A) : (k x) = (k x).
Proof. exact (eq_refl (k x)). Qed.
Lemma lem5052684 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5052685 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (k : A -> Prop) : (term543 A B s x f k) = (term544 A B s x f k).
Proof. exact (MK_COMB (@lem5052684) (@lem5052678 A B s x f k)). Qed.
Lemma lem5052686 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x : A) : (term545 A B s f k x) = (term546 A B s f k x).
Proof. exact (MK_COMB (@lem5052685 A B s x f k) (@lem5052683 A k x)). Qed.
Lemma lem5052687 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5052688 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (k : A -> Prop) : (term547 A B s x f k) = (term547 A B s x f k).
Proof. exact (MK_COMB (@lem5052687) (@lem5052681 A B s x f k)). Qed.
Lemma lem5052689 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x : A) : (term548 A B s f k x) = (term548 A B s f k x).
Proof. exact (MK_COMB (@lem5052688 A B s x f k) (@lem5052682 A k x)). Qed.
Lemma lem5052690 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5052691 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x : A) : (term549 A B s f k x) = (term549 A B s f k x).
Proof. exact (MK_COMB (@lem5052690) (@lem5052689 A B s f k x)). Qed.
Lemma lem5052692 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x : A) : (term550 A B s f k x) = (term551 A B s f k x).
Proof. exact (MK_COMB (@lem5052691 A B s f k x) (@lem5052686 A B s f k x)). Qed.
Lemma lem5052693 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x : A) : (term552 A B s f k x) = (term550 A B s f k x).
Proof. exact (@lem17646 (term457 A B s x f k) (k x)). Qed.
Lemma lem5052694 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x : A) : (term552 A B s f k x) = (term551 A B s f k x).
Proof. exact (TRANS (@lem5052693 A B s f k x) (@lem5052692 A B s f k x)). Qed.
Lemma lem5052695 {A : Type'} (P : A -> Prop) : (term141 A P) = (term142 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem5052696 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term553 A B s f k) = (term554 A B s f k).
Proof. exact (@lem5052695 A (term460 A B s f k)). Qed.
Lemma lem5052697 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x : A) : (term555 A B s f k x) = ((term457 A B s x f k) = (k x)).
Proof. exact (eq_refl (term555 A B s f k x)). Qed.
Lemma lem5052698 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5052699 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x : A) : (term556 A B s f k x) = (term552 A B s f k x).
Proof. exact (MK_COMB (@lem5052698) (@lem5052697 A B s f k x)). Qed.
Lemma lem5052700 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x : A) : (term556 A B s f k x) = (term551 A B s f k x).
Proof. exact (TRANS (@lem5052699 A B s f k x) (@lem5052694 A B s f k x)). Qed.
Lemma lem5052701 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term557 A B s f k) = (term558 A B s f k).
Proof. exact (fun_ext (fun x : A => @lem5052700 A B s f k x)). Qed.
Lemma lem5052702 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5052703 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term554 A B s f k) = (term559 A B s f k).
Proof. exact (MK_COMB (@lem5052702 A) (@lem5052701 A B s f k)). Qed.
Lemma lem5052704 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term553 A B s f k) = (term559 A B s f k).
Proof. exact (TRANS (@lem5052696 A B s f k) (@lem5052703 A B s f k)). Qed.
Lemma lem5052705 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5052706 {A B : Type'} (f : A -> B) (k : A -> Prop) (u : B -> Prop) : (term560 A B f k u) = (term561 A B f k u).
Proof. exact (MK_COMB (@lem5052705) (@lem5052646 A B f k u)). Qed.
Lemma lem5052707 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term562 A B u s f k) = (term563 A B u s f k).
Proof. exact (MK_COMB (@lem5052706 A B f k u) (@lem5052704 A B s f k)). Qed.
Lemma lem5052708 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term487 A B u s f k) = (term562 A B u s f k).
Proof. exact (@lem17045 (term416 A B f k u) (term461 A B s f k)). Qed.
Lemma lem5052709 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term487 A B u s f k) = (term563 A B u s f k).
Proof. exact (TRANS (@lem5052708 A B u s f k) (@lem5052707 A B u s f k)). Qed.
Lemma lem5052791 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term564 A P Q) = (term565 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem5052792 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term564 A P Q) = (term565 A P Q).
Proof. exact (@lem5052791 A P Q). Qed.
Lemma lem5052793 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term566 A B s f k) = (term567 A B s f k).
Proof. exact (@lem5052792 A (term568 A B s f k) (term569 A B s f k)). Qed.
Lemma lem5052794 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x : A) : (term570 A B s f k x) = (term548 A B s f k x).
Proof. exact (eq_refl (term570 A B s f k x)). Qed.
Lemma lem5052795 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5052796 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x : A) : (term571 A B s f k x) = (term549 A B s f k x).
Proof. exact (MK_COMB (@lem5052795) (@lem5052794 A B s f k x)). Qed.
Lemma lem5052797 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x : A) : (term572 A B s f k x) = (term546 A B s f k x).
Proof. exact (eq_refl (term572 A B s f k x)). Qed.
Lemma lem5052798 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x : A) : (term573 A B s f k x) = (term551 A B s f k x).
Proof. exact (MK_COMB (@lem5052796 A B s f k x) (@lem5052797 A B s f k x)). Qed.
Lemma lem5052799 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term574 A B s f k) = (term558 A B s f k).
Proof. exact (fun_ext (fun x : A => @lem5052798 A B s f k x)). Qed.
Lemma lem5052800 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5052801 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term566 A B s f k) = (term559 A B s f k).
Proof. exact (MK_COMB (@lem5052800 A) (@lem5052799 A B s f k)). Qed.
Lemma lem5052802 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5052803 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term575 A B s f k) = (term576 A B s f k).
Proof. exact (MK_COMB (@lem5052802) (@lem5052801 A B s f k)). Qed.
Lemma lem5052804 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x : A) : (term570 A B s f k x) = (term548 A B s f k x).
Proof. exact (eq_refl (term570 A B s f k x)). Qed.
Lemma lem5052805 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term577 A B s f k) = (term568 A B s f k).
Proof. exact (fun_ext (fun x : A => @lem5052804 A B s f k x)). Qed.
Lemma lem5052806 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5052807 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term578 A B s f k) = (term579 A B s f k).
Proof. exact (MK_COMB (@lem5052806 A) (@lem5052805 A B s f k)). Qed.
Lemma lem5052808 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5052809 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term580 A B s f k) = (term581 A B s f k).
Proof. exact (MK_COMB (@lem5052808) (@lem5052807 A B s f k)). Qed.
Lemma lem5052810 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x : A) : (term572 A B s f k x) = (term546 A B s f k x).
Proof. exact (eq_refl (term572 A B s f k x)). Qed.
Lemma lem5052811 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term582 A B s f k) = (term569 A B s f k).
Proof. exact (fun_ext (fun x : A => @lem5052810 A B s f k x)). Qed.
Lemma lem5052812 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5052813 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term583 A B s f k) = (term584 A B s f k).
Proof. exact (MK_COMB (@lem5052812 A) (@lem5052811 A B s f k)). Qed.
Lemma lem5052814 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term567 A B s f k) = (term585 A B s f k).
Proof. exact (MK_COMB (@lem5052809 A B s f k) (@lem5052813 A B s f k)). Qed.
Lemma lem5052815 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) : ((term566 A B s f k) = (term567 A B s f k)) = ((term559 A B s f k) = (term585 A B s f k)).
Proof. exact (MK_COMB (@lem5052803 A B s f k) (@lem5052814 A B s f k)). Qed.
Lemma lem5052816 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term559 A B s f k) = (term585 A B s f k).
Proof. exact (EQ_MP (@lem5052815 A B s f k) (@lem5052793 A B s f k)). Qed.
Lemma lem5052977 {A B : Type'} (f : A -> B) (k : A -> Prop) (u : B -> Prop) : (term561 A B f k u) = (term561 A B f k u).
Proof. exact (eq_refl (term561 A B f k u)). Qed.
Lemma lem5052978 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term563 A B u s f k) = (term586 A B u s f k).
Proof. exact (MK_COMB (@lem5052977 A B f k u) (@lem5052816 A B s f k)). Qed.
Lemma lem5052980 {A : Type'} (P : A -> Prop) (Q : Prop) : (term587 A P Q) = (term588 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5052981 {A : Type'} (P : A -> Prop) (Q : Prop) : (term587 A P Q) = (term588 A P Q).
Proof. exact (@lem5052980 A P Q). Qed.
Lemma lem5052982 {A B : Type'} (f : A -> B) (k : A -> Prop) (u : B -> Prop) (x : B) : (term589 A B f k u x) = (term590 A B f k u x).
Proof. exact (@lem5052981 A (term411 A B x f k) (term240 B u x)). Qed.
Lemma lem5052983 {A B : Type'} (x : B) (f : A -> B) (k : A -> Prop) (x' : A) : (term494 A B x f k x') = (term409 A B x f k x').
Proof. exact (eq_refl (term494 A B x f k x')). Qed.
Lemma lem5052984 {A B : Type'} (x : B) (f : A -> B) (k : A -> Prop) : (term591 A B x f k) = (term411 A B x f k).
Proof. exact (fun_ext (fun x' : A => @lem5052983 A B x f k x')). Qed.
Lemma lem5052985 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5052986 {A B : Type'} (x : B) (f : A -> B) (k : A -> Prop) : (term592 A B x f k) = (term412 A B x f k).
Proof. exact (MK_COMB (@lem5052985 A) (@lem5052984 A B x f k)). Qed.
Lemma lem5052987 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5052988 {A B : Type'} (x : B) (f : A -> B) (k : A -> Prop) : (term593 A B x f k) = (term521 A B x f k).
Proof. exact (MK_COMB (@lem5052987) (@lem5052986 A B x f k)). Qed.
Lemma lem5052989 {B : Type'} (u : B -> Prop) (x : B) : (term240 B u x) = (term240 B u x).
Proof. exact (eq_refl (term240 B u x)). Qed.
Lemma lem5052990 {A B : Type'} (f : A -> B) (k : A -> Prop) (u : B -> Prop) (x : B) : (term589 A B f k u x) = (term522 A B f k u x).
Proof. exact (MK_COMB (@lem5052988 A B x f k) (@lem5052989 B u x)). Qed.
Lemma lem5052991 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5052992 {A B : Type'} (f : A -> B) (k : A -> Prop) (u : B -> Prop) (x : B) : (term594 A B f k u x) = (term595 A B f k u x).
Proof. exact (MK_COMB (@lem5052991) (@lem5052990 A B f k u x)). Qed.
Lemma lem5052993 {A B : Type'} (x : B) (f : A -> B) (k : A -> Prop) (x' : A) : (term494 A B x f k x') = (term409 A B x f k x').
Proof. exact (eq_refl (term494 A B x f k x')). Qed.
Lemma lem5052994 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5052995 {A B : Type'} (x : B) (f : A -> B) (k : A -> Prop) (x' : A) : (term596 A B x f k x') = (term597 A B x f k x').
Proof. exact (MK_COMB (@lem5052994) (@lem5052993 A B x f k x')). Qed.
Lemma lem5052996 {B : Type'} (u : B -> Prop) (x : B) : (term240 B u x) = (term240 B u x).
Proof. exact (eq_refl (term240 B u x)). Qed.
Lemma lem5052997 {A B : Type'} (f : A -> B) (k : A -> Prop) (x : A) (u : B -> Prop) (x' : B) : (term598 A B f k x u x') = (term599 A B f k x u x').
Proof. exact (MK_COMB (@lem5052995 A B x' f k x) (@lem5052996 B u x')). Qed.
Lemma lem5052998 {A B : Type'} (f : A -> B) (k : A -> Prop) (u : B -> Prop) (x : B) : (term600 A B f k u x) = (term601 A B f k u x).
Proof. exact (fun_ext (fun x' : A => @lem5052997 A B f k x' u x)). Qed.
Lemma lem5052999 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5053000 {A B : Type'} (f : A -> B) (k : A -> Prop) (u : B -> Prop) (x : B) : (term590 A B f k u x) = (term602 A B f k u x).
Proof. exact (MK_COMB (@lem5052999 A) (@lem5052998 A B f k u x)). Qed.
Lemma lem5053001 {A B : Type'} (f : A -> B) (k : A -> Prop) (u : B -> Prop) (x : B) : ((term589 A B f k u x) = (term590 A B f k u x)) = ((term522 A B f k u x) = (term602 A B f k u x)).
Proof. exact (MK_COMB (@lem5052992 A B f k u x) (@lem5053000 A B f k u x)). Qed.
Lemma lem5053002 {A B : Type'} (f : A -> B) (k : A -> Prop) (u : B -> Prop) (x : B) : (term522 A B f k u x) = (term602 A B f k u x).
Proof. exact (EQ_MP (@lem5053001 A B f k u x) (@lem5052982 A B f k u x)). Qed.
Lemma lem5053003 {A B : Type'} (f : A -> B) (k : A -> Prop) (u : B -> Prop) : (term529 A B f k u) = (term603 A B f k u).
Proof. exact (fun_ext (fun x : B => @lem5053002 A B f k u x)). Qed.
Lemma lem5053004 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5053005 {A B : Type'} (f : A -> B) (k : A -> Prop) (u : B -> Prop) : (term530 A B f k u) = (term604 A B f k u).
Proof. exact (MK_COMB (@lem5053004 B) (@lem5053003 A B f k u)). Qed.
Lemma lem5053006 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5053007 {A B : Type'} (f : A -> B) (k : A -> Prop) (u : B -> Prop) : (term561 A B f k u) = (term605 A B f k u).
Proof. exact (MK_COMB (@lem5053006) (@lem5053005 A B f k u)). Qed.
Lemma lem5053009 {A : Type'} (P : Prop) (Q : A -> Prop) : (term606 A P Q) = (term607 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5053010 {A : Type'} (P : Prop) (Q : A -> Prop) : (term606 A P Q) = (term607 A P Q).
Proof. exact (@lem5053009 A P Q). Qed.
Lemma lem5053011 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (k : A -> Prop) : (term608 A B s x f k) = (term609 A B s x f k).
Proof. exact (@lem5053010 A (s x) (term455 A B x f k)). Qed.
Lemma lem5053012 {A B : Type'} (x : A) (f : A -> B) (k : A -> Prop) (x' : A) : (term535 A B x f k x') = (term453 A B x f k x').
Proof. exact (eq_refl (term535 A B x f k x')). Qed.
Lemma lem5053013 {A B : Type'} (x : A) (f : A -> B) (k : A -> Prop) : (term610 A B x f k) = (term455 A B x f k).
Proof. exact (fun_ext (fun x' : A => @lem5053012 A B x f k x')). Qed.
Lemma lem5053014 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5053015 {A B : Type'} (x : A) (f : A -> B) (k : A -> Prop) : (term611 A B x f k) = (term456 A B x f k).
Proof. exact (MK_COMB (@lem5053014 A) (@lem5053013 A B x f k)). Qed.
Lemma lem5053016 {A : Type'} (s : A -> Prop) (x : A) : (term99 A s x) = (term99 A s x).
Proof. exact (eq_refl (term99 A s x)). Qed.
Lemma lem5053017 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (k : A -> Prop) : (term608 A B s x f k) = (term457 A B s x f k).
Proof. exact (MK_COMB (@lem5053016 A s x) (@lem5053015 A B x f k)). Qed.
Lemma lem5053018 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5053019 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (k : A -> Prop) : (term612 A B s x f k) = (term458 A B s x f k).
Proof. exact (MK_COMB (@lem5053018) (@lem5053017 A B s x f k)). Qed.
Lemma lem5053020 {A B : Type'} (x : A) (f : A -> B) (k : A -> Prop) (x' : A) : (term535 A B x f k x') = (term453 A B x f k x').
Proof. exact (eq_refl (term535 A B x f k x')). Qed.
Lemma lem5053021 {A : Type'} (s : A -> Prop) (x : A) : (term99 A s x) = (term99 A s x).
Proof. exact (eq_refl (term99 A s x)). Qed.
Lemma lem5053022 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (k : A -> Prop) (x' : A) : (term613 A B s x f k x') = (term614 A B s x f k x').
Proof. exact (MK_COMB (@lem5053021 A s x) (@lem5053020 A B x f k x')). Qed.
Lemma lem5053023 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (k : A -> Prop) : (term615 A B s x f k) = (term616 A B s x f k).
Proof. exact (fun_ext (fun x' : A => @lem5053022 A B s x f k x')). Qed.
Lemma lem5053024 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5053025 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (k : A -> Prop) : (term609 A B s x f k) = (term617 A B s x f k).
Proof. exact (MK_COMB (@lem5053024 A) (@lem5053023 A B s x f k)). Qed.
Lemma lem5053026 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (k : A -> Prop) : ((term608 A B s x f k) = (term609 A B s x f k)) = ((term457 A B s x f k) = (term617 A B s x f k)).
Proof. exact (MK_COMB (@lem5053019 A B s x f k) (@lem5053025 A B s x f k)). Qed.
Lemma lem5053027 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (k : A -> Prop) : (term457 A B s x f k) = (term617 A B s x f k).
Proof. exact (EQ_MP (@lem5053026 A B s x f k) (@lem5053011 A B s x f k)). Qed.
Lemma lem5053028 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5053029 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (k : A -> Prop) : (term547 A B s x f k) = (term618 A B s x f k).
Proof. exact (MK_COMB (@lem5053028) (@lem5053027 A B s x f k)). Qed.
Lemma lem5053030 {A : Type'} (k : A -> Prop) (x : A) : (term240 A k x) = (term240 A k x).
Proof. exact (eq_refl (term240 A k x)). Qed.
Lemma lem5053031 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x : A) : (term548 A B s f k x) = (term619 A B s f k x).
Proof. exact (MK_COMB (@lem5053029 A B s x f k) (@lem5053030 A k x)). Qed.
Lemma lem5053033 {A : Type'} (P : A -> Prop) (Q : Prop) : (term587 A P Q) = (term588 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5053034 {A : Type'} (P : A -> Prop) (Q : Prop) : (term587 A P Q) = (term588 A P Q).
Proof. exact (@lem5053033 A P Q). Qed.
Lemma lem5053035 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x : A) : (term620 A B s f k x) = (term621 A B s f k x).
Proof. exact (@lem5053034 A (term616 A B s x f k) (term240 A k x)). Qed.
Lemma lem5053036 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (k : A -> Prop) (x' : A) : (term622 A B s x f k x') = (term614 A B s x f k x').
Proof. exact (eq_refl (term622 A B s x f k x')). Qed.
Lemma lem5053037 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (k : A -> Prop) : (term623 A B s x f k) = (term616 A B s x f k).
Proof. exact (fun_ext (fun x' : A => @lem5053036 A B s x f k x')). Qed.
Lemma lem5053038 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5053039 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (k : A -> Prop) : (term624 A B s x f k) = (term617 A B s x f k).
Proof. exact (MK_COMB (@lem5053038 A) (@lem5053037 A B s x f k)). Qed.
Lemma lem5053040 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5053041 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (k : A -> Prop) : (term625 A B s x f k) = (term618 A B s x f k).
Proof. exact (MK_COMB (@lem5053040) (@lem5053039 A B s x f k)). Qed.
Lemma lem5053042 {A : Type'} (k : A -> Prop) (x : A) : (term240 A k x) = (term240 A k x).
Proof. exact (eq_refl (term240 A k x)). Qed.
Lemma lem5053043 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x : A) : (term620 A B s f k x) = (term619 A B s f k x).
Proof. exact (MK_COMB (@lem5053041 A B s x f k) (@lem5053042 A k x)). Qed.
Lemma lem5053044 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5053045 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x : A) : (term626 A B s f k x) = (term627 A B s f k x).
Proof. exact (MK_COMB (@lem5053044) (@lem5053043 A B s f k x)). Qed.
Lemma lem5053046 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (k : A -> Prop) (x' : A) : (term622 A B s x f k x') = (term614 A B s x f k x').
Proof. exact (eq_refl (term622 A B s x f k x')). Qed.
Lemma lem5053047 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5053048 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (k : A -> Prop) (x' : A) : (term628 A B s x f k x') = (term629 A B s x f k x').
Proof. exact (MK_COMB (@lem5053047) (@lem5053046 A B s x f k x')). Qed.
Lemma lem5053049 {A : Type'} (k : A -> Prop) (x : A) : (term240 A k x) = (term240 A k x).
Proof. exact (eq_refl (term240 A k x)). Qed.
Lemma lem5053050 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (k : A -> Prop) (x : A) : (term630 A B s f x' k x) = (term631 A B s f x' k x).
Proof. exact (MK_COMB (@lem5053048 A B s x f k x') (@lem5053049 A k x)). Qed.
Lemma lem5053051 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x : A) : (term632 A B s f k x) = (term633 A B s f k x).
Proof. exact (fun_ext (fun x' : A => @lem5053050 A B s f x' k x)). Qed.
Lemma lem5053052 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5053053 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x : A) : (term621 A B s f k x) = (term634 A B s f k x).
Proof. exact (MK_COMB (@lem5053052 A) (@lem5053051 A B s f k x)). Qed.
Lemma lem5053054 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x : A) : ((term620 A B s f k x) = (term621 A B s f k x)) = ((term619 A B s f k x) = (term634 A B s f k x)).
Proof. exact (MK_COMB (@lem5053045 A B s f k x) (@lem5053053 A B s f k x)). Qed.
Lemma lem5053055 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x : A) : (term619 A B s f k x) = (term634 A B s f k x).
Proof. exact (EQ_MP (@lem5053054 A B s f k x) (@lem5053035 A B s f k x)). Qed.
Lemma lem5053056 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x : A) : (term548 A B s f k x) = (term634 A B s f k x).
Proof. exact (TRANS (@lem5053031 A B s f k x) (@lem5053055 A B s f k x)). Qed.
Lemma lem5053057 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term568 A B s f k) = (term635 A B s f k).
Proof. exact (fun_ext (fun x : A => @lem5053056 A B s f k x)). Qed.
Lemma lem5053058 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5053059 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term579 A B s f k) = (term636 A B s f k).
Proof. exact (MK_COMB (@lem5053058 A) (@lem5053057 A B s f k)). Qed.
Lemma lem5053060 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5053061 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term581 A B s f k) = (term637 A B s f k).
Proof. exact (MK_COMB (@lem5053060) (@lem5053059 A B s f k)). Qed.
Lemma lem5053062 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term584 A B s f k) = (term584 A B s f k).
Proof. exact (eq_refl (term584 A B s f k)). Qed.
Lemma lem5053063 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term585 A B s f k) = (term638 A B s f k).
Proof. exact (MK_COMB (@lem5053061 A B s f k) (@lem5053062 A B s f k)). Qed.
Lemma lem5053065 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term565 A P Q) = (term564 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5053066 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term565 A P Q) = (term564 A P Q).
Proof. exact (@lem5053065 A P Q). Qed.
Lemma lem5053067 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term639 A B s f k) = (term640 A B s f k).
Proof. exact (@lem5053066 A (term635 A B s f k) (term569 A B s f k)). Qed.
Lemma lem5053068 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x : A) : (term641 A B s f k x) = (term634 A B s f k x).
Proof. exact (eq_refl (term641 A B s f k x)). Qed.
Lemma lem5053069 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term642 A B s f k) = (term635 A B s f k).
Proof. exact (fun_ext (fun x : A => @lem5053068 A B s f k x)). Qed.
Lemma lem5053070 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5053071 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term643 A B s f k) = (term636 A B s f k).
Proof. exact (MK_COMB (@lem5053070 A) (@lem5053069 A B s f k)). Qed.
Lemma lem5053072 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5053073 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term644 A B s f k) = (term637 A B s f k).
Proof. exact (MK_COMB (@lem5053072) (@lem5053071 A B s f k)). Qed.
Lemma lem5053074 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x : A) : (term572 A B s f k x) = (term546 A B s f k x).
Proof. exact (eq_refl (term572 A B s f k x)). Qed.
Lemma lem5053075 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term582 A B s f k) = (term569 A B s f k).
Proof. exact (fun_ext (fun x : A => @lem5053074 A B s f k x)). Qed.
Lemma lem5053076 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5053077 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term583 A B s f k) = (term584 A B s f k).
Proof. exact (MK_COMB (@lem5053076 A) (@lem5053075 A B s f k)). Qed.
Lemma lem5053078 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term639 A B s f k) = (term638 A B s f k).
Proof. exact (MK_COMB (@lem5053073 A B s f k) (@lem5053077 A B s f k)). Qed.
Lemma lem5053079 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5053080 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term645 A B s f k) = (term646 A B s f k).
Proof. exact (MK_COMB (@lem5053079) (@lem5053078 A B s f k)). Qed.
Lemma lem5053081 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x : A) : (term641 A B s f k x) = (term634 A B s f k x).
Proof. exact (eq_refl (term641 A B s f k x)). Qed.
Lemma lem5053082 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5053083 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x : A) : (term647 A B s f k x) = (term648 A B s f k x).
Proof. exact (MK_COMB (@lem5053082) (@lem5053081 A B s f k x)). Qed.
Lemma lem5053084 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x : A) : (term572 A B s f k x) = (term546 A B s f k x).
Proof. exact (eq_refl (term572 A B s f k x)). Qed.
Lemma lem5053085 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x : A) : (term649 A B s f k x) = (term650 A B s f k x).
Proof. exact (MK_COMB (@lem5053083 A B s f k x) (@lem5053084 A B s f k x)). Qed.
Lemma lem5053086 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term651 A B s f k) = (term652 A B s f k).
Proof. exact (fun_ext (fun x : A => @lem5053085 A B s f k x)). Qed.
Lemma lem5053087 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5053088 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term640 A B s f k) = (term653 A B s f k).
Proof. exact (MK_COMB (@lem5053087 A) (@lem5053086 A B s f k)). Qed.
Lemma lem5053089 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) : ((term639 A B s f k) = (term640 A B s f k)) = ((term638 A B s f k) = (term653 A B s f k)).
Proof. exact (MK_COMB (@lem5053080 A B s f k) (@lem5053088 A B s f k)). Qed.
Lemma lem5053090 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term638 A B s f k) = (term653 A B s f k).
Proof. exact (EQ_MP (@lem5053089 A B s f k) (@lem5053067 A B s f k)). Qed.
Lemma lem5053092 {A : Type'} (P : A -> Prop) (Q : Prop) : (term199 A P Q) = (term200 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5053093 {A : Type'} (P : A -> Prop) (Q : Prop) : (term199 A P Q) = (term200 A P Q).
Proof. exact (@lem5053092 A P Q). Qed.
Lemma lem5053094 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x : A) : (term654 A B s f k x) = (term655 A B s f k x).
Proof. exact (@lem5053093 A (term633 A B s f k x) (term546 A B s f k x)). Qed.
Lemma lem5053095 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (k : A -> Prop) (x : A) : (term656 A B s f k x x') = (term631 A B s f x' k x).
Proof. exact (eq_refl (term656 A B s f k x x')). Qed.
Lemma lem5053096 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x : A) : (term657 A B s f k x) = (term633 A B s f k x).
Proof. exact (fun_ext (fun x' : A => @lem5053095 A B s f x' k x)). Qed.
Lemma lem5053097 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5053098 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x : A) : (term658 A B s f k x) = (term634 A B s f k x).
Proof. exact (MK_COMB (@lem5053097 A) (@lem5053096 A B s f k x)). Qed.
Lemma lem5053099 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5053100 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x : A) : (term659 A B s f k x) = (term648 A B s f k x).
Proof. exact (MK_COMB (@lem5053099) (@lem5053098 A B s f k x)). Qed.
Lemma lem5053101 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x : A) : (term546 A B s f k x) = (term546 A B s f k x).
Proof. exact (eq_refl (term546 A B s f k x)). Qed.
Lemma lem5053102 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x : A) : (term654 A B s f k x) = (term650 A B s f k x).
Proof. exact (MK_COMB (@lem5053100 A B s f k x) (@lem5053101 A B s f k x)). Qed.
Lemma lem5053103 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5053104 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x : A) : (term660 A B s f k x) = (term661 A B s f k x).
Proof. exact (MK_COMB (@lem5053103) (@lem5053102 A B s f k x)). Qed.
Lemma lem5053105 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (k : A -> Prop) (x : A) : (term656 A B s f k x x') = (term631 A B s f x' k x).
Proof. exact (eq_refl (term656 A B s f k x x')). Qed.
Lemma lem5053106 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5053107 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (k : A -> Prop) (x : A) : (term662 A B s f k x x') = (term663 A B s f x' k x).
Proof. exact (MK_COMB (@lem5053106) (@lem5053105 A B s f x' k x)). Qed.
Lemma lem5053108 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x : A) : (term546 A B s f k x) = (term546 A B s f k x).
Proof. exact (eq_refl (term546 A B s f k x)). Qed.
Lemma lem5053109 {A B : Type'} (x' : A) (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x : A) : (term664 A B x' s f k x) = (term665 A B x' s f k x).
Proof. exact (MK_COMB (@lem5053107 A B s f x' k x) (@lem5053108 A B s f k x)). Qed.
Lemma lem5053110 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x : A) : (term666 A B s f k x) = (term667 A B s f k x).
Proof. exact (fun_ext (fun x' : A => @lem5053109 A B x' s f k x)). Qed.
Lemma lem5053111 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5053112 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x : A) : (term655 A B s f k x) = (term668 A B s f k x).
Proof. exact (MK_COMB (@lem5053111 A) (@lem5053110 A B s f k x)). Qed.
Lemma lem5053113 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x : A) : ((term654 A B s f k x) = (term655 A B s f k x)) = ((term650 A B s f k x) = (term668 A B s f k x)).
Proof. exact (MK_COMB (@lem5053104 A B s f k x) (@lem5053112 A B s f k x)). Qed.
Lemma lem5053114 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x : A) : (term650 A B s f k x) = (term668 A B s f k x).
Proof. exact (EQ_MP (@lem5053113 A B s f k x) (@lem5053094 A B s f k x)). Qed.
Lemma lem5053115 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term652 A B s f k) = (term669 A B s f k).
Proof. exact (fun_ext (fun x : A => @lem5053114 A B s f k x)). Qed.
Lemma lem5053116 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5053117 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term653 A B s f k) = (term670 A B s f k).
Proof. exact (MK_COMB (@lem5053116 A) (@lem5053115 A B s f k)). Qed.
Lemma lem5053118 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term638 A B s f k) = (term670 A B s f k).
Proof. exact (TRANS (@lem5053090 A B s f k) (@lem5053117 A B s f k)). Qed.
Lemma lem5053119 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term585 A B s f k) = (term670 A B s f k).
Proof. exact (TRANS (@lem5053063 A B s f k) (@lem5053118 A B s f k)). Qed.
Lemma lem5053120 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term586 A B u s f k) = (term671 A B u s f k).
Proof. exact (MK_COMB (@lem5053007 A B f k u) (@lem5053119 A B s f k)). Qed.
Lemma lem5053124 {A : Type'} (P : A -> Prop) (Q : Prop) : (term199 A P Q) = (term200 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5053125 {B : Type'} (P : B -> Prop) (Q : Prop) : (term199 B P Q) = (term200 B P Q).
Proof. exact (@lem5053124 B P Q). Qed.
Lemma lem5053126 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term672 A B u s f k) = (term673 A B u s f k).
Proof. exact (@lem5053125 B (term603 A B f k u) (term670 A B s f k)). Qed.
Lemma lem5053127 {A B : Type'} (f : A -> B) (k : A -> Prop) (u : B -> Prop) (x : B) : (term674 A B f k u x) = (term602 A B f k u x).
Proof. exact (eq_refl (term674 A B f k u x)). Qed.
Lemma lem5053128 {A B : Type'} (f : A -> B) (k : A -> Prop) (u : B -> Prop) : (term675 A B f k u) = (term603 A B f k u).
Proof. exact (fun_ext (fun x : B => @lem5053127 A B f k u x)). Qed.
Lemma lem5053129 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5053130 {A B : Type'} (f : A -> B) (k : A -> Prop) (u : B -> Prop) : (term676 A B f k u) = (term604 A B f k u).
Proof. exact (MK_COMB (@lem5053129 B) (@lem5053128 A B f k u)). Qed.
Lemma lem5053131 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5053132 {A B : Type'} (f : A -> B) (k : A -> Prop) (u : B -> Prop) : (term677 A B f k u) = (term605 A B f k u).
Proof. exact (MK_COMB (@lem5053131) (@lem5053130 A B f k u)). Qed.
Lemma lem5053133 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term670 A B s f k) = (term670 A B s f k).
Proof. exact (eq_refl (term670 A B s f k)). Qed.
Lemma lem5053134 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term672 A B u s f k) = (term671 A B u s f k).
Proof. exact (MK_COMB (@lem5053132 A B f k u) (@lem5053133 A B s f k)). Qed.
Lemma lem5053135 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5053136 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term678 A B u s f k) = (term679 A B u s f k).
Proof. exact (MK_COMB (@lem5053135) (@lem5053134 A B u s f k)). Qed.
Lemma lem5053137 {A B : Type'} (f : A -> B) (k : A -> Prop) (u : B -> Prop) (x : B) : (term674 A B f k u x) = (term602 A B f k u x).
Proof. exact (eq_refl (term674 A B f k u x)). Qed.
Lemma lem5053138 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5053139 {A B : Type'} (f : A -> B) (k : A -> Prop) (u : B -> Prop) (x : B) : (term680 A B f k u x) = (term681 A B f k u x).
Proof. exact (MK_COMB (@lem5053138) (@lem5053137 A B f k u x)). Qed.
Lemma lem5053140 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term670 A B s f k) = (term670 A B s f k).
Proof. exact (eq_refl (term670 A B s f k)). Qed.
Lemma lem5053141 {A B : Type'} (u : B -> Prop) (x : B) (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term682 A B u x s f k) = (term683 A B u x s f k).
Proof. exact (MK_COMB (@lem5053139 A B f k u x) (@lem5053140 A B s f k)). Qed.
Lemma lem5053142 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term684 A B u s f k) = (term685 A B u s f k).
Proof. exact (fun_ext (fun x : B => @lem5053141 A B u x s f k)). Qed.
Lemma lem5053143 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5053144 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term673 A B u s f k) = (term686 A B u s f k).
Proof. exact (MK_COMB (@lem5053143 B) (@lem5053142 A B u s f k)). Qed.
Lemma lem5053145 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) : ((term672 A B u s f k) = (term673 A B u s f k)) = ((term671 A B u s f k) = (term686 A B u s f k)).
Proof. exact (MK_COMB (@lem5053136 A B u s f k) (@lem5053144 A B u s f k)). Qed.
Lemma lem5053146 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term671 A B u s f k) = (term686 A B u s f k).
Proof. exact (EQ_MP (@lem5053145 A B u s f k) (@lem5053126 A B u s f k)). Qed.
Lemma lem5053148 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term565 A P Q) = (term564 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5053149 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term565 A P Q) = (term564 A P Q).
Proof. exact (@lem5053148 A P Q). Qed.
Lemma lem5053150 {A B : Type'} (u : B -> Prop) (x : B) (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term687 A B u x s f k) = (term688 A B u x s f k).
Proof. exact (@lem5053149 A (term601 A B f k u x) (term669 A B s f k)). Qed.
Lemma lem5053151 {A B : Type'} (f : A -> B) (k : A -> Prop) (x : A) (u : B -> Prop) (x' : B) : (term689 A B f k u x' x) = (term599 A B f k x u x').
Proof. exact (eq_refl (term689 A B f k u x' x)). Qed.
Lemma lem5053152 {A B : Type'} (f : A -> B) (k : A -> Prop) (u : B -> Prop) (x : B) : (term690 A B f k u x) = (term601 A B f k u x).
Proof. exact (fun_ext (fun x' : A => @lem5053151 A B f k x' u x)). Qed.
Lemma lem5053153 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5053154 {A B : Type'} (f : A -> B) (k : A -> Prop) (u : B -> Prop) (x : B) : (term691 A B f k u x) = (term602 A B f k u x).
Proof. exact (MK_COMB (@lem5053153 A) (@lem5053152 A B f k u x)). Qed.
Lemma lem5053155 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5053156 {A B : Type'} (f : A -> B) (k : A -> Prop) (u : B -> Prop) (x : B) : (term692 A B f k u x) = (term681 A B f k u x).
Proof. exact (MK_COMB (@lem5053155) (@lem5053154 A B f k u x)). Qed.
Lemma lem5053157 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x : A) : (term693 A B s f k x) = (term668 A B s f k x).
Proof. exact (eq_refl (term693 A B s f k x)). Qed.
Lemma lem5053158 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term694 A B s f k) = (term669 A B s f k).
Proof. exact (fun_ext (fun x : A => @lem5053157 A B s f k x)). Qed.
Lemma lem5053159 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5053160 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term695 A B s f k) = (term670 A B s f k).
Proof. exact (MK_COMB (@lem5053159 A) (@lem5053158 A B s f k)). Qed.
Lemma lem5053161 {A B : Type'} (u : B -> Prop) (x : B) (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term687 A B u x s f k) = (term683 A B u x s f k).
Proof. exact (MK_COMB (@lem5053156 A B f k u x) (@lem5053160 A B s f k)). Qed.
Lemma lem5053162 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5053163 {A B : Type'} (u : B -> Prop) (x : B) (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term696 A B u x s f k) = (term697 A B u x s f k).
Proof. exact (MK_COMB (@lem5053162) (@lem5053161 A B u x s f k)). Qed.
Lemma lem5053164 {A B : Type'} (f : A -> B) (k : A -> Prop) (x : A) (u : B -> Prop) (x' : B) : (term689 A B f k u x' x) = (term599 A B f k x u x').
Proof. exact (eq_refl (term689 A B f k u x' x)). Qed.
Lemma lem5053165 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5053166 {A B : Type'} (f : A -> B) (k : A -> Prop) (x : A) (u : B -> Prop) (x' : B) : (term698 A B f k u x' x) = (term699 A B f k x u x').
Proof. exact (MK_COMB (@lem5053165) (@lem5053164 A B f k x u x')). Qed.
Lemma lem5053167 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x : A) : (term693 A B s f k x) = (term668 A B s f k x).
Proof. exact (eq_refl (term693 A B s f k x)). Qed.
Lemma lem5053168 {A B : Type'} (u : B -> Prop) (x : B) (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x' : A) : (term700 A B u x s f k x') = (term701 A B u x s f k x').
Proof. exact (MK_COMB (@lem5053166 A B f k x' u x) (@lem5053167 A B s f k x')). Qed.
Lemma lem5053169 {A B : Type'} (u : B -> Prop) (x : B) (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term702 A B u x s f k) = (term703 A B u x s f k).
Proof. exact (fun_ext (fun x' : A => @lem5053168 A B u x s f k x')). Qed.
Lemma lem5053170 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5053171 {A B : Type'} (u : B -> Prop) (x : B) (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term688 A B u x s f k) = (term704 A B u x s f k).
Proof. exact (MK_COMB (@lem5053170 A) (@lem5053169 A B u x s f k)). Qed.
Lemma lem5053172 {A B : Type'} (u : B -> Prop) (x : B) (s : A -> Prop) (f : A -> B) (k : A -> Prop) : ((term687 A B u x s f k) = (term688 A B u x s f k)) = ((term683 A B u x s f k) = (term704 A B u x s f k)).
Proof. exact (MK_COMB (@lem5053163 A B u x s f k) (@lem5053171 A B u x s f k)). Qed.
Lemma lem5053173 {A B : Type'} (u : B -> Prop) (x : B) (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term683 A B u x s f k) = (term704 A B u x s f k).
Proof. exact (EQ_MP (@lem5053172 A B u x s f k) (@lem5053150 A B u x s f k)). Qed.
Lemma lem5053175 {A : Type'} (P : Prop) (Q : A -> Prop) : (term216 A P Q) = (term217 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5053176 {A : Type'} (P : Prop) (Q : A -> Prop) : (term216 A P Q) = (term217 A P Q).
Proof. exact (@lem5053175 A P Q). Qed.
Lemma lem5053177 {A B : Type'} (u : B -> Prop) (x : B) (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x' : A) : (term705 A B u x s f k x') = (term706 A B u x s f k x').
Proof. exact (@lem5053176 A (term599 A B f k x' u x) (term667 A B s f k x')). Qed.
Lemma lem5053178 {A B : Type'} (x' : A) (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x : A) : (term707 A B s f k x x') = (term665 A B x' s f k x).
Proof. exact (eq_refl (term707 A B s f k x x')). Qed.
Lemma lem5053179 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x : A) : (term708 A B s f k x) = (term667 A B s f k x).
Proof. exact (fun_ext (fun x' : A => @lem5053178 A B x' s f k x)). Qed.
Lemma lem5053180 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5053181 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x : A) : (term709 A B s f k x) = (term668 A B s f k x).
Proof. exact (MK_COMB (@lem5053180 A) (@lem5053179 A B s f k x)). Qed.
Lemma lem5053182 {A B : Type'} (f : A -> B) (k : A -> Prop) (x : A) (u : B -> Prop) (x' : B) : (term699 A B f k x u x') = (term699 A B f k x u x').
Proof. exact (eq_refl (term699 A B f k x u x')). Qed.
Lemma lem5053183 {A B : Type'} (u : B -> Prop) (x : B) (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x' : A) : (term705 A B u x s f k x') = (term701 A B u x s f k x').
Proof. exact (MK_COMB (@lem5053182 A B f k x' u x) (@lem5053181 A B s f k x')). Qed.
Lemma lem5053184 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5053185 {A B : Type'} (u : B -> Prop) (x : B) (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x' : A) : (term710 A B u x s f k x') = (term711 A B u x s f k x').
Proof. exact (MK_COMB (@lem5053184) (@lem5053183 A B u x s f k x')). Qed.
Lemma lem5053186 {A B : Type'} (x' : A) (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x : A) : (term707 A B s f k x x') = (term665 A B x' s f k x).
Proof. exact (eq_refl (term707 A B s f k x x')). Qed.
Lemma lem5053187 {A B : Type'} (f : A -> B) (k : A -> Prop) (x : A) (u : B -> Prop) (x' : B) : (term699 A B f k x u x') = (term699 A B f k x u x').
Proof. exact (eq_refl (term699 A B f k x u x')). Qed.
Lemma lem5053188 {A B : Type'} (u : B -> Prop) (x : B) (x' : A) (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x'' : A) : (term712 A B u x s f k x'' x') = (term713 A B u x x' s f k x'').
Proof. exact (MK_COMB (@lem5053187 A B f k x'' u x) (@lem5053186 A B x' s f k x'')). Qed.
Lemma lem5053189 {A B : Type'} (u : B -> Prop) (x : B) (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x' : A) : (term714 A B u x s f k x') = (term715 A B u x s f k x').
Proof. exact (fun_ext (fun x'' : A => @lem5053188 A B u x x'' s f k x')). Qed.
Lemma lem5053190 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5053191 {A B : Type'} (u : B -> Prop) (x : B) (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x' : A) : (term706 A B u x s f k x') = (term716 A B u x s f k x').
Proof. exact (MK_COMB (@lem5053190 A) (@lem5053189 A B u x s f k x')). Qed.
Lemma lem5053192 {A B : Type'} (u : B -> Prop) (x : B) (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x' : A) : ((term705 A B u x s f k x') = (term706 A B u x s f k x')) = ((term701 A B u x s f k x') = (term716 A B u x s f k x')).
Proof. exact (MK_COMB (@lem5053185 A B u x s f k x') (@lem5053191 A B u x s f k x')). Qed.
Lemma lem5053193 {A B : Type'} (u : B -> Prop) (x : B) (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x' : A) : (term701 A B u x s f k x') = (term716 A B u x s f k x').
Proof. exact (EQ_MP (@lem5053192 A B u x s f k x') (@lem5053177 A B u x s f k x')). Qed.
Lemma lem5053194 {A B : Type'} (u : B -> Prop) (x : B) (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term703 A B u x s f k) = (term717 A B u x s f k).
Proof. exact (fun_ext (fun x' : A => @lem5053193 A B u x s f k x')). Qed.
Lemma lem5053195 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5053196 {A B : Type'} (u : B -> Prop) (x : B) (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term704 A B u x s f k) = (term718 A B u x s f k).
Proof. exact (MK_COMB (@lem5053195 A) (@lem5053194 A B u x s f k)). Qed.
Lemma lem5053197 {A B : Type'} (u : B -> Prop) (x : B) (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term683 A B u x s f k) = (term718 A B u x s f k).
Proof. exact (TRANS (@lem5053173 A B u x s f k) (@lem5053196 A B u x s f k)). Qed.
Lemma lem5053198 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term685 A B u s f k) = (term719 A B u s f k).
Proof. exact (fun_ext (fun x : B => @lem5053197 A B u x s f k)). Qed.
Lemma lem5053199 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5053200 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term686 A B u s f k) = (term720 A B u s f k).
Proof. exact (MK_COMB (@lem5053199 B) (@lem5053198 A B u s f k)). Qed.
Lemma lem5053201 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term671 A B u s f k) = (term720 A B u s f k).
Proof. exact (TRANS (@lem5053146 A B u s f k) (@lem5053200 A B u s f k)). Qed.
Lemma lem5053202 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term586 A B u s f k) = (term720 A B u s f k).
Proof. exact (TRANS (@lem5053120 A B u s f k) (@lem5053201 A B u s f k)). Qed.
Lemma lem5053203 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term563 A B u s f k) = (term720 A B u s f k).
Proof. exact (TRANS (@lem5052978 A B u s f k) (@lem5053202 A B u s f k)). Qed.
Lemma lem5053204 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term487 A B u s f k) = (term720 A B u s f k).
Proof. exact (TRANS (@lem5052709 A B u s f k) (@lem5053203 A B u s f k)). Qed.
Lemma lem5053205 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) (h1 : term487 A B u s f k) : term720 A B u s f k.
Proof. exact (EQ_MP (@lem5053204 A B u s f k) (@lem5052386 A B u s f k h1)). Qed.
Lemma lem5053206 {A B : Type'} (u : B -> Prop) (x : B) (s : A -> Prop) (f : A -> B) (k : A -> Prop) (h1 : term718 A B u x s f k) : term718 A B u x s f k.
Proof. exact (h1). Qed.
Lemma lem5053207 {A B : Type'} (u : B -> Prop) (x : B) (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x' : A) (h1 : term716 A B u x s f k x') : term716 A B u x s f k x'.
Proof. exact (h1). Qed.
Lemma lem5053208 {A B : Type'} (u : B -> Prop) (x : B) (x'' : A) (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x' : A) (h1 : term713 A B u x x'' s f k x') : term713 A B u x x'' s f k x'.
Proof. exact (h1). Qed.
Lemma lem5053243 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term513 A B s f x y) = (term513 A B s f x y).
Proof. exact (eq_refl (term513 A B s f x y)). Qed.
Lemma lem5053244 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term514 A B s f x) = (term514 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem5053243 A B s f x y)). Qed.
Lemma lem5053245 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5053246 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term515 A B s f x) = (term515 A B s f x).
Proof. exact (MK_COMB (@lem5053245 A) (@lem5053244 A B s f x)). Qed.
Lemma lem5053247 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term516 A B s f) = (term516 A B s f).
Proof. exact (fun_ext (fun x : A => @lem5053246 A B s f x)). Qed.
Lemma lem5053248 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5053249 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term517 A B s f) = (term517 A B s f).
Proof. exact (MK_COMB (@lem5053248 A) (@lem5053247 A B s f)). Qed.
Lemma lem5053252 {B : Type'} (u : B -> Prop) (x : B) : (u x) = (u x).
Proof. exact (eq_refl (u x)). Qed.
Lemma lem5053269 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term489 A B x f s x') = (term489 A B x f s x').
Proof. exact (eq_refl (term489 A B x f s x')). Qed.
Lemma lem5053270 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term497 A B x f s) = (term497 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem5053269 A B x f s x')). Qed.
Lemma lem5053271 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5053272 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term498 A B x f s) = (term498 A B x f s).
Proof. exact (MK_COMB (@lem5053271 A) (@lem5053270 A B x f s)). Qed.
Lemma lem5053273 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5053274 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term500 A B x f s) = (term500 A B x f s).
Proof. exact (MK_COMB (@lem5053273) (@lem5053272 A B x f s)). Qed.
Lemma lem5053275 {A B : Type'} (f : A -> B) (s : A -> Prop) (u : B -> Prop) (x : B) : (term502 A B f s u x) = (term502 A B f s u x).
Proof. exact (MK_COMB (@lem5053274 A B x f s) (@lem5053252 B u x)). Qed.
Lemma lem5053276 {A B : Type'} (f : A -> B) (s : A -> Prop) (u : B -> Prop) : (term503 A B f s u) = (term503 A B f s u).
Proof. exact (fun_ext (fun x : B => @lem5053275 A B f s u x)). Qed.
Lemma lem5053277 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5053278 {A B : Type'} (f : A -> B) (s : A -> Prop) (u : B -> Prop) : (term504 A B f s u) = (term504 A B f s u).
Proof. exact (MK_COMB (@lem5053277 B) (@lem5053276 A B f s u)). Qed.
Lemma lem5053279 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5053280 {A B : Type'} (f : A -> B) (s : A -> Prop) (u : B -> Prop) : (term518 A B f s u) = (term518 A B f s u).
Proof. exact (MK_COMB (@lem5053279) (@lem5053278 A B f s u)). Qed.
Lemma lem5053281 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) : (term519 A B u s f) = (term519 A B u s f).
Proof. exact (MK_COMB (@lem5053280 A B f s u) (@lem5053249 A B s f)). Qed.
Lemma lem5053292 {A : Type'} (k : A -> Prop) (s : A -> Prop) (x : A) : (term150 A k s x) = (term150 A k s x).
Proof. exact (eq_refl (term150 A k s x)). Qed.
Lemma lem5053293 {A : Type'} (k : A -> Prop) (s : A -> Prop) : (term151 A k s) = (term151 A k s).
Proof. exact (fun_ext (fun x : A => @lem5053292 A k s x)). Qed.
Lemma lem5053294 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5053295 {A : Type'} (k : A -> Prop) (s : A -> Prop) : (term152 A k s) = (term152 A k s).
Proof. exact (MK_COMB (@lem5053294 A) (@lem5053293 A k s)). Qed.
Lemma lem5053296 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5053297 {A : Type'} (k : A -> Prop) (s : A -> Prop) : (term164 A k s) = (term164 A k s).
Proof. exact (MK_COMB (@lem5053296) (@lem5053295 A k s)). Qed.
Lemma lem5053298 {A B : Type'} (k : A -> Prop) (u : B -> Prop) (s : A -> Prop) (f : A -> B) : (term520 A B k u s f) = (term520 A B k u s f).
Proof. exact (MK_COMB (@lem5053297 A k s) (@lem5053281 A B u s f)). Qed.
Lemma lem5053299 {A B : Type'} (k : A -> Prop) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term430 A B k u s f) : term520 A B k u s f.
Proof. exact (EQ_MP (@lem5053298 A B k u s f) (@lem5052622 A B k u s f h1)). Qed.
Lemma lem5053302 {A : Type'} (k : A -> Prop) (x' : A) : (k x') = (k x').
Proof. exact (eq_refl (k x')). Qed.
Lemma lem5053321 {A B : Type'} (x' : A) (f : A -> B) (k : A -> Prop) (x'' : A) : (term532 A B x' f k x'') = (term532 A B x' f k x'').
Proof. exact (eq_refl (term532 A B x' f k x'')). Qed.
Lemma lem5053322 {A B : Type'} (x' : A) (f : A -> B) (k : A -> Prop) : (term538 A B x' f k) = (term538 A B x' f k).
Proof. exact (fun_ext (fun x'' : A => @lem5053321 A B x' f k x'')). Qed.
Lemma lem5053323 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5053324 {A B : Type'} (x' : A) (f : A -> B) (k : A -> Prop) : (term539 A B x' f k) = (term539 A B x' f k).
Proof. exact (MK_COMB (@lem5053323 A) (@lem5053322 A B x' f k)). Qed.
Lemma lem5053331 {A : Type'} (s : A -> Prop) (x' : A) : (term352 A s x') = (term352 A s x').
Proof. exact (eq_refl (term352 A s x')). Qed.
Lemma lem5053332 {A B : Type'} (s : A -> Prop) (x' : A) (f : A -> B) (k : A -> Prop) : (term541 A B s x' f k) = (term541 A B s x' f k).
Proof. exact (MK_COMB (@lem5053331 A s x') (@lem5053324 A B x' f k)). Qed.
Lemma lem5053333 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5053334 {A B : Type'} (s : A -> Prop) (x' : A) (f : A -> B) (k : A -> Prop) : (term544 A B s x' f k) = (term544 A B s x' f k).
Proof. exact (MK_COMB (@lem5053333) (@lem5053332 A B s x' f k)). Qed.
Lemma lem5053335 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x' : A) : (term546 A B s f k x') = (term546 A B s f k x').
Proof. exact (MK_COMB (@lem5053334 A B s x' f k) (@lem5053302 A k x')). Qed.
Lemma lem5053366 {A B : Type'} (s : A -> Prop) (f : A -> B) (x'' : A) (k : A -> Prop) (x' : A) : (term663 A B s f x'' k x') = (term663 A B s f x'' k x').
Proof. exact (eq_refl (term663 A B s f x'' k x')). Qed.
Lemma lem5053367 {A B : Type'} (x'' : A) (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x' : A) : (term665 A B x'' s f k x') = (term665 A B x'' s f k x').
Proof. exact (MK_COMB (@lem5053366 A B s f x'' k x') (@lem5053335 A B s f k x')). Qed.
Lemma lem5053390 {A B : Type'} (f : A -> B) (k : A -> Prop) (x' : A) (u : B -> Prop) (x : B) : (term699 A B f k x' u x) = (term699 A B f k x' u x).
Proof. exact (eq_refl (term699 A B f k x' u x)). Qed.
Lemma lem5053391 {A B : Type'} (u : B -> Prop) (x : B) (x'' : A) (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x' : A) : (term713 A B u x x'' s f k x') = (term713 A B u x x'' s f k x').
Proof. exact (MK_COMB (@lem5053390 A B f k x' u x) (@lem5053367 A B x'' s f k x')). Qed.
Lemma lem5053392 {A B : Type'} (u : B -> Prop) (x : B) (x'' : A) (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x' : A) (h1 : term713 A B u x x'' s f k x') : term713 A B u x x'' s f k x'.
Proof. exact (EQ_MP (@lem5053391 A B u x x'' s f k x') (@lem5053208 A B u x x'' s f k x' h1)). Qed.
Lemma lem5053393 {A B : Type'} (k : A -> Prop) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term430 A B k u s f) : term519 A B u s f.
Proof. exact (proj2 (@lem5053299 A B k u s f h1)). Qed.
Lemma lem5053394 {A B : Type'} (k : A -> Prop) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term430 A B k u s f) : term152 A k s.
Proof. exact (proj1 (@lem5053299 A B k u s f h1)). Qed.
Lemma lem5053395 {A B : Type'} (k : A -> Prop) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term430 A B k u s f) : term517 A B s f.
Proof. exact (proj2 (@lem5053393 A B k u s f h1)). Qed.
Lemma lem5053396 {A B : Type'} (k : A -> Prop) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term430 A B k u s f) : term504 A B f s u.
Proof. exact (proj1 (@lem5053393 A B k u s f h1)). Qed.
Lemma lem5053397 {A B : Type'} (f : A -> B) (k : A -> Prop) (x' : A) (u : B -> Prop) (x : B) (h1 : term599 A B f k x' u x) : term599 A B f k x' u x.
Proof. exact (h1). Qed.
Lemma lem5053398 {A B : Type'} (x'' : A) (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x' : A) (h1 : term665 A B x'' s f k x') : term665 A B x'' s f k x'.
Proof. exact (h1). Qed.
Lemma lem5053400 {A B : Type'} (f : A -> B) (k : A -> Prop) (x' : A) (u : B -> Prop) (x : B) (h1 : term599 A B f k x' u x) : term409 A B x f k x'.
Proof. exact (proj1 (@lem5053397 A B f k x' u x h1)). Qed.
Lemma lem5053403 {A B : Type'} (s : A -> Prop) (f : A -> B) (x'' : A) (k : A -> Prop) (x' : A) (h1 : term631 A B s f x'' k x') : term631 A B s f x'' k x'.
Proof. exact (h1). Qed.
Lemma lem5053404 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x' : A) (h1 : term546 A B s f k x') : term546 A B s f k x'.
Proof. exact (h1). Qed.
Lemma lem5053406 {A B : Type'} (s : A -> Prop) (f : A -> B) (x'' : A) (k : A -> Prop) (x' : A) (h1 : term631 A B s f x'' k x') : term614 A B s x' f k x''.
Proof. exact (proj1 (@lem5053403 A B s f x'' k x' h1)). Qed.
Lemma lem5053407 {A B : Type'} (s : A -> Prop) (f : A -> B) (x'' : A) (k : A -> Prop) (x' : A) (h1 : term631 A B s f x'' k x') : term453 A B x' f k x''.
Proof. exact (proj2 (@lem5053406 A B s f x'' k x' h1)). Qed.
Lemma lem5053412 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x' : A) (h1 : term546 A B s f k x') : term541 A B s x' f k.
Proof. exact (proj1 (@lem5053404 A B s f k x' h1)). Qed.
Lemma lem5053414 {A B : Type'} (x' : A) (f : A -> B) (k : A -> Prop) (h1 : term539 A B x' f k) : term539 A B x' f k.
Proof. exact (h1). Qed.
Lemma lem5053422 {A : Type'} (k : A -> Prop) (s : A -> Prop) (x : A) : (term150 A k s x) = (term150 A k s x).
Proof. exact (eq_refl (term150 A k s x)). Qed.
Lemma lem5053423 {A : Type'} (k : A -> Prop) (s : A -> Prop) : (term151 A k s) = (term151 A k s).
Proof. exact (fun_ext (fun x : A => @lem5053422 A k s x)). Qed.
Lemma lem5053424 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5053426 {A : Type'} (k : A -> Prop) (s : A -> Prop) : (term152 A k s) = (term152 A k s).
Proof. exact (MK_COMB (@lem5053424 A) (@lem5053423 A k s)). Qed.
Lemma lem5053427 {A B : Type'} (k : A -> Prop) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term430 A B k u s f) : term152 A k s.
Proof. exact (EQ_MP (@lem5053426 A k s) (@lem5053394 A B k u s f h1)). Qed.
Lemma lem5053429 {A : Type'} (P : A -> Prop) (Q : Prop) : (term721 A P Q) = (term722 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem5053430 {A : Type'} (P : A -> Prop) (Q : Prop) : (term721 A P Q) = (term722 A P Q).
Proof. exact (@lem5053429 A P Q). Qed.
Lemma lem5053431 {A B : Type'} (f : A -> B) (s : A -> Prop) (u : B -> Prop) (x : B) : (term723 A B f s u x) = (term724 A B f s u x).
Proof. exact (@lem5053430 A (term497 A B x f s) (u x)). Qed.
Lemma lem5053432 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term725 A B x f s x') = (term489 A B x f s x').
Proof. exact (eq_refl (term725 A B x f s x')). Qed.
Lemma lem5053433 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term726 A B x f s) = (term497 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem5053432 A B x f s x')). Qed.
Lemma lem5053434 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5053435 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term727 A B x f s) = (term498 A B x f s).
Proof. exact (MK_COMB (@lem5053434 A) (@lem5053433 A B x f s)). Qed.
Lemma lem5053436 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5053437 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term728 A B x f s) = (term500 A B x f s).
Proof. exact (MK_COMB (@lem5053436) (@lem5053435 A B x f s)). Qed.
Lemma lem5053438 {B : Type'} (u : B -> Prop) (x : B) : (u x) = (u x).
Proof. exact (eq_refl (u x)). Qed.
Lemma lem5053439 {A B : Type'} (f : A -> B) (s : A -> Prop) (u : B -> Prop) (x : B) : (term723 A B f s u x) = (term502 A B f s u x).
Proof. exact (MK_COMB (@lem5053437 A B x f s) (@lem5053438 B u x)). Qed.
Lemma lem5053440 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5053441 {A B : Type'} (f : A -> B) (s : A -> Prop) (u : B -> Prop) (x : B) : (term729 A B f s u x) = (term730 A B f s u x).
Proof. exact (MK_COMB (@lem5053440) (@lem5053439 A B f s u x)). Qed.
Lemma lem5053442 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term725 A B x f s x') = (term489 A B x f s x').
Proof. exact (eq_refl (term725 A B x f s x')). Qed.
Lemma lem5053443 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5053444 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term731 A B x f s x') = (term732 A B x f s x').
Proof. exact (MK_COMB (@lem5053443) (@lem5053442 A B x f s x')). Qed.
Lemma lem5053445 {B : Type'} (u : B -> Prop) (x : B) : (u x) = (u x).
Proof. exact (eq_refl (u x)). Qed.
Lemma lem5053446 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (u : B -> Prop) (x' : B) : (term733 A B f s x u x') = (term734 A B f s x u x').
Proof. exact (MK_COMB (@lem5053444 A B x' f s x) (@lem5053445 B u x')). Qed.
Lemma lem5053447 {A B : Type'} (f : A -> B) (s : A -> Prop) (u : B -> Prop) (x : B) : (term735 A B f s u x) = (term736 A B f s u x).
Proof. exact (fun_ext (fun x' : A => @lem5053446 A B f s x' u x)). Qed.
Lemma lem5053448 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5053449 {A B : Type'} (f : A -> B) (s : A -> Prop) (u : B -> Prop) (x : B) : (term724 A B f s u x) = (term737 A B f s u x).
Proof. exact (MK_COMB (@lem5053448 A) (@lem5053447 A B f s u x)). Qed.
Lemma lem5053450 {A B : Type'} (f : A -> B) (s : A -> Prop) (u : B -> Prop) (x : B) : ((term723 A B f s u x) = (term724 A B f s u x)) = ((term502 A B f s u x) = (term737 A B f s u x)).
Proof. exact (MK_COMB (@lem5053441 A B f s u x) (@lem5053449 A B f s u x)). Qed.
Lemma lem5053451 {A B : Type'} (f : A -> B) (s : A -> Prop) (u : B -> Prop) (x : B) : (term502 A B f s u x) = (term737 A B f s u x).
Proof. exact (EQ_MP (@lem5053450 A B f s u x) (@lem5053431 A B f s u x)). Qed.
Lemma lem5053452 {A B : Type'} (f : A -> B) (s : A -> Prop) (u : B -> Prop) : (term503 A B f s u) = (term738 A B f s u).
Proof. exact (fun_ext (fun x : B => @lem5053451 A B f s u x)). Qed.
Lemma lem5053453 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5053454 {A B : Type'} (f : A -> B) (s : A -> Prop) (u : B -> Prop) : (term504 A B f s u) = (term739 A B f s u).
Proof. exact (MK_COMB (@lem5053453 B) (@lem5053452 A B f s u)). Qed.
Lemma lem5053467 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (u : B -> Prop) (x' : B) : (term734 A B f s x u x') = (term734 A B f s x u x').
Proof. exact (eq_refl (term734 A B f s x u x')). Qed.
Lemma lem5053468 {A B : Type'} (f : A -> B) (s : A -> Prop) (u : B -> Prop) (x : B) : (term736 A B f s u x) = (term736 A B f s u x).
Proof. exact (fun_ext (fun x' : A => @lem5053467 A B f s x' u x)). Qed.
Lemma lem5053469 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5053470 {A B : Type'} (f : A -> B) (s : A -> Prop) (u : B -> Prop) (x : B) : (term737 A B f s u x) = (term737 A B f s u x).
Proof. exact (MK_COMB (@lem5053469 A) (@lem5053468 A B f s u x)). Qed.
Lemma lem5053471 {A B : Type'} (f : A -> B) (s : A -> Prop) (u : B -> Prop) : (term738 A B f s u) = (term738 A B f s u).
Proof. exact (fun_ext (fun x : B => @lem5053470 A B f s u x)). Qed.
Lemma lem5053472 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5053473 {A B : Type'} (f : A -> B) (s : A -> Prop) (u : B -> Prop) : (term739 A B f s u) = (term739 A B f s u).
Proof. exact (MK_COMB (@lem5053472 B) (@lem5053471 A B f s u)). Qed.
Lemma lem5053474 {A B : Type'} (f : A -> B) (s : A -> Prop) (u : B -> Prop) : (term504 A B f s u) = (term739 A B f s u).
Proof. exact (TRANS (@lem5053454 A B f s u) (@lem5053473 A B f s u)). Qed.
Lemma lem5053475 {A B : Type'} (k : A -> Prop) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term430 A B k u s f) : term739 A B f s u.
Proof. exact (EQ_MP (@lem5053474 A B f s u) (@lem5053396 A B k u s f h1)). Qed.
Lemma lem5053523 {A : Type'} (k : A -> Prop) (s : A -> Prop) (x : A) : (term150 A k s x) = (term150 A k s x).
Proof. exact (eq_refl (term150 A k s x)). Qed.
Lemma lem5053524 {A : Type'} (k : A -> Prop) (s : A -> Prop) : (term151 A k s) = (term151 A k s).
Proof. exact (fun_ext (fun x : A => @lem5053523 A k s x)). Qed.
Lemma lem5053525 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5053527 {A : Type'} (k : A -> Prop) (s : A -> Prop) : (term152 A k s) = (term152 A k s).
Proof. exact (MK_COMB (@lem5053525 A) (@lem5053524 A k s)). Qed.
Lemma lem5053528 {A B : Type'} (k : A -> Prop) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term430 A B k u s f) : term152 A k s.
Proof. exact (EQ_MP (@lem5053527 A k s) (@lem5053394 A B k u s f h1)). Qed.
Lemma lem5053596 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term513 A B s f x y) = (term513 A B s f x y).
Proof. exact (eq_refl (term513 A B s f x y)). Qed.
Lemma lem5053597 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term514 A B s f x) = (term514 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem5053596 A B s f x y)). Qed.
Lemma lem5053598 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5053599 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term515 A B s f x) = (term515 A B s f x).
Proof. exact (MK_COMB (@lem5053598 A) (@lem5053597 A B s f x)). Qed.
Lemma lem5053600 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term516 A B s f) = (term516 A B s f).
Proof. exact (fun_ext (fun x : A => @lem5053599 A B s f x)). Qed.
Lemma lem5053601 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5053603 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term517 A B s f) = (term517 A B s f).
Proof. exact (MK_COMB (@lem5053601 A) (@lem5053600 A B s f)). Qed.
Lemma lem5053604 {A B : Type'} (k : A -> Prop) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term430 A B k u s f) : term517 A B s f.
Proof. exact (EQ_MP (@lem5053603 A B s f) (@lem5053395 A B k u s f h1)). Qed.
Lemma lem5053628 {A : Type'} (k : A -> Prop) (s : A -> Prop) (x : A) : (term150 A k s x) = (term150 A k s x).
Proof. exact (eq_refl (term150 A k s x)). Qed.
Lemma lem5053629 {A : Type'} (k : A -> Prop) (s : A -> Prop) : (term151 A k s) = (term151 A k s).
Proof. exact (fun_ext (fun x : A => @lem5053628 A k s x)). Qed.
Lemma lem5053630 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5053632 {A : Type'} (k : A -> Prop) (s : A -> Prop) : (term152 A k s) = (term152 A k s).
Proof. exact (MK_COMB (@lem5053630 A) (@lem5053629 A k s)). Qed.
Lemma lem5053633 {A B : Type'} (k : A -> Prop) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term430 A B k u s f) : term152 A k s.
Proof. exact (EQ_MP (@lem5053632 A k s) (@lem5053394 A B k u s f h1)). Qed.
Lemma lem5053717 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term240 A s x') : term240 A s x'.
Proof. exact (h1). Qed.
Lemma lem5053818 {A B : Type'} (x' : A) (f : A -> B) (k : A -> Prop) (x'' : A) : (term532 A B x' f k x'') = (term532 A B x' f k x'').
Proof. exact (eq_refl (term532 A B x' f k x'')). Qed.
Lemma lem5053819 {A B : Type'} (x' : A) (f : A -> B) (k : A -> Prop) : (term538 A B x' f k) = (term538 A B x' f k).
Proof. exact (fun_ext (fun x'' : A => @lem5053818 A B x' f k x'')). Qed.
Lemma lem5053820 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5053822 {A B : Type'} (x' : A) (f : A -> B) (k : A -> Prop) : (term539 A B x' f k) = (term539 A B x' f k).
Proof. exact (MK_COMB (@lem5053820 A) (@lem5053819 A B x' f k)). Qed.
Lemma lem5053823 {A B : Type'} (x' : A) (f : A -> B) (k : A -> Prop) (h1 : term539 A B x' f k) : term539 A B x' f k.
Proof. exact (EQ_MP (@lem5053822 A B x' f k) (@lem5053414 A B x' f k h1)). Qed.
Lemma lem5053824 {A B : Type'} (_64933 : A) (k : A -> Prop) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term430 A B k u s f) : term238 A k s _64933.
Proof. exact (@lem5053427 A B k u s f h1 _64933). Qed.
Lemma lem5053825 {A : Type'} (k : A -> Prop) (s : A -> Prop) (_64933 : A) : (term238 A k s _64933) = (term150 A k s _64933).
Proof. exact (eq_refl (term238 A k s _64933)). Qed.
Lemma lem5053827 {A B : Type'} (_64934 : B) (k : A -> Prop) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term430 A B k u s f) : term740 A B f s u _64934.
Proof. exact (@lem5053475 A B k u s f h1 _64934). Qed.
Lemma lem5053828 {A B : Type'} (f : A -> B) (s : A -> Prop) (u : B -> Prop) (_64934 : B) : (term740 A B f s u _64934) = (term737 A B f s u _64934).
Proof. exact (eq_refl (term740 A B f s u _64934)). Qed.
Lemma lem5053829 {A B : Type'} (_64934 : B) (k : A -> Prop) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term430 A B k u s f) : term737 A B f s u _64934.
Proof. exact (EQ_MP (@lem5053828 A B f s u _64934) (@lem5053827 A B _64934 k u s f h1)). Qed.
Lemma lem5053830 {A B : Type'} (_64934 : B) (_64935 : A) (k : A -> Prop) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term430 A B k u s f) : term741 A B f s u _64934 _64935.
Proof. exact (@lem5053829 A B _64934 k u s f h1 _64935). Qed.
Lemma lem5053831 {A B : Type'} (f : A -> B) (s : A -> Prop) (_64935 : A) (u : B -> Prop) (_64934 : B) : (term741 A B f s u _64934 _64935) = (term734 A B f s _64935 u _64934).
Proof. exact (eq_refl (term741 A B f s u _64934 _64935)). Qed.
Lemma lem5053832 {A B : Type'} (_64935 : A) (_64934 : B) (k : A -> Prop) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term430 A B k u s f) : term734 A B f s _64935 u _64934.
Proof. exact (EQ_MP (@lem5053831 A B f s _64935 u _64934) (@lem5053830 A B _64934 _64935 k u s f h1)). Qed.
Lemma lem5053839 {A B : Type'} (_64938 : A) (k : A -> Prop) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term430 A B k u s f) : term238 A k s _64938.
Proof. exact (@lem5053528 A B k u s f h1 _64938). Qed.
Lemma lem5053840 {A : Type'} (k : A -> Prop) (s : A -> Prop) (_64938 : A) : (term238 A k s _64938) = (term150 A k s _64938).
Proof. exact (eq_refl (term238 A k s _64938)). Qed.
Lemma lem5053848 {A B : Type'} (_64941 : A) (k : A -> Prop) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term430 A B k u s f) : term742 A B s f _64941.
Proof. exact (@lem5053604 A B k u s f h1 _64941). Qed.
Lemma lem5053849 {A B : Type'} (s : A -> Prop) (f : A -> B) (_64941 : A) : (term742 A B s f _64941) = (term515 A B s f _64941).
Proof. exact (eq_refl (term742 A B s f _64941)). Qed.
Lemma lem5053850 {A B : Type'} (_64941 : A) (k : A -> Prop) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term430 A B k u s f) : term515 A B s f _64941.
Proof. exact (EQ_MP (@lem5053849 A B s f _64941) (@lem5053848 A B _64941 k u s f h1)). Qed.
Lemma lem5053851 {A B : Type'} (_64941 : A) (_64942 : A) (k : A -> Prop) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term430 A B k u s f) : term743 A B s f _64941 _64942.
Proof. exact (@lem5053850 A B _64941 k u s f h1 _64942). Qed.
Lemma lem5053852 {A B : Type'} (s : A -> Prop) (f : A -> B) (_64941 : A) (_64942 : A) : (term743 A B s f _64941 _64942) = (term513 A B s f _64941 _64942).
Proof. exact (eq_refl (term743 A B s f _64941 _64942)). Qed.
Lemma lem5053853 {A B : Type'} (_64941 : A) (_64942 : A) (k : A -> Prop) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term430 A B k u s f) : term513 A B s f _64941 _64942.
Proof. exact (EQ_MP (@lem5053852 A B s f _64941 _64942) (@lem5053851 A B _64941 _64942 k u s f h1)). Qed.
Lemma lem5053854 {A B : Type'} (_64943 : A) (k : A -> Prop) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term430 A B k u s f) : term238 A k s _64943.
Proof. exact (@lem5053633 A B k u s f h1 _64943). Qed.
Lemma lem5053855 {A : Type'} (k : A -> Prop) (s : A -> Prop) (_64943 : A) : (term238 A k s _64943) = (term150 A k s _64943).
Proof. exact (eq_refl (term238 A k s _64943)). Qed.
Lemma lem5053884 {A B : Type'} (_64953 : A) (x' : A) (f : A -> B) (k : A -> Prop) (h1 : term539 A B x' f k) : term744 A B x' f k _64953.
Proof. exact (@lem5053823 A B x' f k h1 _64953). Qed.
Lemma lem5053885 {A B : Type'} (x' : A) (f : A -> B) (k : A -> Prop) (_64953 : A) : (term744 A B x' f k _64953) = (term532 A B x' f k _64953).
Proof. exact (eq_refl (term744 A B x' f k _64953)). Qed.
Lemma lem5053903 {A B : Type'} (f : A -> B) (s : A -> Prop) (_64935 : A) (u : B -> Prop) (_64934 : B) : (term734 A B f s _64935 u _64934) = (term745 A B f s _64935 u _64934).
Proof. exact (@lem5051547 (term746 A B _64934 f _64935) (term240 A s _64935) (u _64934)). Qed.
Lemma lem5053924 {A B : Type'} (f : A -> B) (k : A -> Prop) (x' : A) (u : B -> Prop) (x : B) (h1 : term599 A B f k x' u x) : term240 B u x.
Proof. exact (proj2 (@lem5053397 A B f k x' u x h1)). Qed.
Lemma lem5053926 {A B : Type'} (f : A -> B) (k : A -> Prop) (x' : A) (u : B -> Prop) (x : B) (h1 : term599 A B f k x' u x) : x = (f x').
Proof. exact (proj1 (@lem5053400 A B f k x' u x h1)). Qed.
Lemma lem5053934 {A B : Type'} (_64938 : A) (k : A -> Prop) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term430 A B k u s f) : term150 A k s _64938.
Proof. exact (EQ_MP (@lem5053840 A k s _64938) (@lem5053839 A B _64938 k u s f h1)). Qed.
Lemma lem5053950 {A B : Type'} (s : A -> Prop) (f : A -> B) (_64941 : A) (_64942 : A) : (term513 A B s f _64941 _64942) = (term747 A B s f _64941 _64942).
Proof. exact (@lem5051547 (term240 A s _64941) (term506 A B s _64941 f _64942) (_64941 = _64942)). Qed.
Lemma lem5053957 {A B : Type'} (s : A -> Prop) (f : A -> B) (_64941 : A) (_64942 : A) : (term748 A B s f _64941 _64942) = (term749 A B s f _64941 _64942).
Proof. exact (@lem5051547 (term240 A s _64942) (term329 A B _64941 f _64942) (_64941 = _64942)). Qed.
Lemma lem5053958 {A : Type'} (s : A -> Prop) (_64941 : A) : (term352 A s _64941) = (term352 A s _64941).
Proof. exact (eq_refl (term352 A s _64941)). Qed.
Lemma lem5053961 {A B : Type'} (s : A -> Prop) (f : A -> B) (_64941 : A) (_64942 : A) : (term747 A B s f _64941 _64942) = (term750 A B s f _64941 _64942).
Proof. exact (MK_COMB (@lem5053958 A s _64941) (@lem5053957 A B s f _64941 _64942)). Qed.
Lemma lem5053963 {A B : Type'} (s : A -> Prop) (f : A -> B) (_64941 : A) (_64942 : A) : (term513 A B s f _64941 _64942) = (term750 A B s f _64941 _64942).
Proof. exact (TRANS (@lem5053950 A B s f _64941 _64942) (@lem5053961 A B s f _64941 _64942)). Qed.
Lemma lem5053964 {A B : Type'} (_64941 : A) (_64942 : A) (k : A -> Prop) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term430 A B k u s f) : term750 A B s f _64941 _64942.
Proof. exact (EQ_MP (@lem5053963 A B s f _64941 _64942) (@lem5053853 A B _64941 _64942 k u s f h1)). Qed.
Lemma lem5053966 {A B : Type'} (s : A -> Prop) (f : A -> B) (x'' : A) (k : A -> Prop) (x' : A) (h1 : term631 A B s f x'' k x') : term240 A k x'.
Proof. exact (proj2 (@lem5053403 A B s f x'' k x' h1)). Qed.
Lemma lem5053978 {A B : Type'} (_64943 : A) (k : A -> Prop) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term430 A B k u s f) : term150 A k s _64943.
Proof. exact (EQ_MP (@lem5053855 A k s _64943) (@lem5053854 A B _64943 k u s f h1)). Qed.
Lemma lem5054012 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term240 A s x') : term240 A s x'.
Proof. exact (h1). Qed.
Lemma lem5054056 {A B : Type'} (_64953 : A) (x' : A) (f : A -> B) (k : A -> Prop) (h1 : term539 A B x' f k) : term532 A B x' f k _64953.
Proof. exact (EQ_MP (@lem5053885 A B x' f k _64953) (@lem5053884 A B _64953 x' f k h1)). Qed.
Lemma lem5054084 {A B : Type'} (_64933 : A) (k : A -> Prop) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term430 A B k u s f) : term150 A k s _64933.
Proof. exact (EQ_MP (@lem5053825 A k s _64933) (@lem5053824 A B _64933 k u s f h1)). Qed.
Lemma lem5054098 {A B : Type'} (_64935 : A) (_64934 : B) (k : A -> Prop) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term430 A B k u s f) : term745 A B f s _64935 u _64934.
Proof. exact (EQ_MP (@lem5053903 A B f s _64935 u _64934) (@lem5053832 A B _64935 _64934 k u s f h1)). Qed.
Lemma lem5054113 {B : Type'} (u : B -> Prop) : (term242 B u) = (term242 B u).
Proof. exact (eq_refl (term242 B u)). Qed.
Lemma lem5054114 {A B : Type'} (f : A -> B) (k : A -> Prop) (x' : A) (u : B -> Prop) (x : B) (h1 : term599 A B f k x' u x) : (term243 B u x) = (term751 A B u f x').
Proof. exact (MK_COMB (@lem5054113 B u) (@lem5053926 A B f k x' u x h1)). Qed.
Lemma lem5054115 {A B : Type'} (u : B -> Prop) (f : A -> B) (x' : A) : (term751 A B u f x') = (term138 A B u f x').
Proof. exact (eq_refl (term751 A B u f x')). Qed.
Lemma lem5054116 {B : Type'} (u : B -> Prop) (x : B) : (term244 B u x) = (term244 B u x).
Proof. exact (eq_refl (term244 B u x)). Qed.
Lemma lem5054117 {A B : Type'} (x : B) (u : B -> Prop) (f : A -> B) (x' : A) : ((term243 B u x) = (term751 A B u f x')) = ((term243 B u x) = (term138 A B u f x')).
Proof. exact (MK_COMB (@lem5054116 B u x) (@lem5054115 A B u f x')). Qed.
Lemma lem5054118 {B : Type'} (u : B -> Prop) (x : B) : (term243 B u x) = (term240 B u x).
Proof. exact (eq_refl (term243 B u x)). Qed.
Lemma lem5054119 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5054120 {B : Type'} (u : B -> Prop) (x : B) : (term244 B u x) = (term245 B u x).
Proof. exact (MK_COMB (@lem5054119) (@lem5054118 B u x)). Qed.
Lemma lem5054121 {A B : Type'} (u : B -> Prop) (f : A -> B) (x' : A) : (term138 A B u f x') = (term138 A B u f x').
Proof. exact (eq_refl (term138 A B u f x')). Qed.
Lemma lem5054122 {A B : Type'} (x : B) (u : B -> Prop) (f : A -> B) (x' : A) : ((term243 B u x) = (term138 A B u f x')) = ((term240 B u x) = (term138 A B u f x')).
Proof. exact (MK_COMB (@lem5054120 B u x) (@lem5054121 A B u f x')). Qed.
Lemma lem5054123 {A B : Type'} (x : B) (u : B -> Prop) (f : A -> B) (x' : A) : ((term243 B u x) = (term751 A B u f x')) = ((term240 B u x) = (term138 A B u f x')).
Proof. exact (TRANS (@lem5054117 A B x u f x') (@lem5054122 A B x u f x')). Qed.
Lemma lem5054124 {A B : Type'} (f : A -> B) (k : A -> Prop) (x' : A) (u : B -> Prop) (x : B) (h1 : term599 A B f k x' u x) : (term240 B u x) = (term138 A B u f x').
Proof. exact (EQ_MP (@lem5054123 A B x u f x') (@lem5054114 A B f k x' u x h1)). Qed.
Lemma lem5054125 {A B : Type'} (f : A -> B) (k : A -> Prop) (x' : A) (u : B -> Prop) (x : B) (h1 : term599 A B f k x' u x) : term138 A B u f x'.
Proof. exact (EQ_MP (@lem5054124 A B f k x' u x h1) (@lem5053924 A B f k x' u x h1)). Qed.
Lemma lem5054189 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem5054190 {B : Type'} (x : B) : x = x.
Proof. exact (@lem5054189 B x). Qed.
Lemma lem5054191 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (f x').
Proof. exact (@lem5054190 B (f x')). Qed.
Lemma lem5054192 {A B : Type'} (f : A -> B) (x' : A) : term752 A B f x'.
Proof. exact (fun h0 : term753 A B f x' => @lem5054191 A B f x'). Qed.
Lemma lem5054194 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5054195 {A B : Type'} (f : A -> B) (x' : A) : (term752 A B f x') = ((f x') = (f x')).
Proof. exact (@lem5054194 ((f x') = (f x'))). Qed.
Lemma lem5054196 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (f x').
Proof. exact (EQ_MP (@lem5054195 A B f x') (@lem5054192 A B f x')). Qed.
Lemma lem5054198 {A B : Type'} (f : A -> B) (k : A -> Prop) (x' : A) (u : B -> Prop) (x : B) (h1 : term599 A B f k x' u x) : k x'.
Proof. exact (proj2 (@lem5053400 A B f k x' u x h1)). Qed.
Lemma lem5054199 {A B : Type'} (f : A -> B) (k : A -> Prop) (x' : A) (u : B -> Prop) (x : B) (h1 : term599 A B f k x' u x) : term246 A k x'.
Proof. exact (fun h0 : term240 A k x' => @lem5054198 A B f k x' u x h1). Qed.
Lemma lem5054201 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5054202 {A : Type'} (k : A -> Prop) (x' : A) : (term246 A k x') = (k x').
Proof. exact (@lem5054201 (k x')). Qed.
Lemma lem5054203 {A B : Type'} (f : A -> B) (k : A -> Prop) (x' : A) (u : B -> Prop) (x : B) (h1 : term599 A B f k x' u x) : k x'.
Proof. exact (EQ_MP (@lem5054202 A k x') (@lem5054199 A B f k x' u x h1)). Qed.
Lemma lem5054209 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5054210 {A : Type'} (s : A -> Prop) (k : A -> Prop) (_64933 : A) : (term150 A k s _64933) = (term259 A s k _64933).
Proof. exact (@lem5054209 (s _64933) (term240 A k _64933)). Qed.
Lemma lem5054216 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5054217 {A : Type'} (s : A -> Prop) (k : A -> Prop) (_64933 : A) : (term260 A k s _64933) = (term261 A s k _64933).
Proof. exact (MK_COMB (@lem5054216) (@lem5054210 A s k _64933)). Qed.
Lemma lem5054223 {A : Type'} (s : A -> Prop) (k : A -> Prop) (_64933 : A) : (term259 A s k _64933) = (term259 A s k _64933).
Proof. exact (eq_refl (term259 A s k _64933)). Qed.
Lemma lem5054224 {A : Type'} (s : A -> Prop) (k : A -> Prop) (_64933 : A) : ((term150 A k s _64933) = (term259 A s k _64933)) = ((term259 A s k _64933) = (term259 A s k _64933)).
Proof. exact (MK_COMB (@lem5054217 A s k _64933) (@lem5054223 A s k _64933)). Qed.
Lemma lem5054226 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5054227 (x : Prop) : (x = x) = True.
Proof. exact (@lem5054226 Prop x). Qed.
Lemma lem5054228 {A : Type'} (s : A -> Prop) (k : A -> Prop) (_64933 : A) : ((term259 A s k _64933) = (term259 A s k _64933)) = True.
Proof. exact (@lem5054227 (term259 A s k _64933)). Qed.
Lemma lem5054229 {A : Type'} (s : A -> Prop) (k : A -> Prop) (_64933 : A) : ((term150 A k s _64933) = (term259 A s k _64933)) = True.
Proof. exact (TRANS (@lem5054224 A s k _64933) (@lem5054228 A s k _64933)). Qed.
Lemma lem5054230 {A : Type'} (s : A -> Prop) (k : A -> Prop) (_64933 : A) : True = ((term150 A k s _64933) = (term259 A s k _64933)).
Proof. exact (SYM (@lem5054229 A s k _64933)). Qed.
Lemma lem5054231 {A : Type'} (s : A -> Prop) (k : A -> Prop) (_64933 : A) : (term150 A k s _64933) = (term259 A s k _64933).
Proof. exact (EQ_MP (@lem5054230 A s k _64933) (@lem0)). Qed.
Lemma lem5054232 {A B : Type'} (_64933 : A) (k : A -> Prop) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term430 A B k u s f) : term259 A s k _64933.
Proof. exact (EQ_MP (@lem5054231 A s k _64933) (@lem5054084 A B _64933 k u s f h1)). Qed.
Lemma lem5054234 (b : Prop) (a : Prop) : (a \/ b) = (term252 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5054235 {A : Type'} (k : A -> Prop) (s : A -> Prop) (_64933 : A) : (term259 A s k _64933) = (term262 A k s _64933).
Proof. exact (@lem5054234 (term240 A k _64933) (s _64933)). Qed.
Lemma lem5054237 (a : Prop) : (term120 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5054238 {A : Type'} (k : A -> Prop) (_64933 : A) : (term263 A k _64933) = (k _64933).
Proof. exact (@lem5054237 (k _64933)). Qed.
Lemma lem5054239 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5054240 {A : Type'} (k : A -> Prop) (_64933 : A) : (term264 A k _64933) = (term58 A k _64933).
Proof. exact (MK_COMB (@lem5054239) (@lem5054238 A k _64933)). Qed.
Lemma lem5054241 {A : Type'} (s : A -> Prop) (_64933 : A) : (s _64933) = (s _64933).
Proof. exact (eq_refl (s _64933)). Qed.
Lemma lem5054242 {A : Type'} (k : A -> Prop) (s : A -> Prop) (_64933 : A) : (term262 A k s _64933) = (term74 A k s _64933).
Proof. exact (MK_COMB (@lem5054240 A k _64933) (@lem5054241 A s _64933)). Qed.
Lemma lem5054243 {A : Type'} (k : A -> Prop) (s : A -> Prop) (_64933 : A) : (term259 A s k _64933) = (term74 A k s _64933).
Proof. exact (TRANS (@lem5054235 A k s _64933) (@lem5054242 A k s _64933)). Qed.
Lemma lem5054246 {A B : Type'} (_64933 : A) (k : A -> Prop) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term430 A B k u s f) : term74 A k s _64933.
Proof. exact (EQ_MP (@lem5054243 A k s _64933) (@lem5054232 A B _64933 k u s f h1)). Qed.
Lemma lem5054247 {A B : Type'} (_64933 : A) (k : A -> Prop) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term430 A B k u s f) : term74 A k s _64933.
Proof. exact (@lem5054246 A B _64933 k u s f h1). Qed.
Lemma lem5054248 {A B : Type'} (x' : A) (k : A -> Prop) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term430 A B k u s f) : term74 A k s x'.
Proof. exact (@lem5054247 A B x' k u s f h1). Qed.
Lemma lem5054251 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x' : A) (u : B -> Prop) (x : B) (h1 : term430 A B k u s f) (h2 : term599 A B f k x' u x) : s x'.
Proof. exact (@lem5054248 A B x' k u s f h1 (@lem5054203 A B f k x' u x h2)). Qed.
Lemma lem5054252 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x' : A) (u : B -> Prop) (x : B) (h1 : term430 A B k u s f) (h2 : term599 A B f k x' u x) : term246 A s x'.
Proof. exact (fun h0 : term240 A s x' => @lem5054251 A B s f k x' u x h1 h2). Qed.
Lemma lem5054254 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5054255 {A : Type'} (s : A -> Prop) (x' : A) : (term246 A s x') = (s x').
Proof. exact (@lem5054254 (s x')). Qed.
Lemma lem5054256 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x' : A) (u : B -> Prop) (x : B) (h1 : term430 A B k u s f) (h2 : term599 A B f k x' u x) : s x'.
Proof. exact (EQ_MP (@lem5054255 A s x') (@lem5054252 A B s f k x' u x h1 h2)). Qed.
Lemma lem5054262 (q : Prop) (p : Prop) (r : Prop) : (term278 p q r) = (term278 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5054263 {A B : Type'} (s : A -> Prop) (f : A -> B) (_64935 : A) (u : B -> Prop) (_64934 : B) : (term745 A B f s _64935 u _64934) = (term754 A B s f _64935 u _64934).
Proof. exact (@lem5054262 (term240 A s _64935) (term746 A B _64934 f _64935) (u _64934)). Qed.
Lemma lem5054277 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5054278 {A B : Type'} (u : B -> Prop) (_64934 : B) (f : A -> B) (_64935 : A) : (term755 A B f _64935 u _64934) = (term756 A B u _64934 f _64935).
Proof. exact (@lem5054277 (u _64934) (term746 A B _64934 f _64935)). Qed.
Lemma lem5054286 {A : Type'} (s : A -> Prop) (_64935 : A) : (term352 A s _64935) = (term352 A s _64935).
Proof. exact (eq_refl (term352 A s _64935)). Qed.
Lemma lem5054287 {A B : Type'} (s : A -> Prop) (u : B -> Prop) (_64934 : B) (f : A -> B) (_64935 : A) : (term754 A B s f _64935 u _64934) = (term757 A B s u _64934 f _64935).
Proof. exact (MK_COMB (@lem5054286 A s _64935) (@lem5054278 A B u _64934 f _64935)). Qed.
Lemma lem5054291 (q : Prop) (p : Prop) (r : Prop) : (term278 p q r) = (term278 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5054292 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (_64934 : B) (f : A -> B) (_64935 : A) : (term757 A B s u _64934 f _64935) = (term758 A B u s _64934 f _64935).
Proof. exact (@lem5054291 (u _64934) (term240 A s _64935) (term746 A B _64934 f _64935)). Qed.
Lemma lem5054310 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (_64934 : B) (f : A -> B) (_64935 : A) : (term754 A B s f _64935 u _64934) = (term758 A B u s _64934 f _64935).
Proof. exact (TRANS (@lem5054287 A B s u _64934 f _64935) (@lem5054292 A B u s _64934 f _64935)). Qed.
Lemma lem5054311 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (_64934 : B) (f : A -> B) (_64935 : A) : (term745 A B f s _64935 u _64934) = (term758 A B u s _64934 f _64935).
Proof. exact (TRANS (@lem5054263 A B s f _64935 u _64934) (@lem5054310 A B u s _64934 f _64935)). Qed.
Lemma lem5054312 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5054313 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (_64934 : B) (f : A -> B) (_64935 : A) : (term759 A B f s _64935 u _64934) = (term760 A B u s _64934 f _64935).
Proof. exact (MK_COMB (@lem5054312) (@lem5054311 A B u s _64934 f _64935)). Qed.
Lemma lem5054327 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5054328 {A B : Type'} (s : A -> Prop) (_64934 : B) (f : A -> B) (_64935 : A) : (term489 A B _64934 f s _64935) = (term761 A B s _64934 f _64935).
Proof. exact (@lem5054327 (term240 A s _64935) (term746 A B _64934 f _64935)). Qed.
Lemma lem5054336 {B : Type'} (u : B -> Prop) (_64934 : B) : (term333 B u _64934) = (term333 B u _64934).
Proof. exact (eq_refl (term333 B u _64934)). Qed.
Lemma lem5054337 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (_64934 : B) (f : A -> B) (_64935 : A) : (term762 A B u _64934 f s _64935) = (term758 A B u s _64934 f _64935).
Proof. exact (MK_COMB (@lem5054336 B u _64934) (@lem5054328 A B s _64934 f _64935)). Qed.
Lemma lem5054348 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (_64934 : B) (f : A -> B) (_64935 : A) : ((term745 A B f s _64935 u _64934) = (term762 A B u _64934 f s _64935)) = ((term758 A B u s _64934 f _64935) = (term758 A B u s _64934 f _64935)).
Proof. exact (MK_COMB (@lem5054313 A B u s _64934 f _64935) (@lem5054337 A B u s _64934 f _64935)). Qed.
Lemma lem5054350 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5054351 (x : Prop) : (x = x) = True.
Proof. exact (@lem5054350 Prop x). Qed.
Lemma lem5054352 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (_64934 : B) (f : A -> B) (_64935 : A) : ((term758 A B u s _64934 f _64935) = (term758 A B u s _64934 f _64935)) = True.
Proof. exact (@lem5054351 (term758 A B u s _64934 f _64935)). Qed.
Lemma lem5054353 {A B : Type'} (u : B -> Prop) (_64934 : B) (f : A -> B) (s : A -> Prop) (_64935 : A) : ((term745 A B f s _64935 u _64934) = (term762 A B u _64934 f s _64935)) = True.
Proof. exact (TRANS (@lem5054348 A B u s _64934 f _64935) (@lem5054352 A B u s _64934 f _64935)). Qed.
Lemma lem5054354 {A B : Type'} (u : B -> Prop) (_64934 : B) (f : A -> B) (s : A -> Prop) (_64935 : A) : True = ((term745 A B f s _64935 u _64934) = (term762 A B u _64934 f s _64935)).
Proof. exact (SYM (@lem5054353 A B u _64934 f s _64935)). Qed.
Lemma lem5054355 {A B : Type'} (u : B -> Prop) (_64934 : B) (f : A -> B) (s : A -> Prop) (_64935 : A) : (term745 A B f s _64935 u _64934) = (term762 A B u _64934 f s _64935).
Proof. exact (EQ_MP (@lem5054354 A B u _64934 f s _64935) (@lem0)). Qed.
Lemma lem5054356 {A B : Type'} (_64934 : B) (_64935 : A) (k : A -> Prop) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term430 A B k u s f) : term762 A B u _64934 f s _64935.
Proof. exact (EQ_MP (@lem5054355 A B u _64934 f s _64935) (@lem5054098 A B _64935 _64934 k u s f h1)). Qed.
Lemma lem5054358 (b : Prop) (a : Prop) : (a \/ b) = (term252 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5054359 {A B : Type'} (f : A -> B) (s : A -> Prop) (_64935 : A) (u : B -> Prop) (_64934 : B) : (term762 A B u _64934 f s _64935) = (term763 A B f s _64935 u _64934).
Proof. exact (@lem5054358 (term489 A B _64934 f s _64935) (u _64934)). Qed.
Lemma lem5054361 (a : Prop) (b : Prop) : (term338 a b) = (term339 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5054362 {A B : Type'} (_64934 : B) (f : A -> B) (s : A -> Prop) (_64935 : A) : (term764 A B _64934 f s _64935) = (term765 A B _64934 f s _64935).
Proof. exact (@lem5054361 (term746 A B _64934 f _64935) (term240 A s _64935)). Qed.
Lemma lem5054364 (a : Prop) : (term120 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5054365 {A B : Type'} (_64934 : B) (f : A -> B) (_64935 : A) : (term766 A B _64934 f _64935) = (_64934 = (f _64935)).
Proof. exact (@lem5054364 (_64934 = (f _64935))). Qed.
Lemma lem5054366 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5054367 {A B : Type'} (_64934 : B) (f : A -> B) (_64935 : A) : (term767 A B _64934 f _64935) = (term407 A B _64934 f _64935).
Proof. exact (MK_COMB (@lem5054366) (@lem5054365 A B _64934 f _64935)). Qed.
Lemma lem5054369 (a : Prop) : (term120 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5054370 {A : Type'} (s : A -> Prop) (_64935 : A) : (term263 A s _64935) = (s _64935).
Proof. exact (@lem5054369 (s _64935)). Qed.
Lemma lem5054371 {A B : Type'} (_64934 : B) (f : A -> B) (s : A -> Prop) (_64935 : A) : (term765 A B _64934 f s _64935) = (term409 A B _64934 f s _64935).
Proof. exact (MK_COMB (@lem5054367 A B _64934 f _64935) (@lem5054370 A s _64935)). Qed.
Lemma lem5054372 {A B : Type'} (_64934 : B) (f : A -> B) (s : A -> Prop) (_64935 : A) : (term764 A B _64934 f s _64935) = (term409 A B _64934 f s _64935).
Proof. exact (TRANS (@lem5054362 A B _64934 f s _64935) (@lem5054371 A B _64934 f s _64935)). Qed.
Lemma lem5054373 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5054374 {A B : Type'} (_64934 : B) (f : A -> B) (s : A -> Prop) (_64935 : A) : (term768 A B _64934 f s _64935) = (term769 A B _64934 f s _64935).
Proof. exact (MK_COMB (@lem5054373) (@lem5054372 A B _64934 f s _64935)). Qed.
Lemma lem5054375 {B : Type'} (u : B -> Prop) (_64934 : B) : (u _64934) = (u _64934).
Proof. exact (eq_refl (u _64934)). Qed.
Lemma lem5054376 {A B : Type'} (f : A -> B) (s : A -> Prop) (_64935 : A) (u : B -> Prop) (_64934 : B) : (term763 A B f s _64935 u _64934) = (term770 A B f s _64935 u _64934).
Proof. exact (MK_COMB (@lem5054374 A B _64934 f s _64935) (@lem5054375 B u _64934)). Qed.
Lemma lem5054377 {A B : Type'} (f : A -> B) (s : A -> Prop) (_64935 : A) (u : B -> Prop) (_64934 : B) : (term762 A B u _64934 f s _64935) = (term770 A B f s _64935 u _64934).
Proof. exact (TRANS (@lem5054359 A B f s _64935 u _64934) (@lem5054376 A B f s _64935 u _64934)). Qed.
Lemma lem5054379 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x' : A) (u : B -> Prop) (x : B) (h1 : term430 A B k u s f) (h2 : term599 A B f k x' u x) : term771 A B f s x'.
Proof. exact (conj (@lem5054196 A B f x') (@lem5054256 A B s f k x' u x h1 h2)). Qed.
Lemma lem5054381 {A B : Type'} (_64935 : A) (_64934 : B) (k : A -> Prop) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term430 A B k u s f) : term770 A B f s _64935 u _64934.
Proof. exact (EQ_MP (@lem5054377 A B f s _64935 u _64934) (@lem5054356 A B _64934 _64935 k u s f h1)). Qed.
Lemma lem5054382 {A B : Type'} (_64935 : A) (_64934 : B) (k : A -> Prop) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term430 A B k u s f) : term770 A B f s _64935 u _64934.
Proof. exact (@lem5054381 A B _64935 _64934 k u s f h1). Qed.
Lemma lem5054383 {A B : Type'} (x' : A) (k : A -> Prop) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term430 A B k u s f) : term772 A B s u f x'.
Proof. exact (@lem5054382 A B x' (f x') k u s f h1). Qed.
Lemma lem5054386 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x' : A) (u : B -> Prop) (x : B) (h1 : term430 A B k u s f) (h2 : term599 A B f k x' u x) : term100 A B u f x'.
Proof. exact (@lem5054383 A B x' k u s f h1 (@lem5054379 A B s f k x' u x h1 h2)). Qed.
Lemma lem5054387 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x' : A) (u : B -> Prop) (x : B) (h1 : term430 A B k u s f) (h2 : term599 A B f k x' u x) : term258 A B u f x'.
Proof. exact (fun h0 : term138 A B u f x' => @lem5054386 A B s f k x' u x h1 h2). Qed.
Lemma lem5054389 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5054390 {A B : Type'} (u : B -> Prop) (f : A -> B) (x' : A) : (term258 A B u f x') = (term100 A B u f x').
Proof. exact (@lem5054389 (term100 A B u f x')). Qed.
Lemma lem5054391 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x' : A) (u : B -> Prop) (x : B) (h1 : term430 A B k u s f) (h2 : term599 A B f k x' u x) : term100 A B u f x'.
Proof. exact (EQ_MP (@lem5054390 A B u f x') (@lem5054387 A B s f k x' u x h1 h2)). Qed.
Lemma lem5054394 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5054396 {A B : Type'} (u : B -> Prop) (f : A -> B) (x' : A) : (term138 A B u f x') = (term266 A B u f x').
Proof. exact (@lem5054394 (term100 A B u f x')). Qed.
Lemma lem5054399 {A B : Type'} (f : A -> B) (k : A -> Prop) (x' : A) (u : B -> Prop) (x : B) (h1 : term599 A B f k x' u x) : term266 A B u f x'.
Proof. exact (EQ_MP (@lem5054396 A B u f x') (@lem5054125 A B f k x' u x h1)). Qed.
Lemma lem5054402 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x' : A) (u : B -> Prop) (x : B) (h1 : term430 A B k u s f) (h2 : term599 A B f k x' u x) : False.
Proof. exact (@lem5054399 A B f k x' u x h2 (@lem5054391 A B s f k x' u x h1 h2)). Qed.
Lemma lem5054403 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x' : A) (u : B -> Prop) (x : B) (h1 : term430 A B k u s f) (h2 : term599 A B f k x' u x) : term249.
Proof. exact (fun h0 : ~ False => @lem5054402 A B s f k x' u x h1 h2). Qed.
Lemma lem5054405 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5054406 : term249 = False.
Proof. exact (@lem5054405 False). Qed.
Lemma lem5054420 {A : Type'} (k : A -> Prop) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem5054421 {A : Type'} (_64976 : A) (_64977 : A) (h1 : _64976 = _64977) : _64976 = _64977.
Proof. exact (h1). Qed.
Lemma lem5054422 {A : Type'} (k : A -> Prop) (_64976 : A) (_64977 : A) (h1 : _64976 = _64977) : (k _64976) = (k _64977).
Proof. exact (MK_COMB (@lem5054420 A k) (@lem5054421 A _64976 _64977 h1)). Qed.
Lemma lem5054424 (b : Prop) (a : Prop) : term321 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem5054425 {A : Type'} (_64977 : A) (k : A -> Prop) (_64976 : A) : term322 A _64977 k _64976.
Proof. exact (@lem5054424 (k _64977) (k _64976)). Qed.
Lemma lem5054426 {A : Type'} (k : A -> Prop) (_64976 : A) (_64977 : A) (h1 : _64976 = _64977) : term323 A _64977 k _64976.
Proof. exact (@lem5054425 A _64977 k _64976 (@lem5054422 A k _64976 _64977 h1)). Qed.
Lemma lem5054427 {A : Type'} (_64977 : A) (k : A -> Prop) (_64976 : A) : term324 A _64977 k _64976.
Proof. exact (fun h0 : _64976 = _64977 => @lem5054426 A k _64976 _64977 h0). Qed.
Lemma lem5054429 (a : Prop) (b : Prop) : (a -> b) = (term325 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem5054430 {A : Type'} (_64977 : A) (k : A -> Prop) (_64976 : A) : (term324 A _64977 k _64976) = (term326 A _64977 k _64976).
Proof. exact (@lem5054429 (_64976 = _64977) (term323 A _64977 k _64976)). Qed.
Lemma lem5054431 {A : Type'} (_64977 : A) (k : A -> Prop) (_64976 : A) : term326 A _64977 k _64976.
Proof. exact (EQ_MP (@lem5054430 A _64977 k _64976) (@lem5054427 A _64977 k _64976)). Qed.
Lemma lem5054455 {A : Type'} (x : A) (y : A) (z : A) : term327 A x y z.
Proof. exact (@lem21385 A x y z). Qed.
Lemma lem5054457 {A B : Type'} (s : A -> Prop) (f : A -> B) (x'' : A) (k : A -> Prop) (x' : A) (h1 : term631 A B s f x'' k x') : s x'.
Proof. exact (proj1 (@lem5053406 A B s f x'' k x' h1)). Qed.
Lemma lem5054458 {A B : Type'} (s : A -> Prop) (f : A -> B) (x'' : A) (k : A -> Prop) (x' : A) (h1 : term631 A B s f x'' k x') : term246 A s x'.
Proof. exact (fun h0 : term240 A s x' => @lem5054457 A B s f x'' k x' h1). Qed.
Lemma lem5054460 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5054461 {A : Type'} (s : A -> Prop) (x' : A) : (term246 A s x') = (s x').
Proof. exact (@lem5054460 (s x')). Qed.
Lemma lem5054462 {A B : Type'} (s : A -> Prop) (f : A -> B) (x'' : A) (k : A -> Prop) (x' : A) (h1 : term631 A B s f x'' k x') : s x'.
Proof. exact (EQ_MP (@lem5054461 A s x') (@lem5054458 A B s f x'' k x' h1)). Qed.
Lemma lem5054464 {A B : Type'} (s : A -> Prop) (f : A -> B) (x'' : A) (k : A -> Prop) (x' : A) (h1 : term631 A B s f x'' k x') : k x''.
Proof. exact (proj2 (@lem5053407 A B s f x'' k x' h1)). Qed.
Lemma lem5054465 {A B : Type'} (s : A -> Prop) (f : A -> B) (x'' : A) (k : A -> Prop) (x' : A) (h1 : term631 A B s f x'' k x') : term246 A k x''.
Proof. exact (fun h0 : term240 A k x'' => @lem5054464 A B s f x'' k x' h1). Qed.
Lemma lem5054467 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5054468 {A : Type'} (k : A -> Prop) (x'' : A) : (term246 A k x'') = (k x'').
Proof. exact (@lem5054467 (k x'')). Qed.
Lemma lem5054469 {A B : Type'} (s : A -> Prop) (f : A -> B) (x'' : A) (k : A -> Prop) (x' : A) (h1 : term631 A B s f x'' k x') : k x''.
Proof. exact (EQ_MP (@lem5054468 A k x'') (@lem5054465 A B s f x'' k x' h1)). Qed.
Lemma lem5054475 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5054476 {A : Type'} (s : A -> Prop) (k : A -> Prop) (_64938 : A) : (term150 A k s _64938) = (term259 A s k _64938).
Proof. exact (@lem5054475 (s _64938) (term240 A k _64938)). Qed.
Lemma lem5054482 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5054483 {A : Type'} (s : A -> Prop) (k : A -> Prop) (_64938 : A) : (term260 A k s _64938) = (term261 A s k _64938).
Proof. exact (MK_COMB (@lem5054482) (@lem5054476 A s k _64938)). Qed.
Lemma lem5054489 {A : Type'} (s : A -> Prop) (k : A -> Prop) (_64938 : A) : (term259 A s k _64938) = (term259 A s k _64938).
Proof. exact (eq_refl (term259 A s k _64938)). Qed.
Lemma lem5054490 {A : Type'} (s : A -> Prop) (k : A -> Prop) (_64938 : A) : ((term150 A k s _64938) = (term259 A s k _64938)) = ((term259 A s k _64938) = (term259 A s k _64938)).
Proof. exact (MK_COMB (@lem5054483 A s k _64938) (@lem5054489 A s k _64938)). Qed.
Lemma lem5054492 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5054493 (x : Prop) : (x = x) = True.
Proof. exact (@lem5054492 Prop x). Qed.
Lemma lem5054494 {A : Type'} (s : A -> Prop) (k : A -> Prop) (_64938 : A) : ((term259 A s k _64938) = (term259 A s k _64938)) = True.
Proof. exact (@lem5054493 (term259 A s k _64938)). Qed.
Lemma lem5054495 {A : Type'} (s : A -> Prop) (k : A -> Prop) (_64938 : A) : ((term150 A k s _64938) = (term259 A s k _64938)) = True.
Proof. exact (TRANS (@lem5054490 A s k _64938) (@lem5054494 A s k _64938)). Qed.
Lemma lem5054496 {A : Type'} (s : A -> Prop) (k : A -> Prop) (_64938 : A) : True = ((term150 A k s _64938) = (term259 A s k _64938)).
Proof. exact (SYM (@lem5054495 A s k _64938)). Qed.
Lemma lem5054497 {A : Type'} (s : A -> Prop) (k : A -> Prop) (_64938 : A) : (term150 A k s _64938) = (term259 A s k _64938).
Proof. exact (EQ_MP (@lem5054496 A s k _64938) (@lem0)). Qed.
Lemma lem5054498 {A B : Type'} (_64938 : A) (k : A -> Prop) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term430 A B k u s f) : term259 A s k _64938.
Proof. exact (EQ_MP (@lem5054497 A s k _64938) (@lem5053934 A B _64938 k u s f h1)). Qed.
Lemma lem5054500 (b : Prop) (a : Prop) : (a \/ b) = (term252 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5054501 {A : Type'} (k : A -> Prop) (s : A -> Prop) (_64938 : A) : (term259 A s k _64938) = (term262 A k s _64938).
Proof. exact (@lem5054500 (term240 A k _64938) (s _64938)). Qed.
Lemma lem5054503 (a : Prop) : (term120 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5054504 {A : Type'} (k : A -> Prop) (_64938 : A) : (term263 A k _64938) = (k _64938).
Proof. exact (@lem5054503 (k _64938)). Qed.
Lemma lem5054505 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5054506 {A : Type'} (k : A -> Prop) (_64938 : A) : (term264 A k _64938) = (term58 A k _64938).
Proof. exact (MK_COMB (@lem5054505) (@lem5054504 A k _64938)). Qed.
Lemma lem5054507 {A : Type'} (s : A -> Prop) (_64938 : A) : (s _64938) = (s _64938).
Proof. exact (eq_refl (s _64938)). Qed.
Lemma lem5054508 {A : Type'} (k : A -> Prop) (s : A -> Prop) (_64938 : A) : (term262 A k s _64938) = (term74 A k s _64938).
Proof. exact (MK_COMB (@lem5054506 A k _64938) (@lem5054507 A s _64938)). Qed.
Lemma lem5054509 {A : Type'} (k : A -> Prop) (s : A -> Prop) (_64938 : A) : (term259 A s k _64938) = (term74 A k s _64938).
Proof. exact (TRANS (@lem5054501 A k s _64938) (@lem5054508 A k s _64938)). Qed.
Lemma lem5054512 {A B : Type'} (_64938 : A) (k : A -> Prop) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term430 A B k u s f) : term74 A k s _64938.
Proof. exact (EQ_MP (@lem5054509 A k s _64938) (@lem5054498 A B _64938 k u s f h1)). Qed.
Lemma lem5054513 {A B : Type'} (_64938 : A) (k : A -> Prop) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term430 A B k u s f) : term74 A k s _64938.
Proof. exact (@lem5054512 A B _64938 k u s f h1). Qed.
Lemma lem5054514 {A B : Type'} (x'' : A) (k : A -> Prop) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term430 A B k u s f) : term74 A k s x''.
Proof. exact (@lem5054513 A B x'' k u s f h1). Qed.
Lemma lem5054517 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x'' : A) (k : A -> Prop) (x' : A) (h1 : term430 A B k u s f) (h2 : term631 A B s f x'' k x') : s x''.
Proof. exact (@lem5054514 A B x'' k u s f h1 (@lem5054469 A B s f x'' k x' h2)). Qed.
Lemma lem5054518 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x'' : A) (k : A -> Prop) (x' : A) (h1 : term430 A B k u s f) (h2 : term631 A B s f x'' k x') : term246 A s x''.
Proof. exact (fun h0 : term240 A s x'' => @lem5054517 A B u s f x'' k x' h1 h2). Qed.
Lemma lem5054520 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5054521 {A : Type'} (s : A -> Prop) (x'' : A) : (term246 A s x'') = (s x'').
Proof. exact (@lem5054520 (s x'')). Qed.
Lemma lem5054522 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x'' : A) (k : A -> Prop) (x' : A) (h1 : term430 A B k u s f) (h2 : term631 A B s f x'' k x') : s x''.
Proof. exact (EQ_MP (@lem5054521 A s x'') (@lem5054518 A B u s f x'' k x' h1 h2)). Qed.
Lemma lem5054524 {A B : Type'} (s : A -> Prop) (f : A -> B) (x'' : A) (k : A -> Prop) (x' : A) (h1 : term631 A B s f x'' k x') : (f x') = (f x'').
Proof. exact (proj1 (@lem5053407 A B s f x'' k x' h1)). Qed.
Lemma lem5054525 {A B : Type'} (s : A -> Prop) (f : A -> B) (x'' : A) (k : A -> Prop) (x' : A) (h1 : term631 A B s f x'' k x') : term328 A B x' f x''.
Proof. exact (fun h0 : term329 A B x' f x'' => @lem5054524 A B s f x'' k x' h1). Qed.
Lemma lem5054527 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5054528 {A B : Type'} (x' : A) (f : A -> B) (x'' : A) : (term328 A B x' f x'') = ((f x') = (f x'')).
Proof. exact (@lem5054527 ((f x') = (f x''))). Qed.
Lemma lem5054529 {A B : Type'} (s : A -> Prop) (f : A -> B) (x'' : A) (k : A -> Prop) (x' : A) (h1 : term631 A B s f x'' k x') : (f x') = (f x'').
Proof. exact (EQ_MP (@lem5054528 A B x' f x'') (@lem5054525 A B s f x'' k x' h1)). Qed.
Lemma lem5054555 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5054556 {A B : Type'} (_64941 : A) (f : A -> B) (_64942 : A) : (term773 A B f _64941 _64942) = (term774 A B _64941 f _64942).
Proof. exact (@lem5054555 (_64941 = _64942) (term329 A B _64941 f _64942)). Qed.
Lemma lem5054566 {A : Type'} (s : A -> Prop) (_64942 : A) : (term352 A s _64942) = (term352 A s _64942).
Proof. exact (eq_refl (term352 A s _64942)). Qed.
Lemma lem5054567 {A B : Type'} (s : A -> Prop) (_64941 : A) (f : A -> B) (_64942 : A) : (term749 A B s f _64941 _64942) = (term775 A B s _64941 f _64942).
Proof. exact (MK_COMB (@lem5054566 A s _64942) (@lem5054556 A B _64941 f _64942)). Qed.
Lemma lem5054571 (q : Prop) (p : Prop) (r : Prop) : (term278 p q r) = (term278 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5054572 {A B : Type'} (s : A -> Prop) (_64941 : A) (f : A -> B) (_64942 : A) : (term775 A B s _64941 f _64942) = (term776 A B s _64941 f _64942).
Proof. exact (@lem5054571 (_64941 = _64942) (term240 A s _64942) (term329 A B _64941 f _64942)). Qed.
Lemma lem5054592 {A B : Type'} (s : A -> Prop) (_64941 : A) (f : A -> B) (_64942 : A) : (term749 A B s f _64941 _64942) = (term776 A B s _64941 f _64942).
Proof. exact (TRANS (@lem5054567 A B s _64941 f _64942) (@lem5054572 A B s _64941 f _64942)). Qed.
Lemma lem5054593 {A : Type'} (s : A -> Prop) (_64941 : A) : (term352 A s _64941) = (term352 A s _64941).
Proof. exact (eq_refl (term352 A s _64941)). Qed.
Lemma lem5054594 {A B : Type'} (s : A -> Prop) (_64941 : A) (f : A -> B) (_64942 : A) : (term750 A B s f _64941 _64942) = (term777 A B s _64941 f _64942).
Proof. exact (MK_COMB (@lem5054593 A s _64941) (@lem5054592 A B s _64941 f _64942)). Qed.
Lemma lem5054598 (q : Prop) (p : Prop) (r : Prop) : (term278 p q r) = (term278 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5054599 {A B : Type'} (s : A -> Prop) (_64941 : A) (f : A -> B) (_64942 : A) : (term777 A B s _64941 f _64942) = (term778 A B s _64941 f _64942).
Proof. exact (@lem5054598 (_64941 = _64942) (term240 A s _64941) (term506 A B s _64941 f _64942)). Qed.
Lemma lem5054629 {A B : Type'} (s : A -> Prop) (_64941 : A) (f : A -> B) (_64942 : A) : (term750 A B s f _64941 _64942) = (term778 A B s _64941 f _64942).
Proof. exact (TRANS (@lem5054594 A B s _64941 f _64942) (@lem5054599 A B s _64941 f _64942)). Qed.
Lemma lem5054630 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5054631 {A B : Type'} (s : A -> Prop) (_64941 : A) (f : A -> B) (_64942 : A) : (term779 A B s f _64941 _64942) = (term780 A B s _64941 f _64942).
Proof. exact (MK_COMB (@lem5054630) (@lem5054629 A B s _64941 f _64942)). Qed.
Lemma lem5054661 {A B : Type'} (s : A -> Prop) (_64941 : A) (f : A -> B) (_64942 : A) : (term778 A B s _64941 f _64942) = (term778 A B s _64941 f _64942).
Proof. exact (eq_refl (term778 A B s _64941 f _64942)). Qed.
Lemma lem5054662 {A B : Type'} (s : A -> Prop) (_64941 : A) (f : A -> B) (_64942 : A) : ((term750 A B s f _64941 _64942) = (term778 A B s _64941 f _64942)) = ((term778 A B s _64941 f _64942) = (term778 A B s _64941 f _64942)).
Proof. exact (MK_COMB (@lem5054631 A B s _64941 f _64942) (@lem5054661 A B s _64941 f _64942)). Qed.
Lemma lem5054664 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5054665 (x : Prop) : (x = x) = True.
Proof. exact (@lem5054664 Prop x). Qed.
Lemma lem5054666 {A B : Type'} (s : A -> Prop) (_64941 : A) (f : A -> B) (_64942 : A) : ((term778 A B s _64941 f _64942) = (term778 A B s _64941 f _64942)) = True.
Proof. exact (@lem5054665 (term778 A B s _64941 f _64942)). Qed.
Lemma lem5054667 {A B : Type'} (s : A -> Prop) (_64941 : A) (f : A -> B) (_64942 : A) : ((term750 A B s f _64941 _64942) = (term778 A B s _64941 f _64942)) = True.
Proof. exact (TRANS (@lem5054662 A B s _64941 f _64942) (@lem5054666 A B s _64941 f _64942)). Qed.
Lemma lem5054668 {A B : Type'} (s : A -> Prop) (_64941 : A) (f : A -> B) (_64942 : A) : True = ((term750 A B s f _64941 _64942) = (term778 A B s _64941 f _64942)).
Proof. exact (SYM (@lem5054667 A B s _64941 f _64942)). Qed.
Lemma lem5054669 {A B : Type'} (s : A -> Prop) (_64941 : A) (f : A -> B) (_64942 : A) : (term750 A B s f _64941 _64942) = (term778 A B s _64941 f _64942).
Proof. exact (EQ_MP (@lem5054668 A B s _64941 f _64942) (@lem0)). Qed.
Lemma lem5054670 {A B : Type'} (_64941 : A) (_64942 : A) (k : A -> Prop) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term430 A B k u s f) : term778 A B s _64941 f _64942.
Proof. exact (EQ_MP (@lem5054669 A B s _64941 f _64942) (@lem5053964 A B _64941 _64942 k u s f h1)). Qed.
Lemma lem5054672 (b : Prop) (a : Prop) : (a \/ b) = (term252 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5054673 {A B : Type'} (s : A -> Prop) (f : A -> B) (_64941 : A) (_64942 : A) : (term778 A B s _64941 f _64942) = (term781 A B s f _64941 _64942).
Proof. exact (@lem5054672 (term508 A B s _64941 f _64942) (_64941 = _64942)). Qed.
Lemma lem5054675 (a : Prop) (b : Prop) : (term338 a b) = (term339 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5054676 {A B : Type'} (s : A -> Prop) (_64941 : A) (f : A -> B) (_64942 : A) : (term782 A B s _64941 f _64942) = (term783 A B s _64941 f _64942).
Proof. exact (@lem5054675 (term240 A s _64941) (term506 A B s _64941 f _64942)). Qed.
Lemma lem5054678 (a : Prop) : (term120 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5054679 {A : Type'} (s : A -> Prop) (_64941 : A) : (term263 A s _64941) = (s _64941).
Proof. exact (@lem5054678 (s _64941)). Qed.
Lemma lem5054680 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5054681 {A : Type'} (s : A -> Prop) (_64941 : A) : (term360 A s _64941) = (term99 A s _64941).
Proof. exact (MK_COMB (@lem5054680) (@lem5054679 A s _64941)). Qed.
Lemma lem5054683 (a : Prop) (b : Prop) : (term338 a b) = (term339 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5054684 {A B : Type'} (s : A -> Prop) (_64941 : A) (f : A -> B) (_64942 : A) : (term784 A B s _64941 f _64942) = (term785 A B s _64941 f _64942).
Proof. exact (@lem5054683 (term240 A s _64942) (term329 A B _64941 f _64942)). Qed.
Lemma lem5054686 (a : Prop) : (term120 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5054687 {A : Type'} (s : A -> Prop) (_64942 : A) : (term263 A s _64942) = (s _64942).
Proof. exact (@lem5054686 (s _64942)). Qed.
Lemma lem5054688 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5054689 {A : Type'} (s : A -> Prop) (_64942 : A) : (term360 A s _64942) = (term99 A s _64942).
Proof. exact (MK_COMB (@lem5054688) (@lem5054687 A s _64942)). Qed.
Lemma lem5054691 (a : Prop) : (term120 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5054692 {A B : Type'} (_64941 : A) (f : A -> B) (_64942 : A) : (term786 A B _64941 f _64942) = ((f _64941) = (f _64942)).
Proof. exact (@lem5054691 ((f _64941) = (f _64942))). Qed.
Lemma lem5054693 {A B : Type'} (s : A -> Prop) (_64941 : A) (f : A -> B) (_64942 : A) : (term785 A B s _64941 f _64942) = (term418 A B s _64941 f _64942).
Proof. exact (MK_COMB (@lem5054689 A s _64942) (@lem5054692 A B _64941 f _64942)). Qed.
Lemma lem5054694 {A B : Type'} (s : A -> Prop) (_64941 : A) (f : A -> B) (_64942 : A) : (term784 A B s _64941 f _64942) = (term418 A B s _64941 f _64942).
Proof. exact (TRANS (@lem5054684 A B s _64941 f _64942) (@lem5054693 A B s _64941 f _64942)). Qed.
Lemma lem5054695 {A B : Type'} (s : A -> Prop) (_64941 : A) (f : A -> B) (_64942 : A) : (term783 A B s _64941 f _64942) = (term419 A B s _64941 f _64942).
Proof. exact (MK_COMB (@lem5054681 A s _64941) (@lem5054694 A B s _64941 f _64942)). Qed.
Lemma lem5054696 {A B : Type'} (s : A -> Prop) (_64941 : A) (f : A -> B) (_64942 : A) : (term782 A B s _64941 f _64942) = (term419 A B s _64941 f _64942).
Proof. exact (TRANS (@lem5054676 A B s _64941 f _64942) (@lem5054695 A B s _64941 f _64942)). Qed.
Lemma lem5054697 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5054698 {A B : Type'} (s : A -> Prop) (_64941 : A) (f : A -> B) (_64942 : A) : (term787 A B s _64941 f _64942) = (term421 A B s _64941 f _64942).
Proof. exact (MK_COMB (@lem5054697) (@lem5054696 A B s _64941 f _64942)). Qed.
Lemma lem5054699 {A : Type'} (_64941 : A) (_64942 : A) : (_64941 = _64942) = (_64941 = _64942).
Proof. exact (eq_refl (_64941 = _64942)). Qed.
Lemma lem5054700 {A B : Type'} (s : A -> Prop) (f : A -> B) (_64941 : A) (_64942 : A) : (term781 A B s f _64941 _64942) = (term422 A B s f _64941 _64942).
Proof. exact (MK_COMB (@lem5054698 A B s _64941 f _64942) (@lem5054699 A _64941 _64942)). Qed.
Lemma lem5054701 {A B : Type'} (s : A -> Prop) (f : A -> B) (_64941 : A) (_64942 : A) : (term778 A B s _64941 f _64942) = (term422 A B s f _64941 _64942).
Proof. exact (TRANS (@lem5054673 A B s f _64941 _64942) (@lem5054700 A B s f _64941 _64942)). Qed.
Lemma lem5054703 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x'' : A) (k : A -> Prop) (x' : A) (h1 : term430 A B k u s f) (h2 : term631 A B s f x'' k x') : term418 A B s x' f x''.
Proof. exact (conj (@lem5054522 A B u s f x'' k x' h1 h2) (@lem5054529 A B s f x'' k x' h2)). Qed.
Lemma lem5054704 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x'' : A) (k : A -> Prop) (x' : A) (h1 : term430 A B k u s f) (h2 : term631 A B s f x'' k x') : term419 A B s x' f x''.
Proof. exact (conj (@lem5054462 A B s f x'' k x' h2) (@lem5054703 A B u s f x'' k x' h1 h2)). Qed.
Lemma lem5054706 {A B : Type'} (_64941 : A) (_64942 : A) (k : A -> Prop) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term430 A B k u s f) : term422 A B s f _64941 _64942.
Proof. exact (EQ_MP (@lem5054701 A B s f _64941 _64942) (@lem5054670 A B _64941 _64942 k u s f h1)). Qed.
Lemma lem5054707 {A B : Type'} (_64941 : A) (_64942 : A) (k : A -> Prop) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term430 A B k u s f) : term422 A B s f _64941 _64942.
Proof. exact (@lem5054706 A B _64941 _64942 k u s f h1). Qed.
Lemma lem5054708 {A B : Type'} (x' : A) (x'' : A) (k : A -> Prop) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term430 A B k u s f) : term422 A B s f x' x''.
Proof. exact (@lem5054707 A B x' x'' k u s f h1). Qed.
Lemma lem5054711 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x'' : A) (k : A -> Prop) (x' : A) (h1 : term430 A B k u s f) (h2 : term631 A B s f x'' k x') : x' = x''.
Proof. exact (@lem5054708 A B x' x'' k u s f h1 (@lem5054704 A B u s f x'' k x' h1 h2)). Qed.
Lemma lem5054712 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x'' : A) (k : A -> Prop) (x' : A) (h1 : term430 A B k u s f) (h2 : term631 A B s f x'' k x') : term365 A x' x''.
Proof. exact (fun h0 : term235 A x' x'' => @lem5054711 A B u s f x'' k x' h1 h2). Qed.
Lemma lem5054714 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5054715 {A : Type'} (x' : A) (x'' : A) : (term365 A x' x'') = (x' = x'').
Proof. exact (@lem5054714 (x' = x'')). Qed.
Lemma lem5054716 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x'' : A) (k : A -> Prop) (x' : A) (h1 : term430 A B k u s f) (h2 : term631 A B s f x'' k x') : x' = x''.
Proof. exact (EQ_MP (@lem5054715 A x' x'') (@lem5054712 A B u s f x'' k x' h1 h2)). Qed.
Lemma lem5054718 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem5054719 {A : Type'} (x : A) : x = x.
Proof. exact (@lem5054718 A x). Qed.
Lemma lem5054720 {A : Type'} (x' : A) : x' = x'.
Proof. exact (@lem5054719 A x'). Qed.
Lemma lem5054721 {A : Type'} (x' : A) : term250 A x'.
Proof. exact (fun h0 : term251 A x' => @lem5054720 A x'). Qed.
Lemma lem5054723 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5054724 {A : Type'} (x' : A) : (term250 A x') = (x' = x').
Proof. exact (@lem5054723 (x' = x')). Qed.
Lemma lem5054725 {A : Type'} (x' : A) : x' = x'.
Proof. exact (EQ_MP (@lem5054724 A x') (@lem5054721 A x')). Qed.
Lemma lem5054743 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5054744 {A : Type'} (y : A) (x : A) (z : A) : (term366 A x y z) = (term367 A y x z).
Proof. exact (@lem5054743 (y = z) (term235 A x z)). Qed.
Lemma lem5054754 {A : Type'} (x : A) (y : A) : (term368 A x y) = (term368 A x y).
Proof. exact (eq_refl (term368 A x y)). Qed.
Lemma lem5054755 {A : Type'} (y : A) (x : A) (z : A) : (term327 A x y z) = (term369 A y x z).
Proof. exact (MK_COMB (@lem5054754 A x y) (@lem5054744 A y x z)). Qed.
Lemma lem5054759 (q : Prop) (p : Prop) (r : Prop) : (term278 p q r) = (term278 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5054760 {A : Type'} (y : A) (x : A) (z : A) : (term369 A y x z) = (term370 A y x z).
Proof. exact (@lem5054759 (y = z) (term235 A x y) (term235 A x z)). Qed.
Lemma lem5054782 {A : Type'} (y : A) (x : A) (z : A) : (term327 A x y z) = (term370 A y x z).
Proof. exact (TRANS (@lem5054755 A y x z) (@lem5054760 A y x z)). Qed.
Lemma lem5054783 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5054784 {A : Type'} (y : A) (x : A) (z : A) : (term371 A x y z) = (term372 A y x z).
Proof. exact (MK_COMB (@lem5054783) (@lem5054782 A y x z)). Qed.
Lemma lem5054806 {A : Type'} (y : A) (x : A) (z : A) : (term370 A y x z) = (term370 A y x z).
Proof. exact (eq_refl (term370 A y x z)). Qed.
Lemma lem5054807 {A : Type'} (y : A) (x : A) (z : A) : ((term327 A x y z) = (term370 A y x z)) = ((term370 A y x z) = (term370 A y x z)).
Proof. exact (MK_COMB (@lem5054784 A y x z) (@lem5054806 A y x z)). Qed.
Lemma lem5054809 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5054810 (x : Prop) : (x = x) = True.
Proof. exact (@lem5054809 Prop x). Qed.
Lemma lem5054811 {A : Type'} (y : A) (x : A) (z : A) : ((term370 A y x z) = (term370 A y x z)) = True.
Proof. exact (@lem5054810 (term370 A y x z)). Qed.
Lemma lem5054812 {A : Type'} (y : A) (x : A) (z : A) : ((term327 A x y z) = (term370 A y x z)) = True.
Proof. exact (TRANS (@lem5054807 A y x z) (@lem5054811 A y x z)). Qed.
Lemma lem5054813 {A : Type'} (y : A) (x : A) (z : A) : True = ((term327 A x y z) = (term370 A y x z)).
Proof. exact (SYM (@lem5054812 A y x z)). Qed.
Lemma lem5054814 {A : Type'} (y : A) (x : A) (z : A) : (term327 A x y z) = (term370 A y x z).
Proof. exact (EQ_MP (@lem5054813 A y x z) (@lem0)). Qed.
Lemma lem5054815 {A : Type'} (y : A) (x : A) (z : A) : term370 A y x z.
Proof. exact (EQ_MP (@lem5054814 A y x z) (@lem5054455 A x y z)). Qed.
Lemma lem5054817 (b : Prop) (a : Prop) : (a \/ b) = (term252 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5054818 {A : Type'} (x : A) (y : A) (z : A) : (term370 A y x z) = (term373 A x y z).
Proof. exact (@lem5054817 (term374 A y x z) (y = z)). Qed.
Lemma lem5054820 (a : Prop) (b : Prop) : (term338 a b) = (term339 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5054821 {A : Type'} (y : A) (x : A) (z : A) : (term375 A y x z) = (term376 A y x z).
Proof. exact (@lem5054820 (term235 A x y) (term235 A x z)). Qed.
Lemma lem5054823 (a : Prop) : (term120 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5054824 {A : Type'} (x : A) (y : A) : (term254 A x y) = (x = y).
Proof. exact (@lem5054823 (x = y)). Qed.
Lemma lem5054825 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5054826 {A : Type'} (x : A) (y : A) : (term342 A x y) = (term343 A x y).
Proof. exact (MK_COMB (@lem5054825) (@lem5054824 A x y)). Qed.
Lemma lem5054828 (a : Prop) : (term120 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5054829 {A : Type'} (x : A) (z : A) : (term254 A x z) = (x = z).
Proof. exact (@lem5054828 (x = z)). Qed.
Lemma lem5054830 {A : Type'} (y : A) (x : A) (z : A) : (term376 A y x z) = (term377 A y x z).
Proof. exact (MK_COMB (@lem5054826 A x y) (@lem5054829 A x z)). Qed.
Lemma lem5054831 {A : Type'} (y : A) (x : A) (z : A) : (term375 A y x z) = (term377 A y x z).
Proof. exact (TRANS (@lem5054821 A y x z) (@lem5054830 A y x z)). Qed.
Lemma lem5054832 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5054833 {A : Type'} (y : A) (x : A) (z : A) : (term378 A y x z) = (term379 A y x z).
Proof. exact (MK_COMB (@lem5054832) (@lem5054831 A y x z)). Qed.
Lemma lem5054834 {A : Type'} (y : A) (z : A) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem5054835 {A : Type'} (x : A) (y : A) (z : A) : (term373 A x y z) = (term380 A x y z).
Proof. exact (MK_COMB (@lem5054833 A y x z) (@lem5054834 A y z)). Qed.
Lemma lem5054836 {A : Type'} (x : A) (y : A) (z : A) : (term370 A y x z) = (term380 A x y z).
Proof. exact (TRANS (@lem5054818 A x y z) (@lem5054835 A x y z)). Qed.
Lemma lem5054838 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x'' : A) (k : A -> Prop) (x' : A) (h1 : term430 A B k u s f) (h2 : term631 A B s f x'' k x') : term381 A x'' x'.
Proof. exact (conj (@lem5054716 A B u s f x'' k x' h1 h2) (@lem5054725 A x')). Qed.
Lemma lem5054840 {A : Type'} (x : A) (y : A) (z : A) : term380 A x y z.
Proof. exact (EQ_MP (@lem5054836 A x y z) (@lem5054815 A y x z)). Qed.
Lemma lem5054841 {A : Type'} (x : A) (y : A) (z : A) : term380 A x y z.
Proof. exact (@lem5054840 A x y z). Qed.
Lemma lem5054842 {A : Type'} (x'' : A) (x' : A) : term382 A x'' x'.
Proof. exact (@lem5054841 A x' x'' x'). Qed.
Lemma lem5054845 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x'' : A) (k : A -> Prop) (x' : A) (h1 : term430 A B k u s f) (h2 : term631 A B s f x'' k x') : x'' = x'.
Proof. exact (@lem5054842 A x'' x' (@lem5054838 A B u s f x'' k x' h1 h2)). Qed.
Lemma lem5054846 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x'' : A) (k : A -> Prop) (x' : A) (h1 : term430 A B k u s f) (h2 : term631 A B s f x'' k x') : term365 A x'' x'.
Proof. exact (fun h0 : term235 A x'' x' => @lem5054845 A B u s f x'' k x' h1 h2). Qed.
Lemma lem5054848 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5054849 {A : Type'} (x'' : A) (x' : A) : (term365 A x'' x') = (x'' = x').
Proof. exact (@lem5054848 (x'' = x')). Qed.
Lemma lem5054850 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x'' : A) (k : A -> Prop) (x' : A) (h1 : term430 A B k u s f) (h2 : term631 A B s f x'' k x') : x'' = x'.
Proof. exact (EQ_MP (@lem5054849 A x'' x') (@lem5054846 A B u s f x'' k x' h1 h2)). Qed.
Lemma lem5054852 {A B : Type'} (s : A -> Prop) (f : A -> B) (x'' : A) (k : A -> Prop) (x' : A) (h1 : term631 A B s f x'' k x') : k x''.
Proof. exact (proj2 (@lem5053407 A B s f x'' k x' h1)). Qed.
Lemma lem5054853 {A B : Type'} (s : A -> Prop) (f : A -> B) (x'' : A) (k : A -> Prop) (x' : A) (h1 : term631 A B s f x'' k x') : term246 A k x''.
Proof. exact (fun h0 : term240 A k x'' => @lem5054852 A B s f x'' k x' h1). Qed.
Lemma lem5054855 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5054856 {A : Type'} (k : A -> Prop) (x'' : A) : (term246 A k x'') = (k x'').
Proof. exact (@lem5054855 (k x'')). Qed.
Lemma lem5054857 {A B : Type'} (s : A -> Prop) (f : A -> B) (x'' : A) (k : A -> Prop) (x' : A) (h1 : term631 A B s f x'' k x') : k x''.
Proof. exact (EQ_MP (@lem5054856 A k x'') (@lem5054853 A B s f x'' k x' h1)). Qed.
Lemma lem5054863 (q : Prop) (p : Prop) (r : Prop) : (term278 p q r) = (term278 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5054864 {A : Type'} (_64977 : A) (k : A -> Prop) (_64976 : A) : (term326 A _64977 k _64976) = (term330 A _64977 k _64976).
Proof. exact (@lem5054863 (k _64977) (term235 A _64976 _64977) (term240 A k _64976)). Qed.
Lemma lem5054878 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5054879 {A : Type'} (k : A -> Prop) (_64976 : A) (_64977 : A) : (term331 A _64977 k _64976) = (term332 A k _64976 _64977).
Proof. exact (@lem5054878 (term240 A k _64976) (term235 A _64976 _64977)). Qed.
Lemma lem5054887 {A : Type'} (k : A -> Prop) (_64977 : A) : (term333 A k _64977) = (term333 A k _64977).
Proof. exact (eq_refl (term333 A k _64977)). Qed.
Lemma lem5054888 {A : Type'} (k : A -> Prop) (_64976 : A) (_64977 : A) : (term330 A _64977 k _64976) = (term334 A k _64976 _64977).
Proof. exact (MK_COMB (@lem5054887 A k _64977) (@lem5054879 A k _64976 _64977)). Qed.
Lemma lem5054899 {A : Type'} (k : A -> Prop) (_64976 : A) (_64977 : A) : (term326 A _64977 k _64976) = (term334 A k _64976 _64977).
Proof. exact (TRANS (@lem5054864 A _64977 k _64976) (@lem5054888 A k _64976 _64977)). Qed.
Lemma lem5054900 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5054901 {A : Type'} (k : A -> Prop) (_64976 : A) (_64977 : A) : (term335 A _64977 k _64976) = (term336 A k _64976 _64977).
Proof. exact (MK_COMB (@lem5054900) (@lem5054899 A k _64976 _64977)). Qed.
Lemma lem5054915 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5054916 {A : Type'} (k : A -> Prop) (_64976 : A) (_64977 : A) : (term331 A _64977 k _64976) = (term332 A k _64976 _64977).
Proof. exact (@lem5054915 (term240 A k _64976) (term235 A _64976 _64977)). Qed.
Lemma lem5054924 {A : Type'} (k : A -> Prop) (_64977 : A) : (term333 A k _64977) = (term333 A k _64977).
Proof. exact (eq_refl (term333 A k _64977)). Qed.
Lemma lem5054925 {A : Type'} (k : A -> Prop) (_64976 : A) (_64977 : A) : (term330 A _64977 k _64976) = (term334 A k _64976 _64977).
Proof. exact (MK_COMB (@lem5054924 A k _64977) (@lem5054916 A k _64976 _64977)). Qed.
Lemma lem5054936 {A : Type'} (k : A -> Prop) (_64976 : A) (_64977 : A) : ((term326 A _64977 k _64976) = (term330 A _64977 k _64976)) = ((term334 A k _64976 _64977) = (term334 A k _64976 _64977)).
Proof. exact (MK_COMB (@lem5054901 A k _64976 _64977) (@lem5054925 A k _64976 _64977)). Qed.
Lemma lem5054938 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5054939 (x : Prop) : (x = x) = True.
Proof. exact (@lem5054938 Prop x). Qed.
Lemma lem5054940 {A : Type'} (k : A -> Prop) (_64976 : A) (_64977 : A) : ((term334 A k _64976 _64977) = (term334 A k _64976 _64977)) = True.
Proof. exact (@lem5054939 (term334 A k _64976 _64977)). Qed.
Lemma lem5054941 {A : Type'} (_64977 : A) (k : A -> Prop) (_64976 : A) : ((term326 A _64977 k _64976) = (term330 A _64977 k _64976)) = True.
Proof. exact (TRANS (@lem5054936 A k _64976 _64977) (@lem5054940 A k _64976 _64977)). Qed.
Lemma lem5054942 {A : Type'} (_64977 : A) (k : A -> Prop) (_64976 : A) : True = ((term326 A _64977 k _64976) = (term330 A _64977 k _64976)).
Proof. exact (SYM (@lem5054941 A _64977 k _64976)). Qed.
Lemma lem5054943 {A : Type'} (_64977 : A) (k : A -> Prop) (_64976 : A) : (term326 A _64977 k _64976) = (term330 A _64977 k _64976).
Proof. exact (EQ_MP (@lem5054942 A _64977 k _64976) (@lem0)). Qed.
Lemma lem5054944 {A : Type'} (_64977 : A) (k : A -> Prop) (_64976 : A) : term330 A _64977 k _64976.
Proof. exact (EQ_MP (@lem5054943 A _64977 k _64976) (@lem5054431 A _64977 k _64976)). Qed.
Lemma lem5054946 (b : Prop) (a : Prop) : (a \/ b) = (term252 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5054947 {A : Type'} (_64976 : A) (k : A -> Prop) (_64977 : A) : (term330 A _64977 k _64976) = (term337 A _64976 k _64977).
Proof. exact (@lem5054946 (term331 A _64977 k _64976) (k _64977)). Qed.
Lemma lem5054949 (a : Prop) (b : Prop) : (term338 a b) = (term339 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5054950 {A : Type'} (_64977 : A) (k : A -> Prop) (_64976 : A) : (term340 A _64977 k _64976) = (term341 A _64977 k _64976).
Proof. exact (@lem5054949 (term235 A _64976 _64977) (term240 A k _64976)). Qed.
Lemma lem5054952 (a : Prop) : (term120 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5054953 {A : Type'} (_64976 : A) (_64977 : A) : (term254 A _64976 _64977) = (_64976 = _64977).
Proof. exact (@lem5054952 (_64976 = _64977)). Qed.
Lemma lem5054954 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5054955 {A : Type'} (_64976 : A) (_64977 : A) : (term342 A _64976 _64977) = (term343 A _64976 _64977).
Proof. exact (MK_COMB (@lem5054954) (@lem5054953 A _64976 _64977)). Qed.
Lemma lem5054957 (a : Prop) : (term120 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5054958 {A : Type'} (k : A -> Prop) (_64976 : A) : (term263 A k _64976) = (k _64976).
Proof. exact (@lem5054957 (k _64976)). Qed.
Lemma lem5054959 {A : Type'} (_64977 : A) (k : A -> Prop) (_64976 : A) : (term341 A _64977 k _64976) = (term344 A _64977 k _64976).
Proof. exact (MK_COMB (@lem5054955 A _64976 _64977) (@lem5054958 A k _64976)). Qed.
Lemma lem5054960 {A : Type'} (_64977 : A) (k : A -> Prop) (_64976 : A) : (term340 A _64977 k _64976) = (term344 A _64977 k _64976).
Proof. exact (TRANS (@lem5054950 A _64977 k _64976) (@lem5054959 A _64977 k _64976)). Qed.
Lemma lem5054961 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5054962 {A : Type'} (_64977 : A) (k : A -> Prop) (_64976 : A) : (term345 A _64977 k _64976) = (term346 A _64977 k _64976).
Proof. exact (MK_COMB (@lem5054961) (@lem5054960 A _64977 k _64976)). Qed.
Lemma lem5054963 {A : Type'} (k : A -> Prop) (_64977 : A) : (k _64977) = (k _64977).
Proof. exact (eq_refl (k _64977)). Qed.
Lemma lem5054964 {A : Type'} (_64976 : A) (k : A -> Prop) (_64977 : A) : (term337 A _64976 k _64977) = (term347 A _64976 k _64977).
Proof. exact (MK_COMB (@lem5054962 A _64977 k _64976) (@lem5054963 A k _64977)). Qed.
Lemma lem5054965 {A : Type'} (_64976 : A) (k : A -> Prop) (_64977 : A) : (term330 A _64977 k _64976) = (term347 A _64976 k _64977).
Proof. exact (TRANS (@lem5054947 A _64976 k _64977) (@lem5054964 A _64976 k _64977)). Qed.
Lemma lem5054967 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x'' : A) (k : A -> Prop) (x' : A) (h1 : term430 A B k u s f) (h2 : term631 A B s f x'' k x') : term344 A x' k x''.
Proof. exact (conj (@lem5054850 A B u s f x'' k x' h1 h2) (@lem5054857 A B s f x'' k x' h2)). Qed.
Lemma lem5054969 {A : Type'} (_64976 : A) (k : A -> Prop) (_64977 : A) : term347 A _64976 k _64977.
Proof. exact (EQ_MP (@lem5054965 A _64976 k _64977) (@lem5054944 A _64977 k _64976)). Qed.
Lemma lem5054970 {A : Type'} (_64976 : A) (k : A -> Prop) (_64977 : A) : term347 A _64976 k _64977.
Proof. exact (@lem5054969 A _64976 k _64977). Qed.
Lemma lem5054971 {A : Type'} (x'' : A) (k : A -> Prop) (x' : A) : term347 A x'' k x'.
Proof. exact (@lem5054970 A x'' k x'). Qed.
Lemma lem5054974 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x'' : A) (k : A -> Prop) (x' : A) (h1 : term430 A B k u s f) (h2 : term631 A B s f x'' k x') : k x'.
Proof. exact (@lem5054971 A x'' k x' (@lem5054967 A B u s f x'' k x' h1 h2)). Qed.
Lemma lem5054975 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x'' : A) (k : A -> Prop) (x' : A) (h1 : term430 A B k u s f) (h2 : term631 A B s f x'' k x') : term246 A k x'.
Proof. exact (fun h0 : term240 A k x' => @lem5054974 A B u s f x'' k x' h1 h2). Qed.
Lemma lem5054977 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5054978 {A : Type'} (k : A -> Prop) (x' : A) : (term246 A k x') = (k x').
Proof. exact (@lem5054977 (k x')). Qed.
Lemma lem5054979 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x'' : A) (k : A -> Prop) (x' : A) (h1 : term430 A B k u s f) (h2 : term631 A B s f x'' k x') : k x'.
Proof. exact (EQ_MP (@lem5054978 A k x') (@lem5054975 A B u s f x'' k x' h1 h2)). Qed.
Lemma lem5054982 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5054984 {A : Type'} (k : A -> Prop) (x' : A) : (term240 A k x') = (term248 A k x').
Proof. exact (@lem5054982 (k x')). Qed.
Lemma lem5054987 {A B : Type'} (s : A -> Prop) (f : A -> B) (x'' : A) (k : A -> Prop) (x' : A) (h1 : term631 A B s f x'' k x') : term248 A k x'.
Proof. exact (EQ_MP (@lem5054984 A k x') (@lem5053966 A B s f x'' k x' h1)). Qed.
Lemma lem5054990 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x'' : A) (k : A -> Prop) (x' : A) (h1 : term430 A B k u s f) (h2 : term631 A B s f x'' k x') : False.
Proof. exact (@lem5054987 A B s f x'' k x' h2 (@lem5054979 A B u s f x'' k x' h1 h2)). Qed.
Lemma lem5054991 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x'' : A) (k : A -> Prop) (x' : A) (h1 : term430 A B k u s f) (h2 : term631 A B s f x'' k x') : term249.
Proof. exact (fun h0 : ~ False => @lem5054990 A B u s f x'' k x' h1 h2). Qed.
Lemma lem5054993 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5054994 : term249 = False.
Proof. exact (@lem5054993 False). Qed.
Lemma lem5054995 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (x'' : A) (k : A -> Prop) (x' : A) (h1 : term430 A B k u s f) (h2 : term631 A B s f x'' k x') : False.
Proof. exact (EQ_MP (@lem5054994) (@lem5054991 A B u s f x'' k x' h1 h2)). Qed.
Lemma lem5055045 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x' : A) (h1 : term546 A B s f k x') : k x'.
Proof. exact (proj2 (@lem5053404 A B s f k x' h1)). Qed.
Lemma lem5055046 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x' : A) (h1 : term546 A B s f k x') : term246 A k x'.
Proof. exact (fun h0 : term240 A k x' => @lem5055045 A B s f k x' h1). Qed.
Lemma lem5055048 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5055049 {A : Type'} (k : A -> Prop) (x' : A) : (term246 A k x') = (k x').
Proof. exact (@lem5055048 (k x')). Qed.
Lemma lem5055050 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x' : A) (h1 : term546 A B s f k x') : k x'.
Proof. exact (EQ_MP (@lem5055049 A k x') (@lem5055046 A B s f k x' h1)). Qed.
Lemma lem5055056 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5055057 {A : Type'} (s : A -> Prop) (k : A -> Prop) (_64943 : A) : (term150 A k s _64943) = (term259 A s k _64943).
Proof. exact (@lem5055056 (s _64943) (term240 A k _64943)). Qed.
Lemma lem5055063 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5055064 {A : Type'} (s : A -> Prop) (k : A -> Prop) (_64943 : A) : (term260 A k s _64943) = (term261 A s k _64943).
Proof. exact (MK_COMB (@lem5055063) (@lem5055057 A s k _64943)). Qed.
Lemma lem5055070 {A : Type'} (s : A -> Prop) (k : A -> Prop) (_64943 : A) : (term259 A s k _64943) = (term259 A s k _64943).
Proof. exact (eq_refl (term259 A s k _64943)). Qed.
Lemma lem5055071 {A : Type'} (s : A -> Prop) (k : A -> Prop) (_64943 : A) : ((term150 A k s _64943) = (term259 A s k _64943)) = ((term259 A s k _64943) = (term259 A s k _64943)).
Proof. exact (MK_COMB (@lem5055064 A s k _64943) (@lem5055070 A s k _64943)). Qed.
Lemma lem5055073 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5055074 (x : Prop) : (x = x) = True.
Proof. exact (@lem5055073 Prop x). Qed.
Lemma lem5055075 {A : Type'} (s : A -> Prop) (k : A -> Prop) (_64943 : A) : ((term259 A s k _64943) = (term259 A s k _64943)) = True.
Proof. exact (@lem5055074 (term259 A s k _64943)). Qed.
Lemma lem5055076 {A : Type'} (s : A -> Prop) (k : A -> Prop) (_64943 : A) : ((term150 A k s _64943) = (term259 A s k _64943)) = True.
Proof. exact (TRANS (@lem5055071 A s k _64943) (@lem5055075 A s k _64943)). Qed.
Lemma lem5055077 {A : Type'} (s : A -> Prop) (k : A -> Prop) (_64943 : A) : True = ((term150 A k s _64943) = (term259 A s k _64943)).
Proof. exact (SYM (@lem5055076 A s k _64943)). Qed.
Lemma lem5055078 {A : Type'} (s : A -> Prop) (k : A -> Prop) (_64943 : A) : (term150 A k s _64943) = (term259 A s k _64943).
Proof. exact (EQ_MP (@lem5055077 A s k _64943) (@lem0)). Qed.
Lemma lem5055079 {A B : Type'} (_64943 : A) (k : A -> Prop) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term430 A B k u s f) : term259 A s k _64943.
Proof. exact (EQ_MP (@lem5055078 A s k _64943) (@lem5053978 A B _64943 k u s f h1)). Qed.
Lemma lem5055081 (b : Prop) (a : Prop) : (a \/ b) = (term252 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5055082 {A : Type'} (k : A -> Prop) (s : A -> Prop) (_64943 : A) : (term259 A s k _64943) = (term262 A k s _64943).
Proof. exact (@lem5055081 (term240 A k _64943) (s _64943)). Qed.
Lemma lem5055084 (a : Prop) : (term120 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5055085 {A : Type'} (k : A -> Prop) (_64943 : A) : (term263 A k _64943) = (k _64943).
Proof. exact (@lem5055084 (k _64943)). Qed.
Lemma lem5055086 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5055087 {A : Type'} (k : A -> Prop) (_64943 : A) : (term264 A k _64943) = (term58 A k _64943).
Proof. exact (MK_COMB (@lem5055086) (@lem5055085 A k _64943)). Qed.
Lemma lem5055088 {A : Type'} (s : A -> Prop) (_64943 : A) : (s _64943) = (s _64943).
Proof. exact (eq_refl (s _64943)). Qed.
Lemma lem5055089 {A : Type'} (k : A -> Prop) (s : A -> Prop) (_64943 : A) : (term262 A k s _64943) = (term74 A k s _64943).
Proof. exact (MK_COMB (@lem5055087 A k _64943) (@lem5055088 A s _64943)). Qed.
Lemma lem5055090 {A : Type'} (k : A -> Prop) (s : A -> Prop) (_64943 : A) : (term259 A s k _64943) = (term74 A k s _64943).
Proof. exact (TRANS (@lem5055082 A k s _64943) (@lem5055089 A k s _64943)). Qed.
Lemma lem5055093 {A B : Type'} (_64943 : A) (k : A -> Prop) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term430 A B k u s f) : term74 A k s _64943.
Proof. exact (EQ_MP (@lem5055090 A k s _64943) (@lem5055079 A B _64943 k u s f h1)). Qed.
Lemma lem5055094 {A B : Type'} (_64943 : A) (k : A -> Prop) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term430 A B k u s f) : term74 A k s _64943.
Proof. exact (@lem5055093 A B _64943 k u s f h1). Qed.
Lemma lem5055095 {A B : Type'} (x' : A) (k : A -> Prop) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term430 A B k u s f) : term74 A k s x'.
Proof. exact (@lem5055094 A B x' k u s f h1). Qed.
Lemma lem5055098 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x' : A) (h1 : term430 A B k u s f) (h2 : term546 A B s f k x') : s x'.
Proof. exact (@lem5055095 A B x' k u s f h1 (@lem5055050 A B s f k x' h2)). Qed.
Lemma lem5055099 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x' : A) (h1 : term430 A B k u s f) (h2 : term546 A B s f k x') : term246 A s x'.
Proof. exact (fun h0 : term240 A s x' => @lem5055098 A B u s f k x' h1 h2). Qed.
Lemma lem5055101 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5055102 {A : Type'} (s : A -> Prop) (x' : A) : (term246 A s x') = (s x').
Proof. exact (@lem5055101 (s x')). Qed.
Lemma lem5055103 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x' : A) (h1 : term430 A B k u s f) (h2 : term546 A B s f k x') : s x'.
Proof. exact (EQ_MP (@lem5055102 A s x') (@lem5055099 A B u s f k x' h1 h2)). Qed.
Lemma lem5055106 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5055108 {A : Type'} (s : A -> Prop) (x' : A) : (term240 A s x') = (term248 A s x').
Proof. exact (@lem5055106 (s x')). Qed.
Lemma lem5055111 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term240 A s x') : term248 A s x'.
Proof. exact (EQ_MP (@lem5055108 A s x') (@lem5054012 A s x' h1)). Qed.
Lemma lem5055114 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x' : A) (h1 : term240 A s x') (h2 : term430 A B k u s f) (h3 : term546 A B s f k x') : False.
Proof. exact (@lem5055111 A s x' h1 (@lem5055103 A B u s f k x' h2 h3)). Qed.
Lemma lem5055115 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x' : A) (h1 : term240 A s x') (h2 : term430 A B k u s f) (h3 : term546 A B s f k x') : term249.
Proof. exact (fun h0 : ~ False => @lem5055114 A B u s f k x' h1 h2 h3). Qed.
Lemma lem5055117 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5055118 : term249 = False.
Proof. exact (@lem5055117 False). Qed.
Lemma lem5055119 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x' : A) (h1 : term240 A s x') (h2 : term430 A B k u s f) (h3 : term546 A B s f k x') : False.
Proof. exact (EQ_MP (@lem5055118) (@lem5055115 A B u s f k x' h1 h2 h3)). Qed.
Lemma lem5055169 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem5055170 {B : Type'} (x : B) : x = x.
Proof. exact (@lem5055169 B x). Qed.
Lemma lem5055171 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (f x').
Proof. exact (@lem5055170 B (f x')). Qed.
Lemma lem5055172 {A B : Type'} (f : A -> B) (x' : A) : term752 A B f x'.
Proof. exact (fun h0 : term753 A B f x' => @lem5055171 A B f x'). Qed.
Lemma lem5055174 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5055175 {A B : Type'} (f : A -> B) (x' : A) : (term752 A B f x') = ((f x') = (f x')).
Proof. exact (@lem5055174 ((f x') = (f x'))). Qed.
Lemma lem5055176 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (f x').
Proof. exact (EQ_MP (@lem5055175 A B f x') (@lem5055172 A B f x')). Qed.
Lemma lem5055178 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x' : A) (h1 : term546 A B s f k x') : k x'.
Proof. exact (proj2 (@lem5053404 A B s f k x' h1)). Qed.
Lemma lem5055179 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x' : A) (h1 : term546 A B s f k x') : term246 A k x'.
Proof. exact (fun h0 : term240 A k x' => @lem5055178 A B s f k x' h1). Qed.
Lemma lem5055181 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5055182 {A : Type'} (k : A -> Prop) (x' : A) : (term246 A k x') = (k x').
Proof. exact (@lem5055181 (k x')). Qed.
Lemma lem5055183 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x' : A) (h1 : term546 A B s f k x') : k x'.
Proof. exact (EQ_MP (@lem5055182 A k x') (@lem5055179 A B s f k x' h1)). Qed.
Lemma lem5055185 (a : Prop) (b : Prop) : (term788 a b) = (term789 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem5055186 {A B : Type'} (x' : A) (f : A -> B) (k : A -> Prop) (_64953 : A) : (term532 A B x' f k _64953) = (term531 A B x' f k _64953).
Proof. exact (@lem5055185 ((f x') = (f _64953)) (k _64953)). Qed.
Lemma lem5055188 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5055189 {A B : Type'} (x' : A) (f : A -> B) (k : A -> Prop) (_64953 : A) : (term531 A B x' f k _64953) = (term790 A B x' f k _64953).
Proof. exact (@lem5055188 (term453 A B x' f k _64953)). Qed.
Lemma lem5055190 {A B : Type'} (x' : A) (f : A -> B) (k : A -> Prop) (_64953 : A) : (term532 A B x' f k _64953) = (term790 A B x' f k _64953).
Proof. exact (TRANS (@lem5055186 A B x' f k _64953) (@lem5055189 A B x' f k _64953)). Qed.
Lemma lem5055192 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x' : A) (h1 : term546 A B s f k x') : term771 A B f k x'.
Proof. exact (conj (@lem5055176 A B f x') (@lem5055183 A B s f k x' h1)). Qed.
Lemma lem5055194 {A B : Type'} (_64953 : A) (x' : A) (f : A -> B) (k : A -> Prop) (h1 : term539 A B x' f k) : term790 A B x' f k _64953.
Proof. exact (EQ_MP (@lem5055190 A B x' f k _64953) (@lem5054056 A B _64953 x' f k h1)). Qed.
Lemma lem5055195 {A B : Type'} (_64953 : A) (x' : A) (f : A -> B) (k : A -> Prop) (h1 : term539 A B x' f k) : term790 A B x' f k _64953.
Proof. exact (@lem5055194 A B _64953 x' f k h1). Qed.
Lemma lem5055196 {A B : Type'} (x' : A) (f : A -> B) (k : A -> Prop) (h1 : term539 A B x' f k) : term791 A B f k x'.
Proof. exact (@lem5055195 A B x' x' f k h1). Qed.
Lemma lem5055199 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x' : A) (h1 : term539 A B x' f k) (h2 : term546 A B s f k x') : False.
Proof. exact (@lem5055196 A B x' f k h1 (@lem5055192 A B s f k x' h2)). Qed.
Lemma lem5055200 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x' : A) (h1 : term539 A B x' f k) (h2 : term546 A B s f k x') : term249.
Proof. exact (fun h0 : ~ False => @lem5055199 A B s f k x' h1 h2). Qed.
Lemma lem5055202 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5055203 : term249 = False.
Proof. exact (@lem5055202 False). Qed.
Lemma lem5055204 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x' : A) (h1 : term539 A B x' f k) (h2 : term546 A B s f k x') : False.
Proof. exact (EQ_MP (@lem5055203) (@lem5055200 A B s f k x' h1 h2)). Qed.
Lemma lem5055205 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x' : A) (u : B -> Prop) (x : B) (h1 : term430 A B k u s f) (h2 : term599 A B f k x' u x) : False.
Proof. exact (EQ_MP (@lem5054406) (@lem5054403 A B s f k x' u x h1 h2)). Qed.
Lemma lem5055206 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x' : A) (h1 : term240 A s x') (h2 : term430 A B k u s f) (h3 : term546 A B s f k x') : (term240 A s x') = False.
Proof. exact (prop_ext (fun h4 : term240 A s x' => @lem5055119 A B u s f k x' h1 h2 h3) (fun h4 : False => @lem5054012 A s x' h1)). Qed.
Lemma lem5055207 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x' : A) (h1 : term240 A s x') (h2 : term430 A B k u s f) (h3 : term546 A B s f k x') : False.
Proof. exact (EQ_MP (@lem5055206 A B u s f k x' h1 h2 h3) (@lem5054012 A s x' h1)). Qed.
Lemma lem5055208 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x' : A) (h1 : term240 A s x') (h2 : term430 A B k u s f) (h3 : term546 A B s f k x') : (term240 A s x') = False.
Proof. exact (prop_ext (fun h4 : term240 A s x' => @lem5055207 A B u s f k x' h1 h2 h3) (fun h4 : False => @lem5053717 A s x' h1)). Qed.
Lemma lem5055209 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x' : A) (h1 : term240 A s x') (h2 : term430 A B k u s f) (h3 : term546 A B s f k x') : False.
Proof. exact (EQ_MP (@lem5055208 A B u s f k x' h1 h2 h3) (@lem5053717 A s x' h1)). Qed.
Lemma lem5055210 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x' : A) (h1 : term539 A B x' f k) (h2 : term546 A B s f k x') : (term539 A B x' f k) = False.
Proof. exact (prop_ext (fun h3 : term539 A B x' f k => @lem5055204 A B s f k x' h1 h2) (fun h3 : False => @lem5053823 A B x' f k h1)). Qed.
Lemma lem5055211 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x' : A) (h1 : term539 A B x' f k) (h2 : term546 A B s f k x') : False.
Proof. exact (EQ_MP (@lem5055210 A B s f k x' h1 h2) (@lem5053823 A B x' f k h1)). Qed.
Lemma lem5055212 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x' : A) (h1 : term240 A s x') (h2 : term430 A B k u s f) (h3 : term546 A B s f k x') : (term240 A s x') = False.
Proof. exact (prop_ext (fun h4 : term240 A s x' => @lem5055209 A B u s f k x' h1 h2 h3) (fun h4 : False => @lem5053717 A s x' h1)). Qed.
Lemma lem5055213 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x' : A) (h1 : term240 A s x') (h2 : term430 A B k u s f) (h3 : term546 A B s f k x') : False.
Proof. exact (EQ_MP (@lem5055212 A B u s f k x' h1 h2 h3) (@lem5053717 A s x' h1)). Qed.
Lemma lem5055214 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x' : A) (h1 : term430 A B k u s f) (h2 : term546 A B s f k x') : False.
Proof. exact (or_elim (@lem5053412 A B s f k x' h2) (fun h0 : term240 A s x' => @lem5055213 A B u s f k x' h0 h1 h2) (fun h0 : term539 A B x' f k => @lem5055211 A B s f k x' h0 h2)). Qed.
Lemma lem5055215 {A B : Type'} (u : B -> Prop) (x'' : A) (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x' : A) (h1 : term430 A B k u s f) (h2 : term665 A B x'' s f k x') : False.
Proof. exact (or_elim (@lem5053398 A B x'' s f k x' h2) (fun h0 : term631 A B s f x'' k x' => @lem5054995 A B u s f x'' k x' h1 h0) (fun h0 : term546 A B s f k x' => @lem5055214 A B u s f k x' h1 h0)). Qed.
Lemma lem5055216 {A B : Type'} (u : B -> Prop) (x : B) (x'' : A) (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x' : A) (h1 : term430 A B k u s f) (h2 : term713 A B u x x'' s f k x') : False.
Proof. exact (or_elim (@lem5053392 A B u x x'' s f k x' h2) (fun h0 : term599 A B f k x' u x => @lem5055205 A B s f k x' u x h1 h0) (fun h0 : term665 A B x'' s f k x' => @lem5055215 A B u x'' s f k x' h1 h0)). Qed.
Lemma lem5055217 {A B : Type'} (u : B -> Prop) (x : B) (x'' : A) (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x' : A) (h1 : term430 A B k u s f) (h2 : term713 A B u x x'' s f k x') : (term713 A B u x x'' s f k x') = False.
Proof. exact (prop_ext (fun h3 : term713 A B u x x'' s f k x' => @lem5055216 A B u x x'' s f k x' h1 h2) (fun h3 : False => @lem5053392 A B u x x'' s f k x' h2)). Qed.
Lemma lem5055218 {A B : Type'} (u : B -> Prop) (x : B) (x'' : A) (s : A -> Prop) (f : A -> B) (k : A -> Prop) (x' : A) (h1 : term430 A B k u s f) (h2 : term713 A B u x x'' s f k x') : False.
Proof. exact (EQ_MP (@lem5055217 A B u x x'' s f k x' h1 h2) (@lem5053392 A B u x x'' s f k x' h2)). Qed.
Lemma lem5055219 {A B : Type'} (x : B) (x' : A) (k : A -> Prop) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term716 A B u x s f k x') (h2 : term430 A B k u s f) : False.
Proof. exact (ex_elim (@lem5053207 A B u x s f k x' h1) (fun x'' : A => fun h0 : term715 A B u x s f k x' x'' => @lem5055218 A B u x x'' s f k x' h2 h0)). Qed.
Lemma lem5055220 {A B : Type'} (x : B) (k : A -> Prop) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term718 A B u x s f k) (h2 : term430 A B k u s f) : False.
Proof. exact (ex_elim (@lem5053206 A B u x s f k h1) (fun x' : A => fun h0 : term717 A B u x s f k x' => @lem5055219 A B x x' k u s f h0 h2)). Qed.
Lemma lem5055221 {A B : Type'} (k : A -> Prop) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term487 A B u s f k) (h2 : term430 A B k u s f) : False.
Proof. exact (ex_elim (@lem5053205 A B u s f k h1) (fun x : B => fun h0 : term719 A B u s f k x => @lem5055220 A B x k u s f h0 h2)). Qed.
Lemma lem5055222 {A B : Type'} (k : A -> Prop) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term487 A B u s f k) (h2 : term430 A B k u s f) : (term487 A B u s f k) = False.
Proof. exact (prop_ext (fun h3 : term487 A B u s f k => @lem5055221 A B k u s f h1 h2) (fun h3 : False => @lem5052386 A B u s f k h1)). Qed.
Lemma lem5055223 {A B : Type'} (k : A -> Prop) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term487 A B u s f k) (h2 : term430 A B k u s f) : False.
Proof. exact (EQ_MP (@lem5055222 A B k u s f h1 h2) (@lem5052386 A B u s f k h1)). Qed.
Lemma lem5055224 {A B : Type'} (k : A -> Prop) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term430 A B k u s f) : term486 A B u s f k.
Proof. exact (fun h0 : term487 A B u s f k => @lem5055223 A B k u s f h0 h1). Qed.
Lemma lem5055225 {A B : Type'} (k : A -> Prop) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term430 A B k u s f) : term462 A B u s f k.
Proof. exact (EQ_MP (@lem5052385 A B u s f k) (@lem5055224 A B k u s f h1)). Qed.
Lemma lem5055226 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) : term463 A B u s f k.
Proof. exact (fun h0 : term430 A B k u s f => @lem5055225 A B k u s f h0). Qed.
Lemma lem5055231 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) : term473 A B s f k.
Proof. exact (fun u : B -> Prop => @lem5055226 A B u s f k). Qed.
Lemma lem5055236 {A B : Type'} (f : A -> B) (k : A -> Prop) : term477 A B f k.
Proof. exact (fun s : A -> Prop => @lem5055231 A B s f k). Qed.
Lemma lem5055241 {A B : Type'} (k : A -> Prop) : term481 A B k.
Proof. exact (fun f : A -> B => @lem5055236 A B f k). Qed.
Lemma lem5055246 {A B : Type'} : term485 A B.
Proof. exact (fun k : A -> Prop => @lem5055241 A B k). Qed.
Lemma lem5055247 {A B : Type'} : term484 A B.
Proof. exact (EQ_MP (@lem5052380 A B) (@lem5055246 A B)). Qed.
Lemma lem5055248 {A B : Type'} (k : A -> Prop) : term792 A B k.
Proof. exact (@lem5055247 A B k). Qed.
Lemma lem5055249 {A B : Type'} (k : A -> Prop) : (term792 A B k) = (term480 A B k).
Proof. exact (eq_refl (term792 A B k)). Qed.
Lemma lem5055250 {A B : Type'} (k : A -> Prop) : term480 A B k.
Proof. exact (EQ_MP (@lem5055249 A B k) (@lem5055248 A B k)). Qed.
Lemma lem5055251 {A B : Type'} (k : A -> Prop) (f : A -> B) : term793 A B k f.
Proof. exact (@lem5055250 A B k f). Qed.
Lemma lem5055252 {A B : Type'} (f : A -> B) (k : A -> Prop) : (term793 A B k f) = (term476 A B f k).
Proof. exact (eq_refl (term793 A B k f)). Qed.
Lemma lem5055253 {A B : Type'} (f : A -> B) (k : A -> Prop) : term476 A B f k.
Proof. exact (EQ_MP (@lem5055252 A B f k) (@lem5055251 A B k f)). Qed.
Lemma lem5055254 {A B : Type'} (f : A -> B) (k : A -> Prop) (s : A -> Prop) : term794 A B f k s.
Proof. exact (@lem5055253 A B f k s). Qed.
Lemma lem5055255 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term794 A B f k s) = (term472 A B s f k).
Proof. exact (eq_refl (term794 A B f k s)). Qed.
Lemma lem5055256 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) : term472 A B s f k.
Proof. exact (EQ_MP (@lem5055255 A B s f k) (@lem5055254 A B f k s)). Qed.
Lemma lem5055257 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> Prop) (u : B -> Prop) : term795 A B s f k u.
Proof. exact (@lem5055256 A B s f k u). Qed.
Lemma lem5055258 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) : (term795 A B s f k u) = (term464 A B u s f k).
Proof. exact (eq_refl (term795 A B s f k u)). Qed.
Lemma lem5055259 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) : term464 A B u s f k.
Proof. exact (EQ_MP (@lem5055258 A B u s f k) (@lem5055257 A B s f k u)). Qed.
Lemma lem5055261 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) : term464 A B u s f k.
Proof. exact (@lem5051967 A B u s f k (@lem5055259 A B u s f k)). Qed.
Lemma lem5055262 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) (h1 : term465 A B u s f k) : False.
Proof. exact (@lem5055261 A B u s f k (@lem5051951 A B u s f k h1)). Qed.
Lemma lem5055263 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) (h1 : term465 A B u s f k) : (term465 A B u s f k) = False.
Proof. exact (prop_ext (fun h2 : term465 A B u s f k => @lem5055262 A B u s f k h1) (fun h2 : False => @lem5051951 A B u s f k h1)). Qed.
Lemma lem5055264 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) (h1 : term465 A B u s f k) : False.
Proof. exact (EQ_MP (@lem5055263 A B u s f k h1) (@lem5051951 A B u s f k h1)). Qed.
Lemma lem5055265 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) : term464 A B u s f k.
Proof. exact (fun h0 : term465 A B u s f k => @lem5055264 A B u s f k h0). Qed.
Lemma lem5055266 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) : term463 A B u s f k.
Proof. exact (EQ_MP (@lem5051950 A B u s f k) (@lem5055265 A B u s f k)). Qed.
Lemma lem5055267 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) : term404 A B u s f k.
Proof. exact (EQ_MP (@lem5051946 A B u s f k) (@lem5055266 A B u s f k)). Qed.
Lemma lem5055268 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (k : A -> Prop) : term403 A B u s f k.
Proof. exact (EQ_MP (@lem5051650 A B u s f k) (@lem5055267 A B u s f k)). Qed.
Lemma lem5055269 {A B : Type'} (u : B -> Prop) (f : A -> B) (k : A -> Prop) (s : A -> Prop) (h1 : term10 A B u s f) (h2 : @SUBSET A k s) : term401 A B u s f k.
Proof. exact (@lem5055268 A B u s f k (@lem5051548 A B u f k s h1 h2)). Qed.
Lemma lem5055270 {A B : Type'} (u : B -> Prop) (f : A -> B) (k : A -> Prop) (s : A -> Prop) (h1 : term10 A B u s f) (h2 : @SUBSET A k s) : term796 A B u s f k.
Proof. exact (ex_intro (term797 A B u s f k) (@IMAGE A B f k) (@lem5055269 A B u f k s h1 h2)). Qed.
Lemma lem5055271 {A B : Type'} (u : B -> Prop) (f : A -> B) (k : A -> Prop) (s : A -> Prop) (h1 : term10 A B u s f) (h2 : @SUBSET A k s) : (@SUBSET A k s) = (term796 A B u s f k).
Proof. exact (prop_ext (fun h3 : @SUBSET A k s => @lem5055270 A B u f k s h1 h2) (fun h3 : term796 A B u s f k => @lem5051537 A k s h2)). Qed.
Lemma lem5055272 {A B : Type'} (u : B -> Prop) (f : A -> B) (k : A -> Prop) (s : A -> Prop) (h1 : term10 A B u s f) (h2 : @SUBSET A k s) : term796 A B u s f k.
Proof. exact (EQ_MP (@lem5055271 A B u f k s h1 h2) (@lem5051537 A k s h2)). Qed.
Lemma lem5055273 {A B : Type'} (k : A -> Prop) (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term10 A B u s f) : term798 A B u s f k.
Proof. exact (fun h0 : @SUBSET A k s => @lem5055272 A B u f k s h1 h0). Qed.
Lemma lem5055278 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term10 A B u s f) : term9 A B u s f.
Proof. exact (fun k : A -> Prop => @lem5055273 A B k u s f h1). Qed.
Lemma lem5055279 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) : term799 A B u s f.
Proof. exact (fun h0 : term10 A B u s f => @lem5055278 A B u s f h0). Qed.
Lemma lem5055280 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) : term800 A B u s f.
Proof. exact (fun h0 : term9 A B u s f => @lem5051536 A B u s f h0). Qed.
Lemma lem5055281 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) : term801 A B u s f.
Proof. exact (conj (@lem5055280 A B u s f) (@lem5055279 A B u s f)). Qed.
Lemma lem5055282 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) : (term801 A B u s f) = ((term9 A B u s f) = (term10 A B u s f)).
Proof. exact (@lem32 (term9 A B u s f) (term10 A B u s f)). Qed.
Lemma lem5055283 {A B : Type'} (u : B -> Prop) (s : A -> Prop) (f : A -> B) : (term9 A B u s f) = (term10 A B u s f).
Proof. exact (EQ_MP (@lem5055282 A B u s f) (@lem5055281 A B u s f)). Qed.
Lemma lem5055288 {A B : Type'} (s : A -> Prop) (f : A -> B) : term802 A B s f.
Proof. exact (fun u : B -> Prop => @lem5055283 A B u s f). Qed.
Lemma lem5055293 {A B : Type'} (f : A -> B) : term803 A B f.
Proof. exact (fun s : A -> Prop => @lem5055288 A B s f). Qed.
Lemma lem5055298 {A B : Type'} : term804 A B.
Proof. exact (fun f : A -> B => @lem5055293 A B f). Qed.
