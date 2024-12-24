Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import IMAGE_DIFF_INJ_ALT_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17646_spec.
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
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211656_spec.
Require Import thm3211657_spec.
Require Import thm3211701_spec.
Require Import thm3211702_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3376779 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem3376780 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem3376781 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem3376780 t1) (@lem3376779 t1)). Qed.
Lemma lem3376782 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem3376781 t1 t2). Qed.
Lemma lem3376783 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem3376784 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem3376783 t1 t2) (@lem3376782 t1 t2)). Qed.
Lemma lem3376785 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem3376784 t1 t2 t3). Qed.
Lemma lem3376786 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem3376787 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem3376786 t1 t2 t3) (@lem3376785 t1 t2 t3)). Qed.
Lemma lem3376788 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem3376787 t1 t2 t3)). Qed.
Lemma lem3376828 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term7 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3376829 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term7 A s t).
Proof. exact (@lem3376828 A s t). Qed.
Lemma lem3376830 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (@SUBSET A t s) = (term7 A t s).
Proof. exact (@lem3376829 A t s). Qed.
Lemma lem3376837 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term8 A B s f) = (term8 A B s f).
Proof. exact (eq_refl (term8 A B s f)). Qed.
Lemma lem3376838 {A B : Type'} (f : A -> B) (t : A -> Prop) (s : A -> Prop) : (term9 A B f t s) = (term10 A B f t s).
Proof. exact (MK_COMB (@lem3376837 A B s f) (@lem3376830 A t s)). Qed.
Lemma lem3376841 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3376842 {A B : Type'} (f : A -> B) (t : A -> Prop) (s : A -> Prop) : (term11 A B f t s) = (term12 A B f t s).
Proof. exact (MK_COMB (@lem3376841) (@lem3376838 A B f t s)). Qed.
Lemma lem3376846 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term13 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3376847 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (s = t) = (term13 B s t).
Proof. exact (@lem3376846 B s t). Qed.
Lemma lem3376848 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : ((term14 A B f s t) = (term15 A B s f t)) = (term16 A B s f t).
Proof. exact (@lem3376847 B (term14 A B f s t) (term15 A B s f t)). Qed.
Lemma lem3376857 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term17 A B s f t) = (term18 A B s f t).
Proof. exact (MK_COMB (@lem3376842 A B f t s) (@lem3376848 A B s f t)). Qed.
Lemma lem3376860 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term19 A B s f) = (term20 A B s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3376857 A B s f t)). Qed.
Lemma lem3376861 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3376862 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term21 A B s f) = (term22 A B s f).
Proof. exact (MK_COMB (@lem3376861 A) (@lem3376860 A B s f)). Qed.
Lemma lem3376867 {A B : Type'} (f : A -> B) : (term23 A B f) = (term24 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3376862 A B s f)). Qed.
Lemma lem3376868 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3376869 {A B : Type'} (f : A -> B) : (term25 A B f) = (term26 A B f).
Proof. exact (MK_COMB (@lem3376868 A) (@lem3376867 A B f)). Qed.
Lemma lem3376874 {A B : Type'} : (term27 A B) = (term28 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3376869 A B f)). Qed.
Lemma lem3376875 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3376876 {A B : Type'} : (term29 A B) = (term30 A B).
Proof. exact (MK_COMB (@lem3376875 A B) (@lem3376874 A B)). Qed.
Lemma lem3376881 {A B : Type'} : (term30 A B) = (term29 A B).
Proof. exact (SYM (@lem3376876 A B)). Qed.
Lemma lem3376911 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3376912 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3376911 A P x). Qed.
Lemma lem3376913 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3376912 A s x). Qed.
Lemma lem3376914 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3376915 {A : Type'} (s : A -> Prop) (x : A) : (term31 A x s) = (term32 A s x).
Proof. exact (MK_COMB (@lem3376914) (@lem3376913 A s x)). Qed.
Lemma lem3376919 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3376920 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3376919 A P x). Qed.
Lemma lem3376921 {A : Type'} (s : A -> Prop) (y : A) : (@IN A y s) = (s y).
Proof. exact (@lem3376920 A s y). Qed.
Lemma lem3376922 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3376923 {A : Type'} (s : A -> Prop) (y : A) : (term31 A y s) = (term32 A s y).
Proof. exact (MK_COMB (@lem3376922) (@lem3376921 A s y)). Qed.
Lemma lem3376926 {A B : Type'} (x : A) (f : A -> B) (y : A) : ((f x) = (f y)) = ((f x) = (f y)).
Proof. exact (eq_refl ((f x) = (f y))). Qed.
Lemma lem3376927 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term33 A B s x f y) = (term34 A B s x f y).
Proof. exact (MK_COMB (@lem3376923 A s y) (@lem3376926 A B x f y)). Qed.
Lemma lem3376930 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term35 A B s x f y) = (term36 A B s x f y).
Proof. exact (MK_COMB (@lem3376915 A s x) (@lem3376927 A B s x f y)). Qed.
Lemma lem3376933 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3376934 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term37 A B s x f y) = (term38 A B s x f y).
Proof. exact (MK_COMB (@lem3376933) (@lem3376930 A B s x f y)). Qed.
Lemma lem3376937 {A : Type'} (x : A) (y : A) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem3376938 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term39 A B s f x y) = (term40 A B s f x y).
Proof. exact (MK_COMB (@lem3376934 A B s x f y) (@lem3376937 A x y)). Qed.
Lemma lem3376941 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term41 A B s f x) = (term42 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem3376938 A B s f x y)). Qed.
Lemma lem3376942 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3376943 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term43 A B s f x) = (term44 A B s f x).
Proof. exact (MK_COMB (@lem3376942 A) (@lem3376941 A B s f x)). Qed.
Lemma lem3376948 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term45 A B s f) = (term46 A B s f).
Proof. exact (fun_ext (fun x : A => @lem3376943 A B s f x)). Qed.
Lemma lem3376949 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3376950 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term47 A B s f) = (term48 A B s f).
Proof. exact (MK_COMB (@lem3376949 A) (@lem3376948 A B s f)). Qed.
Lemma lem3376955 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3376956 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term8 A B s f) = (term49 A B s f).
Proof. exact (MK_COMB (@lem3376955) (@lem3376950 A B s f)). Qed.
Lemma lem3376964 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3376965 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3376964 A P x). Qed.
Lemma lem3376966 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3376965 A t x). Qed.
Lemma lem3376967 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3376968 {A : Type'} (t : A -> Prop) (x : A) : (term50 A x t) = (term51 A t x).
Proof. exact (MK_COMB (@lem3376967) (@lem3376966 A t x)). Qed.
Lemma lem3376970 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3376971 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3376970 A P x). Qed.
Lemma lem3376972 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3376971 A s x). Qed.
Lemma lem3376973 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term52 A t x s) = (term53 A t s x).
Proof. exact (MK_COMB (@lem3376968 A t x) (@lem3376972 A s x)). Qed.
Lemma lem3376976 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term54 A t s) = (term55 A t s).
Proof. exact (fun_ext (fun x : A => @lem3376973 A t s x)). Qed.
Lemma lem3376977 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3376978 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term7 A t s) = (term56 A t s).
Proof. exact (MK_COMB (@lem3376977 A) (@lem3376976 A t s)). Qed.
Lemma lem3376983 {A B : Type'} (f : A -> B) (t : A -> Prop) (s : A -> Prop) : (term10 A B f t s) = (term57 A B f t s).
Proof. exact (MK_COMB (@lem3376956 A B s f) (@lem3376978 A t s)). Qed.
Lemma lem3376986 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3376987 {A B : Type'} (f : A -> B) (t : A -> Prop) (s : A -> Prop) : (term12 A B f t s) = (term58 A B f t s).
Proof. exact (MK_COMB (@lem3376986) (@lem3376983 A B f t s)). Qed.
Lemma lem3376995 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term59 A B y f s) = (term60 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem3376996 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term59 A B y f s) = (term60 A B y f s).
Proof. exact (@lem3376995 A B y f s). Qed.
Lemma lem3376997 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term61 A B x f s t) = (term62 A B x f s t).
Proof. exact (@lem3376996 A B x f (@DIFF A s t)). Qed.
Lemma lem3377007 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term63 A x s t) = (term64 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem3377008 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term63 A x s t) = (term64 A s x t).
Proof. exact (@lem3377007 A s x t). Qed.
Lemma lem3377012 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3377013 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3377012 A P x). Qed.
Lemma lem3377014 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3377013 A s x). Qed.
Lemma lem3377015 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3377016 {A : Type'} (s : A -> Prop) (x : A) : (term31 A x s) = (term32 A s x).
Proof. exact (MK_COMB (@lem3377015) (@lem3377014 A s x)). Qed.
Lemma lem3377018 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3377019 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3377018 A P x). Qed.
Lemma lem3377020 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3377019 A t x). Qed.
Lemma lem3377021 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3377022 {A : Type'} (t : A -> Prop) (x : A) : (term65 A x t) = (term66 A t x).
Proof. exact (MK_COMB (@lem3377021) (@lem3377020 A t x)). Qed.
Lemma lem3377023 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term64 A s x t) = (term67 A s t x).
Proof. exact (MK_COMB (@lem3377016 A s x) (@lem3377022 A t x)). Qed.
Lemma lem3377026 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term63 A x s t) = (term67 A s t x).
Proof. exact (TRANS (@lem3377008 A s x t) (@lem3377023 A s t x)). Qed.
Lemma lem3377027 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term68 A B x f x') = (term68 A B x f x').
Proof. exact (eq_refl (term68 A B x f x')). Qed.
Lemma lem3377028 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term69 A B x f x' s t) = (term70 A B x f s t x').
Proof. exact (MK_COMB (@lem3377027 A B x f x') (@lem3377026 A s t x')). Qed.
Lemma lem3377031 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term71 A B x f s t) = (term72 A B x f s t).
Proof. exact (fun_ext (fun x' : A => @lem3377028 A B x f s t x')). Qed.
Lemma lem3377032 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3377033 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term62 A B x f s t) = (term73 A B x f s t).
Proof. exact (MK_COMB (@lem3377032 A) (@lem3377031 A B x f s t)). Qed.
Lemma lem3377038 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term61 A B x f s t) = (term73 A B x f s t).
Proof. exact (TRANS (@lem3376997 A B x f s t) (@lem3377033 A B x f s t)). Qed.
Lemma lem3377039 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3377040 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term74 A B x f s t) = (term75 A B x f s t).
Proof. exact (MK_COMB (@lem3377039) (@lem3377038 A B x f s t)). Qed.
Lemma lem3377042 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term63 A x s t) = (term64 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem3377043 {B : Type'} (s : B -> Prop) (x : B) (t : B -> Prop) : (term63 B x s t) = (term64 B s x t).
Proof. exact (@lem3377042 B s x t). Qed.
Lemma lem3377044 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term76 A B x s f t) = (term77 A B s x f t).
Proof. exact (@lem3377043 B (@IMAGE A B f s) x (@IMAGE A B f t)). Qed.
Lemma lem3377048 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term59 A B y f s) = (term60 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem3377049 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term59 A B y f s) = (term60 A B y f s).
Proof. exact (@lem3377048 A B y f s). Qed.
Lemma lem3377050 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term59 A B x f s) = (term60 A B x f s).
Proof. exact (@lem3377049 A B x f s). Qed.
Lemma lem3377060 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3377061 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3377060 A P x). Qed.
Lemma lem3377062 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3377061 A s x). Qed.
Lemma lem3377063 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term68 A B x f x') = (term68 A B x f x').
Proof. exact (eq_refl (term68 A B x f x')). Qed.
Lemma lem3377064 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term78 A B x f x' s) = (term79 A B x f s x').
Proof. exact (MK_COMB (@lem3377063 A B x f x') (@lem3377062 A s x')). Qed.
Lemma lem3377067 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term80 A B x f s) = (term81 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3377064 A B x f s x')). Qed.
Lemma lem3377068 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3377069 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term60 A B x f s) = (term82 A B x f s).
Proof. exact (MK_COMB (@lem3377068 A) (@lem3377067 A B x f s)). Qed.
Lemma lem3377074 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term59 A B x f s) = (term82 A B x f s).
Proof. exact (TRANS (@lem3377050 A B x f s) (@lem3377069 A B x f s)). Qed.
Lemma lem3377075 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3377076 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term83 A B x f s) = (term84 A B x f s).
Proof. exact (MK_COMB (@lem3377075) (@lem3377074 A B x f s)). Qed.
Lemma lem3377078 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term59 A B y f s) = (term60 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem3377079 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term59 A B y f s) = (term60 A B y f s).
Proof. exact (@lem3377078 A B y f s). Qed.
Lemma lem3377080 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term59 A B x f t) = (term60 A B x f t).
Proof. exact (@lem3377079 A B x f t). Qed.
Lemma lem3377090 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3377091 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3377090 A P x). Qed.
Lemma lem3377092 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3377091 A t x). Qed.
Lemma lem3377093 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term68 A B x f x') = (term68 A B x f x').
Proof. exact (eq_refl (term68 A B x f x')). Qed.
Lemma lem3377094 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term78 A B x f x' t) = (term79 A B x f t x').
Proof. exact (MK_COMB (@lem3377093 A B x f x') (@lem3377092 A t x')). Qed.
Lemma lem3377097 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term80 A B x f t) = (term81 A B x f t).
Proof. exact (fun_ext (fun x' : A => @lem3377094 A B x f t x')). Qed.
Lemma lem3377098 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3377099 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term60 A B x f t) = (term82 A B x f t).
Proof. exact (MK_COMB (@lem3377098 A) (@lem3377097 A B x f t)). Qed.
Lemma lem3377104 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term59 A B x f t) = (term82 A B x f t).
Proof. exact (TRANS (@lem3377080 A B x f t) (@lem3377099 A B x f t)). Qed.
Lemma lem3377105 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3377106 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term85 A B x f t) = (term86 A B x f t).
Proof. exact (MK_COMB (@lem3377105) (@lem3377104 A B x f t)). Qed.
Lemma lem3377107 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term77 A B s x f t) = (term87 A B s x f t).
Proof. exact (MK_COMB (@lem3377076 A B x f s) (@lem3377106 A B x f t)). Qed.
Lemma lem3377110 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term76 A B x s f t) = (term87 A B s x f t).
Proof. exact (TRANS (@lem3377044 A B s x f t) (@lem3377107 A B s x f t)). Qed.
Lemma lem3377111 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : ((term61 A B x f s t) = (term76 A B x s f t)) = ((term73 A B x f s t) = (term87 A B s x f t)).
Proof. exact (MK_COMB (@lem3377040 A B x f s t) (@lem3377110 A B s x f t)). Qed.
Lemma lem3377114 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term88 A B s f t) = (term89 A B s f t).
Proof. exact (fun_ext (fun x : B => @lem3377111 A B s x f t)). Qed.
Lemma lem3377115 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3377116 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term16 A B s f t) = (term90 A B s f t).
Proof. exact (MK_COMB (@lem3377115 B) (@lem3377114 A B s f t)). Qed.
Lemma lem3377121 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term18 A B s f t) = (term91 A B s f t).
Proof. exact (MK_COMB (@lem3376987 A B f t s) (@lem3377116 A B s f t)). Qed.
Lemma lem3377124 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term20 A B s f) = (term92 A B s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3377121 A B s f t)). Qed.
Lemma lem3377125 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3377126 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term22 A B s f) = (term93 A B s f).
Proof. exact (MK_COMB (@lem3377125 A) (@lem3377124 A B s f)). Qed.
Lemma lem3377131 {A B : Type'} (f : A -> B) : (term24 A B f) = (term94 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3377126 A B s f)). Qed.
Lemma lem3377132 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3377133 {A B : Type'} (f : A -> B) : (term26 A B f) = (term95 A B f).
Proof. exact (MK_COMB (@lem3377132 A) (@lem3377131 A B f)). Qed.
Lemma lem3377138 {A B : Type'} : (term28 A B) = (term96 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3377133 A B f)). Qed.
Lemma lem3377139 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3377140 {A B : Type'} : (term30 A B) = (term97 A B).
Proof. exact (MK_COMB (@lem3377139 A B) (@lem3377138 A B)). Qed.
Lemma lem3377145 {A B : Type'} : (term97 A B) = (term30 A B).
Proof. exact (SYM (@lem3377140 A B)). Qed.
Lemma lem3377147 (p : Prop) : p = (term98 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3377148 {A B : Type'} : (term97 A B) = (term99 A B).
Proof. exact (@lem3377147 (term97 A B)). Qed.
Lemma lem3377149 {A B : Type'} : (term99 A B) = (term97 A B).
Proof. exact (SYM (@lem3377148 A B)). Qed.
Lemma lem3377150 {A B : Type'} (h1 : term100 A B) : term100 A B.
Proof. exact (h1). Qed.
Lemma lem3377153 {A B : Type'} (h1 : term99 A B) : term99 A B.
Proof. exact (h1). Qed.
Lemma lem3377154 {A B : Type'} : term101 A B.
Proof. exact (fun h0 : term99 A B => @lem3377153 A B h0). Qed.
Lemma lem3377155 {A B : Type'} (h1 : term101 A B) : term101 A B.
Proof. exact (h1). Qed.
Lemma lem3377156 {A B : Type'} (h1 : term99 A B) : term99 A B.
Proof. exact (h1). Qed.
Lemma lem3377157 {A B : Type'} (h1 : term99 A B) (h2 : term101 A B) : term99 A B.
Proof. exact (@lem3377155 A B h2 (@lem3377156 A B h1)). Qed.
Lemma lem3377158 {A B : Type'} (h1 : term99 A B) : term102 A B.
Proof. exact (fun h0 : term101 A B => @lem3377157 A B h1 h0). Qed.
Lemma lem3377159 {A B : Type'} (h1 : term101 A B) : term101 A B.
Proof. exact (h1). Qed.
Lemma lem3377160 {A B : Type'} (h1 : term99 A B) (h2 : term101 A B) : term99 A B.
Proof. exact (@lem3377158 A B h1 (@lem3377159 A B h2)). Qed.
Lemma lem3377161 {A B : Type'} (h1 : term101 A B) : term101 A B.
Proof. exact (fun h0 : term99 A B => @lem3377160 A B h0 h1). Qed.
Lemma lem3377162 {A B : Type'} : term103 A B.
Proof. exact (fun h0 : term101 A B => @lem3377161 A B h0). Qed.
Lemma lem3377165 {A B : Type'} : term101 A B.
Proof. exact (@lem3377162 A B (@lem3377154 A B)). Qed.
Lemma lem3377166 {A B : Type'} : term101 A B.
Proof. exact (@lem3377165 A B). Qed.
Lemma lem3377168 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3377169 {A B : Type'} : (term99 A B) = (term104 A B).
Proof. exact (@lem3377168 (term100 A B)). Qed.
Lemma lem3377171 (t : Prop) : (term105 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3377172 {A B : Type'} : (term104 A B) = (term97 A B).
Proof. exact (@lem3377171 (term97 A B)). Qed.
Lemma lem3377339 {A B : Type'} : (term99 A B) = (term97 A B).
Proof. exact (TRANS (@lem3377169 A B) (@lem3377172 A B)). Qed.
Lemma lem3377344 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term79 A B x f t x') = (term79 A B x f t x').
Proof. exact (eq_refl (term79 A B x f t x')). Qed.
Lemma lem3377345 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term81 A B x f t) = (term81 A B x f t).
Proof. exact (fun_ext (fun x' : A => @lem3377344 A B x f t x')). Qed.
Lemma lem3377346 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3377347 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term82 A B x f t) = (term82 A B x f t).
Proof. exact (MK_COMB (@lem3377346 A) (@lem3377345 A B x f t)). Qed.
Lemma lem3377348 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3377349 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term86 A B x f t) = (term86 A B x f t).
Proof. exact (MK_COMB (@lem3377348) (@lem3377347 A B x f t)). Qed.
Lemma lem3377354 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term79 A B x f s x') = (term79 A B x f s x').
Proof. exact (eq_refl (term79 A B x f s x')). Qed.
Lemma lem3377355 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term81 A B x f s) = (term81 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3377354 A B x f s x')). Qed.
Lemma lem3377356 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3377357 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term82 A B x f s) = (term82 A B x f s).
Proof. exact (MK_COMB (@lem3377356 A) (@lem3377355 A B x f s)). Qed.
Lemma lem3377358 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3377359 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term84 A B x f s) = (term84 A B x f s).
Proof. exact (MK_COMB (@lem3377358) (@lem3377357 A B x f s)). Qed.
Lemma lem3377360 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term87 A B s x f t) = (term87 A B s x f t).
Proof. exact (MK_COMB (@lem3377359 A B x f s) (@lem3377349 A B x f t)). Qed.
Lemma lem3377371 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term70 A B x f s t x') = (term70 A B x f s t x').
Proof. exact (eq_refl (term70 A B x f s t x')). Qed.
Lemma lem3377372 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term72 A B x f s t) = (term72 A B x f s t).
Proof. exact (fun_ext (fun x' : A => @lem3377371 A B x f s t x')). Qed.
Lemma lem3377373 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3377374 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term73 A B x f s t) = (term73 A B x f s t).
Proof. exact (MK_COMB (@lem3377373 A) (@lem3377372 A B x f s t)). Qed.
Lemma lem3377375 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3377376 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term75 A B x f s t) = (term75 A B x f s t).
Proof. exact (MK_COMB (@lem3377375) (@lem3377374 A B x f s t)). Qed.
Lemma lem3377377 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : ((term73 A B x f s t) = (term87 A B s x f t)) = ((term73 A B x f s t) = (term87 A B s x f t)).
Proof. exact (MK_COMB (@lem3377376 A B x f s t) (@lem3377360 A B s x f t)). Qed.
Lemma lem3377378 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term89 A B s f t) = (term89 A B s f t).
Proof. exact (fun_ext (fun x : B => @lem3377377 A B s x f t)). Qed.
Lemma lem3377379 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3377380 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term90 A B s f t) = (term90 A B s f t).
Proof. exact (MK_COMB (@lem3377379 B) (@lem3377378 A B s f t)). Qed.
Lemma lem3377385 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term53 A t s x) = (term53 A t s x).
Proof. exact (eq_refl (term53 A t s x)). Qed.
Lemma lem3377386 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term55 A t s) = (term55 A t s).
Proof. exact (fun_ext (fun x : A => @lem3377385 A t s x)). Qed.
Lemma lem3377387 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3377388 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term56 A t s) = (term56 A t s).
Proof. exact (MK_COMB (@lem3377387 A) (@lem3377386 A t s)). Qed.
Lemma lem3377401 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term40 A B s f x y) = (term40 A B s f x y).
Proof. exact (eq_refl (term40 A B s f x y)). Qed.
Lemma lem3377402 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term42 A B s f x) = (term42 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem3377401 A B s f x y)). Qed.
Lemma lem3377403 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3377404 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term44 A B s f x) = (term44 A B s f x).
Proof. exact (MK_COMB (@lem3377403 A) (@lem3377402 A B s f x)). Qed.
Lemma lem3377405 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term46 A B s f) = (term46 A B s f).
Proof. exact (fun_ext (fun x : A => @lem3377404 A B s f x)). Qed.
Lemma lem3377406 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3377407 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term48 A B s f) = (term48 A B s f).
Proof. exact (MK_COMB (@lem3377406 A) (@lem3377405 A B s f)). Qed.
Lemma lem3377408 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3377409 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term49 A B s f) = (term49 A B s f).
Proof. exact (MK_COMB (@lem3377408) (@lem3377407 A B s f)). Qed.
Lemma lem3377410 {A B : Type'} (f : A -> B) (t : A -> Prop) (s : A -> Prop) : (term57 A B f t s) = (term57 A B f t s).
Proof. exact (MK_COMB (@lem3377409 A B s f) (@lem3377388 A t s)). Qed.
Lemma lem3377411 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3377412 {A B : Type'} (f : A -> B) (t : A -> Prop) (s : A -> Prop) : (term58 A B f t s) = (term58 A B f t s).
Proof. exact (MK_COMB (@lem3377411) (@lem3377410 A B f t s)). Qed.
Lemma lem3377413 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term91 A B s f t) = (term91 A B s f t).
Proof. exact (MK_COMB (@lem3377412 A B f t s) (@lem3377380 A B s f t)). Qed.
Lemma lem3377414 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term92 A B s f) = (term92 A B s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3377413 A B s f t)). Qed.
Lemma lem3377415 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3377416 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term93 A B s f) = (term93 A B s f).
Proof. exact (MK_COMB (@lem3377415 A) (@lem3377414 A B s f)). Qed.
Lemma lem3377417 {A B : Type'} (f : A -> B) : (term94 A B f) = (term94 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3377416 A B s f)). Qed.
Lemma lem3377418 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3377419 {A B : Type'} (f : A -> B) : (term95 A B f) = (term95 A B f).
Proof. exact (MK_COMB (@lem3377418 A) (@lem3377417 A B f)). Qed.
Lemma lem3377420 {A B : Type'} : (term96 A B) = (term96 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3377419 A B f)). Qed.
Lemma lem3377421 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3377422 {A B : Type'} : (term97 A B) = (term97 A B).
Proof. exact (MK_COMB (@lem3377421 A B) (@lem3377420 A B)). Qed.
Lemma lem3377507 {A B : Type'} : (term99 A B) = (term97 A B).
Proof. exact (TRANS (@lem3377339 A B) (@lem3377422 A B)). Qed.
Lemma lem3377508 {A B : Type'} : (term97 A B) = (term99 A B).
Proof. exact (SYM (@lem3377507 A B)). Qed.
Lemma lem3377509 {A B : Type'} (f : A -> B) (t : A -> Prop) (s : A -> Prop) (h1 : term57 A B f t s) : term57 A B f t s.
Proof. exact (h1). Qed.
Lemma lem3377511 (p : Prop) : p = (term98 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3377512 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : ((term73 A B x f s t) = (term87 A B s x f t)) = (term106 A B s x f t).
Proof. exact (@lem3377511 ((term73 A B x f s t) = (term87 A B s x f t))). Qed.
Lemma lem3377513 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term106 A B s x f t) = ((term73 A B x f s t) = (term87 A B s x f t)).
Proof. exact (SYM (@lem3377512 A B s x f t)). Qed.
Lemma lem3377514 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term107 A B s x f t) : term107 A B s x f t.
Proof. exact (h1). Qed.
Lemma lem3377522 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term108 A B s x f y) = (term109 A B s x f y).
Proof. exact (@lem17045 (s y) ((f x) = (f y))). Qed.
Lemma lem3377524 {A : Type'} (s : A -> Prop) (x : A) : (term110 A s x) = (term110 A s x).
Proof. exact (eq_refl (term110 A s x)). Qed.
Lemma lem3377525 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term111 A B s x f y) = (term112 A B s x f y).
Proof. exact (MK_COMB (@lem3377524 A s x) (@lem3377522 A B s x f y)). Qed.
Lemma lem3377526 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term113 A B s x f y) = (term111 A B s x f y).
Proof. exact (@lem17045 (s x) (term34 A B s x f y)). Qed.
Lemma lem3377527 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term113 A B s x f y) = (term112 A B s x f y).
Proof. exact (TRANS (@lem3377526 A B s x f y) (@lem3377525 A B s x f y)). Qed.
Lemma lem3377528 {A : Type'} (x : A) (y : A) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem3377529 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3377530 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term114 A B s x f y) = (term115 A B s x f y).
Proof. exact (MK_COMB (@lem3377529) (@lem3377527 A B s x f y)). Qed.
Lemma lem3377531 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term116 A B s f x y) = (term117 A B s f x y).
Proof. exact (MK_COMB (@lem3377530 A B s x f y) (@lem3377528 A x y)). Qed.
Lemma lem3377532 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term40 A B s f x y) = (term116 A B s f x y).
Proof. exact (@lem17265 (term36 A B s x f y) (x = y)). Qed.
Lemma lem3377533 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term40 A B s f x y) = (term117 A B s f x y).
Proof. exact (TRANS (@lem3377532 A B s f x y) (@lem3377531 A B s f x y)). Qed.
Lemma lem3377534 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term42 A B s f x) = (term118 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem3377533 A B s f x y)). Qed.
Lemma lem3377535 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3377536 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term44 A B s f x) = (term119 A B s f x).
Proof. exact (MK_COMB (@lem3377535 A) (@lem3377534 A B s f x)). Qed.
Lemma lem3377537 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term46 A B s f) = (term120 A B s f).
Proof. exact (fun_ext (fun x : A => @lem3377536 A B s f x)). Qed.
Lemma lem3377538 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3377539 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term48 A B s f) = (term121 A B s f).
Proof. exact (MK_COMB (@lem3377538 A) (@lem3377537 A B s f)). Qed.
Lemma lem3377546 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term53 A t s x) = (term122 A t s x).
Proof. exact (@lem17265 (t x) (s x)). Qed.
Lemma lem3377547 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term55 A t s) = (term123 A t s).
Proof. exact (fun_ext (fun x : A => @lem3377546 A t s x)). Qed.
Lemma lem3377548 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3377549 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term56 A t s) = (term124 A t s).
Proof. exact (MK_COMB (@lem3377548 A) (@lem3377547 A t s)). Qed.
Lemma lem3377550 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3377551 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term49 A B s f) = (term125 A B s f).
Proof. exact (MK_COMB (@lem3377550) (@lem3377539 A B s f)). Qed.
Lemma lem3377640 {A B : Type'} (f : A -> B) (t : A -> Prop) (s : A -> Prop) : (term57 A B f t s) = (term126 A B f t s).
Proof. exact (MK_COMB (@lem3377551 A B s f) (@lem3377549 A t s)). Qed.
Lemma lem3377641 {A B : Type'} (f : A -> B) (t : A -> Prop) (s : A -> Prop) (h1 : term57 A B f t s) : term126 A B f t s.
Proof. exact (EQ_MP (@lem3377640 A B f t s) (@lem3377509 A B f t s h1)). Qed.
Lemma lem3377649 {A : Type'} (t : A -> Prop) (x : A) : (term127 A t x) = (t x).
Proof. exact (@lem16933 (t x)). Qed.
Lemma lem3377651 {A : Type'} (s : A -> Prop) (x : A) : (term110 A s x) = (term110 A s x).
Proof. exact (eq_refl (term110 A s x)). Qed.
Lemma lem3377652 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term128 A s t x) = (term122 A s t x).
Proof. exact (MK_COMB (@lem3377651 A s x) (@lem3377649 A t x)). Qed.
Lemma lem3377653 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term129 A s t x) = (term128 A s t x).
Proof. exact (@lem17045 (s x) (term66 A t x)). Qed.
Lemma lem3377654 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term129 A s t x) = (term122 A s t x).
Proof. exact (TRANS (@lem3377653 A s t x) (@lem3377652 A s t x)). Qed.
Lemma lem3377659 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term130 A B x f x') = (term130 A B x f x').
Proof. exact (eq_refl (term130 A B x f x')). Qed.
Lemma lem3377660 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term131 A B x f s t x') = (term132 A B x f s t x').
Proof. exact (MK_COMB (@lem3377659 A B x f x') (@lem3377654 A s t x')). Qed.
Lemma lem3377661 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term133 A B x f s t x') = (term131 A B x f s t x').
Proof. exact (@lem17045 (x = (f x')) (term67 A s t x')). Qed.
Lemma lem3377662 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term133 A B x f s t x') = (term132 A B x f s t x').
Proof. exact (TRANS (@lem3377661 A B x f s t x') (@lem3377660 A B x f s t x')). Qed.
Lemma lem3377665 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term70 A B x f s t x') = (term70 A B x f s t x').
Proof. exact (eq_refl (term70 A B x f s t x')). Qed.
Lemma lem3377666 {A : Type'} (P : A -> Prop) : (term134 A P) = (term135 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem3377667 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term136 A B x f s t) = (term137 A B x f s t).
Proof. exact (@lem3377666 A (term72 A B x f s t)). Qed.
Lemma lem3377668 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term138 A B x f s t x') = (term70 A B x f s t x').
Proof. exact (eq_refl (term138 A B x f s t x')). Qed.
Lemma lem3377669 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3377670 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term139 A B x f s t x') = (term133 A B x f s t x').
Proof. exact (MK_COMB (@lem3377669) (@lem3377668 A B x f s t x')). Qed.
Lemma lem3377671 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term139 A B x f s t x') = (term132 A B x f s t x').
Proof. exact (TRANS (@lem3377670 A B x f s t x') (@lem3377662 A B x f s t x')). Qed.
Lemma lem3377672 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term140 A B x f s t) = (term141 A B x f s t).
Proof. exact (fun_ext (fun x' : A => @lem3377671 A B x f s t x')). Qed.
Lemma lem3377673 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3377674 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term137 A B x f s t) = (term142 A B x f s t).
Proof. exact (MK_COMB (@lem3377673 A) (@lem3377672 A B x f s t)). Qed.
Lemma lem3377675 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term136 A B x f s t) = (term142 A B x f s t).
Proof. exact (TRANS (@lem3377667 A B x f s t) (@lem3377674 A B x f s t)). Qed.
Lemma lem3377676 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term72 A B x f s t) = (term72 A B x f s t).
Proof. exact (fun_ext (fun x' : A => @lem3377665 A B x f s t x')). Qed.
Lemma lem3377677 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3377678 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term73 A B x f s t) = (term73 A B x f s t).
Proof. exact (MK_COMB (@lem3377677 A) (@lem3377676 A B x f s t)). Qed.
Lemma lem3377687 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term143 A B x f s x') = (term144 A B x f s x').
Proof. exact (@lem17045 (x = (f x')) (s x')). Qed.
Lemma lem3377690 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term79 A B x f s x') = (term79 A B x f s x').
Proof. exact (eq_refl (term79 A B x f s x')). Qed.
Lemma lem3377691 {A : Type'} (P : A -> Prop) : (term134 A P) = (term135 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem3377692 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term86 A B x f s) = (term145 A B x f s).
Proof. exact (@lem3377691 A (term81 A B x f s)). Qed.
Lemma lem3377693 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term146 A B x f s x') = (term79 A B x f s x').
Proof. exact (eq_refl (term146 A B x f s x')). Qed.
Lemma lem3377694 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3377695 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term147 A B x f s x') = (term143 A B x f s x').
Proof. exact (MK_COMB (@lem3377694) (@lem3377693 A B x f s x')). Qed.
Lemma lem3377696 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term147 A B x f s x') = (term144 A B x f s x').
Proof. exact (TRANS (@lem3377695 A B x f s x') (@lem3377687 A B x f s x')). Qed.
Lemma lem3377697 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term148 A B x f s) = (term149 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3377696 A B x f s x')). Qed.
Lemma lem3377698 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3377699 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term145 A B x f s) = (term150 A B x f s).
Proof. exact (MK_COMB (@lem3377698 A) (@lem3377697 A B x f s)). Qed.
Lemma lem3377700 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term86 A B x f s) = (term150 A B x f s).
Proof. exact (TRANS (@lem3377692 A B x f s) (@lem3377699 A B x f s)). Qed.
Lemma lem3377701 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term81 A B x f s) = (term81 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3377690 A B x f s x')). Qed.
Lemma lem3377702 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3377703 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term82 A B x f s) = (term82 A B x f s).
Proof. exact (MK_COMB (@lem3377702 A) (@lem3377701 A B x f s)). Qed.
Lemma lem3377712 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term143 A B x f t x') = (term144 A B x f t x').
Proof. exact (@lem17045 (x = (f x')) (t x')). Qed.
Lemma lem3377715 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term79 A B x f t x') = (term79 A B x f t x').
Proof. exact (eq_refl (term79 A B x f t x')). Qed.
Lemma lem3377716 {A : Type'} (P : A -> Prop) : (term134 A P) = (term135 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem3377717 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term86 A B x f t) = (term145 A B x f t).
Proof. exact (@lem3377716 A (term81 A B x f t)). Qed.
Lemma lem3377718 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term146 A B x f t x') = (term79 A B x f t x').
Proof. exact (eq_refl (term146 A B x f t x')). Qed.
Lemma lem3377719 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3377720 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term147 A B x f t x') = (term143 A B x f t x').
Proof. exact (MK_COMB (@lem3377719) (@lem3377718 A B x f t x')). Qed.
Lemma lem3377721 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term147 A B x f t x') = (term144 A B x f t x').
Proof. exact (TRANS (@lem3377720 A B x f t x') (@lem3377712 A B x f t x')). Qed.
Lemma lem3377722 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term148 A B x f t) = (term149 A B x f t).
Proof. exact (fun_ext (fun x' : A => @lem3377721 A B x f t x')). Qed.
Lemma lem3377723 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3377724 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term145 A B x f t) = (term150 A B x f t).
Proof. exact (MK_COMB (@lem3377723 A) (@lem3377722 A B x f t)). Qed.
Lemma lem3377725 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term86 A B x f t) = (term150 A B x f t).
Proof. exact (TRANS (@lem3377717 A B x f t) (@lem3377724 A B x f t)). Qed.
Lemma lem3377726 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term81 A B x f t) = (term81 A B x f t).
Proof. exact (fun_ext (fun x' : A => @lem3377715 A B x f t x')). Qed.
Lemma lem3377727 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3377728 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term82 A B x f t) = (term82 A B x f t).
Proof. exact (MK_COMB (@lem3377727 A) (@lem3377726 A B x f t)). Qed.
Lemma lem3377729 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term151 A B x f t) = (term82 A B x f t).
Proof. exact (@lem16933 (term82 A B x f t)). Qed.
Lemma lem3377730 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term151 A B x f t) = (term82 A B x f t).
Proof. exact (TRANS (@lem3377729 A B x f t) (@lem3377728 A B x f t)). Qed.
Lemma lem3377731 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3377732 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term152 A B x f s) = (term153 A B x f s).
Proof. exact (MK_COMB (@lem3377731) (@lem3377700 A B x f s)). Qed.
Lemma lem3377733 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term154 A B s x f t) = (term155 A B s x f t).
Proof. exact (MK_COMB (@lem3377732 A B x f s) (@lem3377730 A B x f t)). Qed.
Lemma lem3377734 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term156 A B s x f t) = (term154 A B s x f t).
Proof. exact (@lem17045 (term82 A B x f s) (term86 A B x f t)). Qed.
Lemma lem3377735 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term156 A B s x f t) = (term155 A B s x f t).
Proof. exact (TRANS (@lem3377734 A B s x f t) (@lem3377733 A B s x f t)). Qed.
Lemma lem3377736 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3377737 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term84 A B x f s) = (term84 A B x f s).
Proof. exact (MK_COMB (@lem3377736) (@lem3377703 A B x f s)). Qed.
Lemma lem3377738 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term87 A B s x f t) = (term157 A B s x f t).
Proof. exact (MK_COMB (@lem3377737 A B x f s) (@lem3377725 A B x f t)). Qed.
Lemma lem3377739 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3377740 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term158 A B x f s t) = (term159 A B x f s t).
Proof. exact (MK_COMB (@lem3377739) (@lem3377675 A B x f s t)). Qed.
Lemma lem3377741 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term160 A B s x f t) = (term161 A B s x f t).
Proof. exact (MK_COMB (@lem3377740 A B x f s t) (@lem3377738 A B s x f t)). Qed.
Lemma lem3377742 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3377743 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term162 A B x f s t) = (term162 A B x f s t).
Proof. exact (MK_COMB (@lem3377742) (@lem3377678 A B x f s t)). Qed.
Lemma lem3377744 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term163 A B s x f t) = (term164 A B s x f t).
Proof. exact (MK_COMB (@lem3377743 A B x f s t) (@lem3377735 A B s x f t)). Qed.
Lemma lem3377745 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3377746 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term165 A B s x f t) = (term166 A B s x f t).
Proof. exact (MK_COMB (@lem3377745) (@lem3377744 A B s x f t)). Qed.
Lemma lem3377747 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term167 A B s x f t) = (term168 A B s x f t).
Proof. exact (MK_COMB (@lem3377746 A B s x f t) (@lem3377741 A B s x f t)). Qed.
Lemma lem3377748 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term107 A B s x f t) = (term167 A B s x f t).
Proof. exact (@lem17646 (term73 A B x f s t) (term87 A B s x f t)). Qed.
Lemma lem3377749 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term107 A B s x f t) = (term168 A B s x f t).
Proof. exact (TRANS (@lem3377748 A B s x f t) (@lem3377747 A B s x f t)). Qed.
Lemma lem3378008 {A : Type'} (P : Prop) (Q : A -> Prop) : (term169 A P Q) = (term170 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3378009 {A : Type'} (P : Prop) (Q : A -> Prop) : (term169 A P Q) = (term170 A P Q).
Proof. exact (@lem3378008 A P Q). Qed.
Lemma lem3378010 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term171 A B s x f t) = (term172 A B s x f t).
Proof. exact (@lem3378009 A (term150 A B x f s) (term81 A B x f t)). Qed.
Lemma lem3378011 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term146 A B x f t x') = (term79 A B x f t x').
Proof. exact (eq_refl (term146 A B x f t x')). Qed.
Lemma lem3378012 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term173 A B x f t) = (term81 A B x f t).
Proof. exact (fun_ext (fun x' : A => @lem3378011 A B x f t x')). Qed.
Lemma lem3378013 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3378014 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term174 A B x f t) = (term82 A B x f t).
Proof. exact (MK_COMB (@lem3378013 A) (@lem3378012 A B x f t)). Qed.
Lemma lem3378015 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term153 A B x f s) = (term153 A B x f s).
Proof. exact (eq_refl (term153 A B x f s)). Qed.
Lemma lem3378016 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term171 A B s x f t) = (term155 A B s x f t).
Proof. exact (MK_COMB (@lem3378015 A B x f s) (@lem3378014 A B x f t)). Qed.
Lemma lem3378017 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3378018 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term175 A B s x f t) = (term176 A B s x f t).
Proof. exact (MK_COMB (@lem3378017) (@lem3378016 A B s x f t)). Qed.
Lemma lem3378019 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term146 A B x f t x') = (term79 A B x f t x').
Proof. exact (eq_refl (term146 A B x f t x')). Qed.
Lemma lem3378020 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term153 A B x f s) = (term153 A B x f s).
Proof. exact (eq_refl (term153 A B x f s)). Qed.
Lemma lem3378021 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term177 A B s x f t x') = (term178 A B s x f t x').
Proof. exact (MK_COMB (@lem3378020 A B x f s) (@lem3378019 A B x f t x')). Qed.
Lemma lem3378022 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term179 A B s x f t) = (term180 A B s x f t).
Proof. exact (fun_ext (fun x' : A => @lem3378021 A B s x f t x')). Qed.
Lemma lem3378023 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3378024 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term172 A B s x f t) = (term181 A B s x f t).
Proof. exact (MK_COMB (@lem3378023 A) (@lem3378022 A B s x f t)). Qed.
Lemma lem3378025 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : ((term171 A B s x f t) = (term172 A B s x f t)) = ((term155 A B s x f t) = (term181 A B s x f t)).
Proof. exact (MK_COMB (@lem3378018 A B s x f t) (@lem3378024 A B s x f t)). Qed.
Lemma lem3378026 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term155 A B s x f t) = (term181 A B s x f t).
Proof. exact (EQ_MP (@lem3378025 A B s x f t) (@lem3378010 A B s x f t)). Qed.
Lemma lem3378027 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term162 A B x f s t) = (term162 A B x f s t).
Proof. exact (eq_refl (term162 A B x f s t)). Qed.
Lemma lem3378028 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term164 A B s x f t) = (term182 A B s x f t).
Proof. exact (MK_COMB (@lem3378027 A B x f s t) (@lem3378026 A B s x f t)). Qed.
Lemma lem3378030 {A : Type'} (P : A -> Prop) (Q : Prop) : (term183 A P Q) = (term184 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3378031 {A : Type'} (P : A -> Prop) (Q : Prop) : (term183 A P Q) = (term184 A P Q).
Proof. exact (@lem3378030 A P Q). Qed.
Lemma lem3378032 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term185 A B s x f t) = (term186 A B s x f t).
Proof. exact (@lem3378031 A (term72 A B x f s t) (term181 A B s x f t)). Qed.
Lemma lem3378033 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term138 A B x f s t x') = (term70 A B x f s t x').
Proof. exact (eq_refl (term138 A B x f s t x')). Qed.
Lemma lem3378034 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term187 A B x f s t) = (term72 A B x f s t).
Proof. exact (fun_ext (fun x' : A => @lem3378033 A B x f s t x')). Qed.
Lemma lem3378035 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3378036 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term188 A B x f s t) = (term73 A B x f s t).
Proof. exact (MK_COMB (@lem3378035 A) (@lem3378034 A B x f s t)). Qed.
Lemma lem3378037 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3378038 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term189 A B x f s t) = (term162 A B x f s t).
Proof. exact (MK_COMB (@lem3378037) (@lem3378036 A B x f s t)). Qed.
Lemma lem3378039 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term181 A B s x f t) = (term181 A B s x f t).
Proof. exact (eq_refl (term181 A B s x f t)). Qed.
Lemma lem3378040 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term185 A B s x f t) = (term182 A B s x f t).
Proof. exact (MK_COMB (@lem3378038 A B x f s t) (@lem3378039 A B s x f t)). Qed.
Lemma lem3378041 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3378042 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term190 A B s x f t) = (term191 A B s x f t).
Proof. exact (MK_COMB (@lem3378041) (@lem3378040 A B s x f t)). Qed.
Lemma lem3378043 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term138 A B x f s t x') = (term70 A B x f s t x').
Proof. exact (eq_refl (term138 A B x f s t x')). Qed.
Lemma lem3378044 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3378045 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term192 A B x f s t x') = (term193 A B x f s t x').
Proof. exact (MK_COMB (@lem3378044) (@lem3378043 A B x f s t x')). Qed.
Lemma lem3378046 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term181 A B s x f t) = (term181 A B s x f t).
Proof. exact (eq_refl (term181 A B s x f t)). Qed.
Lemma lem3378047 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (t : A -> Prop) : (term194 A B x s x' f t) = (term195 A B x s x' f t).
Proof. exact (MK_COMB (@lem3378045 A B x' f s t x) (@lem3378046 A B s x' f t)). Qed.
Lemma lem3378048 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term196 A B s x f t) = (term197 A B s x f t).
Proof. exact (fun_ext (fun x' : A => @lem3378047 A B x' s x f t)). Qed.
Lemma lem3378049 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3378050 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term186 A B s x f t) = (term198 A B s x f t).
Proof. exact (MK_COMB (@lem3378049 A) (@lem3378048 A B s x f t)). Qed.
Lemma lem3378051 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : ((term185 A B s x f t) = (term186 A B s x f t)) = ((term182 A B s x f t) = (term198 A B s x f t)).
Proof. exact (MK_COMB (@lem3378042 A B s x f t) (@lem3378050 A B s x f t)). Qed.
Lemma lem3378052 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term182 A B s x f t) = (term198 A B s x f t).
Proof. exact (EQ_MP (@lem3378051 A B s x f t) (@lem3378032 A B s x f t)). Qed.
Lemma lem3378054 {A : Type'} (P : Prop) (Q : A -> Prop) : (term199 A P Q) = (term200 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3378055 {A : Type'} (P : Prop) (Q : A -> Prop) : (term199 A P Q) = (term200 A P Q).
Proof. exact (@lem3378054 A P Q). Qed.
Lemma lem3378056 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (t : A -> Prop) : (term201 A B x s x' f t) = (term202 A B x s x' f t).
Proof. exact (@lem3378055 A (term70 A B x' f s t x) (term180 A B s x' f t)). Qed.
Lemma lem3378057 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term203 A B s x f t x') = (term178 A B s x f t x').
Proof. exact (eq_refl (term203 A B s x f t x')). Qed.
Lemma lem3378058 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term204 A B s x f t) = (term180 A B s x f t).
Proof. exact (fun_ext (fun x' : A => @lem3378057 A B s x f t x')). Qed.
Lemma lem3378059 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3378060 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term205 A B s x f t) = (term181 A B s x f t).
Proof. exact (MK_COMB (@lem3378059 A) (@lem3378058 A B s x f t)). Qed.
Lemma lem3378061 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term193 A B x f s t x') = (term193 A B x f s t x').
Proof. exact (eq_refl (term193 A B x f s t x')). Qed.
Lemma lem3378062 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (t : A -> Prop) : (term201 A B x s x' f t) = (term195 A B x s x' f t).
Proof. exact (MK_COMB (@lem3378061 A B x' f s t x) (@lem3378060 A B s x' f t)). Qed.
Lemma lem3378063 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3378064 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (t : A -> Prop) : (term206 A B x s x' f t) = (term207 A B x s x' f t).
Proof. exact (MK_COMB (@lem3378063) (@lem3378062 A B x s x' f t)). Qed.
Lemma lem3378065 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term203 A B s x f t x') = (term178 A B s x f t x').
Proof. exact (eq_refl (term203 A B s x f t x')). Qed.
Lemma lem3378066 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term193 A B x f s t x') = (term193 A B x f s t x').
Proof. exact (eq_refl (term193 A B x f s t x')). Qed.
Lemma lem3378067 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (t : A -> Prop) (x'' : A) : (term208 A B x s x' f t x'') = (term209 A B x s x' f t x'').
Proof. exact (MK_COMB (@lem3378066 A B x' f s t x) (@lem3378065 A B s x' f t x'')). Qed.
Lemma lem3378068 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (t : A -> Prop) : (term210 A B x s x' f t) = (term211 A B x s x' f t).
Proof. exact (fun_ext (fun x'' : A => @lem3378067 A B x s x' f t x'')). Qed.
Lemma lem3378069 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3378070 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (t : A -> Prop) : (term202 A B x s x' f t) = (term212 A B x s x' f t).
Proof. exact (MK_COMB (@lem3378069 A) (@lem3378068 A B x s x' f t)). Qed.
Lemma lem3378071 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (t : A -> Prop) : ((term201 A B x s x' f t) = (term202 A B x s x' f t)) = ((term195 A B x s x' f t) = (term212 A B x s x' f t)).
Proof. exact (MK_COMB (@lem3378064 A B x s x' f t) (@lem3378070 A B x s x' f t)). Qed.
Lemma lem3378072 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (t : A -> Prop) : (term195 A B x s x' f t) = (term212 A B x s x' f t).
Proof. exact (EQ_MP (@lem3378071 A B x s x' f t) (@lem3378056 A B x s x' f t)). Qed.
Lemma lem3378073 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term197 A B s x f t) = (term213 A B s x f t).
Proof. exact (fun_ext (fun x' : A => @lem3378072 A B x' s x f t)). Qed.
Lemma lem3378074 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3378075 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term198 A B s x f t) = (term214 A B s x f t).
Proof. exact (MK_COMB (@lem3378074 A) (@lem3378073 A B s x f t)). Qed.
Lemma lem3378076 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term182 A B s x f t) = (term214 A B s x f t).
Proof. exact (TRANS (@lem3378052 A B s x f t) (@lem3378075 A B s x f t)). Qed.
Lemma lem3378077 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term164 A B s x f t) = (term214 A B s x f t).
Proof. exact (TRANS (@lem3378028 A B s x f t) (@lem3378076 A B s x f t)). Qed.
Lemma lem3378078 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3378079 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term166 A B s x f t) = (term215 A B s x f t).
Proof. exact (MK_COMB (@lem3378078) (@lem3378077 A B s x f t)). Qed.
Lemma lem3378081 {A : Type'} (P : A -> Prop) (Q : Prop) : (term183 A P Q) = (term184 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3378082 {A : Type'} (P : A -> Prop) (Q : Prop) : (term183 A P Q) = (term184 A P Q).
Proof. exact (@lem3378081 A P Q). Qed.
Lemma lem3378083 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term216 A B s x f t) = (term217 A B s x f t).
Proof. exact (@lem3378082 A (term81 A B x f s) (term150 A B x f t)). Qed.
Lemma lem3378084 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term146 A B x f s x') = (term79 A B x f s x').
Proof. exact (eq_refl (term146 A B x f s x')). Qed.
Lemma lem3378085 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term173 A B x f s) = (term81 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3378084 A B x f s x')). Qed.
Lemma lem3378086 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3378087 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term174 A B x f s) = (term82 A B x f s).
Proof. exact (MK_COMB (@lem3378086 A) (@lem3378085 A B x f s)). Qed.
Lemma lem3378088 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3378089 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term218 A B x f s) = (term84 A B x f s).
Proof. exact (MK_COMB (@lem3378088) (@lem3378087 A B x f s)). Qed.
Lemma lem3378090 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term150 A B x f t) = (term150 A B x f t).
Proof. exact (eq_refl (term150 A B x f t)). Qed.
Lemma lem3378091 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term216 A B s x f t) = (term157 A B s x f t).
Proof. exact (MK_COMB (@lem3378089 A B x f s) (@lem3378090 A B x f t)). Qed.
Lemma lem3378092 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3378093 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term219 A B s x f t) = (term220 A B s x f t).
Proof. exact (MK_COMB (@lem3378092) (@lem3378091 A B s x f t)). Qed.
Lemma lem3378094 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term146 A B x f s x') = (term79 A B x f s x').
Proof. exact (eq_refl (term146 A B x f s x')). Qed.
Lemma lem3378095 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3378096 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term221 A B x f s x') = (term222 A B x f s x').
Proof. exact (MK_COMB (@lem3378095) (@lem3378094 A B x f s x')). Qed.
Lemma lem3378097 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term150 A B x f t) = (term150 A B x f t).
Proof. exact (eq_refl (term150 A B x f t)). Qed.
Lemma lem3378098 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term223 A B s x x' f t) = (term224 A B s x x' f t).
Proof. exact (MK_COMB (@lem3378096 A B x' f s x) (@lem3378097 A B x' f t)). Qed.
Lemma lem3378099 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term225 A B s x f t) = (term226 A B s x f t).
Proof. exact (fun_ext (fun x' : A => @lem3378098 A B s x' x f t)). Qed.
Lemma lem3378100 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3378101 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term217 A B s x f t) = (term227 A B s x f t).
Proof. exact (MK_COMB (@lem3378100 A) (@lem3378099 A B s x f t)). Qed.
Lemma lem3378102 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : ((term216 A B s x f t) = (term217 A B s x f t)) = ((term157 A B s x f t) = (term227 A B s x f t)).
Proof. exact (MK_COMB (@lem3378093 A B s x f t) (@lem3378101 A B s x f t)). Qed.
Lemma lem3378103 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term157 A B s x f t) = (term227 A B s x f t).
Proof. exact (EQ_MP (@lem3378102 A B s x f t) (@lem3378083 A B s x f t)). Qed.
Lemma lem3378104 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term159 A B x f s t) = (term159 A B x f s t).
Proof. exact (eq_refl (term159 A B x f s t)). Qed.
Lemma lem3378105 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term161 A B s x f t) = (term228 A B s x f t).
Proof. exact (MK_COMB (@lem3378104 A B x f s t) (@lem3378103 A B s x f t)). Qed.
Lemma lem3378107 {A : Type'} (P : Prop) (Q : A -> Prop) : (term199 A P Q) = (term200 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3378108 {A : Type'} (P : Prop) (Q : A -> Prop) : (term199 A P Q) = (term200 A P Q).
Proof. exact (@lem3378107 A P Q). Qed.
Lemma lem3378109 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term229 A B s x f t) = (term230 A B s x f t).
Proof. exact (@lem3378108 A (term142 A B x f s t) (term226 A B s x f t)). Qed.
Lemma lem3378110 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term231 A B s x' f t x) = (term224 A B s x x' f t).
Proof. exact (eq_refl (term231 A B s x' f t x)). Qed.
Lemma lem3378111 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term232 A B s x f t) = (term226 A B s x f t).
Proof. exact (fun_ext (fun x' : A => @lem3378110 A B s x' x f t)). Qed.
Lemma lem3378112 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3378113 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term233 A B s x f t) = (term227 A B s x f t).
Proof. exact (MK_COMB (@lem3378112 A) (@lem3378111 A B s x f t)). Qed.
Lemma lem3378114 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term159 A B x f s t) = (term159 A B x f s t).
Proof. exact (eq_refl (term159 A B x f s t)). Qed.
Lemma lem3378115 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term229 A B s x f t) = (term228 A B s x f t).
Proof. exact (MK_COMB (@lem3378114 A B x f s t) (@lem3378113 A B s x f t)). Qed.
Lemma lem3378116 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3378117 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term234 A B s x f t) = (term235 A B s x f t).
Proof. exact (MK_COMB (@lem3378116) (@lem3378115 A B s x f t)). Qed.
Lemma lem3378118 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term231 A B s x' f t x) = (term224 A B s x x' f t).
Proof. exact (eq_refl (term231 A B s x' f t x)). Qed.
Lemma lem3378119 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term159 A B x f s t) = (term159 A B x f s t).
Proof. exact (eq_refl (term159 A B x f s t)). Qed.
Lemma lem3378120 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term236 A B s x' f t x) = (term237 A B s x x' f t).
Proof. exact (MK_COMB (@lem3378119 A B x' f s t) (@lem3378118 A B s x x' f t)). Qed.
Lemma lem3378121 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term238 A B s x f t) = (term239 A B s x f t).
Proof. exact (fun_ext (fun x' : A => @lem3378120 A B s x' x f t)). Qed.
Lemma lem3378122 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3378123 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term230 A B s x f t) = (term240 A B s x f t).
Proof. exact (MK_COMB (@lem3378122 A) (@lem3378121 A B s x f t)). Qed.
Lemma lem3378124 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : ((term229 A B s x f t) = (term230 A B s x f t)) = ((term228 A B s x f t) = (term240 A B s x f t)).
Proof. exact (MK_COMB (@lem3378117 A B s x f t) (@lem3378123 A B s x f t)). Qed.
Lemma lem3378125 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term228 A B s x f t) = (term240 A B s x f t).
Proof. exact (EQ_MP (@lem3378124 A B s x f t) (@lem3378109 A B s x f t)). Qed.
Lemma lem3378126 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term161 A B s x f t) = (term240 A B s x f t).
Proof. exact (TRANS (@lem3378105 A B s x f t) (@lem3378125 A B s x f t)). Qed.
Lemma lem3378127 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term168 A B s x f t) = (term241 A B s x f t).
Proof. exact (MK_COMB (@lem3378079 A B s x f t) (@lem3378126 A B s x f t)). Qed.
Lemma lem3378129 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term242 A P Q) = (term243 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3378130 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term242 A P Q) = (term243 A P Q).
Proof. exact (@lem3378129 A P Q). Qed.
Lemma lem3378131 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term244 A B s x f t) = (term245 A B s x f t).
Proof. exact (@lem3378130 A (term213 A B s x f t) (term239 A B s x f t)). Qed.
Lemma lem3378132 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (t : A -> Prop) : (term246 A B s x' f t x) = (term212 A B x s x' f t).
Proof. exact (eq_refl (term246 A B s x' f t x)). Qed.
Lemma lem3378133 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term247 A B s x f t) = (term213 A B s x f t).
Proof. exact (fun_ext (fun x' : A => @lem3378132 A B x' s x f t)). Qed.
Lemma lem3378134 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3378135 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term248 A B s x f t) = (term214 A B s x f t).
Proof. exact (MK_COMB (@lem3378134 A) (@lem3378133 A B s x f t)). Qed.
Lemma lem3378136 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3378137 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term249 A B s x f t) = (term215 A B s x f t).
Proof. exact (MK_COMB (@lem3378136) (@lem3378135 A B s x f t)). Qed.
Lemma lem3378138 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term250 A B s x' f t x) = (term237 A B s x x' f t).
Proof. exact (eq_refl (term250 A B s x' f t x)). Qed.
Lemma lem3378139 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term251 A B s x f t) = (term239 A B s x f t).
Proof. exact (fun_ext (fun x' : A => @lem3378138 A B s x' x f t)). Qed.
Lemma lem3378140 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3378141 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term252 A B s x f t) = (term240 A B s x f t).
Proof. exact (MK_COMB (@lem3378140 A) (@lem3378139 A B s x f t)). Qed.
Lemma lem3378142 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term244 A B s x f t) = (term241 A B s x f t).
Proof. exact (MK_COMB (@lem3378137 A B s x f t) (@lem3378141 A B s x f t)). Qed.
Lemma lem3378143 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3378144 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term253 A B s x f t) = (term254 A B s x f t).
Proof. exact (MK_COMB (@lem3378143) (@lem3378142 A B s x f t)). Qed.
Lemma lem3378145 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (t : A -> Prop) : (term246 A B s x' f t x) = (term212 A B x s x' f t).
Proof. exact (eq_refl (term246 A B s x' f t x)). Qed.
Lemma lem3378146 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3378147 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (t : A -> Prop) : (term255 A B s x' f t x) = (term256 A B x s x' f t).
Proof. exact (MK_COMB (@lem3378146) (@lem3378145 A B x s x' f t)). Qed.
Lemma lem3378148 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term250 A B s x' f t x) = (term237 A B s x x' f t).
Proof. exact (eq_refl (term250 A B s x' f t x)). Qed.
Lemma lem3378149 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term257 A B s x' f t x) = (term258 A B s x x' f t).
Proof. exact (MK_COMB (@lem3378147 A B x s x' f t) (@lem3378148 A B s x x' f t)). Qed.
Lemma lem3378150 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term259 A B s x f t) = (term260 A B s x f t).
Proof. exact (fun_ext (fun x' : A => @lem3378149 A B s x' x f t)). Qed.
Lemma lem3378151 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3378152 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term245 A B s x f t) = (term261 A B s x f t).
Proof. exact (MK_COMB (@lem3378151 A) (@lem3378150 A B s x f t)). Qed.
Lemma lem3378153 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : ((term244 A B s x f t) = (term245 A B s x f t)) = ((term241 A B s x f t) = (term261 A B s x f t)).
Proof. exact (MK_COMB (@lem3378144 A B s x f t) (@lem3378152 A B s x f t)). Qed.
Lemma lem3378154 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term241 A B s x f t) = (term261 A B s x f t).
Proof. exact (EQ_MP (@lem3378153 A B s x f t) (@lem3378131 A B s x f t)). Qed.
Lemma lem3378156 {A : Type'} (P : A -> Prop) (Q : Prop) : (term262 A P Q) = (term263 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3378157 {A : Type'} (P : A -> Prop) (Q : Prop) : (term262 A P Q) = (term263 A P Q).
Proof. exact (@lem3378156 A P Q). Qed.
Lemma lem3378158 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term264 A B s x x' f t) = (term265 A B s x x' f t).
Proof. exact (@lem3378157 A (term211 A B x s x' f t) (term237 A B s x x' f t)). Qed.
Lemma lem3378159 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (t : A -> Prop) (x'' : A) : (term266 A B x s x' f t x'') = (term209 A B x s x' f t x'').
Proof. exact (eq_refl (term266 A B x s x' f t x'')). Qed.
Lemma lem3378160 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (t : A -> Prop) : (term267 A B x s x' f t) = (term211 A B x s x' f t).
Proof. exact (fun_ext (fun x'' : A => @lem3378159 A B x s x' f t x'')). Qed.
Lemma lem3378161 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3378162 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (t : A -> Prop) : (term268 A B x s x' f t) = (term212 A B x s x' f t).
Proof. exact (MK_COMB (@lem3378161 A) (@lem3378160 A B x s x' f t)). Qed.
Lemma lem3378163 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3378164 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (t : A -> Prop) : (term269 A B x s x' f t) = (term256 A B x s x' f t).
Proof. exact (MK_COMB (@lem3378163) (@lem3378162 A B x s x' f t)). Qed.
Lemma lem3378165 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term237 A B s x x' f t) = (term237 A B s x x' f t).
Proof. exact (eq_refl (term237 A B s x x' f t)). Qed.
Lemma lem3378166 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term264 A B s x x' f t) = (term258 A B s x x' f t).
Proof. exact (MK_COMB (@lem3378164 A B x s x' f t) (@lem3378165 A B s x x' f t)). Qed.
Lemma lem3378167 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3378168 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term270 A B s x x' f t) = (term271 A B s x x' f t).
Proof. exact (MK_COMB (@lem3378167) (@lem3378166 A B s x x' f t)). Qed.
Lemma lem3378169 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (t : A -> Prop) (x'' : A) : (term266 A B x s x' f t x'') = (term209 A B x s x' f t x'').
Proof. exact (eq_refl (term266 A B x s x' f t x'')). Qed.
Lemma lem3378170 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3378171 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (t : A -> Prop) (x'' : A) : (term272 A B x s x' f t x'') = (term273 A B x s x' f t x'').
Proof. exact (MK_COMB (@lem3378170) (@lem3378169 A B x s x' f t x'')). Qed.
Lemma lem3378172 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term237 A B s x x' f t) = (term237 A B s x x' f t).
Proof. exact (eq_refl (term237 A B s x x' f t)). Qed.
Lemma lem3378173 {A B : Type'} (x' : A) (s : A -> Prop) (x : A) (x'' : B) (f : A -> B) (t : A -> Prop) : (term274 A B x' s x x'' f t) = (term275 A B x' s x x'' f t).
Proof. exact (MK_COMB (@lem3378171 A B x s x'' f t x') (@lem3378172 A B s x x'' f t)). Qed.
Lemma lem3378174 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term276 A B s x x' f t) = (term277 A B s x x' f t).
Proof. exact (fun_ext (fun x'' : A => @lem3378173 A B x'' s x x' f t)). Qed.
Lemma lem3378175 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3378176 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term265 A B s x x' f t) = (term278 A B s x x' f t).
Proof. exact (MK_COMB (@lem3378175 A) (@lem3378174 A B s x x' f t)). Qed.
Lemma lem3378177 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : ((term264 A B s x x' f t) = (term265 A B s x x' f t)) = ((term258 A B s x x' f t) = (term278 A B s x x' f t)).
Proof. exact (MK_COMB (@lem3378168 A B s x x' f t) (@lem3378176 A B s x x' f t)). Qed.
Lemma lem3378178 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term258 A B s x x' f t) = (term278 A B s x x' f t).
Proof. exact (EQ_MP (@lem3378177 A B s x x' f t) (@lem3378158 A B s x x' f t)). Qed.
Lemma lem3378179 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term260 A B s x f t) = (term279 A B s x f t).
Proof. exact (fun_ext (fun x' : A => @lem3378178 A B s x' x f t)). Qed.
Lemma lem3378180 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3378181 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term261 A B s x f t) = (term280 A B s x f t).
Proof. exact (MK_COMB (@lem3378180 A) (@lem3378179 A B s x f t)). Qed.
Lemma lem3378182 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term241 A B s x f t) = (term280 A B s x f t).
Proof. exact (TRANS (@lem3378154 A B s x f t) (@lem3378181 A B s x f t)). Qed.
Lemma lem3378184 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term168 A B s x f t) = (term280 A B s x f t).
Proof. exact (TRANS (@lem3378127 A B s x f t) (@lem3378182 A B s x f t)). Qed.
Lemma lem3378185 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term107 A B s x f t) = (term280 A B s x f t).
Proof. exact (TRANS (@lem3377749 A B s x f t) (@lem3378184 A B s x f t)). Qed.
Lemma lem3378186 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term107 A B s x f t) : term280 A B s x f t.
Proof. exact (EQ_MP (@lem3378185 A B s x f t) (@lem3377514 A B s x f t h1)). Qed.
Lemma lem3378187 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term278 A B s x' x f t) : term278 A B s x' x f t.
Proof. exact (h1). Qed.
Lemma lem3378188 {A B : Type'} (x'' : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term275 A B x'' s x' x f t) : term275 A B x'' s x' x f t.
Proof. exact (h1). Qed.
Lemma lem3378199 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term122 A t s x) = (term122 A t s x).
Proof. exact (eq_refl (term122 A t s x)). Qed.
Lemma lem3378200 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term123 A t s) = (term123 A t s).
Proof. exact (fun_ext (fun x : A => @lem3378199 A t s x)). Qed.
Lemma lem3378201 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3378202 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term124 A t s) = (term124 A t s).
Proof. exact (MK_COMB (@lem3378201 A) (@lem3378200 A t s)). Qed.
Lemma lem3378237 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term117 A B s f x y) = (term117 A B s f x y).
Proof. exact (eq_refl (term117 A B s f x y)). Qed.
Lemma lem3378238 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term118 A B s f x) = (term118 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem3378237 A B s f x y)). Qed.
Lemma lem3378239 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3378240 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term119 A B s f x) = (term119 A B s f x).
Proof. exact (MK_COMB (@lem3378239 A) (@lem3378238 A B s f x)). Qed.
Lemma lem3378241 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term120 A B s f) = (term120 A B s f).
Proof. exact (fun_ext (fun x : A => @lem3378240 A B s f x)). Qed.
Lemma lem3378242 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3378243 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term121 A B s f) = (term121 A B s f).
Proof. exact (MK_COMB (@lem3378242 A) (@lem3378241 A B s f)). Qed.
Lemma lem3378244 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3378245 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term125 A B s f) = (term125 A B s f).
Proof. exact (MK_COMB (@lem3378244) (@lem3378243 A B s f)). Qed.
Lemma lem3378246 {A B : Type'} (f : A -> B) (t : A -> Prop) (s : A -> Prop) : (term126 A B f t s) = (term126 A B f t s).
Proof. exact (MK_COMB (@lem3378245 A B s f) (@lem3378202 A t s)). Qed.
Lemma lem3378247 {A B : Type'} (f : A -> B) (t : A -> Prop) (s : A -> Prop) (h1 : term57 A B f t s) : term126 A B f t s.
Proof. exact (EQ_MP (@lem3378246 A B f t s) (@lem3377641 A B f t s h1)). Qed.
Lemma lem3378264 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term144 A B x f t x') = (term144 A B x f t x').
Proof. exact (eq_refl (term144 A B x f t x')). Qed.
Lemma lem3378265 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term149 A B x f t) = (term149 A B x f t).
Proof. exact (fun_ext (fun x' : A => @lem3378264 A B x f t x')). Qed.
Lemma lem3378266 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3378267 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term150 A B x f t) = (term150 A B x f t).
Proof. exact (MK_COMB (@lem3378266 A) (@lem3378265 A B x f t)). Qed.
Lemma lem3378282 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term222 A B x f s x') = (term222 A B x f s x').
Proof. exact (eq_refl (term222 A B x f s x')). Qed.
Lemma lem3378283 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) : (term224 A B s x' x f t) = (term224 A B s x' x f t).
Proof. exact (MK_COMB (@lem3378282 A B x f s x') (@lem3378267 A B x f t)). Qed.
Lemma lem3378306 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term132 A B x f s t x') = (term132 A B x f s t x').
Proof. exact (eq_refl (term132 A B x f s t x')). Qed.
Lemma lem3378307 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term141 A B x f s t) = (term141 A B x f s t).
Proof. exact (fun_ext (fun x' : A => @lem3378306 A B x f s t x')). Qed.
Lemma lem3378308 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3378309 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term142 A B x f s t) = (term142 A B x f s t).
Proof. exact (MK_COMB (@lem3378308 A) (@lem3378307 A B x f s t)). Qed.
Lemma lem3378310 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3378311 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term159 A B x f s t) = (term159 A B x f s t).
Proof. exact (MK_COMB (@lem3378310) (@lem3378309 A B x f s t)). Qed.
Lemma lem3378312 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) : (term237 A B s x' x f t) = (term237 A B s x' x f t).
Proof. exact (MK_COMB (@lem3378311 A B x f s t) (@lem3378283 A B s x' x f t)). Qed.
Lemma lem3378325 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) : (term79 A B x f t x'') = (term79 A B x f t x'').
Proof. exact (eq_refl (term79 A B x f t x'')). Qed.
Lemma lem3378342 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term144 A B x f s x') = (term144 A B x f s x').
Proof. exact (eq_refl (term144 A B x f s x')). Qed.
Lemma lem3378343 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term149 A B x f s) = (term149 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3378342 A B x f s x')). Qed.
Lemma lem3378344 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3378345 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term150 A B x f s) = (term150 A B x f s).
Proof. exact (MK_COMB (@lem3378344 A) (@lem3378343 A B x f s)). Qed.
Lemma lem3378346 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3378347 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term153 A B x f s) = (term153 A B x f s).
Proof. exact (MK_COMB (@lem3378346) (@lem3378345 A B x f s)). Qed.
Lemma lem3378348 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) : (term178 A B s x f t x'') = (term178 A B s x f t x'').
Proof. exact (MK_COMB (@lem3378347 A B x f s) (@lem3378325 A B x f t x'')). Qed.
Lemma lem3378371 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term193 A B x f s t x') = (term193 A B x f s t x').
Proof. exact (eq_refl (term193 A B x f s t x')). Qed.
Lemma lem3378372 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) : (term209 A B x' s x f t x'') = (term209 A B x' s x f t x'').
Proof. exact (MK_COMB (@lem3378371 A B x f s t x') (@lem3378348 A B s x f t x'')). Qed.
Lemma lem3378373 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3378374 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) : (term273 A B x' s x f t x'') = (term273 A B x' s x f t x'').
Proof. exact (MK_COMB (@lem3378373) (@lem3378372 A B x' s x f t x'')). Qed.
Lemma lem3378375 {A B : Type'} (x'' : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) : (term275 A B x'' s x' x f t) = (term275 A B x'' s x' x f t).
Proof. exact (MK_COMB (@lem3378374 A B x' s x f t x'') (@lem3378312 A B s x' x f t)). Qed.
Lemma lem3378376 {A B : Type'} (x'' : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term275 A B x'' s x' x f t) : term275 A B x'' s x' x f t.
Proof. exact (EQ_MP (@lem3378375 A B x'' s x' x f t) (@lem3378188 A B x'' s x' x f t h1)). Qed.
Lemma lem3378377 {A B : Type'} (f : A -> B) (t : A -> Prop) (s : A -> Prop) (h1 : term57 A B f t s) : term124 A t s.
Proof. exact (proj2 (@lem3378247 A B f t s h1)). Qed.
Lemma lem3378378 {A B : Type'} (f : A -> B) (t : A -> Prop) (s : A -> Prop) (h1 : term57 A B f t s) : term121 A B s f.
Proof. exact (proj1 (@lem3378247 A B f t s h1)). Qed.
Lemma lem3378379 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term209 A B x' s x f t x'') : term209 A B x' s x f t x''.
Proof. exact (h1). Qed.
Lemma lem3378380 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term237 A B s x' x f t) : term237 A B s x' x f t.
Proof. exact (h1). Qed.
Lemma lem3378381 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term209 A B x' s x f t x'') : term178 A B s x f t x''.
Proof. exact (proj2 (@lem3378379 A B x' s x f t x'' h1)). Qed.
Lemma lem3378382 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term209 A B x' s x f t x'') : term70 A B x f s t x'.
Proof. exact (proj1 (@lem3378379 A B x' s x f t x'' h1)). Qed.
Lemma lem3378383 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term209 A B x' s x f t x'') : term67 A s t x'.
Proof. exact (proj2 (@lem3378382 A B x' s x f t x'' h1)). Qed.
Lemma lem3378387 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (h1 : term150 A B x f s) : term150 A B x f s.
Proof. exact (h1). Qed.
Lemma lem3378388 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term79 A B x f t x'') : term79 A B x f t x''.
Proof. exact (h1). Qed.
Lemma lem3378391 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term237 A B s x' x f t) : term224 A B s x' x f t.
Proof. exact (proj2 (@lem3378380 A B s x' x f t h1)). Qed.
Lemma lem3378392 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term237 A B s x' x f t) : term142 A B x f s t.
Proof. exact (proj1 (@lem3378380 A B s x' x f t h1)). Qed.
Lemma lem3378393 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term237 A B s x' x f t) : term150 A B x f t.
Proof. exact (proj2 (@lem3378391 A B s x' x f t h1)). Qed.
Lemma lem3378394 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term237 A B s x' x f t) : term79 A B x f s x'.
Proof. exact (proj1 (@lem3378391 A B s x' x f t h1)). Qed.
Lemma lem3378457 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term144 A B x f s x') = (term144 A B x f s x').
Proof. exact (eq_refl (term144 A B x f s x')). Qed.
Lemma lem3378458 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term149 A B x f s) = (term149 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3378457 A B x f s x')). Qed.
Lemma lem3378459 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3378461 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term150 A B x f s) = (term150 A B x f s).
Proof. exact (MK_COMB (@lem3378459 A) (@lem3378458 A B x f s)). Qed.
Lemma lem3378462 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (h1 : term150 A B x f s) : term150 A B x f s.
Proof. exact (EQ_MP (@lem3378461 A B x f s) (@lem3378387 A B x f s h1)). Qed.
Lemma lem3378482 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term117 A B s f x y) = (term117 A B s f x y).
Proof. exact (eq_refl (term117 A B s f x y)). Qed.
Lemma lem3378483 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term118 A B s f x) = (term118 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem3378482 A B s f x y)). Qed.
Lemma lem3378484 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3378485 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term119 A B s f x) = (term119 A B s f x).
Proof. exact (MK_COMB (@lem3378484 A) (@lem3378483 A B s f x)). Qed.
Lemma lem3378486 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term120 A B s f) = (term120 A B s f).
Proof. exact (fun_ext (fun x : A => @lem3378485 A B s f x)). Qed.
Lemma lem3378487 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3378489 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term121 A B s f) = (term121 A B s f).
Proof. exact (MK_COMB (@lem3378487 A) (@lem3378486 A B s f)). Qed.
Lemma lem3378490 {A B : Type'} (f : A -> B) (t : A -> Prop) (s : A -> Prop) (h1 : term57 A B f t s) : term121 A B s f.
Proof. exact (EQ_MP (@lem3378489 A B s f) (@lem3378378 A B f t s h1)). Qed.
Lemma lem3378498 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term122 A t s x) = (term122 A t s x).
Proof. exact (eq_refl (term122 A t s x)). Qed.
Lemma lem3378499 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term123 A t s) = (term123 A t s).
Proof. exact (fun_ext (fun x : A => @lem3378498 A t s x)). Qed.
Lemma lem3378500 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3378502 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term124 A t s) = (term124 A t s).
Proof. exact (MK_COMB (@lem3378500 A) (@lem3378499 A t s)). Qed.
Lemma lem3378503 {A B : Type'} (f : A -> B) (t : A -> Prop) (s : A -> Prop) (h1 : term57 A B f t s) : term124 A t s.
Proof. exact (EQ_MP (@lem3378502 A t s) (@lem3378377 A B f t s h1)). Qed.
Lemma lem3378578 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term132 A B x f s t x') = (term132 A B x f s t x').
Proof. exact (eq_refl (term132 A B x f s t x')). Qed.
Lemma lem3378579 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term141 A B x f s t) = (term141 A B x f s t).
Proof. exact (fun_ext (fun x' : A => @lem3378578 A B x f s t x')). Qed.
Lemma lem3378580 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3378582 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term142 A B x f s t) = (term142 A B x f s t).
Proof. exact (MK_COMB (@lem3378580 A) (@lem3378579 A B x f s t)). Qed.
Lemma lem3378583 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term237 A B s x' x f t) : term142 A B x f s t.
Proof. exact (EQ_MP (@lem3378582 A B x f s t) (@lem3378392 A B s x' x f t h1)). Qed.
Lemma lem3378591 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term144 A B x f t x') = (term144 A B x f t x').
Proof. exact (eq_refl (term144 A B x f t x')). Qed.
Lemma lem3378592 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term149 A B x f t) = (term149 A B x f t).
Proof. exact (fun_ext (fun x' : A => @lem3378591 A B x f t x')). Qed.
Lemma lem3378593 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3378595 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term150 A B x f t) = (term150 A B x f t).
Proof. exact (MK_COMB (@lem3378593 A) (@lem3378592 A B x f t)). Qed.
Lemma lem3378596 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term237 A B s x' x f t) : term150 A B x f t.
Proof. exact (EQ_MP (@lem3378595 A B x f t) (@lem3378393 A B s x' x f t h1)). Qed.
Lemma lem3378614 {A B : Type'} (_35381 : A) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term150 A B x f s) : term281 A B x f s _35381.
Proof. exact (@lem3378462 A B x f s h1 _35381). Qed.
Lemma lem3378615 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (_35381 : A) : (term281 A B x f s _35381) = (term144 A B x f s _35381).
Proof. exact (eq_refl (term281 A B x f s _35381)). Qed.
Lemma lem3378617 {A B : Type'} (_35382 : A) (f : A -> B) (t : A -> Prop) (s : A -> Prop) (h1 : term57 A B f t s) : term282 A B s f _35382.
Proof. exact (@lem3378490 A B f t s h1 _35382). Qed.
Lemma lem3378618 {A B : Type'} (s : A -> Prop) (f : A -> B) (_35382 : A) : (term282 A B s f _35382) = (term119 A B s f _35382).
Proof. exact (eq_refl (term282 A B s f _35382)). Qed.
Lemma lem3378619 {A B : Type'} (_35382 : A) (f : A -> B) (t : A -> Prop) (s : A -> Prop) (h1 : term57 A B f t s) : term119 A B s f _35382.
Proof. exact (EQ_MP (@lem3378618 A B s f _35382) (@lem3378617 A B _35382 f t s h1)). Qed.
Lemma lem3378620 {A B : Type'} (_35382 : A) (_35383 : A) (f : A -> B) (t : A -> Prop) (s : A -> Prop) (h1 : term57 A B f t s) : term283 A B s f _35382 _35383.
Proof. exact (@lem3378619 A B _35382 f t s h1 _35383). Qed.
Lemma lem3378621 {A B : Type'} (s : A -> Prop) (f : A -> B) (_35382 : A) (_35383 : A) : (term283 A B s f _35382 _35383) = (term117 A B s f _35382 _35383).
Proof. exact (eq_refl (term283 A B s f _35382 _35383)). Qed.
Lemma lem3378622 {A B : Type'} (_35382 : A) (_35383 : A) (f : A -> B) (t : A -> Prop) (s : A -> Prop) (h1 : term57 A B f t s) : term117 A B s f _35382 _35383.
Proof. exact (EQ_MP (@lem3378621 A B s f _35382 _35383) (@lem3378620 A B _35382 _35383 f t s h1)). Qed.
Lemma lem3378623 {A B : Type'} (_35384 : A) (f : A -> B) (t : A -> Prop) (s : A -> Prop) (h1 : term57 A B f t s) : term284 A t s _35384.
Proof. exact (@lem3378503 A B f t s h1 _35384). Qed.
Lemma lem3378624 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_35384 : A) : (term284 A t s _35384) = (term122 A t s _35384).
Proof. exact (eq_refl (term284 A t s _35384)). Qed.
Lemma lem3378635 {A B : Type'} (_35388 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term237 A B s x' x f t) : term285 A B x f s t _35388.
Proof. exact (@lem3378583 A B s x' x f t h1 _35388). Qed.
Lemma lem3378636 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_35388 : A) : (term285 A B x f s t _35388) = (term132 A B x f s t _35388).
Proof. exact (eq_refl (term285 A B x f s t _35388)). Qed.
Lemma lem3378638 {A B : Type'} (_35389 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term237 A B s x' x f t) : term281 A B x f t _35389.
Proof. exact (@lem3378596 A B s x' x f t h1 _35389). Qed.
Lemma lem3378639 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (_35389 : A) : (term281 A B x f t _35389) = (term144 A B x f t _35389).
Proof. exact (eq_refl (term281 A B x f t _35389)). Qed.
Lemma lem3378666 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term209 A B x' s x f t x'') : x = (f x').
Proof. exact (proj1 (@lem3378382 A B x' s x f t x'' h1)). Qed.
Lemma lem3378676 {A B : Type'} (_35381 : A) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term150 A B x f s) : term144 A B x f s _35381.
Proof. exact (EQ_MP (@lem3378615 A B x f s _35381) (@lem3378614 A B _35381 x f s h1)). Qed.
Lemma lem3378680 {A B : Type'} (s : A -> Prop) (f : A -> B) (_35382 : A) (_35383 : A) : (term117 A B s f _35382 _35383) = (term286 A B s f _35382 _35383).
Proof. exact (@lem3376788 (term66 A s _35382) (term109 A B s _35382 f _35383) (_35382 = _35383)). Qed.
Lemma lem3378687 {A B : Type'} (s : A -> Prop) (f : A -> B) (_35382 : A) (_35383 : A) : (term287 A B s f _35382 _35383) = (term288 A B s f _35382 _35383).
Proof. exact (@lem3376788 (term66 A s _35383) (term289 A B _35382 f _35383) (_35382 = _35383)). Qed.
Lemma lem3378688 {A : Type'} (s : A -> Prop) (_35382 : A) : (term110 A s _35382) = (term110 A s _35382).
Proof. exact (eq_refl (term110 A s _35382)). Qed.
Lemma lem3378691 {A B : Type'} (s : A -> Prop) (f : A -> B) (_35382 : A) (_35383 : A) : (term286 A B s f _35382 _35383) = (term290 A B s f _35382 _35383).
Proof. exact (MK_COMB (@lem3378688 A s _35382) (@lem3378687 A B s f _35382 _35383)). Qed.
Lemma lem3378693 {A B : Type'} (s : A -> Prop) (f : A -> B) (_35382 : A) (_35383 : A) : (term117 A B s f _35382 _35383) = (term290 A B s f _35382 _35383).
Proof. exact (TRANS (@lem3378680 A B s f _35382 _35383) (@lem3378691 A B s f _35382 _35383)). Qed.
Lemma lem3378702 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term209 A B x' s x f t x'') : x = (f x').
Proof. exact (proj1 (@lem3378382 A B x' s x f t x'' h1)). Qed.
Lemma lem3378708 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term79 A B x f t x'') : x = (f x'').
Proof. exact (proj1 (@lem3378388 A B x f t x'' h1)). Qed.
Lemma lem3378744 {A B : Type'} (_35388 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term237 A B s x' x f t) : term132 A B x f s t _35388.
Proof. exact (EQ_MP (@lem3378636 A B x f s t _35388) (@lem3378635 A B _35388 s x' x f t h1)). Qed.
Lemma lem3378750 {A B : Type'} (_35389 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term237 A B s x' x f t) : term144 A B x f t _35389.
Proof. exact (EQ_MP (@lem3378639 A B x f t _35389) (@lem3378638 A B _35389 s x' x f t h1)). Qed.
Lemma lem3378752 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term237 A B s x' x f t) : x = (f x').
Proof. exact (proj1 (@lem3378394 A B s x' x f t h1)). Qed.
Lemma lem3378825 {A B : Type'} (f : A -> B) (s : A -> Prop) (_35381 : A) : (term291 A B f s _35381) = (term291 A B f s _35381).
Proof. exact (eq_refl (term291 A B f s _35381)). Qed.
Lemma lem3378826 {A B : Type'} (_35381 : A) (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term209 A B x' s x f t x'') : (term292 A B f s _35381 x) = (term293 A B s _35381 f x').
Proof. exact (MK_COMB (@lem3378825 A B f s _35381) (@lem3378666 A B x' s x f t x'' h1)). Qed.
Lemma lem3378827 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_35381 : A) : (term293 A B s _35381 f x') = (term294 A B x' f s _35381).
Proof. exact (eq_refl (term293 A B s _35381 f x')). Qed.
Lemma lem3378828 {A B : Type'} (f : A -> B) (s : A -> Prop) (_35381 : A) (x : B) : (term295 A B f s _35381 x) = (term295 A B f s _35381 x).
Proof. exact (eq_refl (term295 A B f s _35381 x)). Qed.
Lemma lem3378829 {A B : Type'} (x : B) (x' : A) (f : A -> B) (s : A -> Prop) (_35381 : A) : ((term292 A B f s _35381 x) = (term293 A B s _35381 f x')) = ((term292 A B f s _35381 x) = (term294 A B x' f s _35381)).
Proof. exact (MK_COMB (@lem3378828 A B f s _35381 x) (@lem3378827 A B x' f s _35381)). Qed.
Lemma lem3378830 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (_35381 : A) : (term292 A B f s _35381 x) = (term144 A B x f s _35381).
Proof. exact (eq_refl (term292 A B f s _35381 x)). Qed.
Lemma lem3378831 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3378832 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (_35381 : A) : (term295 A B f s _35381 x) = (term296 A B x f s _35381).
Proof. exact (MK_COMB (@lem3378831) (@lem3378830 A B x f s _35381)). Qed.
Lemma lem3378833 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_35381 : A) : (term294 A B x' f s _35381) = (term294 A B x' f s _35381).
Proof. exact (eq_refl (term294 A B x' f s _35381)). Qed.
Lemma lem3378834 {A B : Type'} (x : B) (x' : A) (f : A -> B) (s : A -> Prop) (_35381 : A) : ((term292 A B f s _35381 x) = (term294 A B x' f s _35381)) = ((term144 A B x f s _35381) = (term294 A B x' f s _35381)).
Proof. exact (MK_COMB (@lem3378832 A B x f s _35381) (@lem3378833 A B x' f s _35381)). Qed.
Lemma lem3378835 {A B : Type'} (x : B) (x' : A) (f : A -> B) (s : A -> Prop) (_35381 : A) : ((term292 A B f s _35381 x) = (term293 A B s _35381 f x')) = ((term144 A B x f s _35381) = (term294 A B x' f s _35381)).
Proof. exact (TRANS (@lem3378829 A B x x' f s _35381) (@lem3378834 A B x x' f s _35381)). Qed.
Lemma lem3378836 {A B : Type'} (_35381 : A) (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term209 A B x' s x f t x'') : (term144 A B x f s _35381) = (term294 A B x' f s _35381).
Proof. exact (EQ_MP (@lem3378835 A B x x' f s _35381) (@lem3378826 A B _35381 x' s x f t x'' h1)). Qed.
Lemma lem3378837 {A B : Type'} (_35381 : A) (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term150 A B x f s) (h2 : term209 A B x' s x f t x'') : term294 A B x' f s _35381.
Proof. exact (EQ_MP (@lem3378836 A B _35381 x' s x f t x'' h2) (@lem3378676 A B _35381 x f s h1)). Qed.
Lemma lem3378865 {A B : Type'} (_35382 : A) (_35383 : A) (f : A -> B) (t : A -> Prop) (s : A -> Prop) (h1 : term57 A B f t s) : term290 A B s f _35382 _35383.
Proof. exact (EQ_MP (@lem3378693 A B s f _35382 _35383) (@lem3378622 A B _35382 _35383 f t s h1)). Qed.
Lemma lem3378879 {A B : Type'} (_35384 : A) (f : A -> B) (t : A -> Prop) (s : A -> Prop) (h1 : term57 A B f t s) : term122 A t s _35384.
Proof. exact (EQ_MP (@lem3378624 A t s _35384) (@lem3378623 A B _35384 f t s h1)). Qed.
Lemma lem3378880 {A B : Type'} (f : A -> B) (x' : A) : (term297 A B f x') = (term297 A B f x').
Proof. exact (eq_refl (term297 A B f x')). Qed.
Lemma lem3378881 {A B : Type'} (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term79 A B x f t x'') : (term298 A B f x' x) = (term299 A B x' f x'').
Proof. exact (MK_COMB (@lem3378880 A B f x') (@lem3378708 A B x f t x'' h1)). Qed.
Lemma lem3378882 {A B : Type'} (x'' : A) (f : A -> B) (x' : A) : (term299 A B x' f x'') = ((f x'') = (f x')).
Proof. exact (eq_refl (term299 A B x' f x'')). Qed.
Lemma lem3378883 {A B : Type'} (f : A -> B) (x' : A) (x : B) : (term300 A B f x' x) = (term300 A B f x' x).
Proof. exact (eq_refl (term300 A B f x' x)). Qed.
Lemma lem3378884 {A B : Type'} (x : B) (x'' : A) (f : A -> B) (x' : A) : ((term298 A B f x' x) = (term299 A B x' f x'')) = ((term298 A B f x' x) = ((f x'') = (f x'))).
Proof. exact (MK_COMB (@lem3378883 A B f x' x) (@lem3378882 A B x'' f x')). Qed.
Lemma lem3378885 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term298 A B f x' x) = (x = (f x')).
Proof. exact (eq_refl (term298 A B f x' x)). Qed.
Lemma lem3378886 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3378887 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term300 A B f x' x) = (term301 A B x f x').
Proof. exact (MK_COMB (@lem3378886) (@lem3378885 A B x f x')). Qed.
Lemma lem3378888 {A B : Type'} (x'' : A) (f : A -> B) (x' : A) : ((f x'') = (f x')) = ((f x'') = (f x')).
Proof. exact (eq_refl ((f x'') = (f x'))). Qed.
Lemma lem3378889 {A B : Type'} (x : B) (x'' : A) (f : A -> B) (x' : A) : ((term298 A B f x' x) = ((f x'') = (f x'))) = ((x = (f x')) = ((f x'') = (f x'))).
Proof. exact (MK_COMB (@lem3378887 A B x f x') (@lem3378888 A B x'' f x')). Qed.
Lemma lem3378890 {A B : Type'} (x : B) (x'' : A) (f : A -> B) (x' : A) : ((term298 A B f x' x) = (term299 A B x' f x'')) = ((x = (f x')) = ((f x'') = (f x'))).
Proof. exact (TRANS (@lem3378884 A B x x'' f x') (@lem3378889 A B x x'' f x')). Qed.
Lemma lem3378891 {A B : Type'} (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term79 A B x f t x'') : (x = (f x')) = ((f x'') = (f x')).
Proof. exact (EQ_MP (@lem3378890 A B x x'' f x') (@lem3378881 A B x' x f t x'' h1)). Qed.
Lemma lem3378920 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term209 A B x' s x f t x'') : term66 A t x'.
Proof. exact (proj2 (@lem3378383 A B x' s x f t x'' h1)). Qed.
Lemma lem3378977 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_35388 : A) : (term302 A B f s t _35388) = (term302 A B f s t _35388).
Proof. exact (eq_refl (term302 A B f s t _35388)). Qed.
Lemma lem3378978 {A B : Type'} (_35388 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term237 A B s x' x f t) : (term303 A B f s t _35388 x) = (term304 A B s t _35388 f x').
Proof. exact (MK_COMB (@lem3378977 A B f s t _35388) (@lem3378752 A B s x' x f t h1)). Qed.
Lemma lem3378979 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_35388 : A) : (term304 A B s t _35388 f x') = (term305 A B x' f s t _35388).
Proof. exact (eq_refl (term304 A B s t _35388 f x')). Qed.
Lemma lem3378980 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_35388 : A) (x : B) : (term306 A B f s t _35388 x) = (term306 A B f s t _35388 x).
Proof. exact (eq_refl (term306 A B f s t _35388 x)). Qed.
Lemma lem3378981 {A B : Type'} (x : B) (x' : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_35388 : A) : ((term303 A B f s t _35388 x) = (term304 A B s t _35388 f x')) = ((term303 A B f s t _35388 x) = (term305 A B x' f s t _35388)).
Proof. exact (MK_COMB (@lem3378980 A B f s t _35388 x) (@lem3378979 A B x' f s t _35388)). Qed.
Lemma lem3378982 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_35388 : A) : (term303 A B f s t _35388 x) = (term132 A B x f s t _35388).
Proof. exact (eq_refl (term303 A B f s t _35388 x)). Qed.
Lemma lem3378983 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3378984 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_35388 : A) : (term306 A B f s t _35388 x) = (term307 A B x f s t _35388).
Proof. exact (MK_COMB (@lem3378983) (@lem3378982 A B x f s t _35388)). Qed.
Lemma lem3378985 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_35388 : A) : (term305 A B x' f s t _35388) = (term305 A B x' f s t _35388).
Proof. exact (eq_refl (term305 A B x' f s t _35388)). Qed.
Lemma lem3378986 {A B : Type'} (x : B) (x' : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_35388 : A) : ((term303 A B f s t _35388 x) = (term305 A B x' f s t _35388)) = ((term132 A B x f s t _35388) = (term305 A B x' f s t _35388)).
Proof. exact (MK_COMB (@lem3378984 A B x f s t _35388) (@lem3378985 A B x' f s t _35388)). Qed.
Lemma lem3378987 {A B : Type'} (x : B) (x' : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_35388 : A) : ((term303 A B f s t _35388 x) = (term304 A B s t _35388 f x')) = ((term132 A B x f s t _35388) = (term305 A B x' f s t _35388)).
Proof. exact (TRANS (@lem3378981 A B x x' f s t _35388) (@lem3378986 A B x x' f s t _35388)). Qed.
Lemma lem3378988 {A B : Type'} (_35388 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term237 A B s x' x f t) : (term132 A B x f s t _35388) = (term305 A B x' f s t _35388).
Proof. exact (EQ_MP (@lem3378987 A B x x' f s t _35388) (@lem3378978 A B _35388 s x' x f t h1)). Qed.
Lemma lem3378989 {A B : Type'} (_35388 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term237 A B s x' x f t) : term305 A B x' f s t _35388.
Proof. exact (EQ_MP (@lem3378988 A B _35388 s x' x f t h1) (@lem3378744 A B _35388 s x' x f t h1)). Qed.
Lemma lem3378990 {A B : Type'} (f : A -> B) (t : A -> Prop) (_35389 : A) : (term291 A B f t _35389) = (term291 A B f t _35389).
Proof. exact (eq_refl (term291 A B f t _35389)). Qed.
Lemma lem3378991 {A B : Type'} (_35389 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term237 A B s x' x f t) : (term292 A B f t _35389 x) = (term293 A B t _35389 f x').
Proof. exact (MK_COMB (@lem3378990 A B f t _35389) (@lem3378752 A B s x' x f t h1)). Qed.
Lemma lem3378992 {A B : Type'} (x' : A) (f : A -> B) (t : A -> Prop) (_35389 : A) : (term293 A B t _35389 f x') = (term294 A B x' f t _35389).
Proof. exact (eq_refl (term293 A B t _35389 f x')). Qed.
Lemma lem3378993 {A B : Type'} (f : A -> B) (t : A -> Prop) (_35389 : A) (x : B) : (term295 A B f t _35389 x) = (term295 A B f t _35389 x).
Proof. exact (eq_refl (term295 A B f t _35389 x)). Qed.
Lemma lem3378994 {A B : Type'} (x : B) (x' : A) (f : A -> B) (t : A -> Prop) (_35389 : A) : ((term292 A B f t _35389 x) = (term293 A B t _35389 f x')) = ((term292 A B f t _35389 x) = (term294 A B x' f t _35389)).
Proof. exact (MK_COMB (@lem3378993 A B f t _35389 x) (@lem3378992 A B x' f t _35389)). Qed.
Lemma lem3378995 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (_35389 : A) : (term292 A B f t _35389 x) = (term144 A B x f t _35389).
Proof. exact (eq_refl (term292 A B f t _35389 x)). Qed.
Lemma lem3378996 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3378997 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (_35389 : A) : (term295 A B f t _35389 x) = (term296 A B x f t _35389).
Proof. exact (MK_COMB (@lem3378996) (@lem3378995 A B x f t _35389)). Qed.
Lemma lem3378998 {A B : Type'} (x' : A) (f : A -> B) (t : A -> Prop) (_35389 : A) : (term294 A B x' f t _35389) = (term294 A B x' f t _35389).
Proof. exact (eq_refl (term294 A B x' f t _35389)). Qed.
Lemma lem3378999 {A B : Type'} (x : B) (x' : A) (f : A -> B) (t : A -> Prop) (_35389 : A) : ((term292 A B f t _35389 x) = (term294 A B x' f t _35389)) = ((term144 A B x f t _35389) = (term294 A B x' f t _35389)).
Proof. exact (MK_COMB (@lem3378997 A B x f t _35389) (@lem3378998 A B x' f t _35389)). Qed.
Lemma lem3379000 {A B : Type'} (x : B) (x' : A) (f : A -> B) (t : A -> Prop) (_35389 : A) : ((term292 A B f t _35389 x) = (term293 A B t _35389 f x')) = ((term144 A B x f t _35389) = (term294 A B x' f t _35389)).
Proof. exact (TRANS (@lem3378994 A B x x' f t _35389) (@lem3378999 A B x x' f t _35389)). Qed.
Lemma lem3379001 {A B : Type'} (_35389 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term237 A B s x' x f t) : (term144 A B x f t _35389) = (term294 A B x' f t _35389).
Proof. exact (EQ_MP (@lem3379000 A B x x' f t _35389) (@lem3378991 A B _35389 s x' x f t h1)). Qed.
Lemma lem3379002 {A B : Type'} (_35389 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term237 A B s x' x f t) : term294 A B x' f t _35389.
Proof. exact (EQ_MP (@lem3379001 A B _35389 s x' x f t h1) (@lem3378750 A B _35389 s x' x f t h1)). Qed.
Lemma lem3379054 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem3379055 {B : Type'} (x : B) : x = x.
Proof. exact (@lem3379054 B x). Qed.
Lemma lem3379056 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (f x').
Proof. exact (@lem3379055 B (f x')). Qed.
Lemma lem3379057 {A B : Type'} (f : A -> B) (x' : A) : term308 A B f x'.
Proof. exact (fun h0 : term309 A B f x' => @lem3379056 A B f x'). Qed.
Lemma lem3379059 (p : Prop) : (term310 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3379060 {A B : Type'} (f : A -> B) (x' : A) : (term308 A B f x') = ((f x') = (f x')).
Proof. exact (@lem3379059 ((f x') = (f x'))). Qed.
Lemma lem3379061 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (f x').
Proof. exact (EQ_MP (@lem3379060 A B f x') (@lem3379057 A B f x')). Qed.
Lemma lem3379063 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term209 A B x' s x f t x'') : s x'.
Proof. exact (proj1 (@lem3378383 A B x' s x f t x'' h1)). Qed.
Lemma lem3379064 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term209 A B x' s x f t x'') : term311 A s x'.
Proof. exact (fun h0 : term66 A s x' => @lem3379063 A B x' s x f t x'' h1). Qed.
Lemma lem3379066 (p : Prop) : (term310 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3379067 {A : Type'} (s : A -> Prop) (x' : A) : (term311 A s x') = (s x').
Proof. exact (@lem3379066 (s x')). Qed.
Lemma lem3379068 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term209 A B x' s x f t x'') : s x'.
Proof. exact (EQ_MP (@lem3379067 A s x') (@lem3379064 A B x' s x f t x'' h1)). Qed.
Lemma lem3379070 (a : Prop) (b : Prop) : (term312 a b) = (term313 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3379071 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_35381 : A) : (term294 A B x' f s _35381) = (term314 A B x' f s _35381).
Proof. exact (@lem3379070 ((f x') = (f _35381)) (s _35381)). Qed.
Lemma lem3379073 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3379074 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_35381 : A) : (term314 A B x' f s _35381) = (term315 A B x' f s _35381).
Proof. exact (@lem3379073 (term316 A B x' f s _35381)). Qed.
Lemma lem3379075 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_35381 : A) : (term294 A B x' f s _35381) = (term315 A B x' f s _35381).
Proof. exact (TRANS (@lem3379071 A B x' f s _35381) (@lem3379074 A B x' f s _35381)). Qed.
Lemma lem3379077 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term209 A B x' s x f t x'') : term317 A B f s x'.
Proof. exact (conj (@lem3379061 A B f x') (@lem3379068 A B x' s x f t x'' h1)). Qed.
Lemma lem3379079 {A B : Type'} (_35381 : A) (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term150 A B x f s) (h2 : term209 A B x' s x f t x'') : term315 A B x' f s _35381.
Proof. exact (EQ_MP (@lem3379075 A B x' f s _35381) (@lem3378837 A B _35381 x' s x f t x'' h1 h2)). Qed.
Lemma lem3379080 {A B : Type'} (_35381 : A) (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term150 A B x f s) (h2 : term209 A B x' s x f t x'') : term315 A B x' f s _35381.
Proof. exact (@lem3379079 A B _35381 x' s x f t x'' h1 h2). Qed.
Lemma lem3379081 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term150 A B x f s) (h2 : term209 A B x' s x f t x'') : term318 A B f s x'.
Proof. exact (@lem3379080 A B x' x' s x f t x'' h1 h2). Qed.
Lemma lem3379084 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term150 A B x f s) (h2 : term209 A B x' s x f t x'') : False.
Proof. exact (@lem3379081 A B x' s x f t x'' h1 h2 (@lem3379077 A B x' s x f t x'' h2)). Qed.
Lemma lem3379085 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term150 A B x f s) (h2 : term209 A B x' s x f t x'') : term319.
Proof. exact (fun h0 : ~ False => @lem3379084 A B x' s x f t x'' h1 h2). Qed.
Lemma lem3379087 (p : Prop) : (term310 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3379088 : term319 = False.
Proof. exact (@lem3379087 False). Qed.
Lemma lem3379090 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem3379091 {A : Type'} (_35434 : A) (_35435 : A) (h1 : _35434 = _35435) : _35434 = _35435.
Proof. exact (h1). Qed.
Lemma lem3379092 {A : Type'} (t : A -> Prop) (_35434 : A) (_35435 : A) (h1 : _35434 = _35435) : (t _35434) = (t _35435).
Proof. exact (MK_COMB (@lem3379090 A t) (@lem3379091 A _35434 _35435 h1)). Qed.
Lemma lem3379094 (b : Prop) (a : Prop) : term320 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem3379095 {A : Type'} (_35435 : A) (t : A -> Prop) (_35434 : A) : term321 A _35435 t _35434.
Proof. exact (@lem3379094 (t _35435) (t _35434)). Qed.
Lemma lem3379096 {A : Type'} (t : A -> Prop) (_35434 : A) (_35435 : A) (h1 : _35434 = _35435) : term322 A _35435 t _35434.
Proof. exact (@lem3379095 A _35435 t _35434 (@lem3379092 A t _35434 _35435 h1)). Qed.
Lemma lem3379097 {A : Type'} (_35435 : A) (t : A -> Prop) (_35434 : A) : term323 A _35435 t _35434.
Proof. exact (fun h0 : _35434 = _35435 => @lem3379096 A t _35434 _35435 h0). Qed.
Lemma lem3379099 (a : Prop) (b : Prop) : (a -> b) = (term324 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem3379100 {A : Type'} (_35435 : A) (t : A -> Prop) (_35434 : A) : (term323 A _35435 t _35434) = (term325 A _35435 t _35434).
Proof. exact (@lem3379099 (_35434 = _35435) (term322 A _35435 t _35434)). Qed.
Lemma lem3379101 {A : Type'} (_35435 : A) (t : A -> Prop) (_35434 : A) : term325 A _35435 t _35434.
Proof. exact (EQ_MP (@lem3379100 A _35435 t _35434) (@lem3379097 A _35435 t _35434)). Qed.
Lemma lem3379127 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term79 A B x f t x'') : t x''.
Proof. exact (proj2 (@lem3378388 A B x f t x'' h1)). Qed.
Lemma lem3379128 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term79 A B x f t x'') : term311 A t x''.
Proof. exact (fun h0 : term66 A t x'' => @lem3379127 A B x f t x'' h1). Qed.
Lemma lem3379130 (p : Prop) : (term310 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3379131 {A : Type'} (t : A -> Prop) (x'' : A) : (term311 A t x'') = (t x'').
Proof. exact (@lem3379130 (t x'')). Qed.
Lemma lem3379132 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term79 A B x f t x'') : t x''.
Proof. exact (EQ_MP (@lem3379131 A t x'') (@lem3379128 A B x f t x'' h1)). Qed.
Lemma lem3379138 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3379139 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_35384 : A) : (term122 A t s _35384) = (term326 A s t _35384).
Proof. exact (@lem3379138 (s _35384) (term66 A t _35384)). Qed.
Lemma lem3379145 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3379146 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_35384 : A) : (term327 A t s _35384) = (term328 A s t _35384).
Proof. exact (MK_COMB (@lem3379145) (@lem3379139 A s t _35384)). Qed.
Lemma lem3379152 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_35384 : A) : (term326 A s t _35384) = (term326 A s t _35384).
Proof. exact (eq_refl (term326 A s t _35384)). Qed.
Lemma lem3379153 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_35384 : A) : ((term122 A t s _35384) = (term326 A s t _35384)) = ((term326 A s t _35384) = (term326 A s t _35384)).
Proof. exact (MK_COMB (@lem3379146 A s t _35384) (@lem3379152 A s t _35384)). Qed.
Lemma lem3379155 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3379156 (x : Prop) : (x = x) = True.
Proof. exact (@lem3379155 Prop x). Qed.
Lemma lem3379157 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_35384 : A) : ((term326 A s t _35384) = (term326 A s t _35384)) = True.
Proof. exact (@lem3379156 (term326 A s t _35384)). Qed.
Lemma lem3379158 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_35384 : A) : ((term122 A t s _35384) = (term326 A s t _35384)) = True.
Proof. exact (TRANS (@lem3379153 A s t _35384) (@lem3379157 A s t _35384)). Qed.
Lemma lem3379159 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_35384 : A) : True = ((term122 A t s _35384) = (term326 A s t _35384)).
Proof. exact (SYM (@lem3379158 A s t _35384)). Qed.
Lemma lem3379160 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_35384 : A) : (term122 A t s _35384) = (term326 A s t _35384).
Proof. exact (EQ_MP (@lem3379159 A s t _35384) (@lem0)). Qed.
Lemma lem3379161 {A B : Type'} (_35384 : A) (f : A -> B) (t : A -> Prop) (s : A -> Prop) (h1 : term57 A B f t s) : term326 A s t _35384.
Proof. exact (EQ_MP (@lem3379160 A s t _35384) (@lem3378879 A B _35384 f t s h1)). Qed.
Lemma lem3379163 (b : Prop) (a : Prop) : (a \/ b) = (term329 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3379164 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_35384 : A) : (term326 A s t _35384) = (term330 A t s _35384).
Proof. exact (@lem3379163 (term66 A t _35384) (s _35384)). Qed.
Lemma lem3379166 (a : Prop) : (term105 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3379167 {A : Type'} (t : A -> Prop) (_35384 : A) : (term127 A t _35384) = (t _35384).
Proof. exact (@lem3379166 (t _35384)). Qed.
Lemma lem3379168 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3379169 {A : Type'} (t : A -> Prop) (_35384 : A) : (term331 A t _35384) = (term51 A t _35384).
Proof. exact (MK_COMB (@lem3379168) (@lem3379167 A t _35384)). Qed.
Lemma lem3379170 {A : Type'} (s : A -> Prop) (_35384 : A) : (s _35384) = (s _35384).
Proof. exact (eq_refl (s _35384)). Qed.
Lemma lem3379171 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_35384 : A) : (term330 A t s _35384) = (term53 A t s _35384).
Proof. exact (MK_COMB (@lem3379169 A t _35384) (@lem3379170 A s _35384)). Qed.
Lemma lem3379172 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_35384 : A) : (term326 A s t _35384) = (term53 A t s _35384).
Proof. exact (TRANS (@lem3379164 A t s _35384) (@lem3379171 A t s _35384)). Qed.
Lemma lem3379175 {A B : Type'} (_35384 : A) (f : A -> B) (t : A -> Prop) (s : A -> Prop) (h1 : term57 A B f t s) : term53 A t s _35384.
Proof. exact (EQ_MP (@lem3379172 A t s _35384) (@lem3379161 A B _35384 f t s h1)). Qed.
Lemma lem3379176 {A B : Type'} (_35384 : A) (f : A -> B) (t : A -> Prop) (s : A -> Prop) (h1 : term57 A B f t s) : term53 A t s _35384.
Proof. exact (@lem3379175 A B _35384 f t s h1). Qed.
Lemma lem3379177 {A B : Type'} (x'' : A) (f : A -> B) (t : A -> Prop) (s : A -> Prop) (h1 : term57 A B f t s) : term53 A t s x''.
Proof. exact (@lem3379176 A B x'' f t s h1). Qed.
Lemma lem3379180 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term57 A B f t s) (h2 : term79 A B x f t x'') : s x''.
Proof. exact (@lem3379177 A B x'' f t s h1 (@lem3379132 A B x f t x'' h2)). Qed.
Lemma lem3379181 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term57 A B f t s) (h2 : term79 A B x f t x'') : term311 A s x''.
Proof. exact (fun h0 : term66 A s x'' => @lem3379180 A B s x f t x'' h1 h2). Qed.
Lemma lem3379183 (p : Prop) : (term310 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3379184 {A : Type'} (s : A -> Prop) (x'' : A) : (term311 A s x'') = (s x'').
Proof. exact (@lem3379183 (s x'')). Qed.
Lemma lem3379185 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term57 A B f t s) (h2 : term79 A B x f t x'') : s x''.
Proof. exact (EQ_MP (@lem3379184 A s x'') (@lem3379181 A B s x f t x'' h1 h2)). Qed.
Lemma lem3379187 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term209 A B x' s x f t x'') : s x'.
Proof. exact (proj1 (@lem3378383 A B x' s x f t x'' h1)). Qed.
Lemma lem3379188 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term209 A B x' s x f t x'') : term311 A s x'.
Proof. exact (fun h0 : term66 A s x' => @lem3379187 A B x' s x f t x'' h1). Qed.
Lemma lem3379190 (p : Prop) : (term310 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3379191 {A : Type'} (s : A -> Prop) (x' : A) : (term311 A s x') = (s x').
Proof. exact (@lem3379190 (s x')). Qed.
Lemma lem3379192 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term209 A B x' s x f t x'') : s x'.
Proof. exact (EQ_MP (@lem3379191 A s x') (@lem3379188 A B x' s x f t x'' h1)). Qed.
Lemma lem3379194 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term209 A B x' s x f t x'') (h2 : term79 A B x f t x'') : (f x'') = (f x').
Proof. exact (EQ_MP (@lem3378891 A B x' x f t x'' h2) (@lem3378702 A B x' s x f t x'' h1)). Qed.
Lemma lem3379195 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term209 A B x' s x f t x'') (h2 : term79 A B x f t x'') : term332 A B x'' f x'.
Proof. exact (fun h0 : term289 A B x'' f x' => @lem3379194 A B x' s x f t x'' h1 h2). Qed.
Lemma lem3379197 (p : Prop) : (term310 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3379198 {A B : Type'} (x'' : A) (f : A -> B) (x' : A) : (term332 A B x'' f x') = ((f x'') = (f x')).
Proof. exact (@lem3379197 ((f x'') = (f x'))). Qed.
Lemma lem3379199 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term209 A B x' s x f t x'') (h2 : term79 A B x f t x'') : (f x'') = (f x').
Proof. exact (EQ_MP (@lem3379198 A B x'' f x') (@lem3379195 A B x' s x f t x'' h1 h2)). Qed.
Lemma lem3379225 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3379226 {A B : Type'} (_35382 : A) (f : A -> B) (_35383 : A) : (term333 A B f _35382 _35383) = (term334 A B _35382 f _35383).
Proof. exact (@lem3379225 (_35382 = _35383) (term289 A B _35382 f _35383)). Qed.
Lemma lem3379236 {A : Type'} (s : A -> Prop) (_35383 : A) : (term110 A s _35383) = (term110 A s _35383).
Proof. exact (eq_refl (term110 A s _35383)). Qed.
Lemma lem3379237 {A B : Type'} (s : A -> Prop) (_35382 : A) (f : A -> B) (_35383 : A) : (term288 A B s f _35382 _35383) = (term335 A B s _35382 f _35383).
Proof. exact (MK_COMB (@lem3379236 A s _35383) (@lem3379226 A B _35382 f _35383)). Qed.
Lemma lem3379241 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3379242 {A B : Type'} (s : A -> Prop) (_35382 : A) (f : A -> B) (_35383 : A) : (term335 A B s _35382 f _35383) = (term336 A B s _35382 f _35383).
Proof. exact (@lem3379241 (_35382 = _35383) (term66 A s _35383) (term289 A B _35382 f _35383)). Qed.
Lemma lem3379262 {A B : Type'} (s : A -> Prop) (_35382 : A) (f : A -> B) (_35383 : A) : (term288 A B s f _35382 _35383) = (term336 A B s _35382 f _35383).
Proof. exact (TRANS (@lem3379237 A B s _35382 f _35383) (@lem3379242 A B s _35382 f _35383)). Qed.
Lemma lem3379263 {A : Type'} (s : A -> Prop) (_35382 : A) : (term110 A s _35382) = (term110 A s _35382).
Proof. exact (eq_refl (term110 A s _35382)). Qed.
Lemma lem3379264 {A B : Type'} (s : A -> Prop) (_35382 : A) (f : A -> B) (_35383 : A) : (term290 A B s f _35382 _35383) = (term337 A B s _35382 f _35383).
Proof. exact (MK_COMB (@lem3379263 A s _35382) (@lem3379262 A B s _35382 f _35383)). Qed.
Lemma lem3379268 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3379269 {A B : Type'} (s : A -> Prop) (_35382 : A) (f : A -> B) (_35383 : A) : (term337 A B s _35382 f _35383) = (term338 A B s _35382 f _35383).
Proof. exact (@lem3379268 (_35382 = _35383) (term66 A s _35382) (term109 A B s _35382 f _35383)). Qed.
Lemma lem3379299 {A B : Type'} (s : A -> Prop) (_35382 : A) (f : A -> B) (_35383 : A) : (term290 A B s f _35382 _35383) = (term338 A B s _35382 f _35383).
Proof. exact (TRANS (@lem3379264 A B s _35382 f _35383) (@lem3379269 A B s _35382 f _35383)). Qed.
Lemma lem3379300 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3379301 {A B : Type'} (s : A -> Prop) (_35382 : A) (f : A -> B) (_35383 : A) : (term339 A B s f _35382 _35383) = (term340 A B s _35382 f _35383).
Proof. exact (MK_COMB (@lem3379300) (@lem3379299 A B s _35382 f _35383)). Qed.
Lemma lem3379331 {A B : Type'} (s : A -> Prop) (_35382 : A) (f : A -> B) (_35383 : A) : (term338 A B s _35382 f _35383) = (term338 A B s _35382 f _35383).
Proof. exact (eq_refl (term338 A B s _35382 f _35383)). Qed.
Lemma lem3379332 {A B : Type'} (s : A -> Prop) (_35382 : A) (f : A -> B) (_35383 : A) : ((term290 A B s f _35382 _35383) = (term338 A B s _35382 f _35383)) = ((term338 A B s _35382 f _35383) = (term338 A B s _35382 f _35383)).
Proof. exact (MK_COMB (@lem3379301 A B s _35382 f _35383) (@lem3379331 A B s _35382 f _35383)). Qed.
Lemma lem3379334 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3379335 (x : Prop) : (x = x) = True.
Proof. exact (@lem3379334 Prop x). Qed.
Lemma lem3379336 {A B : Type'} (s : A -> Prop) (_35382 : A) (f : A -> B) (_35383 : A) : ((term338 A B s _35382 f _35383) = (term338 A B s _35382 f _35383)) = True.
Proof. exact (@lem3379335 (term338 A B s _35382 f _35383)). Qed.
Lemma lem3379337 {A B : Type'} (s : A -> Prop) (_35382 : A) (f : A -> B) (_35383 : A) : ((term290 A B s f _35382 _35383) = (term338 A B s _35382 f _35383)) = True.
Proof. exact (TRANS (@lem3379332 A B s _35382 f _35383) (@lem3379336 A B s _35382 f _35383)). Qed.
Lemma lem3379338 {A B : Type'} (s : A -> Prop) (_35382 : A) (f : A -> B) (_35383 : A) : True = ((term290 A B s f _35382 _35383) = (term338 A B s _35382 f _35383)).
Proof. exact (SYM (@lem3379337 A B s _35382 f _35383)). Qed.
Lemma lem3379339 {A B : Type'} (s : A -> Prop) (_35382 : A) (f : A -> B) (_35383 : A) : (term290 A B s f _35382 _35383) = (term338 A B s _35382 f _35383).
Proof. exact (EQ_MP (@lem3379338 A B s _35382 f _35383) (@lem0)). Qed.
Lemma lem3379340 {A B : Type'} (_35382 : A) (_35383 : A) (f : A -> B) (t : A -> Prop) (s : A -> Prop) (h1 : term57 A B f t s) : term338 A B s _35382 f _35383.
Proof. exact (EQ_MP (@lem3379339 A B s _35382 f _35383) (@lem3378865 A B _35382 _35383 f t s h1)). Qed.
Lemma lem3379342 (b : Prop) (a : Prop) : (a \/ b) = (term329 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3379343 {A B : Type'} (s : A -> Prop) (f : A -> B) (_35382 : A) (_35383 : A) : (term338 A B s _35382 f _35383) = (term341 A B s f _35382 _35383).
Proof. exact (@lem3379342 (term112 A B s _35382 f _35383) (_35382 = _35383)). Qed.
Lemma lem3379345 (a : Prop) (b : Prop) : (term342 a b) = (term343 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3379346 {A B : Type'} (s : A -> Prop) (_35382 : A) (f : A -> B) (_35383 : A) : (term344 A B s _35382 f _35383) = (term345 A B s _35382 f _35383).
Proof. exact (@lem3379345 (term66 A s _35382) (term109 A B s _35382 f _35383)). Qed.
Lemma lem3379348 (a : Prop) : (term105 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3379349 {A : Type'} (s : A -> Prop) (_35382 : A) : (term127 A s _35382) = (s _35382).
Proof. exact (@lem3379348 (s _35382)). Qed.
Lemma lem3379350 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3379351 {A : Type'} (s : A -> Prop) (_35382 : A) : (term346 A s _35382) = (term32 A s _35382).
Proof. exact (MK_COMB (@lem3379350) (@lem3379349 A s _35382)). Qed.
Lemma lem3379353 (a : Prop) (b : Prop) : (term342 a b) = (term343 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3379354 {A B : Type'} (s : A -> Prop) (_35382 : A) (f : A -> B) (_35383 : A) : (term347 A B s _35382 f _35383) = (term348 A B s _35382 f _35383).
Proof. exact (@lem3379353 (term66 A s _35383) (term289 A B _35382 f _35383)). Qed.
Lemma lem3379356 (a : Prop) : (term105 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3379357 {A : Type'} (s : A -> Prop) (_35383 : A) : (term127 A s _35383) = (s _35383).
Proof. exact (@lem3379356 (s _35383)). Qed.
Lemma lem3379358 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3379359 {A : Type'} (s : A -> Prop) (_35383 : A) : (term346 A s _35383) = (term32 A s _35383).
Proof. exact (MK_COMB (@lem3379358) (@lem3379357 A s _35383)). Qed.
Lemma lem3379361 (a : Prop) : (term105 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3379362 {A B : Type'} (_35382 : A) (f : A -> B) (_35383 : A) : (term349 A B _35382 f _35383) = ((f _35382) = (f _35383)).
Proof. exact (@lem3379361 ((f _35382) = (f _35383))). Qed.
Lemma lem3379363 {A B : Type'} (s : A -> Prop) (_35382 : A) (f : A -> B) (_35383 : A) : (term348 A B s _35382 f _35383) = (term34 A B s _35382 f _35383).
Proof. exact (MK_COMB (@lem3379359 A s _35383) (@lem3379362 A B _35382 f _35383)). Qed.
Lemma lem3379364 {A B : Type'} (s : A -> Prop) (_35382 : A) (f : A -> B) (_35383 : A) : (term347 A B s _35382 f _35383) = (term34 A B s _35382 f _35383).
Proof. exact (TRANS (@lem3379354 A B s _35382 f _35383) (@lem3379363 A B s _35382 f _35383)). Qed.
Lemma lem3379365 {A B : Type'} (s : A -> Prop) (_35382 : A) (f : A -> B) (_35383 : A) : (term345 A B s _35382 f _35383) = (term36 A B s _35382 f _35383).
Proof. exact (MK_COMB (@lem3379351 A s _35382) (@lem3379364 A B s _35382 f _35383)). Qed.
Lemma lem3379366 {A B : Type'} (s : A -> Prop) (_35382 : A) (f : A -> B) (_35383 : A) : (term344 A B s _35382 f _35383) = (term36 A B s _35382 f _35383).
Proof. exact (TRANS (@lem3379346 A B s _35382 f _35383) (@lem3379365 A B s _35382 f _35383)). Qed.
Lemma lem3379367 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3379368 {A B : Type'} (s : A -> Prop) (_35382 : A) (f : A -> B) (_35383 : A) : (term350 A B s _35382 f _35383) = (term38 A B s _35382 f _35383).
Proof. exact (MK_COMB (@lem3379367) (@lem3379366 A B s _35382 f _35383)). Qed.
Lemma lem3379369 {A : Type'} (_35382 : A) (_35383 : A) : (_35382 = _35383) = (_35382 = _35383).
Proof. exact (eq_refl (_35382 = _35383)). Qed.
Lemma lem3379370 {A B : Type'} (s : A -> Prop) (f : A -> B) (_35382 : A) (_35383 : A) : (term341 A B s f _35382 _35383) = (term40 A B s f _35382 _35383).
Proof. exact (MK_COMB (@lem3379368 A B s _35382 f _35383) (@lem3379369 A _35382 _35383)). Qed.
Lemma lem3379371 {A B : Type'} (s : A -> Prop) (f : A -> B) (_35382 : A) (_35383 : A) : (term338 A B s _35382 f _35383) = (term40 A B s f _35382 _35383).
Proof. exact (TRANS (@lem3379343 A B s f _35382 _35383) (@lem3379370 A B s f _35382 _35383)). Qed.
Lemma lem3379373 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term209 A B x' s x f t x'') (h2 : term79 A B x f t x'') : term34 A B s x'' f x'.
Proof. exact (conj (@lem3379192 A B x' s x f t x'' h1) (@lem3379199 A B x' s x f t x'' h1 h2)). Qed.
Lemma lem3379374 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term57 A B f t s) (h2 : term209 A B x' s x f t x'') (h3 : term79 A B x f t x'') : term36 A B s x'' f x'.
Proof. exact (conj (@lem3379185 A B s x f t x'' h1 h3) (@lem3379373 A B x' s x f t x'' h2 h3)). Qed.
Lemma lem3379376 {A B : Type'} (_35382 : A) (_35383 : A) (f : A -> B) (t : A -> Prop) (s : A -> Prop) (h1 : term57 A B f t s) : term40 A B s f _35382 _35383.
Proof. exact (EQ_MP (@lem3379371 A B s f _35382 _35383) (@lem3379340 A B _35382 _35383 f t s h1)). Qed.
Lemma lem3379377 {A B : Type'} (_35382 : A) (_35383 : A) (f : A -> B) (t : A -> Prop) (s : A -> Prop) (h1 : term57 A B f t s) : term40 A B s f _35382 _35383.
Proof. exact (@lem3379376 A B _35382 _35383 f t s h1). Qed.
Lemma lem3379378 {A B : Type'} (x'' : A) (x' : A) (f : A -> B) (t : A -> Prop) (s : A -> Prop) (h1 : term57 A B f t s) : term40 A B s f x'' x'.
Proof. exact (@lem3379377 A B x'' x' f t s h1). Qed.
Lemma lem3379381 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term57 A B f t s) (h2 : term209 A B x' s x f t x'') (h3 : term79 A B x f t x'') : x'' = x'.
Proof. exact (@lem3379378 A B x'' x' f t s h1 (@lem3379374 A B x' s x f t x'' h1 h2 h3)). Qed.
Lemma lem3379382 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term57 A B f t s) (h2 : term209 A B x' s x f t x'') (h3 : term79 A B x f t x'') : term351 A x'' x'.
Proof. exact (fun h0 : term352 A x'' x' => @lem3379381 A B x' s x f t x'' h1 h2 h3). Qed.
Lemma lem3379384 (p : Prop) : (term310 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3379385 {A : Type'} (x'' : A) (x' : A) : (term351 A x'' x') = (x'' = x').
Proof. exact (@lem3379384 (x'' = x')). Qed.
Lemma lem3379386 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term57 A B f t s) (h2 : term209 A B x' s x f t x'') (h3 : term79 A B x f t x'') : x'' = x'.
Proof. exact (EQ_MP (@lem3379385 A x'' x') (@lem3379382 A B x' s x f t x'' h1 h2 h3)). Qed.
Lemma lem3379388 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term79 A B x f t x'') : t x''.
Proof. exact (proj2 (@lem3378388 A B x f t x'' h1)). Qed.
Lemma lem3379389 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term79 A B x f t x'') : term311 A t x''.
Proof. exact (fun h0 : term66 A t x'' => @lem3379388 A B x f t x'' h1). Qed.
Lemma lem3379391 (p : Prop) : (term310 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3379392 {A : Type'} (t : A -> Prop) (x'' : A) : (term311 A t x'') = (t x'').
Proof. exact (@lem3379391 (t x'')). Qed.
Lemma lem3379393 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term79 A B x f t x'') : t x''.
Proof. exact (EQ_MP (@lem3379392 A t x'') (@lem3379389 A B x f t x'' h1)). Qed.
Lemma lem3379399 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3379400 {A : Type'} (_35435 : A) (t : A -> Prop) (_35434 : A) : (term325 A _35435 t _35434) = (term353 A _35435 t _35434).
Proof. exact (@lem3379399 (t _35435) (term352 A _35434 _35435) (term66 A t _35434)). Qed.
Lemma lem3379414 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3379415 {A : Type'} (t : A -> Prop) (_35434 : A) (_35435 : A) : (term354 A _35435 t _35434) = (term355 A t _35434 _35435).
Proof. exact (@lem3379414 (term66 A t _35434) (term352 A _35434 _35435)). Qed.
Lemma lem3379423 {A : Type'} (t : A -> Prop) (_35435 : A) : (term356 A t _35435) = (term356 A t _35435).
Proof. exact (eq_refl (term356 A t _35435)). Qed.
Lemma lem3379424 {A : Type'} (t : A -> Prop) (_35434 : A) (_35435 : A) : (term353 A _35435 t _35434) = (term357 A t _35434 _35435).
Proof. exact (MK_COMB (@lem3379423 A t _35435) (@lem3379415 A t _35434 _35435)). Qed.
Lemma lem3379435 {A : Type'} (t : A -> Prop) (_35434 : A) (_35435 : A) : (term325 A _35435 t _35434) = (term357 A t _35434 _35435).
Proof. exact (TRANS (@lem3379400 A _35435 t _35434) (@lem3379424 A t _35434 _35435)). Qed.
Lemma lem3379436 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3379437 {A : Type'} (t : A -> Prop) (_35434 : A) (_35435 : A) : (term358 A _35435 t _35434) = (term359 A t _35434 _35435).
Proof. exact (MK_COMB (@lem3379436) (@lem3379435 A t _35434 _35435)). Qed.
Lemma lem3379451 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3379452 {A : Type'} (t : A -> Prop) (_35434 : A) (_35435 : A) : (term354 A _35435 t _35434) = (term355 A t _35434 _35435).
Proof. exact (@lem3379451 (term66 A t _35434) (term352 A _35434 _35435)). Qed.
Lemma lem3379460 {A : Type'} (t : A -> Prop) (_35435 : A) : (term356 A t _35435) = (term356 A t _35435).
Proof. exact (eq_refl (term356 A t _35435)). Qed.
Lemma lem3379461 {A : Type'} (t : A -> Prop) (_35434 : A) (_35435 : A) : (term353 A _35435 t _35434) = (term357 A t _35434 _35435).
Proof. exact (MK_COMB (@lem3379460 A t _35435) (@lem3379452 A t _35434 _35435)). Qed.
Lemma lem3379472 {A : Type'} (t : A -> Prop) (_35434 : A) (_35435 : A) : ((term325 A _35435 t _35434) = (term353 A _35435 t _35434)) = ((term357 A t _35434 _35435) = (term357 A t _35434 _35435)).
Proof. exact (MK_COMB (@lem3379437 A t _35434 _35435) (@lem3379461 A t _35434 _35435)). Qed.
Lemma lem3379474 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3379475 (x : Prop) : (x = x) = True.
Proof. exact (@lem3379474 Prop x). Qed.
Lemma lem3379476 {A : Type'} (t : A -> Prop) (_35434 : A) (_35435 : A) : ((term357 A t _35434 _35435) = (term357 A t _35434 _35435)) = True.
Proof. exact (@lem3379475 (term357 A t _35434 _35435)). Qed.
Lemma lem3379477 {A : Type'} (_35435 : A) (t : A -> Prop) (_35434 : A) : ((term325 A _35435 t _35434) = (term353 A _35435 t _35434)) = True.
Proof. exact (TRANS (@lem3379472 A t _35434 _35435) (@lem3379476 A t _35434 _35435)). Qed.
Lemma lem3379478 {A : Type'} (_35435 : A) (t : A -> Prop) (_35434 : A) : True = ((term325 A _35435 t _35434) = (term353 A _35435 t _35434)).
Proof. exact (SYM (@lem3379477 A _35435 t _35434)). Qed.
Lemma lem3379479 {A : Type'} (_35435 : A) (t : A -> Prop) (_35434 : A) : (term325 A _35435 t _35434) = (term353 A _35435 t _35434).
Proof. exact (EQ_MP (@lem3379478 A _35435 t _35434) (@lem0)). Qed.
Lemma lem3379480 {A : Type'} (_35435 : A) (t : A -> Prop) (_35434 : A) : term353 A _35435 t _35434.
Proof. exact (EQ_MP (@lem3379479 A _35435 t _35434) (@lem3379101 A _35435 t _35434)). Qed.
Lemma lem3379482 (b : Prop) (a : Prop) : (a \/ b) = (term329 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3379483 {A : Type'} (_35434 : A) (t : A -> Prop) (_35435 : A) : (term353 A _35435 t _35434) = (term360 A _35434 t _35435).
Proof. exact (@lem3379482 (term354 A _35435 t _35434) (t _35435)). Qed.
Lemma lem3379485 (a : Prop) (b : Prop) : (term342 a b) = (term343 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3379486 {A : Type'} (_35435 : A) (t : A -> Prop) (_35434 : A) : (term361 A _35435 t _35434) = (term362 A _35435 t _35434).
Proof. exact (@lem3379485 (term352 A _35434 _35435) (term66 A t _35434)). Qed.
Lemma lem3379488 (a : Prop) : (term105 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3379489 {A : Type'} (_35434 : A) (_35435 : A) : (term363 A _35434 _35435) = (_35434 = _35435).
Proof. exact (@lem3379488 (_35434 = _35435)). Qed.
Lemma lem3379490 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3379491 {A : Type'} (_35434 : A) (_35435 : A) : (term364 A _35434 _35435) = (term365 A _35434 _35435).
Proof. exact (MK_COMB (@lem3379490) (@lem3379489 A _35434 _35435)). Qed.
Lemma lem3379493 (a : Prop) : (term105 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3379494 {A : Type'} (t : A -> Prop) (_35434 : A) : (term127 A t _35434) = (t _35434).
Proof. exact (@lem3379493 (t _35434)). Qed.
Lemma lem3379495 {A : Type'} (_35435 : A) (t : A -> Prop) (_35434 : A) : (term362 A _35435 t _35434) = (term366 A _35435 t _35434).
Proof. exact (MK_COMB (@lem3379491 A _35434 _35435) (@lem3379494 A t _35434)). Qed.
Lemma lem3379496 {A : Type'} (_35435 : A) (t : A -> Prop) (_35434 : A) : (term361 A _35435 t _35434) = (term366 A _35435 t _35434).
Proof. exact (TRANS (@lem3379486 A _35435 t _35434) (@lem3379495 A _35435 t _35434)). Qed.
Lemma lem3379497 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3379498 {A : Type'} (_35435 : A) (t : A -> Prop) (_35434 : A) : (term367 A _35435 t _35434) = (term368 A _35435 t _35434).
Proof. exact (MK_COMB (@lem3379497) (@lem3379496 A _35435 t _35434)). Qed.
Lemma lem3379499 {A : Type'} (t : A -> Prop) (_35435 : A) : (t _35435) = (t _35435).
Proof. exact (eq_refl (t _35435)). Qed.
Lemma lem3379500 {A : Type'} (_35434 : A) (t : A -> Prop) (_35435 : A) : (term360 A _35434 t _35435) = (term369 A _35434 t _35435).
Proof. exact (MK_COMB (@lem3379498 A _35435 t _35434) (@lem3379499 A t _35435)). Qed.
Lemma lem3379501 {A : Type'} (_35434 : A) (t : A -> Prop) (_35435 : A) : (term353 A _35435 t _35434) = (term369 A _35434 t _35435).
Proof. exact (TRANS (@lem3379483 A _35434 t _35435) (@lem3379500 A _35434 t _35435)). Qed.
Lemma lem3379503 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term57 A B f t s) (h2 : term209 A B x' s x f t x'') (h3 : term79 A B x f t x'') : term366 A x' t x''.
Proof. exact (conj (@lem3379386 A B x' s x f t x'' h1 h2 h3) (@lem3379393 A B x f t x'' h3)). Qed.
Lemma lem3379505 {A : Type'} (_35434 : A) (t : A -> Prop) (_35435 : A) : term369 A _35434 t _35435.
Proof. exact (EQ_MP (@lem3379501 A _35434 t _35435) (@lem3379480 A _35435 t _35434)). Qed.
Lemma lem3379506 {A : Type'} (_35434 : A) (t : A -> Prop) (_35435 : A) : term369 A _35434 t _35435.
Proof. exact (@lem3379505 A _35434 t _35435). Qed.
Lemma lem3379507 {A : Type'} (x'' : A) (t : A -> Prop) (x' : A) : term369 A x'' t x'.
Proof. exact (@lem3379506 A x'' t x'). Qed.
Lemma lem3379510 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term57 A B f t s) (h2 : term209 A B x' s x f t x'') (h3 : term79 A B x f t x'') : t x'.
Proof. exact (@lem3379507 A x'' t x' (@lem3379503 A B x' s x f t x'' h1 h2 h3)). Qed.
Lemma lem3379511 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term57 A B f t s) (h2 : term209 A B x' s x f t x'') (h3 : term79 A B x f t x'') : term311 A t x'.
Proof. exact (fun h0 : term66 A t x' => @lem3379510 A B x' s x f t x'' h1 h2 h3). Qed.
Lemma lem3379513 (p : Prop) : (term310 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3379514 {A : Type'} (t : A -> Prop) (x' : A) : (term311 A t x') = (t x').
Proof. exact (@lem3379513 (t x')). Qed.
Lemma lem3379515 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term57 A B f t s) (h2 : term209 A B x' s x f t x'') (h3 : term79 A B x f t x'') : t x'.
Proof. exact (EQ_MP (@lem3379514 A t x') (@lem3379511 A B x' s x f t x'' h1 h2 h3)). Qed.
Lemma lem3379518 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3379520 {A : Type'} (t : A -> Prop) (x' : A) : (term66 A t x') = (term370 A t x').
Proof. exact (@lem3379518 (t x')). Qed.
Lemma lem3379523 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term209 A B x' s x f t x'') : term370 A t x'.
Proof. exact (EQ_MP (@lem3379520 A t x') (@lem3378920 A B x' s x f t x'' h1)). Qed.
Lemma lem3379526 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term57 A B f t s) (h2 : term209 A B x' s x f t x'') (h3 : term79 A B x f t x'') : False.
Proof. exact (@lem3379523 A B x' s x f t x'' h2 (@lem3379515 A B x' s x f t x'' h1 h2 h3)). Qed.
Lemma lem3379527 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term57 A B f t s) (h2 : term209 A B x' s x f t x'') (h3 : term79 A B x f t x'') : term319.
Proof. exact (fun h0 : ~ False => @lem3379526 A B x' s x f t x'' h1 h2 h3). Qed.
Lemma lem3379529 (p : Prop) : (term310 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3379530 : term319 = False.
Proof. exact (@lem3379529 False). Qed.
Lemma lem3379569 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem3379570 {B : Type'} (x : B) : x = x.
Proof. exact (@lem3379569 B x). Qed.
Lemma lem3379571 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (f x').
Proof. exact (@lem3379570 B (f x')). Qed.
Lemma lem3379572 {A B : Type'} (f : A -> B) (x' : A) : term308 A B f x'.
Proof. exact (fun h0 : term309 A B f x' => @lem3379571 A B f x'). Qed.
Lemma lem3379574 (p : Prop) : (term310 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3379575 {A B : Type'} (f : A -> B) (x' : A) : (term308 A B f x') = ((f x') = (f x')).
Proof. exact (@lem3379574 ((f x') = (f x'))). Qed.
Lemma lem3379576 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (f x').
Proof. exact (EQ_MP (@lem3379575 A B f x') (@lem3379572 A B f x')). Qed.
Lemma lem3379578 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem3379579 {B : Type'} (x : B) : x = x.
Proof. exact (@lem3379578 B x). Qed.
Lemma lem3379580 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (f x').
Proof. exact (@lem3379579 B (f x')). Qed.
Lemma lem3379581 {A B : Type'} (f : A -> B) (x' : A) : term308 A B f x'.
Proof. exact (fun h0 : term309 A B f x' => @lem3379580 A B f x'). Qed.
Lemma lem3379583 (p : Prop) : (term310 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3379584 {A B : Type'} (f : A -> B) (x' : A) : (term308 A B f x') = ((f x') = (f x')).
Proof. exact (@lem3379583 ((f x') = (f x'))). Qed.
Lemma lem3379585 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (f x').
Proof. exact (EQ_MP (@lem3379584 A B f x') (@lem3379581 A B f x')). Qed.
Lemma lem3379587 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term237 A B s x' x f t) : s x'.
Proof. exact (proj2 (@lem3378394 A B s x' x f t h1)). Qed.
Lemma lem3379588 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term237 A B s x' x f t) : term311 A s x'.
Proof. exact (fun h0 : term66 A s x' => @lem3379587 A B s x' x f t h1). Qed.
Lemma lem3379590 (p : Prop) : (term310 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3379591 {A : Type'} (s : A -> Prop) (x' : A) : (term311 A s x') = (s x').
Proof. exact (@lem3379590 (s x')). Qed.
Lemma lem3379592 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term237 A B s x' x f t) : s x'.
Proof. exact (EQ_MP (@lem3379591 A s x') (@lem3379588 A B s x' x f t h1)). Qed.
Lemma lem3379598 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3379599 {A B : Type'} (s : A -> Prop) (x' : A) (f : A -> B) (t : A -> Prop) (_35388 : A) : (term305 A B x' f s t _35388) = (term371 A B s x' f t _35388).
Proof. exact (@lem3379598 (term66 A s _35388) (term289 A B x' f _35388) (t _35388)). Qed.
Lemma lem3379613 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3379614 {A B : Type'} (t : A -> Prop) (x' : A) (f : A -> B) (_35388 : A) : (term372 A B x' f t _35388) = (term373 A B t x' f _35388).
Proof. exact (@lem3379613 (t _35388) (term289 A B x' f _35388)). Qed.
Lemma lem3379622 {A : Type'} (s : A -> Prop) (_35388 : A) : (term110 A s _35388) = (term110 A s _35388).
Proof. exact (eq_refl (term110 A s _35388)). Qed.
Lemma lem3379623 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (f : A -> B) (_35388 : A) : (term371 A B s x' f t _35388) = (term374 A B s t x' f _35388).
Proof. exact (MK_COMB (@lem3379622 A s _35388) (@lem3379614 A B t x' f _35388)). Qed.
Lemma lem3379627 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3379628 {A B : Type'} (t : A -> Prop) (s : A -> Prop) (x' : A) (f : A -> B) (_35388 : A) : (term374 A B s t x' f _35388) = (term375 A B t s x' f _35388).
Proof. exact (@lem3379627 (t _35388) (term66 A s _35388) (term289 A B x' f _35388)). Qed.
Lemma lem3379646 {A B : Type'} (t : A -> Prop) (s : A -> Prop) (x' : A) (f : A -> B) (_35388 : A) : (term371 A B s x' f t _35388) = (term375 A B t s x' f _35388).
Proof. exact (TRANS (@lem3379623 A B s t x' f _35388) (@lem3379628 A B t s x' f _35388)). Qed.
Lemma lem3379647 {A B : Type'} (t : A -> Prop) (s : A -> Prop) (x' : A) (f : A -> B) (_35388 : A) : (term305 A B x' f s t _35388) = (term375 A B t s x' f _35388).
Proof. exact (TRANS (@lem3379599 A B s x' f t _35388) (@lem3379646 A B t s x' f _35388)). Qed.
Lemma lem3379648 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3379649 {A B : Type'} (t : A -> Prop) (s : A -> Prop) (x' : A) (f : A -> B) (_35388 : A) : (term376 A B x' f s t _35388) = (term377 A B t s x' f _35388).
Proof. exact (MK_COMB (@lem3379648) (@lem3379647 A B t s x' f _35388)). Qed.
Lemma lem3379663 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3379664 {A B : Type'} (s : A -> Prop) (x' : A) (f : A -> B) (_35388 : A) : (term294 A B x' f s _35388) = (term109 A B s x' f _35388).
Proof. exact (@lem3379663 (term66 A s _35388) (term289 A B x' f _35388)). Qed.
Lemma lem3379672 {A : Type'} (t : A -> Prop) (_35388 : A) : (term356 A t _35388) = (term356 A t _35388).
Proof. exact (eq_refl (term356 A t _35388)). Qed.
Lemma lem3379673 {A B : Type'} (t : A -> Prop) (s : A -> Prop) (x' : A) (f : A -> B) (_35388 : A) : (term378 A B t x' f s _35388) = (term375 A B t s x' f _35388).
Proof. exact (MK_COMB (@lem3379672 A t _35388) (@lem3379664 A B s x' f _35388)). Qed.
Lemma lem3379684 {A B : Type'} (t : A -> Prop) (s : A -> Prop) (x' : A) (f : A -> B) (_35388 : A) : ((term305 A B x' f s t _35388) = (term378 A B t x' f s _35388)) = ((term375 A B t s x' f _35388) = (term375 A B t s x' f _35388)).
Proof. exact (MK_COMB (@lem3379649 A B t s x' f _35388) (@lem3379673 A B t s x' f _35388)). Qed.
Lemma lem3379686 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3379687 (x : Prop) : (x = x) = True.
Proof. exact (@lem3379686 Prop x). Qed.
Lemma lem3379688 {A B : Type'} (t : A -> Prop) (s : A -> Prop) (x' : A) (f : A -> B) (_35388 : A) : ((term375 A B t s x' f _35388) = (term375 A B t s x' f _35388)) = True.
Proof. exact (@lem3379687 (term375 A B t s x' f _35388)). Qed.
Lemma lem3379689 {A B : Type'} (t : A -> Prop) (x' : A) (f : A -> B) (s : A -> Prop) (_35388 : A) : ((term305 A B x' f s t _35388) = (term378 A B t x' f s _35388)) = True.
Proof. exact (TRANS (@lem3379684 A B t s x' f _35388) (@lem3379688 A B t s x' f _35388)). Qed.
Lemma lem3379690 {A B : Type'} (t : A -> Prop) (x' : A) (f : A -> B) (s : A -> Prop) (_35388 : A) : True = ((term305 A B x' f s t _35388) = (term378 A B t x' f s _35388)).
Proof. exact (SYM (@lem3379689 A B t x' f s _35388)). Qed.
Lemma lem3379691 {A B : Type'} (t : A -> Prop) (x' : A) (f : A -> B) (s : A -> Prop) (_35388 : A) : (term305 A B x' f s t _35388) = (term378 A B t x' f s _35388).
Proof. exact (EQ_MP (@lem3379690 A B t x' f s _35388) (@lem0)). Qed.
Lemma lem3379692 {A B : Type'} (_35388 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term237 A B s x' x f t) : term378 A B t x' f s _35388.
Proof. exact (EQ_MP (@lem3379691 A B t x' f s _35388) (@lem3378989 A B _35388 s x' x f t h1)). Qed.
Lemma lem3379694 (b : Prop) (a : Prop) : (a \/ b) = (term329 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3379695 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_35388 : A) : (term378 A B t x' f s _35388) = (term379 A B x' f s t _35388).
Proof. exact (@lem3379694 (term294 A B x' f s _35388) (t _35388)). Qed.
Lemma lem3379697 (a : Prop) (b : Prop) : (term342 a b) = (term343 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3379698 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_35388 : A) : (term380 A B x' f s _35388) = (term381 A B x' f s _35388).
Proof. exact (@lem3379697 (term289 A B x' f _35388) (term66 A s _35388)). Qed.
Lemma lem3379700 (a : Prop) : (term105 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3379701 {A B : Type'} (x' : A) (f : A -> B) (_35388 : A) : (term349 A B x' f _35388) = ((f x') = (f _35388)).
Proof. exact (@lem3379700 ((f x') = (f _35388))). Qed.
Lemma lem3379702 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3379703 {A B : Type'} (x' : A) (f : A -> B) (_35388 : A) : (term382 A B x' f _35388) = (term383 A B x' f _35388).
Proof. exact (MK_COMB (@lem3379702) (@lem3379701 A B x' f _35388)). Qed.
Lemma lem3379705 (a : Prop) : (term105 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3379706 {A : Type'} (s : A -> Prop) (_35388 : A) : (term127 A s _35388) = (s _35388).
Proof. exact (@lem3379705 (s _35388)). Qed.
Lemma lem3379707 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_35388 : A) : (term381 A B x' f s _35388) = (term316 A B x' f s _35388).
Proof. exact (MK_COMB (@lem3379703 A B x' f _35388) (@lem3379706 A s _35388)). Qed.
Lemma lem3379708 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_35388 : A) : (term380 A B x' f s _35388) = (term316 A B x' f s _35388).
Proof. exact (TRANS (@lem3379698 A B x' f s _35388) (@lem3379707 A B x' f s _35388)). Qed.
Lemma lem3379709 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3379710 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_35388 : A) : (term384 A B x' f s _35388) = (term385 A B x' f s _35388).
Proof. exact (MK_COMB (@lem3379709) (@lem3379708 A B x' f s _35388)). Qed.
Lemma lem3379711 {A : Type'} (t : A -> Prop) (_35388 : A) : (t _35388) = (t _35388).
Proof. exact (eq_refl (t _35388)). Qed.
Lemma lem3379712 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_35388 : A) : (term379 A B x' f s t _35388) = (term386 A B x' f s t _35388).
Proof. exact (MK_COMB (@lem3379710 A B x' f s _35388) (@lem3379711 A t _35388)). Qed.
Lemma lem3379713 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_35388 : A) : (term378 A B t x' f s _35388) = (term386 A B x' f s t _35388).
Proof. exact (TRANS (@lem3379695 A B x' f s t _35388) (@lem3379712 A B x' f s t _35388)). Qed.
Lemma lem3379715 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term237 A B s x' x f t) : term317 A B f s x'.
Proof. exact (conj (@lem3379585 A B f x') (@lem3379592 A B s x' x f t h1)). Qed.
Lemma lem3379717 {A B : Type'} (_35388 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term237 A B s x' x f t) : term386 A B x' f s t _35388.
Proof. exact (EQ_MP (@lem3379713 A B x' f s t _35388) (@lem3379692 A B _35388 s x' x f t h1)). Qed.
Lemma lem3379718 {A B : Type'} (_35388 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term237 A B s x' x f t) : term386 A B x' f s t _35388.
Proof. exact (@lem3379717 A B _35388 s x' x f t h1). Qed.
Lemma lem3379719 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term237 A B s x' x f t) : term387 A B f s t x'.
Proof. exact (@lem3379718 A B x' s x' x f t h1). Qed.
Lemma lem3379722 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term237 A B s x' x f t) : t x'.
Proof. exact (@lem3379719 A B s x' x f t h1 (@lem3379715 A B s x' x f t h1)). Qed.
Lemma lem3379723 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term237 A B s x' x f t) : term311 A t x'.
Proof. exact (fun h0 : term66 A t x' => @lem3379722 A B s x' x f t h1). Qed.
Lemma lem3379725 (p : Prop) : (term310 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3379726 {A : Type'} (t : A -> Prop) (x' : A) : (term311 A t x') = (t x').
Proof. exact (@lem3379725 (t x')). Qed.
Lemma lem3379727 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term237 A B s x' x f t) : t x'.
Proof. exact (EQ_MP (@lem3379726 A t x') (@lem3379723 A B s x' x f t h1)). Qed.
Lemma lem3379729 (a : Prop) (b : Prop) : (term312 a b) = (term313 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3379730 {A B : Type'} (x' : A) (f : A -> B) (t : A -> Prop) (_35389 : A) : (term294 A B x' f t _35389) = (term314 A B x' f t _35389).
Proof. exact (@lem3379729 ((f x') = (f _35389)) (t _35389)). Qed.
Lemma lem3379732 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3379733 {A B : Type'} (x' : A) (f : A -> B) (t : A -> Prop) (_35389 : A) : (term314 A B x' f t _35389) = (term315 A B x' f t _35389).
Proof. exact (@lem3379732 (term316 A B x' f t _35389)). Qed.
Lemma lem3379734 {A B : Type'} (x' : A) (f : A -> B) (t : A -> Prop) (_35389 : A) : (term294 A B x' f t _35389) = (term315 A B x' f t _35389).
Proof. exact (TRANS (@lem3379730 A B x' f t _35389) (@lem3379733 A B x' f t _35389)). Qed.
Lemma lem3379736 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term237 A B s x' x f t) : term317 A B f t x'.
Proof. exact (conj (@lem3379576 A B f x') (@lem3379727 A B s x' x f t h1)). Qed.
Lemma lem3379738 {A B : Type'} (_35389 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term237 A B s x' x f t) : term315 A B x' f t _35389.
Proof. exact (EQ_MP (@lem3379734 A B x' f t _35389) (@lem3379002 A B _35389 s x' x f t h1)). Qed.
Lemma lem3379739 {A B : Type'} (_35389 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term237 A B s x' x f t) : term315 A B x' f t _35389.
Proof. exact (@lem3379738 A B _35389 s x' x f t h1). Qed.
Lemma lem3379740 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term237 A B s x' x f t) : term318 A B f t x'.
Proof. exact (@lem3379739 A B x' s x' x f t h1). Qed.
Lemma lem3379743 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term237 A B s x' x f t) : False.
Proof. exact (@lem3379740 A B s x' x f t h1 (@lem3379736 A B s x' x f t h1)). Qed.
Lemma lem3379744 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term237 A B s x' x f t) : term319.
Proof. exact (fun h0 : ~ False => @lem3379743 A B s x' x f t h1). Qed.
Lemma lem3379746 (p : Prop) : (term310 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3379747 : term319 = False.
Proof. exact (@lem3379746 False). Qed.
Lemma lem3379749 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term237 A B s x' x f t) : False.
Proof. exact (EQ_MP (@lem3379747) (@lem3379744 A B s x' x f t h1)). Qed.
Lemma lem3379750 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term57 A B f t s) (h2 : term209 A B x' s x f t x'') (h3 : term79 A B x f t x'') : False.
Proof. exact (EQ_MP (@lem3379530) (@lem3379527 A B x' s x f t x'' h1 h2 h3)). Qed.
Lemma lem3379751 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term150 A B x f s) (h2 : term209 A B x' s x f t x'') : False.
Proof. exact (EQ_MP (@lem3379088) (@lem3379085 A B x' s x f t x'' h1 h2)). Qed.
Lemma lem3379752 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term150 A B x f s) (h2 : term209 A B x' s x f t x'') : (term150 A B x f s) = False.
Proof. exact (prop_ext (fun h3 : term150 A B x f s => @lem3379751 A B x' s x f t x'' h1 h2) (fun h3 : False => @lem3378462 A B x f s h1)). Qed.
Lemma lem3379753 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term150 A B x f s) (h2 : term209 A B x' s x f t x'') : False.
Proof. exact (EQ_MP (@lem3379752 A B x' s x f t x'' h1 h2) (@lem3378462 A B x f s h1)). Qed.
Lemma lem3379754 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term57 A B f t s) (h2 : term209 A B x' s x f t x'') : False.
Proof. exact (or_elim (@lem3378381 A B x' s x f t x'' h2) (fun h0 : term150 A B x f s => @lem3379753 A B x' s x f t x'' h0 h2) (fun h0 : term79 A B x f t x'' => @lem3379750 A B x' s x f t x'' h1 h2 h0)). Qed.
Lemma lem3379755 {A B : Type'} (x'' : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term57 A B f t s) (h2 : term275 A B x'' s x' x f t) : False.
Proof. exact (or_elim (@lem3378376 A B x'' s x' x f t h2) (fun h0 : term209 A B x' s x f t x'' => @lem3379754 A B x' s x f t x'' h1 h0) (fun h0 : term237 A B s x' x f t => @lem3379749 A B s x' x f t h0)). Qed.
Lemma lem3379756 {A B : Type'} (x'' : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term57 A B f t s) (h2 : term275 A B x'' s x' x f t) : (term275 A B x'' s x' x f t) = False.
Proof. exact (prop_ext (fun h3 : term275 A B x'' s x' x f t => @lem3379755 A B x'' s x' x f t h1 h2) (fun h3 : False => @lem3378376 A B x'' s x' x f t h2)). Qed.
Lemma lem3379757 {A B : Type'} (x'' : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term57 A B f t s) (h2 : term275 A B x'' s x' x f t) : False.
Proof. exact (EQ_MP (@lem3379756 A B x'' s x' x f t h1 h2) (@lem3378376 A B x'' s x' x f t h2)). Qed.
Lemma lem3379758 {A B : Type'} (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (s : A -> Prop) (h1 : term278 A B s x' x f t) (h2 : term57 A B f t s) : False.
Proof. exact (ex_elim (@lem3378187 A B s x' x f t h1) (fun x'' : A => fun h0 : term277 A B s x' x f t x'' => @lem3379757 A B x'' s x' x f t h2 h0)). Qed.
Lemma lem3379759 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (s : A -> Prop) (h1 : term107 A B s x f t) (h2 : term57 A B f t s) : False.
Proof. exact (ex_elim (@lem3378186 A B s x f t h1) (fun x' : A => fun h0 : term279 A B s x f t x' => @lem3379758 A B x' x f t s h0 h2)). Qed.
Lemma lem3379760 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (s : A -> Prop) (h1 : term107 A B s x f t) (h2 : term57 A B f t s) : (term107 A B s x f t) = False.
Proof. exact (prop_ext (fun h3 : term107 A B s x f t => @lem3379759 A B x f t s h1 h2) (fun h3 : False => @lem3377514 A B s x f t h1)). Qed.
Lemma lem3379761 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (s : A -> Prop) (h1 : term107 A B s x f t) (h2 : term57 A B f t s) : False.
Proof. exact (EQ_MP (@lem3379760 A B x f t s h1 h2) (@lem3377514 A B s x f t h1)). Qed.
Lemma lem3379762 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (s : A -> Prop) (h1 : term57 A B f t s) : term106 A B s x f t.
Proof. exact (fun h0 : term107 A B s x f t => @lem3379761 A B x f t s h0 h1). Qed.
Lemma lem3379763 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (s : A -> Prop) (h1 : term57 A B f t s) : (term73 A B x f s t) = (term87 A B s x f t).
Proof. exact (EQ_MP (@lem3377513 A B s x f t) (@lem3379762 A B x f t s h1)). Qed.
Lemma lem3379768 {A B : Type'} (f : A -> B) (t : A -> Prop) (s : A -> Prop) (h1 : term57 A B f t s) : term90 A B s f t.
Proof. exact (fun x : B => @lem3379763 A B x f t s h1). Qed.
Lemma lem3379769 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : term91 A B s f t.
Proof. exact (fun h0 : term57 A B f t s => @lem3379768 A B f t s h0). Qed.
Lemma lem3379774 {A B : Type'} (s : A -> Prop) (f : A -> B) : term93 A B s f.
Proof. exact (fun t : A -> Prop => @lem3379769 A B s f t). Qed.
Lemma lem3379779 {A B : Type'} (f : A -> B) : term95 A B f.
Proof. exact (fun s : A -> Prop => @lem3379774 A B s f). Qed.
Lemma lem3379784 {A B : Type'} : term97 A B.
Proof. exact (fun f : A -> B => @lem3379779 A B f). Qed.
Lemma lem3379785 {A B : Type'} : term99 A B.
Proof. exact (EQ_MP (@lem3377508 A B) (@lem3379784 A B)). Qed.
Lemma lem3379787 {A B : Type'} : term99 A B.
Proof. exact (@lem3377166 A B (@lem3379785 A B)). Qed.
Lemma lem3379788 {A B : Type'} (h1 : term100 A B) : False.
Proof. exact (@lem3379787 A B (@lem3377150 A B h1)). Qed.
Lemma lem3379789 {A B : Type'} (h1 : term100 A B) : (term100 A B) = False.
Proof. exact (prop_ext (fun h2 : term100 A B => @lem3379788 A B h1) (fun h2 : False => @lem3377150 A B h1)). Qed.
Lemma lem3379790 {A B : Type'} (h1 : term100 A B) : False.
Proof. exact (EQ_MP (@lem3379789 A B h1) (@lem3377150 A B h1)). Qed.
Lemma lem3379791 {A B : Type'} : term99 A B.
Proof. exact (fun h0 : term100 A B => @lem3379790 A B h0). Qed.
Lemma lem3379792 {A B : Type'} : term97 A B.
Proof. exact (EQ_MP (@lem3377149 A B) (@lem3379791 A B)). Qed.
Lemma lem3379793 {A B : Type'} : term30 A B.
Proof. exact (EQ_MP (@lem3377145 A B) (@lem3379792 A B)). Qed.
Lemma lem3379794 {A B : Type'} : term29 A B.
Proof. exact (EQ_MP (@lem3376881 A B) (@lem3379793 A B)). Qed.
