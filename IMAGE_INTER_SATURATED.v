Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import IMAGE_INTER_SATURATED_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17646_spec.
Require Import thm18394_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
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
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211640_spec.
Require Import thm3211641_spec.
Require Import thm3211656_spec.
Require Import thm3211657_spec.
Require Import thm3211710_spec.
Require Import thm3211711_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3552878 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem3552879 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem3552880 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem3552879 t1) (@lem3552878 t1)). Qed.
Lemma lem3552881 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem3552880 t1 t2). Qed.
Lemma lem3552882 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem3552883 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem3552882 t1 t2) (@lem3552881 t1 t2)). Qed.
Lemma lem3552884 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem3552883 t1 t2 t3). Qed.
Lemma lem3552885 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem3552886 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem3552885 t1 t2 t3) (@lem3552884 t1 t2 t3)). Qed.
Lemma lem3552887 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem3552886 t1 t2 t3)). Qed.
Lemma lem3552905 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term7 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3552906 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term7 A s t).
Proof. exact (@lem3552905 A s t). Qed.
Lemma lem3552907 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term8 A B f s) = (term9 A B f s).
Proof. exact (@lem3552906 A (term10 A B f s) s). Qed.
Lemma lem3552918 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3552919 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term11 A B f s) = (term12 A B f s).
Proof. exact (MK_COMB (@lem3552918) (@lem3552907 A B f s)). Qed.
Lemma lem3552921 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term7 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3552922 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term7 A s t).
Proof. exact (@lem3552921 A s t). Qed.
Lemma lem3552923 {A B : Type'} (f : A -> B) (t : A -> Prop) : (term8 A B f t) = (term9 A B f t).
Proof. exact (@lem3552922 A (term10 A B f t) t). Qed.
Lemma lem3552934 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term13 A B s f t) = (term14 A B s f t).
Proof. exact (MK_COMB (@lem3552919 A B f s) (@lem3552923 A B f t)). Qed.
Lemma lem3552937 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3552938 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term15 A B s f t) = (term16 A B s f t).
Proof. exact (MK_COMB (@lem3552937) (@lem3552934 A B s f t)). Qed.
Lemma lem3552942 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term17 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3552943 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (s = t) = (term17 B s t).
Proof. exact (@lem3552942 B s t). Qed.
Lemma lem3552944 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : ((term18 A B f s t) = (term19 A B s f t)) = (term20 A B s f t).
Proof. exact (@lem3552943 B (term18 A B f s t) (term19 A B s f t)). Qed.
Lemma lem3552953 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term21 A B s f t) = (term22 A B s f t).
Proof. exact (MK_COMB (@lem3552938 A B s f t) (@lem3552944 A B s f t)). Qed.
Lemma lem3552956 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term23 A B s f) = (term24 A B s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3552953 A B s f t)). Qed.
Lemma lem3552957 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3552958 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term25 A B s f) = (term26 A B s f).
Proof. exact (MK_COMB (@lem3552957 A) (@lem3552956 A B s f)). Qed.
Lemma lem3552963 {A B : Type'} (f : A -> B) : (term27 A B f) = (term28 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3552958 A B s f)). Qed.
Lemma lem3552964 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3552965 {A B : Type'} (f : A -> B) : (term29 A B f) = (term30 A B f).
Proof. exact (MK_COMB (@lem3552964 A) (@lem3552963 A B f)). Qed.
Lemma lem3552970 {A B : Type'} : (term31 A B) = (term32 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3552965 A B f)). Qed.
Lemma lem3552971 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3552972 {A B : Type'} : (term33 A B) = (term34 A B).
Proof. exact (MK_COMB (@lem3552971 A B) (@lem3552970 A B)). Qed.
Lemma lem3552977 {A B : Type'} : (term34 A B) = (term33 A B).
Proof. exact (SYM (@lem3552972 A B)). Qed.
Lemma lem3553001 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term35 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem3553002 {A : Type'} (p : A -> Prop) (x : A) : (term35 A x p) = (p x).
Proof. exact (@lem3553001 A p x). Qed.
Lemma lem3553003 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term36 A B x f s) = (term37 A B f s x).
Proof. exact (@lem3553002 A (term38 A B f s) x). Qed.
Lemma lem3553004 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term37 A B f s x) = (term39 A B x f s).
Proof. exact (eq_refl (term37 A B f s x)). Qed.
Lemma lem3553005 {A : Type'} (GEN_PVAR_86 : A) : (@SETSPEC A GEN_PVAR_86) = (@SETSPEC A GEN_PVAR_86).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_86)). Qed.
Lemma lem3553006 {A B : Type'} (GEN_PVAR_86 : A) (x : A) (f : A -> B) (s : A -> Prop) : (term40 A B GEN_PVAR_86 f s x) = (term41 A B GEN_PVAR_86 x f s).
Proof. exact (MK_COMB (@lem3553005 A GEN_PVAR_86) (@lem3553004 A B x f s)). Qed.
Lemma lem3553007 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3553008 {A B : Type'} (GEN_PVAR_86 : A) (f : A -> B) (s : A -> Prop) (x : A) : (term42 A B GEN_PVAR_86 f s x) = (term43 A B GEN_PVAR_86 f s x).
Proof. exact (MK_COMB (@lem3553006 A B GEN_PVAR_86 x f s) (@lem3553007 A x)). Qed.
Lemma lem3553009 {A B : Type'} (GEN_PVAR_86 : A) (f : A -> B) (s : A -> Prop) : (term44 A B GEN_PVAR_86 f s) = (term45 A B GEN_PVAR_86 f s).
Proof. exact (fun_ext (fun x : A => @lem3553008 A B GEN_PVAR_86 f s x)). Qed.
Lemma lem3553010 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3553011 {A B : Type'} (GEN_PVAR_86 : A) (f : A -> B) (s : A -> Prop) : (term46 A B GEN_PVAR_86 f s) = (term47 A B GEN_PVAR_86 f s).
Proof. exact (MK_COMB (@lem3553010 A) (@lem3553009 A B GEN_PVAR_86 f s)). Qed.
Lemma lem3553012 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term48 A B f s) = (term49 A B f s).
Proof. exact (fun_ext (fun GEN_PVAR_86 : A => @lem3553011 A B GEN_PVAR_86 f s)). Qed.
Lemma lem3553013 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem3553014 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term50 A B f s) = (term10 A B f s).
Proof. exact (MK_COMB (@lem3553013 A) (@lem3553012 A B f s)). Qed.
Lemma lem3553015 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem3553016 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term36 A B x f s) = (term51 A B x f s).
Proof. exact (MK_COMB (@lem3553015 A x) (@lem3553014 A B f s)). Qed.
Lemma lem3553017 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3553018 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term52 A B x f s) = (term53 A B x f s).
Proof. exact (MK_COMB (@lem3553017) (@lem3553016 A B x f s)). Qed.
Lemma lem3553019 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term37 A B f s x) = (term39 A B x f s).
Proof. exact (eq_refl (term37 A B f s x)). Qed.
Lemma lem3553020 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : ((term36 A B x f s) = (term37 A B f s x)) = ((term51 A B x f s) = (term39 A B x f s)).
Proof. exact (MK_COMB (@lem3553018 A B x f s) (@lem3553019 A B x f s)). Qed.
Lemma lem3553021 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term51 A B x f s) = (term39 A B x f s).
Proof. exact (EQ_MP (@lem3553020 A B x f s) (@lem3553003 A B f s x)). Qed.
Lemma lem3553023 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term54 A B y f s) = (term55 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem3553024 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term54 A B y f s) = (term55 A B y f s).
Proof. exact (@lem3553023 A B y f s). Qed.
Lemma lem3553025 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term39 A B x f s) = (term56 A B x f s).
Proof. exact (@lem3553024 A B (f x) f s). Qed.
Lemma lem3553030 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term51 A B x f s) = (term56 A B x f s).
Proof. exact (TRANS (@lem3553021 A B x f s) (@lem3553025 A B x f s)). Qed.
Lemma lem3553036 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3553037 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3553036 A P x). Qed.
Lemma lem3553038 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3553037 A s x'). Qed.
Lemma lem3553039 {A B : Type'} (x : A) (f : A -> B) (x' : A) : (term57 A B x f x') = (term57 A B x f x').
Proof. exact (eq_refl (term57 A B x f x')). Qed.
Lemma lem3553040 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (x' : A) : (term58 A B x f x' s) = (term59 A B x f s x').
Proof. exact (MK_COMB (@lem3553039 A B x f x') (@lem3553038 A s x')). Qed.
Lemma lem3553043 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term60 A B x f s) = (term61 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3553040 A B x f s x')). Qed.
Lemma lem3553044 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3553045 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term56 A B x f s) = (term62 A B x f s).
Proof. exact (MK_COMB (@lem3553044 A) (@lem3553043 A B x f s)). Qed.
Lemma lem3553050 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term51 A B x f s) = (term62 A B x f s).
Proof. exact (TRANS (@lem3553030 A B x f s) (@lem3553045 A B x f s)). Qed.
Lemma lem3553051 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3553052 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term63 A B x f s) = (term64 A B x f s).
Proof. exact (MK_COMB (@lem3553051) (@lem3553050 A B x f s)). Qed.
Lemma lem3553054 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3553055 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3553054 A P x). Qed.
Lemma lem3553056 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3553055 A s x). Qed.
Lemma lem3553057 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term65 A B f x s) = (term66 A B f s x).
Proof. exact (MK_COMB (@lem3553052 A B x f s) (@lem3553056 A s x)). Qed.
Lemma lem3553060 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term67 A B f s) = (term68 A B f s).
Proof. exact (fun_ext (fun x : A => @lem3553057 A B f s x)). Qed.
Lemma lem3553061 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3553062 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term9 A B f s) = (term69 A B f s).
Proof. exact (MK_COMB (@lem3553061 A) (@lem3553060 A B f s)). Qed.
Lemma lem3553067 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3553068 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term12 A B f s) = (term70 A B f s).
Proof. exact (MK_COMB (@lem3553067) (@lem3553062 A B f s)). Qed.
Lemma lem3553076 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term35 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem3553077 {A : Type'} (p : A -> Prop) (x : A) : (term35 A x p) = (p x).
Proof. exact (@lem3553076 A p x). Qed.
Lemma lem3553078 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : A) : (term36 A B x f t) = (term37 A B f t x).
Proof. exact (@lem3553077 A (term38 A B f t) x). Qed.
Lemma lem3553079 {A B : Type'} (x : A) (f : A -> B) (t : A -> Prop) : (term37 A B f t x) = (term39 A B x f t).
Proof. exact (eq_refl (term37 A B f t x)). Qed.
Lemma lem3553080 {A : Type'} (GEN_PVAR_87 : A) : (@SETSPEC A GEN_PVAR_87) = (@SETSPEC A GEN_PVAR_87).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_87)). Qed.
Lemma lem3553081 {A B : Type'} (GEN_PVAR_87 : A) (x : A) (f : A -> B) (t : A -> Prop) : (term40 A B GEN_PVAR_87 f t x) = (term41 A B GEN_PVAR_87 x f t).
Proof. exact (MK_COMB (@lem3553080 A GEN_PVAR_87) (@lem3553079 A B x f t)). Qed.
Lemma lem3553082 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3553083 {A B : Type'} (GEN_PVAR_87 : A) (f : A -> B) (t : A -> Prop) (x : A) : (term42 A B GEN_PVAR_87 f t x) = (term43 A B GEN_PVAR_87 f t x).
Proof. exact (MK_COMB (@lem3553081 A B GEN_PVAR_87 x f t) (@lem3553082 A x)). Qed.
Lemma lem3553084 {A B : Type'} (GEN_PVAR_87 : A) (f : A -> B) (t : A -> Prop) : (term44 A B GEN_PVAR_87 f t) = (term45 A B GEN_PVAR_87 f t).
Proof. exact (fun_ext (fun x : A => @lem3553083 A B GEN_PVAR_87 f t x)). Qed.
Lemma lem3553085 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3553086 {A B : Type'} (GEN_PVAR_87 : A) (f : A -> B) (t : A -> Prop) : (term46 A B GEN_PVAR_87 f t) = (term47 A B GEN_PVAR_87 f t).
Proof. exact (MK_COMB (@lem3553085 A) (@lem3553084 A B GEN_PVAR_87 f t)). Qed.
Lemma lem3553087 {A B : Type'} (f : A -> B) (t : A -> Prop) : (term48 A B f t) = (term49 A B f t).
Proof. exact (fun_ext (fun GEN_PVAR_87 : A => @lem3553086 A B GEN_PVAR_87 f t)). Qed.
Lemma lem3553088 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem3553089 {A B : Type'} (f : A -> B) (t : A -> Prop) : (term50 A B f t) = (term10 A B f t).
Proof. exact (MK_COMB (@lem3553088 A) (@lem3553087 A B f t)). Qed.
Lemma lem3553090 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem3553091 {A B : Type'} (x : A) (f : A -> B) (t : A -> Prop) : (term36 A B x f t) = (term51 A B x f t).
Proof. exact (MK_COMB (@lem3553090 A x) (@lem3553089 A B f t)). Qed.
Lemma lem3553092 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3553093 {A B : Type'} (x : A) (f : A -> B) (t : A -> Prop) : (term52 A B x f t) = (term53 A B x f t).
Proof. exact (MK_COMB (@lem3553092) (@lem3553091 A B x f t)). Qed.
Lemma lem3553094 {A B : Type'} (x : A) (f : A -> B) (t : A -> Prop) : (term37 A B f t x) = (term39 A B x f t).
Proof. exact (eq_refl (term37 A B f t x)). Qed.
Lemma lem3553095 {A B : Type'} (x : A) (f : A -> B) (t : A -> Prop) : ((term36 A B x f t) = (term37 A B f t x)) = ((term51 A B x f t) = (term39 A B x f t)).
Proof. exact (MK_COMB (@lem3553093 A B x f t) (@lem3553094 A B x f t)). Qed.
Lemma lem3553096 {A B : Type'} (x : A) (f : A -> B) (t : A -> Prop) : (term51 A B x f t) = (term39 A B x f t).
Proof. exact (EQ_MP (@lem3553095 A B x f t) (@lem3553078 A B f t x)). Qed.
Lemma lem3553098 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term54 A B y f s) = (term55 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem3553099 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term54 A B y f s) = (term55 A B y f s).
Proof. exact (@lem3553098 A B y f s). Qed.
Lemma lem3553100 {A B : Type'} (x : A) (f : A -> B) (t : A -> Prop) : (term39 A B x f t) = (term56 A B x f t).
Proof. exact (@lem3553099 A B (f x) f t). Qed.
Lemma lem3553105 {A B : Type'} (x : A) (f : A -> B) (t : A -> Prop) : (term51 A B x f t) = (term56 A B x f t).
Proof. exact (TRANS (@lem3553096 A B x f t) (@lem3553100 A B x f t)). Qed.
Lemma lem3553111 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3553112 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3553111 A P x). Qed.
Lemma lem3553113 {A : Type'} (t : A -> Prop) (x' : A) : (@IN A x' t) = (t x').
Proof. exact (@lem3553112 A t x'). Qed.
Lemma lem3553114 {A B : Type'} (x : A) (f : A -> B) (x' : A) : (term57 A B x f x') = (term57 A B x f x').
Proof. exact (eq_refl (term57 A B x f x')). Qed.
Lemma lem3553115 {A B : Type'} (x : A) (f : A -> B) (t : A -> Prop) (x' : A) : (term58 A B x f x' t) = (term59 A B x f t x').
Proof. exact (MK_COMB (@lem3553114 A B x f x') (@lem3553113 A t x')). Qed.
Lemma lem3553118 {A B : Type'} (x : A) (f : A -> B) (t : A -> Prop) : (term60 A B x f t) = (term61 A B x f t).
Proof. exact (fun_ext (fun x' : A => @lem3553115 A B x f t x')). Qed.
Lemma lem3553119 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3553120 {A B : Type'} (x : A) (f : A -> B) (t : A -> Prop) : (term56 A B x f t) = (term62 A B x f t).
Proof. exact (MK_COMB (@lem3553119 A) (@lem3553118 A B x f t)). Qed.
Lemma lem3553125 {A B : Type'} (x : A) (f : A -> B) (t : A -> Prop) : (term51 A B x f t) = (term62 A B x f t).
Proof. exact (TRANS (@lem3553105 A B x f t) (@lem3553120 A B x f t)). Qed.
Lemma lem3553126 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3553127 {A B : Type'} (x : A) (f : A -> B) (t : A -> Prop) : (term63 A B x f t) = (term64 A B x f t).
Proof. exact (MK_COMB (@lem3553126) (@lem3553125 A B x f t)). Qed.
Lemma lem3553129 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3553130 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3553129 A P x). Qed.
Lemma lem3553131 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3553130 A t x). Qed.
Lemma lem3553132 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : A) : (term65 A B f x t) = (term66 A B f t x).
Proof. exact (MK_COMB (@lem3553127 A B x f t) (@lem3553131 A t x)). Qed.
Lemma lem3553135 {A B : Type'} (f : A -> B) (t : A -> Prop) : (term67 A B f t) = (term68 A B f t).
Proof. exact (fun_ext (fun x : A => @lem3553132 A B f t x)). Qed.
Lemma lem3553136 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3553137 {A B : Type'} (f : A -> B) (t : A -> Prop) : (term9 A B f t) = (term69 A B f t).
Proof. exact (MK_COMB (@lem3553136 A) (@lem3553135 A B f t)). Qed.
Lemma lem3553142 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term14 A B s f t) = (term71 A B s f t).
Proof. exact (MK_COMB (@lem3553068 A B f s) (@lem3553137 A B f t)). Qed.
Lemma lem3553145 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3553146 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term16 A B s f t) = (term72 A B s f t).
Proof. exact (MK_COMB (@lem3553145) (@lem3553142 A B s f t)). Qed.
Lemma lem3553154 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term54 A B y f s) = (term55 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem3553155 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term54 A B y f s) = (term55 A B y f s).
Proof. exact (@lem3553154 A B y f s). Qed.
Lemma lem3553156 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term73 A B x f s t) = (term74 A B x f s t).
Proof. exact (@lem3553155 A B x f (@INTER A s t)). Qed.
Lemma lem3553166 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term75 A x s t) = (term76 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3553167 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term75 A x s t) = (term76 A s x t).
Proof. exact (@lem3553166 A s x t). Qed.
Lemma lem3553171 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3553172 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3553171 A P x). Qed.
Lemma lem3553173 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3553172 A s x). Qed.
Lemma lem3553174 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3553175 {A : Type'} (s : A -> Prop) (x : A) : (term77 A x s) = (term78 A s x).
Proof. exact (MK_COMB (@lem3553174) (@lem3553173 A s x)). Qed.
Lemma lem3553177 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3553178 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3553177 A P x). Qed.
Lemma lem3553179 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3553178 A t x). Qed.
Lemma lem3553180 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term76 A s x t) = (term79 A s t x).
Proof. exact (MK_COMB (@lem3553175 A s x) (@lem3553179 A t x)). Qed.
Lemma lem3553183 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term75 A x s t) = (term79 A s t x).
Proof. exact (TRANS (@lem3553167 A s x t) (@lem3553180 A s t x)). Qed.
Lemma lem3553184 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term80 A B x f x') = (term80 A B x f x').
Proof. exact (eq_refl (term80 A B x f x')). Qed.
Lemma lem3553185 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term81 A B x f x' s t) = (term82 A B x f s t x').
Proof. exact (MK_COMB (@lem3553184 A B x f x') (@lem3553183 A s t x')). Qed.
Lemma lem3553188 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term83 A B x f s t) = (term84 A B x f s t).
Proof. exact (fun_ext (fun x' : A => @lem3553185 A B x f s t x')). Qed.
Lemma lem3553189 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3553190 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term74 A B x f s t) = (term85 A B x f s t).
Proof. exact (MK_COMB (@lem3553189 A) (@lem3553188 A B x f s t)). Qed.
Lemma lem3553195 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term73 A B x f s t) = (term85 A B x f s t).
Proof. exact (TRANS (@lem3553156 A B x f s t) (@lem3553190 A B x f s t)). Qed.
Lemma lem3553196 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3553197 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term86 A B x f s t) = (term87 A B x f s t).
Proof. exact (MK_COMB (@lem3553196) (@lem3553195 A B x f s t)). Qed.
Lemma lem3553199 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term75 A x s t) = (term76 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3553200 {B : Type'} (s : B -> Prop) (x : B) (t : B -> Prop) : (term75 B x s t) = (term76 B s x t).
Proof. exact (@lem3553199 B s x t). Qed.
Lemma lem3553201 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term88 A B x s f t) = (term89 A B s x f t).
Proof. exact (@lem3553200 B (@IMAGE A B f s) x (@IMAGE A B f t)). Qed.
Lemma lem3553205 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term54 A B y f s) = (term55 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem3553206 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term54 A B y f s) = (term55 A B y f s).
Proof. exact (@lem3553205 A B y f s). Qed.
Lemma lem3553207 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term54 A B x f s) = (term55 A B x f s).
Proof. exact (@lem3553206 A B x f s). Qed.
Lemma lem3553217 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3553218 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3553217 A P x). Qed.
Lemma lem3553219 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3553218 A s x). Qed.
Lemma lem3553220 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term80 A B x f x') = (term80 A B x f x').
Proof. exact (eq_refl (term80 A B x f x')). Qed.
Lemma lem3553221 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term90 A B x f x' s) = (term91 A B x f s x').
Proof. exact (MK_COMB (@lem3553220 A B x f x') (@lem3553219 A s x')). Qed.
Lemma lem3553224 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term92 A B x f s) = (term93 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3553221 A B x f s x')). Qed.
Lemma lem3553225 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3553226 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term55 A B x f s) = (term94 A B x f s).
Proof. exact (MK_COMB (@lem3553225 A) (@lem3553224 A B x f s)). Qed.
Lemma lem3553231 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term54 A B x f s) = (term94 A B x f s).
Proof. exact (TRANS (@lem3553207 A B x f s) (@lem3553226 A B x f s)). Qed.
Lemma lem3553232 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3553233 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term95 A B x f s) = (term96 A B x f s).
Proof. exact (MK_COMB (@lem3553232) (@lem3553231 A B x f s)). Qed.
Lemma lem3553235 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term54 A B y f s) = (term55 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem3553236 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term54 A B y f s) = (term55 A B y f s).
Proof. exact (@lem3553235 A B y f s). Qed.
Lemma lem3553237 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term54 A B x f t) = (term55 A B x f t).
Proof. exact (@lem3553236 A B x f t). Qed.
Lemma lem3553247 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3553248 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3553247 A P x). Qed.
Lemma lem3553249 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3553248 A t x). Qed.
Lemma lem3553250 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term80 A B x f x') = (term80 A B x f x').
Proof. exact (eq_refl (term80 A B x f x')). Qed.
Lemma lem3553251 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term90 A B x f x' t) = (term91 A B x f t x').
Proof. exact (MK_COMB (@lem3553250 A B x f x') (@lem3553249 A t x')). Qed.
Lemma lem3553254 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term92 A B x f t) = (term93 A B x f t).
Proof. exact (fun_ext (fun x' : A => @lem3553251 A B x f t x')). Qed.
Lemma lem3553255 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3553256 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term55 A B x f t) = (term94 A B x f t).
Proof. exact (MK_COMB (@lem3553255 A) (@lem3553254 A B x f t)). Qed.
Lemma lem3553261 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term54 A B x f t) = (term94 A B x f t).
Proof. exact (TRANS (@lem3553237 A B x f t) (@lem3553256 A B x f t)). Qed.
Lemma lem3553262 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term89 A B s x f t) = (term97 A B s x f t).
Proof. exact (MK_COMB (@lem3553233 A B x f s) (@lem3553261 A B x f t)). Qed.
Lemma lem3553265 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term88 A B x s f t) = (term97 A B s x f t).
Proof. exact (TRANS (@lem3553201 A B s x f t) (@lem3553262 A B s x f t)). Qed.
Lemma lem3553266 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : ((term73 A B x f s t) = (term88 A B x s f t)) = ((term85 A B x f s t) = (term97 A B s x f t)).
Proof. exact (MK_COMB (@lem3553197 A B x f s t) (@lem3553265 A B s x f t)). Qed.
Lemma lem3553269 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term98 A B s f t) = (term99 A B s f t).
Proof. exact (fun_ext (fun x : B => @lem3553266 A B s x f t)). Qed.
Lemma lem3553270 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3553271 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term20 A B s f t) = (term100 A B s f t).
Proof. exact (MK_COMB (@lem3553270 B) (@lem3553269 A B s f t)). Qed.
Lemma lem3553276 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term22 A B s f t) = (term101 A B s f t).
Proof. exact (MK_COMB (@lem3553146 A B s f t) (@lem3553271 A B s f t)). Qed.
Lemma lem3553279 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term24 A B s f) = (term102 A B s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3553276 A B s f t)). Qed.
Lemma lem3553280 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3553281 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term26 A B s f) = (term103 A B s f).
Proof. exact (MK_COMB (@lem3553280 A) (@lem3553279 A B s f)). Qed.
Lemma lem3553286 {A B : Type'} (f : A -> B) : (term28 A B f) = (term104 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3553281 A B s f)). Qed.
Lemma lem3553287 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3553288 {A B : Type'} (f : A -> B) : (term30 A B f) = (term105 A B f).
Proof. exact (MK_COMB (@lem3553287 A) (@lem3553286 A B f)). Qed.
Lemma lem3553293 {A B : Type'} : (term32 A B) = (term106 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3553288 A B f)). Qed.
Lemma lem3553294 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3553295 {A B : Type'} : (term34 A B) = (term107 A B).
Proof. exact (MK_COMB (@lem3553294 A B) (@lem3553293 A B)). Qed.
Lemma lem3553300 {A B : Type'} : (term107 A B) = (term34 A B).
Proof. exact (SYM (@lem3553295 A B)). Qed.
Lemma lem3553302 (p : Prop) : p = (term108 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3553303 {A B : Type'} : (term107 A B) = (term109 A B).
Proof. exact (@lem3553302 (term107 A B)). Qed.
Lemma lem3553304 {A B : Type'} : (term109 A B) = (term107 A B).
Proof. exact (SYM (@lem3553303 A B)). Qed.
Lemma lem3553305 {A B : Type'} (h1 : term110 A B) : term110 A B.
Proof. exact (h1). Qed.
Lemma lem3553308 {A B : Type'} (h1 : term109 A B) : term109 A B.
Proof. exact (h1). Qed.
Lemma lem3553309 {A B : Type'} : term111 A B.
Proof. exact (fun h0 : term109 A B => @lem3553308 A B h0). Qed.
Lemma lem3553310 {A B : Type'} (h1 : term111 A B) : term111 A B.
Proof. exact (h1). Qed.
Lemma lem3553311 {A B : Type'} (h1 : term109 A B) : term109 A B.
Proof. exact (h1). Qed.
Lemma lem3553312 {A B : Type'} (h1 : term109 A B) (h2 : term111 A B) : term109 A B.
Proof. exact (@lem3553310 A B h2 (@lem3553311 A B h1)). Qed.
Lemma lem3553313 {A B : Type'} (h1 : term109 A B) : term112 A B.
Proof. exact (fun h0 : term111 A B => @lem3553312 A B h1 h0). Qed.
Lemma lem3553314 {A B : Type'} (h1 : term111 A B) : term111 A B.
Proof. exact (h1). Qed.
Lemma lem3553315 {A B : Type'} (h1 : term109 A B) (h2 : term111 A B) : term109 A B.
Proof. exact (@lem3553313 A B h1 (@lem3553314 A B h2)). Qed.
Lemma lem3553316 {A B : Type'} (h1 : term111 A B) : term111 A B.
Proof. exact (fun h0 : term109 A B => @lem3553315 A B h0 h1). Qed.
Lemma lem3553317 {A B : Type'} : term113 A B.
Proof. exact (fun h0 : term111 A B => @lem3553316 A B h0). Qed.
Lemma lem3553320 {A B : Type'} : term111 A B.
Proof. exact (@lem3553317 A B (@lem3553309 A B)). Qed.
Lemma lem3553321 {A B : Type'} : term111 A B.
Proof. exact (@lem3553320 A B). Qed.
Lemma lem3553323 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3553324 {A B : Type'} : (term109 A B) = (term114 A B).
Proof. exact (@lem3553323 (term110 A B)). Qed.
Lemma lem3553326 (t : Prop) : (term115 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3553327 {A B : Type'} : (term114 A B) = (term107 A B).
Proof. exact (@lem3553326 (term107 A B)). Qed.
Lemma lem3553554 {A B : Type'} : (term109 A B) = (term107 A B).
Proof. exact (TRANS (@lem3553324 A B) (@lem3553327 A B)). Qed.
Lemma lem3553559 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term91 A B x f t x') = (term91 A B x f t x').
Proof. exact (eq_refl (term91 A B x f t x')). Qed.
Lemma lem3553560 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term93 A B x f t) = (term93 A B x f t).
Proof. exact (fun_ext (fun x' : A => @lem3553559 A B x f t x')). Qed.
Lemma lem3553561 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3553562 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term94 A B x f t) = (term94 A B x f t).
Proof. exact (MK_COMB (@lem3553561 A) (@lem3553560 A B x f t)). Qed.
Lemma lem3553567 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term91 A B x f s x') = (term91 A B x f s x').
Proof. exact (eq_refl (term91 A B x f s x')). Qed.
Lemma lem3553568 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term93 A B x f s) = (term93 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3553567 A B x f s x')). Qed.
Lemma lem3553569 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3553570 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term94 A B x f s) = (term94 A B x f s).
Proof. exact (MK_COMB (@lem3553569 A) (@lem3553568 A B x f s)). Qed.
Lemma lem3553571 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3553572 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term96 A B x f s) = (term96 A B x f s).
Proof. exact (MK_COMB (@lem3553571) (@lem3553570 A B x f s)). Qed.
Lemma lem3553573 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term97 A B s x f t) = (term97 A B s x f t).
Proof. exact (MK_COMB (@lem3553572 A B x f s) (@lem3553562 A B x f t)). Qed.
Lemma lem3553582 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term82 A B x f s t x') = (term82 A B x f s t x').
Proof. exact (eq_refl (term82 A B x f s t x')). Qed.
Lemma lem3553583 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term84 A B x f s t) = (term84 A B x f s t).
Proof. exact (fun_ext (fun x' : A => @lem3553582 A B x f s t x')). Qed.
Lemma lem3553584 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3553585 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term85 A B x f s t) = (term85 A B x f s t).
Proof. exact (MK_COMB (@lem3553584 A) (@lem3553583 A B x f s t)). Qed.
Lemma lem3553586 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3553587 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term87 A B x f s t) = (term87 A B x f s t).
Proof. exact (MK_COMB (@lem3553586) (@lem3553585 A B x f s t)). Qed.
Lemma lem3553588 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : ((term85 A B x f s t) = (term97 A B s x f t)) = ((term85 A B x f s t) = (term97 A B s x f t)).
Proof. exact (MK_COMB (@lem3553587 A B x f s t) (@lem3553573 A B s x f t)). Qed.
Lemma lem3553589 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term99 A B s f t) = (term99 A B s f t).
Proof. exact (fun_ext (fun x : B => @lem3553588 A B s x f t)). Qed.
Lemma lem3553590 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3553591 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term100 A B s f t) = (term100 A B s f t).
Proof. exact (MK_COMB (@lem3553590 B) (@lem3553589 A B s f t)). Qed.
Lemma lem3553592 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem3553597 {A B : Type'} (x : A) (f : A -> B) (t : A -> Prop) (x' : A) : (term59 A B x f t x') = (term59 A B x f t x').
Proof. exact (eq_refl (term59 A B x f t x')). Qed.
Lemma lem3553598 {A B : Type'} (x : A) (f : A -> B) (t : A -> Prop) : (term61 A B x f t) = (term61 A B x f t).
Proof. exact (fun_ext (fun x' : A => @lem3553597 A B x f t x')). Qed.
Lemma lem3553599 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3553600 {A B : Type'} (x : A) (f : A -> B) (t : A -> Prop) : (term62 A B x f t) = (term62 A B x f t).
Proof. exact (MK_COMB (@lem3553599 A) (@lem3553598 A B x f t)). Qed.
Lemma lem3553601 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3553602 {A B : Type'} (x : A) (f : A -> B) (t : A -> Prop) : (term64 A B x f t) = (term64 A B x f t).
Proof. exact (MK_COMB (@lem3553601) (@lem3553600 A B x f t)). Qed.
Lemma lem3553603 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : A) : (term66 A B f t x) = (term66 A B f t x).
Proof. exact (MK_COMB (@lem3553602 A B x f t) (@lem3553592 A t x)). Qed.
Lemma lem3553604 {A B : Type'} (f : A -> B) (t : A -> Prop) : (term68 A B f t) = (term68 A B f t).
Proof. exact (fun_ext (fun x : A => @lem3553603 A B f t x)). Qed.
Lemma lem3553605 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3553606 {A B : Type'} (f : A -> B) (t : A -> Prop) : (term69 A B f t) = (term69 A B f t).
Proof. exact (MK_COMB (@lem3553605 A) (@lem3553604 A B f t)). Qed.
Lemma lem3553607 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem3553612 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (x' : A) : (term59 A B x f s x') = (term59 A B x f s x').
Proof. exact (eq_refl (term59 A B x f s x')). Qed.
Lemma lem3553613 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term61 A B x f s) = (term61 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3553612 A B x f s x')). Qed.
Lemma lem3553614 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3553615 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term62 A B x f s) = (term62 A B x f s).
Proof. exact (MK_COMB (@lem3553614 A) (@lem3553613 A B x f s)). Qed.
Lemma lem3553616 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3553617 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term64 A B x f s) = (term64 A B x f s).
Proof. exact (MK_COMB (@lem3553616) (@lem3553615 A B x f s)). Qed.
Lemma lem3553618 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term66 A B f s x) = (term66 A B f s x).
Proof. exact (MK_COMB (@lem3553617 A B x f s) (@lem3553607 A s x)). Qed.
Lemma lem3553619 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term68 A B f s) = (term68 A B f s).
Proof. exact (fun_ext (fun x : A => @lem3553618 A B f s x)). Qed.
Lemma lem3553620 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3553621 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term69 A B f s) = (term69 A B f s).
Proof. exact (MK_COMB (@lem3553620 A) (@lem3553619 A B f s)). Qed.
Lemma lem3553622 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3553623 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term70 A B f s) = (term70 A B f s).
Proof. exact (MK_COMB (@lem3553622) (@lem3553621 A B f s)). Qed.
Lemma lem3553624 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term71 A B s f t) = (term71 A B s f t).
Proof. exact (MK_COMB (@lem3553623 A B f s) (@lem3553606 A B f t)). Qed.
Lemma lem3553625 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3553626 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term72 A B s f t) = (term72 A B s f t).
Proof. exact (MK_COMB (@lem3553625) (@lem3553624 A B s f t)). Qed.
Lemma lem3553627 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term101 A B s f t) = (term101 A B s f t).
Proof. exact (MK_COMB (@lem3553626 A B s f t) (@lem3553591 A B s f t)). Qed.
Lemma lem3553628 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term102 A B s f) = (term102 A B s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3553627 A B s f t)). Qed.
Lemma lem3553629 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3553630 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term103 A B s f) = (term103 A B s f).
Proof. exact (MK_COMB (@lem3553629 A) (@lem3553628 A B s f)). Qed.
Lemma lem3553631 {A B : Type'} (f : A -> B) : (term104 A B f) = (term104 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3553630 A B s f)). Qed.
Lemma lem3553632 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3553633 {A B : Type'} (f : A -> B) : (term105 A B f) = (term105 A B f).
Proof. exact (MK_COMB (@lem3553632 A) (@lem3553631 A B f)). Qed.
Lemma lem3553634 {A B : Type'} : (term106 A B) = (term106 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3553633 A B f)). Qed.
Lemma lem3553635 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3553636 {A B : Type'} : (term107 A B) = (term107 A B).
Proof. exact (MK_COMB (@lem3553635 A B) (@lem3553634 A B)). Qed.
Lemma lem3553727 {A B : Type'} : (term109 A B) = (term107 A B).
Proof. exact (TRANS (@lem3553554 A B) (@lem3553636 A B)). Qed.
Lemma lem3553728 {A B : Type'} : (term107 A B) = (term109 A B).
Proof. exact (SYM (@lem3553727 A B)). Qed.
Lemma lem3553729 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term71 A B s f t) : term71 A B s f t.
Proof. exact (h1). Qed.
Lemma lem3553731 (p : Prop) : p = (term108 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3553732 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : ((term85 A B x f s t) = (term97 A B s x f t)) = (term116 A B s x f t).
Proof. exact (@lem3553731 ((term85 A B x f s t) = (term97 A B s x f t))). Qed.
Lemma lem3553733 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term116 A B s x f t) = ((term85 A B x f s t) = (term97 A B s x f t)).
Proof. exact (SYM (@lem3553732 A B s x f t)). Qed.
Lemma lem3553734 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term117 A B s x f t) : term117 A B s x f t.
Proof. exact (h1). Qed.
Lemma lem3553741 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (x' : A) : (term118 A B x f s x') = (term119 A B x f s x').
Proof. exact (@lem17045 ((f x) = (f x')) (s x')). Qed.
Lemma lem3553742 {A : Type'} (P : A -> Prop) : (term120 A P) = (term121 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem3553743 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term122 A B x f s) = (term123 A B x f s).
Proof. exact (@lem3553742 A (term61 A B x f s)). Qed.
Lemma lem3553744 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (x' : A) : (term124 A B x f s x') = (term59 A B x f s x').
Proof. exact (eq_refl (term124 A B x f s x')). Qed.
Lemma lem3553745 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3553746 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (x' : A) : (term125 A B x f s x') = (term118 A B x f s x').
Proof. exact (MK_COMB (@lem3553745) (@lem3553744 A B x f s x')). Qed.
Lemma lem3553747 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (x' : A) : (term125 A B x f s x') = (term119 A B x f s x').
Proof. exact (TRANS (@lem3553746 A B x f s x') (@lem3553741 A B x f s x')). Qed.
Lemma lem3553748 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term126 A B x f s) = (term127 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3553747 A B x f s x')). Qed.
Lemma lem3553749 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3553750 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term123 A B x f s) = (term128 A B x f s).
Proof. exact (MK_COMB (@lem3553749 A) (@lem3553748 A B x f s)). Qed.
Lemma lem3553751 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term122 A B x f s) = (term128 A B x f s).
Proof. exact (TRANS (@lem3553743 A B x f s) (@lem3553750 A B x f s)). Qed.
Lemma lem3553752 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem3553753 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3553754 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term129 A B x f s) = (term130 A B x f s).
Proof. exact (MK_COMB (@lem3553753) (@lem3553751 A B x f s)). Qed.
Lemma lem3553755 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term131 A B f s x) = (term132 A B f s x).
Proof. exact (MK_COMB (@lem3553754 A B x f s) (@lem3553752 A s x)). Qed.
Lemma lem3553756 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term66 A B f s x) = (term131 A B f s x).
Proof. exact (@lem17265 (term62 A B x f s) (s x)). Qed.
Lemma lem3553757 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term66 A B f s x) = (term132 A B f s x).
Proof. exact (TRANS (@lem3553756 A B f s x) (@lem3553755 A B f s x)). Qed.
Lemma lem3553758 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term68 A B f s) = (term133 A B f s).
Proof. exact (fun_ext (fun x : A => @lem3553757 A B f s x)). Qed.
Lemma lem3553759 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3553760 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term69 A B f s) = (term134 A B f s).
Proof. exact (MK_COMB (@lem3553759 A) (@lem3553758 A B f s)). Qed.
Lemma lem3553767 {A B : Type'} (x : A) (f : A -> B) (t : A -> Prop) (x' : A) : (term118 A B x f t x') = (term119 A B x f t x').
Proof. exact (@lem17045 ((f x) = (f x')) (t x')). Qed.
Lemma lem3553768 {A : Type'} (P : A -> Prop) : (term120 A P) = (term121 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem3553769 {A B : Type'} (x : A) (f : A -> B) (t : A -> Prop) : (term122 A B x f t) = (term123 A B x f t).
Proof. exact (@lem3553768 A (term61 A B x f t)). Qed.
Lemma lem3553770 {A B : Type'} (x : A) (f : A -> B) (t : A -> Prop) (x' : A) : (term124 A B x f t x') = (term59 A B x f t x').
Proof. exact (eq_refl (term124 A B x f t x')). Qed.
Lemma lem3553771 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3553772 {A B : Type'} (x : A) (f : A -> B) (t : A -> Prop) (x' : A) : (term125 A B x f t x') = (term118 A B x f t x').
Proof. exact (MK_COMB (@lem3553771) (@lem3553770 A B x f t x')). Qed.
Lemma lem3553773 {A B : Type'} (x : A) (f : A -> B) (t : A -> Prop) (x' : A) : (term125 A B x f t x') = (term119 A B x f t x').
Proof. exact (TRANS (@lem3553772 A B x f t x') (@lem3553767 A B x f t x')). Qed.
Lemma lem3553774 {A B : Type'} (x : A) (f : A -> B) (t : A -> Prop) : (term126 A B x f t) = (term127 A B x f t).
Proof. exact (fun_ext (fun x' : A => @lem3553773 A B x f t x')). Qed.
Lemma lem3553775 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3553776 {A B : Type'} (x : A) (f : A -> B) (t : A -> Prop) : (term123 A B x f t) = (term128 A B x f t).
Proof. exact (MK_COMB (@lem3553775 A) (@lem3553774 A B x f t)). Qed.
Lemma lem3553777 {A B : Type'} (x : A) (f : A -> B) (t : A -> Prop) : (term122 A B x f t) = (term128 A B x f t).
Proof. exact (TRANS (@lem3553769 A B x f t) (@lem3553776 A B x f t)). Qed.
Lemma lem3553778 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem3553779 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3553780 {A B : Type'} (x : A) (f : A -> B) (t : A -> Prop) : (term129 A B x f t) = (term130 A B x f t).
Proof. exact (MK_COMB (@lem3553779) (@lem3553777 A B x f t)). Qed.
Lemma lem3553781 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : A) : (term131 A B f t x) = (term132 A B f t x).
Proof. exact (MK_COMB (@lem3553780 A B x f t) (@lem3553778 A t x)). Qed.
Lemma lem3553782 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : A) : (term66 A B f t x) = (term131 A B f t x).
Proof. exact (@lem17265 (term62 A B x f t) (t x)). Qed.
Lemma lem3553783 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : A) : (term66 A B f t x) = (term132 A B f t x).
Proof. exact (TRANS (@lem3553782 A B f t x) (@lem3553781 A B f t x)). Qed.
Lemma lem3553784 {A B : Type'} (f : A -> B) (t : A -> Prop) : (term68 A B f t) = (term133 A B f t).
Proof. exact (fun_ext (fun x : A => @lem3553783 A B f t x)). Qed.
Lemma lem3553785 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3553786 {A B : Type'} (f : A -> B) (t : A -> Prop) : (term69 A B f t) = (term134 A B f t).
Proof. exact (MK_COMB (@lem3553785 A) (@lem3553784 A B f t)). Qed.
Lemma lem3553787 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3553788 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term70 A B f s) = (term135 A B f s).
Proof. exact (MK_COMB (@lem3553787) (@lem3553760 A B f s)). Qed.
Lemma lem3553953 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term71 A B s f t) = (term136 A B s f t).
Proof. exact (MK_COMB (@lem3553788 A B f s) (@lem3553786 A B f t)). Qed.
Lemma lem3553954 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term71 A B s f t) : term136 A B s f t.
Proof. exact (EQ_MP (@lem3553953 A B s f t) (@lem3553729 A B s f t h1)). Qed.
Lemma lem3553965 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term137 A s t x) = (term138 A s t x).
Proof. exact (@lem17045 (s x) (t x)). Qed.
Lemma lem3553970 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term139 A B x f x') = (term139 A B x f x').
Proof. exact (eq_refl (term139 A B x f x')). Qed.
Lemma lem3553971 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term140 A B x f s t x') = (term141 A B x f s t x').
Proof. exact (MK_COMB (@lem3553970 A B x f x') (@lem3553965 A s t x')). Qed.
Lemma lem3553972 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term142 A B x f s t x') = (term140 A B x f s t x').
Proof. exact (@lem17045 (x = (f x')) (term79 A s t x')). Qed.
Lemma lem3553973 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term142 A B x f s t x') = (term141 A B x f s t x').
Proof. exact (TRANS (@lem3553972 A B x f s t x') (@lem3553971 A B x f s t x')). Qed.
Lemma lem3553976 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term82 A B x f s t x') = (term82 A B x f s t x').
Proof. exact (eq_refl (term82 A B x f s t x')). Qed.
Lemma lem3553977 {A : Type'} (P : A -> Prop) : (term120 A P) = (term121 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem3553978 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term143 A B x f s t) = (term144 A B x f s t).
Proof. exact (@lem3553977 A (term84 A B x f s t)). Qed.
Lemma lem3553979 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term145 A B x f s t x') = (term82 A B x f s t x').
Proof. exact (eq_refl (term145 A B x f s t x')). Qed.
Lemma lem3553980 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3553981 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term146 A B x f s t x') = (term142 A B x f s t x').
Proof. exact (MK_COMB (@lem3553980) (@lem3553979 A B x f s t x')). Qed.
Lemma lem3553982 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term146 A B x f s t x') = (term141 A B x f s t x').
Proof. exact (TRANS (@lem3553981 A B x f s t x') (@lem3553973 A B x f s t x')). Qed.
Lemma lem3553983 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term147 A B x f s t) = (term148 A B x f s t).
Proof. exact (fun_ext (fun x' : A => @lem3553982 A B x f s t x')). Qed.
Lemma lem3553984 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3553985 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term144 A B x f s t) = (term149 A B x f s t).
Proof. exact (MK_COMB (@lem3553984 A) (@lem3553983 A B x f s t)). Qed.
Lemma lem3553986 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term143 A B x f s t) = (term149 A B x f s t).
Proof. exact (TRANS (@lem3553978 A B x f s t) (@lem3553985 A B x f s t)). Qed.
Lemma lem3553987 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term84 A B x f s t) = (term84 A B x f s t).
Proof. exact (fun_ext (fun x' : A => @lem3553976 A B x f s t x')). Qed.
Lemma lem3553988 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3553989 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term85 A B x f s t) = (term85 A B x f s t).
Proof. exact (MK_COMB (@lem3553988 A) (@lem3553987 A B x f s t)). Qed.
Lemma lem3553998 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term150 A B x f s x') = (term151 A B x f s x').
Proof. exact (@lem17045 (x = (f x')) (s x')). Qed.
Lemma lem3554001 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term91 A B x f s x') = (term91 A B x f s x').
Proof. exact (eq_refl (term91 A B x f s x')). Qed.
Lemma lem3554002 {A : Type'} (P : A -> Prop) : (term120 A P) = (term121 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem3554003 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term152 A B x f s) = (term153 A B x f s).
Proof. exact (@lem3554002 A (term93 A B x f s)). Qed.
Lemma lem3554004 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term154 A B x f s x') = (term91 A B x f s x').
Proof. exact (eq_refl (term154 A B x f s x')). Qed.
Lemma lem3554005 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3554006 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term155 A B x f s x') = (term150 A B x f s x').
Proof. exact (MK_COMB (@lem3554005) (@lem3554004 A B x f s x')). Qed.
Lemma lem3554007 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term155 A B x f s x') = (term151 A B x f s x').
Proof. exact (TRANS (@lem3554006 A B x f s x') (@lem3553998 A B x f s x')). Qed.
Lemma lem3554008 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term156 A B x f s) = (term157 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3554007 A B x f s x')). Qed.
Lemma lem3554009 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3554010 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term153 A B x f s) = (term158 A B x f s).
Proof. exact (MK_COMB (@lem3554009 A) (@lem3554008 A B x f s)). Qed.
Lemma lem3554011 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term152 A B x f s) = (term158 A B x f s).
Proof. exact (TRANS (@lem3554003 A B x f s) (@lem3554010 A B x f s)). Qed.
Lemma lem3554012 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term93 A B x f s) = (term93 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3554001 A B x f s x')). Qed.
Lemma lem3554013 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3554014 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term94 A B x f s) = (term94 A B x f s).
Proof. exact (MK_COMB (@lem3554013 A) (@lem3554012 A B x f s)). Qed.
Lemma lem3554023 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term150 A B x f t x') = (term151 A B x f t x').
Proof. exact (@lem17045 (x = (f x')) (t x')). Qed.
Lemma lem3554026 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term91 A B x f t x') = (term91 A B x f t x').
Proof. exact (eq_refl (term91 A B x f t x')). Qed.
Lemma lem3554027 {A : Type'} (P : A -> Prop) : (term120 A P) = (term121 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem3554028 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term152 A B x f t) = (term153 A B x f t).
Proof. exact (@lem3554027 A (term93 A B x f t)). Qed.
Lemma lem3554029 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term154 A B x f t x') = (term91 A B x f t x').
Proof. exact (eq_refl (term154 A B x f t x')). Qed.
Lemma lem3554030 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3554031 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term155 A B x f t x') = (term150 A B x f t x').
Proof. exact (MK_COMB (@lem3554030) (@lem3554029 A B x f t x')). Qed.
Lemma lem3554032 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term155 A B x f t x') = (term151 A B x f t x').
Proof. exact (TRANS (@lem3554031 A B x f t x') (@lem3554023 A B x f t x')). Qed.
Lemma lem3554033 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term156 A B x f t) = (term157 A B x f t).
Proof. exact (fun_ext (fun x' : A => @lem3554032 A B x f t x')). Qed.
Lemma lem3554034 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3554035 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term153 A B x f t) = (term158 A B x f t).
Proof. exact (MK_COMB (@lem3554034 A) (@lem3554033 A B x f t)). Qed.
Lemma lem3554036 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term152 A B x f t) = (term158 A B x f t).
Proof. exact (TRANS (@lem3554028 A B x f t) (@lem3554035 A B x f t)). Qed.
Lemma lem3554037 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term93 A B x f t) = (term93 A B x f t).
Proof. exact (fun_ext (fun x' : A => @lem3554026 A B x f t x')). Qed.
Lemma lem3554038 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3554039 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term94 A B x f t) = (term94 A B x f t).
Proof. exact (MK_COMB (@lem3554038 A) (@lem3554037 A B x f t)). Qed.
Lemma lem3554040 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3554041 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term159 A B x f s) = (term160 A B x f s).
Proof. exact (MK_COMB (@lem3554040) (@lem3554011 A B x f s)). Qed.
Lemma lem3554042 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term161 A B s x f t) = (term162 A B s x f t).
Proof. exact (MK_COMB (@lem3554041 A B x f s) (@lem3554036 A B x f t)). Qed.
Lemma lem3554043 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term163 A B s x f t) = (term161 A B s x f t).
Proof. exact (@lem17045 (term94 A B x f s) (term94 A B x f t)). Qed.
Lemma lem3554044 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term163 A B s x f t) = (term162 A B s x f t).
Proof. exact (TRANS (@lem3554043 A B s x f t) (@lem3554042 A B s x f t)). Qed.
Lemma lem3554045 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3554046 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term96 A B x f s) = (term96 A B x f s).
Proof. exact (MK_COMB (@lem3554045) (@lem3554014 A B x f s)). Qed.
Lemma lem3554047 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term97 A B s x f t) = (term97 A B s x f t).
Proof. exact (MK_COMB (@lem3554046 A B x f s) (@lem3554039 A B x f t)). Qed.
Lemma lem3554048 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3554049 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term164 A B x f s t) = (term165 A B x f s t).
Proof. exact (MK_COMB (@lem3554048) (@lem3553986 A B x f s t)). Qed.
Lemma lem3554050 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term166 A B s x f t) = (term167 A B s x f t).
Proof. exact (MK_COMB (@lem3554049 A B x f s t) (@lem3554047 A B s x f t)). Qed.
Lemma lem3554051 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3554052 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term168 A B x f s t) = (term168 A B x f s t).
Proof. exact (MK_COMB (@lem3554051) (@lem3553989 A B x f s t)). Qed.
Lemma lem3554053 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term169 A B s x f t) = (term170 A B s x f t).
Proof. exact (MK_COMB (@lem3554052 A B x f s t) (@lem3554044 A B s x f t)). Qed.
Lemma lem3554054 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3554055 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term171 A B s x f t) = (term172 A B s x f t).
Proof. exact (MK_COMB (@lem3554054) (@lem3554053 A B s x f t)). Qed.
Lemma lem3554056 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term173 A B s x f t) = (term174 A B s x f t).
Proof. exact (MK_COMB (@lem3554055 A B s x f t) (@lem3554050 A B s x f t)). Qed.
Lemma lem3554057 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term117 A B s x f t) = (term173 A B s x f t).
Proof. exact (@lem17646 (term85 A B x f s t) (term97 A B s x f t)). Qed.
Lemma lem3554058 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term117 A B s x f t) = (term174 A B s x f t).
Proof. exact (TRANS (@lem3554057 A B s x f t) (@lem3554056 A B s x f t)). Qed.
Lemma lem3554317 {A : Type'} (P : A -> Prop) (Q : Prop) : (term175 A P Q) = (term176 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3554318 {A : Type'} (P : A -> Prop) (Q : Prop) : (term175 A P Q) = (term176 A P Q).
Proof. exact (@lem3554317 A P Q). Qed.
Lemma lem3554319 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term177 A B s x f t) = (term178 A B s x f t).
Proof. exact (@lem3554318 A (term84 A B x f s t) (term162 A B s x f t)). Qed.
Lemma lem3554320 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term145 A B x f s t x') = (term82 A B x f s t x').
Proof. exact (eq_refl (term145 A B x f s t x')). Qed.
Lemma lem3554321 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term179 A B x f s t) = (term84 A B x f s t).
Proof. exact (fun_ext (fun x' : A => @lem3554320 A B x f s t x')). Qed.
Lemma lem3554322 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3554323 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term180 A B x f s t) = (term85 A B x f s t).
Proof. exact (MK_COMB (@lem3554322 A) (@lem3554321 A B x f s t)). Qed.
Lemma lem3554324 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3554325 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term181 A B x f s t) = (term168 A B x f s t).
Proof. exact (MK_COMB (@lem3554324) (@lem3554323 A B x f s t)). Qed.
Lemma lem3554326 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term162 A B s x f t) = (term162 A B s x f t).
Proof. exact (eq_refl (term162 A B s x f t)). Qed.
Lemma lem3554327 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term177 A B s x f t) = (term170 A B s x f t).
Proof. exact (MK_COMB (@lem3554325 A B x f s t) (@lem3554326 A B s x f t)). Qed.
Lemma lem3554328 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3554329 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term182 A B s x f t) = (term183 A B s x f t).
Proof. exact (MK_COMB (@lem3554328) (@lem3554327 A B s x f t)). Qed.
Lemma lem3554330 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term145 A B x f s t x') = (term82 A B x f s t x').
Proof. exact (eq_refl (term145 A B x f s t x')). Qed.
Lemma lem3554331 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3554332 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term184 A B x f s t x') = (term185 A B x f s t x').
Proof. exact (MK_COMB (@lem3554331) (@lem3554330 A B x f s t x')). Qed.
Lemma lem3554333 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term162 A B s x f t) = (term162 A B s x f t).
Proof. exact (eq_refl (term162 A B s x f t)). Qed.
Lemma lem3554334 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (t : A -> Prop) : (term186 A B x s x' f t) = (term187 A B x s x' f t).
Proof. exact (MK_COMB (@lem3554332 A B x' f s t x) (@lem3554333 A B s x' f t)). Qed.
Lemma lem3554335 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term188 A B s x f t) = (term189 A B s x f t).
Proof. exact (fun_ext (fun x' : A => @lem3554334 A B x' s x f t)). Qed.
Lemma lem3554336 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3554337 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term178 A B s x f t) = (term190 A B s x f t).
Proof. exact (MK_COMB (@lem3554336 A) (@lem3554335 A B s x f t)). Qed.
Lemma lem3554338 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : ((term177 A B s x f t) = (term178 A B s x f t)) = ((term170 A B s x f t) = (term190 A B s x f t)).
Proof. exact (MK_COMB (@lem3554329 A B s x f t) (@lem3554337 A B s x f t)). Qed.
Lemma lem3554339 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term170 A B s x f t) = (term190 A B s x f t).
Proof. exact (EQ_MP (@lem3554338 A B s x f t) (@lem3554319 A B s x f t)). Qed.
Lemma lem3554340 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3554341 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term172 A B s x f t) = (term191 A B s x f t).
Proof. exact (MK_COMB (@lem3554340) (@lem3554339 A B s x f t)). Qed.
Lemma lem3554343 {A : Type'} (P : A -> Prop) (Q : Prop) : (term175 A P Q) = (term176 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3554344 {A : Type'} (P : A -> Prop) (Q : Prop) : (term175 A P Q) = (term176 A P Q).
Proof. exact (@lem3554343 A P Q). Qed.
Lemma lem3554345 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term192 A B s x f t) = (term193 A B s x f t).
Proof. exact (@lem3554344 A (term93 A B x f s) (term94 A B x f t)). Qed.
Lemma lem3554346 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term154 A B x f s x') = (term91 A B x f s x').
Proof. exact (eq_refl (term154 A B x f s x')). Qed.
Lemma lem3554347 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term194 A B x f s) = (term93 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3554346 A B x f s x')). Qed.
Lemma lem3554348 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3554349 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term195 A B x f s) = (term94 A B x f s).
Proof. exact (MK_COMB (@lem3554348 A) (@lem3554347 A B x f s)). Qed.
Lemma lem3554350 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3554351 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term196 A B x f s) = (term96 A B x f s).
Proof. exact (MK_COMB (@lem3554350) (@lem3554349 A B x f s)). Qed.
Lemma lem3554352 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term94 A B x f t) = (term94 A B x f t).
Proof. exact (eq_refl (term94 A B x f t)). Qed.
Lemma lem3554353 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term192 A B s x f t) = (term97 A B s x f t).
Proof. exact (MK_COMB (@lem3554351 A B x f s) (@lem3554352 A B x f t)). Qed.
Lemma lem3554354 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3554355 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term197 A B s x f t) = (term198 A B s x f t).
Proof. exact (MK_COMB (@lem3554354) (@lem3554353 A B s x f t)). Qed.
Lemma lem3554356 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term154 A B x f s x') = (term91 A B x f s x').
Proof. exact (eq_refl (term154 A B x f s x')). Qed.
Lemma lem3554357 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3554358 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term199 A B x f s x') = (term200 A B x f s x').
Proof. exact (MK_COMB (@lem3554357) (@lem3554356 A B x f s x')). Qed.
Lemma lem3554359 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term94 A B x f t) = (term94 A B x f t).
Proof. exact (eq_refl (term94 A B x f t)). Qed.
Lemma lem3554360 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term201 A B s x x' f t) = (term202 A B s x x' f t).
Proof. exact (MK_COMB (@lem3554358 A B x' f s x) (@lem3554359 A B x' f t)). Qed.
Lemma lem3554361 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term203 A B s x f t) = (term204 A B s x f t).
Proof. exact (fun_ext (fun x' : A => @lem3554360 A B s x' x f t)). Qed.
Lemma lem3554362 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3554363 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term193 A B s x f t) = (term205 A B s x f t).
Proof. exact (MK_COMB (@lem3554362 A) (@lem3554361 A B s x f t)). Qed.
Lemma lem3554364 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : ((term192 A B s x f t) = (term193 A B s x f t)) = ((term97 A B s x f t) = (term205 A B s x f t)).
Proof. exact (MK_COMB (@lem3554355 A B s x f t) (@lem3554363 A B s x f t)). Qed.
Lemma lem3554365 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term97 A B s x f t) = (term205 A B s x f t).
Proof. exact (EQ_MP (@lem3554364 A B s x f t) (@lem3554345 A B s x f t)). Qed.
Lemma lem3554367 {A : Type'} (P : Prop) (Q : A -> Prop) : (term206 A P Q) = (term207 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3554368 {A : Type'} (P : Prop) (Q : A -> Prop) : (term206 A P Q) = (term207 A P Q).
Proof. exact (@lem3554367 A P Q). Qed.
Lemma lem3554369 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term208 A B s x x' f t) = (term209 A B s x x' f t).
Proof. exact (@lem3554368 A (term91 A B x' f s x) (term93 A B x' f t)). Qed.
Lemma lem3554370 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term154 A B x f t x') = (term91 A B x f t x').
Proof. exact (eq_refl (term154 A B x f t x')). Qed.
Lemma lem3554371 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term194 A B x f t) = (term93 A B x f t).
Proof. exact (fun_ext (fun x' : A => @lem3554370 A B x f t x')). Qed.
Lemma lem3554372 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3554373 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term195 A B x f t) = (term94 A B x f t).
Proof. exact (MK_COMB (@lem3554372 A) (@lem3554371 A B x f t)). Qed.
Lemma lem3554374 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term200 A B x f s x') = (term200 A B x f s x').
Proof. exact (eq_refl (term200 A B x f s x')). Qed.
Lemma lem3554375 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term208 A B s x x' f t) = (term202 A B s x x' f t).
Proof. exact (MK_COMB (@lem3554374 A B x' f s x) (@lem3554373 A B x' f t)). Qed.
Lemma lem3554376 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3554377 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term210 A B s x x' f t) = (term211 A B s x x' f t).
Proof. exact (MK_COMB (@lem3554376) (@lem3554375 A B s x x' f t)). Qed.
Lemma lem3554378 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term154 A B x f t x') = (term91 A B x f t x').
Proof. exact (eq_refl (term154 A B x f t x')). Qed.
Lemma lem3554379 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term200 A B x f s x') = (term200 A B x f s x').
Proof. exact (eq_refl (term200 A B x f s x')). Qed.
Lemma lem3554380 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) (x'' : A) : (term212 A B s x x' f t x'') = (term213 A B s x x' f t x'').
Proof. exact (MK_COMB (@lem3554379 A B x' f s x) (@lem3554378 A B x' f t x'')). Qed.
Lemma lem3554381 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term214 A B s x x' f t) = (term215 A B s x x' f t).
Proof. exact (fun_ext (fun x'' : A => @lem3554380 A B s x x' f t x'')). Qed.
Lemma lem3554382 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3554383 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term209 A B s x x' f t) = (term216 A B s x x' f t).
Proof. exact (MK_COMB (@lem3554382 A) (@lem3554381 A B s x x' f t)). Qed.
Lemma lem3554384 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : ((term208 A B s x x' f t) = (term209 A B s x x' f t)) = ((term202 A B s x x' f t) = (term216 A B s x x' f t)).
Proof. exact (MK_COMB (@lem3554377 A B s x x' f t) (@lem3554383 A B s x x' f t)). Qed.
Lemma lem3554385 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term202 A B s x x' f t) = (term216 A B s x x' f t).
Proof. exact (EQ_MP (@lem3554384 A B s x x' f t) (@lem3554369 A B s x x' f t)). Qed.
Lemma lem3554386 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term204 A B s x f t) = (term217 A B s x f t).
Proof. exact (fun_ext (fun x' : A => @lem3554385 A B s x' x f t)). Qed.
Lemma lem3554387 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3554388 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term205 A B s x f t) = (term218 A B s x f t).
Proof. exact (MK_COMB (@lem3554387 A) (@lem3554386 A B s x f t)). Qed.
Lemma lem3554389 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term97 A B s x f t) = (term218 A B s x f t).
Proof. exact (TRANS (@lem3554365 A B s x f t) (@lem3554388 A B s x f t)). Qed.
Lemma lem3554390 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term165 A B x f s t) = (term165 A B x f s t).
Proof. exact (eq_refl (term165 A B x f s t)). Qed.
Lemma lem3554391 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term167 A B s x f t) = (term219 A B s x f t).
Proof. exact (MK_COMB (@lem3554390 A B x f s t) (@lem3554389 A B s x f t)). Qed.
Lemma lem3554393 {A : Type'} (P : Prop) (Q : A -> Prop) : (term206 A P Q) = (term207 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3554394 {A : Type'} (P : Prop) (Q : A -> Prop) : (term206 A P Q) = (term207 A P Q).
Proof. exact (@lem3554393 A P Q). Qed.
Lemma lem3554395 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term220 A B s x f t) = (term221 A B s x f t).
Proof. exact (@lem3554394 A (term149 A B x f s t) (term217 A B s x f t)). Qed.
Lemma lem3554396 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term222 A B s x' f t x) = (term216 A B s x x' f t).
Proof. exact (eq_refl (term222 A B s x' f t x)). Qed.
Lemma lem3554397 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term223 A B s x f t) = (term217 A B s x f t).
Proof. exact (fun_ext (fun x' : A => @lem3554396 A B s x' x f t)). Qed.
Lemma lem3554398 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3554399 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term224 A B s x f t) = (term218 A B s x f t).
Proof. exact (MK_COMB (@lem3554398 A) (@lem3554397 A B s x f t)). Qed.
Lemma lem3554400 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term165 A B x f s t) = (term165 A B x f s t).
Proof. exact (eq_refl (term165 A B x f s t)). Qed.
Lemma lem3554401 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term220 A B s x f t) = (term219 A B s x f t).
Proof. exact (MK_COMB (@lem3554400 A B x f s t) (@lem3554399 A B s x f t)). Qed.
Lemma lem3554402 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3554403 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term225 A B s x f t) = (term226 A B s x f t).
Proof. exact (MK_COMB (@lem3554402) (@lem3554401 A B s x f t)). Qed.
Lemma lem3554404 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term222 A B s x' f t x) = (term216 A B s x x' f t).
Proof. exact (eq_refl (term222 A B s x' f t x)). Qed.
Lemma lem3554405 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term165 A B x f s t) = (term165 A B x f s t).
Proof. exact (eq_refl (term165 A B x f s t)). Qed.
Lemma lem3554406 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term227 A B s x' f t x) = (term228 A B s x x' f t).
Proof. exact (MK_COMB (@lem3554405 A B x' f s t) (@lem3554404 A B s x x' f t)). Qed.
Lemma lem3554407 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term229 A B s x f t) = (term230 A B s x f t).
Proof. exact (fun_ext (fun x' : A => @lem3554406 A B s x' x f t)). Qed.
Lemma lem3554408 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3554409 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term221 A B s x f t) = (term231 A B s x f t).
Proof. exact (MK_COMB (@lem3554408 A) (@lem3554407 A B s x f t)). Qed.
Lemma lem3554410 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : ((term220 A B s x f t) = (term221 A B s x f t)) = ((term219 A B s x f t) = (term231 A B s x f t)).
Proof. exact (MK_COMB (@lem3554403 A B s x f t) (@lem3554409 A B s x f t)). Qed.
Lemma lem3554411 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term219 A B s x f t) = (term231 A B s x f t).
Proof. exact (EQ_MP (@lem3554410 A B s x f t) (@lem3554395 A B s x f t)). Qed.
Lemma lem3554413 {A : Type'} (P : Prop) (Q : A -> Prop) : (term206 A P Q) = (term207 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3554414 {A : Type'} (P : Prop) (Q : A -> Prop) : (term206 A P Q) = (term207 A P Q).
Proof. exact (@lem3554413 A P Q). Qed.
Lemma lem3554415 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term232 A B s x x' f t) = (term233 A B s x x' f t).
Proof. exact (@lem3554414 A (term149 A B x' f s t) (term215 A B s x x' f t)). Qed.
Lemma lem3554416 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) (x'' : A) : (term234 A B s x x' f t x'') = (term213 A B s x x' f t x'').
Proof. exact (eq_refl (term234 A B s x x' f t x'')). Qed.
Lemma lem3554417 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term235 A B s x x' f t) = (term215 A B s x x' f t).
Proof. exact (fun_ext (fun x'' : A => @lem3554416 A B s x x' f t x'')). Qed.
Lemma lem3554418 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3554419 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term236 A B s x x' f t) = (term216 A B s x x' f t).
Proof. exact (MK_COMB (@lem3554418 A) (@lem3554417 A B s x x' f t)). Qed.
Lemma lem3554420 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term165 A B x f s t) = (term165 A B x f s t).
Proof. exact (eq_refl (term165 A B x f s t)). Qed.
Lemma lem3554421 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term232 A B s x x' f t) = (term228 A B s x x' f t).
Proof. exact (MK_COMB (@lem3554420 A B x' f s t) (@lem3554419 A B s x x' f t)). Qed.
Lemma lem3554422 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3554423 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term237 A B s x x' f t) = (term238 A B s x x' f t).
Proof. exact (MK_COMB (@lem3554422) (@lem3554421 A B s x x' f t)). Qed.
Lemma lem3554424 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) (x'' : A) : (term234 A B s x x' f t x'') = (term213 A B s x x' f t x'').
Proof. exact (eq_refl (term234 A B s x x' f t x'')). Qed.
Lemma lem3554425 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term165 A B x f s t) = (term165 A B x f s t).
Proof. exact (eq_refl (term165 A B x f s t)). Qed.
Lemma lem3554426 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) (x'' : A) : (term239 A B s x x' f t x'') = (term240 A B s x x' f t x'').
Proof. exact (MK_COMB (@lem3554425 A B x' f s t) (@lem3554424 A B s x x' f t x'')). Qed.
Lemma lem3554427 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term241 A B s x x' f t) = (term242 A B s x x' f t).
Proof. exact (fun_ext (fun x'' : A => @lem3554426 A B s x x' f t x'')). Qed.
Lemma lem3554428 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3554429 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term233 A B s x x' f t) = (term243 A B s x x' f t).
Proof. exact (MK_COMB (@lem3554428 A) (@lem3554427 A B s x x' f t)). Qed.
Lemma lem3554430 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : ((term232 A B s x x' f t) = (term233 A B s x x' f t)) = ((term228 A B s x x' f t) = (term243 A B s x x' f t)).
Proof. exact (MK_COMB (@lem3554423 A B s x x' f t) (@lem3554429 A B s x x' f t)). Qed.
Lemma lem3554431 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term228 A B s x x' f t) = (term243 A B s x x' f t).
Proof. exact (EQ_MP (@lem3554430 A B s x x' f t) (@lem3554415 A B s x x' f t)). Qed.
Lemma lem3554432 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term230 A B s x f t) = (term244 A B s x f t).
Proof. exact (fun_ext (fun x' : A => @lem3554431 A B s x' x f t)). Qed.
Lemma lem3554433 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3554434 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term231 A B s x f t) = (term245 A B s x f t).
Proof. exact (MK_COMB (@lem3554433 A) (@lem3554432 A B s x f t)). Qed.
Lemma lem3554435 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term219 A B s x f t) = (term245 A B s x f t).
Proof. exact (TRANS (@lem3554411 A B s x f t) (@lem3554434 A B s x f t)). Qed.
Lemma lem3554436 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term167 A B s x f t) = (term245 A B s x f t).
Proof. exact (TRANS (@lem3554391 A B s x f t) (@lem3554435 A B s x f t)). Qed.
Lemma lem3554437 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term174 A B s x f t) = (term246 A B s x f t).
Proof. exact (MK_COMB (@lem3554341 A B s x f t) (@lem3554436 A B s x f t)). Qed.
Lemma lem3554439 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term247 A P Q) = (term248 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3554440 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term247 A P Q) = (term248 A P Q).
Proof. exact (@lem3554439 A P Q). Qed.
Lemma lem3554441 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term249 A B s x f t) = (term250 A B s x f t).
Proof. exact (@lem3554440 A (term189 A B s x f t) (term244 A B s x f t)). Qed.
Lemma lem3554442 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (t : A -> Prop) : (term251 A B s x' f t x) = (term187 A B x s x' f t).
Proof. exact (eq_refl (term251 A B s x' f t x)). Qed.
Lemma lem3554443 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term252 A B s x f t) = (term189 A B s x f t).
Proof. exact (fun_ext (fun x' : A => @lem3554442 A B x' s x f t)). Qed.
Lemma lem3554444 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3554445 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term253 A B s x f t) = (term190 A B s x f t).
Proof. exact (MK_COMB (@lem3554444 A) (@lem3554443 A B s x f t)). Qed.
Lemma lem3554446 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3554447 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term254 A B s x f t) = (term191 A B s x f t).
Proof. exact (MK_COMB (@lem3554446) (@lem3554445 A B s x f t)). Qed.
Lemma lem3554448 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term255 A B s x' f t x) = (term243 A B s x x' f t).
Proof. exact (eq_refl (term255 A B s x' f t x)). Qed.
Lemma lem3554449 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term256 A B s x f t) = (term244 A B s x f t).
Proof. exact (fun_ext (fun x' : A => @lem3554448 A B s x' x f t)). Qed.
Lemma lem3554450 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3554451 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term257 A B s x f t) = (term245 A B s x f t).
Proof. exact (MK_COMB (@lem3554450 A) (@lem3554449 A B s x f t)). Qed.
Lemma lem3554452 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term249 A B s x f t) = (term246 A B s x f t).
Proof. exact (MK_COMB (@lem3554447 A B s x f t) (@lem3554451 A B s x f t)). Qed.
Lemma lem3554453 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3554454 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term258 A B s x f t) = (term259 A B s x f t).
Proof. exact (MK_COMB (@lem3554453) (@lem3554452 A B s x f t)). Qed.
Lemma lem3554455 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (t : A -> Prop) : (term251 A B s x' f t x) = (term187 A B x s x' f t).
Proof. exact (eq_refl (term251 A B s x' f t x)). Qed.
Lemma lem3554456 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3554457 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (t : A -> Prop) : (term260 A B s x' f t x) = (term261 A B x s x' f t).
Proof. exact (MK_COMB (@lem3554456) (@lem3554455 A B x s x' f t)). Qed.
Lemma lem3554458 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term255 A B s x' f t x) = (term243 A B s x x' f t).
Proof. exact (eq_refl (term255 A B s x' f t x)). Qed.
Lemma lem3554459 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term262 A B s x' f t x) = (term263 A B s x x' f t).
Proof. exact (MK_COMB (@lem3554457 A B x s x' f t) (@lem3554458 A B s x x' f t)). Qed.
Lemma lem3554460 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term264 A B s x f t) = (term265 A B s x f t).
Proof. exact (fun_ext (fun x' : A => @lem3554459 A B s x' x f t)). Qed.
Lemma lem3554461 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3554462 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term250 A B s x f t) = (term266 A B s x f t).
Proof. exact (MK_COMB (@lem3554461 A) (@lem3554460 A B s x f t)). Qed.
Lemma lem3554463 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : ((term249 A B s x f t) = (term250 A B s x f t)) = ((term246 A B s x f t) = (term266 A B s x f t)).
Proof. exact (MK_COMB (@lem3554454 A B s x f t) (@lem3554462 A B s x f t)). Qed.
Lemma lem3554464 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term246 A B s x f t) = (term266 A B s x f t).
Proof. exact (EQ_MP (@lem3554463 A B s x f t) (@lem3554441 A B s x f t)). Qed.
Lemma lem3554466 {A : Type'} (P : Prop) (Q : A -> Prop) : (term267 A P Q) = (term268 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3554467 {A : Type'} (P : Prop) (Q : A -> Prop) : (term267 A P Q) = (term268 A P Q).
Proof. exact (@lem3554466 A P Q). Qed.
Lemma lem3554468 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term269 A B s x x' f t) = (term270 A B s x x' f t).
Proof. exact (@lem3554467 A (term187 A B x s x' f t) (term242 A B s x x' f t)). Qed.
Lemma lem3554469 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) (x'' : A) : (term271 A B s x x' f t x'') = (term240 A B s x x' f t x'').
Proof. exact (eq_refl (term271 A B s x x' f t x'')). Qed.
Lemma lem3554470 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term272 A B s x x' f t) = (term242 A B s x x' f t).
Proof. exact (fun_ext (fun x'' : A => @lem3554469 A B s x x' f t x'')). Qed.
Lemma lem3554471 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3554472 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term273 A B s x x' f t) = (term243 A B s x x' f t).
Proof. exact (MK_COMB (@lem3554471 A) (@lem3554470 A B s x x' f t)). Qed.
Lemma lem3554473 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (t : A -> Prop) : (term261 A B x s x' f t) = (term261 A B x s x' f t).
Proof. exact (eq_refl (term261 A B x s x' f t)). Qed.
Lemma lem3554474 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term269 A B s x x' f t) = (term263 A B s x x' f t).
Proof. exact (MK_COMB (@lem3554473 A B x s x' f t) (@lem3554472 A B s x x' f t)). Qed.
Lemma lem3554475 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3554476 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term274 A B s x x' f t) = (term275 A B s x x' f t).
Proof. exact (MK_COMB (@lem3554475) (@lem3554474 A B s x x' f t)). Qed.
Lemma lem3554477 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) (x'' : A) : (term271 A B s x x' f t x'') = (term240 A B s x x' f t x'').
Proof. exact (eq_refl (term271 A B s x x' f t x'')). Qed.
Lemma lem3554478 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (t : A -> Prop) : (term261 A B x s x' f t) = (term261 A B x s x' f t).
Proof. exact (eq_refl (term261 A B x s x' f t)). Qed.
Lemma lem3554479 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) (x'' : A) : (term276 A B s x x' f t x'') = (term277 A B s x x' f t x'').
Proof. exact (MK_COMB (@lem3554478 A B x s x' f t) (@lem3554477 A B s x x' f t x'')). Qed.
Lemma lem3554480 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term278 A B s x x' f t) = (term279 A B s x x' f t).
Proof. exact (fun_ext (fun x'' : A => @lem3554479 A B s x x' f t x'')). Qed.
Lemma lem3554481 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3554482 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term270 A B s x x' f t) = (term280 A B s x x' f t).
Proof. exact (MK_COMB (@lem3554481 A) (@lem3554480 A B s x x' f t)). Qed.
Lemma lem3554483 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : ((term269 A B s x x' f t) = (term270 A B s x x' f t)) = ((term263 A B s x x' f t) = (term280 A B s x x' f t)).
Proof. exact (MK_COMB (@lem3554476 A B s x x' f t) (@lem3554482 A B s x x' f t)). Qed.
Lemma lem3554484 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term263 A B s x x' f t) = (term280 A B s x x' f t).
Proof. exact (EQ_MP (@lem3554483 A B s x x' f t) (@lem3554468 A B s x x' f t)). Qed.
Lemma lem3554485 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term265 A B s x f t) = (term281 A B s x f t).
Proof. exact (fun_ext (fun x' : A => @lem3554484 A B s x' x f t)). Qed.
Lemma lem3554486 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3554487 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term266 A B s x f t) = (term282 A B s x f t).
Proof. exact (MK_COMB (@lem3554486 A) (@lem3554485 A B s x f t)). Qed.
Lemma lem3554488 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term246 A B s x f t) = (term282 A B s x f t).
Proof. exact (TRANS (@lem3554464 A B s x f t) (@lem3554487 A B s x f t)). Qed.
Lemma lem3554490 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term174 A B s x f t) = (term282 A B s x f t).
Proof. exact (TRANS (@lem3554437 A B s x f t) (@lem3554488 A B s x f t)). Qed.
Lemma lem3554491 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term117 A B s x f t) = (term282 A B s x f t).
Proof. exact (TRANS (@lem3554058 A B s x f t) (@lem3554490 A B s x f t)). Qed.
Lemma lem3554492 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term117 A B s x f t) : term282 A B s x f t.
Proof. exact (EQ_MP (@lem3554491 A B s x f t) (@lem3553734 A B s x f t h1)). Qed.
Lemma lem3554493 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term280 A B s x' x f t) : term280 A B s x' x f t.
Proof. exact (h1). Qed.
Lemma lem3554494 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term277 A B s x' x f t x'') : term277 A B s x' x f t x''.
Proof. exact (h1). Qed.
Lemma lem3554497 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem3554516 {A B : Type'} (x : A) (f : A -> B) (t : A -> Prop) (x' : A) : (term119 A B x f t x') = (term119 A B x f t x').
Proof. exact (eq_refl (term119 A B x f t x')). Qed.
Lemma lem3554517 {A B : Type'} (x : A) (f : A -> B) (t : A -> Prop) : (term127 A B x f t) = (term127 A B x f t).
Proof. exact (fun_ext (fun x' : A => @lem3554516 A B x f t x')). Qed.
Lemma lem3554518 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3554519 {A B : Type'} (x : A) (f : A -> B) (t : A -> Prop) : (term128 A B x f t) = (term128 A B x f t).
Proof. exact (MK_COMB (@lem3554518 A) (@lem3554517 A B x f t)). Qed.
Lemma lem3554520 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3554521 {A B : Type'} (x : A) (f : A -> B) (t : A -> Prop) : (term130 A B x f t) = (term130 A B x f t).
Proof. exact (MK_COMB (@lem3554520) (@lem3554519 A B x f t)). Qed.
Lemma lem3554522 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : A) : (term132 A B f t x) = (term132 A B f t x).
Proof. exact (MK_COMB (@lem3554521 A B x f t) (@lem3554497 A t x)). Qed.
Lemma lem3554523 {A B : Type'} (f : A -> B) (t : A -> Prop) : (term133 A B f t) = (term133 A B f t).
Proof. exact (fun_ext (fun x : A => @lem3554522 A B f t x)). Qed.
Lemma lem3554524 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3554525 {A B : Type'} (f : A -> B) (t : A -> Prop) : (term134 A B f t) = (term134 A B f t).
Proof. exact (MK_COMB (@lem3554524 A) (@lem3554523 A B f t)). Qed.
Lemma lem3554528 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem3554547 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (x' : A) : (term119 A B x f s x') = (term119 A B x f s x').
Proof. exact (eq_refl (term119 A B x f s x')). Qed.
Lemma lem3554548 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term127 A B x f s) = (term127 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3554547 A B x f s x')). Qed.
Lemma lem3554549 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3554550 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term128 A B x f s) = (term128 A B x f s).
Proof. exact (MK_COMB (@lem3554549 A) (@lem3554548 A B x f s)). Qed.
Lemma lem3554551 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3554552 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term130 A B x f s) = (term130 A B x f s).
Proof. exact (MK_COMB (@lem3554551) (@lem3554550 A B x f s)). Qed.
Lemma lem3554553 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term132 A B f s x) = (term132 A B f s x).
Proof. exact (MK_COMB (@lem3554552 A B x f s) (@lem3554528 A s x)). Qed.
Lemma lem3554554 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term133 A B f s) = (term133 A B f s).
Proof. exact (fun_ext (fun x : A => @lem3554553 A B f s x)). Qed.
Lemma lem3554555 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3554556 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term134 A B f s) = (term134 A B f s).
Proof. exact (MK_COMB (@lem3554555 A) (@lem3554554 A B f s)). Qed.
Lemma lem3554557 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3554558 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term135 A B f s) = (term135 A B f s).
Proof. exact (MK_COMB (@lem3554557) (@lem3554556 A B f s)). Qed.
Lemma lem3554559 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term136 A B s f t) = (term136 A B s f t).
Proof. exact (MK_COMB (@lem3554558 A B f s) (@lem3554525 A B f t)). Qed.
Lemma lem3554560 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term71 A B s f t) : term136 A B s f t.
Proof. exact (EQ_MP (@lem3554559 A B s f t) (@lem3553954 A B s f t h1)). Qed.
Lemma lem3554589 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) : (term213 A B s x' x f t x'') = (term213 A B s x' x f t x'').
Proof. exact (eq_refl (term213 A B s x' x f t x'')). Qed.
Lemma lem3554614 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term141 A B x f s t x') = (term141 A B x f s t x').
Proof. exact (eq_refl (term141 A B x f s t x')). Qed.
Lemma lem3554615 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term148 A B x f s t) = (term148 A B x f s t).
Proof. exact (fun_ext (fun x' : A => @lem3554614 A B x f s t x')). Qed.
Lemma lem3554616 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3554617 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term149 A B x f s t) = (term149 A B x f s t).
Proof. exact (MK_COMB (@lem3554616 A) (@lem3554615 A B x f s t)). Qed.
Lemma lem3554618 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3554619 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term165 A B x f s t) = (term165 A B x f s t).
Proof. exact (MK_COMB (@lem3554618) (@lem3554617 A B x f s t)). Qed.
Lemma lem3554620 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) : (term240 A B s x' x f t x'') = (term240 A B s x' x f t x'').
Proof. exact (MK_COMB (@lem3554619 A B x f s t) (@lem3554589 A B s x' x f t x'')). Qed.
Lemma lem3554637 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term151 A B x f t x') = (term151 A B x f t x').
Proof. exact (eq_refl (term151 A B x f t x')). Qed.
Lemma lem3554638 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term157 A B x f t) = (term157 A B x f t).
Proof. exact (fun_ext (fun x' : A => @lem3554637 A B x f t x')). Qed.
Lemma lem3554639 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3554640 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term158 A B x f t) = (term158 A B x f t).
Proof. exact (MK_COMB (@lem3554639 A) (@lem3554638 A B x f t)). Qed.
Lemma lem3554657 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term151 A B x f s x') = (term151 A B x f s x').
Proof. exact (eq_refl (term151 A B x f s x')). Qed.
Lemma lem3554658 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term157 A B x f s) = (term157 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3554657 A B x f s x')). Qed.
Lemma lem3554659 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3554660 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term158 A B x f s) = (term158 A B x f s).
Proof. exact (MK_COMB (@lem3554659 A) (@lem3554658 A B x f s)). Qed.
Lemma lem3554661 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3554662 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term160 A B x f s) = (term160 A B x f s).
Proof. exact (MK_COMB (@lem3554661) (@lem3554660 A B x f s)). Qed.
Lemma lem3554663 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term162 A B s x f t) = (term162 A B s x f t).
Proof. exact (MK_COMB (@lem3554662 A B x f s) (@lem3554640 A B x f t)). Qed.
Lemma lem3554684 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term185 A B x f s t x') = (term185 A B x f s t x').
Proof. exact (eq_refl (term185 A B x f s t x')). Qed.
Lemma lem3554685 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term187 A B x' s x f t) = (term187 A B x' s x f t).
Proof. exact (MK_COMB (@lem3554684 A B x f s t x') (@lem3554663 A B s x f t)). Qed.
Lemma lem3554686 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3554687 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term261 A B x' s x f t) = (term261 A B x' s x f t).
Proof. exact (MK_COMB (@lem3554686) (@lem3554685 A B x' s x f t)). Qed.
Lemma lem3554688 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) : (term277 A B s x' x f t x'') = (term277 A B s x' x f t x'').
Proof. exact (MK_COMB (@lem3554687 A B x' s x f t) (@lem3554620 A B s x' x f t x'')). Qed.
Lemma lem3554689 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term277 A B s x' x f t x'') : term277 A B s x' x f t x''.
Proof. exact (EQ_MP (@lem3554688 A B s x' x f t x'') (@lem3554494 A B s x' x f t x'' h1)). Qed.
Lemma lem3554690 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term187 A B x' s x f t) : term187 A B x' s x f t.
Proof. exact (h1). Qed.
Lemma lem3554691 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term240 A B s x' x f t x'') : term240 A B s x' x f t x''.
Proof. exact (h1). Qed.
Lemma lem3554692 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term187 A B x' s x f t) : term162 A B s x f t.
Proof. exact (proj2 (@lem3554690 A B x' s x f t h1)). Qed.
Lemma lem3554693 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term187 A B x' s x f t) : term82 A B x f s t x'.
Proof. exact (proj1 (@lem3554690 A B x' s x f t h1)). Qed.
Lemma lem3554694 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term187 A B x' s x f t) : term79 A s t x'.
Proof. exact (proj2 (@lem3554693 A B x' s x f t h1)). Qed.
Lemma lem3554698 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (h1 : term158 A B x f s) : term158 A B x f s.
Proof. exact (h1). Qed.
Lemma lem3554699 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (h1 : term158 A B x f t) : term158 A B x f t.
Proof. exact (h1). Qed.
Lemma lem3554704 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term240 A B s x' x f t x'') : term213 A B s x' x f t x''.
Proof. exact (proj2 (@lem3554691 A B s x' x f t x'' h1)). Qed.
Lemma lem3554705 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term240 A B s x' x f t x'') : term149 A B x f s t.
Proof. exact (proj1 (@lem3554691 A B s x' x f t x'' h1)). Qed.
Lemma lem3554706 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term240 A B s x' x f t x'') : term91 A B x f t x''.
Proof. exact (proj2 (@lem3554704 A B s x' x f t x'' h1)). Qed.
Lemma lem3554707 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term240 A B s x' x f t x'') : term91 A B x f s x'.
Proof. exact (proj1 (@lem3554704 A B s x' x f t x'' h1)). Qed.
Lemma lem3554712 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term134 A B f s) : term134 A B f s.
Proof. exact (h1). Qed.
Lemma lem3554713 {A B : Type'} (f : A -> B) (t : A -> Prop) (h1 : term134 A B f t) : term134 A B f t.
Proof. exact (h1). Qed.
Lemma lem3554733 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term151 A B x f s x') = (term151 A B x f s x').
Proof. exact (eq_refl (term151 A B x f s x')). Qed.
Lemma lem3554734 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term157 A B x f s) = (term157 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3554733 A B x f s x')). Qed.
Lemma lem3554735 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3554737 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term158 A B x f s) = (term158 A B x f s).
Proof. exact (MK_COMB (@lem3554735 A) (@lem3554734 A B x f s)). Qed.
Lemma lem3554738 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (h1 : term158 A B x f s) : term158 A B x f s.
Proof. exact (EQ_MP (@lem3554737 A B x f s) (@lem3554698 A B x f s h1)). Qed.
Lemma lem3554806 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term151 A B x f s x') = (term151 A B x f s x').
Proof. exact (eq_refl (term151 A B x f s x')). Qed.
Lemma lem3554807 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term157 A B x f s) = (term157 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3554806 A B x f s x')). Qed.
Lemma lem3554808 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3554810 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term158 A B x f s) = (term158 A B x f s).
Proof. exact (MK_COMB (@lem3554808 A) (@lem3554807 A B x f s)). Qed.
Lemma lem3554811 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (h1 : term158 A B x f s) : term158 A B x f s.
Proof. exact (EQ_MP (@lem3554810 A B x f s) (@lem3554698 A B x f s h1)). Qed.
Lemma lem3554879 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term151 A B x f t x') = (term151 A B x f t x').
Proof. exact (eq_refl (term151 A B x f t x')). Qed.
Lemma lem3554880 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term157 A B x f t) = (term157 A B x f t).
Proof. exact (fun_ext (fun x' : A => @lem3554879 A B x f t x')). Qed.
Lemma lem3554881 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3554883 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term158 A B x f t) = (term158 A B x f t).
Proof. exact (MK_COMB (@lem3554881 A) (@lem3554880 A B x f t)). Qed.
Lemma lem3554884 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (h1 : term158 A B x f t) : term158 A B x f t.
Proof. exact (EQ_MP (@lem3554883 A B x f t) (@lem3554699 A B x f t h1)). Qed.
Lemma lem3554952 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term151 A B x f t x') = (term151 A B x f t x').
Proof. exact (eq_refl (term151 A B x f t x')). Qed.
Lemma lem3554953 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term157 A B x f t) = (term157 A B x f t).
Proof. exact (fun_ext (fun x' : A => @lem3554952 A B x f t x')). Qed.
Lemma lem3554954 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3554956 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term158 A B x f t) = (term158 A B x f t).
Proof. exact (MK_COMB (@lem3554954 A) (@lem3554953 A B x f t)). Qed.
Lemma lem3554957 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (h1 : term158 A B x f t) : term158 A B x f t.
Proof. exact (EQ_MP (@lem3554956 A B x f t) (@lem3554699 A B x f t h1)). Qed.
Lemma lem3555019 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term141 A B x f s t x') = (term141 A B x f s t x').
Proof. exact (eq_refl (term141 A B x f s t x')). Qed.
Lemma lem3555020 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term148 A B x f s t) = (term148 A B x f s t).
Proof. exact (fun_ext (fun x' : A => @lem3555019 A B x f s t x')). Qed.
Lemma lem3555021 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3555023 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term149 A B x f s t) = (term149 A B x f s t).
Proof. exact (MK_COMB (@lem3555021 A) (@lem3555020 A B x f s t)). Qed.
Lemma lem3555024 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term240 A B s x' x f t x'') : term149 A B x f s t.
Proof. exact (EQ_MP (@lem3555023 A B x f s t) (@lem3554705 A B s x' x f t x'' h1)). Qed.
Lemma lem3555042 {A : Type'} (P : A -> Prop) (Q : Prop) : (term283 A P Q) = (term284 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem3555043 {A : Type'} (P : A -> Prop) (Q : Prop) : (term283 A P Q) = (term284 A P Q).
Proof. exact (@lem3555042 A P Q). Qed.
Lemma lem3555044 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term285 A B f s x) = (term286 A B f s x).
Proof. exact (@lem3555043 A (term127 A B x f s) (s x)). Qed.
Lemma lem3555045 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (x' : A) : (term287 A B x f s x') = (term119 A B x f s x').
Proof. exact (eq_refl (term287 A B x f s x')). Qed.
Lemma lem3555046 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term288 A B x f s) = (term127 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3555045 A B x f s x')). Qed.
Lemma lem3555047 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3555048 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term289 A B x f s) = (term128 A B x f s).
Proof. exact (MK_COMB (@lem3555047 A) (@lem3555046 A B x f s)). Qed.
Lemma lem3555049 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3555050 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term290 A B x f s) = (term130 A B x f s).
Proof. exact (MK_COMB (@lem3555049) (@lem3555048 A B x f s)). Qed.
Lemma lem3555051 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem3555052 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term285 A B f s x) = (term132 A B f s x).
Proof. exact (MK_COMB (@lem3555050 A B x f s) (@lem3555051 A s x)). Qed.
Lemma lem3555053 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3555054 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term291 A B f s x) = (term292 A B f s x).
Proof. exact (MK_COMB (@lem3555053) (@lem3555052 A B f s x)). Qed.
Lemma lem3555055 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (x' : A) : (term287 A B x f s x') = (term119 A B x f s x').
Proof. exact (eq_refl (term287 A B x f s x')). Qed.
Lemma lem3555056 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3555057 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (x' : A) : (term293 A B x f s x') = (term294 A B x f s x').
Proof. exact (MK_COMB (@lem3555056) (@lem3555055 A B x f s x')). Qed.
Lemma lem3555058 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem3555059 {A B : Type'} (f : A -> B) (x' : A) (s : A -> Prop) (x : A) : (term295 A B f x' s x) = (term296 A B f x' s x).
Proof. exact (MK_COMB (@lem3555057 A B x f s x') (@lem3555058 A s x)). Qed.
Lemma lem3555060 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term297 A B f s x) = (term298 A B f s x).
Proof. exact (fun_ext (fun x' : A => @lem3555059 A B f x' s x)). Qed.
Lemma lem3555061 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3555062 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term286 A B f s x) = (term299 A B f s x).
Proof. exact (MK_COMB (@lem3555061 A) (@lem3555060 A B f s x)). Qed.
Lemma lem3555063 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : ((term285 A B f s x) = (term286 A B f s x)) = ((term132 A B f s x) = (term299 A B f s x)).
Proof. exact (MK_COMB (@lem3555054 A B f s x) (@lem3555062 A B f s x)). Qed.
Lemma lem3555064 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term132 A B f s x) = (term299 A B f s x).
Proof. exact (EQ_MP (@lem3555063 A B f s x) (@lem3555044 A B f s x)). Qed.
Lemma lem3555065 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term133 A B f s) = (term300 A B f s).
Proof. exact (fun_ext (fun x : A => @lem3555064 A B f s x)). Qed.
Lemma lem3555066 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3555067 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term134 A B f s) = (term301 A B f s).
Proof. exact (MK_COMB (@lem3555066 A) (@lem3555065 A B f s)). Qed.
Lemma lem3555080 {A B : Type'} (f : A -> B) (x' : A) (s : A -> Prop) (x : A) : (term296 A B f x' s x) = (term296 A B f x' s x).
Proof. exact (eq_refl (term296 A B f x' s x)). Qed.
Lemma lem3555081 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term298 A B f s x) = (term298 A B f s x).
Proof. exact (fun_ext (fun x' : A => @lem3555080 A B f x' s x)). Qed.
Lemma lem3555082 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3555083 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term299 A B f s x) = (term299 A B f s x).
Proof. exact (MK_COMB (@lem3555082 A) (@lem3555081 A B f s x)). Qed.
Lemma lem3555084 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term300 A B f s) = (term300 A B f s).
Proof. exact (fun_ext (fun x : A => @lem3555083 A B f s x)). Qed.
Lemma lem3555085 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3555086 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term301 A B f s) = (term301 A B f s).
Proof. exact (MK_COMB (@lem3555085 A) (@lem3555084 A B f s)). Qed.
Lemma lem3555087 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term134 A B f s) = (term301 A B f s).
Proof. exact (TRANS (@lem3555067 A B f s) (@lem3555086 A B f s)). Qed.
Lemma lem3555088 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term134 A B f s) : term301 A B f s.
Proof. exact (EQ_MP (@lem3555087 A B f s) (@lem3554712 A B f s h1)). Qed.
Lemma lem3555102 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term141 A B x f s t x') = (term141 A B x f s t x').
Proof. exact (eq_refl (term141 A B x f s t x')). Qed.
Lemma lem3555103 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term148 A B x f s t) = (term148 A B x f s t).
Proof. exact (fun_ext (fun x' : A => @lem3555102 A B x f s t x')). Qed.
Lemma lem3555104 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3555106 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term149 A B x f s t) = (term149 A B x f s t).
Proof. exact (MK_COMB (@lem3555104 A) (@lem3555103 A B x f s t)). Qed.
Lemma lem3555107 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term240 A B s x' x f t x'') : term149 A B x f s t.
Proof. exact (EQ_MP (@lem3555106 A B x f s t) (@lem3554705 A B s x' x f t x'' h1)). Qed.
Lemma lem3555125 {A : Type'} (P : A -> Prop) (Q : Prop) : (term283 A P Q) = (term284 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem3555126 {A : Type'} (P : A -> Prop) (Q : Prop) : (term283 A P Q) = (term284 A P Q).
Proof. exact (@lem3555125 A P Q). Qed.
Lemma lem3555127 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : A) : (term285 A B f t x) = (term286 A B f t x).
Proof. exact (@lem3555126 A (term127 A B x f t) (t x)). Qed.
Lemma lem3555128 {A B : Type'} (x : A) (f : A -> B) (t : A -> Prop) (x' : A) : (term287 A B x f t x') = (term119 A B x f t x').
Proof. exact (eq_refl (term287 A B x f t x')). Qed.
Lemma lem3555129 {A B : Type'} (x : A) (f : A -> B) (t : A -> Prop) : (term288 A B x f t) = (term127 A B x f t).
Proof. exact (fun_ext (fun x' : A => @lem3555128 A B x f t x')). Qed.
Lemma lem3555130 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3555131 {A B : Type'} (x : A) (f : A -> B) (t : A -> Prop) : (term289 A B x f t) = (term128 A B x f t).
Proof. exact (MK_COMB (@lem3555130 A) (@lem3555129 A B x f t)). Qed.
Lemma lem3555132 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3555133 {A B : Type'} (x : A) (f : A -> B) (t : A -> Prop) : (term290 A B x f t) = (term130 A B x f t).
Proof. exact (MK_COMB (@lem3555132) (@lem3555131 A B x f t)). Qed.
Lemma lem3555134 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem3555135 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : A) : (term285 A B f t x) = (term132 A B f t x).
Proof. exact (MK_COMB (@lem3555133 A B x f t) (@lem3555134 A t x)). Qed.
Lemma lem3555136 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3555137 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : A) : (term291 A B f t x) = (term292 A B f t x).
Proof. exact (MK_COMB (@lem3555136) (@lem3555135 A B f t x)). Qed.
Lemma lem3555138 {A B : Type'} (x : A) (f : A -> B) (t : A -> Prop) (x' : A) : (term287 A B x f t x') = (term119 A B x f t x').
Proof. exact (eq_refl (term287 A B x f t x')). Qed.
Lemma lem3555139 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3555140 {A B : Type'} (x : A) (f : A -> B) (t : A -> Prop) (x' : A) : (term293 A B x f t x') = (term294 A B x f t x').
Proof. exact (MK_COMB (@lem3555139) (@lem3555138 A B x f t x')). Qed.
Lemma lem3555141 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem3555142 {A B : Type'} (f : A -> B) (x' : A) (t : A -> Prop) (x : A) : (term295 A B f x' t x) = (term296 A B f x' t x).
Proof. exact (MK_COMB (@lem3555140 A B x f t x') (@lem3555141 A t x)). Qed.
Lemma lem3555143 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : A) : (term297 A B f t x) = (term298 A B f t x).
Proof. exact (fun_ext (fun x' : A => @lem3555142 A B f x' t x)). Qed.
Lemma lem3555144 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3555145 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : A) : (term286 A B f t x) = (term299 A B f t x).
Proof. exact (MK_COMB (@lem3555144 A) (@lem3555143 A B f t x)). Qed.
Lemma lem3555146 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : A) : ((term285 A B f t x) = (term286 A B f t x)) = ((term132 A B f t x) = (term299 A B f t x)).
Proof. exact (MK_COMB (@lem3555137 A B f t x) (@lem3555145 A B f t x)). Qed.
Lemma lem3555147 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : A) : (term132 A B f t x) = (term299 A B f t x).
Proof. exact (EQ_MP (@lem3555146 A B f t x) (@lem3555127 A B f t x)). Qed.
Lemma lem3555148 {A B : Type'} (f : A -> B) (t : A -> Prop) : (term133 A B f t) = (term300 A B f t).
Proof. exact (fun_ext (fun x : A => @lem3555147 A B f t x)). Qed.
Lemma lem3555149 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3555150 {A B : Type'} (f : A -> B) (t : A -> Prop) : (term134 A B f t) = (term301 A B f t).
Proof. exact (MK_COMB (@lem3555149 A) (@lem3555148 A B f t)). Qed.
Lemma lem3555163 {A B : Type'} (f : A -> B) (x' : A) (t : A -> Prop) (x : A) : (term296 A B f x' t x) = (term296 A B f x' t x).
Proof. exact (eq_refl (term296 A B f x' t x)). Qed.
Lemma lem3555164 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : A) : (term298 A B f t x) = (term298 A B f t x).
Proof. exact (fun_ext (fun x' : A => @lem3555163 A B f x' t x)). Qed.
Lemma lem3555165 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3555166 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : A) : (term299 A B f t x) = (term299 A B f t x).
Proof. exact (MK_COMB (@lem3555165 A) (@lem3555164 A B f t x)). Qed.
Lemma lem3555167 {A B : Type'} (f : A -> B) (t : A -> Prop) : (term300 A B f t) = (term300 A B f t).
Proof. exact (fun_ext (fun x : A => @lem3555166 A B f t x)). Qed.
Lemma lem3555168 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3555169 {A B : Type'} (f : A -> B) (t : A -> Prop) : (term301 A B f t) = (term301 A B f t).
Proof. exact (MK_COMB (@lem3555168 A) (@lem3555167 A B f t)). Qed.
Lemma lem3555170 {A B : Type'} (f : A -> B) (t : A -> Prop) : (term134 A B f t) = (term301 A B f t).
Proof. exact (TRANS (@lem3555150 A B f t) (@lem3555169 A B f t)). Qed.
Lemma lem3555171 {A B : Type'} (f : A -> B) (t : A -> Prop) (h1 : term134 A B f t) : term301 A B f t.
Proof. exact (EQ_MP (@lem3555170 A B f t) (@lem3554713 A B f t h1)). Qed.
Lemma lem3555172 {A B : Type'} (_38015 : A) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term158 A B x f s) : term302 A B x f s _38015.
Proof. exact (@lem3554738 A B x f s h1 _38015). Qed.
Lemma lem3555173 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (_38015 : A) : (term302 A B x f s _38015) = (term151 A B x f s _38015).
Proof. exact (eq_refl (term302 A B x f s _38015)). Qed.
Lemma lem3555181 {A B : Type'} (_38018 : A) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term158 A B x f s) : term302 A B x f s _38018.
Proof. exact (@lem3554811 A B x f s h1 _38018). Qed.
Lemma lem3555182 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (_38018 : A) : (term302 A B x f s _38018) = (term151 A B x f s _38018).
Proof. exact (eq_refl (term302 A B x f s _38018)). Qed.
Lemma lem3555190 {A B : Type'} (_38021 : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term158 A B x f t) : term302 A B x f t _38021.
Proof. exact (@lem3554884 A B x f t h1 _38021). Qed.
Lemma lem3555191 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (_38021 : A) : (term302 A B x f t _38021) = (term151 A B x f t _38021).
Proof. exact (eq_refl (term302 A B x f t _38021)). Qed.
Lemma lem3555199 {A B : Type'} (_38024 : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term158 A B x f t) : term302 A B x f t _38024.
Proof. exact (@lem3554957 A B x f t h1 _38024). Qed.
Lemma lem3555200 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (_38024 : A) : (term302 A B x f t _38024) = (term151 A B x f t _38024).
Proof. exact (eq_refl (term302 A B x f t _38024)). Qed.
Lemma lem3555208 {A B : Type'} (_38027 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term240 A B s x' x f t x'') : term303 A B x f s t _38027.
Proof. exact (@lem3555024 A B s x' x f t x'' h1 _38027). Qed.
Lemma lem3555209 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_38027 : A) : (term303 A B x f s t _38027) = (term141 A B x f s t _38027).
Proof. exact (eq_refl (term303 A B x f s t _38027)). Qed.
Lemma lem3555211 {A B : Type'} (_38028 : A) (f : A -> B) (s : A -> Prop) (h1 : term134 A B f s) : term304 A B f s _38028.
Proof. exact (@lem3555088 A B f s h1 _38028). Qed.
Lemma lem3555212 {A B : Type'} (f : A -> B) (s : A -> Prop) (_38028 : A) : (term304 A B f s _38028) = (term299 A B f s _38028).
Proof. exact (eq_refl (term304 A B f s _38028)). Qed.
Lemma lem3555213 {A B : Type'} (_38028 : A) (f : A -> B) (s : A -> Prop) (h1 : term134 A B f s) : term299 A B f s _38028.
Proof. exact (EQ_MP (@lem3555212 A B f s _38028) (@lem3555211 A B _38028 f s h1)). Qed.
Lemma lem3555214 {A B : Type'} (_38028 : A) (_38029 : A) (f : A -> B) (s : A -> Prop) (h1 : term134 A B f s) : term305 A B f s _38028 _38029.
Proof. exact (@lem3555213 A B _38028 f s h1 _38029). Qed.
Lemma lem3555215 {A B : Type'} (f : A -> B) (_38029 : A) (s : A -> Prop) (_38028 : A) : (term305 A B f s _38028 _38029) = (term296 A B f _38029 s _38028).
Proof. exact (eq_refl (term305 A B f s _38028 _38029)). Qed.
Lemma lem3555216 {A B : Type'} (_38029 : A) (_38028 : A) (f : A -> B) (s : A -> Prop) (h1 : term134 A B f s) : term296 A B f _38029 s _38028.
Proof. exact (EQ_MP (@lem3555215 A B f _38029 s _38028) (@lem3555214 A B _38028 _38029 f s h1)). Qed.
Lemma lem3555217 {A B : Type'} (_38030 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term240 A B s x' x f t x'') : term303 A B x f s t _38030.
Proof. exact (@lem3555107 A B s x' x f t x'' h1 _38030). Qed.
Lemma lem3555218 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_38030 : A) : (term303 A B x f s t _38030) = (term141 A B x f s t _38030).
Proof. exact (eq_refl (term303 A B x f s t _38030)). Qed.
Lemma lem3555220 {A B : Type'} (_38031 : A) (f : A -> B) (t : A -> Prop) (h1 : term134 A B f t) : term304 A B f t _38031.
Proof. exact (@lem3555171 A B f t h1 _38031). Qed.
Lemma lem3555221 {A B : Type'} (f : A -> B) (t : A -> Prop) (_38031 : A) : (term304 A B f t _38031) = (term299 A B f t _38031).
Proof. exact (eq_refl (term304 A B f t _38031)). Qed.
Lemma lem3555222 {A B : Type'} (_38031 : A) (f : A -> B) (t : A -> Prop) (h1 : term134 A B f t) : term299 A B f t _38031.
Proof. exact (EQ_MP (@lem3555221 A B f t _38031) (@lem3555220 A B _38031 f t h1)). Qed.
Lemma lem3555223 {A B : Type'} (_38031 : A) (_38032 : A) (f : A -> B) (t : A -> Prop) (h1 : term134 A B f t) : term305 A B f t _38031 _38032.
Proof. exact (@lem3555222 A B _38031 f t h1 _38032). Qed.
Lemma lem3555224 {A B : Type'} (f : A -> B) (_38032 : A) (t : A -> Prop) (_38031 : A) : (term305 A B f t _38031 _38032) = (term296 A B f _38032 t _38031).
Proof. exact (eq_refl (term305 A B f t _38031 _38032)). Qed.
Lemma lem3555225 {A B : Type'} (_38032 : A) (_38031 : A) (f : A -> B) (t : A -> Prop) (h1 : term134 A B f t) : term296 A B f _38032 t _38031.
Proof. exact (EQ_MP (@lem3555224 A B f _38032 t _38031) (@lem3555223 A B _38031 _38032 f t h1)). Qed.
Lemma lem3555227 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term187 A B x' s x f t) : x = (f x').
Proof. exact (proj1 (@lem3554693 A B x' s x f t h1)). Qed.
Lemma lem3555237 {A B : Type'} (_38015 : A) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term158 A B x f s) : term151 A B x f s _38015.
Proof. exact (EQ_MP (@lem3555173 A B x f s _38015) (@lem3555172 A B _38015 x f s h1)). Qed.
Lemma lem3555251 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term187 A B x' s x f t) : x = (f x').
Proof. exact (proj1 (@lem3554693 A B x' s x f t h1)). Qed.
Lemma lem3555261 {A B : Type'} (_38018 : A) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term158 A B x f s) : term151 A B x f s _38018.
Proof. exact (EQ_MP (@lem3555182 A B x f s _38018) (@lem3555181 A B _38018 x f s h1)). Qed.
Lemma lem3555275 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term187 A B x' s x f t) : x = (f x').
Proof. exact (proj1 (@lem3554693 A B x' s x f t h1)). Qed.
Lemma lem3555285 {A B : Type'} (_38021 : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term158 A B x f t) : term151 A B x f t _38021.
Proof. exact (EQ_MP (@lem3555191 A B x f t _38021) (@lem3555190 A B _38021 x f t h1)). Qed.
Lemma lem3555299 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term187 A B x' s x f t) : x = (f x').
Proof. exact (proj1 (@lem3554693 A B x' s x f t h1)). Qed.
Lemma lem3555309 {A B : Type'} (_38024 : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term158 A B x f t) : term151 A B x f t _38024.
Proof. exact (EQ_MP (@lem3555200 A B x f t _38024) (@lem3555199 A B _38024 x f t h1)). Qed.
Lemma lem3555331 {A B : Type'} (_38027 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term240 A B s x' x f t x'') : term141 A B x f s t _38027.
Proof. exact (EQ_MP (@lem3555209 A B x f s t _38027) (@lem3555208 A B _38027 s x' x f t x'' h1)). Qed.
Lemma lem3555333 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term240 A B s x' x f t x'') : x = (f x'').
Proof. exact (proj1 (@lem3554706 A B s x' x f t x'' h1)). Qed.
Lemma lem3555337 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term240 A B s x' x f t x'') : x = (f x').
Proof. exact (proj1 (@lem3554707 A B s x' x f t x'' h1)). Qed.
Lemma lem3555350 {A B : Type'} (f : A -> B) (_38029 : A) (s : A -> Prop) (_38028 : A) : (term296 A B f _38029 s _38028) = (term306 A B f _38029 s _38028).
Proof. exact (@lem3552887 (term307 A B _38028 f _38029) (term308 A s _38029) (s _38028)). Qed.
Lemma lem3555361 {A B : Type'} (_38030 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term240 A B s x' x f t x'') : term141 A B x f s t _38030.
Proof. exact (EQ_MP (@lem3555218 A B x f s t _38030) (@lem3555217 A B _38030 s x' x f t x'' h1)). Qed.
Lemma lem3555363 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term240 A B s x' x f t x'') : x = (f x'').
Proof. exact (proj1 (@lem3554706 A B s x' x f t x'' h1)). Qed.
Lemma lem3555367 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term240 A B s x' x f t x'') : x = (f x').
Proof. exact (proj1 (@lem3554707 A B s x' x f t x'' h1)). Qed.
Lemma lem3555380 {A B : Type'} (f : A -> B) (_38032 : A) (t : A -> Prop) (_38031 : A) : (term296 A B f _38032 t _38031) = (term306 A B f _38032 t _38031).
Proof. exact (@lem3552887 (term307 A B _38031 f _38032) (term308 A t _38032) (t _38031)). Qed.
Lemma lem3555424 {A B : Type'} (f : A -> B) (s : A -> Prop) (_38015 : A) : (term309 A B f s _38015) = (term309 A B f s _38015).
Proof. exact (eq_refl (term309 A B f s _38015)). Qed.
Lemma lem3555425 {A B : Type'} (_38015 : A) (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term187 A B x' s x f t) : (term310 A B f s _38015 x) = (term311 A B s _38015 f x').
Proof. exact (MK_COMB (@lem3555424 A B f s _38015) (@lem3555227 A B x' s x f t h1)). Qed.
Lemma lem3555426 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_38015 : A) : (term311 A B s _38015 f x') = (term119 A B x' f s _38015).
Proof. exact (eq_refl (term311 A B s _38015 f x')). Qed.
Lemma lem3555427 {A B : Type'} (f : A -> B) (s : A -> Prop) (_38015 : A) (x : B) : (term312 A B f s _38015 x) = (term312 A B f s _38015 x).
Proof. exact (eq_refl (term312 A B f s _38015 x)). Qed.
Lemma lem3555428 {A B : Type'} (x : B) (x' : A) (f : A -> B) (s : A -> Prop) (_38015 : A) : ((term310 A B f s _38015 x) = (term311 A B s _38015 f x')) = ((term310 A B f s _38015 x) = (term119 A B x' f s _38015)).
Proof. exact (MK_COMB (@lem3555427 A B f s _38015 x) (@lem3555426 A B x' f s _38015)). Qed.
Lemma lem3555429 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (_38015 : A) : (term310 A B f s _38015 x) = (term151 A B x f s _38015).
Proof. exact (eq_refl (term310 A B f s _38015 x)). Qed.
Lemma lem3555430 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3555431 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (_38015 : A) : (term312 A B f s _38015 x) = (term313 A B x f s _38015).
Proof. exact (MK_COMB (@lem3555430) (@lem3555429 A B x f s _38015)). Qed.
Lemma lem3555432 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_38015 : A) : (term119 A B x' f s _38015) = (term119 A B x' f s _38015).
Proof. exact (eq_refl (term119 A B x' f s _38015)). Qed.
Lemma lem3555433 {A B : Type'} (x : B) (x' : A) (f : A -> B) (s : A -> Prop) (_38015 : A) : ((term310 A B f s _38015 x) = (term119 A B x' f s _38015)) = ((term151 A B x f s _38015) = (term119 A B x' f s _38015)).
Proof. exact (MK_COMB (@lem3555431 A B x f s _38015) (@lem3555432 A B x' f s _38015)). Qed.
Lemma lem3555434 {A B : Type'} (x : B) (x' : A) (f : A -> B) (s : A -> Prop) (_38015 : A) : ((term310 A B f s _38015 x) = (term311 A B s _38015 f x')) = ((term151 A B x f s _38015) = (term119 A B x' f s _38015)).
Proof. exact (TRANS (@lem3555428 A B x x' f s _38015) (@lem3555433 A B x x' f s _38015)). Qed.
Lemma lem3555435 {A B : Type'} (_38015 : A) (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term187 A B x' s x f t) : (term151 A B x f s _38015) = (term119 A B x' f s _38015).
Proof. exact (EQ_MP (@lem3555434 A B x x' f s _38015) (@lem3555425 A B _38015 x' s x f t h1)). Qed.
Lemma lem3555436 {A B : Type'} (_38015 : A) (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term158 A B x f s) (h2 : term187 A B x' s x f t) : term119 A B x' f s _38015.
Proof. exact (EQ_MP (@lem3555435 A B _38015 x' s x f t h2) (@lem3555237 A B _38015 x f s h1)). Qed.
Lemma lem3555493 {A B : Type'} (f : A -> B) (s : A -> Prop) (_38018 : A) : (term309 A B f s _38018) = (term309 A B f s _38018).
Proof. exact (eq_refl (term309 A B f s _38018)). Qed.
Lemma lem3555494 {A B : Type'} (_38018 : A) (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term187 A B x' s x f t) : (term310 A B f s _38018 x) = (term311 A B s _38018 f x').
Proof. exact (MK_COMB (@lem3555493 A B f s _38018) (@lem3555251 A B x' s x f t h1)). Qed.
Lemma lem3555495 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_38018 : A) : (term311 A B s _38018 f x') = (term119 A B x' f s _38018).
Proof. exact (eq_refl (term311 A B s _38018 f x')). Qed.
Lemma lem3555496 {A B : Type'} (f : A -> B) (s : A -> Prop) (_38018 : A) (x : B) : (term312 A B f s _38018 x) = (term312 A B f s _38018 x).
Proof. exact (eq_refl (term312 A B f s _38018 x)). Qed.
Lemma lem3555497 {A B : Type'} (x : B) (x' : A) (f : A -> B) (s : A -> Prop) (_38018 : A) : ((term310 A B f s _38018 x) = (term311 A B s _38018 f x')) = ((term310 A B f s _38018 x) = (term119 A B x' f s _38018)).
Proof. exact (MK_COMB (@lem3555496 A B f s _38018 x) (@lem3555495 A B x' f s _38018)). Qed.
Lemma lem3555498 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (_38018 : A) : (term310 A B f s _38018 x) = (term151 A B x f s _38018).
Proof. exact (eq_refl (term310 A B f s _38018 x)). Qed.
Lemma lem3555499 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3555500 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (_38018 : A) : (term312 A B f s _38018 x) = (term313 A B x f s _38018).
Proof. exact (MK_COMB (@lem3555499) (@lem3555498 A B x f s _38018)). Qed.
Lemma lem3555501 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_38018 : A) : (term119 A B x' f s _38018) = (term119 A B x' f s _38018).
Proof. exact (eq_refl (term119 A B x' f s _38018)). Qed.
Lemma lem3555502 {A B : Type'} (x : B) (x' : A) (f : A -> B) (s : A -> Prop) (_38018 : A) : ((term310 A B f s _38018 x) = (term119 A B x' f s _38018)) = ((term151 A B x f s _38018) = (term119 A B x' f s _38018)).
Proof. exact (MK_COMB (@lem3555500 A B x f s _38018) (@lem3555501 A B x' f s _38018)). Qed.
Lemma lem3555503 {A B : Type'} (x : B) (x' : A) (f : A -> B) (s : A -> Prop) (_38018 : A) : ((term310 A B f s _38018 x) = (term311 A B s _38018 f x')) = ((term151 A B x f s _38018) = (term119 A B x' f s _38018)).
Proof. exact (TRANS (@lem3555497 A B x x' f s _38018) (@lem3555502 A B x x' f s _38018)). Qed.
Lemma lem3555504 {A B : Type'} (_38018 : A) (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term187 A B x' s x f t) : (term151 A B x f s _38018) = (term119 A B x' f s _38018).
Proof. exact (EQ_MP (@lem3555503 A B x x' f s _38018) (@lem3555494 A B _38018 x' s x f t h1)). Qed.
Lemma lem3555505 {A B : Type'} (_38018 : A) (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term158 A B x f s) (h2 : term187 A B x' s x f t) : term119 A B x' f s _38018.
Proof. exact (EQ_MP (@lem3555504 A B _38018 x' s x f t h2) (@lem3555261 A B _38018 x f s h1)). Qed.
Lemma lem3555562 {A B : Type'} (f : A -> B) (t : A -> Prop) (_38021 : A) : (term309 A B f t _38021) = (term309 A B f t _38021).
Proof. exact (eq_refl (term309 A B f t _38021)). Qed.
Lemma lem3555563 {A B : Type'} (_38021 : A) (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term187 A B x' s x f t) : (term310 A B f t _38021 x) = (term311 A B t _38021 f x').
Proof. exact (MK_COMB (@lem3555562 A B f t _38021) (@lem3555275 A B x' s x f t h1)). Qed.
Lemma lem3555564 {A B : Type'} (x' : A) (f : A -> B) (t : A -> Prop) (_38021 : A) : (term311 A B t _38021 f x') = (term119 A B x' f t _38021).
Proof. exact (eq_refl (term311 A B t _38021 f x')). Qed.
Lemma lem3555565 {A B : Type'} (f : A -> B) (t : A -> Prop) (_38021 : A) (x : B) : (term312 A B f t _38021 x) = (term312 A B f t _38021 x).
Proof. exact (eq_refl (term312 A B f t _38021 x)). Qed.
Lemma lem3555566 {A B : Type'} (x : B) (x' : A) (f : A -> B) (t : A -> Prop) (_38021 : A) : ((term310 A B f t _38021 x) = (term311 A B t _38021 f x')) = ((term310 A B f t _38021 x) = (term119 A B x' f t _38021)).
Proof. exact (MK_COMB (@lem3555565 A B f t _38021 x) (@lem3555564 A B x' f t _38021)). Qed.
Lemma lem3555567 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (_38021 : A) : (term310 A B f t _38021 x) = (term151 A B x f t _38021).
Proof. exact (eq_refl (term310 A B f t _38021 x)). Qed.
Lemma lem3555568 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3555569 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (_38021 : A) : (term312 A B f t _38021 x) = (term313 A B x f t _38021).
Proof. exact (MK_COMB (@lem3555568) (@lem3555567 A B x f t _38021)). Qed.
Lemma lem3555570 {A B : Type'} (x' : A) (f : A -> B) (t : A -> Prop) (_38021 : A) : (term119 A B x' f t _38021) = (term119 A B x' f t _38021).
Proof. exact (eq_refl (term119 A B x' f t _38021)). Qed.
Lemma lem3555571 {A B : Type'} (x : B) (x' : A) (f : A -> B) (t : A -> Prop) (_38021 : A) : ((term310 A B f t _38021 x) = (term119 A B x' f t _38021)) = ((term151 A B x f t _38021) = (term119 A B x' f t _38021)).
Proof. exact (MK_COMB (@lem3555569 A B x f t _38021) (@lem3555570 A B x' f t _38021)). Qed.
Lemma lem3555572 {A B : Type'} (x : B) (x' : A) (f : A -> B) (t : A -> Prop) (_38021 : A) : ((term310 A B f t _38021 x) = (term311 A B t _38021 f x')) = ((term151 A B x f t _38021) = (term119 A B x' f t _38021)).
Proof. exact (TRANS (@lem3555566 A B x x' f t _38021) (@lem3555571 A B x x' f t _38021)). Qed.
Lemma lem3555573 {A B : Type'} (_38021 : A) (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term187 A B x' s x f t) : (term151 A B x f t _38021) = (term119 A B x' f t _38021).
Proof. exact (EQ_MP (@lem3555572 A B x x' f t _38021) (@lem3555563 A B _38021 x' s x f t h1)). Qed.
Lemma lem3555574 {A B : Type'} (_38021 : A) (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term158 A B x f t) (h2 : term187 A B x' s x f t) : term119 A B x' f t _38021.
Proof. exact (EQ_MP (@lem3555573 A B _38021 x' s x f t h2) (@lem3555285 A B _38021 x f t h1)). Qed.
Lemma lem3555631 {A B : Type'} (f : A -> B) (t : A -> Prop) (_38024 : A) : (term309 A B f t _38024) = (term309 A B f t _38024).
Proof. exact (eq_refl (term309 A B f t _38024)). Qed.
Lemma lem3555632 {A B : Type'} (_38024 : A) (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term187 A B x' s x f t) : (term310 A B f t _38024 x) = (term311 A B t _38024 f x').
Proof. exact (MK_COMB (@lem3555631 A B f t _38024) (@lem3555299 A B x' s x f t h1)). Qed.
Lemma lem3555633 {A B : Type'} (x' : A) (f : A -> B) (t : A -> Prop) (_38024 : A) : (term311 A B t _38024 f x') = (term119 A B x' f t _38024).
Proof. exact (eq_refl (term311 A B t _38024 f x')). Qed.
Lemma lem3555634 {A B : Type'} (f : A -> B) (t : A -> Prop) (_38024 : A) (x : B) : (term312 A B f t _38024 x) = (term312 A B f t _38024 x).
Proof. exact (eq_refl (term312 A B f t _38024 x)). Qed.
Lemma lem3555635 {A B : Type'} (x : B) (x' : A) (f : A -> B) (t : A -> Prop) (_38024 : A) : ((term310 A B f t _38024 x) = (term311 A B t _38024 f x')) = ((term310 A B f t _38024 x) = (term119 A B x' f t _38024)).
Proof. exact (MK_COMB (@lem3555634 A B f t _38024 x) (@lem3555633 A B x' f t _38024)). Qed.
Lemma lem3555636 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (_38024 : A) : (term310 A B f t _38024 x) = (term151 A B x f t _38024).
Proof. exact (eq_refl (term310 A B f t _38024 x)). Qed.
Lemma lem3555637 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3555638 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (_38024 : A) : (term312 A B f t _38024 x) = (term313 A B x f t _38024).
Proof. exact (MK_COMB (@lem3555637) (@lem3555636 A B x f t _38024)). Qed.
Lemma lem3555639 {A B : Type'} (x' : A) (f : A -> B) (t : A -> Prop) (_38024 : A) : (term119 A B x' f t _38024) = (term119 A B x' f t _38024).
Proof. exact (eq_refl (term119 A B x' f t _38024)). Qed.
Lemma lem3555640 {A B : Type'} (x : B) (x' : A) (f : A -> B) (t : A -> Prop) (_38024 : A) : ((term310 A B f t _38024 x) = (term119 A B x' f t _38024)) = ((term151 A B x f t _38024) = (term119 A B x' f t _38024)).
Proof. exact (MK_COMB (@lem3555638 A B x f t _38024) (@lem3555639 A B x' f t _38024)). Qed.
Lemma lem3555641 {A B : Type'} (x : B) (x' : A) (f : A -> B) (t : A -> Prop) (_38024 : A) : ((term310 A B f t _38024 x) = (term311 A B t _38024 f x')) = ((term151 A B x f t _38024) = (term119 A B x' f t _38024)).
Proof. exact (TRANS (@lem3555635 A B x x' f t _38024) (@lem3555640 A B x x' f t _38024)). Qed.
Lemma lem3555642 {A B : Type'} (_38024 : A) (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term187 A B x' s x f t) : (term151 A B x f t _38024) = (term119 A B x' f t _38024).
Proof. exact (EQ_MP (@lem3555641 A B x x' f t _38024) (@lem3555632 A B _38024 x' s x f t h1)). Qed.
Lemma lem3555643 {A B : Type'} (_38024 : A) (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term158 A B x f t) (h2 : term187 A B x' s x f t) : term119 A B x' f t _38024.
Proof. exact (EQ_MP (@lem3555642 A B _38024 x' s x f t h2) (@lem3555309 A B _38024 x f t h1)). Qed.
Lemma lem3555672 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_38027 : A) : (term314 A B f s t _38027) = (term314 A B f s t _38027).
Proof. exact (eq_refl (term314 A B f s t _38027)). Qed.
Lemma lem3555673 {A B : Type'} (_38027 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term240 A B s x' x f t x'') : (term315 A B f s t _38027 x) = (term316 A B s t _38027 f x').
Proof. exact (MK_COMB (@lem3555672 A B f s t _38027) (@lem3555337 A B s x' x f t x'' h1)). Qed.
Lemma lem3555674 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_38027 : A) : (term316 A B s t _38027 f x') = (term317 A B x' f s t _38027).
Proof. exact (eq_refl (term316 A B s t _38027 f x')). Qed.
Lemma lem3555675 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_38027 : A) (x : B) : (term318 A B f s t _38027 x) = (term318 A B f s t _38027 x).
Proof. exact (eq_refl (term318 A B f s t _38027 x)). Qed.
Lemma lem3555676 {A B : Type'} (x : B) (x' : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_38027 : A) : ((term315 A B f s t _38027 x) = (term316 A B s t _38027 f x')) = ((term315 A B f s t _38027 x) = (term317 A B x' f s t _38027)).
Proof. exact (MK_COMB (@lem3555675 A B f s t _38027 x) (@lem3555674 A B x' f s t _38027)). Qed.
Lemma lem3555677 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_38027 : A) : (term315 A B f s t _38027 x) = (term141 A B x f s t _38027).
Proof. exact (eq_refl (term315 A B f s t _38027 x)). Qed.
Lemma lem3555678 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3555679 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_38027 : A) : (term318 A B f s t _38027 x) = (term319 A B x f s t _38027).
Proof. exact (MK_COMB (@lem3555678) (@lem3555677 A B x f s t _38027)). Qed.
Lemma lem3555680 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_38027 : A) : (term317 A B x' f s t _38027) = (term317 A B x' f s t _38027).
Proof. exact (eq_refl (term317 A B x' f s t _38027)). Qed.
Lemma lem3555681 {A B : Type'} (x : B) (x' : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_38027 : A) : ((term315 A B f s t _38027 x) = (term317 A B x' f s t _38027)) = ((term141 A B x f s t _38027) = (term317 A B x' f s t _38027)).
Proof. exact (MK_COMB (@lem3555679 A B x f s t _38027) (@lem3555680 A B x' f s t _38027)). Qed.
Lemma lem3555682 {A B : Type'} (x : B) (x' : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_38027 : A) : ((term315 A B f s t _38027 x) = (term316 A B s t _38027 f x')) = ((term141 A B x f s t _38027) = (term317 A B x' f s t _38027)).
Proof. exact (TRANS (@lem3555676 A B x x' f s t _38027) (@lem3555681 A B x x' f s t _38027)). Qed.
Lemma lem3555683 {A B : Type'} (_38027 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term240 A B s x' x f t x'') : (term141 A B x f s t _38027) = (term317 A B x' f s t _38027).
Proof. exact (EQ_MP (@lem3555682 A B x x' f s t _38027) (@lem3555673 A B _38027 s x' x f t x'' h1)). Qed.
Lemma lem3555684 {A B : Type'} (_38027 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term240 A B s x' x f t x'') : term317 A B x' f s t _38027.
Proof. exact (EQ_MP (@lem3555683 A B _38027 s x' x f t x'' h1) (@lem3555331 A B _38027 s x' x f t x'' h1)). Qed.
Lemma lem3555685 {A B : Type'} (f : A -> B) (x'' : A) : (term320 A B f x'') = (term320 A B f x'').
Proof. exact (eq_refl (term320 A B f x'')). Qed.
Lemma lem3555686 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term240 A B s x' x f t x'') : (term321 A B f x'' x) = (term322 A B x'' f x').
Proof. exact (MK_COMB (@lem3555685 A B f x'') (@lem3555337 A B s x' x f t x'' h1)). Qed.
Lemma lem3555687 {A B : Type'} (x' : A) (f : A -> B) (x'' : A) : (term322 A B x'' f x') = ((f x') = (f x'')).
Proof. exact (eq_refl (term322 A B x'' f x')). Qed.
Lemma lem3555688 {A B : Type'} (f : A -> B) (x'' : A) (x : B) : (term323 A B f x'' x) = (term323 A B f x'' x).
Proof. exact (eq_refl (term323 A B f x'' x)). Qed.
Lemma lem3555689 {A B : Type'} (x : B) (x' : A) (f : A -> B) (x'' : A) : ((term321 A B f x'' x) = (term322 A B x'' f x')) = ((term321 A B f x'' x) = ((f x') = (f x''))).
Proof. exact (MK_COMB (@lem3555688 A B f x'' x) (@lem3555687 A B x' f x'')). Qed.
Lemma lem3555690 {A B : Type'} (x : B) (f : A -> B) (x'' : A) : (term321 A B f x'' x) = (x = (f x'')).
Proof. exact (eq_refl (term321 A B f x'' x)). Qed.
Lemma lem3555691 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3555692 {A B : Type'} (x : B) (f : A -> B) (x'' : A) : (term323 A B f x'' x) = (term324 A B x f x'').
Proof. exact (MK_COMB (@lem3555691) (@lem3555690 A B x f x'')). Qed.
Lemma lem3555693 {A B : Type'} (x' : A) (f : A -> B) (x'' : A) : ((f x') = (f x'')) = ((f x') = (f x'')).
Proof. exact (eq_refl ((f x') = (f x''))). Qed.
Lemma lem3555694 {A B : Type'} (x : B) (x' : A) (f : A -> B) (x'' : A) : ((term321 A B f x'' x) = ((f x') = (f x''))) = ((x = (f x'')) = ((f x') = (f x''))).
Proof. exact (MK_COMB (@lem3555692 A B x f x'') (@lem3555693 A B x' f x'')). Qed.
Lemma lem3555695 {A B : Type'} (x : B) (x' : A) (f : A -> B) (x'' : A) : ((term321 A B f x'' x) = (term322 A B x'' f x')) = ((x = (f x'')) = ((f x') = (f x''))).
Proof. exact (TRANS (@lem3555689 A B x x' f x'') (@lem3555694 A B x x' f x'')). Qed.
Lemma lem3555696 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term240 A B s x' x f t x'') : (x = (f x'')) = ((f x') = (f x'')).
Proof. exact (EQ_MP (@lem3555695 A B x x' f x'') (@lem3555686 A B s x' x f t x'' h1)). Qed.
Lemma lem3555739 {A B : Type'} (_38029 : A) (_38028 : A) (f : A -> B) (s : A -> Prop) (h1 : term134 A B f s) : term306 A B f _38029 s _38028.
Proof. exact (EQ_MP (@lem3555350 A B f _38029 s _38028) (@lem3555216 A B _38029 _38028 f s h1)). Qed.
Lemma lem3555754 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_38030 : A) : (term314 A B f s t _38030) = (term314 A B f s t _38030).
Proof. exact (eq_refl (term314 A B f s t _38030)). Qed.
Lemma lem3555755 {A B : Type'} (_38030 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term240 A B s x' x f t x'') : (term315 A B f s t _38030 x) = (term316 A B s t _38030 f x').
Proof. exact (MK_COMB (@lem3555754 A B f s t _38030) (@lem3555367 A B s x' x f t x'' h1)). Qed.
Lemma lem3555756 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_38030 : A) : (term316 A B s t _38030 f x') = (term317 A B x' f s t _38030).
Proof. exact (eq_refl (term316 A B s t _38030 f x')). Qed.
Lemma lem3555757 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_38030 : A) (x : B) : (term318 A B f s t _38030 x) = (term318 A B f s t _38030 x).
Proof. exact (eq_refl (term318 A B f s t _38030 x)). Qed.
Lemma lem3555758 {A B : Type'} (x : B) (x' : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_38030 : A) : ((term315 A B f s t _38030 x) = (term316 A B s t _38030 f x')) = ((term315 A B f s t _38030 x) = (term317 A B x' f s t _38030)).
Proof. exact (MK_COMB (@lem3555757 A B f s t _38030 x) (@lem3555756 A B x' f s t _38030)). Qed.
Lemma lem3555759 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_38030 : A) : (term315 A B f s t _38030 x) = (term141 A B x f s t _38030).
Proof. exact (eq_refl (term315 A B f s t _38030 x)). Qed.
Lemma lem3555760 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3555761 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_38030 : A) : (term318 A B f s t _38030 x) = (term319 A B x f s t _38030).
Proof. exact (MK_COMB (@lem3555760) (@lem3555759 A B x f s t _38030)). Qed.
Lemma lem3555762 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_38030 : A) : (term317 A B x' f s t _38030) = (term317 A B x' f s t _38030).
Proof. exact (eq_refl (term317 A B x' f s t _38030)). Qed.
Lemma lem3555763 {A B : Type'} (x : B) (x' : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_38030 : A) : ((term315 A B f s t _38030 x) = (term317 A B x' f s t _38030)) = ((term141 A B x f s t _38030) = (term317 A B x' f s t _38030)).
Proof. exact (MK_COMB (@lem3555761 A B x f s t _38030) (@lem3555762 A B x' f s t _38030)). Qed.
Lemma lem3555764 {A B : Type'} (x : B) (x' : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_38030 : A) : ((term315 A B f s t _38030 x) = (term316 A B s t _38030 f x')) = ((term141 A B x f s t _38030) = (term317 A B x' f s t _38030)).
Proof. exact (TRANS (@lem3555758 A B x x' f s t _38030) (@lem3555763 A B x x' f s t _38030)). Qed.
Lemma lem3555765 {A B : Type'} (_38030 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term240 A B s x' x f t x'') : (term141 A B x f s t _38030) = (term317 A B x' f s t _38030).
Proof. exact (EQ_MP (@lem3555764 A B x x' f s t _38030) (@lem3555755 A B _38030 s x' x f t x'' h1)). Qed.
Lemma lem3555766 {A B : Type'} (_38030 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term240 A B s x' x f t x'') : term317 A B x' f s t _38030.
Proof. exact (EQ_MP (@lem3555765 A B _38030 s x' x f t x'' h1) (@lem3555361 A B _38030 s x' x f t x'' h1)). Qed.
Lemma lem3555767 {A B : Type'} (f : A -> B) (x'' : A) : (term320 A B f x'') = (term320 A B f x'').
Proof. exact (eq_refl (term320 A B f x'')). Qed.
Lemma lem3555768 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term240 A B s x' x f t x'') : (term321 A B f x'' x) = (term322 A B x'' f x').
Proof. exact (MK_COMB (@lem3555767 A B f x'') (@lem3555367 A B s x' x f t x'' h1)). Qed.
Lemma lem3555769 {A B : Type'} (x' : A) (f : A -> B) (x'' : A) : (term322 A B x'' f x') = ((f x') = (f x'')).
Proof. exact (eq_refl (term322 A B x'' f x')). Qed.
Lemma lem3555770 {A B : Type'} (f : A -> B) (x'' : A) (x : B) : (term323 A B f x'' x) = (term323 A B f x'' x).
Proof. exact (eq_refl (term323 A B f x'' x)). Qed.
Lemma lem3555771 {A B : Type'} (x : B) (x' : A) (f : A -> B) (x'' : A) : ((term321 A B f x'' x) = (term322 A B x'' f x')) = ((term321 A B f x'' x) = ((f x') = (f x''))).
Proof. exact (MK_COMB (@lem3555770 A B f x'' x) (@lem3555769 A B x' f x'')). Qed.
Lemma lem3555772 {A B : Type'} (x : B) (f : A -> B) (x'' : A) : (term321 A B f x'' x) = (x = (f x'')).
Proof. exact (eq_refl (term321 A B f x'' x)). Qed.
Lemma lem3555773 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3555774 {A B : Type'} (x : B) (f : A -> B) (x'' : A) : (term323 A B f x'' x) = (term324 A B x f x'').
Proof. exact (MK_COMB (@lem3555773) (@lem3555772 A B x f x'')). Qed.
Lemma lem3555775 {A B : Type'} (x' : A) (f : A -> B) (x'' : A) : ((f x') = (f x'')) = ((f x') = (f x'')).
Proof. exact (eq_refl ((f x') = (f x''))). Qed.
Lemma lem3555776 {A B : Type'} (x : B) (x' : A) (f : A -> B) (x'' : A) : ((term321 A B f x'' x) = ((f x') = (f x''))) = ((x = (f x'')) = ((f x') = (f x''))).
Proof. exact (MK_COMB (@lem3555774 A B x f x'') (@lem3555775 A B x' f x'')). Qed.
Lemma lem3555777 {A B : Type'} (x : B) (x' : A) (f : A -> B) (x'' : A) : ((term321 A B f x'' x) = (term322 A B x'' f x')) = ((x = (f x'')) = ((f x') = (f x''))).
Proof. exact (TRANS (@lem3555771 A B x x' f x'') (@lem3555776 A B x x' f x'')). Qed.
Lemma lem3555778 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term240 A B s x' x f t x'') : (x = (f x'')) = ((f x') = (f x'')).
Proof. exact (EQ_MP (@lem3555777 A B x x' f x'') (@lem3555768 A B s x' x f t x'' h1)). Qed.
Lemma lem3555821 {A B : Type'} (_38032 : A) (_38031 : A) (f : A -> B) (t : A -> Prop) (h1 : term134 A B f t) : term306 A B f _38032 t _38031.
Proof. exact (EQ_MP (@lem3555380 A B f _38032 t _38031) (@lem3555225 A B _38032 _38031 f t h1)). Qed.
Lemma lem3555859 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem3555860 {B : Type'} (x : B) : x = x.
Proof. exact (@lem3555859 B x). Qed.
Lemma lem3555861 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (f x').
Proof. exact (@lem3555860 B (f x')). Qed.
Lemma lem3555862 {A B : Type'} (f : A -> B) (x' : A) : term325 A B f x'.
Proof. exact (fun h0 : term326 A B f x' => @lem3555861 A B f x'). Qed.
Lemma lem3555864 (p : Prop) : (term327 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3555865 {A B : Type'} (f : A -> B) (x' : A) : (term325 A B f x') = ((f x') = (f x')).
Proof. exact (@lem3555864 ((f x') = (f x'))). Qed.
Lemma lem3555866 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (f x').
Proof. exact (EQ_MP (@lem3555865 A B f x') (@lem3555862 A B f x')). Qed.
Lemma lem3555868 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term187 A B x' s x f t) : s x'.
Proof. exact (proj1 (@lem3554694 A B x' s x f t h1)). Qed.
Lemma lem3555869 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term187 A B x' s x f t) : term328 A s x'.
Proof. exact (fun h0 : term308 A s x' => @lem3555868 A B x' s x f t h1). Qed.
Lemma lem3555871 (p : Prop) : (term327 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3555872 {A : Type'} (s : A -> Prop) (x' : A) : (term328 A s x') = (s x').
Proof. exact (@lem3555871 (s x')). Qed.
Lemma lem3555873 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term187 A B x' s x f t) : s x'.
Proof. exact (EQ_MP (@lem3555872 A s x') (@lem3555869 A B x' s x f t h1)). Qed.
Lemma lem3555875 (a : Prop) (b : Prop) : (term329 a b) = (term330 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3555876 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_38015 : A) : (term119 A B x' f s _38015) = (term118 A B x' f s _38015).
Proof. exact (@lem3555875 ((f x') = (f _38015)) (s _38015)). Qed.
Lemma lem3555878 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3555879 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_38015 : A) : (term118 A B x' f s _38015) = (term331 A B x' f s _38015).
Proof. exact (@lem3555878 (term59 A B x' f s _38015)). Qed.
Lemma lem3555880 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_38015 : A) : (term119 A B x' f s _38015) = (term331 A B x' f s _38015).
Proof. exact (TRANS (@lem3555876 A B x' f s _38015) (@lem3555879 A B x' f s _38015)). Qed.
Lemma lem3555882 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term187 A B x' s x f t) : term332 A B f s x'.
Proof. exact (conj (@lem3555866 A B f x') (@lem3555873 A B x' s x f t h1)). Qed.
Lemma lem3555884 {A B : Type'} (_38015 : A) (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term158 A B x f s) (h2 : term187 A B x' s x f t) : term331 A B x' f s _38015.
Proof. exact (EQ_MP (@lem3555880 A B x' f s _38015) (@lem3555436 A B _38015 x' s x f t h1 h2)). Qed.
Lemma lem3555885 {A B : Type'} (_38015 : A) (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term158 A B x f s) (h2 : term187 A B x' s x f t) : term331 A B x' f s _38015.
Proof. exact (@lem3555884 A B _38015 x' s x f t h1 h2). Qed.
Lemma lem3555886 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term158 A B x f s) (h2 : term187 A B x' s x f t) : term333 A B f s x'.
Proof. exact (@lem3555885 A B x' x' s x f t h1 h2). Qed.
Lemma lem3555889 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term158 A B x f s) (h2 : term187 A B x' s x f t) : False.
Proof. exact (@lem3555886 A B x' s x f t h1 h2 (@lem3555882 A B x' s x f t h2)). Qed.
Lemma lem3555890 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term158 A B x f s) (h2 : term187 A B x' s x f t) : term334.
Proof. exact (fun h0 : ~ False => @lem3555889 A B x' s x f t h1 h2). Qed.
Lemma lem3555892 (p : Prop) : (term327 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3555893 : term334 = False.
Proof. exact (@lem3555892 False). Qed.
Lemma lem3555932 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem3555933 {B : Type'} (x : B) : x = x.
Proof. exact (@lem3555932 B x). Qed.
Lemma lem3555934 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (f x').
Proof. exact (@lem3555933 B (f x')). Qed.
Lemma lem3555935 {A B : Type'} (f : A -> B) (x' : A) : term325 A B f x'.
Proof. exact (fun h0 : term326 A B f x' => @lem3555934 A B f x'). Qed.
Lemma lem3555937 (p : Prop) : (term327 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3555938 {A B : Type'} (f : A -> B) (x' : A) : (term325 A B f x') = ((f x') = (f x')).
Proof. exact (@lem3555937 ((f x') = (f x'))). Qed.
Lemma lem3555939 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (f x').
Proof. exact (EQ_MP (@lem3555938 A B f x') (@lem3555935 A B f x')). Qed.
Lemma lem3555941 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term187 A B x' s x f t) : s x'.
Proof. exact (proj1 (@lem3554694 A B x' s x f t h1)). Qed.
Lemma lem3555942 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term187 A B x' s x f t) : term328 A s x'.
Proof. exact (fun h0 : term308 A s x' => @lem3555941 A B x' s x f t h1). Qed.
Lemma lem3555944 (p : Prop) : (term327 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3555945 {A : Type'} (s : A -> Prop) (x' : A) : (term328 A s x') = (s x').
Proof. exact (@lem3555944 (s x')). Qed.
Lemma lem3555946 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term187 A B x' s x f t) : s x'.
Proof. exact (EQ_MP (@lem3555945 A s x') (@lem3555942 A B x' s x f t h1)). Qed.
Lemma lem3555948 (a : Prop) (b : Prop) : (term329 a b) = (term330 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3555949 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_38018 : A) : (term119 A B x' f s _38018) = (term118 A B x' f s _38018).
Proof. exact (@lem3555948 ((f x') = (f _38018)) (s _38018)). Qed.
Lemma lem3555951 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3555952 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_38018 : A) : (term118 A B x' f s _38018) = (term331 A B x' f s _38018).
Proof. exact (@lem3555951 (term59 A B x' f s _38018)). Qed.
Lemma lem3555953 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_38018 : A) : (term119 A B x' f s _38018) = (term331 A B x' f s _38018).
Proof. exact (TRANS (@lem3555949 A B x' f s _38018) (@lem3555952 A B x' f s _38018)). Qed.
Lemma lem3555955 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term187 A B x' s x f t) : term332 A B f s x'.
Proof. exact (conj (@lem3555939 A B f x') (@lem3555946 A B x' s x f t h1)). Qed.
Lemma lem3555957 {A B : Type'} (_38018 : A) (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term158 A B x f s) (h2 : term187 A B x' s x f t) : term331 A B x' f s _38018.
Proof. exact (EQ_MP (@lem3555953 A B x' f s _38018) (@lem3555505 A B _38018 x' s x f t h1 h2)). Qed.
Lemma lem3555958 {A B : Type'} (_38018 : A) (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term158 A B x f s) (h2 : term187 A B x' s x f t) : term331 A B x' f s _38018.
Proof. exact (@lem3555957 A B _38018 x' s x f t h1 h2). Qed.
Lemma lem3555959 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term158 A B x f s) (h2 : term187 A B x' s x f t) : term333 A B f s x'.
Proof. exact (@lem3555958 A B x' x' s x f t h1 h2). Qed.
Lemma lem3555962 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term158 A B x f s) (h2 : term187 A B x' s x f t) : False.
Proof. exact (@lem3555959 A B x' s x f t h1 h2 (@lem3555955 A B x' s x f t h2)). Qed.
Lemma lem3555963 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term158 A B x f s) (h2 : term187 A B x' s x f t) : term334.
Proof. exact (fun h0 : ~ False => @lem3555962 A B x' s x f t h1 h2). Qed.
Lemma lem3555965 (p : Prop) : (term327 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3555966 : term334 = False.
Proof. exact (@lem3555965 False). Qed.
Lemma lem3556005 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem3556006 {B : Type'} (x : B) : x = x.
Proof. exact (@lem3556005 B x). Qed.
Lemma lem3556007 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (f x').
Proof. exact (@lem3556006 B (f x')). Qed.
Lemma lem3556008 {A B : Type'} (f : A -> B) (x' : A) : term325 A B f x'.
Proof. exact (fun h0 : term326 A B f x' => @lem3556007 A B f x'). Qed.
Lemma lem3556010 (p : Prop) : (term327 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3556011 {A B : Type'} (f : A -> B) (x' : A) : (term325 A B f x') = ((f x') = (f x')).
Proof. exact (@lem3556010 ((f x') = (f x'))). Qed.
Lemma lem3556012 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (f x').
Proof. exact (EQ_MP (@lem3556011 A B f x') (@lem3556008 A B f x')). Qed.
Lemma lem3556014 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term187 A B x' s x f t) : t x'.
Proof. exact (proj2 (@lem3554694 A B x' s x f t h1)). Qed.
Lemma lem3556015 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term187 A B x' s x f t) : term328 A t x'.
Proof. exact (fun h0 : term308 A t x' => @lem3556014 A B x' s x f t h1). Qed.
Lemma lem3556017 (p : Prop) : (term327 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3556018 {A : Type'} (t : A -> Prop) (x' : A) : (term328 A t x') = (t x').
Proof. exact (@lem3556017 (t x')). Qed.
Lemma lem3556019 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term187 A B x' s x f t) : t x'.
Proof. exact (EQ_MP (@lem3556018 A t x') (@lem3556015 A B x' s x f t h1)). Qed.
Lemma lem3556021 (a : Prop) (b : Prop) : (term329 a b) = (term330 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3556022 {A B : Type'} (x' : A) (f : A -> B) (t : A -> Prop) (_38021 : A) : (term119 A B x' f t _38021) = (term118 A B x' f t _38021).
Proof. exact (@lem3556021 ((f x') = (f _38021)) (t _38021)). Qed.
Lemma lem3556024 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3556025 {A B : Type'} (x' : A) (f : A -> B) (t : A -> Prop) (_38021 : A) : (term118 A B x' f t _38021) = (term331 A B x' f t _38021).
Proof. exact (@lem3556024 (term59 A B x' f t _38021)). Qed.
Lemma lem3556026 {A B : Type'} (x' : A) (f : A -> B) (t : A -> Prop) (_38021 : A) : (term119 A B x' f t _38021) = (term331 A B x' f t _38021).
Proof. exact (TRANS (@lem3556022 A B x' f t _38021) (@lem3556025 A B x' f t _38021)). Qed.
Lemma lem3556028 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term187 A B x' s x f t) : term332 A B f t x'.
Proof. exact (conj (@lem3556012 A B f x') (@lem3556019 A B x' s x f t h1)). Qed.
Lemma lem3556030 {A B : Type'} (_38021 : A) (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term158 A B x f t) (h2 : term187 A B x' s x f t) : term331 A B x' f t _38021.
Proof. exact (EQ_MP (@lem3556026 A B x' f t _38021) (@lem3555574 A B _38021 x' s x f t h1 h2)). Qed.
Lemma lem3556031 {A B : Type'} (_38021 : A) (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term158 A B x f t) (h2 : term187 A B x' s x f t) : term331 A B x' f t _38021.
Proof. exact (@lem3556030 A B _38021 x' s x f t h1 h2). Qed.
Lemma lem3556032 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term158 A B x f t) (h2 : term187 A B x' s x f t) : term333 A B f t x'.
Proof. exact (@lem3556031 A B x' x' s x f t h1 h2). Qed.
Lemma lem3556035 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term158 A B x f t) (h2 : term187 A B x' s x f t) : False.
Proof. exact (@lem3556032 A B x' s x f t h1 h2 (@lem3556028 A B x' s x f t h2)). Qed.
Lemma lem3556036 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term158 A B x f t) (h2 : term187 A B x' s x f t) : term334.
Proof. exact (fun h0 : ~ False => @lem3556035 A B x' s x f t h1 h2). Qed.
Lemma lem3556038 (p : Prop) : (term327 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3556039 : term334 = False.
Proof. exact (@lem3556038 False). Qed.
Lemma lem3556078 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem3556079 {B : Type'} (x : B) : x = x.
Proof. exact (@lem3556078 B x). Qed.
Lemma lem3556080 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (f x').
Proof. exact (@lem3556079 B (f x')). Qed.
Lemma lem3556081 {A B : Type'} (f : A -> B) (x' : A) : term325 A B f x'.
Proof. exact (fun h0 : term326 A B f x' => @lem3556080 A B f x'). Qed.
Lemma lem3556083 (p : Prop) : (term327 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3556084 {A B : Type'} (f : A -> B) (x' : A) : (term325 A B f x') = ((f x') = (f x')).
Proof. exact (@lem3556083 ((f x') = (f x'))). Qed.
Lemma lem3556085 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (f x').
Proof. exact (EQ_MP (@lem3556084 A B f x') (@lem3556081 A B f x')). Qed.
Lemma lem3556087 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term187 A B x' s x f t) : t x'.
Proof. exact (proj2 (@lem3554694 A B x' s x f t h1)). Qed.
Lemma lem3556088 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term187 A B x' s x f t) : term328 A t x'.
Proof. exact (fun h0 : term308 A t x' => @lem3556087 A B x' s x f t h1). Qed.
Lemma lem3556090 (p : Prop) : (term327 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3556091 {A : Type'} (t : A -> Prop) (x' : A) : (term328 A t x') = (t x').
Proof. exact (@lem3556090 (t x')). Qed.
Lemma lem3556092 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term187 A B x' s x f t) : t x'.
Proof. exact (EQ_MP (@lem3556091 A t x') (@lem3556088 A B x' s x f t h1)). Qed.
Lemma lem3556094 (a : Prop) (b : Prop) : (term329 a b) = (term330 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3556095 {A B : Type'} (x' : A) (f : A -> B) (t : A -> Prop) (_38024 : A) : (term119 A B x' f t _38024) = (term118 A B x' f t _38024).
Proof. exact (@lem3556094 ((f x') = (f _38024)) (t _38024)). Qed.
Lemma lem3556097 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3556098 {A B : Type'} (x' : A) (f : A -> B) (t : A -> Prop) (_38024 : A) : (term118 A B x' f t _38024) = (term331 A B x' f t _38024).
Proof. exact (@lem3556097 (term59 A B x' f t _38024)). Qed.
Lemma lem3556099 {A B : Type'} (x' : A) (f : A -> B) (t : A -> Prop) (_38024 : A) : (term119 A B x' f t _38024) = (term331 A B x' f t _38024).
Proof. exact (TRANS (@lem3556095 A B x' f t _38024) (@lem3556098 A B x' f t _38024)). Qed.
Lemma lem3556101 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term187 A B x' s x f t) : term332 A B f t x'.
Proof. exact (conj (@lem3556085 A B f x') (@lem3556092 A B x' s x f t h1)). Qed.
Lemma lem3556103 {A B : Type'} (_38024 : A) (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term158 A B x f t) (h2 : term187 A B x' s x f t) : term331 A B x' f t _38024.
Proof. exact (EQ_MP (@lem3556099 A B x' f t _38024) (@lem3555643 A B _38024 x' s x f t h1 h2)). Qed.
Lemma lem3556104 {A B : Type'} (_38024 : A) (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term158 A B x f t) (h2 : term187 A B x' s x f t) : term331 A B x' f t _38024.
Proof. exact (@lem3556103 A B _38024 x' s x f t h1 h2). Qed.
Lemma lem3556105 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term158 A B x f t) (h2 : term187 A B x' s x f t) : term333 A B f t x'.
Proof. exact (@lem3556104 A B x' x' s x f t h1 h2). Qed.
Lemma lem3556108 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term158 A B x f t) (h2 : term187 A B x' s x f t) : False.
Proof. exact (@lem3556105 A B x' s x f t h1 h2 (@lem3556101 A B x' s x f t h2)). Qed.
Lemma lem3556109 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term158 A B x f t) (h2 : term187 A B x' s x f t) : term334.
Proof. exact (fun h0 : ~ False => @lem3556108 A B x' s x f t h1 h2). Qed.
Lemma lem3556111 (p : Prop) : (term327 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3556112 : term334 = False.
Proof. exact (@lem3556111 False). Qed.
Lemma lem3556147 {B : Type'} (x : B) (y : B) (z : B) : term335 B x y z.
Proof. exact (@lem21385 B x y z). Qed.
Lemma lem3556151 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term240 A B s x' x f t x'') : (f x') = (f x'').
Proof. exact (EQ_MP (@lem3555696 A B s x' x f t x'' h1) (@lem3555333 A B s x' x f t x'' h1)). Qed.
Lemma lem3556152 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term240 A B s x' x f t x'') : term336 A B x' f x''.
Proof. exact (fun h0 : term307 A B x' f x'' => @lem3556151 A B s x' x f t x'' h1). Qed.
Lemma lem3556154 (p : Prop) : (term327 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3556155 {A B : Type'} (x' : A) (f : A -> B) (x'' : A) : (term336 A B x' f x'') = ((f x') = (f x'')).
Proof. exact (@lem3556154 ((f x') = (f x''))). Qed.
Lemma lem3556156 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term240 A B s x' x f t x'') : (f x') = (f x'').
Proof. exact (EQ_MP (@lem3556155 A B x' f x'') (@lem3556152 A B s x' x f t x'' h1)). Qed.
Lemma lem3556158 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term240 A B s x' x f t x'') : (f x') = (f x'').
Proof. exact (EQ_MP (@lem3555696 A B s x' x f t x'' h1) (@lem3555333 A B s x' x f t x'' h1)). Qed.
Lemma lem3556159 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term240 A B s x' x f t x'') : term336 A B x' f x''.
Proof. exact (fun h0 : term307 A B x' f x'' => @lem3556158 A B s x' x f t x'' h1). Qed.
Lemma lem3556161 (p : Prop) : (term327 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3556162 {A B : Type'} (x' : A) (f : A -> B) (x'' : A) : (term336 A B x' f x'') = ((f x') = (f x'')).
Proof. exact (@lem3556161 ((f x') = (f x''))). Qed.
Lemma lem3556163 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term240 A B s x' x f t x'') : (f x') = (f x'').
Proof. exact (EQ_MP (@lem3556162 A B x' f x'') (@lem3556159 A B s x' x f t x'' h1)). Qed.
Lemma lem3556165 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem3556166 {B : Type'} (x : B) : x = x.
Proof. exact (@lem3556165 B x). Qed.
Lemma lem3556167 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (f x').
Proof. exact (@lem3556166 B (f x')). Qed.
Lemma lem3556168 {A B : Type'} (f : A -> B) (x' : A) : term325 A B f x'.
Proof. exact (fun h0 : term326 A B f x' => @lem3556167 A B f x'). Qed.
Lemma lem3556170 (p : Prop) : (term327 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3556171 {A B : Type'} (f : A -> B) (x' : A) : (term325 A B f x') = ((f x') = (f x')).
Proof. exact (@lem3556170 ((f x') = (f x'))). Qed.
Lemma lem3556172 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (f x').
Proof. exact (EQ_MP (@lem3556171 A B f x') (@lem3556168 A B f x')). Qed.
Lemma lem3556190 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3556191 {B : Type'} (y : B) (x : B) (z : B) : (term337 B x y z) = (term338 B y x z).
Proof. exact (@lem3556190 (y = z) (term339 B x z)). Qed.
Lemma lem3556201 {B : Type'} (x : B) (y : B) : (term340 B x y) = (term340 B x y).
Proof. exact (eq_refl (term340 B x y)). Qed.
Lemma lem3556202 {B : Type'} (y : B) (x : B) (z : B) : (term335 B x y z) = (term341 B y x z).
Proof. exact (MK_COMB (@lem3556201 B x y) (@lem3556191 B y x z)). Qed.
Lemma lem3556206 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3556207 {B : Type'} (y : B) (x : B) (z : B) : (term341 B y x z) = (term342 B y x z).
Proof. exact (@lem3556206 (y = z) (term339 B x y) (term339 B x z)). Qed.
Lemma lem3556229 {B : Type'} (y : B) (x : B) (z : B) : (term335 B x y z) = (term342 B y x z).
Proof. exact (TRANS (@lem3556202 B y x z) (@lem3556207 B y x z)). Qed.
Lemma lem3556230 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3556231 {B : Type'} (y : B) (x : B) (z : B) : (term343 B x y z) = (term344 B y x z).
Proof. exact (MK_COMB (@lem3556230) (@lem3556229 B y x z)). Qed.
Lemma lem3556253 {B : Type'} (y : B) (x : B) (z : B) : (term342 B y x z) = (term342 B y x z).
Proof. exact (eq_refl (term342 B y x z)). Qed.
Lemma lem3556254 {B : Type'} (y : B) (x : B) (z : B) : ((term335 B x y z) = (term342 B y x z)) = ((term342 B y x z) = (term342 B y x z)).
Proof. exact (MK_COMB (@lem3556231 B y x z) (@lem3556253 B y x z)). Qed.
Lemma lem3556256 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3556257 (x : Prop) : (x = x) = True.
Proof. exact (@lem3556256 Prop x). Qed.
Lemma lem3556258 {B : Type'} (y : B) (x : B) (z : B) : ((term342 B y x z) = (term342 B y x z)) = True.
Proof. exact (@lem3556257 (term342 B y x z)). Qed.
Lemma lem3556259 {B : Type'} (y : B) (x : B) (z : B) : ((term335 B x y z) = (term342 B y x z)) = True.
Proof. exact (TRANS (@lem3556254 B y x z) (@lem3556258 B y x z)). Qed.
Lemma lem3556260 {B : Type'} (y : B) (x : B) (z : B) : True = ((term335 B x y z) = (term342 B y x z)).
Proof. exact (SYM (@lem3556259 B y x z)). Qed.
Lemma lem3556261 {B : Type'} (y : B) (x : B) (z : B) : (term335 B x y z) = (term342 B y x z).
Proof. exact (EQ_MP (@lem3556260 B y x z) (@lem0)). Qed.
Lemma lem3556262 {B : Type'} (y : B) (x : B) (z : B) : term342 B y x z.
Proof. exact (EQ_MP (@lem3556261 B y x z) (@lem3556147 B x y z)). Qed.
Lemma lem3556264 (b : Prop) (a : Prop) : (a \/ b) = (term345 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3556265 {B : Type'} (x : B) (y : B) (z : B) : (term342 B y x z) = (term346 B x y z).
Proof. exact (@lem3556264 (term347 B y x z) (y = z)). Qed.
Lemma lem3556267 (a : Prop) (b : Prop) : (term348 a b) = (term349 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3556268 {B : Type'} (y : B) (x : B) (z : B) : (term350 B y x z) = (term351 B y x z).
Proof. exact (@lem3556267 (term339 B x y) (term339 B x z)). Qed.
Lemma lem3556270 (a : Prop) : (term115 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3556271 {B : Type'} (x : B) (y : B) : (term352 B x y) = (x = y).
Proof. exact (@lem3556270 (x = y)). Qed.
Lemma lem3556272 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3556273 {B : Type'} (x : B) (y : B) : (term353 B x y) = (term354 B x y).
Proof. exact (MK_COMB (@lem3556272) (@lem3556271 B x y)). Qed.
Lemma lem3556275 (a : Prop) : (term115 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3556276 {B : Type'} (x : B) (z : B) : (term352 B x z) = (x = z).
Proof. exact (@lem3556275 (x = z)). Qed.
Lemma lem3556277 {B : Type'} (y : B) (x : B) (z : B) : (term351 B y x z) = (term355 B y x z).
Proof. exact (MK_COMB (@lem3556273 B x y) (@lem3556276 B x z)). Qed.
Lemma lem3556278 {B : Type'} (y : B) (x : B) (z : B) : (term350 B y x z) = (term355 B y x z).
Proof. exact (TRANS (@lem3556268 B y x z) (@lem3556277 B y x z)). Qed.
Lemma lem3556279 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3556280 {B : Type'} (y : B) (x : B) (z : B) : (term356 B y x z) = (term357 B y x z).
Proof. exact (MK_COMB (@lem3556279) (@lem3556278 B y x z)). Qed.
Lemma lem3556281 {B : Type'} (y : B) (z : B) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem3556282 {B : Type'} (x : B) (y : B) (z : B) : (term346 B x y z) = (term358 B x y z).
Proof. exact (MK_COMB (@lem3556280 B y x z) (@lem3556281 B y z)). Qed.
Lemma lem3556283 {B : Type'} (x : B) (y : B) (z : B) : (term342 B y x z) = (term358 B x y z).
Proof. exact (TRANS (@lem3556265 B x y z) (@lem3556282 B x y z)). Qed.
Lemma lem3556285 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term240 A B s x' x f t x'') : term359 A B x'' f x'.
Proof. exact (conj (@lem3556163 A B s x' x f t x'' h1) (@lem3556172 A B f x')). Qed.
Lemma lem3556287 {B : Type'} (x : B) (y : B) (z : B) : term358 B x y z.
Proof. exact (EQ_MP (@lem3556283 B x y z) (@lem3556262 B y x z)). Qed.
Lemma lem3556288 {B : Type'} (x : B) (y : B) (z : B) : term358 B x y z.
Proof. exact (@lem3556287 B x y z). Qed.
Lemma lem3556289 {A B : Type'} (x'' : A) (f : A -> B) (x' : A) : term360 A B x'' f x'.
Proof. exact (@lem3556288 B (f x') (f x'') (f x')). Qed.
Lemma lem3556292 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term240 A B s x' x f t x'') : (f x'') = (f x').
Proof. exact (@lem3556289 A B x'' f x' (@lem3556285 A B s x' x f t x'' h1)). Qed.
Lemma lem3556293 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term240 A B s x' x f t x'') : term336 A B x'' f x'.
Proof. exact (fun h0 : term307 A B x'' f x' => @lem3556292 A B s x' x f t x'' h1). Qed.
Lemma lem3556295 (p : Prop) : (term327 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3556296 {A B : Type'} (x'' : A) (f : A -> B) (x' : A) : (term336 A B x'' f x') = ((f x'') = (f x')).
Proof. exact (@lem3556295 ((f x'') = (f x'))). Qed.
Lemma lem3556297 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term240 A B s x' x f t x'') : (f x'') = (f x').
Proof. exact (EQ_MP (@lem3556296 A B x'' f x') (@lem3556293 A B s x' x f t x'' h1)). Qed.
Lemma lem3556299 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term240 A B s x' x f t x'') : s x'.
Proof. exact (proj2 (@lem3554707 A B s x' x f t x'' h1)). Qed.
Lemma lem3556300 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term240 A B s x' x f t x'') : term328 A s x'.
Proof. exact (fun h0 : term308 A s x' => @lem3556299 A B s x' x f t x'' h1). Qed.
Lemma lem3556302 (p : Prop) : (term327 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3556303 {A : Type'} (s : A -> Prop) (x' : A) : (term328 A s x') = (s x').
Proof. exact (@lem3556302 (s x')). Qed.
Lemma lem3556304 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term240 A B s x' x f t x'') : s x'.
Proof. exact (EQ_MP (@lem3556303 A s x') (@lem3556300 A B s x' x f t x'' h1)). Qed.
Lemma lem3556310 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3556311 {A B : Type'} (f : A -> B) (_38029 : A) (s : A -> Prop) (_38028 : A) : (term306 A B f _38029 s _38028) = (term361 A B f _38029 s _38028).
Proof. exact (@lem3556310 (term308 A s _38029) (term307 A B _38028 f _38029) (s _38028)). Qed.
Lemma lem3556325 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3556326 {A B : Type'} (s : A -> Prop) (_38028 : A) (f : A -> B) (_38029 : A) : (term362 A B f _38029 s _38028) = (term363 A B s _38028 f _38029).
Proof. exact (@lem3556325 (s _38028) (term307 A B _38028 f _38029)). Qed.
Lemma lem3556334 {A : Type'} (s : A -> Prop) (_38029 : A) : (term364 A s _38029) = (term364 A s _38029).
Proof. exact (eq_refl (term364 A s _38029)). Qed.
Lemma lem3556335 {A B : Type'} (s : A -> Prop) (_38028 : A) (f : A -> B) (_38029 : A) : (term361 A B f _38029 s _38028) = (term365 A B s _38028 f _38029).
Proof. exact (MK_COMB (@lem3556334 A s _38029) (@lem3556326 A B s _38028 f _38029)). Qed.
Lemma lem3556339 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3556340 {A B : Type'} (s : A -> Prop) (_38028 : A) (f : A -> B) (_38029 : A) : (term365 A B s _38028 f _38029) = (term366 A B s _38028 f _38029).
Proof. exact (@lem3556339 (s _38028) (term308 A s _38029) (term307 A B _38028 f _38029)). Qed.
Lemma lem3556358 {A B : Type'} (s : A -> Prop) (_38028 : A) (f : A -> B) (_38029 : A) : (term361 A B f _38029 s _38028) = (term366 A B s _38028 f _38029).
Proof. exact (TRANS (@lem3556335 A B s _38028 f _38029) (@lem3556340 A B s _38028 f _38029)). Qed.
Lemma lem3556359 {A B : Type'} (s : A -> Prop) (_38028 : A) (f : A -> B) (_38029 : A) : (term306 A B f _38029 s _38028) = (term366 A B s _38028 f _38029).
Proof. exact (TRANS (@lem3556311 A B f _38029 s _38028) (@lem3556358 A B s _38028 f _38029)). Qed.
Lemma lem3556360 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3556361 {A B : Type'} (s : A -> Prop) (_38028 : A) (f : A -> B) (_38029 : A) : (term367 A B f _38029 s _38028) = (term368 A B s _38028 f _38029).
Proof. exact (MK_COMB (@lem3556360) (@lem3556359 A B s _38028 f _38029)). Qed.
Lemma lem3556375 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3556376 {A B : Type'} (s : A -> Prop) (_38028 : A) (f : A -> B) (_38029 : A) : (term119 A B _38028 f s _38029) = (term369 A B s _38028 f _38029).
Proof. exact (@lem3556375 (term308 A s _38029) (term307 A B _38028 f _38029)). Qed.
Lemma lem3556384 {A : Type'} (s : A -> Prop) (_38028 : A) : (term370 A s _38028) = (term370 A s _38028).
Proof. exact (eq_refl (term370 A s _38028)). Qed.
Lemma lem3556385 {A B : Type'} (s : A -> Prop) (_38028 : A) (f : A -> B) (_38029 : A) : (term371 A B _38028 f s _38029) = (term366 A B s _38028 f _38029).
Proof. exact (MK_COMB (@lem3556384 A s _38028) (@lem3556376 A B s _38028 f _38029)). Qed.
Lemma lem3556396 {A B : Type'} (s : A -> Prop) (_38028 : A) (f : A -> B) (_38029 : A) : ((term306 A B f _38029 s _38028) = (term371 A B _38028 f s _38029)) = ((term366 A B s _38028 f _38029) = (term366 A B s _38028 f _38029)).
Proof. exact (MK_COMB (@lem3556361 A B s _38028 f _38029) (@lem3556385 A B s _38028 f _38029)). Qed.
Lemma lem3556398 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3556399 (x : Prop) : (x = x) = True.
Proof. exact (@lem3556398 Prop x). Qed.
Lemma lem3556400 {A B : Type'} (s : A -> Prop) (_38028 : A) (f : A -> B) (_38029 : A) : ((term366 A B s _38028 f _38029) = (term366 A B s _38028 f _38029)) = True.
Proof. exact (@lem3556399 (term366 A B s _38028 f _38029)). Qed.
Lemma lem3556401 {A B : Type'} (_38028 : A) (f : A -> B) (s : A -> Prop) (_38029 : A) : ((term306 A B f _38029 s _38028) = (term371 A B _38028 f s _38029)) = True.
Proof. exact (TRANS (@lem3556396 A B s _38028 f _38029) (@lem3556400 A B s _38028 f _38029)). Qed.
Lemma lem3556402 {A B : Type'} (_38028 : A) (f : A -> B) (s : A -> Prop) (_38029 : A) : True = ((term306 A B f _38029 s _38028) = (term371 A B _38028 f s _38029)).
Proof. exact (SYM (@lem3556401 A B _38028 f s _38029)). Qed.
Lemma lem3556403 {A B : Type'} (_38028 : A) (f : A -> B) (s : A -> Prop) (_38029 : A) : (term306 A B f _38029 s _38028) = (term371 A B _38028 f s _38029).
Proof. exact (EQ_MP (@lem3556402 A B _38028 f s _38029) (@lem0)). Qed.
Lemma lem3556404 {A B : Type'} (_38028 : A) (_38029 : A) (f : A -> B) (s : A -> Prop) (h1 : term134 A B f s) : term371 A B _38028 f s _38029.
Proof. exact (EQ_MP (@lem3556403 A B _38028 f s _38029) (@lem3555739 A B _38029 _38028 f s h1)). Qed.
Lemma lem3556406 (b : Prop) (a : Prop) : (a \/ b) = (term345 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3556407 {A B : Type'} (f : A -> B) (_38029 : A) (s : A -> Prop) (_38028 : A) : (term371 A B _38028 f s _38029) = (term372 A B f _38029 s _38028).
Proof. exact (@lem3556406 (term119 A B _38028 f s _38029) (s _38028)). Qed.
Lemma lem3556409 (a : Prop) (b : Prop) : (term348 a b) = (term349 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3556410 {A B : Type'} (_38028 : A) (f : A -> B) (s : A -> Prop) (_38029 : A) : (term373 A B _38028 f s _38029) = (term374 A B _38028 f s _38029).
Proof. exact (@lem3556409 (term307 A B _38028 f _38029) (term308 A s _38029)). Qed.
Lemma lem3556412 (a : Prop) : (term115 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3556413 {A B : Type'} (_38028 : A) (f : A -> B) (_38029 : A) : (term375 A B _38028 f _38029) = ((f _38028) = (f _38029)).
Proof. exact (@lem3556412 ((f _38028) = (f _38029))). Qed.
Lemma lem3556414 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3556415 {A B : Type'} (_38028 : A) (f : A -> B) (_38029 : A) : (term376 A B _38028 f _38029) = (term57 A B _38028 f _38029).
Proof. exact (MK_COMB (@lem3556414) (@lem3556413 A B _38028 f _38029)). Qed.
Lemma lem3556417 (a : Prop) : (term115 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3556418 {A : Type'} (s : A -> Prop) (_38029 : A) : (term377 A s _38029) = (s _38029).
Proof. exact (@lem3556417 (s _38029)). Qed.
Lemma lem3556419 {A B : Type'} (_38028 : A) (f : A -> B) (s : A -> Prop) (_38029 : A) : (term374 A B _38028 f s _38029) = (term59 A B _38028 f s _38029).
Proof. exact (MK_COMB (@lem3556415 A B _38028 f _38029) (@lem3556418 A s _38029)). Qed.
Lemma lem3556420 {A B : Type'} (_38028 : A) (f : A -> B) (s : A -> Prop) (_38029 : A) : (term373 A B _38028 f s _38029) = (term59 A B _38028 f s _38029).
Proof. exact (TRANS (@lem3556410 A B _38028 f s _38029) (@lem3556419 A B _38028 f s _38029)). Qed.
Lemma lem3556421 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3556422 {A B : Type'} (_38028 : A) (f : A -> B) (s : A -> Prop) (_38029 : A) : (term378 A B _38028 f s _38029) = (term379 A B _38028 f s _38029).
Proof. exact (MK_COMB (@lem3556421) (@lem3556420 A B _38028 f s _38029)). Qed.
Lemma lem3556423 {A : Type'} (s : A -> Prop) (_38028 : A) : (s _38028) = (s _38028).
Proof. exact (eq_refl (s _38028)). Qed.
Lemma lem3556424 {A B : Type'} (f : A -> B) (_38029 : A) (s : A -> Prop) (_38028 : A) : (term372 A B f _38029 s _38028) = (term380 A B f _38029 s _38028).
Proof. exact (MK_COMB (@lem3556422 A B _38028 f s _38029) (@lem3556423 A s _38028)). Qed.
Lemma lem3556425 {A B : Type'} (f : A -> B) (_38029 : A) (s : A -> Prop) (_38028 : A) : (term371 A B _38028 f s _38029) = (term380 A B f _38029 s _38028).
Proof. exact (TRANS (@lem3556407 A B f _38029 s _38028) (@lem3556424 A B f _38029 s _38028)). Qed.
Lemma lem3556427 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term240 A B s x' x f t x'') : term59 A B x'' f s x'.
Proof. exact (conj (@lem3556297 A B s x' x f t x'' h1) (@lem3556304 A B s x' x f t x'' h1)). Qed.
Lemma lem3556429 {A B : Type'} (_38029 : A) (_38028 : A) (f : A -> B) (s : A -> Prop) (h1 : term134 A B f s) : term380 A B f _38029 s _38028.
Proof. exact (EQ_MP (@lem3556425 A B f _38029 s _38028) (@lem3556404 A B _38028 _38029 f s h1)). Qed.
Lemma lem3556430 {A B : Type'} (_38029 : A) (_38028 : A) (f : A -> B) (s : A -> Prop) (h1 : term134 A B f s) : term380 A B f _38029 s _38028.
Proof. exact (@lem3556429 A B _38029 _38028 f s h1). Qed.
Lemma lem3556431 {A B : Type'} (x' : A) (x'' : A) (f : A -> B) (s : A -> Prop) (h1 : term134 A B f s) : term380 A B f x' s x''.
Proof. exact (@lem3556430 A B x' x'' f s h1). Qed.
Lemma lem3556434 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term134 A B f s) (h2 : term240 A B s x' x f t x'') : s x''.
Proof. exact (@lem3556431 A B x' x'' f s h1 (@lem3556427 A B s x' x f t x'' h2)). Qed.
Lemma lem3556435 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term134 A B f s) (h2 : term240 A B s x' x f t x'') : term328 A s x''.
Proof. exact (fun h0 : term308 A s x'' => @lem3556434 A B s x' x f t x'' h1 h2). Qed.
Lemma lem3556437 (p : Prop) : (term327 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3556438 {A : Type'} (s : A -> Prop) (x'' : A) : (term328 A s x'') = (s x'').
Proof. exact (@lem3556437 (s x'')). Qed.
Lemma lem3556439 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term134 A B f s) (h2 : term240 A B s x' x f t x'') : s x''.
Proof. exact (EQ_MP (@lem3556438 A s x'') (@lem3556435 A B s x' x f t x'' h1 h2)). Qed.
Lemma lem3556441 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term240 A B s x' x f t x'') : t x''.
Proof. exact (proj2 (@lem3554706 A B s x' x f t x'' h1)). Qed.
Lemma lem3556442 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term240 A B s x' x f t x'') : term328 A t x''.
Proof. exact (fun h0 : term308 A t x'' => @lem3556441 A B s x' x f t x'' h1). Qed.
Lemma lem3556444 (p : Prop) : (term327 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3556445 {A : Type'} (t : A -> Prop) (x'' : A) : (term328 A t x'') = (t x'').
Proof. exact (@lem3556444 (t x'')). Qed.
Lemma lem3556446 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term240 A B s x' x f t x'') : t x''.
Proof. exact (EQ_MP (@lem3556445 A t x'') (@lem3556442 A B s x' x f t x'' h1)). Qed.
Lemma lem3556448 (a : Prop) (b : Prop) : (term329 a b) = (term330 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3556449 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_38027 : A) : (term138 A s t _38027) = (term137 A s t _38027).
Proof. exact (@lem3556448 (s _38027) (t _38027)). Qed.
Lemma lem3556450 {A B : Type'} (x' : A) (f : A -> B) (_38027 : A) : (term381 A B x' f _38027) = (term381 A B x' f _38027).
Proof. exact (eq_refl (term381 A B x' f _38027)). Qed.
Lemma lem3556451 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_38027 : A) : (term317 A B x' f s t _38027) = (term382 A B x' f s t _38027).
Proof. exact (MK_COMB (@lem3556450 A B x' f _38027) (@lem3556449 A s t _38027)). Qed.
Lemma lem3556453 (a : Prop) (b : Prop) : (term329 a b) = (term330 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3556454 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_38027 : A) : (term382 A B x' f s t _38027) = (term383 A B x' f s t _38027).
Proof. exact (@lem3556453 ((f x') = (f _38027)) (term79 A s t _38027)). Qed.
Lemma lem3556455 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_38027 : A) : (term317 A B x' f s t _38027) = (term383 A B x' f s t _38027).
Proof. exact (TRANS (@lem3556451 A B x' f s t _38027) (@lem3556454 A B x' f s t _38027)). Qed.
Lemma lem3556457 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3556458 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_38027 : A) : (term383 A B x' f s t _38027) = (term384 A B x' f s t _38027).
Proof. exact (@lem3556457 (term385 A B x' f s t _38027)). Qed.
Lemma lem3556459 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_38027 : A) : (term317 A B x' f s t _38027) = (term384 A B x' f s t _38027).
Proof. exact (TRANS (@lem3556455 A B x' f s t _38027) (@lem3556458 A B x' f s t _38027)). Qed.
Lemma lem3556461 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term134 A B f s) (h2 : term240 A B s x' x f t x'') : term79 A s t x''.
Proof. exact (conj (@lem3556439 A B s x' x f t x'' h1 h2) (@lem3556446 A B s x' x f t x'' h2)). Qed.
Lemma lem3556462 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term134 A B f s) (h2 : term240 A B s x' x f t x'') : term385 A B x' f s t x''.
Proof. exact (conj (@lem3556156 A B s x' x f t x'' h2) (@lem3556461 A B s x' x f t x'' h1 h2)). Qed.
Lemma lem3556464 {A B : Type'} (_38027 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term240 A B s x' x f t x'') : term384 A B x' f s t _38027.
Proof. exact (EQ_MP (@lem3556459 A B x' f s t _38027) (@lem3555684 A B _38027 s x' x f t x'' h1)). Qed.
Lemma lem3556465 {A B : Type'} (_38027 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term240 A B s x' x f t x'') : term384 A B x' f s t _38027.
Proof. exact (@lem3556464 A B _38027 s x' x f t x'' h1). Qed.
Lemma lem3556466 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term240 A B s x' x f t x'') : term384 A B x' f s t x''.
Proof. exact (@lem3556465 A B x'' s x' x f t x'' h1). Qed.
Lemma lem3556469 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term134 A B f s) (h2 : term240 A B s x' x f t x'') : False.
Proof. exact (@lem3556466 A B s x' x f t x'' h2 (@lem3556462 A B s x' x f t x'' h1 h2)). Qed.
Lemma lem3556470 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term134 A B f s) (h2 : term240 A B s x' x f t x'') : term334.
Proof. exact (fun h0 : ~ False => @lem3556469 A B s x' x f t x'' h1 h2). Qed.
Lemma lem3556472 (p : Prop) : (term327 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3556473 : term334 = False.
Proof. exact (@lem3556472 False). Qed.
Lemma lem3556512 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem3556513 {B : Type'} (x : B) : x = x.
Proof. exact (@lem3556512 B x). Qed.
Lemma lem3556514 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (f x').
Proof. exact (@lem3556513 B (f x')). Qed.
Lemma lem3556515 {A B : Type'} (f : A -> B) (x' : A) : term325 A B f x'.
Proof. exact (fun h0 : term326 A B f x' => @lem3556514 A B f x'). Qed.
Lemma lem3556517 (p : Prop) : (term327 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3556518 {A B : Type'} (f : A -> B) (x' : A) : (term325 A B f x') = ((f x') = (f x')).
Proof. exact (@lem3556517 ((f x') = (f x'))). Qed.
Lemma lem3556519 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (f x').
Proof. exact (EQ_MP (@lem3556518 A B f x') (@lem3556515 A B f x')). Qed.
Lemma lem3556521 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term240 A B s x' x f t x'') : s x'.
Proof. exact (proj2 (@lem3554707 A B s x' x f t x'' h1)). Qed.
Lemma lem3556522 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term240 A B s x' x f t x'') : term328 A s x'.
Proof. exact (fun h0 : term308 A s x' => @lem3556521 A B s x' x f t x'' h1). Qed.
Lemma lem3556524 (p : Prop) : (term327 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3556525 {A : Type'} (s : A -> Prop) (x' : A) : (term328 A s x') = (s x').
Proof. exact (@lem3556524 (s x')). Qed.
Lemma lem3556526 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term240 A B s x' x f t x'') : s x'.
Proof. exact (EQ_MP (@lem3556525 A s x') (@lem3556522 A B s x' x f t x'' h1)). Qed.
Lemma lem3556528 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term240 A B s x' x f t x'') : (f x') = (f x'').
Proof. exact (EQ_MP (@lem3555778 A B s x' x f t x'' h1) (@lem3555363 A B s x' x f t x'' h1)). Qed.
Lemma lem3556529 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term240 A B s x' x f t x'') : term336 A B x' f x''.
Proof. exact (fun h0 : term307 A B x' f x'' => @lem3556528 A B s x' x f t x'' h1). Qed.
Lemma lem3556531 (p : Prop) : (term327 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3556532 {A B : Type'} (x' : A) (f : A -> B) (x'' : A) : (term336 A B x' f x'') = ((f x') = (f x'')).
Proof. exact (@lem3556531 ((f x') = (f x''))). Qed.
Lemma lem3556533 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term240 A B s x' x f t x'') : (f x') = (f x'').
Proof. exact (EQ_MP (@lem3556532 A B x' f x'') (@lem3556529 A B s x' x f t x'' h1)). Qed.
Lemma lem3556535 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term240 A B s x' x f t x'') : t x''.
Proof. exact (proj2 (@lem3554706 A B s x' x f t x'' h1)). Qed.
Lemma lem3556536 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term240 A B s x' x f t x'') : term328 A t x''.
Proof. exact (fun h0 : term308 A t x'' => @lem3556535 A B s x' x f t x'' h1). Qed.
Lemma lem3556538 (p : Prop) : (term327 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3556539 {A : Type'} (t : A -> Prop) (x'' : A) : (term328 A t x'') = (t x'').
Proof. exact (@lem3556538 (t x'')). Qed.
Lemma lem3556540 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term240 A B s x' x f t x'') : t x''.
Proof. exact (EQ_MP (@lem3556539 A t x'') (@lem3556536 A B s x' x f t x'' h1)). Qed.
Lemma lem3556546 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3556547 {A B : Type'} (f : A -> B) (_38032 : A) (t : A -> Prop) (_38031 : A) : (term306 A B f _38032 t _38031) = (term361 A B f _38032 t _38031).
Proof. exact (@lem3556546 (term308 A t _38032) (term307 A B _38031 f _38032) (t _38031)). Qed.
Lemma lem3556561 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3556562 {A B : Type'} (t : A -> Prop) (_38031 : A) (f : A -> B) (_38032 : A) : (term362 A B f _38032 t _38031) = (term363 A B t _38031 f _38032).
Proof. exact (@lem3556561 (t _38031) (term307 A B _38031 f _38032)). Qed.
Lemma lem3556570 {A : Type'} (t : A -> Prop) (_38032 : A) : (term364 A t _38032) = (term364 A t _38032).
Proof. exact (eq_refl (term364 A t _38032)). Qed.
Lemma lem3556571 {A B : Type'} (t : A -> Prop) (_38031 : A) (f : A -> B) (_38032 : A) : (term361 A B f _38032 t _38031) = (term365 A B t _38031 f _38032).
Proof. exact (MK_COMB (@lem3556570 A t _38032) (@lem3556562 A B t _38031 f _38032)). Qed.
Lemma lem3556575 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3556576 {A B : Type'} (t : A -> Prop) (_38031 : A) (f : A -> B) (_38032 : A) : (term365 A B t _38031 f _38032) = (term366 A B t _38031 f _38032).
Proof. exact (@lem3556575 (t _38031) (term308 A t _38032) (term307 A B _38031 f _38032)). Qed.
Lemma lem3556594 {A B : Type'} (t : A -> Prop) (_38031 : A) (f : A -> B) (_38032 : A) : (term361 A B f _38032 t _38031) = (term366 A B t _38031 f _38032).
Proof. exact (TRANS (@lem3556571 A B t _38031 f _38032) (@lem3556576 A B t _38031 f _38032)). Qed.
Lemma lem3556595 {A B : Type'} (t : A -> Prop) (_38031 : A) (f : A -> B) (_38032 : A) : (term306 A B f _38032 t _38031) = (term366 A B t _38031 f _38032).
Proof. exact (TRANS (@lem3556547 A B f _38032 t _38031) (@lem3556594 A B t _38031 f _38032)). Qed.
Lemma lem3556596 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3556597 {A B : Type'} (t : A -> Prop) (_38031 : A) (f : A -> B) (_38032 : A) : (term367 A B f _38032 t _38031) = (term368 A B t _38031 f _38032).
Proof. exact (MK_COMB (@lem3556596) (@lem3556595 A B t _38031 f _38032)). Qed.
Lemma lem3556611 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3556612 {A B : Type'} (t : A -> Prop) (_38031 : A) (f : A -> B) (_38032 : A) : (term119 A B _38031 f t _38032) = (term369 A B t _38031 f _38032).
Proof. exact (@lem3556611 (term308 A t _38032) (term307 A B _38031 f _38032)). Qed.
Lemma lem3556620 {A : Type'} (t : A -> Prop) (_38031 : A) : (term370 A t _38031) = (term370 A t _38031).
Proof. exact (eq_refl (term370 A t _38031)). Qed.
Lemma lem3556621 {A B : Type'} (t : A -> Prop) (_38031 : A) (f : A -> B) (_38032 : A) : (term371 A B _38031 f t _38032) = (term366 A B t _38031 f _38032).
Proof. exact (MK_COMB (@lem3556620 A t _38031) (@lem3556612 A B t _38031 f _38032)). Qed.
Lemma lem3556632 {A B : Type'} (t : A -> Prop) (_38031 : A) (f : A -> B) (_38032 : A) : ((term306 A B f _38032 t _38031) = (term371 A B _38031 f t _38032)) = ((term366 A B t _38031 f _38032) = (term366 A B t _38031 f _38032)).
Proof. exact (MK_COMB (@lem3556597 A B t _38031 f _38032) (@lem3556621 A B t _38031 f _38032)). Qed.
Lemma lem3556634 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3556635 (x : Prop) : (x = x) = True.
Proof. exact (@lem3556634 Prop x). Qed.
Lemma lem3556636 {A B : Type'} (t : A -> Prop) (_38031 : A) (f : A -> B) (_38032 : A) : ((term366 A B t _38031 f _38032) = (term366 A B t _38031 f _38032)) = True.
Proof. exact (@lem3556635 (term366 A B t _38031 f _38032)). Qed.
Lemma lem3556637 {A B : Type'} (_38031 : A) (f : A -> B) (t : A -> Prop) (_38032 : A) : ((term306 A B f _38032 t _38031) = (term371 A B _38031 f t _38032)) = True.
Proof. exact (TRANS (@lem3556632 A B t _38031 f _38032) (@lem3556636 A B t _38031 f _38032)). Qed.
Lemma lem3556638 {A B : Type'} (_38031 : A) (f : A -> B) (t : A -> Prop) (_38032 : A) : True = ((term306 A B f _38032 t _38031) = (term371 A B _38031 f t _38032)).
Proof. exact (SYM (@lem3556637 A B _38031 f t _38032)). Qed.
Lemma lem3556639 {A B : Type'} (_38031 : A) (f : A -> B) (t : A -> Prop) (_38032 : A) : (term306 A B f _38032 t _38031) = (term371 A B _38031 f t _38032).
Proof. exact (EQ_MP (@lem3556638 A B _38031 f t _38032) (@lem0)). Qed.
Lemma lem3556640 {A B : Type'} (_38031 : A) (_38032 : A) (f : A -> B) (t : A -> Prop) (h1 : term134 A B f t) : term371 A B _38031 f t _38032.
Proof. exact (EQ_MP (@lem3556639 A B _38031 f t _38032) (@lem3555821 A B _38032 _38031 f t h1)). Qed.
Lemma lem3556642 (b : Prop) (a : Prop) : (a \/ b) = (term345 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3556643 {A B : Type'} (f : A -> B) (_38032 : A) (t : A -> Prop) (_38031 : A) : (term371 A B _38031 f t _38032) = (term372 A B f _38032 t _38031).
Proof. exact (@lem3556642 (term119 A B _38031 f t _38032) (t _38031)). Qed.
Lemma lem3556645 (a : Prop) (b : Prop) : (term348 a b) = (term349 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3556646 {A B : Type'} (_38031 : A) (f : A -> B) (t : A -> Prop) (_38032 : A) : (term373 A B _38031 f t _38032) = (term374 A B _38031 f t _38032).
Proof. exact (@lem3556645 (term307 A B _38031 f _38032) (term308 A t _38032)). Qed.
Lemma lem3556648 (a : Prop) : (term115 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3556649 {A B : Type'} (_38031 : A) (f : A -> B) (_38032 : A) : (term375 A B _38031 f _38032) = ((f _38031) = (f _38032)).
Proof. exact (@lem3556648 ((f _38031) = (f _38032))). Qed.
Lemma lem3556650 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3556651 {A B : Type'} (_38031 : A) (f : A -> B) (_38032 : A) : (term376 A B _38031 f _38032) = (term57 A B _38031 f _38032).
Proof. exact (MK_COMB (@lem3556650) (@lem3556649 A B _38031 f _38032)). Qed.
Lemma lem3556653 (a : Prop) : (term115 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3556654 {A : Type'} (t : A -> Prop) (_38032 : A) : (term377 A t _38032) = (t _38032).
Proof. exact (@lem3556653 (t _38032)). Qed.
Lemma lem3556655 {A B : Type'} (_38031 : A) (f : A -> B) (t : A -> Prop) (_38032 : A) : (term374 A B _38031 f t _38032) = (term59 A B _38031 f t _38032).
Proof. exact (MK_COMB (@lem3556651 A B _38031 f _38032) (@lem3556654 A t _38032)). Qed.
Lemma lem3556656 {A B : Type'} (_38031 : A) (f : A -> B) (t : A -> Prop) (_38032 : A) : (term373 A B _38031 f t _38032) = (term59 A B _38031 f t _38032).
Proof. exact (TRANS (@lem3556646 A B _38031 f t _38032) (@lem3556655 A B _38031 f t _38032)). Qed.
Lemma lem3556657 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3556658 {A B : Type'} (_38031 : A) (f : A -> B) (t : A -> Prop) (_38032 : A) : (term378 A B _38031 f t _38032) = (term379 A B _38031 f t _38032).
Proof. exact (MK_COMB (@lem3556657) (@lem3556656 A B _38031 f t _38032)). Qed.
Lemma lem3556659 {A : Type'} (t : A -> Prop) (_38031 : A) : (t _38031) = (t _38031).
Proof. exact (eq_refl (t _38031)). Qed.
Lemma lem3556660 {A B : Type'} (f : A -> B) (_38032 : A) (t : A -> Prop) (_38031 : A) : (term372 A B f _38032 t _38031) = (term380 A B f _38032 t _38031).
Proof. exact (MK_COMB (@lem3556658 A B _38031 f t _38032) (@lem3556659 A t _38031)). Qed.
Lemma lem3556661 {A B : Type'} (f : A -> B) (_38032 : A) (t : A -> Prop) (_38031 : A) : (term371 A B _38031 f t _38032) = (term380 A B f _38032 t _38031).
Proof. exact (TRANS (@lem3556643 A B f _38032 t _38031) (@lem3556660 A B f _38032 t _38031)). Qed.
Lemma lem3556663 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term240 A B s x' x f t x'') : term59 A B x' f t x''.
Proof. exact (conj (@lem3556533 A B s x' x f t x'' h1) (@lem3556540 A B s x' x f t x'' h1)). Qed.
Lemma lem3556665 {A B : Type'} (_38032 : A) (_38031 : A) (f : A -> B) (t : A -> Prop) (h1 : term134 A B f t) : term380 A B f _38032 t _38031.
Proof. exact (EQ_MP (@lem3556661 A B f _38032 t _38031) (@lem3556640 A B _38031 _38032 f t h1)). Qed.
Lemma lem3556666 {A B : Type'} (_38032 : A) (_38031 : A) (f : A -> B) (t : A -> Prop) (h1 : term134 A B f t) : term380 A B f _38032 t _38031.
Proof. exact (@lem3556665 A B _38032 _38031 f t h1). Qed.
Lemma lem3556667 {A B : Type'} (x'' : A) (x' : A) (f : A -> B) (t : A -> Prop) (h1 : term134 A B f t) : term380 A B f x'' t x'.
Proof. exact (@lem3556666 A B x'' x' f t h1). Qed.
Lemma lem3556670 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term134 A B f t) (h2 : term240 A B s x' x f t x'') : t x'.
Proof. exact (@lem3556667 A B x'' x' f t h1 (@lem3556663 A B s x' x f t x'' h2)). Qed.
Lemma lem3556671 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term134 A B f t) (h2 : term240 A B s x' x f t x'') : term328 A t x'.
Proof. exact (fun h0 : term308 A t x' => @lem3556670 A B s x' x f t x'' h1 h2). Qed.
Lemma lem3556673 (p : Prop) : (term327 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3556674 {A : Type'} (t : A -> Prop) (x' : A) : (term328 A t x') = (t x').
Proof. exact (@lem3556673 (t x')). Qed.
Lemma lem3556675 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term134 A B f t) (h2 : term240 A B s x' x f t x'') : t x'.
Proof. exact (EQ_MP (@lem3556674 A t x') (@lem3556671 A B s x' x f t x'' h1 h2)). Qed.
Lemma lem3556677 (a : Prop) (b : Prop) : (term329 a b) = (term330 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3556678 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_38030 : A) : (term138 A s t _38030) = (term137 A s t _38030).
Proof. exact (@lem3556677 (s _38030) (t _38030)). Qed.
Lemma lem3556679 {A B : Type'} (x' : A) (f : A -> B) (_38030 : A) : (term381 A B x' f _38030) = (term381 A B x' f _38030).
Proof. exact (eq_refl (term381 A B x' f _38030)). Qed.
Lemma lem3556680 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_38030 : A) : (term317 A B x' f s t _38030) = (term382 A B x' f s t _38030).
Proof. exact (MK_COMB (@lem3556679 A B x' f _38030) (@lem3556678 A s t _38030)). Qed.
Lemma lem3556682 (a : Prop) (b : Prop) : (term329 a b) = (term330 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3556683 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_38030 : A) : (term382 A B x' f s t _38030) = (term383 A B x' f s t _38030).
Proof. exact (@lem3556682 ((f x') = (f _38030)) (term79 A s t _38030)). Qed.
Lemma lem3556684 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_38030 : A) : (term317 A B x' f s t _38030) = (term383 A B x' f s t _38030).
Proof. exact (TRANS (@lem3556680 A B x' f s t _38030) (@lem3556683 A B x' f s t _38030)). Qed.
Lemma lem3556686 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3556687 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_38030 : A) : (term383 A B x' f s t _38030) = (term384 A B x' f s t _38030).
Proof. exact (@lem3556686 (term385 A B x' f s t _38030)). Qed.
Lemma lem3556688 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_38030 : A) : (term317 A B x' f s t _38030) = (term384 A B x' f s t _38030).
Proof. exact (TRANS (@lem3556684 A B x' f s t _38030) (@lem3556687 A B x' f s t _38030)). Qed.
Lemma lem3556690 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term134 A B f t) (h2 : term240 A B s x' x f t x'') : term79 A s t x'.
Proof. exact (conj (@lem3556526 A B s x' x f t x'' h2) (@lem3556675 A B s x' x f t x'' h1 h2)). Qed.
Lemma lem3556691 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term134 A B f t) (h2 : term240 A B s x' x f t x'') : term386 A B f s t x'.
Proof. exact (conj (@lem3556519 A B f x') (@lem3556690 A B s x' x f t x'' h1 h2)). Qed.
Lemma lem3556693 {A B : Type'} (_38030 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term240 A B s x' x f t x'') : term384 A B x' f s t _38030.
Proof. exact (EQ_MP (@lem3556688 A B x' f s t _38030) (@lem3555766 A B _38030 s x' x f t x'' h1)). Qed.
Lemma lem3556694 {A B : Type'} (_38030 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term240 A B s x' x f t x'') : term384 A B x' f s t _38030.
Proof. exact (@lem3556693 A B _38030 s x' x f t x'' h1). Qed.
Lemma lem3556695 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term240 A B s x' x f t x'') : term387 A B f s t x'.
Proof. exact (@lem3556694 A B x' s x' x f t x'' h1). Qed.
Lemma lem3556698 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term134 A B f t) (h2 : term240 A B s x' x f t x'') : False.
Proof. exact (@lem3556695 A B s x' x f t x'' h2 (@lem3556691 A B s x' x f t x'' h1 h2)). Qed.
Lemma lem3556699 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term134 A B f t) (h2 : term240 A B s x' x f t x'') : term334.
Proof. exact (fun h0 : ~ False => @lem3556698 A B s x' x f t x'' h1 h2). Qed.
Lemma lem3556701 (p : Prop) : (term327 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3556702 : term334 = False.
Proof. exact (@lem3556701 False). Qed.
Lemma lem3556704 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term134 A B f t) (h2 : term240 A B s x' x f t x'') : False.
Proof. exact (EQ_MP (@lem3556702) (@lem3556699 A B s x' x f t x'' h1 h2)). Qed.
Lemma lem3556705 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term134 A B f s) (h2 : term240 A B s x' x f t x'') : False.
Proof. exact (EQ_MP (@lem3556473) (@lem3556470 A B s x' x f t x'' h1 h2)). Qed.
Lemma lem3556706 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term158 A B x f t) (h2 : term187 A B x' s x f t) : False.
Proof. exact (EQ_MP (@lem3556112) (@lem3556109 A B x' s x f t h1 h2)). Qed.
Lemma lem3556707 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term158 A B x f t) (h2 : term187 A B x' s x f t) : False.
Proof. exact (EQ_MP (@lem3556039) (@lem3556036 A B x' s x f t h1 h2)). Qed.
Lemma lem3556708 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term158 A B x f s) (h2 : term187 A B x' s x f t) : False.
Proof. exact (EQ_MP (@lem3555966) (@lem3555963 A B x' s x f t h1 h2)). Qed.
Lemma lem3556709 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term158 A B x f s) (h2 : term187 A B x' s x f t) : False.
Proof. exact (EQ_MP (@lem3555893) (@lem3555890 A B x' s x f t h1 h2)). Qed.
Lemma lem3556710 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term158 A B x f t) (h2 : term187 A B x' s x f t) : (term158 A B x f t) = False.
Proof. exact (prop_ext (fun h3 : term158 A B x f t => @lem3556706 A B x' s x f t h1 h2) (fun h3 : False => @lem3554957 A B x f t h1)). Qed.
Lemma lem3556711 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term158 A B x f t) (h2 : term187 A B x' s x f t) : False.
Proof. exact (EQ_MP (@lem3556710 A B x' s x f t h1 h2) (@lem3554957 A B x f t h1)). Qed.
Lemma lem3556712 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term158 A B x f t) (h2 : term187 A B x' s x f t) : (term158 A B x f t) = False.
Proof. exact (prop_ext (fun h3 : term158 A B x f t => @lem3556707 A B x' s x f t h1 h2) (fun h3 : False => @lem3554884 A B x f t h1)). Qed.
Lemma lem3556713 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term158 A B x f t) (h2 : term187 A B x' s x f t) : False.
Proof. exact (EQ_MP (@lem3556712 A B x' s x f t h1 h2) (@lem3554884 A B x f t h1)). Qed.
Lemma lem3556714 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term158 A B x f s) (h2 : term187 A B x' s x f t) : (term158 A B x f s) = False.
Proof. exact (prop_ext (fun h3 : term158 A B x f s => @lem3556708 A B x' s x f t h1 h2) (fun h3 : False => @lem3554811 A B x f s h1)). Qed.
Lemma lem3556715 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term158 A B x f s) (h2 : term187 A B x' s x f t) : False.
Proof. exact (EQ_MP (@lem3556714 A B x' s x f t h1 h2) (@lem3554811 A B x f s h1)). Qed.
Lemma lem3556716 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term158 A B x f s) (h2 : term187 A B x' s x f t) : (term158 A B x f s) = False.
Proof. exact (prop_ext (fun h3 : term158 A B x f s => @lem3556709 A B x' s x f t h1 h2) (fun h3 : False => @lem3554738 A B x f s h1)). Qed.
Lemma lem3556717 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term158 A B x f s) (h2 : term187 A B x' s x f t) : False.
Proof. exact (EQ_MP (@lem3556716 A B x' s x f t h1 h2) (@lem3554738 A B x f s h1)). Qed.
Lemma lem3556718 {A B : Type'} (x' : A) (x : B) (x'' : A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term240 A B s x' x f t x'') (h2 : term71 A B s f t) : False.
Proof. exact (or_elim (@lem3554560 A B s f t h2) (fun h0 : term134 A B f s => @lem3556705 A B s x' x f t x'' h0 h1) (fun h0 : term134 A B f t => @lem3556704 A B s x' x f t x'' h0 h1)). Qed.
Lemma lem3556719 {A B : Type'} (x' : A) (x : B) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term158 A B x f t) (h2 : term187 A B x' s x f t) (h3 : term71 A B s f t) : False.
Proof. exact (or_elim (@lem3554560 A B s f t h3) (fun h0 : term134 A B f s => @lem3556713 A B x' s x f t h1 h2) (fun h0 : term134 A B f t => @lem3556711 A B x' s x f t h1 h2)). Qed.
Lemma lem3556720 {A B : Type'} (x' : A) (x : B) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term158 A B x f s) (h2 : term187 A B x' s x f t) (h3 : term71 A B s f t) : False.
Proof. exact (or_elim (@lem3554560 A B s f t h3) (fun h0 : term134 A B f s => @lem3556717 A B x' s x f t h1 h2) (fun h0 : term134 A B f t => @lem3556715 A B x' s x f t h1 h2)). Qed.
Lemma lem3556721 {A B : Type'} (x' : A) (x : B) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term187 A B x' s x f t) (h2 : term71 A B s f t) : False.
Proof. exact (or_elim (@lem3554692 A B x' s x f t h1) (fun h0 : term158 A B x f s => @lem3556720 A B x' x s f t h0 h1 h2) (fun h0 : term158 A B x f t => @lem3556719 A B x' x s f t h0 h1 h2)). Qed.
Lemma lem3556722 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term71 A B s f t) (h2 : term277 A B s x' x f t x'') : False.
Proof. exact (or_elim (@lem3554689 A B s x' x f t x'' h2) (fun h0 : term187 A B x' s x f t => @lem3556721 A B x' x s f t h0 h1) (fun h0 : term240 A B s x' x f t x'' => @lem3556718 A B x' x x'' s f t h0 h1)). Qed.
Lemma lem3556723 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term71 A B s f t) (h2 : term277 A B s x' x f t x'') : (term277 A B s x' x f t x'') = False.
Proof. exact (prop_ext (fun h3 : term277 A B s x' x f t x'' => @lem3556722 A B s x' x f t x'' h1 h2) (fun h3 : False => @lem3554689 A B s x' x f t x'' h2)). Qed.
Lemma lem3556724 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term71 A B s f t) (h2 : term277 A B s x' x f t x'') : False.
Proof. exact (EQ_MP (@lem3556723 A B s x' x f t x'' h1 h2) (@lem3554689 A B s x' x f t x'' h2)). Qed.
Lemma lem3556725 {A B : Type'} (x' : A) (x : B) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term280 A B s x' x f t) (h2 : term71 A B s f t) : False.
Proof. exact (ex_elim (@lem3554493 A B s x' x f t h1) (fun x'' : A => fun h0 : term279 A B s x' x f t x'' => @lem3556724 A B s x' x f t x'' h2 h0)). Qed.
Lemma lem3556726 {A B : Type'} (x : B) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term117 A B s x f t) (h2 : term71 A B s f t) : False.
Proof. exact (ex_elim (@lem3554492 A B s x f t h1) (fun x' : A => fun h0 : term281 A B s x f t x' => @lem3556725 A B x' x s f t h0 h2)). Qed.
Lemma lem3556727 {A B : Type'} (x : B) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term117 A B s x f t) (h2 : term71 A B s f t) : (term117 A B s x f t) = False.
Proof. exact (prop_ext (fun h3 : term117 A B s x f t => @lem3556726 A B x s f t h1 h2) (fun h3 : False => @lem3553734 A B s x f t h1)). Qed.
Lemma lem3556728 {A B : Type'} (x : B) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term117 A B s x f t) (h2 : term71 A B s f t) : False.
Proof. exact (EQ_MP (@lem3556727 A B x s f t h1 h2) (@lem3553734 A B s x f t h1)). Qed.
Lemma lem3556729 {A B : Type'} (x : B) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term71 A B s f t) : term116 A B s x f t.
Proof. exact (fun h0 : term117 A B s x f t => @lem3556728 A B x s f t h0 h1). Qed.
Lemma lem3556730 {A B : Type'} (x : B) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term71 A B s f t) : (term85 A B x f s t) = (term97 A B s x f t).
Proof. exact (EQ_MP (@lem3553733 A B s x f t) (@lem3556729 A B x s f t h1)). Qed.
Lemma lem3556735 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term71 A B s f t) : term100 A B s f t.
Proof. exact (fun x : B => @lem3556730 A B x s f t h1). Qed.
Lemma lem3556736 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : term101 A B s f t.
Proof. exact (fun h0 : term71 A B s f t => @lem3556735 A B s f t h0). Qed.
Lemma lem3556741 {A B : Type'} (s : A -> Prop) (f : A -> B) : term103 A B s f.
Proof. exact (fun t : A -> Prop => @lem3556736 A B s f t). Qed.
Lemma lem3556746 {A B : Type'} (f : A -> B) : term105 A B f.
Proof. exact (fun s : A -> Prop => @lem3556741 A B s f). Qed.
Lemma lem3556751 {A B : Type'} : term107 A B.
Proof. exact (fun f : A -> B => @lem3556746 A B f). Qed.
Lemma lem3556752 {A B : Type'} : term109 A B.
Proof. exact (EQ_MP (@lem3553728 A B) (@lem3556751 A B)). Qed.
Lemma lem3556754 {A B : Type'} : term109 A B.
Proof. exact (@lem3553321 A B (@lem3556752 A B)). Qed.
Lemma lem3556755 {A B : Type'} (h1 : term110 A B) : False.
Proof. exact (@lem3556754 A B (@lem3553305 A B h1)). Qed.
Lemma lem3556756 {A B : Type'} (h1 : term110 A B) : (term110 A B) = False.
Proof. exact (prop_ext (fun h2 : term110 A B => @lem3556755 A B h1) (fun h2 : False => @lem3553305 A B h1)). Qed.
Lemma lem3556757 {A B : Type'} (h1 : term110 A B) : False.
Proof. exact (EQ_MP (@lem3556756 A B h1) (@lem3553305 A B h1)). Qed.
Lemma lem3556758 {A B : Type'} : term109 A B.
Proof. exact (fun h0 : term110 A B => @lem3556757 A B h0). Qed.
Lemma lem3556759 {A B : Type'} : term107 A B.
Proof. exact (EQ_MP (@lem3553304 A B) (@lem3556758 A B)). Qed.
Lemma lem3556760 {A B : Type'} : term34 A B.
Proof. exact (EQ_MP (@lem3553300 A B) (@lem3556759 A B)). Qed.
Lemma lem3556761 {A B : Type'} : term33 A B.
Proof. exact (EQ_MP (@lem3552977 A B) (@lem3556760 A B)). Qed.
