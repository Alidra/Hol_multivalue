Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_GROUP_RELATION_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import FORALL_IN_IMAGE_spec.
Require Import SUBSET_spec.
Require Import SUM_EQ_spec.
Require Import SUM_GROUP_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm129_spec.
Require Import thm137_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17646_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1842_spec.
Require Import thm18897_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18940_spec.
Require Import thm18941_spec.
Require Import thm18946_spec.
Require Import thm18947_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm19018_spec.
Require Import thm19019_spec.
Require Import thm19490_spec.
Require Import thm19732_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211640_spec.
Require Import thm3211641_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm51_spec.
Require Import thm7_spec.
Lemma lem7160835 {_132349 : Type'} (h1 : term0 _132349) : term0 _132349.
Proof. exact (h1). Qed.
Lemma lem7160836 {_132349 : Type'} (f : _132349 -> real) (h1 : term0 _132349) : term1 _132349 f.
Proof. exact (@lem7160835 _132349 h1 f). Qed.
Lemma lem7160837 {_132349 : Type'} (f : _132349 -> real) : (term1 _132349 f) = (term2 _132349 f).
Proof. exact (eq_refl (term1 _132349 f)). Qed.
Lemma lem7160838 {_132349 : Type'} (f : _132349 -> real) (h1 : term0 _132349) : term2 _132349 f.
Proof. exact (EQ_MP (@lem7160837 _132349 f) (@lem7160836 _132349 f h1)). Qed.
Lemma lem7160839 {_132349 : Type'} (f : _132349 -> real) (g : _132349 -> real) (h1 : term0 _132349) : term3 _132349 f g.
Proof. exact (@lem7160838 _132349 f h1 g). Qed.
Lemma lem7160840 {_132349 : Type'} (f : _132349 -> real) (g : _132349 -> real) : (term3 _132349 f g) = (term4 _132349 f g).
Proof. exact (eq_refl (term3 _132349 f g)). Qed.
Lemma lem7160841 {_132349 : Type'} (f : _132349 -> real) (g : _132349 -> real) (h1 : term0 _132349) : term4 _132349 f g.
Proof. exact (EQ_MP (@lem7160840 _132349 f g) (@lem7160839 _132349 f g h1)). Qed.
Lemma lem7160842 {_132349 : Type'} (f : _132349 -> real) (g : _132349 -> real) (s : _132349 -> Prop) (h1 : term0 _132349) : term5 _132349 f g s.
Proof. exact (@lem7160841 _132349 f g h1 s). Qed.
Lemma lem7160843 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : (term5 _132349 f g s) = (term6 _132349 f s g).
Proof. exact (eq_refl (term5 _132349 f g s)). Qed.
Lemma lem7160844 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) (h1 : term0 _132349) : term6 _132349 f s g.
Proof. exact (EQ_MP (@lem7160843 _132349 f s g) (@lem7160842 _132349 f g s h1)). Qed.
Lemma lem7160845 {_132349 : Type'} (s : _132349 -> Prop) (f : _132349 -> real) (g : _132349 -> real) (h1 : term7 _132349 s f g) : term7 _132349 s f g.
Proof. exact (h1). Qed.
Lemma lem7160846 {_132349 : Type'} (s : _132349 -> Prop) (f : _132349 -> real) (g : _132349 -> real) (h1 : term7 _132349 s f g) (h2 : term0 _132349) : (@sum _132349 s f) = (@sum _132349 s g).
Proof. exact (@lem7160844 _132349 f s g h2 (@lem7160845 _132349 s f g h1)). Qed.
Lemma lem7160847 {_132349 : Type'} (s : _132349 -> Prop) (f : _132349 -> real) (g : _132349 -> real) (h1 : term7 _132349 s f g) : term8 _132349 f s g.
Proof. exact (fun h0 : term0 _132349 => @lem7160846 _132349 s f g h1 h0). Qed.
Lemma lem7160848 {_132349 : Type'} (h1 : term0 _132349) : term0 _132349.
Proof. exact (h1). Qed.
Lemma lem7160849 {_132349 : Type'} (s : _132349 -> Prop) (f : _132349 -> real) (g : _132349 -> real) (h1 : term7 _132349 s f g) (h2 : term0 _132349) : (@sum _132349 s f) = (@sum _132349 s g).
Proof. exact (@lem7160847 _132349 s f g h1 (@lem7160848 _132349 h2)). Qed.
Lemma lem7160850 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) (h1 : term0 _132349) : term6 _132349 f s g.
Proof. exact (fun h0 : term7 _132349 s f g => @lem7160849 _132349 s f g h0 h1). Qed.
Lemma lem7160851 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (h1 : term0 _132349) : term9 _132349 f s.
Proof. exact (fun g : _132349 -> real => @lem7160850 _132349 f s g h1). Qed.
Lemma lem7160852 {_132349 : Type'} (f : _132349 -> real) (h1 : term0 _132349) : term10 _132349 f.
Proof. exact (fun s : _132349 -> Prop => @lem7160851 _132349 f s h1). Qed.
Lemma lem7160853 {_132349 : Type'} (h1 : term0 _132349) : term11 _132349.
Proof. exact (fun f : _132349 -> real => @lem7160852 _132349 f h1). Qed.
Lemma lem7160854 {_132349 : Type'} : term12 _132349.
Proof. exact (fun h0 : term0 _132349 => @lem7160853 _132349 h0). Qed.
Lemma lem7160855 {_132349 : Type'} : term11 _132349.
Proof. exact (@lem7160854 _132349 (@lem7081239 _132349)). Qed.
Lemma lem7160856 {_132349 : Type'} (f : _132349 -> real) : term13 _132349 f.
Proof. exact (@lem7160855 _132349 f). Qed.
Lemma lem7160857 {_132349 : Type'} (f : _132349 -> real) : (term13 _132349 f) = (term10 _132349 f).
Proof. exact (eq_refl (term13 _132349 f)). Qed.
Lemma lem7160858 {_132349 : Type'} (f : _132349 -> real) : term10 _132349 f.
Proof. exact (EQ_MP (@lem7160857 _132349 f) (@lem7160856 _132349 f)). Qed.
Lemma lem7160859 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) : term14 _132349 f s.
Proof. exact (@lem7160858 _132349 f s). Qed.
Lemma lem7160860 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) : (term14 _132349 f s) = (term9 _132349 f s).
Proof. exact (eq_refl (term14 _132349 f s)). Qed.
Lemma lem7160861 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) : term9 _132349 f s.
Proof. exact (EQ_MP (@lem7160860 _132349 f s) (@lem7160859 _132349 f s)). Qed.
Lemma lem7160862 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : term15 _132349 f s g.
Proof. exact (@lem7160861 _132349 f s g). Qed.
Lemma lem7160863 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : (term15 _132349 f s g) = (term6 _132349 f s g).
Proof. exact (eq_refl (term15 _132349 f s g)). Qed.
Lemma lem7160865 (t1 : Prop) : term16 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem7160866 (t1 : Prop) : (term16 t1) = (term17 t1).
Proof. exact (eq_refl (term16 t1)). Qed.
Lemma lem7160867 (t1 : Prop) : term17 t1.
Proof. exact (EQ_MP (@lem7160866 t1) (@lem7160865 t1)). Qed.
Lemma lem7160868 (t1 : Prop) (t2 : Prop) : term18 t1 t2.
Proof. exact (@lem7160867 t1 t2). Qed.
Lemma lem7160869 (t1 : Prop) (t2 : Prop) : (term18 t1 t2) = (term19 t1 t2).
Proof. exact (eq_refl (term18 t1 t2)). Qed.
Lemma lem7160870 (t1 : Prop) (t2 : Prop) : term19 t1 t2.
Proof. exact (EQ_MP (@lem7160869 t1 t2) (@lem7160868 t1 t2)). Qed.
Lemma lem7160871 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term20 t1 t2 t3.
Proof. exact (@lem7160870 t1 t2 t3). Qed.
Lemma lem7160872 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term20 t1 t2 t3) = ((term21 t1 t2 t3) = (term22 t1 t2 t3)).
Proof. exact (eq_refl (term20 t1 t2 t3)). Qed.
Lemma lem7160873 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term21 t1 t2 t3) = (term22 t1 t2 t3).
Proof. exact (EQ_MP (@lem7160872 t1 t2 t3) (@lem7160871 t1 t2 t3)). Qed.
Lemma lem7160874 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term22 t1 t2 t3) = (term21 t1 t2 t3).
Proof. exact (SYM (@lem7160873 t1 t2 t3)). Qed.
Lemma lem7160875 {A B : Type'} : term23 A B.
Proof. exact (@lem7160834 A B). Qed.
Lemma lem7160876 {A B : Type'} (t : B -> Prop) (R : type1413 A B) : term24 A B t R.
Proof. exact (@lem7160875 A B (term25 A B t R)). Qed.
Lemma lem7160877 {A B : Type'} (t : B -> Prop) (R : type1413 A B) : (term24 A B t R) = (term26 A B t R).
Proof. exact (eq_refl (term24 A B t R)). Qed.
Lemma lem7160878 {A B : Type'} (t : B -> Prop) (R : type1413 A B) : term26 A B t R.
Proof. exact (EQ_MP (@lem7160877 A B t R) (@lem7160876 A B t R)). Qed.
Lemma lem7160879 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (g : A -> real) : term27 A B t R g.
Proof. exact (@lem7160878 A B t R g). Qed.
Lemma lem7160880 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (g : A -> real) : (term27 A B t R g) = (term28 A B t R g).
Proof. exact (eq_refl (term27 A B t R g)). Qed.
Lemma lem7160881 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (g : A -> real) : term28 A B t R g.
Proof. exact (EQ_MP (@lem7160880 A B t R g) (@lem7160879 A B t R g)). Qed.
Lemma lem7160882 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (g : A -> real) (s : A -> Prop) : term29 A B t R g s.
Proof. exact (@lem7160881 A B t R g s). Qed.
Lemma lem7160883 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (g : A -> real) : (term29 A B t R g s) = (term30 A B t R s g).
Proof. exact (eq_refl (term29 A B t R g s)). Qed.
Lemma lem7160884 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (g : A -> real) : term30 A B t R s g.
Proof. exact (EQ_MP (@lem7160883 A B t R s g) (@lem7160882 A B t R g s)). Qed.
Lemma lem7160885 {A B : Type'} (R : type1413 A B) (s : A -> Prop) (g : A -> real) (t : B -> Prop) : term31 A B R s g t.
Proof. exact (@lem7160884 A B t R s g t). Qed.
Lemma lem7160886 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (g : A -> real) : (term31 A B R s g t) = (term32 A B t R s g).
Proof. exact (eq_refl (term31 A B R s g t)). Qed.
Lemma lem7160887 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (g : A -> real) : term32 A B t R s g.
Proof. exact (EQ_MP (@lem7160886 A B t R s g) (@lem7160885 A B R s g t)). Qed.
Lemma lem7160888 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (h1 : term33 A B s t R) : term33 A B s t R.
Proof. exact (h1). Qed.
Lemma lem7160889 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (h1 : term34 A B s t R) : term34 A B s t R.
Proof. exact (h1). Qed.
Lemma lem7160890 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem7160891 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : term35 _87967 _87968 P f.
Proof. exact (@lem3386920 _87967 _87968 P f). Qed.
Lemma lem7160892 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : (term35 _87967 _87968 P f) = (term36 _87967 _87968 P f).
Proof. exact (eq_refl (term35 _87967 _87968 P f)). Qed.
Lemma lem7160893 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : term36 _87967 _87968 P f.
Proof. exact (EQ_MP (@lem7160892 _87967 _87968 P f) (@lem7160891 _87967 _87968 P f)). Qed.
Lemma lem7160894 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) (s : _87968 -> Prop) : term37 _87967 _87968 P f s.
Proof. exact (@lem7160893 _87967 _87968 P f s). Qed.
Lemma lem7160895 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term37 _87967 _87968 P f s) = ((term38 _87967 _87968 f s P) = (term39 _87967 _87968 s P f)).
Proof. exact (eq_refl (term37 _87967 _87968 P f s)). Qed.
Lemma lem7160897 {A : Type'} (s : A -> Prop) : term40 A s.
Proof. exact (@lem3194148 A s). Qed.
Lemma lem7160898 {A : Type'} (s : A -> Prop) : (term40 A s) = (term41 A s).
Proof. exact (eq_refl (term40 A s)). Qed.
Lemma lem7160899 {A : Type'} (s : A -> Prop) : term41 A s.
Proof. exact (EQ_MP (@lem7160898 A s) (@lem7160897 A s)). Qed.
Lemma lem7160900 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term42 A s t.
Proof. exact (@lem7160899 A s t). Qed.
Lemma lem7160901 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term42 A s t) = ((@SUBSET A s t) = (term43 A s t)).
Proof. exact (eq_refl (term42 A s t)). Qed.
Lemma lem7160903 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem7160917 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem7160903 A s) (@lem7160890 A s h1)). Qed.
Lemma lem7160918 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7160919 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (term44 A s) = (and True).
Proof. exact (MK_COMB (@lem7160918) (@lem7160917 A s h1)). Qed.
Lemma lem7160921 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term43 A s t).
Proof. exact (EQ_MP (@lem7160901 A s t) (@lem7160900 A s t)). Qed.
Lemma lem7160922 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (@SUBSET B s t) = (term43 B s t).
Proof. exact (@lem7160921 B s t). Qed.
Lemma lem7160923 {A B : Type'} (R : type1413 A B) (s : A -> Prop) (t : B -> Prop) : (term45 A B R s t) = (term46 A B R s t).
Proof. exact (@lem7160922 B (term47 A B t R s) t). Qed.
Lemma lem7160925 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term38 _87967 _87968 f s P) = (term39 _87967 _87968 s P f).
Proof. exact (EQ_MP (@lem7160895 _87967 _87968 s P f) (@lem7160894 _87967 _87968 P f s)). Qed.
Lemma lem7160926 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term48 A B f s P) = (term49 A B s P f).
Proof. exact (@lem7160925 B A s P f). Qed.
Lemma lem7160927 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term50 A B R s t) = (term51 A B s t R).
Proof. exact (@lem7160926 A B s (term52 B t) (term25 A B t R)). Qed.
Lemma lem7160928 {B : Type'} (x : B) (t : B -> Prop) : (term53 B t x) = (@IN B x t).
Proof. exact (eq_refl (term53 B t x)). Qed.
Lemma lem7160929 {A B : Type'} (x : B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term54 A B x t R s) = (term54 A B x t R s).
Proof. exact (eq_refl (term54 A B x t R s)). Qed.
Lemma lem7160930 {A B : Type'} (R : type1413 A B) (s : A -> Prop) (x : B) (t : B -> Prop) : (term55 A B R s t x) = (term56 A B R s x t).
Proof. exact (MK_COMB (@lem7160929 A B x t R s) (@lem7160928 B x t)). Qed.
Lemma lem7160931 {A B : Type'} (R : type1413 A B) (s : A -> Prop) (t : B -> Prop) : (term57 A B R s t) = (term58 A B R s t).
Proof. exact (fun_ext (fun x : B => @lem7160930 A B R s x t)). Qed.
Lemma lem7160932 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7160933 {A B : Type'} (R : type1413 A B) (s : A -> Prop) (t : B -> Prop) : (term50 A B R s t) = (term46 A B R s t).
Proof. exact (MK_COMB (@lem7160932 B) (@lem7160931 A B R s t)). Qed.
Lemma lem7160934 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7160935 {A B : Type'} (R : type1413 A B) (s : A -> Prop) (t : B -> Prop) : (term59 A B R s t) = (term60 A B R s t).
Proof. exact (MK_COMB (@lem7160934) (@lem7160933 A B R s t)). Qed.
Lemma lem7160936 {A B : Type'} (R : type1413 A B) (x : A) (t : B -> Prop) : (term61 A B t R x) = (term62 A B R x t).
Proof. exact (eq_refl (term61 A B t R x)). Qed.
Lemma lem7160937 {A : Type'} (x : A) (s : A -> Prop) : (term63 A x s) = (term63 A x s).
Proof. exact (eq_refl (term63 A x s)). Qed.
Lemma lem7160938 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x : A) (t : B -> Prop) : (term64 A B s t R x) = (term65 A B s R x t).
Proof. exact (MK_COMB (@lem7160937 A x s) (@lem7160936 A B R x t)). Qed.
Lemma lem7160939 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : (term66 A B s t R) = (term67 A B s R t).
Proof. exact (fun_ext (fun x : A => @lem7160938 A B s R x t)). Qed.
Lemma lem7160940 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7160941 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : (term51 A B s t R) = (term68 A B s R t).
Proof. exact (MK_COMB (@lem7160940 A) (@lem7160939 A B s R t)). Qed.
Lemma lem7160942 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : ((term50 A B R s t) = (term51 A B s t R)) = ((term46 A B R s t) = (term68 A B s R t)).
Proof. exact (MK_COMB (@lem7160935 A B R s t) (@lem7160941 A B s R t)). Qed.
Lemma lem7160943 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : (term46 A B R s t) = (term68 A B s R t).
Proof. exact (EQ_MP (@lem7160942 A B s R t) (@lem7160927 A B s t R)). Qed.
Lemma lem7160948 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : (term45 A B R s t) = (term68 A B s R t).
Proof. exact (TRANS (@lem7160923 A B R s t) (@lem7160943 A B s R t)). Qed.
Lemma lem7160952 {A B : Type'} (f : A -> B) (y : A) : (term69 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7160953 {A B : Type'} (f : A -> B) (y : A) : (term69 A B f y) = (f y).
Proof. exact (@lem7160952 A B f y). Qed.
Lemma lem7160954 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term70 A B t R x) = (term71 A B t R x).
Proof. exact (@lem7160953 A B (term25 A B t R) x). Qed.
Lemma lem7160955 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term71 A B t R x) = (term72 A B t R x).
Proof. exact (eq_refl (term71 A B t R x)). Qed.
Lemma lem7160956 {A B : Type'} (t : B -> Prop) (R : type1413 A B) : (term73 A B t R) = (term25 A B t R).
Proof. exact (fun_ext (fun x : A => @lem7160955 A B t R x)). Qed.
Lemma lem7160957 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7160958 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term70 A B t R x) = (term71 A B t R x).
Proof. exact (MK_COMB (@lem7160956 A B t R) (@lem7160957 A x)). Qed.
Lemma lem7160959 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem7160960 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term74 A B t R x) = (term75 A B t R x).
Proof. exact (MK_COMB (@lem7160959 B) (@lem7160958 A B t R x)). Qed.
Lemma lem7160961 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term71 A B t R x) = (term72 A B t R x).
Proof. exact (eq_refl (term71 A B t R x)). Qed.
Lemma lem7160962 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : ((term70 A B t R x) = (term71 A B t R x)) = ((term71 A B t R x) = (term72 A B t R x)).
Proof. exact (MK_COMB (@lem7160960 A B t R x) (@lem7160961 A B t R x)). Qed.
Lemma lem7160963 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term71 A B t R x) = (term72 A B t R x).
Proof. exact (EQ_MP (@lem7160962 A B t R x) (@lem7160954 A B t R x)). Qed.
Lemma lem7160966 {B : Type'} : (@IN B) = (@IN B).
Proof. exact (eq_refl (@IN B)). Qed.
Lemma lem7160967 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term76 A B t R x) = (term77 A B t R x).
Proof. exact (MK_COMB (@lem7160966 B) (@lem7160963 A B t R x)). Qed.
Lemma lem7160968 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem7160969 {A B : Type'} (R : type1413 A B) (x : A) (t : B -> Prop) : (term62 A B R x t) = (term78 A B R x t).
Proof. exact (MK_COMB (@lem7160967 A B t R x) (@lem7160968 B t)). Qed.
Lemma lem7160970 {A : Type'} (x : A) (s : A -> Prop) : (term63 A x s) = (term63 A x s).
Proof. exact (eq_refl (term63 A x s)). Qed.
Lemma lem7160971 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x : A) (t : B -> Prop) : (term65 A B s R x t) = (term79 A B s R x t).
Proof. exact (MK_COMB (@lem7160970 A x s) (@lem7160969 A B R x t)). Qed.
Lemma lem7160974 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : (term67 A B s R t) = (term80 A B s R t).
Proof. exact (fun_ext (fun x : A => @lem7160971 A B s R x t)). Qed.
Lemma lem7160975 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7160976 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : (term68 A B s R t) = (term81 A B s R t).
Proof. exact (MK_COMB (@lem7160975 A) (@lem7160974 A B s R t)). Qed.
Lemma lem7160981 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : (term45 A B R s t) = (term81 A B s R t).
Proof. exact (TRANS (@lem7160948 A B s R t) (@lem7160976 A B s R t)). Qed.
Lemma lem7160982 {A B : Type'} (R : type1413 A B) (t : B -> Prop) (s : A -> Prop) (h1 : @FINITE A s) : (term82 A B R s t) = (term83 A B s R t).
Proof. exact (MK_COMB (@lem7160919 A s h1) (@lem7160981 A B s R t)). Qed.
Lemma lem7160984 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7160985 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : (term83 A B s R t) = (term81 A B s R t).
Proof. exact (@lem7160984 (term81 A B s R t)). Qed.
Lemma lem7160994 {A B : Type'} (R : type1413 A B) (t : B -> Prop) (s : A -> Prop) (h1 : @FINITE A s) : (term82 A B R s t) = (term81 A B s R t).
Proof. exact (TRANS (@lem7160982 A B R t s h1) (@lem7160985 A B s R t)). Qed.
Lemma lem7160995 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7160996 {A B : Type'} (R : type1413 A B) (t : B -> Prop) (s : A -> Prop) (h1 : @FINITE A s) : (term84 A B R s t) = (term85 A B s R t).
Proof. exact (MK_COMB (@lem7160995) (@lem7160994 A B R t s h1)). Qed.
Lemma lem7161008 {A B : Type'} (f : A -> B) (y : A) : (term69 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7161009 {A B : Type'} (f : A -> B) (y : A) : (term69 A B f y) = (f y).
Proof. exact (@lem7161008 A B f y). Qed.
Lemma lem7161010 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term70 A B t R x) = (term71 A B t R x).
Proof. exact (@lem7161009 A B (term25 A B t R) x). Qed.
Lemma lem7161011 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term71 A B t R x) = (term72 A B t R x).
Proof. exact (eq_refl (term71 A B t R x)). Qed.
Lemma lem7161012 {A B : Type'} (t : B -> Prop) (R : type1413 A B) : (term73 A B t R) = (term25 A B t R).
Proof. exact (fun_ext (fun x : A => @lem7161011 A B t R x)). Qed.
Lemma lem7161013 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7161014 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term70 A B t R x) = (term71 A B t R x).
Proof. exact (MK_COMB (@lem7161012 A B t R) (@lem7161013 A x)). Qed.
Lemma lem7161015 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem7161016 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term74 A B t R x) = (term75 A B t R x).
Proof. exact (MK_COMB (@lem7161015 B) (@lem7161014 A B t R x)). Qed.
Lemma lem7161017 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term71 A B t R x) = (term72 A B t R x).
Proof. exact (eq_refl (term71 A B t R x)). Qed.
Lemma lem7161018 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : ((term70 A B t R x) = (term71 A B t R x)) = ((term71 A B t R x) = (term72 A B t R x)).
Proof. exact (MK_COMB (@lem7161016 A B t R x) (@lem7161017 A B t R x)). Qed.
Lemma lem7161019 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term71 A B t R x) = (term72 A B t R x).
Proof. exact (EQ_MP (@lem7161018 A B t R x) (@lem7161010 A B t R x)). Qed.
Lemma lem7161022 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem7161023 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term75 A B t R x) = (term86 A B t R x).
Proof. exact (MK_COMB (@lem7161022 B) (@lem7161019 A B t R x)). Qed.
Lemma lem7161024 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem7161025 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : ((term71 A B t R x) = y) = ((term72 A B t R x) = y).
Proof. exact (MK_COMB (@lem7161023 A B t R x) (@lem7161024 B y)). Qed.
Lemma lem7161028 {A : Type'} (x : A) (s : A -> Prop) : (term87 A x s) = (term87 A x s).
Proof. exact (eq_refl (term87 A x s)). Qed.
Lemma lem7161029 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term88 A B s t R x y) = (term89 A B s t R x y).
Proof. exact (MK_COMB (@lem7161028 A x s) (@lem7161025 A B t R x y)). Qed.
Lemma lem7161032 {A : Type'} (GEN_PVAR_325 : A) : (@SETSPEC A GEN_PVAR_325) = (@SETSPEC A GEN_PVAR_325).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_325)). Qed.
Lemma lem7161033 {A B : Type'} (GEN_PVAR_325 : A) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term90 A B GEN_PVAR_325 s t R x y) = (term91 A B GEN_PVAR_325 s t R x y).
Proof. exact (MK_COMB (@lem7161032 A GEN_PVAR_325) (@lem7161029 A B s t R x y)). Qed.
Lemma lem7161034 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7161035 {A B : Type'} (GEN_PVAR_325 : A) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (y : B) (x : A) : (term92 A B GEN_PVAR_325 s t R y x) = (term93 A B GEN_PVAR_325 s t R y x).
Proof. exact (MK_COMB (@lem7161033 A B GEN_PVAR_325 s t R x y) (@lem7161034 A x)). Qed.
Lemma lem7161036 {A B : Type'} (GEN_PVAR_325 : A) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (y : B) : (term94 A B GEN_PVAR_325 s t R y) = (term95 A B GEN_PVAR_325 s t R y).
Proof. exact (fun_ext (fun x : A => @lem7161035 A B GEN_PVAR_325 s t R y x)). Qed.
Lemma lem7161037 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7161038 {A B : Type'} (GEN_PVAR_325 : A) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (y : B) : (term96 A B GEN_PVAR_325 s t R y) = (term97 A B GEN_PVAR_325 s t R y).
Proof. exact (MK_COMB (@lem7161037 A) (@lem7161036 A B GEN_PVAR_325 s t R y)). Qed.
Lemma lem7161043 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (y : B) : (term98 A B s t R y) = (term99 A B s t R y).
Proof. exact (fun_ext (fun GEN_PVAR_325 : A => @lem7161038 A B GEN_PVAR_325 s t R y)). Qed.
Lemma lem7161044 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem7161045 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (y : B) : (term100 A B s t R y) = (term101 A B s t R y).
Proof. exact (MK_COMB (@lem7161044 A) (@lem7161043 A B s t R y)). Qed.
Lemma lem7161046 {A : Type'} : (@sum A) = (@sum A).
Proof. exact (eq_refl (@sum A)). Qed.
Lemma lem7161047 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (y : B) : (term102 A B s t R y) = (term103 A B s t R y).
Proof. exact (MK_COMB (@lem7161046 A) (@lem7161045 A B s t R y)). Qed.
Lemma lem7161048 {A : Type'} (g : A -> real) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7161049 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (y : B) (g : A -> real) : (term104 A B s t R y g) = (term105 A B s t R y g).
Proof. exact (MK_COMB (@lem7161047 A B s t R y) (@lem7161048 A g)). Qed.
Lemma lem7161050 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (g : A -> real) : (term106 A B s t R g) = (term107 A B s t R g).
Proof. exact (fun_ext (fun y : B => @lem7161049 A B s t R y g)). Qed.
Lemma lem7161051 {B : Type'} (t : B -> Prop) : (@sum B t) = (@sum B t).
Proof. exact (eq_refl (@sum B t)). Qed.
Lemma lem7161052 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (g : A -> real) : (term108 A B s t R g) = (term109 A B s t R g).
Proof. exact (MK_COMB (@lem7161051 B t) (@lem7161050 A B s t R g)). Qed.
Lemma lem7161053 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7161054 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (g : A -> real) : (term110 A B s t R g) = (term111 A B s t R g).
Proof. exact (MK_COMB (@lem7161053) (@lem7161052 A B s t R g)). Qed.
Lemma lem7161055 {A : Type'} (s : A -> Prop) (g : A -> real) : (@sum A s g) = (@sum A s g).
Proof. exact (eq_refl (@sum A s g)). Qed.
Lemma lem7161056 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (g : A -> real) : ((term108 A B s t R g) = (@sum A s g)) = ((term109 A B s t R g) = (@sum A s g)).
Proof. exact (MK_COMB (@lem7161054 A B s t R g) (@lem7161055 A s g)). Qed.
Lemma lem7161059 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (g : A -> real) (s : A -> Prop) (h1 : @FINITE A s) : (term32 A B t R s g) = (term112 A B t R s g).
Proof. exact (MK_COMB (@lem7160996 A B R t s h1) (@lem7161056 A B t R s g)). Qed.
Lemma lem7161062 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7161063 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (g : A -> real) (s : A -> Prop) (h1 : @FINITE A s) : (term113 A B t R s g) = (term114 A B t R s g).
Proof. exact (MK_COMB (@lem7161062) (@lem7161059 A B t R g s h1)). Qed.
Lemma lem7161072 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (g : A -> real) : ((term115 A B t s R g) = (@sum A s g)) = ((term115 A B t s R g) = (@sum A s g)).
Proof. exact (eq_refl ((term115 A B t s R g) = (@sum A s g))). Qed.
Lemma lem7161073 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (g : A -> real) (s : A -> Prop) (h1 : @FINITE A s) : (term116 A B t R s g) = (term117 A B t R s g).
Proof. exact (MK_COMB (@lem7161063 A B t R g s h1) (@lem7161072 A B t R s g)). Qed.
Lemma lem7161076 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (g : A -> real) (s : A -> Prop) (h1 : @FINITE A s) : (term117 A B t R s g) = (term116 A B t R s g).
Proof. exact (SYM (@lem7161073 A B t R g s h1)). Qed.
Lemma lem7161078 (p : Prop) (q : Prop) (r : Prop) : term118 p q r.
Proof. exact (@lem137 p q r (@lem129 p q r)). Qed.
Lemma lem7161079 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (g : A -> real) : term119 A B t R s g.
Proof. exact (@lem7161078 (term81 A B s R t) ((term109 A B s t R g) = (@sum A s g)) ((term115 A B t s R g) = (@sum A s g))). Qed.
Lemma lem7161081 (p : Prop) : p = (term120 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7161082 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : (term81 A B s R t) = (term121 A B s R t).
Proof. exact (@lem7161081 (term81 A B s R t)). Qed.
Lemma lem7161083 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : (term121 A B s R t) = (term81 A B s R t).
Proof. exact (SYM (@lem7161082 A B s R t)). Qed.
Lemma lem7161084 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (h1 : term122 A B s R t) : term122 A B s R t.
Proof. exact (h1). Qed.
Lemma lem7161095 {B : Type'} (P : B -> Prop) : term123 B P.
Proof. exact (@lem19732 B P). Qed.
Lemma lem7161096 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : term124 A B t R x.
Proof. exact (@lem7161095 B (term125 A B t R x)). Qed.
Lemma lem7161097 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term126 A B t R x) = (term127 A B t R x).
Proof. exact (eq_refl (term126 A B t R x)). Qed.
Lemma lem7161098 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term128 A B t R x x') = (term129 A B t R x x').
Proof. exact (eq_refl (term128 A B t R x x')). Qed.
Lemma lem7161099 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7161100 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term130 A B t R x x') = (term131 A B t R x x').
Proof. exact (MK_COMB (@lem7161099) (@lem7161098 A B t R x x')). Qed.
Lemma lem7161101 {A B : Type'} (x : B) (t : B -> Prop) (R : type1413 A B) (x' : A) : (term132 A B x t R x') = (term133 A B x t R x').
Proof. exact (MK_COMB (@lem7161100 A B t R x' x) (@lem7161097 A B t R x')). Qed.
Lemma lem7161102 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term134 A B t R x) = (term135 A B t R x).
Proof. exact (fun_ext (fun x' : B => @lem7161101 A B x' t R x)). Qed.
Lemma lem7161103 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7161104 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term124 A B t R x) = (term136 A B t R x).
Proof. exact (MK_COMB (@lem7161103 B) (@lem7161102 A B t R x)). Qed.
Lemma lem7161105 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : term136 A B t R x.
Proof. exact (EQ_MP (@lem7161104 A B t R x) (@lem7161096 A B t R x)). Qed.
Lemma lem7161106 {A B : Type'} (t : B -> Prop) (R : type1413 A B) : term137 A B t R.
Proof. exact (fun x : A => @lem7161105 A B t R x). Qed.
Lemma lem7161107 {A B : Type'} (t : B -> Prop) : term138 A B t.
Proof. exact (fun R : type1413 A B => @lem7161106 A B t R). Qed.
Lemma lem7161108 {A B : Type'} : term139 A B.
Proof. exact (fun t : B -> Prop => @lem7161107 A B t). Qed.
Lemma lem7161109 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (h1 : term140 A B s R t) : term140 A B s R t.
Proof. exact (h1). Qed.
Lemma lem7161110 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (h1 : term140 A B s R t) : term141 A B s R t.
Proof. exact (@lem7161109 A B s R t h1 (@lem7161108 A B)). Qed.
Lemma lem7161111 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : term142 A B s R t.
Proof. exact (fun h0 : term140 A B s R t => @lem7161110 A B s R t h0). Qed.
Lemma lem7161112 {A B : Type'} (_95867 : type830 A B) (h1 : _95867 = (term143 A B)) : _95867 = (term143 A B).
Proof. exact (h1). Qed.
Lemma lem7161113 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem7161114 {A B : Type'} (t : B -> Prop) (_95867 : type830 A B) (h1 : _95867 = (term143 A B)) : (_95867 t) = (term144 A B t).
Proof. exact (MK_COMB (@lem7161112 A B _95867 h1) (@lem7161113 B t)). Qed.
Lemma lem7161115 {A B : Type'} (t : B -> Prop) : (term144 A B t) = (term145 A B t).
Proof. exact (eq_refl (term144 A B t)). Qed.
Lemma lem7161116 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) : (term146 A B _95867 t) = (term146 A B _95867 t).
Proof. exact (eq_refl (term146 A B _95867 t)). Qed.
Lemma lem7161117 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) : ((_95867 t) = (term144 A B t)) = ((_95867 t) = (term145 A B t)).
Proof. exact (MK_COMB (@lem7161116 A B _95867 t) (@lem7161115 A B t)). Qed.
Lemma lem7161118 {A B : Type'} (t : B -> Prop) (_95867 : type830 A B) (h1 : _95867 = (term143 A B)) : (_95867 t) = (term145 A B t).
Proof. exact (EQ_MP (@lem7161117 A B _95867 t) (@lem7161114 A B t _95867 h1)). Qed.
Lemma lem7161119 {A B : Type'} (R : type1413 A B) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem7161120 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (_95867 : type830 A B) (h1 : _95867 = (term143 A B)) : (_95867 t R) = (term147 A B t R).
Proof. exact (MK_COMB (@lem7161118 A B t _95867 h1) (@lem7161119 A B R)). Qed.
Lemma lem7161121 {A B : Type'} (t : B -> Prop) (R : type1413 A B) : (term147 A B t R) = (term25 A B t R).
Proof. exact (eq_refl (term147 A B t R)). Qed.
Lemma lem7161122 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (term148 A B _95867 t R) = (term148 A B _95867 t R).
Proof. exact (eq_refl (term148 A B _95867 t R)). Qed.
Lemma lem7161123 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) : ((_95867 t R) = (term147 A B t R)) = ((_95867 t R) = (term25 A B t R)).
Proof. exact (MK_COMB (@lem7161122 A B _95867 t R) (@lem7161121 A B t R)). Qed.
Lemma lem7161124 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (_95867 : type830 A B) (h1 : _95867 = (term143 A B)) : (_95867 t R) = (term25 A B t R).
Proof. exact (EQ_MP (@lem7161123 A B _95867 t R) (@lem7161120 A B t R _95867 h1)). Qed.
Lemma lem7161125 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7161126 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (_95867 : type830 A B) (h1 : _95867 = (term143 A B)) : (_95867 t R x) = (term71 A B t R x).
Proof. exact (MK_COMB (@lem7161124 A B t R _95867 h1) (@lem7161125 A x)). Qed.
Lemma lem7161127 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term71 A B t R x) = (term72 A B t R x).
Proof. exact (eq_refl (term71 A B t R x)). Qed.
Lemma lem7161128 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term149 A B _95867 t R x) = (term149 A B _95867 t R x).
Proof. exact (eq_refl (term149 A B _95867 t R x)). Qed.
Lemma lem7161129 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : ((_95867 t R x) = (term71 A B t R x)) = ((_95867 t R x) = (term72 A B t R x)).
Proof. exact (MK_COMB (@lem7161128 A B _95867 t R x) (@lem7161127 A B t R x)). Qed.
Lemma lem7161130 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (_95867 : type830 A B) (h1 : _95867 = (term143 A B)) : (_95867 t R x) = (term72 A B t R x).
Proof. exact (EQ_MP (@lem7161129 A B _95867 t R x) (@lem7161126 A B t R x _95867 h1)). Qed.
Lemma lem7161131 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (_95867 : type830 A B) (h1 : _95867 = (term143 A B)) : (term72 A B t R x) = (_95867 t R x).
Proof. exact (SYM (@lem7161130 A B t R x _95867 h1)). Qed.
Lemma lem7161132 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (_95867 : type830 A B) (h1 : _95867 = (term143 A B)) : term150 A B _95867 t R.
Proof. exact (fun x : A => @lem7161131 A B t R x _95867 h1). Qed.
Lemma lem7161133 {A B : Type'} (t : B -> Prop) (_95867 : type830 A B) (h1 : _95867 = (term143 A B)) : term151 A B _95867 t.
Proof. exact (fun R : type1413 A B => @lem7161132 A B t R _95867 h1). Qed.
Lemma lem7161134 {A B : Type'} (_95867 : type830 A B) (h1 : _95867 = (term143 A B)) : term152 A B _95867.
Proof. exact (fun t : B -> Prop => @lem7161133 A B t _95867 h1). Qed.
Lemma lem7161135 {A B : Type'} (t : B -> Prop) (_95867 : type830 A B) (h1 : _95867 = (term143 A B)) : term153 A B _95867 t.
Proof. exact (@lem7161134 A B _95867 h1 t). Qed.
Lemma lem7161136 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) : (term153 A B _95867 t) = (term151 A B _95867 t).
Proof. exact (eq_refl (term153 A B _95867 t)). Qed.
Lemma lem7161137 {A B : Type'} (t : B -> Prop) (_95867 : type830 A B) (h1 : _95867 = (term143 A B)) : term151 A B _95867 t.
Proof. exact (EQ_MP (@lem7161136 A B _95867 t) (@lem7161135 A B t _95867 h1)). Qed.
Lemma lem7161138 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (_95867 : type830 A B) (h1 : _95867 = (term143 A B)) : term154 A B _95867 t R.
Proof. exact (@lem7161137 A B t _95867 h1 R). Qed.
Lemma lem7161139 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (term154 A B _95867 t R) = (term150 A B _95867 t R).
Proof. exact (eq_refl (term154 A B _95867 t R)). Qed.
Lemma lem7161140 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (_95867 : type830 A B) (h1 : _95867 = (term143 A B)) : term150 A B _95867 t R.
Proof. exact (EQ_MP (@lem7161139 A B _95867 t R) (@lem7161138 A B t R _95867 h1)). Qed.
Lemma lem7161141 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (_95867 : type830 A B) (h1 : _95867 = (term143 A B)) : term155 A B _95867 t R x.
Proof. exact (@lem7161140 A B t R _95867 h1 x). Qed.
Lemma lem7161142 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term155 A B _95867 t R x) = ((term72 A B t R x) = (_95867 t R x)).
Proof. exact (eq_refl (term155 A B _95867 t R x)). Qed.
Lemma lem7161145 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (_95867 : type830 A B) (h1 : _95867 = (term143 A B)) : (term72 A B t R x) = (_95867 t R x).
Proof. exact (EQ_MP (@lem7161142 A B _95867 t R x) (@lem7161141 A B t R x _95867 h1)). Qed.
Lemma lem7161146 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (_95867 : type830 A B) (h1 : _95867 = (term143 A B)) : (term72 A B t R x) = (_95867 t R x).
Proof. exact (@lem7161145 A B t R x _95867 h1). Qed.
Lemma lem7161147 {B : Type'} : (@IN B) = (@IN B).
Proof. exact (eq_refl (@IN B)). Qed.
Lemma lem7161148 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (_95867 : type830 A B) (h1 : _95867 = (term143 A B)) : (term77 A B t R x) = (term156 A B _95867 t R x).
Proof. exact (MK_COMB (@lem7161147 B) (@lem7161146 A B t R x _95867 h1)). Qed.
Lemma lem7161149 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem7161150 {A B : Type'} (R : type1413 A B) (x : A) (t : B -> Prop) (_95867 : type830 A B) (h1 : _95867 = (term143 A B)) : (term78 A B R x t) = (term157 A B _95867 R x t).
Proof. exact (MK_COMB (@lem7161148 A B t R x _95867 h1) (@lem7161149 B t)). Qed.
Lemma lem7161151 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7161152 {A B : Type'} (R : type1413 A B) (x : A) (t : B -> Prop) (_95867 : type830 A B) (h1 : _95867 = (term143 A B)) : (term158 A B R x t) = (term159 A B _95867 R x t).
Proof. exact (MK_COMB (@lem7161151) (@lem7161150 A B R x t _95867 h1)). Qed.
Lemma lem7161154 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (_95867 : type830 A B) (h1 : _95867 = (term143 A B)) : (term72 A B t R x) = (_95867 t R x).
Proof. exact (EQ_MP (@lem7161142 A B _95867 t R x) (@lem7161141 A B t R x _95867 h1)). Qed.
Lemma lem7161155 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (_95867 : type830 A B) (h1 : _95867 = (term143 A B)) : (term72 A B t R x) = (_95867 t R x).
Proof. exact (@lem7161154 A B t R x _95867 h1). Qed.
Lemma lem7161156 {A B : Type'} (R : type1413 A B) (x : A) : (R x) = (R x).
Proof. exact (eq_refl (R x)). Qed.
Lemma lem7161157 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (_95867 : type830 A B) (h1 : _95867 = (term143 A B)) : (term160 A B t R x) = (term161 A B _95867 t R x).
Proof. exact (MK_COMB (@lem7161156 A B R x) (@lem7161155 A B t R x _95867 h1)). Qed.
Lemma lem7161158 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (_95867 : type830 A B) (h1 : _95867 = (term143 A B)) : (term127 A B t R x) = (term162 A B _95867 t R x).
Proof. exact (MK_COMB (@lem7161152 A B R x t _95867 h1) (@lem7161157 A B t R x _95867 h1)). Qed.
Lemma lem7161159 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term131 A B t R x x') = (term131 A B t R x x').
Proof. exact (eq_refl (term131 A B t R x x')). Qed.
Lemma lem7161160 {A B : Type'} (x : B) (t : B -> Prop) (R : type1413 A B) (x' : A) (_95867 : type830 A B) (h1 : _95867 = (term143 A B)) : (term133 A B x t R x') = (term163 A B x _95867 t R x').
Proof. exact (MK_COMB (@lem7161159 A B t R x' x) (@lem7161158 A B t R x' _95867 h1)). Qed.
Lemma lem7161161 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (_95867 : type830 A B) (h1 : _95867 = (term143 A B)) : (term135 A B t R x) = (term164 A B _95867 t R x).
Proof. exact (fun_ext (fun x' : B => @lem7161160 A B x' t R x _95867 h1)). Qed.
Lemma lem7161162 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7161163 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (_95867 : type830 A B) (h1 : _95867 = (term143 A B)) : (term136 A B t R x) = (term165 A B _95867 t R x).
Proof. exact (MK_COMB (@lem7161162 B) (@lem7161161 A B t R x _95867 h1)). Qed.
Lemma lem7161164 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (_95867 : type830 A B) (h1 : _95867 = (term143 A B)) : (term166 A B t R) = (term167 A B _95867 t R).
Proof. exact (fun_ext (fun x : A => @lem7161163 A B t R x _95867 h1)). Qed.
Lemma lem7161165 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7161166 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (_95867 : type830 A B) (h1 : _95867 = (term143 A B)) : (term137 A B t R) = (term168 A B _95867 t R).
Proof. exact (MK_COMB (@lem7161165 A) (@lem7161164 A B t R _95867 h1)). Qed.
Lemma lem7161167 {A B : Type'} (t : B -> Prop) (_95867 : type830 A B) (h1 : _95867 = (term143 A B)) : (term169 A B t) = (term170 A B _95867 t).
Proof. exact (fun_ext (fun R : type1413 A B => @lem7161166 A B t R _95867 h1)). Qed.
Lemma lem7161168 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem7161169 {A B : Type'} (t : B -> Prop) (_95867 : type830 A B) (h1 : _95867 = (term143 A B)) : (term138 A B t) = (term171 A B _95867 t).
Proof. exact (MK_COMB (@lem7161168 A B) (@lem7161167 A B t _95867 h1)). Qed.
Lemma lem7161170 {A B : Type'} (_95867 : type830 A B) (h1 : _95867 = (term143 A B)) : (term172 A B) = (term173 A B _95867).
Proof. exact (fun_ext (fun t : B -> Prop => @lem7161169 A B t _95867 h1)). Qed.
Lemma lem7161171 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem7161172 {A B : Type'} (_95867 : type830 A B) (h1 : _95867 = (term143 A B)) : (term139 A B) = (term174 A B _95867).
Proof. exact (MK_COMB (@lem7161171 B) (@lem7161170 A B _95867 h1)). Qed.
Lemma lem7161173 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7161174 {A B : Type'} (_95867 : type830 A B) (h1 : _95867 = (term143 A B)) : (term175 A B) = (term176 A B _95867).
Proof. exact (MK_COMB (@lem7161173) (@lem7161172 A B _95867 h1)). Qed.
Lemma lem7161176 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (_95867 : type830 A B) (h1 : _95867 = (term143 A B)) : (term72 A B t R x) = (_95867 t R x).
Proof. exact (EQ_MP (@lem7161142 A B _95867 t R x) (@lem7161141 A B t R x _95867 h1)). Qed.
Lemma lem7161177 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (_95867 : type830 A B) (h1 : _95867 = (term143 A B)) : (term72 A B t R x) = (_95867 t R x).
Proof. exact (@lem7161176 A B t R x _95867 h1). Qed.
Lemma lem7161178 {B : Type'} : (@IN B) = (@IN B).
Proof. exact (eq_refl (@IN B)). Qed.
Lemma lem7161179 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (_95867 : type830 A B) (h1 : _95867 = (term143 A B)) : (term77 A B t R x) = (term156 A B _95867 t R x).
Proof. exact (MK_COMB (@lem7161178 B) (@lem7161177 A B t R x _95867 h1)). Qed.
Lemma lem7161180 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem7161181 {A B : Type'} (R : type1413 A B) (x : A) (t : B -> Prop) (_95867 : type830 A B) (h1 : _95867 = (term143 A B)) : (term78 A B R x t) = (term157 A B _95867 R x t).
Proof. exact (MK_COMB (@lem7161179 A B t R x _95867 h1) (@lem7161180 B t)). Qed.
Lemma lem7161182 {A : Type'} (x : A) (s : A -> Prop) : (term63 A x s) = (term63 A x s).
Proof. exact (eq_refl (term63 A x s)). Qed.
Lemma lem7161183 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x : A) (t : B -> Prop) (_95867 : type830 A B) (h1 : _95867 = (term143 A B)) : (term79 A B s R x t) = (term177 A B s _95867 R x t).
Proof. exact (MK_COMB (@lem7161182 A x s) (@lem7161181 A B R x t _95867 h1)). Qed.
Lemma lem7161184 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (_95867 : type830 A B) (h1 : _95867 = (term143 A B)) : (term80 A B s R t) = (term178 A B s _95867 R t).
Proof. exact (fun_ext (fun x : A => @lem7161183 A B s R x t _95867 h1)). Qed.
Lemma lem7161185 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7161186 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (_95867 : type830 A B) (h1 : _95867 = (term143 A B)) : (term81 A B s R t) = (term179 A B s _95867 R t).
Proof. exact (MK_COMB (@lem7161185 A) (@lem7161184 A B s R t _95867 h1)). Qed.
Lemma lem7161187 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7161188 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (_95867 : type830 A B) (h1 : _95867 = (term143 A B)) : (term122 A B s R t) = (term180 A B s _95867 R t).
Proof. exact (MK_COMB (@lem7161187) (@lem7161186 A B s R t _95867 h1)). Qed.
Lemma lem7161189 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7161190 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (_95867 : type830 A B) (h1 : _95867 = (term143 A B)) : (term181 A B s R t) = (term182 A B s _95867 R t).
Proof. exact (MK_COMB (@lem7161189) (@lem7161188 A B s R t _95867 h1)). Qed.
Lemma lem7161191 : False = False.
Proof. exact (eq_refl False). Qed.
Lemma lem7161192 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (_95867 : type830 A B) (h1 : _95867 = (term143 A B)) : (term121 A B s R t) = (term183 A B s _95867 R t).
Proof. exact (MK_COMB (@lem7161190 A B s R t _95867 h1) (@lem7161191)). Qed.
Lemma lem7161193 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term184 A B s t R) = (term184 A B s t R).
Proof. exact (eq_refl (term184 A B s t R)). Qed.
Lemma lem7161194 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (_95867 : type830 A B) (h1 : _95867 = (term143 A B)) : (term185 A B s R t) = (term186 A B s _95867 R t).
Proof. exact (MK_COMB (@lem7161193 A B s t R) (@lem7161192 A B s R t _95867 h1)). Qed.
Lemma lem7161195 {A : Type'} (s : A -> Prop) : (term187 A s) = (term187 A s).
Proof. exact (eq_refl (term187 A s)). Qed.
Lemma lem7161196 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (_95867 : type830 A B) (h1 : _95867 = (term143 A B)) : (term141 A B s R t) = (term188 A B s _95867 R t).
Proof. exact (MK_COMB (@lem7161195 A s) (@lem7161194 A B s R t _95867 h1)). Qed.
Lemma lem7161197 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (_95867 : type830 A B) (h1 : _95867 = (term143 A B)) : (term140 A B s R t) = (term189 A B s _95867 R t).
Proof. exact (MK_COMB (@lem7161174 A B _95867 h1) (@lem7161196 A B s R t _95867 h1)). Qed.
Lemma lem7161198 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (h1 : term190 A B s R t) : term190 A B s R t.
Proof. exact (h1). Qed.
Lemma lem7161199 {A B : Type'} (_95867 : type830 A B) (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (h1 : term190 A B s R t) : term191 A B s R t _95867.
Proof. exact (@lem7161198 A B s R t h1 _95867). Qed.
Lemma lem7161200 {A B : Type'} (s : A -> Prop) (_95867 : type830 A B) (R : type1413 A B) (t : B -> Prop) : (term191 A B s R t _95867) = (term189 A B s _95867 R t).
Proof. exact (eq_refl (term191 A B s R t _95867)). Qed.
Lemma lem7161201 {A B : Type'} (_95867 : type830 A B) (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (h1 : term190 A B s R t) : term189 A B s _95867 R t.
Proof. exact (EQ_MP (@lem7161200 A B s _95867 R t) (@lem7161199 A B _95867 s R t h1)). Qed.
Lemma lem7161202 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (_95867 : type830 A B) (h1 : _95867 = (term143 A B)) : (term189 A B s _95867 R t) = (term140 A B s R t).
Proof. exact (SYM (@lem7161197 A B s R t _95867 h1)). Qed.
Lemma lem7161203 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (_95867 : type830 A B) (h1 : term190 A B s R t) (h2 : _95867 = (term143 A B)) : term140 A B s R t.
Proof. exact (EQ_MP (@lem7161202 A B s R t _95867 h2) (@lem7161201 A B _95867 s R t h1)). Qed.
Lemma lem7161204 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (_95867 : type830 A B) (h1 : _95867 = (term143 A B)) : term192 A B s R t.
Proof. exact (fun h0 : term190 A B s R t => @lem7161203 A B s R t _95867 h0 h1). Qed.
Lemma lem7161205 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : term193 A B s R t.
Proof. exact (@lem51 (term140 A B s R t) (term190 A B s R t) (term141 A B s R t)). Qed.
Lemma lem7161206 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (_95867 : type830 A B) (h1 : _95867 = (term143 A B)) : term194 A B s R t.
Proof. exact (@lem7161205 A B s R t (@lem7161204 A B s R t _95867 h1)). Qed.
Lemma lem7161207 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (_95867 : type830 A B) (h1 : _95867 = (term143 A B)) : term195 A B s R t.
Proof. exact (@lem7161206 A B s R t _95867 h1 (@lem7161111 A B s R t)). Qed.
Lemma lem7161208 {A B : Type'} : (term143 A B) = (term143 A B).
Proof. exact (eq_refl (term143 A B)). Qed.
Lemma lem7161209 {A B : Type'} (_95867 : type830 A B) (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : term196 A B _95867 s R t.
Proof. exact (fun h0 : _95867 = (term143 A B) => @lem7161207 A B s R t _95867 h0). Qed.
Lemma lem7161210 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : term197 A B s R t.
Proof. exact (@lem7161209 A B (term143 A B) s R t). Qed.
Lemma lem7161211 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : term195 A B s R t.
Proof. exact (@lem7161210 A B s R t (@lem7161208 A B)). Qed.
Lemma lem7161212 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (h1 : term190 A B s R t) : term190 A B s R t.
Proof. exact (h1). Qed.
Lemma lem7161213 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : term198 A B s R t.
Proof. exact (fun h0 : term190 A B s R t => @lem7161212 A B s R t h0). Qed.
Lemma lem7161214 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : term199 A B s R t.
Proof. exact (@lem51 (term190 A B s R t) (term190 A B s R t) (term141 A B s R t)). Qed.
Lemma lem7161215 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : term200 A B s R t.
Proof. exact (@lem7161214 A B s R t (@lem7161213 A B s R t)). Qed.
Lemma lem7161216 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : term195 A B s R t.
Proof. exact (@lem7161215 A B s R t (@lem7161211 A B s R t)). Qed.
Lemma lem7161217 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (h1 : term195 A B s R t) : term195 A B s R t.
Proof. exact (h1). Qed.
Lemma lem7161218 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (h1 : term190 A B s R t) : term190 A B s R t.
Proof. exact (h1). Qed.
Lemma lem7161219 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (h1 : term190 A B s R t) (h2 : term195 A B s R t) : term141 A B s R t.
Proof. exact (@lem7161217 A B s R t h2 (@lem7161218 A B s R t h1)). Qed.
Lemma lem7161220 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (h1 : term190 A B s R t) : term201 A B s R t.
Proof. exact (fun h0 : term195 A B s R t => @lem7161219 A B s R t h1 h0). Qed.
Lemma lem7161221 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (h1 : term195 A B s R t) : term195 A B s R t.
Proof. exact (h1). Qed.
Lemma lem7161222 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (h1 : term190 A B s R t) (h2 : term195 A B s R t) : term141 A B s R t.
Proof. exact (@lem7161220 A B s R t h1 (@lem7161221 A B s R t h2)). Qed.
Lemma lem7161223 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (h1 : term195 A B s R t) : term195 A B s R t.
Proof. exact (fun h0 : term190 A B s R t => @lem7161222 A B s R t h0 h1). Qed.
Lemma lem7161224 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : term200 A B s R t.
Proof. exact (fun h0 : term195 A B s R t => @lem7161223 A B s R t h0). Qed.
Lemma lem7161227 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : term195 A B s R t.
Proof. exact (@lem7161224 A B s R t (@lem7161216 A B s R t)). Qed.
Lemma lem7161228 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : term195 A B s R t.
Proof. exact (@lem7161227 A B s R t). Qed.
Lemma lem7161282 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7161283 {A B : Type'} (s : A -> Prop) (_95867 : type830 A B) (R : type1413 A B) (t : B -> Prop) : (term183 A B s _95867 R t) = (term202 A B s _95867 R t).
Proof. exact (@lem7161282 (term180 A B s _95867 R t)). Qed.
Lemma lem7161285 (t : Prop) : (term203 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem7161286 {A B : Type'} (s : A -> Prop) (_95867 : type830 A B) (R : type1413 A B) (t : B -> Prop) : (term202 A B s _95867 R t) = (term179 A B s _95867 R t).
Proof. exact (@lem7161285 (term179 A B s _95867 R t)). Qed.
Lemma lem7161291 {A B : Type'} (s : A -> Prop) (_95867 : type830 A B) (R : type1413 A B) (t : B -> Prop) : (term183 A B s _95867 R t) = (term179 A B s _95867 R t).
Proof. exact (TRANS (@lem7161283 A B s _95867 R t) (@lem7161286 A B s _95867 R t)). Qed.
Lemma lem7161294 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term184 A B s t R) = (term184 A B s t R).
Proof. exact (eq_refl (term184 A B s t R)). Qed.
Lemma lem7161295 {A B : Type'} (s : A -> Prop) (_95867 : type830 A B) (R : type1413 A B) (t : B -> Prop) : (term186 A B s _95867 R t) = (term204 A B s _95867 R t).
Proof. exact (MK_COMB (@lem7161294 A B s t R) (@lem7161291 A B s _95867 R t)). Qed.
Lemma lem7161298 {A : Type'} (s : A -> Prop) : (term187 A s) = (term187 A s).
Proof. exact (eq_refl (term187 A s)). Qed.
Lemma lem7161299 {A B : Type'} (s : A -> Prop) (_95867 : type830 A B) (R : type1413 A B) (t : B -> Prop) : (term188 A B s _95867 R t) = (term205 A B s _95867 R t).
Proof. exact (MK_COMB (@lem7161298 A s) (@lem7161295 A B s _95867 R t)). Qed.
Lemma lem7161302 {A B : Type'} (_95867 : type830 A B) : (term176 A B _95867) = (term176 A B _95867).
Proof. exact (eq_refl (term176 A B _95867)). Qed.
Lemma lem7161303 {A B : Type'} (s : A -> Prop) (_95867 : type830 A B) (R : type1413 A B) (t : B -> Prop) : (term189 A B s _95867 R t) = (term206 A B s _95867 R t).
Proof. exact (MK_COMB (@lem7161302 A B _95867) (@lem7161299 A B s _95867 R t)). Qed.
Lemma lem7161306 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : (term207 A B s R t) = (term208 A B s R t).
Proof. exact (fun_ext (fun _95867 : type830 A B => @lem7161303 A B s _95867 R t)). Qed.
Lemma lem7161307 {A B : Type'} : (@all ((B -> Prop) -> (A -> B -> Prop) -> A -> B)) = (@all ((B -> Prop) -> (A -> B -> Prop) -> A -> B)).
Proof. exact (eq_refl (@all ((B -> Prop) -> (A -> B -> Prop) -> A -> B))). Qed.
Lemma lem7161308 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : (term190 A B s R t) = (term209 A B s R t).
Proof. exact (MK_COMB (@lem7161307 A B) (@lem7161306 A B s R t)). Qed.
Lemma lem7161313 {A B : Type'} (R : type1413 A B) (t : B -> Prop) : (term210 A B R t) = (term211 A B R t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7161308 A B s R t)). Qed.
Lemma lem7161314 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7161315 {A B : Type'} (R : type1413 A B) (t : B -> Prop) : (term212 A B R t) = (term213 A B R t).
Proof. exact (MK_COMB (@lem7161314 A) (@lem7161313 A B R t)). Qed.
Lemma lem7161320 {A B : Type'} (t : B -> Prop) : (term214 A B t) = (term215 A B t).
Proof. exact (fun_ext (fun R : type1413 A B => @lem7161315 A B R t)). Qed.
Lemma lem7161321 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem7161322 {A B : Type'} (t : B -> Prop) : (term216 A B t) = (term217 A B t).
Proof. exact (MK_COMB (@lem7161321 A B) (@lem7161320 A B t)). Qed.
Lemma lem7161327 {A B : Type'} : (term218 A B) = (term219 A B).
Proof. exact (fun_ext (fun t : B -> Prop => @lem7161322 A B t)). Qed.
Lemma lem7161328 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem7161337 {A B : Type'} : (term220 A B) = (term221 A B).
Proof. exact (MK_COMB (@lem7161328 B) (@lem7161327 A B)). Qed.
Lemma lem7161342 {A B : Type'} (s : A -> Prop) (_95867 : type830 A B) (R : type1413 A B) (x : A) (t : B -> Prop) : (term177 A B s _95867 R x t) = (term177 A B s _95867 R x t).
Proof. exact (eq_refl (term177 A B s _95867 R x t)). Qed.
Lemma lem7161343 {A B : Type'} (s : A -> Prop) (_95867 : type830 A B) (R : type1413 A B) (t : B -> Prop) : (term178 A B s _95867 R t) = (term178 A B s _95867 R t).
Proof. exact (fun_ext (fun x : A => @lem7161342 A B s _95867 R x t)). Qed.
Lemma lem7161344 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7161345 {A B : Type'} (s : A -> Prop) (_95867 : type830 A B) (R : type1413 A B) (t : B -> Prop) : (term179 A B s _95867 R t) = (term179 A B s _95867 R t).
Proof. exact (MK_COMB (@lem7161344 A) (@lem7161343 A B s _95867 R t)). Qed.
Lemma lem7161350 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term129 A B t R x y) = (term129 A B t R x y).
Proof. exact (eq_refl (term129 A B t R x y)). Qed.
Lemma lem7161351 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term125 A B t R x) = (term125 A B t R x).
Proof. exact (fun_ext (fun y : B => @lem7161350 A B t R x y)). Qed.
Lemma lem7161352 {B : Type'} : (@ex1 B) = (@ex1 B).
Proof. exact (eq_refl (@ex1 B)). Qed.
Lemma lem7161353 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term222 A B t R x) = (term222 A B t R x).
Proof. exact (MK_COMB (@lem7161352 B) (@lem7161351 A B t R x)). Qed.
Lemma lem7161356 {A : Type'} (x : A) (s : A -> Prop) : (term63 A x s) = (term63 A x s).
Proof. exact (eq_refl (term63 A x s)). Qed.
Lemma lem7161357 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term223 A B s t R x) = (term223 A B s t R x).
Proof. exact (MK_COMB (@lem7161356 A x s) (@lem7161353 A B t R x)). Qed.
Lemma lem7161358 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term224 A B s t R) = (term224 A B s t R).
Proof. exact (fun_ext (fun x : A => @lem7161357 A B s t R x)). Qed.
Lemma lem7161359 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7161360 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term34 A B s t R) = (term34 A B s t R).
Proof. exact (MK_COMB (@lem7161359 A) (@lem7161358 A B s t R)). Qed.
Lemma lem7161361 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7161362 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term184 A B s t R) = (term184 A B s t R).
Proof. exact (MK_COMB (@lem7161361) (@lem7161360 A B s t R)). Qed.
Lemma lem7161363 {A B : Type'} (s : A -> Prop) (_95867 : type830 A B) (R : type1413 A B) (t : B -> Prop) : (term204 A B s _95867 R t) = (term204 A B s _95867 R t).
Proof. exact (MK_COMB (@lem7161362 A B s t R) (@lem7161345 A B s _95867 R t)). Qed.
Lemma lem7161366 {A : Type'} (s : A -> Prop) : (term187 A s) = (term187 A s).
Proof. exact (eq_refl (term187 A s)). Qed.
Lemma lem7161367 {A B : Type'} (s : A -> Prop) (_95867 : type830 A B) (R : type1413 A B) (t : B -> Prop) : (term205 A B s _95867 R t) = (term205 A B s _95867 R t).
Proof. exact (MK_COMB (@lem7161366 A s) (@lem7161363 A B s _95867 R t)). Qed.
Lemma lem7161380 {A B : Type'} (x : B) (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) : (term163 A B x _95867 t R x') = (term163 A B x _95867 t R x').
Proof. exact (eq_refl (term163 A B x _95867 t R x')). Qed.
Lemma lem7161381 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term164 A B _95867 t R x) = (term164 A B _95867 t R x).
Proof. exact (fun_ext (fun x' : B => @lem7161380 A B x' _95867 t R x)). Qed.
Lemma lem7161382 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7161383 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term165 A B _95867 t R x) = (term165 A B _95867 t R x).
Proof. exact (MK_COMB (@lem7161382 B) (@lem7161381 A B _95867 t R x)). Qed.
Lemma lem7161384 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (term167 A B _95867 t R) = (term167 A B _95867 t R).
Proof. exact (fun_ext (fun x : A => @lem7161383 A B _95867 t R x)). Qed.
Lemma lem7161385 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7161386 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (term168 A B _95867 t R) = (term168 A B _95867 t R).
Proof. exact (MK_COMB (@lem7161385 A) (@lem7161384 A B _95867 t R)). Qed.
Lemma lem7161387 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) : (term170 A B _95867 t) = (term170 A B _95867 t).
Proof. exact (fun_ext (fun R : type1413 A B => @lem7161386 A B _95867 t R)). Qed.
Lemma lem7161388 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem7161389 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) : (term171 A B _95867 t) = (term171 A B _95867 t).
Proof. exact (MK_COMB (@lem7161388 A B) (@lem7161387 A B _95867 t)). Qed.
Lemma lem7161390 {A B : Type'} (_95867 : type830 A B) : (term173 A B _95867) = (term173 A B _95867).
Proof. exact (fun_ext (fun t : B -> Prop => @lem7161389 A B _95867 t)). Qed.
Lemma lem7161391 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem7161392 {A B : Type'} (_95867 : type830 A B) : (term174 A B _95867) = (term174 A B _95867).
Proof. exact (MK_COMB (@lem7161391 B) (@lem7161390 A B _95867)). Qed.
Lemma lem7161393 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7161394 {A B : Type'} (_95867 : type830 A B) : (term176 A B _95867) = (term176 A B _95867).
Proof. exact (MK_COMB (@lem7161393) (@lem7161392 A B _95867)). Qed.
Lemma lem7161395 {A B : Type'} (s : A -> Prop) (_95867 : type830 A B) (R : type1413 A B) (t : B -> Prop) : (term206 A B s _95867 R t) = (term206 A B s _95867 R t).
Proof. exact (MK_COMB (@lem7161394 A B _95867) (@lem7161367 A B s _95867 R t)). Qed.
Lemma lem7161396 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : (term208 A B s R t) = (term208 A B s R t).
Proof. exact (fun_ext (fun _95867 : type830 A B => @lem7161395 A B s _95867 R t)). Qed.
Lemma lem7161397 {A B : Type'} : (@all ((B -> Prop) -> (A -> B -> Prop) -> A -> B)) = (@all ((B -> Prop) -> (A -> B -> Prop) -> A -> B)).
Proof. exact (eq_refl (@all ((B -> Prop) -> (A -> B -> Prop) -> A -> B))). Qed.
Lemma lem7161398 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : (term209 A B s R t) = (term209 A B s R t).
Proof. exact (MK_COMB (@lem7161397 A B) (@lem7161396 A B s R t)). Qed.
Lemma lem7161399 {A B : Type'} (R : type1413 A B) (t : B -> Prop) : (term211 A B R t) = (term211 A B R t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7161398 A B s R t)). Qed.
Lemma lem7161400 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7161401 {A B : Type'} (R : type1413 A B) (t : B -> Prop) : (term213 A B R t) = (term213 A B R t).
Proof. exact (MK_COMB (@lem7161400 A) (@lem7161399 A B R t)). Qed.
Lemma lem7161402 {A B : Type'} (t : B -> Prop) : (term215 A B t) = (term215 A B t).
Proof. exact (fun_ext (fun R : type1413 A B => @lem7161401 A B R t)). Qed.
Lemma lem7161403 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem7161404 {A B : Type'} (t : B -> Prop) : (term217 A B t) = (term217 A B t).
Proof. exact (MK_COMB (@lem7161403 A B) (@lem7161402 A B t)). Qed.
Lemma lem7161405 {A B : Type'} : (term219 A B) = (term219 A B).
Proof. exact (fun_ext (fun t : B -> Prop => @lem7161404 A B t)). Qed.
Lemma lem7161406 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem7161407 {A B : Type'} : (term221 A B) = (term221 A B).
Proof. exact (MK_COMB (@lem7161406 B) (@lem7161405 A B)). Qed.
Lemma lem7161488 {A B : Type'} : (term220 A B) = (term221 A B).
Proof. exact (TRANS (@lem7161337 A B) (@lem7161407 A B)). Qed.
Lemma lem7161489 {A B : Type'} : (term221 A B) = (term220 A B).
Proof. exact (SYM (@lem7161488 A B)). Qed.
Lemma lem7161490 {A B : Type'} (_95867 : type830 A B) (h1 : term174 A B _95867) : term174 A B _95867.
Proof. exact (h1). Qed.
Lemma lem7161492 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (h1 : term34 A B s t R) : term34 A B s t R.
Proof. exact (h1). Qed.
Lemma lem7161495 (p : Prop) : p = (term120 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7161496 {A B : Type'} (_95867 : type830 A B) (R : type1413 A B) (x : A) (t : B -> Prop) : (term157 A B _95867 R x t) = (term225 A B _95867 R x t).
Proof. exact (@lem7161495 (term157 A B _95867 R x t)). Qed.
Lemma lem7161497 {A B : Type'} (_95867 : type830 A B) (R : type1413 A B) (x : A) (t : B -> Prop) : (term225 A B _95867 R x t) = (term157 A B _95867 R x t).
Proof. exact (SYM (@lem7161496 A B _95867 R x t)). Qed.
Lemma lem7161498 {A B : Type'} (_95867 : type830 A B) (R : type1413 A B) (x : A) (t : B -> Prop) (h1 : term226 A B _95867 R x t) : term226 A B _95867 R x t.
Proof. exact (h1). Qed.
Lemma lem7161505 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term227 A B t R x x') = (term228 A B t R x x').
Proof. exact (@lem17045 (@IN B x' t) (R x x')). Qed.
Lemma lem7161510 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term162 A B _95867 t R x) = (term162 A B _95867 t R x).
Proof. exact (eq_refl (term162 A B _95867 t R x)). Qed.
Lemma lem7161511 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7161512 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term229 A B t R x x') = (term230 A B t R x x').
Proof. exact (MK_COMB (@lem7161511) (@lem7161505 A B t R x x')). Qed.
Lemma lem7161513 {A B : Type'} (x : B) (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) : (term231 A B x _95867 t R x') = (term232 A B x _95867 t R x').
Proof. exact (MK_COMB (@lem7161512 A B t R x' x) (@lem7161510 A B _95867 t R x')). Qed.
Lemma lem7161514 {A B : Type'} (x : B) (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) : (term163 A B x _95867 t R x') = (term231 A B x _95867 t R x').
Proof. exact (@lem17265 (term129 A B t R x' x) (term162 A B _95867 t R x')). Qed.
Lemma lem7161515 {A B : Type'} (x : B) (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) : (term163 A B x _95867 t R x') = (term232 A B x _95867 t R x').
Proof. exact (TRANS (@lem7161514 A B x _95867 t R x') (@lem7161513 A B x _95867 t R x')). Qed.
Lemma lem7161516 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term164 A B _95867 t R x) = (term233 A B _95867 t R x).
Proof. exact (fun_ext (fun x' : B => @lem7161515 A B x' _95867 t R x)). Qed.
Lemma lem7161517 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7161518 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term165 A B _95867 t R x) = (term234 A B _95867 t R x).
Proof. exact (MK_COMB (@lem7161517 B) (@lem7161516 A B _95867 t R x)). Qed.
Lemma lem7161519 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (term167 A B _95867 t R) = (term235 A B _95867 t R).
Proof. exact (fun_ext (fun x : A => @lem7161518 A B _95867 t R x)). Qed.
Lemma lem7161520 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7161521 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (term168 A B _95867 t R) = (term236 A B _95867 t R).
Proof. exact (MK_COMB (@lem7161520 A) (@lem7161519 A B _95867 t R)). Qed.
Lemma lem7161522 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) : (term170 A B _95867 t) = (term237 A B _95867 t).
Proof. exact (fun_ext (fun R : type1413 A B => @lem7161521 A B _95867 t R)). Qed.
Lemma lem7161523 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem7161524 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) : (term171 A B _95867 t) = (term238 A B _95867 t).
Proof. exact (MK_COMB (@lem7161523 A B) (@lem7161522 A B _95867 t)). Qed.
Lemma lem7161525 {A B : Type'} (_95867 : type830 A B) : (term173 A B _95867) = (term239 A B _95867).
Proof. exact (fun_ext (fun t : B -> Prop => @lem7161524 A B _95867 t)). Qed.
Lemma lem7161526 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem7161527 {A B : Type'} (_95867 : type830 A B) : (term174 A B _95867) = (term240 A B _95867).
Proof. exact (MK_COMB (@lem7161526 B) (@lem7161525 A B _95867)). Qed.
Lemma lem7161561 {A : Type'} (P : A -> Prop) (Q : Prop) : (term241 A P Q) = (term242 A P Q).
Proof. exact (EQ_MP (@lem18947 A P Q) (@lem18946 A P Q)). Qed.
Lemma lem7161562 {B : Type'} (P : B -> Prop) (Q : Prop) : (term241 B P Q) = (term242 B P Q).
Proof. exact (@lem7161561 B P Q). Qed.
Lemma lem7161563 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term243 A B _95867 t R x) = (term244 A B _95867 t R x).
Proof. exact (@lem7161562 B (term245 A B t R x) (term162 A B _95867 t R x)). Qed.
Lemma lem7161564 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term246 A B t R x x') = (term228 A B t R x x').
Proof. exact (eq_refl (term246 A B t R x x')). Qed.
Lemma lem7161565 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7161566 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term247 A B t R x x') = (term230 A B t R x x').
Proof. exact (MK_COMB (@lem7161565) (@lem7161564 A B t R x x')). Qed.
Lemma lem7161567 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term162 A B _95867 t R x) = (term162 A B _95867 t R x).
Proof. exact (eq_refl (term162 A B _95867 t R x)). Qed.
Lemma lem7161568 {A B : Type'} (x : B) (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) : (term248 A B x _95867 t R x') = (term232 A B x _95867 t R x').
Proof. exact (MK_COMB (@lem7161566 A B t R x' x) (@lem7161567 A B _95867 t R x')). Qed.
Lemma lem7161569 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term249 A B _95867 t R x) = (term233 A B _95867 t R x).
Proof. exact (fun_ext (fun x' : B => @lem7161568 A B x' _95867 t R x)). Qed.
Lemma lem7161570 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7161571 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term243 A B _95867 t R x) = (term234 A B _95867 t R x).
Proof. exact (MK_COMB (@lem7161570 B) (@lem7161569 A B _95867 t R x)). Qed.
Lemma lem7161572 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7161573 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term250 A B _95867 t R x) = (term251 A B _95867 t R x).
Proof. exact (MK_COMB (@lem7161572) (@lem7161571 A B _95867 t R x)). Qed.
Lemma lem7161574 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term246 A B t R x x') = (term228 A B t R x x').
Proof. exact (eq_refl (term246 A B t R x x')). Qed.
Lemma lem7161575 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term252 A B t R x) = (term245 A B t R x).
Proof. exact (fun_ext (fun x' : B => @lem7161574 A B t R x x')). Qed.
Lemma lem7161576 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7161577 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term253 A B t R x) = (term254 A B t R x).
Proof. exact (MK_COMB (@lem7161576 B) (@lem7161575 A B t R x)). Qed.
Lemma lem7161578 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7161579 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term255 A B t R x) = (term256 A B t R x).
Proof. exact (MK_COMB (@lem7161578) (@lem7161577 A B t R x)). Qed.
Lemma lem7161580 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term162 A B _95867 t R x) = (term162 A B _95867 t R x).
Proof. exact (eq_refl (term162 A B _95867 t R x)). Qed.
Lemma lem7161581 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term244 A B _95867 t R x) = (term257 A B _95867 t R x).
Proof. exact (MK_COMB (@lem7161579 A B t R x) (@lem7161580 A B _95867 t R x)). Qed.
Lemma lem7161582 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : ((term243 A B _95867 t R x) = (term244 A B _95867 t R x)) = ((term234 A B _95867 t R x) = (term257 A B _95867 t R x)).
Proof. exact (MK_COMB (@lem7161573 A B _95867 t R x) (@lem7161581 A B _95867 t R x)). Qed.
Lemma lem7161583 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term234 A B _95867 t R x) = (term257 A B _95867 t R x).
Proof. exact (EQ_MP (@lem7161582 A B _95867 t R x) (@lem7161563 A B _95867 t R x)). Qed.
Lemma lem7161632 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (term235 A B _95867 t R) = (term258 A B _95867 t R).
Proof. exact (fun_ext (fun x : A => @lem7161583 A B _95867 t R x)). Qed.
Lemma lem7161633 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7161634 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (term236 A B _95867 t R) = (term259 A B _95867 t R).
Proof. exact (MK_COMB (@lem7161633 A) (@lem7161632 A B _95867 t R)). Qed.
Lemma lem7161683 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) : (term237 A B _95867 t) = (term260 A B _95867 t).
Proof. exact (fun_ext (fun R : type1413 A B => @lem7161634 A B _95867 t R)). Qed.
Lemma lem7161684 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem7161685 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) : (term238 A B _95867 t) = (term261 A B _95867 t).
Proof. exact (MK_COMB (@lem7161684 A B) (@lem7161683 A B _95867 t)). Qed.
Lemma lem7161690 {A B : Type'} (_95867 : type830 A B) : (term239 A B _95867) = (term262 A B _95867).
Proof. exact (fun_ext (fun t : B -> Prop => @lem7161685 A B _95867 t)). Qed.
Lemma lem7161691 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem7161698 {A B : Type'} (_95867 : type830 A B) : (term240 A B _95867) = (term263 A B _95867).
Proof. exact (MK_COMB (@lem7161691 B) (@lem7161690 A B _95867)). Qed.
Lemma lem7161699 {A B : Type'} (_95867 : type830 A B) : (term174 A B _95867) = (term263 A B _95867).
Proof. exact (TRANS (@lem7161527 A B _95867) (@lem7161698 A B _95867)). Qed.
Lemma lem7161700 {A B : Type'} (_95867 : type830 A B) (h1 : term174 A B _95867) : term263 A B _95867.
Proof. exact (EQ_MP (@lem7161699 A B _95867) (@lem7161490 A B _95867 h1)). Qed.
Lemma lem7161716 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term227 A B t R x y) = (term228 A B t R x y).
Proof. exact (@lem17045 (@IN B y t) (R x y)). Qed.
Lemma lem7161721 {B : Type'} (y' : B) (y : B) : (y' = y) = (y' = y).
Proof. exact (eq_refl (y' = y)). Qed.
Lemma lem7161722 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term128 A B t R x y) = (term129 A B t R x y).
Proof. exact (eq_refl (term128 A B t R x y)). Qed.
Lemma lem7161723 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term128 A B t R x y') = (term129 A B t R x y').
Proof. exact (eq_refl (term128 A B t R x y')). Qed.
Lemma lem7161724 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term227 A B t R x y') = (term228 A B t R x y').
Proof. exact (@lem7161716 A B t R x y'). Qed.
Lemma lem7161725 {B : Type'} (P : B -> Prop) : (@ex1 B P) = (term264 B P).
Proof. exact (@lem18897 B P). Qed.
Lemma lem7161726 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term222 A B t R x) = (term265 A B t R x).
Proof. exact (@lem7161725 B (term125 A B t R x)). Qed.
Lemma lem7161727 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7161728 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term266 A B t R x y') = (term227 A B t R x y').
Proof. exact (MK_COMB (@lem7161727) (@lem7161723 A B t R x y')). Qed.
Lemma lem7161729 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term266 A B t R x y') = (term228 A B t R x y').
Proof. exact (TRANS (@lem7161728 A B t R x y') (@lem7161724 A B t R x y')). Qed.
Lemma lem7161730 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7161731 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term267 A B t R x y') = (term230 A B t R x y').
Proof. exact (MK_COMB (@lem7161730) (@lem7161729 A B t R x y')). Qed.
Lemma lem7161732 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y : B) : (term268 A B t R x y' y) = (term269 A B t R x y' y).
Proof. exact (MK_COMB (@lem7161731 A B t R x y') (@lem7161721 B y' y)). Qed.
Lemma lem7161733 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7161734 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term266 A B t R x y) = (term227 A B t R x y).
Proof. exact (MK_COMB (@lem7161733) (@lem7161722 A B t R x y)). Qed.
Lemma lem7161735 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term266 A B t R x y) = (term228 A B t R x y).
Proof. exact (TRANS (@lem7161734 A B t R x y) (@lem7161716 A B t R x y)). Qed.
Lemma lem7161736 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7161737 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term267 A B t R x y) = (term230 A B t R x y).
Proof. exact (MK_COMB (@lem7161736) (@lem7161735 A B t R x y)). Qed.
Lemma lem7161738 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y : B) : (term270 A B t R x y' y) = (term271 A B t R x y' y).
Proof. exact (MK_COMB (@lem7161737 A B t R x y) (@lem7161732 A B t R x y' y)). Qed.
Lemma lem7161739 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term272 A B t R x y) = (term273 A B t R x y).
Proof. exact (fun_ext (fun y' : B => @lem7161738 A B t R x y' y)). Qed.
Lemma lem7161740 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7161741 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term274 A B t R x y) = (term275 A B t R x y).
Proof. exact (MK_COMB (@lem7161740 B) (@lem7161739 A B t R x y)). Qed.
Lemma lem7161742 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term276 A B t R x) = (term277 A B t R x).
Proof. exact (fun_ext (fun y : B => @lem7161741 A B t R x y)). Qed.
Lemma lem7161743 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7161744 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term278 A B t R x) = (term279 A B t R x).
Proof. exact (MK_COMB (@lem7161743 B) (@lem7161742 A B t R x)). Qed.
Lemma lem7161745 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term128 A B t R x y) = (term129 A B t R x y).
Proof. exact (eq_refl (term128 A B t R x y)). Qed.
Lemma lem7161746 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term280 A B t R x) = (term125 A B t R x).
Proof. exact (fun_ext (fun y : B => @lem7161745 A B t R x y)). Qed.
Lemma lem7161747 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem7161748 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term281 A B t R x) = (term282 A B t R x).
Proof. exact (MK_COMB (@lem7161747 B) (@lem7161746 A B t R x)). Qed.
Lemma lem7161749 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7161750 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term283 A B t R x) = (term284 A B t R x).
Proof. exact (MK_COMB (@lem7161749) (@lem7161748 A B t R x)). Qed.
Lemma lem7161751 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term265 A B t R x) = (term285 A B t R x).
Proof. exact (MK_COMB (@lem7161750 A B t R x) (@lem7161744 A B t R x)). Qed.
Lemma lem7161752 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term222 A B t R x) = (term285 A B t R x).
Proof. exact (TRANS (@lem7161726 A B t R x) (@lem7161751 A B t R x)). Qed.
Lemma lem7161754 {A : Type'} (x : A) (s : A -> Prop) : (term286 A x s) = (term286 A x s).
Proof. exact (eq_refl (term286 A x s)). Qed.
Lemma lem7161755 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term287 A B s t R x) = (term288 A B s t R x).
Proof. exact (MK_COMB (@lem7161754 A x s) (@lem7161752 A B t R x)). Qed.
Lemma lem7161756 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term223 A B s t R x) = (term287 A B s t R x).
Proof. exact (@lem17265 (@IN A x s) (term222 A B t R x)). Qed.
Lemma lem7161757 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term223 A B s t R x) = (term288 A B s t R x).
Proof. exact (TRANS (@lem7161756 A B s t R x) (@lem7161755 A B s t R x)). Qed.
Lemma lem7161758 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term224 A B s t R) = (term289 A B s t R).
Proof. exact (fun_ext (fun x : A => @lem7161757 A B s t R x)). Qed.
Lemma lem7161759 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7161760 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term34 A B s t R) = (term290 A B s t R).
Proof. exact (MK_COMB (@lem7161759 A) (@lem7161758 A B s t R)). Qed.
Lemma lem7161862 {A : Type'} (P : Prop) (Q : A -> Prop) : (term291 A P Q) = (term292 A P Q).
Proof. exact (EQ_MP (@lem18941 A P Q) (@lem18940 A P Q)). Qed.
Lemma lem7161863 {B : Type'} (P : Prop) (Q : B -> Prop) : (term291 B P Q) = (term292 B P Q).
Proof. exact (@lem7161862 B P Q). Qed.
Lemma lem7161864 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term293 A B t R x y) = (term294 A B t R x y).
Proof. exact (@lem7161863 B (term228 A B t R x y) (term295 A B t R x y)). Qed.
Lemma lem7161865 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y : B) : (term296 A B t R x y y') = (term269 A B t R x y' y).
Proof. exact (eq_refl (term296 A B t R x y y')). Qed.
Lemma lem7161866 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term230 A B t R x y) = (term230 A B t R x y).
Proof. exact (eq_refl (term230 A B t R x y)). Qed.
Lemma lem7161867 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y : B) : (term297 A B t R x y y') = (term271 A B t R x y' y).
Proof. exact (MK_COMB (@lem7161866 A B t R x y) (@lem7161865 A B t R x y' y)). Qed.
Lemma lem7161868 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term298 A B t R x y) = (term273 A B t R x y).
Proof. exact (fun_ext (fun y' : B => @lem7161867 A B t R x y' y)). Qed.
Lemma lem7161869 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7161870 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term293 A B t R x y) = (term275 A B t R x y).
Proof. exact (MK_COMB (@lem7161869 B) (@lem7161868 A B t R x y)). Qed.
Lemma lem7161871 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7161872 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term299 A B t R x y) = (term300 A B t R x y).
Proof. exact (MK_COMB (@lem7161871) (@lem7161870 A B t R x y)). Qed.
Lemma lem7161873 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y : B) : (term296 A B t R x y y') = (term269 A B t R x y' y).
Proof. exact (eq_refl (term296 A B t R x y y')). Qed.
Lemma lem7161874 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term301 A B t R x y) = (term295 A B t R x y).
Proof. exact (fun_ext (fun y' : B => @lem7161873 A B t R x y' y)). Qed.
Lemma lem7161875 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7161876 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term302 A B t R x y) = (term303 A B t R x y).
Proof. exact (MK_COMB (@lem7161875 B) (@lem7161874 A B t R x y)). Qed.
Lemma lem7161877 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term230 A B t R x y) = (term230 A B t R x y).
Proof. exact (eq_refl (term230 A B t R x y)). Qed.
Lemma lem7161878 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term294 A B t R x y) = (term304 A B t R x y).
Proof. exact (MK_COMB (@lem7161877 A B t R x y) (@lem7161876 A B t R x y)). Qed.
Lemma lem7161879 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : ((term293 A B t R x y) = (term294 A B t R x y)) = ((term275 A B t R x y) = (term304 A B t R x y)).
Proof. exact (MK_COMB (@lem7161872 A B t R x y) (@lem7161878 A B t R x y)). Qed.
Lemma lem7161880 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term275 A B t R x y) = (term304 A B t R x y).
Proof. exact (EQ_MP (@lem7161879 A B t R x y) (@lem7161864 A B t R x y)). Qed.
Lemma lem7161929 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term277 A B t R x) = (term305 A B t R x).
Proof. exact (fun_ext (fun y : B => @lem7161880 A B t R x y)). Qed.
Lemma lem7161930 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7161931 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term279 A B t R x) = (term306 A B t R x).
Proof. exact (MK_COMB (@lem7161930 B) (@lem7161929 A B t R x)). Qed.
Lemma lem7161980 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term284 A B t R x) = (term284 A B t R x).
Proof. exact (eq_refl (term284 A B t R x)). Qed.
Lemma lem7161981 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term285 A B t R x) = (term307 A B t R x).
Proof. exact (MK_COMB (@lem7161980 A B t R x) (@lem7161931 A B t R x)). Qed.
Lemma lem7161982 {A : Type'} (x : A) (s : A -> Prop) : (term286 A x s) = (term286 A x s).
Proof. exact (eq_refl (term286 A x s)). Qed.
Lemma lem7161983 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term288 A B s t R x) = (term308 A B s t R x).
Proof. exact (MK_COMB (@lem7161982 A x s) (@lem7161981 A B t R x)). Qed.
Lemma lem7161984 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term289 A B s t R) = (term309 A B s t R).
Proof. exact (fun_ext (fun x : A => @lem7161983 A B s t R x)). Qed.
Lemma lem7161985 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7161986 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term290 A B s t R) = (term310 A B s t R).
Proof. exact (MK_COMB (@lem7161985 A) (@lem7161984 A B s t R)). Qed.
Lemma lem7162036 {A : Type'} (P : A -> Prop) (Q : Prop) : (term311 A P Q) = (term312 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem7162037 {B : Type'} (P : B -> Prop) (Q : Prop) : (term311 B P Q) = (term312 B P Q).
Proof. exact (@lem7162036 B P Q). Qed.
Lemma lem7162038 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term313 A B t R x) = (term314 A B t R x).
Proof. exact (@lem7162037 B (term125 A B t R x) (term306 A B t R x)). Qed.
Lemma lem7162039 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term128 A B t R x y) = (term129 A B t R x y).
Proof. exact (eq_refl (term128 A B t R x y)). Qed.
Lemma lem7162040 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term280 A B t R x) = (term125 A B t R x).
Proof. exact (fun_ext (fun y : B => @lem7162039 A B t R x y)). Qed.
Lemma lem7162041 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem7162042 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term281 A B t R x) = (term282 A B t R x).
Proof. exact (MK_COMB (@lem7162041 B) (@lem7162040 A B t R x)). Qed.
Lemma lem7162043 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7162044 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term283 A B t R x) = (term284 A B t R x).
Proof. exact (MK_COMB (@lem7162043) (@lem7162042 A B t R x)). Qed.
Lemma lem7162045 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term306 A B t R x) = (term306 A B t R x).
Proof. exact (eq_refl (term306 A B t R x)). Qed.
Lemma lem7162046 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term313 A B t R x) = (term307 A B t R x).
Proof. exact (MK_COMB (@lem7162044 A B t R x) (@lem7162045 A B t R x)). Qed.
Lemma lem7162047 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7162048 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term315 A B t R x) = (term316 A B t R x).
Proof. exact (MK_COMB (@lem7162047) (@lem7162046 A B t R x)). Qed.
Lemma lem7162049 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term128 A B t R x y) = (term129 A B t R x y).
Proof. exact (eq_refl (term128 A B t R x y)). Qed.
Lemma lem7162050 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7162051 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term317 A B t R x y) = (term318 A B t R x y).
Proof. exact (MK_COMB (@lem7162050) (@lem7162049 A B t R x y)). Qed.
Lemma lem7162052 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term306 A B t R x) = (term306 A B t R x).
Proof. exact (eq_refl (term306 A B t R x)). Qed.
Lemma lem7162053 {A B : Type'} (y : B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term319 A B y t R x) = (term320 A B y t R x).
Proof. exact (MK_COMB (@lem7162051 A B t R x y) (@lem7162052 A B t R x)). Qed.
Lemma lem7162054 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term321 A B t R x) = (term322 A B t R x).
Proof. exact (fun_ext (fun y : B => @lem7162053 A B y t R x)). Qed.
Lemma lem7162055 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem7162056 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term314 A B t R x) = (term323 A B t R x).
Proof. exact (MK_COMB (@lem7162055 B) (@lem7162054 A B t R x)). Qed.
Lemma lem7162057 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : ((term313 A B t R x) = (term314 A B t R x)) = ((term307 A B t R x) = (term323 A B t R x)).
Proof. exact (MK_COMB (@lem7162048 A B t R x) (@lem7162056 A B t R x)). Qed.
Lemma lem7162058 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term307 A B t R x) = (term323 A B t R x).
Proof. exact (EQ_MP (@lem7162057 A B t R x) (@lem7162038 A B t R x)). Qed.
Lemma lem7162059 {A : Type'} (x : A) (s : A -> Prop) : (term286 A x s) = (term286 A x s).
Proof. exact (eq_refl (term286 A x s)). Qed.
Lemma lem7162060 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term308 A B s t R x) = (term324 A B s t R x).
Proof. exact (MK_COMB (@lem7162059 A x s) (@lem7162058 A B t R x)). Qed.
Lemma lem7162062 {A : Type'} (P : Prop) (Q : A -> Prop) : (term325 A P Q) = (term326 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem7162063 {B : Type'} (P : Prop) (Q : B -> Prop) : (term325 B P Q) = (term326 B P Q).
Proof. exact (@lem7162062 B P Q). Qed.
Lemma lem7162064 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term327 A B s t R x) = (term328 A B s t R x).
Proof. exact (@lem7162063 B (term329 A x s) (term322 A B t R x)). Qed.
Lemma lem7162065 {A B : Type'} (y : B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term330 A B t R x y) = (term320 A B y t R x).
Proof. exact (eq_refl (term330 A B t R x y)). Qed.
Lemma lem7162066 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term331 A B t R x) = (term322 A B t R x).
Proof. exact (fun_ext (fun y : B => @lem7162065 A B y t R x)). Qed.
Lemma lem7162067 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem7162068 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term332 A B t R x) = (term323 A B t R x).
Proof. exact (MK_COMB (@lem7162067 B) (@lem7162066 A B t R x)). Qed.
Lemma lem7162069 {A : Type'} (x : A) (s : A -> Prop) : (term286 A x s) = (term286 A x s).
Proof. exact (eq_refl (term286 A x s)). Qed.
Lemma lem7162070 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term327 A B s t R x) = (term324 A B s t R x).
Proof. exact (MK_COMB (@lem7162069 A x s) (@lem7162068 A B t R x)). Qed.
Lemma lem7162071 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7162072 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term333 A B s t R x) = (term334 A B s t R x).
Proof. exact (MK_COMB (@lem7162071) (@lem7162070 A B s t R x)). Qed.
Lemma lem7162073 {A B : Type'} (y : B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term330 A B t R x y) = (term320 A B y t R x).
Proof. exact (eq_refl (term330 A B t R x y)). Qed.
Lemma lem7162074 {A : Type'} (x : A) (s : A -> Prop) : (term286 A x s) = (term286 A x s).
Proof. exact (eq_refl (term286 A x s)). Qed.
Lemma lem7162075 {A B : Type'} (s : A -> Prop) (y : B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term335 A B s t R x y) = (term336 A B s y t R x).
Proof. exact (MK_COMB (@lem7162074 A x s) (@lem7162073 A B y t R x)). Qed.
Lemma lem7162076 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term337 A B s t R x) = (term338 A B s t R x).
Proof. exact (fun_ext (fun y : B => @lem7162075 A B s y t R x)). Qed.
Lemma lem7162077 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem7162078 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term328 A B s t R x) = (term339 A B s t R x).
Proof. exact (MK_COMB (@lem7162077 B) (@lem7162076 A B s t R x)). Qed.
Lemma lem7162079 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : ((term327 A B s t R x) = (term328 A B s t R x)) = ((term324 A B s t R x) = (term339 A B s t R x)).
Proof. exact (MK_COMB (@lem7162072 A B s t R x) (@lem7162078 A B s t R x)). Qed.
Lemma lem7162080 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term324 A B s t R x) = (term339 A B s t R x).
Proof. exact (EQ_MP (@lem7162079 A B s t R x) (@lem7162064 A B s t R x)). Qed.
Lemma lem7162081 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term308 A B s t R x) = (term339 A B s t R x).
Proof. exact (TRANS (@lem7162060 A B s t R x) (@lem7162080 A B s t R x)). Qed.
Lemma lem7162082 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term309 A B s t R) = (term340 A B s t R).
Proof. exact (fun_ext (fun x : A => @lem7162081 A B s t R x)). Qed.
Lemma lem7162083 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7162084 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term310 A B s t R) = (term341 A B s t R).
Proof. exact (MK_COMB (@lem7162083 A) (@lem7162082 A B s t R)). Qed.
Lemma lem7162086 {A B : Type'} (P : type1413 A B) : (term342 A B P) = (term343 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7162087 {A B : Type'} (P : type1413 A B) : (term342 A B P) = (term343 A B P).
Proof. exact (@lem7162086 A B P). Qed.
Lemma lem7162088 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term344 A B s t R) = (term345 A B s t R).
Proof. exact (@lem7162087 A B (term346 A B s t R)). Qed.
Lemma lem7162089 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term347 A B s t R x) = (term338 A B s t R x).
Proof. exact (eq_refl (term347 A B s t R x)). Qed.
Lemma lem7162090 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem7162091 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term348 A B s t R x y) = (term349 A B s t R x y).
Proof. exact (MK_COMB (@lem7162089 A B s t R x) (@lem7162090 B y)). Qed.
Lemma lem7162092 {A B : Type'} (s : A -> Prop) (y : B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term349 A B s t R x y) = (term336 A B s y t R x).
Proof. exact (eq_refl (term349 A B s t R x y)). Qed.
Lemma lem7162093 {A B : Type'} (s : A -> Prop) (y : B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term348 A B s t R x y) = (term336 A B s y t R x).
Proof. exact (TRANS (@lem7162091 A B s t R x y) (@lem7162092 A B s y t R x)). Qed.
Lemma lem7162094 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term350 A B s t R x) = (term338 A B s t R x).
Proof. exact (fun_ext (fun y : B => @lem7162093 A B s y t R x)). Qed.
Lemma lem7162095 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem7162096 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term351 A B s t R x) = (term339 A B s t R x).
Proof. exact (MK_COMB (@lem7162095 B) (@lem7162094 A B s t R x)). Qed.
Lemma lem7162097 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term352 A B s t R) = (term340 A B s t R).
Proof. exact (fun_ext (fun x : A => @lem7162096 A B s t R x)). Qed.
Lemma lem7162098 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7162099 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term344 A B s t R) = (term341 A B s t R).
Proof. exact (MK_COMB (@lem7162098 A) (@lem7162097 A B s t R)). Qed.
Lemma lem7162100 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7162101 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term353 A B s t R) = (term354 A B s t R).
Proof. exact (MK_COMB (@lem7162100) (@lem7162099 A B s t R)). Qed.
Lemma lem7162102 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term347 A B s t R x) = (term338 A B s t R x).
Proof. exact (eq_refl (term347 A B s t R x)). Qed.
Lemma lem7162103 {A B : Type'} (y : A -> B) (x : A) : (y x) = (y x).
Proof. exact (eq_refl (y x)). Qed.
Lemma lem7162104 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (y : A -> B) (x : A) : (term355 A B s t R y x) = (term356 A B s t R y x).
Proof. exact (MK_COMB (@lem7162102 A B s t R x) (@lem7162103 A B y x)). Qed.
Lemma lem7162105 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term356 A B s t R y x) = (term357 A B s y t R x).
Proof. exact (eq_refl (term356 A B s t R y x)). Qed.
Lemma lem7162106 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term355 A B s t R y x) = (term357 A B s y t R x).
Proof. exact (TRANS (@lem7162104 A B s t R y x) (@lem7162105 A B s y t R x)). Qed.
Lemma lem7162107 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) : (term358 A B s t R y) = (term359 A B s y t R).
Proof. exact (fun_ext (fun x : A => @lem7162106 A B s y t R x)). Qed.
Lemma lem7162108 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7162109 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) : (term360 A B s t R y) = (term361 A B s y t R).
Proof. exact (MK_COMB (@lem7162108 A) (@lem7162107 A B s y t R)). Qed.
Lemma lem7162110 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term362 A B s t R) = (term363 A B s t R).
Proof. exact (fun_ext (fun y : A -> B => @lem7162109 A B s y t R)). Qed.
Lemma lem7162111 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem7162112 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term345 A B s t R) = (term364 A B s t R).
Proof. exact (MK_COMB (@lem7162111 A B) (@lem7162110 A B s t R)). Qed.
Lemma lem7162113 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : ((term344 A B s t R) = (term345 A B s t R)) = ((term341 A B s t R) = (term364 A B s t R)).
Proof. exact (MK_COMB (@lem7162101 A B s t R) (@lem7162112 A B s t R)). Qed.
Lemma lem7162114 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term341 A B s t R) = (term364 A B s t R).
Proof. exact (EQ_MP (@lem7162113 A B s t R) (@lem7162088 A B s t R)). Qed.
Lemma lem7162115 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term310 A B s t R) = (term364 A B s t R).
Proof. exact (TRANS (@lem7162084 A B s t R) (@lem7162114 A B s t R)). Qed.
Lemma lem7162116 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term290 A B s t R) = (term364 A B s t R).
Proof. exact (TRANS (@lem7161986 A B s t R) (@lem7162115 A B s t R)). Qed.
Lemma lem7162117 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term34 A B s t R) = (term364 A B s t R).
Proof. exact (TRANS (@lem7161760 A B s t R) (@lem7162116 A B s t R)). Qed.
Lemma lem7162118 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (h1 : term34 A B s t R) : term364 A B s t R.
Proof. exact (EQ_MP (@lem7162117 A B s t R) (@lem7161492 A B s t R h1)). Qed.
Lemma lem7162124 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem7162130 {A B : Type'} (_95867 : type830 A B) (R : type1413 A B) (x : A) (t : B -> Prop) (h1 : term226 A B _95867 R x t) : term226 A B _95867 R x t.
Proof. exact (h1). Qed.
Lemma lem7162131 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (h1 : term361 A B s y t R) : term361 A B s y t R.
Proof. exact (h1). Qed.
Lemma lem7162142 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7162143 {A B : Type'} (f : type830 A B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> (A -> B -> Prop) -> A -> B) f x).
Proof. exact (@lem7162142 (B -> Prop) (type467 A B) f x). Qed.
Lemma lem7162144 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) : (_95867 t) = (@I ((B -> Prop) -> (A -> B -> Prop) -> A -> B) _95867 t).
Proof. exact (@lem7162143 A B _95867 t). Qed.
Lemma lem7162145 {A B : Type'} (R : type1413 A B) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem7162146 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (_95867 t R) = (@I ((B -> Prop) -> (A -> B -> Prop) -> A -> B) _95867 t R).
Proof. exact (MK_COMB (@lem7162144 A B _95867 t) (@lem7162145 A B R)). Qed.
Lemma lem7162148 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7162149 {A B : Type'} (f : type467 A B) (x : type1413 A B) : (f x) = (@I ((A -> B -> Prop) -> A -> B) f x).
Proof. exact (@lem7162148 (type1413 A B) (A -> B) f x). Qed.
Lemma lem7162150 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (@I ((B -> Prop) -> (A -> B -> Prop) -> A -> B) _95867 t R) = (term365 A B _95867 t R).
Proof. exact (@lem7162149 A B (@I ((B -> Prop) -> (A -> B -> Prop) -> A -> B) _95867 t) R). Qed.
Lemma lem7162151 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (_95867 t R) = (term365 A B _95867 t R).
Proof. exact (TRANS (@lem7162146 A B _95867 t R) (@lem7162150 A B _95867 t R)). Qed.
Lemma lem7162152 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7162153 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (_95867 t R x) = (term366 A B _95867 t R x).
Proof. exact (MK_COMB (@lem7162151 A B _95867 t R) (@lem7162152 A x)). Qed.
Lemma lem7162155 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7162156 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem7162155 A B f x). Qed.
Lemma lem7162157 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term366 A B _95867 t R x) = (term367 A B _95867 t R x).
Proof. exact (@lem7162156 A B (term365 A B _95867 t R) x). Qed.
Lemma lem7162159 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (_95867 t R x) = (term367 A B _95867 t R x).
Proof. exact (TRANS (@lem7162153 A B _95867 t R x) (@lem7162157 A B _95867 t R x)). Qed.
Lemma lem7162160 {A B : Type'} (R : type1413 A B) (x : A) : (R x) = (R x).
Proof. exact (eq_refl (R x)). Qed.
Lemma lem7162161 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term161 A B _95867 t R x) = (term368 A B _95867 t R x).
Proof. exact (MK_COMB (@lem7162160 A B R x) (@lem7162159 A B _95867 t R x)). Qed.
Lemma lem7162163 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7162164 {A B : Type'} (f : type1413 A B) (x : A) : (f x) = (@I (A -> B -> Prop) f x).
Proof. exact (@lem7162163 A (B -> Prop) f x). Qed.
Lemma lem7162165 {A B : Type'} (R : type1413 A B) (x : A) : (R x) = (@I (A -> B -> Prop) R x).
Proof. exact (@lem7162164 A B R x). Qed.
Lemma lem7162166 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term367 A B _95867 t R x) = (term367 A B _95867 t R x).
Proof. exact (eq_refl (term367 A B _95867 t R x)). Qed.
Lemma lem7162167 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term368 A B _95867 t R x) = (term369 A B _95867 t R x).
Proof. exact (MK_COMB (@lem7162165 A B R x) (@lem7162166 A B _95867 t R x)). Qed.
Lemma lem7162169 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7162170 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem7162169 B Prop f x). Qed.
Lemma lem7162171 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term369 A B _95867 t R x) = (term370 A B _95867 t R x).
Proof. exact (@lem7162170 B (@I (A -> B -> Prop) R x) (term367 A B _95867 t R x)). Qed.
Lemma lem7162172 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term368 A B _95867 t R x) = (term370 A B _95867 t R x).
Proof. exact (TRANS (@lem7162167 A B _95867 t R x) (@lem7162171 A B _95867 t R x)). Qed.
Lemma lem7162173 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term161 A B _95867 t R x) = (term370 A B _95867 t R x).
Proof. exact (TRANS (@lem7162161 A B _95867 t R x) (@lem7162172 A B _95867 t R x)). Qed.
Lemma lem7162174 {B : Type'} : (@IN B) = (@IN B).
Proof. exact (eq_refl (@IN B)). Qed.
Lemma lem7162183 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7162184 {A B : Type'} (f : type830 A B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> (A -> B -> Prop) -> A -> B) f x).
Proof. exact (@lem7162183 (B -> Prop) (type467 A B) f x). Qed.
Lemma lem7162185 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) : (_95867 t) = (@I ((B -> Prop) -> (A -> B -> Prop) -> A -> B) _95867 t).
Proof. exact (@lem7162184 A B _95867 t). Qed.
Lemma lem7162186 {A B : Type'} (R : type1413 A B) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem7162187 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (_95867 t R) = (@I ((B -> Prop) -> (A -> B -> Prop) -> A -> B) _95867 t R).
Proof. exact (MK_COMB (@lem7162185 A B _95867 t) (@lem7162186 A B R)). Qed.
Lemma lem7162189 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7162190 {A B : Type'} (f : type467 A B) (x : type1413 A B) : (f x) = (@I ((A -> B -> Prop) -> A -> B) f x).
Proof. exact (@lem7162189 (type1413 A B) (A -> B) f x). Qed.
Lemma lem7162191 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (@I ((B -> Prop) -> (A -> B -> Prop) -> A -> B) _95867 t R) = (term365 A B _95867 t R).
Proof. exact (@lem7162190 A B (@I ((B -> Prop) -> (A -> B -> Prop) -> A -> B) _95867 t) R). Qed.
Lemma lem7162192 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (_95867 t R) = (term365 A B _95867 t R).
Proof. exact (TRANS (@lem7162187 A B _95867 t R) (@lem7162191 A B _95867 t R)). Qed.
Lemma lem7162193 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7162194 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (_95867 t R x) = (term366 A B _95867 t R x).
Proof. exact (MK_COMB (@lem7162192 A B _95867 t R) (@lem7162193 A x)). Qed.
Lemma lem7162196 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7162197 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem7162196 A B f x). Qed.
Lemma lem7162198 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term366 A B _95867 t R x) = (term367 A B _95867 t R x).
Proof. exact (@lem7162197 A B (term365 A B _95867 t R) x). Qed.
Lemma lem7162200 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (_95867 t R x) = (term367 A B _95867 t R x).
Proof. exact (TRANS (@lem7162194 A B _95867 t R x) (@lem7162198 A B _95867 t R x)). Qed.
Lemma lem7162201 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem7162202 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term156 A B _95867 t R x) = (term371 A B _95867 t R x).
Proof. exact (MK_COMB (@lem7162174 B) (@lem7162200 A B _95867 t R x)). Qed.
Lemma lem7162203 {A B : Type'} (_95867 : type830 A B) (R : type1413 A B) (x : A) (t : B -> Prop) : (term157 A B _95867 R x t) = (term372 A B _95867 R x t).
Proof. exact (MK_COMB (@lem7162202 A B _95867 t R x) (@lem7162201 B t)). Qed.
Lemma lem7162205 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7162206 {B : Type'} (f : type1364 B) (x : B) : (f x) = (@I (B -> (B -> Prop) -> Prop) f x).
Proof. exact (@lem7162205 B (type686 B) f x). Qed.
Lemma lem7162207 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term371 A B _95867 t R x) = (term373 A B _95867 t R x).
Proof. exact (@lem7162206 B (@IN B) (term367 A B _95867 t R x)). Qed.
Lemma lem7162208 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem7162209 {A B : Type'} (_95867 : type830 A B) (R : type1413 A B) (x : A) (t : B -> Prop) : (term372 A B _95867 R x t) = (term374 A B _95867 R x t).
Proof. exact (MK_COMB (@lem7162207 A B _95867 t R x) (@lem7162208 B t)). Qed.
Lemma lem7162211 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7162212 {B : Type'} (f : type686 B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> Prop) f x).
Proof. exact (@lem7162211 (B -> Prop) Prop f x). Qed.
Lemma lem7162213 {A B : Type'} (_95867 : type830 A B) (R : type1413 A B) (x : A) (t : B -> Prop) : (term374 A B _95867 R x t) = (term375 A B _95867 R x t).
Proof. exact (@lem7162212 B (term373 A B _95867 t R x) t). Qed.
Lemma lem7162214 {A B : Type'} (_95867 : type830 A B) (R : type1413 A B) (x : A) (t : B -> Prop) : (term372 A B _95867 R x t) = (term375 A B _95867 R x t).
Proof. exact (TRANS (@lem7162209 A B _95867 R x t) (@lem7162213 A B _95867 R x t)). Qed.
Lemma lem7162215 {A B : Type'} (_95867 : type830 A B) (R : type1413 A B) (x : A) (t : B -> Prop) : (term157 A B _95867 R x t) = (term375 A B _95867 R x t).
Proof. exact (TRANS (@lem7162203 A B _95867 R x t) (@lem7162214 A B _95867 R x t)). Qed.
Lemma lem7162216 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7162217 {A B : Type'} (_95867 : type830 A B) (R : type1413 A B) (x : A) (t : B -> Prop) : (term159 A B _95867 R x t) = (term376 A B _95867 R x t).
Proof. exact (MK_COMB (@lem7162216) (@lem7162215 A B _95867 R x t)). Qed.
Lemma lem7162218 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term162 A B _95867 t R x) = (term377 A B _95867 t R x).
Proof. exact (MK_COMB (@lem7162217 A B _95867 R x t) (@lem7162173 A B _95867 t R x)). Qed.
Lemma lem7162219 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7162226 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7162227 {A B : Type'} (f : type1413 A B) (x : A) : (f x) = (@I (A -> B -> Prop) f x).
Proof. exact (@lem7162226 A (B -> Prop) f x). Qed.
Lemma lem7162228 {A B : Type'} (R : type1413 A B) (x : A) : (R x) = (@I (A -> B -> Prop) R x).
Proof. exact (@lem7162227 A B R x). Qed.
Lemma lem7162229 {B : Type'} (x : B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7162230 {A B : Type'} (R : type1413 A B) (x : A) (x' : B) : (R x x') = (@I (A -> B -> Prop) R x x').
Proof. exact (MK_COMB (@lem7162228 A B R x) (@lem7162229 B x')). Qed.
Lemma lem7162232 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7162233 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem7162232 B Prop f x). Qed.
Lemma lem7162234 {A B : Type'} (R : type1413 A B) (x : A) (x' : B) : (@I (A -> B -> Prop) R x x') = (term378 A B R x x').
Proof. exact (@lem7162233 B (@I (A -> B -> Prop) R x) x'). Qed.
Lemma lem7162236 {A B : Type'} (R : type1413 A B) (x : A) (x' : B) : (R x x') = (term378 A B R x x').
Proof. exact (TRANS (@lem7162230 A B R x x') (@lem7162234 A B R x x')). Qed.
Lemma lem7162237 {A B : Type'} (R : type1413 A B) (x : A) (x' : B) : (term379 A B R x x') = (term380 A B R x x').
Proof. exact (MK_COMB (@lem7162219) (@lem7162236 A B R x x')). Qed.
Lemma lem7162238 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7162245 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7162246 {B : Type'} (f : type1364 B) (x : B) : (f x) = (@I (B -> (B -> Prop) -> Prop) f x).
Proof. exact (@lem7162245 B (type686 B) f x). Qed.
Lemma lem7162247 {B : Type'} (x : B) : (@IN B x) = (@I (B -> (B -> Prop) -> Prop) (@IN B) x).
Proof. exact (@lem7162246 B (@IN B) x). Qed.
Lemma lem7162248 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem7162249 {B : Type'} (x : B) (t : B -> Prop) : (@IN B x t) = (@I (B -> (B -> Prop) -> Prop) (@IN B) x t).
Proof. exact (MK_COMB (@lem7162247 B x) (@lem7162248 B t)). Qed.
Lemma lem7162251 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7162252 {B : Type'} (f : type686 B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> Prop) f x).
Proof. exact (@lem7162251 (B -> Prop) Prop f x). Qed.
Lemma lem7162253 {B : Type'} (x : B) (t : B -> Prop) : (@I (B -> (B -> Prop) -> Prop) (@IN B) x t) = (term381 B x t).
Proof. exact (@lem7162252 B (@I (B -> (B -> Prop) -> Prop) (@IN B) x) t). Qed.
Lemma lem7162255 {B : Type'} (x : B) (t : B -> Prop) : (@IN B x t) = (term381 B x t).
Proof. exact (TRANS (@lem7162249 B x t) (@lem7162253 B x t)). Qed.
Lemma lem7162256 {B : Type'} (x : B) (t : B -> Prop) : (term329 B x t) = (term382 B x t).
Proof. exact (MK_COMB (@lem7162238) (@lem7162255 B x t)). Qed.
Lemma lem7162257 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7162258 {B : Type'} (x : B) (t : B -> Prop) : (term286 B x t) = (term383 B x t).
Proof. exact (MK_COMB (@lem7162257) (@lem7162256 B x t)). Qed.
Lemma lem7162259 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term228 A B t R x x') = (term384 A B t R x x').
Proof. exact (MK_COMB (@lem7162258 B x' t) (@lem7162237 A B R x x')). Qed.
Lemma lem7162260 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term245 A B t R x) = (term385 A B t R x).
Proof. exact (fun_ext (fun x' : B => @lem7162259 A B t R x x')). Qed.
Lemma lem7162261 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7162262 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term254 A B t R x) = (term386 A B t R x).
Proof. exact (MK_COMB (@lem7162261 B) (@lem7162260 A B t R x)). Qed.
Lemma lem7162263 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7162264 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term256 A B t R x) = (term387 A B t R x).
Proof. exact (MK_COMB (@lem7162263) (@lem7162262 A B t R x)). Qed.
Lemma lem7162265 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term257 A B _95867 t R x) = (term388 A B _95867 t R x).
Proof. exact (MK_COMB (@lem7162264 A B t R x) (@lem7162218 A B _95867 t R x)). Qed.
Lemma lem7162266 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (term258 A B _95867 t R) = (term389 A B _95867 t R).
Proof. exact (fun_ext (fun x : A => @lem7162265 A B _95867 t R x)). Qed.
Lemma lem7162267 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7162268 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (term259 A B _95867 t R) = (term390 A B _95867 t R).
Proof. exact (MK_COMB (@lem7162267 A) (@lem7162266 A B _95867 t R)). Qed.
Lemma lem7162269 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) : (term260 A B _95867 t) = (term391 A B _95867 t).
Proof. exact (fun_ext (fun R : type1413 A B => @lem7162268 A B _95867 t R)). Qed.
Lemma lem7162270 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem7162271 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) : (term261 A B _95867 t) = (term392 A B _95867 t).
Proof. exact (MK_COMB (@lem7162270 A B) (@lem7162269 A B _95867 t)). Qed.
Lemma lem7162272 {A B : Type'} (_95867 : type830 A B) : (term262 A B _95867) = (term393 A B _95867).
Proof. exact (fun_ext (fun t : B -> Prop => @lem7162271 A B _95867 t)). Qed.
Lemma lem7162273 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem7162274 {A B : Type'} (_95867 : type830 A B) : (term263 A B _95867) = (term394 A B _95867).
Proof. exact (MK_COMB (@lem7162273 B) (@lem7162272 A B _95867)). Qed.
Lemma lem7162275 {A B : Type'} (_95867 : type830 A B) (h1 : term174 A B _95867) : term394 A B _95867.
Proof. exact (EQ_MP (@lem7162274 A B _95867) (@lem7161700 A B _95867 h1)). Qed.
Lemma lem7162291 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7162292 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem7162291 A (type686 A) f x). Qed.
Lemma lem7162293 {A : Type'} (x : A) : (@IN A x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x).
Proof. exact (@lem7162292 A (@IN A) x). Qed.
Lemma lem7162294 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7162295 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x s).
Proof. exact (MK_COMB (@lem7162293 A x) (@lem7162294 A s)). Qed.
Lemma lem7162297 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7162298 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem7162297 (A -> Prop) Prop f x). Qed.
Lemma lem7162299 {A : Type'} (x : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x s) = (term381 A x s).
Proof. exact (@lem7162298 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x) s). Qed.
Lemma lem7162301 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (term381 A x s).
Proof. exact (TRANS (@lem7162295 A x s) (@lem7162299 A x s)). Qed.
Lemma lem7162303 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7162304 {B : Type'} : (@IN B) = (@IN B).
Proof. exact (eq_refl (@IN B)). Qed.
Lemma lem7162313 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7162314 {A B : Type'} (f : type830 A B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> (A -> B -> Prop) -> A -> B) f x).
Proof. exact (@lem7162313 (B -> Prop) (type467 A B) f x). Qed.
Lemma lem7162315 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) : (_95867 t) = (@I ((B -> Prop) -> (A -> B -> Prop) -> A -> B) _95867 t).
Proof. exact (@lem7162314 A B _95867 t). Qed.
Lemma lem7162316 {A B : Type'} (R : type1413 A B) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem7162317 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (_95867 t R) = (@I ((B -> Prop) -> (A -> B -> Prop) -> A -> B) _95867 t R).
Proof. exact (MK_COMB (@lem7162315 A B _95867 t) (@lem7162316 A B R)). Qed.
Lemma lem7162319 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7162320 {A B : Type'} (f : type467 A B) (x : type1413 A B) : (f x) = (@I ((A -> B -> Prop) -> A -> B) f x).
Proof. exact (@lem7162319 (type1413 A B) (A -> B) f x). Qed.
Lemma lem7162321 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (@I ((B -> Prop) -> (A -> B -> Prop) -> A -> B) _95867 t R) = (term365 A B _95867 t R).
Proof. exact (@lem7162320 A B (@I ((B -> Prop) -> (A -> B -> Prop) -> A -> B) _95867 t) R). Qed.
Lemma lem7162322 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (_95867 t R) = (term365 A B _95867 t R).
Proof. exact (TRANS (@lem7162317 A B _95867 t R) (@lem7162321 A B _95867 t R)). Qed.
Lemma lem7162323 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7162324 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (_95867 t R x) = (term366 A B _95867 t R x).
Proof. exact (MK_COMB (@lem7162322 A B _95867 t R) (@lem7162323 A x)). Qed.
Lemma lem7162326 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7162327 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem7162326 A B f x). Qed.
Lemma lem7162328 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term366 A B _95867 t R x) = (term367 A B _95867 t R x).
Proof. exact (@lem7162327 A B (term365 A B _95867 t R) x). Qed.
Lemma lem7162330 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (_95867 t R x) = (term367 A B _95867 t R x).
Proof. exact (TRANS (@lem7162324 A B _95867 t R x) (@lem7162328 A B _95867 t R x)). Qed.
Lemma lem7162331 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem7162332 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term156 A B _95867 t R x) = (term371 A B _95867 t R x).
Proof. exact (MK_COMB (@lem7162304 B) (@lem7162330 A B _95867 t R x)). Qed.
Lemma lem7162333 {A B : Type'} (_95867 : type830 A B) (R : type1413 A B) (x : A) (t : B -> Prop) : (term157 A B _95867 R x t) = (term372 A B _95867 R x t).
Proof. exact (MK_COMB (@lem7162332 A B _95867 t R x) (@lem7162331 B t)). Qed.
Lemma lem7162335 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7162336 {B : Type'} (f : type1364 B) (x : B) : (f x) = (@I (B -> (B -> Prop) -> Prop) f x).
Proof. exact (@lem7162335 B (type686 B) f x). Qed.
Lemma lem7162337 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term371 A B _95867 t R x) = (term373 A B _95867 t R x).
Proof. exact (@lem7162336 B (@IN B) (term367 A B _95867 t R x)). Qed.
Lemma lem7162338 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem7162339 {A B : Type'} (_95867 : type830 A B) (R : type1413 A B) (x : A) (t : B -> Prop) : (term372 A B _95867 R x t) = (term374 A B _95867 R x t).
Proof. exact (MK_COMB (@lem7162337 A B _95867 t R x) (@lem7162338 B t)). Qed.
Lemma lem7162341 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7162342 {B : Type'} (f : type686 B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> Prop) f x).
Proof. exact (@lem7162341 (B -> Prop) Prop f x). Qed.
Lemma lem7162343 {A B : Type'} (_95867 : type830 A B) (R : type1413 A B) (x : A) (t : B -> Prop) : (term374 A B _95867 R x t) = (term375 A B _95867 R x t).
Proof. exact (@lem7162342 B (term373 A B _95867 t R x) t). Qed.
Lemma lem7162344 {A B : Type'} (_95867 : type830 A B) (R : type1413 A B) (x : A) (t : B -> Prop) : (term372 A B _95867 R x t) = (term375 A B _95867 R x t).
Proof. exact (TRANS (@lem7162339 A B _95867 R x t) (@lem7162343 A B _95867 R x t)). Qed.
Lemma lem7162345 {A B : Type'} (_95867 : type830 A B) (R : type1413 A B) (x : A) (t : B -> Prop) : (term157 A B _95867 R x t) = (term375 A B _95867 R x t).
Proof. exact (TRANS (@lem7162333 A B _95867 R x t) (@lem7162344 A B _95867 R x t)). Qed.
Lemma lem7162346 {A B : Type'} (_95867 : type830 A B) (R : type1413 A B) (x : A) (t : B -> Prop) : (term226 A B _95867 R x t) = (term395 A B _95867 R x t).
Proof. exact (MK_COMB (@lem7162303) (@lem7162345 A B _95867 R x t)). Qed.
Lemma lem7162352 {B : Type'} (y' : B) (y : B) : (y' = y) = (y' = y).
Proof. exact (eq_refl (y' = y)). Qed.
Lemma lem7162353 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7162360 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7162361 {A B : Type'} (f : type1413 A B) (x : A) : (f x) = (@I (A -> B -> Prop) f x).
Proof. exact (@lem7162360 A (B -> Prop) f x). Qed.
Lemma lem7162362 {A B : Type'} (R : type1413 A B) (x : A) : (R x) = (@I (A -> B -> Prop) R x).
Proof. exact (@lem7162361 A B R x). Qed.
Lemma lem7162363 {B : Type'} (y' : B) : y' = y'.
Proof. exact (eq_refl y'). Qed.
Lemma lem7162364 {A B : Type'} (R : type1413 A B) (x : A) (y' : B) : (R x y') = (@I (A -> B -> Prop) R x y').
Proof. exact (MK_COMB (@lem7162362 A B R x) (@lem7162363 B y')). Qed.
Lemma lem7162366 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7162367 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem7162366 B Prop f x). Qed.
Lemma lem7162368 {A B : Type'} (R : type1413 A B) (x : A) (y' : B) : (@I (A -> B -> Prop) R x y') = (term378 A B R x y').
Proof. exact (@lem7162367 B (@I (A -> B -> Prop) R x) y'). Qed.
Lemma lem7162370 {A B : Type'} (R : type1413 A B) (x : A) (y' : B) : (R x y') = (term378 A B R x y').
Proof. exact (TRANS (@lem7162364 A B R x y') (@lem7162368 A B R x y')). Qed.
Lemma lem7162371 {A B : Type'} (R : type1413 A B) (x : A) (y' : B) : (term379 A B R x y') = (term380 A B R x y').
Proof. exact (MK_COMB (@lem7162353) (@lem7162370 A B R x y')). Qed.
Lemma lem7162372 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7162379 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7162380 {B : Type'} (f : type1364 B) (x : B) : (f x) = (@I (B -> (B -> Prop) -> Prop) f x).
Proof. exact (@lem7162379 B (type686 B) f x). Qed.
Lemma lem7162381 {B : Type'} (y' : B) : (@IN B y') = (@I (B -> (B -> Prop) -> Prop) (@IN B) y').
Proof. exact (@lem7162380 B (@IN B) y'). Qed.
Lemma lem7162382 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem7162383 {B : Type'} (y' : B) (t : B -> Prop) : (@IN B y' t) = (@I (B -> (B -> Prop) -> Prop) (@IN B) y' t).
Proof. exact (MK_COMB (@lem7162381 B y') (@lem7162382 B t)). Qed.
Lemma lem7162385 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7162386 {B : Type'} (f : type686 B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> Prop) f x).
Proof. exact (@lem7162385 (B -> Prop) Prop f x). Qed.
Lemma lem7162387 {B : Type'} (y' : B) (t : B -> Prop) : (@I (B -> (B -> Prop) -> Prop) (@IN B) y' t) = (term381 B y' t).
Proof. exact (@lem7162386 B (@I (B -> (B -> Prop) -> Prop) (@IN B) y') t). Qed.
Lemma lem7162389 {B : Type'} (y' : B) (t : B -> Prop) : (@IN B y' t) = (term381 B y' t).
Proof. exact (TRANS (@lem7162383 B y' t) (@lem7162387 B y' t)). Qed.
Lemma lem7162390 {B : Type'} (y' : B) (t : B -> Prop) : (term329 B y' t) = (term382 B y' t).
Proof. exact (MK_COMB (@lem7162372) (@lem7162389 B y' t)). Qed.
Lemma lem7162391 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7162392 {B : Type'} (y' : B) (t : B -> Prop) : (term286 B y' t) = (term383 B y' t).
Proof. exact (MK_COMB (@lem7162391) (@lem7162390 B y' t)). Qed.
Lemma lem7162393 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term228 A B t R x y') = (term384 A B t R x y').
Proof. exact (MK_COMB (@lem7162392 B y' t) (@lem7162371 A B R x y')). Qed.
Lemma lem7162394 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7162395 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term230 A B t R x y') = (term396 A B t R x y').
Proof. exact (MK_COMB (@lem7162394) (@lem7162393 A B t R x y')). Qed.
Lemma lem7162396 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y : B) : (term269 A B t R x y' y) = (term397 A B t R x y' y).
Proof. exact (MK_COMB (@lem7162395 A B t R x y') (@lem7162352 B y' y)). Qed.
Lemma lem7162397 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term295 A B t R x y) = (term398 A B t R x y).
Proof. exact (fun_ext (fun y' : B => @lem7162396 A B t R x y' y)). Qed.
Lemma lem7162398 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7162399 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term303 A B t R x y) = (term399 A B t R x y).
Proof. exact (MK_COMB (@lem7162398 B) (@lem7162397 A B t R x y)). Qed.
Lemma lem7162400 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7162407 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7162408 {A B : Type'} (f : type1413 A B) (x : A) : (f x) = (@I (A -> B -> Prop) f x).
Proof. exact (@lem7162407 A (B -> Prop) f x). Qed.
Lemma lem7162409 {A B : Type'} (R : type1413 A B) (x : A) : (R x) = (@I (A -> B -> Prop) R x).
Proof. exact (@lem7162408 A B R x). Qed.
Lemma lem7162410 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem7162411 {A B : Type'} (R : type1413 A B) (x : A) (y : B) : (R x y) = (@I (A -> B -> Prop) R x y).
Proof. exact (MK_COMB (@lem7162409 A B R x) (@lem7162410 B y)). Qed.
Lemma lem7162413 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7162414 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem7162413 B Prop f x). Qed.
Lemma lem7162415 {A B : Type'} (R : type1413 A B) (x : A) (y : B) : (@I (A -> B -> Prop) R x y) = (term378 A B R x y).
Proof. exact (@lem7162414 B (@I (A -> B -> Prop) R x) y). Qed.
Lemma lem7162417 {A B : Type'} (R : type1413 A B) (x : A) (y : B) : (R x y) = (term378 A B R x y).
Proof. exact (TRANS (@lem7162411 A B R x y) (@lem7162415 A B R x y)). Qed.
Lemma lem7162418 {A B : Type'} (R : type1413 A B) (x : A) (y : B) : (term379 A B R x y) = (term380 A B R x y).
Proof. exact (MK_COMB (@lem7162400) (@lem7162417 A B R x y)). Qed.
Lemma lem7162419 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7162426 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7162427 {B : Type'} (f : type1364 B) (x : B) : (f x) = (@I (B -> (B -> Prop) -> Prop) f x).
Proof. exact (@lem7162426 B (type686 B) f x). Qed.
Lemma lem7162428 {B : Type'} (y : B) : (@IN B y) = (@I (B -> (B -> Prop) -> Prop) (@IN B) y).
Proof. exact (@lem7162427 B (@IN B) y). Qed.
Lemma lem7162429 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem7162430 {B : Type'} (y : B) (t : B -> Prop) : (@IN B y t) = (@I (B -> (B -> Prop) -> Prop) (@IN B) y t).
Proof. exact (MK_COMB (@lem7162428 B y) (@lem7162429 B t)). Qed.
Lemma lem7162432 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7162433 {B : Type'} (f : type686 B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> Prop) f x).
Proof. exact (@lem7162432 (B -> Prop) Prop f x). Qed.
Lemma lem7162434 {B : Type'} (y : B) (t : B -> Prop) : (@I (B -> (B -> Prop) -> Prop) (@IN B) y t) = (term381 B y t).
Proof. exact (@lem7162433 B (@I (B -> (B -> Prop) -> Prop) (@IN B) y) t). Qed.
Lemma lem7162436 {B : Type'} (y : B) (t : B -> Prop) : (@IN B y t) = (term381 B y t).
Proof. exact (TRANS (@lem7162430 B y t) (@lem7162434 B y t)). Qed.
Lemma lem7162437 {B : Type'} (y : B) (t : B -> Prop) : (term329 B y t) = (term382 B y t).
Proof. exact (MK_COMB (@lem7162419) (@lem7162436 B y t)). Qed.
Lemma lem7162438 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7162439 {B : Type'} (y : B) (t : B -> Prop) : (term286 B y t) = (term383 B y t).
Proof. exact (MK_COMB (@lem7162438) (@lem7162437 B y t)). Qed.
Lemma lem7162440 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term228 A B t R x y) = (term384 A B t R x y).
Proof. exact (MK_COMB (@lem7162439 B y t) (@lem7162418 A B R x y)). Qed.
Lemma lem7162441 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7162442 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term230 A B t R x y) = (term396 A B t R x y).
Proof. exact (MK_COMB (@lem7162441) (@lem7162440 A B t R x y)). Qed.
Lemma lem7162443 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term304 A B t R x y) = (term400 A B t R x y).
Proof. exact (MK_COMB (@lem7162442 A B t R x y) (@lem7162399 A B t R x y)). Qed.
Lemma lem7162444 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term305 A B t R x) = (term401 A B t R x).
Proof. exact (fun_ext (fun y : B => @lem7162443 A B t R x y)). Qed.
Lemma lem7162445 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7162446 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term306 A B t R x) = (term402 A B t R x).
Proof. exact (MK_COMB (@lem7162445 B) (@lem7162444 A B t R x)). Qed.
Lemma lem7162453 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7162454 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem7162453 A B f x). Qed.
Lemma lem7162456 {A B : Type'} (y : A -> B) (x : A) : (y x) = (@I (A -> B) y x).
Proof. exact (@lem7162454 A B y x). Qed.
Lemma lem7162457 {A B : Type'} (R : type1413 A B) (x : A) : (R x) = (R x).
Proof. exact (eq_refl (R x)). Qed.
Lemma lem7162458 {A B : Type'} (R : type1413 A B) (y : A -> B) (x : A) : (term403 A B R y x) = (term404 A B R y x).
Proof. exact (MK_COMB (@lem7162457 A B R x) (@lem7162456 A B y x)). Qed.
Lemma lem7162460 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7162461 {A B : Type'} (f : type1413 A B) (x : A) : (f x) = (@I (A -> B -> Prop) f x).
Proof. exact (@lem7162460 A (B -> Prop) f x). Qed.
Lemma lem7162462 {A B : Type'} (R : type1413 A B) (x : A) : (R x) = (@I (A -> B -> Prop) R x).
Proof. exact (@lem7162461 A B R x). Qed.
Lemma lem7162463 {A B : Type'} (y : A -> B) (x : A) : (@I (A -> B) y x) = (@I (A -> B) y x).
Proof. exact (eq_refl (@I (A -> B) y x)). Qed.
Lemma lem7162464 {A B : Type'} (R : type1413 A B) (y : A -> B) (x : A) : (term404 A B R y x) = (term405 A B R y x).
Proof. exact (MK_COMB (@lem7162462 A B R x) (@lem7162463 A B y x)). Qed.
Lemma lem7162466 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7162467 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem7162466 B Prop f x). Qed.
Lemma lem7162468 {A B : Type'} (R : type1413 A B) (y : A -> B) (x : A) : (term405 A B R y x) = (term406 A B R y x).
Proof. exact (@lem7162467 B (@I (A -> B -> Prop) R x) (@I (A -> B) y x)). Qed.
Lemma lem7162469 {A B : Type'} (R : type1413 A B) (y : A -> B) (x : A) : (term404 A B R y x) = (term406 A B R y x).
Proof. exact (TRANS (@lem7162464 A B R y x) (@lem7162468 A B R y x)). Qed.
Lemma lem7162470 {A B : Type'} (R : type1413 A B) (y : A -> B) (x : A) : (term403 A B R y x) = (term406 A B R y x).
Proof. exact (TRANS (@lem7162458 A B R y x) (@lem7162469 A B R y x)). Qed.
Lemma lem7162471 {B : Type'} : (@IN B) = (@IN B).
Proof. exact (eq_refl (@IN B)). Qed.
Lemma lem7162476 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7162477 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem7162476 A B f x). Qed.
Lemma lem7162479 {A B : Type'} (y : A -> B) (x : A) : (y x) = (@I (A -> B) y x).
Proof. exact (@lem7162477 A B y x). Qed.
Lemma lem7162480 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem7162481 {A B : Type'} (y : A -> B) (x : A) : (term407 A B y x) = (term408 A B y x).
Proof. exact (MK_COMB (@lem7162471 B) (@lem7162479 A B y x)). Qed.
Lemma lem7162482 {A B : Type'} (y : A -> B) (x : A) (t : B -> Prop) : (term409 A B y x t) = (term410 A B y x t).
Proof. exact (MK_COMB (@lem7162481 A B y x) (@lem7162480 B t)). Qed.
Lemma lem7162484 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7162485 {B : Type'} (f : type1364 B) (x : B) : (f x) = (@I (B -> (B -> Prop) -> Prop) f x).
Proof. exact (@lem7162484 B (type686 B) f x). Qed.
Lemma lem7162486 {A B : Type'} (y : A -> B) (x : A) : (term408 A B y x) = (term411 A B y x).
Proof. exact (@lem7162485 B (@IN B) (@I (A -> B) y x)). Qed.
Lemma lem7162487 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem7162488 {A B : Type'} (y : A -> B) (x : A) (t : B -> Prop) : (term410 A B y x t) = (term412 A B y x t).
Proof. exact (MK_COMB (@lem7162486 A B y x) (@lem7162487 B t)). Qed.
Lemma lem7162490 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7162491 {B : Type'} (f : type686 B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> Prop) f x).
Proof. exact (@lem7162490 (B -> Prop) Prop f x). Qed.
Lemma lem7162492 {A B : Type'} (y : A -> B) (x : A) (t : B -> Prop) : (term412 A B y x t) = (term413 A B y x t).
Proof. exact (@lem7162491 B (term411 A B y x) t). Qed.
Lemma lem7162493 {A B : Type'} (y : A -> B) (x : A) (t : B -> Prop) : (term410 A B y x t) = (term413 A B y x t).
Proof. exact (TRANS (@lem7162488 A B y x t) (@lem7162492 A B y x t)). Qed.
Lemma lem7162494 {A B : Type'} (y : A -> B) (x : A) (t : B -> Prop) : (term409 A B y x t) = (term413 A B y x t).
Proof. exact (TRANS (@lem7162482 A B y x t) (@lem7162493 A B y x t)). Qed.
Lemma lem7162495 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7162496 {A B : Type'} (y : A -> B) (x : A) (t : B -> Prop) : (term414 A B y x t) = (term415 A B y x t).
Proof. exact (MK_COMB (@lem7162495) (@lem7162494 A B y x t)). Qed.
Lemma lem7162497 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (y : A -> B) (x : A) : (term416 A B t R y x) = (term417 A B t R y x).
Proof. exact (MK_COMB (@lem7162496 A B y x t) (@lem7162470 A B R y x)). Qed.
Lemma lem7162498 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7162499 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (y : A -> B) (x : A) : (term418 A B t R y x) = (term419 A B t R y x).
Proof. exact (MK_COMB (@lem7162498) (@lem7162497 A B t R y x)). Qed.
Lemma lem7162500 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term420 A B y t R x) = (term421 A B y t R x).
Proof. exact (MK_COMB (@lem7162499 A B t R y x) (@lem7162446 A B t R x)). Qed.
Lemma lem7162501 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7162508 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7162509 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem7162508 A (type686 A) f x). Qed.
Lemma lem7162510 {A : Type'} (x : A) : (@IN A x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x).
Proof. exact (@lem7162509 A (@IN A) x). Qed.
Lemma lem7162511 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7162512 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x s).
Proof. exact (MK_COMB (@lem7162510 A x) (@lem7162511 A s)). Qed.
Lemma lem7162514 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7162515 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem7162514 (A -> Prop) Prop f x). Qed.
Lemma lem7162516 {A : Type'} (x : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x s) = (term381 A x s).
Proof. exact (@lem7162515 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x) s). Qed.
Lemma lem7162518 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (term381 A x s).
Proof. exact (TRANS (@lem7162512 A x s) (@lem7162516 A x s)). Qed.
Lemma lem7162519 {A : Type'} (x : A) (s : A -> Prop) : (term329 A x s) = (term382 A x s).
Proof. exact (MK_COMB (@lem7162501) (@lem7162518 A x s)). Qed.
Lemma lem7162520 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7162521 {A : Type'} (x : A) (s : A -> Prop) : (term286 A x s) = (term383 A x s).
Proof. exact (MK_COMB (@lem7162520) (@lem7162519 A x s)). Qed.
Lemma lem7162522 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term357 A B s y t R x) = (term422 A B s y t R x).
Proof. exact (MK_COMB (@lem7162521 A x s) (@lem7162500 A B y t R x)). Qed.
Lemma lem7162523 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) : (term359 A B s y t R) = (term423 A B s y t R).
Proof. exact (fun_ext (fun x : A => @lem7162522 A B s y t R x)). Qed.
Lemma lem7162524 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7162525 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) : (term361 A B s y t R) = (term424 A B s y t R).
Proof. exact (MK_COMB (@lem7162524 A) (@lem7162523 A B s y t R)). Qed.
Lemma lem7162526 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (h1 : term361 A B s y t R) : term424 A B s y t R.
Proof. exact (EQ_MP (@lem7162525 A B s y t R) (@lem7162131 A B s y t R h1)). Qed.
Lemma lem7162528 {A : Type'} (P : A -> Prop) (Q : Prop) : (term242 A P Q) = (term241 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem7162529 {B : Type'} (P : B -> Prop) (Q : Prop) : (term242 B P Q) = (term241 B P Q).
Proof. exact (@lem7162528 B P Q). Qed.
Lemma lem7162530 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term425 A B _95867 t R x) = (term426 A B _95867 t R x).
Proof. exact (@lem7162529 B (term385 A B t R x) (term377 A B _95867 t R x)). Qed.
Lemma lem7162531 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term427 A B t R x x') = (term384 A B t R x x').
Proof. exact (eq_refl (term427 A B t R x x')). Qed.
Lemma lem7162532 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term428 A B t R x) = (term385 A B t R x).
Proof. exact (fun_ext (fun x' : B => @lem7162531 A B t R x x')). Qed.
Lemma lem7162533 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7162534 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term429 A B t R x) = (term386 A B t R x).
Proof. exact (MK_COMB (@lem7162533 B) (@lem7162532 A B t R x)). Qed.
Lemma lem7162535 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7162536 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term430 A B t R x) = (term387 A B t R x).
Proof. exact (MK_COMB (@lem7162535) (@lem7162534 A B t R x)). Qed.
Lemma lem7162537 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term377 A B _95867 t R x) = (term377 A B _95867 t R x).
Proof. exact (eq_refl (term377 A B _95867 t R x)). Qed.
Lemma lem7162538 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term425 A B _95867 t R x) = (term388 A B _95867 t R x).
Proof. exact (MK_COMB (@lem7162536 A B t R x) (@lem7162537 A B _95867 t R x)). Qed.
Lemma lem7162539 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7162540 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term431 A B _95867 t R x) = (term432 A B _95867 t R x).
Proof. exact (MK_COMB (@lem7162539) (@lem7162538 A B _95867 t R x)). Qed.
Lemma lem7162541 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term427 A B t R x x') = (term384 A B t R x x').
Proof. exact (eq_refl (term427 A B t R x x')). Qed.
Lemma lem7162542 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7162543 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term433 A B t R x x') = (term396 A B t R x x').
Proof. exact (MK_COMB (@lem7162542) (@lem7162541 A B t R x x')). Qed.
Lemma lem7162544 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term377 A B _95867 t R x) = (term377 A B _95867 t R x).
Proof. exact (eq_refl (term377 A B _95867 t R x)). Qed.
Lemma lem7162545 {A B : Type'} (x : B) (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) : (term434 A B x _95867 t R x') = (term435 A B x _95867 t R x').
Proof. exact (MK_COMB (@lem7162543 A B t R x' x) (@lem7162544 A B _95867 t R x')). Qed.
Lemma lem7162546 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term436 A B _95867 t R x) = (term437 A B _95867 t R x).
Proof. exact (fun_ext (fun x' : B => @lem7162545 A B x' _95867 t R x)). Qed.
Lemma lem7162547 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7162548 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term426 A B _95867 t R x) = (term438 A B _95867 t R x).
Proof. exact (MK_COMB (@lem7162547 B) (@lem7162546 A B _95867 t R x)). Qed.
Lemma lem7162549 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : ((term425 A B _95867 t R x) = (term426 A B _95867 t R x)) = ((term388 A B _95867 t R x) = (term438 A B _95867 t R x)).
Proof. exact (MK_COMB (@lem7162540 A B _95867 t R x) (@lem7162548 A B _95867 t R x)). Qed.
Lemma lem7162550 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term388 A B _95867 t R x) = (term438 A B _95867 t R x).
Proof. exact (EQ_MP (@lem7162549 A B _95867 t R x) (@lem7162530 A B _95867 t R x)). Qed.
Lemma lem7162551 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (term389 A B _95867 t R) = (term439 A B _95867 t R).
Proof. exact (fun_ext (fun x : A => @lem7162550 A B _95867 t R x)). Qed.
Lemma lem7162552 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7162553 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (term390 A B _95867 t R) = (term440 A B _95867 t R).
Proof. exact (MK_COMB (@lem7162552 A) (@lem7162551 A B _95867 t R)). Qed.
Lemma lem7162554 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) : (term391 A B _95867 t) = (term441 A B _95867 t).
Proof. exact (fun_ext (fun R : type1413 A B => @lem7162553 A B _95867 t R)). Qed.
Lemma lem7162555 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem7162556 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) : (term392 A B _95867 t) = (term442 A B _95867 t).
Proof. exact (MK_COMB (@lem7162555 A B) (@lem7162554 A B _95867 t)). Qed.
Lemma lem7162557 {A B : Type'} (_95867 : type830 A B) : (term393 A B _95867) = (term443 A B _95867).
Proof. exact (fun_ext (fun t : B -> Prop => @lem7162556 A B _95867 t)). Qed.
Lemma lem7162558 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem7162559 {A B : Type'} (_95867 : type830 A B) : (term394 A B _95867) = (term444 A B _95867).
Proof. exact (MK_COMB (@lem7162558 B) (@lem7162557 A B _95867)). Qed.
Lemma lem7162582 {A B : Type'} (x : B) (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) : (term435 A B x _95867 t R x') = (term445 A B x _95867 t R x').
Proof. exact (@lem19490 (term375 A B _95867 R x' t) (term384 A B t R x' x) (term370 A B _95867 t R x')). Qed.
Lemma lem7162583 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term437 A B _95867 t R x) = (term446 A B _95867 t R x).
Proof. exact (fun_ext (fun x' : B => @lem7162582 A B x' _95867 t R x)). Qed.
Lemma lem7162584 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7162585 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term438 A B _95867 t R x) = (term447 A B _95867 t R x).
Proof. exact (MK_COMB (@lem7162584 B) (@lem7162583 A B _95867 t R x)). Qed.
Lemma lem7162586 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (term439 A B _95867 t R) = (term448 A B _95867 t R).
Proof. exact (fun_ext (fun x : A => @lem7162585 A B _95867 t R x)). Qed.
Lemma lem7162587 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7162588 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (term440 A B _95867 t R) = (term449 A B _95867 t R).
Proof. exact (MK_COMB (@lem7162587 A) (@lem7162586 A B _95867 t R)). Qed.
Lemma lem7162589 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) : (term441 A B _95867 t) = (term450 A B _95867 t).
Proof. exact (fun_ext (fun R : type1413 A B => @lem7162588 A B _95867 t R)). Qed.
Lemma lem7162590 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem7162591 {A B : Type'} (_95867 : type830 A B) (t : B -> Prop) : (term442 A B _95867 t) = (term451 A B _95867 t).
Proof. exact (MK_COMB (@lem7162590 A B) (@lem7162589 A B _95867 t)). Qed.
Lemma lem7162592 {A B : Type'} (_95867 : type830 A B) : (term443 A B _95867) = (term452 A B _95867).
Proof. exact (fun_ext (fun t : B -> Prop => @lem7162591 A B _95867 t)). Qed.
Lemma lem7162593 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem7162594 {A B : Type'} (_95867 : type830 A B) : (term444 A B _95867) = (term453 A B _95867).
Proof. exact (MK_COMB (@lem7162593 B) (@lem7162592 A B _95867)). Qed.
Lemma lem7162595 {A B : Type'} (_95867 : type830 A B) : (term394 A B _95867) = (term453 A B _95867).
Proof. exact (TRANS (@lem7162559 A B _95867) (@lem7162594 A B _95867)). Qed.
Lemma lem7162596 {A B : Type'} (_95867 : type830 A B) (h1 : term174 A B _95867) : term453 A B _95867.
Proof. exact (EQ_MP (@lem7162595 A B _95867) (@lem7162275 A B _95867 h1)). Qed.
Lemma lem7162610 {A : Type'} (P : Prop) (Q : A -> Prop) : (term292 A P Q) = (term291 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem7162611 {B : Type'} (P : Prop) (Q : B -> Prop) : (term292 B P Q) = (term291 B P Q).
Proof. exact (@lem7162610 B P Q). Qed.
Lemma lem7162612 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term454 A B t R x y) = (term455 A B t R x y).
Proof. exact (@lem7162611 B (term384 A B t R x y) (term398 A B t R x y)). Qed.
Lemma lem7162613 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y : B) : (term456 A B t R x y y') = (term397 A B t R x y' y).
Proof. exact (eq_refl (term456 A B t R x y y')). Qed.
Lemma lem7162614 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term457 A B t R x y) = (term398 A B t R x y).
Proof. exact (fun_ext (fun y' : B => @lem7162613 A B t R x y' y)). Qed.
Lemma lem7162615 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7162616 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term458 A B t R x y) = (term399 A B t R x y).
Proof. exact (MK_COMB (@lem7162615 B) (@lem7162614 A B t R x y)). Qed.
Lemma lem7162617 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term396 A B t R x y) = (term396 A B t R x y).
Proof. exact (eq_refl (term396 A B t R x y)). Qed.
Lemma lem7162618 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term454 A B t R x y) = (term400 A B t R x y).
Proof. exact (MK_COMB (@lem7162617 A B t R x y) (@lem7162616 A B t R x y)). Qed.
Lemma lem7162619 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7162620 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term459 A B t R x y) = (term460 A B t R x y).
Proof. exact (MK_COMB (@lem7162619) (@lem7162618 A B t R x y)). Qed.
Lemma lem7162621 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y : B) : (term456 A B t R x y y') = (term397 A B t R x y' y).
Proof. exact (eq_refl (term456 A B t R x y y')). Qed.
Lemma lem7162622 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term396 A B t R x y) = (term396 A B t R x y).
Proof. exact (eq_refl (term396 A B t R x y)). Qed.
Lemma lem7162623 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y : B) : (term461 A B t R x y y') = (term462 A B t R x y' y).
Proof. exact (MK_COMB (@lem7162622 A B t R x y) (@lem7162621 A B t R x y' y)). Qed.
Lemma lem7162624 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term463 A B t R x y) = (term464 A B t R x y).
Proof. exact (fun_ext (fun y' : B => @lem7162623 A B t R x y' y)). Qed.
Lemma lem7162625 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7162626 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term455 A B t R x y) = (term465 A B t R x y).
Proof. exact (MK_COMB (@lem7162625 B) (@lem7162624 A B t R x y)). Qed.
Lemma lem7162627 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : ((term454 A B t R x y) = (term455 A B t R x y)) = ((term400 A B t R x y) = (term465 A B t R x y)).
Proof. exact (MK_COMB (@lem7162620 A B t R x y) (@lem7162626 A B t R x y)). Qed.
Lemma lem7162628 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term400 A B t R x y) = (term465 A B t R x y).
Proof. exact (EQ_MP (@lem7162627 A B t R x y) (@lem7162612 A B t R x y)). Qed.
Lemma lem7162629 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term401 A B t R x) = (term466 A B t R x).
Proof. exact (fun_ext (fun y : B => @lem7162628 A B t R x y)). Qed.
Lemma lem7162630 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7162631 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term402 A B t R x) = (term467 A B t R x).
Proof. exact (MK_COMB (@lem7162630 B) (@lem7162629 A B t R x)). Qed.
Lemma lem7162632 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (y : A -> B) (x : A) : (term419 A B t R y x) = (term419 A B t R y x).
Proof. exact (eq_refl (term419 A B t R y x)). Qed.
Lemma lem7162633 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term421 A B y t R x) = (term468 A B y t R x).
Proof. exact (MK_COMB (@lem7162632 A B t R y x) (@lem7162631 A B t R x)). Qed.
Lemma lem7162635 {A : Type'} (P : Prop) (Q : A -> Prop) : (term469 A P Q) = (term470 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem7162636 {B : Type'} (P : Prop) (Q : B -> Prop) : (term469 B P Q) = (term470 B P Q).
Proof. exact (@lem7162635 B P Q). Qed.
Lemma lem7162637 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term471 A B y t R x) = (term472 A B y t R x).
Proof. exact (@lem7162636 B (term417 A B t R y x) (term466 A B t R x)). Qed.
Lemma lem7162638 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term473 A B t R x y) = (term465 A B t R x y).
Proof. exact (eq_refl (term473 A B t R x y)). Qed.
Lemma lem7162639 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term474 A B t R x) = (term466 A B t R x).
Proof. exact (fun_ext (fun y : B => @lem7162638 A B t R x y)). Qed.
Lemma lem7162640 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7162641 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term475 A B t R x) = (term467 A B t R x).
Proof. exact (MK_COMB (@lem7162640 B) (@lem7162639 A B t R x)). Qed.
Lemma lem7162642 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (y : A -> B) (x : A) : (term419 A B t R y x) = (term419 A B t R y x).
Proof. exact (eq_refl (term419 A B t R y x)). Qed.
Lemma lem7162643 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term471 A B y t R x) = (term468 A B y t R x).
Proof. exact (MK_COMB (@lem7162642 A B t R y x) (@lem7162641 A B t R x)). Qed.
Lemma lem7162644 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7162645 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term476 A B y t R x) = (term477 A B y t R x).
Proof. exact (MK_COMB (@lem7162644) (@lem7162643 A B y t R x)). Qed.
Lemma lem7162646 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term473 A B t R x y) = (term465 A B t R x y).
Proof. exact (eq_refl (term473 A B t R x y)). Qed.
Lemma lem7162647 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (y : A -> B) (x : A) : (term419 A B t R y x) = (term419 A B t R y x).
Proof. exact (eq_refl (term419 A B t R y x)). Qed.
Lemma lem7162648 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term478 A B y t R x y') = (term479 A B y t R x y').
Proof. exact (MK_COMB (@lem7162647 A B t R y x) (@lem7162646 A B t R x y')). Qed.
Lemma lem7162649 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term480 A B y t R x) = (term481 A B y t R x).
Proof. exact (fun_ext (fun y' : B => @lem7162648 A B y t R x y')). Qed.
Lemma lem7162650 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7162651 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term472 A B y t R x) = (term482 A B y t R x).
Proof. exact (MK_COMB (@lem7162650 B) (@lem7162649 A B y t R x)). Qed.
Lemma lem7162652 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : ((term471 A B y t R x) = (term472 A B y t R x)) = ((term468 A B y t R x) = (term482 A B y t R x)).
Proof. exact (MK_COMB (@lem7162645 A B y t R x) (@lem7162651 A B y t R x)). Qed.
Lemma lem7162653 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term468 A B y t R x) = (term482 A B y t R x).
Proof. exact (EQ_MP (@lem7162652 A B y t R x) (@lem7162637 A B y t R x)). Qed.
Lemma lem7162655 {A : Type'} (P : Prop) (Q : A -> Prop) : (term469 A P Q) = (term470 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem7162656 {B : Type'} (P : Prop) (Q : B -> Prop) : (term469 B P Q) = (term470 B P Q).
Proof. exact (@lem7162655 B P Q). Qed.
Lemma lem7162657 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term483 A B y t R x y') = (term484 A B y t R x y').
Proof. exact (@lem7162656 B (term417 A B t R y x) (term464 A B t R x y')). Qed.
Lemma lem7162658 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y : B) : (term485 A B t R x y y') = (term462 A B t R x y' y).
Proof. exact (eq_refl (term485 A B t R x y y')). Qed.
Lemma lem7162659 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term486 A B t R x y) = (term464 A B t R x y).
Proof. exact (fun_ext (fun y' : B => @lem7162658 A B t R x y' y)). Qed.
Lemma lem7162660 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7162661 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term487 A B t R x y) = (term465 A B t R x y).
Proof. exact (MK_COMB (@lem7162660 B) (@lem7162659 A B t R x y)). Qed.
Lemma lem7162662 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (y : A -> B) (x : A) : (term419 A B t R y x) = (term419 A B t R y x).
Proof. exact (eq_refl (term419 A B t R y x)). Qed.
Lemma lem7162663 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term483 A B y t R x y') = (term479 A B y t R x y').
Proof. exact (MK_COMB (@lem7162662 A B t R y x) (@lem7162661 A B t R x y')). Qed.
Lemma lem7162664 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7162665 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term488 A B y t R x y') = (term489 A B y t R x y').
Proof. exact (MK_COMB (@lem7162664) (@lem7162663 A B y t R x y')). Qed.
Lemma lem7162666 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y : B) : (term485 A B t R x y y') = (term462 A B t R x y' y).
Proof. exact (eq_refl (term485 A B t R x y y')). Qed.
Lemma lem7162667 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (y : A -> B) (x : A) : (term419 A B t R y x) = (term419 A B t R y x).
Proof. exact (eq_refl (term419 A B t R y x)). Qed.
Lemma lem7162668 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y'' : B) : (term490 A B y t R x y'' y') = (term491 A B y t R x y' y'').
Proof. exact (MK_COMB (@lem7162667 A B t R y x) (@lem7162666 A B t R x y' y'')). Qed.
Lemma lem7162669 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term492 A B y t R x y') = (term493 A B y t R x y').
Proof. exact (fun_ext (fun y'' : B => @lem7162668 A B y t R x y'' y')). Qed.
Lemma lem7162670 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7162671 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term484 A B y t R x y') = (term494 A B y t R x y').
Proof. exact (MK_COMB (@lem7162670 B) (@lem7162669 A B y t R x y')). Qed.
Lemma lem7162672 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : ((term483 A B y t R x y') = (term484 A B y t R x y')) = ((term479 A B y t R x y') = (term494 A B y t R x y')).
Proof. exact (MK_COMB (@lem7162665 A B y t R x y') (@lem7162671 A B y t R x y')). Qed.
Lemma lem7162673 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term479 A B y t R x y') = (term494 A B y t R x y').
Proof. exact (EQ_MP (@lem7162672 A B y t R x y') (@lem7162657 A B y t R x y')). Qed.
Lemma lem7162674 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term481 A B y t R x) = (term495 A B y t R x).
Proof. exact (fun_ext (fun y' : B => @lem7162673 A B y t R x y')). Qed.
Lemma lem7162675 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7162676 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term482 A B y t R x) = (term496 A B y t R x).
Proof. exact (MK_COMB (@lem7162675 B) (@lem7162674 A B y t R x)). Qed.
Lemma lem7162677 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term468 A B y t R x) = (term496 A B y t R x).
Proof. exact (TRANS (@lem7162653 A B y t R x) (@lem7162676 A B y t R x)). Qed.
Lemma lem7162678 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term421 A B y t R x) = (term496 A B y t R x).
Proof. exact (TRANS (@lem7162633 A B y t R x) (@lem7162677 A B y t R x)). Qed.
Lemma lem7162679 {A : Type'} (x : A) (s : A -> Prop) : (term383 A x s) = (term383 A x s).
Proof. exact (eq_refl (term383 A x s)). Qed.
Lemma lem7162680 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term422 A B s y t R x) = (term497 A B s y t R x).
Proof. exact (MK_COMB (@lem7162679 A x s) (@lem7162678 A B y t R x)). Qed.
Lemma lem7162682 {A : Type'} (P : Prop) (Q : A -> Prop) : (term292 A P Q) = (term291 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem7162683 {B : Type'} (P : Prop) (Q : B -> Prop) : (term292 B P Q) = (term291 B P Q).
Proof. exact (@lem7162682 B P Q). Qed.
Lemma lem7162684 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term498 A B s y t R x) = (term499 A B s y t R x).
Proof. exact (@lem7162683 B (term382 A x s) (term495 A B y t R x)). Qed.
Lemma lem7162685 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term500 A B y t R x y') = (term494 A B y t R x y').
Proof. exact (eq_refl (term500 A B y t R x y')). Qed.
Lemma lem7162686 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term501 A B y t R x) = (term495 A B y t R x).
Proof. exact (fun_ext (fun y' : B => @lem7162685 A B y t R x y')). Qed.
Lemma lem7162687 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7162688 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term502 A B y t R x) = (term496 A B y t R x).
Proof. exact (MK_COMB (@lem7162687 B) (@lem7162686 A B y t R x)). Qed.
Lemma lem7162689 {A : Type'} (x : A) (s : A -> Prop) : (term383 A x s) = (term383 A x s).
Proof. exact (eq_refl (term383 A x s)). Qed.
Lemma lem7162690 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term498 A B s y t R x) = (term497 A B s y t R x).
Proof. exact (MK_COMB (@lem7162689 A x s) (@lem7162688 A B y t R x)). Qed.
Lemma lem7162691 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7162692 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term503 A B s y t R x) = (term504 A B s y t R x).
Proof. exact (MK_COMB (@lem7162691) (@lem7162690 A B s y t R x)). Qed.
Lemma lem7162693 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term500 A B y t R x y') = (term494 A B y t R x y').
Proof. exact (eq_refl (term500 A B y t R x y')). Qed.
Lemma lem7162694 {A : Type'} (x : A) (s : A -> Prop) : (term383 A x s) = (term383 A x s).
Proof. exact (eq_refl (term383 A x s)). Qed.
Lemma lem7162695 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term505 A B s y t R x y') = (term506 A B s y t R x y').
Proof. exact (MK_COMB (@lem7162694 A x s) (@lem7162693 A B y t R x y')). Qed.
Lemma lem7162696 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term507 A B s y t R x) = (term508 A B s y t R x).
Proof. exact (fun_ext (fun y' : B => @lem7162695 A B s y t R x y')). Qed.
Lemma lem7162697 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7162698 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term499 A B s y t R x) = (term509 A B s y t R x).
Proof. exact (MK_COMB (@lem7162697 B) (@lem7162696 A B s y t R x)). Qed.
Lemma lem7162699 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : ((term498 A B s y t R x) = (term499 A B s y t R x)) = ((term497 A B s y t R x) = (term509 A B s y t R x)).
Proof. exact (MK_COMB (@lem7162692 A B s y t R x) (@lem7162698 A B s y t R x)). Qed.
Lemma lem7162700 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term497 A B s y t R x) = (term509 A B s y t R x).
Proof. exact (EQ_MP (@lem7162699 A B s y t R x) (@lem7162684 A B s y t R x)). Qed.
Lemma lem7162702 {A : Type'} (P : Prop) (Q : A -> Prop) : (term292 A P Q) = (term291 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem7162703 {B : Type'} (P : Prop) (Q : B -> Prop) : (term292 B P Q) = (term291 B P Q).
Proof. exact (@lem7162702 B P Q). Qed.
Lemma lem7162704 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term510 A B s y t R x y') = (term511 A B s y t R x y').
Proof. exact (@lem7162703 B (term382 A x s) (term493 A B y t R x y')). Qed.
Lemma lem7162705 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y'' : B) : (term512 A B y t R x y'' y') = (term491 A B y t R x y' y'').
Proof. exact (eq_refl (term512 A B y t R x y'' y')). Qed.
Lemma lem7162706 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term513 A B y t R x y') = (term493 A B y t R x y').
Proof. exact (fun_ext (fun y'' : B => @lem7162705 A B y t R x y'' y')). Qed.
Lemma lem7162707 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7162708 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term514 A B y t R x y') = (term494 A B y t R x y').
Proof. exact (MK_COMB (@lem7162707 B) (@lem7162706 A B y t R x y')). Qed.
Lemma lem7162709 {A : Type'} (x : A) (s : A -> Prop) : (term383 A x s) = (term383 A x s).
Proof. exact (eq_refl (term383 A x s)). Qed.
Lemma lem7162710 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term510 A B s y t R x y') = (term506 A B s y t R x y').
Proof. exact (MK_COMB (@lem7162709 A x s) (@lem7162708 A B y t R x y')). Qed.
Lemma lem7162711 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7162712 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term515 A B s y t R x y') = (term516 A B s y t R x y').
Proof. exact (MK_COMB (@lem7162711) (@lem7162710 A B s y t R x y')). Qed.
Lemma lem7162713 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y'' : B) : (term512 A B y t R x y'' y') = (term491 A B y t R x y' y'').
Proof. exact (eq_refl (term512 A B y t R x y'' y')). Qed.
Lemma lem7162714 {A : Type'} (x : A) (s : A -> Prop) : (term383 A x s) = (term383 A x s).
Proof. exact (eq_refl (term383 A x s)). Qed.
Lemma lem7162715 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y'' : B) : (term517 A B s y t R x y'' y') = (term518 A B s y t R x y' y'').
Proof. exact (MK_COMB (@lem7162714 A x s) (@lem7162713 A B y t R x y' y'')). Qed.
Lemma lem7162716 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term519 A B s y t R x y') = (term520 A B s y t R x y').
Proof. exact (fun_ext (fun y'' : B => @lem7162715 A B s y t R x y'' y')). Qed.
Lemma lem7162717 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7162718 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term511 A B s y t R x y') = (term521 A B s y t R x y').
Proof. exact (MK_COMB (@lem7162717 B) (@lem7162716 A B s y t R x y')). Qed.
Lemma lem7162719 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : ((term510 A B s y t R x y') = (term511 A B s y t R x y')) = ((term506 A B s y t R x y') = (term521 A B s y t R x y')).
Proof. exact (MK_COMB (@lem7162712 A B s y t R x y') (@lem7162718 A B s y t R x y')). Qed.
Lemma lem7162720 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term506 A B s y t R x y') = (term521 A B s y t R x y').
Proof. exact (EQ_MP (@lem7162719 A B s y t R x y') (@lem7162704 A B s y t R x y')). Qed.
Lemma lem7162721 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term508 A B s y t R x) = (term522 A B s y t R x).
Proof. exact (fun_ext (fun y' : B => @lem7162720 A B s y t R x y')). Qed.
Lemma lem7162722 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7162723 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term509 A B s y t R x) = (term523 A B s y t R x).
Proof. exact (MK_COMB (@lem7162722 B) (@lem7162721 A B s y t R x)). Qed.
Lemma lem7162724 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term497 A B s y t R x) = (term523 A B s y t R x).
Proof. exact (TRANS (@lem7162700 A B s y t R x) (@lem7162723 A B s y t R x)). Qed.
Lemma lem7162725 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term422 A B s y t R x) = (term523 A B s y t R x).
Proof. exact (TRANS (@lem7162680 A B s y t R x) (@lem7162724 A B s y t R x)). Qed.
Lemma lem7162726 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) : (term423 A B s y t R) = (term524 A B s y t R).
Proof. exact (fun_ext (fun x : A => @lem7162725 A B s y t R x)). Qed.
Lemma lem7162727 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7162728 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) : (term424 A B s y t R) = (term525 A B s y t R).
Proof. exact (MK_COMB (@lem7162727 A) (@lem7162726 A B s y t R)). Qed.
Lemma lem7162766 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y'' : B) : (term518 A B s y t R x y' y'') = (term526 A B y s t R x y' y'').
Proof. exact (@lem19490 (term417 A B t R y x) (term382 A x s) (term462 A B t R x y' y'')). Qed.
Lemma lem7162767 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y : B) : (term527 A B s t R x y' y) = (term527 A B s t R x y' y).
Proof. exact (eq_refl (term527 A B s t R x y' y)). Qed.
Lemma lem7162774 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (y : A -> B) (x : A) : (term528 A B s t R y x) = (term529 A B t s R y x).
Proof. exact (@lem19490 (term413 A B y x t) (term382 A x s) (term406 A B R y x)). Qed.
Lemma lem7162775 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7162776 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (y : A -> B) (x : A) : (term530 A B s t R y x) = (term531 A B t s R y x).
Proof. exact (MK_COMB (@lem7162775) (@lem7162774 A B t s R y x)). Qed.
Lemma lem7162777 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y'' : B) : (term526 A B y s t R x y' y'') = (term532 A B y s t R x y' y'').
Proof. exact (MK_COMB (@lem7162776 A B t s R y x) (@lem7162767 A B s t R x y' y'')). Qed.
Lemma lem7162779 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y'' : B) : (term518 A B s y t R x y' y'') = (term532 A B y s t R x y' y'').
Proof. exact (TRANS (@lem7162766 A B y s t R x y' y'') (@lem7162777 A B y s t R x y' y'')). Qed.
Lemma lem7162780 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term520 A B s y t R x y') = (term533 A B y s t R x y').
Proof. exact (fun_ext (fun y'' : B => @lem7162779 A B y s t R x y'' y')). Qed.
Lemma lem7162781 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7162782 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term521 A B s y t R x y') = (term534 A B y s t R x y').
Proof. exact (MK_COMB (@lem7162781 B) (@lem7162780 A B y s t R x y')). Qed.
Lemma lem7162783 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term522 A B s y t R x) = (term535 A B y s t R x).
Proof. exact (fun_ext (fun y' : B => @lem7162782 A B y s t R x y')). Qed.
Lemma lem7162784 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7162785 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term523 A B s y t R x) = (term536 A B y s t R x).
Proof. exact (MK_COMB (@lem7162784 B) (@lem7162783 A B y s t R x)). Qed.
Lemma lem7162786 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term524 A B s y t R) = (term537 A B y s t R).
Proof. exact (fun_ext (fun x : A => @lem7162785 A B y s t R x)). Qed.
Lemma lem7162787 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7162788 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term525 A B s y t R) = (term538 A B y s t R).
Proof. exact (MK_COMB (@lem7162787 A) (@lem7162786 A B y s t R)). Qed.
Lemma lem7162789 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term424 A B s y t R) = (term538 A B y s t R).
Proof. exact (TRANS (@lem7162728 A B s y t R) (@lem7162788 A B y s t R)). Qed.
Lemma lem7162790 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (h1 : term361 A B s y t R) : term538 A B y s t R.
Proof. exact (EQ_MP (@lem7162789 A B y s t R) (@lem7162526 A B s y t R h1)). Qed.
Lemma lem7162791 {A B : Type'} (_95868 : B -> Prop) (_95867 : type830 A B) (h1 : term174 A B _95867) : term539 A B _95867 _95868.
Proof. exact (@lem7162596 A B _95867 h1 _95868). Qed.
Lemma lem7162792 {A B : Type'} (_95867 : type830 A B) (_95868 : B -> Prop) : (term539 A B _95867 _95868) = (term451 A B _95867 _95868).
Proof. exact (eq_refl (term539 A B _95867 _95868)). Qed.
Lemma lem7162793 {A B : Type'} (_95868 : B -> Prop) (_95867 : type830 A B) (h1 : term174 A B _95867) : term451 A B _95867 _95868.
Proof. exact (EQ_MP (@lem7162792 A B _95867 _95868) (@lem7162791 A B _95868 _95867 h1)). Qed.
Lemma lem7162794 {A B : Type'} (_95868 : B -> Prop) (_95869 : type1413 A B) (_95867 : type830 A B) (h1 : term174 A B _95867) : term540 A B _95867 _95868 _95869.
Proof. exact (@lem7162793 A B _95868 _95867 h1 _95869). Qed.
Lemma lem7162795 {A B : Type'} (_95867 : type830 A B) (_95868 : B -> Prop) (_95869 : type1413 A B) : (term540 A B _95867 _95868 _95869) = (term449 A B _95867 _95868 _95869).
Proof. exact (eq_refl (term540 A B _95867 _95868 _95869)). Qed.
Lemma lem7162796 {A B : Type'} (_95868 : B -> Prop) (_95869 : type1413 A B) (_95867 : type830 A B) (h1 : term174 A B _95867) : term449 A B _95867 _95868 _95869.
Proof. exact (EQ_MP (@lem7162795 A B _95867 _95868 _95869) (@lem7162794 A B _95868 _95869 _95867 h1)). Qed.
Lemma lem7162797 {A B : Type'} (_95868 : B -> Prop) (_95869 : type1413 A B) (_95870 : A) (_95867 : type830 A B) (h1 : term174 A B _95867) : term541 A B _95867 _95868 _95869 _95870.
Proof. exact (@lem7162796 A B _95868 _95869 _95867 h1 _95870). Qed.
Lemma lem7162798 {A B : Type'} (_95867 : type830 A B) (_95868 : B -> Prop) (_95869 : type1413 A B) (_95870 : A) : (term541 A B _95867 _95868 _95869 _95870) = (term447 A B _95867 _95868 _95869 _95870).
Proof. exact (eq_refl (term541 A B _95867 _95868 _95869 _95870)). Qed.
Lemma lem7162799 {A B : Type'} (_95868 : B -> Prop) (_95869 : type1413 A B) (_95870 : A) (_95867 : type830 A B) (h1 : term174 A B _95867) : term447 A B _95867 _95868 _95869 _95870.
Proof. exact (EQ_MP (@lem7162798 A B _95867 _95868 _95869 _95870) (@lem7162797 A B _95868 _95869 _95870 _95867 h1)). Qed.
Lemma lem7162800 {A B : Type'} (_95868 : B -> Prop) (_95869 : type1413 A B) (_95870 : A) (_95871 : B) (_95867 : type830 A B) (h1 : term174 A B _95867) : term542 A B _95867 _95868 _95869 _95870 _95871.
Proof. exact (@lem7162799 A B _95868 _95869 _95870 _95867 h1 _95871). Qed.
Lemma lem7162801 {A B : Type'} (_95871 : B) (_95867 : type830 A B) (_95868 : B -> Prop) (_95869 : type1413 A B) (_95870 : A) : (term542 A B _95867 _95868 _95869 _95870 _95871) = (term445 A B _95871 _95867 _95868 _95869 _95870).
Proof. exact (eq_refl (term542 A B _95867 _95868 _95869 _95870 _95871)). Qed.
Lemma lem7162802 {A B : Type'} (_95871 : B) (_95868 : B -> Prop) (_95869 : type1413 A B) (_95870 : A) (_95867 : type830 A B) (h1 : term174 A B _95867) : term445 A B _95871 _95867 _95868 _95869 _95870.
Proof. exact (EQ_MP (@lem7162801 A B _95871 _95867 _95868 _95869 _95870) (@lem7162800 A B _95868 _95869 _95870 _95871 _95867 h1)). Qed.
Lemma lem7162803 {A B : Type'} (_95872 : A) (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (h1 : term361 A B s y t R) : term543 A B y s t R _95872.
Proof. exact (@lem7162790 A B s y t R h1 _95872). Qed.
Lemma lem7162804 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (_95872 : A) : (term543 A B y s t R _95872) = (term536 A B y s t R _95872).
Proof. exact (eq_refl (term543 A B y s t R _95872)). Qed.
Lemma lem7162805 {A B : Type'} (_95872 : A) (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (h1 : term361 A B s y t R) : term536 A B y s t R _95872.
Proof. exact (EQ_MP (@lem7162804 A B y s t R _95872) (@lem7162803 A B _95872 s y t R h1)). Qed.
Lemma lem7162806 {A B : Type'} (_95872 : A) (_95873 : B) (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (h1 : term361 A B s y t R) : term544 A B y s t R _95872 _95873.
Proof. exact (@lem7162805 A B _95872 s y t R h1 _95873). Qed.
Lemma lem7162807 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (_95872 : A) (_95873 : B) : (term544 A B y s t R _95872 _95873) = (term534 A B y s t R _95872 _95873).
Proof. exact (eq_refl (term544 A B y s t R _95872 _95873)). Qed.
Lemma lem7162808 {A B : Type'} (_95872 : A) (_95873 : B) (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (h1 : term361 A B s y t R) : term534 A B y s t R _95872 _95873.
Proof. exact (EQ_MP (@lem7162807 A B y s t R _95872 _95873) (@lem7162806 A B _95872 _95873 s y t R h1)). Qed.
Lemma lem7162809 {A B : Type'} (_95872 : A) (_95873 : B) (_95874 : B) (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (h1 : term361 A B s y t R) : term545 A B y s t R _95872 _95873 _95874.
Proof. exact (@lem7162808 A B _95872 _95873 s y t R h1 _95874). Qed.
Lemma lem7162810 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (_95872 : A) (_95874 : B) (_95873 : B) : (term545 A B y s t R _95872 _95873 _95874) = (term532 A B y s t R _95872 _95874 _95873).
Proof. exact (eq_refl (term545 A B y s t R _95872 _95873 _95874)). Qed.
Lemma lem7162811 {A B : Type'} (_95872 : A) (_95874 : B) (_95873 : B) (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (h1 : term361 A B s y t R) : term532 A B y s t R _95872 _95874 _95873.
Proof. exact (EQ_MP (@lem7162810 A B y s t R _95872 _95874 _95873) (@lem7162809 A B _95872 _95873 _95874 s y t R h1)). Qed.
Lemma lem7162813 {A B : Type'} (_95872 : A) (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (h1 : term361 A B s y t R) : term529 A B t s R y _95872.
Proof. exact (proj1 (@lem7162811 A B _95872 (@el B) (@el B) s y t R h1)). Qed.
Lemma lem7162817 {A B : Type'} (_95871 : B) (_95869 : type1413 A B) (_95870 : A) (_95868 : B -> Prop) (_95867 : type830 A B) (h1 : term174 A B _95867) : term546 A B _95871 _95867 _95869 _95870 _95868.
Proof. exact (proj1 (@lem7162802 A B _95871 _95868 _95869 _95870 _95867 h1)). Qed.
Lemma lem7162823 {A B : Type'} (_95867 : type830 A B) (R : type1413 A B) (x : A) (t : B -> Prop) (h1 : term226 A B _95867 R x t) : term395 A B _95867 R x t.
Proof. exact (EQ_MP (@lem7162346 A B _95867 R x t) (@lem7162130 A B _95867 R x t h1)). Qed.
Lemma lem7162855 {A B : Type'} (_95872 : A) (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (h1 : term361 A B s y t R) : term547 A B s y _95872 t.
Proof. exact (proj1 (@lem7162813 A B _95872 s y t R h1)). Qed.
Lemma lem7162861 {A B : Type'} (_95872 : A) (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (h1 : term361 A B s y t R) : term548 A B s R y _95872.
Proof. exact (proj2 (@lem7162813 A B _95872 s y t R h1)). Qed.
Lemma lem7162872 {A B : Type'} (_95871 : B) (_95867 : type830 A B) (_95869 : type1413 A B) (_95870 : A) (_95868 : B -> Prop) : (term546 A B _95871 _95867 _95869 _95870 _95868) = (term549 A B _95871 _95867 _95869 _95870 _95868).
Proof. exact (@lem7160874 (term382 B _95871 _95868) (term380 A B _95869 _95870 _95871) (term375 A B _95867 _95869 _95870 _95868)). Qed.
Lemma lem7162873 {A B : Type'} (_95871 : B) (_95869 : type1413 A B) (_95870 : A) (_95868 : B -> Prop) (_95867 : type830 A B) (h1 : term174 A B _95867) : term549 A B _95871 _95867 _95869 _95870 _95868.
Proof. exact (EQ_MP (@lem7162872 A B _95871 _95867 _95869 _95870 _95868) (@lem7162817 A B _95871 _95869 _95870 _95868 _95867 h1)). Qed.
Lemma lem7163058 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : term381 A x s.
Proof. exact (EQ_MP (@lem7162301 A x s) (@lem7162124 A x s h1)). Qed.
Lemma lem7163059 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : term550 A x s.
Proof. exact (fun h0 : term382 A x s => @lem7163058 A x s h1). Qed.
Lemma lem7163061 (p : Prop) : (term551 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7163062 {A : Type'} (x : A) (s : A -> Prop) : (term550 A x s) = (term381 A x s).
Proof. exact (@lem7163061 (term381 A x s)). Qed.
Lemma lem7163063 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : term381 A x s.
Proof. exact (EQ_MP (@lem7163062 A x s) (@lem7163059 A x s h1)). Qed.
Lemma lem7163069 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7163070 {A B : Type'} (y : A -> B) (t : B -> Prop) (_95872 : A) (s : A -> Prop) : (term547 A B s y _95872 t) = (term552 A B y t _95872 s).
Proof. exact (@lem7163069 (term413 A B y _95872 t) (term382 A _95872 s)). Qed.
Lemma lem7163076 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7163077 {A B : Type'} (y : A -> B) (t : B -> Prop) (_95872 : A) (s : A -> Prop) : (term553 A B s y _95872 t) = (term554 A B y t _95872 s).
Proof. exact (MK_COMB (@lem7163076) (@lem7163070 A B y t _95872 s)). Qed.
Lemma lem7163083 {A B : Type'} (y : A -> B) (t : B -> Prop) (_95872 : A) (s : A -> Prop) : (term552 A B y t _95872 s) = (term552 A B y t _95872 s).
Proof. exact (eq_refl (term552 A B y t _95872 s)). Qed.
Lemma lem7163084 {A B : Type'} (y : A -> B) (t : B -> Prop) (_95872 : A) (s : A -> Prop) : ((term547 A B s y _95872 t) = (term552 A B y t _95872 s)) = ((term552 A B y t _95872 s) = (term552 A B y t _95872 s)).
Proof. exact (MK_COMB (@lem7163077 A B y t _95872 s) (@lem7163083 A B y t _95872 s)). Qed.
Lemma lem7163086 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7163087 (x : Prop) : (x = x) = True.
Proof. exact (@lem7163086 Prop x). Qed.
Lemma lem7163088 {A B : Type'} (y : A -> B) (t : B -> Prop) (_95872 : A) (s : A -> Prop) : ((term552 A B y t _95872 s) = (term552 A B y t _95872 s)) = True.
Proof. exact (@lem7163087 (term552 A B y t _95872 s)). Qed.
Lemma lem7163089 {A B : Type'} (y : A -> B) (t : B -> Prop) (_95872 : A) (s : A -> Prop) : ((term547 A B s y _95872 t) = (term552 A B y t _95872 s)) = True.
Proof. exact (TRANS (@lem7163084 A B y t _95872 s) (@lem7163088 A B y t _95872 s)). Qed.
Lemma lem7163090 {A B : Type'} (y : A -> B) (t : B -> Prop) (_95872 : A) (s : A -> Prop) : True = ((term547 A B s y _95872 t) = (term552 A B y t _95872 s)).
Proof. exact (SYM (@lem7163089 A B y t _95872 s)). Qed.
Lemma lem7163091 {A B : Type'} (y : A -> B) (t : B -> Prop) (_95872 : A) (s : A -> Prop) : (term547 A B s y _95872 t) = (term552 A B y t _95872 s).
Proof. exact (EQ_MP (@lem7163090 A B y t _95872 s) (@lem0)). Qed.
Lemma lem7163092 {A B : Type'} (_95872 : A) (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (h1 : term361 A B s y t R) : term552 A B y t _95872 s.
Proof. exact (EQ_MP (@lem7163091 A B y t _95872 s) (@lem7162855 A B _95872 s y t R h1)). Qed.
Lemma lem7163094 (b : Prop) (a : Prop) : (a \/ b) = (term555 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7163095 {A B : Type'} (s : A -> Prop) (y : A -> B) (_95872 : A) (t : B -> Prop) : (term552 A B y t _95872 s) = (term556 A B s y _95872 t).
Proof. exact (@lem7163094 (term382 A _95872 s) (term413 A B y _95872 t)). Qed.
Lemma lem7163097 (a : Prop) : (term203 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7163098 {A : Type'} (_95872 : A) (s : A -> Prop) : (term557 A _95872 s) = (term381 A _95872 s).
Proof. exact (@lem7163097 (term381 A _95872 s)). Qed.
Lemma lem7163099 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7163100 {A : Type'} (_95872 : A) (s : A -> Prop) : (term558 A _95872 s) = (term559 A _95872 s).
Proof. exact (MK_COMB (@lem7163099) (@lem7163098 A _95872 s)). Qed.
Lemma lem7163101 {A B : Type'} (y : A -> B) (_95872 : A) (t : B -> Prop) : (term413 A B y _95872 t) = (term413 A B y _95872 t).
Proof. exact (eq_refl (term413 A B y _95872 t)). Qed.
Lemma lem7163102 {A B : Type'} (s : A -> Prop) (y : A -> B) (_95872 : A) (t : B -> Prop) : (term556 A B s y _95872 t) = (term560 A B s y _95872 t).
Proof. exact (MK_COMB (@lem7163100 A _95872 s) (@lem7163101 A B y _95872 t)). Qed.
Lemma lem7163103 {A B : Type'} (s : A -> Prop) (y : A -> B) (_95872 : A) (t : B -> Prop) : (term552 A B y t _95872 s) = (term560 A B s y _95872 t).
Proof. exact (TRANS (@lem7163095 A B s y _95872 t) (@lem7163102 A B s y _95872 t)). Qed.
Lemma lem7163106 {A B : Type'} (_95872 : A) (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (h1 : term361 A B s y t R) : term560 A B s y _95872 t.
Proof. exact (EQ_MP (@lem7163103 A B s y _95872 t) (@lem7163092 A B _95872 s y t R h1)). Qed.
Lemma lem7163107 {A B : Type'} (_95872 : A) (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (h1 : term361 A B s y t R) : term560 A B s y _95872 t.
Proof. exact (@lem7163106 A B _95872 s y t R h1). Qed.
Lemma lem7163108 {A B : Type'} (x : A) (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (h1 : term361 A B s y t R) : term560 A B s y x t.
Proof. exact (@lem7163107 A B x s y t R h1). Qed.
Lemma lem7163111 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (s : A -> Prop) (h1 : term361 A B s y t R) (h2 : @IN A x s) : term413 A B y x t.
Proof. exact (@lem7163108 A B x s y t R h1 (@lem7163063 A x s h2)). Qed.
Lemma lem7163112 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (s : A -> Prop) (h1 : term361 A B s y t R) (h2 : @IN A x s) : term561 A B y x t.
Proof. exact (fun h0 : term562 A B y x t => @lem7163111 A B y t R x s h1 h2). Qed.
Lemma lem7163114 (p : Prop) : (term551 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7163115 {A B : Type'} (y : A -> B) (x : A) (t : B -> Prop) : (term561 A B y x t) = (term413 A B y x t).
Proof. exact (@lem7163114 (term413 A B y x t)). Qed.
Lemma lem7163116 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (s : A -> Prop) (h1 : term361 A B s y t R) (h2 : @IN A x s) : term413 A B y x t.
Proof. exact (EQ_MP (@lem7163115 A B y x t) (@lem7163112 A B y t R x s h1 h2)). Qed.
Lemma lem7163118 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : term381 A x s.
Proof. exact (EQ_MP (@lem7162301 A x s) (@lem7162124 A x s h1)). Qed.
Lemma lem7163119 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : term550 A x s.
Proof. exact (fun h0 : term382 A x s => @lem7163118 A x s h1). Qed.
Lemma lem7163121 (p : Prop) : (term551 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7163122 {A : Type'} (x : A) (s : A -> Prop) : (term550 A x s) = (term381 A x s).
Proof. exact (@lem7163121 (term381 A x s)). Qed.
Lemma lem7163123 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : term381 A x s.
Proof. exact (EQ_MP (@lem7163122 A x s) (@lem7163119 A x s h1)). Qed.
Lemma lem7163129 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7163130 {A B : Type'} (R : type1413 A B) (y : A -> B) (_95872 : A) (s : A -> Prop) : (term548 A B s R y _95872) = (term563 A B R y _95872 s).
Proof. exact (@lem7163129 (term406 A B R y _95872) (term382 A _95872 s)). Qed.
Lemma lem7163136 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7163137 {A B : Type'} (R : type1413 A B) (y : A -> B) (_95872 : A) (s : A -> Prop) : (term564 A B s R y _95872) = (term565 A B R y _95872 s).
Proof. exact (MK_COMB (@lem7163136) (@lem7163130 A B R y _95872 s)). Qed.
Lemma lem7163143 {A B : Type'} (R : type1413 A B) (y : A -> B) (_95872 : A) (s : A -> Prop) : (term563 A B R y _95872 s) = (term563 A B R y _95872 s).
Proof. exact (eq_refl (term563 A B R y _95872 s)). Qed.
Lemma lem7163144 {A B : Type'} (R : type1413 A B) (y : A -> B) (_95872 : A) (s : A -> Prop) : ((term548 A B s R y _95872) = (term563 A B R y _95872 s)) = ((term563 A B R y _95872 s) = (term563 A B R y _95872 s)).
Proof. exact (MK_COMB (@lem7163137 A B R y _95872 s) (@lem7163143 A B R y _95872 s)). Qed.
Lemma lem7163146 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7163147 (x : Prop) : (x = x) = True.
Proof. exact (@lem7163146 Prop x). Qed.
Lemma lem7163148 {A B : Type'} (R : type1413 A B) (y : A -> B) (_95872 : A) (s : A -> Prop) : ((term563 A B R y _95872 s) = (term563 A B R y _95872 s)) = True.
Proof. exact (@lem7163147 (term563 A B R y _95872 s)). Qed.
Lemma lem7163149 {A B : Type'} (R : type1413 A B) (y : A -> B) (_95872 : A) (s : A -> Prop) : ((term548 A B s R y _95872) = (term563 A B R y _95872 s)) = True.
Proof. exact (TRANS (@lem7163144 A B R y _95872 s) (@lem7163148 A B R y _95872 s)). Qed.
Lemma lem7163150 {A B : Type'} (R : type1413 A B) (y : A -> B) (_95872 : A) (s : A -> Prop) : True = ((term548 A B s R y _95872) = (term563 A B R y _95872 s)).
Proof. exact (SYM (@lem7163149 A B R y _95872 s)). Qed.
Lemma lem7163151 {A B : Type'} (R : type1413 A B) (y : A -> B) (_95872 : A) (s : A -> Prop) : (term548 A B s R y _95872) = (term563 A B R y _95872 s).
Proof. exact (EQ_MP (@lem7163150 A B R y _95872 s) (@lem0)). Qed.
Lemma lem7163152 {A B : Type'} (_95872 : A) (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (h1 : term361 A B s y t R) : term563 A B R y _95872 s.
Proof. exact (EQ_MP (@lem7163151 A B R y _95872 s) (@lem7162861 A B _95872 s y t R h1)). Qed.
Lemma lem7163154 (b : Prop) (a : Prop) : (a \/ b) = (term555 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7163155 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (y : A -> B) (_95872 : A) : (term563 A B R y _95872 s) = (term566 A B s R y _95872).
Proof. exact (@lem7163154 (term382 A _95872 s) (term406 A B R y _95872)). Qed.
Lemma lem7163157 (a : Prop) : (term203 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7163158 {A : Type'} (_95872 : A) (s : A -> Prop) : (term557 A _95872 s) = (term381 A _95872 s).
Proof. exact (@lem7163157 (term381 A _95872 s)). Qed.
Lemma lem7163159 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7163160 {A : Type'} (_95872 : A) (s : A -> Prop) : (term558 A _95872 s) = (term559 A _95872 s).
Proof. exact (MK_COMB (@lem7163159) (@lem7163158 A _95872 s)). Qed.
Lemma lem7163161 {A B : Type'} (R : type1413 A B) (y : A -> B) (_95872 : A) : (term406 A B R y _95872) = (term406 A B R y _95872).
Proof. exact (eq_refl (term406 A B R y _95872)). Qed.
Lemma lem7163162 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (y : A -> B) (_95872 : A) : (term566 A B s R y _95872) = (term567 A B s R y _95872).
Proof. exact (MK_COMB (@lem7163160 A _95872 s) (@lem7163161 A B R y _95872)). Qed.
Lemma lem7163163 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (y : A -> B) (_95872 : A) : (term563 A B R y _95872 s) = (term567 A B s R y _95872).
Proof. exact (TRANS (@lem7163155 A B s R y _95872) (@lem7163162 A B s R y _95872)). Qed.
Lemma lem7163166 {A B : Type'} (_95872 : A) (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (h1 : term361 A B s y t R) : term567 A B s R y _95872.
Proof. exact (EQ_MP (@lem7163163 A B s R y _95872) (@lem7163152 A B _95872 s y t R h1)). Qed.
Lemma lem7163167 {A B : Type'} (_95872 : A) (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (h1 : term361 A B s y t R) : term567 A B s R y _95872.
Proof. exact (@lem7163166 A B _95872 s y t R h1). Qed.
Lemma lem7163168 {A B : Type'} (x : A) (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (h1 : term361 A B s y t R) : term567 A B s R y x.
Proof. exact (@lem7163167 A B x s y t R h1). Qed.
Lemma lem7163171 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (s : A -> Prop) (h1 : term361 A B s y t R) (h2 : @IN A x s) : term406 A B R y x.
Proof. exact (@lem7163168 A B x s y t R h1 (@lem7163123 A x s h2)). Qed.
Lemma lem7163172 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (s : A -> Prop) (h1 : term361 A B s y t R) (h2 : @IN A x s) : term568 A B R y x.
Proof. exact (fun h0 : term569 A B R y x => @lem7163171 A B y t R x s h1 h2). Qed.
Lemma lem7163174 (p : Prop) : (term551 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7163175 {A B : Type'} (R : type1413 A B) (y : A -> B) (x : A) : (term568 A B R y x) = (term406 A B R y x).
Proof. exact (@lem7163174 (term406 A B R y x)). Qed.
Lemma lem7163176 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (s : A -> Prop) (h1 : term361 A B s y t R) (h2 : @IN A x s) : term406 A B R y x.
Proof. exact (EQ_MP (@lem7163175 A B R y x) (@lem7163172 A B y t R x s h1 h2)). Qed.
Lemma lem7163182 (q : Prop) (p : Prop) (r : Prop) : (term21 p q r) = (term21 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7163183 {A B : Type'} (_95871 : B) (_95867 : type830 A B) (_95869 : type1413 A B) (_95870 : A) (_95868 : B -> Prop) : (term549 A B _95871 _95867 _95869 _95870 _95868) = (term570 A B _95871 _95867 _95869 _95870 _95868).
Proof. exact (@lem7163182 (term380 A B _95869 _95870 _95871) (term382 B _95871 _95868) (term375 A B _95867 _95869 _95870 _95868)). Qed.
Lemma lem7163197 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7163198 {A B : Type'} (_95867 : type830 A B) (_95869 : type1413 A B) (_95870 : A) (_95871 : B) (_95868 : B -> Prop) : (term571 A B _95871 _95867 _95869 _95870 _95868) = (term572 A B _95867 _95869 _95870 _95871 _95868).
Proof. exact (@lem7163197 (term375 A B _95867 _95869 _95870 _95868) (term382 B _95871 _95868)). Qed.
Lemma lem7163204 {A B : Type'} (_95869 : type1413 A B) (_95870 : A) (_95871 : B) : (term573 A B _95869 _95870 _95871) = (term573 A B _95869 _95870 _95871).
Proof. exact (eq_refl (term573 A B _95869 _95870 _95871)). Qed.
Lemma lem7163205 {A B : Type'} (_95867 : type830 A B) (_95869 : type1413 A B) (_95870 : A) (_95871 : B) (_95868 : B -> Prop) : (term570 A B _95871 _95867 _95869 _95870 _95868) = (term574 A B _95867 _95869 _95870 _95871 _95868).
Proof. exact (MK_COMB (@lem7163204 A B _95869 _95870 _95871) (@lem7163198 A B _95867 _95869 _95870 _95871 _95868)). Qed.
Lemma lem7163209 (q : Prop) (p : Prop) (r : Prop) : (term21 p q r) = (term21 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7163210 {A B : Type'} (_95867 : type830 A B) (_95869 : type1413 A B) (_95870 : A) (_95871 : B) (_95868 : B -> Prop) : (term574 A B _95867 _95869 _95870 _95871 _95868) = (term575 A B _95867 _95869 _95870 _95871 _95868).
Proof. exact (@lem7163209 (term375 A B _95867 _95869 _95870 _95868) (term380 A B _95869 _95870 _95871) (term382 B _95871 _95868)). Qed.
Lemma lem7163226 {A B : Type'} (_95867 : type830 A B) (_95869 : type1413 A B) (_95870 : A) (_95871 : B) (_95868 : B -> Prop) : (term570 A B _95871 _95867 _95869 _95870 _95868) = (term575 A B _95867 _95869 _95870 _95871 _95868).
Proof. exact (TRANS (@lem7163205 A B _95867 _95869 _95870 _95871 _95868) (@lem7163210 A B _95867 _95869 _95870 _95871 _95868)). Qed.
Lemma lem7163227 {A B : Type'} (_95867 : type830 A B) (_95869 : type1413 A B) (_95870 : A) (_95871 : B) (_95868 : B -> Prop) : (term549 A B _95871 _95867 _95869 _95870 _95868) = (term575 A B _95867 _95869 _95870 _95871 _95868).
Proof. exact (TRANS (@lem7163183 A B _95871 _95867 _95869 _95870 _95868) (@lem7163226 A B _95867 _95869 _95870 _95871 _95868)). Qed.
Lemma lem7163228 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7163229 {A B : Type'} (_95867 : type830 A B) (_95869 : type1413 A B) (_95870 : A) (_95871 : B) (_95868 : B -> Prop) : (term576 A B _95871 _95867 _95869 _95870 _95868) = (term577 A B _95867 _95869 _95870 _95871 _95868).
Proof. exact (MK_COMB (@lem7163228) (@lem7163227 A B _95867 _95869 _95870 _95871 _95868)). Qed.
Lemma lem7163243 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7163244 {A B : Type'} (_95869 : type1413 A B) (_95870 : A) (_95871 : B) (_95868 : B -> Prop) : (term384 A B _95868 _95869 _95870 _95871) = (term578 A B _95869 _95870 _95871 _95868).
Proof. exact (@lem7163243 (term380 A B _95869 _95870 _95871) (term382 B _95871 _95868)). Qed.
Lemma lem7163250 {A B : Type'} (_95867 : type830 A B) (_95869 : type1413 A B) (_95870 : A) (_95868 : B -> Prop) : (term579 A B _95867 _95869 _95870 _95868) = (term579 A B _95867 _95869 _95870 _95868).
Proof. exact (eq_refl (term579 A B _95867 _95869 _95870 _95868)). Qed.
Lemma lem7163251 {A B : Type'} (_95867 : type830 A B) (_95869 : type1413 A B) (_95870 : A) (_95871 : B) (_95868 : B -> Prop) : (term580 A B _95867 _95868 _95869 _95870 _95871) = (term575 A B _95867 _95869 _95870 _95871 _95868).
Proof. exact (MK_COMB (@lem7163250 A B _95867 _95869 _95870 _95868) (@lem7163244 A B _95869 _95870 _95871 _95868)). Qed.
Lemma lem7163262 {A B : Type'} (_95867 : type830 A B) (_95869 : type1413 A B) (_95870 : A) (_95871 : B) (_95868 : B -> Prop) : ((term549 A B _95871 _95867 _95869 _95870 _95868) = (term580 A B _95867 _95868 _95869 _95870 _95871)) = ((term575 A B _95867 _95869 _95870 _95871 _95868) = (term575 A B _95867 _95869 _95870 _95871 _95868)).
Proof. exact (MK_COMB (@lem7163229 A B _95867 _95869 _95870 _95871 _95868) (@lem7163251 A B _95867 _95869 _95870 _95871 _95868)). Qed.
Lemma lem7163264 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7163265 (x : Prop) : (x = x) = True.
Proof. exact (@lem7163264 Prop x). Qed.
Lemma lem7163266 {A B : Type'} (_95867 : type830 A B) (_95869 : type1413 A B) (_95870 : A) (_95871 : B) (_95868 : B -> Prop) : ((term575 A B _95867 _95869 _95870 _95871 _95868) = (term575 A B _95867 _95869 _95870 _95871 _95868)) = True.
Proof. exact (@lem7163265 (term575 A B _95867 _95869 _95870 _95871 _95868)). Qed.
Lemma lem7163267 {A B : Type'} (_95867 : type830 A B) (_95868 : B -> Prop) (_95869 : type1413 A B) (_95870 : A) (_95871 : B) : ((term549 A B _95871 _95867 _95869 _95870 _95868) = (term580 A B _95867 _95868 _95869 _95870 _95871)) = True.
Proof. exact (TRANS (@lem7163262 A B _95867 _95869 _95870 _95871 _95868) (@lem7163266 A B _95867 _95869 _95870 _95871 _95868)). Qed.
Lemma lem7163268 {A B : Type'} (_95867 : type830 A B) (_95868 : B -> Prop) (_95869 : type1413 A B) (_95870 : A) (_95871 : B) : True = ((term549 A B _95871 _95867 _95869 _95870 _95868) = (term580 A B _95867 _95868 _95869 _95870 _95871)).
Proof. exact (SYM (@lem7163267 A B _95867 _95868 _95869 _95870 _95871)). Qed.
Lemma lem7163269 {A B : Type'} (_95867 : type830 A B) (_95868 : B -> Prop) (_95869 : type1413 A B) (_95870 : A) (_95871 : B) : (term549 A B _95871 _95867 _95869 _95870 _95868) = (term580 A B _95867 _95868 _95869 _95870 _95871).
Proof. exact (EQ_MP (@lem7163268 A B _95867 _95868 _95869 _95870 _95871) (@lem0)). Qed.
Lemma lem7163270 {A B : Type'} (_95868 : B -> Prop) (_95869 : type1413 A B) (_95870 : A) (_95871 : B) (_95867 : type830 A B) (h1 : term174 A B _95867) : term580 A B _95867 _95868 _95869 _95870 _95871.
Proof. exact (EQ_MP (@lem7163269 A B _95867 _95868 _95869 _95870 _95871) (@lem7162873 A B _95871 _95869 _95870 _95868 _95867 h1)). Qed.
Lemma lem7163272 (b : Prop) (a : Prop) : (a \/ b) = (term555 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7163273 {A B : Type'} (_95871 : B) (_95867 : type830 A B) (_95869 : type1413 A B) (_95870 : A) (_95868 : B -> Prop) : (term580 A B _95867 _95868 _95869 _95870 _95871) = (term581 A B _95871 _95867 _95869 _95870 _95868).
Proof. exact (@lem7163272 (term384 A B _95868 _95869 _95870 _95871) (term375 A B _95867 _95869 _95870 _95868)). Qed.
Lemma lem7163275 (a : Prop) (b : Prop) : (term582 a b) = (term583 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7163276 {A B : Type'} (_95868 : B -> Prop) (_95869 : type1413 A B) (_95870 : A) (_95871 : B) : (term584 A B _95868 _95869 _95870 _95871) = (term585 A B _95868 _95869 _95870 _95871).
Proof. exact (@lem7163275 (term382 B _95871 _95868) (term380 A B _95869 _95870 _95871)). Qed.
Lemma lem7163278 (a : Prop) : (term203 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7163279 {B : Type'} (_95871 : B) (_95868 : B -> Prop) : (term557 B _95871 _95868) = (term381 B _95871 _95868).
Proof. exact (@lem7163278 (term381 B _95871 _95868)). Qed.
Lemma lem7163280 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7163281 {B : Type'} (_95871 : B) (_95868 : B -> Prop) : (term586 B _95871 _95868) = (term587 B _95871 _95868).
Proof. exact (MK_COMB (@lem7163280) (@lem7163279 B _95871 _95868)). Qed.
Lemma lem7163283 (a : Prop) : (term203 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7163284 {A B : Type'} (_95869 : type1413 A B) (_95870 : A) (_95871 : B) : (term588 A B _95869 _95870 _95871) = (term378 A B _95869 _95870 _95871).
Proof. exact (@lem7163283 (term378 A B _95869 _95870 _95871)). Qed.
Lemma lem7163285 {A B : Type'} (_95868 : B -> Prop) (_95869 : type1413 A B) (_95870 : A) (_95871 : B) : (term585 A B _95868 _95869 _95870 _95871) = (term589 A B _95868 _95869 _95870 _95871).
Proof. exact (MK_COMB (@lem7163281 B _95871 _95868) (@lem7163284 A B _95869 _95870 _95871)). Qed.
Lemma lem7163286 {A B : Type'} (_95868 : B -> Prop) (_95869 : type1413 A B) (_95870 : A) (_95871 : B) : (term584 A B _95868 _95869 _95870 _95871) = (term589 A B _95868 _95869 _95870 _95871).
Proof. exact (TRANS (@lem7163276 A B _95868 _95869 _95870 _95871) (@lem7163285 A B _95868 _95869 _95870 _95871)). Qed.
Lemma lem7163287 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7163288 {A B : Type'} (_95868 : B -> Prop) (_95869 : type1413 A B) (_95870 : A) (_95871 : B) : (term590 A B _95868 _95869 _95870 _95871) = (term591 A B _95868 _95869 _95870 _95871).
Proof. exact (MK_COMB (@lem7163287) (@lem7163286 A B _95868 _95869 _95870 _95871)). Qed.
Lemma lem7163289 {A B : Type'} (_95867 : type830 A B) (_95869 : type1413 A B) (_95870 : A) (_95868 : B -> Prop) : (term375 A B _95867 _95869 _95870 _95868) = (term375 A B _95867 _95869 _95870 _95868).
Proof. exact (eq_refl (term375 A B _95867 _95869 _95870 _95868)). Qed.
Lemma lem7163290 {A B : Type'} (_95871 : B) (_95867 : type830 A B) (_95869 : type1413 A B) (_95870 : A) (_95868 : B -> Prop) : (term581 A B _95871 _95867 _95869 _95870 _95868) = (term592 A B _95871 _95867 _95869 _95870 _95868).
Proof. exact (MK_COMB (@lem7163288 A B _95868 _95869 _95870 _95871) (@lem7163289 A B _95867 _95869 _95870 _95868)). Qed.
Lemma lem7163291 {A B : Type'} (_95871 : B) (_95867 : type830 A B) (_95869 : type1413 A B) (_95870 : A) (_95868 : B -> Prop) : (term580 A B _95867 _95868 _95869 _95870 _95871) = (term592 A B _95871 _95867 _95869 _95870 _95868).
Proof. exact (TRANS (@lem7163273 A B _95871 _95867 _95869 _95870 _95868) (@lem7163290 A B _95871 _95867 _95869 _95870 _95868)). Qed.
Lemma lem7163293 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (s : A -> Prop) (h1 : term361 A B s y t R) (h2 : @IN A x s) : term417 A B t R y x.
Proof. exact (conj (@lem7163116 A B y t R x s h1 h2) (@lem7163176 A B y t R x s h1 h2)). Qed.
Lemma lem7163295 {A B : Type'} (_95871 : B) (_95869 : type1413 A B) (_95870 : A) (_95868 : B -> Prop) (_95867 : type830 A B) (h1 : term174 A B _95867) : term592 A B _95871 _95867 _95869 _95870 _95868.
Proof. exact (EQ_MP (@lem7163291 A B _95871 _95867 _95869 _95870 _95868) (@lem7163270 A B _95868 _95869 _95870 _95871 _95867 h1)). Qed.
Lemma lem7163296 {A B : Type'} (_95871 : B) (_95869 : type1413 A B) (_95870 : A) (_95868 : B -> Prop) (_95867 : type830 A B) (h1 : term174 A B _95867) : term592 A B _95871 _95867 _95869 _95870 _95868.
Proof. exact (@lem7163295 A B _95871 _95869 _95870 _95868 _95867 h1). Qed.
Lemma lem7163297 {A B : Type'} (y : A -> B) (R : type1413 A B) (x : A) (t : B -> Prop) (_95867 : type830 A B) (h1 : term174 A B _95867) : term593 A B y _95867 R x t.
Proof. exact (@lem7163296 A B (@I (A -> B) y x) R x t _95867 h1). Qed.
Lemma lem7163300 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (_95867 : type830 A B) (x : A) (s : A -> Prop) (h1 : term361 A B s y t R) (h2 : term174 A B _95867) (h3 : @IN A x s) : term375 A B _95867 R x t.
Proof. exact (@lem7163297 A B y R x t _95867 h2 (@lem7163293 A B y t R x s h1 h3)). Qed.
Lemma lem7163301 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (_95867 : type830 A B) (x : A) (s : A -> Prop) (h1 : term361 A B s y t R) (h2 : term174 A B _95867) (h3 : @IN A x s) : term594 A B _95867 R x t.
Proof. exact (fun h0 : term395 A B _95867 R x t => @lem7163300 A B y t R _95867 x s h1 h2 h3). Qed.
Lemma lem7163303 (p : Prop) : (term551 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7163304 {A B : Type'} (_95867 : type830 A B) (R : type1413 A B) (x : A) (t : B -> Prop) : (term594 A B _95867 R x t) = (term375 A B _95867 R x t).
Proof. exact (@lem7163303 (term375 A B _95867 R x t)). Qed.
Lemma lem7163305 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (_95867 : type830 A B) (x : A) (s : A -> Prop) (h1 : term361 A B s y t R) (h2 : term174 A B _95867) (h3 : @IN A x s) : term375 A B _95867 R x t.
Proof. exact (EQ_MP (@lem7163304 A B _95867 R x t) (@lem7163301 A B y t R _95867 x s h1 h2 h3)). Qed.
Lemma lem7163308 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7163310 {A B : Type'} (_95867 : type830 A B) (R : type1413 A B) (x : A) (t : B -> Prop) : (term395 A B _95867 R x t) = (term595 A B _95867 R x t).
Proof. exact (@lem7163308 (term375 A B _95867 R x t)). Qed.
Lemma lem7163313 {A B : Type'} (_95867 : type830 A B) (R : type1413 A B) (x : A) (t : B -> Prop) (h1 : term226 A B _95867 R x t) : term595 A B _95867 R x t.
Proof. exact (EQ_MP (@lem7163310 A B _95867 R x t) (@lem7162823 A B _95867 R x t h1)). Qed.
Lemma lem7163316 {A B : Type'} (y : A -> B) (_95867 : type830 A B) (R : type1413 A B) (t : B -> Prop) (x : A) (s : A -> Prop) (h1 : term361 A B s y t R) (h2 : term174 A B _95867) (h3 : term226 A B _95867 R x t) (h4 : @IN A x s) : False.
Proof. exact (@lem7163313 A B _95867 R x t h3 (@lem7163305 A B y t R _95867 x s h1 h2 h4)). Qed.
Lemma lem7163317 {A B : Type'} (y : A -> B) (_95867 : type830 A B) (R : type1413 A B) (t : B -> Prop) (x : A) (s : A -> Prop) (h1 : term361 A B s y t R) (h2 : term174 A B _95867) (h3 : term226 A B _95867 R x t) (h4 : @IN A x s) : term596.
Proof. exact (fun h0 : ~ False => @lem7163316 A B y _95867 R t x s h1 h2 h3 h4). Qed.
Lemma lem7163319 (p : Prop) : (term551 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7163320 : term596 = False.
Proof. exact (@lem7163319 False). Qed.
Lemma lem7163321 {A B : Type'} (y : A -> B) (_95867 : type830 A B) (R : type1413 A B) (t : B -> Prop) (x : A) (s : A -> Prop) (h1 : term361 A B s y t R) (h2 : term174 A B _95867) (h3 : term226 A B _95867 R x t) (h4 : @IN A x s) : False.
Proof. exact (EQ_MP (@lem7163320) (@lem7163317 A B y _95867 R t x s h1 h2 h3 h4)). Qed.
Lemma lem7163322 {A B : Type'} (_95867 : type830 A B) (R : type1413 A B) (t : B -> Prop) (x : A) (s : A -> Prop) (h1 : term34 A B s t R) (h2 : term174 A B _95867) (h3 : term226 A B _95867 R x t) (h4 : @IN A x s) : False.
Proof. exact (ex_elim (@lem7162118 A B s t R h1) (fun y : A -> B => fun h0 : term363 A B s t R y => @lem7163321 A B y _95867 R t x s h0 h2 h3 h4)). Qed.
Lemma lem7163323 {A B : Type'} (_95867 : type830 A B) (R : type1413 A B) (t : B -> Prop) (x : A) (s : A -> Prop) (h1 : term34 A B s t R) (h2 : term174 A B _95867) (h3 : term226 A B _95867 R x t) (h4 : @IN A x s) : (term226 A B _95867 R x t) = False.
Proof. exact (prop_ext (fun h5 : term226 A B _95867 R x t => @lem7163322 A B _95867 R t x s h1 h2 h3 h4) (fun h5 : False => @lem7162130 A B _95867 R x t h3)). Qed.
Lemma lem7163324 {A B : Type'} (_95867 : type830 A B) (R : type1413 A B) (t : B -> Prop) (x : A) (s : A -> Prop) (h1 : term34 A B s t R) (h2 : term174 A B _95867) (h3 : term226 A B _95867 R x t) (h4 : @IN A x s) : False.
Proof. exact (EQ_MP (@lem7163323 A B _95867 R t x s h1 h2 h3 h4) (@lem7162130 A B _95867 R x t h3)). Qed.
Lemma lem7163325 {A B : Type'} (_95867 : type830 A B) (R : type1413 A B) (t : B -> Prop) (x : A) (s : A -> Prop) (h1 : term34 A B s t R) (h2 : term174 A B _95867) (h3 : term226 A B _95867 R x t) (h4 : @IN A x s) : (@IN A x s) = False.
Proof. exact (prop_ext (fun h5 : @IN A x s => @lem7163324 A B _95867 R t x s h1 h2 h3 h4) (fun h5 : False => @lem7162124 A x s h4)). Qed.
Lemma lem7163326 {A B : Type'} (_95867 : type830 A B) (R : type1413 A B) (t : B -> Prop) (x : A) (s : A -> Prop) (h1 : term34 A B s t R) (h2 : term174 A B _95867) (h3 : term226 A B _95867 R x t) (h4 : @IN A x s) : False.
Proof. exact (EQ_MP (@lem7163325 A B _95867 R t x s h1 h2 h3 h4) (@lem7162124 A x s h4)). Qed.
Lemma lem7163327 {A B : Type'} (_95867 : type830 A B) (R : type1413 A B) (t : B -> Prop) (x : A) (s : A -> Prop) (h1 : term34 A B s t R) (h2 : term174 A B _95867) (h3 : term226 A B _95867 R x t) (h4 : @IN A x s) : (term226 A B _95867 R x t) = False.
Proof. exact (prop_ext (fun h5 : term226 A B _95867 R x t => @lem7163326 A B _95867 R t x s h1 h2 h3 h4) (fun h5 : False => @lem7161498 A B _95867 R x t h3)). Qed.
Lemma lem7163328 {A B : Type'} (_95867 : type830 A B) (R : type1413 A B) (t : B -> Prop) (x : A) (s : A -> Prop) (h1 : term34 A B s t R) (h2 : term174 A B _95867) (h3 : term226 A B _95867 R x t) (h4 : @IN A x s) : False.
Proof. exact (EQ_MP (@lem7163327 A B _95867 R t x s h1 h2 h3 h4) (@lem7161498 A B _95867 R x t h3)). Qed.
Lemma lem7163329 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (_95867 : type830 A B) (x : A) (s : A -> Prop) (h1 : term34 A B s t R) (h2 : term174 A B _95867) (h3 : @IN A x s) : term225 A B _95867 R x t.
Proof. exact (fun h0 : term226 A B _95867 R x t => @lem7163328 A B _95867 R t x s h1 h2 h0 h3). Qed.
Lemma lem7163330 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (_95867 : type830 A B) (x : A) (s : A -> Prop) (h1 : term34 A B s t R) (h2 : term174 A B _95867) (h3 : @IN A x s) : term157 A B _95867 R x t.
Proof. exact (EQ_MP (@lem7161497 A B _95867 R x t) (@lem7163329 A B t R _95867 x s h1 h2 h3)). Qed.
Lemma lem7163331 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (_95867 : type830 A B) (h1 : term34 A B s t R) (h2 : term174 A B _95867) : term177 A B s _95867 R x t.
Proof. exact (fun h0 : @IN A x s => @lem7163330 A B t R _95867 x s h1 h2 h0). Qed.
Lemma lem7163336 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (_95867 : type830 A B) (h1 : term34 A B s t R) (h2 : term174 A B _95867) : term179 A B s _95867 R t.
Proof. exact (fun x : A => @lem7163331 A B x s t R _95867 h1 h2). Qed.
Lemma lem7163337 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (_95867 : type830 A B) (h1 : term174 A B _95867) : term204 A B s _95867 R t.
Proof. exact (fun h0 : term34 A B s t R => @lem7163336 A B s t R _95867 h0 h1). Qed.
Lemma lem7163338 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (_95867 : type830 A B) (h1 : term174 A B _95867) : term205 A B s _95867 R t.
Proof. exact (fun h0 : @FINITE A s => @lem7163337 A B s R t _95867 h1). Qed.
Lemma lem7163339 {A B : Type'} (s : A -> Prop) (_95867 : type830 A B) (R : type1413 A B) (t : B -> Prop) : term206 A B s _95867 R t.
Proof. exact (fun h0 : term174 A B _95867 => @lem7163338 A B s R t _95867 h0). Qed.
Lemma lem7163344 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : term209 A B s R t.
Proof. exact (fun _95867 : type830 A B => @lem7163339 A B s _95867 R t). Qed.
Lemma lem7163349 {A B : Type'} (R : type1413 A B) (t : B -> Prop) : term213 A B R t.
Proof. exact (fun s : A -> Prop => @lem7163344 A B s R t). Qed.
Lemma lem7163354 {A B : Type'} (t : B -> Prop) : term217 A B t.
Proof. exact (fun R : type1413 A B => @lem7163349 A B R t). Qed.
Lemma lem7163359 {A B : Type'} : term221 A B.
Proof. exact (fun t : B -> Prop => @lem7163354 A B t). Qed.
Lemma lem7163360 {A B : Type'} : term220 A B.
Proof. exact (EQ_MP (@lem7161489 A B) (@lem7163359 A B)). Qed.
Lemma lem7163361 {A B : Type'} (t : B -> Prop) : term597 A B t.
Proof. exact (@lem7163360 A B t). Qed.
Lemma lem7163362 {A B : Type'} (t : B -> Prop) : (term597 A B t) = (term216 A B t).
Proof. exact (eq_refl (term597 A B t)). Qed.
Lemma lem7163363 {A B : Type'} (t : B -> Prop) : term216 A B t.
Proof. exact (EQ_MP (@lem7163362 A B t) (@lem7163361 A B t)). Qed.
Lemma lem7163364 {A B : Type'} (t : B -> Prop) (R : type1413 A B) : term598 A B t R.
Proof. exact (@lem7163363 A B t R). Qed.
Lemma lem7163365 {A B : Type'} (R : type1413 A B) (t : B -> Prop) : (term598 A B t R) = (term212 A B R t).
Proof. exact (eq_refl (term598 A B t R)). Qed.
Lemma lem7163366 {A B : Type'} (R : type1413 A B) (t : B -> Prop) : term212 A B R t.
Proof. exact (EQ_MP (@lem7163365 A B R t) (@lem7163364 A B t R)). Qed.
Lemma lem7163367 {A B : Type'} (R : type1413 A B) (t : B -> Prop) (s : A -> Prop) : term599 A B R t s.
Proof. exact (@lem7163366 A B R t s). Qed.
Lemma lem7163368 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : (term599 A B R t s) = (term190 A B s R t).
Proof. exact (eq_refl (term599 A B R t s)). Qed.
Lemma lem7163369 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : term190 A B s R t.
Proof. exact (EQ_MP (@lem7163368 A B s R t) (@lem7163367 A B R t s)). Qed.
Lemma lem7163371 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : term141 A B s R t.
Proof. exact (@lem7161228 A B s R t (@lem7163369 A B s R t)). Qed.
Lemma lem7163372 {A B : Type'} (R : type1413 A B) (t : B -> Prop) (s : A -> Prop) (h1 : @FINITE A s) : term185 A B s R t.
Proof. exact (@lem7163371 A B s R t (@lem7160890 A s h1)). Qed.
Lemma lem7163373 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term34 A B s t R) (h2 : @FINITE A s) : term121 A B s R t.
Proof. exact (@lem7163372 A B R t s h2 (@lem7160889 A B s t R h1)). Qed.
Lemma lem7163374 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (h1 : term34 A B s t R) (h2 : @FINITE A s) (h3 : term122 A B s R t) : False.
Proof. exact (@lem7163373 A B t R s h1 h2 (@lem7161084 A B s R t h3)). Qed.
Lemma lem7163375 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (h1 : term34 A B s t R) (h2 : @FINITE A s) (h3 : term122 A B s R t) : (term122 A B s R t) = False.
Proof. exact (prop_ext (fun h4 : term122 A B s R t => @lem7163374 A B s R t h1 h2 h3) (fun h4 : False => @lem7161084 A B s R t h3)). Qed.
Lemma lem7163376 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (h1 : term34 A B s t R) (h2 : @FINITE A s) (h3 : term122 A B s R t) : False.
Proof. exact (EQ_MP (@lem7163375 A B s R t h1 h2 h3) (@lem7161084 A B s R t h3)). Qed.
Lemma lem7163377 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term34 A B s t R) (h2 : @FINITE A s) : term121 A B s R t.
Proof. exact (fun h0 : term122 A B s R t => @lem7163376 A B s R t h1 h2 h0). Qed.
Lemma lem7163378 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term34 A B s t R) (h2 : @FINITE A s) : term81 A B s R t.
Proof. exact (EQ_MP (@lem7161083 A B s R t) (@lem7163377 A B t R s h1 h2)). Qed.
Lemma lem7163379 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (g : A -> real) (h1 : (term109 A B s t R g) = (@sum A s g)) : (term109 A B s t R g) = (@sum A s g).
Proof. exact (h1). Qed.
Lemma lem7163380 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (g : A -> real) (h1 : (term109 A B s t R g) = (@sum A s g)) : (@sum A s g) = (term109 A B s t R g).
Proof. exact (SYM (@lem7163379 A B t R s g h1)). Qed.
Lemma lem7163381 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (g : A -> real) : (term600 A B t s R g) = (term600 A B t s R g).
Proof. exact (eq_refl (term600 A B t s R g)). Qed.
Lemma lem7163382 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (g : A -> real) (h1 : (term109 A B s t R g) = (@sum A s g)) : (term601 A B t R s g) = (term602 A B s t R g).
Proof. exact (MK_COMB (@lem7163381 A B t s R g) (@lem7163380 A B t R s g h1)). Qed.
Lemma lem7163383 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (g : A -> real) : (term602 A B s t R g) = ((term115 A B t s R g) = (term109 A B s t R g)).
Proof. exact (eq_refl (term602 A B s t R g)). Qed.
Lemma lem7163384 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (g : A -> real) : (term603 A B t R s g) = (term603 A B t R s g).
Proof. exact (eq_refl (term603 A B t R s g)). Qed.
Lemma lem7163385 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (g : A -> real) : ((term601 A B t R s g) = (term602 A B s t R g)) = ((term601 A B t R s g) = ((term115 A B t s R g) = (term109 A B s t R g))).
Proof. exact (MK_COMB (@lem7163384 A B t R s g) (@lem7163383 A B s t R g)). Qed.
Lemma lem7163386 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (g : A -> real) : (term601 A B t R s g) = ((term115 A B t s R g) = (@sum A s g)).
Proof. exact (eq_refl (term601 A B t R s g)). Qed.
Lemma lem7163387 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7163388 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (g : A -> real) : (term603 A B t R s g) = (term604 A B t R s g).
Proof. exact (MK_COMB (@lem7163387) (@lem7163386 A B t R s g)). Qed.
Lemma lem7163389 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (g : A -> real) : ((term115 A B t s R g) = (term109 A B s t R g)) = ((term115 A B t s R g) = (term109 A B s t R g)).
Proof. exact (eq_refl ((term115 A B t s R g) = (term109 A B s t R g))). Qed.
Lemma lem7163390 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (g : A -> real) : ((term601 A B t R s g) = ((term115 A B t s R g) = (term109 A B s t R g))) = (((term115 A B t s R g) = (@sum A s g)) = ((term115 A B t s R g) = (term109 A B s t R g))).
Proof. exact (MK_COMB (@lem7163388 A B t R s g) (@lem7163389 A B s t R g)). Qed.
Lemma lem7163391 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (g : A -> real) : ((term601 A B t R s g) = (term602 A B s t R g)) = (((term115 A B t s R g) = (@sum A s g)) = ((term115 A B t s R g) = (term109 A B s t R g))).
Proof. exact (TRANS (@lem7163385 A B s t R g) (@lem7163390 A B s t R g)). Qed.
Lemma lem7163392 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (g : A -> real) (h1 : (term109 A B s t R g) = (@sum A s g)) : ((term115 A B t s R g) = (@sum A s g)) = ((term115 A B t s R g) = (term109 A B s t R g)).
Proof. exact (EQ_MP (@lem7163391 A B s t R g) (@lem7163382 A B t R s g h1)). Qed.
Lemma lem7163393 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (g : A -> real) (h1 : (term109 A B s t R g) = (@sum A s g)) : ((term115 A B t s R g) = (term109 A B s t R g)) = ((term115 A B t s R g) = (@sum A s g)).
Proof. exact (SYM (@lem7163392 A B t R s g h1)). Qed.
Lemma lem7163395 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : term6 _132349 f s g.
Proof. exact (EQ_MP (@lem7160863 _132349 f s g) (@lem7160862 _132349 f s g)). Qed.
Lemma lem7163396 {B : Type'} (f : B -> real) (s : B -> Prop) (g : B -> real) : term6 B f s g.
Proof. exact (@lem7163395 B f s g). Qed.
Lemma lem7163397 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (g : A -> real) : term605 A B s t R g.
Proof. exact (@lem7163396 B (term606 A B s R g) t (term107 A B s t R g)). Qed.
Lemma lem7163398 {B : Type'} (x : B) (t : B -> Prop) (h1 : @IN B x t) : @IN B x t.
Proof. exact (h1). Qed.
Lemma lem7163402 {A B : Type'} (f : A -> B) (y : A) : (term69 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7163403 {B : Type'} (f : B -> real) (y : B) : (term607 B f y) = (f y).
Proof. exact (@lem7163402 B real f y). Qed.
Lemma lem7163404 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (g : A -> real) (x : B) : (term608 A B s R g x) = (term609 A B s R g x).
Proof. exact (@lem7163403 B (term606 A B s R g) x). Qed.
Lemma lem7163405 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (y : B) (g : A -> real) : (term609 A B s R g y) = (term610 A B s R y g).
Proof. exact (eq_refl (term609 A B s R g y)). Qed.
Lemma lem7163406 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (g : A -> real) : (term611 A B s R g) = (term606 A B s R g).
Proof. exact (fun_ext (fun y : B => @lem7163405 A B s R y g)). Qed.
Lemma lem7163407 {B : Type'} (x : B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7163408 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (g : A -> real) (x : B) : (term608 A B s R g x) = (term609 A B s R g x).
Proof. exact (MK_COMB (@lem7163406 A B s R g) (@lem7163407 B x)). Qed.
Lemma lem7163409 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7163410 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (g : A -> real) (x : B) : (term612 A B s R g x) = (term613 A B s R g x).
Proof. exact (MK_COMB (@lem7163409) (@lem7163408 A B s R g x)). Qed.
Lemma lem7163411 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x : B) (g : A -> real) : (term609 A B s R g x) = (term610 A B s R x g).
Proof. exact (eq_refl (term609 A B s R g x)). Qed.
Lemma lem7163412 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x : B) (g : A -> real) : ((term608 A B s R g x) = (term609 A B s R g x)) = ((term609 A B s R g x) = (term610 A B s R x g)).
Proof. exact (MK_COMB (@lem7163410 A B s R g x) (@lem7163411 A B s R x g)). Qed.
Lemma lem7163413 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x : B) (g : A -> real) : (term609 A B s R g x) = (term610 A B s R x g).
Proof. exact (EQ_MP (@lem7163412 A B s R x g) (@lem7163404 A B s R g x)). Qed.
Lemma lem7163420 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7163421 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x : B) (g : A -> real) : (term613 A B s R g x) = (term614 A B s R x g).
Proof. exact (MK_COMB (@lem7163420) (@lem7163413 A B s R x g)). Qed.
Lemma lem7163423 {A B : Type'} (f : A -> B) (y : A) : (term69 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7163424 {B : Type'} (f : B -> real) (y : B) : (term607 B f y) = (f y).
Proof. exact (@lem7163423 B real f y). Qed.
Lemma lem7163425 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (g : A -> real) (x : B) : (term615 A B s t R g x) = (term616 A B s t R g x).
Proof. exact (@lem7163424 B (term107 A B s t R g) x). Qed.
Lemma lem7163426 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (y : B) (g : A -> real) : (term616 A B s t R g y) = (term105 A B s t R y g).
Proof. exact (eq_refl (term616 A B s t R g y)). Qed.
Lemma lem7163427 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (g : A -> real) : (term617 A B s t R g) = (term107 A B s t R g).
Proof. exact (fun_ext (fun y : B => @lem7163426 A B s t R y g)). Qed.
Lemma lem7163428 {B : Type'} (x : B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7163429 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (g : A -> real) (x : B) : (term615 A B s t R g x) = (term616 A B s t R g x).
Proof. exact (MK_COMB (@lem7163427 A B s t R g) (@lem7163428 B x)). Qed.
Lemma lem7163430 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7163431 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (g : A -> real) (x : B) : (term618 A B s t R g x) = (term619 A B s t R g x).
Proof. exact (MK_COMB (@lem7163430) (@lem7163429 A B s t R g x)). Qed.
Lemma lem7163432 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (g : A -> real) : (term616 A B s t R g x) = (term105 A B s t R x g).
Proof. exact (eq_refl (term616 A B s t R g x)). Qed.
Lemma lem7163433 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (g : A -> real) : ((term615 A B s t R g x) = (term616 A B s t R g x)) = ((term616 A B s t R g x) = (term105 A B s t R x g)).
Proof. exact (MK_COMB (@lem7163431 A B s t R g x) (@lem7163432 A B s t R x g)). Qed.
Lemma lem7163434 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (g : A -> real) : (term616 A B s t R g x) = (term105 A B s t R x g).
Proof. exact (EQ_MP (@lem7163433 A B s t R x g) (@lem7163425 A B s t R g x)). Qed.
Lemma lem7163445 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (g : A -> real) : ((term609 A B s R g x) = (term616 A B s t R g x)) = ((term610 A B s R x g) = (term105 A B s t R x g)).
Proof. exact (MK_COMB (@lem7163421 A B s R x g) (@lem7163434 A B s t R x g)). Qed.
Lemma lem7163448 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (g : A -> real) (x : B) : ((term610 A B s R x g) = (term105 A B s t R x g)) = ((term609 A B s R g x) = (term616 A B s t R g x)).
Proof. exact (SYM (@lem7163445 A B s t R x g)). Qed.
Lemma lem7163449 {A : Type'} (g : A -> real) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7163450 {A : Type'} : (@sum A) = (@sum A).
Proof. exact (eq_refl (@sum A)). Qed.
Lemma lem7163451 (t1 : Prop) : term16 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem7163452 (t1 : Prop) : (term16 t1) = (term17 t1).
Proof. exact (eq_refl (term16 t1)). Qed.
Lemma lem7163453 (t1 : Prop) : term17 t1.
Proof. exact (EQ_MP (@lem7163452 t1) (@lem7163451 t1)). Qed.
Lemma lem7163454 (t1 : Prop) (t2 : Prop) : term18 t1 t2.
Proof. exact (@lem7163453 t1 t2). Qed.
Lemma lem7163455 (t1 : Prop) (t2 : Prop) : (term18 t1 t2) = (term19 t1 t2).
Proof. exact (eq_refl (term18 t1 t2)). Qed.
Lemma lem7163456 (t1 : Prop) (t2 : Prop) : term19 t1 t2.
Proof. exact (EQ_MP (@lem7163455 t1 t2) (@lem7163454 t1 t2)). Qed.
Lemma lem7163457 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term20 t1 t2 t3.
Proof. exact (@lem7163456 t1 t2 t3). Qed.
Lemma lem7163458 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term20 t1 t2 t3) = ((term21 t1 t2 t3) = (term22 t1 t2 t3)).
Proof. exact (eq_refl (term20 t1 t2 t3)). Qed.
Lemma lem7163459 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term21 t1 t2 t3) = (term22 t1 t2 t3).
Proof. exact (EQ_MP (@lem7163458 t1 t2 t3) (@lem7163457 t1 t2 t3)). Qed.
Lemma lem7163460 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term22 t1 t2 t3) = (term21 t1 t2 t3).
Proof. exact (SYM (@lem7163459 t1 t2 t3)). Qed.
Lemma lem7163461 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term34 A B s t R) (h2 : @FINITE A s) : term620 A B t R s.
Proof. exact (conj (@lem7160889 A B s t R h1) (@lem7160890 A s h2)). Qed.
Lemma lem7163462 {A B : Type'} (R : type1413 A B) (s : A -> Prop) (x : B) (t : B -> Prop) (h1 : term34 A B s t R) (h2 : @FINITE A s) (h3 : @IN B x t) : term621 A B x t R s.
Proof. exact (conj (@lem7163398 B x t h3) (@lem7163461 A B t R s h1 h2)). Qed.
Lemma lem7163480 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term622 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem7163481 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term622 A s t).
Proof. exact (@lem7163480 A s t). Qed.
Lemma lem7163482 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : ((term623 A B s R x) = (term101 A B s t R x)) = (term624 A B s t R x).
Proof. exact (@lem7163481 A (term623 A B s R x) (term101 A B s t R x)). Qed.
Lemma lem7163509 {A B : Type'} (x : B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term625 A B x t R s) = (term625 A B x t R s).
Proof. exact (eq_refl (term625 A B x t R s)). Qed.
Lemma lem7163510 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : (term626 A B s t R x) = (term627 A B s t R x).
Proof. exact (MK_COMB (@lem7163509 A B x t R s) (@lem7163482 A B s t R x)). Qed.
Lemma lem7163513 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : (term627 A B s t R x) = (term626 A B s t R x).
Proof. exact (SYM (@lem7163510 A B s t R x)). Qed.
Lemma lem7163519 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem7163520 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem7163519 B P x). Qed.
Lemma lem7163521 {B : Type'} (t : B -> Prop) (x : B) : (@IN B x t) = (t x).
Proof. exact (@lem7163520 B t x). Qed.
Lemma lem7163522 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7163523 {B : Type'} (t : B -> Prop) (x : B) : (term87 B x t) = (term628 B t x).
Proof. exact (MK_COMB (@lem7163522) (@lem7163521 B t x)). Qed.
Lemma lem7163533 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem7163534 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem7163533 A P x). Qed.
Lemma lem7163535 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem7163534 A s x). Qed.
Lemma lem7163536 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7163537 {A : Type'} (s : A -> Prop) (x : A) : (term63 A x s) = (term629 A s x).
Proof. exact (MK_COMB (@lem7163536) (@lem7163535 A s x)). Qed.
Lemma lem7163541 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem7163542 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem7163541 B P x). Qed.
Lemma lem7163543 {B : Type'} (t : B -> Prop) (y : B) : (@IN B y t) = (t y).
Proof. exact (@lem7163542 B t y). Qed.
Lemma lem7163544 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7163545 {B : Type'} (t : B -> Prop) (y : B) : (term87 B y t) = (term628 B t y).
Proof. exact (MK_COMB (@lem7163544) (@lem7163543 B t y)). Qed.
Lemma lem7163546 {A B : Type'} (R : type1413 A B) (x : A) (y : B) : (R x y) = (R x y).
Proof. exact (eq_refl (R x y)). Qed.
Lemma lem7163547 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term129 A B t R x y) = (term630 A B t R x y).
Proof. exact (MK_COMB (@lem7163545 B t y) (@lem7163546 A B R x y)). Qed.
Lemma lem7163550 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term125 A B t R x) = (term631 A B t R x).
Proof. exact (fun_ext (fun y : B => @lem7163547 A B t R x y)). Qed.
Lemma lem7163551 {B : Type'} : (@ex1 B) = (@ex1 B).
Proof. exact (eq_refl (@ex1 B)). Qed.
Lemma lem7163552 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term222 A B t R x) = (term632 A B t R x).
Proof. exact (MK_COMB (@lem7163551 B) (@lem7163550 A B t R x)). Qed.
Lemma lem7163553 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term223 A B s t R x) = (term633 A B s t R x).
Proof. exact (MK_COMB (@lem7163537 A s x) (@lem7163552 A B t R x)). Qed.
Lemma lem7163556 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term224 A B s t R) = (term634 A B s t R).
Proof. exact (fun_ext (fun x : A => @lem7163553 A B s t R x)). Qed.
Lemma lem7163557 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7163558 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term34 A B s t R) = (term635 A B s t R).
Proof. exact (MK_COMB (@lem7163557 A) (@lem7163556 A B s t R)). Qed.
Lemma lem7163563 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7163564 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term636 A B s t R) = (term637 A B s t R).
Proof. exact (MK_COMB (@lem7163563) (@lem7163558 A B s t R)). Qed.
Lemma lem7163565 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem7163566 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term620 A B t R s) = (term638 A B t R s).
Proof. exact (MK_COMB (@lem7163564 A B s t R) (@lem7163565 A s)). Qed.
Lemma lem7163569 {A B : Type'} (x : B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term621 A B x t R s) = (term639 A B x t R s).
Proof. exact (MK_COMB (@lem7163523 B t x) (@lem7163566 A B t R s)). Qed.
Lemma lem7163572 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7163573 {A B : Type'} (x : B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term625 A B x t R s) = (term640 A B x t R s).
Proof. exact (MK_COMB (@lem7163572) (@lem7163569 A B x t R s)). Qed.
Lemma lem7163581 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term641 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem7163582 {A : Type'} (p : A -> Prop) (x : A) : (term641 A x p) = (p x).
Proof. exact (@lem7163581 A p x). Qed.
Lemma lem7163583 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x : B) (x' : A) : (term642 A B x' s R x) = (term643 A B s R x x').
Proof. exact (@lem7163582 A (term644 A B s R x) x'). Qed.
Lemma lem7163584 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term643 A B s R x' x) = (term645 A B s R x x').
Proof. exact (eq_refl (term643 A B s R x' x)). Qed.
Lemma lem7163585 {A : Type'} (GEN_PVAR_326 : A) : (@SETSPEC A GEN_PVAR_326) = (@SETSPEC A GEN_PVAR_326).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_326)). Qed.
Lemma lem7163586 {A B : Type'} (GEN_PVAR_326 : A) (s : A -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term646 A B GEN_PVAR_326 s R x' x) = (term647 A B GEN_PVAR_326 s R x x').
Proof. exact (MK_COMB (@lem7163585 A GEN_PVAR_326) (@lem7163584 A B s R x x')). Qed.
Lemma lem7163587 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7163588 {A B : Type'} (GEN_PVAR_326 : A) (s : A -> Prop) (R : type1413 A B) (x : B) (x' : A) : (term648 A B GEN_PVAR_326 s R x x') = (term649 A B GEN_PVAR_326 s R x x').
Proof. exact (MK_COMB (@lem7163586 A B GEN_PVAR_326 s R x' x) (@lem7163587 A x')). Qed.
Lemma lem7163589 {A B : Type'} (GEN_PVAR_326 : A) (s : A -> Prop) (R : type1413 A B) (x : B) : (term650 A B GEN_PVAR_326 s R x) = (term651 A B GEN_PVAR_326 s R x).
Proof. exact (fun_ext (fun x' : A => @lem7163588 A B GEN_PVAR_326 s R x x')). Qed.
Lemma lem7163590 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7163591 {A B : Type'} (GEN_PVAR_326 : A) (s : A -> Prop) (R : type1413 A B) (x : B) : (term652 A B GEN_PVAR_326 s R x) = (term653 A B GEN_PVAR_326 s R x).
Proof. exact (MK_COMB (@lem7163590 A) (@lem7163589 A B GEN_PVAR_326 s R x)). Qed.
Lemma lem7163592 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x : B) : (term654 A B s R x) = (term655 A B s R x).
Proof. exact (fun_ext (fun GEN_PVAR_326 : A => @lem7163591 A B GEN_PVAR_326 s R x)). Qed.
Lemma lem7163593 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem7163594 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x : B) : (term656 A B s R x) = (term623 A B s R x).
Proof. exact (MK_COMB (@lem7163593 A) (@lem7163592 A B s R x)). Qed.
Lemma lem7163595 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem7163596 {A B : Type'} (x : A) (s : A -> Prop) (R : type1413 A B) (x' : B) : (term642 A B x s R x') = (term657 A B x s R x').
Proof. exact (MK_COMB (@lem7163595 A x) (@lem7163594 A B s R x')). Qed.
Lemma lem7163597 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7163598 {A B : Type'} (x : A) (s : A -> Prop) (R : type1413 A B) (x' : B) : (term658 A B x s R x') = (term659 A B x s R x').
Proof. exact (MK_COMB (@lem7163597) (@lem7163596 A B x s R x')). Qed.
Lemma lem7163599 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term643 A B s R x' x) = (term645 A B s R x x').
Proof. exact (eq_refl (term643 A B s R x' x)). Qed.
Lemma lem7163600 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x : A) (x' : B) : ((term642 A B x s R x') = (term643 A B s R x' x)) = ((term657 A B x s R x') = (term645 A B s R x x')).
Proof. exact (MK_COMB (@lem7163598 A B x s R x') (@lem7163599 A B s R x x')). Qed.
Lemma lem7163601 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term657 A B x s R x') = (term645 A B s R x x').
Proof. exact (EQ_MP (@lem7163600 A B s R x x') (@lem7163583 A B s R x' x)). Qed.
Lemma lem7163605 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem7163606 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem7163605 A P x). Qed.
Lemma lem7163607 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem7163606 A s x). Qed.
Lemma lem7163608 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7163609 {A : Type'} (s : A -> Prop) (x : A) : (term87 A x s) = (term628 A s x).
Proof. exact (MK_COMB (@lem7163608) (@lem7163607 A s x)). Qed.
Lemma lem7163610 {A B : Type'} (R : type1413 A B) (x : A) (x' : B) : (R x x') = (R x x').
Proof. exact (eq_refl (R x x')). Qed.
Lemma lem7163611 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term645 A B s R x x') = (term660 A B s R x x').
Proof. exact (MK_COMB (@lem7163609 A s x) (@lem7163610 A B R x x')). Qed.
Lemma lem7163614 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term657 A B x s R x') = (term660 A B s R x x').
Proof. exact (TRANS (@lem7163601 A B s R x x') (@lem7163611 A B s R x x')). Qed.
Lemma lem7163615 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7163616 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term659 A B x s R x') = (term661 A B s R x x').
Proof. exact (MK_COMB (@lem7163615) (@lem7163614 A B s R x x')). Qed.
Lemma lem7163618 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term641 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem7163619 {A : Type'} (p : A -> Prop) (x : A) : (term641 A x p) = (p x).
Proof. exact (@lem7163618 A p x). Qed.
Lemma lem7163620 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (x' : A) : (term662 A B x' s t R x) = (term663 A B s t R x x').
Proof. exact (@lem7163619 A (term664 A B s t R x) x'). Qed.
Lemma lem7163621 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term663 A B s t R x' x) = (term89 A B s t R x x').
Proof. exact (eq_refl (term663 A B s t R x' x)). Qed.
Lemma lem7163622 {A : Type'} (GEN_PVAR_325 : A) : (@SETSPEC A GEN_PVAR_325) = (@SETSPEC A GEN_PVAR_325).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_325)). Qed.
Lemma lem7163623 {A B : Type'} (GEN_PVAR_325 : A) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term665 A B GEN_PVAR_325 s t R x' x) = (term91 A B GEN_PVAR_325 s t R x x').
Proof. exact (MK_COMB (@lem7163622 A GEN_PVAR_325) (@lem7163621 A B s t R x x')). Qed.
Lemma lem7163624 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7163625 {A B : Type'} (GEN_PVAR_325 : A) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (x' : A) : (term666 A B GEN_PVAR_325 s t R x x') = (term93 A B GEN_PVAR_325 s t R x x').
Proof. exact (MK_COMB (@lem7163623 A B GEN_PVAR_325 s t R x' x) (@lem7163624 A x')). Qed.
Lemma lem7163626 {A B : Type'} (GEN_PVAR_325 : A) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : (term667 A B GEN_PVAR_325 s t R x) = (term95 A B GEN_PVAR_325 s t R x).
Proof. exact (fun_ext (fun x' : A => @lem7163625 A B GEN_PVAR_325 s t R x x')). Qed.
Lemma lem7163627 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7163628 {A B : Type'} (GEN_PVAR_325 : A) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : (term668 A B GEN_PVAR_325 s t R x) = (term97 A B GEN_PVAR_325 s t R x).
Proof. exact (MK_COMB (@lem7163627 A) (@lem7163626 A B GEN_PVAR_325 s t R x)). Qed.
Lemma lem7163629 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : (term669 A B s t R x) = (term99 A B s t R x).
Proof. exact (fun_ext (fun GEN_PVAR_325 : A => @lem7163628 A B GEN_PVAR_325 s t R x)). Qed.
Lemma lem7163630 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem7163631 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : (term670 A B s t R x) = (term101 A B s t R x).
Proof. exact (MK_COMB (@lem7163630 A) (@lem7163629 A B s t R x)). Qed.
Lemma lem7163632 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem7163633 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x' : B) : (term662 A B x s t R x') = (term671 A B x s t R x').
Proof. exact (MK_COMB (@lem7163632 A x) (@lem7163631 A B s t R x')). Qed.
Lemma lem7163634 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7163635 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x' : B) : (term672 A B x s t R x') = (term673 A B x s t R x').
Proof. exact (MK_COMB (@lem7163634) (@lem7163633 A B x s t R x')). Qed.
Lemma lem7163636 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term663 A B s t R x' x) = (term89 A B s t R x x').
Proof. exact (eq_refl (term663 A B s t R x' x)). Qed.
Lemma lem7163637 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : ((term662 A B x s t R x') = (term663 A B s t R x' x)) = ((term671 A B x s t R x') = (term89 A B s t R x x')).
Proof. exact (MK_COMB (@lem7163635 A B x s t R x') (@lem7163636 A B s t R x x')). Qed.
Lemma lem7163638 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term671 A B x s t R x') = (term89 A B s t R x x').
Proof. exact (EQ_MP (@lem7163637 A B s t R x x') (@lem7163620 A B s t R x' x)). Qed.
Lemma lem7163642 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem7163643 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem7163642 A P x). Qed.
Lemma lem7163644 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem7163643 A s x). Qed.
Lemma lem7163645 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7163646 {A : Type'} (s : A -> Prop) (x : A) : (term87 A x s) = (term628 A s x).
Proof. exact (MK_COMB (@lem7163645) (@lem7163644 A s x)). Qed.
Lemma lem7163652 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem7163653 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem7163652 B P x). Qed.
Lemma lem7163654 {B : Type'} (t : B -> Prop) (y : B) : (@IN B y t) = (t y).
Proof. exact (@lem7163653 B t y). Qed.
Lemma lem7163655 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7163656 {B : Type'} (t : B -> Prop) (y : B) : (term87 B y t) = (term628 B t y).
Proof. exact (MK_COMB (@lem7163655) (@lem7163654 B t y)). Qed.
Lemma lem7163657 {A B : Type'} (R : type1413 A B) (x : A) (y : B) : (R x y) = (R x y).
Proof. exact (eq_refl (R x y)). Qed.
Lemma lem7163658 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term129 A B t R x y) = (term630 A B t R x y).
Proof. exact (MK_COMB (@lem7163656 B t y) (@lem7163657 A B R x y)). Qed.
Lemma lem7163661 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term125 A B t R x) = (term631 A B t R x).
Proof. exact (fun_ext (fun y : B => @lem7163658 A B t R x y)). Qed.
Lemma lem7163662 {B : Type'} : (@ε B) = (@ε B).
Proof. exact (eq_refl (@ε B)). Qed.
Lemma lem7163663 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term72 A B t R x) = (term674 A B t R x).
Proof. exact (MK_COMB (@lem7163662 B) (@lem7163661 A B t R x)). Qed.
Lemma lem7163664 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem7163665 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term86 A B t R x) = (term675 A B t R x).
Proof. exact (MK_COMB (@lem7163664 B) (@lem7163663 A B t R x)). Qed.
Lemma lem7163666 {B : Type'} (x : B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7163667 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : ((term72 A B t R x) = x') = ((term674 A B t R x) = x').
Proof. exact (MK_COMB (@lem7163665 A B t R x) (@lem7163666 B x')). Qed.
Lemma lem7163670 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term89 A B s t R x x') = (term676 A B s t R x x').
Proof. exact (MK_COMB (@lem7163646 A s x) (@lem7163667 A B t R x x')). Qed.
Lemma lem7163673 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term671 A B x s t R x') = (term676 A B s t R x x').
Proof. exact (TRANS (@lem7163638 A B s t R x x') (@lem7163670 A B s t R x x')). Qed.
Lemma lem7163674 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : ((term657 A B x s R x') = (term671 A B x s t R x')) = ((term660 A B s R x x') = (term676 A B s t R x x')).
Proof. exact (MK_COMB (@lem7163616 A B s R x x') (@lem7163673 A B s t R x x')). Qed.
Lemma lem7163677 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : (term677 A B s t R x) = (term678 A B s t R x).
Proof. exact (fun_ext (fun x' : A => @lem7163674 A B s t R x' x)). Qed.
Lemma lem7163678 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7163679 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : (term624 A B s t R x) = (term679 A B s t R x).
Proof. exact (MK_COMB (@lem7163678 A) (@lem7163677 A B s t R x)). Qed.
Lemma lem7163684 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : (term627 A B s t R x) = (term680 A B s t R x).
Proof. exact (MK_COMB (@lem7163573 A B x t R s) (@lem7163679 A B s t R x)). Qed.
Lemma lem7163687 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : (term680 A B s t R x) = (term627 A B s t R x).
Proof. exact (SYM (@lem7163684 A B s t R x)). Qed.
Lemma lem7163689 (p : Prop) : p = (term120 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7163690 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : (term680 A B s t R x) = (term681 A B s t R x).
Proof. exact (@lem7163689 (term680 A B s t R x)). Qed.
Lemma lem7163691 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : (term681 A B s t R x) = (term680 A B s t R x).
Proof. exact (SYM (@lem7163690 A B s t R x)). Qed.
Lemma lem7163692 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (h1 : term682 A B s t R x) : term682 A B s t R x.
Proof. exact (h1). Qed.
Lemma lem7163715 {B : Type'} (P : B -> Prop) : term123 B P.
Proof. exact (@lem19732 B P). Qed.
Lemma lem7163716 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : term683 A B t R x.
Proof. exact (@lem7163715 B (term631 A B t R x)). Qed.
Lemma lem7163717 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term684 A B t R x) = (term685 A B t R x).
Proof. exact (eq_refl (term684 A B t R x)). Qed.
Lemma lem7163718 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term686 A B t R x x') = (term630 A B t R x x').
Proof. exact (eq_refl (term686 A B t R x x')). Qed.
Lemma lem7163719 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7163720 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term687 A B t R x x') = (term688 A B t R x x').
Proof. exact (MK_COMB (@lem7163719) (@lem7163718 A B t R x x')). Qed.
Lemma lem7163721 {A B : Type'} (x : B) (t : B -> Prop) (R : type1413 A B) (x' : A) : (term689 A B x t R x') = (term690 A B x t R x').
Proof. exact (MK_COMB (@lem7163720 A B t R x' x) (@lem7163717 A B t R x')). Qed.
Lemma lem7163722 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term691 A B t R x) = (term692 A B t R x).
Proof. exact (fun_ext (fun x' : B => @lem7163721 A B x' t R x)). Qed.
Lemma lem7163723 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7163724 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term683 A B t R x) = (term693 A B t R x).
Proof. exact (MK_COMB (@lem7163723 B) (@lem7163722 A B t R x)). Qed.
Lemma lem7163725 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : term693 A B t R x.
Proof. exact (EQ_MP (@lem7163724 A B t R x) (@lem7163716 A B t R x)). Qed.
Lemma lem7163726 {A B : Type'} (t : B -> Prop) (R : type1413 A B) : term694 A B t R.
Proof. exact (fun x : A => @lem7163725 A B t R x). Qed.
Lemma lem7163727 {A B : Type'} (t : B -> Prop) : term695 A B t.
Proof. exact (fun R : type1413 A B => @lem7163726 A B t R). Qed.
Lemma lem7163728 {A B : Type'} : term696 A B.
Proof. exact (fun t : B -> Prop => @lem7163727 A B t). Qed.
Lemma lem7163729 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (h1 : term697 A B s t R x) : term697 A B s t R x.
Proof. exact (h1). Qed.
Lemma lem7163730 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (h1 : term697 A B s t R x) : term681 A B s t R x.
Proof. exact (@lem7163729 A B s t R x h1 (@lem7163728 A B)). Qed.
Lemma lem7163731 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : term698 A B s t R x.
Proof. exact (fun h0 : term697 A B s t R x => @lem7163730 A B s t R x h0). Qed.
Lemma lem7163732 {A B : Type'} (_95913 : type830 A B) (h1 : _95913 = (term699 A B)) : _95913 = (term699 A B).
Proof. exact (h1). Qed.
Lemma lem7163733 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem7163734 {A B : Type'} (t : B -> Prop) (_95913 : type830 A B) (h1 : _95913 = (term699 A B)) : (_95913 t) = (term700 A B t).
Proof. exact (MK_COMB (@lem7163732 A B _95913 h1) (@lem7163733 B t)). Qed.
Lemma lem7163735 {A B : Type'} (t : B -> Prop) : (term700 A B t) = (term701 A B t).
Proof. exact (eq_refl (term700 A B t)). Qed.
Lemma lem7163736 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) : (term146 A B _95913 t) = (term146 A B _95913 t).
Proof. exact (eq_refl (term146 A B _95913 t)). Qed.
Lemma lem7163737 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) : ((_95913 t) = (term700 A B t)) = ((_95913 t) = (term701 A B t)).
Proof. exact (MK_COMB (@lem7163736 A B _95913 t) (@lem7163735 A B t)). Qed.
Lemma lem7163738 {A B : Type'} (t : B -> Prop) (_95913 : type830 A B) (h1 : _95913 = (term699 A B)) : (_95913 t) = (term701 A B t).
Proof. exact (EQ_MP (@lem7163737 A B _95913 t) (@lem7163734 A B t _95913 h1)). Qed.
Lemma lem7163739 {A B : Type'} (R : type1413 A B) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem7163740 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (_95913 : type830 A B) (h1 : _95913 = (term699 A B)) : (_95913 t R) = (term702 A B t R).
Proof. exact (MK_COMB (@lem7163738 A B t _95913 h1) (@lem7163739 A B R)). Qed.
Lemma lem7163741 {A B : Type'} (t : B -> Prop) (R : type1413 A B) : (term702 A B t R) = (term703 A B t R).
Proof. exact (eq_refl (term702 A B t R)). Qed.
Lemma lem7163742 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (term148 A B _95913 t R) = (term148 A B _95913 t R).
Proof. exact (eq_refl (term148 A B _95913 t R)). Qed.
Lemma lem7163743 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) : ((_95913 t R) = (term702 A B t R)) = ((_95913 t R) = (term703 A B t R)).
Proof. exact (MK_COMB (@lem7163742 A B _95913 t R) (@lem7163741 A B t R)). Qed.
Lemma lem7163744 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (_95913 : type830 A B) (h1 : _95913 = (term699 A B)) : (_95913 t R) = (term703 A B t R).
Proof. exact (EQ_MP (@lem7163743 A B _95913 t R) (@lem7163740 A B t R _95913 h1)). Qed.
Lemma lem7163745 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7163746 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (_95913 : type830 A B) (h1 : _95913 = (term699 A B)) : (_95913 t R x) = (term704 A B t R x).
Proof. exact (MK_COMB (@lem7163744 A B t R _95913 h1) (@lem7163745 A x)). Qed.
Lemma lem7163747 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term704 A B t R x) = (term674 A B t R x).
Proof. exact (eq_refl (term704 A B t R x)). Qed.
Lemma lem7163748 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term149 A B _95913 t R x) = (term149 A B _95913 t R x).
Proof. exact (eq_refl (term149 A B _95913 t R x)). Qed.
Lemma lem7163749 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : ((_95913 t R x) = (term704 A B t R x)) = ((_95913 t R x) = (term674 A B t R x)).
Proof. exact (MK_COMB (@lem7163748 A B _95913 t R x) (@lem7163747 A B t R x)). Qed.
Lemma lem7163750 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (_95913 : type830 A B) (h1 : _95913 = (term699 A B)) : (_95913 t R x) = (term674 A B t R x).
Proof. exact (EQ_MP (@lem7163749 A B _95913 t R x) (@lem7163746 A B t R x _95913 h1)). Qed.
Lemma lem7163751 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (_95913 : type830 A B) (h1 : _95913 = (term699 A B)) : (term674 A B t R x) = (_95913 t R x).
Proof. exact (SYM (@lem7163750 A B t R x _95913 h1)). Qed.
Lemma lem7163752 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (_95913 : type830 A B) (h1 : _95913 = (term699 A B)) : term705 A B _95913 t R.
Proof. exact (fun x : A => @lem7163751 A B t R x _95913 h1). Qed.
Lemma lem7163753 {A B : Type'} (t : B -> Prop) (_95913 : type830 A B) (h1 : _95913 = (term699 A B)) : term706 A B _95913 t.
Proof. exact (fun R : type1413 A B => @lem7163752 A B t R _95913 h1). Qed.
Lemma lem7163754 {A B : Type'} (_95913 : type830 A B) (h1 : _95913 = (term699 A B)) : term707 A B _95913.
Proof. exact (fun t : B -> Prop => @lem7163753 A B t _95913 h1). Qed.
Lemma lem7163755 {A B : Type'} (t : B -> Prop) (_95913 : type830 A B) (h1 : _95913 = (term699 A B)) : term708 A B _95913 t.
Proof. exact (@lem7163754 A B _95913 h1 t). Qed.
Lemma lem7163756 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) : (term708 A B _95913 t) = (term706 A B _95913 t).
Proof. exact (eq_refl (term708 A B _95913 t)). Qed.
Lemma lem7163757 {A B : Type'} (t : B -> Prop) (_95913 : type830 A B) (h1 : _95913 = (term699 A B)) : term706 A B _95913 t.
Proof. exact (EQ_MP (@lem7163756 A B _95913 t) (@lem7163755 A B t _95913 h1)). Qed.
Lemma lem7163758 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (_95913 : type830 A B) (h1 : _95913 = (term699 A B)) : term709 A B _95913 t R.
Proof. exact (@lem7163757 A B t _95913 h1 R). Qed.
Lemma lem7163759 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (term709 A B _95913 t R) = (term705 A B _95913 t R).
Proof. exact (eq_refl (term709 A B _95913 t R)). Qed.
Lemma lem7163760 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (_95913 : type830 A B) (h1 : _95913 = (term699 A B)) : term705 A B _95913 t R.
Proof. exact (EQ_MP (@lem7163759 A B _95913 t R) (@lem7163758 A B t R _95913 h1)). Qed.
Lemma lem7163761 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (_95913 : type830 A B) (h1 : _95913 = (term699 A B)) : term710 A B _95913 t R x.
Proof. exact (@lem7163760 A B t R _95913 h1 x). Qed.
Lemma lem7163762 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term710 A B _95913 t R x) = ((term674 A B t R x) = (_95913 t R x)).
Proof. exact (eq_refl (term710 A B _95913 t R x)). Qed.
Lemma lem7163765 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (_95913 : type830 A B) (h1 : _95913 = (term699 A B)) : (term674 A B t R x) = (_95913 t R x).
Proof. exact (EQ_MP (@lem7163762 A B _95913 t R x) (@lem7163761 A B t R x _95913 h1)). Qed.
Lemma lem7163766 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (_95913 : type830 A B) (h1 : _95913 = (term699 A B)) : (term674 A B t R x) = (_95913 t R x).
Proof. exact (@lem7163765 A B t R x _95913 h1). Qed.
Lemma lem7163767 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem7163768 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (_95913 : type830 A B) (h1 : _95913 = (term699 A B)) : (term711 A B t R x) = (term712 A B _95913 t R x).
Proof. exact (MK_COMB (@lem7163767 B t) (@lem7163766 A B t R x _95913 h1)). Qed.
Lemma lem7163769 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7163770 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (_95913 : type830 A B) (h1 : _95913 = (term699 A B)) : (term713 A B t R x) = (term714 A B _95913 t R x).
Proof. exact (MK_COMB (@lem7163769) (@lem7163768 A B t R x _95913 h1)). Qed.
Lemma lem7163772 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (_95913 : type830 A B) (h1 : _95913 = (term699 A B)) : (term674 A B t R x) = (_95913 t R x).
Proof. exact (EQ_MP (@lem7163762 A B _95913 t R x) (@lem7163761 A B t R x _95913 h1)). Qed.
Lemma lem7163773 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (_95913 : type830 A B) (h1 : _95913 = (term699 A B)) : (term674 A B t R x) = (_95913 t R x).
Proof. exact (@lem7163772 A B t R x _95913 h1). Qed.
Lemma lem7163774 {A B : Type'} (R : type1413 A B) (x : A) : (R x) = (R x).
Proof. exact (eq_refl (R x)). Qed.
Lemma lem7163775 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (_95913 : type830 A B) (h1 : _95913 = (term699 A B)) : (term715 A B t R x) = (term161 A B _95913 t R x).
Proof. exact (MK_COMB (@lem7163774 A B R x) (@lem7163773 A B t R x _95913 h1)). Qed.
Lemma lem7163776 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (_95913 : type830 A B) (h1 : _95913 = (term699 A B)) : (term685 A B t R x) = (term716 A B _95913 t R x).
Proof. exact (MK_COMB (@lem7163770 A B t R x _95913 h1) (@lem7163775 A B t R x _95913 h1)). Qed.
Lemma lem7163777 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term688 A B t R x x') = (term688 A B t R x x').
Proof. exact (eq_refl (term688 A B t R x x')). Qed.
Lemma lem7163778 {A B : Type'} (x : B) (t : B -> Prop) (R : type1413 A B) (x' : A) (_95913 : type830 A B) (h1 : _95913 = (term699 A B)) : (term690 A B x t R x') = (term717 A B x _95913 t R x').
Proof. exact (MK_COMB (@lem7163777 A B t R x' x) (@lem7163776 A B t R x' _95913 h1)). Qed.
Lemma lem7163779 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (_95913 : type830 A B) (h1 : _95913 = (term699 A B)) : (term692 A B t R x) = (term718 A B _95913 t R x).
Proof. exact (fun_ext (fun x' : B => @lem7163778 A B x' t R x _95913 h1)). Qed.
Lemma lem7163780 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7163781 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (_95913 : type830 A B) (h1 : _95913 = (term699 A B)) : (term693 A B t R x) = (term719 A B _95913 t R x).
Proof. exact (MK_COMB (@lem7163780 B) (@lem7163779 A B t R x _95913 h1)). Qed.
Lemma lem7163782 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (_95913 : type830 A B) (h1 : _95913 = (term699 A B)) : (term720 A B t R) = (term721 A B _95913 t R).
Proof. exact (fun_ext (fun x : A => @lem7163781 A B t R x _95913 h1)). Qed.
Lemma lem7163783 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7163784 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (_95913 : type830 A B) (h1 : _95913 = (term699 A B)) : (term694 A B t R) = (term722 A B _95913 t R).
Proof. exact (MK_COMB (@lem7163783 A) (@lem7163782 A B t R _95913 h1)). Qed.
Lemma lem7163785 {A B : Type'} (t : B -> Prop) (_95913 : type830 A B) (h1 : _95913 = (term699 A B)) : (term723 A B t) = (term724 A B _95913 t).
Proof. exact (fun_ext (fun R : type1413 A B => @lem7163784 A B t R _95913 h1)). Qed.
Lemma lem7163786 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem7163787 {A B : Type'} (t : B -> Prop) (_95913 : type830 A B) (h1 : _95913 = (term699 A B)) : (term695 A B t) = (term725 A B _95913 t).
Proof. exact (MK_COMB (@lem7163786 A B) (@lem7163785 A B t _95913 h1)). Qed.
Lemma lem7163788 {A B : Type'} (_95913 : type830 A B) (h1 : _95913 = (term699 A B)) : (term726 A B) = (term727 A B _95913).
Proof. exact (fun_ext (fun t : B -> Prop => @lem7163787 A B t _95913 h1)). Qed.
Lemma lem7163789 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem7163790 {A B : Type'} (_95913 : type830 A B) (h1 : _95913 = (term699 A B)) : (term696 A B) = (term728 A B _95913).
Proof. exact (MK_COMB (@lem7163789 B) (@lem7163788 A B _95913 h1)). Qed.
Lemma lem7163791 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7163792 {A B : Type'} (_95913 : type830 A B) (h1 : _95913 = (term699 A B)) : (term729 A B) = (term730 A B _95913).
Proof. exact (MK_COMB (@lem7163791) (@lem7163790 A B _95913 h1)). Qed.
Lemma lem7163794 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (_95913 : type830 A B) (h1 : _95913 = (term699 A B)) : (term674 A B t R x) = (_95913 t R x).
Proof. exact (EQ_MP (@lem7163762 A B _95913 t R x) (@lem7163761 A B t R x _95913 h1)). Qed.
Lemma lem7163795 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (_95913 : type830 A B) (h1 : _95913 = (term699 A B)) : (term674 A B t R x) = (_95913 t R x).
Proof. exact (@lem7163794 A B t R x _95913 h1). Qed.
Lemma lem7163796 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem7163797 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (_95913 : type830 A B) (h1 : _95913 = (term699 A B)) : (term675 A B t R x) = (term149 A B _95913 t R x).
Proof. exact (MK_COMB (@lem7163796 B) (@lem7163795 A B t R x _95913 h1)). Qed.
Lemma lem7163798 {B : Type'} (x : B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7163799 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) (_95913 : type830 A B) (h1 : _95913 = (term699 A B)) : ((term674 A B t R x) = x') = ((_95913 t R x) = x').
Proof. exact (MK_COMB (@lem7163797 A B t R x _95913 h1) (@lem7163798 B x')). Qed.
Lemma lem7163800 {A : Type'} (s : A -> Prop) (x : A) : (term628 A s x) = (term628 A s x).
Proof. exact (eq_refl (term628 A s x)). Qed.
Lemma lem7163801 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) (_95913 : type830 A B) (h1 : _95913 = (term699 A B)) : (term676 A B s t R x x') = (term731 A B s _95913 t R x x').
Proof. exact (MK_COMB (@lem7163800 A s x) (@lem7163799 A B t R x x' _95913 h1)). Qed.
Lemma lem7163802 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term661 A B s R x x') = (term661 A B s R x x').
Proof. exact (eq_refl (term661 A B s R x x')). Qed.
Lemma lem7163803 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) (_95913 : type830 A B) (h1 : _95913 = (term699 A B)) : ((term660 A B s R x x') = (term676 A B s t R x x')) = ((term660 A B s R x x') = (term731 A B s _95913 t R x x')).
Proof. exact (MK_COMB (@lem7163802 A B s R x x') (@lem7163801 A B s t R x x' _95913 h1)). Qed.
Lemma lem7163804 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (_95913 : type830 A B) (h1 : _95913 = (term699 A B)) : (term678 A B s t R x) = (term732 A B s _95913 t R x).
Proof. exact (fun_ext (fun x' : A => @lem7163803 A B s t R x' x _95913 h1)). Qed.
Lemma lem7163805 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7163806 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (_95913 : type830 A B) (h1 : _95913 = (term699 A B)) : (term679 A B s t R x) = (term733 A B s _95913 t R x).
Proof. exact (MK_COMB (@lem7163805 A) (@lem7163804 A B s t R x _95913 h1)). Qed.
Lemma lem7163807 {A B : Type'} (x : B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term640 A B x t R s) = (term640 A B x t R s).
Proof. exact (eq_refl (term640 A B x t R s)). Qed.
Lemma lem7163808 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (_95913 : type830 A B) (h1 : _95913 = (term699 A B)) : (term680 A B s t R x) = (term734 A B s _95913 t R x).
Proof. exact (MK_COMB (@lem7163807 A B x t R s) (@lem7163806 A B s t R x _95913 h1)). Qed.
Lemma lem7163809 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7163810 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (_95913 : type830 A B) (h1 : _95913 = (term699 A B)) : (term682 A B s t R x) = (term735 A B s _95913 t R x).
Proof. exact (MK_COMB (@lem7163809) (@lem7163808 A B s t R x _95913 h1)). Qed.
Lemma lem7163811 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7163812 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (_95913 : type830 A B) (h1 : _95913 = (term699 A B)) : (term736 A B s t R x) = (term737 A B s _95913 t R x).
Proof. exact (MK_COMB (@lem7163811) (@lem7163810 A B s t R x _95913 h1)). Qed.
Lemma lem7163813 : False = False.
Proof. exact (eq_refl False). Qed.
Lemma lem7163814 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (_95913 : type830 A B) (h1 : _95913 = (term699 A B)) : (term681 A B s t R x) = (term738 A B s _95913 t R x).
Proof. exact (MK_COMB (@lem7163812 A B s t R x _95913 h1) (@lem7163813)). Qed.
Lemma lem7163815 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (_95913 : type830 A B) (h1 : _95913 = (term699 A B)) : (term697 A B s t R x) = (term739 A B s _95913 t R x).
Proof. exact (MK_COMB (@lem7163792 A B _95913 h1) (@lem7163814 A B s t R x _95913 h1)). Qed.
Lemma lem7163816 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (h1 : term740 A B s t R x) : term740 A B s t R x.
Proof. exact (h1). Qed.
Lemma lem7163817 {A B : Type'} (_95913 : type830 A B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (h1 : term740 A B s t R x) : term741 A B s t R x _95913.
Proof. exact (@lem7163816 A B s t R x h1 _95913). Qed.
Lemma lem7163818 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : B) : (term741 A B s t R x _95913) = (term739 A B s _95913 t R x).
Proof. exact (eq_refl (term741 A B s t R x _95913)). Qed.
Lemma lem7163819 {A B : Type'} (_95913 : type830 A B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (h1 : term740 A B s t R x) : term739 A B s _95913 t R x.
Proof. exact (EQ_MP (@lem7163818 A B s _95913 t R x) (@lem7163817 A B _95913 s t R x h1)). Qed.
Lemma lem7163820 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (_95913 : type830 A B) (h1 : _95913 = (term699 A B)) : (term739 A B s _95913 t R x) = (term697 A B s t R x).
Proof. exact (SYM (@lem7163815 A B s t R x _95913 h1)). Qed.
Lemma lem7163821 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (_95913 : type830 A B) (h1 : term740 A B s t R x) (h2 : _95913 = (term699 A B)) : term697 A B s t R x.
Proof. exact (EQ_MP (@lem7163820 A B s t R x _95913 h2) (@lem7163819 A B _95913 s t R x h1)). Qed.
Lemma lem7163822 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (_95913 : type830 A B) (h1 : _95913 = (term699 A B)) : term742 A B s t R x.
Proof. exact (fun h0 : term740 A B s t R x => @lem7163821 A B s t R x _95913 h0 h1). Qed.
Lemma lem7163823 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : term743 A B s t R x.
Proof. exact (@lem51 (term697 A B s t R x) (term740 A B s t R x) (term681 A B s t R x)). Qed.
Lemma lem7163824 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (_95913 : type830 A B) (h1 : _95913 = (term699 A B)) : term744 A B s t R x.
Proof. exact (@lem7163823 A B s t R x (@lem7163822 A B s t R x _95913 h1)). Qed.
Lemma lem7163825 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (_95913 : type830 A B) (h1 : _95913 = (term699 A B)) : term745 A B s t R x.
Proof. exact (@lem7163824 A B s t R x _95913 h1 (@lem7163731 A B s t R x)). Qed.
Lemma lem7163826 {A B : Type'} : (term699 A B) = (term699 A B).
Proof. exact (eq_refl (term699 A B)). Qed.
Lemma lem7163827 {A B : Type'} (_95913 : type830 A B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : term746 A B _95913 s t R x.
Proof. exact (fun h0 : _95913 = (term699 A B) => @lem7163825 A B s t R x _95913 h0). Qed.
Lemma lem7163828 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : term747 A B s t R x.
Proof. exact (@lem7163827 A B (term699 A B) s t R x). Qed.
Lemma lem7163829 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : term745 A B s t R x.
Proof. exact (@lem7163828 A B s t R x (@lem7163826 A B)). Qed.
Lemma lem7163830 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (h1 : term740 A B s t R x) : term740 A B s t R x.
Proof. exact (h1). Qed.
Lemma lem7163831 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : term748 A B s t R x.
Proof. exact (fun h0 : term740 A B s t R x => @lem7163830 A B s t R x h0). Qed.
Lemma lem7163832 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : term749 A B s t R x.
Proof. exact (@lem51 (term740 A B s t R x) (term740 A B s t R x) (term681 A B s t R x)). Qed.
Lemma lem7163833 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : term750 A B s t R x.
Proof. exact (@lem7163832 A B s t R x (@lem7163831 A B s t R x)). Qed.
Lemma lem7163834 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : term745 A B s t R x.
Proof. exact (@lem7163833 A B s t R x (@lem7163829 A B s t R x)). Qed.
Lemma lem7163835 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (h1 : term745 A B s t R x) : term745 A B s t R x.
Proof. exact (h1). Qed.
Lemma lem7163836 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (h1 : term740 A B s t R x) : term740 A B s t R x.
Proof. exact (h1). Qed.
Lemma lem7163837 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (h1 : term740 A B s t R x) (h2 : term745 A B s t R x) : term681 A B s t R x.
Proof. exact (@lem7163835 A B s t R x h2 (@lem7163836 A B s t R x h1)). Qed.
Lemma lem7163838 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (h1 : term740 A B s t R x) : term751 A B s t R x.
Proof. exact (fun h0 : term745 A B s t R x => @lem7163837 A B s t R x h1 h0). Qed.
Lemma lem7163839 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (h1 : term745 A B s t R x) : term745 A B s t R x.
Proof. exact (h1). Qed.
Lemma lem7163840 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (h1 : term740 A B s t R x) (h2 : term745 A B s t R x) : term681 A B s t R x.
Proof. exact (@lem7163838 A B s t R x h1 (@lem7163839 A B s t R x h2)). Qed.
Lemma lem7163841 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (h1 : term745 A B s t R x) : term745 A B s t R x.
Proof. exact (fun h0 : term740 A B s t R x => @lem7163840 A B s t R x h0 h1). Qed.
Lemma lem7163842 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : term750 A B s t R x.
Proof. exact (fun h0 : term745 A B s t R x => @lem7163841 A B s t R x h0). Qed.
Lemma lem7163845 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : term745 A B s t R x.
Proof. exact (@lem7163842 A B s t R x (@lem7163834 A B s t R x)). Qed.
Lemma lem7163846 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : term745 A B s t R x.
Proof. exact (@lem7163845 A B s t R x). Qed.
Lemma lem7163892 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7163893 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : B) : (term738 A B s _95913 t R x) = (term752 A B s _95913 t R x).
Proof. exact (@lem7163892 (term735 A B s _95913 t R x)). Qed.
Lemma lem7163895 (t : Prop) : (term203 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem7163896 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : B) : (term752 A B s _95913 t R x) = (term734 A B s _95913 t R x).
Proof. exact (@lem7163895 (term734 A B s _95913 t R x)). Qed.
Lemma lem7163899 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : B) : (term738 A B s _95913 t R x) = (term734 A B s _95913 t R x).
Proof. exact (TRANS (@lem7163893 A B s _95913 t R x) (@lem7163896 A B s _95913 t R x)). Qed.
Lemma lem7163920 {A B : Type'} (_95913 : type830 A B) : (term730 A B _95913) = (term730 A B _95913).
Proof. exact (eq_refl (term730 A B _95913)). Qed.
Lemma lem7163921 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : B) : (term739 A B s _95913 t R x) = (term753 A B s _95913 t R x).
Proof. exact (MK_COMB (@lem7163920 A B _95913) (@lem7163899 A B s _95913 t R x)). Qed.
Lemma lem7163924 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : (term754 A B s t R x) = (term755 A B s t R x).
Proof. exact (fun_ext (fun _95913 : type830 A B => @lem7163921 A B s _95913 t R x)). Qed.
Lemma lem7163925 {A B : Type'} : (@all ((B -> Prop) -> (A -> B -> Prop) -> A -> B)) = (@all ((B -> Prop) -> (A -> B -> Prop) -> A -> B)).
Proof. exact (eq_refl (@all ((B -> Prop) -> (A -> B -> Prop) -> A -> B))). Qed.
Lemma lem7163926 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : (term740 A B s t R x) = (term756 A B s t R x).
Proof. exact (MK_COMB (@lem7163925 A B) (@lem7163924 A B s t R x)). Qed.
Lemma lem7163931 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : B) : (term757 A B t R x) = (term758 A B t R x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7163926 A B s t R x)). Qed.
Lemma lem7163932 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7163933 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : B) : (term759 A B t R x) = (term760 A B t R x).
Proof. exact (MK_COMB (@lem7163932 A) (@lem7163931 A B t R x)). Qed.
Lemma lem7163938 {A B : Type'} (R : type1413 A B) (x : B) : (term761 A B R x) = (term762 A B R x).
Proof. exact (fun_ext (fun t : B -> Prop => @lem7163933 A B t R x)). Qed.
Lemma lem7163939 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem7163940 {A B : Type'} (R : type1413 A B) (x : B) : (term763 A B R x) = (term764 A B R x).
Proof. exact (MK_COMB (@lem7163939 B) (@lem7163938 A B R x)). Qed.
Lemma lem7163945 {A B : Type'} (x : B) : (term765 A B x) = (term766 A B x).
Proof. exact (fun_ext (fun R : type1413 A B => @lem7163940 A B R x)). Qed.
Lemma lem7163946 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem7163947 {A B : Type'} (x : B) : (term767 A B x) = (term768 A B x).
Proof. exact (MK_COMB (@lem7163946 A B) (@lem7163945 A B x)). Qed.
Lemma lem7163952 {A B : Type'} : (term769 A B) = (term770 A B).
Proof. exact (fun_ext (fun x : B => @lem7163947 A B x)). Qed.
Lemma lem7163953 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7163962 {A B : Type'} : (term771 A B) = (term772 A B).
Proof. exact (MK_COMB (@lem7163953 B) (@lem7163952 A B)). Qed.
Lemma lem7163975 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : ((term660 A B s R x x') = (term731 A B s _95913 t R x x')) = ((term660 A B s R x x') = (term731 A B s _95913 t R x x')).
Proof. exact (eq_refl ((term660 A B s R x x') = (term731 A B s _95913 t R x x'))). Qed.
Lemma lem7163976 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : B) : (term732 A B s _95913 t R x) = (term732 A B s _95913 t R x).
Proof. exact (fun_ext (fun x' : A => @lem7163975 A B s _95913 t R x' x)). Qed.
Lemma lem7163977 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7163978 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : B) : (term733 A B s _95913 t R x) = (term733 A B s _95913 t R x).
Proof. exact (MK_COMB (@lem7163977 A) (@lem7163976 A B s _95913 t R x)). Qed.
Lemma lem7163979 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem7163984 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term630 A B t R x y) = (term630 A B t R x y).
Proof. exact (eq_refl (term630 A B t R x y)). Qed.
Lemma lem7163985 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term631 A B t R x) = (term631 A B t R x).
Proof. exact (fun_ext (fun y : B => @lem7163984 A B t R x y)). Qed.
Lemma lem7163986 {B : Type'} : (@ex1 B) = (@ex1 B).
Proof. exact (eq_refl (@ex1 B)). Qed.
Lemma lem7163987 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term632 A B t R x) = (term632 A B t R x).
Proof. exact (MK_COMB (@lem7163986 B) (@lem7163985 A B t R x)). Qed.
Lemma lem7163990 {A : Type'} (s : A -> Prop) (x : A) : (term629 A s x) = (term629 A s x).
Proof. exact (eq_refl (term629 A s x)). Qed.
Lemma lem7163991 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term633 A B s t R x) = (term633 A B s t R x).
Proof. exact (MK_COMB (@lem7163990 A s x) (@lem7163987 A B t R x)). Qed.
Lemma lem7163992 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term634 A B s t R) = (term634 A B s t R).
Proof. exact (fun_ext (fun x : A => @lem7163991 A B s t R x)). Qed.
Lemma lem7163993 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7163994 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term635 A B s t R) = (term635 A B s t R).
Proof. exact (MK_COMB (@lem7163993 A) (@lem7163992 A B s t R)). Qed.
Lemma lem7163995 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7163996 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term637 A B s t R) = (term637 A B s t R).
Proof. exact (MK_COMB (@lem7163995) (@lem7163994 A B s t R)). Qed.
Lemma lem7163997 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term638 A B t R s) = (term638 A B t R s).
Proof. exact (MK_COMB (@lem7163996 A B s t R) (@lem7163979 A s)). Qed.
Lemma lem7164000 {B : Type'} (t : B -> Prop) (x : B) : (term628 B t x) = (term628 B t x).
Proof. exact (eq_refl (term628 B t x)). Qed.
Lemma lem7164001 {A B : Type'} (x : B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term639 A B x t R s) = (term639 A B x t R s).
Proof. exact (MK_COMB (@lem7164000 B t x) (@lem7163997 A B t R s)). Qed.
Lemma lem7164002 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7164003 {A B : Type'} (x : B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term640 A B x t R s) = (term640 A B x t R s).
Proof. exact (MK_COMB (@lem7164002) (@lem7164001 A B x t R s)). Qed.
Lemma lem7164004 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : B) : (term734 A B s _95913 t R x) = (term734 A B s _95913 t R x).
Proof. exact (MK_COMB (@lem7164003 A B x t R s) (@lem7163978 A B s _95913 t R x)). Qed.
Lemma lem7164017 {A B : Type'} (x : B) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) : (term717 A B x _95913 t R x') = (term717 A B x _95913 t R x').
Proof. exact (eq_refl (term717 A B x _95913 t R x')). Qed.
Lemma lem7164018 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term718 A B _95913 t R x) = (term718 A B _95913 t R x).
Proof. exact (fun_ext (fun x' : B => @lem7164017 A B x' _95913 t R x)). Qed.
Lemma lem7164019 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7164020 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term719 A B _95913 t R x) = (term719 A B _95913 t R x).
Proof. exact (MK_COMB (@lem7164019 B) (@lem7164018 A B _95913 t R x)). Qed.
Lemma lem7164021 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (term721 A B _95913 t R) = (term721 A B _95913 t R).
Proof. exact (fun_ext (fun x : A => @lem7164020 A B _95913 t R x)). Qed.
Lemma lem7164022 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7164023 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (term722 A B _95913 t R) = (term722 A B _95913 t R).
Proof. exact (MK_COMB (@lem7164022 A) (@lem7164021 A B _95913 t R)). Qed.
Lemma lem7164024 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) : (term724 A B _95913 t) = (term724 A B _95913 t).
Proof. exact (fun_ext (fun R : type1413 A B => @lem7164023 A B _95913 t R)). Qed.
Lemma lem7164025 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem7164026 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) : (term725 A B _95913 t) = (term725 A B _95913 t).
Proof. exact (MK_COMB (@lem7164025 A B) (@lem7164024 A B _95913 t)). Qed.
Lemma lem7164027 {A B : Type'} (_95913 : type830 A B) : (term727 A B _95913) = (term727 A B _95913).
Proof. exact (fun_ext (fun t : B -> Prop => @lem7164026 A B _95913 t)). Qed.
Lemma lem7164028 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem7164029 {A B : Type'} (_95913 : type830 A B) : (term728 A B _95913) = (term728 A B _95913).
Proof. exact (MK_COMB (@lem7164028 B) (@lem7164027 A B _95913)). Qed.
Lemma lem7164030 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7164031 {A B : Type'} (_95913 : type830 A B) : (term730 A B _95913) = (term730 A B _95913).
Proof. exact (MK_COMB (@lem7164030) (@lem7164029 A B _95913)). Qed.
Lemma lem7164032 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : B) : (term753 A B s _95913 t R x) = (term753 A B s _95913 t R x).
Proof. exact (MK_COMB (@lem7164031 A B _95913) (@lem7164004 A B s _95913 t R x)). Qed.
Lemma lem7164033 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : (term755 A B s t R x) = (term755 A B s t R x).
Proof. exact (fun_ext (fun _95913 : type830 A B => @lem7164032 A B s _95913 t R x)). Qed.
Lemma lem7164034 {A B : Type'} : (@all ((B -> Prop) -> (A -> B -> Prop) -> A -> B)) = (@all ((B -> Prop) -> (A -> B -> Prop) -> A -> B)).
Proof. exact (eq_refl (@all ((B -> Prop) -> (A -> B -> Prop) -> A -> B))). Qed.
Lemma lem7164035 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : (term756 A B s t R x) = (term756 A B s t R x).
Proof. exact (MK_COMB (@lem7164034 A B) (@lem7164033 A B s t R x)). Qed.
Lemma lem7164036 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : B) : (term758 A B t R x) = (term758 A B t R x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7164035 A B s t R x)). Qed.
Lemma lem7164037 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7164038 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : B) : (term760 A B t R x) = (term760 A B t R x).
Proof. exact (MK_COMB (@lem7164037 A) (@lem7164036 A B t R x)). Qed.
Lemma lem7164039 {A B : Type'} (R : type1413 A B) (x : B) : (term762 A B R x) = (term762 A B R x).
Proof. exact (fun_ext (fun t : B -> Prop => @lem7164038 A B t R x)). Qed.
Lemma lem7164040 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem7164041 {A B : Type'} (R : type1413 A B) (x : B) : (term764 A B R x) = (term764 A B R x).
Proof. exact (MK_COMB (@lem7164040 B) (@lem7164039 A B R x)). Qed.
Lemma lem7164042 {A B : Type'} (x : B) : (term766 A B x) = (term766 A B x).
Proof. exact (fun_ext (fun R : type1413 A B => @lem7164041 A B R x)). Qed.
Lemma lem7164043 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem7164044 {A B : Type'} (x : B) : (term768 A B x) = (term768 A B x).
Proof. exact (MK_COMB (@lem7164043 A B) (@lem7164042 A B x)). Qed.
Lemma lem7164045 {A B : Type'} : (term770 A B) = (term770 A B).
Proof. exact (fun_ext (fun x : B => @lem7164044 A B x)). Qed.
Lemma lem7164046 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7164047 {A B : Type'} : (term772 A B) = (term772 A B).
Proof. exact (MK_COMB (@lem7164046 B) (@lem7164045 A B)). Qed.
Lemma lem7164138 {A B : Type'} : (term771 A B) = (term772 A B).
Proof. exact (TRANS (@lem7163962 A B) (@lem7164047 A B)). Qed.
Lemma lem7164139 {A B : Type'} : (term772 A B) = (term771 A B).
Proof. exact (SYM (@lem7164138 A B)). Qed.
Lemma lem7164140 {A B : Type'} (_95913 : type830 A B) (h1 : term728 A B _95913) : term728 A B _95913.
Proof. exact (h1). Qed.
Lemma lem7164141 {A B : Type'} (x : B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term639 A B x t R s) : term639 A B x t R s.
Proof. exact (h1). Qed.
Lemma lem7164143 (p : Prop) : p = (term120 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7164144 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) : ((term660 A B s R x' x) = (term731 A B s _95913 t R x' x)) = (term773 A B s _95913 t R x' x).
Proof. exact (@lem7164143 ((term660 A B s R x' x) = (term731 A B s _95913 t R x' x))). Qed.
Lemma lem7164145 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) : (term773 A B s _95913 t R x' x) = ((term660 A B s R x' x) = (term731 A B s _95913 t R x' x)).
Proof. exact (SYM (@lem7164144 A B s _95913 t R x' x)). Qed.
Lemma lem7164146 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term774 A B s _95913 t R x' x) : term774 A B s _95913 t R x' x.
Proof. exact (h1). Qed.
Lemma lem7164153 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term775 A B t R x x') = (term776 A B t R x x').
Proof. exact (@lem17045 (t x') (R x x')). Qed.
Lemma lem7164158 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term716 A B _95913 t R x) = (term716 A B _95913 t R x).
Proof. exact (eq_refl (term716 A B _95913 t R x)). Qed.
Lemma lem7164159 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7164160 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term777 A B t R x x') = (term778 A B t R x x').
Proof. exact (MK_COMB (@lem7164159) (@lem7164153 A B t R x x')). Qed.
Lemma lem7164161 {A B : Type'} (x : B) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) : (term779 A B x _95913 t R x') = (term780 A B x _95913 t R x').
Proof. exact (MK_COMB (@lem7164160 A B t R x' x) (@lem7164158 A B _95913 t R x')). Qed.
Lemma lem7164162 {A B : Type'} (x : B) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) : (term717 A B x _95913 t R x') = (term779 A B x _95913 t R x').
Proof. exact (@lem17265 (term630 A B t R x' x) (term716 A B _95913 t R x')). Qed.
Lemma lem7164163 {A B : Type'} (x : B) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) : (term717 A B x _95913 t R x') = (term780 A B x _95913 t R x').
Proof. exact (TRANS (@lem7164162 A B x _95913 t R x') (@lem7164161 A B x _95913 t R x')). Qed.
Lemma lem7164164 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term718 A B _95913 t R x) = (term781 A B _95913 t R x).
Proof. exact (fun_ext (fun x' : B => @lem7164163 A B x' _95913 t R x)). Qed.
Lemma lem7164165 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7164166 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term719 A B _95913 t R x) = (term782 A B _95913 t R x).
Proof. exact (MK_COMB (@lem7164165 B) (@lem7164164 A B _95913 t R x)). Qed.
Lemma lem7164167 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (term721 A B _95913 t R) = (term783 A B _95913 t R).
Proof. exact (fun_ext (fun x : A => @lem7164166 A B _95913 t R x)). Qed.
Lemma lem7164168 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7164169 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (term722 A B _95913 t R) = (term784 A B _95913 t R).
Proof. exact (MK_COMB (@lem7164168 A) (@lem7164167 A B _95913 t R)). Qed.
Lemma lem7164170 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) : (term724 A B _95913 t) = (term785 A B _95913 t).
Proof. exact (fun_ext (fun R : type1413 A B => @lem7164169 A B _95913 t R)). Qed.
Lemma lem7164171 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem7164172 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) : (term725 A B _95913 t) = (term786 A B _95913 t).
Proof. exact (MK_COMB (@lem7164171 A B) (@lem7164170 A B _95913 t)). Qed.
Lemma lem7164173 {A B : Type'} (_95913 : type830 A B) : (term727 A B _95913) = (term787 A B _95913).
Proof. exact (fun_ext (fun t : B -> Prop => @lem7164172 A B _95913 t)). Qed.
Lemma lem7164174 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem7164175 {A B : Type'} (_95913 : type830 A B) : (term728 A B _95913) = (term788 A B _95913).
Proof. exact (MK_COMB (@lem7164174 B) (@lem7164173 A B _95913)). Qed.
Lemma lem7164209 {A : Type'} (P : A -> Prop) (Q : Prop) : (term241 A P Q) = (term242 A P Q).
Proof. exact (EQ_MP (@lem18947 A P Q) (@lem18946 A P Q)). Qed.
Lemma lem7164210 {B : Type'} (P : B -> Prop) (Q : Prop) : (term241 B P Q) = (term242 B P Q).
Proof. exact (@lem7164209 B P Q). Qed.
Lemma lem7164211 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term789 A B _95913 t R x) = (term790 A B _95913 t R x).
Proof. exact (@lem7164210 B (term791 A B t R x) (term716 A B _95913 t R x)). Qed.
Lemma lem7164212 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term792 A B t R x x') = (term776 A B t R x x').
Proof. exact (eq_refl (term792 A B t R x x')). Qed.
Lemma lem7164213 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7164214 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term793 A B t R x x') = (term778 A B t R x x').
Proof. exact (MK_COMB (@lem7164213) (@lem7164212 A B t R x x')). Qed.
Lemma lem7164215 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term716 A B _95913 t R x) = (term716 A B _95913 t R x).
Proof. exact (eq_refl (term716 A B _95913 t R x)). Qed.
Lemma lem7164216 {A B : Type'} (x : B) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) : (term794 A B x _95913 t R x') = (term780 A B x _95913 t R x').
Proof. exact (MK_COMB (@lem7164214 A B t R x' x) (@lem7164215 A B _95913 t R x')). Qed.
Lemma lem7164217 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term795 A B _95913 t R x) = (term781 A B _95913 t R x).
Proof. exact (fun_ext (fun x' : B => @lem7164216 A B x' _95913 t R x)). Qed.
Lemma lem7164218 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7164219 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term789 A B _95913 t R x) = (term782 A B _95913 t R x).
Proof. exact (MK_COMB (@lem7164218 B) (@lem7164217 A B _95913 t R x)). Qed.
Lemma lem7164220 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7164221 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term796 A B _95913 t R x) = (term797 A B _95913 t R x).
Proof. exact (MK_COMB (@lem7164220) (@lem7164219 A B _95913 t R x)). Qed.
Lemma lem7164222 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term792 A B t R x x') = (term776 A B t R x x').
Proof. exact (eq_refl (term792 A B t R x x')). Qed.
Lemma lem7164223 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term798 A B t R x) = (term791 A B t R x).
Proof. exact (fun_ext (fun x' : B => @lem7164222 A B t R x x')). Qed.
Lemma lem7164224 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7164225 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term799 A B t R x) = (term800 A B t R x).
Proof. exact (MK_COMB (@lem7164224 B) (@lem7164223 A B t R x)). Qed.
Lemma lem7164226 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7164227 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term801 A B t R x) = (term802 A B t R x).
Proof. exact (MK_COMB (@lem7164226) (@lem7164225 A B t R x)). Qed.
Lemma lem7164228 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term716 A B _95913 t R x) = (term716 A B _95913 t R x).
Proof. exact (eq_refl (term716 A B _95913 t R x)). Qed.
Lemma lem7164229 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term790 A B _95913 t R x) = (term803 A B _95913 t R x).
Proof. exact (MK_COMB (@lem7164227 A B t R x) (@lem7164228 A B _95913 t R x)). Qed.
Lemma lem7164230 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : ((term789 A B _95913 t R x) = (term790 A B _95913 t R x)) = ((term782 A B _95913 t R x) = (term803 A B _95913 t R x)).
Proof. exact (MK_COMB (@lem7164221 A B _95913 t R x) (@lem7164229 A B _95913 t R x)). Qed.
Lemma lem7164231 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term782 A B _95913 t R x) = (term803 A B _95913 t R x).
Proof. exact (EQ_MP (@lem7164230 A B _95913 t R x) (@lem7164211 A B _95913 t R x)). Qed.
Lemma lem7164280 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (term783 A B _95913 t R) = (term804 A B _95913 t R).
Proof. exact (fun_ext (fun x : A => @lem7164231 A B _95913 t R x)). Qed.
Lemma lem7164281 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7164282 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (term784 A B _95913 t R) = (term805 A B _95913 t R).
Proof. exact (MK_COMB (@lem7164281 A) (@lem7164280 A B _95913 t R)). Qed.
Lemma lem7164331 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) : (term785 A B _95913 t) = (term806 A B _95913 t).
Proof. exact (fun_ext (fun R : type1413 A B => @lem7164282 A B _95913 t R)). Qed.
Lemma lem7164332 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem7164333 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) : (term786 A B _95913 t) = (term807 A B _95913 t).
Proof. exact (MK_COMB (@lem7164332 A B) (@lem7164331 A B _95913 t)). Qed.
Lemma lem7164338 {A B : Type'} (_95913 : type830 A B) : (term787 A B _95913) = (term808 A B _95913).
Proof. exact (fun_ext (fun t : B -> Prop => @lem7164333 A B _95913 t)). Qed.
Lemma lem7164339 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem7164346 {A B : Type'} (_95913 : type830 A B) : (term788 A B _95913) = (term809 A B _95913).
Proof. exact (MK_COMB (@lem7164339 B) (@lem7164338 A B _95913)). Qed.
Lemma lem7164347 {A B : Type'} (_95913 : type830 A B) : (term728 A B _95913) = (term809 A B _95913).
Proof. exact (TRANS (@lem7164175 A B _95913) (@lem7164346 A B _95913)). Qed.
Lemma lem7164348 {A B : Type'} (_95913 : type830 A B) (h1 : term728 A B _95913) : term809 A B _95913.
Proof. exact (EQ_MP (@lem7164347 A B _95913) (@lem7164140 A B _95913 h1)). Qed.
Lemma lem7164359 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term775 A B t R x y) = (term776 A B t R x y).
Proof. exact (@lem17045 (t y) (R x y)). Qed.
Lemma lem7164364 {B : Type'} (y' : B) (y : B) : (y' = y) = (y' = y).
Proof. exact (eq_refl (y' = y)). Qed.
Lemma lem7164365 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term686 A B t R x y) = (term630 A B t R x y).
Proof. exact (eq_refl (term686 A B t R x y)). Qed.
Lemma lem7164366 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term686 A B t R x y') = (term630 A B t R x y').
Proof. exact (eq_refl (term686 A B t R x y')). Qed.
Lemma lem7164367 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term775 A B t R x y') = (term776 A B t R x y').
Proof. exact (@lem7164359 A B t R x y'). Qed.
Lemma lem7164368 {B : Type'} (P : B -> Prop) : (@ex1 B P) = (term264 B P).
Proof. exact (@lem18897 B P). Qed.
Lemma lem7164369 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term632 A B t R x) = (term810 A B t R x).
Proof. exact (@lem7164368 B (term631 A B t R x)). Qed.
Lemma lem7164370 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7164371 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term811 A B t R x y') = (term775 A B t R x y').
Proof. exact (MK_COMB (@lem7164370) (@lem7164366 A B t R x y')). Qed.
Lemma lem7164372 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term811 A B t R x y') = (term776 A B t R x y').
Proof. exact (TRANS (@lem7164371 A B t R x y') (@lem7164367 A B t R x y')). Qed.
Lemma lem7164373 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7164374 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term812 A B t R x y') = (term778 A B t R x y').
Proof. exact (MK_COMB (@lem7164373) (@lem7164372 A B t R x y')). Qed.
Lemma lem7164375 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y : B) : (term813 A B t R x y' y) = (term814 A B t R x y' y).
Proof. exact (MK_COMB (@lem7164374 A B t R x y') (@lem7164364 B y' y)). Qed.
Lemma lem7164376 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7164377 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term811 A B t R x y) = (term775 A B t R x y).
Proof. exact (MK_COMB (@lem7164376) (@lem7164365 A B t R x y)). Qed.
Lemma lem7164378 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term811 A B t R x y) = (term776 A B t R x y).
Proof. exact (TRANS (@lem7164377 A B t R x y) (@lem7164359 A B t R x y)). Qed.
Lemma lem7164379 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7164380 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term812 A B t R x y) = (term778 A B t R x y).
Proof. exact (MK_COMB (@lem7164379) (@lem7164378 A B t R x y)). Qed.
Lemma lem7164381 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y : B) : (term815 A B t R x y' y) = (term816 A B t R x y' y).
Proof. exact (MK_COMB (@lem7164380 A B t R x y) (@lem7164375 A B t R x y' y)). Qed.
Lemma lem7164382 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term817 A B t R x y) = (term818 A B t R x y).
Proof. exact (fun_ext (fun y' : B => @lem7164381 A B t R x y' y)). Qed.
Lemma lem7164383 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7164384 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term819 A B t R x y) = (term820 A B t R x y).
Proof. exact (MK_COMB (@lem7164383 B) (@lem7164382 A B t R x y)). Qed.
Lemma lem7164385 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term821 A B t R x) = (term822 A B t R x).
Proof. exact (fun_ext (fun y : B => @lem7164384 A B t R x y)). Qed.
Lemma lem7164386 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7164387 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term823 A B t R x) = (term824 A B t R x).
Proof. exact (MK_COMB (@lem7164386 B) (@lem7164385 A B t R x)). Qed.
Lemma lem7164388 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term686 A B t R x y) = (term630 A B t R x y).
Proof. exact (eq_refl (term686 A B t R x y)). Qed.
Lemma lem7164389 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term825 A B t R x) = (term631 A B t R x).
Proof. exact (fun_ext (fun y : B => @lem7164388 A B t R x y)). Qed.
Lemma lem7164390 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem7164391 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term826 A B t R x) = (term827 A B t R x).
Proof. exact (MK_COMB (@lem7164390 B) (@lem7164389 A B t R x)). Qed.
Lemma lem7164392 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7164393 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term828 A B t R x) = (term829 A B t R x).
Proof. exact (MK_COMB (@lem7164392) (@lem7164391 A B t R x)). Qed.
Lemma lem7164394 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term810 A B t R x) = (term830 A B t R x).
Proof. exact (MK_COMB (@lem7164393 A B t R x) (@lem7164387 A B t R x)). Qed.
Lemma lem7164395 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term632 A B t R x) = (term830 A B t R x).
Proof. exact (TRANS (@lem7164369 A B t R x) (@lem7164394 A B t R x)). Qed.
Lemma lem7164397 {A : Type'} (s : A -> Prop) (x : A) : (term831 A s x) = (term831 A s x).
Proof. exact (eq_refl (term831 A s x)). Qed.
Lemma lem7164398 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term832 A B s t R x) = (term833 A B s t R x).
Proof. exact (MK_COMB (@lem7164397 A s x) (@lem7164395 A B t R x)). Qed.
Lemma lem7164399 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term633 A B s t R x) = (term832 A B s t R x).
Proof. exact (@lem17265 (s x) (term632 A B t R x)). Qed.
Lemma lem7164400 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term633 A B s t R x) = (term833 A B s t R x).
Proof. exact (TRANS (@lem7164399 A B s t R x) (@lem7164398 A B s t R x)). Qed.
Lemma lem7164401 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term634 A B s t R) = (term834 A B s t R).
Proof. exact (fun_ext (fun x : A => @lem7164400 A B s t R x)). Qed.
Lemma lem7164402 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7164403 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term635 A B s t R) = (term835 A B s t R).
Proof. exact (MK_COMB (@lem7164402 A) (@lem7164401 A B s t R)). Qed.
Lemma lem7164404 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem7164405 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7164406 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term637 A B s t R) = (term836 A B s t R).
Proof. exact (MK_COMB (@lem7164405) (@lem7164403 A B s t R)). Qed.
Lemma lem7164407 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term638 A B t R s) = (term837 A B t R s).
Proof. exact (MK_COMB (@lem7164406 A B s t R) (@lem7164404 A s)). Qed.
Lemma lem7164409 {B : Type'} (t : B -> Prop) (x : B) : (term628 B t x) = (term628 B t x).
Proof. exact (eq_refl (term628 B t x)). Qed.
Lemma lem7164410 {A B : Type'} (x : B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term639 A B x t R s) = (term838 A B x t R s).
Proof. exact (MK_COMB (@lem7164409 B t x) (@lem7164407 A B t R s)). Qed.
Lemma lem7164492 {A : Type'} (P : Prop) (Q : A -> Prop) : (term291 A P Q) = (term292 A P Q).
Proof. exact (EQ_MP (@lem18941 A P Q) (@lem18940 A P Q)). Qed.
Lemma lem7164493 {B : Type'} (P : Prop) (Q : B -> Prop) : (term291 B P Q) = (term292 B P Q).
Proof. exact (@lem7164492 B P Q). Qed.
Lemma lem7164494 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term839 A B t R x y) = (term840 A B t R x y).
Proof. exact (@lem7164493 B (term776 A B t R x y) (term841 A B t R x y)). Qed.
Lemma lem7164495 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y : B) : (term842 A B t R x y y') = (term814 A B t R x y' y).
Proof. exact (eq_refl (term842 A B t R x y y')). Qed.
Lemma lem7164496 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term778 A B t R x y) = (term778 A B t R x y).
Proof. exact (eq_refl (term778 A B t R x y)). Qed.
Lemma lem7164497 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y : B) : (term843 A B t R x y y') = (term816 A B t R x y' y).
Proof. exact (MK_COMB (@lem7164496 A B t R x y) (@lem7164495 A B t R x y' y)). Qed.
Lemma lem7164498 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term844 A B t R x y) = (term818 A B t R x y).
Proof. exact (fun_ext (fun y' : B => @lem7164497 A B t R x y' y)). Qed.
Lemma lem7164499 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7164500 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term839 A B t R x y) = (term820 A B t R x y).
Proof. exact (MK_COMB (@lem7164499 B) (@lem7164498 A B t R x y)). Qed.
Lemma lem7164501 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7164502 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term845 A B t R x y) = (term846 A B t R x y).
Proof. exact (MK_COMB (@lem7164501) (@lem7164500 A B t R x y)). Qed.
Lemma lem7164503 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y : B) : (term842 A B t R x y y') = (term814 A B t R x y' y).
Proof. exact (eq_refl (term842 A B t R x y y')). Qed.
Lemma lem7164504 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term847 A B t R x y) = (term841 A B t R x y).
Proof. exact (fun_ext (fun y' : B => @lem7164503 A B t R x y' y)). Qed.
Lemma lem7164505 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7164506 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term848 A B t R x y) = (term849 A B t R x y).
Proof. exact (MK_COMB (@lem7164505 B) (@lem7164504 A B t R x y)). Qed.
Lemma lem7164507 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term778 A B t R x y) = (term778 A B t R x y).
Proof. exact (eq_refl (term778 A B t R x y)). Qed.
Lemma lem7164508 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term840 A B t R x y) = (term850 A B t R x y).
Proof. exact (MK_COMB (@lem7164507 A B t R x y) (@lem7164506 A B t R x y)). Qed.
Lemma lem7164509 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : ((term839 A B t R x y) = (term840 A B t R x y)) = ((term820 A B t R x y) = (term850 A B t R x y)).
Proof. exact (MK_COMB (@lem7164502 A B t R x y) (@lem7164508 A B t R x y)). Qed.
Lemma lem7164510 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term820 A B t R x y) = (term850 A B t R x y).
Proof. exact (EQ_MP (@lem7164509 A B t R x y) (@lem7164494 A B t R x y)). Qed.
Lemma lem7164559 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term822 A B t R x) = (term851 A B t R x).
Proof. exact (fun_ext (fun y : B => @lem7164510 A B t R x y)). Qed.
Lemma lem7164560 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7164561 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term824 A B t R x) = (term852 A B t R x).
Proof. exact (MK_COMB (@lem7164560 B) (@lem7164559 A B t R x)). Qed.
Lemma lem7164610 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term829 A B t R x) = (term829 A B t R x).
Proof. exact (eq_refl (term829 A B t R x)). Qed.
Lemma lem7164611 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term830 A B t R x) = (term853 A B t R x).
Proof. exact (MK_COMB (@lem7164610 A B t R x) (@lem7164561 A B t R x)). Qed.
Lemma lem7164612 {A : Type'} (s : A -> Prop) (x : A) : (term831 A s x) = (term831 A s x).
Proof. exact (eq_refl (term831 A s x)). Qed.
Lemma lem7164613 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term833 A B s t R x) = (term854 A B s t R x).
Proof. exact (MK_COMB (@lem7164612 A s x) (@lem7164611 A B t R x)). Qed.
Lemma lem7164614 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term834 A B s t R) = (term855 A B s t R).
Proof. exact (fun_ext (fun x : A => @lem7164613 A B s t R x)). Qed.
Lemma lem7164615 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7164616 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term835 A B s t R) = (term856 A B s t R).
Proof. exact (MK_COMB (@lem7164615 A) (@lem7164614 A B s t R)). Qed.
Lemma lem7164665 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7164666 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term836 A B s t R) = (term857 A B s t R).
Proof. exact (MK_COMB (@lem7164665) (@lem7164616 A B s t R)). Qed.
Lemma lem7164667 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem7164668 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term837 A B t R s) = (term858 A B t R s).
Proof. exact (MK_COMB (@lem7164666 A B s t R) (@lem7164667 A s)). Qed.
Lemma lem7164669 {B : Type'} (t : B -> Prop) (x : B) : (term628 B t x) = (term628 B t x).
Proof. exact (eq_refl (term628 B t x)). Qed.
Lemma lem7164670 {A B : Type'} (x : B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term838 A B x t R s) = (term859 A B x t R s).
Proof. exact (MK_COMB (@lem7164669 B t x) (@lem7164668 A B t R s)). Qed.
Lemma lem7164672 {A : Type'} (P : A -> Prop) (Q : Prop) : (term311 A P Q) = (term312 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem7164673 {B : Type'} (P : B -> Prop) (Q : Prop) : (term311 B P Q) = (term312 B P Q).
Proof. exact (@lem7164672 B P Q). Qed.
Lemma lem7164674 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term860 A B t R x) = (term861 A B t R x).
Proof. exact (@lem7164673 B (term631 A B t R x) (term852 A B t R x)). Qed.
Lemma lem7164675 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term686 A B t R x y) = (term630 A B t R x y).
Proof. exact (eq_refl (term686 A B t R x y)). Qed.
Lemma lem7164676 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term825 A B t R x) = (term631 A B t R x).
Proof. exact (fun_ext (fun y : B => @lem7164675 A B t R x y)). Qed.
Lemma lem7164677 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem7164678 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term826 A B t R x) = (term827 A B t R x).
Proof. exact (MK_COMB (@lem7164677 B) (@lem7164676 A B t R x)). Qed.
Lemma lem7164679 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7164680 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term828 A B t R x) = (term829 A B t R x).
Proof. exact (MK_COMB (@lem7164679) (@lem7164678 A B t R x)). Qed.
Lemma lem7164681 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term852 A B t R x) = (term852 A B t R x).
Proof. exact (eq_refl (term852 A B t R x)). Qed.
Lemma lem7164682 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term860 A B t R x) = (term853 A B t R x).
Proof. exact (MK_COMB (@lem7164680 A B t R x) (@lem7164681 A B t R x)). Qed.
Lemma lem7164683 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7164684 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term862 A B t R x) = (term863 A B t R x).
Proof. exact (MK_COMB (@lem7164683) (@lem7164682 A B t R x)). Qed.
Lemma lem7164685 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term686 A B t R x y) = (term630 A B t R x y).
Proof. exact (eq_refl (term686 A B t R x y)). Qed.
Lemma lem7164686 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7164687 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term864 A B t R x y) = (term865 A B t R x y).
Proof. exact (MK_COMB (@lem7164686) (@lem7164685 A B t R x y)). Qed.
Lemma lem7164688 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term852 A B t R x) = (term852 A B t R x).
Proof. exact (eq_refl (term852 A B t R x)). Qed.
Lemma lem7164689 {A B : Type'} (y : B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term866 A B y t R x) = (term867 A B y t R x).
Proof. exact (MK_COMB (@lem7164687 A B t R x y) (@lem7164688 A B t R x)). Qed.
Lemma lem7164690 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term868 A B t R x) = (term869 A B t R x).
Proof. exact (fun_ext (fun y : B => @lem7164689 A B y t R x)). Qed.
Lemma lem7164691 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem7164692 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term861 A B t R x) = (term870 A B t R x).
Proof. exact (MK_COMB (@lem7164691 B) (@lem7164690 A B t R x)). Qed.
Lemma lem7164693 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : ((term860 A B t R x) = (term861 A B t R x)) = ((term853 A B t R x) = (term870 A B t R x)).
Proof. exact (MK_COMB (@lem7164684 A B t R x) (@lem7164692 A B t R x)). Qed.
Lemma lem7164694 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term853 A B t R x) = (term870 A B t R x).
Proof. exact (EQ_MP (@lem7164693 A B t R x) (@lem7164674 A B t R x)). Qed.
Lemma lem7164695 {A : Type'} (s : A -> Prop) (x : A) : (term831 A s x) = (term831 A s x).
Proof. exact (eq_refl (term831 A s x)). Qed.
Lemma lem7164696 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term854 A B s t R x) = (term871 A B s t R x).
Proof. exact (MK_COMB (@lem7164695 A s x) (@lem7164694 A B t R x)). Qed.
Lemma lem7164698 {A : Type'} (P : Prop) (Q : A -> Prop) : (term325 A P Q) = (term326 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem7164699 {B : Type'} (P : Prop) (Q : B -> Prop) : (term325 B P Q) = (term326 B P Q).
Proof. exact (@lem7164698 B P Q). Qed.
Lemma lem7164700 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term872 A B s t R x) = (term873 A B s t R x).
Proof. exact (@lem7164699 B (term874 A s x) (term869 A B t R x)). Qed.
Lemma lem7164701 {A B : Type'} (y : B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term875 A B t R x y) = (term867 A B y t R x).
Proof. exact (eq_refl (term875 A B t R x y)). Qed.
Lemma lem7164702 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term876 A B t R x) = (term869 A B t R x).
Proof. exact (fun_ext (fun y : B => @lem7164701 A B y t R x)). Qed.
Lemma lem7164703 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem7164704 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term877 A B t R x) = (term870 A B t R x).
Proof. exact (MK_COMB (@lem7164703 B) (@lem7164702 A B t R x)). Qed.
Lemma lem7164705 {A : Type'} (s : A -> Prop) (x : A) : (term831 A s x) = (term831 A s x).
Proof. exact (eq_refl (term831 A s x)). Qed.
Lemma lem7164706 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term872 A B s t R x) = (term871 A B s t R x).
Proof. exact (MK_COMB (@lem7164705 A s x) (@lem7164704 A B t R x)). Qed.
Lemma lem7164707 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7164708 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term878 A B s t R x) = (term879 A B s t R x).
Proof. exact (MK_COMB (@lem7164707) (@lem7164706 A B s t R x)). Qed.
Lemma lem7164709 {A B : Type'} (y : B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term875 A B t R x y) = (term867 A B y t R x).
Proof. exact (eq_refl (term875 A B t R x y)). Qed.
Lemma lem7164710 {A : Type'} (s : A -> Prop) (x : A) : (term831 A s x) = (term831 A s x).
Proof. exact (eq_refl (term831 A s x)). Qed.
Lemma lem7164711 {A B : Type'} (s : A -> Prop) (y : B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term880 A B s t R x y) = (term881 A B s y t R x).
Proof. exact (MK_COMB (@lem7164710 A s x) (@lem7164709 A B y t R x)). Qed.
Lemma lem7164712 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term882 A B s t R x) = (term883 A B s t R x).
Proof. exact (fun_ext (fun y : B => @lem7164711 A B s y t R x)). Qed.
Lemma lem7164713 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem7164714 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term873 A B s t R x) = (term884 A B s t R x).
Proof. exact (MK_COMB (@lem7164713 B) (@lem7164712 A B s t R x)). Qed.
Lemma lem7164715 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : ((term872 A B s t R x) = (term873 A B s t R x)) = ((term871 A B s t R x) = (term884 A B s t R x)).
Proof. exact (MK_COMB (@lem7164708 A B s t R x) (@lem7164714 A B s t R x)). Qed.
Lemma lem7164716 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term871 A B s t R x) = (term884 A B s t R x).
Proof. exact (EQ_MP (@lem7164715 A B s t R x) (@lem7164700 A B s t R x)). Qed.
Lemma lem7164717 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term854 A B s t R x) = (term884 A B s t R x).
Proof. exact (TRANS (@lem7164696 A B s t R x) (@lem7164716 A B s t R x)). Qed.
Lemma lem7164718 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term855 A B s t R) = (term885 A B s t R).
Proof. exact (fun_ext (fun x : A => @lem7164717 A B s t R x)). Qed.
Lemma lem7164719 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7164720 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term856 A B s t R) = (term886 A B s t R).
Proof. exact (MK_COMB (@lem7164719 A) (@lem7164718 A B s t R)). Qed.
Lemma lem7164722 {A B : Type'} (P : type1413 A B) : (term342 A B P) = (term343 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7164723 {A B : Type'} (P : type1413 A B) : (term342 A B P) = (term343 A B P).
Proof. exact (@lem7164722 A B P). Qed.
Lemma lem7164724 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term887 A B s t R) = (term888 A B s t R).
Proof. exact (@lem7164723 A B (term889 A B s t R)). Qed.
Lemma lem7164725 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term890 A B s t R x) = (term883 A B s t R x).
Proof. exact (eq_refl (term890 A B s t R x)). Qed.
Lemma lem7164726 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem7164727 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term891 A B s t R x y) = (term892 A B s t R x y).
Proof. exact (MK_COMB (@lem7164725 A B s t R x) (@lem7164726 B y)). Qed.
Lemma lem7164728 {A B : Type'} (s : A -> Prop) (y : B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term892 A B s t R x y) = (term881 A B s y t R x).
Proof. exact (eq_refl (term892 A B s t R x y)). Qed.
Lemma lem7164729 {A B : Type'} (s : A -> Prop) (y : B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term891 A B s t R x y) = (term881 A B s y t R x).
Proof. exact (TRANS (@lem7164727 A B s t R x y) (@lem7164728 A B s y t R x)). Qed.
Lemma lem7164730 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term893 A B s t R x) = (term883 A B s t R x).
Proof. exact (fun_ext (fun y : B => @lem7164729 A B s y t R x)). Qed.
Lemma lem7164731 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem7164732 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term894 A B s t R x) = (term884 A B s t R x).
Proof. exact (MK_COMB (@lem7164731 B) (@lem7164730 A B s t R x)). Qed.
Lemma lem7164733 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term895 A B s t R) = (term885 A B s t R).
Proof. exact (fun_ext (fun x : A => @lem7164732 A B s t R x)). Qed.
Lemma lem7164734 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7164735 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term887 A B s t R) = (term886 A B s t R).
Proof. exact (MK_COMB (@lem7164734 A) (@lem7164733 A B s t R)). Qed.
Lemma lem7164736 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7164737 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term896 A B s t R) = (term897 A B s t R).
Proof. exact (MK_COMB (@lem7164736) (@lem7164735 A B s t R)). Qed.
Lemma lem7164738 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term890 A B s t R x) = (term883 A B s t R x).
Proof. exact (eq_refl (term890 A B s t R x)). Qed.
Lemma lem7164739 {A B : Type'} (y : A -> B) (x : A) : (y x) = (y x).
Proof. exact (eq_refl (y x)). Qed.
Lemma lem7164740 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (y : A -> B) (x : A) : (term898 A B s t R y x) = (term899 A B s t R y x).
Proof. exact (MK_COMB (@lem7164738 A B s t R x) (@lem7164739 A B y x)). Qed.
Lemma lem7164741 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term899 A B s t R y x) = (term900 A B s y t R x).
Proof. exact (eq_refl (term899 A B s t R y x)). Qed.
Lemma lem7164742 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term898 A B s t R y x) = (term900 A B s y t R x).
Proof. exact (TRANS (@lem7164740 A B s t R y x) (@lem7164741 A B s y t R x)). Qed.
Lemma lem7164743 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) : (term901 A B s t R y) = (term902 A B s y t R).
Proof. exact (fun_ext (fun x : A => @lem7164742 A B s y t R x)). Qed.
Lemma lem7164744 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7164745 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) : (term903 A B s t R y) = (term904 A B s y t R).
Proof. exact (MK_COMB (@lem7164744 A) (@lem7164743 A B s y t R)). Qed.
Lemma lem7164746 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term905 A B s t R) = (term906 A B s t R).
Proof. exact (fun_ext (fun y : A -> B => @lem7164745 A B s y t R)). Qed.
Lemma lem7164747 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem7164748 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term888 A B s t R) = (term907 A B s t R).
Proof. exact (MK_COMB (@lem7164747 A B) (@lem7164746 A B s t R)). Qed.
Lemma lem7164749 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : ((term887 A B s t R) = (term888 A B s t R)) = ((term886 A B s t R) = (term907 A B s t R)).
Proof. exact (MK_COMB (@lem7164737 A B s t R) (@lem7164748 A B s t R)). Qed.
Lemma lem7164750 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term886 A B s t R) = (term907 A B s t R).
Proof. exact (EQ_MP (@lem7164749 A B s t R) (@lem7164724 A B s t R)). Qed.
Lemma lem7164751 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term856 A B s t R) = (term907 A B s t R).
Proof. exact (TRANS (@lem7164720 A B s t R) (@lem7164750 A B s t R)). Qed.
Lemma lem7164752 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7164753 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term857 A B s t R) = (term908 A B s t R).
Proof. exact (MK_COMB (@lem7164752) (@lem7164751 A B s t R)). Qed.
Lemma lem7164754 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem7164755 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term858 A B t R s) = (term909 A B t R s).
Proof. exact (MK_COMB (@lem7164753 A B s t R) (@lem7164754 A s)). Qed.
Lemma lem7164757 {A : Type'} (P : A -> Prop) (Q : Prop) : (term311 A P Q) = (term312 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem7164758 {A B : Type'} (P : type572 A B) (Q : Prop) : (term910 A B P Q) = (term911 A B P Q).
Proof. exact (@lem7164757 (A -> B) P Q). Qed.
Lemma lem7164759 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term912 A B t R s) = (term913 A B t R s).
Proof. exact (@lem7164758 A B (term906 A B s t R) (@FINITE A s)). Qed.
Lemma lem7164760 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) : (term914 A B s t R y) = (term904 A B s y t R).
Proof. exact (eq_refl (term914 A B s t R y)). Qed.
Lemma lem7164761 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term915 A B s t R) = (term906 A B s t R).
Proof. exact (fun_ext (fun y : A -> B => @lem7164760 A B s y t R)). Qed.
Lemma lem7164762 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem7164763 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term916 A B s t R) = (term907 A B s t R).
Proof. exact (MK_COMB (@lem7164762 A B) (@lem7164761 A B s t R)). Qed.
Lemma lem7164764 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7164765 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term917 A B s t R) = (term908 A B s t R).
Proof. exact (MK_COMB (@lem7164764) (@lem7164763 A B s t R)). Qed.
Lemma lem7164766 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem7164767 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term912 A B t R s) = (term909 A B t R s).
Proof. exact (MK_COMB (@lem7164765 A B s t R) (@lem7164766 A s)). Qed.
Lemma lem7164768 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7164769 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term918 A B t R s) = (term919 A B t R s).
Proof. exact (MK_COMB (@lem7164768) (@lem7164767 A B t R s)). Qed.
Lemma lem7164770 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) : (term914 A B s t R y) = (term904 A B s y t R).
Proof. exact (eq_refl (term914 A B s t R y)). Qed.
Lemma lem7164771 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7164772 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) : (term920 A B s t R y) = (term921 A B s y t R).
Proof. exact (MK_COMB (@lem7164771) (@lem7164770 A B s y t R)). Qed.
Lemma lem7164773 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem7164774 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term922 A B t R y s) = (term923 A B y t R s).
Proof. exact (MK_COMB (@lem7164772 A B s y t R) (@lem7164773 A s)). Qed.
Lemma lem7164775 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term924 A B t R s) = (term925 A B t R s).
Proof. exact (fun_ext (fun y : A -> B => @lem7164774 A B y t R s)). Qed.
Lemma lem7164776 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem7164777 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term913 A B t R s) = (term926 A B t R s).
Proof. exact (MK_COMB (@lem7164776 A B) (@lem7164775 A B t R s)). Qed.
Lemma lem7164778 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : ((term912 A B t R s) = (term913 A B t R s)) = ((term909 A B t R s) = (term926 A B t R s)).
Proof. exact (MK_COMB (@lem7164769 A B t R s) (@lem7164777 A B t R s)). Qed.
Lemma lem7164779 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term909 A B t R s) = (term926 A B t R s).
Proof. exact (EQ_MP (@lem7164778 A B t R s) (@lem7164759 A B t R s)). Qed.
Lemma lem7164780 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term858 A B t R s) = (term926 A B t R s).
Proof. exact (TRANS (@lem7164755 A B t R s) (@lem7164779 A B t R s)). Qed.
Lemma lem7164781 {B : Type'} (t : B -> Prop) (x : B) : (term628 B t x) = (term628 B t x).
Proof. exact (eq_refl (term628 B t x)). Qed.
Lemma lem7164782 {A B : Type'} (x : B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term859 A B x t R s) = (term927 A B x t R s).
Proof. exact (MK_COMB (@lem7164781 B t x) (@lem7164780 A B t R s)). Qed.
Lemma lem7164784 {A : Type'} (P : Prop) (Q : A -> Prop) : (term928 A P Q) = (term929 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem7164785 {A B : Type'} (P : Prop) (Q : type572 A B) : (term930 A B P Q) = (term931 A B P Q).
Proof. exact (@lem7164784 (A -> B) P Q). Qed.
Lemma lem7164786 {A B : Type'} (x : B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term932 A B x t R s) = (term933 A B x t R s).
Proof. exact (@lem7164785 A B (t x) (term925 A B t R s)). Qed.
Lemma lem7164787 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term934 A B t R s y) = (term923 A B y t R s).
Proof. exact (eq_refl (term934 A B t R s y)). Qed.
Lemma lem7164788 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term935 A B t R s) = (term925 A B t R s).
Proof. exact (fun_ext (fun y : A -> B => @lem7164787 A B y t R s)). Qed.
Lemma lem7164789 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem7164790 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term936 A B t R s) = (term926 A B t R s).
Proof. exact (MK_COMB (@lem7164789 A B) (@lem7164788 A B t R s)). Qed.
Lemma lem7164791 {B : Type'} (t : B -> Prop) (x : B) : (term628 B t x) = (term628 B t x).
Proof. exact (eq_refl (term628 B t x)). Qed.
Lemma lem7164792 {A B : Type'} (x : B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term932 A B x t R s) = (term927 A B x t R s).
Proof. exact (MK_COMB (@lem7164791 B t x) (@lem7164790 A B t R s)). Qed.
Lemma lem7164793 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7164794 {A B : Type'} (x : B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term937 A B x t R s) = (term938 A B x t R s).
Proof. exact (MK_COMB (@lem7164793) (@lem7164792 A B x t R s)). Qed.
Lemma lem7164795 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term934 A B t R s y) = (term923 A B y t R s).
Proof. exact (eq_refl (term934 A B t R s y)). Qed.
Lemma lem7164796 {B : Type'} (t : B -> Prop) (x : B) : (term628 B t x) = (term628 B t x).
Proof. exact (eq_refl (term628 B t x)). Qed.
Lemma lem7164797 {A B : Type'} (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term939 A B x t R s y) = (term940 A B x y t R s).
Proof. exact (MK_COMB (@lem7164796 B t x) (@lem7164795 A B y t R s)). Qed.
Lemma lem7164798 {A B : Type'} (x : B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term941 A B x t R s) = (term942 A B x t R s).
Proof. exact (fun_ext (fun y : A -> B => @lem7164797 A B x y t R s)). Qed.
Lemma lem7164799 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem7164800 {A B : Type'} (x : B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term933 A B x t R s) = (term943 A B x t R s).
Proof. exact (MK_COMB (@lem7164799 A B) (@lem7164798 A B x t R s)). Qed.
Lemma lem7164801 {A B : Type'} (x : B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : ((term932 A B x t R s) = (term933 A B x t R s)) = ((term927 A B x t R s) = (term943 A B x t R s)).
Proof. exact (MK_COMB (@lem7164794 A B x t R s) (@lem7164800 A B x t R s)). Qed.
Lemma lem7164802 {A B : Type'} (x : B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term927 A B x t R s) = (term943 A B x t R s).
Proof. exact (EQ_MP (@lem7164801 A B x t R s) (@lem7164786 A B x t R s)). Qed.
Lemma lem7164803 {A B : Type'} (x : B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term859 A B x t R s) = (term943 A B x t R s).
Proof. exact (TRANS (@lem7164782 A B x t R s) (@lem7164802 A B x t R s)). Qed.
Lemma lem7164804 {A B : Type'} (x : B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term838 A B x t R s) = (term943 A B x t R s).
Proof. exact (TRANS (@lem7164670 A B x t R s) (@lem7164803 A B x t R s)). Qed.
Lemma lem7164805 {A B : Type'} (x : B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term639 A B x t R s) = (term943 A B x t R s).
Proof. exact (TRANS (@lem7164410 A B x t R s) (@lem7164804 A B x t R s)). Qed.
Lemma lem7164806 {A B : Type'} (x : B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term639 A B x t R s) : term943 A B x t R s.
Proof. exact (EQ_MP (@lem7164805 A B x t R s) (@lem7164141 A B x t R s h1)). Qed.
Lemma lem7164815 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x' : A) (x : B) : (term944 A B s R x' x) = (term945 A B s R x' x).
Proof. exact (@lem17045 (s x') (R x' x)). Qed.
Lemma lem7164827 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) : (term946 A B s _95913 t R x' x) = (term947 A B s _95913 t R x' x).
Proof. exact (@lem17045 (s x') ((_95913 t R x') = x)). Qed.
Lemma lem7164830 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) : (term731 A B s _95913 t R x' x) = (term731 A B s _95913 t R x' x).
Proof. exact (eq_refl (term731 A B s _95913 t R x' x)). Qed.
Lemma lem7164831 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7164832 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x' : A) (x : B) : (term948 A B s R x' x) = (term949 A B s R x' x).
Proof. exact (MK_COMB (@lem7164831) (@lem7164815 A B s R x' x)). Qed.
Lemma lem7164833 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) : (term950 A B s _95913 t R x' x) = (term951 A B s _95913 t R x' x).
Proof. exact (MK_COMB (@lem7164832 A B s R x' x) (@lem7164830 A B s _95913 t R x' x)). Qed.
Lemma lem7164835 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x' : A) (x : B) : (term952 A B s R x' x) = (term952 A B s R x' x).
Proof. exact (eq_refl (term952 A B s R x' x)). Qed.
Lemma lem7164836 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) : (term953 A B s _95913 t R x' x) = (term954 A B s _95913 t R x' x).
Proof. exact (MK_COMB (@lem7164835 A B s R x' x) (@lem7164827 A B s _95913 t R x' x)). Qed.
Lemma lem7164837 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7164838 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) : (term955 A B s _95913 t R x' x) = (term956 A B s _95913 t R x' x).
Proof. exact (MK_COMB (@lem7164837) (@lem7164836 A B s _95913 t R x' x)). Qed.
Lemma lem7164839 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) : (term957 A B s _95913 t R x' x) = (term958 A B s _95913 t R x' x).
Proof. exact (MK_COMB (@lem7164838 A B s _95913 t R x' x) (@lem7164833 A B s _95913 t R x' x)). Qed.
Lemma lem7164840 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) : (term774 A B s _95913 t R x' x) = (term957 A B s _95913 t R x' x).
Proof. exact (@lem17646 (term660 A B s R x' x) (term731 A B s _95913 t R x' x)). Qed.
Lemma lem7164845 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) : (term774 A B s _95913 t R x' x) = (term958 A B s _95913 t R x' x).
Proof. exact (TRANS (@lem7164840 A B s _95913 t R x' x) (@lem7164839 A B s _95913 t R x' x)). Qed.
Lemma lem7164846 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term774 A B s _95913 t R x' x) : term958 A B s _95913 t R x' x.
Proof. exact (EQ_MP (@lem7164845 A B s _95913 t R x' x) (@lem7164146 A B s _95913 t R x' x h1)). Qed.
Lemma lem7164847 {A B : Type'} (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term940 A B x y t R s.
Proof. exact (h1). Qed.
Lemma lem7164858 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7164859 {A B : Type'} (f : type830 A B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> (A -> B -> Prop) -> A -> B) f x).
Proof. exact (@lem7164858 (B -> Prop) (type467 A B) f x). Qed.
Lemma lem7164860 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) : (_95913 t) = (@I ((B -> Prop) -> (A -> B -> Prop) -> A -> B) _95913 t).
Proof. exact (@lem7164859 A B _95913 t). Qed.
Lemma lem7164861 {A B : Type'} (R : type1413 A B) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem7164862 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (_95913 t R) = (@I ((B -> Prop) -> (A -> B -> Prop) -> A -> B) _95913 t R).
Proof. exact (MK_COMB (@lem7164860 A B _95913 t) (@lem7164861 A B R)). Qed.
Lemma lem7164864 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7164865 {A B : Type'} (f : type467 A B) (x : type1413 A B) : (f x) = (@I ((A -> B -> Prop) -> A -> B) f x).
Proof. exact (@lem7164864 (type1413 A B) (A -> B) f x). Qed.
Lemma lem7164866 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (@I ((B -> Prop) -> (A -> B -> Prop) -> A -> B) _95913 t R) = (term365 A B _95913 t R).
Proof. exact (@lem7164865 A B (@I ((B -> Prop) -> (A -> B -> Prop) -> A -> B) _95913 t) R). Qed.
Lemma lem7164867 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (_95913 t R) = (term365 A B _95913 t R).
Proof. exact (TRANS (@lem7164862 A B _95913 t R) (@lem7164866 A B _95913 t R)). Qed.
Lemma lem7164868 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7164869 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (_95913 t R x) = (term366 A B _95913 t R x).
Proof. exact (MK_COMB (@lem7164867 A B _95913 t R) (@lem7164868 A x)). Qed.
Lemma lem7164871 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7164872 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem7164871 A B f x). Qed.
Lemma lem7164873 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term366 A B _95913 t R x) = (term367 A B _95913 t R x).
Proof. exact (@lem7164872 A B (term365 A B _95913 t R) x). Qed.
Lemma lem7164875 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (_95913 t R x) = (term367 A B _95913 t R x).
Proof. exact (TRANS (@lem7164869 A B _95913 t R x) (@lem7164873 A B _95913 t R x)). Qed.
Lemma lem7164876 {A B : Type'} (R : type1413 A B) (x : A) : (R x) = (R x).
Proof. exact (eq_refl (R x)). Qed.
Lemma lem7164877 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term161 A B _95913 t R x) = (term368 A B _95913 t R x).
Proof. exact (MK_COMB (@lem7164876 A B R x) (@lem7164875 A B _95913 t R x)). Qed.
Lemma lem7164879 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7164880 {A B : Type'} (f : type1413 A B) (x : A) : (f x) = (@I (A -> B -> Prop) f x).
Proof. exact (@lem7164879 A (B -> Prop) f x). Qed.
Lemma lem7164881 {A B : Type'} (R : type1413 A B) (x : A) : (R x) = (@I (A -> B -> Prop) R x).
Proof. exact (@lem7164880 A B R x). Qed.
Lemma lem7164882 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term367 A B _95913 t R x) = (term367 A B _95913 t R x).
Proof. exact (eq_refl (term367 A B _95913 t R x)). Qed.
Lemma lem7164883 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term368 A B _95913 t R x) = (term369 A B _95913 t R x).
Proof. exact (MK_COMB (@lem7164881 A B R x) (@lem7164882 A B _95913 t R x)). Qed.
Lemma lem7164885 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7164886 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem7164885 B Prop f x). Qed.
Lemma lem7164887 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term369 A B _95913 t R x) = (term370 A B _95913 t R x).
Proof. exact (@lem7164886 B (@I (A -> B -> Prop) R x) (term367 A B _95913 t R x)). Qed.
Lemma lem7164888 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term368 A B _95913 t R x) = (term370 A B _95913 t R x).
Proof. exact (TRANS (@lem7164883 A B _95913 t R x) (@lem7164887 A B _95913 t R x)). Qed.
Lemma lem7164889 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term161 A B _95913 t R x) = (term370 A B _95913 t R x).
Proof. exact (TRANS (@lem7164877 A B _95913 t R x) (@lem7164888 A B _95913 t R x)). Qed.
Lemma lem7164890 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem7164899 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7164900 {A B : Type'} (f : type830 A B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> (A -> B -> Prop) -> A -> B) f x).
Proof. exact (@lem7164899 (B -> Prop) (type467 A B) f x). Qed.
Lemma lem7164901 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) : (_95913 t) = (@I ((B -> Prop) -> (A -> B -> Prop) -> A -> B) _95913 t).
Proof. exact (@lem7164900 A B _95913 t). Qed.
Lemma lem7164902 {A B : Type'} (R : type1413 A B) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem7164903 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (_95913 t R) = (@I ((B -> Prop) -> (A -> B -> Prop) -> A -> B) _95913 t R).
Proof. exact (MK_COMB (@lem7164901 A B _95913 t) (@lem7164902 A B R)). Qed.
Lemma lem7164905 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7164906 {A B : Type'} (f : type467 A B) (x : type1413 A B) : (f x) = (@I ((A -> B -> Prop) -> A -> B) f x).
Proof. exact (@lem7164905 (type1413 A B) (A -> B) f x). Qed.
Lemma lem7164907 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (@I ((B -> Prop) -> (A -> B -> Prop) -> A -> B) _95913 t R) = (term365 A B _95913 t R).
Proof. exact (@lem7164906 A B (@I ((B -> Prop) -> (A -> B -> Prop) -> A -> B) _95913 t) R). Qed.
Lemma lem7164908 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (_95913 t R) = (term365 A B _95913 t R).
Proof. exact (TRANS (@lem7164903 A B _95913 t R) (@lem7164907 A B _95913 t R)). Qed.
Lemma lem7164909 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7164910 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (_95913 t R x) = (term366 A B _95913 t R x).
Proof. exact (MK_COMB (@lem7164908 A B _95913 t R) (@lem7164909 A x)). Qed.
Lemma lem7164912 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7164913 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem7164912 A B f x). Qed.
Lemma lem7164914 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term366 A B _95913 t R x) = (term367 A B _95913 t R x).
Proof. exact (@lem7164913 A B (term365 A B _95913 t R) x). Qed.
Lemma lem7164916 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (_95913 t R x) = (term367 A B _95913 t R x).
Proof. exact (TRANS (@lem7164910 A B _95913 t R x) (@lem7164914 A B _95913 t R x)). Qed.
Lemma lem7164917 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term712 A B _95913 t R x) = (term959 A B _95913 t R x).
Proof. exact (MK_COMB (@lem7164890 B t) (@lem7164916 A B _95913 t R x)). Qed.
Lemma lem7164919 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7164920 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem7164919 B Prop f x). Qed.
Lemma lem7164921 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term959 A B _95913 t R x) = (term960 A B _95913 t R x).
Proof. exact (@lem7164920 B t (term367 A B _95913 t R x)). Qed.
Lemma lem7164922 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term712 A B _95913 t R x) = (term960 A B _95913 t R x).
Proof. exact (TRANS (@lem7164917 A B _95913 t R x) (@lem7164921 A B _95913 t R x)). Qed.
Lemma lem7164923 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7164924 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term714 A B _95913 t R x) = (term961 A B _95913 t R x).
Proof. exact (MK_COMB (@lem7164923) (@lem7164922 A B _95913 t R x)). Qed.
Lemma lem7164925 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term716 A B _95913 t R x) = (term962 A B _95913 t R x).
Proof. exact (MK_COMB (@lem7164924 A B _95913 t R x) (@lem7164889 A B _95913 t R x)). Qed.
Lemma lem7164926 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7164933 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7164934 {A B : Type'} (f : type1413 A B) (x : A) : (f x) = (@I (A -> B -> Prop) f x).
Proof. exact (@lem7164933 A (B -> Prop) f x). Qed.
Lemma lem7164935 {A B : Type'} (R : type1413 A B) (x : A) : (R x) = (@I (A -> B -> Prop) R x).
Proof. exact (@lem7164934 A B R x). Qed.
Lemma lem7164936 {B : Type'} (x : B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7164937 {A B : Type'} (R : type1413 A B) (x : A) (x' : B) : (R x x') = (@I (A -> B -> Prop) R x x').
Proof. exact (MK_COMB (@lem7164935 A B R x) (@lem7164936 B x')). Qed.
Lemma lem7164939 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7164940 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem7164939 B Prop f x). Qed.
Lemma lem7164941 {A B : Type'} (R : type1413 A B) (x : A) (x' : B) : (@I (A -> B -> Prop) R x x') = (term378 A B R x x').
Proof. exact (@lem7164940 B (@I (A -> B -> Prop) R x) x'). Qed.
Lemma lem7164943 {A B : Type'} (R : type1413 A B) (x : A) (x' : B) : (R x x') = (term378 A B R x x').
Proof. exact (TRANS (@lem7164937 A B R x x') (@lem7164941 A B R x x')). Qed.
Lemma lem7164944 {A B : Type'} (R : type1413 A B) (x : A) (x' : B) : (term379 A B R x x') = (term380 A B R x x').
Proof. exact (MK_COMB (@lem7164926) (@lem7164943 A B R x x')). Qed.
Lemma lem7164945 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7164950 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7164951 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem7164950 B Prop f x). Qed.
Lemma lem7164953 {B : Type'} (t : B -> Prop) (x : B) : (t x) = (@I (B -> Prop) t x).
Proof. exact (@lem7164951 B t x). Qed.
Lemma lem7164954 {B : Type'} (t : B -> Prop) (x : B) : (term874 B t x) = (term963 B t x).
Proof. exact (MK_COMB (@lem7164945) (@lem7164953 B t x)). Qed.
Lemma lem7164955 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7164956 {B : Type'} (t : B -> Prop) (x : B) : (term831 B t x) = (term964 B t x).
Proof. exact (MK_COMB (@lem7164955) (@lem7164954 B t x)). Qed.
Lemma lem7164957 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term776 A B t R x x') = (term965 A B t R x x').
Proof. exact (MK_COMB (@lem7164956 B t x') (@lem7164944 A B R x x')). Qed.
Lemma lem7164958 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term791 A B t R x) = (term966 A B t R x).
Proof. exact (fun_ext (fun x' : B => @lem7164957 A B t R x x')). Qed.
Lemma lem7164959 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7164960 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term800 A B t R x) = (term967 A B t R x).
Proof. exact (MK_COMB (@lem7164959 B) (@lem7164958 A B t R x)). Qed.
Lemma lem7164961 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7164962 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term802 A B t R x) = (term968 A B t R x).
Proof. exact (MK_COMB (@lem7164961) (@lem7164960 A B t R x)). Qed.
Lemma lem7164963 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term803 A B _95913 t R x) = (term969 A B _95913 t R x).
Proof. exact (MK_COMB (@lem7164962 A B t R x) (@lem7164925 A B _95913 t R x)). Qed.
Lemma lem7164964 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (term804 A B _95913 t R) = (term970 A B _95913 t R).
Proof. exact (fun_ext (fun x : A => @lem7164963 A B _95913 t R x)). Qed.
Lemma lem7164965 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7164966 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (term805 A B _95913 t R) = (term971 A B _95913 t R).
Proof. exact (MK_COMB (@lem7164965 A) (@lem7164964 A B _95913 t R)). Qed.
Lemma lem7164967 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) : (term806 A B _95913 t) = (term972 A B _95913 t).
Proof. exact (fun_ext (fun R : type1413 A B => @lem7164966 A B _95913 t R)). Qed.
Lemma lem7164968 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem7164969 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) : (term807 A B _95913 t) = (term973 A B _95913 t).
Proof. exact (MK_COMB (@lem7164968 A B) (@lem7164967 A B _95913 t)). Qed.
Lemma lem7164970 {A B : Type'} (_95913 : type830 A B) : (term808 A B _95913) = (term974 A B _95913).
Proof. exact (fun_ext (fun t : B -> Prop => @lem7164969 A B _95913 t)). Qed.
Lemma lem7164971 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem7164972 {A B : Type'} (_95913 : type830 A B) : (term809 A B _95913) = (term975 A B _95913).
Proof. exact (MK_COMB (@lem7164971 B) (@lem7164970 A B _95913)). Qed.
Lemma lem7164973 {A B : Type'} (_95913 : type830 A B) (h1 : term728 A B _95913) : term975 A B _95913.
Proof. exact (EQ_MP (@lem7164972 A B _95913) (@lem7164348 A B _95913 h1)). Qed.
Lemma lem7164974 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem7164983 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7164984 {A B : Type'} (f : type830 A B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> (A -> B -> Prop) -> A -> B) f x).
Proof. exact (@lem7164983 (B -> Prop) (type467 A B) f x). Qed.
Lemma lem7164985 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) : (_95913 t) = (@I ((B -> Prop) -> (A -> B -> Prop) -> A -> B) _95913 t).
Proof. exact (@lem7164984 A B _95913 t). Qed.
Lemma lem7164986 {A B : Type'} (R : type1413 A B) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem7164987 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (_95913 t R) = (@I ((B -> Prop) -> (A -> B -> Prop) -> A -> B) _95913 t R).
Proof. exact (MK_COMB (@lem7164985 A B _95913 t) (@lem7164986 A B R)). Qed.
Lemma lem7164989 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7164990 {A B : Type'} (f : type467 A B) (x : type1413 A B) : (f x) = (@I ((A -> B -> Prop) -> A -> B) f x).
Proof. exact (@lem7164989 (type1413 A B) (A -> B) f x). Qed.
Lemma lem7164991 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (@I ((B -> Prop) -> (A -> B -> Prop) -> A -> B) _95913 t R) = (term365 A B _95913 t R).
Proof. exact (@lem7164990 A B (@I ((B -> Prop) -> (A -> B -> Prop) -> A -> B) _95913 t) R). Qed.
Lemma lem7164992 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (_95913 t R) = (term365 A B _95913 t R).
Proof. exact (TRANS (@lem7164987 A B _95913 t R) (@lem7164991 A B _95913 t R)). Qed.
Lemma lem7164993 {A : Type'} (x' : A) : x' = x'.
Proof. exact (eq_refl x'). Qed.
Lemma lem7164994 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) : (_95913 t R x') = (term366 A B _95913 t R x').
Proof. exact (MK_COMB (@lem7164992 A B _95913 t R) (@lem7164993 A x')). Qed.
Lemma lem7164996 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7164997 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem7164996 A B f x). Qed.
Lemma lem7164998 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) : (term366 A B _95913 t R x') = (term367 A B _95913 t R x').
Proof. exact (@lem7164997 A B (term365 A B _95913 t R) x'). Qed.
Lemma lem7165000 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) : (_95913 t R x') = (term367 A B _95913 t R x').
Proof. exact (TRANS (@lem7164994 A B _95913 t R x') (@lem7164998 A B _95913 t R x')). Qed.
Lemma lem7165001 {B : Type'} (x : B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7165002 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) : (term149 A B _95913 t R x') = (term976 A B _95913 t R x').
Proof. exact (MK_COMB (@lem7164974 B) (@lem7165000 A B _95913 t R x')). Qed.
Lemma lem7165003 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) : ((_95913 t R x') = x) = ((term367 A B _95913 t R x') = x).
Proof. exact (MK_COMB (@lem7165002 A B _95913 t R x') (@lem7165001 B x)). Qed.
Lemma lem7165008 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7165009 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem7165008 A Prop f x). Qed.
Lemma lem7165011 {A : Type'} (s : A -> Prop) (x' : A) : (s x') = (@I (A -> Prop) s x').
Proof. exact (@lem7165009 A s x'). Qed.
Lemma lem7165012 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7165013 {A : Type'} (s : A -> Prop) (x' : A) : (term628 A s x') = (term977 A s x').
Proof. exact (MK_COMB (@lem7165012) (@lem7165011 A s x')). Qed.
Lemma lem7165014 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) : (term731 A B s _95913 t R x' x) = (term978 A B s _95913 t R x' x).
Proof. exact (MK_COMB (@lem7165013 A s x') (@lem7165003 A B _95913 t R x' x)). Qed.
Lemma lem7165015 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7165022 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7165023 {A B : Type'} (f : type1413 A B) (x : A) : (f x) = (@I (A -> B -> Prop) f x).
Proof. exact (@lem7165022 A (B -> Prop) f x). Qed.
Lemma lem7165024 {A B : Type'} (R : type1413 A B) (x' : A) : (R x') = (@I (A -> B -> Prop) R x').
Proof. exact (@lem7165023 A B R x'). Qed.
Lemma lem7165025 {B : Type'} (x : B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7165026 {A B : Type'} (R : type1413 A B) (x' : A) (x : B) : (R x' x) = (@I (A -> B -> Prop) R x' x).
Proof. exact (MK_COMB (@lem7165024 A B R x') (@lem7165025 B x)). Qed.
Lemma lem7165028 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7165029 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem7165028 B Prop f x). Qed.
Lemma lem7165030 {A B : Type'} (R : type1413 A B) (x' : A) (x : B) : (@I (A -> B -> Prop) R x' x) = (term378 A B R x' x).
Proof. exact (@lem7165029 B (@I (A -> B -> Prop) R x') x). Qed.
Lemma lem7165032 {A B : Type'} (R : type1413 A B) (x' : A) (x : B) : (R x' x) = (term378 A B R x' x).
Proof. exact (TRANS (@lem7165026 A B R x' x) (@lem7165030 A B R x' x)). Qed.
Lemma lem7165033 {A B : Type'} (R : type1413 A B) (x' : A) (x : B) : (term379 A B R x' x) = (term380 A B R x' x).
Proof. exact (MK_COMB (@lem7165015) (@lem7165032 A B R x' x)). Qed.
Lemma lem7165034 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7165039 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7165040 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem7165039 A Prop f x). Qed.
Lemma lem7165042 {A : Type'} (s : A -> Prop) (x' : A) : (s x') = (@I (A -> Prop) s x').
Proof. exact (@lem7165040 A s x'). Qed.
Lemma lem7165043 {A : Type'} (s : A -> Prop) (x' : A) : (term874 A s x') = (term963 A s x').
Proof. exact (MK_COMB (@lem7165034) (@lem7165042 A s x')). Qed.
Lemma lem7165044 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7165045 {A : Type'} (s : A -> Prop) (x' : A) : (term831 A s x') = (term964 A s x').
Proof. exact (MK_COMB (@lem7165044) (@lem7165043 A s x')). Qed.
Lemma lem7165046 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x' : A) (x : B) : (term945 A B s R x' x) = (term979 A B s R x' x).
Proof. exact (MK_COMB (@lem7165045 A s x') (@lem7165033 A B R x' x)). Qed.
Lemma lem7165047 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7165048 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x' : A) (x : B) : (term949 A B s R x' x) = (term980 A B s R x' x).
Proof. exact (MK_COMB (@lem7165047) (@lem7165046 A B s R x' x)). Qed.
Lemma lem7165049 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) : (term951 A B s _95913 t R x' x) = (term981 A B s _95913 t R x' x).
Proof. exact (MK_COMB (@lem7165048 A B s R x' x) (@lem7165014 A B s _95913 t R x' x)). Qed.
Lemma lem7165050 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7165051 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem7165060 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7165061 {A B : Type'} (f : type830 A B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> (A -> B -> Prop) -> A -> B) f x).
Proof. exact (@lem7165060 (B -> Prop) (type467 A B) f x). Qed.
Lemma lem7165062 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) : (_95913 t) = (@I ((B -> Prop) -> (A -> B -> Prop) -> A -> B) _95913 t).
Proof. exact (@lem7165061 A B _95913 t). Qed.
Lemma lem7165063 {A B : Type'} (R : type1413 A B) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem7165064 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (_95913 t R) = (@I ((B -> Prop) -> (A -> B -> Prop) -> A -> B) _95913 t R).
Proof. exact (MK_COMB (@lem7165062 A B _95913 t) (@lem7165063 A B R)). Qed.
Lemma lem7165066 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7165067 {A B : Type'} (f : type467 A B) (x : type1413 A B) : (f x) = (@I ((A -> B -> Prop) -> A -> B) f x).
Proof. exact (@lem7165066 (type1413 A B) (A -> B) f x). Qed.
Lemma lem7165068 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (@I ((B -> Prop) -> (A -> B -> Prop) -> A -> B) _95913 t R) = (term365 A B _95913 t R).
Proof. exact (@lem7165067 A B (@I ((B -> Prop) -> (A -> B -> Prop) -> A -> B) _95913 t) R). Qed.
Lemma lem7165069 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (_95913 t R) = (term365 A B _95913 t R).
Proof. exact (TRANS (@lem7165064 A B _95913 t R) (@lem7165068 A B _95913 t R)). Qed.
Lemma lem7165070 {A : Type'} (x' : A) : x' = x'.
Proof. exact (eq_refl x'). Qed.
Lemma lem7165071 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) : (_95913 t R x') = (term366 A B _95913 t R x').
Proof. exact (MK_COMB (@lem7165069 A B _95913 t R) (@lem7165070 A x')). Qed.
Lemma lem7165073 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7165074 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem7165073 A B f x). Qed.
Lemma lem7165075 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) : (term366 A B _95913 t R x') = (term367 A B _95913 t R x').
Proof. exact (@lem7165074 A B (term365 A B _95913 t R) x'). Qed.
Lemma lem7165077 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) : (_95913 t R x') = (term367 A B _95913 t R x').
Proof. exact (TRANS (@lem7165071 A B _95913 t R x') (@lem7165075 A B _95913 t R x')). Qed.
Lemma lem7165078 {B : Type'} (x : B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7165079 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) : (term149 A B _95913 t R x') = (term976 A B _95913 t R x').
Proof. exact (MK_COMB (@lem7165051 B) (@lem7165077 A B _95913 t R x')). Qed.
Lemma lem7165080 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) : ((_95913 t R x') = x) = ((term367 A B _95913 t R x') = x).
Proof. exact (MK_COMB (@lem7165079 A B _95913 t R x') (@lem7165078 B x)). Qed.
Lemma lem7165081 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) : (term982 A B _95913 t R x' x) = (term983 A B _95913 t R x' x).
Proof. exact (MK_COMB (@lem7165050) (@lem7165080 A B _95913 t R x' x)). Qed.
Lemma lem7165082 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7165087 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7165088 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem7165087 A Prop f x). Qed.
Lemma lem7165090 {A : Type'} (s : A -> Prop) (x' : A) : (s x') = (@I (A -> Prop) s x').
Proof. exact (@lem7165088 A s x'). Qed.
Lemma lem7165091 {A : Type'} (s : A -> Prop) (x' : A) : (term874 A s x') = (term963 A s x').
Proof. exact (MK_COMB (@lem7165082) (@lem7165090 A s x')). Qed.
Lemma lem7165092 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7165093 {A : Type'} (s : A -> Prop) (x' : A) : (term831 A s x') = (term964 A s x').
Proof. exact (MK_COMB (@lem7165092) (@lem7165091 A s x')). Qed.
Lemma lem7165094 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) : (term947 A B s _95913 t R x' x) = (term984 A B s _95913 t R x' x).
Proof. exact (MK_COMB (@lem7165093 A s x') (@lem7165081 A B _95913 t R x' x)). Qed.
Lemma lem7165101 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7165102 {A B : Type'} (f : type1413 A B) (x : A) : (f x) = (@I (A -> B -> Prop) f x).
Proof. exact (@lem7165101 A (B -> Prop) f x). Qed.
Lemma lem7165103 {A B : Type'} (R : type1413 A B) (x' : A) : (R x') = (@I (A -> B -> Prop) R x').
Proof. exact (@lem7165102 A B R x'). Qed.
Lemma lem7165104 {B : Type'} (x : B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7165105 {A B : Type'} (R : type1413 A B) (x' : A) (x : B) : (R x' x) = (@I (A -> B -> Prop) R x' x).
Proof. exact (MK_COMB (@lem7165103 A B R x') (@lem7165104 B x)). Qed.
Lemma lem7165107 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7165108 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem7165107 B Prop f x). Qed.
Lemma lem7165109 {A B : Type'} (R : type1413 A B) (x' : A) (x : B) : (@I (A -> B -> Prop) R x' x) = (term378 A B R x' x).
Proof. exact (@lem7165108 B (@I (A -> B -> Prop) R x') x). Qed.
Lemma lem7165111 {A B : Type'} (R : type1413 A B) (x' : A) (x : B) : (R x' x) = (term378 A B R x' x).
Proof. exact (TRANS (@lem7165105 A B R x' x) (@lem7165109 A B R x' x)). Qed.
Lemma lem7165116 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7165117 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem7165116 A Prop f x). Qed.
Lemma lem7165119 {A : Type'} (s : A -> Prop) (x' : A) : (s x') = (@I (A -> Prop) s x').
Proof. exact (@lem7165117 A s x'). Qed.
Lemma lem7165120 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7165121 {A : Type'} (s : A -> Prop) (x' : A) : (term628 A s x') = (term977 A s x').
Proof. exact (MK_COMB (@lem7165120) (@lem7165119 A s x')). Qed.
Lemma lem7165122 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x' : A) (x : B) : (term660 A B s R x' x) = (term985 A B s R x' x).
Proof. exact (MK_COMB (@lem7165121 A s x') (@lem7165111 A B R x' x)). Qed.
Lemma lem7165123 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7165124 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x' : A) (x : B) : (term952 A B s R x' x) = (term986 A B s R x' x).
Proof. exact (MK_COMB (@lem7165123) (@lem7165122 A B s R x' x)). Qed.
Lemma lem7165125 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) : (term954 A B s _95913 t R x' x) = (term987 A B s _95913 t R x' x).
Proof. exact (MK_COMB (@lem7165124 A B s R x' x) (@lem7165094 A B s _95913 t R x' x)). Qed.
Lemma lem7165126 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7165127 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) : (term956 A B s _95913 t R x' x) = (term988 A B s _95913 t R x' x).
Proof. exact (MK_COMB (@lem7165126) (@lem7165125 A B s _95913 t R x' x)). Qed.
Lemma lem7165128 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) : (term958 A B s _95913 t R x' x) = (term989 A B s _95913 t R x' x).
Proof. exact (MK_COMB (@lem7165127 A B s _95913 t R x' x) (@lem7165049 A B s _95913 t R x' x)). Qed.
Lemma lem7165129 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term774 A B s _95913 t R x' x) : term989 A B s _95913 t R x' x.
Proof. exact (EQ_MP (@lem7165128 A B s _95913 t R x' x) (@lem7164846 A B s _95913 t R x' x h1)). Qed.
Lemma lem7165134 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7165135 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem7165134 (A -> Prop) Prop f x). Qed.
Lemma lem7165137 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@I ((A -> Prop) -> Prop) (@FINITE A) s).
Proof. exact (@lem7165135 A (@FINITE A) s). Qed.
Lemma lem7165142 {B : Type'} (y' : B) (y : B) : (y' = y) = (y' = y).
Proof. exact (eq_refl (y' = y)). Qed.
Lemma lem7165143 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7165150 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7165151 {A B : Type'} (f : type1413 A B) (x : A) : (f x) = (@I (A -> B -> Prop) f x).
Proof. exact (@lem7165150 A (B -> Prop) f x). Qed.
Lemma lem7165152 {A B : Type'} (R : type1413 A B) (x : A) : (R x) = (@I (A -> B -> Prop) R x).
Proof. exact (@lem7165151 A B R x). Qed.
Lemma lem7165153 {B : Type'} (y' : B) : y' = y'.
Proof. exact (eq_refl y'). Qed.
Lemma lem7165154 {A B : Type'} (R : type1413 A B) (x : A) (y' : B) : (R x y') = (@I (A -> B -> Prop) R x y').
Proof. exact (MK_COMB (@lem7165152 A B R x) (@lem7165153 B y')). Qed.
Lemma lem7165156 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7165157 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem7165156 B Prop f x). Qed.
Lemma lem7165158 {A B : Type'} (R : type1413 A B) (x : A) (y' : B) : (@I (A -> B -> Prop) R x y') = (term378 A B R x y').
Proof. exact (@lem7165157 B (@I (A -> B -> Prop) R x) y'). Qed.
Lemma lem7165160 {A B : Type'} (R : type1413 A B) (x : A) (y' : B) : (R x y') = (term378 A B R x y').
Proof. exact (TRANS (@lem7165154 A B R x y') (@lem7165158 A B R x y')). Qed.
Lemma lem7165161 {A B : Type'} (R : type1413 A B) (x : A) (y' : B) : (term379 A B R x y') = (term380 A B R x y').
Proof. exact (MK_COMB (@lem7165143) (@lem7165160 A B R x y')). Qed.
Lemma lem7165162 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7165167 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7165168 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem7165167 B Prop f x). Qed.
Lemma lem7165170 {B : Type'} (t : B -> Prop) (y' : B) : (t y') = (@I (B -> Prop) t y').
Proof. exact (@lem7165168 B t y'). Qed.
Lemma lem7165171 {B : Type'} (t : B -> Prop) (y' : B) : (term874 B t y') = (term963 B t y').
Proof. exact (MK_COMB (@lem7165162) (@lem7165170 B t y')). Qed.
Lemma lem7165172 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7165173 {B : Type'} (t : B -> Prop) (y' : B) : (term831 B t y') = (term964 B t y').
Proof. exact (MK_COMB (@lem7165172) (@lem7165171 B t y')). Qed.
Lemma lem7165174 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term776 A B t R x y') = (term965 A B t R x y').
Proof. exact (MK_COMB (@lem7165173 B t y') (@lem7165161 A B R x y')). Qed.
Lemma lem7165175 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7165176 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term778 A B t R x y') = (term990 A B t R x y').
Proof. exact (MK_COMB (@lem7165175) (@lem7165174 A B t R x y')). Qed.
Lemma lem7165177 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y : B) : (term814 A B t R x y' y) = (term991 A B t R x y' y).
Proof. exact (MK_COMB (@lem7165176 A B t R x y') (@lem7165142 B y' y)). Qed.
Lemma lem7165178 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term841 A B t R x y) = (term992 A B t R x y).
Proof. exact (fun_ext (fun y' : B => @lem7165177 A B t R x y' y)). Qed.
Lemma lem7165179 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7165180 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term849 A B t R x y) = (term993 A B t R x y).
Proof. exact (MK_COMB (@lem7165179 B) (@lem7165178 A B t R x y)). Qed.
Lemma lem7165181 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7165188 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7165189 {A B : Type'} (f : type1413 A B) (x : A) : (f x) = (@I (A -> B -> Prop) f x).
Proof. exact (@lem7165188 A (B -> Prop) f x). Qed.
Lemma lem7165190 {A B : Type'} (R : type1413 A B) (x : A) : (R x) = (@I (A -> B -> Prop) R x).
Proof. exact (@lem7165189 A B R x). Qed.
Lemma lem7165191 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem7165192 {A B : Type'} (R : type1413 A B) (x : A) (y : B) : (R x y) = (@I (A -> B -> Prop) R x y).
Proof. exact (MK_COMB (@lem7165190 A B R x) (@lem7165191 B y)). Qed.
Lemma lem7165194 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7165195 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem7165194 B Prop f x). Qed.
Lemma lem7165196 {A B : Type'} (R : type1413 A B) (x : A) (y : B) : (@I (A -> B -> Prop) R x y) = (term378 A B R x y).
Proof. exact (@lem7165195 B (@I (A -> B -> Prop) R x) y). Qed.
Lemma lem7165198 {A B : Type'} (R : type1413 A B) (x : A) (y : B) : (R x y) = (term378 A B R x y).
Proof. exact (TRANS (@lem7165192 A B R x y) (@lem7165196 A B R x y)). Qed.
Lemma lem7165199 {A B : Type'} (R : type1413 A B) (x : A) (y : B) : (term379 A B R x y) = (term380 A B R x y).
Proof. exact (MK_COMB (@lem7165181) (@lem7165198 A B R x y)). Qed.
Lemma lem7165200 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7165205 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7165206 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem7165205 B Prop f x). Qed.
Lemma lem7165208 {B : Type'} (t : B -> Prop) (y : B) : (t y) = (@I (B -> Prop) t y).
Proof. exact (@lem7165206 B t y). Qed.
Lemma lem7165209 {B : Type'} (t : B -> Prop) (y : B) : (term874 B t y) = (term963 B t y).
Proof. exact (MK_COMB (@lem7165200) (@lem7165208 B t y)). Qed.
Lemma lem7165210 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7165211 {B : Type'} (t : B -> Prop) (y : B) : (term831 B t y) = (term964 B t y).
Proof. exact (MK_COMB (@lem7165210) (@lem7165209 B t y)). Qed.
Lemma lem7165212 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term776 A B t R x y) = (term965 A B t R x y).
Proof. exact (MK_COMB (@lem7165211 B t y) (@lem7165199 A B R x y)). Qed.
Lemma lem7165213 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7165214 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term778 A B t R x y) = (term990 A B t R x y).
Proof. exact (MK_COMB (@lem7165213) (@lem7165212 A B t R x y)). Qed.
Lemma lem7165215 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term850 A B t R x y) = (term994 A B t R x y).
Proof. exact (MK_COMB (@lem7165214 A B t R x y) (@lem7165180 A B t R x y)). Qed.
Lemma lem7165216 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term851 A B t R x) = (term995 A B t R x).
Proof. exact (fun_ext (fun y : B => @lem7165215 A B t R x y)). Qed.
Lemma lem7165217 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7165218 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term852 A B t R x) = (term996 A B t R x).
Proof. exact (MK_COMB (@lem7165217 B) (@lem7165216 A B t R x)). Qed.
Lemma lem7165225 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7165226 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem7165225 A B f x). Qed.
Lemma lem7165228 {A B : Type'} (y : A -> B) (x : A) : (y x) = (@I (A -> B) y x).
Proof. exact (@lem7165226 A B y x). Qed.
Lemma lem7165229 {A B : Type'} (R : type1413 A B) (x : A) : (R x) = (R x).
Proof. exact (eq_refl (R x)). Qed.
Lemma lem7165230 {A B : Type'} (R : type1413 A B) (y : A -> B) (x : A) : (term403 A B R y x) = (term404 A B R y x).
Proof. exact (MK_COMB (@lem7165229 A B R x) (@lem7165228 A B y x)). Qed.
Lemma lem7165232 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7165233 {A B : Type'} (f : type1413 A B) (x : A) : (f x) = (@I (A -> B -> Prop) f x).
Proof. exact (@lem7165232 A (B -> Prop) f x). Qed.
Lemma lem7165234 {A B : Type'} (R : type1413 A B) (x : A) : (R x) = (@I (A -> B -> Prop) R x).
Proof. exact (@lem7165233 A B R x). Qed.
Lemma lem7165235 {A B : Type'} (y : A -> B) (x : A) : (@I (A -> B) y x) = (@I (A -> B) y x).
Proof. exact (eq_refl (@I (A -> B) y x)). Qed.
Lemma lem7165236 {A B : Type'} (R : type1413 A B) (y : A -> B) (x : A) : (term404 A B R y x) = (term405 A B R y x).
Proof. exact (MK_COMB (@lem7165234 A B R x) (@lem7165235 A B y x)). Qed.
Lemma lem7165238 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7165239 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem7165238 B Prop f x). Qed.
Lemma lem7165240 {A B : Type'} (R : type1413 A B) (y : A -> B) (x : A) : (term405 A B R y x) = (term406 A B R y x).
Proof. exact (@lem7165239 B (@I (A -> B -> Prop) R x) (@I (A -> B) y x)). Qed.
Lemma lem7165241 {A B : Type'} (R : type1413 A B) (y : A -> B) (x : A) : (term404 A B R y x) = (term406 A B R y x).
Proof. exact (TRANS (@lem7165236 A B R y x) (@lem7165240 A B R y x)). Qed.
Lemma lem7165242 {A B : Type'} (R : type1413 A B) (y : A -> B) (x : A) : (term403 A B R y x) = (term406 A B R y x).
Proof. exact (TRANS (@lem7165230 A B R y x) (@lem7165241 A B R y x)). Qed.
Lemma lem7165243 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem7165248 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7165249 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem7165248 A B f x). Qed.
Lemma lem7165251 {A B : Type'} (y : A -> B) (x : A) : (y x) = (@I (A -> B) y x).
Proof. exact (@lem7165249 A B y x). Qed.
Lemma lem7165252 {A B : Type'} (t : B -> Prop) (y : A -> B) (x : A) : (term997 A B t y x) = (term998 A B t y x).
Proof. exact (MK_COMB (@lem7165243 B t) (@lem7165251 A B y x)). Qed.
Lemma lem7165254 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7165255 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem7165254 B Prop f x). Qed.
Lemma lem7165256 {A B : Type'} (t : B -> Prop) (y : A -> B) (x : A) : (term998 A B t y x) = (term999 A B t y x).
Proof. exact (@lem7165255 B t (@I (A -> B) y x)). Qed.
Lemma lem7165257 {A B : Type'} (t : B -> Prop) (y : A -> B) (x : A) : (term997 A B t y x) = (term999 A B t y x).
Proof. exact (TRANS (@lem7165252 A B t y x) (@lem7165256 A B t y x)). Qed.
Lemma lem7165258 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7165259 {A B : Type'} (t : B -> Prop) (y : A -> B) (x : A) : (term1000 A B t y x) = (term1001 A B t y x).
Proof. exact (MK_COMB (@lem7165258) (@lem7165257 A B t y x)). Qed.
Lemma lem7165260 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (y : A -> B) (x : A) : (term1002 A B t R y x) = (term1003 A B t R y x).
Proof. exact (MK_COMB (@lem7165259 A B t y x) (@lem7165242 A B R y x)). Qed.
Lemma lem7165261 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7165262 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (y : A -> B) (x : A) : (term1004 A B t R y x) = (term1005 A B t R y x).
Proof. exact (MK_COMB (@lem7165261) (@lem7165260 A B t R y x)). Qed.
Lemma lem7165263 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1006 A B y t R x) = (term1007 A B y t R x).
Proof. exact (MK_COMB (@lem7165262 A B t R y x) (@lem7165218 A B t R x)). Qed.
Lemma lem7165264 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7165269 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7165270 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem7165269 A Prop f x). Qed.
Lemma lem7165272 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem7165270 A s x). Qed.
Lemma lem7165273 {A : Type'} (s : A -> Prop) (x : A) : (term874 A s x) = (term963 A s x).
Proof. exact (MK_COMB (@lem7165264) (@lem7165272 A s x)). Qed.
Lemma lem7165274 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7165275 {A : Type'} (s : A -> Prop) (x : A) : (term831 A s x) = (term964 A s x).
Proof. exact (MK_COMB (@lem7165274) (@lem7165273 A s x)). Qed.
Lemma lem7165276 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term900 A B s y t R x) = (term1008 A B s y t R x).
Proof. exact (MK_COMB (@lem7165275 A s x) (@lem7165263 A B y t R x)). Qed.
Lemma lem7165277 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) : (term902 A B s y t R) = (term1009 A B s y t R).
Proof. exact (fun_ext (fun x : A => @lem7165276 A B s y t R x)). Qed.
Lemma lem7165278 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7165279 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) : (term904 A B s y t R) = (term1010 A B s y t R).
Proof. exact (MK_COMB (@lem7165278 A) (@lem7165277 A B s y t R)). Qed.
Lemma lem7165280 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7165281 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) : (term921 A B s y t R) = (term1011 A B s y t R).
Proof. exact (MK_COMB (@lem7165280) (@lem7165279 A B s y t R)). Qed.
Lemma lem7165282 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term923 A B y t R s) = (term1012 A B y t R s).
Proof. exact (MK_COMB (@lem7165281 A B s y t R) (@lem7165137 A s)). Qed.
Lemma lem7165287 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7165288 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem7165287 B Prop f x). Qed.
Lemma lem7165290 {B : Type'} (t : B -> Prop) (x : B) : (t x) = (@I (B -> Prop) t x).
Proof. exact (@lem7165288 B t x). Qed.
Lemma lem7165291 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7165292 {B : Type'} (t : B -> Prop) (x : B) : (term628 B t x) = (term977 B t x).
Proof. exact (MK_COMB (@lem7165291) (@lem7165290 B t x)). Qed.
Lemma lem7165293 {A B : Type'} (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term940 A B x y t R s) = (term1013 A B x y t R s).
Proof. exact (MK_COMB (@lem7165292 B t x) (@lem7165282 A B y t R s)). Qed.
Lemma lem7165294 {A B : Type'} (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1013 A B x y t R s.
Proof. exact (EQ_MP (@lem7165293 A B x y t R s) (@lem7164847 A B x y t R s h1)). Qed.
Lemma lem7165295 {A B : Type'} (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1012 A B y t R s.
Proof. exact (proj2 (@lem7165294 A B x y t R s h1)). Qed.
Lemma lem7165298 {A B : Type'} (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1010 A B s y t R.
Proof. exact (proj1 (@lem7165295 A B x y t R s h1)). Qed.
Lemma lem7165299 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term987 A B s _95913 t R x' x) : term987 A B s _95913 t R x' x.
Proof. exact (h1). Qed.
Lemma lem7165300 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term981 A B s _95913 t R x' x) : term981 A B s _95913 t R x' x.
Proof. exact (h1). Qed.
Lemma lem7165301 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term987 A B s _95913 t R x' x) : term984 A B s _95913 t R x' x.
Proof. exact (proj2 (@lem7165299 A B s _95913 t R x' x h1)). Qed.
Lemma lem7165302 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term987 A B s _95913 t R x' x) : term985 A B s R x' x.
Proof. exact (proj1 (@lem7165299 A B s _95913 t R x' x h1)). Qed.
Lemma lem7165307 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term981 A B s _95913 t R x' x) : term978 A B s _95913 t R x' x.
Proof. exact (proj2 (@lem7165300 A B s _95913 t R x' x h1)). Qed.
Lemma lem7165308 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term981 A B s _95913 t R x' x) : term979 A B s R x' x.
Proof. exact (proj1 (@lem7165300 A B s _95913 t R x' x h1)). Qed.
Lemma lem7165584 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term963 A s x') : term963 A s x'.
Proof. exact (h1). Qed.
Lemma lem7165586 {A : Type'} (P : A -> Prop) (Q : Prop) : (term242 A P Q) = (term241 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem7165587 {B : Type'} (P : B -> Prop) (Q : Prop) : (term242 B P Q) = (term241 B P Q).
Proof. exact (@lem7165586 B P Q). Qed.
Lemma lem7165588 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1014 A B _95913 t R x) = (term1015 A B _95913 t R x).
Proof. exact (@lem7165587 B (term966 A B t R x) (term962 A B _95913 t R x)). Qed.
Lemma lem7165589 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term1016 A B t R x x') = (term965 A B t R x x').
Proof. exact (eq_refl (term1016 A B t R x x')). Qed.
Lemma lem7165590 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term1017 A B t R x) = (term966 A B t R x).
Proof. exact (fun_ext (fun x' : B => @lem7165589 A B t R x x')). Qed.
Lemma lem7165591 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7165592 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term1018 A B t R x) = (term967 A B t R x).
Proof. exact (MK_COMB (@lem7165591 B) (@lem7165590 A B t R x)). Qed.
Lemma lem7165593 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7165594 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term1019 A B t R x) = (term968 A B t R x).
Proof. exact (MK_COMB (@lem7165593) (@lem7165592 A B t R x)). Qed.
Lemma lem7165595 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term962 A B _95913 t R x) = (term962 A B _95913 t R x).
Proof. exact (eq_refl (term962 A B _95913 t R x)). Qed.
Lemma lem7165596 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1014 A B _95913 t R x) = (term969 A B _95913 t R x).
Proof. exact (MK_COMB (@lem7165594 A B t R x) (@lem7165595 A B _95913 t R x)). Qed.
Lemma lem7165597 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7165598 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1020 A B _95913 t R x) = (term1021 A B _95913 t R x).
Proof. exact (MK_COMB (@lem7165597) (@lem7165596 A B _95913 t R x)). Qed.
Lemma lem7165599 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term1016 A B t R x x') = (term965 A B t R x x').
Proof. exact (eq_refl (term1016 A B t R x x')). Qed.
Lemma lem7165600 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7165601 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term1022 A B t R x x') = (term990 A B t R x x').
Proof. exact (MK_COMB (@lem7165600) (@lem7165599 A B t R x x')). Qed.
Lemma lem7165602 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term962 A B _95913 t R x) = (term962 A B _95913 t R x).
Proof. exact (eq_refl (term962 A B _95913 t R x)). Qed.
Lemma lem7165603 {A B : Type'} (x : B) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) : (term1023 A B x _95913 t R x') = (term1024 A B x _95913 t R x').
Proof. exact (MK_COMB (@lem7165601 A B t R x' x) (@lem7165602 A B _95913 t R x')). Qed.
Lemma lem7165604 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1025 A B _95913 t R x) = (term1026 A B _95913 t R x).
Proof. exact (fun_ext (fun x' : B => @lem7165603 A B x' _95913 t R x)). Qed.
Lemma lem7165605 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7165606 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1015 A B _95913 t R x) = (term1027 A B _95913 t R x).
Proof. exact (MK_COMB (@lem7165605 B) (@lem7165604 A B _95913 t R x)). Qed.
Lemma lem7165607 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : ((term1014 A B _95913 t R x) = (term1015 A B _95913 t R x)) = ((term969 A B _95913 t R x) = (term1027 A B _95913 t R x)).
Proof. exact (MK_COMB (@lem7165598 A B _95913 t R x) (@lem7165606 A B _95913 t R x)). Qed.
Lemma lem7165608 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term969 A B _95913 t R x) = (term1027 A B _95913 t R x).
Proof. exact (EQ_MP (@lem7165607 A B _95913 t R x) (@lem7165588 A B _95913 t R x)). Qed.
Lemma lem7165609 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (term970 A B _95913 t R) = (term1028 A B _95913 t R).
Proof. exact (fun_ext (fun x : A => @lem7165608 A B _95913 t R x)). Qed.
Lemma lem7165610 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7165611 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (term971 A B _95913 t R) = (term1029 A B _95913 t R).
Proof. exact (MK_COMB (@lem7165610 A) (@lem7165609 A B _95913 t R)). Qed.
Lemma lem7165612 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) : (term972 A B _95913 t) = (term1030 A B _95913 t).
Proof. exact (fun_ext (fun R : type1413 A B => @lem7165611 A B _95913 t R)). Qed.
Lemma lem7165613 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem7165614 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) : (term973 A B _95913 t) = (term1031 A B _95913 t).
Proof. exact (MK_COMB (@lem7165613 A B) (@lem7165612 A B _95913 t)). Qed.
Lemma lem7165615 {A B : Type'} (_95913 : type830 A B) : (term974 A B _95913) = (term1032 A B _95913).
Proof. exact (fun_ext (fun t : B -> Prop => @lem7165614 A B _95913 t)). Qed.
Lemma lem7165616 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem7165617 {A B : Type'} (_95913 : type830 A B) : (term975 A B _95913) = (term1033 A B _95913).
Proof. exact (MK_COMB (@lem7165616 B) (@lem7165615 A B _95913)). Qed.
Lemma lem7165640 {A B : Type'} (x : B) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) : (term1024 A B x _95913 t R x') = (term1034 A B x _95913 t R x').
Proof. exact (@lem19490 (term960 A B _95913 t R x') (term965 A B t R x' x) (term370 A B _95913 t R x')). Qed.
Lemma lem7165641 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1026 A B _95913 t R x) = (term1035 A B _95913 t R x).
Proof. exact (fun_ext (fun x' : B => @lem7165640 A B x' _95913 t R x)). Qed.
Lemma lem7165642 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7165643 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1027 A B _95913 t R x) = (term1036 A B _95913 t R x).
Proof. exact (MK_COMB (@lem7165642 B) (@lem7165641 A B _95913 t R x)). Qed.
Lemma lem7165644 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (term1028 A B _95913 t R) = (term1037 A B _95913 t R).
Proof. exact (fun_ext (fun x : A => @lem7165643 A B _95913 t R x)). Qed.
Lemma lem7165645 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7165646 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (term1029 A B _95913 t R) = (term1038 A B _95913 t R).
Proof. exact (MK_COMB (@lem7165645 A) (@lem7165644 A B _95913 t R)). Qed.
Lemma lem7165647 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) : (term1030 A B _95913 t) = (term1039 A B _95913 t).
Proof. exact (fun_ext (fun R : type1413 A B => @lem7165646 A B _95913 t R)). Qed.
Lemma lem7165648 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem7165649 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) : (term1031 A B _95913 t) = (term1040 A B _95913 t).
Proof. exact (MK_COMB (@lem7165648 A B) (@lem7165647 A B _95913 t)). Qed.
Lemma lem7165650 {A B : Type'} (_95913 : type830 A B) : (term1032 A B _95913) = (term1041 A B _95913).
Proof. exact (fun_ext (fun t : B -> Prop => @lem7165649 A B _95913 t)). Qed.
Lemma lem7165651 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem7165652 {A B : Type'} (_95913 : type830 A B) : (term1033 A B _95913) = (term1042 A B _95913).
Proof. exact (MK_COMB (@lem7165651 B) (@lem7165650 A B _95913)). Qed.
Lemma lem7165653 {A B : Type'} (_95913 : type830 A B) : (term975 A B _95913) = (term1042 A B _95913).
Proof. exact (TRANS (@lem7165617 A B _95913) (@lem7165652 A B _95913)). Qed.
Lemma lem7165654 {A B : Type'} (_95913 : type830 A B) (h1 : term728 A B _95913) : term1042 A B _95913.
Proof. exact (EQ_MP (@lem7165653 A B _95913) (@lem7164973 A B _95913 h1)). Qed.
Lemma lem7165660 {A : Type'} (P : Prop) (Q : A -> Prop) : (term292 A P Q) = (term291 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem7165661 {B : Type'} (P : Prop) (Q : B -> Prop) : (term292 B P Q) = (term291 B P Q).
Proof. exact (@lem7165660 B P Q). Qed.
Lemma lem7165662 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term1043 A B t R x y) = (term1044 A B t R x y).
Proof. exact (@lem7165661 B (term965 A B t R x y) (term992 A B t R x y)). Qed.
Lemma lem7165663 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y : B) : (term1045 A B t R x y y') = (term991 A B t R x y' y).
Proof. exact (eq_refl (term1045 A B t R x y y')). Qed.
Lemma lem7165664 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term1046 A B t R x y) = (term992 A B t R x y).
Proof. exact (fun_ext (fun y' : B => @lem7165663 A B t R x y' y)). Qed.
Lemma lem7165665 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7165666 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term1047 A B t R x y) = (term993 A B t R x y).
Proof. exact (MK_COMB (@lem7165665 B) (@lem7165664 A B t R x y)). Qed.
Lemma lem7165667 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term990 A B t R x y) = (term990 A B t R x y).
Proof. exact (eq_refl (term990 A B t R x y)). Qed.
Lemma lem7165668 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term1043 A B t R x y) = (term994 A B t R x y).
Proof. exact (MK_COMB (@lem7165667 A B t R x y) (@lem7165666 A B t R x y)). Qed.
Lemma lem7165669 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7165670 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term1048 A B t R x y) = (term1049 A B t R x y).
Proof. exact (MK_COMB (@lem7165669) (@lem7165668 A B t R x y)). Qed.
Lemma lem7165671 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y : B) : (term1045 A B t R x y y') = (term991 A B t R x y' y).
Proof. exact (eq_refl (term1045 A B t R x y y')). Qed.
Lemma lem7165672 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term990 A B t R x y) = (term990 A B t R x y).
Proof. exact (eq_refl (term990 A B t R x y)). Qed.
Lemma lem7165673 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y : B) : (term1050 A B t R x y y') = (term1051 A B t R x y' y).
Proof. exact (MK_COMB (@lem7165672 A B t R x y) (@lem7165671 A B t R x y' y)). Qed.
Lemma lem7165674 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term1052 A B t R x y) = (term1053 A B t R x y).
Proof. exact (fun_ext (fun y' : B => @lem7165673 A B t R x y' y)). Qed.
Lemma lem7165675 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7165676 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term1044 A B t R x y) = (term1054 A B t R x y).
Proof. exact (MK_COMB (@lem7165675 B) (@lem7165674 A B t R x y)). Qed.
Lemma lem7165677 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : ((term1043 A B t R x y) = (term1044 A B t R x y)) = ((term994 A B t R x y) = (term1054 A B t R x y)).
Proof. exact (MK_COMB (@lem7165670 A B t R x y) (@lem7165676 A B t R x y)). Qed.
Lemma lem7165678 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term994 A B t R x y) = (term1054 A B t R x y).
Proof. exact (EQ_MP (@lem7165677 A B t R x y) (@lem7165662 A B t R x y)). Qed.
Lemma lem7165679 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term995 A B t R x) = (term1055 A B t R x).
Proof. exact (fun_ext (fun y : B => @lem7165678 A B t R x y)). Qed.
Lemma lem7165680 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7165681 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term996 A B t R x) = (term1056 A B t R x).
Proof. exact (MK_COMB (@lem7165680 B) (@lem7165679 A B t R x)). Qed.
Lemma lem7165682 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (y : A -> B) (x : A) : (term1005 A B t R y x) = (term1005 A B t R y x).
Proof. exact (eq_refl (term1005 A B t R y x)). Qed.
Lemma lem7165683 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1007 A B y t R x) = (term1057 A B y t R x).
Proof. exact (MK_COMB (@lem7165682 A B t R y x) (@lem7165681 A B t R x)). Qed.
Lemma lem7165685 {A : Type'} (P : Prop) (Q : A -> Prop) : (term469 A P Q) = (term470 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem7165686 {B : Type'} (P : Prop) (Q : B -> Prop) : (term469 B P Q) = (term470 B P Q).
Proof. exact (@lem7165685 B P Q). Qed.
Lemma lem7165687 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1058 A B y t R x) = (term1059 A B y t R x).
Proof. exact (@lem7165686 B (term1003 A B t R y x) (term1055 A B t R x)). Qed.
Lemma lem7165688 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term1060 A B t R x y) = (term1054 A B t R x y).
Proof. exact (eq_refl (term1060 A B t R x y)). Qed.
Lemma lem7165689 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term1061 A B t R x) = (term1055 A B t R x).
Proof. exact (fun_ext (fun y : B => @lem7165688 A B t R x y)). Qed.
Lemma lem7165690 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7165691 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term1062 A B t R x) = (term1056 A B t R x).
Proof. exact (MK_COMB (@lem7165690 B) (@lem7165689 A B t R x)). Qed.
Lemma lem7165692 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (y : A -> B) (x : A) : (term1005 A B t R y x) = (term1005 A B t R y x).
Proof. exact (eq_refl (term1005 A B t R y x)). Qed.
Lemma lem7165693 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1058 A B y t R x) = (term1057 A B y t R x).
Proof. exact (MK_COMB (@lem7165692 A B t R y x) (@lem7165691 A B t R x)). Qed.
Lemma lem7165694 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7165695 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1063 A B y t R x) = (term1064 A B y t R x).
Proof. exact (MK_COMB (@lem7165694) (@lem7165693 A B y t R x)). Qed.
Lemma lem7165696 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term1060 A B t R x y) = (term1054 A B t R x y).
Proof. exact (eq_refl (term1060 A B t R x y)). Qed.
Lemma lem7165697 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (y : A -> B) (x : A) : (term1005 A B t R y x) = (term1005 A B t R y x).
Proof. exact (eq_refl (term1005 A B t R y x)). Qed.
Lemma lem7165698 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1065 A B y t R x y') = (term1066 A B y t R x y').
Proof. exact (MK_COMB (@lem7165697 A B t R y x) (@lem7165696 A B t R x y')). Qed.
Lemma lem7165699 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1067 A B y t R x) = (term1068 A B y t R x).
Proof. exact (fun_ext (fun y' : B => @lem7165698 A B y t R x y')). Qed.
Lemma lem7165700 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7165701 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1059 A B y t R x) = (term1069 A B y t R x).
Proof. exact (MK_COMB (@lem7165700 B) (@lem7165699 A B y t R x)). Qed.
Lemma lem7165702 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : ((term1058 A B y t R x) = (term1059 A B y t R x)) = ((term1057 A B y t R x) = (term1069 A B y t R x)).
Proof. exact (MK_COMB (@lem7165695 A B y t R x) (@lem7165701 A B y t R x)). Qed.
Lemma lem7165703 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1057 A B y t R x) = (term1069 A B y t R x).
Proof. exact (EQ_MP (@lem7165702 A B y t R x) (@lem7165687 A B y t R x)). Qed.
Lemma lem7165705 {A : Type'} (P : Prop) (Q : A -> Prop) : (term469 A P Q) = (term470 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem7165706 {B : Type'} (P : Prop) (Q : B -> Prop) : (term469 B P Q) = (term470 B P Q).
Proof. exact (@lem7165705 B P Q). Qed.
Lemma lem7165707 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1070 A B y t R x y') = (term1071 A B y t R x y').
Proof. exact (@lem7165706 B (term1003 A B t R y x) (term1053 A B t R x y')). Qed.
Lemma lem7165708 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y : B) : (term1072 A B t R x y y') = (term1051 A B t R x y' y).
Proof. exact (eq_refl (term1072 A B t R x y y')). Qed.
Lemma lem7165709 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term1073 A B t R x y) = (term1053 A B t R x y).
Proof. exact (fun_ext (fun y' : B => @lem7165708 A B t R x y' y)). Qed.
Lemma lem7165710 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7165711 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term1074 A B t R x y) = (term1054 A B t R x y).
Proof. exact (MK_COMB (@lem7165710 B) (@lem7165709 A B t R x y)). Qed.
Lemma lem7165712 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (y : A -> B) (x : A) : (term1005 A B t R y x) = (term1005 A B t R y x).
Proof. exact (eq_refl (term1005 A B t R y x)). Qed.
Lemma lem7165713 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1070 A B y t R x y') = (term1066 A B y t R x y').
Proof. exact (MK_COMB (@lem7165712 A B t R y x) (@lem7165711 A B t R x y')). Qed.
Lemma lem7165714 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7165715 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1075 A B y t R x y') = (term1076 A B y t R x y').
Proof. exact (MK_COMB (@lem7165714) (@lem7165713 A B y t R x y')). Qed.
Lemma lem7165716 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y : B) : (term1072 A B t R x y y') = (term1051 A B t R x y' y).
Proof. exact (eq_refl (term1072 A B t R x y y')). Qed.
Lemma lem7165717 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (y : A -> B) (x : A) : (term1005 A B t R y x) = (term1005 A B t R y x).
Proof. exact (eq_refl (term1005 A B t R y x)). Qed.
Lemma lem7165718 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y'' : B) : (term1077 A B y t R x y'' y') = (term1078 A B y t R x y' y'').
Proof. exact (MK_COMB (@lem7165717 A B t R y x) (@lem7165716 A B t R x y' y'')). Qed.
Lemma lem7165719 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1079 A B y t R x y') = (term1080 A B y t R x y').
Proof. exact (fun_ext (fun y'' : B => @lem7165718 A B y t R x y'' y')). Qed.
Lemma lem7165720 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7165721 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1071 A B y t R x y') = (term1081 A B y t R x y').
Proof. exact (MK_COMB (@lem7165720 B) (@lem7165719 A B y t R x y')). Qed.
Lemma lem7165722 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : ((term1070 A B y t R x y') = (term1071 A B y t R x y')) = ((term1066 A B y t R x y') = (term1081 A B y t R x y')).
Proof. exact (MK_COMB (@lem7165715 A B y t R x y') (@lem7165721 A B y t R x y')). Qed.
Lemma lem7165723 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1066 A B y t R x y') = (term1081 A B y t R x y').
Proof. exact (EQ_MP (@lem7165722 A B y t R x y') (@lem7165707 A B y t R x y')). Qed.
Lemma lem7165724 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1068 A B y t R x) = (term1082 A B y t R x).
Proof. exact (fun_ext (fun y' : B => @lem7165723 A B y t R x y')). Qed.
Lemma lem7165725 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7165726 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1069 A B y t R x) = (term1083 A B y t R x).
Proof. exact (MK_COMB (@lem7165725 B) (@lem7165724 A B y t R x)). Qed.
Lemma lem7165727 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1057 A B y t R x) = (term1083 A B y t R x).
Proof. exact (TRANS (@lem7165703 A B y t R x) (@lem7165726 A B y t R x)). Qed.
Lemma lem7165728 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1007 A B y t R x) = (term1083 A B y t R x).
Proof. exact (TRANS (@lem7165683 A B y t R x) (@lem7165727 A B y t R x)). Qed.
Lemma lem7165729 {A : Type'} (s : A -> Prop) (x : A) : (term964 A s x) = (term964 A s x).
Proof. exact (eq_refl (term964 A s x)). Qed.
Lemma lem7165730 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1008 A B s y t R x) = (term1084 A B s y t R x).
Proof. exact (MK_COMB (@lem7165729 A s x) (@lem7165728 A B y t R x)). Qed.
Lemma lem7165732 {A : Type'} (P : Prop) (Q : A -> Prop) : (term292 A P Q) = (term291 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem7165733 {B : Type'} (P : Prop) (Q : B -> Prop) : (term292 B P Q) = (term291 B P Q).
Proof. exact (@lem7165732 B P Q). Qed.
Lemma lem7165734 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1085 A B s y t R x) = (term1086 A B s y t R x).
Proof. exact (@lem7165733 B (term963 A s x) (term1082 A B y t R x)). Qed.
Lemma lem7165735 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1087 A B y t R x y') = (term1081 A B y t R x y').
Proof. exact (eq_refl (term1087 A B y t R x y')). Qed.
Lemma lem7165736 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1088 A B y t R x) = (term1082 A B y t R x).
Proof. exact (fun_ext (fun y' : B => @lem7165735 A B y t R x y')). Qed.
Lemma lem7165737 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7165738 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1089 A B y t R x) = (term1083 A B y t R x).
Proof. exact (MK_COMB (@lem7165737 B) (@lem7165736 A B y t R x)). Qed.
Lemma lem7165739 {A : Type'} (s : A -> Prop) (x : A) : (term964 A s x) = (term964 A s x).
Proof. exact (eq_refl (term964 A s x)). Qed.
Lemma lem7165740 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1085 A B s y t R x) = (term1084 A B s y t R x).
Proof. exact (MK_COMB (@lem7165739 A s x) (@lem7165738 A B y t R x)). Qed.
Lemma lem7165741 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7165742 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1090 A B s y t R x) = (term1091 A B s y t R x).
Proof. exact (MK_COMB (@lem7165741) (@lem7165740 A B s y t R x)). Qed.
Lemma lem7165743 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1087 A B y t R x y') = (term1081 A B y t R x y').
Proof. exact (eq_refl (term1087 A B y t R x y')). Qed.
Lemma lem7165744 {A : Type'} (s : A -> Prop) (x : A) : (term964 A s x) = (term964 A s x).
Proof. exact (eq_refl (term964 A s x)). Qed.
Lemma lem7165745 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1092 A B s y t R x y') = (term1093 A B s y t R x y').
Proof. exact (MK_COMB (@lem7165744 A s x) (@lem7165743 A B y t R x y')). Qed.
Lemma lem7165746 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1094 A B s y t R x) = (term1095 A B s y t R x).
Proof. exact (fun_ext (fun y' : B => @lem7165745 A B s y t R x y')). Qed.
Lemma lem7165747 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7165748 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1086 A B s y t R x) = (term1096 A B s y t R x).
Proof. exact (MK_COMB (@lem7165747 B) (@lem7165746 A B s y t R x)). Qed.
Lemma lem7165749 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : ((term1085 A B s y t R x) = (term1086 A B s y t R x)) = ((term1084 A B s y t R x) = (term1096 A B s y t R x)).
Proof. exact (MK_COMB (@lem7165742 A B s y t R x) (@lem7165748 A B s y t R x)). Qed.
Lemma lem7165750 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1084 A B s y t R x) = (term1096 A B s y t R x).
Proof. exact (EQ_MP (@lem7165749 A B s y t R x) (@lem7165734 A B s y t R x)). Qed.
Lemma lem7165752 {A : Type'} (P : Prop) (Q : A -> Prop) : (term292 A P Q) = (term291 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem7165753 {B : Type'} (P : Prop) (Q : B -> Prop) : (term292 B P Q) = (term291 B P Q).
Proof. exact (@lem7165752 B P Q). Qed.
Lemma lem7165754 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1097 A B s y t R x y') = (term1098 A B s y t R x y').
Proof. exact (@lem7165753 B (term963 A s x) (term1080 A B y t R x y')). Qed.
Lemma lem7165755 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y'' : B) : (term1099 A B y t R x y'' y') = (term1078 A B y t R x y' y'').
Proof. exact (eq_refl (term1099 A B y t R x y'' y')). Qed.
Lemma lem7165756 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1100 A B y t R x y') = (term1080 A B y t R x y').
Proof. exact (fun_ext (fun y'' : B => @lem7165755 A B y t R x y'' y')). Qed.
Lemma lem7165757 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7165758 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1101 A B y t R x y') = (term1081 A B y t R x y').
Proof. exact (MK_COMB (@lem7165757 B) (@lem7165756 A B y t R x y')). Qed.
Lemma lem7165759 {A : Type'} (s : A -> Prop) (x : A) : (term964 A s x) = (term964 A s x).
Proof. exact (eq_refl (term964 A s x)). Qed.
Lemma lem7165760 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1097 A B s y t R x y') = (term1093 A B s y t R x y').
Proof. exact (MK_COMB (@lem7165759 A s x) (@lem7165758 A B y t R x y')). Qed.
Lemma lem7165761 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7165762 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1102 A B s y t R x y') = (term1103 A B s y t R x y').
Proof. exact (MK_COMB (@lem7165761) (@lem7165760 A B s y t R x y')). Qed.
Lemma lem7165763 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y'' : B) : (term1099 A B y t R x y'' y') = (term1078 A B y t R x y' y'').
Proof. exact (eq_refl (term1099 A B y t R x y'' y')). Qed.
Lemma lem7165764 {A : Type'} (s : A -> Prop) (x : A) : (term964 A s x) = (term964 A s x).
Proof. exact (eq_refl (term964 A s x)). Qed.
Lemma lem7165765 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y'' : B) : (term1104 A B s y t R x y'' y') = (term1105 A B s y t R x y' y'').
Proof. exact (MK_COMB (@lem7165764 A s x) (@lem7165763 A B y t R x y' y'')). Qed.
Lemma lem7165766 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1106 A B s y t R x y') = (term1107 A B s y t R x y').
Proof. exact (fun_ext (fun y'' : B => @lem7165765 A B s y t R x y'' y')). Qed.
Lemma lem7165767 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7165768 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1098 A B s y t R x y') = (term1108 A B s y t R x y').
Proof. exact (MK_COMB (@lem7165767 B) (@lem7165766 A B s y t R x y')). Qed.
Lemma lem7165769 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : ((term1097 A B s y t R x y') = (term1098 A B s y t R x y')) = ((term1093 A B s y t R x y') = (term1108 A B s y t R x y')).
Proof. exact (MK_COMB (@lem7165762 A B s y t R x y') (@lem7165768 A B s y t R x y')). Qed.
Lemma lem7165770 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1093 A B s y t R x y') = (term1108 A B s y t R x y').
Proof. exact (EQ_MP (@lem7165769 A B s y t R x y') (@lem7165754 A B s y t R x y')). Qed.
Lemma lem7165771 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1095 A B s y t R x) = (term1109 A B s y t R x).
Proof. exact (fun_ext (fun y' : B => @lem7165770 A B s y t R x y')). Qed.
Lemma lem7165772 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7165773 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1096 A B s y t R x) = (term1110 A B s y t R x).
Proof. exact (MK_COMB (@lem7165772 B) (@lem7165771 A B s y t R x)). Qed.
Lemma lem7165774 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1084 A B s y t R x) = (term1110 A B s y t R x).
Proof. exact (TRANS (@lem7165750 A B s y t R x) (@lem7165773 A B s y t R x)). Qed.
Lemma lem7165775 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1008 A B s y t R x) = (term1110 A B s y t R x).
Proof. exact (TRANS (@lem7165730 A B s y t R x) (@lem7165774 A B s y t R x)). Qed.
Lemma lem7165776 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) : (term1009 A B s y t R) = (term1111 A B s y t R).
Proof. exact (fun_ext (fun x : A => @lem7165775 A B s y t R x)). Qed.
Lemma lem7165777 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7165778 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) : (term1010 A B s y t R) = (term1112 A B s y t R).
Proof. exact (MK_COMB (@lem7165777 A) (@lem7165776 A B s y t R)). Qed.
Lemma lem7165816 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y'' : B) : (term1105 A B s y t R x y' y'') = (term1113 A B y s t R x y' y'').
Proof. exact (@lem19490 (term1003 A B t R y x) (term963 A s x) (term1051 A B t R x y' y'')). Qed.
Lemma lem7165817 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y : B) : (term1114 A B s t R x y' y) = (term1114 A B s t R x y' y).
Proof. exact (eq_refl (term1114 A B s t R x y' y)). Qed.
Lemma lem7165824 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (y : A -> B) (x : A) : (term1115 A B s t R y x) = (term1116 A B t s R y x).
Proof. exact (@lem19490 (term999 A B t y x) (term963 A s x) (term406 A B R y x)). Qed.
Lemma lem7165825 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7165826 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (y : A -> B) (x : A) : (term1117 A B s t R y x) = (term1118 A B t s R y x).
Proof. exact (MK_COMB (@lem7165825) (@lem7165824 A B t s R y x)). Qed.
Lemma lem7165827 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y'' : B) : (term1113 A B y s t R x y' y'') = (term1119 A B y s t R x y' y'').
Proof. exact (MK_COMB (@lem7165826 A B t s R y x) (@lem7165817 A B s t R x y' y'')). Qed.
Lemma lem7165829 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y'' : B) : (term1105 A B s y t R x y' y'') = (term1119 A B y s t R x y' y'').
Proof. exact (TRANS (@lem7165816 A B y s t R x y' y'') (@lem7165827 A B y s t R x y' y'')). Qed.
Lemma lem7165830 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1107 A B s y t R x y') = (term1120 A B y s t R x y').
Proof. exact (fun_ext (fun y'' : B => @lem7165829 A B y s t R x y'' y')). Qed.
Lemma lem7165831 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7165832 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1108 A B s y t R x y') = (term1121 A B y s t R x y').
Proof. exact (MK_COMB (@lem7165831 B) (@lem7165830 A B y s t R x y')). Qed.
Lemma lem7165833 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1109 A B s y t R x) = (term1122 A B y s t R x).
Proof. exact (fun_ext (fun y' : B => @lem7165832 A B y s t R x y')). Qed.
Lemma lem7165834 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7165835 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1110 A B s y t R x) = (term1123 A B y s t R x).
Proof. exact (MK_COMB (@lem7165834 B) (@lem7165833 A B y s t R x)). Qed.
Lemma lem7165836 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term1111 A B s y t R) = (term1124 A B y s t R).
Proof. exact (fun_ext (fun x : A => @lem7165835 A B y s t R x)). Qed.
Lemma lem7165837 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7165838 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term1112 A B s y t R) = (term1125 A B y s t R).
Proof. exact (MK_COMB (@lem7165837 A) (@lem7165836 A B y s t R)). Qed.
Lemma lem7165839 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term1010 A B s y t R) = (term1125 A B y s t R).
Proof. exact (TRANS (@lem7165778 A B s y t R) (@lem7165838 A B y s t R)). Qed.
Lemma lem7165840 {A B : Type'} (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1125 A B y s t R.
Proof. exact (EQ_MP (@lem7165839 A B y s t R) (@lem7165298 A B x y t R s h1)). Qed.
Lemma lem7165856 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term983 A B _95913 t R x' x) : term983 A B _95913 t R x' x.
Proof. exact (h1). Qed.
Lemma lem7166128 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term963 A s x') : term963 A s x'.
Proof. exact (h1). Qed.
Lemma lem7166130 {A : Type'} (P : A -> Prop) (Q : Prop) : (term242 A P Q) = (term241 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem7166131 {B : Type'} (P : B -> Prop) (Q : Prop) : (term242 B P Q) = (term241 B P Q).
Proof. exact (@lem7166130 B P Q). Qed.
Lemma lem7166132 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1014 A B _95913 t R x) = (term1015 A B _95913 t R x).
Proof. exact (@lem7166131 B (term966 A B t R x) (term962 A B _95913 t R x)). Qed.
Lemma lem7166133 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term1016 A B t R x x') = (term965 A B t R x x').
Proof. exact (eq_refl (term1016 A B t R x x')). Qed.
Lemma lem7166134 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term1017 A B t R x) = (term966 A B t R x).
Proof. exact (fun_ext (fun x' : B => @lem7166133 A B t R x x')). Qed.
Lemma lem7166135 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7166136 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term1018 A B t R x) = (term967 A B t R x).
Proof. exact (MK_COMB (@lem7166135 B) (@lem7166134 A B t R x)). Qed.
Lemma lem7166137 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7166138 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term1019 A B t R x) = (term968 A B t R x).
Proof. exact (MK_COMB (@lem7166137) (@lem7166136 A B t R x)). Qed.
Lemma lem7166139 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term962 A B _95913 t R x) = (term962 A B _95913 t R x).
Proof. exact (eq_refl (term962 A B _95913 t R x)). Qed.
Lemma lem7166140 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1014 A B _95913 t R x) = (term969 A B _95913 t R x).
Proof. exact (MK_COMB (@lem7166138 A B t R x) (@lem7166139 A B _95913 t R x)). Qed.
Lemma lem7166141 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7166142 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1020 A B _95913 t R x) = (term1021 A B _95913 t R x).
Proof. exact (MK_COMB (@lem7166141) (@lem7166140 A B _95913 t R x)). Qed.
Lemma lem7166143 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term1016 A B t R x x') = (term965 A B t R x x').
Proof. exact (eq_refl (term1016 A B t R x x')). Qed.
Lemma lem7166144 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7166145 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term1022 A B t R x x') = (term990 A B t R x x').
Proof. exact (MK_COMB (@lem7166144) (@lem7166143 A B t R x x')). Qed.
Lemma lem7166146 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term962 A B _95913 t R x) = (term962 A B _95913 t R x).
Proof. exact (eq_refl (term962 A B _95913 t R x)). Qed.
Lemma lem7166147 {A B : Type'} (x : B) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) : (term1023 A B x _95913 t R x') = (term1024 A B x _95913 t R x').
Proof. exact (MK_COMB (@lem7166145 A B t R x' x) (@lem7166146 A B _95913 t R x')). Qed.
Lemma lem7166148 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1025 A B _95913 t R x) = (term1026 A B _95913 t R x).
Proof. exact (fun_ext (fun x' : B => @lem7166147 A B x' _95913 t R x)). Qed.
Lemma lem7166149 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7166150 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1015 A B _95913 t R x) = (term1027 A B _95913 t R x).
Proof. exact (MK_COMB (@lem7166149 B) (@lem7166148 A B _95913 t R x)). Qed.
Lemma lem7166151 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : ((term1014 A B _95913 t R x) = (term1015 A B _95913 t R x)) = ((term969 A B _95913 t R x) = (term1027 A B _95913 t R x)).
Proof. exact (MK_COMB (@lem7166142 A B _95913 t R x) (@lem7166150 A B _95913 t R x)). Qed.
Lemma lem7166152 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term969 A B _95913 t R x) = (term1027 A B _95913 t R x).
Proof. exact (EQ_MP (@lem7166151 A B _95913 t R x) (@lem7166132 A B _95913 t R x)). Qed.
Lemma lem7166153 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (term970 A B _95913 t R) = (term1028 A B _95913 t R).
Proof. exact (fun_ext (fun x : A => @lem7166152 A B _95913 t R x)). Qed.
Lemma lem7166154 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7166155 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (term971 A B _95913 t R) = (term1029 A B _95913 t R).
Proof. exact (MK_COMB (@lem7166154 A) (@lem7166153 A B _95913 t R)). Qed.
Lemma lem7166156 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) : (term972 A B _95913 t) = (term1030 A B _95913 t).
Proof. exact (fun_ext (fun R : type1413 A B => @lem7166155 A B _95913 t R)). Qed.
Lemma lem7166157 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem7166158 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) : (term973 A B _95913 t) = (term1031 A B _95913 t).
Proof. exact (MK_COMB (@lem7166157 A B) (@lem7166156 A B _95913 t)). Qed.
Lemma lem7166159 {A B : Type'} (_95913 : type830 A B) : (term974 A B _95913) = (term1032 A B _95913).
Proof. exact (fun_ext (fun t : B -> Prop => @lem7166158 A B _95913 t)). Qed.
Lemma lem7166160 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem7166161 {A B : Type'} (_95913 : type830 A B) : (term975 A B _95913) = (term1033 A B _95913).
Proof. exact (MK_COMB (@lem7166160 B) (@lem7166159 A B _95913)). Qed.
Lemma lem7166184 {A B : Type'} (x : B) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) : (term1024 A B x _95913 t R x') = (term1034 A B x _95913 t R x').
Proof. exact (@lem19490 (term960 A B _95913 t R x') (term965 A B t R x' x) (term370 A B _95913 t R x')). Qed.
Lemma lem7166185 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1026 A B _95913 t R x) = (term1035 A B _95913 t R x).
Proof. exact (fun_ext (fun x' : B => @lem7166184 A B x' _95913 t R x)). Qed.
Lemma lem7166186 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7166187 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1027 A B _95913 t R x) = (term1036 A B _95913 t R x).
Proof. exact (MK_COMB (@lem7166186 B) (@lem7166185 A B _95913 t R x)). Qed.
Lemma lem7166188 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (term1028 A B _95913 t R) = (term1037 A B _95913 t R).
Proof. exact (fun_ext (fun x : A => @lem7166187 A B _95913 t R x)). Qed.
Lemma lem7166189 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7166190 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (term1029 A B _95913 t R) = (term1038 A B _95913 t R).
Proof. exact (MK_COMB (@lem7166189 A) (@lem7166188 A B _95913 t R)). Qed.
Lemma lem7166191 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) : (term1030 A B _95913 t) = (term1039 A B _95913 t).
Proof. exact (fun_ext (fun R : type1413 A B => @lem7166190 A B _95913 t R)). Qed.
Lemma lem7166192 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem7166193 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) : (term1031 A B _95913 t) = (term1040 A B _95913 t).
Proof. exact (MK_COMB (@lem7166192 A B) (@lem7166191 A B _95913 t)). Qed.
Lemma lem7166194 {A B : Type'} (_95913 : type830 A B) : (term1032 A B _95913) = (term1041 A B _95913).
Proof. exact (fun_ext (fun t : B -> Prop => @lem7166193 A B _95913 t)). Qed.
Lemma lem7166195 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem7166196 {A B : Type'} (_95913 : type830 A B) : (term1033 A B _95913) = (term1042 A B _95913).
Proof. exact (MK_COMB (@lem7166195 B) (@lem7166194 A B _95913)). Qed.
Lemma lem7166197 {A B : Type'} (_95913 : type830 A B) : (term975 A B _95913) = (term1042 A B _95913).
Proof. exact (TRANS (@lem7166161 A B _95913) (@lem7166196 A B _95913)). Qed.
Lemma lem7166198 {A B : Type'} (_95913 : type830 A B) (h1 : term728 A B _95913) : term1042 A B _95913.
Proof. exact (EQ_MP (@lem7166197 A B _95913) (@lem7164973 A B _95913 h1)). Qed.
Lemma lem7166204 {A : Type'} (P : Prop) (Q : A -> Prop) : (term292 A P Q) = (term291 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem7166205 {B : Type'} (P : Prop) (Q : B -> Prop) : (term292 B P Q) = (term291 B P Q).
Proof. exact (@lem7166204 B P Q). Qed.
Lemma lem7166206 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term1043 A B t R x y) = (term1044 A B t R x y).
Proof. exact (@lem7166205 B (term965 A B t R x y) (term992 A B t R x y)). Qed.
Lemma lem7166207 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y : B) : (term1045 A B t R x y y') = (term991 A B t R x y' y).
Proof. exact (eq_refl (term1045 A B t R x y y')). Qed.
Lemma lem7166208 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term1046 A B t R x y) = (term992 A B t R x y).
Proof. exact (fun_ext (fun y' : B => @lem7166207 A B t R x y' y)). Qed.
Lemma lem7166209 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7166210 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term1047 A B t R x y) = (term993 A B t R x y).
Proof. exact (MK_COMB (@lem7166209 B) (@lem7166208 A B t R x y)). Qed.
Lemma lem7166211 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term990 A B t R x y) = (term990 A B t R x y).
Proof. exact (eq_refl (term990 A B t R x y)). Qed.
Lemma lem7166212 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term1043 A B t R x y) = (term994 A B t R x y).
Proof. exact (MK_COMB (@lem7166211 A B t R x y) (@lem7166210 A B t R x y)). Qed.
Lemma lem7166213 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7166214 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term1048 A B t R x y) = (term1049 A B t R x y).
Proof. exact (MK_COMB (@lem7166213) (@lem7166212 A B t R x y)). Qed.
Lemma lem7166215 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y : B) : (term1045 A B t R x y y') = (term991 A B t R x y' y).
Proof. exact (eq_refl (term1045 A B t R x y y')). Qed.
Lemma lem7166216 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term990 A B t R x y) = (term990 A B t R x y).
Proof. exact (eq_refl (term990 A B t R x y)). Qed.
Lemma lem7166217 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y : B) : (term1050 A B t R x y y') = (term1051 A B t R x y' y).
Proof. exact (MK_COMB (@lem7166216 A B t R x y) (@lem7166215 A B t R x y' y)). Qed.
Lemma lem7166218 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term1052 A B t R x y) = (term1053 A B t R x y).
Proof. exact (fun_ext (fun y' : B => @lem7166217 A B t R x y' y)). Qed.
Lemma lem7166219 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7166220 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term1044 A B t R x y) = (term1054 A B t R x y).
Proof. exact (MK_COMB (@lem7166219 B) (@lem7166218 A B t R x y)). Qed.
Lemma lem7166221 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : ((term1043 A B t R x y) = (term1044 A B t R x y)) = ((term994 A B t R x y) = (term1054 A B t R x y)).
Proof. exact (MK_COMB (@lem7166214 A B t R x y) (@lem7166220 A B t R x y)). Qed.
Lemma lem7166222 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term994 A B t R x y) = (term1054 A B t R x y).
Proof. exact (EQ_MP (@lem7166221 A B t R x y) (@lem7166206 A B t R x y)). Qed.
Lemma lem7166223 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term995 A B t R x) = (term1055 A B t R x).
Proof. exact (fun_ext (fun y : B => @lem7166222 A B t R x y)). Qed.
Lemma lem7166224 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7166225 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term996 A B t R x) = (term1056 A B t R x).
Proof. exact (MK_COMB (@lem7166224 B) (@lem7166223 A B t R x)). Qed.
Lemma lem7166226 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (y : A -> B) (x : A) : (term1005 A B t R y x) = (term1005 A B t R y x).
Proof. exact (eq_refl (term1005 A B t R y x)). Qed.
Lemma lem7166227 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1007 A B y t R x) = (term1057 A B y t R x).
Proof. exact (MK_COMB (@lem7166226 A B t R y x) (@lem7166225 A B t R x)). Qed.
Lemma lem7166229 {A : Type'} (P : Prop) (Q : A -> Prop) : (term469 A P Q) = (term470 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem7166230 {B : Type'} (P : Prop) (Q : B -> Prop) : (term469 B P Q) = (term470 B P Q).
Proof. exact (@lem7166229 B P Q). Qed.
Lemma lem7166231 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1058 A B y t R x) = (term1059 A B y t R x).
Proof. exact (@lem7166230 B (term1003 A B t R y x) (term1055 A B t R x)). Qed.
Lemma lem7166232 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term1060 A B t R x y) = (term1054 A B t R x y).
Proof. exact (eq_refl (term1060 A B t R x y)). Qed.
Lemma lem7166233 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term1061 A B t R x) = (term1055 A B t R x).
Proof. exact (fun_ext (fun y : B => @lem7166232 A B t R x y)). Qed.
Lemma lem7166234 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7166235 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term1062 A B t R x) = (term1056 A B t R x).
Proof. exact (MK_COMB (@lem7166234 B) (@lem7166233 A B t R x)). Qed.
Lemma lem7166236 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (y : A -> B) (x : A) : (term1005 A B t R y x) = (term1005 A B t R y x).
Proof. exact (eq_refl (term1005 A B t R y x)). Qed.
Lemma lem7166237 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1058 A B y t R x) = (term1057 A B y t R x).
Proof. exact (MK_COMB (@lem7166236 A B t R y x) (@lem7166235 A B t R x)). Qed.
Lemma lem7166238 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7166239 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1063 A B y t R x) = (term1064 A B y t R x).
Proof. exact (MK_COMB (@lem7166238) (@lem7166237 A B y t R x)). Qed.
Lemma lem7166240 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term1060 A B t R x y) = (term1054 A B t R x y).
Proof. exact (eq_refl (term1060 A B t R x y)). Qed.
Lemma lem7166241 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (y : A -> B) (x : A) : (term1005 A B t R y x) = (term1005 A B t R y x).
Proof. exact (eq_refl (term1005 A B t R y x)). Qed.
Lemma lem7166242 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1065 A B y t R x y') = (term1066 A B y t R x y').
Proof. exact (MK_COMB (@lem7166241 A B t R y x) (@lem7166240 A B t R x y')). Qed.
Lemma lem7166243 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1067 A B y t R x) = (term1068 A B y t R x).
Proof. exact (fun_ext (fun y' : B => @lem7166242 A B y t R x y')). Qed.
Lemma lem7166244 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7166245 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1059 A B y t R x) = (term1069 A B y t R x).
Proof. exact (MK_COMB (@lem7166244 B) (@lem7166243 A B y t R x)). Qed.
Lemma lem7166246 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : ((term1058 A B y t R x) = (term1059 A B y t R x)) = ((term1057 A B y t R x) = (term1069 A B y t R x)).
Proof. exact (MK_COMB (@lem7166239 A B y t R x) (@lem7166245 A B y t R x)). Qed.
Lemma lem7166247 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1057 A B y t R x) = (term1069 A B y t R x).
Proof. exact (EQ_MP (@lem7166246 A B y t R x) (@lem7166231 A B y t R x)). Qed.
Lemma lem7166249 {A : Type'} (P : Prop) (Q : A -> Prop) : (term469 A P Q) = (term470 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem7166250 {B : Type'} (P : Prop) (Q : B -> Prop) : (term469 B P Q) = (term470 B P Q).
Proof. exact (@lem7166249 B P Q). Qed.
Lemma lem7166251 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1070 A B y t R x y') = (term1071 A B y t R x y').
Proof. exact (@lem7166250 B (term1003 A B t R y x) (term1053 A B t R x y')). Qed.
Lemma lem7166252 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y : B) : (term1072 A B t R x y y') = (term1051 A B t R x y' y).
Proof. exact (eq_refl (term1072 A B t R x y y')). Qed.
Lemma lem7166253 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term1073 A B t R x y) = (term1053 A B t R x y).
Proof. exact (fun_ext (fun y' : B => @lem7166252 A B t R x y' y)). Qed.
Lemma lem7166254 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7166255 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term1074 A B t R x y) = (term1054 A B t R x y).
Proof. exact (MK_COMB (@lem7166254 B) (@lem7166253 A B t R x y)). Qed.
Lemma lem7166256 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (y : A -> B) (x : A) : (term1005 A B t R y x) = (term1005 A B t R y x).
Proof. exact (eq_refl (term1005 A B t R y x)). Qed.
Lemma lem7166257 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1070 A B y t R x y') = (term1066 A B y t R x y').
Proof. exact (MK_COMB (@lem7166256 A B t R y x) (@lem7166255 A B t R x y')). Qed.
Lemma lem7166258 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7166259 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1075 A B y t R x y') = (term1076 A B y t R x y').
Proof. exact (MK_COMB (@lem7166258) (@lem7166257 A B y t R x y')). Qed.
Lemma lem7166260 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y : B) : (term1072 A B t R x y y') = (term1051 A B t R x y' y).
Proof. exact (eq_refl (term1072 A B t R x y y')). Qed.
Lemma lem7166261 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (y : A -> B) (x : A) : (term1005 A B t R y x) = (term1005 A B t R y x).
Proof. exact (eq_refl (term1005 A B t R y x)). Qed.
Lemma lem7166262 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y'' : B) : (term1077 A B y t R x y'' y') = (term1078 A B y t R x y' y'').
Proof. exact (MK_COMB (@lem7166261 A B t R y x) (@lem7166260 A B t R x y' y'')). Qed.
Lemma lem7166263 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1079 A B y t R x y') = (term1080 A B y t R x y').
Proof. exact (fun_ext (fun y'' : B => @lem7166262 A B y t R x y'' y')). Qed.
Lemma lem7166264 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7166265 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1071 A B y t R x y') = (term1081 A B y t R x y').
Proof. exact (MK_COMB (@lem7166264 B) (@lem7166263 A B y t R x y')). Qed.
Lemma lem7166266 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : ((term1070 A B y t R x y') = (term1071 A B y t R x y')) = ((term1066 A B y t R x y') = (term1081 A B y t R x y')).
Proof. exact (MK_COMB (@lem7166259 A B y t R x y') (@lem7166265 A B y t R x y')). Qed.
Lemma lem7166267 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1066 A B y t R x y') = (term1081 A B y t R x y').
Proof. exact (EQ_MP (@lem7166266 A B y t R x y') (@lem7166251 A B y t R x y')). Qed.
Lemma lem7166268 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1068 A B y t R x) = (term1082 A B y t R x).
Proof. exact (fun_ext (fun y' : B => @lem7166267 A B y t R x y')). Qed.
Lemma lem7166269 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7166270 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1069 A B y t R x) = (term1083 A B y t R x).
Proof. exact (MK_COMB (@lem7166269 B) (@lem7166268 A B y t R x)). Qed.
Lemma lem7166271 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1057 A B y t R x) = (term1083 A B y t R x).
Proof. exact (TRANS (@lem7166247 A B y t R x) (@lem7166270 A B y t R x)). Qed.
Lemma lem7166272 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1007 A B y t R x) = (term1083 A B y t R x).
Proof. exact (TRANS (@lem7166227 A B y t R x) (@lem7166271 A B y t R x)). Qed.
Lemma lem7166273 {A : Type'} (s : A -> Prop) (x : A) : (term964 A s x) = (term964 A s x).
Proof. exact (eq_refl (term964 A s x)). Qed.
Lemma lem7166274 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1008 A B s y t R x) = (term1084 A B s y t R x).
Proof. exact (MK_COMB (@lem7166273 A s x) (@lem7166272 A B y t R x)). Qed.
Lemma lem7166276 {A : Type'} (P : Prop) (Q : A -> Prop) : (term292 A P Q) = (term291 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem7166277 {B : Type'} (P : Prop) (Q : B -> Prop) : (term292 B P Q) = (term291 B P Q).
Proof. exact (@lem7166276 B P Q). Qed.
Lemma lem7166278 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1085 A B s y t R x) = (term1086 A B s y t R x).
Proof. exact (@lem7166277 B (term963 A s x) (term1082 A B y t R x)). Qed.
Lemma lem7166279 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1087 A B y t R x y') = (term1081 A B y t R x y').
Proof. exact (eq_refl (term1087 A B y t R x y')). Qed.
Lemma lem7166280 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1088 A B y t R x) = (term1082 A B y t R x).
Proof. exact (fun_ext (fun y' : B => @lem7166279 A B y t R x y')). Qed.
Lemma lem7166281 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7166282 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1089 A B y t R x) = (term1083 A B y t R x).
Proof. exact (MK_COMB (@lem7166281 B) (@lem7166280 A B y t R x)). Qed.
Lemma lem7166283 {A : Type'} (s : A -> Prop) (x : A) : (term964 A s x) = (term964 A s x).
Proof. exact (eq_refl (term964 A s x)). Qed.
Lemma lem7166284 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1085 A B s y t R x) = (term1084 A B s y t R x).
Proof. exact (MK_COMB (@lem7166283 A s x) (@lem7166282 A B y t R x)). Qed.
Lemma lem7166285 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7166286 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1090 A B s y t R x) = (term1091 A B s y t R x).
Proof. exact (MK_COMB (@lem7166285) (@lem7166284 A B s y t R x)). Qed.
Lemma lem7166287 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1087 A B y t R x y') = (term1081 A B y t R x y').
Proof. exact (eq_refl (term1087 A B y t R x y')). Qed.
Lemma lem7166288 {A : Type'} (s : A -> Prop) (x : A) : (term964 A s x) = (term964 A s x).
Proof. exact (eq_refl (term964 A s x)). Qed.
Lemma lem7166289 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1092 A B s y t R x y') = (term1093 A B s y t R x y').
Proof. exact (MK_COMB (@lem7166288 A s x) (@lem7166287 A B y t R x y')). Qed.
Lemma lem7166290 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1094 A B s y t R x) = (term1095 A B s y t R x).
Proof. exact (fun_ext (fun y' : B => @lem7166289 A B s y t R x y')). Qed.
Lemma lem7166291 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7166292 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1086 A B s y t R x) = (term1096 A B s y t R x).
Proof. exact (MK_COMB (@lem7166291 B) (@lem7166290 A B s y t R x)). Qed.
Lemma lem7166293 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : ((term1085 A B s y t R x) = (term1086 A B s y t R x)) = ((term1084 A B s y t R x) = (term1096 A B s y t R x)).
Proof. exact (MK_COMB (@lem7166286 A B s y t R x) (@lem7166292 A B s y t R x)). Qed.
Lemma lem7166294 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1084 A B s y t R x) = (term1096 A B s y t R x).
Proof. exact (EQ_MP (@lem7166293 A B s y t R x) (@lem7166278 A B s y t R x)). Qed.
Lemma lem7166296 {A : Type'} (P : Prop) (Q : A -> Prop) : (term292 A P Q) = (term291 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem7166297 {B : Type'} (P : Prop) (Q : B -> Prop) : (term292 B P Q) = (term291 B P Q).
Proof. exact (@lem7166296 B P Q). Qed.
Lemma lem7166298 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1097 A B s y t R x y') = (term1098 A B s y t R x y').
Proof. exact (@lem7166297 B (term963 A s x) (term1080 A B y t R x y')). Qed.
Lemma lem7166299 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y'' : B) : (term1099 A B y t R x y'' y') = (term1078 A B y t R x y' y'').
Proof. exact (eq_refl (term1099 A B y t R x y'' y')). Qed.
Lemma lem7166300 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1100 A B y t R x y') = (term1080 A B y t R x y').
Proof. exact (fun_ext (fun y'' : B => @lem7166299 A B y t R x y'' y')). Qed.
Lemma lem7166301 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7166302 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1101 A B y t R x y') = (term1081 A B y t R x y').
Proof. exact (MK_COMB (@lem7166301 B) (@lem7166300 A B y t R x y')). Qed.
Lemma lem7166303 {A : Type'} (s : A -> Prop) (x : A) : (term964 A s x) = (term964 A s x).
Proof. exact (eq_refl (term964 A s x)). Qed.
Lemma lem7166304 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1097 A B s y t R x y') = (term1093 A B s y t R x y').
Proof. exact (MK_COMB (@lem7166303 A s x) (@lem7166302 A B y t R x y')). Qed.
Lemma lem7166305 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7166306 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1102 A B s y t R x y') = (term1103 A B s y t R x y').
Proof. exact (MK_COMB (@lem7166305) (@lem7166304 A B s y t R x y')). Qed.
Lemma lem7166307 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y'' : B) : (term1099 A B y t R x y'' y') = (term1078 A B y t R x y' y'').
Proof. exact (eq_refl (term1099 A B y t R x y'' y')). Qed.
Lemma lem7166308 {A : Type'} (s : A -> Prop) (x : A) : (term964 A s x) = (term964 A s x).
Proof. exact (eq_refl (term964 A s x)). Qed.
Lemma lem7166309 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y'' : B) : (term1104 A B s y t R x y'' y') = (term1105 A B s y t R x y' y'').
Proof. exact (MK_COMB (@lem7166308 A s x) (@lem7166307 A B y t R x y' y'')). Qed.
Lemma lem7166310 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1106 A B s y t R x y') = (term1107 A B s y t R x y').
Proof. exact (fun_ext (fun y'' : B => @lem7166309 A B s y t R x y'' y')). Qed.
Lemma lem7166311 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7166312 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1098 A B s y t R x y') = (term1108 A B s y t R x y').
Proof. exact (MK_COMB (@lem7166311 B) (@lem7166310 A B s y t R x y')). Qed.
Lemma lem7166313 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : ((term1097 A B s y t R x y') = (term1098 A B s y t R x y')) = ((term1093 A B s y t R x y') = (term1108 A B s y t R x y')).
Proof. exact (MK_COMB (@lem7166306 A B s y t R x y') (@lem7166312 A B s y t R x y')). Qed.
Lemma lem7166314 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1093 A B s y t R x y') = (term1108 A B s y t R x y').
Proof. exact (EQ_MP (@lem7166313 A B s y t R x y') (@lem7166298 A B s y t R x y')). Qed.
Lemma lem7166315 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1095 A B s y t R x) = (term1109 A B s y t R x).
Proof. exact (fun_ext (fun y' : B => @lem7166314 A B s y t R x y')). Qed.
Lemma lem7166316 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7166317 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1096 A B s y t R x) = (term1110 A B s y t R x).
Proof. exact (MK_COMB (@lem7166316 B) (@lem7166315 A B s y t R x)). Qed.
Lemma lem7166318 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1084 A B s y t R x) = (term1110 A B s y t R x).
Proof. exact (TRANS (@lem7166294 A B s y t R x) (@lem7166317 A B s y t R x)). Qed.
Lemma lem7166319 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1008 A B s y t R x) = (term1110 A B s y t R x).
Proof. exact (TRANS (@lem7166274 A B s y t R x) (@lem7166318 A B s y t R x)). Qed.
Lemma lem7166320 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) : (term1009 A B s y t R) = (term1111 A B s y t R).
Proof. exact (fun_ext (fun x : A => @lem7166319 A B s y t R x)). Qed.
Lemma lem7166321 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7166322 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) : (term1010 A B s y t R) = (term1112 A B s y t R).
Proof. exact (MK_COMB (@lem7166321 A) (@lem7166320 A B s y t R)). Qed.
Lemma lem7166360 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y'' : B) : (term1105 A B s y t R x y' y'') = (term1113 A B y s t R x y' y'').
Proof. exact (@lem19490 (term1003 A B t R y x) (term963 A s x) (term1051 A B t R x y' y'')). Qed.
Lemma lem7166361 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y : B) : (term1114 A B s t R x y' y) = (term1114 A B s t R x y' y).
Proof. exact (eq_refl (term1114 A B s t R x y' y)). Qed.
Lemma lem7166368 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (y : A -> B) (x : A) : (term1115 A B s t R y x) = (term1116 A B t s R y x).
Proof. exact (@lem19490 (term999 A B t y x) (term963 A s x) (term406 A B R y x)). Qed.
Lemma lem7166369 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7166370 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (y : A -> B) (x : A) : (term1117 A B s t R y x) = (term1118 A B t s R y x).
Proof. exact (MK_COMB (@lem7166369) (@lem7166368 A B t s R y x)). Qed.
Lemma lem7166371 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y'' : B) : (term1113 A B y s t R x y' y'') = (term1119 A B y s t R x y' y'').
Proof. exact (MK_COMB (@lem7166370 A B t s R y x) (@lem7166361 A B s t R x y' y'')). Qed.
Lemma lem7166373 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y'' : B) : (term1105 A B s y t R x y' y'') = (term1119 A B y s t R x y' y'').
Proof. exact (TRANS (@lem7166360 A B y s t R x y' y'') (@lem7166371 A B y s t R x y' y'')). Qed.
Lemma lem7166374 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1107 A B s y t R x y') = (term1120 A B y s t R x y').
Proof. exact (fun_ext (fun y'' : B => @lem7166373 A B y s t R x y'' y')). Qed.
Lemma lem7166375 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7166376 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1108 A B s y t R x y') = (term1121 A B y s t R x y').
Proof. exact (MK_COMB (@lem7166375 B) (@lem7166374 A B y s t R x y')). Qed.
Lemma lem7166377 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1109 A B s y t R x) = (term1122 A B y s t R x).
Proof. exact (fun_ext (fun y' : B => @lem7166376 A B y s t R x y')). Qed.
Lemma lem7166378 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7166379 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1110 A B s y t R x) = (term1123 A B y s t R x).
Proof. exact (MK_COMB (@lem7166378 B) (@lem7166377 A B y s t R x)). Qed.
Lemma lem7166380 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term1111 A B s y t R) = (term1124 A B y s t R).
Proof. exact (fun_ext (fun x : A => @lem7166379 A B y s t R x)). Qed.
Lemma lem7166381 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7166382 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term1112 A B s y t R) = (term1125 A B y s t R).
Proof. exact (MK_COMB (@lem7166381 A) (@lem7166380 A B y s t R)). Qed.
Lemma lem7166383 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term1010 A B s y t R) = (term1125 A B y s t R).
Proof. exact (TRANS (@lem7166322 A B s y t R) (@lem7166382 A B y s t R)). Qed.
Lemma lem7166384 {A B : Type'} (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1125 A B y s t R.
Proof. exact (EQ_MP (@lem7166383 A B y s t R) (@lem7165298 A B x y t R s h1)). Qed.
Lemma lem7166400 {A B : Type'} (R : type1413 A B) (x' : A) (x : B) (h1 : term380 A B R x' x) : term380 A B R x' x.
Proof. exact (h1). Qed.
Lemma lem7166422 {A B : Type'} (_95921 : B -> Prop) (_95913 : type830 A B) (h1 : term728 A B _95913) : term1126 A B _95913 _95921.
Proof. exact (@lem7165654 A B _95913 h1 _95921). Qed.
Lemma lem7166423 {A B : Type'} (_95913 : type830 A B) (_95921 : B -> Prop) : (term1126 A B _95913 _95921) = (term1040 A B _95913 _95921).
Proof. exact (eq_refl (term1126 A B _95913 _95921)). Qed.
Lemma lem7166424 {A B : Type'} (_95921 : B -> Prop) (_95913 : type830 A B) (h1 : term728 A B _95913) : term1040 A B _95913 _95921.
Proof. exact (EQ_MP (@lem7166423 A B _95913 _95921) (@lem7166422 A B _95921 _95913 h1)). Qed.
Lemma lem7166425 {A B : Type'} (_95921 : B -> Prop) (_95922 : type1413 A B) (_95913 : type830 A B) (h1 : term728 A B _95913) : term1127 A B _95913 _95921 _95922.
Proof. exact (@lem7166424 A B _95921 _95913 h1 _95922). Qed.
Lemma lem7166426 {A B : Type'} (_95913 : type830 A B) (_95921 : B -> Prop) (_95922 : type1413 A B) : (term1127 A B _95913 _95921 _95922) = (term1038 A B _95913 _95921 _95922).
Proof. exact (eq_refl (term1127 A B _95913 _95921 _95922)). Qed.
Lemma lem7166427 {A B : Type'} (_95921 : B -> Prop) (_95922 : type1413 A B) (_95913 : type830 A B) (h1 : term728 A B _95913) : term1038 A B _95913 _95921 _95922.
Proof. exact (EQ_MP (@lem7166426 A B _95913 _95921 _95922) (@lem7166425 A B _95921 _95922 _95913 h1)). Qed.
Lemma lem7166428 {A B : Type'} (_95921 : B -> Prop) (_95922 : type1413 A B) (_95923 : A) (_95913 : type830 A B) (h1 : term728 A B _95913) : term1128 A B _95913 _95921 _95922 _95923.
Proof. exact (@lem7166427 A B _95921 _95922 _95913 h1 _95923). Qed.
Lemma lem7166429 {A B : Type'} (_95913 : type830 A B) (_95921 : B -> Prop) (_95922 : type1413 A B) (_95923 : A) : (term1128 A B _95913 _95921 _95922 _95923) = (term1036 A B _95913 _95921 _95922 _95923).
Proof. exact (eq_refl (term1128 A B _95913 _95921 _95922 _95923)). Qed.
Lemma lem7166430 {A B : Type'} (_95921 : B -> Prop) (_95922 : type1413 A B) (_95923 : A) (_95913 : type830 A B) (h1 : term728 A B _95913) : term1036 A B _95913 _95921 _95922 _95923.
Proof. exact (EQ_MP (@lem7166429 A B _95913 _95921 _95922 _95923) (@lem7166428 A B _95921 _95922 _95923 _95913 h1)). Qed.
Lemma lem7166431 {A B : Type'} (_95921 : B -> Prop) (_95922 : type1413 A B) (_95923 : A) (_95924 : B) (_95913 : type830 A B) (h1 : term728 A B _95913) : term1129 A B _95913 _95921 _95922 _95923 _95924.
Proof. exact (@lem7166430 A B _95921 _95922 _95923 _95913 h1 _95924). Qed.
Lemma lem7166432 {A B : Type'} (_95924 : B) (_95913 : type830 A B) (_95921 : B -> Prop) (_95922 : type1413 A B) (_95923 : A) : (term1129 A B _95913 _95921 _95922 _95923 _95924) = (term1034 A B _95924 _95913 _95921 _95922 _95923).
Proof. exact (eq_refl (term1129 A B _95913 _95921 _95922 _95923 _95924)). Qed.
Lemma lem7166433 {A B : Type'} (_95924 : B) (_95921 : B -> Prop) (_95922 : type1413 A B) (_95923 : A) (_95913 : type830 A B) (h1 : term728 A B _95913) : term1034 A B _95924 _95913 _95921 _95922 _95923.
Proof. exact (EQ_MP (@lem7166432 A B _95924 _95913 _95921 _95922 _95923) (@lem7166431 A B _95921 _95922 _95923 _95924 _95913 h1)). Qed.
Lemma lem7166434 {A B : Type'} (_95925 : A) (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1130 A B y s t R _95925.
Proof. exact (@lem7165840 A B x y t R s h1 _95925). Qed.
Lemma lem7166435 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (_95925 : A) : (term1130 A B y s t R _95925) = (term1123 A B y s t R _95925).
Proof. exact (eq_refl (term1130 A B y s t R _95925)). Qed.
Lemma lem7166436 {A B : Type'} (_95925 : A) (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1123 A B y s t R _95925.
Proof. exact (EQ_MP (@lem7166435 A B y s t R _95925) (@lem7166434 A B _95925 x y t R s h1)). Qed.
Lemma lem7166437 {A B : Type'} (_95925 : A) (_95926 : B) (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1131 A B y s t R _95925 _95926.
Proof. exact (@lem7166436 A B _95925 x y t R s h1 _95926). Qed.
Lemma lem7166438 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (_95925 : A) (_95926 : B) : (term1131 A B y s t R _95925 _95926) = (term1121 A B y s t R _95925 _95926).
Proof. exact (eq_refl (term1131 A B y s t R _95925 _95926)). Qed.
Lemma lem7166439 {A B : Type'} (_95925 : A) (_95926 : B) (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1121 A B y s t R _95925 _95926.
Proof. exact (EQ_MP (@lem7166438 A B y s t R _95925 _95926) (@lem7166437 A B _95925 _95926 x y t R s h1)). Qed.
Lemma lem7166440 {A B : Type'} (_95925 : A) (_95926 : B) (_95927 : B) (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1132 A B y s t R _95925 _95926 _95927.
Proof. exact (@lem7166439 A B _95925 _95926 x y t R s h1 _95927). Qed.
Lemma lem7166441 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (_95925 : A) (_95927 : B) (_95926 : B) : (term1132 A B y s t R _95925 _95926 _95927) = (term1119 A B y s t R _95925 _95927 _95926).
Proof. exact (eq_refl (term1132 A B y s t R _95925 _95926 _95927)). Qed.
Lemma lem7166442 {A B : Type'} (_95925 : A) (_95927 : B) (_95926 : B) (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1119 A B y s t R _95925 _95927 _95926.
Proof. exact (EQ_MP (@lem7166441 A B y s t R _95925 _95927 _95926) (@lem7166440 A B _95925 _95926 _95927 x y t R s h1)). Qed.
Lemma lem7166464 {A B : Type'} (_95935 : B -> Prop) (_95913 : type830 A B) (h1 : term728 A B _95913) : term1126 A B _95913 _95935.
Proof. exact (@lem7166198 A B _95913 h1 _95935). Qed.
Lemma lem7166465 {A B : Type'} (_95913 : type830 A B) (_95935 : B -> Prop) : (term1126 A B _95913 _95935) = (term1040 A B _95913 _95935).
Proof. exact (eq_refl (term1126 A B _95913 _95935)). Qed.
Lemma lem7166466 {A B : Type'} (_95935 : B -> Prop) (_95913 : type830 A B) (h1 : term728 A B _95913) : term1040 A B _95913 _95935.
Proof. exact (EQ_MP (@lem7166465 A B _95913 _95935) (@lem7166464 A B _95935 _95913 h1)). Qed.
Lemma lem7166467 {A B : Type'} (_95935 : B -> Prop) (_95936 : type1413 A B) (_95913 : type830 A B) (h1 : term728 A B _95913) : term1127 A B _95913 _95935 _95936.
Proof. exact (@lem7166466 A B _95935 _95913 h1 _95936). Qed.
Lemma lem7166468 {A B : Type'} (_95913 : type830 A B) (_95935 : B -> Prop) (_95936 : type1413 A B) : (term1127 A B _95913 _95935 _95936) = (term1038 A B _95913 _95935 _95936).
Proof. exact (eq_refl (term1127 A B _95913 _95935 _95936)). Qed.
Lemma lem7166469 {A B : Type'} (_95935 : B -> Prop) (_95936 : type1413 A B) (_95913 : type830 A B) (h1 : term728 A B _95913) : term1038 A B _95913 _95935 _95936.
Proof. exact (EQ_MP (@lem7166468 A B _95913 _95935 _95936) (@lem7166467 A B _95935 _95936 _95913 h1)). Qed.
Lemma lem7166470 {A B : Type'} (_95935 : B -> Prop) (_95936 : type1413 A B) (_95937 : A) (_95913 : type830 A B) (h1 : term728 A B _95913) : term1128 A B _95913 _95935 _95936 _95937.
Proof. exact (@lem7166469 A B _95935 _95936 _95913 h1 _95937). Qed.
Lemma lem7166471 {A B : Type'} (_95913 : type830 A B) (_95935 : B -> Prop) (_95936 : type1413 A B) (_95937 : A) : (term1128 A B _95913 _95935 _95936 _95937) = (term1036 A B _95913 _95935 _95936 _95937).
Proof. exact (eq_refl (term1128 A B _95913 _95935 _95936 _95937)). Qed.
Lemma lem7166472 {A B : Type'} (_95935 : B -> Prop) (_95936 : type1413 A B) (_95937 : A) (_95913 : type830 A B) (h1 : term728 A B _95913) : term1036 A B _95913 _95935 _95936 _95937.
Proof. exact (EQ_MP (@lem7166471 A B _95913 _95935 _95936 _95937) (@lem7166470 A B _95935 _95936 _95937 _95913 h1)). Qed.
Lemma lem7166473 {A B : Type'} (_95935 : B -> Prop) (_95936 : type1413 A B) (_95937 : A) (_95938 : B) (_95913 : type830 A B) (h1 : term728 A B _95913) : term1129 A B _95913 _95935 _95936 _95937 _95938.
Proof. exact (@lem7166472 A B _95935 _95936 _95937 _95913 h1 _95938). Qed.
Lemma lem7166474 {A B : Type'} (_95938 : B) (_95913 : type830 A B) (_95935 : B -> Prop) (_95936 : type1413 A B) (_95937 : A) : (term1129 A B _95913 _95935 _95936 _95937 _95938) = (term1034 A B _95938 _95913 _95935 _95936 _95937).
Proof. exact (eq_refl (term1129 A B _95913 _95935 _95936 _95937 _95938)). Qed.
Lemma lem7166475 {A B : Type'} (_95938 : B) (_95935 : B -> Prop) (_95936 : type1413 A B) (_95937 : A) (_95913 : type830 A B) (h1 : term728 A B _95913) : term1034 A B _95938 _95913 _95935 _95936 _95937.
Proof. exact (EQ_MP (@lem7166474 A B _95938 _95913 _95935 _95936 _95937) (@lem7166473 A B _95935 _95936 _95937 _95938 _95913 h1)). Qed.
Lemma lem7166476 {A B : Type'} (_95939 : A) (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1130 A B y s t R _95939.
Proof. exact (@lem7166384 A B x y t R s h1 _95939). Qed.
Lemma lem7166477 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (_95939 : A) : (term1130 A B y s t R _95939) = (term1123 A B y s t R _95939).
Proof. exact (eq_refl (term1130 A B y s t R _95939)). Qed.
Lemma lem7166478 {A B : Type'} (_95939 : A) (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1123 A B y s t R _95939.
Proof. exact (EQ_MP (@lem7166477 A B y s t R _95939) (@lem7166476 A B _95939 x y t R s h1)). Qed.
Lemma lem7166479 {A B : Type'} (_95939 : A) (_95940 : B) (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1131 A B y s t R _95939 _95940.
Proof. exact (@lem7166478 A B _95939 x y t R s h1 _95940). Qed.
Lemma lem7166480 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (_95939 : A) (_95940 : B) : (term1131 A B y s t R _95939 _95940) = (term1121 A B y s t R _95939 _95940).
Proof. exact (eq_refl (term1131 A B y s t R _95939 _95940)). Qed.
Lemma lem7166481 {A B : Type'} (_95939 : A) (_95940 : B) (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1121 A B y s t R _95939 _95940.
Proof. exact (EQ_MP (@lem7166480 A B y s t R _95939 _95940) (@lem7166479 A B _95939 _95940 x y t R s h1)). Qed.
Lemma lem7166482 {A B : Type'} (_95939 : A) (_95940 : B) (_95941 : B) (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1132 A B y s t R _95939 _95940 _95941.
Proof. exact (@lem7166481 A B _95939 _95940 x y t R s h1 _95941). Qed.
Lemma lem7166483 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (_95939 : A) (_95941 : B) (_95940 : B) : (term1132 A B y s t R _95939 _95940 _95941) = (term1119 A B y s t R _95939 _95941 _95940).
Proof. exact (eq_refl (term1132 A B y s t R _95939 _95940 _95941)). Qed.
Lemma lem7166484 {A B : Type'} (_95939 : A) (_95941 : B) (_95940 : B) (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1119 A B y s t R _95939 _95941 _95940.
Proof. exact (EQ_MP (@lem7166483 A B y s t R _95939 _95941 _95940) (@lem7166482 A B _95939 _95940 _95941 x y t R s h1)). Qed.
Lemma lem7166491 {A B : Type'} (_95925 : A) (_95927 : B) (_95926 : B) (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1114 A B s t R _95925 _95927 _95926.
Proof. exact (proj2 (@lem7166442 A B _95925 _95927 _95926 x y t R s h1)). Qed.
Lemma lem7166495 {A B : Type'} (_95924 : B) (_95921 : B -> Prop) (_95922 : type1413 A B) (_95923 : A) (_95913 : type830 A B) (h1 : term728 A B _95913) : term1133 A B _95924 _95913 _95921 _95922 _95923.
Proof. exact (proj2 (@lem7166433 A B _95924 _95921 _95922 _95923 _95913 h1)). Qed.
Lemma lem7166496 {A B : Type'} (_95924 : B) (_95921 : B -> Prop) (_95922 : type1413 A B) (_95923 : A) (_95913 : type830 A B) (h1 : term728 A B _95913) : term1134 A B _95924 _95913 _95921 _95922 _95923.
Proof. exact (proj1 (@lem7166433 A B _95924 _95921 _95922 _95923 _95913 h1)). Qed.
Lemma lem7166504 {A B : Type'} (_95939 : A) (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1116 A B t s R y _95939.
Proof. exact (proj1 (@lem7166484 A B _95939 (@el B) (@el B) x y t R s h1)). Qed.
Lemma lem7166507 {A B : Type'} (_95938 : B) (_95935 : B -> Prop) (_95936 : type1413 A B) (_95937 : A) (_95913 : type830 A B) (h1 : term728 A B _95913) : term1133 A B _95938 _95913 _95935 _95936 _95937.
Proof. exact (proj2 (@lem7166475 A B _95938 _95935 _95936 _95937 _95913 h1)). Qed.
Lemma lem7166518 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term963 A s x') : term963 A s x'.
Proof. exact (h1). Qed.
Lemma lem7166590 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term983 A B _95913 t R x' x) : term983 A B _95913 t R x' x.
Proof. exact (h1). Qed.
Lemma lem7166601 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (_95925 : A) (_95927 : B) (_95926 : B) : (term991 A B t R _95925 _95927 _95926) = (term1135 A B t R _95925 _95927 _95926).
Proof. exact (@lem7163460 (term963 B t _95927) (term380 A B R _95925 _95927) (_95927 = _95926)). Qed.
Lemma lem7166602 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (_95925 : A) (_95926 : B) : (term990 A B t R _95925 _95926) = (term990 A B t R _95925 _95926).
Proof. exact (eq_refl (term990 A B t R _95925 _95926)). Qed.
Lemma lem7166603 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (_95925 : A) (_95927 : B) (_95926 : B) : (term1051 A B t R _95925 _95927 _95926) = (term1136 A B t R _95925 _95927 _95926).
Proof. exact (MK_COMB (@lem7166602 A B t R _95925 _95926) (@lem7166601 A B t R _95925 _95927 _95926)). Qed.
Lemma lem7166610 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (_95925 : A) (_95927 : B) (_95926 : B) : (term1136 A B t R _95925 _95927 _95926) = (term1137 A B t R _95925 _95927 _95926).
Proof. exact (@lem7163460 (term963 B t _95926) (term380 A B R _95925 _95926) (term1135 A B t R _95925 _95927 _95926)). Qed.
Lemma lem7166611 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (_95925 : A) (_95927 : B) (_95926 : B) : (term1051 A B t R _95925 _95927 _95926) = (term1137 A B t R _95925 _95927 _95926).
Proof. exact (TRANS (@lem7166603 A B t R _95925 _95927 _95926) (@lem7166610 A B t R _95925 _95927 _95926)). Qed.
Lemma lem7166612 {A : Type'} (s : A -> Prop) (_95925 : A) : (term964 A s _95925) = (term964 A s _95925).
Proof. exact (eq_refl (term964 A s _95925)). Qed.
Lemma lem7166615 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (_95925 : A) (_95927 : B) (_95926 : B) : (term1114 A B s t R _95925 _95927 _95926) = (term1138 A B s t R _95925 _95927 _95926).
Proof. exact (MK_COMB (@lem7166612 A s _95925) (@lem7166611 A B t R _95925 _95927 _95926)). Qed.
Lemma lem7166616 {A B : Type'} (_95925 : A) (_95927 : B) (_95926 : B) (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1138 A B s t R _95925 _95927 _95926.
Proof. exact (EQ_MP (@lem7166615 A B s t R _95925 _95927 _95926) (@lem7166491 A B _95925 _95927 _95926 x y t R s h1)). Qed.
Lemma lem7166639 {A B : Type'} (_95924 : B) (_95913 : type830 A B) (_95921 : B -> Prop) (_95922 : type1413 A B) (_95923 : A) : (term1134 A B _95924 _95913 _95921 _95922 _95923) = (term1139 A B _95924 _95913 _95921 _95922 _95923).
Proof. exact (@lem7163460 (term963 B _95921 _95924) (term380 A B _95922 _95923 _95924) (term960 A B _95913 _95921 _95922 _95923)). Qed.
Lemma lem7166640 {A B : Type'} (_95924 : B) (_95921 : B -> Prop) (_95922 : type1413 A B) (_95923 : A) (_95913 : type830 A B) (h1 : term728 A B _95913) : term1139 A B _95924 _95913 _95921 _95922 _95923.
Proof. exact (EQ_MP (@lem7166639 A B _95924 _95913 _95921 _95922 _95923) (@lem7166496 A B _95924 _95921 _95922 _95923 _95913 h1)). Qed.
Lemma lem7166651 {A B : Type'} (_95924 : B) (_95913 : type830 A B) (_95921 : B -> Prop) (_95922 : type1413 A B) (_95923 : A) : (term1133 A B _95924 _95913 _95921 _95922 _95923) = (term1140 A B _95924 _95913 _95921 _95922 _95923).
Proof. exact (@lem7163460 (term963 B _95921 _95924) (term380 A B _95922 _95923 _95924) (term370 A B _95913 _95921 _95922 _95923)). Qed.
Lemma lem7166652 {A B : Type'} (_95924 : B) (_95921 : B -> Prop) (_95922 : type1413 A B) (_95923 : A) (_95913 : type830 A B) (h1 : term728 A B _95913) : term1140 A B _95924 _95913 _95921 _95922 _95923.
Proof. exact (EQ_MP (@lem7166651 A B _95924 _95913 _95921 _95922 _95923) (@lem7166495 A B _95924 _95921 _95922 _95923 _95913 h1)). Qed.
Lemma lem7166662 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term963 A s x') : term963 A s x'.
Proof. exact (h1). Qed.
Lemma lem7166732 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term981 A B s _95913 t R x' x) : (term367 A B _95913 t R x') = x.
Proof. exact (proj2 (@lem7165307 A B s _95913 t R x' x h1)). Qed.
Lemma lem7166734 {A B : Type'} (R : type1413 A B) (x' : A) (x : B) (h1 : term380 A B R x' x) : term380 A B R x' x.
Proof. exact (h1). Qed.
Lemma lem7166795 {A B : Type'} (_95938 : B) (_95913 : type830 A B) (_95935 : B -> Prop) (_95936 : type1413 A B) (_95937 : A) : (term1133 A B _95938 _95913 _95935 _95936 _95937) = (term1140 A B _95938 _95913 _95935 _95936 _95937).
Proof. exact (@lem7163460 (term963 B _95935 _95938) (term380 A B _95936 _95937 _95938) (term370 A B _95913 _95935 _95936 _95937)). Qed.
Lemma lem7166866 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term963 A s x') : term963 A s x'.
Proof. exact (h1). Qed.
Lemma lem7166937 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term981 A B s _95913 t R x' x) : x = (term367 A B _95913 t R x').
Proof. exact (SYM (@lem7166732 A B s _95913 t R x' x h1)). Qed.
Lemma lem7166993 {A B : Type'} (R : type1413 A B) (x' : A) : (term1141 A B R x') = (term1141 A B R x').
Proof. exact (eq_refl (term1141 A B R x')). Qed.
Lemma lem7166994 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term981 A B s _95913 t R x' x) : (term1142 A B R x' x) = (term1143 A B _95913 t R x').
Proof. exact (MK_COMB (@lem7166993 A B R x') (@lem7166937 A B s _95913 t R x' x h1)). Qed.
Lemma lem7166995 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) : (term1143 A B _95913 t R x') = (term1144 A B _95913 t R x').
Proof. exact (eq_refl (term1143 A B _95913 t R x')). Qed.
Lemma lem7166996 {A B : Type'} (R : type1413 A B) (x' : A) (x : B) : (term1145 A B R x' x) = (term1145 A B R x' x).
Proof. exact (eq_refl (term1145 A B R x' x)). Qed.
Lemma lem7166997 {A B : Type'} (x : B) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) : ((term1142 A B R x' x) = (term1143 A B _95913 t R x')) = ((term1142 A B R x' x) = (term1144 A B _95913 t R x')).
Proof. exact (MK_COMB (@lem7166996 A B R x' x) (@lem7166995 A B _95913 t R x')). Qed.
Lemma lem7166998 {A B : Type'} (R : type1413 A B) (x' : A) (x : B) : (term1142 A B R x' x) = (term380 A B R x' x).
Proof. exact (eq_refl (term1142 A B R x' x)). Qed.
Lemma lem7166999 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7167000 {A B : Type'} (R : type1413 A B) (x' : A) (x : B) : (term1145 A B R x' x) = (term1146 A B R x' x).
Proof. exact (MK_COMB (@lem7166999) (@lem7166998 A B R x' x)). Qed.
Lemma lem7167001 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) : (term1144 A B _95913 t R x') = (term1144 A B _95913 t R x').
Proof. exact (eq_refl (term1144 A B _95913 t R x')). Qed.
Lemma lem7167002 {A B : Type'} (x : B) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) : ((term1142 A B R x' x) = (term1144 A B _95913 t R x')) = ((term380 A B R x' x) = (term1144 A B _95913 t R x')).
Proof. exact (MK_COMB (@lem7167000 A B R x' x) (@lem7167001 A B _95913 t R x')). Qed.
Lemma lem7167003 {A B : Type'} (x : B) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) : ((term1142 A B R x' x) = (term1143 A B _95913 t R x')) = ((term380 A B R x' x) = (term1144 A B _95913 t R x')).
Proof. exact (TRANS (@lem7166997 A B x _95913 t R x') (@lem7167002 A B x _95913 t R x')). Qed.
Lemma lem7167004 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term981 A B s _95913 t R x' x) : (term380 A B R x' x) = (term1144 A B _95913 t R x').
Proof. exact (EQ_MP (@lem7167003 A B x _95913 t R x') (@lem7166994 A B s _95913 t R x' x h1)). Qed.
Lemma lem7167005 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term380 A B R x' x) (h2 : term981 A B s _95913 t R x' x) : term1144 A B _95913 t R x'.
Proof. exact (EQ_MP (@lem7167004 A B s _95913 t R x' x h2) (@lem7166734 A B R x' x h1)). Qed.
Lemma lem7167033 {A B : Type'} (_95939 : A) (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1147 A B s t y _95939.
Proof. exact (proj1 (@lem7166504 A B _95939 x y t R s h1)). Qed.
Lemma lem7167047 {A B : Type'} (_95939 : A) (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1148 A B s R y _95939.
Proof. exact (proj2 (@lem7166504 A B _95939 x y t R s h1)). Qed.
Lemma lem7167075 {A B : Type'} (_95938 : B) (_95935 : B -> Prop) (_95936 : type1413 A B) (_95937 : A) (_95913 : type830 A B) (h1 : term728 A B _95913) : term1140 A B _95938 _95913 _95935 _95936 _95937.
Proof. exact (EQ_MP (@lem7166795 A B _95938 _95913 _95935 _95936 _95937) (@lem7166507 A B _95938 _95935 _95936 _95937 _95913 h1)). Qed.
Lemma lem7167212 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term987 A B s _95913 t R x' x) : @I (A -> Prop) s x'.
Proof. exact (proj1 (@lem7165302 A B s _95913 t R x' x h1)). Qed.
Lemma lem7167213 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term987 A B s _95913 t R x' x) : term1149 A s x'.
Proof. exact (fun h0 : term963 A s x' => @lem7167212 A B s _95913 t R x' x h1). Qed.
Lemma lem7167215 (p : Prop) : (term551 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7167216 {A : Type'} (s : A -> Prop) (x' : A) : (term1149 A s x') = (@I (A -> Prop) s x').
Proof. exact (@lem7167215 (@I (A -> Prop) s x')). Qed.
Lemma lem7167217 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term987 A B s _95913 t R x' x) : @I (A -> Prop) s x'.
Proof. exact (EQ_MP (@lem7167216 A s x') (@lem7167213 A B s _95913 t R x' x h1)). Qed.
Lemma lem7167220 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7167222 {A : Type'} (s : A -> Prop) (x' : A) : (term963 A s x') = (term1150 A s x').
Proof. exact (@lem7167220 (@I (A -> Prop) s x')). Qed.
Lemma lem7167225 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term963 A s x') : term1150 A s x'.
Proof. exact (EQ_MP (@lem7167222 A s x') (@lem7166518 A s x' h1)). Qed.
Lemma lem7167228 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term963 A s x') (h2 : term987 A B s _95913 t R x' x) : False.
Proof. exact (@lem7167225 A s x' h1 (@lem7167217 A B s _95913 t R x' x h2)). Qed.
Lemma lem7167229 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term963 A s x') (h2 : term987 A B s _95913 t R x' x) : term596.
Proof. exact (fun h0 : ~ False => @lem7167228 A B s _95913 t R x' x h1 h2). Qed.
Lemma lem7167231 (p : Prop) : (term551 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7167232 : term596 = False.
Proof. exact (@lem7167231 False). Qed.
Lemma lem7167233 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term963 A s x') (h2 : term987 A B s _95913 t R x' x) : False.
Proof. exact (EQ_MP (@lem7167232) (@lem7167229 A B s _95913 t R x' x h1 h2)). Qed.
Lemma lem7167370 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term987 A B s _95913 t R x' x) : @I (A -> Prop) s x'.
Proof. exact (proj1 (@lem7165302 A B s _95913 t R x' x h1)). Qed.
Lemma lem7167371 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term987 A B s _95913 t R x' x) : term1149 A s x'.
Proof. exact (fun h0 : term963 A s x' => @lem7167370 A B s _95913 t R x' x h1). Qed.
Lemma lem7167373 (p : Prop) : (term551 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7167374 {A : Type'} (s : A -> Prop) (x' : A) : (term1149 A s x') = (@I (A -> Prop) s x').
Proof. exact (@lem7167373 (@I (A -> Prop) s x')). Qed.
Lemma lem7167375 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term987 A B s _95913 t R x' x) : @I (A -> Prop) s x'.
Proof. exact (EQ_MP (@lem7167374 A s x') (@lem7167371 A B s _95913 t R x' x h1)). Qed.
Lemma lem7167377 {A B : Type'} (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : @I (B -> Prop) t x.
Proof. exact (proj1 (@lem7165294 A B x y t R s h1)). Qed.
Lemma lem7167378 {A B : Type'} (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1149 B t x.
Proof. exact (fun h0 : term963 B t x => @lem7167377 A B x y t R s h1). Qed.
Lemma lem7167380 (p : Prop) : (term551 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7167381 {B : Type'} (t : B -> Prop) (x : B) : (term1149 B t x) = (@I (B -> Prop) t x).
Proof. exact (@lem7167380 (@I (B -> Prop) t x)). Qed.
Lemma lem7167382 {A B : Type'} (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : @I (B -> Prop) t x.
Proof. exact (EQ_MP (@lem7167381 B t x) (@lem7167378 A B x y t R s h1)). Qed.
Lemma lem7167384 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term987 A B s _95913 t R x' x) : term378 A B R x' x.
Proof. exact (proj2 (@lem7165302 A B s _95913 t R x' x h1)). Qed.
Lemma lem7167385 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term987 A B s _95913 t R x' x) : term1151 A B R x' x.
Proof. exact (fun h0 : term380 A B R x' x => @lem7167384 A B s _95913 t R x' x h1). Qed.
Lemma lem7167387 (p : Prop) : (term551 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7167388 {A B : Type'} (R : type1413 A B) (x' : A) (x : B) : (term1151 A B R x' x) = (term378 A B R x' x).
Proof. exact (@lem7167387 (term378 A B R x' x)). Qed.
Lemma lem7167389 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term987 A B s _95913 t R x' x) : term378 A B R x' x.
Proof. exact (EQ_MP (@lem7167388 A B R x' x) (@lem7167385 A B s _95913 t R x' x h1)). Qed.
Lemma lem7167391 {A B : Type'} (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : @I (B -> Prop) t x.
Proof. exact (proj1 (@lem7165294 A B x y t R s h1)). Qed.
Lemma lem7167392 {A B : Type'} (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1149 B t x.
Proof. exact (fun h0 : term963 B t x => @lem7167391 A B x y t R s h1). Qed.
Lemma lem7167394 (p : Prop) : (term551 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7167395 {B : Type'} (t : B -> Prop) (x : B) : (term1149 B t x) = (@I (B -> Prop) t x).
Proof. exact (@lem7167394 (@I (B -> Prop) t x)). Qed.
Lemma lem7167396 {A B : Type'} (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : @I (B -> Prop) t x.
Proof. exact (EQ_MP (@lem7167395 B t x) (@lem7167392 A B x y t R s h1)). Qed.
Lemma lem7167398 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term987 A B s _95913 t R x' x) : term378 A B R x' x.
Proof. exact (proj2 (@lem7165302 A B s _95913 t R x' x h1)). Qed.
Lemma lem7167399 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term987 A B s _95913 t R x' x) : term1151 A B R x' x.
Proof. exact (fun h0 : term380 A B R x' x => @lem7167398 A B s _95913 t R x' x h1). Qed.
Lemma lem7167401 (p : Prop) : (term551 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7167402 {A B : Type'} (R : type1413 A B) (x' : A) (x : B) : (term1151 A B R x' x) = (term378 A B R x' x).
Proof. exact (@lem7167401 (term378 A B R x' x)). Qed.
Lemma lem7167403 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term987 A B s _95913 t R x' x) : term378 A B R x' x.
Proof. exact (EQ_MP (@lem7167402 A B R x' x) (@lem7167399 A B s _95913 t R x' x h1)). Qed.
Lemma lem7167419 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7167420 {A B : Type'} (_95913 : type830 A B) (_95921 : B -> Prop) (_95922 : type1413 A B) (_95923 : A) (_95924 : B) : (term1152 A B _95924 _95913 _95921 _95922 _95923) = (term1153 A B _95913 _95921 _95922 _95923 _95924).
Proof. exact (@lem7167419 (term960 A B _95913 _95921 _95922 _95923) (term380 A B _95922 _95923 _95924)). Qed.
Lemma lem7167426 {B : Type'} (_95921 : B -> Prop) (_95924 : B) : (term964 B _95921 _95924) = (term964 B _95921 _95924).
Proof. exact (eq_refl (term964 B _95921 _95924)). Qed.
Lemma lem7167427 {A B : Type'} (_95913 : type830 A B) (_95921 : B -> Prop) (_95922 : type1413 A B) (_95923 : A) (_95924 : B) : (term1139 A B _95924 _95913 _95921 _95922 _95923) = (term1154 A B _95913 _95921 _95922 _95923 _95924).
Proof. exact (MK_COMB (@lem7167426 B _95921 _95924) (@lem7167420 A B _95913 _95921 _95922 _95923 _95924)). Qed.
Lemma lem7167431 (q : Prop) (p : Prop) (r : Prop) : (term21 p q r) = (term21 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7167432 {A B : Type'} (_95913 : type830 A B) (_95921 : B -> Prop) (_95922 : type1413 A B) (_95923 : A) (_95924 : B) : (term1154 A B _95913 _95921 _95922 _95923 _95924) = (term1155 A B _95913 _95921 _95922 _95923 _95924).
Proof. exact (@lem7167431 (term960 A B _95913 _95921 _95922 _95923) (term963 B _95921 _95924) (term380 A B _95922 _95923 _95924)). Qed.
Lemma lem7167448 {A B : Type'} (_95913 : type830 A B) (_95921 : B -> Prop) (_95922 : type1413 A B) (_95923 : A) (_95924 : B) : (term1139 A B _95924 _95913 _95921 _95922 _95923) = (term1155 A B _95913 _95921 _95922 _95923 _95924).
Proof. exact (TRANS (@lem7167427 A B _95913 _95921 _95922 _95923 _95924) (@lem7167432 A B _95913 _95921 _95922 _95923 _95924)). Qed.
Lemma lem7167449 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7167450 {A B : Type'} (_95913 : type830 A B) (_95921 : B -> Prop) (_95922 : type1413 A B) (_95923 : A) (_95924 : B) : (term1156 A B _95924 _95913 _95921 _95922 _95923) = (term1157 A B _95913 _95921 _95922 _95923 _95924).
Proof. exact (MK_COMB (@lem7167449) (@lem7167448 A B _95913 _95921 _95922 _95923 _95924)). Qed.
Lemma lem7167466 {A B : Type'} (_95913 : type830 A B) (_95921 : B -> Prop) (_95922 : type1413 A B) (_95923 : A) (_95924 : B) : (term1155 A B _95913 _95921 _95922 _95923 _95924) = (term1155 A B _95913 _95921 _95922 _95923 _95924).
Proof. exact (eq_refl (term1155 A B _95913 _95921 _95922 _95923 _95924)). Qed.
Lemma lem7167467 {A B : Type'} (_95913 : type830 A B) (_95921 : B -> Prop) (_95922 : type1413 A B) (_95923 : A) (_95924 : B) : ((term1139 A B _95924 _95913 _95921 _95922 _95923) = (term1155 A B _95913 _95921 _95922 _95923 _95924)) = ((term1155 A B _95913 _95921 _95922 _95923 _95924) = (term1155 A B _95913 _95921 _95922 _95923 _95924)).
Proof. exact (MK_COMB (@lem7167450 A B _95913 _95921 _95922 _95923 _95924) (@lem7167466 A B _95913 _95921 _95922 _95923 _95924)). Qed.
Lemma lem7167469 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7167470 (x : Prop) : (x = x) = True.
Proof. exact (@lem7167469 Prop x). Qed.
Lemma lem7167471 {A B : Type'} (_95913 : type830 A B) (_95921 : B -> Prop) (_95922 : type1413 A B) (_95923 : A) (_95924 : B) : ((term1155 A B _95913 _95921 _95922 _95923 _95924) = (term1155 A B _95913 _95921 _95922 _95923 _95924)) = True.
Proof. exact (@lem7167470 (term1155 A B _95913 _95921 _95922 _95923 _95924)). Qed.
Lemma lem7167472 {A B : Type'} (_95913 : type830 A B) (_95921 : B -> Prop) (_95922 : type1413 A B) (_95923 : A) (_95924 : B) : ((term1139 A B _95924 _95913 _95921 _95922 _95923) = (term1155 A B _95913 _95921 _95922 _95923 _95924)) = True.
Proof. exact (TRANS (@lem7167467 A B _95913 _95921 _95922 _95923 _95924) (@lem7167471 A B _95913 _95921 _95922 _95923 _95924)). Qed.
Lemma lem7167473 {A B : Type'} (_95913 : type830 A B) (_95921 : B -> Prop) (_95922 : type1413 A B) (_95923 : A) (_95924 : B) : True = ((term1139 A B _95924 _95913 _95921 _95922 _95923) = (term1155 A B _95913 _95921 _95922 _95923 _95924)).
Proof. exact (SYM (@lem7167472 A B _95913 _95921 _95922 _95923 _95924)). Qed.
Lemma lem7167474 {A B : Type'} (_95913 : type830 A B) (_95921 : B -> Prop) (_95922 : type1413 A B) (_95923 : A) (_95924 : B) : (term1139 A B _95924 _95913 _95921 _95922 _95923) = (term1155 A B _95913 _95921 _95922 _95923 _95924).
Proof. exact (EQ_MP (@lem7167473 A B _95913 _95921 _95922 _95923 _95924) (@lem0)). Qed.
Lemma lem7167475 {A B : Type'} (_95921 : B -> Prop) (_95922 : type1413 A B) (_95923 : A) (_95924 : B) (_95913 : type830 A B) (h1 : term728 A B _95913) : term1155 A B _95913 _95921 _95922 _95923 _95924.
Proof. exact (EQ_MP (@lem7167474 A B _95913 _95921 _95922 _95923 _95924) (@lem7166640 A B _95924 _95921 _95922 _95923 _95913 h1)). Qed.
Lemma lem7167477 (b : Prop) (a : Prop) : (a \/ b) = (term555 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7167478 {A B : Type'} (_95924 : B) (_95913 : type830 A B) (_95921 : B -> Prop) (_95922 : type1413 A B) (_95923 : A) : (term1155 A B _95913 _95921 _95922 _95923 _95924) = (term1158 A B _95924 _95913 _95921 _95922 _95923).
Proof. exact (@lem7167477 (term965 A B _95921 _95922 _95923 _95924) (term960 A B _95913 _95921 _95922 _95923)). Qed.
Lemma lem7167480 (a : Prop) (b : Prop) : (term582 a b) = (term583 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7167481 {A B : Type'} (_95921 : B -> Prop) (_95922 : type1413 A B) (_95923 : A) (_95924 : B) : (term1159 A B _95921 _95922 _95923 _95924) = (term1160 A B _95921 _95922 _95923 _95924).
Proof. exact (@lem7167480 (term963 B _95921 _95924) (term380 A B _95922 _95923 _95924)). Qed.
Lemma lem7167483 (a : Prop) : (term203 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7167484 {B : Type'} (_95921 : B -> Prop) (_95924 : B) : (term1161 B _95921 _95924) = (@I (B -> Prop) _95921 _95924).
Proof. exact (@lem7167483 (@I (B -> Prop) _95921 _95924)). Qed.
Lemma lem7167485 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7167486 {B : Type'} (_95921 : B -> Prop) (_95924 : B) : (term1162 B _95921 _95924) = (term977 B _95921 _95924).
Proof. exact (MK_COMB (@lem7167485) (@lem7167484 B _95921 _95924)). Qed.
Lemma lem7167488 (a : Prop) : (term203 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7167489 {A B : Type'} (_95922 : type1413 A B) (_95923 : A) (_95924 : B) : (term588 A B _95922 _95923 _95924) = (term378 A B _95922 _95923 _95924).
Proof. exact (@lem7167488 (term378 A B _95922 _95923 _95924)). Qed.
Lemma lem7167490 {A B : Type'} (_95921 : B -> Prop) (_95922 : type1413 A B) (_95923 : A) (_95924 : B) : (term1160 A B _95921 _95922 _95923 _95924) = (term1163 A B _95921 _95922 _95923 _95924).
Proof. exact (MK_COMB (@lem7167486 B _95921 _95924) (@lem7167489 A B _95922 _95923 _95924)). Qed.
Lemma lem7167491 {A B : Type'} (_95921 : B -> Prop) (_95922 : type1413 A B) (_95923 : A) (_95924 : B) : (term1159 A B _95921 _95922 _95923 _95924) = (term1163 A B _95921 _95922 _95923 _95924).
Proof. exact (TRANS (@lem7167481 A B _95921 _95922 _95923 _95924) (@lem7167490 A B _95921 _95922 _95923 _95924)). Qed.
Lemma lem7167492 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7167493 {A B : Type'} (_95921 : B -> Prop) (_95922 : type1413 A B) (_95923 : A) (_95924 : B) : (term1164 A B _95921 _95922 _95923 _95924) = (term1165 A B _95921 _95922 _95923 _95924).
Proof. exact (MK_COMB (@lem7167492) (@lem7167491 A B _95921 _95922 _95923 _95924)). Qed.
Lemma lem7167494 {A B : Type'} (_95913 : type830 A B) (_95921 : B -> Prop) (_95922 : type1413 A B) (_95923 : A) : (term960 A B _95913 _95921 _95922 _95923) = (term960 A B _95913 _95921 _95922 _95923).
Proof. exact (eq_refl (term960 A B _95913 _95921 _95922 _95923)). Qed.
Lemma lem7167495 {A B : Type'} (_95924 : B) (_95913 : type830 A B) (_95921 : B -> Prop) (_95922 : type1413 A B) (_95923 : A) : (term1158 A B _95924 _95913 _95921 _95922 _95923) = (term1166 A B _95924 _95913 _95921 _95922 _95923).
Proof. exact (MK_COMB (@lem7167493 A B _95921 _95922 _95923 _95924) (@lem7167494 A B _95913 _95921 _95922 _95923)). Qed.
Lemma lem7167496 {A B : Type'} (_95924 : B) (_95913 : type830 A B) (_95921 : B -> Prop) (_95922 : type1413 A B) (_95923 : A) : (term1155 A B _95913 _95921 _95922 _95923 _95924) = (term1166 A B _95924 _95913 _95921 _95922 _95923).
Proof. exact (TRANS (@lem7167478 A B _95924 _95913 _95921 _95922 _95923) (@lem7167495 A B _95924 _95913 _95921 _95922 _95923)). Qed.
Lemma lem7167498 {A B : Type'} (y : A -> B) (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term940 A B x y t R s) (h2 : term987 A B s _95913 t R x' x) : term1163 A B t R x' x.
Proof. exact (conj (@lem7167396 A B x y t R s h1) (@lem7167403 A B s _95913 t R x' x h2)). Qed.
Lemma lem7167500 {A B : Type'} (_95924 : B) (_95921 : B -> Prop) (_95922 : type1413 A B) (_95923 : A) (_95913 : type830 A B) (h1 : term728 A B _95913) : term1166 A B _95924 _95913 _95921 _95922 _95923.
Proof. exact (EQ_MP (@lem7167496 A B _95924 _95913 _95921 _95922 _95923) (@lem7167475 A B _95921 _95922 _95923 _95924 _95913 h1)). Qed.
Lemma lem7167501 {A B : Type'} (_95924 : B) (_95921 : B -> Prop) (_95922 : type1413 A B) (_95923 : A) (_95913 : type830 A B) (h1 : term728 A B _95913) : term1166 A B _95924 _95913 _95921 _95922 _95923.
Proof. exact (@lem7167500 A B _95924 _95921 _95922 _95923 _95913 h1). Qed.
Lemma lem7167502 {A B : Type'} (x : B) (t : B -> Prop) (R : type1413 A B) (x' : A) (_95913 : type830 A B) (h1 : term728 A B _95913) : term1166 A B x _95913 t R x'.
Proof. exact (@lem7167501 A B x t R x' _95913 h1). Qed.
Lemma lem7167505 {A B : Type'} (y : A -> B) (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _95913) (h2 : term940 A B x y t R s) (h3 : term987 A B s _95913 t R x' x) : term960 A B _95913 t R x'.
Proof. exact (@lem7167502 A B x t R x' _95913 h1 (@lem7167498 A B y s _95913 t R x' x h2 h3)). Qed.
Lemma lem7167506 {A B : Type'} (y : A -> B) (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _95913) (h2 : term940 A B x y t R s) (h3 : term987 A B s _95913 t R x' x) : term1167 A B _95913 t R x'.
Proof. exact (fun h0 : term1168 A B _95913 t R x' => @lem7167505 A B y s _95913 t R x' x h1 h2 h3). Qed.
Lemma lem7167508 (p : Prop) : (term551 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7167509 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) : (term1167 A B _95913 t R x') = (term960 A B _95913 t R x').
Proof. exact (@lem7167508 (term960 A B _95913 t R x')). Qed.
Lemma lem7167510 {A B : Type'} (y : A -> B) (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _95913) (h2 : term940 A B x y t R s) (h3 : term987 A B s _95913 t R x' x) : term960 A B _95913 t R x'.
Proof. exact (EQ_MP (@lem7167509 A B _95913 t R x') (@lem7167506 A B y s _95913 t R x' x h1 h2 h3)). Qed.
Lemma lem7167512 {A B : Type'} (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : @I (B -> Prop) t x.
Proof. exact (proj1 (@lem7165294 A B x y t R s h1)). Qed.
Lemma lem7167513 {A B : Type'} (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1149 B t x.
Proof. exact (fun h0 : term963 B t x => @lem7167512 A B x y t R s h1). Qed.
Lemma lem7167515 (p : Prop) : (term551 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7167516 {B : Type'} (t : B -> Prop) (x : B) : (term1149 B t x) = (@I (B -> Prop) t x).
Proof. exact (@lem7167515 (@I (B -> Prop) t x)). Qed.
Lemma lem7167517 {A B : Type'} (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : @I (B -> Prop) t x.
Proof. exact (EQ_MP (@lem7167516 B t x) (@lem7167513 A B x y t R s h1)). Qed.
Lemma lem7167519 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term987 A B s _95913 t R x' x) : term378 A B R x' x.
Proof. exact (proj2 (@lem7165302 A B s _95913 t R x' x h1)). Qed.
Lemma lem7167520 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term987 A B s _95913 t R x' x) : term1151 A B R x' x.
Proof. exact (fun h0 : term380 A B R x' x => @lem7167519 A B s _95913 t R x' x h1). Qed.
Lemma lem7167522 (p : Prop) : (term551 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7167523 {A B : Type'} (R : type1413 A B) (x' : A) (x : B) : (term1151 A B R x' x) = (term378 A B R x' x).
Proof. exact (@lem7167522 (term378 A B R x' x)). Qed.
Lemma lem7167524 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term987 A B s _95913 t R x' x) : term378 A B R x' x.
Proof. exact (EQ_MP (@lem7167523 A B R x' x) (@lem7167520 A B s _95913 t R x' x h1)). Qed.
Lemma lem7167540 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7167541 {A B : Type'} (_95913 : type830 A B) (_95921 : B -> Prop) (_95922 : type1413 A B) (_95923 : A) (_95924 : B) : (term1169 A B _95924 _95913 _95921 _95922 _95923) = (term1170 A B _95913 _95921 _95922 _95923 _95924).
Proof. exact (@lem7167540 (term370 A B _95913 _95921 _95922 _95923) (term380 A B _95922 _95923 _95924)). Qed.
Lemma lem7167547 {B : Type'} (_95921 : B -> Prop) (_95924 : B) : (term964 B _95921 _95924) = (term964 B _95921 _95924).
Proof. exact (eq_refl (term964 B _95921 _95924)). Qed.
Lemma lem7167548 {A B : Type'} (_95913 : type830 A B) (_95921 : B -> Prop) (_95922 : type1413 A B) (_95923 : A) (_95924 : B) : (term1140 A B _95924 _95913 _95921 _95922 _95923) = (term1171 A B _95913 _95921 _95922 _95923 _95924).
Proof. exact (MK_COMB (@lem7167547 B _95921 _95924) (@lem7167541 A B _95913 _95921 _95922 _95923 _95924)). Qed.
Lemma lem7167552 (q : Prop) (p : Prop) (r : Prop) : (term21 p q r) = (term21 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7167553 {A B : Type'} (_95913 : type830 A B) (_95921 : B -> Prop) (_95922 : type1413 A B) (_95923 : A) (_95924 : B) : (term1171 A B _95913 _95921 _95922 _95923 _95924) = (term1172 A B _95913 _95921 _95922 _95923 _95924).
Proof. exact (@lem7167552 (term370 A B _95913 _95921 _95922 _95923) (term963 B _95921 _95924) (term380 A B _95922 _95923 _95924)). Qed.
Lemma lem7167569 {A B : Type'} (_95913 : type830 A B) (_95921 : B -> Prop) (_95922 : type1413 A B) (_95923 : A) (_95924 : B) : (term1140 A B _95924 _95913 _95921 _95922 _95923) = (term1172 A B _95913 _95921 _95922 _95923 _95924).
Proof. exact (TRANS (@lem7167548 A B _95913 _95921 _95922 _95923 _95924) (@lem7167553 A B _95913 _95921 _95922 _95923 _95924)). Qed.
Lemma lem7167570 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7167571 {A B : Type'} (_95913 : type830 A B) (_95921 : B -> Prop) (_95922 : type1413 A B) (_95923 : A) (_95924 : B) : (term1173 A B _95924 _95913 _95921 _95922 _95923) = (term1174 A B _95913 _95921 _95922 _95923 _95924).
Proof. exact (MK_COMB (@lem7167570) (@lem7167569 A B _95913 _95921 _95922 _95923 _95924)). Qed.
Lemma lem7167587 {A B : Type'} (_95913 : type830 A B) (_95921 : B -> Prop) (_95922 : type1413 A B) (_95923 : A) (_95924 : B) : (term1172 A B _95913 _95921 _95922 _95923 _95924) = (term1172 A B _95913 _95921 _95922 _95923 _95924).
Proof. exact (eq_refl (term1172 A B _95913 _95921 _95922 _95923 _95924)). Qed.
Lemma lem7167588 {A B : Type'} (_95913 : type830 A B) (_95921 : B -> Prop) (_95922 : type1413 A B) (_95923 : A) (_95924 : B) : ((term1140 A B _95924 _95913 _95921 _95922 _95923) = (term1172 A B _95913 _95921 _95922 _95923 _95924)) = ((term1172 A B _95913 _95921 _95922 _95923 _95924) = (term1172 A B _95913 _95921 _95922 _95923 _95924)).
Proof. exact (MK_COMB (@lem7167571 A B _95913 _95921 _95922 _95923 _95924) (@lem7167587 A B _95913 _95921 _95922 _95923 _95924)). Qed.
Lemma lem7167590 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7167591 (x : Prop) : (x = x) = True.
Proof. exact (@lem7167590 Prop x). Qed.
Lemma lem7167592 {A B : Type'} (_95913 : type830 A B) (_95921 : B -> Prop) (_95922 : type1413 A B) (_95923 : A) (_95924 : B) : ((term1172 A B _95913 _95921 _95922 _95923 _95924) = (term1172 A B _95913 _95921 _95922 _95923 _95924)) = True.
Proof. exact (@lem7167591 (term1172 A B _95913 _95921 _95922 _95923 _95924)). Qed.
Lemma lem7167593 {A B : Type'} (_95913 : type830 A B) (_95921 : B -> Prop) (_95922 : type1413 A B) (_95923 : A) (_95924 : B) : ((term1140 A B _95924 _95913 _95921 _95922 _95923) = (term1172 A B _95913 _95921 _95922 _95923 _95924)) = True.
Proof. exact (TRANS (@lem7167588 A B _95913 _95921 _95922 _95923 _95924) (@lem7167592 A B _95913 _95921 _95922 _95923 _95924)). Qed.
Lemma lem7167594 {A B : Type'} (_95913 : type830 A B) (_95921 : B -> Prop) (_95922 : type1413 A B) (_95923 : A) (_95924 : B) : True = ((term1140 A B _95924 _95913 _95921 _95922 _95923) = (term1172 A B _95913 _95921 _95922 _95923 _95924)).
Proof. exact (SYM (@lem7167593 A B _95913 _95921 _95922 _95923 _95924)). Qed.
Lemma lem7167595 {A B : Type'} (_95913 : type830 A B) (_95921 : B -> Prop) (_95922 : type1413 A B) (_95923 : A) (_95924 : B) : (term1140 A B _95924 _95913 _95921 _95922 _95923) = (term1172 A B _95913 _95921 _95922 _95923 _95924).
Proof. exact (EQ_MP (@lem7167594 A B _95913 _95921 _95922 _95923 _95924) (@lem0)). Qed.
Lemma lem7167596 {A B : Type'} (_95921 : B -> Prop) (_95922 : type1413 A B) (_95923 : A) (_95924 : B) (_95913 : type830 A B) (h1 : term728 A B _95913) : term1172 A B _95913 _95921 _95922 _95923 _95924.
Proof. exact (EQ_MP (@lem7167595 A B _95913 _95921 _95922 _95923 _95924) (@lem7166652 A B _95924 _95921 _95922 _95923 _95913 h1)). Qed.
Lemma lem7167598 (b : Prop) (a : Prop) : (a \/ b) = (term555 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7167599 {A B : Type'} (_95924 : B) (_95913 : type830 A B) (_95921 : B -> Prop) (_95922 : type1413 A B) (_95923 : A) : (term1172 A B _95913 _95921 _95922 _95923 _95924) = (term1175 A B _95924 _95913 _95921 _95922 _95923).
Proof. exact (@lem7167598 (term965 A B _95921 _95922 _95923 _95924) (term370 A B _95913 _95921 _95922 _95923)). Qed.
Lemma lem7167601 (a : Prop) (b : Prop) : (term582 a b) = (term583 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7167602 {A B : Type'} (_95921 : B -> Prop) (_95922 : type1413 A B) (_95923 : A) (_95924 : B) : (term1159 A B _95921 _95922 _95923 _95924) = (term1160 A B _95921 _95922 _95923 _95924).
Proof. exact (@lem7167601 (term963 B _95921 _95924) (term380 A B _95922 _95923 _95924)). Qed.
Lemma lem7167604 (a : Prop) : (term203 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7167605 {B : Type'} (_95921 : B -> Prop) (_95924 : B) : (term1161 B _95921 _95924) = (@I (B -> Prop) _95921 _95924).
Proof. exact (@lem7167604 (@I (B -> Prop) _95921 _95924)). Qed.
Lemma lem7167606 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7167607 {B : Type'} (_95921 : B -> Prop) (_95924 : B) : (term1162 B _95921 _95924) = (term977 B _95921 _95924).
Proof. exact (MK_COMB (@lem7167606) (@lem7167605 B _95921 _95924)). Qed.
Lemma lem7167609 (a : Prop) : (term203 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7167610 {A B : Type'} (_95922 : type1413 A B) (_95923 : A) (_95924 : B) : (term588 A B _95922 _95923 _95924) = (term378 A B _95922 _95923 _95924).
Proof. exact (@lem7167609 (term378 A B _95922 _95923 _95924)). Qed.
Lemma lem7167611 {A B : Type'} (_95921 : B -> Prop) (_95922 : type1413 A B) (_95923 : A) (_95924 : B) : (term1160 A B _95921 _95922 _95923 _95924) = (term1163 A B _95921 _95922 _95923 _95924).
Proof. exact (MK_COMB (@lem7167607 B _95921 _95924) (@lem7167610 A B _95922 _95923 _95924)). Qed.
Lemma lem7167612 {A B : Type'} (_95921 : B -> Prop) (_95922 : type1413 A B) (_95923 : A) (_95924 : B) : (term1159 A B _95921 _95922 _95923 _95924) = (term1163 A B _95921 _95922 _95923 _95924).
Proof. exact (TRANS (@lem7167602 A B _95921 _95922 _95923 _95924) (@lem7167611 A B _95921 _95922 _95923 _95924)). Qed.
Lemma lem7167613 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7167614 {A B : Type'} (_95921 : B -> Prop) (_95922 : type1413 A B) (_95923 : A) (_95924 : B) : (term1164 A B _95921 _95922 _95923 _95924) = (term1165 A B _95921 _95922 _95923 _95924).
Proof. exact (MK_COMB (@lem7167613) (@lem7167612 A B _95921 _95922 _95923 _95924)). Qed.
Lemma lem7167615 {A B : Type'} (_95913 : type830 A B) (_95921 : B -> Prop) (_95922 : type1413 A B) (_95923 : A) : (term370 A B _95913 _95921 _95922 _95923) = (term370 A B _95913 _95921 _95922 _95923).
Proof. exact (eq_refl (term370 A B _95913 _95921 _95922 _95923)). Qed.
Lemma lem7167616 {A B : Type'} (_95924 : B) (_95913 : type830 A B) (_95921 : B -> Prop) (_95922 : type1413 A B) (_95923 : A) : (term1175 A B _95924 _95913 _95921 _95922 _95923) = (term1176 A B _95924 _95913 _95921 _95922 _95923).
Proof. exact (MK_COMB (@lem7167614 A B _95921 _95922 _95923 _95924) (@lem7167615 A B _95913 _95921 _95922 _95923)). Qed.
Lemma lem7167617 {A B : Type'} (_95924 : B) (_95913 : type830 A B) (_95921 : B -> Prop) (_95922 : type1413 A B) (_95923 : A) : (term1172 A B _95913 _95921 _95922 _95923 _95924) = (term1176 A B _95924 _95913 _95921 _95922 _95923).
Proof. exact (TRANS (@lem7167599 A B _95924 _95913 _95921 _95922 _95923) (@lem7167616 A B _95924 _95913 _95921 _95922 _95923)). Qed.
Lemma lem7167619 {A B : Type'} (y : A -> B) (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term940 A B x y t R s) (h2 : term987 A B s _95913 t R x' x) : term1163 A B t R x' x.
Proof. exact (conj (@lem7167517 A B x y t R s h1) (@lem7167524 A B s _95913 t R x' x h2)). Qed.
Lemma lem7167621 {A B : Type'} (_95924 : B) (_95921 : B -> Prop) (_95922 : type1413 A B) (_95923 : A) (_95913 : type830 A B) (h1 : term728 A B _95913) : term1176 A B _95924 _95913 _95921 _95922 _95923.
Proof. exact (EQ_MP (@lem7167617 A B _95924 _95913 _95921 _95922 _95923) (@lem7167596 A B _95921 _95922 _95923 _95924 _95913 h1)). Qed.
Lemma lem7167622 {A B : Type'} (_95924 : B) (_95921 : B -> Prop) (_95922 : type1413 A B) (_95923 : A) (_95913 : type830 A B) (h1 : term728 A B _95913) : term1176 A B _95924 _95913 _95921 _95922 _95923.
Proof. exact (@lem7167621 A B _95924 _95921 _95922 _95923 _95913 h1). Qed.
Lemma lem7167623 {A B : Type'} (x : B) (t : B -> Prop) (R : type1413 A B) (x' : A) (_95913 : type830 A B) (h1 : term728 A B _95913) : term1176 A B x _95913 t R x'.
Proof. exact (@lem7167622 A B x t R x' _95913 h1). Qed.
Lemma lem7167626 {A B : Type'} (y : A -> B) (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _95913) (h2 : term940 A B x y t R s) (h3 : term987 A B s _95913 t R x' x) : term370 A B _95913 t R x'.
Proof. exact (@lem7167623 A B x t R x' _95913 h1 (@lem7167619 A B y s _95913 t R x' x h2 h3)). Qed.
Lemma lem7167627 {A B : Type'} (y : A -> B) (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _95913) (h2 : term940 A B x y t R s) (h3 : term987 A B s _95913 t R x' x) : term1177 A B _95913 t R x'.
Proof. exact (fun h0 : term1144 A B _95913 t R x' => @lem7167626 A B y s _95913 t R x' x h1 h2 h3). Qed.
Lemma lem7167629 (p : Prop) : (term551 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7167630 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) : (term1177 A B _95913 t R x') = (term370 A B _95913 t R x').
Proof. exact (@lem7167629 (term370 A B _95913 t R x')). Qed.
Lemma lem7167631 {A B : Type'} (y : A -> B) (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _95913) (h2 : term940 A B x y t R s) (h3 : term987 A B s _95913 t R x' x) : term370 A B _95913 t R x'.
Proof. exact (EQ_MP (@lem7167630 A B _95913 t R x') (@lem7167627 A B y s _95913 t R x' x h1 h2 h3)). Qed.
Lemma lem7167657 (q : Prop) (p : Prop) (r : Prop) : (term21 p q r) = (term21 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7167658 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (_95925 : A) (_95927 : B) (_95926 : B) : (term1178 A B t R _95925 _95927 _95926) = (term1179 A B t R _95925 _95927 _95926).
Proof. exact (@lem7167657 (term963 B t _95927) (term380 A B R _95925 _95926) (term1180 A B R _95925 _95927 _95926)). Qed.
Lemma lem7167682 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7167683 {A B : Type'} (_95926 : B) (R : type1413 A B) (_95925 : A) (_95927 : B) : (term1180 A B R _95925 _95927 _95926) = (term1181 A B _95926 R _95925 _95927).
Proof. exact (@lem7167682 (_95927 = _95926) (term380 A B R _95925 _95927)). Qed.
Lemma lem7167691 {A B : Type'} (R : type1413 A B) (_95925 : A) (_95926 : B) : (term573 A B R _95925 _95926) = (term573 A B R _95925 _95926).
Proof. exact (eq_refl (term573 A B R _95925 _95926)). Qed.
Lemma lem7167692 {A B : Type'} (_95926 : B) (R : type1413 A B) (_95925 : A) (_95927 : B) : (term1182 A B R _95925 _95927 _95926) = (term1183 A B _95926 R _95925 _95927).
Proof. exact (MK_COMB (@lem7167691 A B R _95925 _95926) (@lem7167683 A B _95926 R _95925 _95927)). Qed.
Lemma lem7167696 (q : Prop) (p : Prop) (r : Prop) : (term21 p q r) = (term21 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7167697 {A B : Type'} (_95926 : B) (R : type1413 A B) (_95925 : A) (_95927 : B) : (term1183 A B _95926 R _95925 _95927) = (term1184 A B _95926 R _95925 _95927).
Proof. exact (@lem7167696 (_95927 = _95926) (term380 A B R _95925 _95926) (term380 A B R _95925 _95927)). Qed.
Lemma lem7167715 {A B : Type'} (_95926 : B) (R : type1413 A B) (_95925 : A) (_95927 : B) : (term1182 A B R _95925 _95927 _95926) = (term1184 A B _95926 R _95925 _95927).
Proof. exact (TRANS (@lem7167692 A B _95926 R _95925 _95927) (@lem7167697 A B _95926 R _95925 _95927)). Qed.
Lemma lem7167716 {B : Type'} (t : B -> Prop) (_95927 : B) : (term964 B t _95927) = (term964 B t _95927).
Proof. exact (eq_refl (term964 B t _95927)). Qed.
Lemma lem7167717 {A B : Type'} (t : B -> Prop) (_95926 : B) (R : type1413 A B) (_95925 : A) (_95927 : B) : (term1179 A B t R _95925 _95927 _95926) = (term1185 A B t _95926 R _95925 _95927).
Proof. exact (MK_COMB (@lem7167716 B t _95927) (@lem7167715 A B _95926 R _95925 _95927)). Qed.
Lemma lem7167721 (q : Prop) (p : Prop) (r : Prop) : (term21 p q r) = (term21 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7167722 {A B : Type'} (t : B -> Prop) (_95926 : B) (R : type1413 A B) (_95925 : A) (_95927 : B) : (term1185 A B t _95926 R _95925 _95927) = (term1186 A B t _95926 R _95925 _95927).
Proof. exact (@lem7167721 (_95927 = _95926) (term963 B t _95927) (term1187 A B _95926 R _95925 _95927)). Qed.
Lemma lem7167750 {A B : Type'} (t : B -> Prop) (_95926 : B) (R : type1413 A B) (_95925 : A) (_95927 : B) : (term1179 A B t R _95925 _95927 _95926) = (term1186 A B t _95926 R _95925 _95927).
Proof. exact (TRANS (@lem7167717 A B t _95926 R _95925 _95927) (@lem7167722 A B t _95926 R _95925 _95927)). Qed.
Lemma lem7167751 {A B : Type'} (t : B -> Prop) (_95926 : B) (R : type1413 A B) (_95925 : A) (_95927 : B) : (term1178 A B t R _95925 _95927 _95926) = (term1186 A B t _95926 R _95925 _95927).
Proof. exact (TRANS (@lem7167658 A B t R _95925 _95927 _95926) (@lem7167750 A B t _95926 R _95925 _95927)). Qed.
Lemma lem7167752 {B : Type'} (t : B -> Prop) (_95926 : B) : (term964 B t _95926) = (term964 B t _95926).
Proof. exact (eq_refl (term964 B t _95926)). Qed.
Lemma lem7167753 {A B : Type'} (t : B -> Prop) (_95926 : B) (R : type1413 A B) (_95925 : A) (_95927 : B) : (term1137 A B t R _95925 _95927 _95926) = (term1188 A B t _95926 R _95925 _95927).
Proof. exact (MK_COMB (@lem7167752 B t _95926) (@lem7167751 A B t _95926 R _95925 _95927)). Qed.
Lemma lem7167757 (q : Prop) (p : Prop) (r : Prop) : (term21 p q r) = (term21 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7167758 {A B : Type'} (t : B -> Prop) (_95926 : B) (R : type1413 A B) (_95925 : A) (_95927 : B) : (term1188 A B t _95926 R _95925 _95927) = (term1189 A B t _95926 R _95925 _95927).
Proof. exact (@lem7167757 (_95927 = _95926) (term963 B t _95926) (term1190 A B t _95926 R _95925 _95927)). Qed.
Lemma lem7167796 {A B : Type'} (t : B -> Prop) (_95926 : B) (R : type1413 A B) (_95925 : A) (_95927 : B) : (term1137 A B t R _95925 _95927 _95926) = (term1189 A B t _95926 R _95925 _95927).
Proof. exact (TRANS (@lem7167753 A B t _95926 R _95925 _95927) (@lem7167758 A B t _95926 R _95925 _95927)). Qed.
Lemma lem7167797 {A : Type'} (s : A -> Prop) (_95925 : A) : (term964 A s _95925) = (term964 A s _95925).
Proof. exact (eq_refl (term964 A s _95925)). Qed.
Lemma lem7167798 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (_95926 : B) (R : type1413 A B) (_95925 : A) (_95927 : B) : (term1138 A B s t R _95925 _95927 _95926) = (term1191 A B s t _95926 R _95925 _95927).
Proof. exact (MK_COMB (@lem7167797 A s _95925) (@lem7167796 A B t _95926 R _95925 _95927)). Qed.
Lemma lem7167802 (q : Prop) (p : Prop) (r : Prop) : (term21 p q r) = (term21 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7167803 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (_95926 : B) (R : type1413 A B) (_95925 : A) (_95927 : B) : (term1191 A B s t _95926 R _95925 _95927) = (term1192 A B s t _95926 R _95925 _95927).
Proof. exact (@lem7167802 (_95927 = _95926) (term963 A s _95925) (term1193 A B t _95926 R _95925 _95927)). Qed.
Lemma lem7167851 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (_95926 : B) (R : type1413 A B) (_95925 : A) (_95927 : B) : (term1138 A B s t R _95925 _95927 _95926) = (term1192 A B s t _95926 R _95925 _95927).
Proof. exact (TRANS (@lem7167798 A B s t _95926 R _95925 _95927) (@lem7167803 A B s t _95926 R _95925 _95927)). Qed.
Lemma lem7167852 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7167853 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (_95926 : B) (R : type1413 A B) (_95925 : A) (_95927 : B) : (term1194 A B s t R _95925 _95927 _95926) = (term1195 A B s t _95926 R _95925 _95927).
Proof. exact (MK_COMB (@lem7167852) (@lem7167851 A B s t _95926 R _95925 _95927)). Qed.
Lemma lem7167889 (q : Prop) (p : Prop) (r : Prop) : (term21 p q r) = (term21 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7167890 {A B : Type'} (t : B -> Prop) (_95926 : B) (R : type1413 A B) (_95925 : A) (_95927 : B) : (term1196 A B _95926 t R _95925 _95927) = (term1190 A B t _95926 R _95925 _95927).
Proof. exact (@lem7167889 (term963 B t _95927) (term380 A B R _95925 _95926) (term380 A B R _95925 _95927)). Qed.
Lemma lem7167906 {B : Type'} (t : B -> Prop) (_95926 : B) : (term964 B t _95926) = (term964 B t _95926).
Proof. exact (eq_refl (term964 B t _95926)). Qed.
Lemma lem7167907 {A B : Type'} (t : B -> Prop) (_95926 : B) (R : type1413 A B) (_95925 : A) (_95927 : B) : (term1197 A B _95926 t R _95925 _95927) = (term1193 A B t _95926 R _95925 _95927).
Proof. exact (MK_COMB (@lem7167906 B t _95926) (@lem7167890 A B t _95926 R _95925 _95927)). Qed.
Lemma lem7167918 {A : Type'} (s : A -> Prop) (_95925 : A) : (term964 A s _95925) = (term964 A s _95925).
Proof. exact (eq_refl (term964 A s _95925)). Qed.
Lemma lem7167919 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (_95926 : B) (R : type1413 A B) (_95925 : A) (_95927 : B) : (term1198 A B s _95926 t R _95925 _95927) = (term1199 A B s t _95926 R _95925 _95927).
Proof. exact (MK_COMB (@lem7167918 A s _95925) (@lem7167907 A B t _95926 R _95925 _95927)). Qed.
Lemma lem7167930 {B : Type'} (_95927 : B) (_95926 : B) : (term1200 B _95927 _95926) = (term1200 B _95927 _95926).
Proof. exact (eq_refl (term1200 B _95927 _95926)). Qed.
Lemma lem7167931 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (_95926 : B) (R : type1413 A B) (_95925 : A) (_95927 : B) : (term1201 A B s _95926 t R _95925 _95927) = (term1192 A B s t _95926 R _95925 _95927).
Proof. exact (MK_COMB (@lem7167930 B _95927 _95926) (@lem7167919 A B s t _95926 R _95925 _95927)). Qed.
Lemma lem7167942 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (_95926 : B) (R : type1413 A B) (_95925 : A) (_95927 : B) : ((term1138 A B s t R _95925 _95927 _95926) = (term1201 A B s _95926 t R _95925 _95927)) = ((term1192 A B s t _95926 R _95925 _95927) = (term1192 A B s t _95926 R _95925 _95927)).
Proof. exact (MK_COMB (@lem7167853 A B s t _95926 R _95925 _95927) (@lem7167931 A B s t _95926 R _95925 _95927)). Qed.
Lemma lem7167944 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7167945 (x : Prop) : (x = x) = True.
Proof. exact (@lem7167944 Prop x). Qed.
Lemma lem7167946 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (_95926 : B) (R : type1413 A B) (_95925 : A) (_95927 : B) : ((term1192 A B s t _95926 R _95925 _95927) = (term1192 A B s t _95926 R _95925 _95927)) = True.
Proof. exact (@lem7167945 (term1192 A B s t _95926 R _95925 _95927)). Qed.
Lemma lem7167947 {A B : Type'} (s : A -> Prop) (_95926 : B) (t : B -> Prop) (R : type1413 A B) (_95925 : A) (_95927 : B) : ((term1138 A B s t R _95925 _95927 _95926) = (term1201 A B s _95926 t R _95925 _95927)) = True.
Proof. exact (TRANS (@lem7167942 A B s t _95926 R _95925 _95927) (@lem7167946 A B s t _95926 R _95925 _95927)). Qed.
Lemma lem7167948 {A B : Type'} (s : A -> Prop) (_95926 : B) (t : B -> Prop) (R : type1413 A B) (_95925 : A) (_95927 : B) : True = ((term1138 A B s t R _95925 _95927 _95926) = (term1201 A B s _95926 t R _95925 _95927)).
Proof. exact (SYM (@lem7167947 A B s _95926 t R _95925 _95927)). Qed.
Lemma lem7167949 {A B : Type'} (s : A -> Prop) (_95926 : B) (t : B -> Prop) (R : type1413 A B) (_95925 : A) (_95927 : B) : (term1138 A B s t R _95925 _95927 _95926) = (term1201 A B s _95926 t R _95925 _95927).
Proof. exact (EQ_MP (@lem7167948 A B s _95926 t R _95925 _95927) (@lem0)). Qed.
Lemma lem7167950 {A B : Type'} (_95926 : B) (_95925 : A) (_95927 : B) (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1201 A B s _95926 t R _95925 _95927.
Proof. exact (EQ_MP (@lem7167949 A B s _95926 t R _95925 _95927) (@lem7166616 A B _95925 _95927 _95926 x y t R s h1)). Qed.
Lemma lem7167952 (b : Prop) (a : Prop) : (a \/ b) = (term555 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7167953 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (_95925 : A) (_95927 : B) (_95926 : B) : (term1201 A B s _95926 t R _95925 _95927) = (term1202 A B s t R _95925 _95927 _95926).
Proof. exact (@lem7167952 (term1198 A B s _95926 t R _95925 _95927) (_95927 = _95926)). Qed.
Lemma lem7167955 (a : Prop) (b : Prop) : (term582 a b) = (term583 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7167956 {A B : Type'} (s : A -> Prop) (_95926 : B) (t : B -> Prop) (R : type1413 A B) (_95925 : A) (_95927 : B) : (term1203 A B s _95926 t R _95925 _95927) = (term1204 A B s _95926 t R _95925 _95927).
Proof. exact (@lem7167955 (term963 A s _95925) (term1197 A B _95926 t R _95925 _95927)). Qed.
Lemma lem7167958 (a : Prop) : (term203 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7167959 {A : Type'} (s : A -> Prop) (_95925 : A) : (term1161 A s _95925) = (@I (A -> Prop) s _95925).
Proof. exact (@lem7167958 (@I (A -> Prop) s _95925)). Qed.
Lemma lem7167960 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7167961 {A : Type'} (s : A -> Prop) (_95925 : A) : (term1162 A s _95925) = (term977 A s _95925).
Proof. exact (MK_COMB (@lem7167960) (@lem7167959 A s _95925)). Qed.
Lemma lem7167963 (a : Prop) (b : Prop) : (term582 a b) = (term583 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7167964 {A B : Type'} (_95926 : B) (t : B -> Prop) (R : type1413 A B) (_95925 : A) (_95927 : B) : (term1205 A B _95926 t R _95925 _95927) = (term1206 A B _95926 t R _95925 _95927).
Proof. exact (@lem7167963 (term963 B t _95926) (term1196 A B _95926 t R _95925 _95927)). Qed.
Lemma lem7167966 (a : Prop) : (term203 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7167967 {B : Type'} (t : B -> Prop) (_95926 : B) : (term1161 B t _95926) = (@I (B -> Prop) t _95926).
Proof. exact (@lem7167966 (@I (B -> Prop) t _95926)). Qed.
Lemma lem7167968 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7167969 {B : Type'} (t : B -> Prop) (_95926 : B) : (term1162 B t _95926) = (term977 B t _95926).
Proof. exact (MK_COMB (@lem7167968) (@lem7167967 B t _95926)). Qed.
Lemma lem7167971 (a : Prop) (b : Prop) : (term582 a b) = (term583 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7167972 {A B : Type'} (_95926 : B) (t : B -> Prop) (R : type1413 A B) (_95925 : A) (_95927 : B) : (term1207 A B _95926 t R _95925 _95927) = (term1208 A B _95926 t R _95925 _95927).
Proof. exact (@lem7167971 (term380 A B R _95925 _95926) (term965 A B t R _95925 _95927)). Qed.
Lemma lem7167974 (a : Prop) : (term203 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7167975 {A B : Type'} (R : type1413 A B) (_95925 : A) (_95926 : B) : (term588 A B R _95925 _95926) = (term378 A B R _95925 _95926).
Proof. exact (@lem7167974 (term378 A B R _95925 _95926)). Qed.
Lemma lem7167976 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7167977 {A B : Type'} (R : type1413 A B) (_95925 : A) (_95926 : B) : (term1209 A B R _95925 _95926) = (term1210 A B R _95925 _95926).
Proof. exact (MK_COMB (@lem7167976) (@lem7167975 A B R _95925 _95926)). Qed.
Lemma lem7167979 (a : Prop) (b : Prop) : (term582 a b) = (term583 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7167980 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (_95925 : A) (_95927 : B) : (term1159 A B t R _95925 _95927) = (term1160 A B t R _95925 _95927).
Proof. exact (@lem7167979 (term963 B t _95927) (term380 A B R _95925 _95927)). Qed.
Lemma lem7167982 (a : Prop) : (term203 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7167983 {B : Type'} (t : B -> Prop) (_95927 : B) : (term1161 B t _95927) = (@I (B -> Prop) t _95927).
Proof. exact (@lem7167982 (@I (B -> Prop) t _95927)). Qed.
Lemma lem7167984 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7167985 {B : Type'} (t : B -> Prop) (_95927 : B) : (term1162 B t _95927) = (term977 B t _95927).
Proof. exact (MK_COMB (@lem7167984) (@lem7167983 B t _95927)). Qed.
Lemma lem7167987 (a : Prop) : (term203 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7167988 {A B : Type'} (R : type1413 A B) (_95925 : A) (_95927 : B) : (term588 A B R _95925 _95927) = (term378 A B R _95925 _95927).
Proof. exact (@lem7167987 (term378 A B R _95925 _95927)). Qed.
Lemma lem7167989 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (_95925 : A) (_95927 : B) : (term1160 A B t R _95925 _95927) = (term1163 A B t R _95925 _95927).
Proof. exact (MK_COMB (@lem7167985 B t _95927) (@lem7167988 A B R _95925 _95927)). Qed.
Lemma lem7167990 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (_95925 : A) (_95927 : B) : (term1159 A B t R _95925 _95927) = (term1163 A B t R _95925 _95927).
Proof. exact (TRANS (@lem7167980 A B t R _95925 _95927) (@lem7167989 A B t R _95925 _95927)). Qed.
Lemma lem7167991 {A B : Type'} (_95926 : B) (t : B -> Prop) (R : type1413 A B) (_95925 : A) (_95927 : B) : (term1208 A B _95926 t R _95925 _95927) = (term1211 A B _95926 t R _95925 _95927).
Proof. exact (MK_COMB (@lem7167977 A B R _95925 _95926) (@lem7167990 A B t R _95925 _95927)). Qed.
Lemma lem7167992 {A B : Type'} (_95926 : B) (t : B -> Prop) (R : type1413 A B) (_95925 : A) (_95927 : B) : (term1207 A B _95926 t R _95925 _95927) = (term1211 A B _95926 t R _95925 _95927).
Proof. exact (TRANS (@lem7167972 A B _95926 t R _95925 _95927) (@lem7167991 A B _95926 t R _95925 _95927)). Qed.
Lemma lem7167993 {A B : Type'} (_95926 : B) (t : B -> Prop) (R : type1413 A B) (_95925 : A) (_95927 : B) : (term1206 A B _95926 t R _95925 _95927) = (term1212 A B _95926 t R _95925 _95927).
Proof. exact (MK_COMB (@lem7167969 B t _95926) (@lem7167992 A B _95926 t R _95925 _95927)). Qed.
Lemma lem7167994 {A B : Type'} (_95926 : B) (t : B -> Prop) (R : type1413 A B) (_95925 : A) (_95927 : B) : (term1205 A B _95926 t R _95925 _95927) = (term1212 A B _95926 t R _95925 _95927).
Proof. exact (TRANS (@lem7167964 A B _95926 t R _95925 _95927) (@lem7167993 A B _95926 t R _95925 _95927)). Qed.
Lemma lem7167995 {A B : Type'} (s : A -> Prop) (_95926 : B) (t : B -> Prop) (R : type1413 A B) (_95925 : A) (_95927 : B) : (term1204 A B s _95926 t R _95925 _95927) = (term1213 A B s _95926 t R _95925 _95927).
Proof. exact (MK_COMB (@lem7167961 A s _95925) (@lem7167994 A B _95926 t R _95925 _95927)). Qed.
Lemma lem7167996 {A B : Type'} (s : A -> Prop) (_95926 : B) (t : B -> Prop) (R : type1413 A B) (_95925 : A) (_95927 : B) : (term1203 A B s _95926 t R _95925 _95927) = (term1213 A B s _95926 t R _95925 _95927).
Proof. exact (TRANS (@lem7167956 A B s _95926 t R _95925 _95927) (@lem7167995 A B s _95926 t R _95925 _95927)). Qed.
Lemma lem7167997 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7167998 {A B : Type'} (s : A -> Prop) (_95926 : B) (t : B -> Prop) (R : type1413 A B) (_95925 : A) (_95927 : B) : (term1214 A B s _95926 t R _95925 _95927) = (term1215 A B s _95926 t R _95925 _95927).
Proof. exact (MK_COMB (@lem7167997) (@lem7167996 A B s _95926 t R _95925 _95927)). Qed.
Lemma lem7167999 {B : Type'} (_95927 : B) (_95926 : B) : (_95927 = _95926) = (_95927 = _95926).
Proof. exact (eq_refl (_95927 = _95926)). Qed.
Lemma lem7168000 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (_95925 : A) (_95927 : B) (_95926 : B) : (term1202 A B s t R _95925 _95927 _95926) = (term1216 A B s t R _95925 _95927 _95926).
Proof. exact (MK_COMB (@lem7167998 A B s _95926 t R _95925 _95927) (@lem7167999 B _95927 _95926)). Qed.
Lemma lem7168001 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (_95925 : A) (_95927 : B) (_95926 : B) : (term1201 A B s _95926 t R _95925 _95927) = (term1216 A B s t R _95925 _95927 _95926).
Proof. exact (TRANS (@lem7167953 A B s t R _95925 _95927 _95926) (@lem7168000 A B s t R _95925 _95927 _95926)). Qed.
Lemma lem7168003 {A B : Type'} (y : A -> B) (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _95913) (h2 : term940 A B x y t R s) (h3 : term987 A B s _95913 t R x' x) : term962 A B _95913 t R x'.
Proof. exact (conj (@lem7167510 A B y s _95913 t R x' x h1 h2 h3) (@lem7167631 A B y s _95913 t R x' x h1 h2 h3)). Qed.
Lemma lem7168004 {A B : Type'} (y : A -> B) (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _95913) (h2 : term940 A B x y t R s) (h3 : term987 A B s _95913 t R x' x) : term1217 A B x _95913 t R x'.
Proof. exact (conj (@lem7167389 A B s _95913 t R x' x h3) (@lem7168003 A B y s _95913 t R x' x h1 h2 h3)). Qed.
Lemma lem7168005 {A B : Type'} (y : A -> B) (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _95913) (h2 : term940 A B x y t R s) (h3 : term987 A B s _95913 t R x' x) : term1218 A B x _95913 t R x'.
Proof. exact (conj (@lem7167382 A B x y t R s h2) (@lem7168004 A B y s _95913 t R x' x h1 h2 h3)). Qed.
Lemma lem7168006 {A B : Type'} (y : A -> B) (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _95913) (h2 : term940 A B x y t R s) (h3 : term987 A B s _95913 t R x' x) : term1219 A B s x _95913 t R x'.
Proof. exact (conj (@lem7167375 A B s _95913 t R x' x h3) (@lem7168005 A B y s _95913 t R x' x h1 h2 h3)). Qed.
Lemma lem7168008 {A B : Type'} (_95925 : A) (_95927 : B) (_95926 : B) (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1216 A B s t R _95925 _95927 _95926.
Proof. exact (EQ_MP (@lem7168001 A B s t R _95925 _95927 _95926) (@lem7167950 A B _95926 _95925 _95927 x y t R s h1)). Qed.
Lemma lem7168009 {A B : Type'} (_95925 : A) (_95927 : B) (_95926 : B) (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1216 A B s t R _95925 _95927 _95926.
Proof. exact (@lem7168008 A B _95925 _95927 _95926 x y t R s h1). Qed.
Lemma lem7168010 {A B : Type'} (_95913 : type830 A B) (x' : A) (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1220 A B s _95913 t R x' x.
Proof. exact (@lem7168009 A B x' (term367 A B _95913 t R x') x x y t R s h1). Qed.
Lemma lem7168013 {A B : Type'} (y : A -> B) (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _95913) (h2 : term940 A B x y t R s) (h3 : term987 A B s _95913 t R x' x) : (term367 A B _95913 t R x') = x.
Proof. exact (@lem7168010 A B _95913 x' x y t R s h2 (@lem7168006 A B y s _95913 t R x' x h1 h2 h3)). Qed.
Lemma lem7168014 {A B : Type'} (y : A -> B) (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _95913) (h2 : term940 A B x y t R s) (h3 : term987 A B s _95913 t R x' x) : term1221 A B _95913 t R x' x.
Proof. exact (fun h0 : term983 A B _95913 t R x' x => @lem7168013 A B y s _95913 t R x' x h1 h2 h3). Qed.
Lemma lem7168016 (p : Prop) : (term551 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7168017 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) : (term1221 A B _95913 t R x' x) = ((term367 A B _95913 t R x') = x).
Proof. exact (@lem7168016 ((term367 A B _95913 t R x') = x)). Qed.
Lemma lem7168018 {A B : Type'} (y : A -> B) (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _95913) (h2 : term940 A B x y t R s) (h3 : term987 A B s _95913 t R x' x) : (term367 A B _95913 t R x') = x.
Proof. exact (EQ_MP (@lem7168017 A B _95913 t R x' x) (@lem7168014 A B y s _95913 t R x' x h1 h2 h3)). Qed.
Lemma lem7168021 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7168023 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) : (term983 A B _95913 t R x' x) = (term1222 A B _95913 t R x' x).
Proof. exact (@lem7168021 ((term367 A B _95913 t R x') = x)). Qed.
Lemma lem7168026 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term983 A B _95913 t R x' x) : term1222 A B _95913 t R x' x.
Proof. exact (EQ_MP (@lem7168023 A B _95913 t R x' x) (@lem7166590 A B _95913 t R x' x h1)). Qed.
Lemma lem7168029 {A B : Type'} (y : A -> B) (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _95913) (h2 : term983 A B _95913 t R x' x) (h3 : term940 A B x y t R s) (h4 : term987 A B s _95913 t R x' x) : False.
Proof. exact (@lem7168026 A B _95913 t R x' x h2 (@lem7168018 A B y s _95913 t R x' x h1 h3 h4)). Qed.
Lemma lem7168030 {A B : Type'} (y : A -> B) (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _95913) (h2 : term983 A B _95913 t R x' x) (h3 : term940 A B x y t R s) (h4 : term987 A B s _95913 t R x' x) : term596.
Proof. exact (fun h0 : ~ False => @lem7168029 A B y s _95913 t R x' x h1 h2 h3 h4). Qed.
Lemma lem7168032 (p : Prop) : (term551 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7168033 : term596 = False.
Proof. exact (@lem7168032 False). Qed.
Lemma lem7168034 {A B : Type'} (y : A -> B) (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _95913) (h2 : term983 A B _95913 t R x' x) (h3 : term940 A B x y t R s) (h4 : term987 A B s _95913 t R x' x) : False.
Proof. exact (EQ_MP (@lem7168033) (@lem7168030 A B y s _95913 t R x' x h1 h2 h3 h4)). Qed.
Lemma lem7168171 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term981 A B s _95913 t R x' x) : @I (A -> Prop) s x'.
Proof. exact (proj1 (@lem7165307 A B s _95913 t R x' x h1)). Qed.
Lemma lem7168172 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term981 A B s _95913 t R x' x) : term1149 A s x'.
Proof. exact (fun h0 : term963 A s x' => @lem7168171 A B s _95913 t R x' x h1). Qed.
Lemma lem7168174 (p : Prop) : (term551 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7168175 {A : Type'} (s : A -> Prop) (x' : A) : (term1149 A s x') = (@I (A -> Prop) s x').
Proof. exact (@lem7168174 (@I (A -> Prop) s x')). Qed.
Lemma lem7168176 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term981 A B s _95913 t R x' x) : @I (A -> Prop) s x'.
Proof. exact (EQ_MP (@lem7168175 A s x') (@lem7168172 A B s _95913 t R x' x h1)). Qed.
Lemma lem7168179 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7168181 {A : Type'} (s : A -> Prop) (x' : A) : (term963 A s x') = (term1150 A s x').
Proof. exact (@lem7168179 (@I (A -> Prop) s x')). Qed.
Lemma lem7168184 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term963 A s x') : term1150 A s x'.
Proof. exact (EQ_MP (@lem7168181 A s x') (@lem7166866 A s x' h1)). Qed.
Lemma lem7168187 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term963 A s x') (h2 : term981 A B s _95913 t R x' x) : False.
Proof. exact (@lem7168184 A s x' h1 (@lem7168176 A B s _95913 t R x' x h2)). Qed.
Lemma lem7168188 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term963 A s x') (h2 : term981 A B s _95913 t R x' x) : term596.
Proof. exact (fun h0 : ~ False => @lem7168187 A B s _95913 t R x' x h1 h2). Qed.
Lemma lem7168190 (p : Prop) : (term551 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7168191 : term596 = False.
Proof. exact (@lem7168190 False). Qed.
Lemma lem7168192 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term963 A s x') (h2 : term981 A B s _95913 t R x' x) : False.
Proof. exact (EQ_MP (@lem7168191) (@lem7168188 A B s _95913 t R x' x h1 h2)). Qed.
Lemma lem7168329 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term981 A B s _95913 t R x' x) : @I (A -> Prop) s x'.
Proof. exact (proj1 (@lem7165307 A B s _95913 t R x' x h1)). Qed.
Lemma lem7168330 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term981 A B s _95913 t R x' x) : term1149 A s x'.
Proof. exact (fun h0 : term963 A s x' => @lem7168329 A B s _95913 t R x' x h1). Qed.
Lemma lem7168332 (p : Prop) : (term551 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7168333 {A : Type'} (s : A -> Prop) (x' : A) : (term1149 A s x') = (@I (A -> Prop) s x').
Proof. exact (@lem7168332 (@I (A -> Prop) s x')). Qed.
Lemma lem7168334 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term981 A B s _95913 t R x' x) : @I (A -> Prop) s x'.
Proof. exact (EQ_MP (@lem7168333 A s x') (@lem7168330 A B s _95913 t R x' x h1)). Qed.
Lemma lem7168340 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7168341 {A B : Type'} (t : B -> Prop) (y : A -> B) (s : A -> Prop) (_95939 : A) : (term1147 A B s t y _95939) = (term1223 A B t y s _95939).
Proof. exact (@lem7168340 (term999 A B t y _95939) (term963 A s _95939)). Qed.
Lemma lem7168347 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7168348 {A B : Type'} (t : B -> Prop) (y : A -> B) (s : A -> Prop) (_95939 : A) : (term1224 A B s t y _95939) = (term1225 A B t y s _95939).
Proof. exact (MK_COMB (@lem7168347) (@lem7168341 A B t y s _95939)). Qed.
Lemma lem7168354 {A B : Type'} (t : B -> Prop) (y : A -> B) (s : A -> Prop) (_95939 : A) : (term1223 A B t y s _95939) = (term1223 A B t y s _95939).
Proof. exact (eq_refl (term1223 A B t y s _95939)). Qed.
Lemma lem7168355 {A B : Type'} (t : B -> Prop) (y : A -> B) (s : A -> Prop) (_95939 : A) : ((term1147 A B s t y _95939) = (term1223 A B t y s _95939)) = ((term1223 A B t y s _95939) = (term1223 A B t y s _95939)).
Proof. exact (MK_COMB (@lem7168348 A B t y s _95939) (@lem7168354 A B t y s _95939)). Qed.
Lemma lem7168357 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7168358 (x : Prop) : (x = x) = True.
Proof. exact (@lem7168357 Prop x). Qed.
Lemma lem7168359 {A B : Type'} (t : B -> Prop) (y : A -> B) (s : A -> Prop) (_95939 : A) : ((term1223 A B t y s _95939) = (term1223 A B t y s _95939)) = True.
Proof. exact (@lem7168358 (term1223 A B t y s _95939)). Qed.
Lemma lem7168360 {A B : Type'} (t : B -> Prop) (y : A -> B) (s : A -> Prop) (_95939 : A) : ((term1147 A B s t y _95939) = (term1223 A B t y s _95939)) = True.
Proof. exact (TRANS (@lem7168355 A B t y s _95939) (@lem7168359 A B t y s _95939)). Qed.
Lemma lem7168361 {A B : Type'} (t : B -> Prop) (y : A -> B) (s : A -> Prop) (_95939 : A) : True = ((term1147 A B s t y _95939) = (term1223 A B t y s _95939)).
Proof. exact (SYM (@lem7168360 A B t y s _95939)). Qed.
Lemma lem7168362 {A B : Type'} (t : B -> Prop) (y : A -> B) (s : A -> Prop) (_95939 : A) : (term1147 A B s t y _95939) = (term1223 A B t y s _95939).
Proof. exact (EQ_MP (@lem7168361 A B t y s _95939) (@lem0)). Qed.
Lemma lem7168363 {A B : Type'} (_95939 : A) (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1223 A B t y s _95939.
Proof. exact (EQ_MP (@lem7168362 A B t y s _95939) (@lem7167033 A B _95939 x y t R s h1)). Qed.
Lemma lem7168365 (b : Prop) (a : Prop) : (a \/ b) = (term555 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7168366 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (y : A -> B) (_95939 : A) : (term1223 A B t y s _95939) = (term1226 A B s t y _95939).
Proof. exact (@lem7168365 (term963 A s _95939) (term999 A B t y _95939)). Qed.
Lemma lem7168368 (a : Prop) : (term203 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7168369 {A : Type'} (s : A -> Prop) (_95939 : A) : (term1161 A s _95939) = (@I (A -> Prop) s _95939).
Proof. exact (@lem7168368 (@I (A -> Prop) s _95939)). Qed.
Lemma lem7168370 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7168371 {A : Type'} (s : A -> Prop) (_95939 : A) : (term1227 A s _95939) = (term1228 A s _95939).
Proof. exact (MK_COMB (@lem7168370) (@lem7168369 A s _95939)). Qed.
Lemma lem7168372 {A B : Type'} (t : B -> Prop) (y : A -> B) (_95939 : A) : (term999 A B t y _95939) = (term999 A B t y _95939).
Proof. exact (eq_refl (term999 A B t y _95939)). Qed.
Lemma lem7168373 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (y : A -> B) (_95939 : A) : (term1226 A B s t y _95939) = (term1229 A B s t y _95939).
Proof. exact (MK_COMB (@lem7168371 A s _95939) (@lem7168372 A B t y _95939)). Qed.
Lemma lem7168374 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (y : A -> B) (_95939 : A) : (term1223 A B t y s _95939) = (term1229 A B s t y _95939).
Proof. exact (TRANS (@lem7168366 A B s t y _95939) (@lem7168373 A B s t y _95939)). Qed.
Lemma lem7168377 {A B : Type'} (_95939 : A) (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1229 A B s t y _95939.
Proof. exact (EQ_MP (@lem7168374 A B s t y _95939) (@lem7168363 A B _95939 x y t R s h1)). Qed.
Lemma lem7168378 {A B : Type'} (_95939 : A) (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1229 A B s t y _95939.
Proof. exact (@lem7168377 A B _95939 x y t R s h1). Qed.
Lemma lem7168379 {A B : Type'} (x' : A) (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1229 A B s t y x'.
Proof. exact (@lem7168378 A B x' x y t R s h1). Qed.
Lemma lem7168382 {A B : Type'} (y : A -> B) (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term940 A B x y t R s) (h2 : term981 A B s _95913 t R x' x) : term999 A B t y x'.
Proof. exact (@lem7168379 A B x' x y t R s h1 (@lem7168334 A B s _95913 t R x' x h2)). Qed.
Lemma lem7168383 {A B : Type'} (y : A -> B) (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term940 A B x y t R s) (h2 : term981 A B s _95913 t R x' x) : term1230 A B t y x'.
Proof. exact (fun h0 : term1231 A B t y x' => @lem7168382 A B y s _95913 t R x' x h1 h2). Qed.
Lemma lem7168385 (p : Prop) : (term551 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7168386 {A B : Type'} (t : B -> Prop) (y : A -> B) (x' : A) : (term1230 A B t y x') = (term999 A B t y x').
Proof. exact (@lem7168385 (term999 A B t y x')). Qed.
Lemma lem7168387 {A B : Type'} (y : A -> B) (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term940 A B x y t R s) (h2 : term981 A B s _95913 t R x' x) : term999 A B t y x'.
Proof. exact (EQ_MP (@lem7168386 A B t y x') (@lem7168383 A B y s _95913 t R x' x h1 h2)). Qed.
Lemma lem7168389 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term981 A B s _95913 t R x' x) : @I (A -> Prop) s x'.
Proof. exact (proj1 (@lem7165307 A B s _95913 t R x' x h1)). Qed.
Lemma lem7168390 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term981 A B s _95913 t R x' x) : term1149 A s x'.
Proof. exact (fun h0 : term963 A s x' => @lem7168389 A B s _95913 t R x' x h1). Qed.
Lemma lem7168392 (p : Prop) : (term551 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7168393 {A : Type'} (s : A -> Prop) (x' : A) : (term1149 A s x') = (@I (A -> Prop) s x').
Proof. exact (@lem7168392 (@I (A -> Prop) s x')). Qed.
Lemma lem7168394 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term981 A B s _95913 t R x' x) : @I (A -> Prop) s x'.
Proof. exact (EQ_MP (@lem7168393 A s x') (@lem7168390 A B s _95913 t R x' x h1)). Qed.
Lemma lem7168400 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7168401 {A B : Type'} (R : type1413 A B) (y : A -> B) (s : A -> Prop) (_95939 : A) : (term1148 A B s R y _95939) = (term1232 A B R y s _95939).
Proof. exact (@lem7168400 (term406 A B R y _95939) (term963 A s _95939)). Qed.
Lemma lem7168407 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7168408 {A B : Type'} (R : type1413 A B) (y : A -> B) (s : A -> Prop) (_95939 : A) : (term1233 A B s R y _95939) = (term1234 A B R y s _95939).
Proof. exact (MK_COMB (@lem7168407) (@lem7168401 A B R y s _95939)). Qed.
Lemma lem7168414 {A B : Type'} (R : type1413 A B) (y : A -> B) (s : A -> Prop) (_95939 : A) : (term1232 A B R y s _95939) = (term1232 A B R y s _95939).
Proof. exact (eq_refl (term1232 A B R y s _95939)). Qed.
Lemma lem7168415 {A B : Type'} (R : type1413 A B) (y : A -> B) (s : A -> Prop) (_95939 : A) : ((term1148 A B s R y _95939) = (term1232 A B R y s _95939)) = ((term1232 A B R y s _95939) = (term1232 A B R y s _95939)).
Proof. exact (MK_COMB (@lem7168408 A B R y s _95939) (@lem7168414 A B R y s _95939)). Qed.
Lemma lem7168417 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7168418 (x : Prop) : (x = x) = True.
Proof. exact (@lem7168417 Prop x). Qed.
Lemma lem7168419 {A B : Type'} (R : type1413 A B) (y : A -> B) (s : A -> Prop) (_95939 : A) : ((term1232 A B R y s _95939) = (term1232 A B R y s _95939)) = True.
Proof. exact (@lem7168418 (term1232 A B R y s _95939)). Qed.
Lemma lem7168420 {A B : Type'} (R : type1413 A B) (y : A -> B) (s : A -> Prop) (_95939 : A) : ((term1148 A B s R y _95939) = (term1232 A B R y s _95939)) = True.
Proof. exact (TRANS (@lem7168415 A B R y s _95939) (@lem7168419 A B R y s _95939)). Qed.
Lemma lem7168421 {A B : Type'} (R : type1413 A B) (y : A -> B) (s : A -> Prop) (_95939 : A) : True = ((term1148 A B s R y _95939) = (term1232 A B R y s _95939)).
Proof. exact (SYM (@lem7168420 A B R y s _95939)). Qed.
Lemma lem7168422 {A B : Type'} (R : type1413 A B) (y : A -> B) (s : A -> Prop) (_95939 : A) : (term1148 A B s R y _95939) = (term1232 A B R y s _95939).
Proof. exact (EQ_MP (@lem7168421 A B R y s _95939) (@lem0)). Qed.
Lemma lem7168423 {A B : Type'} (_95939 : A) (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1232 A B R y s _95939.
Proof. exact (EQ_MP (@lem7168422 A B R y s _95939) (@lem7167047 A B _95939 x y t R s h1)). Qed.
Lemma lem7168425 (b : Prop) (a : Prop) : (a \/ b) = (term555 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7168426 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (y : A -> B) (_95939 : A) : (term1232 A B R y s _95939) = (term1235 A B s R y _95939).
Proof. exact (@lem7168425 (term963 A s _95939) (term406 A B R y _95939)). Qed.
Lemma lem7168428 (a : Prop) : (term203 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7168429 {A : Type'} (s : A -> Prop) (_95939 : A) : (term1161 A s _95939) = (@I (A -> Prop) s _95939).
Proof. exact (@lem7168428 (@I (A -> Prop) s _95939)). Qed.
Lemma lem7168430 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7168431 {A : Type'} (s : A -> Prop) (_95939 : A) : (term1227 A s _95939) = (term1228 A s _95939).
Proof. exact (MK_COMB (@lem7168430) (@lem7168429 A s _95939)). Qed.
Lemma lem7168432 {A B : Type'} (R : type1413 A B) (y : A -> B) (_95939 : A) : (term406 A B R y _95939) = (term406 A B R y _95939).
Proof. exact (eq_refl (term406 A B R y _95939)). Qed.
Lemma lem7168433 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (y : A -> B) (_95939 : A) : (term1235 A B s R y _95939) = (term1236 A B s R y _95939).
Proof. exact (MK_COMB (@lem7168431 A s _95939) (@lem7168432 A B R y _95939)). Qed.
Lemma lem7168434 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (y : A -> B) (_95939 : A) : (term1232 A B R y s _95939) = (term1236 A B s R y _95939).
Proof. exact (TRANS (@lem7168426 A B s R y _95939) (@lem7168433 A B s R y _95939)). Qed.
Lemma lem7168437 {A B : Type'} (_95939 : A) (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1236 A B s R y _95939.
Proof. exact (EQ_MP (@lem7168434 A B s R y _95939) (@lem7168423 A B _95939 x y t R s h1)). Qed.
Lemma lem7168438 {A B : Type'} (_95939 : A) (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1236 A B s R y _95939.
Proof. exact (@lem7168437 A B _95939 x y t R s h1). Qed.
Lemma lem7168439 {A B : Type'} (x' : A) (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1236 A B s R y x'.
Proof. exact (@lem7168438 A B x' x y t R s h1). Qed.
Lemma lem7168442 {A B : Type'} (y : A -> B) (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term940 A B x y t R s) (h2 : term981 A B s _95913 t R x' x) : term406 A B R y x'.
Proof. exact (@lem7168439 A B x' x y t R s h1 (@lem7168394 A B s _95913 t R x' x h2)). Qed.
Lemma lem7168443 {A B : Type'} (y : A -> B) (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term940 A B x y t R s) (h2 : term981 A B s _95913 t R x' x) : term568 A B R y x'.
Proof. exact (fun h0 : term569 A B R y x' => @lem7168442 A B y s _95913 t R x' x h1 h2). Qed.
Lemma lem7168445 (p : Prop) : (term551 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7168446 {A B : Type'} (R : type1413 A B) (y : A -> B) (x' : A) : (term568 A B R y x') = (term406 A B R y x').
Proof. exact (@lem7168445 (term406 A B R y x')). Qed.
Lemma lem7168447 {A B : Type'} (y : A -> B) (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term940 A B x y t R s) (h2 : term981 A B s _95913 t R x' x) : term406 A B R y x'.
Proof. exact (EQ_MP (@lem7168446 A B R y x') (@lem7168443 A B y s _95913 t R x' x h1 h2)). Qed.
Lemma lem7168463 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7168464 {A B : Type'} (_95913 : type830 A B) (_95935 : B -> Prop) (_95936 : type1413 A B) (_95937 : A) (_95938 : B) : (term1169 A B _95938 _95913 _95935 _95936 _95937) = (term1170 A B _95913 _95935 _95936 _95937 _95938).
Proof. exact (@lem7168463 (term370 A B _95913 _95935 _95936 _95937) (term380 A B _95936 _95937 _95938)). Qed.
Lemma lem7168470 {B : Type'} (_95935 : B -> Prop) (_95938 : B) : (term964 B _95935 _95938) = (term964 B _95935 _95938).
Proof. exact (eq_refl (term964 B _95935 _95938)). Qed.
Lemma lem7168471 {A B : Type'} (_95913 : type830 A B) (_95935 : B -> Prop) (_95936 : type1413 A B) (_95937 : A) (_95938 : B) : (term1140 A B _95938 _95913 _95935 _95936 _95937) = (term1171 A B _95913 _95935 _95936 _95937 _95938).
Proof. exact (MK_COMB (@lem7168470 B _95935 _95938) (@lem7168464 A B _95913 _95935 _95936 _95937 _95938)). Qed.
Lemma lem7168475 (q : Prop) (p : Prop) (r : Prop) : (term21 p q r) = (term21 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7168476 {A B : Type'} (_95913 : type830 A B) (_95935 : B -> Prop) (_95936 : type1413 A B) (_95937 : A) (_95938 : B) : (term1171 A B _95913 _95935 _95936 _95937 _95938) = (term1172 A B _95913 _95935 _95936 _95937 _95938).
Proof. exact (@lem7168475 (term370 A B _95913 _95935 _95936 _95937) (term963 B _95935 _95938) (term380 A B _95936 _95937 _95938)). Qed.
Lemma lem7168492 {A B : Type'} (_95913 : type830 A B) (_95935 : B -> Prop) (_95936 : type1413 A B) (_95937 : A) (_95938 : B) : (term1140 A B _95938 _95913 _95935 _95936 _95937) = (term1172 A B _95913 _95935 _95936 _95937 _95938).
Proof. exact (TRANS (@lem7168471 A B _95913 _95935 _95936 _95937 _95938) (@lem7168476 A B _95913 _95935 _95936 _95937 _95938)). Qed.
Lemma lem7168493 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7168494 {A B : Type'} (_95913 : type830 A B) (_95935 : B -> Prop) (_95936 : type1413 A B) (_95937 : A) (_95938 : B) : (term1173 A B _95938 _95913 _95935 _95936 _95937) = (term1174 A B _95913 _95935 _95936 _95937 _95938).
Proof. exact (MK_COMB (@lem7168493) (@lem7168492 A B _95913 _95935 _95936 _95937 _95938)). Qed.
Lemma lem7168510 {A B : Type'} (_95913 : type830 A B) (_95935 : B -> Prop) (_95936 : type1413 A B) (_95937 : A) (_95938 : B) : (term1172 A B _95913 _95935 _95936 _95937 _95938) = (term1172 A B _95913 _95935 _95936 _95937 _95938).
Proof. exact (eq_refl (term1172 A B _95913 _95935 _95936 _95937 _95938)). Qed.
Lemma lem7168511 {A B : Type'} (_95913 : type830 A B) (_95935 : B -> Prop) (_95936 : type1413 A B) (_95937 : A) (_95938 : B) : ((term1140 A B _95938 _95913 _95935 _95936 _95937) = (term1172 A B _95913 _95935 _95936 _95937 _95938)) = ((term1172 A B _95913 _95935 _95936 _95937 _95938) = (term1172 A B _95913 _95935 _95936 _95937 _95938)).
Proof. exact (MK_COMB (@lem7168494 A B _95913 _95935 _95936 _95937 _95938) (@lem7168510 A B _95913 _95935 _95936 _95937 _95938)). Qed.
Lemma lem7168513 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7168514 (x : Prop) : (x = x) = True.
Proof. exact (@lem7168513 Prop x). Qed.
Lemma lem7168515 {A B : Type'} (_95913 : type830 A B) (_95935 : B -> Prop) (_95936 : type1413 A B) (_95937 : A) (_95938 : B) : ((term1172 A B _95913 _95935 _95936 _95937 _95938) = (term1172 A B _95913 _95935 _95936 _95937 _95938)) = True.
Proof. exact (@lem7168514 (term1172 A B _95913 _95935 _95936 _95937 _95938)). Qed.
Lemma lem7168516 {A B : Type'} (_95913 : type830 A B) (_95935 : B -> Prop) (_95936 : type1413 A B) (_95937 : A) (_95938 : B) : ((term1140 A B _95938 _95913 _95935 _95936 _95937) = (term1172 A B _95913 _95935 _95936 _95937 _95938)) = True.
Proof. exact (TRANS (@lem7168511 A B _95913 _95935 _95936 _95937 _95938) (@lem7168515 A B _95913 _95935 _95936 _95937 _95938)). Qed.
Lemma lem7168517 {A B : Type'} (_95913 : type830 A B) (_95935 : B -> Prop) (_95936 : type1413 A B) (_95937 : A) (_95938 : B) : True = ((term1140 A B _95938 _95913 _95935 _95936 _95937) = (term1172 A B _95913 _95935 _95936 _95937 _95938)).
Proof. exact (SYM (@lem7168516 A B _95913 _95935 _95936 _95937 _95938)). Qed.
Lemma lem7168518 {A B : Type'} (_95913 : type830 A B) (_95935 : B -> Prop) (_95936 : type1413 A B) (_95937 : A) (_95938 : B) : (term1140 A B _95938 _95913 _95935 _95936 _95937) = (term1172 A B _95913 _95935 _95936 _95937 _95938).
Proof. exact (EQ_MP (@lem7168517 A B _95913 _95935 _95936 _95937 _95938) (@lem0)). Qed.
Lemma lem7168519 {A B : Type'} (_95935 : B -> Prop) (_95936 : type1413 A B) (_95937 : A) (_95938 : B) (_95913 : type830 A B) (h1 : term728 A B _95913) : term1172 A B _95913 _95935 _95936 _95937 _95938.
Proof. exact (EQ_MP (@lem7168518 A B _95913 _95935 _95936 _95937 _95938) (@lem7167075 A B _95938 _95935 _95936 _95937 _95913 h1)). Qed.
Lemma lem7168521 (b : Prop) (a : Prop) : (a \/ b) = (term555 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7168522 {A B : Type'} (_95938 : B) (_95913 : type830 A B) (_95935 : B -> Prop) (_95936 : type1413 A B) (_95937 : A) : (term1172 A B _95913 _95935 _95936 _95937 _95938) = (term1175 A B _95938 _95913 _95935 _95936 _95937).
Proof. exact (@lem7168521 (term965 A B _95935 _95936 _95937 _95938) (term370 A B _95913 _95935 _95936 _95937)). Qed.
Lemma lem7168524 (a : Prop) (b : Prop) : (term582 a b) = (term583 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7168525 {A B : Type'} (_95935 : B -> Prop) (_95936 : type1413 A B) (_95937 : A) (_95938 : B) : (term1159 A B _95935 _95936 _95937 _95938) = (term1160 A B _95935 _95936 _95937 _95938).
Proof. exact (@lem7168524 (term963 B _95935 _95938) (term380 A B _95936 _95937 _95938)). Qed.
Lemma lem7168527 (a : Prop) : (term203 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7168528 {B : Type'} (_95935 : B -> Prop) (_95938 : B) : (term1161 B _95935 _95938) = (@I (B -> Prop) _95935 _95938).
Proof. exact (@lem7168527 (@I (B -> Prop) _95935 _95938)). Qed.
Lemma lem7168529 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7168530 {B : Type'} (_95935 : B -> Prop) (_95938 : B) : (term1162 B _95935 _95938) = (term977 B _95935 _95938).
Proof. exact (MK_COMB (@lem7168529) (@lem7168528 B _95935 _95938)). Qed.
Lemma lem7168532 (a : Prop) : (term203 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7168533 {A B : Type'} (_95936 : type1413 A B) (_95937 : A) (_95938 : B) : (term588 A B _95936 _95937 _95938) = (term378 A B _95936 _95937 _95938).
Proof. exact (@lem7168532 (term378 A B _95936 _95937 _95938)). Qed.
Lemma lem7168534 {A B : Type'} (_95935 : B -> Prop) (_95936 : type1413 A B) (_95937 : A) (_95938 : B) : (term1160 A B _95935 _95936 _95937 _95938) = (term1163 A B _95935 _95936 _95937 _95938).
Proof. exact (MK_COMB (@lem7168530 B _95935 _95938) (@lem7168533 A B _95936 _95937 _95938)). Qed.
Lemma lem7168535 {A B : Type'} (_95935 : B -> Prop) (_95936 : type1413 A B) (_95937 : A) (_95938 : B) : (term1159 A B _95935 _95936 _95937 _95938) = (term1163 A B _95935 _95936 _95937 _95938).
Proof. exact (TRANS (@lem7168525 A B _95935 _95936 _95937 _95938) (@lem7168534 A B _95935 _95936 _95937 _95938)). Qed.
Lemma lem7168536 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7168537 {A B : Type'} (_95935 : B -> Prop) (_95936 : type1413 A B) (_95937 : A) (_95938 : B) : (term1164 A B _95935 _95936 _95937 _95938) = (term1165 A B _95935 _95936 _95937 _95938).
Proof. exact (MK_COMB (@lem7168536) (@lem7168535 A B _95935 _95936 _95937 _95938)). Qed.
Lemma lem7168538 {A B : Type'} (_95913 : type830 A B) (_95935 : B -> Prop) (_95936 : type1413 A B) (_95937 : A) : (term370 A B _95913 _95935 _95936 _95937) = (term370 A B _95913 _95935 _95936 _95937).
Proof. exact (eq_refl (term370 A B _95913 _95935 _95936 _95937)). Qed.
Lemma lem7168539 {A B : Type'} (_95938 : B) (_95913 : type830 A B) (_95935 : B -> Prop) (_95936 : type1413 A B) (_95937 : A) : (term1175 A B _95938 _95913 _95935 _95936 _95937) = (term1176 A B _95938 _95913 _95935 _95936 _95937).
Proof. exact (MK_COMB (@lem7168537 A B _95935 _95936 _95937 _95938) (@lem7168538 A B _95913 _95935 _95936 _95937)). Qed.
Lemma lem7168540 {A B : Type'} (_95938 : B) (_95913 : type830 A B) (_95935 : B -> Prop) (_95936 : type1413 A B) (_95937 : A) : (term1172 A B _95913 _95935 _95936 _95937 _95938) = (term1176 A B _95938 _95913 _95935 _95936 _95937).
Proof. exact (TRANS (@lem7168522 A B _95938 _95913 _95935 _95936 _95937) (@lem7168539 A B _95938 _95913 _95935 _95936 _95937)). Qed.
Lemma lem7168542 {A B : Type'} (y : A -> B) (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term940 A B x y t R s) (h2 : term981 A B s _95913 t R x' x) : term1003 A B t R y x'.
Proof. exact (conj (@lem7168387 A B y s _95913 t R x' x h1 h2) (@lem7168447 A B y s _95913 t R x' x h1 h2)). Qed.
Lemma lem7168544 {A B : Type'} (_95938 : B) (_95935 : B -> Prop) (_95936 : type1413 A B) (_95937 : A) (_95913 : type830 A B) (h1 : term728 A B _95913) : term1176 A B _95938 _95913 _95935 _95936 _95937.
Proof. exact (EQ_MP (@lem7168540 A B _95938 _95913 _95935 _95936 _95937) (@lem7168519 A B _95935 _95936 _95937 _95938 _95913 h1)). Qed.
Lemma lem7168545 {A B : Type'} (_95938 : B) (_95935 : B -> Prop) (_95936 : type1413 A B) (_95937 : A) (_95913 : type830 A B) (h1 : term728 A B _95913) : term1176 A B _95938 _95913 _95935 _95936 _95937.
Proof. exact (@lem7168544 A B _95938 _95935 _95936 _95937 _95913 h1). Qed.
Lemma lem7168546 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x' : A) (_95913 : type830 A B) (h1 : term728 A B _95913) : term1237 A B y _95913 t R x'.
Proof. exact (@lem7168545 A B (@I (A -> B) y x') t R x' _95913 h1). Qed.
Lemma lem7168549 {A B : Type'} (y : A -> B) (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _95913) (h2 : term940 A B x y t R s) (h3 : term981 A B s _95913 t R x' x) : term370 A B _95913 t R x'.
Proof. exact (@lem7168546 A B y t R x' _95913 h1 (@lem7168542 A B y s _95913 t R x' x h2 h3)). Qed.
Lemma lem7168550 {A B : Type'} (y : A -> B) (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _95913) (h2 : term940 A B x y t R s) (h3 : term981 A B s _95913 t R x' x) : term1177 A B _95913 t R x'.
Proof. exact (fun h0 : term1144 A B _95913 t R x' => @lem7168549 A B y s _95913 t R x' x h1 h2 h3). Qed.
Lemma lem7168552 (p : Prop) : (term551 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7168553 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) : (term1177 A B _95913 t R x') = (term370 A B _95913 t R x').
Proof. exact (@lem7168552 (term370 A B _95913 t R x')). Qed.
Lemma lem7168554 {A B : Type'} (y : A -> B) (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _95913) (h2 : term940 A B x y t R s) (h3 : term981 A B s _95913 t R x' x) : term370 A B _95913 t R x'.
Proof. exact (EQ_MP (@lem7168553 A B _95913 t R x') (@lem7168550 A B y s _95913 t R x' x h1 h2 h3)). Qed.
Lemma lem7168557 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7168559 {A B : Type'} (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) : (term1144 A B _95913 t R x') = (term1238 A B _95913 t R x').
Proof. exact (@lem7168557 (term370 A B _95913 t R x')). Qed.
Lemma lem7168562 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term380 A B R x' x) (h2 : term981 A B s _95913 t R x' x) : term1238 A B _95913 t R x'.
Proof. exact (EQ_MP (@lem7168559 A B _95913 t R x') (@lem7167005 A B s _95913 t R x' x h1 h2)). Qed.
Lemma lem7168565 {A B : Type'} (y : A -> B) (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _95913) (h2 : term380 A B R x' x) (h3 : term940 A B x y t R s) (h4 : term981 A B s _95913 t R x' x) : False.
Proof. exact (@lem7168562 A B s _95913 t R x' x h2 h4 (@lem7168554 A B y s _95913 t R x' x h1 h3 h4)). Qed.
Lemma lem7168566 {A B : Type'} (y : A -> B) (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _95913) (h2 : term380 A B R x' x) (h3 : term940 A B x y t R s) (h4 : term981 A B s _95913 t R x' x) : term596.
Proof. exact (fun h0 : ~ False => @lem7168565 A B y s _95913 t R x' x h1 h2 h3 h4). Qed.
Lemma lem7168568 (p : Prop) : (term551 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7168569 : term596 = False.
Proof. exact (@lem7168568 False). Qed.
Lemma lem7168571 {A B : Type'} (y : A -> B) (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _95913) (h2 : term380 A B R x' x) (h3 : term940 A B x y t R s) (h4 : term981 A B s _95913 t R x' x) : False.
Proof. exact (EQ_MP (@lem7168569) (@lem7168566 A B y s _95913 t R x' x h1 h2 h3 h4)). Qed.
Lemma lem7168572 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term963 A s x') (h2 : term981 A B s _95913 t R x' x) : (term963 A s x') = False.
Proof. exact (prop_ext (fun h3 : term963 A s x' => @lem7168192 A B s _95913 t R x' x h1 h2) (fun h3 : False => @lem7166866 A s x' h1)). Qed.
Lemma lem7168574 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term963 A s x') (h2 : term981 A B s _95913 t R x' x) : False.
Proof. exact (EQ_MP (@lem7168572 A B s _95913 t R x' x h1 h2) (@lem7166866 A s x' h1)). Qed.
Lemma lem7168575 {A B : Type'} (y : A -> B) (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _95913) (h2 : term380 A B R x' x) (h3 : term940 A B x y t R s) (h4 : term981 A B s _95913 t R x' x) : (term380 A B R x' x) = False.
Proof. exact (prop_ext (fun h5 : term380 A B R x' x => @lem7168571 A B y s _95913 t R x' x h1 h2 h3 h4) (fun h5 : False => @lem7166734 A B R x' x h2)). Qed.
Lemma lem7168576 {A B : Type'} (y : A -> B) (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _95913) (h2 : term380 A B R x' x) (h3 : term940 A B x y t R s) (h4 : term981 A B s _95913 t R x' x) : False.
Proof. exact (EQ_MP (@lem7168575 A B y s _95913 t R x' x h1 h2 h3 h4) (@lem7166734 A B R x' x h2)). Qed.
Lemma lem7168577 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term963 A s x') (h2 : term981 A B s _95913 t R x' x) : (term963 A s x') = False.
Proof. exact (prop_ext (fun h3 : term963 A s x' => @lem7168574 A B s _95913 t R x' x h1 h2) (fun h3 : False => @lem7166662 A s x' h1)). Qed.
Lemma lem7168578 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term963 A s x') (h2 : term981 A B s _95913 t R x' x) : False.
Proof. exact (EQ_MP (@lem7168577 A B s _95913 t R x' x h1 h2) (@lem7166662 A s x' h1)). Qed.
Lemma lem7168579 {A B : Type'} (y : A -> B) (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _95913) (h2 : term983 A B _95913 t R x' x) (h3 : term940 A B x y t R s) (h4 : term987 A B s _95913 t R x' x) : (term983 A B _95913 t R x' x) = False.
Proof. exact (prop_ext (fun h5 : term983 A B _95913 t R x' x => @lem7168034 A B y s _95913 t R x' x h1 h2 h3 h4) (fun h5 : False => @lem7166590 A B _95913 t R x' x h2)). Qed.
Lemma lem7168580 {A B : Type'} (y : A -> B) (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _95913) (h2 : term983 A B _95913 t R x' x) (h3 : term940 A B x y t R s) (h4 : term987 A B s _95913 t R x' x) : False.
Proof. exact (EQ_MP (@lem7168579 A B y s _95913 t R x' x h1 h2 h3 h4) (@lem7166590 A B _95913 t R x' x h2)). Qed.
Lemma lem7168581 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term963 A s x') (h2 : term987 A B s _95913 t R x' x) : (term963 A s x') = False.
Proof. exact (prop_ext (fun h3 : term963 A s x' => @lem7167233 A B s _95913 t R x' x h1 h2) (fun h3 : False => @lem7166518 A s x' h1)). Qed.
Lemma lem7168582 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term963 A s x') (h2 : term987 A B s _95913 t R x' x) : False.
Proof. exact (EQ_MP (@lem7168581 A B s _95913 t R x' x h1 h2) (@lem7166518 A s x' h1)). Qed.
Lemma lem7168583 {A B : Type'} (y : A -> B) (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _95913) (h2 : term380 A B R x' x) (h3 : term940 A B x y t R s) (h4 : term981 A B s _95913 t R x' x) : (term380 A B R x' x) = False.
Proof. exact (prop_ext (fun h5 : term380 A B R x' x => @lem7168576 A B y s _95913 t R x' x h1 h2 h3 h4) (fun h5 : False => @lem7166400 A B R x' x h2)). Qed.
Lemma lem7168584 {A B : Type'} (y : A -> B) (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _95913) (h2 : term380 A B R x' x) (h3 : term940 A B x y t R s) (h4 : term981 A B s _95913 t R x' x) : False.
Proof. exact (EQ_MP (@lem7168583 A B y s _95913 t R x' x h1 h2 h3 h4) (@lem7166400 A B R x' x h2)). Qed.
Lemma lem7168585 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term963 A s x') (h2 : term981 A B s _95913 t R x' x) : (term963 A s x') = False.
Proof. exact (prop_ext (fun h3 : term963 A s x' => @lem7168578 A B s _95913 t R x' x h1 h2) (fun h3 : False => @lem7166128 A s x' h1)). Qed.
Lemma lem7168586 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term963 A s x') (h2 : term981 A B s _95913 t R x' x) : False.
Proof. exact (EQ_MP (@lem7168585 A B s _95913 t R x' x h1 h2) (@lem7166128 A s x' h1)). Qed.
Lemma lem7168587 {A B : Type'} (y : A -> B) (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _95913) (h2 : term983 A B _95913 t R x' x) (h3 : term940 A B x y t R s) (h4 : term987 A B s _95913 t R x' x) : (term983 A B _95913 t R x' x) = False.
Proof. exact (prop_ext (fun h5 : term983 A B _95913 t R x' x => @lem7168580 A B y s _95913 t R x' x h1 h2 h3 h4) (fun h5 : False => @lem7165856 A B _95913 t R x' x h2)). Qed.
Lemma lem7168588 {A B : Type'} (y : A -> B) (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _95913) (h2 : term983 A B _95913 t R x' x) (h3 : term940 A B x y t R s) (h4 : term987 A B s _95913 t R x' x) : False.
Proof. exact (EQ_MP (@lem7168587 A B y s _95913 t R x' x h1 h2 h3 h4) (@lem7165856 A B _95913 t R x' x h2)). Qed.
Lemma lem7168589 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term963 A s x') (h2 : term987 A B s _95913 t R x' x) : (term963 A s x') = False.
Proof. exact (prop_ext (fun h3 : term963 A s x' => @lem7168582 A B s _95913 t R x' x h1 h2) (fun h3 : False => @lem7165584 A s x' h1)). Qed.
Lemma lem7168590 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term963 A s x') (h2 : term987 A B s _95913 t R x' x) : False.
Proof. exact (EQ_MP (@lem7168589 A B s _95913 t R x' x h1 h2) (@lem7165584 A s x' h1)). Qed.
Lemma lem7168591 {A B : Type'} (y : A -> B) (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _95913) (h2 : term380 A B R x' x) (h3 : term940 A B x y t R s) (h4 : term981 A B s _95913 t R x' x) : (term380 A B R x' x) = False.
Proof. exact (prop_ext (fun h5 : term380 A B R x' x => @lem7168584 A B y s _95913 t R x' x h1 h2 h3 h4) (fun h5 : False => @lem7166400 A B R x' x h2)). Qed.
Lemma lem7168592 {A B : Type'} (y : A -> B) (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _95913) (h2 : term380 A B R x' x) (h3 : term940 A B x y t R s) (h4 : term981 A B s _95913 t R x' x) : False.
Proof. exact (EQ_MP (@lem7168591 A B y s _95913 t R x' x h1 h2 h3 h4) (@lem7166400 A B R x' x h2)). Qed.
Lemma lem7168593 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term963 A s x') (h2 : term981 A B s _95913 t R x' x) : (term963 A s x') = False.
Proof. exact (prop_ext (fun h3 : term963 A s x' => @lem7168586 A B s _95913 t R x' x h1 h2) (fun h3 : False => @lem7166128 A s x' h1)). Qed.
Lemma lem7168594 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term963 A s x') (h2 : term981 A B s _95913 t R x' x) : False.
Proof. exact (EQ_MP (@lem7168593 A B s _95913 t R x' x h1 h2) (@lem7166128 A s x' h1)). Qed.
Lemma lem7168595 {A B : Type'} (y : A -> B) (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _95913) (h2 : term983 A B _95913 t R x' x) (h3 : term940 A B x y t R s) (h4 : term987 A B s _95913 t R x' x) : (term983 A B _95913 t R x' x) = False.
Proof. exact (prop_ext (fun h5 : term983 A B _95913 t R x' x => @lem7168588 A B y s _95913 t R x' x h1 h2 h3 h4) (fun h5 : False => @lem7165856 A B _95913 t R x' x h2)). Qed.
Lemma lem7168596 {A B : Type'} (y : A -> B) (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _95913) (h2 : term983 A B _95913 t R x' x) (h3 : term940 A B x y t R s) (h4 : term987 A B s _95913 t R x' x) : False.
Proof. exact (EQ_MP (@lem7168595 A B y s _95913 t R x' x h1 h2 h3 h4) (@lem7165856 A B _95913 t R x' x h2)). Qed.
Lemma lem7168597 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term963 A s x') (h2 : term987 A B s _95913 t R x' x) : (term963 A s x') = False.
Proof. exact (prop_ext (fun h3 : term963 A s x' => @lem7168590 A B s _95913 t R x' x h1 h2) (fun h3 : False => @lem7165584 A s x' h1)). Qed.
Lemma lem7168598 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term963 A s x') (h2 : term987 A B s _95913 t R x' x) : False.
Proof. exact (EQ_MP (@lem7168597 A B s _95913 t R x' x h1 h2) (@lem7165584 A s x' h1)). Qed.
Lemma lem7168599 {A B : Type'} (y : A -> B) (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _95913) (h2 : term940 A B x y t R s) (h3 : term981 A B s _95913 t R x' x) : False.
Proof. exact (or_elim (@lem7165308 A B s _95913 t R x' x h3) (fun h0 : term963 A s x' => @lem7168594 A B s _95913 t R x' x h0 h3) (fun h0 : term380 A B R x' x => @lem7168592 A B y s _95913 t R x' x h1 h0 h2 h3)). Qed.
Lemma lem7168600 {A B : Type'} (y : A -> B) (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _95913) (h2 : term940 A B x y t R s) (h3 : term987 A B s _95913 t R x' x) : False.
Proof. exact (or_elim (@lem7165301 A B s _95913 t R x' x h3) (fun h0 : term963 A s x' => @lem7168598 A B s _95913 t R x' x h0 h3) (fun h0 : term983 A B _95913 t R x' x => @lem7168596 A B y s _95913 t R x' x h1 h0 h2 h3)). Qed.
Lemma lem7168601 {A B : Type'} (_95913 : type830 A B) (x' : A) (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term728 A B _95913) (h2 : term774 A B s _95913 t R x' x) (h3 : term940 A B x y t R s) : False.
Proof. exact (or_elim (@lem7165129 A B s _95913 t R x' x h2) (fun h0 : term987 A B s _95913 t R x' x => @lem7168600 A B y s _95913 t R x' x h1 h3 h0) (fun h0 : term981 A B s _95913 t R x' x => @lem7168599 A B y s _95913 t R x' x h1 h3 h0)). Qed.
Lemma lem7168602 {A B : Type'} (_95913 : type830 A B) (x' : A) (x : B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term728 A B _95913) (h2 : term774 A B s _95913 t R x' x) (h3 : term639 A B x t R s) : False.
Proof. exact (ex_elim (@lem7164806 A B x t R s h3) (fun y : A -> B => fun h0 : term942 A B x t R s y => @lem7168601 A B _95913 x' x y t R s h1 h2 h0)). Qed.
Lemma lem7168603 {A B : Type'} (_95913 : type830 A B) (x' : A) (x : B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term728 A B _95913) (h2 : term774 A B s _95913 t R x' x) (h3 : term639 A B x t R s) : (term774 A B s _95913 t R x' x) = False.
Proof. exact (prop_ext (fun h4 : term774 A B s _95913 t R x' x => @lem7168602 A B _95913 x' x t R s h1 h2 h3) (fun h4 : False => @lem7164146 A B s _95913 t R x' x h2)). Qed.
Lemma lem7168604 {A B : Type'} (_95913 : type830 A B) (x' : A) (x : B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term728 A B _95913) (h2 : term774 A B s _95913 t R x' x) (h3 : term639 A B x t R s) : False.
Proof. exact (EQ_MP (@lem7168603 A B _95913 x' x t R s h1 h2 h3) (@lem7164146 A B s _95913 t R x' x h2)). Qed.
Lemma lem7168605 {A B : Type'} (x' : A) (_95913 : type830 A B) (x : B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term728 A B _95913) (h2 : term639 A B x t R s) : term773 A B s _95913 t R x' x.
Proof. exact (fun h0 : term774 A B s _95913 t R x' x => @lem7168604 A B _95913 x' x t R s h1 h0 h2). Qed.
Lemma lem7168606 {A B : Type'} (x' : A) (_95913 : type830 A B) (x : B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term728 A B _95913) (h2 : term639 A B x t R s) : (term660 A B s R x' x) = (term731 A B s _95913 t R x' x).
Proof. exact (EQ_MP (@lem7164145 A B s _95913 t R x' x) (@lem7168605 A B x' _95913 x t R s h1 h2)). Qed.
Lemma lem7168611 {A B : Type'} (_95913 : type830 A B) (x : B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term728 A B _95913) (h2 : term639 A B x t R s) : term733 A B s _95913 t R x.
Proof. exact (fun x' : A => @lem7168606 A B x' _95913 x t R s h1 h2). Qed.
Lemma lem7168612 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (_95913 : type830 A B) (h1 : term728 A B _95913) : term734 A B s _95913 t R x.
Proof. exact (fun h0 : term639 A B x t R s => @lem7168611 A B _95913 x t R s h1 h0). Qed.
Lemma lem7168613 {A B : Type'} (s : A -> Prop) (_95913 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : B) : term753 A B s _95913 t R x.
Proof. exact (fun h0 : term728 A B _95913 => @lem7168612 A B s t R x _95913 h0). Qed.
Lemma lem7168618 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : term756 A B s t R x.
Proof. exact (fun _95913 : type830 A B => @lem7168613 A B s _95913 t R x). Qed.
Lemma lem7168623 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : B) : term760 A B t R x.
Proof. exact (fun s : A -> Prop => @lem7168618 A B s t R x). Qed.
Lemma lem7168628 {A B : Type'} (R : type1413 A B) (x : B) : term764 A B R x.
Proof. exact (fun t : B -> Prop => @lem7168623 A B t R x). Qed.
Lemma lem7168633 {A B : Type'} (x : B) : term768 A B x.
Proof. exact (fun R : type1413 A B => @lem7168628 A B R x). Qed.
Lemma lem7168638 {A B : Type'} : term772 A B.
Proof. exact (fun x : B => @lem7168633 A B x). Qed.
Lemma lem7168639 {A B : Type'} : term771 A B.
Proof. exact (EQ_MP (@lem7164139 A B) (@lem7168638 A B)). Qed.
Lemma lem7168640 {A B : Type'} (x : B) : term1239 A B x.
Proof. exact (@lem7168639 A B x). Qed.
Lemma lem7168641 {A B : Type'} (x : B) : (term1239 A B x) = (term767 A B x).
Proof. exact (eq_refl (term1239 A B x)). Qed.
Lemma lem7168642 {A B : Type'} (x : B) : term767 A B x.
Proof. exact (EQ_MP (@lem7168641 A B x) (@lem7168640 A B x)). Qed.
Lemma lem7168643 {A B : Type'} (x : B) (R : type1413 A B) : term1240 A B x R.
Proof. exact (@lem7168642 A B x R). Qed.
Lemma lem7168644 {A B : Type'} (R : type1413 A B) (x : B) : (term1240 A B x R) = (term763 A B R x).
Proof. exact (eq_refl (term1240 A B x R)). Qed.
Lemma lem7168645 {A B : Type'} (R : type1413 A B) (x : B) : term763 A B R x.
Proof. exact (EQ_MP (@lem7168644 A B R x) (@lem7168643 A B x R)). Qed.
Lemma lem7168646 {A B : Type'} (R : type1413 A B) (x : B) (t : B -> Prop) : term1241 A B R x t.
Proof. exact (@lem7168645 A B R x t). Qed.
Lemma lem7168647 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : B) : (term1241 A B R x t) = (term759 A B t R x).
Proof. exact (eq_refl (term1241 A B R x t)). Qed.
Lemma lem7168648 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : B) : term759 A B t R x.
Proof. exact (EQ_MP (@lem7168647 A B t R x) (@lem7168646 A B R x t)). Qed.
Lemma lem7168649 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : B) (s : A -> Prop) : term1242 A B t R x s.
Proof. exact (@lem7168648 A B t R x s). Qed.
Lemma lem7168650 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : (term1242 A B t R x s) = (term740 A B s t R x).
Proof. exact (eq_refl (term1242 A B t R x s)). Qed.
Lemma lem7168651 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : term740 A B s t R x.
Proof. exact (EQ_MP (@lem7168650 A B s t R x) (@lem7168649 A B t R x s)). Qed.
Lemma lem7168653 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : term681 A B s t R x.
Proof. exact (@lem7163846 A B s t R x (@lem7168651 A B s t R x)). Qed.
Lemma lem7168654 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (h1 : term682 A B s t R x) : False.
Proof. exact (@lem7168653 A B s t R x (@lem7163692 A B s t R x h1)). Qed.
Lemma lem7168655 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (h1 : term682 A B s t R x) : (term682 A B s t R x) = False.
Proof. exact (prop_ext (fun h2 : term682 A B s t R x => @lem7168654 A B s t R x h1) (fun h2 : False => @lem7163692 A B s t R x h1)). Qed.
Lemma lem7168656 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (h1 : term682 A B s t R x) : False.
Proof. exact (EQ_MP (@lem7168655 A B s t R x h1) (@lem7163692 A B s t R x h1)). Qed.
Lemma lem7168657 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : term681 A B s t R x.
Proof. exact (fun h0 : term682 A B s t R x => @lem7168656 A B s t R x h0). Qed.
Lemma lem7168658 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : term680 A B s t R x.
Proof. exact (EQ_MP (@lem7163691 A B s t R x) (@lem7168657 A B s t R x)). Qed.
Lemma lem7168659 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : term627 A B s t R x.
Proof. exact (EQ_MP (@lem7163687 A B s t R x) (@lem7168658 A B s t R x)). Qed.
Lemma lem7168660 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : term626 A B s t R x.
Proof. exact (EQ_MP (@lem7163513 A B s t R x) (@lem7168659 A B s t R x)). Qed.
Lemma lem7168661 {A B : Type'} (R : type1413 A B) (s : A -> Prop) (x : B) (t : B -> Prop) (h1 : term34 A B s t R) (h2 : @FINITE A s) (h3 : @IN B x t) : (term623 A B s R x) = (term101 A B s t R x).
Proof. exact (@lem7168660 A B s t R x (@lem7163462 A B R s x t h1 h2 h3)). Qed.
Lemma lem7168662 {A B : Type'} (R : type1413 A B) (s : A -> Prop) (x : B) (t : B -> Prop) (h1 : term34 A B s t R) (h2 : @FINITE A s) (h3 : @IN B x t) : (term1243 A B s R x) = (term103 A B s t R x).
Proof. exact (MK_COMB (@lem7163450 A) (@lem7168661 A B R s x t h1 h2 h3)). Qed.
Lemma lem7168663 {A B : Type'} (g : A -> real) (R : type1413 A B) (s : A -> Prop) (x : B) (t : B -> Prop) (h1 : term34 A B s t R) (h2 : @FINITE A s) (h3 : @IN B x t) : (term610 A B s R x g) = (term105 A B s t R x g).
Proof. exact (MK_COMB (@lem7168662 A B R s x t h1 h2 h3) (@lem7163449 A g)). Qed.
Lemma lem7168664 {A B : Type'} (g : A -> real) (R : type1413 A B) (s : A -> Prop) (x : B) (t : B -> Prop) (h1 : term34 A B s t R) (h2 : @FINITE A s) (h3 : @IN B x t) : (term609 A B s R g x) = (term616 A B s t R g x).
Proof. exact (EQ_MP (@lem7163448 A B s t R g x) (@lem7168663 A B g R s x t h1 h2 h3)). Qed.
Lemma lem7168665 {A B : Type'} (g : A -> real) (R : type1413 A B) (s : A -> Prop) (x : B) (t : B -> Prop) (h1 : term34 A B s t R) (h2 : @FINITE A s) (h3 : @IN B x t) : (@IN B x t) = ((term609 A B s R g x) = (term616 A B s t R g x)).
Proof. exact (prop_ext (fun h4 : @IN B x t => @lem7168664 A B g R s x t h1 h2 h3) (fun h4 : (term609 A B s R g x) = (term616 A B s t R g x) => @lem7163398 B x t h3)). Qed.
Lemma lem7168666 {A B : Type'} (g : A -> real) (R : type1413 A B) (s : A -> Prop) (x : B) (t : B -> Prop) (h1 : term34 A B s t R) (h2 : @FINITE A s) (h3 : @IN B x t) : (term609 A B s R g x) = (term616 A B s t R g x).
Proof. exact (EQ_MP (@lem7168665 A B g R s x t h1 h2 h3) (@lem7163398 B x t h3)). Qed.
Lemma lem7168667 {A B : Type'} (g : A -> real) (x : B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term34 A B s t R) (h2 : @FINITE A s) : term1244 A B s t R g x.
Proof. exact (fun h0 : @IN B x t => @lem7168666 A B g R s x t h1 h2 h0). Qed.
Lemma lem7168672 {A B : Type'} (g : A -> real) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term34 A B s t R) (h2 : @FINITE A s) : term1245 A B s t R g.
Proof. exact (fun x : B => @lem7168667 A B g x t R s h1 h2). Qed.
Lemma lem7168673 {A B : Type'} (g : A -> real) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term34 A B s t R) (h2 : @FINITE A s) : (term115 A B t s R g) = (term109 A B s t R g).
Proof. exact (@lem7163397 A B s t R g (@lem7168672 A B g t R s h1 h2)). Qed.
Lemma lem7168674 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (g : A -> real) (h1 : term34 A B s t R) (h2 : @FINITE A s) (h3 : (term109 A B s t R g) = (@sum A s g)) : (term115 A B t s R g) = (@sum A s g).
Proof. exact (EQ_MP (@lem7163393 A B t R s g h3) (@lem7168673 A B g t R s h1 h2)). Qed.
Lemma lem7168675 {A B : Type'} (g : A -> real) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term34 A B s t R) (h2 : @FINITE A s) : term1246 A B t R s g.
Proof. exact (fun h0 : (term109 A B s t R g) = (@sum A s g) => @lem7168674 A B t R s g h1 h2 h0). Qed.
Lemma lem7168676 {A B : Type'} (g : A -> real) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term34 A B s t R) (h2 : @FINITE A s) : term1247 A B t R s g.
Proof. exact (conj (@lem7163378 A B t R s h1 h2) (@lem7168675 A B g t R s h1 h2)). Qed.
Lemma lem7168677 {A B : Type'} (g : A -> real) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term34 A B s t R) (h2 : @FINITE A s) : term117 A B t R s g.
Proof. exact (@lem7161079 A B t R s g (@lem7168676 A B g t R s h1 h2)). Qed.
Lemma lem7168678 {A B : Type'} (g : A -> real) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term34 A B s t R) (h2 : @FINITE A s) : term116 A B t R s g.
Proof. exact (EQ_MP (@lem7161076 A B t R g s h2) (@lem7168677 A B g t R s h1 h2)). Qed.
Lemma lem7168679 {A B : Type'} (g : A -> real) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term34 A B s t R) (h2 : @FINITE A s) : (term115 A B t s R g) = (@sum A s g).
Proof. exact (@lem7168678 A B g t R s h1 h2 (@lem7160887 A B t R s g)). Qed.
Lemma lem7168680 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (h1 : term33 A B s t R) : term34 A B s t R.
Proof. exact (proj2 (@lem7160888 A B s t R h1)). Qed.
Lemma lem7168681 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (h1 : term33 A B s t R) : @FINITE A s.
Proof. exact (proj1 (@lem7160888 A B s t R h1)). Qed.
Lemma lem7168682 {A B : Type'} (g : A -> real) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term34 A B s t R) (h2 : @FINITE A s) : (term34 A B s t R) = ((term115 A B t s R g) = (@sum A s g)).
Proof. exact (prop_ext (fun h3 : term34 A B s t R => @lem7168679 A B g t R s h1 h2) (fun h3 : (term115 A B t s R g) = (@sum A s g) => @lem7160889 A B s t R h1)). Qed.
Lemma lem7168683 {A B : Type'} (g : A -> real) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term34 A B s t R) (h2 : @FINITE A s) : (term115 A B t s R g) = (@sum A s g).
Proof. exact (EQ_MP (@lem7168682 A B g t R s h1 h2) (@lem7160889 A B s t R h1)). Qed.
Lemma lem7168684 {A B : Type'} (g : A -> real) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term34 A B s t R) (h2 : @FINITE A s) : (@FINITE A s) = ((term115 A B t s R g) = (@sum A s g)).
Proof. exact (prop_ext (fun h3 : @FINITE A s => @lem7168683 A B g t R s h1 h2) (fun h3 : (term115 A B t s R g) = (@sum A s g) => @lem7160890 A s h2)). Qed.
Lemma lem7168685 {A B : Type'} (g : A -> real) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term34 A B s t R) (h2 : @FINITE A s) : (term115 A B t s R g) = (@sum A s g).
Proof. exact (EQ_MP (@lem7168684 A B g t R s h1 h2) (@lem7160890 A s h2)). Qed.
Lemma lem7168686 {A B : Type'} (g : A -> real) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (h1 : @FINITE A s) (h2 : term33 A B s t R) : (term34 A B s t R) = ((term115 A B t s R g) = (@sum A s g)).
Proof. exact (prop_ext (fun h3 : term34 A B s t R => @lem7168685 A B g t R s h3 h1) (fun h3 : (term115 A B t s R g) = (@sum A s g) => @lem7168680 A B s t R h2)). Qed.
Lemma lem7168687 {A B : Type'} (g : A -> real) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (h1 : @FINITE A s) (h2 : term33 A B s t R) : (term115 A B t s R g) = (@sum A s g).
Proof. exact (EQ_MP (@lem7168686 A B g s t R h1 h2) (@lem7168680 A B s t R h2)). Qed.
Lemma lem7168688 {A B : Type'} (g : A -> real) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (h1 : term33 A B s t R) : (@FINITE A s) = ((term115 A B t s R g) = (@sum A s g)).
Proof. exact (prop_ext (fun h2 : @FINITE A s => @lem7168687 A B g s t R h2 h1) (fun h2 : (term115 A B t s R g) = (@sum A s g) => @lem7168681 A B s t R h1)). Qed.
Lemma lem7168689 {A B : Type'} (g : A -> real) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (h1 : term33 A B s t R) : (term115 A B t s R g) = (@sum A s g).
Proof. exact (EQ_MP (@lem7168688 A B g s t R h1) (@lem7168681 A B s t R h1)). Qed.
Lemma lem7168690 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (g : A -> real) : term1248 A B t R s g.
Proof. exact (fun h0 : term33 A B s t R => @lem7168689 A B g s t R h0). Qed.
Lemma lem7168695 {A B : Type'} (R : type1413 A B) (s : A -> Prop) (g : A -> real) : term1249 A B R s g.
Proof. exact (fun t : B -> Prop => @lem7168690 A B t R s g). Qed.
Lemma lem7168700 {A B : Type'} (R : type1413 A B) (g : A -> real) : term1250 A B R g.
Proof. exact (fun s : A -> Prop => @lem7168695 A B R s g). Qed.
Lemma lem7168705 {A B : Type'} (R : type1413 A B) : term1251 A B R.
Proof. exact (fun g : A -> real => @lem7168700 A B R g). Qed.
Lemma lem7168710 {A B : Type'} : term1252 A B.
Proof. exact (fun R : type1413 A B => @lem7168705 A B R). Qed.
