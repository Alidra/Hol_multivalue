Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SIMPLE_IMAGE_term_abbrevs.
Require Import EXTENSION_spec.
Require Import IN_IMAGE_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm18394_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3184747_spec.
Require Import thm3184750_spec.
Lemma lem3392839 {A B : Type'} (y : B) : term0 A B y.
Proof. exact (@lem3206070 A B y). Qed.
Lemma lem3392840 {A B : Type'} (y : B) : (term0 A B y) = (term1 A B y).
Proof. exact (eq_refl (term0 A B y)). Qed.
Lemma lem3392841 {A B : Type'} (y : B) : term1 A B y.
Proof. exact (EQ_MP (@lem3392840 A B y) (@lem3392839 A B y)). Qed.
Lemma lem3392842 {A B : Type'} (y : B) (s : A -> Prop) : term2 A B y s.
Proof. exact (@lem3392841 A B y s). Qed.
Lemma lem3392843 {A B : Type'} (y : B) (s : A -> Prop) : (term2 A B y s) = (term3 A B y s).
Proof. exact (eq_refl (term2 A B y s)). Qed.
Lemma lem3392844 {A B : Type'} (y : B) (s : A -> Prop) : term3 A B y s.
Proof. exact (EQ_MP (@lem3392843 A B y s) (@lem3392842 A B y s)). Qed.
Lemma lem3392845 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) : term4 A B y s f.
Proof. exact (@lem3392844 A B y s f). Qed.
Lemma lem3392846 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term4 A B y s f) = ((term5 A B y f s) = (term6 A B y f s)).
Proof. exact (eq_refl (term4 A B y s f)). Qed.
Lemma lem3392879 {_83064 : Type'} : term7 _83064.
Proof. exact (EQ_MP (@lem3184750 _83064) (@lem3184747 _83064)). Qed.
Lemma lem3392880 {_83064 : Type'} (P : type919 _83064) : term8 _83064 P.
Proof. exact (@lem3392879 _83064 P). Qed.
Lemma lem3392881 {_83064 : Type'} (P : type919 _83064) : (term8 _83064 P) = (term9 _83064 P).
Proof. exact (eq_refl (term8 _83064 P)). Qed.
Lemma lem3392882 {_83064 : Type'} (P : type919 _83064) : term9 _83064 P.
Proof. exact (EQ_MP (@lem3392881 _83064 P) (@lem3392880 _83064 P)). Qed.
Lemma lem3392883 {_83064 : Type'} (P : type919 _83064) (x : _83064) : term10 _83064 P x.
Proof. exact (@lem3392882 _83064 P x). Qed.
Lemma lem3392884 {_83064 : Type'} (P : type919 _83064) (x : _83064) : (term10 _83064 P x) = ((term11 _83064 x P) = (term12 _83064 P x)).
Proof. exact (eq_refl (term10 _83064 P x)). Qed.
Lemma lem3392886 {A : Type'} (s : A -> Prop) : term13 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem3392887 {A : Type'} (s : A -> Prop) : (term13 A s) = (term14 A s).
Proof. exact (eq_refl (term13 A s)). Qed.
Lemma lem3392888 {A : Type'} (s : A -> Prop) : term14 A s.
Proof. exact (EQ_MP (@lem3392887 A s) (@lem3392886 A s)). Qed.
Lemma lem3392889 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term15 A s t.
Proof. exact (@lem3392888 A s t). Qed.
Lemma lem3392890 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term15 A s t) = ((s = t) = (term16 A s t)).
Proof. exact (eq_refl (term15 A s t)). Qed.
Lemma lem3392903 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term16 A s t).
Proof. exact (EQ_MP (@lem3392890 A s t) (@lem3392889 A s t)). Qed.
Lemma lem3392904 {_88132 : Type'} (s : _88132 -> Prop) (t : _88132 -> Prop) : (s = t) = (term16 _88132 s t).
Proof. exact (@lem3392903 _88132 s t). Qed.
Lemma lem3392905 {_88128 _88132 : Type'} (f : _88128 -> _88132) (s : _88128 -> Prop) : ((term17 _88128 _88132 s f) = (@IMAGE _88128 _88132 f s)) = (term18 _88128 _88132 f s).
Proof. exact (@lem3392904 _88132 (term17 _88128 _88132 s f) (@IMAGE _88128 _88132 f s)). Qed.
Lemma lem3392917 {_83064 : Type'} (P : type919 _83064) (x : _83064) : (term11 _83064 x P) = (term12 _83064 P x).
Proof. exact (EQ_MP (@lem3392884 _83064 P x) (@lem3392883 _83064 P x)). Qed.
Lemma lem3392918 {_88132 : Type'} (P : type919 _88132) (x : _88132) : (term11 _88132 x P) = (term12 _88132 P x).
Proof. exact (@lem3392917 _88132 P x). Qed.
Lemma lem3392919 {_88128 _88132 : Type'} (s : _88128 -> Prop) (f : _88128 -> _88132) (x : _88132) : (term19 _88128 _88132 x s f) = (term20 _88128 _88132 s f x).
Proof. exact (@lem3392918 _88132 (term21 _88128 _88132 s f) x). Qed.
Lemma lem3392920 {_88128 _88132 : Type'} (GEN_PVAR_23 : _88132) (s : _88128 -> Prop) (f : _88128 -> _88132) : (term22 _88128 _88132 s f GEN_PVAR_23) = (term23 _88128 _88132 GEN_PVAR_23 s f).
Proof. exact (eq_refl (term22 _88128 _88132 s f GEN_PVAR_23)). Qed.
Lemma lem3392921 {_88128 _88132 : Type'} (s : _88128 -> Prop) (f : _88128 -> _88132) : (term24 _88128 _88132 s f) = (term25 _88128 _88132 s f).
Proof. exact (fun_ext (fun GEN_PVAR_23 : _88132 => @lem3392920 _88128 _88132 GEN_PVAR_23 s f)). Qed.
Lemma lem3392922 {_88132 : Type'} : (@GSPEC _88132) = (@GSPEC _88132).
Proof. exact (eq_refl (@GSPEC _88132)). Qed.
Lemma lem3392923 {_88128 _88132 : Type'} (s : _88128 -> Prop) (f : _88128 -> _88132) : (term26 _88128 _88132 s f) = (term17 _88128 _88132 s f).
Proof. exact (MK_COMB (@lem3392922 _88132) (@lem3392921 _88128 _88132 s f)). Qed.
Lemma lem3392924 {_88132 : Type'} (x : _88132) : (@IN _88132 x) = (@IN _88132 x).
Proof. exact (eq_refl (@IN _88132 x)). Qed.
Lemma lem3392925 {_88128 _88132 : Type'} (x : _88132) (s : _88128 -> Prop) (f : _88128 -> _88132) : (term19 _88128 _88132 x s f) = (term27 _88128 _88132 x s f).
Proof. exact (MK_COMB (@lem3392924 _88132 x) (@lem3392923 _88128 _88132 s f)). Qed.
Lemma lem3392926 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3392927 {_88128 _88132 : Type'} (x : _88132) (s : _88128 -> Prop) (f : _88128 -> _88132) : (term28 _88128 _88132 x s f) = (term29 _88128 _88132 x s f).
Proof. exact (MK_COMB (@lem3392926) (@lem3392925 _88128 _88132 x s f)). Qed.
Lemma lem3392928 {_88128 _88132 : Type'} (x : _88132) (s : _88128 -> Prop) (f : _88128 -> _88132) : (term20 _88128 _88132 s f x) = (term30 _88128 _88132 x s f).
Proof. exact (eq_refl (term20 _88128 _88132 s f x)). Qed.
Lemma lem3392929 {_88128 _88132 : Type'} (x : _88132) (s : _88128 -> Prop) (f : _88128 -> _88132) : ((term19 _88128 _88132 x s f) = (term20 _88128 _88132 s f x)) = ((term27 _88128 _88132 x s f) = (term30 _88128 _88132 x s f)).
Proof. exact (MK_COMB (@lem3392927 _88128 _88132 x s f) (@lem3392928 _88128 _88132 x s f)). Qed.
Lemma lem3392930 {_88128 _88132 : Type'} (x : _88132) (s : _88128 -> Prop) (f : _88128 -> _88132) : (term27 _88128 _88132 x s f) = (term30 _88128 _88132 x s f).
Proof. exact (EQ_MP (@lem3392929 _88128 _88132 x s f) (@lem3392919 _88128 _88132 s f x)). Qed.
Lemma lem3392936 {A B : Type'} (f : A -> B) (y : A) : (term31 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3392937 {_88132 : Type'} (f : type1538 _88132) (y : Prop) : (term32 _88132 f y) = (f y).
Proof. exact (@lem3392936 Prop (_88132 -> Prop) f y). Qed.
Lemma lem3392938 {_88128 _88132 : Type'} (x : _88132) (x' : _88128) (s : _88128 -> Prop) : (term33 _88128 _88132 x x' s) = (term34 _88128 _88132 x x' s).
Proof. exact (@lem3392937 _88132 (term35 _88132 x) (@IN _88128 x' s)). Qed.
Lemma lem3392939 {_88132 : Type'} (p : Prop) (x : _88132) : (term36 _88132 x p) = (term37 _88132 p x).
Proof. exact (eq_refl (term36 _88132 x p)). Qed.
Lemma lem3392940 {_88132 : Type'} (x : _88132) : (term38 _88132 x) = (term35 _88132 x).
Proof. exact (fun_ext (fun p : Prop => @lem3392939 _88132 p x)). Qed.
Lemma lem3392941 {_88128 : Type'} (x : _88128) (s : _88128 -> Prop) : (@IN _88128 x s) = (@IN _88128 x s).
Proof. exact (eq_refl (@IN _88128 x s)). Qed.
Lemma lem3392942 {_88128 _88132 : Type'} (x : _88132) (x' : _88128) (s : _88128 -> Prop) : (term33 _88128 _88132 x x' s) = (term34 _88128 _88132 x x' s).
Proof. exact (MK_COMB (@lem3392940 _88132 x) (@lem3392941 _88128 x' s)). Qed.
Lemma lem3392943 {_88132 : Type'} : (@eq (_88132 -> Prop)) = (@eq (_88132 -> Prop)).
Proof. exact (eq_refl (@eq (_88132 -> Prop))). Qed.
Lemma lem3392944 {_88128 _88132 : Type'} (x : _88132) (x' : _88128) (s : _88128 -> Prop) : (term39 _88128 _88132 x x' s) = (term40 _88128 _88132 x x' s).
Proof. exact (MK_COMB (@lem3392943 _88132) (@lem3392942 _88128 _88132 x x' s)). Qed.
Lemma lem3392945 {_88128 _88132 : Type'} (x : _88128) (s : _88128 -> Prop) (x' : _88132) : (term34 _88128 _88132 x' x s) = (term41 _88128 _88132 x s x').
Proof. exact (eq_refl (term34 _88128 _88132 x' x s)). Qed.
Lemma lem3392946 {_88128 _88132 : Type'} (x : _88128) (s : _88128 -> Prop) (x' : _88132) : ((term33 _88128 _88132 x' x s) = (term34 _88128 _88132 x' x s)) = ((term34 _88128 _88132 x' x s) = (term41 _88128 _88132 x s x')).
Proof. exact (MK_COMB (@lem3392944 _88128 _88132 x' x s) (@lem3392945 _88128 _88132 x s x')). Qed.
Lemma lem3392947 {_88128 _88132 : Type'} (x : _88128) (s : _88128 -> Prop) (x' : _88132) : (term34 _88128 _88132 x' x s) = (term41 _88128 _88132 x s x').
Proof. exact (EQ_MP (@lem3392946 _88128 _88132 x s x') (@lem3392938 _88128 _88132 x' x s)). Qed.
Lemma lem3392954 {_88128 _88132 : Type'} (f : _88128 -> _88132) (x : _88128) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem3392955 {_88128 _88132 : Type'} (s : _88128 -> Prop) (x : _88132) (f : _88128 -> _88132) (x' : _88128) : (term42 _88128 _88132 x s f x') = (term43 _88128 _88132 s x f x').
Proof. exact (MK_COMB (@lem3392947 _88128 _88132 x' s x) (@lem3392954 _88128 _88132 f x')). Qed.
Lemma lem3392957 {A B : Type'} (f : A -> B) (y : A) : (term31 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3392958 {_88132 : Type'} (f : _88132 -> Prop) (y : _88132) : (term44 _88132 f y) = (f y).
Proof. exact (@lem3392957 _88132 Prop f y). Qed.
Lemma lem3392959 {_88128 _88132 : Type'} (s : _88128 -> Prop) (x : _88132) (f : _88128 -> _88132) (x' : _88128) : (term45 _88128 _88132 s x f x') = (term43 _88128 _88132 s x f x').
Proof. exact (@lem3392958 _88132 (term41 _88128 _88132 x' s x) (f x')). Qed.
Lemma lem3392960 {_88128 _88132 : Type'} (x : _88128) (s : _88128 -> Prop) (x' : _88132) (t : _88132) : (term46 _88128 _88132 x s x' t) = (term47 _88128 _88132 x s x' t).
Proof. exact (eq_refl (term46 _88128 _88132 x s x' t)). Qed.
Lemma lem3392961 {_88128 _88132 : Type'} (x : _88128) (s : _88128 -> Prop) (x' : _88132) : (term48 _88128 _88132 x s x') = (term41 _88128 _88132 x s x').
Proof. exact (fun_ext (fun t : _88132 => @lem3392960 _88128 _88132 x s x' t)). Qed.
Lemma lem3392962 {_88128 _88132 : Type'} (f : _88128 -> _88132) (x : _88128) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem3392963 {_88128 _88132 : Type'} (s : _88128 -> Prop) (x : _88132) (f : _88128 -> _88132) (x' : _88128) : (term45 _88128 _88132 s x f x') = (term43 _88128 _88132 s x f x').
Proof. exact (MK_COMB (@lem3392961 _88128 _88132 x' s x) (@lem3392962 _88128 _88132 f x')). Qed.
Lemma lem3392964 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3392965 {_88128 _88132 : Type'} (s : _88128 -> Prop) (x : _88132) (f : _88128 -> _88132) (x' : _88128) : (term49 _88128 _88132 s x f x') = (term50 _88128 _88132 s x f x').
Proof. exact (MK_COMB (@lem3392964) (@lem3392963 _88128 _88132 s x f x')). Qed.
Lemma lem3392966 {_88128 _88132 : Type'} (s : _88128 -> Prop) (x : _88132) (f : _88128 -> _88132) (x' : _88128) : (term43 _88128 _88132 s x f x') = (term51 _88128 _88132 s x f x').
Proof. exact (eq_refl (term43 _88128 _88132 s x f x')). Qed.
Lemma lem3392967 {_88128 _88132 : Type'} (s : _88128 -> Prop) (x : _88132) (f : _88128 -> _88132) (x' : _88128) : ((term45 _88128 _88132 s x f x') = (term43 _88128 _88132 s x f x')) = ((term43 _88128 _88132 s x f x') = (term51 _88128 _88132 s x f x')).
Proof. exact (MK_COMB (@lem3392965 _88128 _88132 s x f x') (@lem3392966 _88128 _88132 s x f x')). Qed.
Lemma lem3392968 {_88128 _88132 : Type'} (s : _88128 -> Prop) (x : _88132) (f : _88128 -> _88132) (x' : _88128) : (term43 _88128 _88132 s x f x') = (term51 _88128 _88132 s x f x').
Proof. exact (EQ_MP (@lem3392967 _88128 _88132 s x f x') (@lem3392959 _88128 _88132 s x f x')). Qed.
Lemma lem3392975 {_88128 _88132 : Type'} (s : _88128 -> Prop) (x : _88132) (f : _88128 -> _88132) (x' : _88128) : (term42 _88128 _88132 x s f x') = (term51 _88128 _88132 s x f x').
Proof. exact (TRANS (@lem3392955 _88128 _88132 s x f x') (@lem3392968 _88128 _88132 s x f x')). Qed.
Lemma lem3392976 {_88128 _88132 : Type'} (s : _88128 -> Prop) (x : _88132) (f : _88128 -> _88132) : (term52 _88128 _88132 x s f) = (term53 _88128 _88132 s x f).
Proof. exact (fun_ext (fun x' : _88128 => @lem3392975 _88128 _88132 s x f x')). Qed.
Lemma lem3392977 {_88128 : Type'} : (@ex _88128) = (@ex _88128).
Proof. exact (eq_refl (@ex _88128)). Qed.
Lemma lem3392978 {_88128 _88132 : Type'} (s : _88128 -> Prop) (x : _88132) (f : _88128 -> _88132) : (term30 _88128 _88132 x s f) = (term54 _88128 _88132 s x f).
Proof. exact (MK_COMB (@lem3392977 _88128) (@lem3392976 _88128 _88132 s x f)). Qed.
Lemma lem3392983 {_88128 _88132 : Type'} (s : _88128 -> Prop) (x : _88132) (f : _88128 -> _88132) : (term27 _88128 _88132 x s f) = (term54 _88128 _88132 s x f).
Proof. exact (TRANS (@lem3392930 _88128 _88132 x s f) (@lem3392978 _88128 _88132 s x f)). Qed.
Lemma lem3392984 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3392985 {_88128 _88132 : Type'} (s : _88128 -> Prop) (x : _88132) (f : _88128 -> _88132) : (term29 _88128 _88132 x s f) = (term55 _88128 _88132 s x f).
Proof. exact (MK_COMB (@lem3392984) (@lem3392983 _88128 _88132 s x f)). Qed.
Lemma lem3392987 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term5 A B y f s) = (term6 A B y f s).
Proof. exact (EQ_MP (@lem3392846 A B y f s) (@lem3392845 A B y s f)). Qed.
Lemma lem3392988 {_88128 _88132 : Type'} (y : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) : (term5 _88128 _88132 y f s) = (term6 _88128 _88132 y f s).
Proof. exact (@lem3392987 _88128 _88132 y f s). Qed.
Lemma lem3392989 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) : (term5 _88128 _88132 x f s) = (term6 _88128 _88132 x f s).
Proof. exact (@lem3392988 _88128 _88132 x f s). Qed.
Lemma lem3393000 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) : ((term27 _88128 _88132 x s f) = (term5 _88128 _88132 x f s)) = ((term54 _88128 _88132 s x f) = (term6 _88128 _88132 x f s)).
Proof. exact (MK_COMB (@lem3392985 _88128 _88132 s x f) (@lem3392989 _88128 _88132 x f s)). Qed.
Lemma lem3393005 {_88128 _88132 : Type'} (f : _88128 -> _88132) (s : _88128 -> Prop) : (term56 _88128 _88132 f s) = (term57 _88128 _88132 f s).
Proof. exact (fun_ext (fun x : _88132 => @lem3393000 _88128 _88132 x f s)). Qed.
Lemma lem3393006 {_88132 : Type'} : (@all _88132) = (@all _88132).
Proof. exact (eq_refl (@all _88132)). Qed.
Lemma lem3393007 {_88128 _88132 : Type'} (f : _88128 -> _88132) (s : _88128 -> Prop) : (term18 _88128 _88132 f s) = (term58 _88128 _88132 f s).
Proof. exact (MK_COMB (@lem3393006 _88132) (@lem3393005 _88128 _88132 f s)). Qed.
Lemma lem3393012 {_88128 _88132 : Type'} (f : _88128 -> _88132) (s : _88128 -> Prop) : ((term17 _88128 _88132 s f) = (@IMAGE _88128 _88132 f s)) = (term58 _88128 _88132 f s).
Proof. exact (TRANS (@lem3392905 _88128 _88132 f s) (@lem3393007 _88128 _88132 f s)). Qed.
Lemma lem3393013 {_88128 _88132 : Type'} (f : _88128 -> _88132) : (term59 _88128 _88132 f) = (term60 _88128 _88132 f).
Proof. exact (fun_ext (fun s : _88128 -> Prop => @lem3393012 _88128 _88132 f s)). Qed.
Lemma lem3393014 {_88128 : Type'} : (@all (_88128 -> Prop)) = (@all (_88128 -> Prop)).
Proof. exact (eq_refl (@all (_88128 -> Prop))). Qed.
Lemma lem3393015 {_88128 _88132 : Type'} (f : _88128 -> _88132) : (term61 _88128 _88132 f) = (term62 _88128 _88132 f).
Proof. exact (MK_COMB (@lem3393014 _88128) (@lem3393013 _88128 _88132 f)). Qed.
Lemma lem3393020 {_88128 _88132 : Type'} : (term63 _88128 _88132) = (term64 _88128 _88132).
Proof. exact (fun_ext (fun f : _88128 -> _88132 => @lem3393015 _88128 _88132 f)). Qed.
Lemma lem3393021 {_88128 _88132 : Type'} : (@all (_88128 -> _88132)) = (@all (_88128 -> _88132)).
Proof. exact (eq_refl (@all (_88128 -> _88132))). Qed.
Lemma lem3393022 {_88128 _88132 : Type'} : (term65 _88128 _88132) = (term66 _88128 _88132).
Proof. exact (MK_COMB (@lem3393021 _88128 _88132) (@lem3393020 _88128 _88132)). Qed.
Lemma lem3393027 {_88128 _88132 : Type'} : (term66 _88128 _88132) = (term65 _88128 _88132).
Proof. exact (SYM (@lem3393022 _88128 _88132)). Qed.
Lemma lem3393029 (p : Prop) : p = (term67 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3393030 {_88128 _88132 : Type'} : (term66 _88128 _88132) = (term68 _88128 _88132).
Proof. exact (@lem3393029 (term66 _88128 _88132)). Qed.
Lemma lem3393031 {_88128 _88132 : Type'} : (term68 _88128 _88132) = (term66 _88128 _88132).
Proof. exact (SYM (@lem3393030 _88128 _88132)). Qed.
Lemma lem3393032 {_88128 _88132 : Type'} (h1 : term69 _88128 _88132) : term69 _88128 _88132.
Proof. exact (h1). Qed.
Lemma lem3393035 {_88128 _88132 : Type'} (h1 : term68 _88128 _88132) : term68 _88128 _88132.
Proof. exact (h1). Qed.
Lemma lem3393036 {_88128 _88132 : Type'} : term70 _88128 _88132.
Proof. exact (fun h0 : term68 _88128 _88132 => @lem3393035 _88128 _88132 h0). Qed.
Lemma lem3393037 {_88128 _88132 : Type'} (h1 : term70 _88128 _88132) : term70 _88128 _88132.
Proof. exact (h1). Qed.
Lemma lem3393038 {_88128 _88132 : Type'} (h1 : term68 _88128 _88132) : term68 _88128 _88132.
Proof. exact (h1). Qed.
Lemma lem3393039 {_88128 _88132 : Type'} (h1 : term68 _88128 _88132) (h2 : term70 _88128 _88132) : term68 _88128 _88132.
Proof. exact (@lem3393037 _88128 _88132 h2 (@lem3393038 _88128 _88132 h1)). Qed.
Lemma lem3393040 {_88128 _88132 : Type'} (h1 : term68 _88128 _88132) : term71 _88128 _88132.
Proof. exact (fun h0 : term70 _88128 _88132 => @lem3393039 _88128 _88132 h1 h0). Qed.
Lemma lem3393041 {_88128 _88132 : Type'} (h1 : term70 _88128 _88132) : term70 _88128 _88132.
Proof. exact (h1). Qed.
Lemma lem3393042 {_88128 _88132 : Type'} (h1 : term68 _88128 _88132) (h2 : term70 _88128 _88132) : term68 _88128 _88132.
Proof. exact (@lem3393040 _88128 _88132 h1 (@lem3393041 _88128 _88132 h2)). Qed.
Lemma lem3393043 {_88128 _88132 : Type'} (h1 : term70 _88128 _88132) : term70 _88128 _88132.
Proof. exact (fun h0 : term68 _88128 _88132 => @lem3393042 _88128 _88132 h0 h1). Qed.
Lemma lem3393044 {_88128 _88132 : Type'} : term72 _88128 _88132.
Proof. exact (fun h0 : term70 _88128 _88132 => @lem3393043 _88128 _88132 h0). Qed.
Lemma lem3393047 {_88128 _88132 : Type'} : term70 _88128 _88132.
Proof. exact (@lem3393044 _88128 _88132 (@lem3393036 _88128 _88132)). Qed.
Lemma lem3393048 {_88128 _88132 : Type'} : term70 _88128 _88132.
Proof. exact (@lem3393047 _88128 _88132). Qed.
Lemma lem3393050 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3393051 {_88128 _88132 : Type'} : (term68 _88128 _88132) = (term73 _88128 _88132).
Proof. exact (@lem3393050 (term69 _88128 _88132)). Qed.
Lemma lem3393053 (t : Prop) : (term74 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3393054 {_88128 _88132 : Type'} : (term73 _88128 _88132) = (term66 _88128 _88132).
Proof. exact (@lem3393053 (term66 _88128 _88132)). Qed.
Lemma lem3393171 {_88128 _88132 : Type'} : (term68 _88128 _88132) = (term66 _88128 _88132).
Proof. exact (TRANS (@lem3393051 _88128 _88132) (@lem3393054 _88128 _88132)). Qed.
Lemma lem3393176 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (x' : _88128) (s : _88128 -> Prop) : (term75 _88128 _88132 x f x' s) = (term75 _88128 _88132 x f x' s).
Proof. exact (eq_refl (term75 _88128 _88132 x f x' s)). Qed.
Lemma lem3393177 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) : (term76 _88128 _88132 x f s) = (term76 _88128 _88132 x f s).
Proof. exact (fun_ext (fun x' : _88128 => @lem3393176 _88128 _88132 x f x' s)). Qed.
Lemma lem3393178 {_88128 : Type'} : (@ex _88128) = (@ex _88128).
Proof. exact (eq_refl (@ex _88128)). Qed.
Lemma lem3393179 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) : (term6 _88128 _88132 x f s) = (term6 _88128 _88132 x f s).
Proof. exact (MK_COMB (@lem3393178 _88128) (@lem3393177 _88128 _88132 x f s)). Qed.
Lemma lem3393184 {_88128 _88132 : Type'} (s : _88128 -> Prop) (x : _88132) (f : _88128 -> _88132) (x' : _88128) : (term51 _88128 _88132 s x f x') = (term51 _88128 _88132 s x f x').
Proof. exact (eq_refl (term51 _88128 _88132 s x f x')). Qed.
Lemma lem3393185 {_88128 _88132 : Type'} (s : _88128 -> Prop) (x : _88132) (f : _88128 -> _88132) : (term53 _88128 _88132 s x f) = (term53 _88128 _88132 s x f).
Proof. exact (fun_ext (fun x' : _88128 => @lem3393184 _88128 _88132 s x f x')). Qed.
Lemma lem3393186 {_88128 : Type'} : (@ex _88128) = (@ex _88128).
Proof. exact (eq_refl (@ex _88128)). Qed.
Lemma lem3393187 {_88128 _88132 : Type'} (s : _88128 -> Prop) (x : _88132) (f : _88128 -> _88132) : (term54 _88128 _88132 s x f) = (term54 _88128 _88132 s x f).
Proof. exact (MK_COMB (@lem3393186 _88128) (@lem3393185 _88128 _88132 s x f)). Qed.
Lemma lem3393188 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3393189 {_88128 _88132 : Type'} (s : _88128 -> Prop) (x : _88132) (f : _88128 -> _88132) : (term55 _88128 _88132 s x f) = (term55 _88128 _88132 s x f).
Proof. exact (MK_COMB (@lem3393188) (@lem3393187 _88128 _88132 s x f)). Qed.
Lemma lem3393190 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) : ((term54 _88128 _88132 s x f) = (term6 _88128 _88132 x f s)) = ((term54 _88128 _88132 s x f) = (term6 _88128 _88132 x f s)).
Proof. exact (MK_COMB (@lem3393189 _88128 _88132 s x f) (@lem3393179 _88128 _88132 x f s)). Qed.
Lemma lem3393191 {_88128 _88132 : Type'} (f : _88128 -> _88132) (s : _88128 -> Prop) : (term57 _88128 _88132 f s) = (term57 _88128 _88132 f s).
Proof. exact (fun_ext (fun x : _88132 => @lem3393190 _88128 _88132 x f s)). Qed.
Lemma lem3393192 {_88132 : Type'} : (@all _88132) = (@all _88132).
Proof. exact (eq_refl (@all _88132)). Qed.
Lemma lem3393193 {_88128 _88132 : Type'} (f : _88128 -> _88132) (s : _88128 -> Prop) : (term58 _88128 _88132 f s) = (term58 _88128 _88132 f s).
Proof. exact (MK_COMB (@lem3393192 _88132) (@lem3393191 _88128 _88132 f s)). Qed.
Lemma lem3393194 {_88128 _88132 : Type'} (f : _88128 -> _88132) : (term60 _88128 _88132 f) = (term60 _88128 _88132 f).
Proof. exact (fun_ext (fun s : _88128 -> Prop => @lem3393193 _88128 _88132 f s)). Qed.
Lemma lem3393195 {_88128 : Type'} : (@all (_88128 -> Prop)) = (@all (_88128 -> Prop)).
Proof. exact (eq_refl (@all (_88128 -> Prop))). Qed.
Lemma lem3393196 {_88128 _88132 : Type'} (f : _88128 -> _88132) : (term62 _88128 _88132 f) = (term62 _88128 _88132 f).
Proof. exact (MK_COMB (@lem3393195 _88128) (@lem3393194 _88128 _88132 f)). Qed.
Lemma lem3393197 {_88128 _88132 : Type'} : (term64 _88128 _88132) = (term64 _88128 _88132).
Proof. exact (fun_ext (fun f : _88128 -> _88132 => @lem3393196 _88128 _88132 f)). Qed.
Lemma lem3393198 {_88128 _88132 : Type'} : (@all (_88128 -> _88132)) = (@all (_88128 -> _88132)).
Proof. exact (eq_refl (@all (_88128 -> _88132))). Qed.
Lemma lem3393199 {_88128 _88132 : Type'} : (term66 _88128 _88132) = (term66 _88128 _88132).
Proof. exact (MK_COMB (@lem3393198 _88128 _88132) (@lem3393197 _88128 _88132)). Qed.
Lemma lem3393236 {_88128 _88132 : Type'} : (term68 _88128 _88132) = (term66 _88128 _88132).
Proof. exact (TRANS (@lem3393171 _88128 _88132) (@lem3393199 _88128 _88132)). Qed.
Lemma lem3393237 {_88128 _88132 : Type'} : (term66 _88128 _88132) = (term68 _88128 _88132).
Proof. exact (SYM (@lem3393236 _88128 _88132)). Qed.
Lemma lem3393239 (p : Prop) : p = (term67 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3393240 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) : ((term54 _88128 _88132 s x f) = (term6 _88128 _88132 x f s)) = (term77 _88128 _88132 x f s).
Proof. exact (@lem3393239 ((term54 _88128 _88132 s x f) = (term6 _88128 _88132 x f s))). Qed.
Lemma lem3393241 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) : (term77 _88128 _88132 x f s) = ((term54 _88128 _88132 s x f) = (term6 _88128 _88132 x f s)).
Proof. exact (SYM (@lem3393240 _88128 _88132 x f s)). Qed.
Lemma lem3393242 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) (h1 : term78 _88128 _88132 x f s) : term78 _88128 _88132 x f s.
Proof. exact (h1). Qed.
Lemma lem3393251 {_88128 _88132 : Type'} (s : _88128 -> Prop) (x : _88132) (f : _88128 -> _88132) (x' : _88128) : (term79 _88128 _88132 s x f x') = (term80 _88128 _88132 s x f x').
Proof. exact (@lem17045 (@IN _88128 x' s) (x = (f x'))). Qed.
Lemma lem3393254 {_88128 _88132 : Type'} (s : _88128 -> Prop) (x : _88132) (f : _88128 -> _88132) (x' : _88128) : (term51 _88128 _88132 s x f x') = (term51 _88128 _88132 s x f x').
Proof. exact (eq_refl (term51 _88128 _88132 s x f x')). Qed.
Lemma lem3393255 {_88128 : Type'} (P : _88128 -> Prop) : (term81 _88128 P) = (term82 _88128 P).
Proof. exact (@lem18394 _88128 P). Qed.
Lemma lem3393256 {_88128 _88132 : Type'} (s : _88128 -> Prop) (x : _88132) (f : _88128 -> _88132) : (term83 _88128 _88132 s x f) = (term84 _88128 _88132 s x f).
Proof. exact (@lem3393255 _88128 (term53 _88128 _88132 s x f)). Qed.
Lemma lem3393257 {_88128 _88132 : Type'} (s : _88128 -> Prop) (x : _88132) (f : _88128 -> _88132) (x' : _88128) : (term85 _88128 _88132 s x f x') = (term51 _88128 _88132 s x f x').
Proof. exact (eq_refl (term85 _88128 _88132 s x f x')). Qed.
Lemma lem3393258 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3393259 {_88128 _88132 : Type'} (s : _88128 -> Prop) (x : _88132) (f : _88128 -> _88132) (x' : _88128) : (term86 _88128 _88132 s x f x') = (term79 _88128 _88132 s x f x').
Proof. exact (MK_COMB (@lem3393258) (@lem3393257 _88128 _88132 s x f x')). Qed.
Lemma lem3393260 {_88128 _88132 : Type'} (s : _88128 -> Prop) (x : _88132) (f : _88128 -> _88132) (x' : _88128) : (term86 _88128 _88132 s x f x') = (term80 _88128 _88132 s x f x').
Proof. exact (TRANS (@lem3393259 _88128 _88132 s x f x') (@lem3393251 _88128 _88132 s x f x')). Qed.
Lemma lem3393261 {_88128 _88132 : Type'} (s : _88128 -> Prop) (x : _88132) (f : _88128 -> _88132) : (term87 _88128 _88132 s x f) = (term88 _88128 _88132 s x f).
Proof. exact (fun_ext (fun x' : _88128 => @lem3393260 _88128 _88132 s x f x')). Qed.
Lemma lem3393262 {_88128 : Type'} : (@all _88128) = (@all _88128).
Proof. exact (eq_refl (@all _88128)). Qed.
Lemma lem3393263 {_88128 _88132 : Type'} (s : _88128 -> Prop) (x : _88132) (f : _88128 -> _88132) : (term84 _88128 _88132 s x f) = (term89 _88128 _88132 s x f).
Proof. exact (MK_COMB (@lem3393262 _88128) (@lem3393261 _88128 _88132 s x f)). Qed.
Lemma lem3393264 {_88128 _88132 : Type'} (s : _88128 -> Prop) (x : _88132) (f : _88128 -> _88132) : (term83 _88128 _88132 s x f) = (term89 _88128 _88132 s x f).
Proof. exact (TRANS (@lem3393256 _88128 _88132 s x f) (@lem3393263 _88128 _88132 s x f)). Qed.
Lemma lem3393265 {_88128 _88132 : Type'} (s : _88128 -> Prop) (x : _88132) (f : _88128 -> _88132) : (term53 _88128 _88132 s x f) = (term53 _88128 _88132 s x f).
Proof. exact (fun_ext (fun x' : _88128 => @lem3393254 _88128 _88132 s x f x')). Qed.
Lemma lem3393266 {_88128 : Type'} : (@ex _88128) = (@ex _88128).
Proof. exact (eq_refl (@ex _88128)). Qed.
Lemma lem3393267 {_88128 _88132 : Type'} (s : _88128 -> Prop) (x : _88132) (f : _88128 -> _88132) : (term54 _88128 _88132 s x f) = (term54 _88128 _88132 s x f).
Proof. exact (MK_COMB (@lem3393266 _88128) (@lem3393265 _88128 _88132 s x f)). Qed.
Lemma lem3393276 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (x' : _88128) (s : _88128 -> Prop) : (term90 _88128 _88132 x f x' s) = (term91 _88128 _88132 x f x' s).
Proof. exact (@lem17045 (x = (f x')) (@IN _88128 x' s)). Qed.
Lemma lem3393279 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (x' : _88128) (s : _88128 -> Prop) : (term75 _88128 _88132 x f x' s) = (term75 _88128 _88132 x f x' s).
Proof. exact (eq_refl (term75 _88128 _88132 x f x' s)). Qed.
Lemma lem3393280 {_88128 : Type'} (P : _88128 -> Prop) : (term81 _88128 P) = (term82 _88128 P).
Proof. exact (@lem18394 _88128 P). Qed.
Lemma lem3393281 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) : (term92 _88128 _88132 x f s) = (term93 _88128 _88132 x f s).
Proof. exact (@lem3393280 _88128 (term76 _88128 _88132 x f s)). Qed.
Lemma lem3393282 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (x' : _88128) (s : _88128 -> Prop) : (term94 _88128 _88132 x f s x') = (term75 _88128 _88132 x f x' s).
Proof. exact (eq_refl (term94 _88128 _88132 x f s x')). Qed.
Lemma lem3393283 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3393284 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (x' : _88128) (s : _88128 -> Prop) : (term95 _88128 _88132 x f s x') = (term90 _88128 _88132 x f x' s).
Proof. exact (MK_COMB (@lem3393283) (@lem3393282 _88128 _88132 x f x' s)). Qed.
Lemma lem3393285 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (x' : _88128) (s : _88128 -> Prop) : (term95 _88128 _88132 x f s x') = (term91 _88128 _88132 x f x' s).
Proof. exact (TRANS (@lem3393284 _88128 _88132 x f x' s) (@lem3393276 _88128 _88132 x f x' s)). Qed.
Lemma lem3393286 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) : (term96 _88128 _88132 x f s) = (term97 _88128 _88132 x f s).
Proof. exact (fun_ext (fun x' : _88128 => @lem3393285 _88128 _88132 x f x' s)). Qed.
Lemma lem3393287 {_88128 : Type'} : (@all _88128) = (@all _88128).
Proof. exact (eq_refl (@all _88128)). Qed.
Lemma lem3393288 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) : (term93 _88128 _88132 x f s) = (term98 _88128 _88132 x f s).
Proof. exact (MK_COMB (@lem3393287 _88128) (@lem3393286 _88128 _88132 x f s)). Qed.
Lemma lem3393289 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) : (term92 _88128 _88132 x f s) = (term98 _88128 _88132 x f s).
Proof. exact (TRANS (@lem3393281 _88128 _88132 x f s) (@lem3393288 _88128 _88132 x f s)). Qed.
Lemma lem3393290 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) : (term76 _88128 _88132 x f s) = (term76 _88128 _88132 x f s).
Proof. exact (fun_ext (fun x' : _88128 => @lem3393279 _88128 _88132 x f x' s)). Qed.
Lemma lem3393291 {_88128 : Type'} : (@ex _88128) = (@ex _88128).
Proof. exact (eq_refl (@ex _88128)). Qed.
Lemma lem3393292 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) : (term6 _88128 _88132 x f s) = (term6 _88128 _88132 x f s).
Proof. exact (MK_COMB (@lem3393291 _88128) (@lem3393290 _88128 _88132 x f s)). Qed.
Lemma lem3393293 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3393294 {_88128 _88132 : Type'} (s : _88128 -> Prop) (x : _88132) (f : _88128 -> _88132) : (term99 _88128 _88132 s x f) = (term100 _88128 _88132 s x f).
Proof. exact (MK_COMB (@lem3393293) (@lem3393264 _88128 _88132 s x f)). Qed.
Lemma lem3393295 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) : (term101 _88128 _88132 x f s) = (term102 _88128 _88132 x f s).
Proof. exact (MK_COMB (@lem3393294 _88128 _88132 s x f) (@lem3393292 _88128 _88132 x f s)). Qed.
Lemma lem3393296 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3393297 {_88128 _88132 : Type'} (s : _88128 -> Prop) (x : _88132) (f : _88128 -> _88132) : (term103 _88128 _88132 s x f) = (term103 _88128 _88132 s x f).
Proof. exact (MK_COMB (@lem3393296) (@lem3393267 _88128 _88132 s x f)). Qed.
Lemma lem3393298 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) : (term104 _88128 _88132 x f s) = (term105 _88128 _88132 x f s).
Proof. exact (MK_COMB (@lem3393297 _88128 _88132 s x f) (@lem3393289 _88128 _88132 x f s)). Qed.
Lemma lem3393299 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3393300 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) : (term106 _88128 _88132 x f s) = (term107 _88128 _88132 x f s).
Proof. exact (MK_COMB (@lem3393299) (@lem3393298 _88128 _88132 x f s)). Qed.
Lemma lem3393301 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) : (term108 _88128 _88132 x f s) = (term109 _88128 _88132 x f s).
Proof. exact (MK_COMB (@lem3393300 _88128 _88132 x f s) (@lem3393295 _88128 _88132 x f s)). Qed.
Lemma lem3393302 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) : (term78 _88128 _88132 x f s) = (term108 _88128 _88132 x f s).
Proof. exact (@lem17646 (term54 _88128 _88132 s x f) (term6 _88128 _88132 x f s)). Qed.
Lemma lem3393303 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) : (term78 _88128 _88132 x f s) = (term109 _88128 _88132 x f s).
Proof. exact (TRANS (@lem3393302 _88128 _88132 x f s) (@lem3393301 _88128 _88132 x f s)). Qed.
Lemma lem3393498 {A : Type'} (P : A -> Prop) (Q : Prop) : (term110 A P Q) = (term111 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3393499 {_88128 : Type'} (P : _88128 -> Prop) (Q : Prop) : (term110 _88128 P Q) = (term111 _88128 P Q).
Proof. exact (@lem3393498 _88128 P Q). Qed.
Lemma lem3393500 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) : (term112 _88128 _88132 x f s) = (term113 _88128 _88132 x f s).
Proof. exact (@lem3393499 _88128 (term53 _88128 _88132 s x f) (term98 _88128 _88132 x f s)). Qed.
Lemma lem3393501 {_88128 _88132 : Type'} (s : _88128 -> Prop) (x : _88132) (f : _88128 -> _88132) (x' : _88128) : (term85 _88128 _88132 s x f x') = (term51 _88128 _88132 s x f x').
Proof. exact (eq_refl (term85 _88128 _88132 s x f x')). Qed.
Lemma lem3393502 {_88128 _88132 : Type'} (s : _88128 -> Prop) (x : _88132) (f : _88128 -> _88132) : (term114 _88128 _88132 s x f) = (term53 _88128 _88132 s x f).
Proof. exact (fun_ext (fun x' : _88128 => @lem3393501 _88128 _88132 s x f x')). Qed.
Lemma lem3393503 {_88128 : Type'} : (@ex _88128) = (@ex _88128).
Proof. exact (eq_refl (@ex _88128)). Qed.
Lemma lem3393504 {_88128 _88132 : Type'} (s : _88128 -> Prop) (x : _88132) (f : _88128 -> _88132) : (term115 _88128 _88132 s x f) = (term54 _88128 _88132 s x f).
Proof. exact (MK_COMB (@lem3393503 _88128) (@lem3393502 _88128 _88132 s x f)). Qed.
Lemma lem3393505 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3393506 {_88128 _88132 : Type'} (s : _88128 -> Prop) (x : _88132) (f : _88128 -> _88132) : (term116 _88128 _88132 s x f) = (term103 _88128 _88132 s x f).
Proof. exact (MK_COMB (@lem3393505) (@lem3393504 _88128 _88132 s x f)). Qed.
Lemma lem3393507 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) : (term98 _88128 _88132 x f s) = (term98 _88128 _88132 x f s).
Proof. exact (eq_refl (term98 _88128 _88132 x f s)). Qed.
Lemma lem3393508 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) : (term112 _88128 _88132 x f s) = (term105 _88128 _88132 x f s).
Proof. exact (MK_COMB (@lem3393506 _88128 _88132 s x f) (@lem3393507 _88128 _88132 x f s)). Qed.
Lemma lem3393509 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3393510 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) : (term117 _88128 _88132 x f s) = (term118 _88128 _88132 x f s).
Proof. exact (MK_COMB (@lem3393509) (@lem3393508 _88128 _88132 x f s)). Qed.
Lemma lem3393511 {_88128 _88132 : Type'} (s : _88128 -> Prop) (x : _88132) (f : _88128 -> _88132) (x' : _88128) : (term85 _88128 _88132 s x f x') = (term51 _88128 _88132 s x f x').
Proof. exact (eq_refl (term85 _88128 _88132 s x f x')). Qed.
Lemma lem3393512 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3393513 {_88128 _88132 : Type'} (s : _88128 -> Prop) (x : _88132) (f : _88128 -> _88132) (x' : _88128) : (term119 _88128 _88132 s x f x') = (term120 _88128 _88132 s x f x').
Proof. exact (MK_COMB (@lem3393512) (@lem3393511 _88128 _88132 s x f x')). Qed.
Lemma lem3393514 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) : (term98 _88128 _88132 x f s) = (term98 _88128 _88132 x f s).
Proof. exact (eq_refl (term98 _88128 _88132 x f s)). Qed.
Lemma lem3393515 {_88128 _88132 : Type'} (x : _88128) (x' : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) : (term121 _88128 _88132 x x' f s) = (term122 _88128 _88132 x x' f s).
Proof. exact (MK_COMB (@lem3393513 _88128 _88132 s x' f x) (@lem3393514 _88128 _88132 x' f s)). Qed.
Lemma lem3393516 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) : (term123 _88128 _88132 x f s) = (term124 _88128 _88132 x f s).
Proof. exact (fun_ext (fun x' : _88128 => @lem3393515 _88128 _88132 x' x f s)). Qed.
Lemma lem3393517 {_88128 : Type'} : (@ex _88128) = (@ex _88128).
Proof. exact (eq_refl (@ex _88128)). Qed.
Lemma lem3393518 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) : (term113 _88128 _88132 x f s) = (term125 _88128 _88132 x f s).
Proof. exact (MK_COMB (@lem3393517 _88128) (@lem3393516 _88128 _88132 x f s)). Qed.
Lemma lem3393519 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) : ((term112 _88128 _88132 x f s) = (term113 _88128 _88132 x f s)) = ((term105 _88128 _88132 x f s) = (term125 _88128 _88132 x f s)).
Proof. exact (MK_COMB (@lem3393510 _88128 _88132 x f s) (@lem3393518 _88128 _88132 x f s)). Qed.
Lemma lem3393520 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) : (term105 _88128 _88132 x f s) = (term125 _88128 _88132 x f s).
Proof. exact (EQ_MP (@lem3393519 _88128 _88132 x f s) (@lem3393500 _88128 _88132 x f s)). Qed.
Lemma lem3393521 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3393522 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) : (term107 _88128 _88132 x f s) = (term126 _88128 _88132 x f s).
Proof. exact (MK_COMB (@lem3393521) (@lem3393520 _88128 _88132 x f s)). Qed.
Lemma lem3393524 {A : Type'} (P : Prop) (Q : A -> Prop) : (term127 A P Q) = (term128 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3393525 {_88128 : Type'} (P : Prop) (Q : _88128 -> Prop) : (term127 _88128 P Q) = (term128 _88128 P Q).
Proof. exact (@lem3393524 _88128 P Q). Qed.
Lemma lem3393526 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) : (term129 _88128 _88132 x f s) = (term130 _88128 _88132 x f s).
Proof. exact (@lem3393525 _88128 (term89 _88128 _88132 s x f) (term76 _88128 _88132 x f s)). Qed.
Lemma lem3393527 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (x' : _88128) (s : _88128 -> Prop) : (term94 _88128 _88132 x f s x') = (term75 _88128 _88132 x f x' s).
Proof. exact (eq_refl (term94 _88128 _88132 x f s x')). Qed.
Lemma lem3393528 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) : (term131 _88128 _88132 x f s) = (term76 _88128 _88132 x f s).
Proof. exact (fun_ext (fun x' : _88128 => @lem3393527 _88128 _88132 x f x' s)). Qed.
Lemma lem3393529 {_88128 : Type'} : (@ex _88128) = (@ex _88128).
Proof. exact (eq_refl (@ex _88128)). Qed.
Lemma lem3393530 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) : (term132 _88128 _88132 x f s) = (term6 _88128 _88132 x f s).
Proof. exact (MK_COMB (@lem3393529 _88128) (@lem3393528 _88128 _88132 x f s)). Qed.
Lemma lem3393531 {_88128 _88132 : Type'} (s : _88128 -> Prop) (x : _88132) (f : _88128 -> _88132) : (term100 _88128 _88132 s x f) = (term100 _88128 _88132 s x f).
Proof. exact (eq_refl (term100 _88128 _88132 s x f)). Qed.
Lemma lem3393532 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) : (term129 _88128 _88132 x f s) = (term102 _88128 _88132 x f s).
Proof. exact (MK_COMB (@lem3393531 _88128 _88132 s x f) (@lem3393530 _88128 _88132 x f s)). Qed.
Lemma lem3393533 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3393534 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) : (term133 _88128 _88132 x f s) = (term134 _88128 _88132 x f s).
Proof. exact (MK_COMB (@lem3393533) (@lem3393532 _88128 _88132 x f s)). Qed.
Lemma lem3393535 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (x' : _88128) (s : _88128 -> Prop) : (term94 _88128 _88132 x f s x') = (term75 _88128 _88132 x f x' s).
Proof. exact (eq_refl (term94 _88128 _88132 x f s x')). Qed.
Lemma lem3393536 {_88128 _88132 : Type'} (s : _88128 -> Prop) (x : _88132) (f : _88128 -> _88132) : (term100 _88128 _88132 s x f) = (term100 _88128 _88132 s x f).
Proof. exact (eq_refl (term100 _88128 _88132 s x f)). Qed.
Lemma lem3393537 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (x' : _88128) (s : _88128 -> Prop) : (term135 _88128 _88132 x f s x') = (term136 _88128 _88132 x f x' s).
Proof. exact (MK_COMB (@lem3393536 _88128 _88132 s x f) (@lem3393535 _88128 _88132 x f x' s)). Qed.
Lemma lem3393538 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) : (term137 _88128 _88132 x f s) = (term138 _88128 _88132 x f s).
Proof. exact (fun_ext (fun x' : _88128 => @lem3393537 _88128 _88132 x f x' s)). Qed.
Lemma lem3393539 {_88128 : Type'} : (@ex _88128) = (@ex _88128).
Proof. exact (eq_refl (@ex _88128)). Qed.
Lemma lem3393540 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) : (term130 _88128 _88132 x f s) = (term139 _88128 _88132 x f s).
Proof. exact (MK_COMB (@lem3393539 _88128) (@lem3393538 _88128 _88132 x f s)). Qed.
Lemma lem3393541 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) : ((term129 _88128 _88132 x f s) = (term130 _88128 _88132 x f s)) = ((term102 _88128 _88132 x f s) = (term139 _88128 _88132 x f s)).
Proof. exact (MK_COMB (@lem3393534 _88128 _88132 x f s) (@lem3393540 _88128 _88132 x f s)). Qed.
Lemma lem3393542 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) : (term102 _88128 _88132 x f s) = (term139 _88128 _88132 x f s).
Proof. exact (EQ_MP (@lem3393541 _88128 _88132 x f s) (@lem3393526 _88128 _88132 x f s)). Qed.
Lemma lem3393543 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) : (term109 _88128 _88132 x f s) = (term140 _88128 _88132 x f s).
Proof. exact (MK_COMB (@lem3393522 _88128 _88132 x f s) (@lem3393542 _88128 _88132 x f s)). Qed.
Lemma lem3393545 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term141 A P Q) = (term142 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3393546 {_88128 : Type'} (P : _88128 -> Prop) (Q : _88128 -> Prop) : (term141 _88128 P Q) = (term142 _88128 P Q).
Proof. exact (@lem3393545 _88128 P Q). Qed.
Lemma lem3393547 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) : (term143 _88128 _88132 x f s) = (term144 _88128 _88132 x f s).
Proof. exact (@lem3393546 _88128 (term124 _88128 _88132 x f s) (term138 _88128 _88132 x f s)). Qed.
Lemma lem3393548 {_88128 _88132 : Type'} (x : _88128) (x' : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) : (term145 _88128 _88132 x' f s x) = (term122 _88128 _88132 x x' f s).
Proof. exact (eq_refl (term145 _88128 _88132 x' f s x)). Qed.
Lemma lem3393549 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) : (term146 _88128 _88132 x f s) = (term124 _88128 _88132 x f s).
Proof. exact (fun_ext (fun x' : _88128 => @lem3393548 _88128 _88132 x' x f s)). Qed.
Lemma lem3393550 {_88128 : Type'} : (@ex _88128) = (@ex _88128).
Proof. exact (eq_refl (@ex _88128)). Qed.
Lemma lem3393551 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) : (term147 _88128 _88132 x f s) = (term125 _88128 _88132 x f s).
Proof. exact (MK_COMB (@lem3393550 _88128) (@lem3393549 _88128 _88132 x f s)). Qed.
Lemma lem3393552 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3393553 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) : (term148 _88128 _88132 x f s) = (term126 _88128 _88132 x f s).
Proof. exact (MK_COMB (@lem3393552) (@lem3393551 _88128 _88132 x f s)). Qed.
Lemma lem3393554 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (x' : _88128) (s : _88128 -> Prop) : (term149 _88128 _88132 x f s x') = (term136 _88128 _88132 x f x' s).
Proof. exact (eq_refl (term149 _88128 _88132 x f s x')). Qed.
Lemma lem3393555 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) : (term150 _88128 _88132 x f s) = (term138 _88128 _88132 x f s).
Proof. exact (fun_ext (fun x' : _88128 => @lem3393554 _88128 _88132 x f x' s)). Qed.
Lemma lem3393556 {_88128 : Type'} : (@ex _88128) = (@ex _88128).
Proof. exact (eq_refl (@ex _88128)). Qed.
Lemma lem3393557 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) : (term151 _88128 _88132 x f s) = (term139 _88128 _88132 x f s).
Proof. exact (MK_COMB (@lem3393556 _88128) (@lem3393555 _88128 _88132 x f s)). Qed.
Lemma lem3393558 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) : (term143 _88128 _88132 x f s) = (term140 _88128 _88132 x f s).
Proof. exact (MK_COMB (@lem3393553 _88128 _88132 x f s) (@lem3393557 _88128 _88132 x f s)). Qed.
Lemma lem3393559 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3393560 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) : (term152 _88128 _88132 x f s) = (term153 _88128 _88132 x f s).
Proof. exact (MK_COMB (@lem3393559) (@lem3393558 _88128 _88132 x f s)). Qed.
Lemma lem3393561 {_88128 _88132 : Type'} (x : _88128) (x' : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) : (term145 _88128 _88132 x' f s x) = (term122 _88128 _88132 x x' f s).
Proof. exact (eq_refl (term145 _88128 _88132 x' f s x)). Qed.
Lemma lem3393562 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3393563 {_88128 _88132 : Type'} (x : _88128) (x' : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) : (term154 _88128 _88132 x' f s x) = (term155 _88128 _88132 x x' f s).
Proof. exact (MK_COMB (@lem3393562) (@lem3393561 _88128 _88132 x x' f s)). Qed.
Lemma lem3393564 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (x' : _88128) (s : _88128 -> Prop) : (term149 _88128 _88132 x f s x') = (term136 _88128 _88132 x f x' s).
Proof. exact (eq_refl (term149 _88128 _88132 x f s x')). Qed.
Lemma lem3393565 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (x' : _88128) (s : _88128 -> Prop) : (term156 _88128 _88132 x f s x') = (term157 _88128 _88132 x f x' s).
Proof. exact (MK_COMB (@lem3393563 _88128 _88132 x' x f s) (@lem3393564 _88128 _88132 x f x' s)). Qed.
Lemma lem3393566 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) : (term158 _88128 _88132 x f s) = (term159 _88128 _88132 x f s).
Proof. exact (fun_ext (fun x' : _88128 => @lem3393565 _88128 _88132 x f x' s)). Qed.
Lemma lem3393567 {_88128 : Type'} : (@ex _88128) = (@ex _88128).
Proof. exact (eq_refl (@ex _88128)). Qed.
Lemma lem3393568 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) : (term144 _88128 _88132 x f s) = (term160 _88128 _88132 x f s).
Proof. exact (MK_COMB (@lem3393567 _88128) (@lem3393566 _88128 _88132 x f s)). Qed.
Lemma lem3393569 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) : ((term143 _88128 _88132 x f s) = (term144 _88128 _88132 x f s)) = ((term140 _88128 _88132 x f s) = (term160 _88128 _88132 x f s)).
Proof. exact (MK_COMB (@lem3393560 _88128 _88132 x f s) (@lem3393568 _88128 _88132 x f s)). Qed.
Lemma lem3393570 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) : (term140 _88128 _88132 x f s) = (term160 _88128 _88132 x f s).
Proof. exact (EQ_MP (@lem3393569 _88128 _88132 x f s) (@lem3393547 _88128 _88132 x f s)). Qed.
Lemma lem3393572 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) : (term109 _88128 _88132 x f s) = (term160 _88128 _88132 x f s).
Proof. exact (TRANS (@lem3393543 _88128 _88132 x f s) (@lem3393570 _88128 _88132 x f s)). Qed.
Lemma lem3393573 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) : (term78 _88128 _88132 x f s) = (term160 _88128 _88132 x f s).
Proof. exact (TRANS (@lem3393303 _88128 _88132 x f s) (@lem3393572 _88128 _88132 x f s)). Qed.
Lemma lem3393574 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) (h1 : term78 _88128 _88132 x f s) : term160 _88128 _88132 x f s.
Proof. exact (EQ_MP (@lem3393573 _88128 _88132 x f s) (@lem3393242 _88128 _88132 x f s h1)). Qed.
Lemma lem3393575 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (x' : _88128) (s : _88128 -> Prop) (h1 : term157 _88128 _88132 x f x' s) : term157 _88128 _88132 x f x' s.
Proof. exact (h1). Qed.
Lemma lem3393590 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (x' : _88128) (s : _88128 -> Prop) : (term75 _88128 _88132 x f x' s) = (term75 _88128 _88132 x f x' s).
Proof. exact (eq_refl (term75 _88128 _88132 x f x' s)). Qed.
Lemma lem3393609 {_88128 _88132 : Type'} (s : _88128 -> Prop) (x : _88132) (f : _88128 -> _88132) (x' : _88128) : (term80 _88128 _88132 s x f x') = (term80 _88128 _88132 s x f x').
Proof. exact (eq_refl (term80 _88128 _88132 s x f x')). Qed.
Lemma lem3393610 {_88128 _88132 : Type'} (s : _88128 -> Prop) (x : _88132) (f : _88128 -> _88132) : (term88 _88128 _88132 s x f) = (term88 _88128 _88132 s x f).
Proof. exact (fun_ext (fun x' : _88128 => @lem3393609 _88128 _88132 s x f x')). Qed.
Lemma lem3393611 {_88128 : Type'} : (@all _88128) = (@all _88128).
Proof. exact (eq_refl (@all _88128)). Qed.
Lemma lem3393612 {_88128 _88132 : Type'} (s : _88128 -> Prop) (x : _88132) (f : _88128 -> _88132) : (term89 _88128 _88132 s x f) = (term89 _88128 _88132 s x f).
Proof. exact (MK_COMB (@lem3393611 _88128) (@lem3393610 _88128 _88132 s x f)). Qed.
Lemma lem3393613 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3393614 {_88128 _88132 : Type'} (s : _88128 -> Prop) (x : _88132) (f : _88128 -> _88132) : (term100 _88128 _88132 s x f) = (term100 _88128 _88132 s x f).
Proof. exact (MK_COMB (@lem3393613) (@lem3393612 _88128 _88132 s x f)). Qed.
Lemma lem3393615 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (x' : _88128) (s : _88128 -> Prop) : (term136 _88128 _88132 x f x' s) = (term136 _88128 _88132 x f x' s).
Proof. exact (MK_COMB (@lem3393614 _88128 _88132 s x f) (@lem3393590 _88128 _88132 x f x' s)). Qed.
Lemma lem3393634 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (x' : _88128) (s : _88128 -> Prop) : (term91 _88128 _88132 x f x' s) = (term91 _88128 _88132 x f x' s).
Proof. exact (eq_refl (term91 _88128 _88132 x f x' s)). Qed.
Lemma lem3393635 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) : (term97 _88128 _88132 x f s) = (term97 _88128 _88132 x f s).
Proof. exact (fun_ext (fun x' : _88128 => @lem3393634 _88128 _88132 x f x' s)). Qed.
Lemma lem3393636 {_88128 : Type'} : (@all _88128) = (@all _88128).
Proof. exact (eq_refl (@all _88128)). Qed.
Lemma lem3393637 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) : (term98 _88128 _88132 x f s) = (term98 _88128 _88132 x f s).
Proof. exact (MK_COMB (@lem3393636 _88128) (@lem3393635 _88128 _88132 x f s)). Qed.
Lemma lem3393654 {_88128 _88132 : Type'} (s : _88128 -> Prop) (x : _88132) (f : _88128 -> _88132) (x' : _88128) : (term120 _88128 _88132 s x f x') = (term120 _88128 _88132 s x f x').
Proof. exact (eq_refl (term120 _88128 _88132 s x f x')). Qed.
Lemma lem3393655 {_88128 _88132 : Type'} (x' : _88128) (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) : (term122 _88128 _88132 x' x f s) = (term122 _88128 _88132 x' x f s).
Proof. exact (MK_COMB (@lem3393654 _88128 _88132 s x f x') (@lem3393637 _88128 _88132 x f s)). Qed.
Lemma lem3393656 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3393657 {_88128 _88132 : Type'} (x' : _88128) (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) : (term155 _88128 _88132 x' x f s) = (term155 _88128 _88132 x' x f s).
Proof. exact (MK_COMB (@lem3393656) (@lem3393655 _88128 _88132 x' x f s)). Qed.
Lemma lem3393658 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (x' : _88128) (s : _88128 -> Prop) : (term157 _88128 _88132 x f x' s) = (term157 _88128 _88132 x f x' s).
Proof. exact (MK_COMB (@lem3393657 _88128 _88132 x' x f s) (@lem3393615 _88128 _88132 x f x' s)). Qed.
Lemma lem3393659 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (x' : _88128) (s : _88128 -> Prop) (h1 : term157 _88128 _88132 x f x' s) : term157 _88128 _88132 x f x' s.
Proof. exact (EQ_MP (@lem3393658 _88128 _88132 x f x' s) (@lem3393575 _88128 _88132 x f x' s h1)). Qed.
Lemma lem3393660 {_88128 _88132 : Type'} (x' : _88128) (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) (h1 : term122 _88128 _88132 x' x f s) : term122 _88128 _88132 x' x f s.
Proof. exact (h1). Qed.
Lemma lem3393661 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (x' : _88128) (s : _88128 -> Prop) (h1 : term136 _88128 _88132 x f x' s) : term136 _88128 _88132 x f x' s.
Proof. exact (h1). Qed.
Lemma lem3393662 {_88128 _88132 : Type'} (x' : _88128) (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) (h1 : term122 _88128 _88132 x' x f s) : term98 _88128 _88132 x f s.
Proof. exact (proj2 (@lem3393660 _88128 _88132 x' x f s h1)). Qed.
Lemma lem3393663 {_88128 _88132 : Type'} (x' : _88128) (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) (h1 : term122 _88128 _88132 x' x f s) : term51 _88128 _88132 s x f x'.
Proof. exact (proj1 (@lem3393660 _88128 _88132 x' x f s h1)). Qed.
Lemma lem3393666 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (x' : _88128) (s : _88128 -> Prop) (h1 : term136 _88128 _88132 x f x' s) : term75 _88128 _88132 x f x' s.
Proof. exact (proj2 (@lem3393661 _88128 _88132 x f x' s h1)). Qed.
Lemma lem3393667 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (x' : _88128) (s : _88128 -> Prop) (h1 : term136 _88128 _88132 x f x' s) : term89 _88128 _88132 s x f.
Proof. exact (proj1 (@lem3393661 _88128 _88132 x f x' s h1)). Qed.
Lemma lem3393677 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (x' : _88128) (s : _88128 -> Prop) : (term91 _88128 _88132 x f x' s) = (term91 _88128 _88132 x f x' s).
Proof. exact (eq_refl (term91 _88128 _88132 x f x' s)). Qed.
Lemma lem3393678 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) : (term97 _88128 _88132 x f s) = (term97 _88128 _88132 x f s).
Proof. exact (fun_ext (fun x' : _88128 => @lem3393677 _88128 _88132 x f x' s)). Qed.
Lemma lem3393679 {_88128 : Type'} : (@all _88128) = (@all _88128).
Proof. exact (eq_refl (@all _88128)). Qed.
Lemma lem3393681 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) : (term98 _88128 _88132 x f s) = (term98 _88128 _88132 x f s).
Proof. exact (MK_COMB (@lem3393679 _88128) (@lem3393678 _88128 _88132 x f s)). Qed.
Lemma lem3393682 {_88128 _88132 : Type'} (x' : _88128) (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) (h1 : term122 _88128 _88132 x' x f s) : term98 _88128 _88132 x f s.
Proof. exact (EQ_MP (@lem3393681 _88128 _88132 x f s) (@lem3393662 _88128 _88132 x' x f s h1)). Qed.
Lemma lem3393698 {_88128 _88132 : Type'} (s : _88128 -> Prop) (x : _88132) (f : _88128 -> _88132) (x' : _88128) : (term80 _88128 _88132 s x f x') = (term80 _88128 _88132 s x f x').
Proof. exact (eq_refl (term80 _88128 _88132 s x f x')). Qed.
Lemma lem3393699 {_88128 _88132 : Type'} (s : _88128 -> Prop) (x : _88132) (f : _88128 -> _88132) : (term88 _88128 _88132 s x f) = (term88 _88128 _88132 s x f).
Proof. exact (fun_ext (fun x' : _88128 => @lem3393698 _88128 _88132 s x f x')). Qed.
Lemma lem3393700 {_88128 : Type'} : (@all _88128) = (@all _88128).
Proof. exact (eq_refl (@all _88128)). Qed.
Lemma lem3393702 {_88128 _88132 : Type'} (s : _88128 -> Prop) (x : _88132) (f : _88128 -> _88132) : (term89 _88128 _88132 s x f) = (term89 _88128 _88132 s x f).
Proof. exact (MK_COMB (@lem3393700 _88128) (@lem3393699 _88128 _88132 s x f)). Qed.
Lemma lem3393703 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (x' : _88128) (s : _88128 -> Prop) (h1 : term136 _88128 _88132 x f x' s) : term89 _88128 _88132 s x f.
Proof. exact (EQ_MP (@lem3393702 _88128 _88132 s x f) (@lem3393667 _88128 _88132 x f x' s h1)). Qed.
Lemma lem3393712 {_88128 _88132 : Type'} (_35706 : _88128) (x' : _88128) (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) (h1 : term122 _88128 _88132 x' x f s) : term161 _88128 _88132 x f s _35706.
Proof. exact (@lem3393682 _88128 _88132 x' x f s h1 _35706). Qed.
Lemma lem3393713 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (_35706 : _88128) (s : _88128 -> Prop) : (term161 _88128 _88132 x f s _35706) = (term91 _88128 _88132 x f _35706 s).
Proof. exact (eq_refl (term161 _88128 _88132 x f s _35706)). Qed.
Lemma lem3393715 {_88128 _88132 : Type'} (_35707 : _88128) (x : _88132) (f : _88128 -> _88132) (x' : _88128) (s : _88128 -> Prop) (h1 : term136 _88128 _88132 x f x' s) : term162 _88128 _88132 s x f _35707.
Proof. exact (@lem3393703 _88128 _88132 x f x' s h1 _35707). Qed.
Lemma lem3393716 {_88128 _88132 : Type'} (s : _88128 -> Prop) (x : _88132) (f : _88128 -> _88132) (_35707 : _88128) : (term162 _88128 _88132 s x f _35707) = (term80 _88128 _88132 s x f _35707).
Proof. exact (eq_refl (term162 _88128 _88132 s x f _35707)). Qed.
Lemma lem3393723 {_88128 _88132 : Type'} (_35706 : _88128) (x' : _88128) (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) (h1 : term122 _88128 _88132 x' x f s) : term91 _88128 _88132 x f _35706 s.
Proof. exact (EQ_MP (@lem3393713 _88128 _88132 x f _35706 s) (@lem3393712 _88128 _88132 _35706 x' x f s h1)). Qed.
Lemma lem3393727 {_88128 _88132 : Type'} (x' : _88128) (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) (h1 : term122 _88128 _88132 x' x f s) : x = (f x').
Proof. exact (proj2 (@lem3393663 _88128 _88132 x' x f s h1)). Qed.
Lemma lem3393733 {_88128 _88132 : Type'} (_35707 : _88128) (x : _88132) (f : _88128 -> _88132) (x' : _88128) (s : _88128 -> Prop) (h1 : term136 _88128 _88132 x f x' s) : term80 _88128 _88132 s x f _35707.
Proof. exact (EQ_MP (@lem3393716 _88128 _88132 s x f _35707) (@lem3393715 _88128 _88132 _35707 x f x' s h1)). Qed.
Lemma lem3393735 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (x' : _88128) (s : _88128 -> Prop) (h1 : term136 _88128 _88132 x f x' s) : x = (f x').
Proof. exact (proj1 (@lem3393666 _88128 _88132 x f x' s h1)). Qed.
Lemma lem3393752 {_88128 _88132 : Type'} (f : _88128 -> _88132) (_35706 : _88128) (s : _88128 -> Prop) : (term163 _88128 _88132 f _35706 s) = (term163 _88128 _88132 f _35706 s).
Proof. exact (eq_refl (term163 _88128 _88132 f _35706 s)). Qed.
Lemma lem3393753 {_88128 _88132 : Type'} (_35706 : _88128) (x' : _88128) (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) (h1 : term122 _88128 _88132 x' x f s) : (term164 _88128 _88132 f _35706 s x) = (term165 _88128 _88132 _35706 s f x').
Proof. exact (MK_COMB (@lem3393752 _88128 _88132 f _35706 s) (@lem3393727 _88128 _88132 x' x f s h1)). Qed.
Lemma lem3393754 {_88128 _88132 : Type'} (x' : _88128) (f : _88128 -> _88132) (_35706 : _88128) (s : _88128 -> Prop) : (term165 _88128 _88132 _35706 s f x') = (term166 _88128 _88132 x' f _35706 s).
Proof. exact (eq_refl (term165 _88128 _88132 _35706 s f x')). Qed.
Lemma lem3393755 {_88128 _88132 : Type'} (f : _88128 -> _88132) (_35706 : _88128) (s : _88128 -> Prop) (x : _88132) : (term167 _88128 _88132 f _35706 s x) = (term167 _88128 _88132 f _35706 s x).
Proof. exact (eq_refl (term167 _88128 _88132 f _35706 s x)). Qed.
Lemma lem3393756 {_88128 _88132 : Type'} (x : _88132) (x' : _88128) (f : _88128 -> _88132) (_35706 : _88128) (s : _88128 -> Prop) : ((term164 _88128 _88132 f _35706 s x) = (term165 _88128 _88132 _35706 s f x')) = ((term164 _88128 _88132 f _35706 s x) = (term166 _88128 _88132 x' f _35706 s)).
Proof. exact (MK_COMB (@lem3393755 _88128 _88132 f _35706 s x) (@lem3393754 _88128 _88132 x' f _35706 s)). Qed.
Lemma lem3393757 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (_35706 : _88128) (s : _88128 -> Prop) : (term164 _88128 _88132 f _35706 s x) = (term91 _88128 _88132 x f _35706 s).
Proof. exact (eq_refl (term164 _88128 _88132 f _35706 s x)). Qed.
Lemma lem3393758 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3393759 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (_35706 : _88128) (s : _88128 -> Prop) : (term167 _88128 _88132 f _35706 s x) = (term168 _88128 _88132 x f _35706 s).
Proof. exact (MK_COMB (@lem3393758) (@lem3393757 _88128 _88132 x f _35706 s)). Qed.
Lemma lem3393760 {_88128 _88132 : Type'} (x' : _88128) (f : _88128 -> _88132) (_35706 : _88128) (s : _88128 -> Prop) : (term166 _88128 _88132 x' f _35706 s) = (term166 _88128 _88132 x' f _35706 s).
Proof. exact (eq_refl (term166 _88128 _88132 x' f _35706 s)). Qed.
Lemma lem3393761 {_88128 _88132 : Type'} (x : _88132) (x' : _88128) (f : _88128 -> _88132) (_35706 : _88128) (s : _88128 -> Prop) : ((term164 _88128 _88132 f _35706 s x) = (term166 _88128 _88132 x' f _35706 s)) = ((term91 _88128 _88132 x f _35706 s) = (term166 _88128 _88132 x' f _35706 s)).
Proof. exact (MK_COMB (@lem3393759 _88128 _88132 x f _35706 s) (@lem3393760 _88128 _88132 x' f _35706 s)). Qed.
Lemma lem3393762 {_88128 _88132 : Type'} (x : _88132) (x' : _88128) (f : _88128 -> _88132) (_35706 : _88128) (s : _88128 -> Prop) : ((term164 _88128 _88132 f _35706 s x) = (term165 _88128 _88132 _35706 s f x')) = ((term91 _88128 _88132 x f _35706 s) = (term166 _88128 _88132 x' f _35706 s)).
Proof. exact (TRANS (@lem3393756 _88128 _88132 x x' f _35706 s) (@lem3393761 _88128 _88132 x x' f _35706 s)). Qed.
Lemma lem3393763 {_88128 _88132 : Type'} (_35706 : _88128) (x' : _88128) (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) (h1 : term122 _88128 _88132 x' x f s) : (term91 _88128 _88132 x f _35706 s) = (term166 _88128 _88132 x' f _35706 s).
Proof. exact (EQ_MP (@lem3393762 _88128 _88132 x x' f _35706 s) (@lem3393753 _88128 _88132 _35706 x' x f s h1)). Qed.
Lemma lem3393764 {_88128 _88132 : Type'} (_35706 : _88128) (x' : _88128) (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) (h1 : term122 _88128 _88132 x' x f s) : term166 _88128 _88132 x' f _35706 s.
Proof. exact (EQ_MP (@lem3393763 _88128 _88132 _35706 x' x f s h1) (@lem3393723 _88128 _88132 _35706 x' x f s h1)). Qed.
Lemma lem3393793 {_88128 _88132 : Type'} (s : _88128 -> Prop) (f : _88128 -> _88132) (_35707 : _88128) : (term169 _88128 _88132 s f _35707) = (term169 _88128 _88132 s f _35707).
Proof. exact (eq_refl (term169 _88128 _88132 s f _35707)). Qed.
Lemma lem3393794 {_88128 _88132 : Type'} (_35707 : _88128) (x : _88132) (f : _88128 -> _88132) (x' : _88128) (s : _88128 -> Prop) (h1 : term136 _88128 _88132 x f x' s) : (term170 _88128 _88132 s f _35707 x) = (term171 _88128 _88132 s _35707 f x').
Proof. exact (MK_COMB (@lem3393793 _88128 _88132 s f _35707) (@lem3393735 _88128 _88132 x f x' s h1)). Qed.
Lemma lem3393795 {_88128 _88132 : Type'} (s : _88128 -> Prop) (x' : _88128) (f : _88128 -> _88132) (_35707 : _88128) : (term171 _88128 _88132 s _35707 f x') = (term172 _88128 _88132 s x' f _35707).
Proof. exact (eq_refl (term171 _88128 _88132 s _35707 f x')). Qed.
Lemma lem3393796 {_88128 _88132 : Type'} (s : _88128 -> Prop) (f : _88128 -> _88132) (_35707 : _88128) (x : _88132) : (term173 _88128 _88132 s f _35707 x) = (term173 _88128 _88132 s f _35707 x).
Proof. exact (eq_refl (term173 _88128 _88132 s f _35707 x)). Qed.
Lemma lem3393797 {_88128 _88132 : Type'} (x : _88132) (s : _88128 -> Prop) (x' : _88128) (f : _88128 -> _88132) (_35707 : _88128) : ((term170 _88128 _88132 s f _35707 x) = (term171 _88128 _88132 s _35707 f x')) = ((term170 _88128 _88132 s f _35707 x) = (term172 _88128 _88132 s x' f _35707)).
Proof. exact (MK_COMB (@lem3393796 _88128 _88132 s f _35707 x) (@lem3393795 _88128 _88132 s x' f _35707)). Qed.
Lemma lem3393798 {_88128 _88132 : Type'} (s : _88128 -> Prop) (x : _88132) (f : _88128 -> _88132) (_35707 : _88128) : (term170 _88128 _88132 s f _35707 x) = (term80 _88128 _88132 s x f _35707).
Proof. exact (eq_refl (term170 _88128 _88132 s f _35707 x)). Qed.
Lemma lem3393799 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3393800 {_88128 _88132 : Type'} (s : _88128 -> Prop) (x : _88132) (f : _88128 -> _88132) (_35707 : _88128) : (term173 _88128 _88132 s f _35707 x) = (term174 _88128 _88132 s x f _35707).
Proof. exact (MK_COMB (@lem3393799) (@lem3393798 _88128 _88132 s x f _35707)). Qed.
Lemma lem3393801 {_88128 _88132 : Type'} (s : _88128 -> Prop) (x' : _88128) (f : _88128 -> _88132) (_35707 : _88128) : (term172 _88128 _88132 s x' f _35707) = (term172 _88128 _88132 s x' f _35707).
Proof. exact (eq_refl (term172 _88128 _88132 s x' f _35707)). Qed.
Lemma lem3393802 {_88128 _88132 : Type'} (x : _88132) (s : _88128 -> Prop) (x' : _88128) (f : _88128 -> _88132) (_35707 : _88128) : ((term170 _88128 _88132 s f _35707 x) = (term172 _88128 _88132 s x' f _35707)) = ((term80 _88128 _88132 s x f _35707) = (term172 _88128 _88132 s x' f _35707)).
Proof. exact (MK_COMB (@lem3393800 _88128 _88132 s x f _35707) (@lem3393801 _88128 _88132 s x' f _35707)). Qed.
Lemma lem3393803 {_88128 _88132 : Type'} (x : _88132) (s : _88128 -> Prop) (x' : _88128) (f : _88128 -> _88132) (_35707 : _88128) : ((term170 _88128 _88132 s f _35707 x) = (term171 _88128 _88132 s _35707 f x')) = ((term80 _88128 _88132 s x f _35707) = (term172 _88128 _88132 s x' f _35707)).
Proof. exact (TRANS (@lem3393797 _88128 _88132 x s x' f _35707) (@lem3393802 _88128 _88132 x s x' f _35707)). Qed.
Lemma lem3393804 {_88128 _88132 : Type'} (_35707 : _88128) (x : _88132) (f : _88128 -> _88132) (x' : _88128) (s : _88128 -> Prop) (h1 : term136 _88128 _88132 x f x' s) : (term80 _88128 _88132 s x f _35707) = (term172 _88128 _88132 s x' f _35707).
Proof. exact (EQ_MP (@lem3393803 _88128 _88132 x s x' f _35707) (@lem3393794 _88128 _88132 _35707 x f x' s h1)). Qed.
Lemma lem3393805 {_88128 _88132 : Type'} (_35707 : _88128) (x : _88132) (f : _88128 -> _88132) (x' : _88128) (s : _88128 -> Prop) (h1 : term136 _88128 _88132 x f x' s) : term172 _88128 _88132 s x' f _35707.
Proof. exact (EQ_MP (@lem3393804 _88128 _88132 _35707 x f x' s h1) (@lem3393733 _88128 _88132 _35707 x f x' s h1)). Qed.
Lemma lem3393854 {_88132 : Type'} (x : _88132) : x = x.
Proof. exact (@lem21386 _88132 x). Qed.
Lemma lem3393855 {_88132 : Type'} (x : _88132) : x = x.
Proof. exact (@lem3393854 _88132 x). Qed.
Lemma lem3393856 {_88128 _88132 : Type'} (f : _88128 -> _88132) (x' : _88128) : (f x') = (f x').
Proof. exact (@lem3393855 _88132 (f x')). Qed.
Lemma lem3393857 {_88128 _88132 : Type'} (f : _88128 -> _88132) (x' : _88128) : term175 _88128 _88132 f x'.
Proof. exact (fun h0 : term176 _88128 _88132 f x' => @lem3393856 _88128 _88132 f x'). Qed.
Lemma lem3393859 (p : Prop) : (term177 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3393860 {_88128 _88132 : Type'} (f : _88128 -> _88132) (x' : _88128) : (term175 _88128 _88132 f x') = ((f x') = (f x')).
Proof. exact (@lem3393859 ((f x') = (f x'))). Qed.
Lemma lem3393861 {_88128 _88132 : Type'} (f : _88128 -> _88132) (x' : _88128) : (f x') = (f x').
Proof. exact (EQ_MP (@lem3393860 _88128 _88132 f x') (@lem3393857 _88128 _88132 f x')). Qed.
Lemma lem3393863 {_88128 _88132 : Type'} (x' : _88128) (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) (h1 : term122 _88128 _88132 x' x f s) : @IN _88128 x' s.
Proof. exact (proj1 (@lem3393663 _88128 _88132 x' x f s h1)). Qed.
Lemma lem3393864 {_88128 _88132 : Type'} (x' : _88128) (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) (h1 : term122 _88128 _88132 x' x f s) : term178 _88128 x' s.
Proof. exact (fun h0 : term179 _88128 x' s => @lem3393863 _88128 _88132 x' x f s h1). Qed.
Lemma lem3393866 (p : Prop) : (term177 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3393867 {_88128 : Type'} (x' : _88128) (s : _88128 -> Prop) : (term178 _88128 x' s) = (@IN _88128 x' s).
Proof. exact (@lem3393866 (@IN _88128 x' s)). Qed.
Lemma lem3393868 {_88128 _88132 : Type'} (x' : _88128) (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) (h1 : term122 _88128 _88132 x' x f s) : @IN _88128 x' s.
Proof. exact (EQ_MP (@lem3393867 _88128 x' s) (@lem3393864 _88128 _88132 x' x f s h1)). Qed.
Lemma lem3393870 (a : Prop) (b : Prop) : (term180 a b) = (term181 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3393871 {_88128 _88132 : Type'} (x' : _88128) (f : _88128 -> _88132) (_35706 : _88128) (s : _88128 -> Prop) : (term166 _88128 _88132 x' f _35706 s) = (term182 _88128 _88132 x' f _35706 s).
Proof. exact (@lem3393870 ((f x') = (f _35706)) (@IN _88128 _35706 s)). Qed.
Lemma lem3393873 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3393874 {_88128 _88132 : Type'} (x' : _88128) (f : _88128 -> _88132) (_35706 : _88128) (s : _88128 -> Prop) : (term182 _88128 _88132 x' f _35706 s) = (term183 _88128 _88132 x' f _35706 s).
Proof. exact (@lem3393873 (term184 _88128 _88132 x' f _35706 s)). Qed.
Lemma lem3393875 {_88128 _88132 : Type'} (x' : _88128) (f : _88128 -> _88132) (_35706 : _88128) (s : _88128 -> Prop) : (term166 _88128 _88132 x' f _35706 s) = (term183 _88128 _88132 x' f _35706 s).
Proof. exact (TRANS (@lem3393871 _88128 _88132 x' f _35706 s) (@lem3393874 _88128 _88132 x' f _35706 s)). Qed.
Lemma lem3393877 {_88128 _88132 : Type'} (x' : _88128) (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) (h1 : term122 _88128 _88132 x' x f s) : term185 _88128 _88132 f x' s.
Proof. exact (conj (@lem3393861 _88128 _88132 f x') (@lem3393868 _88128 _88132 x' x f s h1)). Qed.
Lemma lem3393879 {_88128 _88132 : Type'} (_35706 : _88128) (x' : _88128) (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) (h1 : term122 _88128 _88132 x' x f s) : term183 _88128 _88132 x' f _35706 s.
Proof. exact (EQ_MP (@lem3393875 _88128 _88132 x' f _35706 s) (@lem3393764 _88128 _88132 _35706 x' x f s h1)). Qed.
Lemma lem3393880 {_88128 _88132 : Type'} (_35706 : _88128) (x' : _88128) (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) (h1 : term122 _88128 _88132 x' x f s) : term183 _88128 _88132 x' f _35706 s.
Proof. exact (@lem3393879 _88128 _88132 _35706 x' x f s h1). Qed.
Lemma lem3393881 {_88128 _88132 : Type'} (x' : _88128) (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) (h1 : term122 _88128 _88132 x' x f s) : term186 _88128 _88132 f x' s.
Proof. exact (@lem3393880 _88128 _88132 x' x' x f s h1). Qed.
Lemma lem3393884 {_88128 _88132 : Type'} (x' : _88128) (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) (h1 : term122 _88128 _88132 x' x f s) : False.
Proof. exact (@lem3393881 _88128 _88132 x' x f s h1 (@lem3393877 _88128 _88132 x' x f s h1)). Qed.
Lemma lem3393885 {_88128 _88132 : Type'} (x' : _88128) (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) (h1 : term122 _88128 _88132 x' x f s) : term187.
Proof. exact (fun h0 : ~ False => @lem3393884 _88128 _88132 x' x f s h1). Qed.
Lemma lem3393887 (p : Prop) : (term177 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3393888 : term187 = False.
Proof. exact (@lem3393887 False). Qed.
Lemma lem3393924 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (x' : _88128) (s : _88128 -> Prop) (h1 : term136 _88128 _88132 x f x' s) : @IN _88128 x' s.
Proof. exact (proj2 (@lem3393666 _88128 _88132 x f x' s h1)). Qed.
Lemma lem3393925 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (x' : _88128) (s : _88128 -> Prop) (h1 : term136 _88128 _88132 x f x' s) : term178 _88128 x' s.
Proof. exact (fun h0 : term179 _88128 x' s => @lem3393924 _88128 _88132 x f x' s h1). Qed.
Lemma lem3393927 (p : Prop) : (term177 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3393928 {_88128 : Type'} (x' : _88128) (s : _88128 -> Prop) : (term178 _88128 x' s) = (@IN _88128 x' s).
Proof. exact (@lem3393927 (@IN _88128 x' s)). Qed.
Lemma lem3393929 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (x' : _88128) (s : _88128 -> Prop) (h1 : term136 _88128 _88132 x f x' s) : @IN _88128 x' s.
Proof. exact (EQ_MP (@lem3393928 _88128 x' s) (@lem3393925 _88128 _88132 x f x' s h1)). Qed.
Lemma lem3393931 {_88132 : Type'} (x : _88132) : x = x.
Proof. exact (@lem21386 _88132 x). Qed.
Lemma lem3393932 {_88132 : Type'} (x : _88132) : x = x.
Proof. exact (@lem3393931 _88132 x). Qed.
Lemma lem3393933 {_88128 _88132 : Type'} (f : _88128 -> _88132) (x' : _88128) : (f x') = (f x').
Proof. exact (@lem3393932 _88132 (f x')). Qed.
Lemma lem3393934 {_88128 _88132 : Type'} (f : _88128 -> _88132) (x' : _88128) : term175 _88128 _88132 f x'.
Proof. exact (fun h0 : term176 _88128 _88132 f x' => @lem3393933 _88128 _88132 f x'). Qed.
Lemma lem3393936 (p : Prop) : (term177 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3393937 {_88128 _88132 : Type'} (f : _88128 -> _88132) (x' : _88128) : (term175 _88128 _88132 f x') = ((f x') = (f x')).
Proof. exact (@lem3393936 ((f x') = (f x'))). Qed.
Lemma lem3393938 {_88128 _88132 : Type'} (f : _88128 -> _88132) (x' : _88128) : (f x') = (f x').
Proof. exact (EQ_MP (@lem3393937 _88128 _88132 f x') (@lem3393934 _88128 _88132 f x')). Qed.
Lemma lem3393940 (a : Prop) (b : Prop) : (term180 a b) = (term181 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3393941 {_88128 _88132 : Type'} (s : _88128 -> Prop) (x' : _88128) (f : _88128 -> _88132) (_35707 : _88128) : (term172 _88128 _88132 s x' f _35707) = (term188 _88128 _88132 s x' f _35707).
Proof. exact (@lem3393940 (@IN _88128 _35707 s) ((f x') = (f _35707))). Qed.
Lemma lem3393943 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3393944 {_88128 _88132 : Type'} (s : _88128 -> Prop) (x' : _88128) (f : _88128 -> _88132) (_35707 : _88128) : (term188 _88128 _88132 s x' f _35707) = (term189 _88128 _88132 s x' f _35707).
Proof. exact (@lem3393943 (term190 _88128 _88132 s x' f _35707)). Qed.
Lemma lem3393945 {_88128 _88132 : Type'} (s : _88128 -> Prop) (x' : _88128) (f : _88128 -> _88132) (_35707 : _88128) : (term172 _88128 _88132 s x' f _35707) = (term189 _88128 _88132 s x' f _35707).
Proof. exact (TRANS (@lem3393941 _88128 _88132 s x' f _35707) (@lem3393944 _88128 _88132 s x' f _35707)). Qed.
Lemma lem3393947 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (x' : _88128) (s : _88128 -> Prop) (h1 : term136 _88128 _88132 x f x' s) : term191 _88128 _88132 s f x'.
Proof. exact (conj (@lem3393929 _88128 _88132 x f x' s h1) (@lem3393938 _88128 _88132 f x')). Qed.
Lemma lem3393949 {_88128 _88132 : Type'} (_35707 : _88128) (x : _88132) (f : _88128 -> _88132) (x' : _88128) (s : _88128 -> Prop) (h1 : term136 _88128 _88132 x f x' s) : term189 _88128 _88132 s x' f _35707.
Proof. exact (EQ_MP (@lem3393945 _88128 _88132 s x' f _35707) (@lem3393805 _88128 _88132 _35707 x f x' s h1)). Qed.
Lemma lem3393950 {_88128 _88132 : Type'} (_35707 : _88128) (x : _88132) (f : _88128 -> _88132) (x' : _88128) (s : _88128 -> Prop) (h1 : term136 _88128 _88132 x f x' s) : term189 _88128 _88132 s x' f _35707.
Proof. exact (@lem3393949 _88128 _88132 _35707 x f x' s h1). Qed.
Lemma lem3393951 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (x' : _88128) (s : _88128 -> Prop) (h1 : term136 _88128 _88132 x f x' s) : term192 _88128 _88132 s f x'.
Proof. exact (@lem3393950 _88128 _88132 x' x f x' s h1). Qed.
Lemma lem3393954 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (x' : _88128) (s : _88128 -> Prop) (h1 : term136 _88128 _88132 x f x' s) : False.
Proof. exact (@lem3393951 _88128 _88132 x f x' s h1 (@lem3393947 _88128 _88132 x f x' s h1)). Qed.
Lemma lem3393955 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (x' : _88128) (s : _88128 -> Prop) (h1 : term136 _88128 _88132 x f x' s) : term187.
Proof. exact (fun h0 : ~ False => @lem3393954 _88128 _88132 x f x' s h1). Qed.
Lemma lem3393957 (p : Prop) : (term177 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3393958 : term187 = False.
Proof. exact (@lem3393957 False). Qed.
Lemma lem3393960 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (x' : _88128) (s : _88128 -> Prop) (h1 : term136 _88128 _88132 x f x' s) : False.
Proof. exact (EQ_MP (@lem3393958) (@lem3393955 _88128 _88132 x f x' s h1)). Qed.
Lemma lem3393961 {_88128 _88132 : Type'} (x' : _88128) (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) (h1 : term122 _88128 _88132 x' x f s) : False.
Proof. exact (EQ_MP (@lem3393888) (@lem3393885 _88128 _88132 x' x f s h1)). Qed.
Lemma lem3393962 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (x' : _88128) (s : _88128 -> Prop) (h1 : term157 _88128 _88132 x f x' s) : False.
Proof. exact (or_elim (@lem3393659 _88128 _88132 x f x' s h1) (fun h0 : term122 _88128 _88132 x' x f s => @lem3393961 _88128 _88132 x' x f s h0) (fun h0 : term136 _88128 _88132 x f x' s => @lem3393960 _88128 _88132 x f x' s h0)). Qed.
Lemma lem3393963 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (x' : _88128) (s : _88128 -> Prop) (h1 : term157 _88128 _88132 x f x' s) : (term157 _88128 _88132 x f x' s) = False.
Proof. exact (prop_ext (fun h2 : term157 _88128 _88132 x f x' s => @lem3393962 _88128 _88132 x f x' s h1) (fun h2 : False => @lem3393659 _88128 _88132 x f x' s h1)). Qed.
Lemma lem3393964 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (x' : _88128) (s : _88128 -> Prop) (h1 : term157 _88128 _88132 x f x' s) : False.
Proof. exact (EQ_MP (@lem3393963 _88128 _88132 x f x' s h1) (@lem3393659 _88128 _88132 x f x' s h1)). Qed.
Lemma lem3393965 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) (h1 : term78 _88128 _88132 x f s) : False.
Proof. exact (ex_elim (@lem3393574 _88128 _88132 x f s h1) (fun x' : _88128 => fun h0 : term159 _88128 _88132 x f s x' => @lem3393964 _88128 _88132 x f x' s h0)). Qed.
Lemma lem3393966 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) (h1 : term78 _88128 _88132 x f s) : (term78 _88128 _88132 x f s) = False.
Proof. exact (prop_ext (fun h2 : term78 _88128 _88132 x f s => @lem3393965 _88128 _88132 x f s h1) (fun h2 : False => @lem3393242 _88128 _88132 x f s h1)). Qed.
Lemma lem3393967 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) (h1 : term78 _88128 _88132 x f s) : False.
Proof. exact (EQ_MP (@lem3393966 _88128 _88132 x f s h1) (@lem3393242 _88128 _88132 x f s h1)). Qed.
Lemma lem3393968 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) : term77 _88128 _88132 x f s.
Proof. exact (fun h0 : term78 _88128 _88132 x f s => @lem3393967 _88128 _88132 x f s h0). Qed.
Lemma lem3393969 {_88128 _88132 : Type'} (x : _88132) (f : _88128 -> _88132) (s : _88128 -> Prop) : (term54 _88128 _88132 s x f) = (term6 _88128 _88132 x f s).
Proof. exact (EQ_MP (@lem3393241 _88128 _88132 x f s) (@lem3393968 _88128 _88132 x f s)). Qed.
Lemma lem3393974 {_88128 _88132 : Type'} (f : _88128 -> _88132) (s : _88128 -> Prop) : term58 _88128 _88132 f s.
Proof. exact (fun x : _88132 => @lem3393969 _88128 _88132 x f s). Qed.
Lemma lem3393979 {_88128 _88132 : Type'} (f : _88128 -> _88132) : term62 _88128 _88132 f.
Proof. exact (fun s : _88128 -> Prop => @lem3393974 _88128 _88132 f s). Qed.
Lemma lem3393984 {_88128 _88132 : Type'} : term66 _88128 _88132.
Proof. exact (fun f : _88128 -> _88132 => @lem3393979 _88128 _88132 f). Qed.
Lemma lem3393985 {_88128 _88132 : Type'} : term68 _88128 _88132.
Proof. exact (EQ_MP (@lem3393237 _88128 _88132) (@lem3393984 _88128 _88132)). Qed.
Lemma lem3393987 {_88128 _88132 : Type'} : term68 _88128 _88132.
Proof. exact (@lem3393048 _88128 _88132 (@lem3393985 _88128 _88132)). Qed.
Lemma lem3393988 {_88128 _88132 : Type'} (h1 : term69 _88128 _88132) : False.
Proof. exact (@lem3393987 _88128 _88132 (@lem3393032 _88128 _88132 h1)). Qed.
Lemma lem3393989 {_88128 _88132 : Type'} (h1 : term69 _88128 _88132) : (term69 _88128 _88132) = False.
Proof. exact (prop_ext (fun h2 : term69 _88128 _88132 => @lem3393988 _88128 _88132 h1) (fun h2 : False => @lem3393032 _88128 _88132 h1)). Qed.
Lemma lem3393990 {_88128 _88132 : Type'} (h1 : term69 _88128 _88132) : False.
Proof. exact (EQ_MP (@lem3393989 _88128 _88132 h1) (@lem3393032 _88128 _88132 h1)). Qed.
Lemma lem3393991 {_88128 _88132 : Type'} : term68 _88128 _88132.
Proof. exact (fun h0 : term69 _88128 _88132 => @lem3393990 _88128 _88132 h0). Qed.
Lemma lem3393992 {_88128 _88132 : Type'} : term66 _88128 _88132.
Proof. exact (EQ_MP (@lem3393031 _88128 _88132) (@lem3393991 _88128 _88132)). Qed.
Lemma lem3393993 {_88128 _88132 : Type'} : term65 _88128 _88132.
Proof. exact (EQ_MP (@lem3393027 _88128 _88132) (@lem3393992 _88128 _88132)). Qed.
