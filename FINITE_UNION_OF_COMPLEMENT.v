Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_UNION_OF_COMPLEMENT_term_abbrevs.
Require Import COMPL_COMPL_spec.
Require Import DISJ_ASSOC_spec.
Require Import FINITE_IMAGE_spec.
Require Import FORALL_IN_IMAGE_spec.
Require Import IMAGE_ID_spec.
Require Import INTERSECTION_OF_spec.
Require Import INTERS_UNIONS_spec.
Require Import UNIONS_INTERS_spec.
Require Import UNION_OF_spec.
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
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm32_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211647_spec.
Require Import thm3211648_spec.
Require Import thm3211656_spec.
Require Import thm3211657_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem4876896 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem4876897 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem4876898 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem4876897 t1) (@lem4876896 t1)). Qed.
Lemma lem4876899 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem4876898 t1 t2). Qed.
Lemma lem4876900 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem4876901 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem4876900 t1 t2) (@lem4876899 t1 t2)). Qed.
Lemma lem4876902 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem4876901 t1 t2 t3). Qed.
Lemma lem4876903 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem4876904 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem4876903 t1 t2 t3) (@lem4876902 t1 t2 t3)). Qed.
Lemma lem4876905 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem4876904 t1 t2 t3)). Qed.
Lemma lem4876909 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term7 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem4876910 {_112226 : Type'} (s : _112226 -> Prop) (t : _112226 -> Prop) : (s = t) = (term7 _112226 s t).
Proof. exact (@lem4876909 _112226 s t). Qed.
Lemma lem4876911 {_112226 _112228 _112229 : Type'} (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : ((term8 _112226 _112228 _112229 g s f) = (term9 _112226 _112228 _112229 f g s)) = (term10 _112226 _112228 _112229 f g s).
Proof. exact (@lem4876910 _112226 (term8 _112226 _112228 _112229 g s f) (term9 _112226 _112228 _112229 f g s)). Qed.
Lemma lem4876924 {_112226 _112228 _112229 : Type'} (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term10 _112226 _112228 _112229 f g s) = ((term8 _112226 _112228 _112229 g s f) = (term9 _112226 _112228 _112229 f g s)).
Proof. exact (SYM (@lem4876911 _112226 _112228 _112229 f g s)). Qed.
Lemma lem4876934 {_83064 : Type'} (P : type919 _83064) (x : _83064) : (term11 _83064 x P) = (term12 _83064 P x).
Proof. exact (EQ_MP (@lem3211648 _83064 P x) (@lem3211647 _83064 P x)). Qed.
Lemma lem4876935 {_112226 : Type'} (P : type919 _112226) (x : _112226) : (term11 _112226 x P) = (term12 _112226 P x).
Proof. exact (@lem4876934 _112226 P x). Qed.
Lemma lem4876936 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (f : _112228 -> _112226) (x : _112226) : (term13 _112226 _112228 _112229 x g s f) = (term14 _112226 _112228 _112229 g s f x).
Proof. exact (@lem4876935 _112226 (term15 _112226 _112228 _112229 g s f) x). Qed.
Lemma lem4876937 {_112226 _112228 _112229 : Type'} (GEN_PVAR_213 : _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (f : _112228 -> _112226) : (term16 _112226 _112228 _112229 g s f GEN_PVAR_213) = (term17 _112226 _112228 _112229 GEN_PVAR_213 g s f).
Proof. exact (eq_refl (term16 _112226 _112228 _112229 g s f GEN_PVAR_213)). Qed.
Lemma lem4876938 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (f : _112228 -> _112226) : (term18 _112226 _112228 _112229 g s f) = (term19 _112226 _112228 _112229 g s f).
Proof. exact (fun_ext (fun GEN_PVAR_213 : _112226 => @lem4876937 _112226 _112228 _112229 GEN_PVAR_213 g s f)). Qed.
Lemma lem4876939 {_112226 : Type'} : (@GSPEC _112226) = (@GSPEC _112226).
Proof. exact (eq_refl (@GSPEC _112226)). Qed.
Lemma lem4876940 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (f : _112228 -> _112226) : (term20 _112226 _112228 _112229 g s f) = (term8 _112226 _112228 _112229 g s f).
Proof. exact (MK_COMB (@lem4876939 _112226) (@lem4876938 _112226 _112228 _112229 g s f)). Qed.
Lemma lem4876941 {_112226 : Type'} (x : _112226) : (@IN _112226 x) = (@IN _112226 x).
Proof. exact (eq_refl (@IN _112226 x)). Qed.
Lemma lem4876942 {_112226 _112228 _112229 : Type'} (x : _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (f : _112228 -> _112226) : (term13 _112226 _112228 _112229 x g s f) = (term21 _112226 _112228 _112229 x g s f).
Proof. exact (MK_COMB (@lem4876941 _112226 x) (@lem4876940 _112226 _112228 _112229 g s f)). Qed.
Lemma lem4876943 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4876944 {_112226 _112228 _112229 : Type'} (x : _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (f : _112228 -> _112226) : (term22 _112226 _112228 _112229 x g s f) = (term23 _112226 _112228 _112229 x g s f).
Proof. exact (MK_COMB (@lem4876943) (@lem4876942 _112226 _112228 _112229 x g s f)). Qed.
Lemma lem4876945 {_112226 _112228 _112229 : Type'} (x : _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (f : _112228 -> _112226) : (term14 _112226 _112228 _112229 g s f x) = (term24 _112226 _112228 _112229 x g s f).
Proof. exact (eq_refl (term14 _112226 _112228 _112229 g s f x)). Qed.
Lemma lem4876946 {_112226 _112228 _112229 : Type'} (x : _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (f : _112228 -> _112226) : ((term13 _112226 _112228 _112229 x g s f) = (term14 _112226 _112228 _112229 g s f x)) = ((term21 _112226 _112228 _112229 x g s f) = (term24 _112226 _112228 _112229 x g s f)).
Proof. exact (MK_COMB (@lem4876944 _112226 _112228 _112229 x g s f) (@lem4876945 _112226 _112228 _112229 x g s f)). Qed.
Lemma lem4876947 {_112226 _112228 _112229 : Type'} (x : _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (f : _112228 -> _112226) : (term21 _112226 _112228 _112229 x g s f) = (term24 _112226 _112228 _112229 x g s f).
Proof. exact (EQ_MP (@lem4876946 _112226 _112228 _112229 x g s f) (@lem4876936 _112226 _112228 _112229 g s f x)). Qed.
Lemma lem4876953 {A B : Type'} (f : A -> B) (y : A) : (term25 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4876954 {_112226 : Type'} (f : type1538 _112226) (y : Prop) : (term26 _112226 f y) = (f y).
Proof. exact (@lem4876953 Prop (_112226 -> Prop) f y). Qed.
Lemma lem4876955 {_112226 _112228 _112229 : Type'} (x : _112226) (y : _112228) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term27 _112226 _112228 _112229 x y g s) = (term28 _112226 _112228 _112229 x y g s).
Proof. exact (@lem4876954 _112226 (term29 _112226 x) (term30 _112228 _112229 y g s)). Qed.
Lemma lem4876956 {_112226 : Type'} (p : Prop) (x : _112226) : (term31 _112226 x p) = (term32 _112226 p x).
Proof. exact (eq_refl (term31 _112226 x p)). Qed.
Lemma lem4876957 {_112226 : Type'} (x : _112226) : (term33 _112226 x) = (term29 _112226 x).
Proof. exact (fun_ext (fun p : Prop => @lem4876956 _112226 p x)). Qed.
Lemma lem4876958 {_112228 _112229 : Type'} (y : _112228) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term30 _112228 _112229 y g s) = (term30 _112228 _112229 y g s).
Proof. exact (eq_refl (term30 _112228 _112229 y g s)). Qed.
Lemma lem4876959 {_112226 _112228 _112229 : Type'} (x : _112226) (y : _112228) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term27 _112226 _112228 _112229 x y g s) = (term28 _112226 _112228 _112229 x y g s).
Proof. exact (MK_COMB (@lem4876957 _112226 x) (@lem4876958 _112228 _112229 y g s)). Qed.
Lemma lem4876960 {_112226 : Type'} : (@eq (_112226 -> Prop)) = (@eq (_112226 -> Prop)).
Proof. exact (eq_refl (@eq (_112226 -> Prop))). Qed.
Lemma lem4876961 {_112226 _112228 _112229 : Type'} (x : _112226) (y : _112228) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term34 _112226 _112228 _112229 x y g s) = (term35 _112226 _112228 _112229 x y g s).
Proof. exact (MK_COMB (@lem4876960 _112226) (@lem4876959 _112226 _112228 _112229 x y g s)). Qed.
Lemma lem4876962 {_112226 _112228 _112229 : Type'} (y : _112228) (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) : (term28 _112226 _112228 _112229 x y g s) = (term36 _112226 _112228 _112229 y g s x).
Proof. exact (eq_refl (term28 _112226 _112228 _112229 x y g s)). Qed.
Lemma lem4876963 {_112226 _112228 _112229 : Type'} (y : _112228) (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) : ((term27 _112226 _112228 _112229 x y g s) = (term28 _112226 _112228 _112229 x y g s)) = ((term28 _112226 _112228 _112229 x y g s) = (term36 _112226 _112228 _112229 y g s x)).
Proof. exact (MK_COMB (@lem4876961 _112226 _112228 _112229 x y g s) (@lem4876962 _112226 _112228 _112229 y g s x)). Qed.
Lemma lem4876964 {_112226 _112228 _112229 : Type'} (y : _112228) (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) : (term28 _112226 _112228 _112229 x y g s) = (term36 _112226 _112228 _112229 y g s x).
Proof. exact (EQ_MP (@lem4876963 _112226 _112228 _112229 y g s x) (@lem4876955 _112226 _112228 _112229 x y g s)). Qed.
Lemma lem4876968 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term37 A B y f s) = (term38 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem4876969 {_112228 _112229 : Type'} (y : _112228) (f : _112229 -> _112228) (s : _112229 -> Prop) : (term30 _112228 _112229 y f s) = (term39 _112228 _112229 y f s).
Proof. exact (@lem4876968 _112229 _112228 y f s). Qed.
Lemma lem4876970 {_112228 _112229 : Type'} (y : _112228) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term30 _112228 _112229 y g s) = (term39 _112228 _112229 y g s).
Proof. exact (@lem4876969 _112228 _112229 y g s). Qed.
Lemma lem4876980 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4876981 {_112229 : Type'} (P : _112229 -> Prop) (x : _112229) : (@IN _112229 x P) = (P x).
Proof. exact (@lem4876980 _112229 P x). Qed.
Lemma lem4876982 {_112229 : Type'} (s : _112229 -> Prop) (x : _112229) : (@IN _112229 x s) = (s x).
Proof. exact (@lem4876981 _112229 s x). Qed.
Lemma lem4876983 {_112228 _112229 : Type'} (y : _112228) (g : _112229 -> _112228) (x : _112229) : (term40 _112228 _112229 y g x) = (term40 _112228 _112229 y g x).
Proof. exact (eq_refl (term40 _112228 _112229 y g x)). Qed.
Lemma lem4876984 {_112228 _112229 : Type'} (y : _112228) (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112229) : (term41 _112228 _112229 y g x s) = (term42 _112228 _112229 y g s x).
Proof. exact (MK_COMB (@lem4876983 _112228 _112229 y g x) (@lem4876982 _112229 s x)). Qed.
Lemma lem4876987 {_112228 _112229 : Type'} (y : _112228) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term43 _112228 _112229 y g s) = (term44 _112228 _112229 y g s).
Proof. exact (fun_ext (fun x : _112229 => @lem4876984 _112228 _112229 y g s x)). Qed.
Lemma lem4876988 {_112229 : Type'} : (@ex _112229) = (@ex _112229).
Proof. exact (eq_refl (@ex _112229)). Qed.
Lemma lem4876989 {_112228 _112229 : Type'} (y : _112228) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term39 _112228 _112229 y g s) = (term45 _112228 _112229 y g s).
Proof. exact (MK_COMB (@lem4876988 _112229) (@lem4876987 _112228 _112229 y g s)). Qed.
Lemma lem4876994 {_112228 _112229 : Type'} (y : _112228) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term30 _112228 _112229 y g s) = (term45 _112228 _112229 y g s).
Proof. exact (TRANS (@lem4876970 _112228 _112229 y g s) (@lem4876989 _112228 _112229 y g s)). Qed.
Lemma lem4876995 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4876996 {_112228 _112229 : Type'} (y : _112228) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term46 _112228 _112229 y g s) = (term47 _112228 _112229 y g s).
Proof. exact (MK_COMB (@lem4876995) (@lem4876994 _112228 _112229 y g s)). Qed.
Lemma lem4876999 {_112226 : Type'} (x : _112226) (t : _112226) : (x = t) = (x = t).
Proof. exact (eq_refl (x = t)). Qed.
Lemma lem4877000 {_112226 _112228 _112229 : Type'} (y : _112228) (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (t : _112226) : (term48 _112226 _112228 _112229 y g s x t) = (term49 _112226 _112228 _112229 y g s x t).
Proof. exact (MK_COMB (@lem4876996 _112228 _112229 y g s) (@lem4876999 _112226 x t)). Qed.
Lemma lem4877003 {_112226 _112228 _112229 : Type'} (y : _112228) (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) : (term36 _112226 _112228 _112229 y g s x) = (term50 _112226 _112228 _112229 y g s x).
Proof. exact (fun_ext (fun t : _112226 => @lem4877000 _112226 _112228 _112229 y g s x t)). Qed.
Lemma lem4877004 {_112226 _112228 _112229 : Type'} (y : _112228) (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) : (term28 _112226 _112228 _112229 x y g s) = (term50 _112226 _112228 _112229 y g s x).
Proof. exact (TRANS (@lem4876964 _112226 _112228 _112229 y g s x) (@lem4877003 _112226 _112228 _112229 y g s x)). Qed.
Lemma lem4877005 {_112226 _112228 : Type'} (f : _112228 -> _112226) (y : _112228) : (f y) = (f y).
Proof. exact (eq_refl (f y)). Qed.
Lemma lem4877006 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (f : _112228 -> _112226) (y : _112228) : (term51 _112226 _112228 _112229 x g s f y) = (term52 _112226 _112228 _112229 g s x f y).
Proof. exact (MK_COMB (@lem4877004 _112226 _112228 _112229 y g s x) (@lem4877005 _112226 _112228 f y)). Qed.
Lemma lem4877008 {A B : Type'} (f : A -> B) (y : A) : (term25 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4877009 {_112226 : Type'} (f : _112226 -> Prop) (y : _112226) : (term53 _112226 f y) = (f y).
Proof. exact (@lem4877008 _112226 Prop f y). Qed.
Lemma lem4877010 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (f : _112228 -> _112226) (y : _112228) : (term54 _112226 _112228 _112229 g s x f y) = (term52 _112226 _112228 _112229 g s x f y).
Proof. exact (@lem4877009 _112226 (term50 _112226 _112228 _112229 y g s x) (f y)). Qed.
Lemma lem4877011 {_112226 _112228 _112229 : Type'} (y : _112228) (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (t : _112226) : (term55 _112226 _112228 _112229 y g s x t) = (term49 _112226 _112228 _112229 y g s x t).
Proof. exact (eq_refl (term55 _112226 _112228 _112229 y g s x t)). Qed.
Lemma lem4877012 {_112226 _112228 _112229 : Type'} (y : _112228) (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) : (term56 _112226 _112228 _112229 y g s x) = (term50 _112226 _112228 _112229 y g s x).
Proof. exact (fun_ext (fun t : _112226 => @lem4877011 _112226 _112228 _112229 y g s x t)). Qed.
Lemma lem4877013 {_112226 _112228 : Type'} (f : _112228 -> _112226) (y : _112228) : (f y) = (f y).
Proof. exact (eq_refl (f y)). Qed.
Lemma lem4877014 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (f : _112228 -> _112226) (y : _112228) : (term54 _112226 _112228 _112229 g s x f y) = (term52 _112226 _112228 _112229 g s x f y).
Proof. exact (MK_COMB (@lem4877012 _112226 _112228 _112229 y g s x) (@lem4877013 _112226 _112228 f y)). Qed.
Lemma lem4877015 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4877016 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (f : _112228 -> _112226) (y : _112228) : (term57 _112226 _112228 _112229 g s x f y) = (term58 _112226 _112228 _112229 g s x f y).
Proof. exact (MK_COMB (@lem4877015) (@lem4877014 _112226 _112228 _112229 g s x f y)). Qed.
Lemma lem4877017 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (f : _112228 -> _112226) (y : _112228) : (term52 _112226 _112228 _112229 g s x f y) = (term59 _112226 _112228 _112229 g s x f y).
Proof. exact (eq_refl (term52 _112226 _112228 _112229 g s x f y)). Qed.
Lemma lem4877018 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (f : _112228 -> _112226) (y : _112228) : ((term54 _112226 _112228 _112229 g s x f y) = (term52 _112226 _112228 _112229 g s x f y)) = ((term52 _112226 _112228 _112229 g s x f y) = (term59 _112226 _112228 _112229 g s x f y)).
Proof. exact (MK_COMB (@lem4877016 _112226 _112228 _112229 g s x f y) (@lem4877017 _112226 _112228 _112229 g s x f y)). Qed.
Lemma lem4877019 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (f : _112228 -> _112226) (y : _112228) : (term52 _112226 _112228 _112229 g s x f y) = (term59 _112226 _112228 _112229 g s x f y).
Proof. exact (EQ_MP (@lem4877018 _112226 _112228 _112229 g s x f y) (@lem4877010 _112226 _112228 _112229 g s x f y)). Qed.
Lemma lem4877032 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (f : _112228 -> _112226) (y : _112228) : (term51 _112226 _112228 _112229 x g s f y) = (term59 _112226 _112228 _112229 g s x f y).
Proof. exact (TRANS (@lem4877006 _112226 _112228 _112229 g s x f y) (@lem4877019 _112226 _112228 _112229 g s x f y)). Qed.
Lemma lem4877033 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (f : _112228 -> _112226) : (term60 _112226 _112228 _112229 x g s f) = (term61 _112226 _112228 _112229 g s x f).
Proof. exact (fun_ext (fun y : _112228 => @lem4877032 _112226 _112228 _112229 g s x f y)). Qed.
Lemma lem4877034 {_112228 : Type'} : (@ex _112228) = (@ex _112228).
Proof. exact (eq_refl (@ex _112228)). Qed.
Lemma lem4877035 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (f : _112228 -> _112226) : (term24 _112226 _112228 _112229 x g s f) = (term62 _112226 _112228 _112229 g s x f).
Proof. exact (MK_COMB (@lem4877034 _112228) (@lem4877033 _112226 _112228 _112229 g s x f)). Qed.
Lemma lem4877040 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (f : _112228 -> _112226) : (term21 _112226 _112228 _112229 x g s f) = (term62 _112226 _112228 _112229 g s x f).
Proof. exact (TRANS (@lem4876947 _112226 _112228 _112229 x g s f) (@lem4877035 _112226 _112228 _112229 g s x f)). Qed.
Lemma lem4877041 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4877042 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (f : _112228 -> _112226) : (term23 _112226 _112228 _112229 x g s f) = (term63 _112226 _112228 _112229 g s x f).
Proof. exact (MK_COMB (@lem4877041) (@lem4877040 _112226 _112228 _112229 g s x f)). Qed.
Lemma lem4877044 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term37 A B y f s) = (term38 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem4877045 {_112226 _112229 : Type'} (y : _112226) (f : _112229 -> _112226) (s : _112229 -> Prop) : (term30 _112226 _112229 y f s) = (term39 _112226 _112229 y f s).
Proof. exact (@lem4877044 _112229 _112226 y f s). Qed.
Lemma lem4877046 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term64 _112226 _112228 _112229 x f g s) = (term65 _112226 _112228 _112229 x f g s).
Proof. exact (@lem4877045 _112226 _112229 x (term66 _112226 _112228 _112229 f g) s). Qed.
Lemma lem4877056 {A B : Type'} (f : A -> B) (y : A) : (term25 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4877057 {_112226 _112229 : Type'} (f : _112229 -> _112226) (y : _112229) : (term67 _112226 _112229 f y) = (f y).
Proof. exact (@lem4877056 _112229 _112226 f y). Qed.
Lemma lem4877058 {_112226 _112228 _112229 : Type'} (f : _112228 -> _112226) (g : _112229 -> _112228) (x : _112229) : (term68 _112226 _112228 _112229 f g x) = (term69 _112226 _112228 _112229 f g x).
Proof. exact (@lem4877057 _112226 _112229 (term66 _112226 _112228 _112229 f g) x). Qed.
Lemma lem4877059 {_112226 _112228 _112229 : Type'} (f : _112228 -> _112226) (g : _112229 -> _112228) (x : _112229) : (term69 _112226 _112228 _112229 f g x) = (term70 _112226 _112228 _112229 f g x).
Proof. exact (eq_refl (term69 _112226 _112228 _112229 f g x)). Qed.
Lemma lem4877060 {_112226 _112228 _112229 : Type'} (f : _112228 -> _112226) (g : _112229 -> _112228) : (term71 _112226 _112228 _112229 f g) = (term66 _112226 _112228 _112229 f g).
Proof. exact (fun_ext (fun x : _112229 => @lem4877059 _112226 _112228 _112229 f g x)). Qed.
Lemma lem4877061 {_112229 : Type'} (x : _112229) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4877062 {_112226 _112228 _112229 : Type'} (f : _112228 -> _112226) (g : _112229 -> _112228) (x : _112229) : (term68 _112226 _112228 _112229 f g x) = (term69 _112226 _112228 _112229 f g x).
Proof. exact (MK_COMB (@lem4877060 _112226 _112228 _112229 f g) (@lem4877061 _112229 x)). Qed.
Lemma lem4877063 {_112226 : Type'} : (@eq _112226) = (@eq _112226).
Proof. exact (eq_refl (@eq _112226)). Qed.
Lemma lem4877064 {_112226 _112228 _112229 : Type'} (f : _112228 -> _112226) (g : _112229 -> _112228) (x : _112229) : (term72 _112226 _112228 _112229 f g x) = (term73 _112226 _112228 _112229 f g x).
Proof. exact (MK_COMB (@lem4877063 _112226) (@lem4877062 _112226 _112228 _112229 f g x)). Qed.
Lemma lem4877065 {_112226 _112228 _112229 : Type'} (f : _112228 -> _112226) (g : _112229 -> _112228) (x : _112229) : (term69 _112226 _112228 _112229 f g x) = (term70 _112226 _112228 _112229 f g x).
Proof. exact (eq_refl (term69 _112226 _112228 _112229 f g x)). Qed.
Lemma lem4877066 {_112226 _112228 _112229 : Type'} (f : _112228 -> _112226) (g : _112229 -> _112228) (x : _112229) : ((term68 _112226 _112228 _112229 f g x) = (term69 _112226 _112228 _112229 f g x)) = ((term69 _112226 _112228 _112229 f g x) = (term70 _112226 _112228 _112229 f g x)).
Proof. exact (MK_COMB (@lem4877064 _112226 _112228 _112229 f g x) (@lem4877065 _112226 _112228 _112229 f g x)). Qed.
Lemma lem4877067 {_112226 _112228 _112229 : Type'} (f : _112228 -> _112226) (g : _112229 -> _112228) (x : _112229) : (term69 _112226 _112228 _112229 f g x) = (term70 _112226 _112228 _112229 f g x).
Proof. exact (EQ_MP (@lem4877066 _112226 _112228 _112229 f g x) (@lem4877058 _112226 _112228 _112229 f g x)). Qed.
Lemma lem4877068 {_112226 : Type'} (x : _112226) : (@eq _112226 x) = (@eq _112226 x).
Proof. exact (eq_refl (@eq _112226 x)). Qed.
Lemma lem4877069 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (x' : _112229) : (x = (term69 _112226 _112228 _112229 f g x')) = (x = (term70 _112226 _112228 _112229 f g x')).
Proof. exact (MK_COMB (@lem4877068 _112226 x) (@lem4877067 _112226 _112228 _112229 f g x')). Qed.
Lemma lem4877072 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4877073 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (x' : _112229) : (term74 _112226 _112228 _112229 x f g x') = (term75 _112226 _112228 _112229 x f g x').
Proof. exact (MK_COMB (@lem4877072) (@lem4877069 _112226 _112228 _112229 x f g x')). Qed.
Lemma lem4877075 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4877076 {_112229 : Type'} (P : _112229 -> Prop) (x : _112229) : (@IN _112229 x P) = (P x).
Proof. exact (@lem4877075 _112229 P x). Qed.
Lemma lem4877077 {_112229 : Type'} (s : _112229 -> Prop) (x : _112229) : (@IN _112229 x s) = (s x).
Proof. exact (@lem4877076 _112229 s x). Qed.
Lemma lem4877078 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (x' : _112229) : (term76 _112226 _112228 _112229 x f g x' s) = (term77 _112226 _112228 _112229 x f g s x').
Proof. exact (MK_COMB (@lem4877073 _112226 _112228 _112229 x f g x') (@lem4877077 _112229 s x')). Qed.
Lemma lem4877081 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term78 _112226 _112228 _112229 x f g s) = (term79 _112226 _112228 _112229 x f g s).
Proof. exact (fun_ext (fun x' : _112229 => @lem4877078 _112226 _112228 _112229 x f g s x')). Qed.
Lemma lem4877082 {_112229 : Type'} : (@ex _112229) = (@ex _112229).
Proof. exact (eq_refl (@ex _112229)). Qed.
Lemma lem4877083 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term65 _112226 _112228 _112229 x f g s) = (term80 _112226 _112228 _112229 x f g s).
Proof. exact (MK_COMB (@lem4877082 _112229) (@lem4877081 _112226 _112228 _112229 x f g s)). Qed.
Lemma lem4877088 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term64 _112226 _112228 _112229 x f g s) = (term80 _112226 _112228 _112229 x f g s).
Proof. exact (TRANS (@lem4877046 _112226 _112228 _112229 x f g s) (@lem4877083 _112226 _112228 _112229 x f g s)). Qed.
Lemma lem4877089 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : ((term21 _112226 _112228 _112229 x g s f) = (term64 _112226 _112228 _112229 x f g s)) = ((term62 _112226 _112228 _112229 g s x f) = (term80 _112226 _112228 _112229 x f g s)).
Proof. exact (MK_COMB (@lem4877042 _112226 _112228 _112229 g s x f) (@lem4877088 _112226 _112228 _112229 x f g s)). Qed.
Lemma lem4877092 {_112226 _112228 _112229 : Type'} (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term81 _112226 _112228 _112229 f g s) = (term82 _112226 _112228 _112229 f g s).
Proof. exact (fun_ext (fun x : _112226 => @lem4877089 _112226 _112228 _112229 x f g s)). Qed.
Lemma lem4877093 {_112226 : Type'} : (@all _112226) = (@all _112226).
Proof. exact (eq_refl (@all _112226)). Qed.
Lemma lem4877094 {_112226 _112228 _112229 : Type'} (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term10 _112226 _112228 _112229 f g s) = (term83 _112226 _112228 _112229 f g s).
Proof. exact (MK_COMB (@lem4877093 _112226) (@lem4877092 _112226 _112228 _112229 f g s)). Qed.
Lemma lem4877099 {_112226 _112228 _112229 : Type'} (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term83 _112226 _112228 _112229 f g s) = (term10 _112226 _112228 _112229 f g s).
Proof. exact (SYM (@lem4877094 _112226 _112228 _112229 f g s)). Qed.
Lemma lem4877101 (p : Prop) : p = (term84 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4877102 {_112226 _112228 _112229 : Type'} (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term83 _112226 _112228 _112229 f g s) = (term85 _112226 _112228 _112229 f g s).
Proof. exact (@lem4877101 (term83 _112226 _112228 _112229 f g s)). Qed.
Lemma lem4877103 {_112226 _112228 _112229 : Type'} (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term85 _112226 _112228 _112229 f g s) = (term83 _112226 _112228 _112229 f g s).
Proof. exact (SYM (@lem4877102 _112226 _112228 _112229 f g s)). Qed.
Lemma lem4877104 {_112226 _112228 _112229 : Type'} (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (h1 : term86 _112226 _112228 _112229 f g s) : term86 _112226 _112228 _112229 f g s.
Proof. exact (h1). Qed.
Lemma lem4877107 {_112226 _112228 _112229 : Type'} (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (h1 : term85 _112226 _112228 _112229 f g s) : term85 _112226 _112228 _112229 f g s.
Proof. exact (h1). Qed.
Lemma lem4877108 {_112226 _112228 _112229 : Type'} (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : term87 _112226 _112228 _112229 f g s.
Proof. exact (fun h0 : term85 _112226 _112228 _112229 f g s => @lem4877107 _112226 _112228 _112229 f g s h0). Qed.
Lemma lem4877109 {_112226 _112228 _112229 : Type'} (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (h1 : term87 _112226 _112228 _112229 f g s) : term87 _112226 _112228 _112229 f g s.
Proof. exact (h1). Qed.
Lemma lem4877110 {_112226 _112228 _112229 : Type'} (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (h1 : term85 _112226 _112228 _112229 f g s) : term85 _112226 _112228 _112229 f g s.
Proof. exact (h1). Qed.
Lemma lem4877111 {_112226 _112228 _112229 : Type'} (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (h1 : term85 _112226 _112228 _112229 f g s) (h2 : term87 _112226 _112228 _112229 f g s) : term85 _112226 _112228 _112229 f g s.
Proof. exact (@lem4877109 _112226 _112228 _112229 f g s h2 (@lem4877110 _112226 _112228 _112229 f g s h1)). Qed.
Lemma lem4877112 {_112226 _112228 _112229 : Type'} (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (h1 : term85 _112226 _112228 _112229 f g s) : term88 _112226 _112228 _112229 f g s.
Proof. exact (fun h0 : term87 _112226 _112228 _112229 f g s => @lem4877111 _112226 _112228 _112229 f g s h1 h0). Qed.
Lemma lem4877113 {_112226 _112228 _112229 : Type'} (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (h1 : term87 _112226 _112228 _112229 f g s) : term87 _112226 _112228 _112229 f g s.
Proof. exact (h1). Qed.
Lemma lem4877114 {_112226 _112228 _112229 : Type'} (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (h1 : term85 _112226 _112228 _112229 f g s) (h2 : term87 _112226 _112228 _112229 f g s) : term85 _112226 _112228 _112229 f g s.
Proof. exact (@lem4877112 _112226 _112228 _112229 f g s h1 (@lem4877113 _112226 _112228 _112229 f g s h2)). Qed.
Lemma lem4877115 {_112226 _112228 _112229 : Type'} (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (h1 : term87 _112226 _112228 _112229 f g s) : term87 _112226 _112228 _112229 f g s.
Proof. exact (fun h0 : term85 _112226 _112228 _112229 f g s => @lem4877114 _112226 _112228 _112229 f g s h0 h1). Qed.
Lemma lem4877116 {_112226 _112228 _112229 : Type'} (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : term89 _112226 _112228 _112229 f g s.
Proof. exact (fun h0 : term87 _112226 _112228 _112229 f g s => @lem4877115 _112226 _112228 _112229 f g s h0). Qed.
Lemma lem4877119 {_112226 _112228 _112229 : Type'} (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : term87 _112226 _112228 _112229 f g s.
Proof. exact (@lem4877116 _112226 _112228 _112229 f g s (@lem4877108 _112226 _112228 _112229 f g s)). Qed.
Lemma lem4877120 {_112226 _112228 _112229 : Type'} (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : term87 _112226 _112228 _112229 f g s.
Proof. exact (@lem4877119 _112226 _112228 _112229 f g s). Qed.
Lemma lem4877134 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4877135 {_112226 _112228 _112229 : Type'} (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term85 _112226 _112228 _112229 f g s) = (term90 _112226 _112228 _112229 f g s).
Proof. exact (@lem4877134 (term86 _112226 _112228 _112229 f g s)). Qed.
Lemma lem4877137 (t : Prop) : (term91 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4877138 {_112226 _112228 _112229 : Type'} (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term90 _112226 _112228 _112229 f g s) = (term83 _112226 _112228 _112229 f g s).
Proof. exact (@lem4877137 (term83 _112226 _112228 _112229 f g s)). Qed.
Lemma lem4877143 {_112226 _112228 _112229 : Type'} (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term85 _112226 _112228 _112229 f g s) = (term83 _112226 _112228 _112229 f g s).
Proof. exact (TRANS (@lem4877135 _112226 _112228 _112229 f g s) (@lem4877138 _112226 _112228 _112229 f g s)). Qed.
Lemma lem4877262 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) : (term92 _112226 _112228 _112229 g s) = (term93 _112226 _112228 _112229 g s).
Proof. exact (fun_ext (fun f : _112228 -> _112226 => @lem4877143 _112226 _112228 _112229 f g s)). Qed.
Lemma lem4877263 {_112226 _112228 : Type'} : (@all (_112228 -> _112226)) = (@all (_112228 -> _112226)).
Proof. exact (eq_refl (@all (_112228 -> _112226))). Qed.
Lemma lem4877264 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) : (term94 _112226 _112228 _112229 g s) = (term95 _112226 _112228 _112229 g s).
Proof. exact (MK_COMB (@lem4877263 _112226 _112228) (@lem4877262 _112226 _112228 _112229 g s)). Qed.
Lemma lem4877269 {_112226 _112228 _112229 : Type'} (s : _112229 -> Prop) : (term96 _112226 _112228 _112229 s) = (term97 _112226 _112228 _112229 s).
Proof. exact (fun_ext (fun g : _112229 -> _112228 => @lem4877264 _112226 _112228 _112229 g s)). Qed.
Lemma lem4877270 {_112228 _112229 : Type'} : (@all (_112229 -> _112228)) = (@all (_112229 -> _112228)).
Proof. exact (eq_refl (@all (_112229 -> _112228))). Qed.
Lemma lem4877271 {_112226 _112228 _112229 : Type'} (s : _112229 -> Prop) : (term98 _112226 _112228 _112229 s) = (term99 _112226 _112228 _112229 s).
Proof. exact (MK_COMB (@lem4877270 _112228 _112229) (@lem4877269 _112226 _112228 _112229 s)). Qed.
Lemma lem4877276 {_112226 _112228 _112229 : Type'} : (term100 _112226 _112228 _112229) = (term101 _112226 _112228 _112229).
Proof. exact (fun_ext (fun s : _112229 -> Prop => @lem4877271 _112226 _112228 _112229 s)). Qed.
Lemma lem4877277 {_112229 : Type'} : (@all (_112229 -> Prop)) = (@all (_112229 -> Prop)).
Proof. exact (eq_refl (@all (_112229 -> Prop))). Qed.
Lemma lem4877286 {_112226 _112228 _112229 : Type'} : (term102 _112226 _112228 _112229) = (term103 _112226 _112228 _112229).
Proof. exact (MK_COMB (@lem4877277 _112229) (@lem4877276 _112226 _112228 _112229)). Qed.
Lemma lem4877291 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (x' : _112229) : (term77 _112226 _112228 _112229 x f g s x') = (term77 _112226 _112228 _112229 x f g s x').
Proof. exact (eq_refl (term77 _112226 _112228 _112229 x f g s x')). Qed.
Lemma lem4877292 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term79 _112226 _112228 _112229 x f g s) = (term79 _112226 _112228 _112229 x f g s).
Proof. exact (fun_ext (fun x' : _112229 => @lem4877291 _112226 _112228 _112229 x f g s x')). Qed.
Lemma lem4877293 {_112229 : Type'} : (@ex _112229) = (@ex _112229).
Proof. exact (eq_refl (@ex _112229)). Qed.
Lemma lem4877294 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term80 _112226 _112228 _112229 x f g s) = (term80 _112226 _112228 _112229 x f g s).
Proof. exact (MK_COMB (@lem4877293 _112229) (@lem4877292 _112226 _112228 _112229 x f g s)). Qed.
Lemma lem4877295 {_112226 _112228 : Type'} (x : _112226) (f : _112228 -> _112226) (y : _112228) : (x = (f y)) = (x = (f y)).
Proof. exact (eq_refl (x = (f y))). Qed.
Lemma lem4877300 {_112228 _112229 : Type'} (y : _112228) (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112229) : (term42 _112228 _112229 y g s x) = (term42 _112228 _112229 y g s x).
Proof. exact (eq_refl (term42 _112228 _112229 y g s x)). Qed.
Lemma lem4877301 {_112228 _112229 : Type'} (y : _112228) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term44 _112228 _112229 y g s) = (term44 _112228 _112229 y g s).
Proof. exact (fun_ext (fun x : _112229 => @lem4877300 _112228 _112229 y g s x)). Qed.
Lemma lem4877302 {_112229 : Type'} : (@ex _112229) = (@ex _112229).
Proof. exact (eq_refl (@ex _112229)). Qed.
Lemma lem4877303 {_112228 _112229 : Type'} (y : _112228) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term45 _112228 _112229 y g s) = (term45 _112228 _112229 y g s).
Proof. exact (MK_COMB (@lem4877302 _112229) (@lem4877301 _112228 _112229 y g s)). Qed.
Lemma lem4877304 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4877305 {_112228 _112229 : Type'} (y : _112228) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term47 _112228 _112229 y g s) = (term47 _112228 _112229 y g s).
Proof. exact (MK_COMB (@lem4877304) (@lem4877303 _112228 _112229 y g s)). Qed.
Lemma lem4877306 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (f : _112228 -> _112226) (y : _112228) : (term59 _112226 _112228 _112229 g s x f y) = (term59 _112226 _112228 _112229 g s x f y).
Proof. exact (MK_COMB (@lem4877305 _112228 _112229 y g s) (@lem4877295 _112226 _112228 x f y)). Qed.
Lemma lem4877307 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (f : _112228 -> _112226) : (term61 _112226 _112228 _112229 g s x f) = (term61 _112226 _112228 _112229 g s x f).
Proof. exact (fun_ext (fun y : _112228 => @lem4877306 _112226 _112228 _112229 g s x f y)). Qed.
Lemma lem4877308 {_112228 : Type'} : (@ex _112228) = (@ex _112228).
Proof. exact (eq_refl (@ex _112228)). Qed.
Lemma lem4877309 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (f : _112228 -> _112226) : (term62 _112226 _112228 _112229 g s x f) = (term62 _112226 _112228 _112229 g s x f).
Proof. exact (MK_COMB (@lem4877308 _112228) (@lem4877307 _112226 _112228 _112229 g s x f)). Qed.
Lemma lem4877310 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4877311 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (f : _112228 -> _112226) : (term63 _112226 _112228 _112229 g s x f) = (term63 _112226 _112228 _112229 g s x f).
Proof. exact (MK_COMB (@lem4877310) (@lem4877309 _112226 _112228 _112229 g s x f)). Qed.
Lemma lem4877312 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : ((term62 _112226 _112228 _112229 g s x f) = (term80 _112226 _112228 _112229 x f g s)) = ((term62 _112226 _112228 _112229 g s x f) = (term80 _112226 _112228 _112229 x f g s)).
Proof. exact (MK_COMB (@lem4877311 _112226 _112228 _112229 g s x f) (@lem4877294 _112226 _112228 _112229 x f g s)). Qed.
Lemma lem4877313 {_112226 _112228 _112229 : Type'} (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term82 _112226 _112228 _112229 f g s) = (term82 _112226 _112228 _112229 f g s).
Proof. exact (fun_ext (fun x : _112226 => @lem4877312 _112226 _112228 _112229 x f g s)). Qed.
Lemma lem4877314 {_112226 : Type'} : (@all _112226) = (@all _112226).
Proof. exact (eq_refl (@all _112226)). Qed.
Lemma lem4877315 {_112226 _112228 _112229 : Type'} (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term83 _112226 _112228 _112229 f g s) = (term83 _112226 _112228 _112229 f g s).
Proof. exact (MK_COMB (@lem4877314 _112226) (@lem4877313 _112226 _112228 _112229 f g s)). Qed.
Lemma lem4877316 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) : (term93 _112226 _112228 _112229 g s) = (term93 _112226 _112228 _112229 g s).
Proof. exact (fun_ext (fun f : _112228 -> _112226 => @lem4877315 _112226 _112228 _112229 f g s)). Qed.
Lemma lem4877317 {_112226 _112228 : Type'} : (@all (_112228 -> _112226)) = (@all (_112228 -> _112226)).
Proof. exact (eq_refl (@all (_112228 -> _112226))). Qed.
Lemma lem4877318 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) : (term95 _112226 _112228 _112229 g s) = (term95 _112226 _112228 _112229 g s).
Proof. exact (MK_COMB (@lem4877317 _112226 _112228) (@lem4877316 _112226 _112228 _112229 g s)). Qed.
Lemma lem4877319 {_112226 _112228 _112229 : Type'} (s : _112229 -> Prop) : (term97 _112226 _112228 _112229 s) = (term97 _112226 _112228 _112229 s).
Proof. exact (fun_ext (fun g : _112229 -> _112228 => @lem4877318 _112226 _112228 _112229 g s)). Qed.
Lemma lem4877320 {_112228 _112229 : Type'} : (@all (_112229 -> _112228)) = (@all (_112229 -> _112228)).
Proof. exact (eq_refl (@all (_112229 -> _112228))). Qed.
Lemma lem4877321 {_112226 _112228 _112229 : Type'} (s : _112229 -> Prop) : (term99 _112226 _112228 _112229 s) = (term99 _112226 _112228 _112229 s).
Proof. exact (MK_COMB (@lem4877320 _112228 _112229) (@lem4877319 _112226 _112228 _112229 s)). Qed.
Lemma lem4877322 {_112226 _112228 _112229 : Type'} : (term101 _112226 _112228 _112229) = (term101 _112226 _112228 _112229).
Proof. exact (fun_ext (fun s : _112229 -> Prop => @lem4877321 _112226 _112228 _112229 s)). Qed.
Lemma lem4877323 {_112229 : Type'} : (@all (_112229 -> Prop)) = (@all (_112229 -> Prop)).
Proof. exact (eq_refl (@all (_112229 -> Prop))). Qed.
Lemma lem4877324 {_112226 _112228 _112229 : Type'} : (term103 _112226 _112228 _112229) = (term103 _112226 _112228 _112229).
Proof. exact (MK_COMB (@lem4877323 _112229) (@lem4877322 _112226 _112228 _112229)). Qed.
Lemma lem4877375 {_112226 _112228 _112229 : Type'} : (term102 _112226 _112228 _112229) = (term103 _112226 _112228 _112229).
Proof. exact (TRANS (@lem4877286 _112226 _112228 _112229) (@lem4877324 _112226 _112228 _112229)). Qed.
Lemma lem4877376 {_112226 _112228 _112229 : Type'} : (term103 _112226 _112228 _112229) = (term102 _112226 _112228 _112229).
Proof. exact (SYM (@lem4877375 _112226 _112228 _112229)). Qed.
Lemma lem4877378 (p : Prop) : p = (term84 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4877379 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : ((term62 _112226 _112228 _112229 g s x f) = (term80 _112226 _112228 _112229 x f g s)) = (term104 _112226 _112228 _112229 x f g s).
Proof. exact (@lem4877378 ((term62 _112226 _112228 _112229 g s x f) = (term80 _112226 _112228 _112229 x f g s))). Qed.
Lemma lem4877380 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term104 _112226 _112228 _112229 x f g s) = ((term62 _112226 _112228 _112229 g s x f) = (term80 _112226 _112228 _112229 x f g s)).
Proof. exact (SYM (@lem4877379 _112226 _112228 _112229 x f g s)). Qed.
Lemma lem4877381 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (h1 : term105 _112226 _112228 _112229 x f g s) : term105 _112226 _112228 _112229 x f g s.
Proof. exact (h1). Qed.
Lemma lem4877390 {_112228 _112229 : Type'} (y : _112228) (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112229) : (term106 _112228 _112229 y g s x) = (term107 _112228 _112229 y g s x).
Proof. exact (@lem17045 (y = (g x)) (s x)). Qed.
Lemma lem4877393 {_112228 _112229 : Type'} (y : _112228) (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112229) : (term42 _112228 _112229 y g s x) = (term42 _112228 _112229 y g s x).
Proof. exact (eq_refl (term42 _112228 _112229 y g s x)). Qed.
Lemma lem4877394 {_112229 : Type'} (P : _112229 -> Prop) : (term108 _112229 P) = (term109 _112229 P).
Proof. exact (@lem18394 _112229 P). Qed.
Lemma lem4877395 {_112228 _112229 : Type'} (y : _112228) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term110 _112228 _112229 y g s) = (term111 _112228 _112229 y g s).
Proof. exact (@lem4877394 _112229 (term44 _112228 _112229 y g s)). Qed.
Lemma lem4877396 {_112228 _112229 : Type'} (y : _112228) (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112229) : (term112 _112228 _112229 y g s x) = (term42 _112228 _112229 y g s x).
Proof. exact (eq_refl (term112 _112228 _112229 y g s x)). Qed.
Lemma lem4877397 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4877398 {_112228 _112229 : Type'} (y : _112228) (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112229) : (term113 _112228 _112229 y g s x) = (term106 _112228 _112229 y g s x).
Proof. exact (MK_COMB (@lem4877397) (@lem4877396 _112228 _112229 y g s x)). Qed.
Lemma lem4877399 {_112228 _112229 : Type'} (y : _112228) (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112229) : (term113 _112228 _112229 y g s x) = (term107 _112228 _112229 y g s x).
Proof. exact (TRANS (@lem4877398 _112228 _112229 y g s x) (@lem4877390 _112228 _112229 y g s x)). Qed.
Lemma lem4877400 {_112228 _112229 : Type'} (y : _112228) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term114 _112228 _112229 y g s) = (term115 _112228 _112229 y g s).
Proof. exact (fun_ext (fun x : _112229 => @lem4877399 _112228 _112229 y g s x)). Qed.
Lemma lem4877401 {_112229 : Type'} : (@all _112229) = (@all _112229).
Proof. exact (eq_refl (@all _112229)). Qed.
Lemma lem4877402 {_112228 _112229 : Type'} (y : _112228) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term111 _112228 _112229 y g s) = (term116 _112228 _112229 y g s).
Proof. exact (MK_COMB (@lem4877401 _112229) (@lem4877400 _112228 _112229 y g s)). Qed.
Lemma lem4877403 {_112228 _112229 : Type'} (y : _112228) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term110 _112228 _112229 y g s) = (term116 _112228 _112229 y g s).
Proof. exact (TRANS (@lem4877395 _112228 _112229 y g s) (@lem4877402 _112228 _112229 y g s)). Qed.
Lemma lem4877404 {_112228 _112229 : Type'} (y : _112228) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term44 _112228 _112229 y g s) = (term44 _112228 _112229 y g s).
Proof. exact (fun_ext (fun x : _112229 => @lem4877393 _112228 _112229 y g s x)). Qed.
Lemma lem4877405 {_112229 : Type'} : (@ex _112229) = (@ex _112229).
Proof. exact (eq_refl (@ex _112229)). Qed.
Lemma lem4877406 {_112228 _112229 : Type'} (y : _112228) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term45 _112228 _112229 y g s) = (term45 _112228 _112229 y g s).
Proof. exact (MK_COMB (@lem4877405 _112229) (@lem4877404 _112228 _112229 y g s)). Qed.
Lemma lem4877407 {_112226 _112228 : Type'} (x : _112226) (f : _112228 -> _112226) (y : _112228) : (term117 _112226 _112228 x f y) = (term117 _112226 _112228 x f y).
Proof. exact (eq_refl (term117 _112226 _112228 x f y)). Qed.
Lemma lem4877408 {_112226 _112228 : Type'} (x : _112226) (f : _112228 -> _112226) (y : _112228) : (x = (f y)) = (x = (f y)).
Proof. exact (eq_refl (x = (f y))). Qed.
Lemma lem4877409 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4877410 {_112228 _112229 : Type'} (y : _112228) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term118 _112228 _112229 y g s) = (term119 _112228 _112229 y g s).
Proof. exact (MK_COMB (@lem4877409) (@lem4877403 _112228 _112229 y g s)). Qed.
Lemma lem4877411 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (f : _112228 -> _112226) (y : _112228) : (term120 _112226 _112228 _112229 g s x f y) = (term121 _112226 _112228 _112229 g s x f y).
Proof. exact (MK_COMB (@lem4877410 _112228 _112229 y g s) (@lem4877407 _112226 _112228 x f y)). Qed.
Lemma lem4877412 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (f : _112228 -> _112226) (y : _112228) : (term122 _112226 _112228 _112229 g s x f y) = (term120 _112226 _112228 _112229 g s x f y).
Proof. exact (@lem17045 (term45 _112228 _112229 y g s) (x = (f y))). Qed.
Lemma lem4877413 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (f : _112228 -> _112226) (y : _112228) : (term122 _112226 _112228 _112229 g s x f y) = (term121 _112226 _112228 _112229 g s x f y).
Proof. exact (TRANS (@lem4877412 _112226 _112228 _112229 g s x f y) (@lem4877411 _112226 _112228 _112229 g s x f y)). Qed.
Lemma lem4877414 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4877415 {_112228 _112229 : Type'} (y : _112228) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term47 _112228 _112229 y g s) = (term47 _112228 _112229 y g s).
Proof. exact (MK_COMB (@lem4877414) (@lem4877406 _112228 _112229 y g s)). Qed.
Lemma lem4877416 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (f : _112228 -> _112226) (y : _112228) : (term59 _112226 _112228 _112229 g s x f y) = (term59 _112226 _112228 _112229 g s x f y).
Proof. exact (MK_COMB (@lem4877415 _112228 _112229 y g s) (@lem4877408 _112226 _112228 x f y)). Qed.
Lemma lem4877417 {_112228 : Type'} (P : _112228 -> Prop) : (term108 _112228 P) = (term109 _112228 P).
Proof. exact (@lem18394 _112228 P). Qed.
Lemma lem4877418 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (f : _112228 -> _112226) : (term123 _112226 _112228 _112229 g s x f) = (term124 _112226 _112228 _112229 g s x f).
Proof. exact (@lem4877417 _112228 (term61 _112226 _112228 _112229 g s x f)). Qed.
Lemma lem4877419 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (f : _112228 -> _112226) (y : _112228) : (term125 _112226 _112228 _112229 g s x f y) = (term59 _112226 _112228 _112229 g s x f y).
Proof. exact (eq_refl (term125 _112226 _112228 _112229 g s x f y)). Qed.
Lemma lem4877420 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4877421 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (f : _112228 -> _112226) (y : _112228) : (term126 _112226 _112228 _112229 g s x f y) = (term122 _112226 _112228 _112229 g s x f y).
Proof. exact (MK_COMB (@lem4877420) (@lem4877419 _112226 _112228 _112229 g s x f y)). Qed.
Lemma lem4877422 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (f : _112228 -> _112226) (y : _112228) : (term126 _112226 _112228 _112229 g s x f y) = (term121 _112226 _112228 _112229 g s x f y).
Proof. exact (TRANS (@lem4877421 _112226 _112228 _112229 g s x f y) (@lem4877413 _112226 _112228 _112229 g s x f y)). Qed.
Lemma lem4877423 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (f : _112228 -> _112226) : (term127 _112226 _112228 _112229 g s x f) = (term128 _112226 _112228 _112229 g s x f).
Proof. exact (fun_ext (fun y : _112228 => @lem4877422 _112226 _112228 _112229 g s x f y)). Qed.
Lemma lem4877424 {_112228 : Type'} : (@all _112228) = (@all _112228).
Proof. exact (eq_refl (@all _112228)). Qed.
Lemma lem4877425 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (f : _112228 -> _112226) : (term124 _112226 _112228 _112229 g s x f) = (term129 _112226 _112228 _112229 g s x f).
Proof. exact (MK_COMB (@lem4877424 _112228) (@lem4877423 _112226 _112228 _112229 g s x f)). Qed.
Lemma lem4877426 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (f : _112228 -> _112226) : (term123 _112226 _112228 _112229 g s x f) = (term129 _112226 _112228 _112229 g s x f).
Proof. exact (TRANS (@lem4877418 _112226 _112228 _112229 g s x f) (@lem4877425 _112226 _112228 _112229 g s x f)). Qed.
Lemma lem4877427 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (f : _112228 -> _112226) : (term61 _112226 _112228 _112229 g s x f) = (term61 _112226 _112228 _112229 g s x f).
Proof. exact (fun_ext (fun y : _112228 => @lem4877416 _112226 _112228 _112229 g s x f y)). Qed.
Lemma lem4877428 {_112228 : Type'} : (@ex _112228) = (@ex _112228).
Proof. exact (eq_refl (@ex _112228)). Qed.
Lemma lem4877429 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (f : _112228 -> _112226) : (term62 _112226 _112228 _112229 g s x f) = (term62 _112226 _112228 _112229 g s x f).
Proof. exact (MK_COMB (@lem4877428 _112228) (@lem4877427 _112226 _112228 _112229 g s x f)). Qed.
Lemma lem4877438 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (x' : _112229) : (term130 _112226 _112228 _112229 x f g s x') = (term131 _112226 _112228 _112229 x f g s x').
Proof. exact (@lem17045 (x = (term70 _112226 _112228 _112229 f g x')) (s x')). Qed.
Lemma lem4877441 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (x' : _112229) : (term77 _112226 _112228 _112229 x f g s x') = (term77 _112226 _112228 _112229 x f g s x').
Proof. exact (eq_refl (term77 _112226 _112228 _112229 x f g s x')). Qed.
Lemma lem4877442 {_112229 : Type'} (P : _112229 -> Prop) : (term108 _112229 P) = (term109 _112229 P).
Proof. exact (@lem18394 _112229 P). Qed.
Lemma lem4877443 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term132 _112226 _112228 _112229 x f g s) = (term133 _112226 _112228 _112229 x f g s).
Proof. exact (@lem4877442 _112229 (term79 _112226 _112228 _112229 x f g s)). Qed.
Lemma lem4877444 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (x' : _112229) : (term134 _112226 _112228 _112229 x f g s x') = (term77 _112226 _112228 _112229 x f g s x').
Proof. exact (eq_refl (term134 _112226 _112228 _112229 x f g s x')). Qed.
Lemma lem4877445 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4877446 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (x' : _112229) : (term135 _112226 _112228 _112229 x f g s x') = (term130 _112226 _112228 _112229 x f g s x').
Proof. exact (MK_COMB (@lem4877445) (@lem4877444 _112226 _112228 _112229 x f g s x')). Qed.
Lemma lem4877447 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (x' : _112229) : (term135 _112226 _112228 _112229 x f g s x') = (term131 _112226 _112228 _112229 x f g s x').
Proof. exact (TRANS (@lem4877446 _112226 _112228 _112229 x f g s x') (@lem4877438 _112226 _112228 _112229 x f g s x')). Qed.
Lemma lem4877448 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term136 _112226 _112228 _112229 x f g s) = (term137 _112226 _112228 _112229 x f g s).
Proof. exact (fun_ext (fun x' : _112229 => @lem4877447 _112226 _112228 _112229 x f g s x')). Qed.
Lemma lem4877449 {_112229 : Type'} : (@all _112229) = (@all _112229).
Proof. exact (eq_refl (@all _112229)). Qed.
Lemma lem4877450 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term133 _112226 _112228 _112229 x f g s) = (term138 _112226 _112228 _112229 x f g s).
Proof. exact (MK_COMB (@lem4877449 _112229) (@lem4877448 _112226 _112228 _112229 x f g s)). Qed.
Lemma lem4877451 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term132 _112226 _112228 _112229 x f g s) = (term138 _112226 _112228 _112229 x f g s).
Proof. exact (TRANS (@lem4877443 _112226 _112228 _112229 x f g s) (@lem4877450 _112226 _112228 _112229 x f g s)). Qed.
Lemma lem4877452 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term79 _112226 _112228 _112229 x f g s) = (term79 _112226 _112228 _112229 x f g s).
Proof. exact (fun_ext (fun x' : _112229 => @lem4877441 _112226 _112228 _112229 x f g s x')). Qed.
Lemma lem4877453 {_112229 : Type'} : (@ex _112229) = (@ex _112229).
Proof. exact (eq_refl (@ex _112229)). Qed.
Lemma lem4877454 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term80 _112226 _112228 _112229 x f g s) = (term80 _112226 _112228 _112229 x f g s).
Proof. exact (MK_COMB (@lem4877453 _112229) (@lem4877452 _112226 _112228 _112229 x f g s)). Qed.
Lemma lem4877455 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4877456 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (f : _112228 -> _112226) : (term139 _112226 _112228 _112229 g s x f) = (term140 _112226 _112228 _112229 g s x f).
Proof. exact (MK_COMB (@lem4877455) (@lem4877426 _112226 _112228 _112229 g s x f)). Qed.
Lemma lem4877457 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term141 _112226 _112228 _112229 x f g s) = (term142 _112226 _112228 _112229 x f g s).
Proof. exact (MK_COMB (@lem4877456 _112226 _112228 _112229 g s x f) (@lem4877454 _112226 _112228 _112229 x f g s)). Qed.
Lemma lem4877458 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4877459 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (f : _112228 -> _112226) : (term143 _112226 _112228 _112229 g s x f) = (term143 _112226 _112228 _112229 g s x f).
Proof. exact (MK_COMB (@lem4877458) (@lem4877429 _112226 _112228 _112229 g s x f)). Qed.
Lemma lem4877460 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term144 _112226 _112228 _112229 x f g s) = (term145 _112226 _112228 _112229 x f g s).
Proof. exact (MK_COMB (@lem4877459 _112226 _112228 _112229 g s x f) (@lem4877451 _112226 _112228 _112229 x f g s)). Qed.
Lemma lem4877461 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4877462 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term146 _112226 _112228 _112229 x f g s) = (term147 _112226 _112228 _112229 x f g s).
Proof. exact (MK_COMB (@lem4877461) (@lem4877460 _112226 _112228 _112229 x f g s)). Qed.
Lemma lem4877463 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term148 _112226 _112228 _112229 x f g s) = (term149 _112226 _112228 _112229 x f g s).
Proof. exact (MK_COMB (@lem4877462 _112226 _112228 _112229 x f g s) (@lem4877457 _112226 _112228 _112229 x f g s)). Qed.
Lemma lem4877464 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term105 _112226 _112228 _112229 x f g s) = (term148 _112226 _112228 _112229 x f g s).
Proof. exact (@lem17646 (term62 _112226 _112228 _112229 g s x f) (term80 _112226 _112228 _112229 x f g s)). Qed.
Lemma lem4877465 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term105 _112226 _112228 _112229 x f g s) = (term149 _112226 _112228 _112229 x f g s).
Proof. exact (TRANS (@lem4877464 _112226 _112228 _112229 x f g s) (@lem4877463 _112226 _112228 _112229 x f g s)). Qed.
Lemma lem4877724 {A : Type'} (P : A -> Prop) (Q : Prop) : (term150 A P Q) = (term151 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4877725 {_112229 : Type'} (P : _112229 -> Prop) (Q : Prop) : (term150 _112229 P Q) = (term151 _112229 P Q).
Proof. exact (@lem4877724 _112229 P Q). Qed.
Lemma lem4877726 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (f : _112228 -> _112226) (y : _112228) : (term152 _112226 _112228 _112229 g s x f y) = (term153 _112226 _112228 _112229 g s x f y).
Proof. exact (@lem4877725 _112229 (term44 _112228 _112229 y g s) (x = (f y))). Qed.
Lemma lem4877727 {_112228 _112229 : Type'} (y : _112228) (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112229) : (term112 _112228 _112229 y g s x) = (term42 _112228 _112229 y g s x).
Proof. exact (eq_refl (term112 _112228 _112229 y g s x)). Qed.
Lemma lem4877728 {_112228 _112229 : Type'} (y : _112228) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term154 _112228 _112229 y g s) = (term44 _112228 _112229 y g s).
Proof. exact (fun_ext (fun x : _112229 => @lem4877727 _112228 _112229 y g s x)). Qed.
Lemma lem4877729 {_112229 : Type'} : (@ex _112229) = (@ex _112229).
Proof. exact (eq_refl (@ex _112229)). Qed.
Lemma lem4877730 {_112228 _112229 : Type'} (y : _112228) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term155 _112228 _112229 y g s) = (term45 _112228 _112229 y g s).
Proof. exact (MK_COMB (@lem4877729 _112229) (@lem4877728 _112228 _112229 y g s)). Qed.
Lemma lem4877731 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4877732 {_112228 _112229 : Type'} (y : _112228) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term156 _112228 _112229 y g s) = (term47 _112228 _112229 y g s).
Proof. exact (MK_COMB (@lem4877731) (@lem4877730 _112228 _112229 y g s)). Qed.
Lemma lem4877733 {_112226 _112228 : Type'} (x : _112226) (f : _112228 -> _112226) (y : _112228) : (x = (f y)) = (x = (f y)).
Proof. exact (eq_refl (x = (f y))). Qed.
Lemma lem4877734 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (f : _112228 -> _112226) (y : _112228) : (term152 _112226 _112228 _112229 g s x f y) = (term59 _112226 _112228 _112229 g s x f y).
Proof. exact (MK_COMB (@lem4877732 _112228 _112229 y g s) (@lem4877733 _112226 _112228 x f y)). Qed.
Lemma lem4877735 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4877736 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (f : _112228 -> _112226) (y : _112228) : (term157 _112226 _112228 _112229 g s x f y) = (term158 _112226 _112228 _112229 g s x f y).
Proof. exact (MK_COMB (@lem4877735) (@lem4877734 _112226 _112228 _112229 g s x f y)). Qed.
Lemma lem4877737 {_112228 _112229 : Type'} (y : _112228) (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112229) : (term112 _112228 _112229 y g s x) = (term42 _112228 _112229 y g s x).
Proof. exact (eq_refl (term112 _112228 _112229 y g s x)). Qed.
Lemma lem4877738 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4877739 {_112228 _112229 : Type'} (y : _112228) (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112229) : (term159 _112228 _112229 y g s x) = (term160 _112228 _112229 y g s x).
Proof. exact (MK_COMB (@lem4877738) (@lem4877737 _112228 _112229 y g s x)). Qed.
Lemma lem4877740 {_112226 _112228 : Type'} (x : _112226) (f : _112228 -> _112226) (y : _112228) : (x = (f y)) = (x = (f y)).
Proof. exact (eq_refl (x = (f y))). Qed.
Lemma lem4877741 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112229) (x' : _112226) (f : _112228 -> _112226) (y : _112228) : (term161 _112226 _112228 _112229 g s x x' f y) = (term162 _112226 _112228 _112229 g s x x' f y).
Proof. exact (MK_COMB (@lem4877739 _112228 _112229 y g s x) (@lem4877740 _112226 _112228 x' f y)). Qed.
Lemma lem4877742 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (f : _112228 -> _112226) (y : _112228) : (term163 _112226 _112228 _112229 g s x f y) = (term164 _112226 _112228 _112229 g s x f y).
Proof. exact (fun_ext (fun x' : _112229 => @lem4877741 _112226 _112228 _112229 g s x' x f y)). Qed.
Lemma lem4877743 {_112229 : Type'} : (@ex _112229) = (@ex _112229).
Proof. exact (eq_refl (@ex _112229)). Qed.
Lemma lem4877744 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (f : _112228 -> _112226) (y : _112228) : (term153 _112226 _112228 _112229 g s x f y) = (term165 _112226 _112228 _112229 g s x f y).
Proof. exact (MK_COMB (@lem4877743 _112229) (@lem4877742 _112226 _112228 _112229 g s x f y)). Qed.
Lemma lem4877745 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (f : _112228 -> _112226) (y : _112228) : ((term152 _112226 _112228 _112229 g s x f y) = (term153 _112226 _112228 _112229 g s x f y)) = ((term59 _112226 _112228 _112229 g s x f y) = (term165 _112226 _112228 _112229 g s x f y)).
Proof. exact (MK_COMB (@lem4877736 _112226 _112228 _112229 g s x f y) (@lem4877744 _112226 _112228 _112229 g s x f y)). Qed.
Lemma lem4877746 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (f : _112228 -> _112226) (y : _112228) : (term59 _112226 _112228 _112229 g s x f y) = (term165 _112226 _112228 _112229 g s x f y).
Proof. exact (EQ_MP (@lem4877745 _112226 _112228 _112229 g s x f y) (@lem4877726 _112226 _112228 _112229 g s x f y)). Qed.
Lemma lem4877747 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (f : _112228 -> _112226) : (term61 _112226 _112228 _112229 g s x f) = (term166 _112226 _112228 _112229 g s x f).
Proof. exact (fun_ext (fun y : _112228 => @lem4877746 _112226 _112228 _112229 g s x f y)). Qed.
Lemma lem4877748 {_112228 : Type'} : (@ex _112228) = (@ex _112228).
Proof. exact (eq_refl (@ex _112228)). Qed.
Lemma lem4877749 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (f : _112228 -> _112226) : (term62 _112226 _112228 _112229 g s x f) = (term167 _112226 _112228 _112229 g s x f).
Proof. exact (MK_COMB (@lem4877748 _112228) (@lem4877747 _112226 _112228 _112229 g s x f)). Qed.
Lemma lem4877750 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4877751 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (f : _112228 -> _112226) : (term143 _112226 _112228 _112229 g s x f) = (term168 _112226 _112228 _112229 g s x f).
Proof. exact (MK_COMB (@lem4877750) (@lem4877749 _112226 _112228 _112229 g s x f)). Qed.
Lemma lem4877752 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term138 _112226 _112228 _112229 x f g s) = (term138 _112226 _112228 _112229 x f g s).
Proof. exact (eq_refl (term138 _112226 _112228 _112229 x f g s)). Qed.
Lemma lem4877753 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term145 _112226 _112228 _112229 x f g s) = (term169 _112226 _112228 _112229 x f g s).
Proof. exact (MK_COMB (@lem4877751 _112226 _112228 _112229 g s x f) (@lem4877752 _112226 _112228 _112229 x f g s)). Qed.
Lemma lem4877755 {A : Type'} (P : A -> Prop) (Q : Prop) : (term150 A P Q) = (term151 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4877756 {_112228 : Type'} (P : _112228 -> Prop) (Q : Prop) : (term150 _112228 P Q) = (term151 _112228 P Q).
Proof. exact (@lem4877755 _112228 P Q). Qed.
Lemma lem4877757 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term170 _112226 _112228 _112229 x f g s) = (term171 _112226 _112228 _112229 x f g s).
Proof. exact (@lem4877756 _112228 (term166 _112226 _112228 _112229 g s x f) (term138 _112226 _112228 _112229 x f g s)). Qed.
Lemma lem4877758 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (f : _112228 -> _112226) (y : _112228) : (term172 _112226 _112228 _112229 g s x f y) = (term165 _112226 _112228 _112229 g s x f y).
Proof. exact (eq_refl (term172 _112226 _112228 _112229 g s x f y)). Qed.
Lemma lem4877759 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (f : _112228 -> _112226) : (term173 _112226 _112228 _112229 g s x f) = (term166 _112226 _112228 _112229 g s x f).
Proof. exact (fun_ext (fun y : _112228 => @lem4877758 _112226 _112228 _112229 g s x f y)). Qed.
Lemma lem4877760 {_112228 : Type'} : (@ex _112228) = (@ex _112228).
Proof. exact (eq_refl (@ex _112228)). Qed.
Lemma lem4877761 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (f : _112228 -> _112226) : (term174 _112226 _112228 _112229 g s x f) = (term167 _112226 _112228 _112229 g s x f).
Proof. exact (MK_COMB (@lem4877760 _112228) (@lem4877759 _112226 _112228 _112229 g s x f)). Qed.
Lemma lem4877762 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4877763 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (f : _112228 -> _112226) : (term175 _112226 _112228 _112229 g s x f) = (term168 _112226 _112228 _112229 g s x f).
Proof. exact (MK_COMB (@lem4877762) (@lem4877761 _112226 _112228 _112229 g s x f)). Qed.
Lemma lem4877764 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term138 _112226 _112228 _112229 x f g s) = (term138 _112226 _112228 _112229 x f g s).
Proof. exact (eq_refl (term138 _112226 _112228 _112229 x f g s)). Qed.
Lemma lem4877765 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term170 _112226 _112228 _112229 x f g s) = (term169 _112226 _112228 _112229 x f g s).
Proof. exact (MK_COMB (@lem4877763 _112226 _112228 _112229 g s x f) (@lem4877764 _112226 _112228 _112229 x f g s)). Qed.
Lemma lem4877766 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4877767 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term176 _112226 _112228 _112229 x f g s) = (term177 _112226 _112228 _112229 x f g s).
Proof. exact (MK_COMB (@lem4877766) (@lem4877765 _112226 _112228 _112229 x f g s)). Qed.
Lemma lem4877768 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (f : _112228 -> _112226) (y : _112228) : (term172 _112226 _112228 _112229 g s x f y) = (term165 _112226 _112228 _112229 g s x f y).
Proof. exact (eq_refl (term172 _112226 _112228 _112229 g s x f y)). Qed.
Lemma lem4877769 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4877770 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (f : _112228 -> _112226) (y : _112228) : (term178 _112226 _112228 _112229 g s x f y) = (term179 _112226 _112228 _112229 g s x f y).
Proof. exact (MK_COMB (@lem4877769) (@lem4877768 _112226 _112228 _112229 g s x f y)). Qed.
Lemma lem4877771 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term138 _112226 _112228 _112229 x f g s) = (term138 _112226 _112228 _112229 x f g s).
Proof. exact (eq_refl (term138 _112226 _112228 _112229 x f g s)). Qed.
Lemma lem4877772 {_112226 _112228 _112229 : Type'} (y : _112228) (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term180 _112226 _112228 _112229 y x f g s) = (term181 _112226 _112228 _112229 y x f g s).
Proof. exact (MK_COMB (@lem4877770 _112226 _112228 _112229 g s x f y) (@lem4877771 _112226 _112228 _112229 x f g s)). Qed.
Lemma lem4877773 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term182 _112226 _112228 _112229 x f g s) = (term183 _112226 _112228 _112229 x f g s).
Proof. exact (fun_ext (fun y : _112228 => @lem4877772 _112226 _112228 _112229 y x f g s)). Qed.
Lemma lem4877774 {_112228 : Type'} : (@ex _112228) = (@ex _112228).
Proof. exact (eq_refl (@ex _112228)). Qed.
Lemma lem4877775 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term171 _112226 _112228 _112229 x f g s) = (term184 _112226 _112228 _112229 x f g s).
Proof. exact (MK_COMB (@lem4877774 _112228) (@lem4877773 _112226 _112228 _112229 x f g s)). Qed.
Lemma lem4877776 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : ((term170 _112226 _112228 _112229 x f g s) = (term171 _112226 _112228 _112229 x f g s)) = ((term169 _112226 _112228 _112229 x f g s) = (term184 _112226 _112228 _112229 x f g s)).
Proof. exact (MK_COMB (@lem4877767 _112226 _112228 _112229 x f g s) (@lem4877775 _112226 _112228 _112229 x f g s)). Qed.
Lemma lem4877777 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term169 _112226 _112228 _112229 x f g s) = (term184 _112226 _112228 _112229 x f g s).
Proof. exact (EQ_MP (@lem4877776 _112226 _112228 _112229 x f g s) (@lem4877757 _112226 _112228 _112229 x f g s)). Qed.
Lemma lem4877779 {A : Type'} (P : A -> Prop) (Q : Prop) : (term150 A P Q) = (term151 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4877780 {_112229 : Type'} (P : _112229 -> Prop) (Q : Prop) : (term150 _112229 P Q) = (term151 _112229 P Q).
Proof. exact (@lem4877779 _112229 P Q). Qed.
Lemma lem4877781 {_112226 _112228 _112229 : Type'} (y : _112228) (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term185 _112226 _112228 _112229 y x f g s) = (term186 _112226 _112228 _112229 y x f g s).
Proof. exact (@lem4877780 _112229 (term164 _112226 _112228 _112229 g s x f y) (term138 _112226 _112228 _112229 x f g s)). Qed.
Lemma lem4877782 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112229) (x' : _112226) (f : _112228 -> _112226) (y : _112228) : (term187 _112226 _112228 _112229 g s x' f y x) = (term162 _112226 _112228 _112229 g s x x' f y).
Proof. exact (eq_refl (term187 _112226 _112228 _112229 g s x' f y x)). Qed.
Lemma lem4877783 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (f : _112228 -> _112226) (y : _112228) : (term188 _112226 _112228 _112229 g s x f y) = (term164 _112226 _112228 _112229 g s x f y).
Proof. exact (fun_ext (fun x' : _112229 => @lem4877782 _112226 _112228 _112229 g s x' x f y)). Qed.
Lemma lem4877784 {_112229 : Type'} : (@ex _112229) = (@ex _112229).
Proof. exact (eq_refl (@ex _112229)). Qed.
Lemma lem4877785 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (f : _112228 -> _112226) (y : _112228) : (term189 _112226 _112228 _112229 g s x f y) = (term165 _112226 _112228 _112229 g s x f y).
Proof. exact (MK_COMB (@lem4877784 _112229) (@lem4877783 _112226 _112228 _112229 g s x f y)). Qed.
Lemma lem4877786 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4877787 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (f : _112228 -> _112226) (y : _112228) : (term190 _112226 _112228 _112229 g s x f y) = (term179 _112226 _112228 _112229 g s x f y).
Proof. exact (MK_COMB (@lem4877786) (@lem4877785 _112226 _112228 _112229 g s x f y)). Qed.
Lemma lem4877788 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term138 _112226 _112228 _112229 x f g s) = (term138 _112226 _112228 _112229 x f g s).
Proof. exact (eq_refl (term138 _112226 _112228 _112229 x f g s)). Qed.
Lemma lem4877789 {_112226 _112228 _112229 : Type'} (y : _112228) (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term185 _112226 _112228 _112229 y x f g s) = (term181 _112226 _112228 _112229 y x f g s).
Proof. exact (MK_COMB (@lem4877787 _112226 _112228 _112229 g s x f y) (@lem4877788 _112226 _112228 _112229 x f g s)). Qed.
Lemma lem4877790 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4877791 {_112226 _112228 _112229 : Type'} (y : _112228) (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term191 _112226 _112228 _112229 y x f g s) = (term192 _112226 _112228 _112229 y x f g s).
Proof. exact (MK_COMB (@lem4877790) (@lem4877789 _112226 _112228 _112229 y x f g s)). Qed.
Lemma lem4877792 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112229) (x' : _112226) (f : _112228 -> _112226) (y : _112228) : (term187 _112226 _112228 _112229 g s x' f y x) = (term162 _112226 _112228 _112229 g s x x' f y).
Proof. exact (eq_refl (term187 _112226 _112228 _112229 g s x' f y x)). Qed.
Lemma lem4877793 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4877794 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112229) (x' : _112226) (f : _112228 -> _112226) (y : _112228) : (term193 _112226 _112228 _112229 g s x' f y x) = (term194 _112226 _112228 _112229 g s x x' f y).
Proof. exact (MK_COMB (@lem4877793) (@lem4877792 _112226 _112228 _112229 g s x x' f y)). Qed.
Lemma lem4877795 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term138 _112226 _112228 _112229 x f g s) = (term138 _112226 _112228 _112229 x f g s).
Proof. exact (eq_refl (term138 _112226 _112228 _112229 x f g s)). Qed.
Lemma lem4877796 {_112226 _112228 _112229 : Type'} (x : _112229) (y : _112228) (x' : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term195 _112226 _112228 _112229 y x x' f g s) = (term196 _112226 _112228 _112229 x y x' f g s).
Proof. exact (MK_COMB (@lem4877794 _112226 _112228 _112229 g s x x' f y) (@lem4877795 _112226 _112228 _112229 x' f g s)). Qed.
Lemma lem4877797 {_112226 _112228 _112229 : Type'} (y : _112228) (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term197 _112226 _112228 _112229 y x f g s) = (term198 _112226 _112228 _112229 y x f g s).
Proof. exact (fun_ext (fun x' : _112229 => @lem4877796 _112226 _112228 _112229 x' y x f g s)). Qed.
Lemma lem4877798 {_112229 : Type'} : (@ex _112229) = (@ex _112229).
Proof. exact (eq_refl (@ex _112229)). Qed.
Lemma lem4877799 {_112226 _112228 _112229 : Type'} (y : _112228) (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term186 _112226 _112228 _112229 y x f g s) = (term199 _112226 _112228 _112229 y x f g s).
Proof. exact (MK_COMB (@lem4877798 _112229) (@lem4877797 _112226 _112228 _112229 y x f g s)). Qed.
Lemma lem4877800 {_112226 _112228 _112229 : Type'} (y : _112228) (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : ((term185 _112226 _112228 _112229 y x f g s) = (term186 _112226 _112228 _112229 y x f g s)) = ((term181 _112226 _112228 _112229 y x f g s) = (term199 _112226 _112228 _112229 y x f g s)).
Proof. exact (MK_COMB (@lem4877791 _112226 _112228 _112229 y x f g s) (@lem4877799 _112226 _112228 _112229 y x f g s)). Qed.
Lemma lem4877801 {_112226 _112228 _112229 : Type'} (y : _112228) (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term181 _112226 _112228 _112229 y x f g s) = (term199 _112226 _112228 _112229 y x f g s).
Proof. exact (EQ_MP (@lem4877800 _112226 _112228 _112229 y x f g s) (@lem4877781 _112226 _112228 _112229 y x f g s)). Qed.
Lemma lem4877802 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term183 _112226 _112228 _112229 x f g s) = (term200 _112226 _112228 _112229 x f g s).
Proof. exact (fun_ext (fun y : _112228 => @lem4877801 _112226 _112228 _112229 y x f g s)). Qed.
Lemma lem4877803 {_112228 : Type'} : (@ex _112228) = (@ex _112228).
Proof. exact (eq_refl (@ex _112228)). Qed.
Lemma lem4877804 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term184 _112226 _112228 _112229 x f g s) = (term201 _112226 _112228 _112229 x f g s).
Proof. exact (MK_COMB (@lem4877803 _112228) (@lem4877802 _112226 _112228 _112229 x f g s)). Qed.
Lemma lem4877805 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term169 _112226 _112228 _112229 x f g s) = (term201 _112226 _112228 _112229 x f g s).
Proof. exact (TRANS (@lem4877777 _112226 _112228 _112229 x f g s) (@lem4877804 _112226 _112228 _112229 x f g s)). Qed.
Lemma lem4877806 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term145 _112226 _112228 _112229 x f g s) = (term201 _112226 _112228 _112229 x f g s).
Proof. exact (TRANS (@lem4877753 _112226 _112228 _112229 x f g s) (@lem4877805 _112226 _112228 _112229 x f g s)). Qed.
Lemma lem4877807 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4877808 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term147 _112226 _112228 _112229 x f g s) = (term202 _112226 _112228 _112229 x f g s).
Proof. exact (MK_COMB (@lem4877807) (@lem4877806 _112226 _112228 _112229 x f g s)). Qed.
Lemma lem4877810 {A : Type'} (P : Prop) (Q : A -> Prop) : (term203 A P Q) = (term204 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4877811 {_112229 : Type'} (P : Prop) (Q : _112229 -> Prop) : (term203 _112229 P Q) = (term204 _112229 P Q).
Proof. exact (@lem4877810 _112229 P Q). Qed.
Lemma lem4877812 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term205 _112226 _112228 _112229 x f g s) = (term206 _112226 _112228 _112229 x f g s).
Proof. exact (@lem4877811 _112229 (term129 _112226 _112228 _112229 g s x f) (term79 _112226 _112228 _112229 x f g s)). Qed.
Lemma lem4877813 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (x' : _112229) : (term134 _112226 _112228 _112229 x f g s x') = (term77 _112226 _112228 _112229 x f g s x').
Proof. exact (eq_refl (term134 _112226 _112228 _112229 x f g s x')). Qed.
Lemma lem4877814 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term207 _112226 _112228 _112229 x f g s) = (term79 _112226 _112228 _112229 x f g s).
Proof. exact (fun_ext (fun x' : _112229 => @lem4877813 _112226 _112228 _112229 x f g s x')). Qed.
Lemma lem4877815 {_112229 : Type'} : (@ex _112229) = (@ex _112229).
Proof. exact (eq_refl (@ex _112229)). Qed.
Lemma lem4877816 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term208 _112226 _112228 _112229 x f g s) = (term80 _112226 _112228 _112229 x f g s).
Proof. exact (MK_COMB (@lem4877815 _112229) (@lem4877814 _112226 _112228 _112229 x f g s)). Qed.
Lemma lem4877817 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (f : _112228 -> _112226) : (term140 _112226 _112228 _112229 g s x f) = (term140 _112226 _112228 _112229 g s x f).
Proof. exact (eq_refl (term140 _112226 _112228 _112229 g s x f)). Qed.
Lemma lem4877818 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term205 _112226 _112228 _112229 x f g s) = (term142 _112226 _112228 _112229 x f g s).
Proof. exact (MK_COMB (@lem4877817 _112226 _112228 _112229 g s x f) (@lem4877816 _112226 _112228 _112229 x f g s)). Qed.
Lemma lem4877819 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4877820 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term209 _112226 _112228 _112229 x f g s) = (term210 _112226 _112228 _112229 x f g s).
Proof. exact (MK_COMB (@lem4877819) (@lem4877818 _112226 _112228 _112229 x f g s)). Qed.
Lemma lem4877821 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (x' : _112229) : (term134 _112226 _112228 _112229 x f g s x') = (term77 _112226 _112228 _112229 x f g s x').
Proof. exact (eq_refl (term134 _112226 _112228 _112229 x f g s x')). Qed.
Lemma lem4877822 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (f : _112228 -> _112226) : (term140 _112226 _112228 _112229 g s x f) = (term140 _112226 _112228 _112229 g s x f).
Proof. exact (eq_refl (term140 _112226 _112228 _112229 g s x f)). Qed.
Lemma lem4877823 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (x' : _112229) : (term211 _112226 _112228 _112229 x f g s x') = (term212 _112226 _112228 _112229 x f g s x').
Proof. exact (MK_COMB (@lem4877822 _112226 _112228 _112229 g s x f) (@lem4877821 _112226 _112228 _112229 x f g s x')). Qed.
Lemma lem4877824 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term213 _112226 _112228 _112229 x f g s) = (term214 _112226 _112228 _112229 x f g s).
Proof. exact (fun_ext (fun x' : _112229 => @lem4877823 _112226 _112228 _112229 x f g s x')). Qed.
Lemma lem4877825 {_112229 : Type'} : (@ex _112229) = (@ex _112229).
Proof. exact (eq_refl (@ex _112229)). Qed.
Lemma lem4877826 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term206 _112226 _112228 _112229 x f g s) = (term215 _112226 _112228 _112229 x f g s).
Proof. exact (MK_COMB (@lem4877825 _112229) (@lem4877824 _112226 _112228 _112229 x f g s)). Qed.
Lemma lem4877827 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : ((term205 _112226 _112228 _112229 x f g s) = (term206 _112226 _112228 _112229 x f g s)) = ((term142 _112226 _112228 _112229 x f g s) = (term215 _112226 _112228 _112229 x f g s)).
Proof. exact (MK_COMB (@lem4877820 _112226 _112228 _112229 x f g s) (@lem4877826 _112226 _112228 _112229 x f g s)). Qed.
Lemma lem4877828 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term142 _112226 _112228 _112229 x f g s) = (term215 _112226 _112228 _112229 x f g s).
Proof. exact (EQ_MP (@lem4877827 _112226 _112228 _112229 x f g s) (@lem4877812 _112226 _112228 _112229 x f g s)). Qed.
Lemma lem4877829 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term149 _112226 _112228 _112229 x f g s) = (term216 _112226 _112228 _112229 x f g s).
Proof. exact (MK_COMB (@lem4877808 _112226 _112228 _112229 x f g s) (@lem4877828 _112226 _112228 _112229 x f g s)). Qed.
Lemma lem4877833 {A : Type'} (P : A -> Prop) (Q : Prop) : (term217 A P Q) = (term218 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4877834 {_112228 : Type'} (P : _112228 -> Prop) (Q : Prop) : (term217 _112228 P Q) = (term218 _112228 P Q).
Proof. exact (@lem4877833 _112228 P Q). Qed.
Lemma lem4877835 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term219 _112226 _112228 _112229 x f g s) = (term220 _112226 _112228 _112229 x f g s).
Proof. exact (@lem4877834 _112228 (term200 _112226 _112228 _112229 x f g s) (term215 _112226 _112228 _112229 x f g s)). Qed.
Lemma lem4877836 {_112226 _112228 _112229 : Type'} (y : _112228) (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term221 _112226 _112228 _112229 x f g s y) = (term199 _112226 _112228 _112229 y x f g s).
Proof. exact (eq_refl (term221 _112226 _112228 _112229 x f g s y)). Qed.
Lemma lem4877837 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term222 _112226 _112228 _112229 x f g s) = (term200 _112226 _112228 _112229 x f g s).
Proof. exact (fun_ext (fun y : _112228 => @lem4877836 _112226 _112228 _112229 y x f g s)). Qed.
Lemma lem4877838 {_112228 : Type'} : (@ex _112228) = (@ex _112228).
Proof. exact (eq_refl (@ex _112228)). Qed.
Lemma lem4877839 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term223 _112226 _112228 _112229 x f g s) = (term201 _112226 _112228 _112229 x f g s).
Proof. exact (MK_COMB (@lem4877838 _112228) (@lem4877837 _112226 _112228 _112229 x f g s)). Qed.
Lemma lem4877840 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4877841 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term224 _112226 _112228 _112229 x f g s) = (term202 _112226 _112228 _112229 x f g s).
Proof. exact (MK_COMB (@lem4877840) (@lem4877839 _112226 _112228 _112229 x f g s)). Qed.
Lemma lem4877842 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term215 _112226 _112228 _112229 x f g s) = (term215 _112226 _112228 _112229 x f g s).
Proof. exact (eq_refl (term215 _112226 _112228 _112229 x f g s)). Qed.
Lemma lem4877843 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term219 _112226 _112228 _112229 x f g s) = (term216 _112226 _112228 _112229 x f g s).
Proof. exact (MK_COMB (@lem4877841 _112226 _112228 _112229 x f g s) (@lem4877842 _112226 _112228 _112229 x f g s)). Qed.
Lemma lem4877844 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4877845 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term225 _112226 _112228 _112229 x f g s) = (term226 _112226 _112228 _112229 x f g s).
Proof. exact (MK_COMB (@lem4877844) (@lem4877843 _112226 _112228 _112229 x f g s)). Qed.
Lemma lem4877846 {_112226 _112228 _112229 : Type'} (y : _112228) (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term221 _112226 _112228 _112229 x f g s y) = (term199 _112226 _112228 _112229 y x f g s).
Proof. exact (eq_refl (term221 _112226 _112228 _112229 x f g s y)). Qed.
Lemma lem4877847 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4877848 {_112226 _112228 _112229 : Type'} (y : _112228) (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term227 _112226 _112228 _112229 x f g s y) = (term228 _112226 _112228 _112229 y x f g s).
Proof. exact (MK_COMB (@lem4877847) (@lem4877846 _112226 _112228 _112229 y x f g s)). Qed.
Lemma lem4877849 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term215 _112226 _112228 _112229 x f g s) = (term215 _112226 _112228 _112229 x f g s).
Proof. exact (eq_refl (term215 _112226 _112228 _112229 x f g s)). Qed.
Lemma lem4877850 {_112226 _112228 _112229 : Type'} (y : _112228) (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term229 _112226 _112228 _112229 y x f g s) = (term230 _112226 _112228 _112229 y x f g s).
Proof. exact (MK_COMB (@lem4877848 _112226 _112228 _112229 y x f g s) (@lem4877849 _112226 _112228 _112229 x f g s)). Qed.
Lemma lem4877851 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term231 _112226 _112228 _112229 x f g s) = (term232 _112226 _112228 _112229 x f g s).
Proof. exact (fun_ext (fun y : _112228 => @lem4877850 _112226 _112228 _112229 y x f g s)). Qed.
Lemma lem4877852 {_112228 : Type'} : (@ex _112228) = (@ex _112228).
Proof. exact (eq_refl (@ex _112228)). Qed.
Lemma lem4877853 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term220 _112226 _112228 _112229 x f g s) = (term233 _112226 _112228 _112229 x f g s).
Proof. exact (MK_COMB (@lem4877852 _112228) (@lem4877851 _112226 _112228 _112229 x f g s)). Qed.
Lemma lem4877854 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : ((term219 _112226 _112228 _112229 x f g s) = (term220 _112226 _112228 _112229 x f g s)) = ((term216 _112226 _112228 _112229 x f g s) = (term233 _112226 _112228 _112229 x f g s)).
Proof. exact (MK_COMB (@lem4877845 _112226 _112228 _112229 x f g s) (@lem4877853 _112226 _112228 _112229 x f g s)). Qed.
Lemma lem4877855 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term216 _112226 _112228 _112229 x f g s) = (term233 _112226 _112228 _112229 x f g s).
Proof. exact (EQ_MP (@lem4877854 _112226 _112228 _112229 x f g s) (@lem4877835 _112226 _112228 _112229 x f g s)). Qed.
Lemma lem4877857 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term234 A P Q) = (term235 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4877858 {_112229 : Type'} (P : _112229 -> Prop) (Q : _112229 -> Prop) : (term234 _112229 P Q) = (term235 _112229 P Q).
Proof. exact (@lem4877857 _112229 P Q). Qed.
Lemma lem4877859 {_112226 _112228 _112229 : Type'} (y : _112228) (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term236 _112226 _112228 _112229 y x f g s) = (term237 _112226 _112228 _112229 y x f g s).
Proof. exact (@lem4877858 _112229 (term198 _112226 _112228 _112229 y x f g s) (term214 _112226 _112228 _112229 x f g s)). Qed.
Lemma lem4877860 {_112226 _112228 _112229 : Type'} (x : _112229) (y : _112228) (x' : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term238 _112226 _112228 _112229 y x' f g s x) = (term196 _112226 _112228 _112229 x y x' f g s).
Proof. exact (eq_refl (term238 _112226 _112228 _112229 y x' f g s x)). Qed.
Lemma lem4877861 {_112226 _112228 _112229 : Type'} (y : _112228) (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term239 _112226 _112228 _112229 y x f g s) = (term198 _112226 _112228 _112229 y x f g s).
Proof. exact (fun_ext (fun x' : _112229 => @lem4877860 _112226 _112228 _112229 x' y x f g s)). Qed.
Lemma lem4877862 {_112229 : Type'} : (@ex _112229) = (@ex _112229).
Proof. exact (eq_refl (@ex _112229)). Qed.
Lemma lem4877863 {_112226 _112228 _112229 : Type'} (y : _112228) (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term240 _112226 _112228 _112229 y x f g s) = (term199 _112226 _112228 _112229 y x f g s).
Proof. exact (MK_COMB (@lem4877862 _112229) (@lem4877861 _112226 _112228 _112229 y x f g s)). Qed.
Lemma lem4877864 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4877865 {_112226 _112228 _112229 : Type'} (y : _112228) (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term241 _112226 _112228 _112229 y x f g s) = (term228 _112226 _112228 _112229 y x f g s).
Proof. exact (MK_COMB (@lem4877864) (@lem4877863 _112226 _112228 _112229 y x f g s)). Qed.
Lemma lem4877866 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (x' : _112229) : (term242 _112226 _112228 _112229 x f g s x') = (term212 _112226 _112228 _112229 x f g s x').
Proof. exact (eq_refl (term242 _112226 _112228 _112229 x f g s x')). Qed.
Lemma lem4877867 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term243 _112226 _112228 _112229 x f g s) = (term214 _112226 _112228 _112229 x f g s).
Proof. exact (fun_ext (fun x' : _112229 => @lem4877866 _112226 _112228 _112229 x f g s x')). Qed.
Lemma lem4877868 {_112229 : Type'} : (@ex _112229) = (@ex _112229).
Proof. exact (eq_refl (@ex _112229)). Qed.
Lemma lem4877869 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term244 _112226 _112228 _112229 x f g s) = (term215 _112226 _112228 _112229 x f g s).
Proof. exact (MK_COMB (@lem4877868 _112229) (@lem4877867 _112226 _112228 _112229 x f g s)). Qed.
Lemma lem4877870 {_112226 _112228 _112229 : Type'} (y : _112228) (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term236 _112226 _112228 _112229 y x f g s) = (term230 _112226 _112228 _112229 y x f g s).
Proof. exact (MK_COMB (@lem4877865 _112226 _112228 _112229 y x f g s) (@lem4877869 _112226 _112228 _112229 x f g s)). Qed.
Lemma lem4877871 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4877872 {_112226 _112228 _112229 : Type'} (y : _112228) (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term245 _112226 _112228 _112229 y x f g s) = (term246 _112226 _112228 _112229 y x f g s).
Proof. exact (MK_COMB (@lem4877871) (@lem4877870 _112226 _112228 _112229 y x f g s)). Qed.
Lemma lem4877873 {_112226 _112228 _112229 : Type'} (x : _112229) (y : _112228) (x' : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term238 _112226 _112228 _112229 y x' f g s x) = (term196 _112226 _112228 _112229 x y x' f g s).
Proof. exact (eq_refl (term238 _112226 _112228 _112229 y x' f g s x)). Qed.
Lemma lem4877874 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4877875 {_112226 _112228 _112229 : Type'} (x : _112229) (y : _112228) (x' : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term247 _112226 _112228 _112229 y x' f g s x) = (term248 _112226 _112228 _112229 x y x' f g s).
Proof. exact (MK_COMB (@lem4877874) (@lem4877873 _112226 _112228 _112229 x y x' f g s)). Qed.
Lemma lem4877876 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (x' : _112229) : (term242 _112226 _112228 _112229 x f g s x') = (term212 _112226 _112228 _112229 x f g s x').
Proof. exact (eq_refl (term242 _112226 _112228 _112229 x f g s x')). Qed.
Lemma lem4877877 {_112226 _112228 _112229 : Type'} (y : _112228) (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (x' : _112229) : (term249 _112226 _112228 _112229 y x f g s x') = (term250 _112226 _112228 _112229 y x f g s x').
Proof. exact (MK_COMB (@lem4877875 _112226 _112228 _112229 x' y x f g s) (@lem4877876 _112226 _112228 _112229 x f g s x')). Qed.
Lemma lem4877878 {_112226 _112228 _112229 : Type'} (y : _112228) (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term251 _112226 _112228 _112229 y x f g s) = (term252 _112226 _112228 _112229 y x f g s).
Proof. exact (fun_ext (fun x' : _112229 => @lem4877877 _112226 _112228 _112229 y x f g s x')). Qed.
Lemma lem4877879 {_112229 : Type'} : (@ex _112229) = (@ex _112229).
Proof. exact (eq_refl (@ex _112229)). Qed.
Lemma lem4877880 {_112226 _112228 _112229 : Type'} (y : _112228) (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term237 _112226 _112228 _112229 y x f g s) = (term253 _112226 _112228 _112229 y x f g s).
Proof. exact (MK_COMB (@lem4877879 _112229) (@lem4877878 _112226 _112228 _112229 y x f g s)). Qed.
Lemma lem4877881 {_112226 _112228 _112229 : Type'} (y : _112228) (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : ((term236 _112226 _112228 _112229 y x f g s) = (term237 _112226 _112228 _112229 y x f g s)) = ((term230 _112226 _112228 _112229 y x f g s) = (term253 _112226 _112228 _112229 y x f g s)).
Proof. exact (MK_COMB (@lem4877872 _112226 _112228 _112229 y x f g s) (@lem4877880 _112226 _112228 _112229 y x f g s)). Qed.
Lemma lem4877882 {_112226 _112228 _112229 : Type'} (y : _112228) (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term230 _112226 _112228 _112229 y x f g s) = (term253 _112226 _112228 _112229 y x f g s).
Proof. exact (EQ_MP (@lem4877881 _112226 _112228 _112229 y x f g s) (@lem4877859 _112226 _112228 _112229 y x f g s)). Qed.
Lemma lem4877883 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term232 _112226 _112228 _112229 x f g s) = (term254 _112226 _112228 _112229 x f g s).
Proof. exact (fun_ext (fun y : _112228 => @lem4877882 _112226 _112228 _112229 y x f g s)). Qed.
Lemma lem4877884 {_112228 : Type'} : (@ex _112228) = (@ex _112228).
Proof. exact (eq_refl (@ex _112228)). Qed.
Lemma lem4877885 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term233 _112226 _112228 _112229 x f g s) = (term255 _112226 _112228 _112229 x f g s).
Proof. exact (MK_COMB (@lem4877884 _112228) (@lem4877883 _112226 _112228 _112229 x f g s)). Qed.
Lemma lem4877886 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term216 _112226 _112228 _112229 x f g s) = (term255 _112226 _112228 _112229 x f g s).
Proof. exact (TRANS (@lem4877855 _112226 _112228 _112229 x f g s) (@lem4877885 _112226 _112228 _112229 x f g s)). Qed.
Lemma lem4877888 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term149 _112226 _112228 _112229 x f g s) = (term255 _112226 _112228 _112229 x f g s).
Proof. exact (TRANS (@lem4877829 _112226 _112228 _112229 x f g s) (@lem4877886 _112226 _112228 _112229 x f g s)). Qed.
Lemma lem4877889 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term105 _112226 _112228 _112229 x f g s) = (term255 _112226 _112228 _112229 x f g s).
Proof. exact (TRANS (@lem4877465 _112226 _112228 _112229 x f g s) (@lem4877888 _112226 _112228 _112229 x f g s)). Qed.
Lemma lem4877890 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (h1 : term105 _112226 _112228 _112229 x f g s) : term255 _112226 _112228 _112229 x f g s.
Proof. exact (EQ_MP (@lem4877889 _112226 _112228 _112229 x f g s) (@lem4877381 _112226 _112228 _112229 x f g s h1)). Qed.
Lemma lem4877891 {_112226 _112228 _112229 : Type'} (y : _112228) (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (h1 : term253 _112226 _112228 _112229 y x f g s) : term253 _112226 _112228 _112229 y x f g s.
Proof. exact (h1). Qed.
Lemma lem4877892 {_112226 _112228 _112229 : Type'} (y : _112228) (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (x' : _112229) (h1 : term250 _112226 _112228 _112229 y x f g s x') : term250 _112226 _112228 _112229 y x f g s x'.
Proof. exact (h1). Qed.
Lemma lem4877907 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (x' : _112229) : (term77 _112226 _112228 _112229 x f g s x') = (term77 _112226 _112228 _112229 x f g s x').
Proof. exact (eq_refl (term77 _112226 _112228 _112229 x f g s x')). Qed.
Lemma lem4877916 {_112226 _112228 : Type'} (x : _112226) (f : _112228 -> _112226) (y : _112228) : (term117 _112226 _112228 x f y) = (term117 _112226 _112228 x f y).
Proof. exact (eq_refl (term117 _112226 _112228 x f y)). Qed.
Lemma lem4877933 {_112228 _112229 : Type'} (y : _112228) (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112229) : (term107 _112228 _112229 y g s x) = (term107 _112228 _112229 y g s x).
Proof. exact (eq_refl (term107 _112228 _112229 y g s x)). Qed.
Lemma lem4877934 {_112228 _112229 : Type'} (y : _112228) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term115 _112228 _112229 y g s) = (term115 _112228 _112229 y g s).
Proof. exact (fun_ext (fun x : _112229 => @lem4877933 _112228 _112229 y g s x)). Qed.
Lemma lem4877935 {_112229 : Type'} : (@all _112229) = (@all _112229).
Proof. exact (eq_refl (@all _112229)). Qed.
Lemma lem4877936 {_112228 _112229 : Type'} (y : _112228) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term116 _112228 _112229 y g s) = (term116 _112228 _112229 y g s).
Proof. exact (MK_COMB (@lem4877935 _112229) (@lem4877934 _112228 _112229 y g s)). Qed.
Lemma lem4877937 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4877938 {_112228 _112229 : Type'} (y : _112228) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term119 _112228 _112229 y g s) = (term119 _112228 _112229 y g s).
Proof. exact (MK_COMB (@lem4877937) (@lem4877936 _112228 _112229 y g s)). Qed.
Lemma lem4877939 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (f : _112228 -> _112226) (y : _112228) : (term121 _112226 _112228 _112229 g s x f y) = (term121 _112226 _112228 _112229 g s x f y).
Proof. exact (MK_COMB (@lem4877938 _112228 _112229 y g s) (@lem4877916 _112226 _112228 x f y)). Qed.
Lemma lem4877940 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (f : _112228 -> _112226) : (term128 _112226 _112228 _112229 g s x f) = (term128 _112226 _112228 _112229 g s x f).
Proof. exact (fun_ext (fun y : _112228 => @lem4877939 _112226 _112228 _112229 g s x f y)). Qed.
Lemma lem4877941 {_112228 : Type'} : (@all _112228) = (@all _112228).
Proof. exact (eq_refl (@all _112228)). Qed.
Lemma lem4877942 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (f : _112228 -> _112226) : (term129 _112226 _112228 _112229 g s x f) = (term129 _112226 _112228 _112229 g s x f).
Proof. exact (MK_COMB (@lem4877941 _112228) (@lem4877940 _112226 _112228 _112229 g s x f)). Qed.
Lemma lem4877943 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4877944 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (f : _112228 -> _112226) : (term140 _112226 _112228 _112229 g s x f) = (term140 _112226 _112228 _112229 g s x f).
Proof. exact (MK_COMB (@lem4877943) (@lem4877942 _112226 _112228 _112229 g s x f)). Qed.
Lemma lem4877945 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (x' : _112229) : (term212 _112226 _112228 _112229 x f g s x') = (term212 _112226 _112228 _112229 x f g s x').
Proof. exact (MK_COMB (@lem4877944 _112226 _112228 _112229 g s x f) (@lem4877907 _112226 _112228 _112229 x f g s x')). Qed.
Lemma lem4877964 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (x' : _112229) : (term131 _112226 _112228 _112229 x f g s x') = (term131 _112226 _112228 _112229 x f g s x').
Proof. exact (eq_refl (term131 _112226 _112228 _112229 x f g s x')). Qed.
Lemma lem4877965 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term137 _112226 _112228 _112229 x f g s) = (term137 _112226 _112228 _112229 x f g s).
Proof. exact (fun_ext (fun x' : _112229 => @lem4877964 _112226 _112228 _112229 x f g s x')). Qed.
Lemma lem4877966 {_112229 : Type'} : (@all _112229) = (@all _112229).
Proof. exact (eq_refl (@all _112229)). Qed.
Lemma lem4877967 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term138 _112226 _112228 _112229 x f g s) = (term138 _112226 _112228 _112229 x f g s).
Proof. exact (MK_COMB (@lem4877966 _112229) (@lem4877965 _112226 _112228 _112229 x f g s)). Qed.
Lemma lem4877992 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x' : _112229) (x : _112226) (f : _112228 -> _112226) (y : _112228) : (term194 _112226 _112228 _112229 g s x' x f y) = (term194 _112226 _112228 _112229 g s x' x f y).
Proof. exact (eq_refl (term194 _112226 _112228 _112229 g s x' x f y)). Qed.
Lemma lem4877993 {_112226 _112228 _112229 : Type'} (x' : _112229) (y : _112228) (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term196 _112226 _112228 _112229 x' y x f g s) = (term196 _112226 _112228 _112229 x' y x f g s).
Proof. exact (MK_COMB (@lem4877992 _112226 _112228 _112229 g s x' x f y) (@lem4877967 _112226 _112228 _112229 x f g s)). Qed.
Lemma lem4877994 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4877995 {_112226 _112228 _112229 : Type'} (x' : _112229) (y : _112228) (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term248 _112226 _112228 _112229 x' y x f g s) = (term248 _112226 _112228 _112229 x' y x f g s).
Proof. exact (MK_COMB (@lem4877994) (@lem4877993 _112226 _112228 _112229 x' y x f g s)). Qed.
Lemma lem4877996 {_112226 _112228 _112229 : Type'} (y : _112228) (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (x' : _112229) : (term250 _112226 _112228 _112229 y x f g s x') = (term250 _112226 _112228 _112229 y x f g s x').
Proof. exact (MK_COMB (@lem4877995 _112226 _112228 _112229 x' y x f g s) (@lem4877945 _112226 _112228 _112229 x f g s x')). Qed.
Lemma lem4877997 {_112226 _112228 _112229 : Type'} (y : _112228) (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (x' : _112229) (h1 : term250 _112226 _112228 _112229 y x f g s x') : term250 _112226 _112228 _112229 y x f g s x'.
Proof. exact (EQ_MP (@lem4877996 _112226 _112228 _112229 y x f g s x') (@lem4877892 _112226 _112228 _112229 y x f g s x' h1)). Qed.
Lemma lem4877998 {_112226 _112228 _112229 : Type'} (x' : _112229) (y : _112228) (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (h1 : term196 _112226 _112228 _112229 x' y x f g s) : term196 _112226 _112228 _112229 x' y x f g s.
Proof. exact (h1). Qed.
Lemma lem4877999 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (x' : _112229) (h1 : term212 _112226 _112228 _112229 x f g s x') : term212 _112226 _112228 _112229 x f g s x'.
Proof. exact (h1). Qed.
Lemma lem4878000 {_112226 _112228 _112229 : Type'} (x' : _112229) (y : _112228) (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (h1 : term196 _112226 _112228 _112229 x' y x f g s) : term138 _112226 _112228 _112229 x f g s.
Proof. exact (proj2 (@lem4877998 _112226 _112228 _112229 x' y x f g s h1)). Qed.
Lemma lem4878001 {_112226 _112228 _112229 : Type'} (x' : _112229) (y : _112228) (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (h1 : term196 _112226 _112228 _112229 x' y x f g s) : term162 _112226 _112228 _112229 g s x' x f y.
Proof. exact (proj1 (@lem4877998 _112226 _112228 _112229 x' y x f g s h1)). Qed.
Lemma lem4878003 {_112226 _112228 _112229 : Type'} (x' : _112229) (y : _112228) (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (h1 : term196 _112226 _112228 _112229 x' y x f g s) : term42 _112228 _112229 y g s x'.
Proof. exact (proj1 (@lem4878001 _112226 _112228 _112229 x' y x f g s h1)). Qed.
Lemma lem4878006 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (x' : _112229) (h1 : term212 _112226 _112228 _112229 x f g s x') : term77 _112226 _112228 _112229 x f g s x'.
Proof. exact (proj2 (@lem4877999 _112226 _112228 _112229 x f g s x' h1)). Qed.
Lemma lem4878007 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (x' : _112229) (h1 : term212 _112226 _112228 _112229 x f g s x') : term129 _112226 _112228 _112229 g s x f.
Proof. exact (proj1 (@lem4877999 _112226 _112228 _112229 x f g s x' h1)). Qed.
Lemma lem4878017 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (x' : _112229) : (term131 _112226 _112228 _112229 x f g s x') = (term131 _112226 _112228 _112229 x f g s x').
Proof. exact (eq_refl (term131 _112226 _112228 _112229 x f g s x')). Qed.
Lemma lem4878018 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term137 _112226 _112228 _112229 x f g s) = (term137 _112226 _112228 _112229 x f g s).
Proof. exact (fun_ext (fun x' : _112229 => @lem4878017 _112226 _112228 _112229 x f g s x')). Qed.
Lemma lem4878019 {_112229 : Type'} : (@all _112229) = (@all _112229).
Proof. exact (eq_refl (@all _112229)). Qed.
Lemma lem4878021 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term138 _112226 _112228 _112229 x f g s) = (term138 _112226 _112228 _112229 x f g s).
Proof. exact (MK_COMB (@lem4878019 _112229) (@lem4878018 _112226 _112228 _112229 x f g s)). Qed.
Lemma lem4878022 {_112226 _112228 _112229 : Type'} (x' : _112229) (y : _112228) (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (h1 : term196 _112226 _112228 _112229 x' y x f g s) : term138 _112226 _112228 _112229 x f g s.
Proof. exact (EQ_MP (@lem4878021 _112226 _112228 _112229 x f g s) (@lem4878000 _112226 _112228 _112229 x' y x f g s h1)). Qed.
Lemma lem4878036 {A : Type'} (P : A -> Prop) (Q : Prop) : (term256 A P Q) = (term257 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem4878037 {_112229 : Type'} (P : _112229 -> Prop) (Q : Prop) : (term256 _112229 P Q) = (term257 _112229 P Q).
Proof. exact (@lem4878036 _112229 P Q). Qed.
Lemma lem4878038 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (f : _112228 -> _112226) (y : _112228) : (term258 _112226 _112228 _112229 g s x f y) = (term259 _112226 _112228 _112229 g s x f y).
Proof. exact (@lem4878037 _112229 (term115 _112228 _112229 y g s) (term117 _112226 _112228 x f y)). Qed.
Lemma lem4878039 {_112228 _112229 : Type'} (y : _112228) (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112229) : (term260 _112228 _112229 y g s x) = (term107 _112228 _112229 y g s x).
Proof. exact (eq_refl (term260 _112228 _112229 y g s x)). Qed.
Lemma lem4878040 {_112228 _112229 : Type'} (y : _112228) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term261 _112228 _112229 y g s) = (term115 _112228 _112229 y g s).
Proof. exact (fun_ext (fun x : _112229 => @lem4878039 _112228 _112229 y g s x)). Qed.
Lemma lem4878041 {_112229 : Type'} : (@all _112229) = (@all _112229).
Proof. exact (eq_refl (@all _112229)). Qed.
Lemma lem4878042 {_112228 _112229 : Type'} (y : _112228) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term262 _112228 _112229 y g s) = (term116 _112228 _112229 y g s).
Proof. exact (MK_COMB (@lem4878041 _112229) (@lem4878040 _112228 _112229 y g s)). Qed.
Lemma lem4878043 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4878044 {_112228 _112229 : Type'} (y : _112228) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term263 _112228 _112229 y g s) = (term119 _112228 _112229 y g s).
Proof. exact (MK_COMB (@lem4878043) (@lem4878042 _112228 _112229 y g s)). Qed.
Lemma lem4878045 {_112226 _112228 : Type'} (x : _112226) (f : _112228 -> _112226) (y : _112228) : (term117 _112226 _112228 x f y) = (term117 _112226 _112228 x f y).
Proof. exact (eq_refl (term117 _112226 _112228 x f y)). Qed.
Lemma lem4878046 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (f : _112228 -> _112226) (y : _112228) : (term258 _112226 _112228 _112229 g s x f y) = (term121 _112226 _112228 _112229 g s x f y).
Proof. exact (MK_COMB (@lem4878044 _112228 _112229 y g s) (@lem4878045 _112226 _112228 x f y)). Qed.
Lemma lem4878047 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4878048 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (f : _112228 -> _112226) (y : _112228) : (term264 _112226 _112228 _112229 g s x f y) = (term265 _112226 _112228 _112229 g s x f y).
Proof. exact (MK_COMB (@lem4878047) (@lem4878046 _112226 _112228 _112229 g s x f y)). Qed.
Lemma lem4878049 {_112228 _112229 : Type'} (y : _112228) (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112229) : (term260 _112228 _112229 y g s x) = (term107 _112228 _112229 y g s x).
Proof. exact (eq_refl (term260 _112228 _112229 y g s x)). Qed.
Lemma lem4878050 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4878051 {_112228 _112229 : Type'} (y : _112228) (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112229) : (term266 _112228 _112229 y g s x) = (term267 _112228 _112229 y g s x).
Proof. exact (MK_COMB (@lem4878050) (@lem4878049 _112228 _112229 y g s x)). Qed.
Lemma lem4878052 {_112226 _112228 : Type'} (x : _112226) (f : _112228 -> _112226) (y : _112228) : (term117 _112226 _112228 x f y) = (term117 _112226 _112228 x f y).
Proof. exact (eq_refl (term117 _112226 _112228 x f y)). Qed.
Lemma lem4878053 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112229) (x' : _112226) (f : _112228 -> _112226) (y : _112228) : (term268 _112226 _112228 _112229 g s x x' f y) = (term269 _112226 _112228 _112229 g s x x' f y).
Proof. exact (MK_COMB (@lem4878051 _112228 _112229 y g s x) (@lem4878052 _112226 _112228 x' f y)). Qed.
Lemma lem4878054 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (f : _112228 -> _112226) (y : _112228) : (term270 _112226 _112228 _112229 g s x f y) = (term271 _112226 _112228 _112229 g s x f y).
Proof. exact (fun_ext (fun x' : _112229 => @lem4878053 _112226 _112228 _112229 g s x' x f y)). Qed.
Lemma lem4878055 {_112229 : Type'} : (@all _112229) = (@all _112229).
Proof. exact (eq_refl (@all _112229)). Qed.
Lemma lem4878056 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (f : _112228 -> _112226) (y : _112228) : (term259 _112226 _112228 _112229 g s x f y) = (term272 _112226 _112228 _112229 g s x f y).
Proof. exact (MK_COMB (@lem4878055 _112229) (@lem4878054 _112226 _112228 _112229 g s x f y)). Qed.
Lemma lem4878057 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (f : _112228 -> _112226) (y : _112228) : ((term258 _112226 _112228 _112229 g s x f y) = (term259 _112226 _112228 _112229 g s x f y)) = ((term121 _112226 _112228 _112229 g s x f y) = (term272 _112226 _112228 _112229 g s x f y)).
Proof. exact (MK_COMB (@lem4878048 _112226 _112228 _112229 g s x f y) (@lem4878056 _112226 _112228 _112229 g s x f y)). Qed.
Lemma lem4878058 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (f : _112228 -> _112226) (y : _112228) : (term121 _112226 _112228 _112229 g s x f y) = (term272 _112226 _112228 _112229 g s x f y).
Proof. exact (EQ_MP (@lem4878057 _112226 _112228 _112229 g s x f y) (@lem4878038 _112226 _112228 _112229 g s x f y)). Qed.
Lemma lem4878059 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (f : _112228 -> _112226) : (term128 _112226 _112228 _112229 g s x f) = (term273 _112226 _112228 _112229 g s x f).
Proof. exact (fun_ext (fun y : _112228 => @lem4878058 _112226 _112228 _112229 g s x f y)). Qed.
Lemma lem4878060 {_112228 : Type'} : (@all _112228) = (@all _112228).
Proof. exact (eq_refl (@all _112228)). Qed.
Lemma lem4878061 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (f : _112228 -> _112226) : (term129 _112226 _112228 _112229 g s x f) = (term274 _112226 _112228 _112229 g s x f).
Proof. exact (MK_COMB (@lem4878060 _112228) (@lem4878059 _112226 _112228 _112229 g s x f)). Qed.
Lemma lem4878074 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112229) (x' : _112226) (f : _112228 -> _112226) (y : _112228) : (term269 _112226 _112228 _112229 g s x x' f y) = (term269 _112226 _112228 _112229 g s x x' f y).
Proof. exact (eq_refl (term269 _112226 _112228 _112229 g s x x' f y)). Qed.
Lemma lem4878075 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (f : _112228 -> _112226) (y : _112228) : (term271 _112226 _112228 _112229 g s x f y) = (term271 _112226 _112228 _112229 g s x f y).
Proof. exact (fun_ext (fun x' : _112229 => @lem4878074 _112226 _112228 _112229 g s x' x f y)). Qed.
Lemma lem4878076 {_112229 : Type'} : (@all _112229) = (@all _112229).
Proof. exact (eq_refl (@all _112229)). Qed.
Lemma lem4878077 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (f : _112228 -> _112226) (y : _112228) : (term272 _112226 _112228 _112229 g s x f y) = (term272 _112226 _112228 _112229 g s x f y).
Proof. exact (MK_COMB (@lem4878076 _112229) (@lem4878075 _112226 _112228 _112229 g s x f y)). Qed.
Lemma lem4878078 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (f : _112228 -> _112226) : (term273 _112226 _112228 _112229 g s x f) = (term273 _112226 _112228 _112229 g s x f).
Proof. exact (fun_ext (fun y : _112228 => @lem4878077 _112226 _112228 _112229 g s x f y)). Qed.
Lemma lem4878079 {_112228 : Type'} : (@all _112228) = (@all _112228).
Proof. exact (eq_refl (@all _112228)). Qed.
Lemma lem4878080 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (f : _112228 -> _112226) : (term274 _112226 _112228 _112229 g s x f) = (term274 _112226 _112228 _112229 g s x f).
Proof. exact (MK_COMB (@lem4878079 _112228) (@lem4878078 _112226 _112228 _112229 g s x f)). Qed.
Lemma lem4878081 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (f : _112228 -> _112226) : (term129 _112226 _112228 _112229 g s x f) = (term274 _112226 _112228 _112229 g s x f).
Proof. exact (TRANS (@lem4878061 _112226 _112228 _112229 g s x f) (@lem4878080 _112226 _112228 _112229 g s x f)). Qed.
Lemma lem4878082 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (x' : _112229) (h1 : term212 _112226 _112228 _112229 x f g s x') : term274 _112226 _112228 _112229 g s x f.
Proof. exact (EQ_MP (@lem4878081 _112226 _112228 _112229 g s x f) (@lem4878007 _112226 _112228 _112229 x f g s x' h1)). Qed.
Lemma lem4878091 {_112226 _112228 _112229 : Type'} (_60345 : _112229) (x' : _112229) (y : _112228) (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (h1 : term196 _112226 _112228 _112229 x' y x f g s) : term275 _112226 _112228 _112229 x f g s _60345.
Proof. exact (@lem4878022 _112226 _112228 _112229 x' y x f g s h1 _60345). Qed.
Lemma lem4878092 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (_60345 : _112229) : (term275 _112226 _112228 _112229 x f g s _60345) = (term131 _112226 _112228 _112229 x f g s _60345).
Proof. exact (eq_refl (term275 _112226 _112228 _112229 x f g s _60345)). Qed.
Lemma lem4878094 {_112226 _112228 _112229 : Type'} (_60346 : _112228) (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (x' : _112229) (h1 : term212 _112226 _112228 _112229 x f g s x') : term276 _112226 _112228 _112229 g s x f _60346.
Proof. exact (@lem4878082 _112226 _112228 _112229 x f g s x' h1 _60346). Qed.
Lemma lem4878095 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (x : _112226) (f : _112228 -> _112226) (_60346 : _112228) : (term276 _112226 _112228 _112229 g s x f _60346) = (term272 _112226 _112228 _112229 g s x f _60346).
Proof. exact (eq_refl (term276 _112226 _112228 _112229 g s x f _60346)). Qed.
Lemma lem4878096 {_112226 _112228 _112229 : Type'} (_60346 : _112228) (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (x' : _112229) (h1 : term212 _112226 _112228 _112229 x f g s x') : term272 _112226 _112228 _112229 g s x f _60346.
Proof. exact (EQ_MP (@lem4878095 _112226 _112228 _112229 g s x f _60346) (@lem4878094 _112226 _112228 _112229 _60346 x f g s x' h1)). Qed.
Lemma lem4878097 {_112226 _112228 _112229 : Type'} (_60346 : _112228) (_60347 : _112229) (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (x' : _112229) (h1 : term212 _112226 _112228 _112229 x f g s x') : term277 _112226 _112228 _112229 g s x f _60346 _60347.
Proof. exact (@lem4878096 _112226 _112228 _112229 _60346 x f g s x' h1 _60347). Qed.
Lemma lem4878098 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (_60347 : _112229) (x : _112226) (f : _112228 -> _112226) (_60346 : _112228) : (term277 _112226 _112228 _112229 g s x f _60346 _60347) = (term269 _112226 _112228 _112229 g s _60347 x f _60346).
Proof. exact (eq_refl (term277 _112226 _112228 _112229 g s x f _60346 _60347)). Qed.
Lemma lem4878099 {_112226 _112228 _112229 : Type'} (_60347 : _112229) (_60346 : _112228) (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (x' : _112229) (h1 : term212 _112226 _112228 _112229 x f g s x') : term269 _112226 _112228 _112229 g s _60347 x f _60346.
Proof. exact (EQ_MP (@lem4878098 _112226 _112228 _112229 g s _60347 x f _60346) (@lem4878097 _112226 _112228 _112229 _60346 _60347 x f g s x' h1)). Qed.
Lemma lem4878107 {_112226 _112228 _112229 : Type'} (x' : _112229) (y : _112228) (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (h1 : term196 _112226 _112228 _112229 x' y x f g s) : x = (f y).
Proof. exact (proj2 (@lem4878001 _112226 _112228 _112229 x' y x f g s h1)). Qed.
Lemma lem4878109 {_112226 _112228 _112229 : Type'} (x' : _112229) (y : _112228) (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (h1 : term196 _112226 _112228 _112229 x' y x f g s) : y = (g x').
Proof. exact (proj1 (@lem4878003 _112226 _112228 _112229 x' y x f g s h1)). Qed.
Lemma lem4878122 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (_60347 : _112229) (x : _112226) (f : _112228 -> _112226) (_60346 : _112228) : (term269 _112226 _112228 _112229 g s _60347 x f _60346) = (term278 _112226 _112228 _112229 g s _60347 x f _60346).
Proof. exact (@lem4876905 (term117 _112228 _112229 _60346 g _60347) (term279 _112229 s _60347) (term117 _112226 _112228 x f _60346)). Qed.
Lemma lem4878123 {_112226 _112228 _112229 : Type'} (_60347 : _112229) (_60346 : _112228) (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (x' : _112229) (h1 : term212 _112226 _112228 _112229 x f g s x') : term278 _112226 _112228 _112229 g s _60347 x f _60346.
Proof. exact (EQ_MP (@lem4878122 _112226 _112228 _112229 g s _60347 x f _60346) (@lem4878099 _112226 _112228 _112229 _60347 _60346 x f g s x' h1)). Qed.
Lemma lem4878125 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (x' : _112229) (h1 : term212 _112226 _112228 _112229 x f g s x') : x = (term70 _112226 _112228 _112229 f g x').
Proof. exact (proj1 (@lem4878006 _112226 _112228 _112229 x f g s x' h1)). Qed.
Lemma lem4878155 {_112226 _112228 _112229 : Type'} (_60345 : _112229) (x' : _112229) (y : _112228) (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (h1 : term196 _112226 _112228 _112229 x' y x f g s) : term131 _112226 _112228 _112229 x f g s _60345.
Proof. exact (EQ_MP (@lem4878092 _112226 _112228 _112229 x f g s _60345) (@lem4878091 _112226 _112228 _112229 _60345 x' y x f g s h1)). Qed.
Lemma lem4878156 {_112226 _112228 : Type'} (x : _112226) (f : _112228 -> _112226) : (term280 _112226 _112228 x f) = (term280 _112226 _112228 x f).
Proof. exact (eq_refl (term280 _112226 _112228 x f)). Qed.
Lemma lem4878157 {_112226 _112228 _112229 : Type'} (x' : _112229) (y : _112228) (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (h1 : term196 _112226 _112228 _112229 x' y x f g s) : (term281 _112226 _112228 x f y) = (term282 _112226 _112228 _112229 x f g x').
Proof. exact (MK_COMB (@lem4878156 _112226 _112228 x f) (@lem4878109 _112226 _112228 _112229 x' y x f g s h1)). Qed.
Lemma lem4878158 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (x' : _112229) : (term282 _112226 _112228 _112229 x f g x') = (x = (term70 _112226 _112228 _112229 f g x')).
Proof. exact (eq_refl (term282 _112226 _112228 _112229 x f g x')). Qed.
Lemma lem4878159 {_112226 _112228 : Type'} (x : _112226) (f : _112228 -> _112226) (y : _112228) : (term283 _112226 _112228 x f y) = (term283 _112226 _112228 x f y).
Proof. exact (eq_refl (term283 _112226 _112228 x f y)). Qed.
Lemma lem4878160 {_112226 _112228 _112229 : Type'} (y : _112228) (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (x' : _112229) : ((term281 _112226 _112228 x f y) = (term282 _112226 _112228 _112229 x f g x')) = ((term281 _112226 _112228 x f y) = (x = (term70 _112226 _112228 _112229 f g x'))).
Proof. exact (MK_COMB (@lem4878159 _112226 _112228 x f y) (@lem4878158 _112226 _112228 _112229 x f g x')). Qed.
Lemma lem4878161 {_112226 _112228 : Type'} (x : _112226) (f : _112228 -> _112226) (y : _112228) : (term281 _112226 _112228 x f y) = (x = (f y)).
Proof. exact (eq_refl (term281 _112226 _112228 x f y)). Qed.
Lemma lem4878162 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4878163 {_112226 _112228 : Type'} (x : _112226) (f : _112228 -> _112226) (y : _112228) : (term283 _112226 _112228 x f y) = (term284 _112226 _112228 x f y).
Proof. exact (MK_COMB (@lem4878162) (@lem4878161 _112226 _112228 x f y)). Qed.
Lemma lem4878164 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (x' : _112229) : (x = (term70 _112226 _112228 _112229 f g x')) = (x = (term70 _112226 _112228 _112229 f g x')).
Proof. exact (eq_refl (x = (term70 _112226 _112228 _112229 f g x'))). Qed.
Lemma lem4878165 {_112226 _112228 _112229 : Type'} (y : _112228) (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (x' : _112229) : ((term281 _112226 _112228 x f y) = (x = (term70 _112226 _112228 _112229 f g x'))) = ((x = (f y)) = (x = (term70 _112226 _112228 _112229 f g x'))).
Proof. exact (MK_COMB (@lem4878163 _112226 _112228 x f y) (@lem4878164 _112226 _112228 _112229 x f g x')). Qed.
Lemma lem4878166 {_112226 _112228 _112229 : Type'} (y : _112228) (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (x' : _112229) : ((term281 _112226 _112228 x f y) = (term282 _112226 _112228 _112229 x f g x')) = ((x = (f y)) = (x = (term70 _112226 _112228 _112229 f g x'))).
Proof. exact (TRANS (@lem4878160 _112226 _112228 _112229 y x f g x') (@lem4878165 _112226 _112228 _112229 y x f g x')). Qed.
Lemma lem4878167 {_112226 _112228 _112229 : Type'} (x' : _112229) (y : _112228) (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (h1 : term196 _112226 _112228 _112229 x' y x f g s) : (x = (f y)) = (x = (term70 _112226 _112228 _112229 f g x')).
Proof. exact (EQ_MP (@lem4878166 _112226 _112228 _112229 y x f g x') (@lem4878157 _112226 _112228 _112229 x' y x f g s h1)). Qed.
Lemma lem4878168 {_112226 _112228 _112229 : Type'} (x' : _112229) (y : _112228) (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (h1 : term196 _112226 _112228 _112229 x' y x f g s) : x = (term70 _112226 _112228 _112229 f g x').
Proof. exact (EQ_MP (@lem4878167 _112226 _112228 _112229 x' y x f g s h1) (@lem4878107 _112226 _112228 _112229 x' y x f g s h1)). Qed.
Lemma lem4878197 {_112226 _112228 _112229 : Type'} (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (_60345 : _112229) : (term285 _112226 _112228 _112229 f g s _60345) = (term285 _112226 _112228 _112229 f g s _60345).
Proof. exact (eq_refl (term285 _112226 _112228 _112229 f g s _60345)). Qed.
Lemma lem4878198 {_112226 _112228 _112229 : Type'} (_60345 : _112229) (x' : _112229) (y : _112228) (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (h1 : term196 _112226 _112228 _112229 x' y x f g s) : (term286 _112226 _112228 _112229 f g s _60345 x) = (term287 _112226 _112228 _112229 s _60345 f g x').
Proof. exact (MK_COMB (@lem4878197 _112226 _112228 _112229 f g s _60345) (@lem4878168 _112226 _112228 _112229 x' y x f g s h1)). Qed.
Lemma lem4878199 {_112226 _112228 _112229 : Type'} (x' : _112229) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (_60345 : _112229) : (term287 _112226 _112228 _112229 s _60345 f g x') = (term288 _112226 _112228 _112229 x' f g s _60345).
Proof. exact (eq_refl (term287 _112226 _112228 _112229 s _60345 f g x')). Qed.
Lemma lem4878200 {_112226 _112228 _112229 : Type'} (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (_60345 : _112229) (x : _112226) : (term289 _112226 _112228 _112229 f g s _60345 x) = (term289 _112226 _112228 _112229 f g s _60345 x).
Proof. exact (eq_refl (term289 _112226 _112228 _112229 f g s _60345 x)). Qed.
Lemma lem4878201 {_112226 _112228 _112229 : Type'} (x : _112226) (x' : _112229) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (_60345 : _112229) : ((term286 _112226 _112228 _112229 f g s _60345 x) = (term287 _112226 _112228 _112229 s _60345 f g x')) = ((term286 _112226 _112228 _112229 f g s _60345 x) = (term288 _112226 _112228 _112229 x' f g s _60345)).
Proof. exact (MK_COMB (@lem4878200 _112226 _112228 _112229 f g s _60345 x) (@lem4878199 _112226 _112228 _112229 x' f g s _60345)). Qed.
Lemma lem4878202 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (_60345 : _112229) : (term286 _112226 _112228 _112229 f g s _60345 x) = (term131 _112226 _112228 _112229 x f g s _60345).
Proof. exact (eq_refl (term286 _112226 _112228 _112229 f g s _60345 x)). Qed.
Lemma lem4878203 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4878204 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (_60345 : _112229) : (term289 _112226 _112228 _112229 f g s _60345 x) = (term290 _112226 _112228 _112229 x f g s _60345).
Proof. exact (MK_COMB (@lem4878203) (@lem4878202 _112226 _112228 _112229 x f g s _60345)). Qed.
Lemma lem4878205 {_112226 _112228 _112229 : Type'} (x' : _112229) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (_60345 : _112229) : (term288 _112226 _112228 _112229 x' f g s _60345) = (term288 _112226 _112228 _112229 x' f g s _60345).
Proof. exact (eq_refl (term288 _112226 _112228 _112229 x' f g s _60345)). Qed.
Lemma lem4878206 {_112226 _112228 _112229 : Type'} (x : _112226) (x' : _112229) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (_60345 : _112229) : ((term286 _112226 _112228 _112229 f g s _60345 x) = (term288 _112226 _112228 _112229 x' f g s _60345)) = ((term131 _112226 _112228 _112229 x f g s _60345) = (term288 _112226 _112228 _112229 x' f g s _60345)).
Proof. exact (MK_COMB (@lem4878204 _112226 _112228 _112229 x f g s _60345) (@lem4878205 _112226 _112228 _112229 x' f g s _60345)). Qed.
Lemma lem4878207 {_112226 _112228 _112229 : Type'} (x : _112226) (x' : _112229) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (_60345 : _112229) : ((term286 _112226 _112228 _112229 f g s _60345 x) = (term287 _112226 _112228 _112229 s _60345 f g x')) = ((term131 _112226 _112228 _112229 x f g s _60345) = (term288 _112226 _112228 _112229 x' f g s _60345)).
Proof. exact (TRANS (@lem4878201 _112226 _112228 _112229 x x' f g s _60345) (@lem4878206 _112226 _112228 _112229 x x' f g s _60345)). Qed.
Lemma lem4878208 {_112226 _112228 _112229 : Type'} (_60345 : _112229) (x' : _112229) (y : _112228) (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (h1 : term196 _112226 _112228 _112229 x' y x f g s) : (term131 _112226 _112228 _112229 x f g s _60345) = (term288 _112226 _112228 _112229 x' f g s _60345).
Proof. exact (EQ_MP (@lem4878207 _112226 _112228 _112229 x x' f g s _60345) (@lem4878198 _112226 _112228 _112229 _60345 x' y x f g s h1)). Qed.
Lemma lem4878209 {_112226 _112228 _112229 : Type'} (_60345 : _112229) (x' : _112229) (y : _112228) (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (h1 : term196 _112226 _112228 _112229 x' y x f g s) : term288 _112226 _112228 _112229 x' f g s _60345.
Proof. exact (EQ_MP (@lem4878208 _112226 _112228 _112229 _60345 x' y x f g s h1) (@lem4878155 _112226 _112228 _112229 _60345 x' y x f g s h1)). Qed.
Lemma lem4878238 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (_60347 : _112229) (f : _112228 -> _112226) (_60346 : _112228) : (term291 _112226 _112228 _112229 g s _60347 f _60346) = (term291 _112226 _112228 _112229 g s _60347 f _60346).
Proof. exact (eq_refl (term291 _112226 _112228 _112229 g s _60347 f _60346)). Qed.
Lemma lem4878239 {_112226 _112228 _112229 : Type'} (_60347 : _112229) (_60346 : _112228) (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (x' : _112229) (h1 : term212 _112226 _112228 _112229 x f g s x') : (term292 _112226 _112228 _112229 g s _60347 f _60346 x) = (term293 _112226 _112228 _112229 s _60347 _60346 f g x').
Proof. exact (MK_COMB (@lem4878238 _112226 _112228 _112229 g s _60347 f _60346) (@lem4878125 _112226 _112228 _112229 x f g s x' h1)). Qed.
Lemma lem4878240 {_112226 _112228 _112229 : Type'} (s : _112229 -> Prop) (_60347 : _112229) (g : _112229 -> _112228) (x' : _112229) (f : _112228 -> _112226) (_60346 : _112228) : (term293 _112226 _112228 _112229 s _60347 _60346 f g x') = (term294 _112226 _112228 _112229 s _60347 g x' f _60346).
Proof. exact (eq_refl (term293 _112226 _112228 _112229 s _60347 _60346 f g x')). Qed.
Lemma lem4878241 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (_60347 : _112229) (f : _112228 -> _112226) (_60346 : _112228) (x : _112226) : (term295 _112226 _112228 _112229 g s _60347 f _60346 x) = (term295 _112226 _112228 _112229 g s _60347 f _60346 x).
Proof. exact (eq_refl (term295 _112226 _112228 _112229 g s _60347 f _60346 x)). Qed.
Lemma lem4878242 {_112226 _112228 _112229 : Type'} (x : _112226) (s : _112229 -> Prop) (_60347 : _112229) (g : _112229 -> _112228) (x' : _112229) (f : _112228 -> _112226) (_60346 : _112228) : ((term292 _112226 _112228 _112229 g s _60347 f _60346 x) = (term293 _112226 _112228 _112229 s _60347 _60346 f g x')) = ((term292 _112226 _112228 _112229 g s _60347 f _60346 x) = (term294 _112226 _112228 _112229 s _60347 g x' f _60346)).
Proof. exact (MK_COMB (@lem4878241 _112226 _112228 _112229 g s _60347 f _60346 x) (@lem4878240 _112226 _112228 _112229 s _60347 g x' f _60346)). Qed.
Lemma lem4878243 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (_60347 : _112229) (x : _112226) (f : _112228 -> _112226) (_60346 : _112228) : (term292 _112226 _112228 _112229 g s _60347 f _60346 x) = (term278 _112226 _112228 _112229 g s _60347 x f _60346).
Proof. exact (eq_refl (term292 _112226 _112228 _112229 g s _60347 f _60346 x)). Qed.
Lemma lem4878244 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4878245 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (_60347 : _112229) (x : _112226) (f : _112228 -> _112226) (_60346 : _112228) : (term295 _112226 _112228 _112229 g s _60347 f _60346 x) = (term296 _112226 _112228 _112229 g s _60347 x f _60346).
Proof. exact (MK_COMB (@lem4878244) (@lem4878243 _112226 _112228 _112229 g s _60347 x f _60346)). Qed.
Lemma lem4878246 {_112226 _112228 _112229 : Type'} (s : _112229 -> Prop) (_60347 : _112229) (g : _112229 -> _112228) (x' : _112229) (f : _112228 -> _112226) (_60346 : _112228) : (term294 _112226 _112228 _112229 s _60347 g x' f _60346) = (term294 _112226 _112228 _112229 s _60347 g x' f _60346).
Proof. exact (eq_refl (term294 _112226 _112228 _112229 s _60347 g x' f _60346)). Qed.
Lemma lem4878247 {_112226 _112228 _112229 : Type'} (x : _112226) (s : _112229 -> Prop) (_60347 : _112229) (g : _112229 -> _112228) (x' : _112229) (f : _112228 -> _112226) (_60346 : _112228) : ((term292 _112226 _112228 _112229 g s _60347 f _60346 x) = (term294 _112226 _112228 _112229 s _60347 g x' f _60346)) = ((term278 _112226 _112228 _112229 g s _60347 x f _60346) = (term294 _112226 _112228 _112229 s _60347 g x' f _60346)).
Proof. exact (MK_COMB (@lem4878245 _112226 _112228 _112229 g s _60347 x f _60346) (@lem4878246 _112226 _112228 _112229 s _60347 g x' f _60346)). Qed.
Lemma lem4878248 {_112226 _112228 _112229 : Type'} (x : _112226) (s : _112229 -> Prop) (_60347 : _112229) (g : _112229 -> _112228) (x' : _112229) (f : _112228 -> _112226) (_60346 : _112228) : ((term292 _112226 _112228 _112229 g s _60347 f _60346 x) = (term293 _112226 _112228 _112229 s _60347 _60346 f g x')) = ((term278 _112226 _112228 _112229 g s _60347 x f _60346) = (term294 _112226 _112228 _112229 s _60347 g x' f _60346)).
Proof. exact (TRANS (@lem4878242 _112226 _112228 _112229 x s _60347 g x' f _60346) (@lem4878247 _112226 _112228 _112229 x s _60347 g x' f _60346)). Qed.
Lemma lem4878249 {_112226 _112228 _112229 : Type'} (_60347 : _112229) (_60346 : _112228) (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (x' : _112229) (h1 : term212 _112226 _112228 _112229 x f g s x') : (term278 _112226 _112228 _112229 g s _60347 x f _60346) = (term294 _112226 _112228 _112229 s _60347 g x' f _60346).
Proof. exact (EQ_MP (@lem4878248 _112226 _112228 _112229 x s _60347 g x' f _60346) (@lem4878239 _112226 _112228 _112229 _60347 _60346 x f g s x' h1)). Qed.
Lemma lem4878250 {_112226 _112228 _112229 : Type'} (_60347 : _112229) (_60346 : _112228) (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (x' : _112229) (h1 : term212 _112226 _112228 _112229 x f g s x') : term294 _112226 _112228 _112229 s _60347 g x' f _60346.
Proof. exact (EQ_MP (@lem4878249 _112226 _112228 _112229 _60347 _60346 x f g s x' h1) (@lem4878123 _112226 _112228 _112229 _60347 _60346 x f g s x' h1)). Qed.
Lemma lem4878300 {_112226 : Type'} (x : _112226) : x = x.
Proof. exact (@lem21386 _112226 x). Qed.
Lemma lem4878301 {_112226 : Type'} (x : _112226) : x = x.
Proof. exact (@lem4878300 _112226 x). Qed.
Lemma lem4878302 {_112226 _112228 _112229 : Type'} (f : _112228 -> _112226) (g : _112229 -> _112228) (x' : _112229) : (term70 _112226 _112228 _112229 f g x') = (term70 _112226 _112228 _112229 f g x').
Proof. exact (@lem4878301 _112226 (term70 _112226 _112228 _112229 f g x')). Qed.
Lemma lem4878303 {_112226 _112228 _112229 : Type'} (f : _112228 -> _112226) (g : _112229 -> _112228) (x' : _112229) : term297 _112226 _112228 _112229 f g x'.
Proof. exact (fun h0 : term298 _112226 _112228 _112229 f g x' => @lem4878302 _112226 _112228 _112229 f g x'). Qed.
Lemma lem4878305 (p : Prop) : (term299 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4878306 {_112226 _112228 _112229 : Type'} (f : _112228 -> _112226) (g : _112229 -> _112228) (x' : _112229) : (term297 _112226 _112228 _112229 f g x') = ((term70 _112226 _112228 _112229 f g x') = (term70 _112226 _112228 _112229 f g x')).
Proof. exact (@lem4878305 ((term70 _112226 _112228 _112229 f g x') = (term70 _112226 _112228 _112229 f g x'))). Qed.
Lemma lem4878307 {_112226 _112228 _112229 : Type'} (f : _112228 -> _112226) (g : _112229 -> _112228) (x' : _112229) : (term70 _112226 _112228 _112229 f g x') = (term70 _112226 _112228 _112229 f g x').
Proof. exact (EQ_MP (@lem4878306 _112226 _112228 _112229 f g x') (@lem4878303 _112226 _112228 _112229 f g x')). Qed.
Lemma lem4878309 {_112226 _112228 _112229 : Type'} (x' : _112229) (y : _112228) (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (h1 : term196 _112226 _112228 _112229 x' y x f g s) : s x'.
Proof. exact (proj2 (@lem4878003 _112226 _112228 _112229 x' y x f g s h1)). Qed.
Lemma lem4878310 {_112226 _112228 _112229 : Type'} (x' : _112229) (y : _112228) (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (h1 : term196 _112226 _112228 _112229 x' y x f g s) : term300 _112229 s x'.
Proof. exact (fun h0 : term279 _112229 s x' => @lem4878309 _112226 _112228 _112229 x' y x f g s h1). Qed.
Lemma lem4878312 (p : Prop) : (term299 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4878313 {_112229 : Type'} (s : _112229 -> Prop) (x' : _112229) : (term300 _112229 s x') = (s x').
Proof. exact (@lem4878312 (s x')). Qed.
Lemma lem4878314 {_112226 _112228 _112229 : Type'} (x' : _112229) (y : _112228) (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (h1 : term196 _112226 _112228 _112229 x' y x f g s) : s x'.
Proof. exact (EQ_MP (@lem4878313 _112229 s x') (@lem4878310 _112226 _112228 _112229 x' y x f g s h1)). Qed.
Lemma lem4878316 (a : Prop) (b : Prop) : (term301 a b) = (term302 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4878317 {_112226 _112228 _112229 : Type'} (x' : _112229) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (_60345 : _112229) : (term288 _112226 _112228 _112229 x' f g s _60345) = (term303 _112226 _112228 _112229 x' f g s _60345).
Proof. exact (@lem4878316 ((term70 _112226 _112228 _112229 f g x') = (term70 _112226 _112228 _112229 f g _60345)) (s _60345)). Qed.
Lemma lem4878319 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4878320 {_112226 _112228 _112229 : Type'} (x' : _112229) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (_60345 : _112229) : (term303 _112226 _112228 _112229 x' f g s _60345) = (term304 _112226 _112228 _112229 x' f g s _60345).
Proof. exact (@lem4878319 (term305 _112226 _112228 _112229 x' f g s _60345)). Qed.
Lemma lem4878321 {_112226 _112228 _112229 : Type'} (x' : _112229) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (_60345 : _112229) : (term288 _112226 _112228 _112229 x' f g s _60345) = (term304 _112226 _112228 _112229 x' f g s _60345).
Proof. exact (TRANS (@lem4878317 _112226 _112228 _112229 x' f g s _60345) (@lem4878320 _112226 _112228 _112229 x' f g s _60345)). Qed.
Lemma lem4878323 {_112226 _112228 _112229 : Type'} (x' : _112229) (y : _112228) (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (h1 : term196 _112226 _112228 _112229 x' y x f g s) : term306 _112226 _112228 _112229 f g s x'.
Proof. exact (conj (@lem4878307 _112226 _112228 _112229 f g x') (@lem4878314 _112226 _112228 _112229 x' y x f g s h1)). Qed.
Lemma lem4878325 {_112226 _112228 _112229 : Type'} (_60345 : _112229) (x' : _112229) (y : _112228) (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (h1 : term196 _112226 _112228 _112229 x' y x f g s) : term304 _112226 _112228 _112229 x' f g s _60345.
Proof. exact (EQ_MP (@lem4878321 _112226 _112228 _112229 x' f g s _60345) (@lem4878209 _112226 _112228 _112229 _60345 x' y x f g s h1)). Qed.
Lemma lem4878326 {_112226 _112228 _112229 : Type'} (_60345 : _112229) (x' : _112229) (y : _112228) (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (h1 : term196 _112226 _112228 _112229 x' y x f g s) : term304 _112226 _112228 _112229 x' f g s _60345.
Proof. exact (@lem4878325 _112226 _112228 _112229 _60345 x' y x f g s h1). Qed.
Lemma lem4878327 {_112226 _112228 _112229 : Type'} (x' : _112229) (y : _112228) (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (h1 : term196 _112226 _112228 _112229 x' y x f g s) : term307 _112226 _112228 _112229 f g s x'.
Proof. exact (@lem4878326 _112226 _112228 _112229 x' x' y x f g s h1). Qed.
Lemma lem4878330 {_112226 _112228 _112229 : Type'} (x' : _112229) (y : _112228) (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (h1 : term196 _112226 _112228 _112229 x' y x f g s) : False.
Proof. exact (@lem4878327 _112226 _112228 _112229 x' y x f g s h1 (@lem4878323 _112226 _112228 _112229 x' y x f g s h1)). Qed.
Lemma lem4878331 {_112226 _112228 _112229 : Type'} (x' : _112229) (y : _112228) (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (h1 : term196 _112226 _112228 _112229 x' y x f g s) : term308.
Proof. exact (fun h0 : ~ False => @lem4878330 _112226 _112228 _112229 x' y x f g s h1). Qed.
Lemma lem4878333 (p : Prop) : (term299 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4878334 : term308 = False.
Proof. exact (@lem4878333 False). Qed.
Lemma lem4878371 {_112228 : Type'} (x : _112228) : x = x.
Proof. exact (@lem21386 _112228 x). Qed.
Lemma lem4878372 {_112228 : Type'} (x : _112228) : x = x.
Proof. exact (@lem4878371 _112228 x). Qed.
Lemma lem4878373 {_112228 _112229 : Type'} (g : _112229 -> _112228) (x' : _112229) : (g x') = (g x').
Proof. exact (@lem4878372 _112228 (g x')). Qed.
Lemma lem4878374 {_112228 _112229 : Type'} (g : _112229 -> _112228) (x' : _112229) : term309 _112228 _112229 g x'.
Proof. exact (fun h0 : term310 _112228 _112229 g x' => @lem4878373 _112228 _112229 g x'). Qed.
Lemma lem4878376 (p : Prop) : (term299 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4878377 {_112228 _112229 : Type'} (g : _112229 -> _112228) (x' : _112229) : (term309 _112228 _112229 g x') = ((g x') = (g x')).
Proof. exact (@lem4878376 ((g x') = (g x'))). Qed.
Lemma lem4878378 {_112228 _112229 : Type'} (g : _112229 -> _112228) (x' : _112229) : (g x') = (g x').
Proof. exact (EQ_MP (@lem4878377 _112228 _112229 g x') (@lem4878374 _112228 _112229 g x')). Qed.
Lemma lem4878380 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (x' : _112229) (h1 : term212 _112226 _112228 _112229 x f g s x') : s x'.
Proof. exact (proj2 (@lem4878006 _112226 _112228 _112229 x f g s x' h1)). Qed.
Lemma lem4878381 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (x' : _112229) (h1 : term212 _112226 _112228 _112229 x f g s x') : term300 _112229 s x'.
Proof. exact (fun h0 : term279 _112229 s x' => @lem4878380 _112226 _112228 _112229 x f g s x' h1). Qed.
Lemma lem4878383 (p : Prop) : (term299 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4878384 {_112229 : Type'} (s : _112229 -> Prop) (x' : _112229) : (term300 _112229 s x') = (s x').
Proof. exact (@lem4878383 (s x')). Qed.
Lemma lem4878385 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (x' : _112229) (h1 : term212 _112226 _112228 _112229 x f g s x') : s x'.
Proof. exact (EQ_MP (@lem4878384 _112229 s x') (@lem4878381 _112226 _112228 _112229 x f g s x' h1)). Qed.
Lemma lem4878387 {_112226 : Type'} (x : _112226) : x = x.
Proof. exact (@lem21386 _112226 x). Qed.
Lemma lem4878388 {_112226 : Type'} (x : _112226) : x = x.
Proof. exact (@lem4878387 _112226 x). Qed.
Lemma lem4878389 {_112226 _112228 _112229 : Type'} (f : _112228 -> _112226) (g : _112229 -> _112228) (x' : _112229) : (term70 _112226 _112228 _112229 f g x') = (term70 _112226 _112228 _112229 f g x').
Proof. exact (@lem4878388 _112226 (term70 _112226 _112228 _112229 f g x')). Qed.
Lemma lem4878390 {_112226 _112228 _112229 : Type'} (f : _112228 -> _112226) (g : _112229 -> _112228) (x' : _112229) : term297 _112226 _112228 _112229 f g x'.
Proof. exact (fun h0 : term298 _112226 _112228 _112229 f g x' => @lem4878389 _112226 _112228 _112229 f g x'). Qed.
Lemma lem4878392 (p : Prop) : (term299 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4878393 {_112226 _112228 _112229 : Type'} (f : _112228 -> _112226) (g : _112229 -> _112228) (x' : _112229) : (term297 _112226 _112228 _112229 f g x') = ((term70 _112226 _112228 _112229 f g x') = (term70 _112226 _112228 _112229 f g x')).
Proof. exact (@lem4878392 ((term70 _112226 _112228 _112229 f g x') = (term70 _112226 _112228 _112229 f g x'))). Qed.
Lemma lem4878394 {_112226 _112228 _112229 : Type'} (f : _112228 -> _112226) (g : _112229 -> _112228) (x' : _112229) : (term70 _112226 _112228 _112229 f g x') = (term70 _112226 _112228 _112229 f g x').
Proof. exact (EQ_MP (@lem4878393 _112226 _112228 _112229 f g x') (@lem4878390 _112226 _112228 _112229 f g x')). Qed.
Lemma lem4878396 (a : Prop) (b : Prop) : (term301 a b) = (term302 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4878397 {_112226 _112228 _112229 : Type'} (s : _112229 -> Prop) (_60347 : _112229) (g : _112229 -> _112228) (x' : _112229) (f : _112228 -> _112226) (_60346 : _112228) : (term311 _112226 _112228 _112229 s _60347 g x' f _60346) = (term312 _112226 _112228 _112229 s _60347 g x' f _60346).
Proof. exact (@lem4878396 (s _60347) ((term70 _112226 _112228 _112229 f g x') = (f _60346))). Qed.
Lemma lem4878398 {_112228 _112229 : Type'} (_60346 : _112228) (g : _112229 -> _112228) (_60347 : _112229) : (term313 _112228 _112229 _60346 g _60347) = (term313 _112228 _112229 _60346 g _60347).
Proof. exact (eq_refl (term313 _112228 _112229 _60346 g _60347)). Qed.
Lemma lem4878399 {_112226 _112228 _112229 : Type'} (s : _112229 -> Prop) (_60347 : _112229) (g : _112229 -> _112228) (x' : _112229) (f : _112228 -> _112226) (_60346 : _112228) : (term294 _112226 _112228 _112229 s _60347 g x' f _60346) = (term314 _112226 _112228 _112229 s _60347 g x' f _60346).
Proof. exact (MK_COMB (@lem4878398 _112228 _112229 _60346 g _60347) (@lem4878397 _112226 _112228 _112229 s _60347 g x' f _60346)). Qed.
Lemma lem4878401 (a : Prop) (b : Prop) : (term301 a b) = (term302 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4878402 {_112226 _112228 _112229 : Type'} (s : _112229 -> Prop) (_60347 : _112229) (g : _112229 -> _112228) (x' : _112229) (f : _112228 -> _112226) (_60346 : _112228) : (term314 _112226 _112228 _112229 s _60347 g x' f _60346) = (term315 _112226 _112228 _112229 s _60347 g x' f _60346).
Proof. exact (@lem4878401 (_60346 = (g _60347)) (term316 _112226 _112228 _112229 s _60347 g x' f _60346)). Qed.
Lemma lem4878403 {_112226 _112228 _112229 : Type'} (s : _112229 -> Prop) (_60347 : _112229) (g : _112229 -> _112228) (x' : _112229) (f : _112228 -> _112226) (_60346 : _112228) : (term294 _112226 _112228 _112229 s _60347 g x' f _60346) = (term315 _112226 _112228 _112229 s _60347 g x' f _60346).
Proof. exact (TRANS (@lem4878399 _112226 _112228 _112229 s _60347 g x' f _60346) (@lem4878402 _112226 _112228 _112229 s _60347 g x' f _60346)). Qed.
Lemma lem4878405 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4878406 {_112226 _112228 _112229 : Type'} (s : _112229 -> Prop) (_60347 : _112229) (g : _112229 -> _112228) (x' : _112229) (f : _112228 -> _112226) (_60346 : _112228) : (term315 _112226 _112228 _112229 s _60347 g x' f _60346) = (term317 _112226 _112228 _112229 s _60347 g x' f _60346).
Proof. exact (@lem4878405 (term318 _112226 _112228 _112229 s _60347 g x' f _60346)). Qed.
Lemma lem4878407 {_112226 _112228 _112229 : Type'} (s : _112229 -> Prop) (_60347 : _112229) (g : _112229 -> _112228) (x' : _112229) (f : _112228 -> _112226) (_60346 : _112228) : (term294 _112226 _112228 _112229 s _60347 g x' f _60346) = (term317 _112226 _112228 _112229 s _60347 g x' f _60346).
Proof. exact (TRANS (@lem4878403 _112226 _112228 _112229 s _60347 g x' f _60346) (@lem4878406 _112226 _112228 _112229 s _60347 g x' f _60346)). Qed.
Lemma lem4878409 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (x' : _112229) (h1 : term212 _112226 _112228 _112229 x f g s x') : term319 _112226 _112228 _112229 s f g x'.
Proof. exact (conj (@lem4878385 _112226 _112228 _112229 x f g s x' h1) (@lem4878394 _112226 _112228 _112229 f g x')). Qed.
Lemma lem4878410 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (x' : _112229) (h1 : term212 _112226 _112228 _112229 x f g s x') : term320 _112226 _112228 _112229 s f g x'.
Proof. exact (conj (@lem4878378 _112228 _112229 g x') (@lem4878409 _112226 _112228 _112229 x f g s x' h1)). Qed.
Lemma lem4878412 {_112226 _112228 _112229 : Type'} (_60347 : _112229) (_60346 : _112228) (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (x' : _112229) (h1 : term212 _112226 _112228 _112229 x f g s x') : term317 _112226 _112228 _112229 s _60347 g x' f _60346.
Proof. exact (EQ_MP (@lem4878407 _112226 _112228 _112229 s _60347 g x' f _60346) (@lem4878250 _112226 _112228 _112229 _60347 _60346 x f g s x' h1)). Qed.
Lemma lem4878413 {_112226 _112228 _112229 : Type'} (_60347 : _112229) (_60346 : _112228) (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (x' : _112229) (h1 : term212 _112226 _112228 _112229 x f g s x') : term317 _112226 _112228 _112229 s _60347 g x' f _60346.
Proof. exact (@lem4878412 _112226 _112228 _112229 _60347 _60346 x f g s x' h1). Qed.
Lemma lem4878414 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (x' : _112229) (h1 : term212 _112226 _112228 _112229 x f g s x') : term321 _112226 _112228 _112229 s f g x'.
Proof. exact (@lem4878413 _112226 _112228 _112229 x' (g x') x f g s x' h1). Qed.
Lemma lem4878417 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (x' : _112229) (h1 : term212 _112226 _112228 _112229 x f g s x') : False.
Proof. exact (@lem4878414 _112226 _112228 _112229 x f g s x' h1 (@lem4878410 _112226 _112228 _112229 x f g s x' h1)). Qed.
Lemma lem4878418 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (x' : _112229) (h1 : term212 _112226 _112228 _112229 x f g s x') : term308.
Proof. exact (fun h0 : ~ False => @lem4878417 _112226 _112228 _112229 x f g s x' h1). Qed.
Lemma lem4878420 (p : Prop) : (term299 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4878421 : term308 = False.
Proof. exact (@lem4878420 False). Qed.
Lemma lem4878423 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (x' : _112229) (h1 : term212 _112226 _112228 _112229 x f g s x') : False.
Proof. exact (EQ_MP (@lem4878421) (@lem4878418 _112226 _112228 _112229 x f g s x' h1)). Qed.
Lemma lem4878425 {_112226 _112228 _112229 : Type'} (x' : _112229) (y : _112228) (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (h1 : term196 _112226 _112228 _112229 x' y x f g s) : False.
Proof. exact (EQ_MP (@lem4878334) (@lem4878331 _112226 _112228 _112229 x' y x f g s h1)). Qed.
Lemma lem4878426 {_112226 _112228 _112229 : Type'} (y : _112228) (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (x' : _112229) (h1 : term250 _112226 _112228 _112229 y x f g s x') : False.
Proof. exact (or_elim (@lem4877997 _112226 _112228 _112229 y x f g s x' h1) (fun h0 : term196 _112226 _112228 _112229 x' y x f g s => @lem4878425 _112226 _112228 _112229 x' y x f g s h0) (fun h0 : term212 _112226 _112228 _112229 x f g s x' => @lem4878423 _112226 _112228 _112229 x f g s x' h0)). Qed.
Lemma lem4878427 {_112226 _112228 _112229 : Type'} (y : _112228) (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (x' : _112229) (h1 : term250 _112226 _112228 _112229 y x f g s x') : (term250 _112226 _112228 _112229 y x f g s x') = False.
Proof. exact (prop_ext (fun h2 : term250 _112226 _112228 _112229 y x f g s x' => @lem4878426 _112226 _112228 _112229 y x f g s x' h1) (fun h2 : False => @lem4877997 _112226 _112228 _112229 y x f g s x' h1)). Qed.
Lemma lem4878428 {_112226 _112228 _112229 : Type'} (y : _112228) (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (x' : _112229) (h1 : term250 _112226 _112228 _112229 y x f g s x') : False.
Proof. exact (EQ_MP (@lem4878427 _112226 _112228 _112229 y x f g s x' h1) (@lem4877997 _112226 _112228 _112229 y x f g s x' h1)). Qed.
Lemma lem4878429 {_112226 _112228 _112229 : Type'} (y : _112228) (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (h1 : term253 _112226 _112228 _112229 y x f g s) : False.
Proof. exact (ex_elim (@lem4877891 _112226 _112228 _112229 y x f g s h1) (fun x' : _112229 => fun h0 : term252 _112226 _112228 _112229 y x f g s x' => @lem4878428 _112226 _112228 _112229 y x f g s x' h0)). Qed.
Lemma lem4878430 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (h1 : term105 _112226 _112228 _112229 x f g s) : False.
Proof. exact (ex_elim (@lem4877890 _112226 _112228 _112229 x f g s h1) (fun y : _112228 => fun h0 : term254 _112226 _112228 _112229 x f g s y => @lem4878429 _112226 _112228 _112229 y x f g s h0)). Qed.
Lemma lem4878431 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (h1 : term105 _112226 _112228 _112229 x f g s) : (term105 _112226 _112228 _112229 x f g s) = False.
Proof. exact (prop_ext (fun h2 : term105 _112226 _112228 _112229 x f g s => @lem4878430 _112226 _112228 _112229 x f g s h1) (fun h2 : False => @lem4877381 _112226 _112228 _112229 x f g s h1)). Qed.
Lemma lem4878432 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (h1 : term105 _112226 _112228 _112229 x f g s) : False.
Proof. exact (EQ_MP (@lem4878431 _112226 _112228 _112229 x f g s h1) (@lem4877381 _112226 _112228 _112229 x f g s h1)). Qed.
Lemma lem4878433 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : term104 _112226 _112228 _112229 x f g s.
Proof. exact (fun h0 : term105 _112226 _112228 _112229 x f g s => @lem4878432 _112226 _112228 _112229 x f g s h0). Qed.
Lemma lem4878434 {_112226 _112228 _112229 : Type'} (x : _112226) (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term62 _112226 _112228 _112229 g s x f) = (term80 _112226 _112228 _112229 x f g s).
Proof. exact (EQ_MP (@lem4877380 _112226 _112228 _112229 x f g s) (@lem4878433 _112226 _112228 _112229 x f g s)). Qed.
Lemma lem4878439 {_112226 _112228 _112229 : Type'} (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : term83 _112226 _112228 _112229 f g s.
Proof. exact (fun x : _112226 => @lem4878434 _112226 _112228 _112229 x f g s). Qed.
Lemma lem4878444 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) : term95 _112226 _112228 _112229 g s.
Proof. exact (fun f : _112228 -> _112226 => @lem4878439 _112226 _112228 _112229 f g s). Qed.
Lemma lem4878449 {_112226 _112228 _112229 : Type'} (s : _112229 -> Prop) : term99 _112226 _112228 _112229 s.
Proof. exact (fun g : _112229 -> _112228 => @lem4878444 _112226 _112228 _112229 g s). Qed.
Lemma lem4878454 {_112226 _112228 _112229 : Type'} : term103 _112226 _112228 _112229.
Proof. exact (fun s : _112229 -> Prop => @lem4878449 _112226 _112228 _112229 s). Qed.
Lemma lem4878455 {_112226 _112228 _112229 : Type'} : term102 _112226 _112228 _112229.
Proof. exact (EQ_MP (@lem4877376 _112226 _112228 _112229) (@lem4878454 _112226 _112228 _112229)). Qed.
Lemma lem4878456 {_112226 _112228 _112229 : Type'} (s : _112229 -> Prop) : term322 _112226 _112228 _112229 s.
Proof. exact (@lem4878455 _112226 _112228 _112229 s). Qed.
Lemma lem4878457 {_112226 _112228 _112229 : Type'} (s : _112229 -> Prop) : (term322 _112226 _112228 _112229 s) = (term98 _112226 _112228 _112229 s).
Proof. exact (eq_refl (term322 _112226 _112228 _112229 s)). Qed.
Lemma lem4878458 {_112226 _112228 _112229 : Type'} (s : _112229 -> Prop) : term98 _112226 _112228 _112229 s.
Proof. exact (EQ_MP (@lem4878457 _112226 _112228 _112229 s) (@lem4878456 _112226 _112228 _112229 s)). Qed.
Lemma lem4878459 {_112226 _112228 _112229 : Type'} (s : _112229 -> Prop) (g : _112229 -> _112228) : term323 _112226 _112228 _112229 s g.
Proof. exact (@lem4878458 _112226 _112228 _112229 s g). Qed.
Lemma lem4878460 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) : (term323 _112226 _112228 _112229 s g) = (term94 _112226 _112228 _112229 g s).
Proof. exact (eq_refl (term323 _112226 _112228 _112229 s g)). Qed.
Lemma lem4878461 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) : term94 _112226 _112228 _112229 g s.
Proof. exact (EQ_MP (@lem4878460 _112226 _112228 _112229 g s) (@lem4878459 _112226 _112228 _112229 s g)). Qed.
Lemma lem4878462 {_112226 _112228 _112229 : Type'} (g : _112229 -> _112228) (s : _112229 -> Prop) (f : _112228 -> _112226) : term324 _112226 _112228 _112229 g s f.
Proof. exact (@lem4878461 _112226 _112228 _112229 g s f). Qed.
Lemma lem4878463 {_112226 _112228 _112229 : Type'} (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term324 _112226 _112228 _112229 g s f) = (term85 _112226 _112228 _112229 f g s).
Proof. exact (eq_refl (term324 _112226 _112228 _112229 g s f)). Qed.
Lemma lem4878464 {_112226 _112228 _112229 : Type'} (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : term85 _112226 _112228 _112229 f g s.
Proof. exact (EQ_MP (@lem4878463 _112226 _112228 _112229 f g s) (@lem4878462 _112226 _112228 _112229 g s f)). Qed.
Lemma lem4878466 {_112226 _112228 _112229 : Type'} (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : term85 _112226 _112228 _112229 f g s.
Proof. exact (@lem4877120 _112226 _112228 _112229 f g s (@lem4878464 _112226 _112228 _112229 f g s)). Qed.
Lemma lem4878467 {_112226 _112228 _112229 : Type'} (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (h1 : term86 _112226 _112228 _112229 f g s) : False.
Proof. exact (@lem4878466 _112226 _112228 _112229 f g s (@lem4877104 _112226 _112228 _112229 f g s h1)). Qed.
Lemma lem4878468 {_112226 _112228 _112229 : Type'} (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (h1 : term86 _112226 _112228 _112229 f g s) : (term86 _112226 _112228 _112229 f g s) = False.
Proof. exact (prop_ext (fun h2 : term86 _112226 _112228 _112229 f g s => @lem4878467 _112226 _112228 _112229 f g s h1) (fun h2 : False => @lem4877104 _112226 _112228 _112229 f g s h1)). Qed.
Lemma lem4878469 {_112226 _112228 _112229 : Type'} (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) (h1 : term86 _112226 _112228 _112229 f g s) : False.
Proof. exact (EQ_MP (@lem4878468 _112226 _112228 _112229 f g s h1) (@lem4877104 _112226 _112228 _112229 f g s h1)). Qed.
Lemma lem4878470 {_112226 _112228 _112229 : Type'} (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : term85 _112226 _112228 _112229 f g s.
Proof. exact (fun h0 : term86 _112226 _112228 _112229 f g s => @lem4878469 _112226 _112228 _112229 f g s h0). Qed.
Lemma lem4878471 {_112226 _112228 _112229 : Type'} (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : term83 _112226 _112228 _112229 f g s.
Proof. exact (EQ_MP (@lem4877103 _112226 _112228 _112229 f g s) (@lem4878470 _112226 _112228 _112229 f g s)). Qed.
Lemma lem4878472 {_112226 _112228 _112229 : Type'} (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : term10 _112226 _112228 _112229 f g s.
Proof. exact (EQ_MP (@lem4877099 _112226 _112228 _112229 f g s) (@lem4878471 _112226 _112228 _112229 f g s)). Qed.
Lemma lem4878474 {_90072 : Type'} (s : type686 _90072) : term325 _90072 s.
Proof. exact (@lem3472199 _90072 s). Qed.
Lemma lem4878475 {_90072 : Type'} (s : type686 _90072) : (term325 _90072 s) = ((@INTERS _90072 s) = (term326 _90072 s)).
Proof. exact (eq_refl (term325 _90072 s)). Qed.
Lemma lem4878477 {_90107 : Type'} (s : type686 _90107) : term327 _90107 s.
Proof. exact (@lem3473248 _90107 s). Qed.
Lemma lem4878478 {_90107 : Type'} (s : type686 _90107) : (term327 _90107 s) = ((@UNIONS _90107 s) = (term328 _90107 s)).
Proof. exact (eq_refl (term327 _90107 s)). Qed.
Lemma lem4878480 {A : Type'} (P : type180 A) : term329 A P.
Proof. exact (@lem4842239 A P). Qed.
Lemma lem4878481 {A : Type'} (P : type180 A) : (term329 A P) = (term330 A P).
Proof. exact (eq_refl (term329 A P)). Qed.
Lemma lem4878482 {A : Type'} (P : type180 A) : term330 A P.
Proof. exact (EQ_MP (@lem4878481 A P) (@lem4878480 A P)). Qed.
Lemma lem4878483 {A : Type'} (P : type180 A) (Q : type686 A) : term331 A P Q.
Proof. exact (@lem4878482 A P Q). Qed.
Lemma lem4878484 {A : Type'} (P : type180 A) (Q : type686 A) : (term331 A P Q) = ((@INTERSECTION_OF A P Q) = (term332 A P Q)).
Proof. exact (eq_refl (term331 A P Q)). Qed.
Lemma lem4878486 {A : Type'} (P : type180 A) : term333 A P.
Proof. exact (@lem4841086 A P). Qed.
Lemma lem4878487 {A : Type'} (P : type180 A) : (term333 A P) = (term334 A P).
Proof. exact (eq_refl (term333 A P)). Qed.
Lemma lem4878488 {A : Type'} (P : type180 A) : term334 A P.
Proof. exact (EQ_MP (@lem4878487 A P) (@lem4878486 A P)). Qed.
Lemma lem4878489 {A : Type'} (P : type180 A) (Q : type686 A) : term335 A P Q.
Proof. exact (@lem4878488 A P Q). Qed.
Lemma lem4878490 {A : Type'} (P : type180 A) (Q : type686 A) : (term335 A P Q) = ((@UNION_OF A P Q) = (term336 A P Q)).
Proof. exact (eq_refl (term335 A P Q)). Qed.
Lemma lem4878495 {A : Type'} (P : type180 A) (Q : type686 A) : (@UNION_OF A P Q) = (term336 A P Q).
Proof. exact (EQ_MP (@lem4878490 A P Q) (@lem4878489 A P Q)). Qed.
Lemma lem4878496 {A : Type'} (P : type180 A) (Q : type686 A) : (@UNION_OF A P Q) = (term336 A P Q).
Proof. exact (@lem4878495 A P Q). Qed.
Lemma lem4878497 {A : Type'} (P : type686 A) : (@UNION_OF A (@FINITE (A -> Prop)) P) = (term337 A P).
Proof. exact (@lem4878496 A (@FINITE (A -> Prop)) P). Qed.
Lemma lem4878514 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4878515 {A : Type'} (P : type686 A) (s : A -> Prop) : (@UNION_OF A (@FINITE (A -> Prop)) P s) = (term338 A P s).
Proof. exact (MK_COMB (@lem4878497 A P) (@lem4878514 A s)). Qed.
Lemma lem4878517 {A B : Type'} (f : A -> B) (y : A) : (term25 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4878518 {A : Type'} (f : type686 A) (y : A -> Prop) : (term339 A f y) = (f y).
Proof. exact (@lem4878517 (A -> Prop) Prop f y). Qed.
Lemma lem4878519 {A : Type'} (P : type686 A) (s : A -> Prop) : (term340 A P s) = (term338 A P s).
Proof. exact (@lem4878518 A (term337 A P) s). Qed.
Lemma lem4878520 {A : Type'} (P : type686 A) (s : A -> Prop) : (term338 A P s) = (term341 A P s).
Proof. exact (eq_refl (term338 A P s)). Qed.
Lemma lem4878521 {A : Type'} (P : type686 A) : (term342 A P) = (term337 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4878520 A P s)). Qed.
Lemma lem4878522 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4878523 {A : Type'} (P : type686 A) (s : A -> Prop) : (term340 A P s) = (term338 A P s).
Proof. exact (MK_COMB (@lem4878521 A P) (@lem4878522 A s)). Qed.
Lemma lem4878524 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4878525 {A : Type'} (P : type686 A) (s : A -> Prop) : (term343 A P s) = (term344 A P s).
Proof. exact (MK_COMB (@lem4878524) (@lem4878523 A P s)). Qed.
Lemma lem4878526 {A : Type'} (P : type686 A) (s : A -> Prop) : (term338 A P s) = (term341 A P s).
Proof. exact (eq_refl (term338 A P s)). Qed.
Lemma lem4878527 {A : Type'} (P : type686 A) (s : A -> Prop) : ((term340 A P s) = (term338 A P s)) = ((term338 A P s) = (term341 A P s)).
Proof. exact (MK_COMB (@lem4878525 A P s) (@lem4878526 A P s)). Qed.
Lemma lem4878528 {A : Type'} (P : type686 A) (s : A -> Prop) : (term338 A P s) = (term341 A P s).
Proof. exact (EQ_MP (@lem4878527 A P s) (@lem4878519 A P s)). Qed.
Lemma lem4878545 {A : Type'} (P : type686 A) (s : A -> Prop) : (@UNION_OF A (@FINITE (A -> Prop)) P s) = (term341 A P s).
Proof. exact (TRANS (@lem4878515 A P s) (@lem4878528 A P s)). Qed.
Lemma lem4878546 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4878547 {A : Type'} (P : type686 A) (s : A -> Prop) : (term345 A P s) = (term346 A P s).
Proof. exact (MK_COMB (@lem4878546) (@lem4878545 A P s)). Qed.
Lemma lem4878549 {A : Type'} (P : type180 A) (Q : type686 A) : (@INTERSECTION_OF A P Q) = (term332 A P Q).
Proof. exact (EQ_MP (@lem4878484 A P Q) (@lem4878483 A P Q)). Qed.
Lemma lem4878550 {A : Type'} (P : type180 A) (Q : type686 A) : (@INTERSECTION_OF A P Q) = (term332 A P Q).
Proof. exact (@lem4878549 A P Q). Qed.
Lemma lem4878551 {A : Type'} (P : type686 A) : (term347 A P) = (term348 A P).
Proof. exact (@lem4878550 A (@FINITE (A -> Prop)) (term349 A P)). Qed.
Lemma lem4878567 {A B : Type'} (f : A -> B) (y : A) : (term25 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4878568 {A : Type'} (f : type686 A) (y : A -> Prop) : (term339 A f y) = (f y).
Proof. exact (@lem4878567 (A -> Prop) Prop f y). Qed.
Lemma lem4878569 {A : Type'} (P : type686 A) (c : A -> Prop) : (term350 A P c) = (term351 A P c).
Proof. exact (@lem4878568 A (term349 A P) c). Qed.
Lemma lem4878570 {A : Type'} (P : type686 A) (s : A -> Prop) : (term351 A P s) = (term352 A P s).
Proof. exact (eq_refl (term351 A P s)). Qed.
Lemma lem4878571 {A : Type'} (P : type686 A) : (term353 A P) = (term349 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4878570 A P s)). Qed.
Lemma lem4878572 {A : Type'} (c : A -> Prop) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem4878573 {A : Type'} (P : type686 A) (c : A -> Prop) : (term350 A P c) = (term351 A P c).
Proof. exact (MK_COMB (@lem4878571 A P) (@lem4878572 A c)). Qed.
Lemma lem4878574 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4878575 {A : Type'} (P : type686 A) (c : A -> Prop) : (term354 A P c) = (term355 A P c).
Proof. exact (MK_COMB (@lem4878574) (@lem4878573 A P c)). Qed.
Lemma lem4878576 {A : Type'} (P : type686 A) (c : A -> Prop) : (term351 A P c) = (term352 A P c).
Proof. exact (eq_refl (term351 A P c)). Qed.
Lemma lem4878577 {A : Type'} (P : type686 A) (c : A -> Prop) : ((term350 A P c) = (term351 A P c)) = ((term351 A P c) = (term352 A P c)).
Proof. exact (MK_COMB (@lem4878575 A P c) (@lem4878576 A P c)). Qed.
Lemma lem4878578 {A : Type'} (P : type686 A) (c : A -> Prop) : (term351 A P c) = (term352 A P c).
Proof. exact (EQ_MP (@lem4878577 A P c) (@lem4878569 A P c)). Qed.
Lemma lem4878579 {A : Type'} (c : A -> Prop) (u : type686 A) : (term356 A c u) = (term356 A c u).
Proof. exact (eq_refl (term356 A c u)). Qed.
Lemma lem4878580 {A : Type'} (u : type686 A) (P : type686 A) (c : A -> Prop) : (term357 A u P c) = (term358 A u P c).
Proof. exact (MK_COMB (@lem4878579 A c u) (@lem4878578 A P c)). Qed.
Lemma lem4878583 {A : Type'} (u : type686 A) (P : type686 A) : (term359 A u P) = (term360 A u P).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4878580 A u P c)). Qed.
Lemma lem4878584 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4878585 {A : Type'} (u : type686 A) (P : type686 A) : (term361 A u P) = (term362 A u P).
Proof. exact (MK_COMB (@lem4878584 A) (@lem4878583 A u P)). Qed.
Lemma lem4878590 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4878591 {A : Type'} (u : type686 A) (P : type686 A) : (term363 A u P) = (term364 A u P).
Proof. exact (MK_COMB (@lem4878590) (@lem4878585 A u P)). Qed.
Lemma lem4878594 {A : Type'} (u : type686 A) (s : A -> Prop) : ((@INTERS A u) = s) = ((@INTERS A u) = s).
Proof. exact (eq_refl ((@INTERS A u) = s)). Qed.
Lemma lem4878595 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) : (term365 A P u s) = (term366 A P u s).
Proof. exact (MK_COMB (@lem4878591 A u P) (@lem4878594 A u s)). Qed.
Lemma lem4878598 {A : Type'} (u : type686 A) : (term367 A u) = (term367 A u).
Proof. exact (eq_refl (term367 A u)). Qed.
Lemma lem4878599 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) : (term368 A P u s) = (term369 A P u s).
Proof. exact (MK_COMB (@lem4878598 A u) (@lem4878595 A P u s)). Qed.
Lemma lem4878602 {A : Type'} (P : type686 A) (s : A -> Prop) : (term370 A P s) = (term371 A P s).
Proof. exact (fun_ext (fun u : type686 A => @lem4878599 A P u s)). Qed.
Lemma lem4878603 {A : Type'} : (@ex ((A -> Prop) -> Prop)) = (@ex ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> Prop))). Qed.
Lemma lem4878604 {A : Type'} (P : type686 A) (s : A -> Prop) : (term372 A P s) = (term373 A P s).
Proof. exact (MK_COMB (@lem4878603 A) (@lem4878602 A P s)). Qed.
Lemma lem4878609 {A : Type'} (P : type686 A) : (term348 A P) = (term374 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4878604 A P s)). Qed.
Lemma lem4878610 {A : Type'} (P : type686 A) : (term347 A P) = (term374 A P).
Proof. exact (TRANS (@lem4878551 A P) (@lem4878609 A P)). Qed.
Lemma lem4878611 {A : Type'} (s : A -> Prop) : (@DIFF A (@UNIV A) s) = (@DIFF A (@UNIV A) s).
Proof. exact (eq_refl (@DIFF A (@UNIV A) s)). Qed.
Lemma lem4878612 {A : Type'} (P : type686 A) (s : A -> Prop) : (term375 A P s) = (term376 A P s).
Proof. exact (MK_COMB (@lem4878610 A P) (@lem4878611 A s)). Qed.
Lemma lem4878614 {A B : Type'} (f : A -> B) (y : A) : (term25 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4878615 {A : Type'} (f : type686 A) (y : A -> Prop) : (term339 A f y) = (f y).
Proof. exact (@lem4878614 (A -> Prop) Prop f y). Qed.
Lemma lem4878616 {A : Type'} (P : type686 A) (s : A -> Prop) : (term377 A P s) = (term376 A P s).
Proof. exact (@lem4878615 A (term374 A P) (@DIFF A (@UNIV A) s)). Qed.
Lemma lem4878617 {A : Type'} (P : type686 A) (s : A -> Prop) : (term378 A P s) = (term373 A P s).
Proof. exact (eq_refl (term378 A P s)). Qed.
Lemma lem4878618 {A : Type'} (P : type686 A) : (term379 A P) = (term374 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4878617 A P s)). Qed.
Lemma lem4878619 {A : Type'} (s : A -> Prop) : (@DIFF A (@UNIV A) s) = (@DIFF A (@UNIV A) s).
Proof. exact (eq_refl (@DIFF A (@UNIV A) s)). Qed.
Lemma lem4878620 {A : Type'} (P : type686 A) (s : A -> Prop) : (term377 A P s) = (term376 A P s).
Proof. exact (MK_COMB (@lem4878618 A P) (@lem4878619 A s)). Qed.
Lemma lem4878621 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4878622 {A : Type'} (P : type686 A) (s : A -> Prop) : (term380 A P s) = (term381 A P s).
Proof. exact (MK_COMB (@lem4878621) (@lem4878620 A P s)). Qed.
Lemma lem4878623 {A : Type'} (P : type686 A) (s : A -> Prop) : (term376 A P s) = (term382 A P s).
Proof. exact (eq_refl (term376 A P s)). Qed.
Lemma lem4878624 {A : Type'} (P : type686 A) (s : A -> Prop) : ((term377 A P s) = (term376 A P s)) = ((term376 A P s) = (term382 A P s)).
Proof. exact (MK_COMB (@lem4878622 A P s) (@lem4878623 A P s)). Qed.
Lemma lem4878625 {A : Type'} (P : type686 A) (s : A -> Prop) : (term376 A P s) = (term382 A P s).
Proof. exact (EQ_MP (@lem4878624 A P s) (@lem4878616 A P s)). Qed.
Lemma lem4878642 {A : Type'} (P : type686 A) (s : A -> Prop) : (term375 A P s) = (term382 A P s).
Proof. exact (TRANS (@lem4878612 A P s) (@lem4878625 A P s)). Qed.
Lemma lem4878643 {A : Type'} (P : type686 A) (s : A -> Prop) : ((@UNION_OF A (@FINITE (A -> Prop)) P s) = (term375 A P s)) = ((term341 A P s) = (term382 A P s)).
Proof. exact (MK_COMB (@lem4878547 A P s) (@lem4878642 A P s)). Qed.
Lemma lem4878646 {A : Type'} (P : type686 A) (s : A -> Prop) : ((term341 A P s) = (term382 A P s)) = ((@UNION_OF A (@FINITE (A -> Prop)) P s) = (term375 A P s)).
Proof. exact (SYM (@lem4878643 A P s)). Qed.
Lemma lem4878647 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term341 A P s) : term341 A P s.
Proof. exact (h1). Qed.
Lemma lem4878648 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term383 A P u s) : term383 A P u s.
Proof. exact (h1). Qed.
Lemma lem4878649 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term384 A P u s) : term384 A P u s.
Proof. exact (h1). Qed.
Lemma lem4878650 {A : Type'} (u : type686 A) (h1 : @FINITE (A -> Prop) u) : @FINITE (A -> Prop) u.
Proof. exact (h1). Qed.
Lemma lem4878651 {A : Type'} (u : type686 A) (s : A -> Prop) (h1 : (@UNIONS A u) = s) : (@UNIONS A u) = s.
Proof. exact (h1). Qed.
Lemma lem4878652 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term385 A u P) : term385 A u P.
Proof. exact (h1). Qed.
Lemma lem4878653 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term382 A P s) : term382 A P s.
Proof. exact (h1). Qed.
Lemma lem4878654 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term386 A P u s) : term386 A P u s.
Proof. exact (h1). Qed.
Lemma lem4878655 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term387 A P u s) : term387 A P u s.
Proof. exact (h1). Qed.
Lemma lem4878656 {A : Type'} (u : type686 A) (h1 : @FINITE (A -> Prop) u) : @FINITE (A -> Prop) u.
Proof. exact (h1). Qed.
Lemma lem4878657 {A : Type'} (u : type686 A) (s : A -> Prop) (h1 : (@INTERS A u) = (@DIFF A (@UNIV A) s)) : (@INTERS A u) = (@DIFF A (@UNIV A) s).
Proof. exact (h1). Qed.
Lemma lem4878658 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term362 A u P) : term362 A u P.
Proof. exact (h1). Qed.
Lemma lem4878659 {A : Type'} (s : A -> Prop) : term388 A s.
Proof. exact (@lem3270825 A s). Qed.
Lemma lem4878660 {A : Type'} (s : A -> Prop) : (term388 A s) = ((term389 A s) = s).
Proof. exact (eq_refl (term388 A s)). Qed.
Lemma lem4878662 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : term390 _87967 _87968 P f.
Proof. exact (@lem3386920 _87967 _87968 P f). Qed.
Lemma lem4878663 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : (term390 _87967 _87968 P f) = (term391 _87967 _87968 P f).
Proof. exact (eq_refl (term390 _87967 _87968 P f)). Qed.
Lemma lem4878664 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : term391 _87967 _87968 P f.
Proof. exact (EQ_MP (@lem4878663 _87967 _87968 P f) (@lem4878662 _87967 _87968 P f)). Qed.
Lemma lem4878665 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) (s : _87968 -> Prop) : term392 _87967 _87968 P f s.
Proof. exact (@lem4878664 _87967 _87968 P f s). Qed.
Lemma lem4878666 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term392 _87967 _87968 P f s) = ((term393 _87967 _87968 f s P) = (term394 _87967 _87968 s P f)).
Proof. exact (eq_refl (term392 _87967 _87968 P f s)). Qed.
Lemma lem4878668 {A B : Type'} (f : A -> B) : term395 A B f.
Proof. exact (@lem3615104 A B f). Qed.
Lemma lem4878669 {A B : Type'} (f : A -> B) : (term395 A B f) = (term396 A B f).
Proof. exact (eq_refl (term395 A B f)). Qed.
Lemma lem4878670 {A B : Type'} (f : A -> B) : term396 A B f.
Proof. exact (EQ_MP (@lem4878669 A B f) (@lem4878668 A B f)). Qed.
Lemma lem4878671 {A B : Type'} (f : A -> B) (s : A -> Prop) : term397 A B f s.
Proof. exact (@lem4878670 A B f s). Qed.
Lemma lem4878672 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term397 A B f s) = (term398 A B f s).
Proof. exact (eq_refl (term397 A B f s)). Qed.
Lemma lem4878673 {A B : Type'} (f : A -> B) (s : A -> Prop) : term398 A B f s.
Proof. exact (EQ_MP (@lem4878672 A B f s) (@lem4878671 A B f s)). Qed.
Lemma lem4878674 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem4878675 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : term399 A B f s.
Proof. exact (@lem4878673 A B f s (@lem4878674 A s h1)). Qed.
Lemma lem4878676 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term399 A B f s) = ((term399 A B f s) = True).
Proof. exact (@lem7 (term399 A B f s)). Qed.
Lemma lem4878677 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : (term399 A B f s) = True.
Proof. exact (EQ_MP (@lem4878676 A B f s) (@lem4878675 A B f s h1)). Qed.
Lemma lem4878683 {A : Type'} (u : type686 A) : (@FINITE (A -> Prop) u) = ((@FINITE (A -> Prop) u) = True).
Proof. exact (@lem7 (@FINITE (A -> Prop) u)). Qed.
Lemma lem4878685 {A : Type'} (c : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term385 A u P) : term400 A u P c.
Proof. exact (@lem4878652 A u P h1 c). Qed.
Lemma lem4878686 {A : Type'} (u : type686 A) (P : type686 A) (c : A -> Prop) : (term400 A u P c) = (term401 A u P c).
Proof. exact (eq_refl (term400 A u P c)). Qed.
Lemma lem4878687 {A : Type'} (c : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term385 A u P) : term401 A u P c.
Proof. exact (EQ_MP (@lem4878686 A u P c) (@lem4878685 A c u P h1)). Qed.
Lemma lem4878688 {A : Type'} (c : A -> Prop) (u : type686 A) (h1 : @IN (A -> Prop) c u) : @IN (A -> Prop) c u.
Proof. exact (h1). Qed.
Lemma lem4878689 {A : Type'} (P : type686 A) (c : A -> Prop) (u : type686 A) (h1 : term385 A u P) (h2 : @IN (A -> Prop) c u) : P c.
Proof. exact (@lem4878687 A c u P h1 (@lem4878688 A c u h2)). Qed.
Lemma lem4878690 {A : Type'} (P : type686 A) (c : A -> Prop) : (P c) = ((P c) = True).
Proof. exact (@lem7 (P c)). Qed.
Lemma lem4878691 {A : Type'} (P : type686 A) (c : A -> Prop) (u : type686 A) (h1 : term385 A u P) (h2 : @IN (A -> Prop) c u) : (P c) = True.
Proof. exact (EQ_MP (@lem4878690 A P c) (@lem4878689 A P c u h1 h2)). Qed.
Lemma lem4878700 {A B : Type'} (f : A -> B) (s : A -> Prop) : term402 A B f s.
Proof. exact (fun h0 : @FINITE A s => @lem4878677 A B f s h0). Qed.
Lemma lem4878701 {A : Type'} (f : type672 A) (s : type686 A) : term403 A f s.
Proof. exact (@lem4878700 (A -> Prop) (A -> Prop) f s). Qed.
Lemma lem4878702 {A : Type'} (u : type686 A) : term404 A u.
Proof. exact (@lem4878701 A (term405 A) u). Qed.
Lemma lem4878704 {A : Type'} (u : type686 A) (h1 : @FINITE (A -> Prop) u) : (@FINITE (A -> Prop) u) = True.
Proof. exact (EQ_MP (@lem4878683 A u) (@lem4878650 A u h1)). Qed.
Lemma lem4878705 {A : Type'} (u : type686 A) (h1 : @FINITE (A -> Prop) u) : True = (@FINITE (A -> Prop) u).
Proof. exact (SYM (@lem4878704 A u h1)). Qed.
Lemma lem4878706 {A : Type'} (u : type686 A) (h1 : @FINITE (A -> Prop) u) : @FINITE (A -> Prop) u.
Proof. exact (EQ_MP (@lem4878705 A u h1) (@lem0)). Qed.
Lemma lem4878707 {A : Type'} (u : type686 A) (h1 : @FINITE (A -> Prop) u) : (term406 A u) = True.
Proof. exact (@lem4878702 A u (@lem4878706 A u h1)). Qed.
Lemma lem4878708 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4878709 {A : Type'} (u : type686 A) (h1 : @FINITE (A -> Prop) u) : (term407 A u) = (and True).
Proof. exact (MK_COMB (@lem4878708) (@lem4878707 A u h1)). Qed.
Lemma lem4878713 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term393 _87967 _87968 f s P) = (term394 _87967 _87968 s P f).
Proof. exact (EQ_MP (@lem4878666 _87967 _87968 s P f) (@lem4878665 _87967 _87968 P f s)). Qed.
Lemma lem4878714 {A : Type'} (s : type686 A) (P : type686 A) (f : type672 A) : (term408 A f s P) = (term409 A s P f).
Proof. exact (@lem4878713 (A -> Prop) (A -> Prop) s P f). Qed.
Lemma lem4878715 {A : Type'} (u : type686 A) (P : type686 A) : (term410 A u P) = (term411 A u P).
Proof. exact (@lem4878714 A u (term349 A P) (term405 A)). Qed.
Lemma lem4878716 {A : Type'} (P : type686 A) (c : A -> Prop) : (term351 A P c) = (term352 A P c).
Proof. exact (eq_refl (term351 A P c)). Qed.
Lemma lem4878717 {A : Type'} (c : A -> Prop) (u : type686 A) : (term412 A c u) = (term412 A c u).
Proof. exact (eq_refl (term412 A c u)). Qed.
Lemma lem4878718 {A : Type'} (u : type686 A) (P : type686 A) (c : A -> Prop) : (term413 A u P c) = (term414 A u P c).
Proof. exact (MK_COMB (@lem4878717 A c u) (@lem4878716 A P c)). Qed.
Lemma lem4878719 {A : Type'} (u : type686 A) (P : type686 A) : (term415 A u P) = (term416 A u P).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4878718 A u P c)). Qed.
Lemma lem4878720 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4878721 {A : Type'} (u : type686 A) (P : type686 A) : (term410 A u P) = (term417 A u P).
Proof. exact (MK_COMB (@lem4878720 A) (@lem4878719 A u P)). Qed.
Lemma lem4878722 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4878723 {A : Type'} (u : type686 A) (P : type686 A) : (term418 A u P) = (term419 A u P).
Proof. exact (MK_COMB (@lem4878722) (@lem4878721 A u P)). Qed.
Lemma lem4878724 {A : Type'} (P : type686 A) (x : A -> Prop) : (term420 A P x) = (term421 A P x).
Proof. exact (eq_refl (term420 A P x)). Qed.
Lemma lem4878725 {A : Type'} (x : A -> Prop) (u : type686 A) : (term356 A x u) = (term356 A x u).
Proof. exact (eq_refl (term356 A x u)). Qed.
Lemma lem4878726 {A : Type'} (u : type686 A) (P : type686 A) (x : A -> Prop) : (term422 A u P x) = (term423 A u P x).
Proof. exact (MK_COMB (@lem4878725 A x u) (@lem4878724 A P x)). Qed.
Lemma lem4878727 {A : Type'} (u : type686 A) (P : type686 A) : (term424 A u P) = (term425 A u P).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4878726 A u P x)). Qed.
Lemma lem4878728 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4878729 {A : Type'} (u : type686 A) (P : type686 A) : (term411 A u P) = (term426 A u P).
Proof. exact (MK_COMB (@lem4878728 A) (@lem4878727 A u P)). Qed.
Lemma lem4878730 {A : Type'} (u : type686 A) (P : type686 A) : ((term410 A u P) = (term411 A u P)) = ((term417 A u P) = (term426 A u P)).
Proof. exact (MK_COMB (@lem4878723 A u P) (@lem4878729 A u P)). Qed.
Lemma lem4878731 {A : Type'} (u : type686 A) (P : type686 A) : (term417 A u P) = (term426 A u P).
Proof. exact (EQ_MP (@lem4878730 A u P) (@lem4878715 A u P)). Qed.
Lemma lem4878739 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term427 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4878740 (p : Prop) (q : Prop) (p' : Prop) : term428 p q p'.
Proof. exact (fun q' : Prop => @lem4878739 p q p' q'). Qed.
Lemma lem4878741 (p : Prop) (q : Prop) : term429 p q.
Proof. exact (fun p' : Prop => @lem4878740 p q p'). Qed.
Lemma lem4878742 {A : Type'} (u : type686 A) (P : type686 A) (x : A -> Prop) : term430 A u P x.
Proof. exact (@lem4878741 (@IN (A -> Prop) x u) (term421 A P x)). Qed.
Lemma lem4878743 {A : Type'} (u : type686 A) (P : type686 A) (x : A -> Prop) (p' : Prop) : term431 A u P x p'.
Proof. exact (@lem4878742 A u P x p'). Qed.
Lemma lem4878744 {A : Type'} (u : type686 A) (P : type686 A) (x : A -> Prop) (p' : Prop) : (term431 A u P x p') = (term432 A u P x p').
Proof. exact (eq_refl (term431 A u P x p')). Qed.
Lemma lem4878745 {A : Type'} (u : type686 A) (P : type686 A) (x : A -> Prop) (p' : Prop) : term432 A u P x p'.
Proof. exact (EQ_MP (@lem4878744 A u P x p') (@lem4878743 A u P x p')). Qed.
Lemma lem4878746 {A : Type'} (u : type686 A) (P : type686 A) (x : A -> Prop) (p' : Prop) (q' : Prop) : term433 A u P x p' q'.
Proof. exact (@lem4878745 A u P x p' q'). Qed.
Lemma lem4878747 {A : Type'} (u : type686 A) (P : type686 A) (x : A -> Prop) (p' : Prop) (q' : Prop) : (term433 A u P x p' q') = (term434 A u P x p' q').
Proof. exact (eq_refl (term433 A u P x p' q')). Qed.
Lemma lem4878748 {A : Type'} (u : type686 A) (P : type686 A) (x : A -> Prop) (p' : Prop) (q' : Prop) : term434 A u P x p' q'.
Proof. exact (EQ_MP (@lem4878747 A u P x p' q') (@lem4878746 A u P x p' q')). Qed.
Lemma lem4878749 {A : Type'} (x : A -> Prop) (u : type686 A) : (@IN (A -> Prop) x u) = (@IN (A -> Prop) x u).
Proof. exact (eq_refl (@IN (A -> Prop) x u)). Qed.
Lemma lem4878750 {A : Type'} (P : type686 A) (x : A -> Prop) (u : type686 A) (q' : Prop) : term435 A P x u q'.
Proof. exact (@lem4878748 A u P x (@IN (A -> Prop) x u) q'). Qed.
Lemma lem4878751 {A : Type'} (P : type686 A) (x : A -> Prop) (u : type686 A) (q' : Prop) : term436 A P x u q'.
Proof. exact (@lem4878750 A P x u q' (@lem4878749 A x u)). Qed.
Lemma lem4878752 {A : Type'} (x : A -> Prop) (u : type686 A) (h1 : @IN (A -> Prop) x u) : @IN (A -> Prop) x u.
Proof. exact (h1). Qed.
Lemma lem4878753 {A : Type'} (x : A -> Prop) (u : type686 A) : (@IN (A -> Prop) x u) = ((@IN (A -> Prop) x u) = True).
Proof. exact (@lem7 (@IN (A -> Prop) x u)). Qed.
Lemma lem4878756 {A : Type'} (c : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term385 A u P) : term437 A u P c.
Proof. exact (fun h0 : @IN (A -> Prop) c u => @lem4878691 A P c u h1 h0). Qed.
Lemma lem4878757 {A : Type'} (c : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term385 A u P) : term437 A u P c.
Proof. exact (@lem4878756 A c u P h1). Qed.
Lemma lem4878758 {A : Type'} (x : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term385 A u P) : term438 A u P x.
Proof. exact (@lem4878757 A (term439 A x) u P h1). Qed.
Lemma lem4878760 {A B : Type'} (f : A -> B) (y : A) : (term25 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4878761 {A : Type'} (f : type672 A) (y : A -> Prop) : (term440 A f y) = (f y).
Proof. exact (@lem4878760 (A -> Prop) (A -> Prop) f y). Qed.
Lemma lem4878762 {A : Type'} (x : A -> Prop) : (term441 A x) = (term442 A x).
Proof. exact (@lem4878761 A (term405 A) x). Qed.
Lemma lem4878763 {A : Type'} (c : A -> Prop) : (term442 A c) = (@DIFF A (@UNIV A) c).
Proof. exact (eq_refl (term442 A c)). Qed.
Lemma lem4878764 {A : Type'} : (term443 A) = (term405 A).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4878763 A c)). Qed.
Lemma lem4878765 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4878766 {A : Type'} (x : A -> Prop) : (term441 A x) = (term442 A x).
Proof. exact (MK_COMB (@lem4878764 A) (@lem4878765 A x)). Qed.
Lemma lem4878767 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4878768 {A : Type'} (x : A -> Prop) : (term444 A x) = (term445 A x).
Proof. exact (MK_COMB (@lem4878767 A) (@lem4878766 A x)). Qed.
Lemma lem4878769 {A : Type'} (x : A -> Prop) : (term442 A x) = (@DIFF A (@UNIV A) x).
Proof. exact (eq_refl (term442 A x)). Qed.
Lemma lem4878770 {A : Type'} (x : A -> Prop) : ((term441 A x) = (term442 A x)) = ((term442 A x) = (@DIFF A (@UNIV A) x)).
Proof. exact (MK_COMB (@lem4878768 A x) (@lem4878769 A x)). Qed.
Lemma lem4878771 {A : Type'} (x : A -> Prop) : (term442 A x) = (@DIFF A (@UNIV A) x).
Proof. exact (EQ_MP (@lem4878770 A x) (@lem4878762 A x)). Qed.
Lemma lem4878772 {A : Type'} : (@DIFF A (@UNIV A)) = (@DIFF A (@UNIV A)).
Proof. exact (eq_refl (@DIFF A (@UNIV A))). Qed.
Lemma lem4878773 {A : Type'} (x : A -> Prop) : (term439 A x) = (term389 A x).
Proof. exact (MK_COMB (@lem4878772 A) (@lem4878771 A x)). Qed.
Lemma lem4878775 {A : Type'} (s : A -> Prop) : (term389 A s) = s.
Proof. exact (EQ_MP (@lem4878660 A s) (@lem4878659 A s)). Qed.
Lemma lem4878776 {A : Type'} (s : A -> Prop) : (term389 A s) = s.
Proof. exact (@lem4878775 A s). Qed.
Lemma lem4878777 {A : Type'} (x : A -> Prop) : (term389 A x) = x.
Proof. exact (@lem4878776 A x). Qed.
Lemma lem4878778 {A : Type'} (x : A -> Prop) : (term439 A x) = x.
Proof. exact (TRANS (@lem4878773 A x) (@lem4878777 A x)). Qed.
Lemma lem4878779 {A : Type'} : (@IN (A -> Prop)) = (@IN (A -> Prop)).
Proof. exact (eq_refl (@IN (A -> Prop))). Qed.
Lemma lem4878780 {A : Type'} (x : A -> Prop) : (term446 A x) = (@IN (A -> Prop) x).
Proof. exact (MK_COMB (@lem4878779 A) (@lem4878778 A x)). Qed.
Lemma lem4878781 {A : Type'} (u : type686 A) : u = u.
Proof. exact (eq_refl u). Qed.
Lemma lem4878782 {A : Type'} (x : A -> Prop) (u : type686 A) : (term447 A x u) = (@IN (A -> Prop) x u).
Proof. exact (MK_COMB (@lem4878780 A x) (@lem4878781 A u)). Qed.
Lemma lem4878784 {A : Type'} (x : A -> Prop) (u : type686 A) (h1 : @IN (A -> Prop) x u) : (@IN (A -> Prop) x u) = True.
Proof. exact (EQ_MP (@lem4878753 A x u) (@lem4878752 A x u h1)). Qed.
Lemma lem4878785 {A : Type'} (x : A -> Prop) (u : type686 A) (h1 : @IN (A -> Prop) x u) : (term447 A x u) = True.
Proof. exact (TRANS (@lem4878782 A x u) (@lem4878784 A x u h1)). Qed.
Lemma lem4878786 {A : Type'} (x : A -> Prop) (u : type686 A) (h1 : @IN (A -> Prop) x u) : True = (term447 A x u).
Proof. exact (SYM (@lem4878785 A x u h1)). Qed.
Lemma lem4878787 {A : Type'} (x : A -> Prop) (u : type686 A) (h1 : @IN (A -> Prop) x u) : term447 A x u.
Proof. exact (EQ_MP (@lem4878786 A x u h1) (@lem0)). Qed.
Lemma lem4878788 {A : Type'} (P : type686 A) (x : A -> Prop) (u : type686 A) (h1 : term385 A u P) (h2 : @IN (A -> Prop) x u) : (term421 A P x) = True.
Proof. exact (@lem4878758 A x u P h1 (@lem4878787 A x u h2)). Qed.
Lemma lem4878789 {A : Type'} (x : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term385 A u P) : term448 A u P x.
Proof. exact (fun h0 : @IN (A -> Prop) x u => @lem4878788 A P x u h1 h0). Qed.
Lemma lem4878790 {A : Type'} (P : type686 A) (x : A -> Prop) (u : type686 A) : term449 A P x u.
Proof. exact (@lem4878751 A P x u True). Qed.
Lemma lem4878791 {A : Type'} (x : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term385 A u P) : (term423 A u P x) = (term450 A x u).
Proof. exact (@lem4878790 A P x u (@lem4878789 A x u P h1)). Qed.
Lemma lem4878793 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem4878794 {A : Type'} (x : A -> Prop) (u : type686 A) : (term450 A x u) = True.
Proof. exact (@lem4878793 (@IN (A -> Prop) x u)). Qed.
Lemma lem4878795 {A : Type'} (x : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term385 A u P) : (term423 A u P x) = True.
Proof. exact (TRANS (@lem4878791 A x u P h1) (@lem4878794 A x u)). Qed.
Lemma lem4878796 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term385 A u P) : (term425 A u P) = (term451 A).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4878795 A x u P h1)). Qed.
Lemma lem4878797 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4878798 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term385 A u P) : (term426 A u P) = (term452 A).
Proof. exact (MK_COMB (@lem4878797 A) (@lem4878796 A u P h1)). Qed.
Lemma lem4878800 {A : Type'} (t : Prop) : (term453 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4878801 {A : Type'} (t : Prop) : (term454 A t) = t.
Proof. exact (@lem4878800 (A -> Prop) t). Qed.
Lemma lem4878802 {A : Type'} : (term452 A) = True.
Proof. exact (@lem4878801 A True). Qed.
Lemma lem4878803 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term385 A u P) : (term426 A u P) = True.
Proof. exact (TRANS (@lem4878798 A u P h1) (@lem4878802 A)). Qed.
Lemma lem4878804 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term385 A u P) : (term417 A u P) = True.
Proof. exact (TRANS (@lem4878731 A u P) (@lem4878803 A u P h1)). Qed.
Lemma lem4878805 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4878806 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term385 A u P) : (term455 A u P) = (and True).
Proof. exact (MK_COMB (@lem4878805) (@lem4878804 A u P h1)). Qed.
Lemma lem4878809 {A : Type'} (u : type686 A) (s : A -> Prop) : ((term456 A u) = (@DIFF A (@UNIV A) s)) = ((term456 A u) = (@DIFF A (@UNIV A) s)).
Proof. exact (eq_refl ((term456 A u) = (@DIFF A (@UNIV A) s))). Qed.
Lemma lem4878810 {A : Type'} (s : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term385 A u P) : (term457 A P u s) = (term458 A u s).
Proof. exact (MK_COMB (@lem4878806 A u P h1) (@lem4878809 A u s)). Qed.
Lemma lem4878812 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4878813 {A : Type'} (u : type686 A) (s : A -> Prop) : (term458 A u s) = ((term456 A u) = (@DIFF A (@UNIV A) s)).
Proof. exact (@lem4878812 ((term456 A u) = (@DIFF A (@UNIV A) s))). Qed.
Lemma lem4878816 {A : Type'} (s : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term385 A u P) : (term457 A P u s) = ((term456 A u) = (@DIFF A (@UNIV A) s)).
Proof. exact (TRANS (@lem4878810 A s u P h1) (@lem4878813 A u s)). Qed.
Lemma lem4878817 {A : Type'} (s : A -> Prop) (P : type686 A) (u : type686 A) (h1 : term385 A u P) (h2 : @FINITE (A -> Prop) u) : (term459 A P u s) = (term458 A u s).
Proof. exact (MK_COMB (@lem4878709 A u h2) (@lem4878816 A s u P h1)). Qed.
Lemma lem4878819 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4878820 {A : Type'} (u : type686 A) (s : A -> Prop) : (term458 A u s) = ((term456 A u) = (@DIFF A (@UNIV A) s)).
Proof. exact (@lem4878819 ((term456 A u) = (@DIFF A (@UNIV A) s))). Qed.
Lemma lem4878823 {A : Type'} (s : A -> Prop) (P : type686 A) (u : type686 A) (h1 : term385 A u P) (h2 : @FINITE (A -> Prop) u) : (term459 A P u s) = ((term456 A u) = (@DIFF A (@UNIV A) s)).
Proof. exact (TRANS (@lem4878817 A s P u h1 h2) (@lem4878820 A u s)). Qed.
Lemma lem4878824 {A : Type'} (s : A -> Prop) (P : type686 A) (u : type686 A) (h1 : term385 A u P) (h2 : @FINITE (A -> Prop) u) : ((term456 A u) = (@DIFF A (@UNIV A) s)) = (term459 A P u s).
Proof. exact (SYM (@lem4878823 A s P u h1 h2)). Qed.
Lemma lem4878828 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : term390 _87967 _87968 P f.
Proof. exact (@lem3386920 _87967 _87968 P f). Qed.
Lemma lem4878829 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : (term390 _87967 _87968 P f) = (term391 _87967 _87968 P f).
Proof. exact (eq_refl (term390 _87967 _87968 P f)). Qed.
Lemma lem4878830 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : term391 _87967 _87968 P f.
Proof. exact (EQ_MP (@lem4878829 _87967 _87968 P f) (@lem4878828 _87967 _87968 P f)). Qed.
Lemma lem4878831 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) (s : _87968 -> Prop) : term392 _87967 _87968 P f s.
Proof. exact (@lem4878830 _87967 _87968 P f s). Qed.
Lemma lem4878832 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term392 _87967 _87968 P f s) = ((term393 _87967 _87968 f s P) = (term394 _87967 _87968 s P f)).
Proof. exact (eq_refl (term392 _87967 _87968 P f s)). Qed.
Lemma lem4878834 {A B : Type'} (f : A -> B) : term395 A B f.
Proof. exact (@lem3615104 A B f). Qed.
Lemma lem4878835 {A B : Type'} (f : A -> B) : (term395 A B f) = (term396 A B f).
Proof. exact (eq_refl (term395 A B f)). Qed.
Lemma lem4878836 {A B : Type'} (f : A -> B) : term396 A B f.
Proof. exact (EQ_MP (@lem4878835 A B f) (@lem4878834 A B f)). Qed.
Lemma lem4878837 {A B : Type'} (f : A -> B) (s : A -> Prop) : term397 A B f s.
Proof. exact (@lem4878836 A B f s). Qed.
Lemma lem4878838 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term397 A B f s) = (term398 A B f s).
Proof. exact (eq_refl (term397 A B f s)). Qed.
Lemma lem4878839 {A B : Type'} (f : A -> B) (s : A -> Prop) : term398 A B f s.
Proof. exact (EQ_MP (@lem4878838 A B f s) (@lem4878837 A B f s)). Qed.
Lemma lem4878840 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem4878841 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : term399 A B f s.
Proof. exact (@lem4878839 A B f s (@lem4878840 A s h1)). Qed.
Lemma lem4878842 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term399 A B f s) = ((term399 A B f s) = True).
Proof. exact (@lem7 (term399 A B f s)). Qed.
Lemma lem4878843 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : (term399 A B f s) = True.
Proof. exact (EQ_MP (@lem4878842 A B f s) (@lem4878841 A B f s h1)). Qed.
Lemma lem4878849 {A : Type'} (u : type686 A) : (@FINITE (A -> Prop) u) = ((@FINITE (A -> Prop) u) = True).
Proof. exact (@lem7 (@FINITE (A -> Prop) u)). Qed.
Lemma lem4878851 {A : Type'} (c : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term362 A u P) : term460 A u P c.
Proof. exact (@lem4878658 A u P h1 c). Qed.
Lemma lem4878852 {A : Type'} (u : type686 A) (P : type686 A) (c : A -> Prop) : (term460 A u P c) = (term358 A u P c).
Proof. exact (eq_refl (term460 A u P c)). Qed.
Lemma lem4878853 {A : Type'} (c : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term362 A u P) : term358 A u P c.
Proof. exact (EQ_MP (@lem4878852 A u P c) (@lem4878851 A c u P h1)). Qed.
Lemma lem4878854 {A : Type'} (c : A -> Prop) (u : type686 A) (h1 : @IN (A -> Prop) c u) : @IN (A -> Prop) c u.
Proof. exact (h1). Qed.
Lemma lem4878855 {A : Type'} (P : type686 A) (c : A -> Prop) (u : type686 A) (h1 : term362 A u P) (h2 : @IN (A -> Prop) c u) : term352 A P c.
Proof. exact (@lem4878853 A c u P h1 (@lem4878854 A c u h2)). Qed.
Lemma lem4878856 {A : Type'} (P : type686 A) (c : A -> Prop) : (term352 A P c) = ((term352 A P c) = True).
Proof. exact (@lem7 (term352 A P c)). Qed.
Lemma lem4878857 {A : Type'} (P : type686 A) (c : A -> Prop) (u : type686 A) (h1 : term362 A u P) (h2 : @IN (A -> Prop) c u) : (term352 A P c) = True.
Proof. exact (EQ_MP (@lem4878856 A P c) (@lem4878855 A P c u h1 h2)). Qed.
Lemma lem4878866 {A B : Type'} (f : A -> B) (s : A -> Prop) : term402 A B f s.
Proof. exact (fun h0 : @FINITE A s => @lem4878843 A B f s h0). Qed.
Lemma lem4878867 {A : Type'} (f : type672 A) (s : type686 A) : term403 A f s.
Proof. exact (@lem4878866 (A -> Prop) (A -> Prop) f s). Qed.
Lemma lem4878868 {A : Type'} (u : type686 A) : term404 A u.
Proof. exact (@lem4878867 A (term405 A) u). Qed.
Lemma lem4878870 {A : Type'} (u : type686 A) (h1 : @FINITE (A -> Prop) u) : (@FINITE (A -> Prop) u) = True.
Proof. exact (EQ_MP (@lem4878849 A u) (@lem4878656 A u h1)). Qed.
Lemma lem4878871 {A : Type'} (u : type686 A) (h1 : @FINITE (A -> Prop) u) : True = (@FINITE (A -> Prop) u).
Proof. exact (SYM (@lem4878870 A u h1)). Qed.
Lemma lem4878872 {A : Type'} (u : type686 A) (h1 : @FINITE (A -> Prop) u) : @FINITE (A -> Prop) u.
Proof. exact (EQ_MP (@lem4878871 A u h1) (@lem0)). Qed.
Lemma lem4878873 {A : Type'} (u : type686 A) (h1 : @FINITE (A -> Prop) u) : (term406 A u) = True.
Proof. exact (@lem4878868 A u (@lem4878872 A u h1)). Qed.
Lemma lem4878874 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4878875 {A : Type'} (u : type686 A) (h1 : @FINITE (A -> Prop) u) : (term407 A u) = (and True).
Proof. exact (MK_COMB (@lem4878874) (@lem4878873 A u h1)). Qed.
Lemma lem4878879 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term393 _87967 _87968 f s P) = (term394 _87967 _87968 s P f).
Proof. exact (EQ_MP (@lem4878832 _87967 _87968 s P f) (@lem4878831 _87967 _87968 P f s)). Qed.
Lemma lem4878880 {A : Type'} (s : type686 A) (P : type686 A) (f : type672 A) : (term408 A f s P) = (term409 A s P f).
Proof. exact (@lem4878879 (A -> Prop) (A -> Prop) s P f). Qed.
Lemma lem4878881 {A : Type'} (u : type686 A) (P : type686 A) : (term461 A u P) = (term462 A u P).
Proof. exact (@lem4878880 A u P (term405 A)). Qed.
Lemma lem4878889 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term427 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4878890 (p : Prop) (q : Prop) (p' : Prop) : term428 p q p'.
Proof. exact (fun q' : Prop => @lem4878889 p q p' q'). Qed.
Lemma lem4878891 (p : Prop) (q : Prop) : term429 p q.
Proof. exact (fun p' : Prop => @lem4878890 p q p'). Qed.
Lemma lem4878892 {A : Type'} (u : type686 A) (P : type686 A) (x : A -> Prop) : term463 A u P x.
Proof. exact (@lem4878891 (@IN (A -> Prop) x u) (term464 A P x)). Qed.
Lemma lem4878893 {A : Type'} (u : type686 A) (P : type686 A) (x : A -> Prop) (p' : Prop) : term465 A u P x p'.
Proof. exact (@lem4878892 A u P x p'). Qed.
Lemma lem4878894 {A : Type'} (u : type686 A) (P : type686 A) (x : A -> Prop) (p' : Prop) : (term465 A u P x p') = (term466 A u P x p').
Proof. exact (eq_refl (term465 A u P x p')). Qed.
Lemma lem4878895 {A : Type'} (u : type686 A) (P : type686 A) (x : A -> Prop) (p' : Prop) : term466 A u P x p'.
Proof. exact (EQ_MP (@lem4878894 A u P x p') (@lem4878893 A u P x p')). Qed.
Lemma lem4878896 {A : Type'} (u : type686 A) (P : type686 A) (x : A -> Prop) (p' : Prop) (q' : Prop) : term467 A u P x p' q'.
Proof. exact (@lem4878895 A u P x p' q'). Qed.
Lemma lem4878897 {A : Type'} (u : type686 A) (P : type686 A) (x : A -> Prop) (p' : Prop) (q' : Prop) : (term467 A u P x p' q') = (term468 A u P x p' q').
Proof. exact (eq_refl (term467 A u P x p' q')). Qed.
Lemma lem4878898 {A : Type'} (u : type686 A) (P : type686 A) (x : A -> Prop) (p' : Prop) (q' : Prop) : term468 A u P x p' q'.
Proof. exact (EQ_MP (@lem4878897 A u P x p' q') (@lem4878896 A u P x p' q')). Qed.
Lemma lem4878899 {A : Type'} (x : A -> Prop) (u : type686 A) : (@IN (A -> Prop) x u) = (@IN (A -> Prop) x u).
Proof. exact (eq_refl (@IN (A -> Prop) x u)). Qed.
Lemma lem4878900 {A : Type'} (P : type686 A) (x : A -> Prop) (u : type686 A) (q' : Prop) : term469 A P x u q'.
Proof. exact (@lem4878898 A u P x (@IN (A -> Prop) x u) q'). Qed.
Lemma lem4878901 {A : Type'} (P : type686 A) (x : A -> Prop) (u : type686 A) (q' : Prop) : term470 A P x u q'.
Proof. exact (@lem4878900 A P x u q' (@lem4878899 A x u)). Qed.
Lemma lem4878902 {A : Type'} (x : A -> Prop) (u : type686 A) (h1 : @IN (A -> Prop) x u) : @IN (A -> Prop) x u.
Proof. exact (h1). Qed.
Lemma lem4878903 {A : Type'} (x : A -> Prop) (u : type686 A) : (@IN (A -> Prop) x u) = ((@IN (A -> Prop) x u) = True).
Proof. exact (@lem7 (@IN (A -> Prop) x u)). Qed.
Lemma lem4878906 {A B : Type'} (f : A -> B) (y : A) : (term25 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4878907 {A : Type'} (f : type672 A) (y : A -> Prop) : (term440 A f y) = (f y).
Proof. exact (@lem4878906 (A -> Prop) (A -> Prop) f y). Qed.
Lemma lem4878908 {A : Type'} (x : A -> Prop) : (term441 A x) = (term442 A x).
Proof. exact (@lem4878907 A (term405 A) x). Qed.
Lemma lem4878909 {A : Type'} (c : A -> Prop) : (term442 A c) = (@DIFF A (@UNIV A) c).
Proof. exact (eq_refl (term442 A c)). Qed.
Lemma lem4878910 {A : Type'} : (term443 A) = (term405 A).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4878909 A c)). Qed.
Lemma lem4878911 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4878912 {A : Type'} (x : A -> Prop) : (term441 A x) = (term442 A x).
Proof. exact (MK_COMB (@lem4878910 A) (@lem4878911 A x)). Qed.
Lemma lem4878913 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4878914 {A : Type'} (x : A -> Prop) : (term444 A x) = (term445 A x).
Proof. exact (MK_COMB (@lem4878913 A) (@lem4878912 A x)). Qed.
Lemma lem4878915 {A : Type'} (x : A -> Prop) : (term442 A x) = (@DIFF A (@UNIV A) x).
Proof. exact (eq_refl (term442 A x)). Qed.
Lemma lem4878916 {A : Type'} (x : A -> Prop) : ((term441 A x) = (term442 A x)) = ((term442 A x) = (@DIFF A (@UNIV A) x)).
Proof. exact (MK_COMB (@lem4878914 A x) (@lem4878915 A x)). Qed.
Lemma lem4878917 {A : Type'} (x : A -> Prop) : (term442 A x) = (@DIFF A (@UNIV A) x).
Proof. exact (EQ_MP (@lem4878916 A x) (@lem4878908 A x)). Qed.
Lemma lem4878918 {A : Type'} (P : type686 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem4878919 {A : Type'} (P : type686 A) (x : A -> Prop) : (term464 A P x) = (term352 A P x).
Proof. exact (MK_COMB (@lem4878918 A P) (@lem4878917 A x)). Qed.
Lemma lem4878921 {A : Type'} (c : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term362 A u P) : term471 A u P c.
Proof. exact (fun h0 : @IN (A -> Prop) c u => @lem4878857 A P c u h1 h0). Qed.
Lemma lem4878922 {A : Type'} (c : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term362 A u P) : term471 A u P c.
Proof. exact (@lem4878921 A c u P h1). Qed.
Lemma lem4878923 {A : Type'} (x : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term362 A u P) : term471 A u P x.
Proof. exact (@lem4878922 A x u P h1). Qed.
Lemma lem4878925 {A : Type'} (x : A -> Prop) (u : type686 A) (h1 : @IN (A -> Prop) x u) : (@IN (A -> Prop) x u) = True.
Proof. exact (EQ_MP (@lem4878903 A x u) (@lem4878902 A x u h1)). Qed.
Lemma lem4878926 {A : Type'} (x : A -> Prop) (u : type686 A) (h1 : @IN (A -> Prop) x u) : True = (@IN (A -> Prop) x u).
Proof. exact (SYM (@lem4878925 A x u h1)). Qed.
Lemma lem4878927 {A : Type'} (x : A -> Prop) (u : type686 A) (h1 : @IN (A -> Prop) x u) : @IN (A -> Prop) x u.
Proof. exact (EQ_MP (@lem4878926 A x u h1) (@lem0)). Qed.
Lemma lem4878928 {A : Type'} (P : type686 A) (x : A -> Prop) (u : type686 A) (h1 : term362 A u P) (h2 : @IN (A -> Prop) x u) : (term352 A P x) = True.
Proof. exact (@lem4878923 A x u P h1 (@lem4878927 A x u h2)). Qed.
Lemma lem4878929 {A : Type'} (P : type686 A) (x : A -> Prop) (u : type686 A) (h1 : term362 A u P) (h2 : @IN (A -> Prop) x u) : (term464 A P x) = True.
Proof. exact (TRANS (@lem4878919 A P x) (@lem4878928 A P x u h1 h2)). Qed.
Lemma lem4878930 {A : Type'} (x : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term362 A u P) : term472 A u P x.
Proof. exact (fun h0 : @IN (A -> Prop) x u => @lem4878929 A P x u h1 h0). Qed.
Lemma lem4878931 {A : Type'} (P : type686 A) (x : A -> Prop) (u : type686 A) : term473 A P x u.
Proof. exact (@lem4878901 A P x u True). Qed.
Lemma lem4878932 {A : Type'} (x : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term362 A u P) : (term474 A u P x) = (term450 A x u).
Proof. exact (@lem4878931 A P x u (@lem4878930 A x u P h1)). Qed.
Lemma lem4878934 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem4878935 {A : Type'} (x : A -> Prop) (u : type686 A) : (term450 A x u) = True.
Proof. exact (@lem4878934 (@IN (A -> Prop) x u)). Qed.
Lemma lem4878936 {A : Type'} (x : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term362 A u P) : (term474 A u P x) = True.
Proof. exact (TRANS (@lem4878932 A x u P h1) (@lem4878935 A x u)). Qed.
Lemma lem4878937 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term362 A u P) : (term475 A u P) = (term451 A).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4878936 A x u P h1)). Qed.
Lemma lem4878938 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4878939 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term362 A u P) : (term462 A u P) = (term452 A).
Proof. exact (MK_COMB (@lem4878938 A) (@lem4878937 A u P h1)). Qed.
Lemma lem4878941 {A : Type'} (t : Prop) : (term453 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4878942 {A : Type'} (t : Prop) : (term454 A t) = t.
Proof. exact (@lem4878941 (A -> Prop) t). Qed.
Lemma lem4878943 {A : Type'} : (term452 A) = True.
Proof. exact (@lem4878942 A True). Qed.
Lemma lem4878944 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term362 A u P) : (term462 A u P) = True.
Proof. exact (TRANS (@lem4878939 A u P h1) (@lem4878943 A)). Qed.
Lemma lem4878945 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term362 A u P) : (term461 A u P) = True.
Proof. exact (TRANS (@lem4878881 A u P) (@lem4878944 A u P h1)). Qed.
Lemma lem4878946 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4878947 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term362 A u P) : (term476 A u P) = (and True).
Proof. exact (MK_COMB (@lem4878946) (@lem4878945 A u P h1)). Qed.
Lemma lem4878950 {A : Type'} (u : type686 A) (s : A -> Prop) : ((term477 A u) = s) = ((term477 A u) = s).
Proof. exact (eq_refl ((term477 A u) = s)). Qed.
Lemma lem4878951 {A : Type'} (s : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term362 A u P) : (term478 A P u s) = (term479 A u s).
Proof. exact (MK_COMB (@lem4878947 A u P h1) (@lem4878950 A u s)). Qed.
Lemma lem4878953 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4878954 {A : Type'} (u : type686 A) (s : A -> Prop) : (term479 A u s) = ((term477 A u) = s).
Proof. exact (@lem4878953 ((term477 A u) = s)). Qed.
Lemma lem4878957 {A : Type'} (s : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term362 A u P) : (term478 A P u s) = ((term477 A u) = s).
Proof. exact (TRANS (@lem4878951 A s u P h1) (@lem4878954 A u s)). Qed.
Lemma lem4878958 {A : Type'} (s : A -> Prop) (P : type686 A) (u : type686 A) (h1 : term362 A u P) (h2 : @FINITE (A -> Prop) u) : (term480 A P u s) = (term479 A u s).
Proof. exact (MK_COMB (@lem4878875 A u h2) (@lem4878957 A s u P h1)). Qed.
Lemma lem4878960 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4878961 {A : Type'} (u : type686 A) (s : A -> Prop) : (term479 A u s) = ((term477 A u) = s).
Proof. exact (@lem4878960 ((term477 A u) = s)). Qed.
Lemma lem4878964 {A : Type'} (s : A -> Prop) (P : type686 A) (u : type686 A) (h1 : term362 A u P) (h2 : @FINITE (A -> Prop) u) : (term480 A P u s) = ((term477 A u) = s).
Proof. exact (TRANS (@lem4878958 A s P u h1 h2) (@lem4878961 A u s)). Qed.
Lemma lem4878965 {A : Type'} (s : A -> Prop) (P : type686 A) (u : type686 A) (h1 : term362 A u P) (h2 : @FINITE (A -> Prop) u) : ((term477 A u) = s) = (term480 A P u s).
Proof. exact (SYM (@lem4878964 A s P u h1 h2)). Qed.
Lemma lem4878969 {_90072 : Type'} (s : type686 _90072) : (@INTERS _90072 s) = (term326 _90072 s).
Proof. exact (EQ_MP (@lem4878475 _90072 s) (@lem4878474 _90072 s)). Qed.
Lemma lem4878970 {A : Type'} (s : type686 A) : (@INTERS A s) = (term326 A s).
Proof. exact (@lem4878969 A s). Qed.
Lemma lem4878971 {A : Type'} (u : type686 A) : (term456 A u) = (term481 A u).
Proof. exact (@lem4878970 A (term482 A u)). Qed.
Lemma lem4878972 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4878973 {A : Type'} (u : type686 A) : (term483 A u) = (term484 A u).
Proof. exact (MK_COMB (@lem4878972 A) (@lem4878971 A u)). Qed.
Lemma lem4878974 {A : Type'} (s : A -> Prop) : (@DIFF A (@UNIV A) s) = (@DIFF A (@UNIV A) s).
Proof. exact (eq_refl (@DIFF A (@UNIV A) s)). Qed.
Lemma lem4878975 {A : Type'} (u : type686 A) (s : A -> Prop) : ((term456 A u) = (@DIFF A (@UNIV A) s)) = ((term481 A u) = (@DIFF A (@UNIV A) s)).
Proof. exact (MK_COMB (@lem4878973 A u) (@lem4878974 A s)). Qed.
Lemma lem4878976 {A : Type'} (u : type686 A) (s : A -> Prop) : ((term481 A u) = (@DIFF A (@UNIV A) s)) = ((term456 A u) = (@DIFF A (@UNIV A) s)).
Proof. exact (SYM (@lem4878975 A u s)). Qed.
Lemma lem4878980 {_90107 : Type'} (s : type686 _90107) : (@UNIONS _90107 s) = (term328 _90107 s).
Proof. exact (EQ_MP (@lem4878478 _90107 s) (@lem4878477 _90107 s)). Qed.
Lemma lem4878981 {A : Type'} (s : type686 A) : (@UNIONS A s) = (term328 A s).
Proof. exact (@lem4878980 A s). Qed.
Lemma lem4878982 {A : Type'} (u : type686 A) : (term477 A u) = (term485 A u).
Proof. exact (@lem4878981 A (term482 A u)). Qed.
Lemma lem4878983 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4878984 {A : Type'} (u : type686 A) : (term486 A u) = (term487 A u).
Proof. exact (MK_COMB (@lem4878983 A) (@lem4878982 A u)). Qed.
Lemma lem4878985 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4878986 {A : Type'} (u : type686 A) (s : A -> Prop) : ((term477 A u) = s) = ((term485 A u) = s).
Proof. exact (MK_COMB (@lem4878984 A u) (@lem4878985 A s)). Qed.
Lemma lem4878987 {A : Type'} (u : type686 A) (s : A -> Prop) : ((term485 A u) = s) = ((term477 A u) = s).
Proof. exact (SYM (@lem4878986 A u s)). Qed.
Lemma lem4878991 {_112226 _112228 _112229 : Type'} (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term8 _112226 _112228 _112229 g s f) = (term9 _112226 _112228 _112229 f g s).
Proof. exact (EQ_MP (@lem4876924 _112226 _112228 _112229 f g s) (@lem4878472 _112226 _112228 _112229 f g s)). Qed.
Lemma lem4878992 {A : Type'} (f : type672 A) (g : type672 A) (s : type686 A) : (term488 A g s f) = (term489 A f g s).
Proof. exact (@lem4878991 (A -> Prop) (A -> Prop) (A -> Prop) f g s). Qed.
Lemma lem4878993 {A : Type'} (u : type686 A) : (term490 A u) = (term491 A u).
Proof. exact (@lem4878992 A (term405 A) (term405 A) u). Qed.
Lemma lem4878994 {A : Type'} (t : A -> Prop) : (term442 A t) = (@DIFF A (@UNIV A) t).
Proof. exact (eq_refl (term442 A t)). Qed.
Lemma lem4878995 {A : Type'} (GEN_PVAR_65 : A -> Prop) (t : A -> Prop) (u : type686 A) : (term492 A GEN_PVAR_65 t u) = (term492 A GEN_PVAR_65 t u).
Proof. exact (eq_refl (term492 A GEN_PVAR_65 t u)). Qed.
Lemma lem4878996 {A : Type'} (GEN_PVAR_65 : A -> Prop) (u : type686 A) (t : A -> Prop) : (term493 A GEN_PVAR_65 u t) = (term494 A GEN_PVAR_65 u t).
Proof. exact (MK_COMB (@lem4878995 A GEN_PVAR_65 t u) (@lem4878994 A t)). Qed.
Lemma lem4878997 {A : Type'} (GEN_PVAR_65 : A -> Prop) (u : type686 A) : (term495 A GEN_PVAR_65 u) = (term496 A GEN_PVAR_65 u).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4878996 A GEN_PVAR_65 u t)). Qed.
Lemma lem4878998 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4878999 {A : Type'} (GEN_PVAR_65 : A -> Prop) (u : type686 A) : (term497 A GEN_PVAR_65 u) = (term498 A GEN_PVAR_65 u).
Proof. exact (MK_COMB (@lem4878998 A) (@lem4878997 A GEN_PVAR_65 u)). Qed.
Lemma lem4879000 {A : Type'} (u : type686 A) : (term499 A u) = (term500 A u).
Proof. exact (fun_ext (fun GEN_PVAR_65 : A -> Prop => @lem4878999 A GEN_PVAR_65 u)). Qed.
Lemma lem4879001 {A : Type'} : (@GSPEC (A -> Prop)) = (@GSPEC (A -> Prop)).
Proof. exact (eq_refl (@GSPEC (A -> Prop))). Qed.
Lemma lem4879002 {A : Type'} (u : type686 A) : (term490 A u) = (term501 A u).
Proof. exact (MK_COMB (@lem4879001 A) (@lem4879000 A u)). Qed.
Lemma lem4879003 {A : Type'} : (@eq ((A -> Prop) -> Prop)) = (@eq ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@eq ((A -> Prop) -> Prop))). Qed.
Lemma lem4879004 {A : Type'} (u : type686 A) : (term502 A u) = (term503 A u).
Proof. exact (MK_COMB (@lem4879003 A) (@lem4879002 A u)). Qed.
Lemma lem4879005 {A : Type'} (x : A -> Prop) : (term504 A x) = (term439 A x).
Proof. exact (eq_refl (term504 A x)). Qed.
Lemma lem4879006 {A : Type'} : (term505 A) = (term506 A).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4879005 A x)). Qed.
Lemma lem4879007 {A : Type'} : (@IMAGE (A -> Prop) (A -> Prop)) = (@IMAGE (A -> Prop) (A -> Prop)).
Proof. exact (eq_refl (@IMAGE (A -> Prop) (A -> Prop))). Qed.
Lemma lem4879008 {A : Type'} : (term507 A) = (term508 A).
Proof. exact (MK_COMB (@lem4879007 A) (@lem4879006 A)). Qed.
Lemma lem4879009 {A : Type'} (u : type686 A) : u = u.
Proof. exact (eq_refl u). Qed.
Lemma lem4879010 {A : Type'} (u : type686 A) : (term491 A u) = (term509 A u).
Proof. exact (MK_COMB (@lem4879008 A) (@lem4879009 A u)). Qed.
Lemma lem4879011 {A : Type'} (u : type686 A) : ((term490 A u) = (term491 A u)) = ((term501 A u) = (term509 A u)).
Proof. exact (MK_COMB (@lem4879004 A u) (@lem4879010 A u)). Qed.
Lemma lem4879012 {A : Type'} (u : type686 A) : (term501 A u) = (term509 A u).
Proof. exact (EQ_MP (@lem4879011 A u) (@lem4878993 A u)). Qed.
Lemma lem4879014 {A B : Type'} (f : A -> B) (y : A) : (term25 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4879015 {A : Type'} (f : type672 A) (y : A -> Prop) : (term440 A f y) = (f y).
Proof. exact (@lem4879014 (A -> Prop) (A -> Prop) f y). Qed.
Lemma lem4879016 {A : Type'} (x : A -> Prop) : (term441 A x) = (term442 A x).
Proof. exact (@lem4879015 A (term405 A) x). Qed.
Lemma lem4879017 {A : Type'} (c : A -> Prop) : (term442 A c) = (@DIFF A (@UNIV A) c).
Proof. exact (eq_refl (term442 A c)). Qed.
Lemma lem4879018 {A : Type'} : (term443 A) = (term405 A).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4879017 A c)). Qed.
Lemma lem4879019 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4879020 {A : Type'} (x : A -> Prop) : (term441 A x) = (term442 A x).
Proof. exact (MK_COMB (@lem4879018 A) (@lem4879019 A x)). Qed.
Lemma lem4879021 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4879022 {A : Type'} (x : A -> Prop) : (term444 A x) = (term445 A x).
Proof. exact (MK_COMB (@lem4879021 A) (@lem4879020 A x)). Qed.
Lemma lem4879023 {A : Type'} (x : A -> Prop) : (term442 A x) = (@DIFF A (@UNIV A) x).
Proof. exact (eq_refl (term442 A x)). Qed.
Lemma lem4879024 {A : Type'} (x : A -> Prop) : ((term441 A x) = (term442 A x)) = ((term442 A x) = (@DIFF A (@UNIV A) x)).
Proof. exact (MK_COMB (@lem4879022 A x) (@lem4879023 A x)). Qed.
Lemma lem4879025 {A : Type'} (x : A -> Prop) : (term442 A x) = (@DIFF A (@UNIV A) x).
Proof. exact (EQ_MP (@lem4879024 A x) (@lem4879016 A x)). Qed.
Lemma lem4879026 {A : Type'} : (@DIFF A (@UNIV A)) = (@DIFF A (@UNIV A)).
Proof. exact (eq_refl (@DIFF A (@UNIV A))). Qed.
Lemma lem4879027 {A : Type'} (x : A -> Prop) : (term439 A x) = (term389 A x).
Proof. exact (MK_COMB (@lem4879026 A) (@lem4879025 A x)). Qed.
Lemma lem4879028 {A : Type'} : (term506 A) = (term510 A).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4879027 A x)). Qed.
Lemma lem4879029 {A : Type'} : (@IMAGE (A -> Prop) (A -> Prop)) = (@IMAGE (A -> Prop) (A -> Prop)).
Proof. exact (eq_refl (@IMAGE (A -> Prop) (A -> Prop))). Qed.
Lemma lem4879030 {A : Type'} : (term508 A) = (term511 A).
Proof. exact (MK_COMB (@lem4879029 A) (@lem4879028 A)). Qed.
Lemma lem4879031 {A : Type'} (u : type686 A) : u = u.
Proof. exact (eq_refl u). Qed.
Lemma lem4879032 {A : Type'} (u : type686 A) : (term509 A u) = (term512 A u).
Proof. exact (MK_COMB (@lem4879030 A) (@lem4879031 A u)). Qed.
Lemma lem4879033 {A : Type'} (u : type686 A) : (term501 A u) = (term512 A u).
Proof. exact (TRANS (@lem4879012 A u) (@lem4879032 A u)). Qed.
Lemma lem4879034 {A : Type'} : (@UNIONS A) = (@UNIONS A).
Proof. exact (eq_refl (@UNIONS A)). Qed.
Lemma lem4879035 {A : Type'} (u : type686 A) : (term513 A u) = (term514 A u).
Proof. exact (MK_COMB (@lem4879034 A) (@lem4879033 A u)). Qed.
Lemma lem4879036 {A : Type'} : (@DIFF A (@UNIV A)) = (@DIFF A (@UNIV A)).
Proof. exact (eq_refl (@DIFF A (@UNIV A))). Qed.
Lemma lem4879037 {A : Type'} (u : type686 A) : (term481 A u) = (term515 A u).
Proof. exact (MK_COMB (@lem4879036 A) (@lem4879035 A u)). Qed.
Lemma lem4879038 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4879039 {A : Type'} (u : type686 A) : (term484 A u) = (term516 A u).
Proof. exact (MK_COMB (@lem4879038 A) (@lem4879037 A u)). Qed.
Lemma lem4879040 {A : Type'} (s : A -> Prop) : (@DIFF A (@UNIV A) s) = (@DIFF A (@UNIV A) s).
Proof. exact (eq_refl (@DIFF A (@UNIV A) s)). Qed.
Lemma lem4879041 {A : Type'} (u : type686 A) (s : A -> Prop) : ((term481 A u) = (@DIFF A (@UNIV A) s)) = ((term515 A u) = (@DIFF A (@UNIV A) s)).
Proof. exact (MK_COMB (@lem4879039 A u) (@lem4879040 A s)). Qed.
Lemma lem4879044 {A : Type'} (u : type686 A) (s : A -> Prop) : ((term515 A u) = (@DIFF A (@UNIV A) s)) = ((term481 A u) = (@DIFF A (@UNIV A) s)).
Proof. exact (SYM (@lem4879041 A u s)). Qed.
Lemma lem4879048 {_112226 _112228 _112229 : Type'} (f : _112228 -> _112226) (g : _112229 -> _112228) (s : _112229 -> Prop) : (term8 _112226 _112228 _112229 g s f) = (term9 _112226 _112228 _112229 f g s).
Proof. exact (EQ_MP (@lem4876924 _112226 _112228 _112229 f g s) (@lem4878472 _112226 _112228 _112229 f g s)). Qed.
Lemma lem4879049 {A : Type'} (f : type672 A) (g : type672 A) (s : type686 A) : (term488 A g s f) = (term489 A f g s).
Proof. exact (@lem4879048 (A -> Prop) (A -> Prop) (A -> Prop) f g s). Qed.
Lemma lem4879050 {A : Type'} (u : type686 A) : (term490 A u) = (term491 A u).
Proof. exact (@lem4879049 A (term405 A) (term405 A) u). Qed.
Lemma lem4879051 {A : Type'} (t : A -> Prop) : (term442 A t) = (@DIFF A (@UNIV A) t).
Proof. exact (eq_refl (term442 A t)). Qed.
Lemma lem4879052 {A : Type'} (GEN_PVAR_66 : A -> Prop) (t : A -> Prop) (u : type686 A) : (term492 A GEN_PVAR_66 t u) = (term492 A GEN_PVAR_66 t u).
Proof. exact (eq_refl (term492 A GEN_PVAR_66 t u)). Qed.
Lemma lem4879053 {A : Type'} (GEN_PVAR_66 : A -> Prop) (u : type686 A) (t : A -> Prop) : (term493 A GEN_PVAR_66 u t) = (term494 A GEN_PVAR_66 u t).
Proof. exact (MK_COMB (@lem4879052 A GEN_PVAR_66 t u) (@lem4879051 A t)). Qed.
Lemma lem4879054 {A : Type'} (GEN_PVAR_66 : A -> Prop) (u : type686 A) : (term495 A GEN_PVAR_66 u) = (term496 A GEN_PVAR_66 u).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4879053 A GEN_PVAR_66 u t)). Qed.
Lemma lem4879055 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4879056 {A : Type'} (GEN_PVAR_66 : A -> Prop) (u : type686 A) : (term497 A GEN_PVAR_66 u) = (term498 A GEN_PVAR_66 u).
Proof. exact (MK_COMB (@lem4879055 A) (@lem4879054 A GEN_PVAR_66 u)). Qed.
Lemma lem4879057 {A : Type'} (u : type686 A) : (term499 A u) = (term500 A u).
Proof. exact (fun_ext (fun GEN_PVAR_66 : A -> Prop => @lem4879056 A GEN_PVAR_66 u)). Qed.
Lemma lem4879058 {A : Type'} : (@GSPEC (A -> Prop)) = (@GSPEC (A -> Prop)).
Proof. exact (eq_refl (@GSPEC (A -> Prop))). Qed.
Lemma lem4879059 {A : Type'} (u : type686 A) : (term490 A u) = (term501 A u).
Proof. exact (MK_COMB (@lem4879058 A) (@lem4879057 A u)). Qed.
Lemma lem4879060 {A : Type'} : (@eq ((A -> Prop) -> Prop)) = (@eq ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@eq ((A -> Prop) -> Prop))). Qed.
Lemma lem4879061 {A : Type'} (u : type686 A) : (term502 A u) = (term503 A u).
Proof. exact (MK_COMB (@lem4879060 A) (@lem4879059 A u)). Qed.
Lemma lem4879062 {A : Type'} (x : A -> Prop) : (term504 A x) = (term439 A x).
Proof. exact (eq_refl (term504 A x)). Qed.
Lemma lem4879063 {A : Type'} : (term505 A) = (term506 A).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4879062 A x)). Qed.
Lemma lem4879064 {A : Type'} : (@IMAGE (A -> Prop) (A -> Prop)) = (@IMAGE (A -> Prop) (A -> Prop)).
Proof. exact (eq_refl (@IMAGE (A -> Prop) (A -> Prop))). Qed.
Lemma lem4879065 {A : Type'} : (term507 A) = (term508 A).
Proof. exact (MK_COMB (@lem4879064 A) (@lem4879063 A)). Qed.
Lemma lem4879066 {A : Type'} (u : type686 A) : u = u.
Proof. exact (eq_refl u). Qed.
Lemma lem4879067 {A : Type'} (u : type686 A) : (term491 A u) = (term509 A u).
Proof. exact (MK_COMB (@lem4879065 A) (@lem4879066 A u)). Qed.
Lemma lem4879068 {A : Type'} (u : type686 A) : ((term490 A u) = (term491 A u)) = ((term501 A u) = (term509 A u)).
Proof. exact (MK_COMB (@lem4879061 A u) (@lem4879067 A u)). Qed.
Lemma lem4879069 {A : Type'} (u : type686 A) : (term501 A u) = (term509 A u).
Proof. exact (EQ_MP (@lem4879068 A u) (@lem4879050 A u)). Qed.
Lemma lem4879071 {A B : Type'} (f : A -> B) (y : A) : (term25 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4879072 {A : Type'} (f : type672 A) (y : A -> Prop) : (term440 A f y) = (f y).
Proof. exact (@lem4879071 (A -> Prop) (A -> Prop) f y). Qed.
Lemma lem4879073 {A : Type'} (x : A -> Prop) : (term441 A x) = (term442 A x).
Proof. exact (@lem4879072 A (term405 A) x). Qed.
Lemma lem4879074 {A : Type'} (c : A -> Prop) : (term442 A c) = (@DIFF A (@UNIV A) c).
Proof. exact (eq_refl (term442 A c)). Qed.
Lemma lem4879075 {A : Type'} : (term443 A) = (term405 A).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4879074 A c)). Qed.
Lemma lem4879076 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4879077 {A : Type'} (x : A -> Prop) : (term441 A x) = (term442 A x).
Proof. exact (MK_COMB (@lem4879075 A) (@lem4879076 A x)). Qed.
Lemma lem4879078 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4879079 {A : Type'} (x : A -> Prop) : (term444 A x) = (term445 A x).
Proof. exact (MK_COMB (@lem4879078 A) (@lem4879077 A x)). Qed.
Lemma lem4879080 {A : Type'} (x : A -> Prop) : (term442 A x) = (@DIFF A (@UNIV A) x).
Proof. exact (eq_refl (term442 A x)). Qed.
Lemma lem4879081 {A : Type'} (x : A -> Prop) : ((term441 A x) = (term442 A x)) = ((term442 A x) = (@DIFF A (@UNIV A) x)).
Proof. exact (MK_COMB (@lem4879079 A x) (@lem4879080 A x)). Qed.
Lemma lem4879082 {A : Type'} (x : A -> Prop) : (term442 A x) = (@DIFF A (@UNIV A) x).
Proof. exact (EQ_MP (@lem4879081 A x) (@lem4879073 A x)). Qed.
Lemma lem4879083 {A : Type'} : (@DIFF A (@UNIV A)) = (@DIFF A (@UNIV A)).
Proof. exact (eq_refl (@DIFF A (@UNIV A))). Qed.
Lemma lem4879084 {A : Type'} (x : A -> Prop) : (term439 A x) = (term389 A x).
Proof. exact (MK_COMB (@lem4879083 A) (@lem4879082 A x)). Qed.
Lemma lem4879085 {A : Type'} : (term506 A) = (term510 A).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4879084 A x)). Qed.
Lemma lem4879086 {A : Type'} : (@IMAGE (A -> Prop) (A -> Prop)) = (@IMAGE (A -> Prop) (A -> Prop)).
Proof. exact (eq_refl (@IMAGE (A -> Prop) (A -> Prop))). Qed.
Lemma lem4879087 {A : Type'} : (term508 A) = (term511 A).
Proof. exact (MK_COMB (@lem4879086 A) (@lem4879085 A)). Qed.
Lemma lem4879088 {A : Type'} (u : type686 A) : u = u.
Proof. exact (eq_refl u). Qed.
Lemma lem4879089 {A : Type'} (u : type686 A) : (term509 A u) = (term512 A u).
Proof. exact (MK_COMB (@lem4879087 A) (@lem4879088 A u)). Qed.
Lemma lem4879090 {A : Type'} (u : type686 A) : (term501 A u) = (term512 A u).
Proof. exact (TRANS (@lem4879069 A u) (@lem4879089 A u)). Qed.
Lemma lem4879091 {A : Type'} : (@INTERS A) = (@INTERS A).
Proof. exact (eq_refl (@INTERS A)). Qed.
Lemma lem4879092 {A : Type'} (u : type686 A) : (term517 A u) = (term518 A u).
Proof. exact (MK_COMB (@lem4879091 A) (@lem4879090 A u)). Qed.
Lemma lem4879093 {A : Type'} : (@DIFF A (@UNIV A)) = (@DIFF A (@UNIV A)).
Proof. exact (eq_refl (@DIFF A (@UNIV A))). Qed.
Lemma lem4879094 {A : Type'} (u : type686 A) : (term485 A u) = (term519 A u).
Proof. exact (MK_COMB (@lem4879093 A) (@lem4879092 A u)). Qed.
Lemma lem4879095 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4879096 {A : Type'} (u : type686 A) : (term487 A u) = (term520 A u).
Proof. exact (MK_COMB (@lem4879095 A) (@lem4879094 A u)). Qed.
Lemma lem4879097 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4879098 {A : Type'} (u : type686 A) (s : A -> Prop) : ((term485 A u) = s) = ((term519 A u) = s).
Proof. exact (MK_COMB (@lem4879096 A u) (@lem4879097 A s)). Qed.
Lemma lem4879101 {A : Type'} (u : type686 A) (s : A -> Prop) : ((term519 A u) = s) = ((term485 A u) = s).
Proof. exact (SYM (@lem4879098 A u s)). Qed.
Lemma lem4879102 {A : Type'} (s : A -> Prop) : term388 A s.
Proof. exact (@lem3270825 A s). Qed.
Lemma lem4879103 {A : Type'} (s : A -> Prop) : (term388 A s) = ((term389 A s) = s).
Proof. exact (eq_refl (term388 A s)). Qed.
Lemma lem4879105 {_87528 : Type'} (s : _87528 -> Prop) : term521 _87528 s.
Proof. exact (@lem3368911 _87528 s). Qed.
Lemma lem4879106 {_87528 : Type'} (s : _87528 -> Prop) : (term521 _87528 s) = ((term522 _87528 s) = s).
Proof. exact (eq_refl (term521 _87528 s)). Qed.
Lemma lem4879120 {A : Type'} (s : A -> Prop) : (term389 A s) = s.
Proof. exact (EQ_MP (@lem4879103 A s) (@lem4879102 A s)). Qed.
Lemma lem4879121 {A : Type'} (s : A -> Prop) : (term389 A s) = s.
Proof. exact (@lem4879120 A s). Qed.
Lemma lem4879122 {A : Type'} (x : A -> Prop) : (term389 A x) = x.
Proof. exact (@lem4879121 A x). Qed.
Lemma lem4879123 {A : Type'} : (term510 A) = (term523 A).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4879122 A x)). Qed.
Lemma lem4879124 {A : Type'} : (@IMAGE (A -> Prop) (A -> Prop)) = (@IMAGE (A -> Prop) (A -> Prop)).
Proof. exact (eq_refl (@IMAGE (A -> Prop) (A -> Prop))). Qed.
Lemma lem4879125 {A : Type'} : (term511 A) = (term524 A).
Proof. exact (MK_COMB (@lem4879124 A) (@lem4879123 A)). Qed.
Lemma lem4879126 {A : Type'} (u : type686 A) : u = u.
Proof. exact (eq_refl u). Qed.
Lemma lem4879127 {A : Type'} (u : type686 A) : (term512 A u) = (term525 A u).
Proof. exact (MK_COMB (@lem4879125 A) (@lem4879126 A u)). Qed.
Lemma lem4879129 {_87528 : Type'} (s : _87528 -> Prop) : (term522 _87528 s) = s.
Proof. exact (EQ_MP (@lem4879106 _87528 s) (@lem4879105 _87528 s)). Qed.
Lemma lem4879130 {A : Type'} (s : type686 A) : (term525 A s) = s.
Proof. exact (@lem4879129 (A -> Prop) s). Qed.
Lemma lem4879131 {A : Type'} (u : type686 A) : (term525 A u) = u.
Proof. exact (@lem4879130 A u). Qed.
Lemma lem4879132 {A : Type'} (u : type686 A) : (term512 A u) = u.
Proof. exact (TRANS (@lem4879127 A u) (@lem4879131 A u)). Qed.
Lemma lem4879133 {A : Type'} : (@UNIONS A) = (@UNIONS A).
Proof. exact (eq_refl (@UNIONS A)). Qed.
Lemma lem4879134 {A : Type'} (u : type686 A) : (term514 A u) = (@UNIONS A u).
Proof. exact (MK_COMB (@lem4879133 A) (@lem4879132 A u)). Qed.
Lemma lem4879136 {A : Type'} (u : type686 A) (s : A -> Prop) (h1 : (@UNIONS A u) = s) : (@UNIONS A u) = s.
Proof. exact (h1). Qed.
Lemma lem4879137 {A : Type'} (u : type686 A) (s : A -> Prop) (h1 : (@UNIONS A u) = s) : (term514 A u) = s.
Proof. exact (TRANS (@lem4879134 A u) (@lem4879136 A u s h1)). Qed.
Lemma lem4879138 {A : Type'} : (@DIFF A (@UNIV A)) = (@DIFF A (@UNIV A)).
Proof. exact (eq_refl (@DIFF A (@UNIV A))). Qed.
Lemma lem4879139 {A : Type'} (u : type686 A) (s : A -> Prop) (h1 : (@UNIONS A u) = s) : (term515 A u) = (@DIFF A (@UNIV A) s).
Proof. exact (MK_COMB (@lem4879138 A) (@lem4879137 A u s h1)). Qed.
Lemma lem4879140 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4879141 {A : Type'} (u : type686 A) (s : A -> Prop) (h1 : (@UNIONS A u) = s) : (term516 A u) = (term526 A s).
Proof. exact (MK_COMB (@lem4879140 A) (@lem4879139 A u s h1)). Qed.
Lemma lem4879142 {A : Type'} (s : A -> Prop) : (@DIFF A (@UNIV A) s) = (@DIFF A (@UNIV A) s).
Proof. exact (eq_refl (@DIFF A (@UNIV A) s)). Qed.
Lemma lem4879143 {A : Type'} (u : type686 A) (s : A -> Prop) (h1 : (@UNIONS A u) = s) : ((term515 A u) = (@DIFF A (@UNIV A) s)) = ((@DIFF A (@UNIV A) s) = (@DIFF A (@UNIV A) s)).
Proof. exact (MK_COMB (@lem4879141 A u s h1) (@lem4879142 A s)). Qed.
Lemma lem4879145 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4879146 {A : Type'} (x : A -> Prop) : (x = x) = True.
Proof. exact (@lem4879145 (A -> Prop) x). Qed.
Lemma lem4879147 {A : Type'} (s : A -> Prop) : ((@DIFF A (@UNIV A) s) = (@DIFF A (@UNIV A) s)) = True.
Proof. exact (@lem4879146 A (@DIFF A (@UNIV A) s)). Qed.
Lemma lem4879148 {A : Type'} (u : type686 A) (s : A -> Prop) (h1 : (@UNIONS A u) = s) : ((term515 A u) = (@DIFF A (@UNIV A) s)) = True.
Proof. exact (TRANS (@lem4879143 A u s h1) (@lem4879147 A s)). Qed.
Lemma lem4879149 {A : Type'} (u : type686 A) (s : A -> Prop) (h1 : (@UNIONS A u) = s) : True = ((term515 A u) = (@DIFF A (@UNIV A) s)).
Proof. exact (SYM (@lem4879148 A u s h1)). Qed.
Lemma lem4879150 {A : Type'} (u : type686 A) (s : A -> Prop) (h1 : (@UNIONS A u) = s) : (term515 A u) = (@DIFF A (@UNIV A) s).
Proof. exact (EQ_MP (@lem4879149 A u s h1) (@lem0)). Qed.
Lemma lem4879151 {A : Type'} (s : A -> Prop) : term388 A s.
Proof. exact (@lem3270825 A s). Qed.
Lemma lem4879152 {A : Type'} (s : A -> Prop) : (term388 A s) = ((term389 A s) = s).
Proof. exact (eq_refl (term388 A s)). Qed.
Lemma lem4879154 {_87528 : Type'} (s : _87528 -> Prop) : term521 _87528 s.
Proof. exact (@lem3368911 _87528 s). Qed.
Lemma lem4879155 {_87528 : Type'} (s : _87528 -> Prop) : (term521 _87528 s) = ((term522 _87528 s) = s).
Proof. exact (eq_refl (term521 _87528 s)). Qed.
Lemma lem4879169 {A : Type'} (s : A -> Prop) : (term389 A s) = s.
Proof. exact (EQ_MP (@lem4879152 A s) (@lem4879151 A s)). Qed.
Lemma lem4879170 {A : Type'} (s : A -> Prop) : (term389 A s) = s.
Proof. exact (@lem4879169 A s). Qed.
Lemma lem4879171 {A : Type'} (x : A -> Prop) : (term389 A x) = x.
Proof. exact (@lem4879170 A x). Qed.
Lemma lem4879172 {A : Type'} : (term510 A) = (term523 A).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4879171 A x)). Qed.
Lemma lem4879173 {A : Type'} : (@IMAGE (A -> Prop) (A -> Prop)) = (@IMAGE (A -> Prop) (A -> Prop)).
Proof. exact (eq_refl (@IMAGE (A -> Prop) (A -> Prop))). Qed.
Lemma lem4879174 {A : Type'} : (term511 A) = (term524 A).
Proof. exact (MK_COMB (@lem4879173 A) (@lem4879172 A)). Qed.
Lemma lem4879175 {A : Type'} (u : type686 A) : u = u.
Proof. exact (eq_refl u). Qed.
Lemma lem4879176 {A : Type'} (u : type686 A) : (term512 A u) = (term525 A u).
Proof. exact (MK_COMB (@lem4879174 A) (@lem4879175 A u)). Qed.
Lemma lem4879178 {_87528 : Type'} (s : _87528 -> Prop) : (term522 _87528 s) = s.
Proof. exact (EQ_MP (@lem4879155 _87528 s) (@lem4879154 _87528 s)). Qed.
Lemma lem4879179 {A : Type'} (s : type686 A) : (term525 A s) = s.
Proof. exact (@lem4879178 (A -> Prop) s). Qed.
Lemma lem4879180 {A : Type'} (u : type686 A) : (term525 A u) = u.
Proof. exact (@lem4879179 A u). Qed.
Lemma lem4879181 {A : Type'} (u : type686 A) : (term512 A u) = u.
Proof. exact (TRANS (@lem4879176 A u) (@lem4879180 A u)). Qed.
Lemma lem4879182 {A : Type'} : (@INTERS A) = (@INTERS A).
Proof. exact (eq_refl (@INTERS A)). Qed.
Lemma lem4879183 {A : Type'} (u : type686 A) : (term518 A u) = (@INTERS A u).
Proof. exact (MK_COMB (@lem4879182 A) (@lem4879181 A u)). Qed.
Lemma lem4879185 {A : Type'} (u : type686 A) (s : A -> Prop) (h1 : (@INTERS A u) = (@DIFF A (@UNIV A) s)) : (@INTERS A u) = (@DIFF A (@UNIV A) s).
Proof. exact (h1). Qed.
Lemma lem4879186 {A : Type'} (u : type686 A) (s : A -> Prop) (h1 : (@INTERS A u) = (@DIFF A (@UNIV A) s)) : (term518 A u) = (@DIFF A (@UNIV A) s).
Proof. exact (TRANS (@lem4879183 A u) (@lem4879185 A u s h1)). Qed.
Lemma lem4879187 {A : Type'} : (@DIFF A (@UNIV A)) = (@DIFF A (@UNIV A)).
Proof. exact (eq_refl (@DIFF A (@UNIV A))). Qed.
Lemma lem4879188 {A : Type'} (u : type686 A) (s : A -> Prop) (h1 : (@INTERS A u) = (@DIFF A (@UNIV A) s)) : (term519 A u) = (term389 A s).
Proof. exact (MK_COMB (@lem4879187 A) (@lem4879186 A u s h1)). Qed.
Lemma lem4879190 {A : Type'} (s : A -> Prop) : (term389 A s) = s.
Proof. exact (EQ_MP (@lem4879152 A s) (@lem4879151 A s)). Qed.
Lemma lem4879191 {A : Type'} (s : A -> Prop) : (term389 A s) = s.
Proof. exact (@lem4879190 A s). Qed.
Lemma lem4879192 {A : Type'} (u : type686 A) (s : A -> Prop) (h1 : (@INTERS A u) = (@DIFF A (@UNIV A) s)) : (term519 A u) = s.
Proof. exact (TRANS (@lem4879188 A u s h1) (@lem4879191 A s)). Qed.
Lemma lem4879193 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4879194 {A : Type'} (u : type686 A) (s : A -> Prop) (h1 : (@INTERS A u) = (@DIFF A (@UNIV A) s)) : (term520 A u) = (@eq (A -> Prop) s).
Proof. exact (MK_COMB (@lem4879193 A) (@lem4879192 A u s h1)). Qed.
Lemma lem4879195 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4879196 {A : Type'} (u : type686 A) (s : A -> Prop) (h1 : (@INTERS A u) = (@DIFF A (@UNIV A) s)) : ((term519 A u) = s) = (s = s).
Proof. exact (MK_COMB (@lem4879194 A u s h1) (@lem4879195 A s)). Qed.
Lemma lem4879198 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4879199 {A : Type'} (x : A -> Prop) : (x = x) = True.
Proof. exact (@lem4879198 (A -> Prop) x). Qed.
Lemma lem4879200 {A : Type'} (s : A -> Prop) : (s = s) = True.
Proof. exact (@lem4879199 A s). Qed.
Lemma lem4879201 {A : Type'} (u : type686 A) (s : A -> Prop) (h1 : (@INTERS A u) = (@DIFF A (@UNIV A) s)) : ((term519 A u) = s) = True.
Proof. exact (TRANS (@lem4879196 A u s h1) (@lem4879200 A s)). Qed.
Lemma lem4879202 {A : Type'} (u : type686 A) (s : A -> Prop) (h1 : (@INTERS A u) = (@DIFF A (@UNIV A) s)) : True = ((term519 A u) = s).
Proof. exact (SYM (@lem4879201 A u s h1)). Qed.
Lemma lem4879203 {A : Type'} (u : type686 A) (s : A -> Prop) (h1 : (@INTERS A u) = (@DIFF A (@UNIV A) s)) : (term519 A u) = s.
Proof. exact (EQ_MP (@lem4879202 A u s h1) (@lem0)). Qed.
Lemma lem4879204 {A : Type'} (u : type686 A) (s : A -> Prop) (h1 : (@INTERS A u) = (@DIFF A (@UNIV A) s)) : (term485 A u) = s.
Proof. exact (EQ_MP (@lem4879101 A u s) (@lem4879203 A u s h1)). Qed.
Lemma lem4879205 {A : Type'} (u : type686 A) (s : A -> Prop) (h1 : (@UNIONS A u) = s) : (term481 A u) = (@DIFF A (@UNIV A) s).
Proof. exact (EQ_MP (@lem4879044 A u s) (@lem4879150 A u s h1)). Qed.
Lemma lem4879206 {A : Type'} (u : type686 A) (s : A -> Prop) (h1 : (@INTERS A u) = (@DIFF A (@UNIV A) s)) : (term477 A u) = s.
Proof. exact (EQ_MP (@lem4878987 A u s) (@lem4879204 A u s h1)). Qed.
Lemma lem4879207 {A : Type'} (u : type686 A) (s : A -> Prop) (h1 : (@UNIONS A u) = s) : (term456 A u) = (@DIFF A (@UNIV A) s).
Proof. exact (EQ_MP (@lem4878976 A u s) (@lem4879205 A u s h1)). Qed.
Lemma lem4879208 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term362 A u P) (h2 : @FINITE (A -> Prop) u) (h3 : (@INTERS A u) = (@DIFF A (@UNIV A) s)) : term480 A P u s.
Proof. exact (EQ_MP (@lem4878965 A s P u h1 h2) (@lem4879206 A u s h3)). Qed.
Lemma lem4879209 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term385 A u P) (h2 : @FINITE (A -> Prop) u) (h3 : (@UNIONS A u) = s) : term459 A P u s.
Proof. exact (EQ_MP (@lem4878824 A s P u h1 h2) (@lem4879207 A u s h3)). Qed.
Lemma lem4879210 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term362 A u P) (h2 : @FINITE (A -> Prop) u) (h3 : (@INTERS A u) = (@DIFF A (@UNIV A) s)) : term341 A P s.
Proof. exact (ex_intro (term527 A P s) (term482 A u) (@lem4879208 A P u s h1 h2 h3)). Qed.
Lemma lem4879211 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term385 A u P) (h2 : @FINITE (A -> Prop) u) (h3 : (@UNIONS A u) = s) : term382 A P s.
Proof. exact (ex_intro (term528 A P s) (term482 A u) (@lem4879209 A P u s h1 h2 h3)). Qed.
Lemma lem4879212 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term386 A P u s) : term387 A P u s.
Proof. exact (proj2 (@lem4878654 A P u s h1)). Qed.
Lemma lem4879213 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term386 A P u s) : @FINITE (A -> Prop) u.
Proof. exact (proj1 (@lem4878654 A P u s h1)). Qed.
Lemma lem4879214 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term387 A P u s) : (@INTERS A u) = (@DIFF A (@UNIV A) s).
Proof. exact (proj2 (@lem4878655 A P u s h1)). Qed.
Lemma lem4879215 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term387 A P u s) : term362 A u P.
Proof. exact (proj1 (@lem4878655 A P u s h1)). Qed.
Lemma lem4879216 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term362 A u P) (h2 : @FINITE (A -> Prop) u) (h3 : (@INTERS A u) = (@DIFF A (@UNIV A) s)) : ((@INTERS A u) = (@DIFF A (@UNIV A) s)) = (term341 A P s).
Proof. exact (prop_ext (fun h4 : (@INTERS A u) = (@DIFF A (@UNIV A) s) => @lem4879210 A P u s h1 h2 h3) (fun h4 : term341 A P s => @lem4878657 A u s h3)). Qed.
Lemma lem4879217 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term362 A u P) (h2 : @FINITE (A -> Prop) u) (h3 : (@INTERS A u) = (@DIFF A (@UNIV A) s)) : term341 A P s.
Proof. exact (EQ_MP (@lem4879216 A P u s h1 h2 h3) (@lem4878657 A u s h3)). Qed.
Lemma lem4879218 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term362 A u P) (h2 : @FINITE (A -> Prop) u) (h3 : (@INTERS A u) = (@DIFF A (@UNIV A) s)) : (term362 A u P) = (term341 A P s).
Proof. exact (prop_ext (fun h4 : term362 A u P => @lem4879217 A P u s h1 h2 h3) (fun h4 : term341 A P s => @lem4878658 A u P h1)). Qed.
Lemma lem4879219 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term362 A u P) (h2 : @FINITE (A -> Prop) u) (h3 : (@INTERS A u) = (@DIFF A (@UNIV A) s)) : term341 A P s.
Proof. exact (EQ_MP (@lem4879218 A P u s h1 h2 h3) (@lem4878658 A u P h1)). Qed.
Lemma lem4879220 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term362 A u P) (h2 : @FINITE (A -> Prop) u) (h3 : term387 A P u s) : ((@INTERS A u) = (@DIFF A (@UNIV A) s)) = (term341 A P s).
Proof. exact (prop_ext (fun h4 : (@INTERS A u) = (@DIFF A (@UNIV A) s) => @lem4879219 A P u s h1 h2 h4) (fun h4 : term341 A P s => @lem4879214 A P u s h3)). Qed.
Lemma lem4879221 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term362 A u P) (h2 : @FINITE (A -> Prop) u) (h3 : term387 A P u s) : term341 A P s.
Proof. exact (EQ_MP (@lem4879220 A P u s h1 h2 h3) (@lem4879214 A P u s h3)). Qed.
Lemma lem4879222 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : @FINITE (A -> Prop) u) (h2 : term387 A P u s) : (term362 A u P) = (term341 A P s).
Proof. exact (prop_ext (fun h3 : term362 A u P => @lem4879221 A P u s h3 h1 h2) (fun h3 : term341 A P s => @lem4879215 A P u s h2)). Qed.
Lemma lem4879223 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : @FINITE (A -> Prop) u) (h2 : term387 A P u s) : term341 A P s.
Proof. exact (EQ_MP (@lem4879222 A P u s h1 h2) (@lem4879215 A P u s h2)). Qed.
Lemma lem4879224 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : @FINITE (A -> Prop) u) (h2 : term387 A P u s) : (@FINITE (A -> Prop) u) = (term341 A P s).
Proof. exact (prop_ext (fun h3 : @FINITE (A -> Prop) u => @lem4879223 A P u s h1 h2) (fun h3 : term341 A P s => @lem4878656 A u h1)). Qed.
Lemma lem4879225 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : @FINITE (A -> Prop) u) (h2 : term387 A P u s) : term341 A P s.
Proof. exact (EQ_MP (@lem4879224 A P u s h1 h2) (@lem4878656 A u h1)). Qed.
Lemma lem4879226 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : @FINITE (A -> Prop) u) (h2 : term386 A P u s) : (term387 A P u s) = (term341 A P s).
Proof. exact (prop_ext (fun h3 : term387 A P u s => @lem4879225 A P u s h1 h3) (fun h3 : term341 A P s => @lem4879212 A P u s h2)). Qed.
Lemma lem4879227 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : @FINITE (A -> Prop) u) (h2 : term386 A P u s) : term341 A P s.
Proof. exact (EQ_MP (@lem4879226 A P u s h1 h2) (@lem4879212 A P u s h2)). Qed.
Lemma lem4879228 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term386 A P u s) : (@FINITE (A -> Prop) u) = (term341 A P s).
Proof. exact (prop_ext (fun h2 : @FINITE (A -> Prop) u => @lem4879227 A P u s h2 h1) (fun h2 : term341 A P s => @lem4879213 A P u s h1)). Qed.
Lemma lem4879229 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term386 A P u s) : term341 A P s.
Proof. exact (EQ_MP (@lem4879228 A P u s h1) (@lem4879213 A P u s h1)). Qed.
Lemma lem4879230 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term382 A P s) : term341 A P s.
Proof. exact (ex_elim (@lem4878653 A P s h1) (fun u : type686 A => fun h0 : term528 A P s u => @lem4879229 A P u s h0)). Qed.
Lemma lem4879231 {A : Type'} (P : type686 A) (s : A -> Prop) : term529 A P s.
Proof. exact (fun h0 : term382 A P s => @lem4879230 A P s h0). Qed.
Lemma lem4879232 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term383 A P u s) : term384 A P u s.
Proof. exact (proj2 (@lem4878648 A P u s h1)). Qed.
Lemma lem4879233 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term383 A P u s) : @FINITE (A -> Prop) u.
Proof. exact (proj1 (@lem4878648 A P u s h1)). Qed.
Lemma lem4879234 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term384 A P u s) : (@UNIONS A u) = s.
Proof. exact (proj2 (@lem4878649 A P u s h1)). Qed.
Lemma lem4879235 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term384 A P u s) : term385 A u P.
Proof. exact (proj1 (@lem4878649 A P u s h1)). Qed.
Lemma lem4879236 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term385 A u P) (h2 : @FINITE (A -> Prop) u) (h3 : (@UNIONS A u) = s) : ((@UNIONS A u) = s) = (term382 A P s).
Proof. exact (prop_ext (fun h4 : (@UNIONS A u) = s => @lem4879211 A P u s h1 h2 h3) (fun h4 : term382 A P s => @lem4878651 A u s h3)). Qed.
Lemma lem4879237 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term385 A u P) (h2 : @FINITE (A -> Prop) u) (h3 : (@UNIONS A u) = s) : term382 A P s.
Proof. exact (EQ_MP (@lem4879236 A P u s h1 h2 h3) (@lem4878651 A u s h3)). Qed.
Lemma lem4879238 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term385 A u P) (h2 : @FINITE (A -> Prop) u) (h3 : (@UNIONS A u) = s) : (term385 A u P) = (term382 A P s).
Proof. exact (prop_ext (fun h4 : term385 A u P => @lem4879237 A P u s h1 h2 h3) (fun h4 : term382 A P s => @lem4878652 A u P h1)). Qed.
Lemma lem4879239 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term385 A u P) (h2 : @FINITE (A -> Prop) u) (h3 : (@UNIONS A u) = s) : term382 A P s.
Proof. exact (EQ_MP (@lem4879238 A P u s h1 h2 h3) (@lem4878652 A u P h1)). Qed.
Lemma lem4879240 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term385 A u P) (h2 : @FINITE (A -> Prop) u) (h3 : term384 A P u s) : ((@UNIONS A u) = s) = (term382 A P s).
Proof. exact (prop_ext (fun h4 : (@UNIONS A u) = s => @lem4879239 A P u s h1 h2 h4) (fun h4 : term382 A P s => @lem4879234 A P u s h3)). Qed.
Lemma lem4879241 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term385 A u P) (h2 : @FINITE (A -> Prop) u) (h3 : term384 A P u s) : term382 A P s.
Proof. exact (EQ_MP (@lem4879240 A P u s h1 h2 h3) (@lem4879234 A P u s h3)). Qed.
Lemma lem4879242 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : @FINITE (A -> Prop) u) (h2 : term384 A P u s) : (term385 A u P) = (term382 A P s).
Proof. exact (prop_ext (fun h3 : term385 A u P => @lem4879241 A P u s h3 h1 h2) (fun h3 : term382 A P s => @lem4879235 A P u s h2)). Qed.
Lemma lem4879243 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : @FINITE (A -> Prop) u) (h2 : term384 A P u s) : term382 A P s.
Proof. exact (EQ_MP (@lem4879242 A P u s h1 h2) (@lem4879235 A P u s h2)). Qed.
Lemma lem4879244 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : @FINITE (A -> Prop) u) (h2 : term384 A P u s) : (@FINITE (A -> Prop) u) = (term382 A P s).
Proof. exact (prop_ext (fun h3 : @FINITE (A -> Prop) u => @lem4879243 A P u s h1 h2) (fun h3 : term382 A P s => @lem4878650 A u h1)). Qed.
Lemma lem4879245 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : @FINITE (A -> Prop) u) (h2 : term384 A P u s) : term382 A P s.
Proof. exact (EQ_MP (@lem4879244 A P u s h1 h2) (@lem4878650 A u h1)). Qed.
Lemma lem4879246 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : @FINITE (A -> Prop) u) (h2 : term383 A P u s) : (term384 A P u s) = (term382 A P s).
Proof. exact (prop_ext (fun h3 : term384 A P u s => @lem4879245 A P u s h1 h3) (fun h3 : term382 A P s => @lem4879232 A P u s h2)). Qed.
Lemma lem4879247 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : @FINITE (A -> Prop) u) (h2 : term383 A P u s) : term382 A P s.
Proof. exact (EQ_MP (@lem4879246 A P u s h1 h2) (@lem4879232 A P u s h2)). Qed.
Lemma lem4879248 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term383 A P u s) : (@FINITE (A -> Prop) u) = (term382 A P s).
Proof. exact (prop_ext (fun h2 : @FINITE (A -> Prop) u => @lem4879247 A P u s h2 h1) (fun h2 : term382 A P s => @lem4879233 A P u s h1)). Qed.
Lemma lem4879249 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term383 A P u s) : term382 A P s.
Proof. exact (EQ_MP (@lem4879248 A P u s h1) (@lem4879233 A P u s h1)). Qed.
Lemma lem4879250 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term341 A P s) : term382 A P s.
Proof. exact (ex_elim (@lem4878647 A P s h1) (fun u : type686 A => fun h0 : term527 A P s u => @lem4879249 A P u s h0)). Qed.
Lemma lem4879251 {A : Type'} (P : type686 A) (s : A -> Prop) : term530 A P s.
Proof. exact (fun h0 : term341 A P s => @lem4879250 A P s h0). Qed.
Lemma lem4879252 {A : Type'} (P : type686 A) (s : A -> Prop) : term531 A P s.
Proof. exact (conj (@lem4879251 A P s) (@lem4879231 A P s)). Qed.
Lemma lem4879253 {A : Type'} (P : type686 A) (s : A -> Prop) : (term531 A P s) = ((term341 A P s) = (term382 A P s)).
Proof. exact (@lem32 (term341 A P s) (term382 A P s)). Qed.
Lemma lem4879254 {A : Type'} (P : type686 A) (s : A -> Prop) : (term341 A P s) = (term382 A P s).
Proof. exact (EQ_MP (@lem4879253 A P s) (@lem4879252 A P s)). Qed.
Lemma lem4879255 {A : Type'} (P : type686 A) (s : A -> Prop) : (@UNION_OF A (@FINITE (A -> Prop)) P s) = (term375 A P s).
Proof. exact (EQ_MP (@lem4878646 A P s) (@lem4879254 A P s)). Qed.
Lemma lem4879260 {A : Type'} (P : type686 A) : term532 A P.
Proof. exact (fun s : A -> Prop => @lem4879255 A P s). Qed.
Lemma lem4879265 {A : Type'} : term533 A.
Proof. exact (fun P : type686 A => @lem4879260 A P). Qed.
