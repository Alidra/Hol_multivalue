Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_LT_term_abbrevs.
Require Import FINITE_DELETE_spec.
Require Import IN_DELETE_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import REAL_LTE_ADD2_spec.
Require Import SUM_CLAUSES_spec.
Require Import SUM_LE_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17646_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211683_spec.
Require Import thm3211684_spec.
Require Import thm3211692_spec.
Require Import thm3211693_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem7071856 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (h1 : term0 A s f g) : term0 A s f g.
Proof. exact (h1). Qed.
Lemma lem7071857 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (h1 : term1 A s f g) : term1 A s f g.
Proof. exact (h1). Qed.
Lemma lem7071858 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem7071859 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (h1 : term1 A s f g) : term1 A s f g.
Proof. exact (h1). Qed.
Lemma lem7071860 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (h1 : term2 A s f g) : term2 A s f g.
Proof. exact (h1). Qed.
Lemma lem7071861 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (h1 : term3 A s f g) : term3 A s f g.
Proof. exact (h1). Qed.
Lemma lem7071863 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (h1 : term2 A s f g) : term2 A s f g.
Proof. exact (h1). Qed.
Lemma lem7071864 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (a : A) (h1 : term4 A s f g a) : term4 A s f g a.
Proof. exact (h1). Qed.
Lemma lem7071865 {A : Type'} (f : A -> real) (g : A -> real) (a : A) (h1 : term5 A f g a) : term5 A f g a.
Proof. exact (h1). Qed.
Lemma lem7071866 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : @IN A a s.
Proof. exact (h1). Qed.
Lemma lem7071867 {A : Type'} (s : A -> Prop) (a : A) (h1 : s = (term6 A s a)) : s = (term6 A s a).
Proof. exact (h1). Qed.
Lemma lem7071868 {A : Type'} (f : A -> real) (g : A -> real) : (term7 A f g) = (term7 A f g).
Proof. exact (eq_refl (term7 A f g)). Qed.
Lemma lem7071869 {A : Type'} (f : A -> real) (g : A -> real) (s : A -> Prop) (a : A) (h1 : s = (term6 A s a)) : (term8 A f g s) = (term9 A f g s a).
Proof. exact (MK_COMB (@lem7071868 A f g) (@lem7071867 A s a h1)). Qed.
Lemma lem7071870 {A : Type'} (f : A -> real) (s : A -> Prop) (a : A) (g : A -> real) : (term9 A f g s a) = (term10 A f s a g).
Proof. exact (eq_refl (term9 A f g s a)). Qed.
Lemma lem7071871 {A : Type'} (f : A -> real) (g : A -> real) (s : A -> Prop) : (term11 A f g s) = (term11 A f g s).
Proof. exact (eq_refl (term11 A f g s)). Qed.
Lemma lem7071872 {A : Type'} (f : A -> real) (s : A -> Prop) (a : A) (g : A -> real) : ((term8 A f g s) = (term9 A f g s a)) = ((term8 A f g s) = (term10 A f s a g)).
Proof. exact (MK_COMB (@lem7071871 A f g s) (@lem7071870 A f s a g)). Qed.
Lemma lem7071873 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) : (term8 A f g s) = (term12 A f s g).
Proof. exact (eq_refl (term8 A f g s)). Qed.
Lemma lem7071874 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7071875 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) : (term11 A f g s) = (term13 A f s g).
Proof. exact (MK_COMB (@lem7071874) (@lem7071873 A f s g)). Qed.
Lemma lem7071876 {A : Type'} (f : A -> real) (s : A -> Prop) (a : A) (g : A -> real) : (term10 A f s a g) = (term10 A f s a g).
Proof. exact (eq_refl (term10 A f s a g)). Qed.
Lemma lem7071877 {A : Type'} (f : A -> real) (s : A -> Prop) (a : A) (g : A -> real) : ((term8 A f g s) = (term10 A f s a g)) = ((term12 A f s g) = (term10 A f s a g)).
Proof. exact (MK_COMB (@lem7071875 A f s g) (@lem7071876 A f s a g)). Qed.
Lemma lem7071878 {A : Type'} (f : A -> real) (s : A -> Prop) (a : A) (g : A -> real) : ((term8 A f g s) = (term9 A f g s a)) = ((term12 A f s g) = (term10 A f s a g)).
Proof. exact (TRANS (@lem7071872 A f s a g) (@lem7071877 A f s a g)). Qed.
Lemma lem7071879 {A : Type'} (f : A -> real) (g : A -> real) (s : A -> Prop) (a : A) (h1 : s = (term6 A s a)) : (term12 A f s g) = (term10 A f s a g).
Proof. exact (EQ_MP (@lem7071878 A f s a g) (@lem7071869 A f g s a h1)). Qed.
Lemma lem7071880 {A : Type'} (f : A -> real) (g : A -> real) (s : A -> Prop) (a : A) (h1 : s = (term6 A s a)) : (term10 A f s a g) = (term12 A f s g).
Proof. exact (SYM (@lem7071879 A f g s a h1)). Qed.
Lemma lem7071886 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term14 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem7071887 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term14 A s t).
Proof. exact (@lem7071886 A s t). Qed.
Lemma lem7071888 {A : Type'} (s : A -> Prop) (a : A) : (s = (term6 A s a)) = (term15 A s a).
Proof. exact (@lem7071887 A s (term6 A s a)). Qed.
Lemma lem7071897 {A : Type'} (a : A) (s : A -> Prop) : (term16 A a s) = (term16 A a s).
Proof. exact (eq_refl (term16 A a s)). Qed.
Lemma lem7071898 {A : Type'} (s : A -> Prop) (a : A) : (term17 A s a) = (term18 A s a).
Proof. exact (MK_COMB (@lem7071897 A a s) (@lem7071888 A s a)). Qed.
Lemma lem7071901 {A : Type'} (s : A -> Prop) (a : A) : (term18 A s a) = (term17 A s a).
Proof. exact (SYM (@lem7071898 A s a)). Qed.
Lemma lem7071905 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem7071906 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem7071905 A P x). Qed.
Lemma lem7071907 {A : Type'} (s : A -> Prop) (a : A) : (@IN A a s) = (s a).
Proof. exact (@lem7071906 A s a). Qed.
Lemma lem7071908 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7071909 {A : Type'} (s : A -> Prop) (a : A) : (term16 A a s) = (term19 A s a).
Proof. exact (MK_COMB (@lem7071908) (@lem7071907 A s a)). Qed.
Lemma lem7071917 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem7071918 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem7071917 A P x). Qed.
Lemma lem7071919 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem7071918 A s x). Qed.
Lemma lem7071920 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7071921 {A : Type'} (s : A -> Prop) (x : A) : (term20 A x s) = (term21 A s x).
Proof. exact (MK_COMB (@lem7071920) (@lem7071919 A s x)). Qed.
Lemma lem7071923 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term22 A x y s) = (term23 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem7071924 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term22 A x y s) = (term23 A y x s).
Proof. exact (@lem7071923 A y x s). Qed.
Lemma lem7071925 {A : Type'} (x : A) (s : A -> Prop) (a : A) : (term24 A x s a) = (term25 A x s a).
Proof. exact (@lem7071924 A a x (@DELETE A s a)). Qed.
Lemma lem7071931 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term26 A x s y) = (term27 A s x y).
Proof. exact (EQ_MP (@lem3211684 A s x y) (@lem3211683 A s x y)). Qed.
Lemma lem7071932 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term26 A x s y) = (term27 A s x y).
Proof. exact (@lem7071931 A s x y). Qed.
Lemma lem7071933 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term26 A x s a) = (term27 A s x a).
Proof. exact (@lem7071932 A s x a). Qed.
Lemma lem7071937 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem7071938 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem7071937 A P x). Qed.
Lemma lem7071939 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem7071938 A s x). Qed.
Lemma lem7071940 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7071941 {A : Type'} (s : A -> Prop) (x : A) : (term28 A x s) = (term29 A s x).
Proof. exact (MK_COMB (@lem7071940) (@lem7071939 A s x)). Qed.
Lemma lem7071944 {A : Type'} (x : A) (a : A) : (term30 A x a) = (term30 A x a).
Proof. exact (eq_refl (term30 A x a)). Qed.
Lemma lem7071945 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term27 A s x a) = (term31 A s x a).
Proof. exact (MK_COMB (@lem7071941 A s x) (@lem7071944 A x a)). Qed.
Lemma lem7071948 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term26 A x s a) = (term31 A s x a).
Proof. exact (TRANS (@lem7071933 A s x a) (@lem7071945 A s x a)). Qed.
Lemma lem7071949 {A : Type'} (x : A) (a : A) : (term32 A x a) = (term32 A x a).
Proof. exact (eq_refl (term32 A x a)). Qed.
Lemma lem7071950 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term25 A x s a) = (term33 A s x a).
Proof. exact (MK_COMB (@lem7071949 A x a) (@lem7071948 A s x a)). Qed.
Lemma lem7071953 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term24 A x s a) = (term33 A s x a).
Proof. exact (TRANS (@lem7071925 A x s a) (@lem7071950 A s x a)). Qed.
Lemma lem7071954 {A : Type'} (s : A -> Prop) (x : A) (a : A) : ((@IN A x s) = (term24 A x s a)) = ((s x) = (term33 A s x a)).
Proof. exact (MK_COMB (@lem7071921 A s x) (@lem7071953 A s x a)). Qed.
Lemma lem7071957 {A : Type'} (s : A -> Prop) (a : A) : (term34 A s a) = (term35 A s a).
Proof. exact (fun_ext (fun x : A => @lem7071954 A s x a)). Qed.
Lemma lem7071958 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7071959 {A : Type'} (s : A -> Prop) (a : A) : (term15 A s a) = (term36 A s a).
Proof. exact (MK_COMB (@lem7071958 A) (@lem7071957 A s a)). Qed.
Lemma lem7071964 {A : Type'} (s : A -> Prop) (a : A) : (term18 A s a) = (term37 A s a).
Proof. exact (MK_COMB (@lem7071909 A s a) (@lem7071959 A s a)). Qed.
Lemma lem7071967 {A : Type'} (s : A -> Prop) (a : A) : (term37 A s a) = (term18 A s a).
Proof. exact (SYM (@lem7071964 A s a)). Qed.
Lemma lem7071969 (p : Prop) : p = (term38 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7071970 {A : Type'} (s : A -> Prop) (a : A) : (term37 A s a) = (term39 A s a).
Proof. exact (@lem7071969 (term37 A s a)). Qed.
Lemma lem7071971 {A : Type'} (s : A -> Prop) (a : A) : (term39 A s a) = (term37 A s a).
Proof. exact (SYM (@lem7071970 A s a)). Qed.
Lemma lem7071972 {A : Type'} (s : A -> Prop) (a : A) (h1 : term40 A s a) : term40 A s a.
Proof. exact (h1). Qed.
Lemma lem7071975 {A : Type'} (s : A -> Prop) (a : A) (h1 : term39 A s a) : term39 A s a.
Proof. exact (h1). Qed.
Lemma lem7071976 {A : Type'} (s : A -> Prop) (a : A) : term41 A s a.
Proof. exact (fun h0 : term39 A s a => @lem7071975 A s a h0). Qed.
Lemma lem7071977 {A : Type'} (s : A -> Prop) (a : A) (h1 : term41 A s a) : term41 A s a.
Proof. exact (h1). Qed.
Lemma lem7071978 {A : Type'} (s : A -> Prop) (a : A) (h1 : term39 A s a) : term39 A s a.
Proof. exact (h1). Qed.
Lemma lem7071979 {A : Type'} (s : A -> Prop) (a : A) (h1 : term39 A s a) (h2 : term41 A s a) : term39 A s a.
Proof. exact (@lem7071977 A s a h2 (@lem7071978 A s a h1)). Qed.
Lemma lem7071980 {A : Type'} (s : A -> Prop) (a : A) (h1 : term39 A s a) : term42 A s a.
Proof. exact (fun h0 : term41 A s a => @lem7071979 A s a h1 h0). Qed.
Lemma lem7071981 {A : Type'} (s : A -> Prop) (a : A) (h1 : term41 A s a) : term41 A s a.
Proof. exact (h1). Qed.
Lemma lem7071982 {A : Type'} (s : A -> Prop) (a : A) (h1 : term39 A s a) (h2 : term41 A s a) : term39 A s a.
Proof. exact (@lem7071980 A s a h1 (@lem7071981 A s a h2)). Qed.
Lemma lem7071983 {A : Type'} (s : A -> Prop) (a : A) (h1 : term41 A s a) : term41 A s a.
Proof. exact (fun h0 : term39 A s a => @lem7071982 A s a h0 h1). Qed.
Lemma lem7071984 {A : Type'} (s : A -> Prop) (a : A) : term43 A s a.
Proof. exact (fun h0 : term41 A s a => @lem7071983 A s a h0). Qed.
Lemma lem7071987 {A : Type'} (s : A -> Prop) (a : A) : term41 A s a.
Proof. exact (@lem7071984 A s a (@lem7071976 A s a)). Qed.
Lemma lem7071988 {A : Type'} (s : A -> Prop) (a : A) : term41 A s a.
Proof. exact (@lem7071987 A s a). Qed.
Lemma lem7071998 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7071999 {A : Type'} (s : A -> Prop) (a : A) : (term39 A s a) = (term44 A s a).
Proof. exact (@lem7071998 (term40 A s a)). Qed.
Lemma lem7072001 (t : Prop) : (term45 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem7072002 {A : Type'} (s : A -> Prop) (a : A) : (term44 A s a) = (term37 A s a).
Proof. exact (@lem7072001 (term37 A s a)). Qed.
Lemma lem7072005 {A : Type'} (s : A -> Prop) (a : A) : (term39 A s a) = (term37 A s a).
Proof. exact (TRANS (@lem7071999 A s a) (@lem7072002 A s a)). Qed.
Lemma lem7072014 {A : Type'} (a : A) : (term46 A a) = (term47 A a).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7072005 A s a)). Qed.
Lemma lem7072015 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7072016 {A : Type'} (a : A) : (term48 A a) = (term49 A a).
Proof. exact (MK_COMB (@lem7072015 A) (@lem7072014 A a)). Qed.
Lemma lem7072021 {A : Type'} : (term50 A) = (term51 A).
Proof. exact (fun_ext (fun a : A => @lem7072016 A a)). Qed.
Lemma lem7072022 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7072031 {A : Type'} : (term52 A) = (term53 A).
Proof. exact (MK_COMB (@lem7072022 A) (@lem7072021 A)). Qed.
Lemma lem7072046 {A : Type'} (s : A -> Prop) (x : A) (a : A) : ((s x) = (term33 A s x a)) = ((s x) = (term33 A s x a)).
Proof. exact (eq_refl ((s x) = (term33 A s x a))). Qed.
Lemma lem7072047 {A : Type'} (s : A -> Prop) (a : A) : (term35 A s a) = (term35 A s a).
Proof. exact (fun_ext (fun x : A => @lem7072046 A s x a)). Qed.
Lemma lem7072048 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7072049 {A : Type'} (s : A -> Prop) (a : A) : (term36 A s a) = (term36 A s a).
Proof. exact (MK_COMB (@lem7072048 A) (@lem7072047 A s a)). Qed.
Lemma lem7072052 {A : Type'} (s : A -> Prop) (a : A) : (term19 A s a) = (term19 A s a).
Proof. exact (eq_refl (term19 A s a)). Qed.
Lemma lem7072053 {A : Type'} (s : A -> Prop) (a : A) : (term37 A s a) = (term37 A s a).
Proof. exact (MK_COMB (@lem7072052 A s a) (@lem7072049 A s a)). Qed.
Lemma lem7072054 {A : Type'} (a : A) : (term47 A a) = (term47 A a).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7072053 A s a)). Qed.
Lemma lem7072055 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7072056 {A : Type'} (a : A) : (term49 A a) = (term49 A a).
Proof. exact (MK_COMB (@lem7072055 A) (@lem7072054 A a)). Qed.
Lemma lem7072057 {A : Type'} : (term51 A) = (term51 A).
Proof. exact (fun_ext (fun a : A => @lem7072056 A a)). Qed.
Lemma lem7072058 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7072059 {A : Type'} : (term53 A) = (term53 A).
Proof. exact (MK_COMB (@lem7072058 A) (@lem7072057 A)). Qed.
Lemma lem7072086 {A : Type'} : (term52 A) = (term53 A).
Proof. exact (TRANS (@lem7072031 A) (@lem7072059 A)). Qed.
Lemma lem7072087 {A : Type'} : (term53 A) = (term52 A).
Proof. exact (SYM (@lem7072086 A)). Qed.
Lemma lem7072090 (p : Prop) : p = (term38 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7072091 {A : Type'} (s : A -> Prop) (x : A) (a : A) : ((s x) = (term33 A s x a)) = (term54 A s x a).
Proof. exact (@lem7072090 ((s x) = (term33 A s x a))). Qed.
Lemma lem7072092 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term54 A s x a) = ((s x) = (term33 A s x a)).
Proof. exact (SYM (@lem7072091 A s x a)). Qed.
Lemma lem7072093 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term55 A s x a) : term55 A s x a.
Proof. exact (h1). Qed.
Lemma lem7072099 {A : Type'} (s : A -> Prop) (a : A) (h1 : s a) : s a.
Proof. exact (h1). Qed.
Lemma lem7072109 {A : Type'} (x : A) (a : A) : (term56 A x a) = (x = a).
Proof. exact (@lem16933 (x = a)). Qed.
Lemma lem7072111 {A : Type'} (s : A -> Prop) (x : A) : (term57 A s x) = (term57 A s x).
Proof. exact (eq_refl (term57 A s x)). Qed.
Lemma lem7072112 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term58 A s x a) = (term59 A s x a).
Proof. exact (MK_COMB (@lem7072111 A s x) (@lem7072109 A x a)). Qed.
Lemma lem7072113 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term60 A s x a) = (term58 A s x a).
Proof. exact (@lem17045 (s x) (term30 A x a)). Qed.
Lemma lem7072114 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term60 A s x a) = (term59 A s x a).
Proof. exact (TRANS (@lem7072113 A s x a) (@lem7072112 A s x a)). Qed.
Lemma lem7072119 {A : Type'} (x : A) (a : A) : (term61 A x a) = (term61 A x a).
Proof. exact (eq_refl (term61 A x a)). Qed.
Lemma lem7072120 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term62 A s x a) = (term63 A s x a).
Proof. exact (MK_COMB (@lem7072119 A x a) (@lem7072114 A s x a)). Qed.
Lemma lem7072121 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term64 A s x a) = (term62 A s x a).
Proof. exact (@lem17160 (x = a) (term31 A s x a)). Qed.
Lemma lem7072122 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term64 A s x a) = (term63 A s x a).
Proof. exact (TRANS (@lem7072121 A s x a) (@lem7072120 A s x a)). Qed.
Lemma lem7072128 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term65 A s x a) = (term65 A s x a).
Proof. exact (eq_refl (term65 A s x a)). Qed.
Lemma lem7072130 {A : Type'} (s : A -> Prop) (x : A) : (term29 A s x) = (term29 A s x).
Proof. exact (eq_refl (term29 A s x)). Qed.
Lemma lem7072131 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term66 A s x a) = (term67 A s x a).
Proof. exact (MK_COMB (@lem7072130 A s x) (@lem7072122 A s x a)). Qed.
Lemma lem7072132 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7072133 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term68 A s x a) = (term69 A s x a).
Proof. exact (MK_COMB (@lem7072132) (@lem7072131 A s x a)). Qed.
Lemma lem7072134 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term70 A s x a) = (term71 A s x a).
Proof. exact (MK_COMB (@lem7072133 A s x a) (@lem7072128 A s x a)). Qed.
Lemma lem7072135 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term55 A s x a) = (term70 A s x a).
Proof. exact (@lem17646 (s x) (term33 A s x a)). Qed.
Lemma lem7072140 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term55 A s x a) = (term71 A s x a).
Proof. exact (TRANS (@lem7072135 A s x a) (@lem7072134 A s x a)). Qed.
Lemma lem7072145 {A : Type'} (s : A -> Prop) (a : A) (h1 : s a) : s a.
Proof. exact (h1). Qed.
Lemma lem7072207 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term55 A s x a) : term71 A s x a.
Proof. exact (EQ_MP (@lem7072140 A s x a) (@lem7072093 A s x a h1)). Qed.
Lemma lem7072208 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term67 A s x a) : term67 A s x a.
Proof. exact (h1). Qed.
Lemma lem7072209 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term65 A s x a) : term65 A s x a.
Proof. exact (h1). Qed.
Lemma lem7072210 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term67 A s x a) : term63 A s x a.
Proof. exact (proj2 (@lem7072208 A s x a h1)). Qed.
Lemma lem7072212 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term67 A s x a) : term59 A s x a.
Proof. exact (proj2 (@lem7072210 A s x a h1)). Qed.
Lemma lem7072216 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term65 A s x a) : term33 A s x a.
Proof. exact (proj2 (@lem7072209 A s x a h1)). Qed.
Lemma lem7072219 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term31 A s x a) : term31 A s x a.
Proof. exact (h1). Qed.
Lemma lem7072237 {A : Type'} (s : A -> Prop) (x : A) (h1 : term72 A s x) : term72 A s x.
Proof. exact (h1). Qed.
Lemma lem7072253 {A : Type'} (x : A) (a : A) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem7072257 {A : Type'} (s : A -> Prop) (a : A) (h1 : s a) : s a.
Proof. exact (h1). Qed.
Lemma lem7072265 {A : Type'} (x : A) (a : A) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem7072289 {A : Type'} (s : A -> Prop) (x : A) (h1 : term72 A s x) : term72 A s x.
Proof. exact (h1). Qed.
Lemma lem7072295 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term67 A s x a) : term30 A x a.
Proof. exact (proj1 (@lem7072210 A s x a h1)). Qed.
Lemma lem7072297 {A : Type'} (x : A) (a : A) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem7072299 {A : Type'} (s : A -> Prop) (a : A) (h1 : s a) : s a.
Proof. exact (h1). Qed.
Lemma lem7072301 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term65 A s x a) : term72 A s x.
Proof. exact (proj1 (@lem7072209 A s x a h1)). Qed.
Lemma lem7072303 {A : Type'} (x : A) (a : A) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem7072307 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term65 A s x a) : term72 A s x.
Proof. exact (proj1 (@lem7072209 A s x a h1)). Qed.
Lemma lem7072353 {A : Type'} (a : A) : (term73 A a) = (term73 A a).
Proof. exact (eq_refl (term73 A a)). Qed.
Lemma lem7072354 {A : Type'} (x : A) (a : A) (h1 : x = a) : (term74 A a x) = (term75 A a).
Proof. exact (MK_COMB (@lem7072353 A a) (@lem7072297 A x a h1)). Qed.
Lemma lem7072355 {A : Type'} (a : A) : (term75 A a) = (term76 A a).
Proof. exact (eq_refl (term75 A a)). Qed.
Lemma lem7072356 {A : Type'} (a : A) (x : A) : (term77 A a x) = (term77 A a x).
Proof. exact (eq_refl (term77 A a x)). Qed.
Lemma lem7072357 {A : Type'} (x : A) (a : A) : ((term74 A a x) = (term75 A a)) = ((term74 A a x) = (term76 A a)).
Proof. exact (MK_COMB (@lem7072356 A a x) (@lem7072355 A a)). Qed.
Lemma lem7072358 {A : Type'} (x : A) (a : A) : (term74 A a x) = (term30 A x a).
Proof. exact (eq_refl (term74 A a x)). Qed.
Lemma lem7072359 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7072360 {A : Type'} (x : A) (a : A) : (term77 A a x) = (term78 A x a).
Proof. exact (MK_COMB (@lem7072359) (@lem7072358 A x a)). Qed.
Lemma lem7072361 {A : Type'} (a : A) : (term76 A a) = (term76 A a).
Proof. exact (eq_refl (term76 A a)). Qed.
Lemma lem7072362 {A : Type'} (x : A) (a : A) : ((term74 A a x) = (term76 A a)) = ((term30 A x a) = (term76 A a)).
Proof. exact (MK_COMB (@lem7072360 A x a) (@lem7072361 A a)). Qed.
Lemma lem7072363 {A : Type'} (x : A) (a : A) : ((term74 A a x) = (term75 A a)) = ((term30 A x a) = (term76 A a)).
Proof. exact (TRANS (@lem7072357 A x a) (@lem7072362 A x a)). Qed.
Lemma lem7072364 {A : Type'} (x : A) (a : A) (h1 : x = a) : (term30 A x a) = (term76 A a).
Proof. exact (EQ_MP (@lem7072363 A x a) (@lem7072354 A x a h1)). Qed.
Lemma lem7072365 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term67 A s x a) (h2 : x = a) : term76 A a.
Proof. exact (EQ_MP (@lem7072364 A x a h2) (@lem7072295 A s x a h1)). Qed.
Lemma lem7072393 {A : Type'} (s : A -> Prop) (a : A) (h1 : s a) : s a.
Proof. exact (h1). Qed.
Lemma lem7072394 {A : Type'} (s : A -> Prop) : (term79 A s) = (term79 A s).
Proof. exact (eq_refl (term79 A s)). Qed.
Lemma lem7072395 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : x = a) : (term80 A s x) = (term80 A s a).
Proof. exact (MK_COMB (@lem7072394 A s) (@lem7072303 A x a h1)). Qed.
Lemma lem7072396 {A : Type'} (s : A -> Prop) (a : A) : (term80 A s a) = (term72 A s a).
Proof. exact (eq_refl (term80 A s a)). Qed.
Lemma lem7072397 {A : Type'} (s : A -> Prop) (x : A) : (term81 A s x) = (term81 A s x).
Proof. exact (eq_refl (term81 A s x)). Qed.
Lemma lem7072398 {A : Type'} (x : A) (s : A -> Prop) (a : A) : ((term80 A s x) = (term80 A s a)) = ((term80 A s x) = (term72 A s a)).
Proof. exact (MK_COMB (@lem7072397 A s x) (@lem7072396 A s a)). Qed.
Lemma lem7072399 {A : Type'} (s : A -> Prop) (x : A) : (term80 A s x) = (term72 A s x).
Proof. exact (eq_refl (term80 A s x)). Qed.
Lemma lem7072400 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7072401 {A : Type'} (s : A -> Prop) (x : A) : (term81 A s x) = (term82 A s x).
Proof. exact (MK_COMB (@lem7072400) (@lem7072399 A s x)). Qed.
Lemma lem7072402 {A : Type'} (s : A -> Prop) (a : A) : (term72 A s a) = (term72 A s a).
Proof. exact (eq_refl (term72 A s a)). Qed.
Lemma lem7072403 {A : Type'} (x : A) (s : A -> Prop) (a : A) : ((term80 A s x) = (term72 A s a)) = ((term72 A s x) = (term72 A s a)).
Proof. exact (MK_COMB (@lem7072401 A s x) (@lem7072402 A s a)). Qed.
Lemma lem7072404 {A : Type'} (x : A) (s : A -> Prop) (a : A) : ((term80 A s x) = (term80 A s a)) = ((term72 A s x) = (term72 A s a)).
Proof. exact (TRANS (@lem7072398 A x s a) (@lem7072403 A x s a)). Qed.
Lemma lem7072405 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : x = a) : (term72 A s x) = (term72 A s a).
Proof. exact (EQ_MP (@lem7072404 A x s a) (@lem7072395 A s x a h1)). Qed.
Lemma lem7072406 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term65 A s x a) (h2 : x = a) : term72 A s a.
Proof. exact (EQ_MP (@lem7072405 A s x a h2) (@lem7072301 A s x a h1)). Qed.
Lemma lem7072422 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term67 A s x a) : s x.
Proof. exact (proj1 (@lem7072208 A s x a h1)). Qed.
Lemma lem7072423 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term67 A s x a) : term83 A s x.
Proof. exact (fun h0 : term72 A s x => @lem7072422 A s x a h1). Qed.
Lemma lem7072425 (p : Prop) : (term84 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7072426 {A : Type'} (s : A -> Prop) (x : A) : (term83 A s x) = (s x).
Proof. exact (@lem7072425 (s x)). Qed.
Lemma lem7072427 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term67 A s x a) : s x.
Proof. exact (EQ_MP (@lem7072426 A s x) (@lem7072423 A s x a h1)). Qed.
Lemma lem7072430 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7072432 {A : Type'} (s : A -> Prop) (x : A) : (term72 A s x) = (term85 A s x).
Proof. exact (@lem7072430 (s x)). Qed.
Lemma lem7072435 {A : Type'} (s : A -> Prop) (x : A) (h1 : term72 A s x) : term85 A s x.
Proof. exact (EQ_MP (@lem7072432 A s x) (@lem7072289 A s x h1)). Qed.
Lemma lem7072438 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term72 A s x) (h2 : term67 A s x a) : False.
Proof. exact (@lem7072435 A s x h1 (@lem7072427 A s x a h2)). Qed.
Lemma lem7072439 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term72 A s x) (h2 : term67 A s x a) : term86.
Proof. exact (fun h0 : ~ False => @lem7072438 A s x a h1 h2). Qed.
Lemma lem7072441 (p : Prop) : (term84 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7072442 : term86 = False.
Proof. exact (@lem7072441 False). Qed.
Lemma lem7072443 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term72 A s x) (h2 : term67 A s x a) : False.
Proof. exact (EQ_MP (@lem7072442) (@lem7072439 A s x a h1 h2)). Qed.
Lemma lem7072459 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem7072460 {A : Type'} (x : A) : x = x.
Proof. exact (@lem7072459 A x). Qed.
Lemma lem7072461 {A : Type'} (a : A) : a = a.
Proof. exact (@lem7072460 A a). Qed.
Lemma lem7072462 {A : Type'} (a : A) : term87 A a.
Proof. exact (fun h0 : term76 A a => @lem7072461 A a). Qed.
Lemma lem7072464 (p : Prop) : (term84 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7072465 {A : Type'} (a : A) : (term87 A a) = (a = a).
Proof. exact (@lem7072464 (a = a)). Qed.
Lemma lem7072466 {A : Type'} (a : A) : a = a.
Proof. exact (EQ_MP (@lem7072465 A a) (@lem7072462 A a)). Qed.
Lemma lem7072469 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7072471 {A : Type'} (a : A) : (term76 A a) = (term88 A a).
Proof. exact (@lem7072469 (a = a)). Qed.
Lemma lem7072474 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term67 A s x a) (h2 : x = a) : term88 A a.
Proof. exact (EQ_MP (@lem7072471 A a) (@lem7072365 A s x a h1 h2)). Qed.
Lemma lem7072477 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term67 A s x a) (h2 : x = a) : False.
Proof. exact (@lem7072474 A s x a h1 h2 (@lem7072466 A a)). Qed.
Lemma lem7072478 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term67 A s x a) (h2 : x = a) : term86.
Proof. exact (fun h0 : ~ False => @lem7072477 A s x a h1 h2). Qed.
Lemma lem7072480 (p : Prop) : (term84 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7072481 : term86 = False.
Proof. exact (@lem7072480 False). Qed.
Lemma lem7072484 {A : Type'} (s : A -> Prop) (a : A) (h1 : s a) : s a.
Proof. exact (h1). Qed.
Lemma lem7072485 {A : Type'} (s : A -> Prop) (a : A) (h1 : s a) : term83 A s a.
Proof. exact (fun h0 : term72 A s a => @lem7072484 A s a h1). Qed.
Lemma lem7072487 (p : Prop) : (term84 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7072488 {A : Type'} (s : A -> Prop) (a : A) : (term83 A s a) = (s a).
Proof. exact (@lem7072487 (s a)). Qed.
Lemma lem7072489 {A : Type'} (s : A -> Prop) (a : A) (h1 : s a) : s a.
Proof. exact (EQ_MP (@lem7072488 A s a) (@lem7072485 A s a h1)). Qed.
Lemma lem7072492 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7072494 {A : Type'} (s : A -> Prop) (a : A) : (term72 A s a) = (term85 A s a).
Proof. exact (@lem7072492 (s a)). Qed.
Lemma lem7072497 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term65 A s x a) (h2 : x = a) : term85 A s a.
Proof. exact (EQ_MP (@lem7072494 A s a) (@lem7072406 A s x a h1 h2)). Qed.
Lemma lem7072500 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : s a) (h2 : term65 A s x a) (h3 : x = a) : False.
Proof. exact (@lem7072497 A s x a h2 h3 (@lem7072489 A s a h1)). Qed.
Lemma lem7072501 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : s a) (h2 : term65 A s x a) (h3 : x = a) : term86.
Proof. exact (fun h0 : ~ False => @lem7072500 A s x a h1 h2 h3). Qed.
Lemma lem7072503 (p : Prop) : (term84 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7072504 : term86 = False.
Proof. exact (@lem7072503 False). Qed.
Lemma lem7072505 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : s a) (h2 : term65 A s x a) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem7072504) (@lem7072501 A s x a h1 h2 h3)). Qed.
Lemma lem7072521 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term31 A s x a) : s x.
Proof. exact (proj1 (@lem7072219 A s x a h1)). Qed.
Lemma lem7072522 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term31 A s x a) : term83 A s x.
Proof. exact (fun h0 : term72 A s x => @lem7072521 A s x a h1). Qed.
Lemma lem7072524 (p : Prop) : (term84 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7072525 {A : Type'} (s : A -> Prop) (x : A) : (term83 A s x) = (s x).
Proof. exact (@lem7072524 (s x)). Qed.
Lemma lem7072526 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term31 A s x a) : s x.
Proof. exact (EQ_MP (@lem7072525 A s x) (@lem7072522 A s x a h1)). Qed.
Lemma lem7072529 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7072531 {A : Type'} (s : A -> Prop) (x : A) : (term72 A s x) = (term85 A s x).
Proof. exact (@lem7072529 (s x)). Qed.
Lemma lem7072534 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term65 A s x a) : term85 A s x.
Proof. exact (EQ_MP (@lem7072531 A s x) (@lem7072307 A s x a h1)). Qed.
Lemma lem7072537 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term65 A s x a) (h2 : term31 A s x a) : False.
Proof. exact (@lem7072534 A s x a h1 (@lem7072526 A s x a h2)). Qed.
Lemma lem7072538 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term65 A s x a) (h2 : term31 A s x a) : term86.
Proof. exact (fun h0 : ~ False => @lem7072537 A s x a h1 h2). Qed.
Lemma lem7072540 (p : Prop) : (term84 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7072541 : term86 = False.
Proof. exact (@lem7072540 False). Qed.
Lemma lem7072542 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term65 A s x a) (h2 : term31 A s x a) : False.
Proof. exact (EQ_MP (@lem7072541) (@lem7072538 A s x a h1 h2)). Qed.
Lemma lem7072543 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : s a) (h2 : term65 A s x a) (h3 : x = a) : (s a) = False.
Proof. exact (prop_ext (fun h4 : s a => @lem7072505 A s x a h1 h2 h3) (fun h4 : False => @lem7072393 A s a h1)). Qed.
Lemma lem7072545 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : s a) (h2 : term65 A s x a) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem7072543 A s x a h1 h2 h3) (@lem7072393 A s a h1)). Qed.
Lemma lem7072546 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term67 A s x a) (h2 : x = a) : False.
Proof. exact (EQ_MP (@lem7072481) (@lem7072478 A s x a h1 h2)). Qed.
Lemma lem7072547 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : s a) (h2 : term65 A s x a) (h3 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h4 : x = a => @lem7072545 A s x a h1 h2 h3) (fun h4 : False => @lem7072303 A x a h3)). Qed.
Lemma lem7072548 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : s a) (h2 : term65 A s x a) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem7072547 A s x a h1 h2 h3) (@lem7072303 A x a h3)). Qed.
Lemma lem7072549 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : s a) (h2 : term65 A s x a) (h3 : x = a) : (s a) = False.
Proof. exact (prop_ext (fun h4 : s a => @lem7072548 A s x a h1 h2 h3) (fun h4 : False => @lem7072299 A s a h1)). Qed.
Lemma lem7072550 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : s a) (h2 : term65 A s x a) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem7072549 A s x a h1 h2 h3) (@lem7072299 A s a h1)). Qed.
Lemma lem7072551 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term67 A s x a) (h2 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h3 : x = a => @lem7072546 A s x a h1 h2) (fun h3 : False => @lem7072297 A x a h2)). Qed.
Lemma lem7072552 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term67 A s x a) (h2 : x = a) : False.
Proof. exact (EQ_MP (@lem7072551 A s x a h1 h2) (@lem7072297 A x a h2)). Qed.
Lemma lem7072553 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term72 A s x) (h2 : term67 A s x a) : (term72 A s x) = False.
Proof. exact (prop_ext (fun h3 : term72 A s x => @lem7072443 A s x a h1 h2) (fun h3 : False => @lem7072289 A s x h1)). Qed.
Lemma lem7072554 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term72 A s x) (h2 : term67 A s x a) : False.
Proof. exact (EQ_MP (@lem7072553 A s x a h1 h2) (@lem7072289 A s x h1)). Qed.
Lemma lem7072555 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : s a) (h2 : term65 A s x a) (h3 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h4 : x = a => @lem7072550 A s x a h1 h2 h3) (fun h4 : False => @lem7072265 A x a h3)). Qed.
Lemma lem7072556 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : s a) (h2 : term65 A s x a) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem7072555 A s x a h1 h2 h3) (@lem7072265 A x a h3)). Qed.
Lemma lem7072557 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : s a) (h2 : term65 A s x a) (h3 : x = a) : (s a) = False.
Proof. exact (prop_ext (fun h4 : s a => @lem7072556 A s x a h1 h2 h3) (fun h4 : False => @lem7072257 A s a h1)). Qed.
Lemma lem7072558 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : s a) (h2 : term65 A s x a) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem7072557 A s x a h1 h2 h3) (@lem7072257 A s a h1)). Qed.
Lemma lem7072559 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term67 A s x a) (h2 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h3 : x = a => @lem7072552 A s x a h1 h2) (fun h3 : False => @lem7072253 A x a h2)). Qed.
Lemma lem7072560 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term67 A s x a) (h2 : x = a) : False.
Proof. exact (EQ_MP (@lem7072559 A s x a h1 h2) (@lem7072253 A x a h2)). Qed.
Lemma lem7072561 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term72 A s x) (h2 : term67 A s x a) : (term72 A s x) = False.
Proof. exact (prop_ext (fun h3 : term72 A s x => @lem7072554 A s x a h1 h2) (fun h3 : False => @lem7072237 A s x h1)). Qed.
Lemma lem7072562 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term72 A s x) (h2 : term67 A s x a) : False.
Proof. exact (EQ_MP (@lem7072561 A s x a h1 h2) (@lem7072237 A s x h1)). Qed.
Lemma lem7072563 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : s a) (h2 : term65 A s x a) (h3 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h4 : x = a => @lem7072558 A s x a h1 h2 h3) (fun h4 : False => @lem7072265 A x a h3)). Qed.
Lemma lem7072564 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : s a) (h2 : term65 A s x a) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem7072563 A s x a h1 h2 h3) (@lem7072265 A x a h3)). Qed.
Lemma lem7072565 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : s a) (h2 : term65 A s x a) (h3 : x = a) : (s a) = False.
Proof. exact (prop_ext (fun h4 : s a => @lem7072564 A s x a h1 h2 h3) (fun h4 : False => @lem7072257 A s a h1)). Qed.
Lemma lem7072566 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : s a) (h2 : term65 A s x a) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem7072565 A s x a h1 h2 h3) (@lem7072257 A s a h1)). Qed.
Lemma lem7072567 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term67 A s x a) (h2 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h3 : x = a => @lem7072560 A s x a h1 h2) (fun h3 : False => @lem7072253 A x a h2)). Qed.
Lemma lem7072568 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term67 A s x a) (h2 : x = a) : False.
Proof. exact (EQ_MP (@lem7072567 A s x a h1 h2) (@lem7072253 A x a h2)). Qed.
Lemma lem7072569 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term72 A s x) (h2 : term67 A s x a) : (term72 A s x) = False.
Proof. exact (prop_ext (fun h3 : term72 A s x => @lem7072562 A s x a h1 h2) (fun h3 : False => @lem7072237 A s x h1)). Qed.
Lemma lem7072570 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term72 A s x) (h2 : term67 A s x a) : False.
Proof. exact (EQ_MP (@lem7072569 A s x a h1 h2) (@lem7072237 A s x h1)). Qed.
Lemma lem7072571 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : s a) (h2 : term65 A s x a) : False.
Proof. exact (or_elim (@lem7072216 A s x a h2) (fun h0 : x = a => @lem7072566 A s x a h1 h2 h0) (fun h0 : term31 A s x a => @lem7072542 A s x a h2 h0)). Qed.
Lemma lem7072572 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term67 A s x a) : False.
Proof. exact (or_elim (@lem7072212 A s x a h1) (fun h0 : term72 A s x => @lem7072570 A s x a h0 h1) (fun h0 : x = a => @lem7072568 A s x a h1 h0)). Qed.
Lemma lem7072573 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : term55 A s x a) (h2 : s a) : False.
Proof. exact (or_elim (@lem7072207 A s x a h1) (fun h0 : term67 A s x a => @lem7072572 A s x a h0) (fun h0 : term65 A s x a => @lem7072571 A s x a h2 h0)). Qed.
Lemma lem7072574 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : term55 A s x a) (h2 : s a) : (s a) = False.
Proof. exact (prop_ext (fun h3 : s a => @lem7072573 A x s a h1 h2) (fun h3 : False => @lem7072145 A s a h2)). Qed.
Lemma lem7072575 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : term55 A s x a) (h2 : s a) : False.
Proof. exact (EQ_MP (@lem7072574 A x s a h1 h2) (@lem7072145 A s a h2)). Qed.
Lemma lem7072576 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : term55 A s x a) (h2 : s a) : (s a) = False.
Proof. exact (prop_ext (fun h3 : s a => @lem7072575 A x s a h1 h2) (fun h3 : False => @lem7072099 A s a h2)). Qed.
Lemma lem7072577 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : term55 A s x a) (h2 : s a) : False.
Proof. exact (EQ_MP (@lem7072576 A x s a h1 h2) (@lem7072099 A s a h2)). Qed.
Lemma lem7072578 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : term55 A s x a) (h2 : s a) : (term55 A s x a) = False.
Proof. exact (prop_ext (fun h3 : term55 A s x a => @lem7072577 A x s a h1 h2) (fun h3 : False => @lem7072093 A s x a h1)). Qed.
Lemma lem7072579 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : term55 A s x a) (h2 : s a) : False.
Proof. exact (EQ_MP (@lem7072578 A x s a h1 h2) (@lem7072093 A s x a h1)). Qed.
Lemma lem7072580 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : s a) : term54 A s x a.
Proof. exact (fun h0 : term55 A s x a => @lem7072579 A x s a h0 h1). Qed.
Lemma lem7072581 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : s a) : (s x) = (term33 A s x a).
Proof. exact (EQ_MP (@lem7072092 A s x a) (@lem7072580 A x s a h1)). Qed.
Lemma lem7072586 {A : Type'} (s : A -> Prop) (a : A) (h1 : s a) : term36 A s a.
Proof. exact (fun x : A => @lem7072581 A x s a h1). Qed.
Lemma lem7072587 {A : Type'} (s : A -> Prop) (a : A) : term37 A s a.
Proof. exact (fun h0 : s a => @lem7072586 A s a h0). Qed.
Lemma lem7072592 {A : Type'} (a : A) : term49 A a.
Proof. exact (fun s : A -> Prop => @lem7072587 A s a). Qed.
Lemma lem7072597 {A : Type'} : term53 A.
Proof. exact (fun a : A => @lem7072592 A a). Qed.
Lemma lem7072598 {A : Type'} : term52 A.
Proof. exact (EQ_MP (@lem7072087 A) (@lem7072597 A)). Qed.
Lemma lem7072599 {A : Type'} (a : A) : term89 A a.
Proof. exact (@lem7072598 A a). Qed.
Lemma lem7072600 {A : Type'} (a : A) : (term89 A a) = (term48 A a).
Proof. exact (eq_refl (term89 A a)). Qed.
Lemma lem7072601 {A : Type'} (a : A) : term48 A a.
Proof. exact (EQ_MP (@lem7072600 A a) (@lem7072599 A a)). Qed.
Lemma lem7072602 {A : Type'} (a : A) (s : A -> Prop) : term90 A a s.
Proof. exact (@lem7072601 A a s). Qed.
Lemma lem7072603 {A : Type'} (s : A -> Prop) (a : A) : (term90 A a s) = (term39 A s a).
Proof. exact (eq_refl (term90 A a s)). Qed.
Lemma lem7072604 {A : Type'} (s : A -> Prop) (a : A) : term39 A s a.
Proof. exact (EQ_MP (@lem7072603 A s a) (@lem7072602 A a s)). Qed.
Lemma lem7072606 {A : Type'} (s : A -> Prop) (a : A) : term39 A s a.
Proof. exact (@lem7071988 A s a (@lem7072604 A s a)). Qed.
Lemma lem7072607 {A : Type'} (s : A -> Prop) (a : A) (h1 : term40 A s a) : False.
Proof. exact (@lem7072606 A s a (@lem7071972 A s a h1)). Qed.
Lemma lem7072608 {A : Type'} (s : A -> Prop) (a : A) (h1 : term40 A s a) : (term40 A s a) = False.
Proof. exact (prop_ext (fun h2 : term40 A s a => @lem7072607 A s a h1) (fun h2 : False => @lem7071972 A s a h1)). Qed.
Lemma lem7072609 {A : Type'} (s : A -> Prop) (a : A) (h1 : term40 A s a) : False.
Proof. exact (EQ_MP (@lem7072608 A s a h1) (@lem7071972 A s a h1)). Qed.
Lemma lem7072610 {A : Type'} (s : A -> Prop) (a : A) : term39 A s a.
Proof. exact (fun h0 : term40 A s a => @lem7072609 A s a h0). Qed.
Lemma lem7072611 {A : Type'} (s : A -> Prop) (a : A) : term37 A s a.
Proof. exact (EQ_MP (@lem7071971 A s a) (@lem7072610 A s a)). Qed.
Lemma lem7072612 {A : Type'} (s : A -> Prop) (a : A) : term18 A s a.
Proof. exact (EQ_MP (@lem7071967 A s a) (@lem7072611 A s a)). Qed.
Lemma lem7072613 {A : Type'} (s : A -> Prop) (a : A) : term17 A s a.
Proof. exact (EQ_MP (@lem7071901 A s a) (@lem7072612 A s a)). Qed.
Lemma lem7072614 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : s = (term6 A s a).
Proof. exact (@lem7072613 A s a (@lem7071866 A a s h1)). Qed.
Lemma lem7072615 {A : Type'} (s : A -> Prop) : term91 A s.
Proof. exact (@lem3205803 A s). Qed.
Lemma lem7072616 {A : Type'} (s : A -> Prop) : (term91 A s) = (term92 A s).
Proof. exact (eq_refl (term91 A s)). Qed.
Lemma lem7072617 {A : Type'} (s : A -> Prop) : term92 A s.
Proof. exact (EQ_MP (@lem7072616 A s) (@lem7072615 A s)). Qed.
Lemma lem7072618 {A : Type'} (s : A -> Prop) (x : A) : term93 A s x.
Proof. exact (@lem7072617 A s x). Qed.
Lemma lem7072619 {A : Type'} (s : A -> Prop) (x : A) : (term93 A s x) = (term94 A s x).
Proof. exact (eq_refl (term93 A s x)). Qed.
Lemma lem7072620 {A : Type'} (s : A -> Prop) (x : A) : term94 A s x.
Proof. exact (EQ_MP (@lem7072619 A s x) (@lem7072618 A s x)). Qed.
Lemma lem7072621 {A : Type'} (s : A -> Prop) (x : A) (y : A) : term95 A s x y.
Proof. exact (@lem7072620 A s x y). Qed.
Lemma lem7072622 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term95 A s x y) = ((term26 A x s y) = (term27 A s x y)).
Proof. exact (eq_refl (term95 A s x y)). Qed.
Lemma lem7072624 {A : Type'} (s : A -> Prop) : term96 A s.
Proof. exact (@lem3610594 A s). Qed.
Lemma lem7072625 {A : Type'} (s : A -> Prop) : (term96 A s) = (term97 A s).
Proof. exact (eq_refl (term96 A s)). Qed.
Lemma lem7072626 {A : Type'} (s : A -> Prop) : term97 A s.
Proof. exact (EQ_MP (@lem7072625 A s) (@lem7072624 A s)). Qed.
Lemma lem7072627 {A : Type'} (s : A -> Prop) (x : A) : term98 A s x.
Proof. exact (@lem7072626 A s x). Qed.
Lemma lem7072628 {A : Type'} (x : A) (s : A -> Prop) : (term98 A s x) = ((term99 A s x) = (@FINITE A s)).
Proof. exact (eq_refl (term98 A s x)). Qed.
Lemma lem7072630 {_131524 : Type'} : term100 _131524.
Proof. exact (proj2 (@lem7067645 Prop _131524)). Qed.
Lemma lem7072631 {_131524 : Type'} (x : _131524) : term101 _131524 x.
Proof. exact (@lem7072630 _131524 x). Qed.
Lemma lem7072632 {_131524 : Type'} (x : _131524) : (term101 _131524 x) = (term102 _131524 x).
Proof. exact (eq_refl (term101 _131524 x)). Qed.
Lemma lem7072633 {_131524 : Type'} (x : _131524) : term102 _131524 x.
Proof. exact (EQ_MP (@lem7072632 _131524 x) (@lem7072631 _131524 x)). Qed.
Lemma lem7072634 {_131524 : Type'} (x : _131524) (f : _131524 -> real) : term103 _131524 x f.
Proof. exact (@lem7072633 _131524 x f). Qed.
Lemma lem7072635 {_131524 : Type'} (x : _131524) (f : _131524 -> real) : (term103 _131524 x f) = (term104 _131524 x f).
Proof. exact (eq_refl (term103 _131524 x f)). Qed.
Lemma lem7072636 {_131524 : Type'} (x : _131524) (f : _131524 -> real) : term104 _131524 x f.
Proof. exact (EQ_MP (@lem7072635 _131524 x f) (@lem7072634 _131524 x f)). Qed.
Lemma lem7072637 {_131524 : Type'} (x : _131524) (f : _131524 -> real) (s : _131524 -> Prop) : term105 _131524 x f s.
Proof. exact (@lem7072636 _131524 x f s). Qed.
Lemma lem7072638 {_131524 : Type'} (x : _131524) (s : _131524 -> Prop) (f : _131524 -> real) : (term105 _131524 x f s) = (term106 _131524 x s f).
Proof. exact (eq_refl (term105 _131524 x f s)). Qed.
Lemma lem7072639 {_131524 : Type'} (x : _131524) (s : _131524 -> Prop) (f : _131524 -> real) : term106 _131524 x s f.
Proof. exact (EQ_MP (@lem7072638 _131524 x s f) (@lem7072637 _131524 x f s)). Qed.
Lemma lem7072640 {_131524 : Type'} (s : _131524 -> Prop) (h1 : @FINITE _131524 s) : @FINITE _131524 s.
Proof. exact (h1). Qed.
Lemma lem7072641 {_131524 : Type'} (x : _131524) (f : _131524 -> real) (s : _131524 -> Prop) (h1 : @FINITE _131524 s) : (term107 _131524 x s f) = (term108 _131524 x s f).
Proof. exact (@lem7072639 _131524 x s f (@lem7072640 _131524 s h1)). Qed.
Lemma lem7072651 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem7072665 {A : Type'} (a : A) (s : A -> Prop) : (@IN A a s) = ((@IN A a s) = True).
Proof. exact (@lem7 (@IN A a s)). Qed.
Lemma lem7072670 {_131524 : Type'} (x : _131524) (s : _131524 -> Prop) (f : _131524 -> real) : term106 _131524 x s f.
Proof. exact (fun h0 : @FINITE _131524 s => @lem7072641 _131524 x f s h0). Qed.
Lemma lem7072671 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) : term106 A x s f.
Proof. exact (@lem7072670 A x s f). Qed.
Lemma lem7072672 {A : Type'} (s : A -> Prop) (a : A) (f : A -> real) : term109 A s a f.
Proof. exact (@lem7072671 A a (@DELETE A s a) f). Qed.
Lemma lem7072674 {A : Type'} (x : A) (s : A -> Prop) : (term99 A s x) = (@FINITE A s).
Proof. exact (EQ_MP (@lem7072628 A x s) (@lem7072627 A s x)). Qed.
Lemma lem7072675 {A : Type'} (x : A) (s : A -> Prop) : (term99 A s x) = (@FINITE A s).
Proof. exact (@lem7072674 A x s). Qed.
Lemma lem7072676 {A : Type'} (a : A) (s : A -> Prop) : (term99 A s a) = (@FINITE A s).
Proof. exact (@lem7072675 A a s). Qed.
Lemma lem7072678 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem7072651 A s) (@lem7071858 A s h1)). Qed.
Lemma lem7072679 {A : Type'} (a : A) (s : A -> Prop) (h1 : @FINITE A s) : (term99 A s a) = True.
Proof. exact (TRANS (@lem7072676 A a s) (@lem7072678 A s h1)). Qed.
Lemma lem7072680 {A : Type'} (a : A) (s : A -> Prop) (h1 : @FINITE A s) : True = (term99 A s a).
Proof. exact (SYM (@lem7072679 A a s h1)). Qed.
Lemma lem7072681 {A : Type'} (a : A) (s : A -> Prop) (h1 : @FINITE A s) : term99 A s a.
Proof. exact (EQ_MP (@lem7072680 A a s h1) (@lem0)). Qed.
Lemma lem7072682 {A : Type'} (a : A) (f : A -> real) (s : A -> Prop) (h1 : @FINITE A s) : (term110 A s a f) = (term111 A s a f).
Proof. exact (@lem7072672 A s a f (@lem7072681 A a s h1)). Qed.
Lemma lem7072684 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term112 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem7072685 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term113 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem7072684 _2963 g t e g' t' e'). Qed.
Lemma lem7072686 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term114 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem7072685 _2963 g t e g' t'). Qed.
Lemma lem7072687 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term115 _2963 g t e.
Proof. exact (fun g' : Prop => @lem7072686 _2963 g t e g'). Qed.
Lemma lem7072688 (g : Prop) (t : real) (e : real) : term116 g t e.
Proof. exact (@lem7072687 real g t e). Qed.
Lemma lem7072689 {A : Type'} (s : A -> Prop) (a : A) (f : A -> real) : term117 A s a f.
Proof. exact (@lem7072688 (term118 A s a) (term119 A s a f) (term120 A s a f)). Qed.
Lemma lem7072690 {A : Type'} (s : A -> Prop) (a : A) (f : A -> real) (g' : Prop) : term121 A s a f g'.
Proof. exact (@lem7072689 A s a f g'). Qed.
Lemma lem7072691 {A : Type'} (s : A -> Prop) (a : A) (f : A -> real) (g' : Prop) : (term121 A s a f g') = (term122 A s a f g').
Proof. exact (eq_refl (term121 A s a f g')). Qed.
Lemma lem7072692 {A : Type'} (s : A -> Prop) (a : A) (f : A -> real) (g' : Prop) : term122 A s a f g'.
Proof. exact (EQ_MP (@lem7072691 A s a f g') (@lem7072690 A s a f g')). Qed.
Lemma lem7072693 {A : Type'} (s : A -> Prop) (a : A) (f : A -> real) (g' : Prop) (t' : real) : term123 A s a f g' t'.
Proof. exact (@lem7072692 A s a f g' t'). Qed.
Lemma lem7072694 {A : Type'} (s : A -> Prop) (a : A) (f : A -> real) (g' : Prop) (t' : real) : (term123 A s a f g' t') = (term124 A s a f g' t').
Proof. exact (eq_refl (term123 A s a f g' t')). Qed.
Lemma lem7072695 {A : Type'} (s : A -> Prop) (a : A) (f : A -> real) (g' : Prop) (t' : real) : term124 A s a f g' t'.
Proof. exact (EQ_MP (@lem7072694 A s a f g' t') (@lem7072693 A s a f g' t')). Qed.
Lemma lem7072696 {A : Type'} (s : A -> Prop) (a : A) (f : A -> real) (g' : Prop) (t' : real) (e' : real) : term125 A s a f g' t' e'.
Proof. exact (@lem7072695 A s a f g' t' e'). Qed.
Lemma lem7072697 {A : Type'} (s : A -> Prop) (a : A) (f : A -> real) (g' : Prop) (t' : real) (e' : real) : (term125 A s a f g' t' e') = (term126 A s a f g' t' e').
Proof. exact (eq_refl (term125 A s a f g' t' e')). Qed.
Lemma lem7072698 {A : Type'} (s : A -> Prop) (a : A) (f : A -> real) (g' : Prop) (t' : real) (e' : real) : term126 A s a f g' t' e'.
Proof. exact (EQ_MP (@lem7072697 A s a f g' t' e') (@lem7072696 A s a f g' t' e')). Qed.
Lemma lem7072700 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term26 A x s y) = (term27 A s x y).
Proof. exact (EQ_MP (@lem7072622 A s x y) (@lem7072621 A s x y)). Qed.
Lemma lem7072701 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term26 A x s y) = (term27 A s x y).
Proof. exact (@lem7072700 A s x y). Qed.
Lemma lem7072702 {A : Type'} (s : A -> Prop) (a : A) : (term118 A s a) = (term127 A s a).
Proof. exact (@lem7072701 A s a a). Qed.
Lemma lem7072706 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : (@IN A a s) = True.
Proof. exact (EQ_MP (@lem7072665 A a s) (@lem7071866 A a s h1)). Qed.
Lemma lem7072707 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7072708 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : (term28 A a s) = (and True).
Proof. exact (MK_COMB (@lem7072707) (@lem7072706 A a s h1)). Qed.
Lemma lem7072710 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7072711 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem7072710 A x). Qed.
Lemma lem7072712 {A : Type'} (a : A) : (a = a) = True.
Proof. exact (@lem7072711 A a). Qed.
Lemma lem7072713 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7072714 {A : Type'} (a : A) : (term76 A a) = (~ True).
Proof. exact (MK_COMB (@lem7072713) (@lem7072712 A a)). Qed.
Lemma lem7072716 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem7072717 {A : Type'} (a : A) : (term76 A a) = False.
Proof. exact (TRANS (@lem7072714 A a) (@lem7072716)). Qed.
Lemma lem7072718 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : (term127 A s a) = (True /\ False).
Proof. exact (MK_COMB (@lem7072708 A a s h1) (@lem7072717 A a)). Qed.
Lemma lem7072720 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7072721 : (True /\ False) = False.
Proof. exact (@lem7072720 False). Qed.
Lemma lem7072722 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : (term127 A s a) = False.
Proof. exact (TRANS (@lem7072718 A a s h1) (@lem7072721)). Qed.
Lemma lem7072723 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : (term118 A s a) = False.
Proof. exact (TRANS (@lem7072702 A s a) (@lem7072722 A a s h1)). Qed.
Lemma lem7072724 {A : Type'} (s : A -> Prop) (a : A) (f : A -> real) (t' : real) (e' : real) : term128 A s a f t' e'.
Proof. exact (@lem7072698 A s a f False t' e'). Qed.
Lemma lem7072725 {A : Type'} (f : A -> real) (t' : real) (e' : real) (a : A) (s : A -> Prop) (h1 : @IN A a s) : term129 A s a f t' e'.
Proof. exact (@lem7072724 A s a f t' e' (@lem7072723 A a s h1)). Qed.
Lemma lem7072729 {A : Type'} (s : A -> Prop) (a : A) (f : A -> real) : (term119 A s a f) = (term119 A s a f).
Proof. exact (eq_refl (term119 A s a f)). Qed.
Lemma lem7072730 {A : Type'} (s : A -> Prop) (a : A) (f : A -> real) : term130 A s a f.
Proof. exact (fun h0 : False => @lem7072729 A s a f). Qed.
Lemma lem7072731 {A : Type'} (f : A -> real) (e' : real) (a : A) (s : A -> Prop) (h1 : @IN A a s) : term131 A s a f e'.
Proof. exact (@lem7072725 A f (term119 A s a f) e' a s h1). Qed.
Lemma lem7072732 {A : Type'} (f : A -> real) (e' : real) (a : A) (s : A -> Prop) (h1 : @IN A a s) : term132 A s a f e'.
Proof. exact (@lem7072731 A f e' a s h1 (@lem7072730 A s a f)). Qed.
Lemma lem7072738 {A : Type'} (s : A -> Prop) (a : A) (f : A -> real) : (term120 A s a f) = (term120 A s a f).
Proof. exact (eq_refl (term120 A s a f)). Qed.
Lemma lem7072739 {A : Type'} (s : A -> Prop) (a : A) (f : A -> real) : term133 A s a f.
Proof. exact (fun h0 : ~ False => @lem7072738 A s a f). Qed.
Lemma lem7072740 {A : Type'} (f : A -> real) (a : A) (s : A -> Prop) (h1 : @IN A a s) : term134 A s a f.
Proof. exact (@lem7072732 A f (term120 A s a f) a s h1). Qed.
Lemma lem7072741 {A : Type'} (f : A -> real) (a : A) (s : A -> Prop) (h1 : @IN A a s) : (term111 A s a f) = (term135 A s a f).
Proof. exact (@lem7072740 A f a s h1 (@lem7072739 A s a f)). Qed.
Lemma lem7072743 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem7072744 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem7072743 real t1 t2). Qed.
Lemma lem7072745 {A : Type'} (s : A -> Prop) (a : A) (f : A -> real) : (term135 A s a f) = (term120 A s a f).
Proof. exact (@lem7072744 (term119 A s a f) (term120 A s a f)). Qed.
Lemma lem7072746 {A : Type'} (f : A -> real) (a : A) (s : A -> Prop) (h1 : @IN A a s) : (term111 A s a f) = (term120 A s a f).
Proof. exact (TRANS (@lem7072741 A f a s h1) (@lem7072745 A s a f)). Qed.
Lemma lem7072747 {A : Type'} (f : A -> real) (a : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : @IN A a s) : (term110 A s a f) = (term120 A s a f).
Proof. exact (TRANS (@lem7072682 A a f s h1) (@lem7072746 A f a s h2)). Qed.
Lemma lem7072748 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7072749 {A : Type'} (f : A -> real) (a : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : @IN A a s) : (term136 A s a f) = (term137 A s a f).
Proof. exact (MK_COMB (@lem7072748) (@lem7072747 A f a s h1 h2)). Qed.
Lemma lem7072751 {_131524 : Type'} (x : _131524) (s : _131524 -> Prop) (f : _131524 -> real) : term106 _131524 x s f.
Proof. exact (fun h0 : @FINITE _131524 s => @lem7072641 _131524 x f s h0). Qed.
Lemma lem7072752 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) : term106 A x s f.
Proof. exact (@lem7072751 A x s f). Qed.
Lemma lem7072753 {A : Type'} (s : A -> Prop) (a : A) (g : A -> real) : term109 A s a g.
Proof. exact (@lem7072752 A a (@DELETE A s a) g). Qed.
Lemma lem7072755 {A : Type'} (x : A) (s : A -> Prop) : (term99 A s x) = (@FINITE A s).
Proof. exact (EQ_MP (@lem7072628 A x s) (@lem7072627 A s x)). Qed.
Lemma lem7072756 {A : Type'} (x : A) (s : A -> Prop) : (term99 A s x) = (@FINITE A s).
Proof. exact (@lem7072755 A x s). Qed.
Lemma lem7072757 {A : Type'} (a : A) (s : A -> Prop) : (term99 A s a) = (@FINITE A s).
Proof. exact (@lem7072756 A a s). Qed.
Lemma lem7072759 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem7072651 A s) (@lem7071858 A s h1)). Qed.
Lemma lem7072760 {A : Type'} (a : A) (s : A -> Prop) (h1 : @FINITE A s) : (term99 A s a) = True.
Proof. exact (TRANS (@lem7072757 A a s) (@lem7072759 A s h1)). Qed.
Lemma lem7072761 {A : Type'} (a : A) (s : A -> Prop) (h1 : @FINITE A s) : True = (term99 A s a).
Proof. exact (SYM (@lem7072760 A a s h1)). Qed.
Lemma lem7072762 {A : Type'} (a : A) (s : A -> Prop) (h1 : @FINITE A s) : term99 A s a.
Proof. exact (EQ_MP (@lem7072761 A a s h1) (@lem0)). Qed.
Lemma lem7072763 {A : Type'} (a : A) (g : A -> real) (s : A -> Prop) (h1 : @FINITE A s) : (term110 A s a g) = (term111 A s a g).
Proof. exact (@lem7072753 A s a g (@lem7072762 A a s h1)). Qed.
Lemma lem7072765 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term112 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem7072766 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term113 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem7072765 _2963 g t e g' t' e'). Qed.
Lemma lem7072767 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term114 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem7072766 _2963 g t e g' t'). Qed.
Lemma lem7072768 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term115 _2963 g t e.
Proof. exact (fun g' : Prop => @lem7072767 _2963 g t e g'). Qed.
Lemma lem7072769 (g : Prop) (t : real) (e : real) : term116 g t e.
Proof. exact (@lem7072768 real g t e). Qed.
Lemma lem7072770 {A : Type'} (s : A -> Prop) (a : A) (g : A -> real) : term117 A s a g.
Proof. exact (@lem7072769 (term118 A s a) (term119 A s a g) (term120 A s a g)). Qed.
Lemma lem7072771 {A : Type'} (s : A -> Prop) (a : A) (g : A -> real) (g' : Prop) : term121 A s a g g'.
Proof. exact (@lem7072770 A s a g g'). Qed.
Lemma lem7072772 {A : Type'} (s : A -> Prop) (a : A) (g : A -> real) (g' : Prop) : (term121 A s a g g') = (term122 A s a g g').
Proof. exact (eq_refl (term121 A s a g g')). Qed.
Lemma lem7072773 {A : Type'} (s : A -> Prop) (a : A) (g : A -> real) (g' : Prop) : term122 A s a g g'.
Proof. exact (EQ_MP (@lem7072772 A s a g g') (@lem7072771 A s a g g')). Qed.
Lemma lem7072774 {A : Type'} (s : A -> Prop) (a : A) (g : A -> real) (g' : Prop) (t' : real) : term123 A s a g g' t'.
Proof. exact (@lem7072773 A s a g g' t'). Qed.
Lemma lem7072775 {A : Type'} (s : A -> Prop) (a : A) (g : A -> real) (g' : Prop) (t' : real) : (term123 A s a g g' t') = (term124 A s a g g' t').
Proof. exact (eq_refl (term123 A s a g g' t')). Qed.
Lemma lem7072776 {A : Type'} (s : A -> Prop) (a : A) (g : A -> real) (g' : Prop) (t' : real) : term124 A s a g g' t'.
Proof. exact (EQ_MP (@lem7072775 A s a g g' t') (@lem7072774 A s a g g' t')). Qed.
Lemma lem7072777 {A : Type'} (s : A -> Prop) (a : A) (g : A -> real) (g' : Prop) (t' : real) (e' : real) : term125 A s a g g' t' e'.
Proof. exact (@lem7072776 A s a g g' t' e'). Qed.
Lemma lem7072778 {A : Type'} (s : A -> Prop) (a : A) (g : A -> real) (g' : Prop) (t' : real) (e' : real) : (term125 A s a g g' t' e') = (term126 A s a g g' t' e').
Proof. exact (eq_refl (term125 A s a g g' t' e')). Qed.
Lemma lem7072779 {A : Type'} (s : A -> Prop) (a : A) (g : A -> real) (g' : Prop) (t' : real) (e' : real) : term126 A s a g g' t' e'.
Proof. exact (EQ_MP (@lem7072778 A s a g g' t' e') (@lem7072777 A s a g g' t' e')). Qed.
Lemma lem7072781 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term26 A x s y) = (term27 A s x y).
Proof. exact (EQ_MP (@lem7072622 A s x y) (@lem7072621 A s x y)). Qed.
Lemma lem7072782 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term26 A x s y) = (term27 A s x y).
Proof. exact (@lem7072781 A s x y). Qed.
Lemma lem7072783 {A : Type'} (s : A -> Prop) (a : A) : (term118 A s a) = (term127 A s a).
Proof. exact (@lem7072782 A s a a). Qed.
Lemma lem7072787 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : (@IN A a s) = True.
Proof. exact (EQ_MP (@lem7072665 A a s) (@lem7071866 A a s h1)). Qed.
Lemma lem7072788 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7072789 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : (term28 A a s) = (and True).
Proof. exact (MK_COMB (@lem7072788) (@lem7072787 A a s h1)). Qed.
Lemma lem7072791 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7072792 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem7072791 A x). Qed.
Lemma lem7072793 {A : Type'} (a : A) : (a = a) = True.
Proof. exact (@lem7072792 A a). Qed.
Lemma lem7072794 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7072795 {A : Type'} (a : A) : (term76 A a) = (~ True).
Proof. exact (MK_COMB (@lem7072794) (@lem7072793 A a)). Qed.
Lemma lem7072797 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem7072798 {A : Type'} (a : A) : (term76 A a) = False.
Proof. exact (TRANS (@lem7072795 A a) (@lem7072797)). Qed.
Lemma lem7072799 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : (term127 A s a) = (True /\ False).
Proof. exact (MK_COMB (@lem7072789 A a s h1) (@lem7072798 A a)). Qed.
Lemma lem7072801 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7072802 : (True /\ False) = False.
Proof. exact (@lem7072801 False). Qed.
Lemma lem7072803 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : (term127 A s a) = False.
Proof. exact (TRANS (@lem7072799 A a s h1) (@lem7072802)). Qed.
Lemma lem7072804 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : (term118 A s a) = False.
Proof. exact (TRANS (@lem7072783 A s a) (@lem7072803 A a s h1)). Qed.
Lemma lem7072805 {A : Type'} (s : A -> Prop) (a : A) (g : A -> real) (t' : real) (e' : real) : term128 A s a g t' e'.
Proof. exact (@lem7072779 A s a g False t' e'). Qed.
Lemma lem7072806 {A : Type'} (g : A -> real) (t' : real) (e' : real) (a : A) (s : A -> Prop) (h1 : @IN A a s) : term129 A s a g t' e'.
Proof. exact (@lem7072805 A s a g t' e' (@lem7072804 A a s h1)). Qed.
Lemma lem7072810 {A : Type'} (s : A -> Prop) (a : A) (g : A -> real) : (term119 A s a g) = (term119 A s a g).
Proof. exact (eq_refl (term119 A s a g)). Qed.
Lemma lem7072811 {A : Type'} (s : A -> Prop) (a : A) (g : A -> real) : term130 A s a g.
Proof. exact (fun h0 : False => @lem7072810 A s a g). Qed.
Lemma lem7072812 {A : Type'} (g : A -> real) (e' : real) (a : A) (s : A -> Prop) (h1 : @IN A a s) : term131 A s a g e'.
Proof. exact (@lem7072806 A g (term119 A s a g) e' a s h1). Qed.
Lemma lem7072813 {A : Type'} (g : A -> real) (e' : real) (a : A) (s : A -> Prop) (h1 : @IN A a s) : term132 A s a g e'.
Proof. exact (@lem7072812 A g e' a s h1 (@lem7072811 A s a g)). Qed.
Lemma lem7072819 {A : Type'} (s : A -> Prop) (a : A) (g : A -> real) : (term120 A s a g) = (term120 A s a g).
Proof. exact (eq_refl (term120 A s a g)). Qed.
Lemma lem7072820 {A : Type'} (s : A -> Prop) (a : A) (g : A -> real) : term133 A s a g.
Proof. exact (fun h0 : ~ False => @lem7072819 A s a g). Qed.
Lemma lem7072821 {A : Type'} (g : A -> real) (a : A) (s : A -> Prop) (h1 : @IN A a s) : term134 A s a g.
Proof. exact (@lem7072813 A g (term120 A s a g) a s h1). Qed.
Lemma lem7072822 {A : Type'} (g : A -> real) (a : A) (s : A -> Prop) (h1 : @IN A a s) : (term111 A s a g) = (term135 A s a g).
Proof. exact (@lem7072821 A g a s h1 (@lem7072820 A s a g)). Qed.
Lemma lem7072824 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem7072825 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem7072824 real t1 t2). Qed.
Lemma lem7072826 {A : Type'} (s : A -> Prop) (a : A) (g : A -> real) : (term135 A s a g) = (term120 A s a g).
Proof. exact (@lem7072825 (term119 A s a g) (term120 A s a g)). Qed.
Lemma lem7072827 {A : Type'} (g : A -> real) (a : A) (s : A -> Prop) (h1 : @IN A a s) : (term111 A s a g) = (term120 A s a g).
Proof. exact (TRANS (@lem7072822 A g a s h1) (@lem7072826 A s a g)). Qed.
Lemma lem7072828 {A : Type'} (g : A -> real) (a : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : @IN A a s) : (term110 A s a g) = (term120 A s a g).
Proof. exact (TRANS (@lem7072763 A a g s h1) (@lem7072827 A g a s h2)). Qed.
Lemma lem7072829 {A : Type'} (f : A -> real) (g : A -> real) (a : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : @IN A a s) : (term10 A f s a g) = (term138 A f s a g).
Proof. exact (MK_COMB (@lem7072749 A f a s h1 h2) (@lem7072828 A g a s h1 h2)). Qed.
Lemma lem7072830 {A : Type'} (f : A -> real) (g : A -> real) (a : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : @IN A a s) : (term138 A f s a g) = (term10 A f s a g).
Proof. exact (SYM (@lem7072829 A f g a s h1 h2)). Qed.
Lemma lem7072831 {A : Type'} (s : A -> Prop) : term96 A s.
Proof. exact (@lem3610594 A s). Qed.
Lemma lem7072832 {A : Type'} (s : A -> Prop) : (term96 A s) = (term97 A s).
Proof. exact (eq_refl (term96 A s)). Qed.
Lemma lem7072833 {A : Type'} (s : A -> Prop) : term97 A s.
Proof. exact (EQ_MP (@lem7072832 A s) (@lem7072831 A s)). Qed.
Lemma lem7072834 {A : Type'} (s : A -> Prop) (x : A) : term98 A s x.
Proof. exact (@lem7072833 A s x). Qed.
Lemma lem7072835 {A : Type'} (x : A) (s : A -> Prop) : (term98 A s x) = ((term99 A s x) = (@FINITE A s)).
Proof. exact (eq_refl (term98 A s x)). Qed.
Lemma lem7072837 {A : Type'} (s : A -> Prop) : term91 A s.
Proof. exact (@lem3205803 A s). Qed.
Lemma lem7072838 {A : Type'} (s : A -> Prop) : (term91 A s) = (term92 A s).
Proof. exact (eq_refl (term91 A s)). Qed.
Lemma lem7072839 {A : Type'} (s : A -> Prop) : term92 A s.
Proof. exact (EQ_MP (@lem7072838 A s) (@lem7072837 A s)). Qed.
Lemma lem7072840 {A : Type'} (s : A -> Prop) (x : A) : term93 A s x.
Proof. exact (@lem7072839 A s x). Qed.
Lemma lem7072841 {A : Type'} (s : A -> Prop) (x : A) : (term93 A s x) = (term94 A s x).
Proof. exact (eq_refl (term93 A s x)). Qed.
Lemma lem7072842 {A : Type'} (s : A -> Prop) (x : A) : term94 A s x.
Proof. exact (EQ_MP (@lem7072841 A s x) (@lem7072840 A s x)). Qed.
Lemma lem7072843 {A : Type'} (s : A -> Prop) (x : A) (y : A) : term95 A s x y.
Proof. exact (@lem7072842 A s x y). Qed.
Lemma lem7072844 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term95 A s x y) = ((term26 A x s y) = (term27 A s x y)).
Proof. exact (eq_refl (term95 A s x y)). Qed.
Lemma lem7072846 {_132081 : Type'} (f : _132081 -> real) : term139 _132081 f.
Proof. exact (@lem7071845 _132081 f). Qed.
Lemma lem7072847 {_132081 : Type'} (f : _132081 -> real) : (term139 _132081 f) = (term140 _132081 f).
Proof. exact (eq_refl (term139 _132081 f)). Qed.
Lemma lem7072848 {_132081 : Type'} (f : _132081 -> real) : term140 _132081 f.
Proof. exact (EQ_MP (@lem7072847 _132081 f) (@lem7072846 _132081 f)). Qed.
Lemma lem7072849 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) : term141 _132081 f g.
Proof. exact (@lem7072848 _132081 f g). Qed.
Lemma lem7072850 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) : (term141 _132081 f g) = (term142 _132081 f g).
Proof. exact (eq_refl (term141 _132081 f g)). Qed.
Lemma lem7072851 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) : term142 _132081 f g.
Proof. exact (EQ_MP (@lem7072850 _132081 f g) (@lem7072849 _132081 f g)). Qed.
Lemma lem7072852 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (s : _132081 -> Prop) : term143 _132081 f g s.
Proof. exact (@lem7072851 _132081 f g s). Qed.
Lemma lem7072853 {_132081 : Type'} (f : _132081 -> real) (s : _132081 -> Prop) (g : _132081 -> real) : (term143 _132081 f g s) = (term144 _132081 f s g).
Proof. exact (eq_refl (term143 _132081 f g s)). Qed.
Lemma lem7072854 {_132081 : Type'} (f : _132081 -> real) (s : _132081 -> Prop) (g : _132081 -> real) : term144 _132081 f s g.
Proof. exact (EQ_MP (@lem7072853 _132081 f s g) (@lem7072852 _132081 f g s)). Qed.
Lemma lem7072855 {_132081 : Type'} (s : _132081 -> Prop) (f : _132081 -> real) (g : _132081 -> real) (h1 : term145 _132081 s f g) : term145 _132081 s f g.
Proof. exact (h1). Qed.
Lemma lem7072856 {_132081 : Type'} (s : _132081 -> Prop) (f : _132081 -> real) (g : _132081 -> real) (h1 : term145 _132081 s f g) : term146 _132081 f s g.
Proof. exact (@lem7072854 _132081 f s g (@lem7072855 _132081 s f g h1)). Qed.
Lemma lem7072857 {_132081 : Type'} (f : _132081 -> real) (s : _132081 -> Prop) (g : _132081 -> real) : (term146 _132081 f s g) = ((term146 _132081 f s g) = True).
Proof. exact (@lem7 (term146 _132081 f s g)). Qed.
Lemma lem7072858 {_132081 : Type'} (s : _132081 -> Prop) (f : _132081 -> real) (g : _132081 -> real) (h1 : term145 _132081 s f g) : (term146 _132081 f s g) = True.
Proof. exact (EQ_MP (@lem7072857 _132081 f s g) (@lem7072856 _132081 s f g h1)). Qed.
Lemma lem7072864 (w : real) : term147 w.
Proof. exact (@lem1519000 w). Qed.
Lemma lem7072865 (w : real) : (term147 w) = (term148 w).
Proof. exact (eq_refl (term147 w)). Qed.
Lemma lem7072866 (w : real) : term148 w.
Proof. exact (EQ_MP (@lem7072865 w) (@lem7072864 w)). Qed.
Lemma lem7072867 (w : real) (x : real) : term149 w x.
Proof. exact (@lem7072866 w x). Qed.
Lemma lem7072868 (w : real) (x : real) : (term149 w x) = (term150 w x).
Proof. exact (eq_refl (term149 w x)). Qed.
Lemma lem7072869 (w : real) (x : real) : term150 w x.
Proof. exact (EQ_MP (@lem7072868 w x) (@lem7072867 w x)). Qed.
Lemma lem7072870 (w : real) (x : real) (y : real) : term151 w x y.
Proof. exact (@lem7072869 w x y). Qed.
Lemma lem7072871 (w : real) (y : real) (x : real) : (term151 w x y) = (term152 w y x).
Proof. exact (eq_refl (term151 w x y)). Qed.
Lemma lem7072872 (w : real) (y : real) (x : real) : term152 w y x.
Proof. exact (EQ_MP (@lem7072871 w y x) (@lem7072870 w x y)). Qed.
Lemma lem7072873 (w : real) (y : real) (x : real) (z : real) : term153 w y x z.
Proof. exact (@lem7072872 w y x z). Qed.
Lemma lem7072874 (w : real) (y : real) (x : real) (z : real) : (term153 w y x z) = (term154 w y x z).
Proof. exact (eq_refl (term153 w y x z)). Qed.
Lemma lem7072875 (w : real) (y : real) (x : real) (z : real) : term154 w y x z.
Proof. exact (EQ_MP (@lem7072874 w y x z) (@lem7072873 w y x z)). Qed.
Lemma lem7072876 (w : real) (x : real) (y : real) (z : real) (h1 : term155 w x y z) : term155 w x y z.
Proof. exact (h1). Qed.
Lemma lem7072877 (w : real) (x : real) (y : real) (z : real) (h1 : term155 w x y z) : term156 w y x z.
Proof. exact (@lem7072875 w y x z (@lem7072876 w x y z h1)). Qed.
Lemma lem7072878 (w : real) (y : real) (x : real) (z : real) : (term156 w y x z) = ((term156 w y x z) = True).
Proof. exact (@lem7 (term156 w y x z)). Qed.
Lemma lem7072879 (w : real) (x : real) (y : real) (z : real) (h1 : term155 w x y z) : (term156 w y x z) = True.
Proof. exact (EQ_MP (@lem7072878 w y x z) (@lem7072877 w x y z h1)). Qed.
Lemma lem7072885 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem7072887 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (g : A -> real) (h1 : term3 A s f g) : term157 A s f g x.
Proof. exact (@lem7071861 A s f g h1 x). Qed.
Lemma lem7072888 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (x : A) : (term157 A s f g x) = (term158 A s f g x).
Proof. exact (eq_refl (term157 A s f g x)). Qed.
Lemma lem7072889 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (g : A -> real) (h1 : term3 A s f g) : term158 A s f g x.
Proof. exact (EQ_MP (@lem7072888 A s f g x) (@lem7072887 A x s f g h1)). Qed.
Lemma lem7072890 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem7072891 {A : Type'} (f : A -> real) (g : A -> real) (x : A) (s : A -> Prop) (h1 : term3 A s f g) (h2 : @IN A x s) : term159 A f g x.
Proof. exact (@lem7072889 A x s f g h1 (@lem7072890 A x s h2)). Qed.
Lemma lem7072892 {A : Type'} (f : A -> real) (g : A -> real) (x : A) : (term159 A f g x) = ((term159 A f g x) = True).
Proof. exact (@lem7 (term159 A f g x)). Qed.
Lemma lem7072893 {A : Type'} (f : A -> real) (g : A -> real) (x : A) (s : A -> Prop) (h1 : term3 A s f g) (h2 : @IN A x s) : (term159 A f g x) = True.
Proof. exact (EQ_MP (@lem7072892 A f g x) (@lem7072891 A f g x s h1 h2)). Qed.
Lemma lem7072901 {A : Type'} (f : A -> real) (g : A -> real) (a : A) : (term5 A f g a) = ((term5 A f g a) = True).
Proof. exact (@lem7 (term5 A f g a)). Qed.
Lemma lem7072904 (w : real) (y : real) (x : real) (z : real) : term160 w y x z.
Proof. exact (fun h0 : term155 w x y z => @lem7072879 w x y z h0). Qed.
Lemma lem7072905 {A : Type'} (f : A -> real) (s : A -> Prop) (a : A) (g : A -> real) : term161 A f s a g.
Proof. exact (@lem7072904 (f a) (term119 A s a f) (g a) (term119 A s a g)). Qed.
Lemma lem7072909 {A : Type'} (f : A -> real) (g : A -> real) (a : A) (h1 : term5 A f g a) : (term5 A f g a) = True.
Proof. exact (EQ_MP (@lem7072901 A f g a) (@lem7071865 A f g a h1)). Qed.
Lemma lem7072910 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7072911 {A : Type'} (f : A -> real) (g : A -> real) (a : A) (h1 : term5 A f g a) : (term162 A f g a) = (and True).
Proof. exact (MK_COMB (@lem7072910) (@lem7072909 A f g a h1)). Qed.
Lemma lem7072913 {_132081 : Type'} (f : _132081 -> real) (s : _132081 -> Prop) (g : _132081 -> real) : term163 _132081 f s g.
Proof. exact (fun h0 : term145 _132081 s f g => @lem7072858 _132081 s f g h0). Qed.
Lemma lem7072914 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) : term163 A f s g.
Proof. exact (@lem7072913 A f s g). Qed.
Lemma lem7072915 {A : Type'} (f : A -> real) (s : A -> Prop) (a : A) (g : A -> real) : term164 A f s a g.
Proof. exact (@lem7072914 A f (@DELETE A s a) g). Qed.
Lemma lem7072919 {A : Type'} (x : A) (s : A -> Prop) : (term99 A s x) = (@FINITE A s).
Proof. exact (EQ_MP (@lem7072835 A x s) (@lem7072834 A s x)). Qed.
Lemma lem7072920 {A : Type'} (x : A) (s : A -> Prop) : (term99 A s x) = (@FINITE A s).
Proof. exact (@lem7072919 A x s). Qed.
Lemma lem7072921 {A : Type'} (a : A) (s : A -> Prop) : (term99 A s a) = (@FINITE A s).
Proof. exact (@lem7072920 A a s). Qed.
Lemma lem7072923 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem7072885 A s) (@lem7071858 A s h1)). Qed.
Lemma lem7072924 {A : Type'} (a : A) (s : A -> Prop) (h1 : @FINITE A s) : (term99 A s a) = True.
Proof. exact (TRANS (@lem7072921 A a s) (@lem7072923 A s h1)). Qed.
Lemma lem7072925 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7072926 {A : Type'} (a : A) (s : A -> Prop) (h1 : @FINITE A s) : (term165 A s a) = (and True).
Proof. exact (MK_COMB (@lem7072925) (@lem7072924 A a s h1)). Qed.
Lemma lem7072934 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term166 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7072935 (p : Prop) (q : Prop) (p' : Prop) : term167 p q p'.
Proof. exact (fun q' : Prop => @lem7072934 p q p' q'). Qed.
Lemma lem7072936 (p : Prop) (q : Prop) : term168 p q.
Proof. exact (fun p' : Prop => @lem7072935 p q p'). Qed.
Lemma lem7072937 {A : Type'} (s : A -> Prop) (a : A) (f : A -> real) (g : A -> real) (x : A) : term169 A s a f g x.
Proof. exact (@lem7072936 (term26 A x s a) (term159 A f g x)). Qed.
Lemma lem7072938 {A : Type'} (s : A -> Prop) (a : A) (f : A -> real) (g : A -> real) (x : A) (p' : Prop) : term170 A s a f g x p'.
Proof. exact (@lem7072937 A s a f g x p'). Qed.
Lemma lem7072939 {A : Type'} (s : A -> Prop) (a : A) (f : A -> real) (g : A -> real) (x : A) (p' : Prop) : (term170 A s a f g x p') = (term171 A s a f g x p').
Proof. exact (eq_refl (term170 A s a f g x p')). Qed.
Lemma lem7072940 {A : Type'} (s : A -> Prop) (a : A) (f : A -> real) (g : A -> real) (x : A) (p' : Prop) : term171 A s a f g x p'.
Proof. exact (EQ_MP (@lem7072939 A s a f g x p') (@lem7072938 A s a f g x p')). Qed.
Lemma lem7072941 {A : Type'} (s : A -> Prop) (a : A) (f : A -> real) (g : A -> real) (x : A) (p' : Prop) (q' : Prop) : term172 A s a f g x p' q'.
Proof. exact (@lem7072940 A s a f g x p' q'). Qed.
Lemma lem7072942 {A : Type'} (s : A -> Prop) (a : A) (f : A -> real) (g : A -> real) (x : A) (p' : Prop) (q' : Prop) : (term172 A s a f g x p' q') = (term173 A s a f g x p' q').
Proof. exact (eq_refl (term172 A s a f g x p' q')). Qed.
Lemma lem7072943 {A : Type'} (s : A -> Prop) (a : A) (f : A -> real) (g : A -> real) (x : A) (p' : Prop) (q' : Prop) : term173 A s a f g x p' q'.
Proof. exact (EQ_MP (@lem7072942 A s a f g x p' q') (@lem7072941 A s a f g x p' q')). Qed.
Lemma lem7072945 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term26 A x s y) = (term27 A s x y).
Proof. exact (EQ_MP (@lem7072844 A s x y) (@lem7072843 A s x y)). Qed.
Lemma lem7072946 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term26 A x s y) = (term27 A s x y).
Proof. exact (@lem7072945 A s x y). Qed.
Lemma lem7072947 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term26 A x s a) = (term27 A s x a).
Proof. exact (@lem7072946 A s x a). Qed.
Lemma lem7072952 {A : Type'} (f : A -> real) (g : A -> real) (s : A -> Prop) (x : A) (a : A) (q' : Prop) : term174 A f g s x a q'.
Proof. exact (@lem7072943 A s a f g x (term27 A s x a) q'). Qed.
Lemma lem7072953 {A : Type'} (f : A -> real) (g : A -> real) (s : A -> Prop) (x : A) (a : A) (q' : Prop) : term175 A f g s x a q'.
Proof. exact (@lem7072952 A f g s x a q' (@lem7072947 A s x a)). Qed.
Lemma lem7072954 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term27 A s x a) : term27 A s x a.
Proof. exact (h1). Qed.
Lemma lem7072969 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term27 A s x a) : @IN A x s.
Proof. exact (proj1 (@lem7072954 A s x a h1)). Qed.
Lemma lem7072970 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = ((@IN A x s) = True).
Proof. exact (@lem7 (@IN A x s)). Qed.
Lemma lem7072973 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (g : A -> real) (h1 : term3 A s f g) : term176 A s f g x.
Proof. exact (fun h0 : @IN A x s => @lem7072893 A f g x s h1 h0). Qed.
Lemma lem7072974 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (g : A -> real) (h1 : term3 A s f g) : term176 A s f g x.
Proof. exact (@lem7072973 A x s f g h1). Qed.
Lemma lem7072976 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term27 A s x a) : (@IN A x s) = True.
Proof. exact (EQ_MP (@lem7072970 A x s) (@lem7072969 A s x a h1)). Qed.
Lemma lem7072977 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term27 A s x a) : True = (@IN A x s).
Proof. exact (SYM (@lem7072976 A s x a h1)). Qed.
Lemma lem7072978 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term27 A s x a) : @IN A x s.
Proof. exact (EQ_MP (@lem7072977 A s x a h1) (@lem0)). Qed.
Lemma lem7072979 {A : Type'} (f : A -> real) (g : A -> real) (s : A -> Prop) (x : A) (a : A) (h1 : term3 A s f g) (h2 : term27 A s x a) : (term159 A f g x) = True.
Proof. exact (@lem7072974 A x s f g h1 (@lem7072978 A s x a h2)). Qed.
Lemma lem7072980 {A : Type'} (a : A) (x : A) (s : A -> Prop) (f : A -> real) (g : A -> real) (h1 : term3 A s f g) : term177 A s a f g x.
Proof. exact (fun h0 : term27 A s x a => @lem7072979 A f g s x a h1 h0). Qed.
Lemma lem7072981 {A : Type'} (f : A -> real) (g : A -> real) (s : A -> Prop) (x : A) (a : A) : term178 A f g s x a.
Proof. exact (@lem7072953 A f g s x a True). Qed.
Lemma lem7072982 {A : Type'} (x : A) (a : A) (s : A -> Prop) (f : A -> real) (g : A -> real) (h1 : term3 A s f g) : (term179 A s a f g x) = (term180 A s x a).
Proof. exact (@lem7072981 A f g s x a (@lem7072980 A a x s f g h1)). Qed.
Lemma lem7072984 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7072985 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term180 A s x a) = True.
Proof. exact (@lem7072984 (term27 A s x a)). Qed.
Lemma lem7072986 {A : Type'} (a : A) (x : A) (s : A -> Prop) (f : A -> real) (g : A -> real) (h1 : term3 A s f g) : (term179 A s a f g x) = True.
Proof. exact (TRANS (@lem7072982 A x a s f g h1) (@lem7072985 A s x a)). Qed.
Lemma lem7072987 {A : Type'} (a : A) (s : A -> Prop) (f : A -> real) (g : A -> real) (h1 : term3 A s f g) : (term181 A s a f g) = (term182 A).
Proof. exact (fun_ext (fun x : A => @lem7072986 A a x s f g h1)). Qed.
Lemma lem7072988 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7072989 {A : Type'} (a : A) (s : A -> Prop) (f : A -> real) (g : A -> real) (h1 : term3 A s f g) : (term183 A s a f g) = (term184 A).
Proof. exact (MK_COMB (@lem7072988 A) (@lem7072987 A a s f g h1)). Qed.
Lemma lem7072991 {A : Type'} (t : Prop) : (term185 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7072992 {A : Type'} (t : Prop) : (term185 A t) = t.
Proof. exact (@lem7072991 A t). Qed.
Lemma lem7072993 {A : Type'} : (term184 A) = True.
Proof. exact (@lem7072992 A True). Qed.
Lemma lem7072994 {A : Type'} (a : A) (s : A -> Prop) (f : A -> real) (g : A -> real) (h1 : term3 A s f g) : (term183 A s a f g) = True.
Proof. exact (TRANS (@lem7072989 A a s f g h1) (@lem7072993 A)). Qed.
Lemma lem7072995 {A : Type'} (a : A) (f : A -> real) (g : A -> real) (s : A -> Prop) (h1 : term3 A s f g) (h2 : @FINITE A s) : (term186 A s a f g) = (True /\ True).
Proof. exact (MK_COMB (@lem7072926 A a s h2) (@lem7072994 A a s f g h1)). Qed.
Lemma lem7072997 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7072998 : (True /\ True) = True.
Proof. exact (@lem7072997 True). Qed.
Lemma lem7072999 {A : Type'} (a : A) (f : A -> real) (g : A -> real) (s : A -> Prop) (h1 : term3 A s f g) (h2 : @FINITE A s) : (term186 A s a f g) = True.
Proof. exact (TRANS (@lem7072995 A a f g s h1 h2) (@lem7072998)). Qed.
Lemma lem7073000 {A : Type'} (a : A) (f : A -> real) (g : A -> real) (s : A -> Prop) (h1 : term3 A s f g) (h2 : @FINITE A s) : True = (term186 A s a f g).
Proof. exact (SYM (@lem7072999 A a f g s h1 h2)). Qed.
Lemma lem7073001 {A : Type'} (a : A) (f : A -> real) (g : A -> real) (s : A -> Prop) (h1 : term3 A s f g) (h2 : @FINITE A s) : term186 A s a f g.
Proof. exact (EQ_MP (@lem7073000 A a f g s h1 h2) (@lem0)). Qed.
Lemma lem7073002 {A : Type'} (a : A) (f : A -> real) (g : A -> real) (s : A -> Prop) (h1 : term3 A s f g) (h2 : @FINITE A s) : (term187 A f s a g) = True.
Proof. exact (@lem7072915 A f s a g (@lem7073001 A a f g s h1 h2)). Qed.
Lemma lem7073003 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (a : A) (h1 : term3 A s f g) (h2 : @FINITE A s) (h3 : term5 A f g a) : (term188 A f s a g) = (True /\ True).
Proof. exact (MK_COMB (@lem7072911 A f g a h3) (@lem7073002 A a f g s h1 h2)). Qed.
Lemma lem7073005 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7073006 : (True /\ True) = True.
Proof. exact (@lem7073005 True). Qed.
Lemma lem7073007 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (a : A) (h1 : term3 A s f g) (h2 : @FINITE A s) (h3 : term5 A f g a) : (term188 A f s a g) = True.
Proof. exact (TRANS (@lem7073003 A s f g a h1 h2 h3) (@lem7073006)). Qed.
Lemma lem7073008 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (a : A) (h1 : term3 A s f g) (h2 : @FINITE A s) (h3 : term5 A f g a) : True = (term188 A f s a g).
Proof. exact (SYM (@lem7073007 A s f g a h1 h2 h3)). Qed.
Lemma lem7073009 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (a : A) (h1 : term3 A s f g) (h2 : @FINITE A s) (h3 : term5 A f g a) : term188 A f s a g.
Proof. exact (EQ_MP (@lem7073008 A s f g a h1 h2 h3) (@lem0)). Qed.
Lemma lem7073010 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (a : A) (h1 : term3 A s f g) (h2 : @FINITE A s) (h3 : term5 A f g a) : (term138 A f s a g) = True.
Proof. exact (@lem7072905 A f s a g (@lem7073009 A s f g a h1 h2 h3)). Qed.
Lemma lem7073011 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (a : A) (h1 : term3 A s f g) (h2 : @FINITE A s) (h3 : term5 A f g a) : True = (term138 A f s a g).
Proof. exact (SYM (@lem7073010 A s f g a h1 h2 h3)). Qed.
Lemma lem7073012 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (a : A) (h1 : term3 A s f g) (h2 : @FINITE A s) (h3 : term5 A f g a) : term138 A f s a g.
Proof. exact (EQ_MP (@lem7073011 A s f g a h1 h2 h3) (@lem0)). Qed.
Lemma lem7073013 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (a : A) (h1 : term3 A s f g) (h2 : @FINITE A s) (h3 : @IN A a s) (h4 : term5 A f g a) : term10 A f s a g.
Proof. exact (EQ_MP (@lem7072830 A f g a s h2 h3) (@lem7073012 A s f g a h1 h2 h4)). Qed.
Lemma lem7073014 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (a : A) (h1 : term3 A s f g) (h2 : @FINITE A s) (h3 : s = (term6 A s a)) (h4 : @IN A a s) (h5 : term5 A f g a) : term12 A f s g.
Proof. exact (EQ_MP (@lem7071880 A f g s a h3) (@lem7073013 A s f g a h1 h2 h4 h5)). Qed.
Lemma lem7073015 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (a : A) (h1 : term3 A s f g) (h2 : @FINITE A s) (h3 : @IN A a s) (h4 : term5 A f g a) : (s = (term6 A s a)) = (term12 A f s g).
Proof. exact (prop_ext (fun h5 : s = (term6 A s a) => @lem7073014 A s f g a h1 h2 h5 h3 h4) (fun h5 : term12 A f s g => @lem7072614 A a s h3)). Qed.
Lemma lem7073016 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (a : A) (h1 : term3 A s f g) (h2 : @FINITE A s) (h3 : @IN A a s) (h4 : term5 A f g a) : term12 A f s g.
Proof. exact (EQ_MP (@lem7073015 A s f g a h1 h2 h3 h4) (@lem7072614 A a s h3)). Qed.
Lemma lem7073017 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (a : A) (h1 : term4 A s f g a) : term5 A f g a.
Proof. exact (proj2 (@lem7071864 A s f g a h1)). Qed.
Lemma lem7073018 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (a : A) (h1 : term4 A s f g a) : @IN A a s.
Proof. exact (proj1 (@lem7071864 A s f g a h1)). Qed.
Lemma lem7073019 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (a : A) (h1 : term3 A s f g) (h2 : @FINITE A s) (h3 : @IN A a s) (h4 : term5 A f g a) : (term5 A f g a) = (term12 A f s g).
Proof. exact (prop_ext (fun h5 : term5 A f g a => @lem7073016 A s f g a h1 h2 h3 h4) (fun h5 : term12 A f s g => @lem7071865 A f g a h4)). Qed.
Lemma lem7073020 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (a : A) (h1 : term3 A s f g) (h2 : @FINITE A s) (h3 : @IN A a s) (h4 : term5 A f g a) : term12 A f s g.
Proof. exact (EQ_MP (@lem7073019 A s f g a h1 h2 h3 h4) (@lem7071865 A f g a h4)). Qed.
Lemma lem7073021 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (a : A) (h1 : term3 A s f g) (h2 : @FINITE A s) (h3 : @IN A a s) (h4 : term5 A f g a) : (@IN A a s) = (term12 A f s g).
Proof. exact (prop_ext (fun h5 : @IN A a s => @lem7073020 A s f g a h1 h2 h3 h4) (fun h5 : term12 A f s g => @lem7071866 A a s h3)). Qed.
Lemma lem7073022 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (a : A) (h1 : term3 A s f g) (h2 : @FINITE A s) (h3 : @IN A a s) (h4 : term5 A f g a) : term12 A f s g.
Proof. exact (EQ_MP (@lem7073021 A s f g a h1 h2 h3 h4) (@lem7071866 A a s h3)). Qed.
Lemma lem7073023 {A : Type'} (f : A -> real) (g : A -> real) (a : A) (s : A -> Prop) (h1 : term3 A s f g) (h2 : @FINITE A s) (h3 : term4 A s f g a) (h4 : @IN A a s) : (term5 A f g a) = (term12 A f s g).
Proof. exact (prop_ext (fun h5 : term5 A f g a => @lem7073022 A s f g a h1 h2 h4 h5) (fun h5 : term12 A f s g => @lem7073017 A s f g a h3)). Qed.
Lemma lem7073024 {A : Type'} (f : A -> real) (g : A -> real) (a : A) (s : A -> Prop) (h1 : term3 A s f g) (h2 : @FINITE A s) (h3 : term4 A s f g a) (h4 : @IN A a s) : term12 A f s g.
Proof. exact (EQ_MP (@lem7073023 A f g a s h1 h2 h3 h4) (@lem7073017 A s f g a h3)). Qed.
Lemma lem7073025 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (a : A) (h1 : term3 A s f g) (h2 : @FINITE A s) (h3 : term4 A s f g a) : (@IN A a s) = (term12 A f s g).
Proof. exact (prop_ext (fun h4 : @IN A a s => @lem7073024 A f g a s h1 h2 h3 h4) (fun h4 : term12 A f s g => @lem7073018 A s f g a h3)). Qed.
Lemma lem7073026 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (a : A) (h1 : term3 A s f g) (h2 : @FINITE A s) (h3 : term4 A s f g a) : term12 A f s g.
Proof. exact (EQ_MP (@lem7073025 A s f g a h1 h2 h3) (@lem7073018 A s f g a h3)). Qed.
Lemma lem7073027 {A : Type'} (f : A -> real) (g : A -> real) (s : A -> Prop) (h1 : term3 A s f g) (h2 : term2 A s f g) (h3 : @FINITE A s) : term12 A f s g.
Proof. exact (ex_elim (@lem7071863 A s f g h2) (fun a : A => fun h0 : term189 A s f g a => @lem7073026 A s f g a h1 h3 h0)). Qed.
Lemma lem7073028 {A : Type'} (f : A -> real) (g : A -> real) (s : A -> Prop) (h1 : term3 A s f g) (h2 : @FINITE A s) : term190 A f s g.
Proof. exact (fun h0 : term2 A s f g => @lem7073027 A f g s h1 h0 h2). Qed.
Lemma lem7073029 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (h1 : term1 A s f g) : term2 A s f g.
Proof. exact (proj2 (@lem7071859 A s f g h1)). Qed.
Lemma lem7073030 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (h1 : term1 A s f g) : term3 A s f g.
Proof. exact (proj1 (@lem7071859 A s f g h1)). Qed.
Lemma lem7073031 {A : Type'} (f : A -> real) (g : A -> real) (s : A -> Prop) (h1 : term3 A s f g) (h2 : term2 A s f g) (h3 : @FINITE A s) : term12 A f s g.
Proof. exact (@lem7073028 A f g s h1 h3 (@lem7071860 A s f g h2)). Qed.
Lemma lem7073032 {A : Type'} (f : A -> real) (g : A -> real) (s : A -> Prop) (h1 : term3 A s f g) (h2 : term2 A s f g) (h3 : @FINITE A s) : (term3 A s f g) = (term12 A f s g).
Proof. exact (prop_ext (fun h4 : term3 A s f g => @lem7073031 A f g s h1 h2 h3) (fun h4 : term12 A f s g => @lem7071861 A s f g h1)). Qed.
Lemma lem7073033 {A : Type'} (f : A -> real) (g : A -> real) (s : A -> Prop) (h1 : term3 A s f g) (h2 : term2 A s f g) (h3 : @FINITE A s) : term12 A f s g.
Proof. exact (EQ_MP (@lem7073032 A f g s h1 h2 h3) (@lem7071861 A s f g h1)). Qed.
Lemma lem7073034 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (h1 : term3 A s f g) (h2 : @FINITE A s) (h3 : term1 A s f g) : (term2 A s f g) = (term12 A f s g).
Proof. exact (prop_ext (fun h4 : term2 A s f g => @lem7073033 A f g s h1 h4 h2) (fun h4 : term12 A f s g => @lem7073029 A s f g h3)). Qed.
Lemma lem7073035 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (h1 : term3 A s f g) (h2 : @FINITE A s) (h3 : term1 A s f g) : term12 A f s g.
Proof. exact (EQ_MP (@lem7073034 A s f g h1 h2 h3) (@lem7073029 A s f g h3)). Qed.
Lemma lem7073036 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (h1 : @FINITE A s) (h2 : term1 A s f g) : (term3 A s f g) = (term12 A f s g).
Proof. exact (prop_ext (fun h3 : term3 A s f g => @lem7073035 A s f g h3 h1 h2) (fun h3 : term12 A f s g => @lem7073030 A s f g h2)). Qed.
Lemma lem7073037 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (h1 : @FINITE A s) (h2 : term1 A s f g) : term12 A f s g.
Proof. exact (EQ_MP (@lem7073036 A s f g h1 h2) (@lem7073030 A s f g h2)). Qed.
Lemma lem7073038 {A : Type'} (f : A -> real) (g : A -> real) (s : A -> Prop) (h1 : @FINITE A s) : term191 A f s g.
Proof. exact (fun h0 : term1 A s f g => @lem7073037 A s f g h1 h0). Qed.
Lemma lem7073039 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (h1 : term0 A s f g) : term1 A s f g.
Proof. exact (proj2 (@lem7071856 A s f g h1)). Qed.
Lemma lem7073040 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (h1 : term0 A s f g) : @FINITE A s.
Proof. exact (proj1 (@lem7071856 A s f g h1)). Qed.
Lemma lem7073041 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (h1 : @FINITE A s) (h2 : term1 A s f g) : term12 A f s g.
Proof. exact (@lem7073038 A f g s h1 (@lem7071857 A s f g h2)). Qed.
Lemma lem7073042 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (h1 : @FINITE A s) (h2 : term1 A s f g) : (@FINITE A s) = (term12 A f s g).
Proof. exact (prop_ext (fun h3 : @FINITE A s => @lem7073041 A s f g h1 h2) (fun h3 : term12 A f s g => @lem7071858 A s h1)). Qed.
Lemma lem7073043 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (h1 : @FINITE A s) (h2 : term1 A s f g) : term12 A f s g.
Proof. exact (EQ_MP (@lem7073042 A s f g h1 h2) (@lem7071858 A s h1)). Qed.
Lemma lem7073044 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (h1 : @FINITE A s) (h2 : term0 A s f g) : (term1 A s f g) = (term12 A f s g).
Proof. exact (prop_ext (fun h3 : term1 A s f g => @lem7073043 A s f g h1 h3) (fun h3 : term12 A f s g => @lem7073039 A s f g h2)). Qed.
Lemma lem7073045 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (h1 : @FINITE A s) (h2 : term0 A s f g) : term12 A f s g.
Proof. exact (EQ_MP (@lem7073044 A s f g h1 h2) (@lem7073039 A s f g h2)). Qed.
Lemma lem7073046 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (h1 : term0 A s f g) : (@FINITE A s) = (term12 A f s g).
Proof. exact (prop_ext (fun h2 : @FINITE A s => @lem7073045 A s f g h2 h1) (fun h2 : term12 A f s g => @lem7073040 A s f g h1)). Qed.
Lemma lem7073047 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (h1 : term0 A s f g) : term12 A f s g.
Proof. exact (EQ_MP (@lem7073046 A s f g h1) (@lem7073040 A s f g h1)). Qed.
Lemma lem7073048 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) : term192 A f s g.
Proof. exact (fun h0 : term0 A s f g => @lem7073047 A s f g h0). Qed.
Lemma lem7073053 {A : Type'} (f : A -> real) (g : A -> real) : term193 A f g.
Proof. exact (fun s : A -> Prop => @lem7073048 A f s g). Qed.
Lemma lem7073058 {A : Type'} (f : A -> real) : term194 A f.
Proof. exact (fun g : A -> real => @lem7073053 A f g). Qed.
Lemma lem7073063 {A : Type'} : term195 A.
Proof. exact (fun f : A -> real => @lem7073058 A f). Qed.
