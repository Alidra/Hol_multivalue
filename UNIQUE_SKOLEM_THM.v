Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import UNIQUE_SKOLEM_THM_term_abbrevs.
Require Import EXISTS_UNIQUE_THM_spec.
Require Import FORALL_AND_THM_spec.
Require Import FUN_EQ_THM_spec.
Require Import SKOLEM_THM_spec.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm13473_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1823_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm32_spec.
Require Import thm7_spec.
Lemma lem13834 {A B : Type'} (f : A -> B) : term0 A B f.
Proof. exact (@lem9220 A B f). Qed.
Lemma lem13835 {A B : Type'} (f : A -> B) : (term0 A B f) = (term1 A B f).
Proof. exact (eq_refl (term0 A B f)). Qed.
Lemma lem13836 {A B : Type'} (f : A -> B) : term1 A B f.
Proof. exact (EQ_MP (@lem13835 A B f) (@lem13834 A B f)). Qed.
Lemma lem13837 {A B : Type'} (f : A -> B) (g : A -> B) : term2 A B f g.
Proof. exact (@lem13836 A B f g). Qed.
Lemma lem13838 {A B : Type'} (f : A -> B) (g : A -> B) : (term2 A B f g) = ((f = g) = (term3 A B f g)).
Proof. exact (eq_refl (term2 A B f g)). Qed.
Lemma lem13840 {A : Type'} (P : A -> Prop) : term4 A P.
Proof. exact (@lem4997 A P). Qed.
Lemma lem13841 {A : Type'} (P : A -> Prop) : (term4 A P) = (term5 A P).
Proof. exact (eq_refl (term4 A P)). Qed.
Lemma lem13842 {A : Type'} (P : A -> Prop) : term5 A P.
Proof. exact (EQ_MP (@lem13841 A P) (@lem13840 A P)). Qed.
Lemma lem13843 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term6 A P Q.
Proof. exact (@lem13842 A P Q). Qed.
Lemma lem13844 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term6 A P Q) = ((term7 A P Q) = (term8 A P Q)).
Proof. exact (eq_refl (term6 A P Q)). Qed.
Lemma lem13846 {A B : Type'} (P : type1413 A B) : term9 A B P.
Proof. exact (@lem13546 A B P). Qed.
Lemma lem13847 {A B : Type'} (P : type1413 A B) : (term9 A B P) = ((term10 A B P) = (term11 A B P)).
Proof. exact (eq_refl (term9 A B P)). Qed.
Lemma lem13849 {A : Type'} (P : A -> Prop) : term12 A P.
Proof. exact (@lem4356 A P). Qed.
Lemma lem13850 {A : Type'} (P : A -> Prop) : (term12 A P) = ((term13 A P) = (term14 A P)).
Proof. exact (eq_refl (term12 A P)). Qed.
Lemma lem13859 {A : Type'} (P : A -> Prop) : (term13 A P) = (term14 A P).
Proof. exact (EQ_MP (@lem13850 A P) (@lem13849 A P)). Qed.
Lemma lem13860 {B : Type'} (P : B -> Prop) : (term13 B P) = (term14 B P).
Proof. exact (@lem13859 B P). Qed.
Lemma lem13861 {A B : Type'} (P : type1413 A B) (x : A) : (term15 A B P x) = (term16 A B P x).
Proof. exact (@lem13860 B (term17 A B P x)). Qed.
Lemma lem13862 {A B : Type'} (P : type1413 A B) (x : A) (y : B) : (term18 A B P x y) = (P x y).
Proof. exact (eq_refl (term18 A B P x y)). Qed.
Lemma lem13863 {A B : Type'} (P : type1413 A B) (x : A) : (term19 A B P x) = (term17 A B P x).
Proof. exact (fun_ext (fun y : B => @lem13862 A B P x y)). Qed.
Lemma lem13864 {B : Type'} : (@ex1 B) = (@ex1 B).
Proof. exact (eq_refl (@ex1 B)). Qed.
Lemma lem13865 {A B : Type'} (P : type1413 A B) (x : A) : (term15 A B P x) = (term20 A B P x).
Proof. exact (MK_COMB (@lem13864 B) (@lem13863 A B P x)). Qed.
Lemma lem13866 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem13867 {A B : Type'} (P : type1413 A B) (x : A) : (term21 A B P x) = (term22 A B P x).
Proof. exact (MK_COMB (@lem13866) (@lem13865 A B P x)). Qed.
Lemma lem13868 {A B : Type'} (P : type1413 A B) (x : A) (y : B) : (term18 A B P x y) = (P x y).
Proof. exact (eq_refl (term18 A B P x y)). Qed.
Lemma lem13869 {A B : Type'} (P : type1413 A B) (x : A) : (term19 A B P x) = (term17 A B P x).
Proof. exact (fun_ext (fun y : B => @lem13868 A B P x y)). Qed.
Lemma lem13870 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem13871 {A B : Type'} (P : type1413 A B) (x : A) : (term23 A B P x) = (term24 A B P x).
Proof. exact (MK_COMB (@lem13870 B) (@lem13869 A B P x)). Qed.
Lemma lem13872 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem13873 {A B : Type'} (P : type1413 A B) (x : A) : (term25 A B P x) = (term26 A B P x).
Proof. exact (MK_COMB (@lem13872) (@lem13871 A B P x)). Qed.
Lemma lem13874 {A B : Type'} (P : type1413 A B) (x : A) (y : B) : (term18 A B P x y) = (P x y).
Proof. exact (eq_refl (term18 A B P x y)). Qed.
Lemma lem13875 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem13876 {A B : Type'} (P : type1413 A B) (x : A) (y : B) : (term27 A B P x y) = (term28 A B P x y).
Proof. exact (MK_COMB (@lem13875) (@lem13874 A B P x y)). Qed.
Lemma lem13877 {A B : Type'} (P : type1413 A B) (x : A) (x' : B) : (term18 A B P x x') = (P x x').
Proof. exact (eq_refl (term18 A B P x x')). Qed.
Lemma lem13878 {A B : Type'} (y : B) (P : type1413 A B) (x : A) (x' : B) : (term29 A B y P x x') = (term30 A B y P x x').
Proof. exact (MK_COMB (@lem13876 A B P x y) (@lem13877 A B P x x')). Qed.
Lemma lem13879 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem13880 {A B : Type'} (y : B) (P : type1413 A B) (x : A) (x' : B) : (term31 A B y P x x') = (term32 A B y P x x').
Proof. exact (MK_COMB (@lem13879) (@lem13878 A B y P x x')). Qed.
Lemma lem13881 {B : Type'} (y : B) (x' : B) : (y = x') = (y = x').
Proof. exact (eq_refl (y = x')). Qed.
Lemma lem13882 {A B : Type'} (P : type1413 A B) (x : A) (y : B) (x' : B) : (term33 A B P x y x') = (term34 A B P x y x').
Proof. exact (MK_COMB (@lem13880 A B y P x x') (@lem13881 B y x')). Qed.
Lemma lem13883 {A B : Type'} (P : type1413 A B) (x : A) (y : B) : (term35 A B P x y) = (term36 A B P x y).
Proof. exact (fun_ext (fun x' : B => @lem13882 A B P x y x')). Qed.
Lemma lem13884 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem13885 {A B : Type'} (P : type1413 A B) (x : A) (y : B) : (term37 A B P x y) = (term38 A B P x y).
Proof. exact (MK_COMB (@lem13884 B) (@lem13883 A B P x y)). Qed.
Lemma lem13886 {A B : Type'} (P : type1413 A B) (x : A) : (term39 A B P x) = (term40 A B P x).
Proof. exact (fun_ext (fun y : B => @lem13885 A B P x y)). Qed.
Lemma lem13887 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem13888 {A B : Type'} (P : type1413 A B) (x : A) : (term41 A B P x) = (term42 A B P x).
Proof. exact (MK_COMB (@lem13887 B) (@lem13886 A B P x)). Qed.
Lemma lem13889 {A B : Type'} (P : type1413 A B) (x : A) : (term16 A B P x) = (term43 A B P x).
Proof. exact (MK_COMB (@lem13873 A B P x) (@lem13888 A B P x)). Qed.
Lemma lem13890 {A B : Type'} (P : type1413 A B) (x : A) : ((term15 A B P x) = (term16 A B P x)) = ((term20 A B P x) = (term43 A B P x)).
Proof. exact (MK_COMB (@lem13867 A B P x) (@lem13889 A B P x)). Qed.
Lemma lem13891 {A B : Type'} (P : type1413 A B) (x : A) : (term20 A B P x) = (term43 A B P x).
Proof. exact (EQ_MP (@lem13890 A B P x) (@lem13861 A B P x)). Qed.
Lemma lem13912 {A B : Type'} (P : type1413 A B) : (term44 A B P) = (term45 A B P).
Proof. exact (fun_ext (fun x : A => @lem13891 A B P x)). Qed.
Lemma lem13913 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem13914 {A B : Type'} (P : type1413 A B) : (term46 A B P) = (term47 A B P).
Proof. exact (MK_COMB (@lem13913 A) (@lem13912 A B P)). Qed.
Lemma lem13916 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term7 A P Q) = (term8 A P Q).
Proof. exact (EQ_MP (@lem13844 A P Q) (@lem13843 A P Q)). Qed.
Lemma lem13917 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term7 A P Q) = (term8 A P Q).
Proof. exact (@lem13916 A P Q). Qed.
Lemma lem13918 {A B : Type'} (P : type1413 A B) : (term48 A B P) = (term49 A B P).
Proof. exact (@lem13917 A (term50 A B P) (term51 A B P)). Qed.
Lemma lem13919 {A B : Type'} (P : type1413 A B) (x : A) : (term52 A B P x) = (term24 A B P x).
Proof. exact (eq_refl (term52 A B P x)). Qed.
Lemma lem13920 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem13921 {A B : Type'} (P : type1413 A B) (x : A) : (term53 A B P x) = (term26 A B P x).
Proof. exact (MK_COMB (@lem13920) (@lem13919 A B P x)). Qed.
Lemma lem13922 {A B : Type'} (P : type1413 A B) (x : A) : (term54 A B P x) = (term42 A B P x).
Proof. exact (eq_refl (term54 A B P x)). Qed.
Lemma lem13923 {A B : Type'} (P : type1413 A B) (x : A) : (term55 A B P x) = (term43 A B P x).
Proof. exact (MK_COMB (@lem13921 A B P x) (@lem13922 A B P x)). Qed.
Lemma lem13924 {A B : Type'} (P : type1413 A B) : (term56 A B P) = (term45 A B P).
Proof. exact (fun_ext (fun x : A => @lem13923 A B P x)). Qed.
Lemma lem13925 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem13926 {A B : Type'} (P : type1413 A B) : (term48 A B P) = (term47 A B P).
Proof. exact (MK_COMB (@lem13925 A) (@lem13924 A B P)). Qed.
Lemma lem13927 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem13928 {A B : Type'} (P : type1413 A B) : (term57 A B P) = (term58 A B P).
Proof. exact (MK_COMB (@lem13927) (@lem13926 A B P)). Qed.
Lemma lem13929 {A B : Type'} (P : type1413 A B) (x : A) : (term52 A B P x) = (term24 A B P x).
Proof. exact (eq_refl (term52 A B P x)). Qed.
Lemma lem13930 {A B : Type'} (P : type1413 A B) : (term59 A B P) = (term50 A B P).
Proof. exact (fun_ext (fun x : A => @lem13929 A B P x)). Qed.
Lemma lem13931 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem13932 {A B : Type'} (P : type1413 A B) : (term60 A B P) = (term10 A B P).
Proof. exact (MK_COMB (@lem13931 A) (@lem13930 A B P)). Qed.
Lemma lem13933 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem13934 {A B : Type'} (P : type1413 A B) : (term61 A B P) = (term62 A B P).
Proof. exact (MK_COMB (@lem13933) (@lem13932 A B P)). Qed.
Lemma lem13935 {A B : Type'} (P : type1413 A B) (x : A) : (term54 A B P x) = (term42 A B P x).
Proof. exact (eq_refl (term54 A B P x)). Qed.
Lemma lem13936 {A B : Type'} (P : type1413 A B) : (term63 A B P) = (term51 A B P).
Proof. exact (fun_ext (fun x : A => @lem13935 A B P x)). Qed.
Lemma lem13937 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem13938 {A B : Type'} (P : type1413 A B) : (term64 A B P) = (term65 A B P).
Proof. exact (MK_COMB (@lem13937 A) (@lem13936 A B P)). Qed.
Lemma lem13939 {A B : Type'} (P : type1413 A B) : (term49 A B P) = (term66 A B P).
Proof. exact (MK_COMB (@lem13934 A B P) (@lem13938 A B P)). Qed.
Lemma lem13940 {A B : Type'} (P : type1413 A B) : ((term48 A B P) = (term49 A B P)) = ((term47 A B P) = (term66 A B P)).
Proof. exact (MK_COMB (@lem13928 A B P) (@lem13939 A B P)). Qed.
Lemma lem13941 {A B : Type'} (P : type1413 A B) : (term47 A B P) = (term66 A B P).
Proof. exact (EQ_MP (@lem13940 A B P) (@lem13918 A B P)). Qed.
Lemma lem13945 {A B : Type'} (P : type1413 A B) : (term10 A B P) = (term11 A B P).
Proof. exact (EQ_MP (@lem13847 A B P) (@lem13846 A B P)). Qed.
Lemma lem13946 {A B : Type'} (P : type1413 A B) : (term10 A B P) = (term11 A B P).
Proof. exact (@lem13945 A B P). Qed.
Lemma lem13955 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem13956 {A B : Type'} (P : type1413 A B) : (term62 A B P) = (term67 A B P).
Proof. exact (MK_COMB (@lem13955) (@lem13946 A B P)). Qed.
Lemma lem13975 {A B : Type'} (P : type1413 A B) : (term65 A B P) = (term65 A B P).
Proof. exact (eq_refl (term65 A B P)). Qed.
Lemma lem13976 {A B : Type'} (P : type1413 A B) : (term66 A B P) = (term68 A B P).
Proof. exact (MK_COMB (@lem13956 A B P) (@lem13975 A B P)). Qed.
Lemma lem13979 {A B : Type'} (P : type1413 A B) : (term47 A B P) = (term68 A B P).
Proof. exact (TRANS (@lem13941 A B P) (@lem13976 A B P)). Qed.
Lemma lem13980 {A B : Type'} (P : type1413 A B) : (term46 A B P) = (term68 A B P).
Proof. exact (TRANS (@lem13914 A B P) (@lem13979 A B P)). Qed.
Lemma lem13981 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem13982 {A B : Type'} (P : type1413 A B) : (term69 A B P) = (term70 A B P).
Proof. exact (MK_COMB (@lem13981) (@lem13980 A B P)). Qed.
Lemma lem13984 {A : Type'} (P : A -> Prop) : (term13 A P) = (term14 A P).
Proof. exact (EQ_MP (@lem13850 A P) (@lem13849 A P)). Qed.
Lemma lem13985 {A B : Type'} (P : type572 A B) : (term71 A B P) = (term72 A B P).
Proof. exact (@lem13984 (A -> B) P). Qed.
Lemma lem13986 {A B : Type'} (P : type1413 A B) : (term73 A B P) = (term74 A B P).
Proof. exact (@lem13985 A B (term75 A B P)). Qed.
Lemma lem13987 {A B : Type'} (P : type1413 A B) (f : A -> B) : (term76 A B P f) = (term77 A B P f).
Proof. exact (eq_refl (term76 A B P f)). Qed.
Lemma lem13988 {A B : Type'} (P : type1413 A B) : (term78 A B P) = (term75 A B P).
Proof. exact (fun_ext (fun f : A -> B => @lem13987 A B P f)). Qed.
Lemma lem13989 {A B : Type'} : (@ex1 (A -> B)) = (@ex1 (A -> B)).
Proof. exact (eq_refl (@ex1 (A -> B))). Qed.
Lemma lem13990 {A B : Type'} (P : type1413 A B) : (term73 A B P) = (term79 A B P).
Proof. exact (MK_COMB (@lem13989 A B) (@lem13988 A B P)). Qed.
Lemma lem13991 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem13992 {A B : Type'} (P : type1413 A B) : (term80 A B P) = (term81 A B P).
Proof. exact (MK_COMB (@lem13991) (@lem13990 A B P)). Qed.
Lemma lem13993 {A B : Type'} (P : type1413 A B) (f : A -> B) : (term76 A B P f) = (term77 A B P f).
Proof. exact (eq_refl (term76 A B P f)). Qed.
Lemma lem13994 {A B : Type'} (P : type1413 A B) : (term78 A B P) = (term75 A B P).
Proof. exact (fun_ext (fun f : A -> B => @lem13993 A B P f)). Qed.
Lemma lem13995 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem13996 {A B : Type'} (P : type1413 A B) : (term82 A B P) = (term11 A B P).
Proof. exact (MK_COMB (@lem13995 A B) (@lem13994 A B P)). Qed.
Lemma lem13997 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem13998 {A B : Type'} (P : type1413 A B) : (term83 A B P) = (term67 A B P).
Proof. exact (MK_COMB (@lem13997) (@lem13996 A B P)). Qed.
Lemma lem13999 {A B : Type'} (P : type1413 A B) (f : A -> B) : (term76 A B P f) = (term77 A B P f).
Proof. exact (eq_refl (term76 A B P f)). Qed.
Lemma lem14000 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem14001 {A B : Type'} (P : type1413 A B) (f : A -> B) : (term84 A B P f) = (term85 A B P f).
Proof. exact (MK_COMB (@lem14000) (@lem13999 A B P f)). Qed.
Lemma lem14002 {A B : Type'} (P : type1413 A B) (x' : A -> B) : (term76 A B P x') = (term77 A B P x').
Proof. exact (eq_refl (term76 A B P x')). Qed.
Lemma lem14003 {A B : Type'} (f : A -> B) (P : type1413 A B) (x' : A -> B) : (term86 A B f P x') = (term87 A B f P x').
Proof. exact (MK_COMB (@lem14001 A B P f) (@lem14002 A B P x')). Qed.
Lemma lem14004 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem14005 {A B : Type'} (f : A -> B) (P : type1413 A B) (x' : A -> B) : (term88 A B f P x') = (term89 A B f P x').
Proof. exact (MK_COMB (@lem14004) (@lem14003 A B f P x')). Qed.
Lemma lem14006 {A B : Type'} (f : A -> B) (x' : A -> B) : (f = x') = (f = x').
Proof. exact (eq_refl (f = x')). Qed.
Lemma lem14007 {A B : Type'} (P : type1413 A B) (f : A -> B) (x' : A -> B) : (term90 A B P f x') = (term91 A B P f x').
Proof. exact (MK_COMB (@lem14005 A B f P x') (@lem14006 A B f x')). Qed.
Lemma lem14008 {A B : Type'} (P : type1413 A B) (f : A -> B) : (term92 A B P f) = (term93 A B P f).
Proof. exact (fun_ext (fun x' : A -> B => @lem14007 A B P f x')). Qed.
Lemma lem14009 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem14010 {A B : Type'} (P : type1413 A B) (f : A -> B) : (term94 A B P f) = (term95 A B P f).
Proof. exact (MK_COMB (@lem14009 A B) (@lem14008 A B P f)). Qed.
Lemma lem14011 {A B : Type'} (P : type1413 A B) : (term96 A B P) = (term97 A B P).
Proof. exact (fun_ext (fun f : A -> B => @lem14010 A B P f)). Qed.
Lemma lem14012 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem14013 {A B : Type'} (P : type1413 A B) : (term98 A B P) = (term99 A B P).
Proof. exact (MK_COMB (@lem14012 A B) (@lem14011 A B P)). Qed.
Lemma lem14014 {A B : Type'} (P : type1413 A B) : (term74 A B P) = (term100 A B P).
Proof. exact (MK_COMB (@lem13998 A B P) (@lem14013 A B P)). Qed.
Lemma lem14015 {A B : Type'} (P : type1413 A B) : ((term73 A B P) = (term74 A B P)) = ((term79 A B P) = (term100 A B P)).
Proof. exact (MK_COMB (@lem13992 A B P) (@lem14014 A B P)). Qed.
Lemma lem14016 {A B : Type'} (P : type1413 A B) : (term79 A B P) = (term100 A B P).
Proof. exact (EQ_MP (@lem14015 A B P) (@lem13986 A B P)). Qed.
Lemma lem14049 {A B : Type'} (P : type1413 A B) : ((term46 A B P) = (term79 A B P)) = ((term68 A B P) = (term100 A B P)).
Proof. exact (MK_COMB (@lem13982 A B P) (@lem14016 A B P)). Qed.
Lemma lem14052 {A B : Type'} (P : type1413 A B) : ((term68 A B P) = (term100 A B P)) = ((term46 A B P) = (term79 A B P)).
Proof. exact (SYM (@lem14049 A B P)). Qed.
Lemma lem14053 {A B : Type'} (P : type1413 A B) (h1 : term68 A B P) : term68 A B P.
Proof. exact (h1). Qed.
Lemma lem14054 {A B : Type'} (P : type1413 A B) (h1 : term65 A B P) : term65 A B P.
Proof. exact (h1). Qed.
Lemma lem14055 {A B : Type'} (P : type1413 A B) (h1 : term11 A B P) : term11 A B P.
Proof. exact (h1). Qed.
Lemma lem14056 {A B : Type'} (P : type1413 A B) (h1 : term100 A B P) : term100 A B P.
Proof. exact (h1). Qed.
Lemma lem14057 {A B : Type'} (P : type1413 A B) (h1 : term99 A B P) : term99 A B P.
Proof. exact (h1). Qed.
Lemma lem14058 {A B : Type'} (P : type1413 A B) (h1 : term11 A B P) : term11 A B P.
Proof. exact (h1). Qed.
Lemma lem14059 {A B : Type'} (P : type1413 A B) : (term11 A B P) = ((term11 A B P) = True).
Proof. exact (@lem7 (term11 A B P)). Qed.
Lemma lem14075 {A B : Type'} (P : type1413 A B) (h1 : term11 A B P) : (term11 A B P) = True.
Proof. exact (EQ_MP (@lem14059 A B P) (@lem14055 A B P h1)). Qed.
Lemma lem14076 {A B : Type'} (P : type1413 A B) (h1 : term11 A B P) : (term11 A B P) = True.
Proof. exact (@lem14075 A B P h1). Qed.
Lemma lem14077 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem14078 {A B : Type'} (P : type1413 A B) (h1 : term11 A B P) : (term67 A B P) = (and True).
Proof. exact (MK_COMB (@lem14077) (@lem14076 A B P h1)). Qed.
Lemma lem14101 {A B : Type'} (P : type1413 A B) : (term99 A B P) = (term99 A B P).
Proof. exact (eq_refl (term99 A B P)). Qed.
Lemma lem14102 {A B : Type'} (P : type1413 A B) (h1 : term11 A B P) : (term100 A B P) = (term101 A B P).
Proof. exact (MK_COMB (@lem14078 A B P h1) (@lem14101 A B P)). Qed.
Lemma lem14104 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem14105 {A B : Type'} (P : type1413 A B) : (term101 A B P) = (term99 A B P).
Proof. exact (@lem14104 (term99 A B P)). Qed.
Lemma lem14128 {A B : Type'} (P : type1413 A B) (h1 : term11 A B P) : (term100 A B P) = (term99 A B P).
Proof. exact (TRANS (@lem14102 A B P h1) (@lem14105 A B P)). Qed.
Lemma lem14129 {A B : Type'} (P : type1413 A B) (h1 : term11 A B P) : (term99 A B P) = (term100 A B P).
Proof. exact (SYM (@lem14128 A B P h1)). Qed.
Lemma lem14130 {A B : Type'} (P : type1413 A B) : (term11 A B P) = ((term11 A B P) = True).
Proof. exact (@lem7 (term11 A B P)). Qed.
Lemma lem14143 {A B : Type'} (P : type1413 A B) (h1 : term11 A B P) : (term11 A B P) = True.
Proof. exact (EQ_MP (@lem14130 A B P) (@lem14058 A B P h1)). Qed.
Lemma lem14144 {A B : Type'} (P : type1413 A B) (h1 : term11 A B P) : (term11 A B P) = True.
Proof. exact (@lem14143 A B P h1). Qed.
Lemma lem14145 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem14146 {A B : Type'} (P : type1413 A B) (h1 : term11 A B P) : (term67 A B P) = (and True).
Proof. exact (MK_COMB (@lem14145) (@lem14144 A B P h1)). Qed.
Lemma lem14165 {A B : Type'} (P : type1413 A B) : (term65 A B P) = (term65 A B P).
Proof. exact (eq_refl (term65 A B P)). Qed.
Lemma lem14166 {A B : Type'} (P : type1413 A B) (h1 : term11 A B P) : (term68 A B P) = (term102 A B P).
Proof. exact (MK_COMB (@lem14146 A B P h1) (@lem14165 A B P)). Qed.
Lemma lem14168 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem14169 {A B : Type'} (P : type1413 A B) : (term102 A B P) = (term65 A B P).
Proof. exact (@lem14168 (term65 A B P)). Qed.
Lemma lem14188 {A B : Type'} (P : type1413 A B) (h1 : term11 A B P) : (term68 A B P) = (term65 A B P).
Proof. exact (TRANS (@lem14166 A B P h1) (@lem14169 A B P)). Qed.
Lemma lem14189 {A B : Type'} (P : type1413 A B) (h1 : term11 A B P) : (term65 A B P) = (term68 A B P).
Proof. exact (SYM (@lem14188 A B P h1)). Qed.
Lemma lem14190 {A B : Type'} (f : A -> B) (P : type1413 A B) (x' : A -> B) (h1 : term87 A B f P x') : term87 A B f P x'.
Proof. exact (h1). Qed.
Lemma lem14191 {A B : Type'} (P : type1413 A B) (x' : A -> B) (h1 : term77 A B P x') : term77 A B P x'.
Proof. exact (h1). Qed.
Lemma lem14192 {A B : Type'} (P : type1413 A B) (f : A -> B) (h1 : term77 A B P f) : term77 A B P f.
Proof. exact (h1). Qed.
Lemma lem14196 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term3 A B f g).
Proof. exact (EQ_MP (@lem13838 A B f g) (@lem13837 A B f g)). Qed.
Lemma lem14197 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term3 A B f g).
Proof. exact (@lem14196 A B f g). Qed.
Lemma lem14198 {A B : Type'} (f : A -> B) (x' : A -> B) : (f = x') = (term3 A B f x').
Proof. exact (@lem14197 A B f x'). Qed.
Lemma lem14199 {A B : Type'} (f : A -> B) (x' : A -> B) : (term3 A B f x') = (f = x').
Proof. exact (SYM (@lem14198 A B f x')). Qed.
Lemma lem14200 {A B : Type'} (P : type1413 A B) (h1 : term65 A B P) : term65 A B P.
Proof. exact (h1). Qed.
Lemma lem14201 {A B : Type'} (x : A) (P : type1413 A B) (h1 : term65 A B P) : term54 A B P x.
Proof. exact (@lem14200 A B P h1 x). Qed.
Lemma lem14202 {A B : Type'} (P : type1413 A B) (x : A) : (term54 A B P x) = (term42 A B P x).
Proof. exact (eq_refl (term54 A B P x)). Qed.
Lemma lem14203 {A B : Type'} (x : A) (P : type1413 A B) (h1 : term65 A B P) : term42 A B P x.
Proof. exact (EQ_MP (@lem14202 A B P x) (@lem14201 A B x P h1)). Qed.
Lemma lem14204 {A B : Type'} (x : A) (y : B) (P : type1413 A B) (h1 : term65 A B P) : term103 A B P x y.
Proof. exact (@lem14203 A B x P h1 y). Qed.
Lemma lem14205 {A B : Type'} (P : type1413 A B) (x : A) (y : B) : (term103 A B P x y) = (term38 A B P x y).
Proof. exact (eq_refl (term103 A B P x y)). Qed.
Lemma lem14206 {A B : Type'} (x : A) (y : B) (P : type1413 A B) (h1 : term65 A B P) : term38 A B P x y.
Proof. exact (EQ_MP (@lem14205 A B P x y) (@lem14204 A B x y P h1)). Qed.
Lemma lem14207 {A B : Type'} (x : A) (y : B) (x' : B) (P : type1413 A B) (h1 : term65 A B P) : term104 A B P x y x'.
Proof. exact (@lem14206 A B x y P h1 x'). Qed.
Lemma lem14208 {A B : Type'} (P : type1413 A B) (x : A) (y : B) (x' : B) : (term104 A B P x y x') = (term34 A B P x y x').
Proof. exact (eq_refl (term104 A B P x y x')). Qed.
Lemma lem14209 {A B : Type'} (x : A) (y : B) (x' : B) (P : type1413 A B) (h1 : term65 A B P) : term34 A B P x y x'.
Proof. exact (EQ_MP (@lem14208 A B P x y x') (@lem14207 A B x y x' P h1)). Qed.
Lemma lem14210 {A B : Type'} (y : B) (P : type1413 A B) (x : A) (x' : B) (h1 : term30 A B y P x x') : term30 A B y P x x'.
Proof. exact (h1). Qed.
Lemma lem14211 {A B : Type'} (y : B) (P : type1413 A B) (x : A) (x' : B) (h1 : term65 A B P) (h2 : term30 A B y P x x') : y = x'.
Proof. exact (@lem14209 A B x y x' P h1 (@lem14210 A B y P x x' h2)). Qed.
Lemma lem14212 {A B : Type'} (y : B) (P : type1413 A B) (x : A) (x' : B) (h1 : term30 A B y P x x') : term105 A B P y x'.
Proof. exact (fun h0 : term65 A B P => @lem14211 A B y P x x' h0 h1). Qed.
Lemma lem14213 {A B : Type'} (y : B) (P : type1413 A B) (x' : B) (h1 : term106 A B y P x') : term106 A B y P x'.
Proof. exact (h1). Qed.
Lemma lem14214 {A B : Type'} (y : B) (P : type1413 A B) (x' : B) (h1 : term106 A B y P x') : term105 A B P y x'.
Proof. exact (ex_elim (@lem14213 A B y P x' h1) (fun x : A => fun h0 : term107 A B y P x' x => @lem14212 A B y P x x' h0)). Qed.
Lemma lem14215 {A B : Type'} (P : type1413 A B) (h1 : term65 A B P) : term65 A B P.
Proof. exact (h1). Qed.
Lemma lem14216 {A B : Type'} (y : B) (P : type1413 A B) (x' : B) (h1 : term65 A B P) (h2 : term106 A B y P x') : y = x'.
Proof. exact (@lem14214 A B y P x' h2 (@lem14215 A B P h1)). Qed.
Lemma lem14217 {A B : Type'} (y : B) (x' : B) (P : type1413 A B) (h1 : term65 A B P) : term108 A B P y x'.
Proof. exact (fun h0 : term106 A B y P x' => @lem14216 A B y P x' h1 h0). Qed.
Lemma lem14218 {A B : Type'} (y : B) (P : type1413 A B) (h1 : term65 A B P) : term109 A B P y.
Proof. exact (fun x' : B => @lem14217 A B y x' P h1). Qed.
Lemma lem14219 {A B : Type'} (P : type1413 A B) (h1 : term65 A B P) : term110 A B P.
Proof. exact (fun y : B => @lem14218 A B y P h1). Qed.
Lemma lem14220 {A B : Type'} (P : type1413 A B) : term111 A B P.
Proof. exact (fun h0 : term65 A B P => @lem14219 A B P h0). Qed.
Lemma lem14221 {A B : Type'} (P : type1413 A B) (h1 : term65 A B P) : term110 A B P.
Proof. exact (@lem14220 A B P (@lem14054 A B P h1)). Qed.
Lemma lem14222 {A B : Type'} (y : B) (P : type1413 A B) (h1 : term65 A B P) : term112 A B P y.
Proof. exact (@lem14221 A B P h1 y). Qed.
Lemma lem14223 {A B : Type'} (P : type1413 A B) (y : B) : (term112 A B P y) = (term109 A B P y).
Proof. exact (eq_refl (term112 A B P y)). Qed.
Lemma lem14224 {A B : Type'} (y : B) (P : type1413 A B) (h1 : term65 A B P) : term109 A B P y.
Proof. exact (EQ_MP (@lem14223 A B P y) (@lem14222 A B y P h1)). Qed.
Lemma lem14225 {A B : Type'} (y : B) (x' : B) (P : type1413 A B) (h1 : term65 A B P) : term113 A B P y x'.
Proof. exact (@lem14224 A B y P h1 x'). Qed.
Lemma lem14226 {A B : Type'} (P : type1413 A B) (y : B) (x' : B) : (term113 A B P y x') = (term108 A B P y x').
Proof. exact (eq_refl (term113 A B P y x')). Qed.
Lemma lem14229 {A B : Type'} (y : B) (x' : B) (P : type1413 A B) (h1 : term65 A B P) : term108 A B P y x'.
Proof. exact (EQ_MP (@lem14226 A B P y x') (@lem14225 A B y x' P h1)). Qed.
Lemma lem14230 {A B : Type'} (y : B) (x' : B) (P : type1413 A B) (h1 : term65 A B P) : term108 A B P y x'.
Proof. exact (@lem14229 A B y x' P h1). Qed.
Lemma lem14231 {A B : Type'} (f : A -> B) (x' : A -> B) (x : A) (P : type1413 A B) (h1 : term65 A B P) : term114 A B P f x' x.
Proof. exact (@lem14230 A B (f x) (x' x) P h1). Qed.
Lemma lem14245 {A B : Type'} (x : A) (P : type1413 A B) (f : A -> B) (h1 : term77 A B P f) : term115 A B P f x.
Proof. exact (@lem14192 A B P f h1 x). Qed.
Lemma lem14246 {A B : Type'} (P : type1413 A B) (f : A -> B) (x : A) : (term115 A B P f x) = (term116 A B P f x).
Proof. exact (eq_refl (term115 A B P f x)). Qed.
Lemma lem14247 {A B : Type'} (x : A) (P : type1413 A B) (f : A -> B) (h1 : term77 A B P f) : term116 A B P f x.
Proof. exact (EQ_MP (@lem14246 A B P f x) (@lem14245 A B x P f h1)). Qed.
Lemma lem14248 {A B : Type'} (P : type1413 A B) (f : A -> B) (x : A) : (term116 A B P f x) = ((term116 A B P f x) = True).
Proof. exact (@lem7 (term116 A B P f x)). Qed.
Lemma lem14250 {A B : Type'} (x : A) (P : type1413 A B) (x' : A -> B) (h1 : term77 A B P x') : term115 A B P x' x.
Proof. exact (@lem14191 A B P x' h1 x). Qed.
Lemma lem14251 {A B : Type'} (P : type1413 A B) (x' : A -> B) (x : A) : (term115 A B P x' x) = (term116 A B P x' x).
Proof. exact (eq_refl (term115 A B P x' x)). Qed.
Lemma lem14252 {A B : Type'} (x : A) (P : type1413 A B) (x' : A -> B) (h1 : term77 A B P x') : term116 A B P x' x.
Proof. exact (EQ_MP (@lem14251 A B P x' x) (@lem14250 A B x P x' h1)). Qed.
Lemma lem14253 {A B : Type'} (P : type1413 A B) (x' : A -> B) (x : A) : (term116 A B P x' x) = ((term116 A B P x' x) = True).
Proof. exact (@lem7 (term116 A B P x' x)). Qed.
Lemma lem14258 {A B : Type'} (x : A) (P : type1413 A B) (f : A -> B) (h1 : term77 A B P f) : (term116 A B P f x) = True.
Proof. exact (EQ_MP (@lem14248 A B P f x) (@lem14247 A B x P f h1)). Qed.
Lemma lem14259 {A B : Type'} (x : A) (P : type1413 A B) (f : A -> B) (h1 : term77 A B P f) : (term116 A B P f x) = True.
Proof. exact (@lem14258 A B x P f h1). Qed.
Lemma lem14260 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem14261 {A B : Type'} (x : A) (P : type1413 A B) (f : A -> B) (h1 : term77 A B P f) : (term117 A B P f x) = (and True).
Proof. exact (MK_COMB (@lem14260) (@lem14259 A B x P f h1)). Qed.
Lemma lem14263 {A B : Type'} (x : A) (P : type1413 A B) (x' : A -> B) (h1 : term77 A B P x') : (term116 A B P x' x) = True.
Proof. exact (EQ_MP (@lem14253 A B P x' x) (@lem14252 A B x P x' h1)). Qed.
Lemma lem14264 {A B : Type'} (x : A) (P : type1413 A B) (x' : A -> B) (h1 : term77 A B P x') : (term116 A B P x' x) = True.
Proof. exact (@lem14263 A B x P x' h1). Qed.
Lemma lem14265 {A B : Type'} (x : A) (f : A -> B) (P : type1413 A B) (x' : A -> B) (h1 : term77 A B P f) (h2 : term77 A B P x') : (term118 A B f P x' x) = (True /\ True).
Proof. exact (MK_COMB (@lem14261 A B x P f h1) (@lem14264 A B x P x' h2)). Qed.
Lemma lem14267 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem14268 : (True /\ True) = True.
Proof. exact (@lem14267 True). Qed.
Lemma lem14269 {A B : Type'} (x : A) (f : A -> B) (P : type1413 A B) (x' : A -> B) (h1 : term77 A B P f) (h2 : term77 A B P x') : (term118 A B f P x' x) = True.
Proof. exact (TRANS (@lem14265 A B x f P x' h1 h2) (@lem14268)). Qed.
Lemma lem14270 {A B : Type'} (x : A) (f : A -> B) (P : type1413 A B) (x' : A -> B) (h1 : term77 A B P f) (h2 : term77 A B P x') : True = (term118 A B f P x' x).
Proof. exact (SYM (@lem14269 A B x f P x' h1 h2)). Qed.
Lemma lem14271 {A B : Type'} (x : A) (f : A -> B) (P : type1413 A B) (x' : A -> B) (h1 : term77 A B P f) (h2 : term77 A B P x') : term118 A B f P x' x.
Proof. exact (EQ_MP (@lem14270 A B x f P x' h1 h2) (@lem0)). Qed.
Lemma lem14272 {A B : Type'} (x : A) (f : A -> B) (P : type1413 A B) (x' : A -> B) (h1 : term77 A B P f) (h2 : term77 A B P x') : term119 A B f P x' x.
Proof. exact (ex_intro (term120 A B f P x' x) x (@lem14271 A B x f P x' h1 h2)). Qed.
Lemma lem14273 {A B : Type'} (x : A) (f : A -> B) (P : type1413 A B) (x' : A -> B) (h1 : term65 A B P) (h2 : term77 A B P f) (h3 : term77 A B P x') : (f x) = (x' x).
Proof. exact (@lem14231 A B f x' x P h1 (@lem14272 A B x f P x' h2 h3)). Qed.
Lemma lem14278 {A B : Type'} (f : A -> B) (P : type1413 A B) (x' : A -> B) (h1 : term65 A B P) (h2 : term77 A B P f) (h3 : term77 A B P x') : term3 A B f x'.
Proof. exact (fun x : A => @lem14273 A B x f P x' h1 h2 h3). Qed.
Lemma lem14279 {A B : Type'} (f : A -> B) (P : type1413 A B) (x' : A -> B) (h1 : term65 A B P) (h2 : term77 A B P f) (h3 : term77 A B P x') : f = x'.
Proof. exact (EQ_MP (@lem14199 A B f x') (@lem14278 A B f P x' h1 h2 h3)). Qed.
Lemma lem14280 {A B : Type'} (f : A -> B) (P : type1413 A B) (x' : A -> B) (h1 : term87 A B f P x') : term77 A B P x'.
Proof. exact (proj2 (@lem14190 A B f P x' h1)). Qed.
Lemma lem14281 {A B : Type'} (f : A -> B) (P : type1413 A B) (x' : A -> B) (h1 : term87 A B f P x') : term77 A B P f.
Proof. exact (proj1 (@lem14190 A B f P x' h1)). Qed.
Lemma lem14282 {A B : Type'} (f : A -> B) (P : type1413 A B) (x' : A -> B) (h1 : term65 A B P) (h2 : term77 A B P f) (h3 : term77 A B P x') : (term77 A B P x') = (f = x').
Proof. exact (prop_ext (fun h4 : term77 A B P x' => @lem14279 A B f P x' h1 h2 h3) (fun h4 : f = x' => @lem14191 A B P x' h3)). Qed.
Lemma lem14283 {A B : Type'} (f : A -> B) (P : type1413 A B) (x' : A -> B) (h1 : term65 A B P) (h2 : term77 A B P f) (h3 : term77 A B P x') : f = x'.
Proof. exact (EQ_MP (@lem14282 A B f P x' h1 h2 h3) (@lem14191 A B P x' h3)). Qed.
Lemma lem14284 {A B : Type'} (f : A -> B) (P : type1413 A B) (x' : A -> B) (h1 : term65 A B P) (h2 : term77 A B P f) (h3 : term77 A B P x') : (term77 A B P f) = (f = x').
Proof. exact (prop_ext (fun h4 : term77 A B P f => @lem14283 A B f P x' h1 h2 h3) (fun h4 : f = x' => @lem14192 A B P f h2)). Qed.
Lemma lem14285 {A B : Type'} (f : A -> B) (P : type1413 A B) (x' : A -> B) (h1 : term65 A B P) (h2 : term77 A B P f) (h3 : term77 A B P x') : f = x'.
Proof. exact (EQ_MP (@lem14284 A B f P x' h1 h2 h3) (@lem14192 A B P f h2)). Qed.
Lemma lem14286 {A B : Type'} (f : A -> B) (P : type1413 A B) (x' : A -> B) (h1 : term65 A B P) (h2 : term77 A B P f) (h3 : term87 A B f P x') : (term77 A B P x') = (f = x').
Proof. exact (prop_ext (fun h4 : term77 A B P x' => @lem14285 A B f P x' h1 h2 h4) (fun h4 : f = x' => @lem14280 A B f P x' h3)). Qed.
Lemma lem14287 {A B : Type'} (f : A -> B) (P : type1413 A B) (x' : A -> B) (h1 : term65 A B P) (h2 : term77 A B P f) (h3 : term87 A B f P x') : f = x'.
Proof. exact (EQ_MP (@lem14286 A B f P x' h1 h2 h3) (@lem14280 A B f P x' h3)). Qed.
Lemma lem14288 {A B : Type'} (f : A -> B) (P : type1413 A B) (x' : A -> B) (h1 : term65 A B P) (h2 : term87 A B f P x') : (term77 A B P f) = (f = x').
Proof. exact (prop_ext (fun h3 : term77 A B P f => @lem14287 A B f P x' h1 h3 h2) (fun h3 : f = x' => @lem14281 A B f P x' h2)). Qed.
Lemma lem14289 {A B : Type'} (f : A -> B) (P : type1413 A B) (x' : A -> B) (h1 : term65 A B P) (h2 : term87 A B f P x') : f = x'.
Proof. exact (EQ_MP (@lem14288 A B f P x' h1 h2) (@lem14281 A B f P x' h2)). Qed.
Lemma lem14290 {A B : Type'} (f : A -> B) (x' : A -> B) (P : type1413 A B) (h1 : term65 A B P) : term91 A B P f x'.
Proof. exact (fun h0 : term87 A B f P x' => @lem14289 A B f P x' h1 h0). Qed.
Lemma lem14295 {A B : Type'} (f : A -> B) (P : type1413 A B) (h1 : term65 A B P) : term95 A B P f.
Proof. exact (fun x' : A -> B => @lem14290 A B f x' P h1). Qed.
Lemma lem14300 {A B : Type'} (P : type1413 A B) (h1 : term65 A B P) : term99 A B P.
Proof. exact (fun f : A -> B => @lem14295 A B f P h1). Qed.
Lemma lem14301 {A B : Type'} (y1 : B) (P : type1413 A B) (x : A) (y2 : B) (h1 : term30 A B y1 P x y2) : term30 A B y1 P x y2.
Proof. exact (h1). Qed.
Lemma lem14302 {A B : Type'} (P : type1413 A B) (x : A) (y2 : B) (h1 : P x y2) : P x y2.
Proof. exact (h1). Qed.
Lemma lem14303 {A B : Type'} (P : type1413 A B) (x : A) (y1 : B) (h1 : P x y1) : P x y1.
Proof. exact (h1). Qed.
Lemma lem14304 {A B : Type'} (P : type1413 A B) (f : A -> B) (h1 : term77 A B P f) : term77 A B P f.
Proof. exact (h1). Qed.
Lemma lem14305 {A B : Type'} (y1 : B) (x : A) (y2 : B) (f : A -> B) (h1 : (term121 A B x y1 f) = (term121 A B x y2 f)) : (term121 A B x y1 f) = (term121 A B x y2 f).
Proof. exact (h1). Qed.
Lemma lem14306 {A B : Type'} (P : type1413 A B) (h1 : term99 A B P) : term99 A B P.
Proof. exact (h1). Qed.
Lemma lem14307 {A B : Type'} (f : A -> B) (P : type1413 A B) (h1 : term99 A B P) : term122 A B P f.
Proof. exact (@lem14306 A B P h1 f). Qed.
Lemma lem14308 {A B : Type'} (P : type1413 A B) (f : A -> B) : (term122 A B P f) = (term95 A B P f).
Proof. exact (eq_refl (term122 A B P f)). Qed.
Lemma lem14309 {A B : Type'} (f : A -> B) (P : type1413 A B) (h1 : term99 A B P) : term95 A B P f.
Proof. exact (EQ_MP (@lem14308 A B P f) (@lem14307 A B f P h1)). Qed.
Lemma lem14310 {A B : Type'} (f : A -> B) (x' : A -> B) (P : type1413 A B) (h1 : term99 A B P) : term123 A B P f x'.
Proof. exact (@lem14309 A B f P h1 x'). Qed.
Lemma lem14311 {A B : Type'} (P : type1413 A B) (f : A -> B) (x' : A -> B) : (term123 A B P f x') = (term91 A B P f x').
Proof. exact (eq_refl (term123 A B P f x')). Qed.
Lemma lem14312 {A B : Type'} (f : A -> B) (x' : A -> B) (P : type1413 A B) (h1 : term99 A B P) : term91 A B P f x'.
Proof. exact (EQ_MP (@lem14311 A B P f x') (@lem14310 A B f x' P h1)). Qed.
Lemma lem14313 {A B : Type'} (f : A -> B) (P : type1413 A B) (x' : A -> B) (h1 : term87 A B f P x') : term87 A B f P x'.
Proof. exact (h1). Qed.
Lemma lem14314 {A B : Type'} (f : A -> B) (P : type1413 A B) (x' : A -> B) (h1 : term99 A B P) (h2 : term87 A B f P x') : f = x'.
Proof. exact (@lem14312 A B f x' P h1 (@lem14313 A B f P x' h2)). Qed.
Lemma lem14315 {A B : Type'} (f : A -> B) (P : type1413 A B) (x' : A -> B) (h1 : term87 A B f P x') : term124 A B P f x'.
Proof. exact (fun h0 : term99 A B P => @lem14314 A B f P x' h0 h1). Qed.
Lemma lem14316 {A B : Type'} (P : type1413 A B) (h1 : term99 A B P) : term99 A B P.
Proof. exact (h1). Qed.
Lemma lem14317 {A B : Type'} (f : A -> B) (P : type1413 A B) (x' : A -> B) (h1 : term99 A B P) (h2 : term87 A B f P x') : f = x'.
Proof. exact (@lem14315 A B f P x' h2 (@lem14316 A B P h1)). Qed.
Lemma lem14318 {A B : Type'} (f : A -> B) (x' : A -> B) (P : type1413 A B) (h1 : term99 A B P) : term91 A B P f x'.
Proof. exact (fun h0 : term87 A B f P x' => @lem14317 A B f P x' h1 h0). Qed.
Lemma lem14319 {A B : Type'} (f : A -> B) (P : type1413 A B) (h1 : term99 A B P) : term95 A B P f.
Proof. exact (fun x' : A -> B => @lem14318 A B f x' P h1). Qed.
Lemma lem14320 {A B : Type'} (P : type1413 A B) (h1 : term99 A B P) : term99 A B P.
Proof. exact (fun f : A -> B => @lem14319 A B f P h1). Qed.
Lemma lem14321 {A B : Type'} (P : type1413 A B) : term125 A B P.
Proof. exact (fun h0 : term99 A B P => @lem14320 A B P h0). Qed.
Lemma lem14322 {A B : Type'} (P : type1413 A B) (h1 : term99 A B P) : term99 A B P.
Proof. exact (@lem14321 A B P (@lem14057 A B P h1)). Qed.
Lemma lem14323 {A B : Type'} (f : A -> B) (P : type1413 A B) (h1 : term99 A B P) : term122 A B P f.
Proof. exact (@lem14322 A B P h1 f). Qed.
Lemma lem14324 {A B : Type'} (P : type1413 A B) (f : A -> B) : (term122 A B P f) = (term95 A B P f).
Proof. exact (eq_refl (term122 A B P f)). Qed.
Lemma lem14325 {A B : Type'} (f : A -> B) (P : type1413 A B) (h1 : term99 A B P) : term95 A B P f.
Proof. exact (EQ_MP (@lem14324 A B P f) (@lem14323 A B f P h1)). Qed.
Lemma lem14326 {A B : Type'} (f : A -> B) (x' : A -> B) (P : type1413 A B) (h1 : term99 A B P) : term123 A B P f x'.
Proof. exact (@lem14325 A B f P h1 x'). Qed.
Lemma lem14327 {A B : Type'} (P : type1413 A B) (f : A -> B) (x' : A -> B) : (term123 A B P f x') = (term91 A B P f x').
Proof. exact (eq_refl (term123 A B P f x')). Qed.
Lemma lem14330 {A B : Type'} (f : A -> B) (x' : A -> B) (P : type1413 A B) (h1 : term99 A B P) : term91 A B P f x'.
Proof. exact (EQ_MP (@lem14327 A B P f x') (@lem14326 A B f x' P h1)). Qed.
Lemma lem14331 {A B : Type'} (f : A -> B) (x' : A -> B) (P : type1413 A B) (h1 : term99 A B P) : term91 A B P f x'.
Proof. exact (@lem14330 A B f x' P h1). Qed.
Lemma lem14332 {A B : Type'} (y1 : B) (x : A) (y2 : B) (f : A -> B) (P : type1413 A B) (h1 : term99 A B P) : term126 A B P y1 x y2 f.
Proof. exact (@lem14331 A B (term121 A B x y1 f) (term121 A B x y2 f) P h1). Qed.
Lemma lem14333 {A B : Type'} (x : A) (y1 : B) (f : A -> B) (x' : A) : (term127 A B x y1 f x') = (term128 A B x y1 f x').
Proof. exact (eq_refl (term127 A B x y1 f x')). Qed.
Lemma lem14334 {A B : Type'} (P : type1413 A B) (x' : A) : (P x') = (P x').
Proof. exact (eq_refl (P x')). Qed.
Lemma lem14335 {A B : Type'} (P : type1413 A B) (x : A) (y1 : B) (f : A -> B) (x' : A) : (term129 A B P x y1 f x') = (term130 A B P x y1 f x').
Proof. exact (MK_COMB (@lem14334 A B P x') (@lem14333 A B x y1 f x')). Qed.
Lemma lem14336 {A B : Type'} (P : type1413 A B) (x : A) (y1 : B) (f : A -> B) (x' : A) : (term130 A B P x y1 f x') = (term129 A B P x y1 f x').
Proof. exact (SYM (@lem14335 A B P x y1 f x')). Qed.
Lemma lem14337 {A B : Type'} (x : A) (y2 : B) (f : A -> B) (x' : A) : (term127 A B x y2 f x') = (term128 A B x y2 f x').
Proof. exact (eq_refl (term127 A B x y2 f x')). Qed.
Lemma lem14338 {A B : Type'} (P : type1413 A B) (x' : A) : (P x') = (P x').
Proof. exact (eq_refl (P x')). Qed.
Lemma lem14339 {A B : Type'} (P : type1413 A B) (x : A) (y2 : B) (f : A -> B) (x' : A) : (term129 A B P x y2 f x') = (term130 A B P x y2 f x').
Proof. exact (MK_COMB (@lem14338 A B P x') (@lem14337 A B x y2 f x')). Qed.
Lemma lem14340 {A B : Type'} (P : type1413 A B) (x : A) (y2 : B) (f : A -> B) (x' : A) : (term130 A B P x y2 f x') = (term129 A B P x y2 f x').
Proof. exact (SYM (@lem14339 A B P x y2 f x')). Qed.
Lemma lem14341 {B : Type'} (_474 : B) (_475 : Prop) (_476 : B -> Prop) (_477 : B) : (term131 B _476 _475 _474 _477) = (term132 B _474 _475 _476 _477).
Proof. exact (@lem13473 B _474 _475 _476 _477). Qed.
Lemma lem14342 {A B : Type'} (_474 : B) (_475 : Prop) (P : type1413 A B) (x' : A) (_477 : B) : (term133 A B P x' _475 _474 _477) = (term134 A B _474 _475 P x' _477).
Proof. exact (@lem14341 B _474 _475 (term17 A B P x') _477). Qed.
Lemma lem14343 {A B : Type'} (y1 : B) (x : A) (P : type1413 A B) (f : A -> B) (x' : A) : (term135 A B P x y1 f x') = (term136 A B y1 x P f x').
Proof. exact (@lem14342 A B y1 (x' = x) P x' (f x')). Qed.
Lemma lem14344 {A B : Type'} (P : type1413 A B) (f : A -> B) (x' : A) : (term137 A B P f x') = (term116 A B P f x').
Proof. exact (eq_refl (term137 A B P f x')). Qed.
Lemma lem14345 {A : Type'} (x' : A) (x : A) : (term138 A x' x) = (term138 A x' x).
Proof. exact (eq_refl (term138 A x' x)). Qed.
Lemma lem14346 {A B : Type'} (x : A) (P : type1413 A B) (f : A -> B) (x' : A) : (term139 A B x P f x') = (term140 A B x P f x').
Proof. exact (MK_COMB (@lem14345 A x' x) (@lem14344 A B P f x')). Qed.
Lemma lem14347 {A B : Type'} (P : type1413 A B) (x' : A) (y1 : B) : (term18 A B P x' y1) = (P x' y1).
Proof. exact (eq_refl (term18 A B P x' y1)). Qed.
Lemma lem14348 {A : Type'} (x' : A) (x : A) : (term141 A x' x) = (term141 A x' x).
Proof. exact (eq_refl (term141 A x' x)). Qed.
Lemma lem14349 {A B : Type'} (x : A) (P : type1413 A B) (x' : A) (y1 : B) : (term142 A B x P x' y1) = (term143 A B x P x' y1).
Proof. exact (MK_COMB (@lem14348 A x' x) (@lem14347 A B P x' y1)). Qed.
Lemma lem14350 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem14351 {A B : Type'} (x : A) (P : type1413 A B) (x' : A) (y1 : B) : (term144 A B x P x' y1) = (term145 A B x P x' y1).
Proof. exact (MK_COMB (@lem14350) (@lem14349 A B x P x' y1)). Qed.
Lemma lem14352 {A B : Type'} (y1 : B) (x : A) (P : type1413 A B) (f : A -> B) (x' : A) : (term136 A B y1 x P f x') = (term146 A B y1 x P f x').
Proof. exact (MK_COMB (@lem14351 A B x P x' y1) (@lem14346 A B x P f x')). Qed.
Lemma lem14353 {A B : Type'} (P : type1413 A B) (x : A) (y1 : B) (f : A -> B) (x' : A) : (term135 A B P x y1 f x') = (term130 A B P x y1 f x').
Proof. exact (eq_refl (term135 A B P x y1 f x')). Qed.
Lemma lem14354 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem14355 {A B : Type'} (P : type1413 A B) (x : A) (y1 : B) (f : A -> B) (x' : A) : (term147 A B P x y1 f x') = (term148 A B P x y1 f x').
Proof. exact (MK_COMB (@lem14354) (@lem14353 A B P x y1 f x')). Qed.
Lemma lem14356 {A B : Type'} (y1 : B) (x : A) (P : type1413 A B) (f : A -> B) (x' : A) : ((term135 A B P x y1 f x') = (term136 A B y1 x P f x')) = ((term130 A B P x y1 f x') = (term146 A B y1 x P f x')).
Proof. exact (MK_COMB (@lem14355 A B P x y1 f x') (@lem14352 A B y1 x P f x')). Qed.
Lemma lem14357 {A B : Type'} (y1 : B) (x : A) (P : type1413 A B) (f : A -> B) (x' : A) : (term130 A B P x y1 f x') = (term146 A B y1 x P f x').
Proof. exact (EQ_MP (@lem14356 A B y1 x P f x') (@lem14343 A B y1 x P f x')). Qed.
Lemma lem14358 {A B : Type'} (P : type1413 A B) (x : A) (y1 : B) (f : A -> B) (x' : A) : (term146 A B y1 x P f x') = (term130 A B P x y1 f x').
Proof. exact (SYM (@lem14357 A B y1 x P f x')). Qed.
Lemma lem14359 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem14393 {B : Type'} (_474 : B) (_475 : Prop) (_476 : B -> Prop) (_477 : B) : (term131 B _476 _475 _474 _477) = (term132 B _474 _475 _476 _477).
Proof. exact (@lem13473 B _474 _475 _476 _477). Qed.
Lemma lem14394 {A B : Type'} (_474 : B) (_475 : Prop) (P : type1413 A B) (x' : A) (_477 : B) : (term133 A B P x' _475 _474 _477) = (term134 A B _474 _475 P x' _477).
Proof. exact (@lem14393 B _474 _475 (term17 A B P x') _477). Qed.
Lemma lem14395 {A B : Type'} (y2 : B) (x : A) (P : type1413 A B) (f : A -> B) (x' : A) : (term135 A B P x y2 f x') = (term136 A B y2 x P f x').
Proof. exact (@lem14394 A B y2 (x' = x) P x' (f x')). Qed.
Lemma lem14396 {A B : Type'} (P : type1413 A B) (f : A -> B) (x' : A) : (term137 A B P f x') = (term116 A B P f x').
Proof. exact (eq_refl (term137 A B P f x')). Qed.
Lemma lem14397 {A : Type'} (x' : A) (x : A) : (term138 A x' x) = (term138 A x' x).
Proof. exact (eq_refl (term138 A x' x)). Qed.
Lemma lem14398 {A B : Type'} (x : A) (P : type1413 A B) (f : A -> B) (x' : A) : (term139 A B x P f x') = (term140 A B x P f x').
Proof. exact (MK_COMB (@lem14397 A x' x) (@lem14396 A B P f x')). Qed.
Lemma lem14399 {A B : Type'} (P : type1413 A B) (x' : A) (y2 : B) : (term18 A B P x' y2) = (P x' y2).
Proof. exact (eq_refl (term18 A B P x' y2)). Qed.
Lemma lem14400 {A : Type'} (x' : A) (x : A) : (term141 A x' x) = (term141 A x' x).
Proof. exact (eq_refl (term141 A x' x)). Qed.
Lemma lem14401 {A B : Type'} (x : A) (P : type1413 A B) (x' : A) (y2 : B) : (term142 A B x P x' y2) = (term143 A B x P x' y2).
Proof. exact (MK_COMB (@lem14400 A x' x) (@lem14399 A B P x' y2)). Qed.
Lemma lem14402 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem14403 {A B : Type'} (x : A) (P : type1413 A B) (x' : A) (y2 : B) : (term144 A B x P x' y2) = (term145 A B x P x' y2).
Proof. exact (MK_COMB (@lem14402) (@lem14401 A B x P x' y2)). Qed.
Lemma lem14404 {A B : Type'} (y2 : B) (x : A) (P : type1413 A B) (f : A -> B) (x' : A) : (term136 A B y2 x P f x') = (term146 A B y2 x P f x').
Proof. exact (MK_COMB (@lem14403 A B x P x' y2) (@lem14398 A B x P f x')). Qed.
Lemma lem14405 {A B : Type'} (P : type1413 A B) (x : A) (y2 : B) (f : A -> B) (x' : A) : (term135 A B P x y2 f x') = (term130 A B P x y2 f x').
Proof. exact (eq_refl (term135 A B P x y2 f x')). Qed.
Lemma lem14406 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem14407 {A B : Type'} (P : type1413 A B) (x : A) (y2 : B) (f : A -> B) (x' : A) : (term147 A B P x y2 f x') = (term148 A B P x y2 f x').
Proof. exact (MK_COMB (@lem14406) (@lem14405 A B P x y2 f x')). Qed.
Lemma lem14408 {A B : Type'} (y2 : B) (x : A) (P : type1413 A B) (f : A -> B) (x' : A) : ((term135 A B P x y2 f x') = (term136 A B y2 x P f x')) = ((term130 A B P x y2 f x') = (term146 A B y2 x P f x')).
Proof. exact (MK_COMB (@lem14407 A B P x y2 f x') (@lem14404 A B y2 x P f x')). Qed.
Lemma lem14409 {A B : Type'} (y2 : B) (x : A) (P : type1413 A B) (f : A -> B) (x' : A) : (term130 A B P x y2 f x') = (term146 A B y2 x P f x').
Proof. exact (EQ_MP (@lem14408 A B y2 x P f x') (@lem14395 A B y2 x P f x')). Qed.
Lemma lem14410 {A B : Type'} (P : type1413 A B) (x : A) (y2 : B) (f : A -> B) (x' : A) : (term146 A B y2 x P f x') = (term130 A B P x y2 f x').
Proof. exact (SYM (@lem14409 A B y2 x P f x')). Qed.
Lemma lem14411 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem14455 {A B : Type'} (P : type1413 A B) (x : A) (y1 : B) : (P x y1) = ((P x y1) = True).
Proof. exact (@lem7 (P x y1)). Qed.
Lemma lem14465 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem14466 {A B : Type'} (P : type1413 A B) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem14467 {A B : Type'} (P : type1413 A B) (x' : A) (x : A) (h1 : x' = x) : (P x') = (P x).
Proof. exact (MK_COMB (@lem14466 A B P) (@lem14465 A x' x h1)). Qed.
Lemma lem14468 {B : Type'} (y1 : B) : y1 = y1.
Proof. exact (eq_refl y1). Qed.
Lemma lem14469 {A B : Type'} (P : type1413 A B) (y1 : B) (x' : A) (x : A) (h1 : x' = x) : (P x' y1) = (P x y1).
Proof. exact (MK_COMB (@lem14467 A B P x' x h1) (@lem14468 B y1)). Qed.
Lemma lem14471 {A B : Type'} (P : type1413 A B) (x : A) (y1 : B) (h1 : P x y1) : (P x y1) = True.
Proof. exact (EQ_MP (@lem14455 A B P x y1) (@lem14303 A B P x y1 h1)). Qed.
Lemma lem14472 {A B : Type'} (x' : A) (P : type1413 A B) (x : A) (y1 : B) (h1 : x' = x) (h2 : P x y1) : (P x' y1) = True.
Proof. exact (TRANS (@lem14469 A B P y1 x' x h1) (@lem14471 A B P x y1 h2)). Qed.
Lemma lem14473 {A B : Type'} (x' : A) (P : type1413 A B) (x : A) (y1 : B) (h1 : x' = x) (h2 : P x y1) : True = (P x' y1).
Proof. exact (SYM (@lem14472 A B x' P x y1 h1 h2)). Qed.
Lemma lem14489 {A B : Type'} (x : A) (P : type1413 A B) (f : A -> B) (h1 : term77 A B P f) : term115 A B P f x.
Proof. exact (@lem14304 A B P f h1 x). Qed.
Lemma lem14490 {A B : Type'} (P : type1413 A B) (f : A -> B) (x : A) : (term115 A B P f x) = (term116 A B P f x).
Proof. exact (eq_refl (term115 A B P f x)). Qed.
Lemma lem14491 {A B : Type'} (x : A) (P : type1413 A B) (f : A -> B) (h1 : term77 A B P f) : term116 A B P f x.
Proof. exact (EQ_MP (@lem14490 A B P f x) (@lem14489 A B x P f h1)). Qed.
Lemma lem14492 {A B : Type'} (P : type1413 A B) (f : A -> B) (x : A) : (term116 A B P f x) = ((term116 A B P f x) = True).
Proof. exact (@lem7 (term116 A B P f x)). Qed.
Lemma lem14508 {A B : Type'} (x : A) (P : type1413 A B) (f : A -> B) (h1 : term77 A B P f) : (term116 A B P f x) = True.
Proof. exact (EQ_MP (@lem14492 A B P f x) (@lem14491 A B x P f h1)). Qed.
Lemma lem14509 {A B : Type'} (x : A) (P : type1413 A B) (f : A -> B) (h1 : term77 A B P f) : (term116 A B P f x) = True.
Proof. exact (@lem14508 A B x P f h1). Qed.
Lemma lem14510 {A B : Type'} (x' : A) (P : type1413 A B) (f : A -> B) (h1 : term77 A B P f) : (term116 A B P f x') = True.
Proof. exact (@lem14509 A B x' P f h1). Qed.
Lemma lem14511 {A B : Type'} (x' : A) (P : type1413 A B) (f : A -> B) (h1 : term77 A B P f) : True = (term116 A B P f x').
Proof. exact (SYM (@lem14510 A B x' P f h1)). Qed.
Lemma lem14525 {A B : Type'} (P : type1413 A B) (x : A) (y2 : B) : (P x y2) = ((P x y2) = True).
Proof. exact (@lem7 (P x y2)). Qed.
Lemma lem14533 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem14534 {A B : Type'} (P : type1413 A B) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem14535 {A B : Type'} (P : type1413 A B) (x' : A) (x : A) (h1 : x' = x) : (P x') = (P x).
Proof. exact (MK_COMB (@lem14534 A B P) (@lem14533 A x' x h1)). Qed.
Lemma lem14536 {B : Type'} (y2 : B) : y2 = y2.
Proof. exact (eq_refl y2). Qed.
Lemma lem14537 {A B : Type'} (P : type1413 A B) (y2 : B) (x' : A) (x : A) (h1 : x' = x) : (P x' y2) = (P x y2).
Proof. exact (MK_COMB (@lem14535 A B P x' x h1) (@lem14536 B y2)). Qed.
Lemma lem14539 {A B : Type'} (P : type1413 A B) (x : A) (y2 : B) (h1 : P x y2) : (P x y2) = True.
Proof. exact (EQ_MP (@lem14525 A B P x y2) (@lem14302 A B P x y2 h1)). Qed.
Lemma lem14540 {A B : Type'} (x' : A) (P : type1413 A B) (x : A) (y2 : B) (h1 : x' = x) (h2 : P x y2) : (P x' y2) = True.
Proof. exact (TRANS (@lem14537 A B P y2 x' x h1) (@lem14539 A B P x y2 h2)). Qed.
Lemma lem14541 {A B : Type'} (x' : A) (P : type1413 A B) (x : A) (y2 : B) (h1 : x' = x) (h2 : P x y2) : True = (P x' y2).
Proof. exact (SYM (@lem14540 A B x' P x y2 h1 h2)). Qed.
Lemma lem14557 {A B : Type'} (x : A) (P : type1413 A B) (f : A -> B) (h1 : term77 A B P f) : term115 A B P f x.
Proof. exact (@lem14304 A B P f h1 x). Qed.
Lemma lem14558 {A B : Type'} (P : type1413 A B) (f : A -> B) (x : A) : (term115 A B P f x) = (term116 A B P f x).
Proof. exact (eq_refl (term115 A B P f x)). Qed.
Lemma lem14559 {A B : Type'} (x : A) (P : type1413 A B) (f : A -> B) (h1 : term77 A B P f) : term116 A B P f x.
Proof. exact (EQ_MP (@lem14558 A B P f x) (@lem14557 A B x P f h1)). Qed.
Lemma lem14560 {A B : Type'} (P : type1413 A B) (f : A -> B) (x : A) : (term116 A B P f x) = ((term116 A B P f x) = True).
Proof. exact (@lem7 (term116 A B P f x)). Qed.
Lemma lem14576 {A B : Type'} (x : A) (P : type1413 A B) (f : A -> B) (h1 : term77 A B P f) : (term116 A B P f x) = True.
Proof. exact (EQ_MP (@lem14560 A B P f x) (@lem14559 A B x P f h1)). Qed.
Lemma lem14577 {A B : Type'} (x : A) (P : type1413 A B) (f : A -> B) (h1 : term77 A B P f) : (term116 A B P f x) = True.
Proof. exact (@lem14576 A B x P f h1). Qed.
Lemma lem14578 {A B : Type'} (x' : A) (P : type1413 A B) (f : A -> B) (h1 : term77 A B P f) : (term116 A B P f x') = True.
Proof. exact (@lem14577 A B x' P f h1). Qed.
Lemma lem14579 {A B : Type'} (x' : A) (P : type1413 A B) (f : A -> B) (h1 : term77 A B P f) : True = (term116 A B P f x').
Proof. exact (SYM (@lem14578 A B x' P f h1)). Qed.
Lemma lem14581 {A B : Type'} (x' : A) (P : type1413 A B) (f : A -> B) (h1 : term77 A B P f) : term116 A B P f x'.
Proof. exact (EQ_MP (@lem14579 A B x' P f h1) (@lem0)). Qed.
Lemma lem14582 {A B : Type'} (x : A) (x' : A) (P : type1413 A B) (f : A -> B) (h1 : term77 A B P f) : term140 A B x P f x'.
Proof. exact (fun h0 : term149 A x' x => @lem14581 A B x' P f h1). Qed.
Lemma lem14583 {A B : Type'} (x' : A) (P : type1413 A B) (x : A) (y2 : B) (h1 : x' = x) (h2 : P x y2) : P x' y2.
Proof. exact (EQ_MP (@lem14541 A B x' P x y2 h1 h2) (@lem0)). Qed.
Lemma lem14584 {A B : Type'} (x' : A) (P : type1413 A B) (x : A) (y2 : B) (h1 : x' = x) (h2 : P x y2) : (x' = x) = (P x' y2).
Proof. exact (prop_ext (fun h3 : x' = x => @lem14583 A B x' P x y2 h1 h2) (fun h3 : P x' y2 => @lem14411 A x' x h1)). Qed.
Lemma lem14585 {A B : Type'} (x' : A) (P : type1413 A B) (x : A) (y2 : B) (h1 : x' = x) (h2 : P x y2) : P x' y2.
Proof. exact (EQ_MP (@lem14584 A B x' P x y2 h1 h2) (@lem14411 A x' x h1)). Qed.
Lemma lem14586 {A B : Type'} (x' : A) (P : type1413 A B) (x : A) (y2 : B) (h1 : P x y2) : term143 A B x P x' y2.
Proof. exact (fun h0 : x' = x => @lem14585 A B x' P x y2 h0 h1). Qed.
Lemma lem14587 {A B : Type'} (x' : A) (f : A -> B) (P : type1413 A B) (x : A) (y2 : B) (h1 : term77 A B P f) (h2 : P x y2) : term146 A B y2 x P f x'.
Proof. exact (conj (@lem14586 A B x' P x y2 h2) (@lem14582 A B x x' P f h1)). Qed.
Lemma lem14588 {A B : Type'} (x' : A) (f : A -> B) (P : type1413 A B) (x : A) (y2 : B) (h1 : term77 A B P f) (h2 : P x y2) : term130 A B P x y2 f x'.
Proof. exact (EQ_MP (@lem14410 A B P x y2 f x') (@lem14587 A B x' f P x y2 h1 h2)). Qed.
Lemma lem14589 {A B : Type'} (x' : A) (P : type1413 A B) (f : A -> B) (h1 : term77 A B P f) : term116 A B P f x'.
Proof. exact (EQ_MP (@lem14511 A B x' P f h1) (@lem0)). Qed.
Lemma lem14590 {A B : Type'} (x : A) (x' : A) (P : type1413 A B) (f : A -> B) (h1 : term77 A B P f) : term140 A B x P f x'.
Proof. exact (fun h0 : term149 A x' x => @lem14589 A B x' P f h1). Qed.
Lemma lem14591 {A B : Type'} (x' : A) (P : type1413 A B) (x : A) (y1 : B) (h1 : x' = x) (h2 : P x y1) : P x' y1.
Proof. exact (EQ_MP (@lem14473 A B x' P x y1 h1 h2) (@lem0)). Qed.
Lemma lem14592 {A B : Type'} (x' : A) (P : type1413 A B) (x : A) (y1 : B) (h1 : x' = x) (h2 : P x y1) : (x' = x) = (P x' y1).
Proof. exact (prop_ext (fun h3 : x' = x => @lem14591 A B x' P x y1 h1 h2) (fun h3 : P x' y1 => @lem14359 A x' x h1)). Qed.
Lemma lem14593 {A B : Type'} (x' : A) (P : type1413 A B) (x : A) (y1 : B) (h1 : x' = x) (h2 : P x y1) : P x' y1.
Proof. exact (EQ_MP (@lem14592 A B x' P x y1 h1 h2) (@lem14359 A x' x h1)). Qed.
Lemma lem14594 {A B : Type'} (x' : A) (P : type1413 A B) (x : A) (y1 : B) (h1 : P x y1) : term143 A B x P x' y1.
Proof. exact (fun h0 : x' = x => @lem14593 A B x' P x y1 h0 h1). Qed.
Lemma lem14595 {A B : Type'} (x' : A) (f : A -> B) (P : type1413 A B) (x : A) (y1 : B) (h1 : term77 A B P f) (h2 : P x y1) : term146 A B y1 x P f x'.
Proof. exact (conj (@lem14594 A B x' P x y1 h2) (@lem14590 A B x x' P f h1)). Qed.
Lemma lem14596 {A B : Type'} (x' : A) (f : A -> B) (P : type1413 A B) (x : A) (y1 : B) (h1 : term77 A B P f) (h2 : P x y1) : term130 A B P x y1 f x'.
Proof. exact (EQ_MP (@lem14358 A B P x y1 f x') (@lem14595 A B x' f P x y1 h1 h2)). Qed.
Lemma lem14597 {A B : Type'} (x' : A) (f : A -> B) (P : type1413 A B) (x : A) (y2 : B) (h1 : term77 A B P f) (h2 : P x y2) : term129 A B P x y2 f x'.
Proof. exact (EQ_MP (@lem14340 A B P x y2 f x') (@lem14588 A B x' f P x y2 h1 h2)). Qed.
Lemma lem14598 {A B : Type'} (x' : A) (f : A -> B) (P : type1413 A B) (x : A) (y1 : B) (h1 : term77 A B P f) (h2 : P x y1) : term129 A B P x y1 f x'.
Proof. exact (EQ_MP (@lem14336 A B P x y1 f x') (@lem14596 A B x' f P x y1 h1 h2)). Qed.
Lemma lem14603 {A B : Type'} (f : A -> B) (P : type1413 A B) (x : A) (y2 : B) (h1 : term77 A B P f) (h2 : P x y2) : term150 A B P x y2 f.
Proof. exact (fun x' : A => @lem14597 A B x' f P x y2 h1 h2). Qed.
Lemma lem14608 {A B : Type'} (f : A -> B) (P : type1413 A B) (x : A) (y1 : B) (h1 : term77 A B P f) (h2 : P x y1) : term150 A B P x y1 f.
Proof. exact (fun x' : A => @lem14598 A B x' f P x y1 h1 h2). Qed.
Lemma lem14609 {A B : Type'} (f : A -> B) (y1 : B) (P : type1413 A B) (x : A) (y2 : B) (h1 : term77 A B P f) (h2 : P x y1) (h3 : P x y2) : term151 A B y1 P x y2 f.
Proof. exact (conj (@lem14608 A B f P x y1 h1 h2) (@lem14603 A B f P x y2 h1 h3)). Qed.
Lemma lem14610 {A B : Type'} (f : A -> B) (y1 : B) (P : type1413 A B) (x : A) (y2 : B) (h1 : term77 A B P f) (h2 : term99 A B P) (h3 : P x y1) (h4 : P x y2) : (term121 A B x y1 f) = (term121 A B x y2 f).
Proof. exact (@lem14332 A B y1 x y2 f P h2 (@lem14609 A B f y1 P x y2 h1 h3 h4)). Qed.
Lemma lem14611 {A B : Type'} (y1 : B) (x : A) (y2 : B) (f : A -> B) (h1 : (term121 A B x y1 f) = (term121 A B x y2 f)) : (term121 A B x y1 f) = (term121 A B x y2 f).
Proof. exact (h1). Qed.
Lemma lem14612 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem14613 {A B : Type'} (y1 : B) (x : A) (y2 : B) (f : A -> B) (h1 : (term121 A B x y1 f) = (term121 A B x y2 f)) : (term152 A B y1 f x) = (term152 A B y2 f x).
Proof. exact (MK_COMB (@lem14611 A B y1 x y2 f h1) (@lem14612 A x)). Qed.
Lemma lem14621 {A B : Type'} (f : A -> B) (y : A) : (term153 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem14622 {A B : Type'} (f : A -> B) (y : A) : (term153 A B f y) = (f y).
Proof. exact (@lem14621 A B f y). Qed.
Lemma lem14623 {A B : Type'} (y1 : B) (f : A -> B) (x : A) : (term154 A B y1 f x) = (term152 A B y1 f x).
Proof. exact (@lem14622 A B (term121 A B x y1 f) x). Qed.
Lemma lem14624 {A B : Type'} (x : A) (y1 : B) (f : A -> B) (z : A) : (term127 A B x y1 f z) = (term128 A B x y1 f z).
Proof. exact (eq_refl (term127 A B x y1 f z)). Qed.
Lemma lem14625 {A B : Type'} (x : A) (y1 : B) (f : A -> B) : (term155 A B x y1 f) = (term121 A B x y1 f).
Proof. exact (fun_ext (fun z : A => @lem14624 A B x y1 f z)). Qed.
Lemma lem14626 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem14627 {A B : Type'} (y1 : B) (f : A -> B) (x : A) : (term154 A B y1 f x) = (term152 A B y1 f x).
Proof. exact (MK_COMB (@lem14625 A B x y1 f) (@lem14626 A x)). Qed.
Lemma lem14628 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem14629 {A B : Type'} (y1 : B) (f : A -> B) (x : A) : (term156 A B y1 f x) = (term157 A B y1 f x).
Proof. exact (MK_COMB (@lem14628 B) (@lem14627 A B y1 f x)). Qed.
Lemma lem14630 {A B : Type'} (y1 : B) (f : A -> B) (x : A) : (term152 A B y1 f x) = (term158 A B y1 f x).
Proof. exact (eq_refl (term152 A B y1 f x)). Qed.
Lemma lem14631 {A B : Type'} (y1 : B) (f : A -> B) (x : A) : ((term154 A B y1 f x) = (term152 A B y1 f x)) = ((term152 A B y1 f x) = (term158 A B y1 f x)).
Proof. exact (MK_COMB (@lem14629 A B y1 f x) (@lem14630 A B y1 f x)). Qed.
Lemma lem14632 {A B : Type'} (y1 : B) (f : A -> B) (x : A) : (term152 A B y1 f x) = (term158 A B y1 f x).
Proof. exact (EQ_MP (@lem14631 A B y1 f x) (@lem14623 A B y1 f x)). Qed.
Lemma lem14634 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem14635 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem14634 A x). Qed.
Lemma lem14636 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem14637 {A B : Type'} (x : A) : (term159 A B x) = (@COND B True).
Proof. exact (MK_COMB (@lem14636 B) (@lem14635 A x)). Qed.
Lemma lem14638 {B : Type'} (y1 : B) : y1 = y1.
Proof. exact (eq_refl y1). Qed.
Lemma lem14639 {A B : Type'} (x : A) (y1 : B) : (term160 A B x y1) = (@COND B True y1).
Proof. exact (MK_COMB (@lem14637 A B x) (@lem14638 B y1)). Qed.
Lemma lem14640 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem14641 {A B : Type'} (y1 : B) (f : A -> B) (x : A) : (term158 A B y1 f x) = (term161 A B y1 f x).
Proof. exact (MK_COMB (@lem14639 A B x y1) (@lem14640 A B f x)). Qed.
Lemma lem14643 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem14644 {B : Type'} (t2 : B) (t1 : B) : (@COND B True t1 t2) = t1.
Proof. exact (@lem14643 B t2 t1). Qed.
Lemma lem14645 {A B : Type'} (f : A -> B) (x : A) (y1 : B) : (term161 A B y1 f x) = y1.
Proof. exact (@lem14644 B (f x) y1). Qed.
Lemma lem14646 {A B : Type'} (f : A -> B) (x : A) (y1 : B) : (term158 A B y1 f x) = y1.
Proof. exact (TRANS (@lem14641 A B y1 f x) (@lem14645 A B f x y1)). Qed.
Lemma lem14647 {A B : Type'} (f : A -> B) (x : A) (y1 : B) : (term152 A B y1 f x) = y1.
Proof. exact (TRANS (@lem14632 A B y1 f x) (@lem14646 A B f x y1)). Qed.
Lemma lem14648 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem14649 {A B : Type'} (f : A -> B) (x : A) (y1 : B) : (term157 A B y1 f x) = (@eq B y1).
Proof. exact (MK_COMB (@lem14648 B) (@lem14647 A B f x y1)). Qed.
Lemma lem14651 {A B : Type'} (f : A -> B) (y : A) : (term153 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem14652 {A B : Type'} (f : A -> B) (y : A) : (term153 A B f y) = (f y).
Proof. exact (@lem14651 A B f y). Qed.
Lemma lem14653 {A B : Type'} (y2 : B) (f : A -> B) (x : A) : (term154 A B y2 f x) = (term152 A B y2 f x).
Proof. exact (@lem14652 A B (term121 A B x y2 f) x). Qed.
Lemma lem14654 {A B : Type'} (x : A) (y2 : B) (f : A -> B) (z : A) : (term127 A B x y2 f z) = (term128 A B x y2 f z).
Proof. exact (eq_refl (term127 A B x y2 f z)). Qed.
Lemma lem14655 {A B : Type'} (x : A) (y2 : B) (f : A -> B) : (term155 A B x y2 f) = (term121 A B x y2 f).
Proof. exact (fun_ext (fun z : A => @lem14654 A B x y2 f z)). Qed.
Lemma lem14656 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem14657 {A B : Type'} (y2 : B) (f : A -> B) (x : A) : (term154 A B y2 f x) = (term152 A B y2 f x).
Proof. exact (MK_COMB (@lem14655 A B x y2 f) (@lem14656 A x)). Qed.
Lemma lem14658 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem14659 {A B : Type'} (y2 : B) (f : A -> B) (x : A) : (term156 A B y2 f x) = (term157 A B y2 f x).
Proof. exact (MK_COMB (@lem14658 B) (@lem14657 A B y2 f x)). Qed.
Lemma lem14660 {A B : Type'} (y2 : B) (f : A -> B) (x : A) : (term152 A B y2 f x) = (term158 A B y2 f x).
Proof. exact (eq_refl (term152 A B y2 f x)). Qed.
Lemma lem14661 {A B : Type'} (y2 : B) (f : A -> B) (x : A) : ((term154 A B y2 f x) = (term152 A B y2 f x)) = ((term152 A B y2 f x) = (term158 A B y2 f x)).
Proof. exact (MK_COMB (@lem14659 A B y2 f x) (@lem14660 A B y2 f x)). Qed.
Lemma lem14662 {A B : Type'} (y2 : B) (f : A -> B) (x : A) : (term152 A B y2 f x) = (term158 A B y2 f x).
Proof. exact (EQ_MP (@lem14661 A B y2 f x) (@lem14653 A B y2 f x)). Qed.
Lemma lem14664 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem14665 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem14664 A x). Qed.
Lemma lem14666 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem14667 {A B : Type'} (x : A) : (term159 A B x) = (@COND B True).
Proof. exact (MK_COMB (@lem14666 B) (@lem14665 A x)). Qed.
Lemma lem14668 {B : Type'} (y2 : B) : y2 = y2.
Proof. exact (eq_refl y2). Qed.
Lemma lem14669 {A B : Type'} (x : A) (y2 : B) : (term160 A B x y2) = (@COND B True y2).
Proof. exact (MK_COMB (@lem14667 A B x) (@lem14668 B y2)). Qed.
Lemma lem14670 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem14671 {A B : Type'} (y2 : B) (f : A -> B) (x : A) : (term158 A B y2 f x) = (term161 A B y2 f x).
Proof. exact (MK_COMB (@lem14669 A B x y2) (@lem14670 A B f x)). Qed.
Lemma lem14673 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem14674 {B : Type'} (t2 : B) (t1 : B) : (@COND B True t1 t2) = t1.
Proof. exact (@lem14673 B t2 t1). Qed.
Lemma lem14675 {A B : Type'} (f : A -> B) (x : A) (y2 : B) : (term161 A B y2 f x) = y2.
Proof. exact (@lem14674 B (f x) y2). Qed.
Lemma lem14676 {A B : Type'} (f : A -> B) (x : A) (y2 : B) : (term158 A B y2 f x) = y2.
Proof. exact (TRANS (@lem14671 A B y2 f x) (@lem14675 A B f x y2)). Qed.
Lemma lem14677 {A B : Type'} (f : A -> B) (x : A) (y2 : B) : (term152 A B y2 f x) = y2.
Proof. exact (TRANS (@lem14662 A B y2 f x) (@lem14676 A B f x y2)). Qed.
Lemma lem14678 {A B : Type'} (f : A -> B) (x : A) (y1 : B) (y2 : B) : ((term152 A B y1 f x) = (term152 A B y2 f x)) = (y1 = y2).
Proof. exact (MK_COMB (@lem14649 A B f x y1) (@lem14677 A B f x y2)). Qed.
Lemma lem14681 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem14682 {A B : Type'} (f : A -> B) (x : A) (y1 : B) (y2 : B) : (term162 A B y1 y2 f x) = (term141 B y1 y2).
Proof. exact (MK_COMB (@lem14681) (@lem14678 A B f x y1 y2)). Qed.
Lemma lem14685 {B : Type'} (y1 : B) (y2 : B) : (y1 = y2) = (y1 = y2).
Proof. exact (eq_refl (y1 = y2)). Qed.
Lemma lem14686 {A B : Type'} (f : A -> B) (x : A) (y1 : B) (y2 : B) : (term163 A B f x y1 y2) = (term164 B y1 y2).
Proof. exact (MK_COMB (@lem14682 A B f x y1 y2) (@lem14685 B y1 y2)). Qed.
Lemma lem14690 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem14691 {B : Type'} (y1 : B) (y2 : B) : (term164 B y1 y2) = True.
Proof. exact (@lem14690 (y1 = y2)). Qed.
Lemma lem14692 {A B : Type'} (f : A -> B) (x : A) (y1 : B) (y2 : B) : (term163 A B f x y1 y2) = True.
Proof. exact (TRANS (@lem14686 A B f x y1 y2) (@lem14691 B y1 y2)). Qed.
Lemma lem14693 {A B : Type'} (f : A -> B) (x : A) (y1 : B) (y2 : B) : True = (term163 A B f x y1 y2).
Proof. exact (SYM (@lem14692 A B f x y1 y2)). Qed.
Lemma lem14694 {A B : Type'} (f : A -> B) (x : A) (y1 : B) (y2 : B) : term163 A B f x y1 y2.
Proof. exact (EQ_MP (@lem14693 A B f x y1 y2) (@lem0)). Qed.
Lemma lem14695 {A B : Type'} (y1 : B) (x : A) (y2 : B) (f : A -> B) (h1 : (term121 A B x y1 f) = (term121 A B x y2 f)) : y1 = y2.
Proof. exact (@lem14694 A B f x y1 y2 (@lem14613 A B y1 x y2 f h1)). Qed.
Lemma lem14696 {A B : Type'} (x : A) (f : A -> B) (y1 : B) (y2 : B) : term165 A B x f y1 y2.
Proof. exact (fun h0 : (term121 A B x y1 f) = (term121 A B x y2 f) => @lem14695 A B y1 x y2 f h0). Qed.
Lemma lem14697 {A B : Type'} (y1 : B) (x : A) (y2 : B) (f : A -> B) (h1 : (term121 A B x y1 f) = (term121 A B x y2 f)) : y1 = y2.
Proof. exact (@lem14696 A B x f y1 y2 (@lem14305 A B y1 x y2 f h1)). Qed.
Lemma lem14698 {A B : Type'} (f : A -> B) (y1 : B) (P : type1413 A B) (x : A) (y2 : B) (h1 : term77 A B P f) (h2 : term99 A B P) (h3 : P x y1) (h4 : P x y2) : ((term121 A B x y1 f) = (term121 A B x y2 f)) = (y1 = y2).
Proof. exact (prop_ext (fun h5 : (term121 A B x y1 f) = (term121 A B x y2 f) => @lem14697 A B y1 x y2 f h5) (fun h5 : y1 = y2 => @lem14610 A B f y1 P x y2 h1 h2 h3 h4)). Qed.
Lemma lem14699 {A B : Type'} (f : A -> B) (y1 : B) (P : type1413 A B) (x : A) (y2 : B) (h1 : term77 A B P f) (h2 : term99 A B P) (h3 : P x y1) (h4 : P x y2) : y1 = y2.
Proof. exact (EQ_MP (@lem14698 A B f y1 P x y2 h1 h2 h3 h4) (@lem14610 A B f y1 P x y2 h1 h2 h3 h4)). Qed.
Lemma lem14700 {A B : Type'} (y1 : B) (P : type1413 A B) (x : A) (y2 : B) (h1 : term99 A B P) (h2 : term11 A B P) (h3 : P x y1) (h4 : P x y2) : y1 = y2.
Proof. exact (ex_elim (@lem14058 A B P h2) (fun f : A -> B => fun h0 : term75 A B P f => @lem14699 A B f y1 P x y2 h0 h1 h3 h4)). Qed.
Lemma lem14701 {A B : Type'} (y1 : B) (P : type1413 A B) (x : A) (y2 : B) (h1 : term30 A B y1 P x y2) : P x y2.
Proof. exact (proj2 (@lem14301 A B y1 P x y2 h1)). Qed.
Lemma lem14702 {A B : Type'} (y1 : B) (P : type1413 A B) (x : A) (y2 : B) (h1 : term30 A B y1 P x y2) : P x y1.
Proof. exact (proj1 (@lem14301 A B y1 P x y2 h1)). Qed.
Lemma lem14703 {A B : Type'} (y1 : B) (P : type1413 A B) (x : A) (y2 : B) (h1 : term99 A B P) (h2 : term11 A B P) (h3 : P x y1) (h4 : P x y2) : (P x y2) = (y1 = y2).
Proof. exact (prop_ext (fun h5 : P x y2 => @lem14700 A B y1 P x y2 h1 h2 h3 h4) (fun h5 : y1 = y2 => @lem14302 A B P x y2 h4)). Qed.
Lemma lem14704 {A B : Type'} (y1 : B) (P : type1413 A B) (x : A) (y2 : B) (h1 : term99 A B P) (h2 : term11 A B P) (h3 : P x y1) (h4 : P x y2) : y1 = y2.
Proof. exact (EQ_MP (@lem14703 A B y1 P x y2 h1 h2 h3 h4) (@lem14302 A B P x y2 h4)). Qed.
Lemma lem14705 {A B : Type'} (y1 : B) (P : type1413 A B) (x : A) (y2 : B) (h1 : term99 A B P) (h2 : term11 A B P) (h3 : P x y1) (h4 : P x y2) : (P x y1) = (y1 = y2).
Proof. exact (prop_ext (fun h5 : P x y1 => @lem14704 A B y1 P x y2 h1 h2 h3 h4) (fun h5 : y1 = y2 => @lem14303 A B P x y1 h3)). Qed.
Lemma lem14706 {A B : Type'} (y1 : B) (P : type1413 A B) (x : A) (y2 : B) (h1 : term99 A B P) (h2 : term11 A B P) (h3 : P x y1) (h4 : P x y2) : y1 = y2.
Proof. exact (EQ_MP (@lem14705 A B y1 P x y2 h1 h2 h3 h4) (@lem14303 A B P x y1 h3)). Qed.
Lemma lem14707 {A B : Type'} (y2 : B) (P : type1413 A B) (x : A) (y1 : B) (h1 : term99 A B P) (h2 : term11 A B P) (h3 : term30 A B y1 P x y2) (h4 : P x y1) : (P x y2) = (y1 = y2).
Proof. exact (prop_ext (fun h5 : P x y2 => @lem14706 A B y1 P x y2 h1 h2 h4 h5) (fun h5 : y1 = y2 => @lem14701 A B y1 P x y2 h3)). Qed.
Lemma lem14708 {A B : Type'} (y2 : B) (P : type1413 A B) (x : A) (y1 : B) (h1 : term99 A B P) (h2 : term11 A B P) (h3 : term30 A B y1 P x y2) (h4 : P x y1) : y1 = y2.
Proof. exact (EQ_MP (@lem14707 A B y2 P x y1 h1 h2 h3 h4) (@lem14701 A B y1 P x y2 h3)). Qed.
Lemma lem14709 {A B : Type'} (y1 : B) (P : type1413 A B) (x : A) (y2 : B) (h1 : term99 A B P) (h2 : term11 A B P) (h3 : term30 A B y1 P x y2) : (P x y1) = (y1 = y2).
Proof. exact (prop_ext (fun h4 : P x y1 => @lem14708 A B y2 P x y1 h1 h2 h3 h4) (fun h4 : y1 = y2 => @lem14702 A B y1 P x y2 h3)). Qed.
Lemma lem14710 {A B : Type'} (y1 : B) (P : type1413 A B) (x : A) (y2 : B) (h1 : term99 A B P) (h2 : term11 A B P) (h3 : term30 A B y1 P x y2) : y1 = y2.
Proof. exact (EQ_MP (@lem14709 A B y1 P x y2 h1 h2 h3) (@lem14702 A B y1 P x y2 h3)). Qed.
Lemma lem14711 {A B : Type'} (x : A) (y1 : B) (y2 : B) (P : type1413 A B) (h1 : term99 A B P) (h2 : term11 A B P) : term34 A B P x y1 y2.
Proof. exact (fun h0 : term30 A B y1 P x y2 => @lem14710 A B y1 P x y2 h1 h2 h0). Qed.
Lemma lem14716 {A B : Type'} (x : A) (y1 : B) (P : type1413 A B) (h1 : term99 A B P) (h2 : term11 A B P) : term38 A B P x y1.
Proof. exact (fun y2 : B => @lem14711 A B x y1 y2 P h1 h2). Qed.
Lemma lem14721 {A B : Type'} (x : A) (P : type1413 A B) (h1 : term99 A B P) (h2 : term11 A B P) : term42 A B P x.
Proof. exact (fun y1 : B => @lem14716 A B x y1 P h1 h2). Qed.
Lemma lem14726 {A B : Type'} (P : type1413 A B) (h1 : term99 A B P) (h2 : term11 A B P) : term65 A B P.
Proof. exact (fun x : A => @lem14721 A B x P h1 h2). Qed.
Lemma lem14727 {A B : Type'} (P : type1413 A B) (h1 : term99 A B P) (h2 : term11 A B P) : term68 A B P.
Proof. exact (EQ_MP (@lem14189 A B P h2) (@lem14726 A B P h1 h2)). Qed.
Lemma lem14728 {A B : Type'} (P : type1413 A B) (h1 : term65 A B P) (h2 : term11 A B P) : term100 A B P.
Proof. exact (EQ_MP (@lem14129 A B P h2) (@lem14300 A B P h1)). Qed.
Lemma lem14729 {A B : Type'} (P : type1413 A B) (h1 : term100 A B P) : term99 A B P.
Proof. exact (proj2 (@lem14056 A B P h1)). Qed.
Lemma lem14730 {A B : Type'} (P : type1413 A B) (h1 : term100 A B P) : term11 A B P.
Proof. exact (proj1 (@lem14056 A B P h1)). Qed.
Lemma lem14731 {A B : Type'} (P : type1413 A B) (h1 : term99 A B P) (h2 : term11 A B P) : (term99 A B P) = (term68 A B P).
Proof. exact (prop_ext (fun h3 : term99 A B P => @lem14727 A B P h1 h2) (fun h3 : term68 A B P => @lem14057 A B P h1)). Qed.
Lemma lem14732 {A B : Type'} (P : type1413 A B) (h1 : term99 A B P) (h2 : term11 A B P) : term68 A B P.
Proof. exact (EQ_MP (@lem14731 A B P h1 h2) (@lem14057 A B P h1)). Qed.
Lemma lem14733 {A B : Type'} (P : type1413 A B) (h1 : term99 A B P) (h2 : term11 A B P) : (term11 A B P) = (term68 A B P).
Proof. exact (prop_ext (fun h3 : term11 A B P => @lem14732 A B P h1 h2) (fun h3 : term68 A B P => @lem14058 A B P h2)). Qed.
Lemma lem14734 {A B : Type'} (P : type1413 A B) (h1 : term99 A B P) (h2 : term11 A B P) : term68 A B P.
Proof. exact (EQ_MP (@lem14733 A B P h1 h2) (@lem14058 A B P h2)). Qed.
Lemma lem14735 {A B : Type'} (P : type1413 A B) (h1 : term11 A B P) (h2 : term100 A B P) : (term99 A B P) = (term68 A B P).
Proof. exact (prop_ext (fun h3 : term99 A B P => @lem14734 A B P h3 h1) (fun h3 : term68 A B P => @lem14729 A B P h2)). Qed.
Lemma lem14736 {A B : Type'} (P : type1413 A B) (h1 : term11 A B P) (h2 : term100 A B P) : term68 A B P.
Proof. exact (EQ_MP (@lem14735 A B P h1 h2) (@lem14729 A B P h2)). Qed.
Lemma lem14737 {A B : Type'} (P : type1413 A B) (h1 : term100 A B P) : (term11 A B P) = (term68 A B P).
Proof. exact (prop_ext (fun h2 : term11 A B P => @lem14736 A B P h2 h1) (fun h2 : term68 A B P => @lem14730 A B P h1)). Qed.
Lemma lem14738 {A B : Type'} (P : type1413 A B) (h1 : term100 A B P) : term68 A B P.
Proof. exact (EQ_MP (@lem14737 A B P h1) (@lem14730 A B P h1)). Qed.
Lemma lem14739 {A B : Type'} (P : type1413 A B) : term166 A B P.
Proof. exact (fun h0 : term100 A B P => @lem14738 A B P h0). Qed.
Lemma lem14740 {A B : Type'} (P : type1413 A B) (h1 : term68 A B P) : term65 A B P.
Proof. exact (proj2 (@lem14053 A B P h1)). Qed.
Lemma lem14741 {A B : Type'} (P : type1413 A B) (h1 : term68 A B P) : term11 A B P.
Proof. exact (proj1 (@lem14053 A B P h1)). Qed.
Lemma lem14742 {A B : Type'} (P : type1413 A B) (h1 : term65 A B P) (h2 : term11 A B P) : (term65 A B P) = (term100 A B P).
Proof. exact (prop_ext (fun h3 : term65 A B P => @lem14728 A B P h1 h2) (fun h3 : term100 A B P => @lem14054 A B P h1)). Qed.
Lemma lem14743 {A B : Type'} (P : type1413 A B) (h1 : term65 A B P) (h2 : term11 A B P) : term100 A B P.
Proof. exact (EQ_MP (@lem14742 A B P h1 h2) (@lem14054 A B P h1)). Qed.
Lemma lem14744 {A B : Type'} (P : type1413 A B) (h1 : term65 A B P) (h2 : term11 A B P) : (term11 A B P) = (term100 A B P).
Proof. exact (prop_ext (fun h3 : term11 A B P => @lem14743 A B P h1 h2) (fun h3 : term100 A B P => @lem14055 A B P h2)). Qed.
Lemma lem14745 {A B : Type'} (P : type1413 A B) (h1 : term65 A B P) (h2 : term11 A B P) : term100 A B P.
Proof. exact (EQ_MP (@lem14744 A B P h1 h2) (@lem14055 A B P h2)). Qed.
Lemma lem14746 {A B : Type'} (P : type1413 A B) (h1 : term11 A B P) (h2 : term68 A B P) : (term65 A B P) = (term100 A B P).
Proof. exact (prop_ext (fun h3 : term65 A B P => @lem14745 A B P h3 h1) (fun h3 : term100 A B P => @lem14740 A B P h2)). Qed.
Lemma lem14747 {A B : Type'} (P : type1413 A B) (h1 : term11 A B P) (h2 : term68 A B P) : term100 A B P.
Proof. exact (EQ_MP (@lem14746 A B P h1 h2) (@lem14740 A B P h2)). Qed.
Lemma lem14748 {A B : Type'} (P : type1413 A B) (h1 : term68 A B P) : (term11 A B P) = (term100 A B P).
Proof. exact (prop_ext (fun h2 : term11 A B P => @lem14747 A B P h2 h1) (fun h2 : term100 A B P => @lem14741 A B P h1)). Qed.
Lemma lem14749 {A B : Type'} (P : type1413 A B) (h1 : term68 A B P) : term100 A B P.
Proof. exact (EQ_MP (@lem14748 A B P h1) (@lem14741 A B P h1)). Qed.
Lemma lem14750 {A B : Type'} (P : type1413 A B) : term167 A B P.
Proof. exact (fun h0 : term68 A B P => @lem14749 A B P h0). Qed.
Lemma lem14751 {A B : Type'} (P : type1413 A B) : term168 A B P.
Proof. exact (conj (@lem14750 A B P) (@lem14739 A B P)). Qed.
Lemma lem14752 {A B : Type'} (P : type1413 A B) : (term168 A B P) = ((term68 A B P) = (term100 A B P)).
Proof. exact (@lem32 (term68 A B P) (term100 A B P)). Qed.
Lemma lem14753 {A B : Type'} (P : type1413 A B) : (term68 A B P) = (term100 A B P).
Proof. exact (EQ_MP (@lem14752 A B P) (@lem14751 A B P)). Qed.
Lemma lem14754 {A B : Type'} (P : type1413 A B) : (term46 A B P) = (term79 A B P).
Proof. exact (EQ_MP (@lem14052 A B P) (@lem14753 A B P)). Qed.
Lemma lem14759 {A B : Type'} : term169 A B.
Proof. exact (fun P : type1413 A B => @lem14754 A B P). Qed.
