Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SURJECTIVE_IMAGE_THM_term_abbrevs.
Require Import DISJ_ACI_spec.
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
Require Import thm18394_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
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
Require Import thm21741_spec.
Require Import thm21761_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Require Import thm32_spec.
Lemma lem3586853 {_83095 : Type'} : term0 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem3586854 {_83095 : Type'} (p : _83095 -> Prop) : term1 _83095 p.
Proof. exact (@lem3586853 _83095 p). Qed.
Lemma lem3586855 {_83095 : Type'} (p : _83095 -> Prop) : (term1 _83095 p) = (term2 _83095 p).
Proof. exact (eq_refl (term1 _83095 p)). Qed.
Lemma lem3586856 {_83095 : Type'} (p : _83095 -> Prop) : term2 _83095 p.
Proof. exact (EQ_MP (@lem3586855 _83095 p) (@lem3586854 _83095 p)). Qed.
Lemma lem3586857 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term3 _83095 p x.
Proof. exact (@lem3586856 _83095 p x). Qed.
Lemma lem3586858 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term3 _83095 p x) = ((term4 _83095 x p) = (p x)).
Proof. exact (eq_refl (term3 _83095 p x)). Qed.
Lemma lem3586867 {A B : Type'} (y : B) : term5 A B y.
Proof. exact (@lem3206070 A B y). Qed.
Lemma lem3586868 {A B : Type'} (y : B) : (term5 A B y) = (term6 A B y).
Proof. exact (eq_refl (term5 A B y)). Qed.
Lemma lem3586869 {A B : Type'} (y : B) : term6 A B y.
Proof. exact (EQ_MP (@lem3586868 A B y) (@lem3586867 A B y)). Qed.
Lemma lem3586870 {A B : Type'} (y : B) (s : A -> Prop) : term7 A B y s.
Proof. exact (@lem3586869 A B y s). Qed.
Lemma lem3586871 {A B : Type'} (y : B) (s : A -> Prop) : (term7 A B y s) = (term8 A B y s).
Proof. exact (eq_refl (term7 A B y s)). Qed.
Lemma lem3586872 {A B : Type'} (y : B) (s : A -> Prop) : term8 A B y s.
Proof. exact (EQ_MP (@lem3586871 A B y s) (@lem3586870 A B y s)). Qed.
Lemma lem3586873 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) : term9 A B y s f.
Proof. exact (@lem3586872 A B y s f). Qed.
Lemma lem3586874 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term9 A B y s f) = ((term10 A B y f s) = (term11 A B y f s)).
Proof. exact (eq_refl (term9 A B y s f)). Qed.
Lemma lem3586876 {A : Type'} (s : A -> Prop) : term12 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem3586877 {A : Type'} (s : A -> Prop) : (term12 A s) = (term13 A s).
Proof. exact (eq_refl (term12 A s)). Qed.
Lemma lem3586878 {A : Type'} (s : A -> Prop) : term13 A s.
Proof. exact (EQ_MP (@lem3586877 A s) (@lem3586876 A s)). Qed.
Lemma lem3586879 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term14 A s t.
Proof. exact (@lem3586878 A s t). Qed.
Lemma lem3586880 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term14 A s t) = ((s = t) = (term15 A s t)).
Proof. exact (eq_refl (term14 A s t)). Qed.
Lemma lem3586905 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term15 A s t).
Proof. exact (EQ_MP (@lem3586880 A s t) (@lem3586879 A s t)). Qed.
Lemma lem3586906 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (s = t) = (term15 B s t).
Proof. exact (@lem3586905 B s t). Qed.
Lemma lem3586907 {A B : Type'} (f : A -> B) (P : B -> Prop) : ((term16 A B P f) = (term17 B P)) = (term18 A B f P).
Proof. exact (@lem3586906 B (term16 A B P f) (term17 B P)). Qed.
Lemma lem3586917 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term10 A B y f s) = (term11 A B y f s).
Proof. exact (EQ_MP (@lem3586874 A B y f s) (@lem3586873 A B y s f)). Qed.
Lemma lem3586918 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term10 A B y f s) = (term11 A B y f s).
Proof. exact (@lem3586917 A B y f s). Qed.
Lemma lem3586919 {A B : Type'} (x : B) (P : B -> Prop) (f : A -> B) : (term19 A B x P f) = (term20 A B x P f).
Proof. exact (@lem3586918 A B x f (term21 A B P f)). Qed.
Lemma lem3586931 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term4 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3586858 _83095 p x) (@lem3586857 _83095 p x)). Qed.
Lemma lem3586932 {A : Type'} (p : A -> Prop) (x : A) : (term4 A x p) = (p x).
Proof. exact (@lem3586931 A p x). Qed.
Lemma lem3586933 {A B : Type'} (P : B -> Prop) (f : A -> B) (x : A) : (term22 A B x P f) = (term23 A B P f x).
Proof. exact (@lem3586932 A (term24 A B P f) x). Qed.
Lemma lem3586934 {A B : Type'} (P : B -> Prop) (f : A -> B) (x : A) : (term23 A B P f x) = (term25 A B P f x).
Proof. exact (eq_refl (term23 A B P f x)). Qed.
Lemma lem3586935 {A : Type'} (GEN_PVAR_89 : A) : (@SETSPEC A GEN_PVAR_89) = (@SETSPEC A GEN_PVAR_89).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_89)). Qed.
Lemma lem3586936 {A B : Type'} (GEN_PVAR_89 : A) (P : B -> Prop) (f : A -> B) (x : A) : (term26 A B GEN_PVAR_89 P f x) = (term27 A B GEN_PVAR_89 P f x).
Proof. exact (MK_COMB (@lem3586935 A GEN_PVAR_89) (@lem3586934 A B P f x)). Qed.
Lemma lem3586937 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3586938 {A B : Type'} (GEN_PVAR_89 : A) (P : B -> Prop) (f : A -> B) (x : A) : (term28 A B GEN_PVAR_89 P f x) = (term29 A B GEN_PVAR_89 P f x).
Proof. exact (MK_COMB (@lem3586936 A B GEN_PVAR_89 P f x) (@lem3586937 A x)). Qed.
Lemma lem3586939 {A B : Type'} (GEN_PVAR_89 : A) (P : B -> Prop) (f : A -> B) : (term30 A B GEN_PVAR_89 P f) = (term31 A B GEN_PVAR_89 P f).
Proof. exact (fun_ext (fun x : A => @lem3586938 A B GEN_PVAR_89 P f x)). Qed.
Lemma lem3586940 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3586941 {A B : Type'} (GEN_PVAR_89 : A) (P : B -> Prop) (f : A -> B) : (term32 A B GEN_PVAR_89 P f) = (term33 A B GEN_PVAR_89 P f).
Proof. exact (MK_COMB (@lem3586940 A) (@lem3586939 A B GEN_PVAR_89 P f)). Qed.
Lemma lem3586942 {A B : Type'} (P : B -> Prop) (f : A -> B) : (term34 A B P f) = (term35 A B P f).
Proof. exact (fun_ext (fun GEN_PVAR_89 : A => @lem3586941 A B GEN_PVAR_89 P f)). Qed.
Lemma lem3586943 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem3586944 {A B : Type'} (P : B -> Prop) (f : A -> B) : (term36 A B P f) = (term21 A B P f).
Proof. exact (MK_COMB (@lem3586943 A) (@lem3586942 A B P f)). Qed.
Lemma lem3586945 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem3586946 {A B : Type'} (x : A) (P : B -> Prop) (f : A -> B) : (term22 A B x P f) = (term37 A B x P f).
Proof. exact (MK_COMB (@lem3586945 A x) (@lem3586944 A B P f)). Qed.
Lemma lem3586947 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3586948 {A B : Type'} (x : A) (P : B -> Prop) (f : A -> B) : (term38 A B x P f) = (term39 A B x P f).
Proof. exact (MK_COMB (@lem3586947) (@lem3586946 A B x P f)). Qed.
Lemma lem3586949 {A B : Type'} (P : B -> Prop) (f : A -> B) (x : A) : (term23 A B P f x) = (term25 A B P f x).
Proof. exact (eq_refl (term23 A B P f x)). Qed.
Lemma lem3586950 {A B : Type'} (P : B -> Prop) (f : A -> B) (x : A) : ((term22 A B x P f) = (term23 A B P f x)) = ((term37 A B x P f) = (term25 A B P f x)).
Proof. exact (MK_COMB (@lem3586948 A B x P f) (@lem3586949 A B P f x)). Qed.
Lemma lem3586951 {A B : Type'} (P : B -> Prop) (f : A -> B) (x : A) : (term37 A B x P f) = (term25 A B P f x).
Proof. exact (EQ_MP (@lem3586950 A B P f x) (@lem3586933 A B P f x)). Qed.
Lemma lem3586952 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term40 A B x f x') = (term40 A B x f x').
Proof. exact (eq_refl (term40 A B x f x')). Qed.
Lemma lem3586953 {A B : Type'} (x : B) (P : B -> Prop) (f : A -> B) (x' : A) : (term41 A B x x' P f) = (term42 A B x P f x').
Proof. exact (MK_COMB (@lem3586952 A B x f x') (@lem3586951 A B P f x')). Qed.
Lemma lem3586956 {A B : Type'} (x : B) (P : B -> Prop) (f : A -> B) : (term43 A B x P f) = (term44 A B x P f).
Proof. exact (fun_ext (fun x' : A => @lem3586953 A B x P f x')). Qed.
Lemma lem3586957 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3586958 {A B : Type'} (x : B) (P : B -> Prop) (f : A -> B) : (term20 A B x P f) = (term45 A B x P f).
Proof. exact (MK_COMB (@lem3586957 A) (@lem3586956 A B x P f)). Qed.
Lemma lem3586963 {A B : Type'} (x : B) (P : B -> Prop) (f : A -> B) : (term19 A B x P f) = (term45 A B x P f).
Proof. exact (TRANS (@lem3586919 A B x P f) (@lem3586958 A B x P f)). Qed.
Lemma lem3586964 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3586965 {A B : Type'} (x : B) (P : B -> Prop) (f : A -> B) : (term46 A B x P f) = (term47 A B x P f).
Proof. exact (MK_COMB (@lem3586964) (@lem3586963 A B x P f)). Qed.
Lemma lem3586967 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term4 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3586858 _83095 p x) (@lem3586857 _83095 p x)). Qed.
Lemma lem3586968 {B : Type'} (p : B -> Prop) (x : B) : (term4 B x p) = (p x).
Proof. exact (@lem3586967 B p x). Qed.
Lemma lem3586969 {B : Type'} (P : B -> Prop) (x : B) : (term4 B x P) = (P x).
Proof. exact (@lem3586968 B P x). Qed.
Lemma lem3586970 {A B : Type'} (f : A -> B) (P : B -> Prop) (x : B) : ((term19 A B x P f) = (term4 B x P)) = ((term45 A B x P f) = (P x)).
Proof. exact (MK_COMB (@lem3586965 A B x P f) (@lem3586969 B P x)). Qed.
Lemma lem3586975 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term48 A B f P) = (term49 A B f P).
Proof. exact (fun_ext (fun x : B => @lem3586970 A B f P x)). Qed.
Lemma lem3586976 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3586977 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term18 A B f P) = (term50 A B f P).
Proof. exact (MK_COMB (@lem3586976 B) (@lem3586975 A B f P)). Qed.
Lemma lem3586982 {A B : Type'} (f : A -> B) (P : B -> Prop) : ((term16 A B P f) = (term17 B P)) = (term50 A B f P).
Proof. exact (TRANS (@lem3586907 A B f P) (@lem3586977 A B f P)). Qed.
Lemma lem3586983 {A B : Type'} (f : A -> B) : (term51 A B f) = (term52 A B f).
Proof. exact (fun_ext (fun P : B -> Prop => @lem3586982 A B f P)). Qed.
Lemma lem3586984 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3586985 {A B : Type'} (f : A -> B) : (term53 A B f) = (term54 A B f).
Proof. exact (MK_COMB (@lem3586984 B) (@lem3586983 A B f)). Qed.
Lemma lem3586990 {A B : Type'} (f : A -> B) : (term55 A B f) = (term55 A B f).
Proof. exact (eq_refl (term55 A B f)). Qed.
Lemma lem3586991 {A B : Type'} (f : A -> B) : ((term56 A B f) = (term53 A B f)) = ((term56 A B f) = (term54 A B f)).
Proof. exact (MK_COMB (@lem3586990 A B f) (@lem3586985 A B f)). Qed.
Lemma lem3586996 {A B : Type'} (f : A -> B) : ((term56 A B f) = (term54 A B f)) = ((term56 A B f) = (term53 A B f)).
Proof. exact (SYM (@lem3586991 A B f)). Qed.
Lemma lem3586997 {A B : Type'} (f : A -> B) (h1 : term54 A B f) : term54 A B f.
Proof. exact (h1). Qed.
Lemma lem3586998 {A B : Type'} (f : A -> B) (h1 : term54 A B f) : term57 A B f.
Proof. exact (@lem3586997 A B f h1 (term58 B)). Qed.
Lemma lem3586999 {A B : Type'} (f : A -> B) : (term57 A B f) = (term59 A B f).
Proof. exact (eq_refl (term57 A B f)). Qed.
Lemma lem3587000 {A B : Type'} (f : A -> B) (h1 : term54 A B f) : term59 A B f.
Proof. exact (EQ_MP (@lem3586999 A B f) (@lem3586998 A B f h1)). Qed.
Lemma lem3587002 (p : Prop) : p = (term60 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3587003 {A B : Type'} (f : A -> B) : (term61 A B f) = (term62 A B f).
Proof. exact (@lem3587002 (term61 A B f)). Qed.
Lemma lem3587004 {A B : Type'} (f : A -> B) : (term62 A B f) = (term61 A B f).
Proof. exact (SYM (@lem3587003 A B f)). Qed.
Lemma lem3587005 {A B : Type'} (f : A -> B) (h1 : term63 A B f) : term63 A B f.
Proof. exact (h1). Qed.
Lemma lem3587008 {A B : Type'} (f : A -> B) (h1 : term62 A B f) : term62 A B f.
Proof. exact (h1). Qed.
Lemma lem3587009 {A B : Type'} (f : A -> B) : term64 A B f.
Proof. exact (fun h0 : term62 A B f => @lem3587008 A B f h0). Qed.
Lemma lem3587010 {A B : Type'} (f : A -> B) (h1 : term64 A B f) : term64 A B f.
Proof. exact (h1). Qed.
Lemma lem3587011 {A B : Type'} (f : A -> B) (h1 : term62 A B f) : term62 A B f.
Proof. exact (h1). Qed.
Lemma lem3587012 {A B : Type'} (f : A -> B) (h1 : term62 A B f) (h2 : term64 A B f) : term62 A B f.
Proof. exact (@lem3587010 A B f h2 (@lem3587011 A B f h1)). Qed.
Lemma lem3587013 {A B : Type'} (f : A -> B) (h1 : term62 A B f) : term65 A B f.
Proof. exact (fun h0 : term64 A B f => @lem3587012 A B f h1 h0). Qed.
Lemma lem3587014 {A B : Type'} (f : A -> B) (h1 : term64 A B f) : term64 A B f.
Proof. exact (h1). Qed.
Lemma lem3587015 {A B : Type'} (f : A -> B) (h1 : term62 A B f) (h2 : term64 A B f) : term62 A B f.
Proof. exact (@lem3587013 A B f h1 (@lem3587014 A B f h2)). Qed.
Lemma lem3587016 {A B : Type'} (f : A -> B) (h1 : term64 A B f) : term64 A B f.
Proof. exact (fun h0 : term62 A B f => @lem3587015 A B f h0 h1). Qed.
Lemma lem3587017 {A B : Type'} (f : A -> B) : term66 A B f.
Proof. exact (fun h0 : term64 A B f => @lem3587016 A B f h0). Qed.
Lemma lem3587020 {A B : Type'} (f : A -> B) : term64 A B f.
Proof. exact (@lem3587017 A B f (@lem3587009 A B f)). Qed.
Lemma lem3587021 {A B : Type'} (f : A -> B) : term64 A B f.
Proof. exact (@lem3587020 A B f). Qed.
Lemma lem3587027 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3587028 {A B : Type'} (f : A -> B) : (term62 A B f) = (term67 A B f).
Proof. exact (@lem3587027 (term63 A B f)). Qed.
Lemma lem3587030 (t : Prop) : (term68 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3587031 {A B : Type'} (f : A -> B) : (term67 A B f) = (term61 A B f).
Proof. exact (@lem3587030 (term61 A B f)). Qed.
Lemma lem3587034 {A B : Type'} (f : A -> B) : (term62 A B f) = (term61 A B f).
Proof. exact (TRANS (@lem3587028 A B f) (@lem3587031 A B f)). Qed.
Lemma lem3587101 {A B : Type'} : (term69 A B) = (term70 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3587034 A B f)). Qed.
Lemma lem3587102 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3587111 {A B : Type'} : (term71 A B) = (term72 A B).
Proof. exact (MK_COMB (@lem3587102 A B) (@lem3587101 A B)). Qed.
Lemma lem3587112 {B : Type'} (P : B -> Prop) (x : B) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem3587117 {A B : Type'} (x : B) (P : B -> Prop) (f : A -> B) (x' : A) : (term42 A B x P f x') = (term42 A B x P f x').
Proof. exact (eq_refl (term42 A B x P f x')). Qed.
Lemma lem3587118 {A B : Type'} (x : B) (P : B -> Prop) (f : A -> B) : (term44 A B x P f) = (term44 A B x P f).
Proof. exact (fun_ext (fun x' : A => @lem3587117 A B x P f x')). Qed.
Lemma lem3587119 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3587120 {A B : Type'} (x : B) (P : B -> Prop) (f : A -> B) : (term45 A B x P f) = (term45 A B x P f).
Proof. exact (MK_COMB (@lem3587119 A) (@lem3587118 A B x P f)). Qed.
Lemma lem3587121 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3587122 {A B : Type'} (x : B) (P : B -> Prop) (f : A -> B) : (term47 A B x P f) = (term47 A B x P f).
Proof. exact (MK_COMB (@lem3587121) (@lem3587120 A B x P f)). Qed.
Lemma lem3587123 {A B : Type'} (f : A -> B) (P : B -> Prop) (x : B) : ((term45 A B x P f) = (P x)) = ((term45 A B x P f) = (P x)).
Proof. exact (MK_COMB (@lem3587122 A B x P f) (@lem3587112 B P x)). Qed.
Lemma lem3587124 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term49 A B f P) = (term49 A B f P).
Proof. exact (fun_ext (fun x : B => @lem3587123 A B f P x)). Qed.
Lemma lem3587125 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3587126 {A B : Type'} (f : A -> B) (P : B -> Prop) : (term50 A B f P) = (term50 A B f P).
Proof. exact (MK_COMB (@lem3587125 B) (@lem3587124 A B f P)). Qed.
Lemma lem3587127 {A B : Type'} (f : A -> B) : (term52 A B f) = (term52 A B f).
Proof. exact (fun_ext (fun P : B -> Prop => @lem3587126 A B f P)). Qed.
Lemma lem3587128 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3587129 {A B : Type'} (f : A -> B) : (term54 A B f) = (term54 A B f).
Proof. exact (MK_COMB (@lem3587128 B) (@lem3587127 A B f)). Qed.
Lemma lem3587130 {A B : Type'} (f : A -> B) (x : A) (y : B) : ((f x) = y) = ((f x) = y).
Proof. exact (eq_refl ((f x) = y)). Qed.
Lemma lem3587131 {A B : Type'} (f : A -> B) (y : B) : (term73 A B f y) = (term73 A B f y).
Proof. exact (fun_ext (fun x : A => @lem3587130 A B f x y)). Qed.
Lemma lem3587132 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3587133 {A B : Type'} (f : A -> B) (y : B) : (term74 A B f y) = (term74 A B f y).
Proof. exact (MK_COMB (@lem3587132 A) (@lem3587131 A B f y)). Qed.
Lemma lem3587134 {A B : Type'} (f : A -> B) : (term75 A B f) = (term75 A B f).
Proof. exact (fun_ext (fun y : B => @lem3587133 A B f y)). Qed.
Lemma lem3587135 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3587136 {A B : Type'} (f : A -> B) : (term56 A B f) = (term56 A B f).
Proof. exact (MK_COMB (@lem3587135 B) (@lem3587134 A B f)). Qed.
Lemma lem3587137 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3587138 {A B : Type'} (f : A -> B) : (term76 A B f) = (term76 A B f).
Proof. exact (MK_COMB (@lem3587137) (@lem3587136 A B f)). Qed.
Lemma lem3587139 {A B : Type'} (f : A -> B) : (term61 A B f) = (term61 A B f).
Proof. exact (MK_COMB (@lem3587138 A B f) (@lem3587129 A B f)). Qed.
Lemma lem3587140 {A B : Type'} : (term70 A B) = (term70 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3587139 A B f)). Qed.
Lemma lem3587141 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3587142 {A B : Type'} : (term72 A B) = (term72 A B).
Proof. exact (MK_COMB (@lem3587141 A B) (@lem3587140 A B)). Qed.
Lemma lem3587185 {A B : Type'} : (term71 A B) = (term72 A B).
Proof. exact (TRANS (@lem3587111 A B) (@lem3587142 A B)). Qed.
Lemma lem3587186 {A B : Type'} : (term72 A B) = (term71 A B).
Proof. exact (SYM (@lem3587185 A B)). Qed.
Lemma lem3587187 {A B : Type'} (f : A -> B) (h1 : term56 A B f) : term56 A B f.
Proof. exact (h1). Qed.
Lemma lem3587189 (p : Prop) : p = (term60 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3587190 {A B : Type'} (f : A -> B) (P : B -> Prop) (x : B) : ((term45 A B x P f) = (P x)) = (term77 A B f P x).
Proof. exact (@lem3587189 ((term45 A B x P f) = (P x))). Qed.
Lemma lem3587191 {A B : Type'} (f : A -> B) (P : B -> Prop) (x : B) : (term77 A B f P x) = ((term45 A B x P f) = (P x)).
Proof. exact (SYM (@lem3587190 A B f P x)). Qed.
Lemma lem3587192 {A B : Type'} (f : A -> B) (P : B -> Prop) (x : B) (h1 : term78 A B f P x) : term78 A B f P x.
Proof. exact (h1). Qed.
Lemma lem3587193 {A B : Type'} (f : A -> B) (x : A) (y : B) : ((f x) = y) = ((f x) = y).
Proof. exact (eq_refl ((f x) = y)). Qed.
Lemma lem3587194 {A B : Type'} (f : A -> B) (y : B) : (term73 A B f y) = (term73 A B f y).
Proof. exact (fun_ext (fun x : A => @lem3587193 A B f x y)). Qed.
Lemma lem3587195 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3587196 {A B : Type'} (f : A -> B) (y : B) : (term74 A B f y) = (term74 A B f y).
Proof. exact (MK_COMB (@lem3587195 A) (@lem3587194 A B f y)). Qed.
Lemma lem3587197 {A B : Type'} (f : A -> B) : (term75 A B f) = (term75 A B f).
Proof. exact (fun_ext (fun y : B => @lem3587196 A B f y)). Qed.
Lemma lem3587198 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3587199 {A B : Type'} (f : A -> B) : (term56 A B f) = (term56 A B f).
Proof. exact (MK_COMB (@lem3587198 B) (@lem3587197 A B f)). Qed.
Lemma lem3587210 {A B : Type'} (P : type1413 A B) : (term79 A B P) = (term80 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3587211 {A B : Type'} (P : type1470 A B) : (term81 A B P) = (term82 A B P).
Proof. exact (@lem3587210 B A P). Qed.
Lemma lem3587212 {A B : Type'} (f : A -> B) : (term83 A B f) = (term84 A B f).
Proof. exact (@lem3587211 A B (term85 A B f)). Qed.
Lemma lem3587213 {A B : Type'} (f : A -> B) (y : B) : (term86 A B f y) = (term73 A B f y).
Proof. exact (eq_refl (term86 A B f y)). Qed.
Lemma lem3587214 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3587215 {A B : Type'} (f : A -> B) (y : B) (x : A) : (term87 A B f y x) = (term88 A B f y x).
Proof. exact (MK_COMB (@lem3587213 A B f y) (@lem3587214 A x)). Qed.
Lemma lem3587216 {A B : Type'} (f : A -> B) (x : A) (y : B) : (term88 A B f y x) = ((f x) = y).
Proof. exact (eq_refl (term88 A B f y x)). Qed.
Lemma lem3587217 {A B : Type'} (f : A -> B) (x : A) (y : B) : (term87 A B f y x) = ((f x) = y).
Proof. exact (TRANS (@lem3587215 A B f y x) (@lem3587216 A B f x y)). Qed.
Lemma lem3587218 {A B : Type'} (f : A -> B) (y : B) : (term89 A B f y) = (term73 A B f y).
Proof. exact (fun_ext (fun x : A => @lem3587217 A B f x y)). Qed.
Lemma lem3587219 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3587220 {A B : Type'} (f : A -> B) (y : B) : (term90 A B f y) = (term74 A B f y).
Proof. exact (MK_COMB (@lem3587219 A) (@lem3587218 A B f y)). Qed.
Lemma lem3587221 {A B : Type'} (f : A -> B) : (term91 A B f) = (term75 A B f).
Proof. exact (fun_ext (fun y : B => @lem3587220 A B f y)). Qed.
Lemma lem3587222 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3587223 {A B : Type'} (f : A -> B) : (term83 A B f) = (term56 A B f).
Proof. exact (MK_COMB (@lem3587222 B) (@lem3587221 A B f)). Qed.
Lemma lem3587224 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3587225 {A B : Type'} (f : A -> B) : (term92 A B f) = (term55 A B f).
Proof. exact (MK_COMB (@lem3587224) (@lem3587223 A B f)). Qed.
Lemma lem3587226 {A B : Type'} (f : A -> B) (y : B) : (term86 A B f y) = (term73 A B f y).
Proof. exact (eq_refl (term86 A B f y)). Qed.
Lemma lem3587227 {A B : Type'} (x : B -> A) (y : B) : (x y) = (x y).
Proof. exact (eq_refl (x y)). Qed.
Lemma lem3587228 {A B : Type'} (f : A -> B) (x : B -> A) (y : B) : (term93 A B f x y) = (term94 A B f x y).
Proof. exact (MK_COMB (@lem3587226 A B f y) (@lem3587227 A B x y)). Qed.
Lemma lem3587229 {A B : Type'} (f : A -> B) (x : B -> A) (y : B) : (term94 A B f x y) = ((term95 A B f x y) = y).
Proof. exact (eq_refl (term94 A B f x y)). Qed.
Lemma lem3587230 {A B : Type'} (f : A -> B) (x : B -> A) (y : B) : (term93 A B f x y) = ((term95 A B f x y) = y).
Proof. exact (TRANS (@lem3587228 A B f x y) (@lem3587229 A B f x y)). Qed.
Lemma lem3587231 {A B : Type'} (f : A -> B) (x : B -> A) : (term96 A B f x) = (term97 A B f x).
Proof. exact (fun_ext (fun y : B => @lem3587230 A B f x y)). Qed.
Lemma lem3587232 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3587233 {A B : Type'} (f : A -> B) (x : B -> A) : (term98 A B f x) = (term99 A B f x).
Proof. exact (MK_COMB (@lem3587232 B) (@lem3587231 A B f x)). Qed.
Lemma lem3587234 {A B : Type'} (f : A -> B) : (term100 A B f) = (term101 A B f).
Proof. exact (fun_ext (fun x : B -> A => @lem3587233 A B f x)). Qed.
Lemma lem3587235 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem3587236 {A B : Type'} (f : A -> B) : (term84 A B f) = (term102 A B f).
Proof. exact (MK_COMB (@lem3587235 A B) (@lem3587234 A B f)). Qed.
Lemma lem3587237 {A B : Type'} (f : A -> B) : ((term83 A B f) = (term84 A B f)) = ((term56 A B f) = (term102 A B f)).
Proof. exact (MK_COMB (@lem3587225 A B f) (@lem3587236 A B f)). Qed.
Lemma lem3587239 {A B : Type'} (f : A -> B) : (term56 A B f) = (term102 A B f).
Proof. exact (EQ_MP (@lem3587237 A B f) (@lem3587212 A B f)). Qed.
Lemma lem3587240 {A B : Type'} (f : A -> B) : (term56 A B f) = (term102 A B f).
Proof. exact (TRANS (@lem3587199 A B f) (@lem3587239 A B f)). Qed.
Lemma lem3587241 {A B : Type'} (f : A -> B) (h1 : term56 A B f) : term102 A B f.
Proof. exact (EQ_MP (@lem3587240 A B f) (@lem3587187 A B f h1)). Qed.
Lemma lem3587250 {A B : Type'} (x : B) (P : B -> Prop) (f : A -> B) (x' : A) : (term103 A B x P f x') = (term104 A B x P f x').
Proof. exact (@lem17045 (x = (f x')) (term25 A B P f x')). Qed.
Lemma lem3587253 {A B : Type'} (x : B) (P : B -> Prop) (f : A -> B) (x' : A) : (term42 A B x P f x') = (term42 A B x P f x').
Proof. exact (eq_refl (term42 A B x P f x')). Qed.
Lemma lem3587254 {A : Type'} (P : A -> Prop) : (term105 A P) = (term106 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem3587255 {A B : Type'} (x : B) (P : B -> Prop) (f : A -> B) : (term107 A B x P f) = (term108 A B x P f).
Proof. exact (@lem3587254 A (term44 A B x P f)). Qed.
Lemma lem3587256 {A B : Type'} (x : B) (P : B -> Prop) (f : A -> B) (x' : A) : (term109 A B x P f x') = (term42 A B x P f x').
Proof. exact (eq_refl (term109 A B x P f x')). Qed.
Lemma lem3587257 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3587258 {A B : Type'} (x : B) (P : B -> Prop) (f : A -> B) (x' : A) : (term110 A B x P f x') = (term103 A B x P f x').
Proof. exact (MK_COMB (@lem3587257) (@lem3587256 A B x P f x')). Qed.
Lemma lem3587259 {A B : Type'} (x : B) (P : B -> Prop) (f : A -> B) (x' : A) : (term110 A B x P f x') = (term104 A B x P f x').
Proof. exact (TRANS (@lem3587258 A B x P f x') (@lem3587250 A B x P f x')). Qed.
Lemma lem3587260 {A B : Type'} (x : B) (P : B -> Prop) (f : A -> B) : (term111 A B x P f) = (term112 A B x P f).
Proof. exact (fun_ext (fun x' : A => @lem3587259 A B x P f x')). Qed.
Lemma lem3587261 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3587262 {A B : Type'} (x : B) (P : B -> Prop) (f : A -> B) : (term108 A B x P f) = (term113 A B x P f).
Proof. exact (MK_COMB (@lem3587261 A) (@lem3587260 A B x P f)). Qed.
Lemma lem3587263 {A B : Type'} (x : B) (P : B -> Prop) (f : A -> B) : (term107 A B x P f) = (term113 A B x P f).
Proof. exact (TRANS (@lem3587255 A B x P f) (@lem3587262 A B x P f)). Qed.
Lemma lem3587264 {A B : Type'} (x : B) (P : B -> Prop) (f : A -> B) : (term44 A B x P f) = (term44 A B x P f).
Proof. exact (fun_ext (fun x' : A => @lem3587253 A B x P f x')). Qed.
Lemma lem3587265 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3587266 {A B : Type'} (x : B) (P : B -> Prop) (f : A -> B) : (term45 A B x P f) = (term45 A B x P f).
Proof. exact (MK_COMB (@lem3587265 A) (@lem3587264 A B x P f)). Qed.
Lemma lem3587267 {B : Type'} (P : B -> Prop) (x : B) : (term114 B P x) = (term114 B P x).
Proof. exact (eq_refl (term114 B P x)). Qed.
Lemma lem3587268 {B : Type'} (P : B -> Prop) (x : B) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem3587269 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3587270 {A B : Type'} (x : B) (P : B -> Prop) (f : A -> B) : (term115 A B x P f) = (term116 A B x P f).
Proof. exact (MK_COMB (@lem3587269) (@lem3587263 A B x P f)). Qed.
Lemma lem3587271 {A B : Type'} (f : A -> B) (P : B -> Prop) (x : B) : (term117 A B f P x) = (term118 A B f P x).
Proof. exact (MK_COMB (@lem3587270 A B x P f) (@lem3587268 B P x)). Qed.
Lemma lem3587272 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3587273 {A B : Type'} (x : B) (P : B -> Prop) (f : A -> B) : (term119 A B x P f) = (term119 A B x P f).
Proof. exact (MK_COMB (@lem3587272) (@lem3587266 A B x P f)). Qed.
Lemma lem3587274 {A B : Type'} (f : A -> B) (P : B -> Prop) (x : B) : (term120 A B f P x) = (term120 A B f P x).
Proof. exact (MK_COMB (@lem3587273 A B x P f) (@lem3587267 B P x)). Qed.
Lemma lem3587275 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3587276 {A B : Type'} (f : A -> B) (P : B -> Prop) (x : B) : (term121 A B f P x) = (term121 A B f P x).
Proof. exact (MK_COMB (@lem3587275) (@lem3587274 A B f P x)). Qed.
Lemma lem3587277 {A B : Type'} (f : A -> B) (P : B -> Prop) (x : B) : (term122 A B f P x) = (term123 A B f P x).
Proof. exact (MK_COMB (@lem3587276 A B f P x) (@lem3587271 A B f P x)). Qed.
Lemma lem3587278 {A B : Type'} (f : A -> B) (P : B -> Prop) (x : B) : (term78 A B f P x) = (term122 A B f P x).
Proof. exact (@lem17646 (term45 A B x P f) (P x)). Qed.
Lemma lem3587279 {A B : Type'} (f : A -> B) (P : B -> Prop) (x : B) : (term78 A B f P x) = (term123 A B f P x).
Proof. exact (TRANS (@lem3587278 A B f P x) (@lem3587277 A B f P x)). Qed.
Lemma lem3587378 {A : Type'} (P : A -> Prop) (Q : Prop) : (term124 A P Q) = (term125 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3587379 {A : Type'} (P : A -> Prop) (Q : Prop) : (term124 A P Q) = (term125 A P Q).
Proof. exact (@lem3587378 A P Q). Qed.
Lemma lem3587380 {A B : Type'} (f : A -> B) (P : B -> Prop) (x : B) : (term126 A B f P x) = (term127 A B f P x).
Proof. exact (@lem3587379 A (term44 A B x P f) (term114 B P x)). Qed.
Lemma lem3587381 {A B : Type'} (x : B) (P : B -> Prop) (f : A -> B) (x' : A) : (term109 A B x P f x') = (term42 A B x P f x').
Proof. exact (eq_refl (term109 A B x P f x')). Qed.
Lemma lem3587382 {A B : Type'} (x : B) (P : B -> Prop) (f : A -> B) : (term128 A B x P f) = (term44 A B x P f).
Proof. exact (fun_ext (fun x' : A => @lem3587381 A B x P f x')). Qed.
Lemma lem3587383 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3587384 {A B : Type'} (x : B) (P : B -> Prop) (f : A -> B) : (term129 A B x P f) = (term45 A B x P f).
Proof. exact (MK_COMB (@lem3587383 A) (@lem3587382 A B x P f)). Qed.
Lemma lem3587385 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3587386 {A B : Type'} (x : B) (P : B -> Prop) (f : A -> B) : (term130 A B x P f) = (term119 A B x P f).
Proof. exact (MK_COMB (@lem3587385) (@lem3587384 A B x P f)). Qed.
Lemma lem3587387 {B : Type'} (P : B -> Prop) (x : B) : (term114 B P x) = (term114 B P x).
Proof. exact (eq_refl (term114 B P x)). Qed.
Lemma lem3587388 {A B : Type'} (f : A -> B) (P : B -> Prop) (x : B) : (term126 A B f P x) = (term120 A B f P x).
Proof. exact (MK_COMB (@lem3587386 A B x P f) (@lem3587387 B P x)). Qed.
Lemma lem3587389 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3587390 {A B : Type'} (f : A -> B) (P : B -> Prop) (x : B) : (term131 A B f P x) = (term132 A B f P x).
Proof. exact (MK_COMB (@lem3587389) (@lem3587388 A B f P x)). Qed.
Lemma lem3587391 {A B : Type'} (x : B) (P : B -> Prop) (f : A -> B) (x' : A) : (term109 A B x P f x') = (term42 A B x P f x').
Proof. exact (eq_refl (term109 A B x P f x')). Qed.
Lemma lem3587392 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3587393 {A B : Type'} (x : B) (P : B -> Prop) (f : A -> B) (x' : A) : (term133 A B x P f x') = (term134 A B x P f x').
Proof. exact (MK_COMB (@lem3587392) (@lem3587391 A B x P f x')). Qed.
Lemma lem3587394 {B : Type'} (P : B -> Prop) (x : B) : (term114 B P x) = (term114 B P x).
Proof. exact (eq_refl (term114 B P x)). Qed.
Lemma lem3587395 {A B : Type'} (f : A -> B) (x : A) (P : B -> Prop) (x' : B) : (term135 A B f x P x') = (term136 A B f x P x').
Proof. exact (MK_COMB (@lem3587393 A B x' P f x) (@lem3587394 B P x')). Qed.
Lemma lem3587396 {A B : Type'} (f : A -> B) (P : B -> Prop) (x : B) : (term137 A B f P x) = (term138 A B f P x).
Proof. exact (fun_ext (fun x' : A => @lem3587395 A B f x' P x)). Qed.
Lemma lem3587397 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3587398 {A B : Type'} (f : A -> B) (P : B -> Prop) (x : B) : (term127 A B f P x) = (term139 A B f P x).
Proof. exact (MK_COMB (@lem3587397 A) (@lem3587396 A B f P x)). Qed.
Lemma lem3587399 {A B : Type'} (f : A -> B) (P : B -> Prop) (x : B) : ((term126 A B f P x) = (term127 A B f P x)) = ((term120 A B f P x) = (term139 A B f P x)).
Proof. exact (MK_COMB (@lem3587390 A B f P x) (@lem3587398 A B f P x)). Qed.
Lemma lem3587400 {A B : Type'} (f : A -> B) (P : B -> Prop) (x : B) : (term120 A B f P x) = (term139 A B f P x).
Proof. exact (EQ_MP (@lem3587399 A B f P x) (@lem3587380 A B f P x)). Qed.
Lemma lem3587401 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3587402 {A B : Type'} (f : A -> B) (P : B -> Prop) (x : B) : (term121 A B f P x) = (term140 A B f P x).
Proof. exact (MK_COMB (@lem3587401) (@lem3587400 A B f P x)). Qed.
Lemma lem3587403 {A B : Type'} (f : A -> B) (P : B -> Prop) (x : B) : (term118 A B f P x) = (term118 A B f P x).
Proof. exact (eq_refl (term118 A B f P x)). Qed.
Lemma lem3587404 {A B : Type'} (f : A -> B) (P : B -> Prop) (x : B) : (term123 A B f P x) = (term141 A B f P x).
Proof. exact (MK_COMB (@lem3587402 A B f P x) (@lem3587403 A B f P x)). Qed.
Lemma lem3587406 {A : Type'} (P : A -> Prop) (Q : Prop) : (term142 A P Q) = (term143 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3587407 {A : Type'} (P : A -> Prop) (Q : Prop) : (term142 A P Q) = (term143 A P Q).
Proof. exact (@lem3587406 A P Q). Qed.
Lemma lem3587408 {A B : Type'} (f : A -> B) (P : B -> Prop) (x : B) : (term144 A B f P x) = (term145 A B f P x).
Proof. exact (@lem3587407 A (term138 A B f P x) (term118 A B f P x)). Qed.
Lemma lem3587409 {A B : Type'} (f : A -> B) (x : A) (P : B -> Prop) (x' : B) : (term146 A B f P x' x) = (term136 A B f x P x').
Proof. exact (eq_refl (term146 A B f P x' x)). Qed.
Lemma lem3587410 {A B : Type'} (f : A -> B) (P : B -> Prop) (x : B) : (term147 A B f P x) = (term138 A B f P x).
Proof. exact (fun_ext (fun x' : A => @lem3587409 A B f x' P x)). Qed.
Lemma lem3587411 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3587412 {A B : Type'} (f : A -> B) (P : B -> Prop) (x : B) : (term148 A B f P x) = (term139 A B f P x).
Proof. exact (MK_COMB (@lem3587411 A) (@lem3587410 A B f P x)). Qed.
Lemma lem3587413 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3587414 {A B : Type'} (f : A -> B) (P : B -> Prop) (x : B) : (term149 A B f P x) = (term140 A B f P x).
Proof. exact (MK_COMB (@lem3587413) (@lem3587412 A B f P x)). Qed.
Lemma lem3587415 {A B : Type'} (f : A -> B) (P : B -> Prop) (x : B) : (term118 A B f P x) = (term118 A B f P x).
Proof. exact (eq_refl (term118 A B f P x)). Qed.
Lemma lem3587416 {A B : Type'} (f : A -> B) (P : B -> Prop) (x : B) : (term144 A B f P x) = (term141 A B f P x).
Proof. exact (MK_COMB (@lem3587414 A B f P x) (@lem3587415 A B f P x)). Qed.
Lemma lem3587417 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3587418 {A B : Type'} (f : A -> B) (P : B -> Prop) (x : B) : (term150 A B f P x) = (term151 A B f P x).
Proof. exact (MK_COMB (@lem3587417) (@lem3587416 A B f P x)). Qed.
Lemma lem3587419 {A B : Type'} (f : A -> B) (x : A) (P : B -> Prop) (x' : B) : (term146 A B f P x' x) = (term136 A B f x P x').
Proof. exact (eq_refl (term146 A B f P x' x)). Qed.
Lemma lem3587420 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3587421 {A B : Type'} (f : A -> B) (x : A) (P : B -> Prop) (x' : B) : (term152 A B f P x' x) = (term153 A B f x P x').
Proof. exact (MK_COMB (@lem3587420) (@lem3587419 A B f x P x')). Qed.
Lemma lem3587422 {A B : Type'} (f : A -> B) (P : B -> Prop) (x : B) : (term118 A B f P x) = (term118 A B f P x).
Proof. exact (eq_refl (term118 A B f P x)). Qed.
Lemma lem3587423 {A B : Type'} (x : A) (f : A -> B) (P : B -> Prop) (x' : B) : (term154 A B x f P x') = (term155 A B x f P x').
Proof. exact (MK_COMB (@lem3587421 A B f x P x') (@lem3587422 A B f P x')). Qed.
Lemma lem3587424 {A B : Type'} (f : A -> B) (P : B -> Prop) (x : B) : (term156 A B f P x) = (term157 A B f P x).
Proof. exact (fun_ext (fun x' : A => @lem3587423 A B x' f P x)). Qed.
Lemma lem3587425 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3587426 {A B : Type'} (f : A -> B) (P : B -> Prop) (x : B) : (term145 A B f P x) = (term158 A B f P x).
Proof. exact (MK_COMB (@lem3587425 A) (@lem3587424 A B f P x)). Qed.
Lemma lem3587427 {A B : Type'} (f : A -> B) (P : B -> Prop) (x : B) : ((term144 A B f P x) = (term145 A B f P x)) = ((term141 A B f P x) = (term158 A B f P x)).
Proof. exact (MK_COMB (@lem3587418 A B f P x) (@lem3587426 A B f P x)). Qed.
Lemma lem3587428 {A B : Type'} (f : A -> B) (P : B -> Prop) (x : B) : (term141 A B f P x) = (term158 A B f P x).
Proof. exact (EQ_MP (@lem3587427 A B f P x) (@lem3587408 A B f P x)). Qed.
Lemma lem3587430 {A B : Type'} (f : A -> B) (P : B -> Prop) (x : B) : (term123 A B f P x) = (term158 A B f P x).
Proof. exact (TRANS (@lem3587404 A B f P x) (@lem3587428 A B f P x)). Qed.
Lemma lem3587431 {A B : Type'} (f : A -> B) (P : B -> Prop) (x : B) : (term78 A B f P x) = (term158 A B f P x).
Proof. exact (TRANS (@lem3587279 A B f P x) (@lem3587430 A B f P x)). Qed.
Lemma lem3587432 {A B : Type'} (f : A -> B) (P : B -> Prop) (x : B) (h1 : term78 A B f P x) : term158 A B f P x.
Proof. exact (EQ_MP (@lem3587431 A B f P x) (@lem3587192 A B f P x h1)). Qed.
Lemma lem3587433 {A B : Type'} (x' : A) (f : A -> B) (P : B -> Prop) (x : B) (h1 : term155 A B x' f P x) : term155 A B x' f P x.
Proof. exact (h1). Qed.
Lemma lem3587434 {A B : Type'} (f : A -> B) (x'' : B -> A) (h1 : term99 A B f x'') : term99 A B f x''.
Proof. exact (h1). Qed.
Lemma lem3587437 {B : Type'} (P : B -> Prop) (x : B) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem3587456 {A B : Type'} (x : B) (P : B -> Prop) (f : A -> B) (x' : A) : (term104 A B x P f x') = (term104 A B x P f x').
Proof. exact (eq_refl (term104 A B x P f x')). Qed.
Lemma lem3587457 {A B : Type'} (x : B) (P : B -> Prop) (f : A -> B) : (term112 A B x P f) = (term112 A B x P f).
Proof. exact (fun_ext (fun x' : A => @lem3587456 A B x P f x')). Qed.
Lemma lem3587458 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3587459 {A B : Type'} (x : B) (P : B -> Prop) (f : A -> B) : (term113 A B x P f) = (term113 A B x P f).
Proof. exact (MK_COMB (@lem3587458 A) (@lem3587457 A B x P f)). Qed.
Lemma lem3587460 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3587461 {A B : Type'} (x : B) (P : B -> Prop) (f : A -> B) : (term116 A B x P f) = (term116 A B x P f).
Proof. exact (MK_COMB (@lem3587460) (@lem3587459 A B x P f)). Qed.
Lemma lem3587462 {A B : Type'} (f : A -> B) (P : B -> Prop) (x : B) : (term118 A B f P x) = (term118 A B f P x).
Proof. exact (MK_COMB (@lem3587461 A B x P f) (@lem3587437 B P x)). Qed.
Lemma lem3587487 {A B : Type'} (f : A -> B) (x' : A) (P : B -> Prop) (x : B) : (term153 A B f x' P x) = (term153 A B f x' P x).
Proof. exact (eq_refl (term153 A B f x' P x)). Qed.
Lemma lem3587488 {A B : Type'} (x' : A) (f : A -> B) (P : B -> Prop) (x : B) : (term155 A B x' f P x) = (term155 A B x' f P x).
Proof. exact (MK_COMB (@lem3587487 A B f x' P x) (@lem3587462 A B f P x)). Qed.
Lemma lem3587489 {A B : Type'} (x' : A) (f : A -> B) (P : B -> Prop) (x : B) (h1 : term155 A B x' f P x) : term155 A B x' f P x.
Proof. exact (EQ_MP (@lem3587488 A B x' f P x) (@lem3587433 A B x' f P x h1)). Qed.
Lemma lem3587498 {A B : Type'} (f : A -> B) (x'' : B -> A) (y : B) : ((term95 A B f x'' y) = y) = ((term95 A B f x'' y) = y).
Proof. exact (eq_refl ((term95 A B f x'' y) = y)). Qed.
Lemma lem3587499 {A B : Type'} (f : A -> B) (x'' : B -> A) : (term97 A B f x'') = (term97 A B f x'').
Proof. exact (fun_ext (fun y : B => @lem3587498 A B f x'' y)). Qed.
Lemma lem3587500 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3587501 {A B : Type'} (f : A -> B) (x'' : B -> A) : (term99 A B f x'') = (term99 A B f x'').
Proof. exact (MK_COMB (@lem3587500 B) (@lem3587499 A B f x'')). Qed.
Lemma lem3587502 {A B : Type'} (f : A -> B) (x'' : B -> A) (h1 : term99 A B f x'') : term99 A B f x''.
Proof. exact (EQ_MP (@lem3587501 A B f x'') (@lem3587434 A B f x'' h1)). Qed.
Lemma lem3587503 {A B : Type'} (f : A -> B) (x' : A) (P : B -> Prop) (x : B) (h1 : term136 A B f x' P x) : term136 A B f x' P x.
Proof. exact (h1). Qed.
Lemma lem3587504 {A B : Type'} (f : A -> B) (P : B -> Prop) (x : B) (h1 : term118 A B f P x) : term118 A B f P x.
Proof. exact (h1). Qed.
Lemma lem3587506 {A B : Type'} (f : A -> B) (x' : A) (P : B -> Prop) (x : B) (h1 : term136 A B f x' P x) : term42 A B x P f x'.
Proof. exact (proj1 (@lem3587503 A B f x' P x h1)). Qed.
Lemma lem3587510 {A B : Type'} (f : A -> B) (P : B -> Prop) (x : B) (h1 : term118 A B f P x) : term113 A B x P f.
Proof. exact (proj1 (@lem3587504 A B f P x h1)). Qed.
Lemma lem3587531 {A B : Type'} (f : A -> B) (x'' : B -> A) (y : B) : ((term95 A B f x'' y) = y) = ((term95 A B f x'' y) = y).
Proof. exact (eq_refl ((term95 A B f x'' y) = y)). Qed.
Lemma lem3587532 {A B : Type'} (f : A -> B) (x'' : B -> A) : (term97 A B f x'') = (term97 A B f x'').
Proof. exact (fun_ext (fun y : B => @lem3587531 A B f x'' y)). Qed.
Lemma lem3587533 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3587535 {A B : Type'} (f : A -> B) (x'' : B -> A) : (term99 A B f x'') = (term99 A B f x'').
Proof. exact (MK_COMB (@lem3587533 B) (@lem3587532 A B f x'')). Qed.
Lemma lem3587536 {A B : Type'} (f : A -> B) (x'' : B -> A) (h1 : term99 A B f x'') : term99 A B f x''.
Proof. exact (EQ_MP (@lem3587535 A B f x'') (@lem3587502 A B f x'' h1)). Qed.
Lemma lem3587544 {A B : Type'} (x : B) (P : B -> Prop) (f : A -> B) (x' : A) : (term104 A B x P f x') = (term104 A B x P f x').
Proof. exact (eq_refl (term104 A B x P f x')). Qed.
Lemma lem3587545 {A B : Type'} (x : B) (P : B -> Prop) (f : A -> B) : (term112 A B x P f) = (term112 A B x P f).
Proof. exact (fun_ext (fun x' : A => @lem3587544 A B x P f x')). Qed.
Lemma lem3587546 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3587548 {A B : Type'} (x : B) (P : B -> Prop) (f : A -> B) : (term113 A B x P f) = (term113 A B x P f).
Proof. exact (MK_COMB (@lem3587546 A) (@lem3587545 A B x P f)). Qed.
Lemma lem3587549 {A B : Type'} (f : A -> B) (P : B -> Prop) (x : B) (h1 : term118 A B f P x) : term113 A B x P f.
Proof. exact (EQ_MP (@lem3587548 A B x P f) (@lem3587510 A B f P x h1)). Qed.
Lemma lem3587557 {A B : Type'} (_38749 : B) (f : A -> B) (x'' : B -> A) (h1 : term99 A B f x'') : term159 A B f x'' _38749.
Proof. exact (@lem3587536 A B f x'' h1 _38749). Qed.
Lemma lem3587558 {A B : Type'} (f : A -> B) (x'' : B -> A) (_38749 : B) : (term159 A B f x'' _38749) = ((term95 A B f x'' _38749) = _38749).
Proof. exact (eq_refl (term159 A B f x'' _38749)). Qed.
Lemma lem3587560 {A B : Type'} (_38750 : A) (f : A -> B) (P : B -> Prop) (x : B) (h1 : term118 A B f P x) : term160 A B x P f _38750.
Proof. exact (@lem3587549 A B f P x h1 _38750). Qed.
Lemma lem3587561 {A B : Type'} (x : B) (P : B -> Prop) (f : A -> B) (_38750 : A) : (term160 A B x P f _38750) = (term104 A B x P f _38750).
Proof. exact (eq_refl (term160 A B x P f _38750)). Qed.
Lemma lem3587566 {A B : Type'} (f : A -> B) (x' : A) (P : B -> Prop) (x : B) (h1 : term136 A B f x' P x) : term114 B P x.
Proof. exact (proj2 (@lem3587503 A B f x' P x h1)). Qed.
Lemma lem3587568 {A B : Type'} (f : A -> B) (x' : A) (P : B -> Prop) (x : B) (h1 : term136 A B f x' P x) : x = (f x').
Proof. exact (proj1 (@lem3587506 A B f x' P x h1)). Qed.
Lemma lem3587578 {A B : Type'} (_38750 : A) (f : A -> B) (P : B -> Prop) (x : B) (h1 : term118 A B f P x) : term104 A B x P f _38750.
Proof. exact (EQ_MP (@lem3587561 A B x P f _38750) (@lem3587560 A B _38750 f P x h1)). Qed.
Lemma lem3587609 {B : Type'} (P : B -> Prop) : (term161 B P) = (term161 B P).
Proof. exact (eq_refl (term161 B P)). Qed.
Lemma lem3587610 {A B : Type'} (f : A -> B) (x' : A) (P : B -> Prop) (x : B) (h1 : term136 A B f x' P x) : (term162 B P x) = (term163 A B P f x').
Proof. exact (MK_COMB (@lem3587609 B P) (@lem3587568 A B f x' P x h1)). Qed.
Lemma lem3587611 {A B : Type'} (P : B -> Prop) (f : A -> B) (x' : A) : (term163 A B P f x') = (term164 A B P f x').
Proof. exact (eq_refl (term163 A B P f x')). Qed.
Lemma lem3587612 {B : Type'} (P : B -> Prop) (x : B) : (term165 B P x) = (term165 B P x).
Proof. exact (eq_refl (term165 B P x)). Qed.
Lemma lem3587613 {A B : Type'} (x : B) (P : B -> Prop) (f : A -> B) (x' : A) : ((term162 B P x) = (term163 A B P f x')) = ((term162 B P x) = (term164 A B P f x')).
Proof. exact (MK_COMB (@lem3587612 B P x) (@lem3587611 A B P f x')). Qed.
Lemma lem3587614 {B : Type'} (P : B -> Prop) (x : B) : (term162 B P x) = (term114 B P x).
Proof. exact (eq_refl (term162 B P x)). Qed.
Lemma lem3587615 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3587616 {B : Type'} (P : B -> Prop) (x : B) : (term165 B P x) = (term166 B P x).
Proof. exact (MK_COMB (@lem3587615) (@lem3587614 B P x)). Qed.
Lemma lem3587617 {A B : Type'} (P : B -> Prop) (f : A -> B) (x' : A) : (term164 A B P f x') = (term164 A B P f x').
Proof. exact (eq_refl (term164 A B P f x')). Qed.
Lemma lem3587618 {A B : Type'} (x : B) (P : B -> Prop) (f : A -> B) (x' : A) : ((term162 B P x) = (term164 A B P f x')) = ((term114 B P x) = (term164 A B P f x')).
Proof. exact (MK_COMB (@lem3587616 B P x) (@lem3587617 A B P f x')). Qed.
Lemma lem3587619 {A B : Type'} (x : B) (P : B -> Prop) (f : A -> B) (x' : A) : ((term162 B P x) = (term163 A B P f x')) = ((term114 B P x) = (term164 A B P f x')).
Proof. exact (TRANS (@lem3587613 A B x P f x') (@lem3587618 A B x P f x')). Qed.
Lemma lem3587620 {A B : Type'} (f : A -> B) (x' : A) (P : B -> Prop) (x : B) (h1 : term136 A B f x' P x) : (term114 B P x) = (term164 A B P f x').
Proof. exact (EQ_MP (@lem3587619 A B x P f x') (@lem3587610 A B f x' P x h1)). Qed.
Lemma lem3587621 {A B : Type'} (f : A -> B) (x' : A) (P : B -> Prop) (x : B) (h1 : term136 A B f x' P x) : term164 A B P f x'.
Proof. exact (EQ_MP (@lem3587620 A B f x' P x h1) (@lem3587566 A B f x' P x h1)). Qed.
Lemma lem3587669 {A B : Type'} (f : A -> B) (x' : A) (P : B -> Prop) (x : B) (h1 : term136 A B f x' P x) : term25 A B P f x'.
Proof. exact (proj2 (@lem3587506 A B f x' P x h1)). Qed.
Lemma lem3587670 {A B : Type'} (f : A -> B) (x' : A) (P : B -> Prop) (x : B) (h1 : term136 A B f x' P x) : term167 A B P f x'.
Proof. exact (fun h0 : term164 A B P f x' => @lem3587669 A B f x' P x h1). Qed.
Lemma lem3587672 (p : Prop) : (term168 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3587673 {A B : Type'} (P : B -> Prop) (f : A -> B) (x' : A) : (term167 A B P f x') = (term25 A B P f x').
Proof. exact (@lem3587672 (term25 A B P f x')). Qed.
Lemma lem3587674 {A B : Type'} (f : A -> B) (x' : A) (P : B -> Prop) (x : B) (h1 : term136 A B f x' P x) : term25 A B P f x'.
Proof. exact (EQ_MP (@lem3587673 A B P f x') (@lem3587670 A B f x' P x h1)). Qed.
Lemma lem3587677 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3587679 {A B : Type'} (P : B -> Prop) (f : A -> B) (x' : A) : (term164 A B P f x') = (term169 A B P f x').
Proof. exact (@lem3587677 (term25 A B P f x')). Qed.
Lemma lem3587682 {A B : Type'} (f : A -> B) (x' : A) (P : B -> Prop) (x : B) (h1 : term136 A B f x' P x) : term169 A B P f x'.
Proof. exact (EQ_MP (@lem3587679 A B P f x') (@lem3587621 A B f x' P x h1)). Qed.
Lemma lem3587685 {A B : Type'} (f : A -> B) (x' : A) (P : B -> Prop) (x : B) (h1 : term136 A B f x' P x) : False.
Proof. exact (@lem3587682 A B f x' P x h1 (@lem3587674 A B f x' P x h1)). Qed.
Lemma lem3587686 {A B : Type'} (f : A -> B) (x' : A) (P : B -> Prop) (x : B) (h1 : term136 A B f x' P x) : term170.
Proof. exact (fun h0 : ~ False => @lem3587685 A B f x' P x h1). Qed.
Lemma lem3587688 (p : Prop) : (term168 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3587689 : term170 = False.
Proof. exact (@lem3587688 False). Qed.
Lemma lem3587691 {B : Type'} (P : B -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem3587692 {B : Type'} (_38765 : B) (_38766 : B) (h1 : _38765 = _38766) : _38765 = _38766.
Proof. exact (h1). Qed.
Lemma lem3587693 {B : Type'} (P : B -> Prop) (_38765 : B) (_38766 : B) (h1 : _38765 = _38766) : (P _38765) = (P _38766).
Proof. exact (MK_COMB (@lem3587691 B P) (@lem3587692 B _38765 _38766 h1)). Qed.
Lemma lem3587695 (b : Prop) (a : Prop) : term171 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem3587696 {B : Type'} (_38766 : B) (P : B -> Prop) (_38765 : B) : term172 B _38766 P _38765.
Proof. exact (@lem3587695 (P _38766) (P _38765)). Qed.
Lemma lem3587697 {B : Type'} (P : B -> Prop) (_38765 : B) (_38766 : B) (h1 : _38765 = _38766) : term173 B _38766 P _38765.
Proof. exact (@lem3587696 B _38766 P _38765 (@lem3587693 B P _38765 _38766 h1)). Qed.
Lemma lem3587698 {B : Type'} (_38766 : B) (P : B -> Prop) (_38765 : B) : term174 B _38766 P _38765.
Proof. exact (fun h0 : _38765 = _38766 => @lem3587697 B P _38765 _38766 h0). Qed.
Lemma lem3587700 (a : Prop) (b : Prop) : (a -> b) = (term175 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem3587701 {B : Type'} (_38766 : B) (P : B -> Prop) (_38765 : B) : (term174 B _38766 P _38765) = (term176 B _38766 P _38765).
Proof. exact (@lem3587700 (_38765 = _38766) (term173 B _38766 P _38765)). Qed.
Lemma lem3587702 {B : Type'} (_38766 : B) (P : B -> Prop) (_38765 : B) : term176 B _38766 P _38765.
Proof. exact (EQ_MP (@lem3587701 B _38766 P _38765) (@lem3587698 B _38766 P _38765)). Qed.
Lemma lem3587720 {B : Type'} (x : B) (y : B) (z : B) : term177 B x y z.
Proof. exact (@lem21385 B x y z). Qed.
Lemma lem3587724 {A B : Type'} (_38749 : B) (f : A -> B) (x'' : B -> A) (h1 : term99 A B f x'') : (term95 A B f x'' _38749) = _38749.
Proof. exact (EQ_MP (@lem3587558 A B f x'' _38749) (@lem3587557 A B _38749 f x'' h1)). Qed.
Lemma lem3587725 {A B : Type'} (_38749 : B) (f : A -> B) (x'' : B -> A) (h1 : term99 A B f x'') : (term95 A B f x'' _38749) = _38749.
Proof. exact (@lem3587724 A B _38749 f x'' h1). Qed.
Lemma lem3587726 {A B : Type'} (x : B) (f : A -> B) (x'' : B -> A) (h1 : term99 A B f x'') : (term95 A B f x'' x) = x.
Proof. exact (@lem3587725 A B x f x'' h1). Qed.
Lemma lem3587727 {A B : Type'} (x : B) (f : A -> B) (x'' : B -> A) (h1 : term99 A B f x'') : term178 A B f x'' x.
Proof. exact (fun h0 : term179 A B f x'' x => @lem3587726 A B x f x'' h1). Qed.
Lemma lem3587729 (p : Prop) : (term168 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3587730 {A B : Type'} (f : A -> B) (x'' : B -> A) (x : B) : (term178 A B f x'' x) = ((term95 A B f x'' x) = x).
Proof. exact (@lem3587729 ((term95 A B f x'' x) = x)). Qed.
Lemma lem3587731 {A B : Type'} (x : B) (f : A -> B) (x'' : B -> A) (h1 : term99 A B f x'') : (term95 A B f x'' x) = x.
Proof. exact (EQ_MP (@lem3587730 A B f x'' x) (@lem3587727 A B x f x'' h1)). Qed.
Lemma lem3587733 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem3587734 {B : Type'} (x : B) : x = x.
Proof. exact (@lem3587733 B x). Qed.
Lemma lem3587735 {A B : Type'} (f : A -> B) (x'' : B -> A) (x : B) : (term95 A B f x'' x) = (term95 A B f x'' x).
Proof. exact (@lem3587734 B (term95 A B f x'' x)). Qed.
Lemma lem3587736 {A B : Type'} (f : A -> B) (x'' : B -> A) (x : B) : term180 A B f x'' x.
Proof. exact (fun h0 : term181 A B f x'' x => @lem3587735 A B f x'' x). Qed.
Lemma lem3587738 (p : Prop) : (term168 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3587739 {A B : Type'} (f : A -> B) (x'' : B -> A) (x : B) : (term180 A B f x'' x) = ((term95 A B f x'' x) = (term95 A B f x'' x)).
Proof. exact (@lem3587738 ((term95 A B f x'' x) = (term95 A B f x'' x))). Qed.
Lemma lem3587740 {A B : Type'} (f : A -> B) (x'' : B -> A) (x : B) : (term95 A B f x'' x) = (term95 A B f x'' x).
Proof. exact (EQ_MP (@lem3587739 A B f x'' x) (@lem3587736 A B f x'' x)). Qed.
Lemma lem3587758 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3587759 {B : Type'} (y : B) (x : B) (z : B) : (term182 B x y z) = (term183 B y x z).
Proof. exact (@lem3587758 (y = z) (term184 B x z)). Qed.
Lemma lem3587769 {B : Type'} (x : B) (y : B) : (term185 B x y) = (term185 B x y).
Proof. exact (eq_refl (term185 B x y)). Qed.
Lemma lem3587770 {B : Type'} (y : B) (x : B) (z : B) : (term177 B x y z) = (term186 B y x z).
Proof. exact (MK_COMB (@lem3587769 B x y) (@lem3587759 B y x z)). Qed.
Lemma lem3587774 (q : Prop) (p : Prop) (r : Prop) : (term187 p q r) = (term187 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3587775 {B : Type'} (y : B) (x : B) (z : B) : (term186 B y x z) = (term188 B y x z).
Proof. exact (@lem3587774 (y = z) (term184 B x y) (term184 B x z)). Qed.
Lemma lem3587797 {B : Type'} (y : B) (x : B) (z : B) : (term177 B x y z) = (term188 B y x z).
Proof. exact (TRANS (@lem3587770 B y x z) (@lem3587775 B y x z)). Qed.
Lemma lem3587798 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3587799 {B : Type'} (y : B) (x : B) (z : B) : (term189 B x y z) = (term190 B y x z).
Proof. exact (MK_COMB (@lem3587798) (@lem3587797 B y x z)). Qed.
Lemma lem3587821 {B : Type'} (y : B) (x : B) (z : B) : (term188 B y x z) = (term188 B y x z).
Proof. exact (eq_refl (term188 B y x z)). Qed.
Lemma lem3587822 {B : Type'} (y : B) (x : B) (z : B) : ((term177 B x y z) = (term188 B y x z)) = ((term188 B y x z) = (term188 B y x z)).
Proof. exact (MK_COMB (@lem3587799 B y x z) (@lem3587821 B y x z)). Qed.
Lemma lem3587824 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3587825 (x : Prop) : (x = x) = True.
Proof. exact (@lem3587824 Prop x). Qed.
Lemma lem3587826 {B : Type'} (y : B) (x : B) (z : B) : ((term188 B y x z) = (term188 B y x z)) = True.
Proof. exact (@lem3587825 (term188 B y x z)). Qed.
Lemma lem3587827 {B : Type'} (y : B) (x : B) (z : B) : ((term177 B x y z) = (term188 B y x z)) = True.
Proof. exact (TRANS (@lem3587822 B y x z) (@lem3587826 B y x z)). Qed.
Lemma lem3587828 {B : Type'} (y : B) (x : B) (z : B) : True = ((term177 B x y z) = (term188 B y x z)).
Proof. exact (SYM (@lem3587827 B y x z)). Qed.
Lemma lem3587829 {B : Type'} (y : B) (x : B) (z : B) : (term177 B x y z) = (term188 B y x z).
Proof. exact (EQ_MP (@lem3587828 B y x z) (@lem0)). Qed.
Lemma lem3587830 {B : Type'} (y : B) (x : B) (z : B) : term188 B y x z.
Proof. exact (EQ_MP (@lem3587829 B y x z) (@lem3587720 B x y z)). Qed.
Lemma lem3587832 (b : Prop) (a : Prop) : (a \/ b) = (term191 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3587833 {B : Type'} (x : B) (y : B) (z : B) : (term188 B y x z) = (term192 B x y z).
Proof. exact (@lem3587832 (term193 B y x z) (y = z)). Qed.
Lemma lem3587835 (a : Prop) (b : Prop) : (term194 a b) = (term195 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3587836 {B : Type'} (y : B) (x : B) (z : B) : (term196 B y x z) = (term197 B y x z).
Proof. exact (@lem3587835 (term184 B x y) (term184 B x z)). Qed.
Lemma lem3587838 (a : Prop) : (term68 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3587839 {B : Type'} (x : B) (y : B) : (term198 B x y) = (x = y).
Proof. exact (@lem3587838 (x = y)). Qed.
Lemma lem3587840 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3587841 {B : Type'} (x : B) (y : B) : (term199 B x y) = (term200 B x y).
Proof. exact (MK_COMB (@lem3587840) (@lem3587839 B x y)). Qed.
Lemma lem3587843 (a : Prop) : (term68 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3587844 {B : Type'} (x : B) (z : B) : (term198 B x z) = (x = z).
Proof. exact (@lem3587843 (x = z)). Qed.
Lemma lem3587845 {B : Type'} (y : B) (x : B) (z : B) : (term197 B y x z) = (term201 B y x z).
Proof. exact (MK_COMB (@lem3587841 B x y) (@lem3587844 B x z)). Qed.
Lemma lem3587846 {B : Type'} (y : B) (x : B) (z : B) : (term196 B y x z) = (term201 B y x z).
Proof. exact (TRANS (@lem3587836 B y x z) (@lem3587845 B y x z)). Qed.
Lemma lem3587847 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3587848 {B : Type'} (y : B) (x : B) (z : B) : (term202 B y x z) = (term203 B y x z).
Proof. exact (MK_COMB (@lem3587847) (@lem3587846 B y x z)). Qed.
Lemma lem3587849 {B : Type'} (y : B) (z : B) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem3587850 {B : Type'} (x : B) (y : B) (z : B) : (term192 B x y z) = (term204 B x y z).
Proof. exact (MK_COMB (@lem3587848 B y x z) (@lem3587849 B y z)). Qed.
Lemma lem3587851 {B : Type'} (x : B) (y : B) (z : B) : (term188 B y x z) = (term204 B x y z).
Proof. exact (TRANS (@lem3587833 B x y z) (@lem3587850 B x y z)). Qed.
Lemma lem3587853 {A B : Type'} (x : B) (f : A -> B) (x'' : B -> A) (h1 : term99 A B f x'') : term205 A B f x'' x.
Proof. exact (conj (@lem3587731 A B x f x'' h1) (@lem3587740 A B f x'' x)). Qed.
Lemma lem3587855 {B : Type'} (x : B) (y : B) (z : B) : term204 B x y z.
Proof. exact (EQ_MP (@lem3587851 B x y z) (@lem3587830 B y x z)). Qed.
Lemma lem3587856 {B : Type'} (x : B) (y : B) (z : B) : term204 B x y z.
Proof. exact (@lem3587855 B x y z). Qed.
Lemma lem3587857 {A B : Type'} (f : A -> B) (x'' : B -> A) (x : B) : term206 A B f x'' x.
Proof. exact (@lem3587856 B (term95 A B f x'' x) x (term95 A B f x'' x)). Qed.
Lemma lem3587860 {A B : Type'} (x : B) (f : A -> B) (x'' : B -> A) (h1 : term99 A B f x'') : x = (term95 A B f x'' x).
Proof. exact (@lem3587857 A B f x'' x (@lem3587853 A B x f x'' h1)). Qed.
Lemma lem3587861 {A B : Type'} (x : B) (f : A -> B) (x'' : B -> A) (h1 : term99 A B f x'') : x = (term95 A B f x'' x).
Proof. exact (@lem3587860 A B x f x'' h1). Qed.
Lemma lem3587862 {A B : Type'} (x : B) (f : A -> B) (x'' : B -> A) (h1 : term99 A B f x'') : term207 A B f x'' x.
Proof. exact (fun h0 : term208 A B f x'' x => @lem3587861 A B x f x'' h1). Qed.
Lemma lem3587864 (p : Prop) : (term168 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3587865 {A B : Type'} (f : A -> B) (x'' : B -> A) (x : B) : (term207 A B f x'' x) = (x = (term95 A B f x'' x)).
Proof. exact (@lem3587864 (x = (term95 A B f x'' x))). Qed.
Lemma lem3587866 {A B : Type'} (x : B) (f : A -> B) (x'' : B -> A) (h1 : term99 A B f x'') : x = (term95 A B f x'' x).
Proof. exact (EQ_MP (@lem3587865 A B f x'' x) (@lem3587862 A B x f x'' h1)). Qed.
Lemma lem3587868 {A B : Type'} (_38749 : B) (f : A -> B) (x'' : B -> A) (h1 : term99 A B f x'') : (term95 A B f x'' _38749) = _38749.
Proof. exact (EQ_MP (@lem3587558 A B f x'' _38749) (@lem3587557 A B _38749 f x'' h1)). Qed.
Lemma lem3587869 {A B : Type'} (_38749 : B) (f : A -> B) (x'' : B -> A) (h1 : term99 A B f x'') : (term95 A B f x'' _38749) = _38749.
Proof. exact (@lem3587868 A B _38749 f x'' h1). Qed.
Lemma lem3587870 {A B : Type'} (x : B) (f : A -> B) (x'' : B -> A) (h1 : term99 A B f x'') : (term95 A B f x'' x) = x.
Proof. exact (@lem3587869 A B x f x'' h1). Qed.
Lemma lem3587871 {A B : Type'} (x : B) (f : A -> B) (x'' : B -> A) (h1 : term99 A B f x'') : term178 A B f x'' x.
Proof. exact (fun h0 : term179 A B f x'' x => @lem3587870 A B x f x'' h1). Qed.
Lemma lem3587873 (p : Prop) : (term168 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3587874 {A B : Type'} (f : A -> B) (x'' : B -> A) (x : B) : (term178 A B f x'' x) = ((term95 A B f x'' x) = x).
Proof. exact (@lem3587873 ((term95 A B f x'' x) = x)). Qed.
Lemma lem3587875 {A B : Type'} (x : B) (f : A -> B) (x'' : B -> A) (h1 : term99 A B f x'') : (term95 A B f x'' x) = x.
Proof. exact (EQ_MP (@lem3587874 A B f x'' x) (@lem3587871 A B x f x'' h1)). Qed.
Lemma lem3587877 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem3587878 {B : Type'} (x : B) : x = x.
Proof. exact (@lem3587877 B x). Qed.
Lemma lem3587879 {A B : Type'} (f : A -> B) (x'' : B -> A) (x : B) : (term95 A B f x'' x) = (term95 A B f x'' x).
Proof. exact (@lem3587878 B (term95 A B f x'' x)). Qed.
Lemma lem3587880 {A B : Type'} (f : A -> B) (x'' : B -> A) (x : B) : term180 A B f x'' x.
Proof. exact (fun h0 : term181 A B f x'' x => @lem3587879 A B f x'' x). Qed.
Lemma lem3587882 (p : Prop) : (term168 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3587883 {A B : Type'} (f : A -> B) (x'' : B -> A) (x : B) : (term180 A B f x'' x) = ((term95 A B f x'' x) = (term95 A B f x'' x)).
Proof. exact (@lem3587882 ((term95 A B f x'' x) = (term95 A B f x'' x))). Qed.
Lemma lem3587884 {A B : Type'} (f : A -> B) (x'' : B -> A) (x : B) : (term95 A B f x'' x) = (term95 A B f x'' x).
Proof. exact (EQ_MP (@lem3587883 A B f x'' x) (@lem3587880 A B f x'' x)). Qed.
Lemma lem3587885 {A B : Type'} (x : B) (f : A -> B) (x'' : B -> A) (h1 : term99 A B f x'') : term205 A B f x'' x.
Proof. exact (conj (@lem3587875 A B x f x'' h1) (@lem3587884 A B f x'' x)). Qed.
Lemma lem3587887 {B : Type'} (x : B) (y : B) (z : B) : term204 B x y z.
Proof. exact (EQ_MP (@lem3587851 B x y z) (@lem3587830 B y x z)). Qed.
Lemma lem3587888 {B : Type'} (x : B) (y : B) (z : B) : term204 B x y z.
Proof. exact (@lem3587887 B x y z). Qed.
Lemma lem3587889 {A B : Type'} (f : A -> B) (x'' : B -> A) (x : B) : term206 A B f x'' x.
Proof. exact (@lem3587888 B (term95 A B f x'' x) x (term95 A B f x'' x)). Qed.
Lemma lem3587892 {A B : Type'} (x : B) (f : A -> B) (x'' : B -> A) (h1 : term99 A B f x'') : x = (term95 A B f x'' x).
Proof. exact (@lem3587889 A B f x'' x (@lem3587885 A B x f x'' h1)). Qed.
Lemma lem3587893 {A B : Type'} (x : B) (f : A -> B) (x'' : B -> A) (h1 : term99 A B f x'') : x = (term95 A B f x'' x).
Proof. exact (@lem3587892 A B x f x'' h1). Qed.
Lemma lem3587894 {A B : Type'} (x : B) (f : A -> B) (x'' : B -> A) (h1 : term99 A B f x'') : term207 A B f x'' x.
Proof. exact (fun h0 : term208 A B f x'' x => @lem3587893 A B x f x'' h1). Qed.
Lemma lem3587896 (p : Prop) : (term168 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3587897 {A B : Type'} (f : A -> B) (x'' : B -> A) (x : B) : (term207 A B f x'' x) = (x = (term95 A B f x'' x)).
Proof. exact (@lem3587896 (x = (term95 A B f x'' x))). Qed.
Lemma lem3587898 {A B : Type'} (x : B) (f : A -> B) (x'' : B -> A) (h1 : term99 A B f x'') : x = (term95 A B f x'' x).
Proof. exact (EQ_MP (@lem3587897 A B f x'' x) (@lem3587894 A B x f x'' h1)). Qed.
Lemma lem3587900 {A B : Type'} (f : A -> B) (P : B -> Prop) (x : B) (h1 : term118 A B f P x) : P x.
Proof. exact (proj2 (@lem3587504 A B f P x h1)). Qed.
Lemma lem3587901 {A B : Type'} (f : A -> B) (P : B -> Prop) (x : B) (h1 : term118 A B f P x) : term209 B P x.
Proof. exact (fun h0 : term114 B P x => @lem3587900 A B f P x h1). Qed.
Lemma lem3587903 (p : Prop) : (term168 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3587904 {B : Type'} (P : B -> Prop) (x : B) : (term209 B P x) = (P x).
Proof. exact (@lem3587903 (P x)). Qed.
Lemma lem3587905 {A B : Type'} (f : A -> B) (P : B -> Prop) (x : B) (h1 : term118 A B f P x) : P x.
Proof. exact (EQ_MP (@lem3587904 B P x) (@lem3587901 A B f P x h1)). Qed.
Lemma lem3587911 (q : Prop) (p : Prop) (r : Prop) : (term187 p q r) = (term187 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3587912 {B : Type'} (_38766 : B) (P : B -> Prop) (_38765 : B) : (term176 B _38766 P _38765) = (term210 B _38766 P _38765).
Proof. exact (@lem3587911 (P _38766) (term184 B _38765 _38766) (term114 B P _38765)). Qed.
Lemma lem3587926 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3587927 {B : Type'} (P : B -> Prop) (_38765 : B) (_38766 : B) : (term211 B _38766 P _38765) = (term212 B P _38765 _38766).
Proof. exact (@lem3587926 (term114 B P _38765) (term184 B _38765 _38766)). Qed.
Lemma lem3587935 {B : Type'} (P : B -> Prop) (_38766 : B) : (term213 B P _38766) = (term213 B P _38766).
Proof. exact (eq_refl (term213 B P _38766)). Qed.
Lemma lem3587936 {B : Type'} (P : B -> Prop) (_38765 : B) (_38766 : B) : (term210 B _38766 P _38765) = (term214 B P _38765 _38766).
Proof. exact (MK_COMB (@lem3587935 B P _38766) (@lem3587927 B P _38765 _38766)). Qed.
Lemma lem3587947 {B : Type'} (P : B -> Prop) (_38765 : B) (_38766 : B) : (term176 B _38766 P _38765) = (term214 B P _38765 _38766).
Proof. exact (TRANS (@lem3587912 B _38766 P _38765) (@lem3587936 B P _38765 _38766)). Qed.
Lemma lem3587948 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3587949 {B : Type'} (P : B -> Prop) (_38765 : B) (_38766 : B) : (term215 B _38766 P _38765) = (term216 B P _38765 _38766).
Proof. exact (MK_COMB (@lem3587948) (@lem3587947 B P _38765 _38766)). Qed.
Lemma lem3587963 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3587964 {B : Type'} (P : B -> Prop) (_38765 : B) (_38766 : B) : (term211 B _38766 P _38765) = (term212 B P _38765 _38766).
Proof. exact (@lem3587963 (term114 B P _38765) (term184 B _38765 _38766)). Qed.
Lemma lem3587972 {B : Type'} (P : B -> Prop) (_38766 : B) : (term213 B P _38766) = (term213 B P _38766).
Proof. exact (eq_refl (term213 B P _38766)). Qed.
Lemma lem3587973 {B : Type'} (P : B -> Prop) (_38765 : B) (_38766 : B) : (term210 B _38766 P _38765) = (term214 B P _38765 _38766).
Proof. exact (MK_COMB (@lem3587972 B P _38766) (@lem3587964 B P _38765 _38766)). Qed.
Lemma lem3587984 {B : Type'} (P : B -> Prop) (_38765 : B) (_38766 : B) : ((term176 B _38766 P _38765) = (term210 B _38766 P _38765)) = ((term214 B P _38765 _38766) = (term214 B P _38765 _38766)).
Proof. exact (MK_COMB (@lem3587949 B P _38765 _38766) (@lem3587973 B P _38765 _38766)). Qed.
Lemma lem3587986 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3587987 (x : Prop) : (x = x) = True.
Proof. exact (@lem3587986 Prop x). Qed.
Lemma lem3587988 {B : Type'} (P : B -> Prop) (_38765 : B) (_38766 : B) : ((term214 B P _38765 _38766) = (term214 B P _38765 _38766)) = True.
Proof. exact (@lem3587987 (term214 B P _38765 _38766)). Qed.
Lemma lem3587989 {B : Type'} (_38766 : B) (P : B -> Prop) (_38765 : B) : ((term176 B _38766 P _38765) = (term210 B _38766 P _38765)) = True.
Proof. exact (TRANS (@lem3587984 B P _38765 _38766) (@lem3587988 B P _38765 _38766)). Qed.
Lemma lem3587990 {B : Type'} (_38766 : B) (P : B -> Prop) (_38765 : B) : True = ((term176 B _38766 P _38765) = (term210 B _38766 P _38765)).
Proof. exact (SYM (@lem3587989 B _38766 P _38765)). Qed.
Lemma lem3587991 {B : Type'} (_38766 : B) (P : B -> Prop) (_38765 : B) : (term176 B _38766 P _38765) = (term210 B _38766 P _38765).
Proof. exact (EQ_MP (@lem3587990 B _38766 P _38765) (@lem0)). Qed.
Lemma lem3587992 {B : Type'} (_38766 : B) (P : B -> Prop) (_38765 : B) : term210 B _38766 P _38765.
Proof. exact (EQ_MP (@lem3587991 B _38766 P _38765) (@lem3587702 B _38766 P _38765)). Qed.
Lemma lem3587994 (b : Prop) (a : Prop) : (a \/ b) = (term191 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3587995 {B : Type'} (_38765 : B) (P : B -> Prop) (_38766 : B) : (term210 B _38766 P _38765) = (term217 B _38765 P _38766).
Proof. exact (@lem3587994 (term211 B _38766 P _38765) (P _38766)). Qed.
Lemma lem3587997 (a : Prop) (b : Prop) : (term194 a b) = (term195 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3587998 {B : Type'} (_38766 : B) (P : B -> Prop) (_38765 : B) : (term218 B _38766 P _38765) = (term219 B _38766 P _38765).
Proof. exact (@lem3587997 (term184 B _38765 _38766) (term114 B P _38765)). Qed.
Lemma lem3588000 (a : Prop) : (term68 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3588001 {B : Type'} (_38765 : B) (_38766 : B) : (term198 B _38765 _38766) = (_38765 = _38766).
Proof. exact (@lem3588000 (_38765 = _38766)). Qed.
Lemma lem3588002 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3588003 {B : Type'} (_38765 : B) (_38766 : B) : (term199 B _38765 _38766) = (term200 B _38765 _38766).
Proof. exact (MK_COMB (@lem3588002) (@lem3588001 B _38765 _38766)). Qed.
Lemma lem3588005 (a : Prop) : (term68 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3588006 {B : Type'} (P : B -> Prop) (_38765 : B) : (term220 B P _38765) = (P _38765).
Proof. exact (@lem3588005 (P _38765)). Qed.
Lemma lem3588007 {B : Type'} (_38766 : B) (P : B -> Prop) (_38765 : B) : (term219 B _38766 P _38765) = (term221 B _38766 P _38765).
Proof. exact (MK_COMB (@lem3588003 B _38765 _38766) (@lem3588006 B P _38765)). Qed.
Lemma lem3588008 {B : Type'} (_38766 : B) (P : B -> Prop) (_38765 : B) : (term218 B _38766 P _38765) = (term221 B _38766 P _38765).
Proof. exact (TRANS (@lem3587998 B _38766 P _38765) (@lem3588007 B _38766 P _38765)). Qed.
Lemma lem3588009 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3588010 {B : Type'} (_38766 : B) (P : B -> Prop) (_38765 : B) : (term222 B _38766 P _38765) = (term223 B _38766 P _38765).
Proof. exact (MK_COMB (@lem3588009) (@lem3588008 B _38766 P _38765)). Qed.
Lemma lem3588011 {B : Type'} (P : B -> Prop) (_38766 : B) : (P _38766) = (P _38766).
Proof. exact (eq_refl (P _38766)). Qed.
Lemma lem3588012 {B : Type'} (_38765 : B) (P : B -> Prop) (_38766 : B) : (term217 B _38765 P _38766) = (term224 B _38765 P _38766).
Proof. exact (MK_COMB (@lem3588010 B _38766 P _38765) (@lem3588011 B P _38766)). Qed.
Lemma lem3588013 {B : Type'} (_38765 : B) (P : B -> Prop) (_38766 : B) : (term210 B _38766 P _38765) = (term224 B _38765 P _38766).
Proof. exact (TRANS (@lem3587995 B _38765 P _38766) (@lem3588012 B _38765 P _38766)). Qed.
Lemma lem3588015 {A B : Type'} (x'' : B -> A) (f : A -> B) (P : B -> Prop) (x : B) (h1 : term99 A B f x'') (h2 : term118 A B f P x) : term225 A B f x'' P x.
Proof. exact (conj (@lem3587898 A B x f x'' h1) (@lem3587905 A B f P x h2)). Qed.
Lemma lem3588017 {B : Type'} (_38765 : B) (P : B -> Prop) (_38766 : B) : term224 B _38765 P _38766.
Proof. exact (EQ_MP (@lem3588013 B _38765 P _38766) (@lem3587992 B _38766 P _38765)). Qed.
Lemma lem3588018 {B : Type'} (_38765 : B) (P : B -> Prop) (_38766 : B) : term224 B _38765 P _38766.
Proof. exact (@lem3588017 B _38765 P _38766). Qed.
Lemma lem3588019 {A B : Type'} (P : B -> Prop) (f : A -> B) (x'' : B -> A) (x : B) : term226 A B P f x'' x.
Proof. exact (@lem3588018 B x P (term95 A B f x'' x)). Qed.
Lemma lem3588022 {A B : Type'} (x'' : B -> A) (f : A -> B) (P : B -> Prop) (x : B) (h1 : term99 A B f x'') (h2 : term118 A B f P x) : term227 A B P f x'' x.
Proof. exact (@lem3588019 A B P f x'' x (@lem3588015 A B x'' f P x h1 h2)). Qed.
Lemma lem3588023 {A B : Type'} (x'' : B -> A) (f : A -> B) (P : B -> Prop) (x : B) (h1 : term99 A B f x'') (h2 : term118 A B f P x) : term228 A B P f x'' x.
Proof. exact (fun h0 : term229 A B P f x'' x => @lem3588022 A B x'' f P x h1 h2). Qed.
Lemma lem3588025 (p : Prop) : (term168 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3588026 {A B : Type'} (P : B -> Prop) (f : A -> B) (x'' : B -> A) (x : B) : (term228 A B P f x'' x) = (term227 A B P f x'' x).
Proof. exact (@lem3588025 (term227 A B P f x'' x)). Qed.
Lemma lem3588027 {A B : Type'} (x'' : B -> A) (f : A -> B) (P : B -> Prop) (x : B) (h1 : term99 A B f x'') (h2 : term118 A B f P x) : term227 A B P f x'' x.
Proof. exact (EQ_MP (@lem3588026 A B P f x'' x) (@lem3588023 A B x'' f P x h1 h2)). Qed.
Lemma lem3588029 (a : Prop) (b : Prop) : (term230 a b) = (term231 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3588030 {A B : Type'} (x : B) (P : B -> Prop) (f : A -> B) (_38750 : A) : (term104 A B x P f _38750) = (term103 A B x P f _38750).
Proof. exact (@lem3588029 (x = (f _38750)) (term25 A B P f _38750)). Qed.
Lemma lem3588032 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3588033 {A B : Type'} (x : B) (P : B -> Prop) (f : A -> B) (_38750 : A) : (term103 A B x P f _38750) = (term232 A B x P f _38750).
Proof. exact (@lem3588032 (term42 A B x P f _38750)). Qed.
Lemma lem3588034 {A B : Type'} (x : B) (P : B -> Prop) (f : A -> B) (_38750 : A) : (term104 A B x P f _38750) = (term232 A B x P f _38750).
Proof. exact (TRANS (@lem3588030 A B x P f _38750) (@lem3588033 A B x P f _38750)). Qed.
Lemma lem3588036 {A B : Type'} (x'' : B -> A) (f : A -> B) (P : B -> Prop) (x : B) (h1 : term99 A B f x'') (h2 : term118 A B f P x) : term233 A B P f x'' x.
Proof. exact (conj (@lem3587866 A B x f x'' h1) (@lem3588027 A B x'' f P x h1 h2)). Qed.
Lemma lem3588038 {A B : Type'} (_38750 : A) (f : A -> B) (P : B -> Prop) (x : B) (h1 : term118 A B f P x) : term232 A B x P f _38750.
Proof. exact (EQ_MP (@lem3588034 A B x P f _38750) (@lem3587578 A B _38750 f P x h1)). Qed.
Lemma lem3588039 {A B : Type'} (_38750 : A) (f : A -> B) (P : B -> Prop) (x : B) (h1 : term118 A B f P x) : term232 A B x P f _38750.
Proof. exact (@lem3588038 A B _38750 f P x h1). Qed.
Lemma lem3588040 {A B : Type'} (x'' : B -> A) (f : A -> B) (P : B -> Prop) (x : B) (h1 : term118 A B f P x) : term234 A B P f x'' x.
Proof. exact (@lem3588039 A B (x'' x) f P x h1). Qed.
Lemma lem3588043 {A B : Type'} (x'' : B -> A) (f : A -> B) (P : B -> Prop) (x : B) (h1 : term99 A B f x'') (h2 : term118 A B f P x) : False.
Proof. exact (@lem3588040 A B x'' f P x h2 (@lem3588036 A B x'' f P x h1 h2)). Qed.
Lemma lem3588044 {A B : Type'} (x'' : B -> A) (f : A -> B) (P : B -> Prop) (x : B) (h1 : term99 A B f x'') (h2 : term118 A B f P x) : term170.
Proof. exact (fun h0 : ~ False => @lem3588043 A B x'' f P x h1 h2). Qed.
Lemma lem3588046 (p : Prop) : (term168 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3588047 : term170 = False.
Proof. exact (@lem3588046 False). Qed.
Lemma lem3588048 {A B : Type'} (x'' : B -> A) (f : A -> B) (P : B -> Prop) (x : B) (h1 : term99 A B f x'') (h2 : term118 A B f P x) : False.
Proof. exact (EQ_MP (@lem3588047) (@lem3588044 A B x'' f P x h1 h2)). Qed.
Lemma lem3588049 {A B : Type'} (f : A -> B) (x' : A) (P : B -> Prop) (x : B) (h1 : term136 A B f x' P x) : False.
Proof. exact (EQ_MP (@lem3587689) (@lem3587686 A B f x' P x h1)). Qed.
Lemma lem3588050 {A B : Type'} (x'' : B -> A) (f : A -> B) (P : B -> Prop) (x : B) (h1 : term99 A B f x'') (h2 : term118 A B f P x) : (term99 A B f x'') = False.
Proof. exact (prop_ext (fun h3 : term99 A B f x'' => @lem3588048 A B x'' f P x h1 h2) (fun h3 : False => @lem3587536 A B f x'' h1)). Qed.
Lemma lem3588051 {A B : Type'} (x'' : B -> A) (f : A -> B) (P : B -> Prop) (x : B) (h1 : term99 A B f x'') (h2 : term118 A B f P x) : False.
Proof. exact (EQ_MP (@lem3588050 A B x'' f P x h1 h2) (@lem3587536 A B f x'' h1)). Qed.
Lemma lem3588052 {A B : Type'} (x'' : B -> A) (x' : A) (f : A -> B) (P : B -> Prop) (x : B) (h1 : term99 A B f x'') (h2 : term155 A B x' f P x) : False.
Proof. exact (or_elim (@lem3587489 A B x' f P x h2) (fun h0 : term136 A B f x' P x => @lem3588049 A B f x' P x h0) (fun h0 : term118 A B f P x => @lem3588051 A B x'' f P x h1 h0)). Qed.
Lemma lem3588053 {A B : Type'} (x'' : B -> A) (x' : A) (f : A -> B) (P : B -> Prop) (x : B) (h1 : term99 A B f x'') (h2 : term155 A B x' f P x) : (term99 A B f x'') = False.
Proof. exact (prop_ext (fun h3 : term99 A B f x'' => @lem3588052 A B x'' x' f P x h1 h2) (fun h3 : False => @lem3587502 A B f x'' h1)). Qed.
Lemma lem3588054 {A B : Type'} (x'' : B -> A) (x' : A) (f : A -> B) (P : B -> Prop) (x : B) (h1 : term99 A B f x'') (h2 : term155 A B x' f P x) : False.
Proof. exact (EQ_MP (@lem3588053 A B x'' x' f P x h1 h2) (@lem3587502 A B f x'' h1)). Qed.
Lemma lem3588055 {A B : Type'} (x'' : B -> A) (x' : A) (f : A -> B) (P : B -> Prop) (x : B) (h1 : term99 A B f x'') (h2 : term155 A B x' f P x) : (term155 A B x' f P x) = False.
Proof. exact (prop_ext (fun h3 : term155 A B x' f P x => @lem3588054 A B x'' x' f P x h1 h2) (fun h3 : False => @lem3587489 A B x' f P x h2)). Qed.
Lemma lem3588056 {A B : Type'} (x'' : B -> A) (x' : A) (f : A -> B) (P : B -> Prop) (x : B) (h1 : term99 A B f x'') (h2 : term155 A B x' f P x) : False.
Proof. exact (EQ_MP (@lem3588055 A B x'' x' f P x h1 h2) (@lem3587489 A B x' f P x h2)). Qed.
Lemma lem3588057 {A B : Type'} (x' : A) (f : A -> B) (P : B -> Prop) (x : B) (h1 : term56 A B f) (h2 : term155 A B x' f P x) : False.
Proof. exact (ex_elim (@lem3587241 A B f h1) (fun x'' : B -> A => fun h0 : term101 A B f x'' => @lem3588056 A B x'' x' f P x h0 h2)). Qed.
Lemma lem3588058 {A B : Type'} (f : A -> B) (P : B -> Prop) (x : B) (h1 : term56 A B f) (h2 : term78 A B f P x) : False.
Proof. exact (ex_elim (@lem3587432 A B f P x h2) (fun x' : A => fun h0 : term157 A B f P x x' => @lem3588057 A B x' f P x h1 h0)). Qed.
Lemma lem3588059 {A B : Type'} (f : A -> B) (P : B -> Prop) (x : B) (h1 : term56 A B f) (h2 : term78 A B f P x) : (term78 A B f P x) = False.
Proof. exact (prop_ext (fun h3 : term78 A B f P x => @lem3588058 A B f P x h1 h2) (fun h3 : False => @lem3587192 A B f P x h2)). Qed.
Lemma lem3588060 {A B : Type'} (f : A -> B) (P : B -> Prop) (x : B) (h1 : term56 A B f) (h2 : term78 A B f P x) : False.
Proof. exact (EQ_MP (@lem3588059 A B f P x h1 h2) (@lem3587192 A B f P x h2)). Qed.
Lemma lem3588061 {A B : Type'} (P : B -> Prop) (x : B) (f : A -> B) (h1 : term56 A B f) : term77 A B f P x.
Proof. exact (fun h0 : term78 A B f P x => @lem3588060 A B f P x h1 h0). Qed.
Lemma lem3588062 {A B : Type'} (P : B -> Prop) (x : B) (f : A -> B) (h1 : term56 A B f) : (term45 A B x P f) = (P x).
Proof. exact (EQ_MP (@lem3587191 A B f P x) (@lem3588061 A B P x f h1)). Qed.
Lemma lem3588067 {A B : Type'} (P : B -> Prop) (f : A -> B) (h1 : term56 A B f) : term50 A B f P.
Proof. exact (fun x : B => @lem3588062 A B P x f h1). Qed.
Lemma lem3588072 {A B : Type'} (f : A -> B) (h1 : term56 A B f) : term54 A B f.
Proof. exact (fun P : B -> Prop => @lem3588067 A B P f h1). Qed.
Lemma lem3588073 {A B : Type'} (f : A -> B) : term61 A B f.
Proof. exact (fun h0 : term56 A B f => @lem3588072 A B f h0). Qed.
Lemma lem3588078 {A B : Type'} : term72 A B.
Proof. exact (fun f : A -> B => @lem3588073 A B f). Qed.
Lemma lem3588079 {A B : Type'} : term71 A B.
Proof. exact (EQ_MP (@lem3587186 A B) (@lem3588078 A B)). Qed.
Lemma lem3588080 {A B : Type'} (f : A -> B) : term235 A B f.
Proof. exact (@lem3588079 A B f). Qed.
Lemma lem3588081 {A B : Type'} (f : A -> B) : (term235 A B f) = (term62 A B f).
Proof. exact (eq_refl (term235 A B f)). Qed.
Lemma lem3588082 {A B : Type'} (f : A -> B) : term62 A B f.
Proof. exact (EQ_MP (@lem3588081 A B f) (@lem3588080 A B f)). Qed.
Lemma lem3588084 {A B : Type'} (f : A -> B) : term62 A B f.
Proof. exact (@lem3587021 A B f (@lem3588082 A B f)). Qed.
Lemma lem3588085 {A B : Type'} (f : A -> B) (h1 : term63 A B f) : False.
Proof. exact (@lem3588084 A B f (@lem3587005 A B f h1)). Qed.
Lemma lem3588086 {A B : Type'} (f : A -> B) (h1 : term63 A B f) : (term63 A B f) = False.
Proof. exact (prop_ext (fun h2 : term63 A B f => @lem3588085 A B f h1) (fun h2 : False => @lem3587005 A B f h1)). Qed.
Lemma lem3588087 {A B : Type'} (f : A -> B) (h1 : term63 A B f) : False.
Proof. exact (EQ_MP (@lem3588086 A B f h1) (@lem3587005 A B f h1)). Qed.
Lemma lem3588088 {A B : Type'} (f : A -> B) : term62 A B f.
Proof. exact (fun h0 : term63 A B f => @lem3588087 A B f h0). Qed.
Lemma lem3588089 {A B : Type'} (f : A -> B) : term61 A B f.
Proof. exact (EQ_MP (@lem3587004 A B f) (@lem3588088 A B f)). Qed.
Lemma lem3588091 (p : Prop) : p = (term60 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3588092 {A B : Type'} (f : A -> B) : (term236 A B f) = (term237 A B f).
Proof. exact (@lem3588091 (term236 A B f)). Qed.
Lemma lem3588093 {A B : Type'} (f : A -> B) : (term237 A B f) = (term236 A B f).
Proof. exact (SYM (@lem3588092 A B f)). Qed.
Lemma lem3588094 {A B : Type'} (f : A -> B) (h1 : term238 A B f) : term238 A B f.
Proof. exact (h1). Qed.
Lemma lem3588097 {A B : Type'} (f : A -> B) (h1 : term237 A B f) : term237 A B f.
Proof. exact (h1). Qed.
Lemma lem3588098 {A B : Type'} (f : A -> B) : term239 A B f.
Proof. exact (fun h0 : term237 A B f => @lem3588097 A B f h0). Qed.
Lemma lem3588099 {A B : Type'} (f : A -> B) (h1 : term239 A B f) : term239 A B f.
Proof. exact (h1). Qed.
Lemma lem3588100 {A B : Type'} (f : A -> B) (h1 : term237 A B f) : term237 A B f.
Proof. exact (h1). Qed.
Lemma lem3588101 {A B : Type'} (f : A -> B) (h1 : term237 A B f) (h2 : term239 A B f) : term237 A B f.
Proof. exact (@lem3588099 A B f h2 (@lem3588100 A B f h1)). Qed.
Lemma lem3588102 {A B : Type'} (f : A -> B) (h1 : term237 A B f) : term240 A B f.
Proof. exact (fun h0 : term239 A B f => @lem3588101 A B f h1 h0). Qed.
Lemma lem3588103 {A B : Type'} (f : A -> B) (h1 : term239 A B f) : term239 A B f.
Proof. exact (h1). Qed.
Lemma lem3588104 {A B : Type'} (f : A -> B) (h1 : term237 A B f) (h2 : term239 A B f) : term237 A B f.
Proof. exact (@lem3588102 A B f h1 (@lem3588103 A B f h2)). Qed.
Lemma lem3588105 {A B : Type'} (f : A -> B) (h1 : term239 A B f) : term239 A B f.
Proof. exact (fun h0 : term237 A B f => @lem3588104 A B f h0 h1). Qed.
Lemma lem3588106 {A B : Type'} (f : A -> B) : term241 A B f.
Proof. exact (fun h0 : term239 A B f => @lem3588105 A B f h0). Qed.
Lemma lem3588109 {A B : Type'} (f : A -> B) : term239 A B f.
Proof. exact (@lem3588106 A B f (@lem3588098 A B f)). Qed.
Lemma lem3588110 {A B : Type'} (f : A -> B) : term239 A B f.
Proof. exact (@lem3588109 A B f). Qed.
Lemma lem3588116 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3588117 {A B : Type'} (f : A -> B) : (term237 A B f) = (term242 A B f).
Proof. exact (@lem3588116 (term238 A B f)). Qed.
Lemma lem3588119 (t : Prop) : (term68 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3588120 {A B : Type'} (f : A -> B) : (term242 A B f) = (term236 A B f).
Proof. exact (@lem3588119 (term236 A B f)). Qed.
Lemma lem3588123 {A B : Type'} (f : A -> B) : (term237 A B f) = (term236 A B f).
Proof. exact (TRANS (@lem3588117 A B f) (@lem3588120 A B f)). Qed.
Lemma lem3588186 {A B : Type'} : (term243 A B) = (term244 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3588123 A B f)). Qed.
Lemma lem3588187 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3588188 {A B : Type'} : (term245 A B) = (term246 A B).
Proof. exact (MK_COMB (@lem3588187 A B) (@lem3588186 A B)). Qed.
Lemma lem3588193 {A B : Type'} (f : A -> B) (x : A) : (term247 A B f x) = True.
Proof. exact (eq_refl (term247 A B f x)). Qed.
Lemma lem3588194 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term40 A B x f x') = (term40 A B x f x').
Proof. exact (eq_refl (term40 A B x f x')). Qed.
Lemma lem3588195 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term248 A B x f x') = (term249 A B x f x').
Proof. exact (MK_COMB (@lem3588194 A B x f x') (@lem3588193 A B f x')). Qed.
Lemma lem3588196 {A B : Type'} (x : B) (f : A -> B) : (term250 A B x f) = (term251 A B x f).
Proof. exact (fun_ext (fun x' : A => @lem3588195 A B x f x')). Qed.
Lemma lem3588197 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3588198 {A B : Type'} (x : B) (f : A -> B) : (term252 A B x f) = (term253 A B x f).
Proof. exact (MK_COMB (@lem3588197 A) (@lem3588196 A B x f)). Qed.
Lemma lem3588199 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3588200 {A B : Type'} (x : B) (f : A -> B) : (term254 A B x f) = (term255 A B x f).
Proof. exact (MK_COMB (@lem3588199) (@lem3588198 A B x f)). Qed.
Lemma lem3588201 {B : Type'} (x : B) : (term256 B x) = True.
Proof. exact (eq_refl (term256 B x)). Qed.
Lemma lem3588202 {A B : Type'} (x : B) (f : A -> B) : ((term252 A B x f) = (term256 B x)) = ((term253 A B x f) = True).
Proof. exact (MK_COMB (@lem3588200 A B x f) (@lem3588201 B x)). Qed.
Lemma lem3588203 {A B : Type'} (f : A -> B) : (term257 A B f) = (term258 A B f).
Proof. exact (fun_ext (fun x : B => @lem3588202 A B x f)). Qed.
Lemma lem3588204 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3588205 {A B : Type'} (f : A -> B) : (term59 A B f) = (term259 A B f).
Proof. exact (MK_COMB (@lem3588204 B) (@lem3588203 A B f)). Qed.
Lemma lem3588206 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3588207 {A B : Type'} (f : A -> B) : (term260 A B f) = (term261 A B f).
Proof. exact (MK_COMB (@lem3588206) (@lem3588205 A B f)). Qed.
Lemma lem3588208 {A B : Type'} (f : A -> B) : (term56 A B f) = (term56 A B f).
Proof. exact (eq_refl (term56 A B f)). Qed.
Lemma lem3588209 {A B : Type'} (f : A -> B) : (term236 A B f) = (term262 A B f).
Proof. exact (MK_COMB (@lem3588207 A B f) (@lem3588208 A B f)). Qed.
Lemma lem3588210 {A B : Type'} : (term244 A B) = (term263 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3588209 A B f)). Qed.
Lemma lem3588211 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3588212 {A B : Type'} : (term246 A B) = (term264 A B).
Proof. exact (MK_COMB (@lem3588211 A B) (@lem3588210 A B)). Qed.
Lemma lem3588215 {A B : Type'} : (term245 A B) = (term264 A B).
Proof. exact (TRANS (@lem3588188 A B) (@lem3588212 A B)). Qed.
Lemma lem3588216 {A B : Type'} (f : A -> B) (x : A) (y : B) : ((f x) = y) = ((f x) = y).
Proof. exact (eq_refl ((f x) = y)). Qed.
Lemma lem3588217 {A B : Type'} (f : A -> B) (y : B) : (term73 A B f y) = (term73 A B f y).
Proof. exact (fun_ext (fun x : A => @lem3588216 A B f x y)). Qed.
Lemma lem3588218 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3588219 {A B : Type'} (f : A -> B) (y : B) : (term74 A B f y) = (term74 A B f y).
Proof. exact (MK_COMB (@lem3588218 A) (@lem3588217 A B f y)). Qed.
Lemma lem3588220 {A B : Type'} (f : A -> B) : (term75 A B f) = (term75 A B f).
Proof. exact (fun_ext (fun y : B => @lem3588219 A B f y)). Qed.
Lemma lem3588221 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3588222 {A B : Type'} (f : A -> B) : (term56 A B f) = (term56 A B f).
Proof. exact (MK_COMB (@lem3588221 B) (@lem3588220 A B f)). Qed.
Lemma lem3588223 : True = True.
Proof. exact (eq_refl True). Qed.
Lemma lem3588228 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term249 A B x f x') = (term249 A B x f x').
Proof. exact (eq_refl (term249 A B x f x')). Qed.
Lemma lem3588229 {A B : Type'} (x : B) (f : A -> B) : (term251 A B x f) = (term251 A B x f).
Proof. exact (fun_ext (fun x' : A => @lem3588228 A B x f x')). Qed.
Lemma lem3588230 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3588231 {A B : Type'} (x : B) (f : A -> B) : (term253 A B x f) = (term253 A B x f).
Proof. exact (MK_COMB (@lem3588230 A) (@lem3588229 A B x f)). Qed.
Lemma lem3588232 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3588233 {A B : Type'} (x : B) (f : A -> B) : (term255 A B x f) = (term255 A B x f).
Proof. exact (MK_COMB (@lem3588232) (@lem3588231 A B x f)). Qed.
Lemma lem3588234 {A B : Type'} (x : B) (f : A -> B) : ((term253 A B x f) = True) = ((term253 A B x f) = True).
Proof. exact (MK_COMB (@lem3588233 A B x f) (@lem3588223)). Qed.
Lemma lem3588235 {A B : Type'} (f : A -> B) : (term258 A B f) = (term258 A B f).
Proof. exact (fun_ext (fun x : B => @lem3588234 A B x f)). Qed.
Lemma lem3588236 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3588237 {A B : Type'} (f : A -> B) : (term259 A B f) = (term259 A B f).
Proof. exact (MK_COMB (@lem3588236 B) (@lem3588235 A B f)). Qed.
Lemma lem3588238 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3588239 {A B : Type'} (f : A -> B) : (term261 A B f) = (term261 A B f).
Proof. exact (MK_COMB (@lem3588238) (@lem3588237 A B f)). Qed.
Lemma lem3588240 {A B : Type'} (f : A -> B) : (term262 A B f) = (term262 A B f).
Proof. exact (MK_COMB (@lem3588239 A B f) (@lem3588222 A B f)). Qed.
Lemma lem3588241 {A B : Type'} : (term263 A B) = (term263 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3588240 A B f)). Qed.
Lemma lem3588242 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3588243 {A B : Type'} : (term264 A B) = (term264 A B).
Proof. exact (MK_COMB (@lem3588242 A B) (@lem3588241 A B)). Qed.
Lemma lem3588244 {A B : Type'} : (term245 A B) = (term264 A B).
Proof. exact (TRANS (@lem3588215 A B) (@lem3588243 A B)). Qed.
Lemma lem3588260 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem21741 t)). Qed.
Lemma lem3588261 {A B : Type'} (x : B) (f : A -> B) : ((term253 A B x f) = True) = (term253 A B x f).
Proof. exact (@lem3588260 (term253 A B x f)). Qed.
Lemma lem3588269 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem21761 t)). Qed.
Lemma lem3588270 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term249 A B x f x') = (x = (f x')).
Proof. exact (@lem3588269 (x = (f x'))). Qed.
Lemma lem3588271 {A B : Type'} (x : B) (f : A -> B) : (term251 A B x f) = (term265 A B x f).
Proof. exact (fun_ext (fun x' : A => @lem3588270 A B x f x')). Qed.
Lemma lem3588272 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3588273 {A B : Type'} (x : B) (f : A -> B) : (term253 A B x f) = (term266 A B x f).
Proof. exact (MK_COMB (@lem3588272 A) (@lem3588271 A B x f)). Qed.
Lemma lem3588280 {A B : Type'} (x : B) (f : A -> B) : ((term253 A B x f) = True) = (term266 A B x f).
Proof. exact (TRANS (@lem3588261 A B x f) (@lem3588273 A B x f)). Qed.
Lemma lem3588281 {A B : Type'} (f : A -> B) : (term258 A B f) = (term267 A B f).
Proof. exact (fun_ext (fun x : B => @lem3588280 A B x f)). Qed.
Lemma lem3588282 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3588283 {A B : Type'} (f : A -> B) : (term259 A B f) = (term268 A B f).
Proof. exact (MK_COMB (@lem3588282 B) (@lem3588281 A B f)). Qed.
Lemma lem3588290 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3588291 {A B : Type'} (f : A -> B) : (term261 A B f) = (term269 A B f).
Proof. exact (MK_COMB (@lem3588290) (@lem3588283 A B f)). Qed.
Lemma lem3588304 {A B : Type'} (f : A -> B) : (term56 A B f) = (term56 A B f).
Proof. exact (eq_refl (term56 A B f)). Qed.
Lemma lem3588305 {A B : Type'} (f : A -> B) : (term262 A B f) = (term270 A B f).
Proof. exact (MK_COMB (@lem3588291 A B f) (@lem3588304 A B f)). Qed.
Lemma lem3588308 {A B : Type'} : (term263 A B) = (term271 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3588305 A B f)). Qed.
Lemma lem3588309 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3588310 {A B : Type'} : (term264 A B) = (term272 A B).
Proof. exact (MK_COMB (@lem3588309 A B) (@lem3588308 A B)). Qed.
Lemma lem3588317 {A B : Type'} : (term245 A B) = (term272 A B).
Proof. exact (TRANS (@lem3588244 A B) (@lem3588310 A B)). Qed.
Lemma lem3588318 {A B : Type'} : (term272 A B) = (term245 A B).
Proof. exact (SYM (@lem3588317 A B)). Qed.
Lemma lem3588319 {A B : Type'} (f : A -> B) (h1 : term268 A B f) : term268 A B f.
Proof. exact (h1). Qed.
Lemma lem3588321 (p : Prop) : p = (term60 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3588322 {A B : Type'} (f : A -> B) (y : B) : (term74 A B f y) = (term273 A B f y).
Proof. exact (@lem3588321 (term74 A B f y)). Qed.
Lemma lem3588323 {A B : Type'} (f : A -> B) (y : B) : (term273 A B f y) = (term74 A B f y).
Proof. exact (SYM (@lem3588322 A B f y)). Qed.
Lemma lem3588324 {A B : Type'} (f : A -> B) (y : B) (h1 : term274 A B f y) : term274 A B f y.
Proof. exact (h1). Qed.
Lemma lem3588325 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (x = (f x')) = (x = (f x')).
Proof. exact (eq_refl (x = (f x'))). Qed.
Lemma lem3588326 {A B : Type'} (x : B) (f : A -> B) : (term265 A B x f) = (term265 A B x f).
Proof. exact (fun_ext (fun x' : A => @lem3588325 A B x f x')). Qed.
Lemma lem3588327 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3588328 {A B : Type'} (x : B) (f : A -> B) : (term266 A B x f) = (term266 A B x f).
Proof. exact (MK_COMB (@lem3588327 A) (@lem3588326 A B x f)). Qed.
Lemma lem3588329 {A B : Type'} (f : A -> B) : (term267 A B f) = (term267 A B f).
Proof. exact (fun_ext (fun x : B => @lem3588328 A B x f)). Qed.
Lemma lem3588330 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3588331 {A B : Type'} (f : A -> B) : (term268 A B f) = (term268 A B f).
Proof. exact (MK_COMB (@lem3588330 B) (@lem3588329 A B f)). Qed.
Lemma lem3588342 {A B : Type'} (P : type1413 A B) : (term79 A B P) = (term80 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3588343 {A B : Type'} (P : type1470 A B) : (term81 A B P) = (term82 A B P).
Proof. exact (@lem3588342 B A P). Qed.
Lemma lem3588344 {A B : Type'} (f : A -> B) : (term275 A B f) = (term276 A B f).
Proof. exact (@lem3588343 A B (term277 A B f)). Qed.
Lemma lem3588345 {A B : Type'} (x : B) (f : A -> B) : (term278 A B f x) = (term265 A B x f).
Proof. exact (eq_refl (term278 A B f x)). Qed.
Lemma lem3588346 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3588347 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term279 A B f x x') = (term280 A B x f x').
Proof. exact (MK_COMB (@lem3588345 A B x f) (@lem3588346 A x')). Qed.
Lemma lem3588348 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term280 A B x f x') = (x = (f x')).
Proof. exact (eq_refl (term280 A B x f x')). Qed.
Lemma lem3588349 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term279 A B f x x') = (x = (f x')).
Proof. exact (TRANS (@lem3588347 A B x f x') (@lem3588348 A B x f x')). Qed.
Lemma lem3588350 {A B : Type'} (x : B) (f : A -> B) : (term281 A B f x) = (term265 A B x f).
Proof. exact (fun_ext (fun x' : A => @lem3588349 A B x f x')). Qed.
Lemma lem3588351 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3588352 {A B : Type'} (x : B) (f : A -> B) : (term282 A B f x) = (term266 A B x f).
Proof. exact (MK_COMB (@lem3588351 A) (@lem3588350 A B x f)). Qed.
Lemma lem3588353 {A B : Type'} (f : A -> B) : (term283 A B f) = (term267 A B f).
Proof. exact (fun_ext (fun x : B => @lem3588352 A B x f)). Qed.
Lemma lem3588354 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3588355 {A B : Type'} (f : A -> B) : (term275 A B f) = (term268 A B f).
Proof. exact (MK_COMB (@lem3588354 B) (@lem3588353 A B f)). Qed.
Lemma lem3588356 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3588357 {A B : Type'} (f : A -> B) : (term284 A B f) = (term285 A B f).
Proof. exact (MK_COMB (@lem3588356) (@lem3588355 A B f)). Qed.
Lemma lem3588358 {A B : Type'} (x : B) (f : A -> B) : (term278 A B f x) = (term265 A B x f).
Proof. exact (eq_refl (term278 A B f x)). Qed.
Lemma lem3588359 {A B : Type'} (x : B -> A) (x' : B) : (x x') = (x x').
Proof. exact (eq_refl (x x')). Qed.
Lemma lem3588360 {A B : Type'} (f : A -> B) (x : B -> A) (x' : B) : (term286 A B f x x') = (term287 A B f x x').
Proof. exact (MK_COMB (@lem3588358 A B x' f) (@lem3588359 A B x x')). Qed.
Lemma lem3588361 {A B : Type'} (f : A -> B) (x : B -> A) (x' : B) : (term287 A B f x x') = (x' = (term95 A B f x x')).
Proof. exact (eq_refl (term287 A B f x x')). Qed.
Lemma lem3588362 {A B : Type'} (f : A -> B) (x : B -> A) (x' : B) : (term286 A B f x x') = (x' = (term95 A B f x x')).
Proof. exact (TRANS (@lem3588360 A B f x x') (@lem3588361 A B f x x')). Qed.
Lemma lem3588363 {A B : Type'} (f : A -> B) (x : B -> A) : (term288 A B f x) = (term289 A B f x).
Proof. exact (fun_ext (fun x' : B => @lem3588362 A B f x x')). Qed.
Lemma lem3588364 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3588365 {A B : Type'} (f : A -> B) (x : B -> A) : (term290 A B f x) = (term291 A B f x).
Proof. exact (MK_COMB (@lem3588364 B) (@lem3588363 A B f x)). Qed.
Lemma lem3588366 {A B : Type'} (f : A -> B) : (term292 A B f) = (term293 A B f).
Proof. exact (fun_ext (fun x : B -> A => @lem3588365 A B f x)). Qed.
Lemma lem3588367 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem3588368 {A B : Type'} (f : A -> B) : (term276 A B f) = (term294 A B f).
Proof. exact (MK_COMB (@lem3588367 A B) (@lem3588366 A B f)). Qed.
Lemma lem3588369 {A B : Type'} (f : A -> B) : ((term275 A B f) = (term276 A B f)) = ((term268 A B f) = (term294 A B f)).
Proof. exact (MK_COMB (@lem3588357 A B f) (@lem3588368 A B f)). Qed.
Lemma lem3588371 {A B : Type'} (f : A -> B) : (term268 A B f) = (term294 A B f).
Proof. exact (EQ_MP (@lem3588369 A B f) (@lem3588344 A B f)). Qed.
Lemma lem3588372 {A B : Type'} (f : A -> B) : (term268 A B f) = (term294 A B f).
Proof. exact (TRANS (@lem3588331 A B f) (@lem3588371 A B f)). Qed.
Lemma lem3588373 {A B : Type'} (f : A -> B) (h1 : term268 A B f) : term294 A B f.
Proof. exact (EQ_MP (@lem3588372 A B f) (@lem3588319 A B f h1)). Qed.
Lemma lem3588375 {A : Type'} (P : A -> Prop) : (term105 A P) = (term106 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem3588376 {A B : Type'} (f : A -> B) (y : B) : (term274 A B f y) = (term295 A B f y).
Proof. exact (@lem3588375 A (term73 A B f y)). Qed.
Lemma lem3588377 {A B : Type'} (f : A -> B) (x : A) (y : B) : (term88 A B f y x) = ((f x) = y).
Proof. exact (eq_refl (term88 A B f y x)). Qed.
Lemma lem3588378 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3588380 {A B : Type'} (f : A -> B) (x : A) (y : B) : (term296 A B f y x) = (term297 A B f x y).
Proof. exact (MK_COMB (@lem3588378) (@lem3588377 A B f x y)). Qed.
Lemma lem3588381 {A B : Type'} (f : A -> B) (y : B) : (term298 A B f y) = (term299 A B f y).
Proof. exact (fun_ext (fun x : A => @lem3588380 A B f x y)). Qed.
Lemma lem3588382 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3588383 {A B : Type'} (f : A -> B) (y : B) : (term295 A B f y) = (term300 A B f y).
Proof. exact (MK_COMB (@lem3588382 A) (@lem3588381 A B f y)). Qed.
Lemma lem3588392 {A B : Type'} (f : A -> B) (y : B) : (term274 A B f y) = (term300 A B f y).
Proof. exact (TRANS (@lem3588376 A B f y) (@lem3588383 A B f y)). Qed.
Lemma lem3588393 {A B : Type'} (f : A -> B) (y : B) (h1 : term274 A B f y) : term300 A B f y.
Proof. exact (EQ_MP (@lem3588392 A B f y) (@lem3588324 A B f y h1)). Qed.
Lemma lem3588394 {A B : Type'} (f : A -> B) (x : B -> A) (h1 : term291 A B f x) : term291 A B f x.
Proof. exact (h1). Qed.
Lemma lem3588403 {A B : Type'} (f : A -> B) (x : A) (y : B) : (term297 A B f x y) = (term297 A B f x y).
Proof. exact (eq_refl (term297 A B f x y)). Qed.
Lemma lem3588404 {A B : Type'} (f : A -> B) (y : B) : (term299 A B f y) = (term299 A B f y).
Proof. exact (fun_ext (fun x : A => @lem3588403 A B f x y)). Qed.
Lemma lem3588405 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3588406 {A B : Type'} (f : A -> B) (y : B) : (term300 A B f y) = (term300 A B f y).
Proof. exact (MK_COMB (@lem3588405 A) (@lem3588404 A B f y)). Qed.
Lemma lem3588407 {A B : Type'} (f : A -> B) (y : B) (h1 : term274 A B f y) : term300 A B f y.
Proof. exact (EQ_MP (@lem3588406 A B f y) (@lem3588393 A B f y h1)). Qed.
Lemma lem3588416 {A B : Type'} (f : A -> B) (x : B -> A) (x' : B) : (x' = (term95 A B f x x')) = (x' = (term95 A B f x x')).
Proof. exact (eq_refl (x' = (term95 A B f x x'))). Qed.
Lemma lem3588417 {A B : Type'} (f : A -> B) (x : B -> A) : (term289 A B f x) = (term289 A B f x).
Proof. exact (fun_ext (fun x' : B => @lem3588416 A B f x x')). Qed.
Lemma lem3588418 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3588419 {A B : Type'} (f : A -> B) (x : B -> A) : (term291 A B f x) = (term291 A B f x).
Proof. exact (MK_COMB (@lem3588418 B) (@lem3588417 A B f x)). Qed.
Lemma lem3588420 {A B : Type'} (f : A -> B) (x : B -> A) (h1 : term291 A B f x) : term291 A B f x.
Proof. exact (EQ_MP (@lem3588419 A B f x) (@lem3588394 A B f x h1)). Qed.
Lemma lem3588422 {A B : Type'} (f : A -> B) (x : A) (y : B) : (term297 A B f x y) = (term297 A B f x y).
Proof. exact (eq_refl (term297 A B f x y)). Qed.
Lemma lem3588423 {A B : Type'} (f : A -> B) (y : B) : (term299 A B f y) = (term299 A B f y).
Proof. exact (fun_ext (fun x : A => @lem3588422 A B f x y)). Qed.
Lemma lem3588424 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3588426 {A B : Type'} (f : A -> B) (y : B) : (term300 A B f y) = (term300 A B f y).
Proof. exact (MK_COMB (@lem3588424 A) (@lem3588423 A B f y)). Qed.
Lemma lem3588427 {A B : Type'} (f : A -> B) (y : B) (h1 : term274 A B f y) : term300 A B f y.
Proof. exact (EQ_MP (@lem3588426 A B f y) (@lem3588407 A B f y h1)). Qed.
Lemma lem3588429 {A B : Type'} (f : A -> B) (x : B -> A) (x' : B) : (x' = (term95 A B f x x')) = (x' = (term95 A B f x x')).
Proof. exact (eq_refl (x' = (term95 A B f x x'))). Qed.
Lemma lem3588430 {A B : Type'} (f : A -> B) (x : B -> A) : (term289 A B f x) = (term289 A B f x).
Proof. exact (fun_ext (fun x' : B => @lem3588429 A B f x x')). Qed.
Lemma lem3588431 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3588433 {A B : Type'} (f : A -> B) (x : B -> A) : (term291 A B f x) = (term291 A B f x).
Proof. exact (MK_COMB (@lem3588431 B) (@lem3588430 A B f x)). Qed.
Lemma lem3588434 {A B : Type'} (f : A -> B) (x : B -> A) (h1 : term291 A B f x) : term291 A B f x.
Proof. exact (EQ_MP (@lem3588433 A B f x) (@lem3588420 A B f x h1)). Qed.
Lemma lem3588435 {A B : Type'} (_38771 : A) (f : A -> B) (y : B) (h1 : term274 A B f y) : term301 A B f y _38771.
Proof. exact (@lem3588427 A B f y h1 _38771). Qed.
Lemma lem3588436 {A B : Type'} (f : A -> B) (_38771 : A) (y : B) : (term301 A B f y _38771) = (term297 A B f _38771 y).
Proof. exact (eq_refl (term301 A B f y _38771)). Qed.
Lemma lem3588438 {A B : Type'} (_38772 : B) (f : A -> B) (x : B -> A) (h1 : term291 A B f x) : term302 A B f x _38772.
Proof. exact (@lem3588434 A B f x h1 _38772). Qed.
Lemma lem3588439 {A B : Type'} (f : A -> B) (x : B -> A) (_38772 : B) : (term302 A B f x _38772) = (_38772 = (term95 A B f x _38772)).
Proof. exact (eq_refl (term302 A B f x _38772)). Qed.
Lemma lem3588442 {A B : Type'} (_38771 : A) (f : A -> B) (y : B) (h1 : term274 A B f y) : term297 A B f _38771 y.
Proof. exact (EQ_MP (@lem3588436 A B f _38771 y) (@lem3588435 A B _38771 f y h1)). Qed.
Lemma lem3588462 {B : Type'} (x : B) (y : B) (z : B) : term177 B x y z.
Proof. exact (@lem21385 B x y z). Qed.
Lemma lem3588466 {A B : Type'} (_38772 : B) (f : A -> B) (x : B -> A) (h1 : term291 A B f x) : _38772 = (term95 A B f x _38772).
Proof. exact (EQ_MP (@lem3588439 A B f x _38772) (@lem3588438 A B _38772 f x h1)). Qed.
Lemma lem3588467 {A B : Type'} (_38772 : B) (f : A -> B) (x : B -> A) (h1 : term291 A B f x) : _38772 = (term95 A B f x _38772).
Proof. exact (@lem3588466 A B _38772 f x h1). Qed.
Lemma lem3588468 {A B : Type'} (y : B) (f : A -> B) (x : B -> A) (h1 : term291 A B f x) : y = (term95 A B f x y).
Proof. exact (@lem3588467 A B y f x h1). Qed.
Lemma lem3588469 {A B : Type'} (y : B) (f : A -> B) (x : B -> A) (h1 : term291 A B f x) : term207 A B f x y.
Proof. exact (fun h0 : term208 A B f x y => @lem3588468 A B y f x h1). Qed.
Lemma lem3588471 (p : Prop) : (term168 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3588472 {A B : Type'} (f : A -> B) (x : B -> A) (y : B) : (term207 A B f x y) = (y = (term95 A B f x y)).
Proof. exact (@lem3588471 (y = (term95 A B f x y))). Qed.
Lemma lem3588473 {A B : Type'} (y : B) (f : A -> B) (x : B -> A) (h1 : term291 A B f x) : y = (term95 A B f x y).
Proof. exact (EQ_MP (@lem3588472 A B f x y) (@lem3588469 A B y f x h1)). Qed.
Lemma lem3588475 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem3588476 {B : Type'} (x : B) : x = x.
Proof. exact (@lem3588475 B x). Qed.
Lemma lem3588477 {B : Type'} (y : B) : y = y.
Proof. exact (@lem3588476 B y). Qed.
Lemma lem3588478 {B : Type'} (y : B) : term303 B y.
Proof. exact (fun h0 : term304 B y => @lem3588477 B y). Qed.
Lemma lem3588480 (p : Prop) : (term168 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3588481 {B : Type'} (y : B) : (term303 B y) = (y = y).
Proof. exact (@lem3588480 (y = y)). Qed.
Lemma lem3588482 {B : Type'} (y : B) : y = y.
Proof. exact (EQ_MP (@lem3588481 B y) (@lem3588478 B y)). Qed.
Lemma lem3588500 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3588501 {B : Type'} (y : B) (x : B) (z : B) : (term182 B x y z) = (term183 B y x z).
Proof. exact (@lem3588500 (y = z) (term184 B x z)). Qed.
Lemma lem3588511 {B : Type'} (x : B) (y : B) : (term185 B x y) = (term185 B x y).
Proof. exact (eq_refl (term185 B x y)). Qed.
Lemma lem3588512 {B : Type'} (y : B) (x : B) (z : B) : (term177 B x y z) = (term186 B y x z).
Proof. exact (MK_COMB (@lem3588511 B x y) (@lem3588501 B y x z)). Qed.
Lemma lem3588516 (q : Prop) (p : Prop) (r : Prop) : (term187 p q r) = (term187 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3588517 {B : Type'} (y : B) (x : B) (z : B) : (term186 B y x z) = (term188 B y x z).
Proof. exact (@lem3588516 (y = z) (term184 B x y) (term184 B x z)). Qed.
Lemma lem3588539 {B : Type'} (y : B) (x : B) (z : B) : (term177 B x y z) = (term188 B y x z).
Proof. exact (TRANS (@lem3588512 B y x z) (@lem3588517 B y x z)). Qed.
Lemma lem3588540 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3588541 {B : Type'} (y : B) (x : B) (z : B) : (term189 B x y z) = (term190 B y x z).
Proof. exact (MK_COMB (@lem3588540) (@lem3588539 B y x z)). Qed.
Lemma lem3588563 {B : Type'} (y : B) (x : B) (z : B) : (term188 B y x z) = (term188 B y x z).
Proof. exact (eq_refl (term188 B y x z)). Qed.
Lemma lem3588564 {B : Type'} (y : B) (x : B) (z : B) : ((term177 B x y z) = (term188 B y x z)) = ((term188 B y x z) = (term188 B y x z)).
Proof. exact (MK_COMB (@lem3588541 B y x z) (@lem3588563 B y x z)). Qed.
Lemma lem3588566 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3588567 (x : Prop) : (x = x) = True.
Proof. exact (@lem3588566 Prop x). Qed.
Lemma lem3588568 {B : Type'} (y : B) (x : B) (z : B) : ((term188 B y x z) = (term188 B y x z)) = True.
Proof. exact (@lem3588567 (term188 B y x z)). Qed.
Lemma lem3588569 {B : Type'} (y : B) (x : B) (z : B) : ((term177 B x y z) = (term188 B y x z)) = True.
Proof. exact (TRANS (@lem3588564 B y x z) (@lem3588568 B y x z)). Qed.
Lemma lem3588570 {B : Type'} (y : B) (x : B) (z : B) : True = ((term177 B x y z) = (term188 B y x z)).
Proof. exact (SYM (@lem3588569 B y x z)). Qed.
Lemma lem3588571 {B : Type'} (y : B) (x : B) (z : B) : (term177 B x y z) = (term188 B y x z).
Proof. exact (EQ_MP (@lem3588570 B y x z) (@lem0)). Qed.
Lemma lem3588572 {B : Type'} (y : B) (x : B) (z : B) : term188 B y x z.
Proof. exact (EQ_MP (@lem3588571 B y x z) (@lem3588462 B x y z)). Qed.
Lemma lem3588574 (b : Prop) (a : Prop) : (a \/ b) = (term191 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3588575 {B : Type'} (x : B) (y : B) (z : B) : (term188 B y x z) = (term192 B x y z).
Proof. exact (@lem3588574 (term193 B y x z) (y = z)). Qed.
Lemma lem3588577 (a : Prop) (b : Prop) : (term194 a b) = (term195 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3588578 {B : Type'} (y : B) (x : B) (z : B) : (term196 B y x z) = (term197 B y x z).
Proof. exact (@lem3588577 (term184 B x y) (term184 B x z)). Qed.
Lemma lem3588580 (a : Prop) : (term68 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3588581 {B : Type'} (x : B) (y : B) : (term198 B x y) = (x = y).
Proof. exact (@lem3588580 (x = y)). Qed.
Lemma lem3588582 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3588583 {B : Type'} (x : B) (y : B) : (term199 B x y) = (term200 B x y).
Proof. exact (MK_COMB (@lem3588582) (@lem3588581 B x y)). Qed.
Lemma lem3588585 (a : Prop) : (term68 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3588586 {B : Type'} (x : B) (z : B) : (term198 B x z) = (x = z).
Proof. exact (@lem3588585 (x = z)). Qed.
Lemma lem3588587 {B : Type'} (y : B) (x : B) (z : B) : (term197 B y x z) = (term201 B y x z).
Proof. exact (MK_COMB (@lem3588583 B x y) (@lem3588586 B x z)). Qed.
Lemma lem3588588 {B : Type'} (y : B) (x : B) (z : B) : (term196 B y x z) = (term201 B y x z).
Proof. exact (TRANS (@lem3588578 B y x z) (@lem3588587 B y x z)). Qed.
Lemma lem3588589 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3588590 {B : Type'} (y : B) (x : B) (z : B) : (term202 B y x z) = (term203 B y x z).
Proof. exact (MK_COMB (@lem3588589) (@lem3588588 B y x z)). Qed.
Lemma lem3588591 {B : Type'} (y : B) (z : B) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem3588592 {B : Type'} (x : B) (y : B) (z : B) : (term192 B x y z) = (term204 B x y z).
Proof. exact (MK_COMB (@lem3588590 B y x z) (@lem3588591 B y z)). Qed.
Lemma lem3588593 {B : Type'} (x : B) (y : B) (z : B) : (term188 B y x z) = (term204 B x y z).
Proof. exact (TRANS (@lem3588575 B x y z) (@lem3588592 B x y z)). Qed.
Lemma lem3588595 {A B : Type'} (y : B) (f : A -> B) (x : B -> A) (h1 : term291 A B f x) : term305 A B f x y.
Proof. exact (conj (@lem3588473 A B y f x h1) (@lem3588482 B y)). Qed.
Lemma lem3588597 {B : Type'} (x : B) (y : B) (z : B) : term204 B x y z.
Proof. exact (EQ_MP (@lem3588593 B x y z) (@lem3588572 B y x z)). Qed.
Lemma lem3588598 {B : Type'} (x : B) (y : B) (z : B) : term204 B x y z.
Proof. exact (@lem3588597 B x y z). Qed.
Lemma lem3588599 {A B : Type'} (f : A -> B) (x : B -> A) (y : B) : term306 A B f x y.
Proof. exact (@lem3588598 B y (term95 A B f x y) y). Qed.
Lemma lem3588602 {A B : Type'} (y : B) (f : A -> B) (x : B -> A) (h1 : term291 A B f x) : (term95 A B f x y) = y.
Proof. exact (@lem3588599 A B f x y (@lem3588595 A B y f x h1)). Qed.
Lemma lem3588603 {A B : Type'} (y : B) (f : A -> B) (x : B -> A) (h1 : term291 A B f x) : (term95 A B f x y) = y.
Proof. exact (@lem3588602 A B y f x h1). Qed.
Lemma lem3588604 {A B : Type'} (y : B) (f : A -> B) (x : B -> A) (h1 : term291 A B f x) : term178 A B f x y.
Proof. exact (fun h0 : term179 A B f x y => @lem3588603 A B y f x h1). Qed.
Lemma lem3588606 (p : Prop) : (term168 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3588607 {A B : Type'} (f : A -> B) (x : B -> A) (y : B) : (term178 A B f x y) = ((term95 A B f x y) = y).
Proof. exact (@lem3588606 ((term95 A B f x y) = y)). Qed.
Lemma lem3588608 {A B : Type'} (y : B) (f : A -> B) (x : B -> A) (h1 : term291 A B f x) : (term95 A B f x y) = y.
Proof. exact (EQ_MP (@lem3588607 A B f x y) (@lem3588604 A B y f x h1)). Qed.
Lemma lem3588611 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3588613 {A B : Type'} (f : A -> B) (_38771 : A) (y : B) : (term297 A B f _38771 y) = (term307 A B f _38771 y).
Proof. exact (@lem3588611 ((f _38771) = y)). Qed.
Lemma lem3588616 {A B : Type'} (_38771 : A) (f : A -> B) (y : B) (h1 : term274 A B f y) : term307 A B f _38771 y.
Proof. exact (EQ_MP (@lem3588613 A B f _38771 y) (@lem3588442 A B _38771 f y h1)). Qed.
Lemma lem3588617 {A B : Type'} (_38771 : A) (f : A -> B) (y : B) (h1 : term274 A B f y) : term307 A B f _38771 y.
Proof. exact (@lem3588616 A B _38771 f y h1). Qed.
Lemma lem3588618 {A B : Type'} (x : B -> A) (f : A -> B) (y : B) (h1 : term274 A B f y) : term308 A B f x y.
Proof. exact (@lem3588617 A B (x y) f y h1). Qed.
Lemma lem3588621 {A B : Type'} (x : B -> A) (f : A -> B) (y : B) (h1 : term291 A B f x) (h2 : term274 A B f y) : False.
Proof. exact (@lem3588618 A B x f y h2 (@lem3588608 A B y f x h1)). Qed.
Lemma lem3588622 {A B : Type'} (x : B -> A) (f : A -> B) (y : B) (h1 : term291 A B f x) (h2 : term274 A B f y) : term170.
Proof. exact (fun h0 : ~ False => @lem3588621 A B x f y h1 h2). Qed.
Lemma lem3588624 (p : Prop) : (term168 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3588625 : term170 = False.
Proof. exact (@lem3588624 False). Qed.
Lemma lem3588626 {A B : Type'} (x : B -> A) (f : A -> B) (y : B) (h1 : term291 A B f x) (h2 : term274 A B f y) : False.
Proof. exact (EQ_MP (@lem3588625) (@lem3588622 A B x f y h1 h2)). Qed.
Lemma lem3588627 {A B : Type'} (x : B -> A) (f : A -> B) (y : B) (h1 : term291 A B f x) (h2 : term274 A B f y) : (term291 A B f x) = False.
Proof. exact (prop_ext (fun h3 : term291 A B f x => @lem3588626 A B x f y h1 h2) (fun h3 : False => @lem3588434 A B f x h1)). Qed.
Lemma lem3588628 {A B : Type'} (x : B -> A) (f : A -> B) (y : B) (h1 : term291 A B f x) (h2 : term274 A B f y) : False.
Proof. exact (EQ_MP (@lem3588627 A B x f y h1 h2) (@lem3588434 A B f x h1)). Qed.
Lemma lem3588629 {A B : Type'} (x : B -> A) (f : A -> B) (y : B) (h1 : term291 A B f x) (h2 : term274 A B f y) : (term291 A B f x) = False.
Proof. exact (prop_ext (fun h3 : term291 A B f x => @lem3588628 A B x f y h1 h2) (fun h3 : False => @lem3588420 A B f x h1)). Qed.
Lemma lem3588630 {A B : Type'} (x : B -> A) (f : A -> B) (y : B) (h1 : term291 A B f x) (h2 : term274 A B f y) : False.
Proof. exact (EQ_MP (@lem3588629 A B x f y h1 h2) (@lem3588420 A B f x h1)). Qed.
Lemma lem3588631 {A B : Type'} (f : A -> B) (y : B) (h1 : term268 A B f) (h2 : term274 A B f y) : False.
Proof. exact (ex_elim (@lem3588373 A B f h1) (fun x : B -> A => fun h0 : term293 A B f x => @lem3588630 A B x f y h0 h2)). Qed.
Lemma lem3588632 {A B : Type'} (f : A -> B) (y : B) (h1 : term268 A B f) (h2 : term274 A B f y) : (term274 A B f y) = False.
Proof. exact (prop_ext (fun h3 : term274 A B f y => @lem3588631 A B f y h1 h2) (fun h3 : False => @lem3588324 A B f y h2)). Qed.
Lemma lem3588633 {A B : Type'} (f : A -> B) (y : B) (h1 : term268 A B f) (h2 : term274 A B f y) : False.
Proof. exact (EQ_MP (@lem3588632 A B f y h1 h2) (@lem3588324 A B f y h2)). Qed.
Lemma lem3588634 {A B : Type'} (y : B) (f : A -> B) (h1 : term268 A B f) : term273 A B f y.
Proof. exact (fun h0 : term274 A B f y => @lem3588633 A B f y h1 h0). Qed.
Lemma lem3588635 {A B : Type'} (y : B) (f : A -> B) (h1 : term268 A B f) : term74 A B f y.
Proof. exact (EQ_MP (@lem3588323 A B f y) (@lem3588634 A B y f h1)). Qed.
Lemma lem3588640 {A B : Type'} (f : A -> B) (h1 : term268 A B f) : term56 A B f.
Proof. exact (fun y : B => @lem3588635 A B y f h1). Qed.
Lemma lem3588641 {A B : Type'} (f : A -> B) : term270 A B f.
Proof. exact (fun h0 : term268 A B f => @lem3588640 A B f h0). Qed.
Lemma lem3588646 {A B : Type'} : term272 A B.
Proof. exact (fun f : A -> B => @lem3588641 A B f). Qed.
Lemma lem3588647 {A B : Type'} : term245 A B.
Proof. exact (EQ_MP (@lem3588318 A B) (@lem3588646 A B)). Qed.
Lemma lem3588648 {A B : Type'} (f : A -> B) : term309 A B f.
Proof. exact (@lem3588647 A B f). Qed.
Lemma lem3588649 {A B : Type'} (f : A -> B) : (term309 A B f) = (term237 A B f).
Proof. exact (eq_refl (term309 A B f)). Qed.
Lemma lem3588650 {A B : Type'} (f : A -> B) : term237 A B f.
Proof. exact (EQ_MP (@lem3588649 A B f) (@lem3588648 A B f)). Qed.
Lemma lem3588652 {A B : Type'} (f : A -> B) : term237 A B f.
Proof. exact (@lem3588110 A B f (@lem3588650 A B f)). Qed.
Lemma lem3588653 {A B : Type'} (f : A -> B) (h1 : term238 A B f) : False.
Proof. exact (@lem3588652 A B f (@lem3588094 A B f h1)). Qed.
Lemma lem3588654 {A B : Type'} (f : A -> B) (h1 : term238 A B f) : (term238 A B f) = False.
Proof. exact (prop_ext (fun h2 : term238 A B f => @lem3588653 A B f h1) (fun h2 : False => @lem3588094 A B f h1)). Qed.
Lemma lem3588655 {A B : Type'} (f : A -> B) (h1 : term238 A B f) : False.
Proof. exact (EQ_MP (@lem3588654 A B f h1) (@lem3588094 A B f h1)). Qed.
Lemma lem3588656 {A B : Type'} (f : A -> B) : term237 A B f.
Proof. exact (fun h0 : term238 A B f => @lem3588655 A B f h0). Qed.
Lemma lem3588657 {A B : Type'} (f : A -> B) : term236 A B f.
Proof. exact (EQ_MP (@lem3588093 A B f) (@lem3588656 A B f)). Qed.
Lemma lem3588658 {A B : Type'} (f : A -> B) (h1 : term54 A B f) : term56 A B f.
Proof. exact (@lem3588657 A B f (@lem3587000 A B f h1)). Qed.
Lemma lem3588659 {A B : Type'} (f : A -> B) : term310 A B f.
Proof. exact (fun h0 : term54 A B f => @lem3588658 A B f h0). Qed.
Lemma lem3588660 {A B : Type'} (f : A -> B) : term311 A B f.
Proof. exact (conj (@lem3588089 A B f) (@lem3588659 A B f)). Qed.
Lemma lem3588661 {A B : Type'} (f : A -> B) : (term311 A B f) = ((term56 A B f) = (term54 A B f)).
Proof. exact (@lem32 (term56 A B f) (term54 A B f)). Qed.
Lemma lem3588662 {A B : Type'} (f : A -> B) : (term56 A B f) = (term54 A B f).
Proof. exact (EQ_MP (@lem3588661 A B f) (@lem3588660 A B f)). Qed.
Lemma lem3588663 {A B : Type'} (f : A -> B) : (term56 A B f) = (term53 A B f).
Proof. exact (EQ_MP (@lem3586996 A B f) (@lem3588662 A B f)). Qed.
Lemma lem3588668 {A B : Type'} : term312 A B.
Proof. exact (fun f : A -> B => @lem3588663 A B f). Qed.
