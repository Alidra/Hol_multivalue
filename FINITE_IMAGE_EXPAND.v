Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_IMAGE_EXPAND_term_abbrevs.
Require Import EXTENSION_spec.
Require Import FINITE_INDUCT_spec.
Require Import FINITE_INSERT_spec.
Require Import FINITE_RULES_spec.
Require Import FINITE_UNION_spec.
Require Import IN_INSERT_spec.
Require Import IN_UNION_spec.
Require Import NOT_IN_EMPTY_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17646_spec.
Require Import thm1812_spec.
Require Import thm1813_spec.
Require Import thm1823_spec.
Require Import thm1834_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1844_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19699_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Require Import thm3399706_spec.
Require Import thm3399757_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem3612904 {A : Type'} : @FINITE A (@EMPTY A).
Proof. exact (proj1 (@lem3197565 A)). Qed.
Lemma lem3612905 {A : Type'} : (@FINITE A (@EMPTY A)) = ((@FINITE A (@EMPTY A)) = True).
Proof. exact (@lem7 (@FINITE A (@EMPTY A))). Qed.
Lemma lem3612907 {A : Type'} (s : A -> Prop) : term0 A s.
Proof. exact (@lem3608316 A s). Qed.
Lemma lem3612908 {A : Type'} (s : A -> Prop) : (term0 A s) = (term1 A s).
Proof. exact (eq_refl (term0 A s)). Qed.
Lemma lem3612909 {A : Type'} (s : A -> Prop) : term1 A s.
Proof. exact (EQ_MP (@lem3612908 A s) (@lem3612907 A s)). Qed.
Lemma lem3612910 {A : Type'} (s : A -> Prop) (x : A) : term2 A s x.
Proof. exact (@lem3612909 A s x). Qed.
Lemma lem3612911 {A : Type'} (x : A) (s : A -> Prop) : (term2 A s x) = ((term3 A x s) = (@FINITE A s)).
Proof. exact (eq_refl (term2 A s x)). Qed.
Lemma lem3612913 {A : Type'} (s : A -> Prop) : term4 A s.
Proof. exact (@lem3606772 A s). Qed.
Lemma lem3612914 {A : Type'} (s : A -> Prop) : (term4 A s) = (term5 A s).
Proof. exact (eq_refl (term4 A s)). Qed.
Lemma lem3612915 {A : Type'} (s : A -> Prop) : term5 A s.
Proof. exact (EQ_MP (@lem3612914 A s) (@lem3612913 A s)). Qed.
Lemma lem3612916 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term6 A s t.
Proof. exact (@lem3612915 A s t). Qed.
Lemma lem3612917 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term6 A s t) = ((term7 A s t) = (term8 A s t)).
Proof. exact (eq_refl (term6 A s t)). Qed.
Lemma lem3612929 {A : Type'} (x : A) : term9 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem3612930 {A : Type'} (x : A) : (term9 A x) = (term10 A x).
Proof. exact (eq_refl (term9 A x)). Qed.
Lemma lem3612931 {A : Type'} (x : A) : term10 A x.
Proof. exact (EQ_MP (@lem3612930 A x) (@lem3612929 A x)). Qed.
Lemma lem3612932 {A : Type'} (x : A) : term11 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem3612934 {A : Type'} (s : A -> Prop) : term12 A s.
Proof. exact (@lem3204949 A s). Qed.
Lemma lem3612935 {A : Type'} (s : A -> Prop) : (term12 A s) = (term13 A s).
Proof. exact (eq_refl (term12 A s)). Qed.
Lemma lem3612936 {A : Type'} (s : A -> Prop) : term13 A s.
Proof. exact (EQ_MP (@lem3612935 A s) (@lem3612934 A s)). Qed.
Lemma lem3612937 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term14 A s t.
Proof. exact (@lem3612936 A s t). Qed.
Lemma lem3612938 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term14 A s t) = (term15 A s t).
Proof. exact (eq_refl (term14 A s t)). Qed.
Lemma lem3612939 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term15 A s t.
Proof. exact (EQ_MP (@lem3612938 A s t) (@lem3612937 A s t)). Qed.
Lemma lem3612940 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : term16 A s t x.
Proof. exact (@lem3612939 A s t x). Qed.
Lemma lem3612941 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term16 A s t x) = ((term17 A x s t) = (term18 A s x t)).
Proof. exact (eq_refl (term16 A s t x)). Qed.
Lemma lem3612943 {A : Type'} (x : A) : term19 A x.
Proof. exact (@lem3205665 A x). Qed.
Lemma lem3612944 {A : Type'} (x : A) : (term19 A x) = (term20 A x).
Proof. exact (eq_refl (term19 A x)). Qed.
Lemma lem3612945 {A : Type'} (x : A) : term20 A x.
Proof. exact (EQ_MP (@lem3612944 A x) (@lem3612943 A x)). Qed.
Lemma lem3612946 {A : Type'} (x : A) (y : A) : term21 A x y.
Proof. exact (@lem3612945 A x y). Qed.
Lemma lem3612947 {A : Type'} (y : A) (x : A) : (term21 A x y) = (term22 A y x).
Proof. exact (eq_refl (term21 A x y)). Qed.
Lemma lem3612948 {A : Type'} (y : A) (x : A) : term22 A y x.
Proof. exact (EQ_MP (@lem3612947 A y x) (@lem3612946 A x y)). Qed.
Lemma lem3612949 {A : Type'} (y : A) (x : A) (s : A -> Prop) : term23 A y x s.
Proof. exact (@lem3612948 A y x s). Qed.
Lemma lem3612950 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term23 A y x s) = ((term24 A x y s) = (term25 A y x s)).
Proof. exact (eq_refl (term23 A y x s)). Qed.
Lemma lem3612976 {_83095 : Type'} : term26 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem3612977 {_83095 : Type'} (p : _83095 -> Prop) : term27 _83095 p.
Proof. exact (@lem3612976 _83095 p). Qed.
Lemma lem3612978 {_83095 : Type'} (p : _83095 -> Prop) : (term27 _83095 p) = (term28 _83095 p).
Proof. exact (eq_refl (term27 _83095 p)). Qed.
Lemma lem3612979 {_83095 : Type'} (p : _83095 -> Prop) : term28 _83095 p.
Proof. exact (EQ_MP (@lem3612978 _83095 p) (@lem3612977 _83095 p)). Qed.
Lemma lem3612980 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term29 _83095 p x.
Proof. exact (@lem3612979 _83095 p x). Qed.
Lemma lem3612981 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term29 _83095 p x) = ((term30 _83095 x p) = (p x)).
Proof. exact (eq_refl (term29 _83095 p x)). Qed.
Lemma lem3612990 {A : Type'} (s : A -> Prop) : term31 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem3612991 {A : Type'} (s : A -> Prop) : (term31 A s) = (term32 A s).
Proof. exact (eq_refl (term31 A s)). Qed.
Lemma lem3612992 {A : Type'} (s : A -> Prop) : term32 A s.
Proof. exact (EQ_MP (@lem3612991 A s) (@lem3612990 A s)). Qed.
Lemma lem3612993 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term33 A s t.
Proof. exact (@lem3612992 A s t). Qed.
Lemma lem3612994 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term33 A s t) = ((s = t) = (term34 A s t)).
Proof. exact (eq_refl (term33 A s t)). Qed.
Lemma lem3613013 {A : Type'} : @FINITE A (@EMPTY A).
Proof. exact (proj1 (@lem3197565 A)). Qed.
Lemma lem3613014 {A : Type'} : (@FINITE A (@EMPTY A)) = ((@FINITE A (@EMPTY A)) = True).
Proof. exact (@lem7 (@FINITE A (@EMPTY A))). Qed.
Lemma lem3613016 {A : Type'} (x : A) : term9 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem3613017 {A : Type'} (x : A) : (term9 A x) = (term10 A x).
Proof. exact (eq_refl (term9 A x)). Qed.
Lemma lem3613018 {A : Type'} (x : A) : term10 A x.
Proof. exact (EQ_MP (@lem3613017 A x) (@lem3613016 A x)). Qed.
Lemma lem3613019 {A : Type'} (x : A) : term11 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem3613021 {A : Type'} (h1 : term35 A) : term35 A.
Proof. exact (h1). Qed.
Lemma lem3613022 {A : Type'} (FINITE' : type686 A) (h1 : term35 A) : term36 A FINITE'.
Proof. exact (@lem3613021 A h1 FINITE'). Qed.
Lemma lem3613023 {A : Type'} (FINITE' : type686 A) : (term36 A FINITE') = (term37 A FINITE').
Proof. exact (eq_refl (term36 A FINITE')). Qed.
Lemma lem3613024 {A : Type'} (FINITE' : type686 A) (h1 : term35 A) : term37 A FINITE'.
Proof. exact (EQ_MP (@lem3613023 A FINITE') (@lem3613022 A FINITE' h1)). Qed.
Lemma lem3613025 {A : Type'} (FINITE' : type686 A) (h1 : term38 A FINITE') : term38 A FINITE'.
Proof. exact (h1). Qed.
Lemma lem3613026 {A : Type'} (FINITE' : type686 A) (h1 : term35 A) (h2 : term38 A FINITE') : term39 A FINITE'.
Proof. exact (@lem3613024 A FINITE' h1 (@lem3613025 A FINITE' h2)). Qed.
Lemma lem3613027 {A : Type'} (FINITE' : type686 A) (h1 : term38 A FINITE') : term40 A FINITE'.
Proof. exact (fun h0 : term35 A => @lem3613026 A FINITE' h0 h1). Qed.
Lemma lem3613028 {A : Type'} (h1 : term35 A) : term35 A.
Proof. exact (h1). Qed.
Lemma lem3613029 {A : Type'} (FINITE' : type686 A) (h1 : term35 A) (h2 : term38 A FINITE') : term39 A FINITE'.
Proof. exact (@lem3613027 A FINITE' h2 (@lem3613028 A h1)). Qed.
Lemma lem3613030 {A : Type'} (FINITE' : type686 A) (h1 : term35 A) : term37 A FINITE'.
Proof. exact (fun h0 : term38 A FINITE' => @lem3613029 A FINITE' h1 h0). Qed.
Lemma lem3613031 {A : Type'} (h1 : term35 A) : term35 A.
Proof. exact (fun FINITE' : type686 A => @lem3613030 A FINITE' h1). Qed.
Lemma lem3613032 {A : Type'} : term41 A.
Proof. exact (fun h0 : term35 A => @lem3613031 A h0). Qed.
Lemma lem3613033 {A : Type'} : term35 A.
Proof. exact (@lem3613032 A (@lem3197567 A)). Qed.
Lemma lem3613034 {A : Type'} (FINITE' : type686 A) : term36 A FINITE'.
Proof. exact (@lem3613033 A FINITE'). Qed.
Lemma lem3613035 {A : Type'} (FINITE' : type686 A) : (term36 A FINITE') = (term37 A FINITE').
Proof. exact (eq_refl (term36 A FINITE')). Qed.
Lemma lem3613038 {A : Type'} (FINITE' : type686 A) : term37 A FINITE'.
Proof. exact (EQ_MP (@lem3613035 A FINITE') (@lem3613034 A FINITE')). Qed.
Lemma lem3613039 {A : Type'} (FINITE' : type686 A) : term37 A FINITE'.
Proof. exact (@lem3613038 A FINITE'). Qed.
Lemma lem3613040 {A B : Type'} (f : A -> B) : term42 A B f.
Proof. exact (@lem3613039 A (term43 A B f)). Qed.
Lemma lem3613041 {A B : Type'} (f : A -> B) : (term44 A B f) = (term45 A B f).
Proof. exact (eq_refl (term44 A B f)). Qed.
Lemma lem3613042 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3613043 {A B : Type'} (f : A -> B) : (term46 A B f) = (term47 A B f).
Proof. exact (MK_COMB (@lem3613042) (@lem3613041 A B f)). Qed.
Lemma lem3613044 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term48 A B f s) = (term49 A B s f).
Proof. exact (eq_refl (term48 A B f s)). Qed.
Lemma lem3613045 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3613046 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term50 A B f s) = (term51 A B s f).
Proof. exact (MK_COMB (@lem3613045) (@lem3613044 A B s f)). Qed.
Lemma lem3613047 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) : (term52 A B f x s) = (term53 A B x s f).
Proof. exact (eq_refl (term52 A B f x s)). Qed.
Lemma lem3613048 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) : (term54 A B f x s) = (term55 A B x s f).
Proof. exact (MK_COMB (@lem3613046 A B s f) (@lem3613047 A B x s f)). Qed.
Lemma lem3613049 {A B : Type'} (x : A) (f : A -> B) : (term56 A B f x) = (term57 A B x f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3613048 A B x s f)). Qed.
Lemma lem3613050 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3613051 {A B : Type'} (x : A) (f : A -> B) : (term58 A B f x) = (term59 A B x f).
Proof. exact (MK_COMB (@lem3613050 A) (@lem3613049 A B x f)). Qed.
Lemma lem3613052 {A B : Type'} (f : A -> B) : (term60 A B f) = (term61 A B f).
Proof. exact (fun_ext (fun x : A => @lem3613051 A B x f)). Qed.
Lemma lem3613053 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3613054 {A B : Type'} (f : A -> B) : (term62 A B f) = (term63 A B f).
Proof. exact (MK_COMB (@lem3613053 A) (@lem3613052 A B f)). Qed.
Lemma lem3613055 {A B : Type'} (f : A -> B) : (term64 A B f) = (term65 A B f).
Proof. exact (MK_COMB (@lem3613043 A B f) (@lem3613054 A B f)). Qed.
Lemma lem3613056 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3613057 {A B : Type'} (f : A -> B) : (term66 A B f) = (term67 A B f).
Proof. exact (MK_COMB (@lem3613056) (@lem3613055 A B f)). Qed.
Lemma lem3613058 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term48 A B f s) = (term49 A B s f).
Proof. exact (eq_refl (term48 A B f s)). Qed.
Lemma lem3613059 {A : Type'} (s : A -> Prop) : (term68 A s) = (term68 A s).
Proof. exact (eq_refl (term68 A s)). Qed.
Lemma lem3613060 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term69 A B f s) = (term70 A B s f).
Proof. exact (MK_COMB (@lem3613059 A s) (@lem3613058 A B s f)). Qed.
Lemma lem3613061 {A B : Type'} (f : A -> B) : (term71 A B f) = (term72 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3613060 A B s f)). Qed.
Lemma lem3613062 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3613063 {A B : Type'} (f : A -> B) : (term73 A B f) = (term74 A B f).
Proof. exact (MK_COMB (@lem3613062 A) (@lem3613061 A B f)). Qed.
Lemma lem3613064 {A B : Type'} (f : A -> B) : (term42 A B f) = (term75 A B f).
Proof. exact (MK_COMB (@lem3613057 A B f) (@lem3613063 A B f)). Qed.
Lemma lem3613065 {A B : Type'} (f : A -> B) : term75 A B f.
Proof. exact (EQ_MP (@lem3613064 A B f) (@lem3613040 A B f)). Qed.
Lemma lem3613079 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3613019 A x (@lem3613018 A x)). Qed.
Lemma lem3613080 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3613079 A x). Qed.
Lemma lem3613081 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3613082 {A : Type'} (x : A) : (term76 A x) = (and False).
Proof. exact (MK_COMB (@lem3613081) (@lem3613080 A x)). Qed.
Lemma lem3613085 {A B : Type'} (y : B) (f : A -> B) (x : A) : (y = (f x)) = (y = (f x)).
Proof. exact (eq_refl (y = (f x))). Qed.
Lemma lem3613086 {A B : Type'} (y : B) (f : A -> B) (x : A) : (term77 A B y f x) = (term78 A B y f x).
Proof. exact (MK_COMB (@lem3613082 A x) (@lem3613085 A B y f x)). Qed.
Lemma lem3613088 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem3613089 {A B : Type'} (y : B) (f : A -> B) (x : A) : (term78 A B y f x) = False.
Proof. exact (@lem3613088 (y = (f x))). Qed.
Lemma lem3613090 {A B : Type'} (y : B) (f : A -> B) (x : A) : (term77 A B y f x) = False.
Proof. exact (TRANS (@lem3613086 A B y f x) (@lem3613089 A B y f x)). Qed.
Lemma lem3613091 {A B : Type'} (y : B) (f : A -> B) : (term79 A B y f) = (term80 A).
Proof. exact (fun_ext (fun x : A => @lem3613090 A B y f x)). Qed.
Lemma lem3613092 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3613093 {A B : Type'} (y : B) (f : A -> B) : (term81 A B y f) = (term82 A).
Proof. exact (MK_COMB (@lem3613092 A) (@lem3613091 A B y f)). Qed.
Lemma lem3613095 {A : Type'} (t : Prop) : (term83 A t) = t.
Proof. exact (EQ_MP (@lem1813 A t) (@lem1812 A t)). Qed.
Lemma lem3613096 {A : Type'} (t : Prop) : (term83 A t) = t.
Proof. exact (@lem3613095 A t). Qed.
Lemma lem3613097 {A : Type'} : (term82 A) = False.
Proof. exact (@lem3613096 A False). Qed.
Lemma lem3613098 {A B : Type'} (y : B) (f : A -> B) : (term81 A B y f) = False.
Proof. exact (TRANS (@lem3613093 A B y f) (@lem3613097 A)). Qed.
Lemma lem3613099 {B : Type'} (GEN_PVAR_94 : B) : (@SETSPEC B GEN_PVAR_94) = (@SETSPEC B GEN_PVAR_94).
Proof. exact (eq_refl (@SETSPEC B GEN_PVAR_94)). Qed.
Lemma lem3613100 {A B : Type'} (y : B) (f : A -> B) (GEN_PVAR_94 : B) : (term84 A B GEN_PVAR_94 y f) = (@SETSPEC B GEN_PVAR_94 False).
Proof. exact (MK_COMB (@lem3613099 B GEN_PVAR_94) (@lem3613098 A B y f)). Qed.
Lemma lem3613101 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem3613102 {A B : Type'} (f : A -> B) (GEN_PVAR_94 : B) (y : B) : (term85 A B GEN_PVAR_94 f y) = (@SETSPEC B GEN_PVAR_94 False y).
Proof. exact (MK_COMB (@lem3613100 A B y f GEN_PVAR_94) (@lem3613101 B y)). Qed.
Lemma lem3613103 {A B : Type'} (f : A -> B) (GEN_PVAR_94 : B) : (term86 A B GEN_PVAR_94 f) = (term87 B GEN_PVAR_94).
Proof. exact (fun_ext (fun y : B => @lem3613102 A B f GEN_PVAR_94 y)). Qed.
Lemma lem3613104 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3613105 {A B : Type'} (f : A -> B) (GEN_PVAR_94 : B) : (term88 A B GEN_PVAR_94 f) = (term89 B GEN_PVAR_94).
Proof. exact (MK_COMB (@lem3613104 B) (@lem3613103 A B f GEN_PVAR_94)). Qed.
Lemma lem3613110 {A B : Type'} (f : A -> B) : (term90 A B f) = (term91 B).
Proof. exact (fun_ext (fun GEN_PVAR_94 : B => @lem3613105 A B f GEN_PVAR_94)). Qed.
Lemma lem3613111 {B : Type'} : (@GSPEC B) = (@GSPEC B).
Proof. exact (eq_refl (@GSPEC B)). Qed.
Lemma lem3613112 {A B : Type'} (f : A -> B) : (term92 A B f) = (term93 B).
Proof. exact (MK_COMB (@lem3613111 B) (@lem3613110 A B f)). Qed.
Lemma lem3613114 {_88295 : Type'} : (term93 _88295) = (@EMPTY _88295).
Proof. exact (EQ_MP (@lem3399706 _88295) (@lem3399757 _88295)). Qed.
Lemma lem3613115 {B : Type'} : (term93 B) = (@EMPTY B).
Proof. exact (@lem3613114 B). Qed.
Lemma lem3613116 {A B : Type'} (f : A -> B) : (term92 A B f) = (@EMPTY B).
Proof. exact (TRANS (@lem3613112 A B f) (@lem3613115 B)). Qed.
Lemma lem3613117 {B : Type'} : (@FINITE B) = (@FINITE B).
Proof. exact (eq_refl (@FINITE B)). Qed.
Lemma lem3613118 {A B : Type'} (f : A -> B) : (term45 A B f) = (@FINITE B (@EMPTY B)).
Proof. exact (MK_COMB (@lem3613117 B) (@lem3613116 A B f)). Qed.
Lemma lem3613120 {A : Type'} : (@FINITE A (@EMPTY A)) = True.
Proof. exact (EQ_MP (@lem3613014 A) (@lem3613013 A)). Qed.
Lemma lem3613121 {B : Type'} : (@FINITE B (@EMPTY B)) = True.
Proof. exact (@lem3613120 B). Qed.
Lemma lem3613122 {A B : Type'} (f : A -> B) : (term45 A B f) = True.
Proof. exact (TRANS (@lem3613118 A B f) (@lem3613121 B)). Qed.
Lemma lem3613123 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3613124 {A B : Type'} (f : A -> B) : (term47 A B f) = (and True).
Proof. exact (MK_COMB (@lem3613123) (@lem3613122 A B f)). Qed.
Lemma lem3613159 {A B : Type'} (f : A -> B) : (term63 A B f) = (term63 A B f).
Proof. exact (eq_refl (term63 A B f)). Qed.
Lemma lem3613160 {A B : Type'} (f : A -> B) : (term65 A B f) = (term94 A B f).
Proof. exact (MK_COMB (@lem3613124 A B f) (@lem3613159 A B f)). Qed.
Lemma lem3613162 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3613163 {A B : Type'} (f : A -> B) : (term94 A B f) = (term63 A B f).
Proof. exact (@lem3613162 (term63 A B f)). Qed.
Lemma lem3613198 {A B : Type'} (f : A -> B) : (term65 A B f) = (term63 A B f).
Proof. exact (TRANS (@lem3613160 A B f) (@lem3613163 A B f)). Qed.
Lemma lem3613199 {A B : Type'} (f : A -> B) : (term63 A B f) = (term65 A B f).
Proof. exact (SYM (@lem3613198 A B f)). Qed.
Lemma lem3613216 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : (term95 A B x s f) = (term96 A B s f x)) : (term95 A B x s f) = (term96 A B s f x).
Proof. exact (h1). Qed.
Lemma lem3613217 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : (term95 A B x s f) = (term96 A B s f x)) : (term95 A B x s f) = (term96 A B s f x).
Proof. exact (@lem3613216 A B s f x h1). Qed.
Lemma lem3613230 {B : Type'} : (@FINITE B) = (@FINITE B).
Proof. exact (eq_refl (@FINITE B)). Qed.
Lemma lem3613231 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : (term95 A B x s f) = (term96 A B s f x)) : (term53 A B x s f) = (term97 A B s f x).
Proof. exact (MK_COMB (@lem3613230 B) (@lem3613217 A B s f x h1)). Qed.
Lemma lem3613232 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term51 A B s f) = (term51 A B s f).
Proof. exact (eq_refl (term51 A B s f)). Qed.
Lemma lem3613233 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : (term95 A B x s f) = (term96 A B s f x)) : (term55 A B x s f) = (term98 A B s f x).
Proof. exact (MK_COMB (@lem3613232 A B s f) (@lem3613231 A B s f x h1)). Qed.
Lemma lem3613236 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : (term95 A B x s f) = (term96 A B s f x)) : (term98 A B s f x) = (term55 A B x s f).
Proof. exact (SYM (@lem3613233 A B s f x h1)). Qed.
Lemma lem3613240 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term34 A s t).
Proof. exact (EQ_MP (@lem3612994 A s t) (@lem3612993 A s t)). Qed.
Lemma lem3613241 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (s = t) = (term34 B s t).
Proof. exact (@lem3613240 B s t). Qed.
Lemma lem3613242 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : ((term95 A B x s f) = (term96 A B s f x)) = (term99 A B s f x).
Proof. exact (@lem3613241 B (term95 A B x s f) (term96 A B s f x)). Qed.
Lemma lem3613252 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term30 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3612981 _83095 p x) (@lem3612980 _83095 p x)). Qed.
Lemma lem3613253 {B : Type'} (p : B -> Prop) (x : B) : (term30 B x p) = (p x).
Proof. exact (@lem3613252 B p x). Qed.
Lemma lem3613254 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (x' : B) : (term100 A B x' x s f) = (term101 A B x s f x').
Proof. exact (@lem3613253 B (term102 A B x s f) x'). Qed.
Lemma lem3613255 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) : (term101 A B x s f y) = (term103 A B x s y f).
Proof. exact (eq_refl (term101 A B x s f y)). Qed.
Lemma lem3613256 {B : Type'} (GEN_PVAR_92 : B) : (@SETSPEC B GEN_PVAR_92) = (@SETSPEC B GEN_PVAR_92).
Proof. exact (eq_refl (@SETSPEC B GEN_PVAR_92)). Qed.
Lemma lem3613257 {A B : Type'} (GEN_PVAR_92 : B) (x : A) (s : A -> Prop) (y : B) (f : A -> B) : (term104 A B GEN_PVAR_92 x s f y) = (term105 A B GEN_PVAR_92 x s y f).
Proof. exact (MK_COMB (@lem3613256 B GEN_PVAR_92) (@lem3613255 A B x s y f)). Qed.
Lemma lem3613258 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem3613259 {A B : Type'} (GEN_PVAR_92 : B) (x : A) (s : A -> Prop) (f : A -> B) (y : B) : (term106 A B GEN_PVAR_92 x s f y) = (term107 A B GEN_PVAR_92 x s f y).
Proof. exact (MK_COMB (@lem3613257 A B GEN_PVAR_92 x s y f) (@lem3613258 B y)). Qed.
Lemma lem3613260 {A B : Type'} (GEN_PVAR_92 : B) (x : A) (s : A -> Prop) (f : A -> B) : (term108 A B GEN_PVAR_92 x s f) = (term109 A B GEN_PVAR_92 x s f).
Proof. exact (fun_ext (fun y : B => @lem3613259 A B GEN_PVAR_92 x s f y)). Qed.
Lemma lem3613261 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3613262 {A B : Type'} (GEN_PVAR_92 : B) (x : A) (s : A -> Prop) (f : A -> B) : (term110 A B GEN_PVAR_92 x s f) = (term111 A B GEN_PVAR_92 x s f).
Proof. exact (MK_COMB (@lem3613261 B) (@lem3613260 A B GEN_PVAR_92 x s f)). Qed.
Lemma lem3613263 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) : (term112 A B x s f) = (term113 A B x s f).
Proof. exact (fun_ext (fun GEN_PVAR_92 : B => @lem3613262 A B GEN_PVAR_92 x s f)). Qed.
Lemma lem3613264 {B : Type'} : (@GSPEC B) = (@GSPEC B).
Proof. exact (eq_refl (@GSPEC B)). Qed.
Lemma lem3613265 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) : (term114 A B x s f) = (term95 A B x s f).
Proof. exact (MK_COMB (@lem3613264 B) (@lem3613263 A B x s f)). Qed.
Lemma lem3613266 {B : Type'} (x : B) : (@IN B x) = (@IN B x).
Proof. exact (eq_refl (@IN B x)). Qed.
Lemma lem3613267 {A B : Type'} (x : B) (x' : A) (s : A -> Prop) (f : A -> B) : (term100 A B x x' s f) = (term115 A B x x' s f).
Proof. exact (MK_COMB (@lem3613266 B x) (@lem3613265 A B x' s f)). Qed.
Lemma lem3613268 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3613269 {A B : Type'} (x : B) (x' : A) (s : A -> Prop) (f : A -> B) : (term116 A B x x' s f) = (term117 A B x x' s f).
Proof. exact (MK_COMB (@lem3613268) (@lem3613267 A B x x' s f)). Qed.
Lemma lem3613270 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) : (term101 A B x s f x') = (term103 A B x s x' f).
Proof. exact (eq_refl (term101 A B x s f x')). Qed.
Lemma lem3613271 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) : ((term100 A B x' x s f) = (term101 A B x s f x')) = ((term115 A B x' x s f) = (term103 A B x s x' f)).
Proof. exact (MK_COMB (@lem3613269 A B x' x s f) (@lem3613270 A B x s x' f)). Qed.
Lemma lem3613272 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) : (term115 A B x' x s f) = (term103 A B x s x' f).
Proof. exact (EQ_MP (@lem3613271 A B x s x' f) (@lem3613254 A B x s f x')). Qed.
Lemma lem3613280 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term24 A x y s) = (term25 A y x s).
Proof. exact (EQ_MP (@lem3612950 A y x s) (@lem3612949 A y x s)). Qed.
Lemma lem3613281 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term24 A x y s) = (term25 A y x s).
Proof. exact (@lem3613280 A y x s). Qed.
Lemma lem3613282 {A : Type'} (x : A) (z : A) (s : A -> Prop) : (term24 A z x s) = (term25 A x z s).
Proof. exact (@lem3613281 A x z s). Qed.
Lemma lem3613289 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3613290 {A : Type'} (x : A) (z : A) (s : A -> Prop) : (term118 A z x s) = (term119 A x z s).
Proof. exact (MK_COMB (@lem3613289) (@lem3613282 A x z s)). Qed.
Lemma lem3613295 {A B : Type'} (x : B) (f : A -> B) (z : A) : (x = (f z)) = (x = (f z)).
Proof. exact (eq_refl (x = (f z))). Qed.
Lemma lem3613296 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (z : A) : (term120 A B x s x' f z) = (term121 A B x s x' f z).
Proof. exact (MK_COMB (@lem3613290 A x z s) (@lem3613295 A B x' f z)). Qed.
Lemma lem3613299 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) : (term122 A B x s x' f) = (term123 A B x s x' f).
Proof. exact (fun_ext (fun z : A => @lem3613296 A B x s x' f z)). Qed.
Lemma lem3613300 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3613301 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) : (term103 A B x s x' f) = (term124 A B x s x' f).
Proof. exact (MK_COMB (@lem3613300 A) (@lem3613299 A B x s x' f)). Qed.
Lemma lem3613306 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) : (term115 A B x' x s f) = (term124 A B x s x' f).
Proof. exact (TRANS (@lem3613272 A B x s x' f) (@lem3613301 A B x s x' f)). Qed.
Lemma lem3613307 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3613308 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) : (term117 A B x' x s f) = (term125 A B x s x' f).
Proof. exact (MK_COMB (@lem3613307) (@lem3613306 A B x s x' f)). Qed.
Lemma lem3613310 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term17 A x s t) = (term18 A s x t).
Proof. exact (EQ_MP (@lem3612941 A s x t) (@lem3612940 A s t x)). Qed.
Lemma lem3613311 {B : Type'} (s : B -> Prop) (x : B) (t : B -> Prop) : (term17 B x s t) = (term18 B s x t).
Proof. exact (@lem3613310 B s x t). Qed.
Lemma lem3613312 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (x' : A) : (term126 A B x s f x') = (term127 A B s x f x').
Proof. exact (@lem3613311 B (term128 A B s f) x (term129 A B f x')). Qed.
Lemma lem3613316 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term30 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3612981 _83095 p x) (@lem3612980 _83095 p x)). Qed.
Lemma lem3613317 {B : Type'} (p : B -> Prop) (x : B) : (term30 B x p) = (p x).
Proof. exact (@lem3613316 B p x). Qed.
Lemma lem3613318 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) : (term130 A B x s f) = (term131 A B s f x).
Proof. exact (@lem3613317 B (term132 A B s f) x). Qed.
Lemma lem3613319 {A B : Type'} (s : A -> Prop) (y : B) (f : A -> B) : (term131 A B s f y) = (term133 A B s y f).
Proof. exact (eq_refl (term131 A B s f y)). Qed.
Lemma lem3613320 {B : Type'} (GEN_PVAR_93 : B) : (@SETSPEC B GEN_PVAR_93) = (@SETSPEC B GEN_PVAR_93).
Proof. exact (eq_refl (@SETSPEC B GEN_PVAR_93)). Qed.
Lemma lem3613321 {A B : Type'} (GEN_PVAR_93 : B) (s : A -> Prop) (y : B) (f : A -> B) : (term134 A B GEN_PVAR_93 s f y) = (term135 A B GEN_PVAR_93 s y f).
Proof. exact (MK_COMB (@lem3613320 B GEN_PVAR_93) (@lem3613319 A B s y f)). Qed.
Lemma lem3613322 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem3613323 {A B : Type'} (GEN_PVAR_93 : B) (s : A -> Prop) (f : A -> B) (y : B) : (term136 A B GEN_PVAR_93 s f y) = (term137 A B GEN_PVAR_93 s f y).
Proof. exact (MK_COMB (@lem3613321 A B GEN_PVAR_93 s y f) (@lem3613322 B y)). Qed.
Lemma lem3613324 {A B : Type'} (GEN_PVAR_93 : B) (s : A -> Prop) (f : A -> B) : (term138 A B GEN_PVAR_93 s f) = (term139 A B GEN_PVAR_93 s f).
Proof. exact (fun_ext (fun y : B => @lem3613323 A B GEN_PVAR_93 s f y)). Qed.
Lemma lem3613325 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3613326 {A B : Type'} (GEN_PVAR_93 : B) (s : A -> Prop) (f : A -> B) : (term140 A B GEN_PVAR_93 s f) = (term141 A B GEN_PVAR_93 s f).
Proof. exact (MK_COMB (@lem3613325 B) (@lem3613324 A B GEN_PVAR_93 s f)). Qed.
Lemma lem3613327 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term142 A B s f) = (term143 A B s f).
Proof. exact (fun_ext (fun GEN_PVAR_93 : B => @lem3613326 A B GEN_PVAR_93 s f)). Qed.
Lemma lem3613328 {B : Type'} : (@GSPEC B) = (@GSPEC B).
Proof. exact (eq_refl (@GSPEC B)). Qed.
Lemma lem3613329 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term144 A B s f) = (term128 A B s f).
Proof. exact (MK_COMB (@lem3613328 B) (@lem3613327 A B s f)). Qed.
Lemma lem3613330 {B : Type'} (x : B) : (@IN B x) = (@IN B x).
Proof. exact (eq_refl (@IN B x)). Qed.
Lemma lem3613331 {A B : Type'} (x : B) (s : A -> Prop) (f : A -> B) : (term130 A B x s f) = (term145 A B x s f).
Proof. exact (MK_COMB (@lem3613330 B x) (@lem3613329 A B s f)). Qed.
Lemma lem3613332 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3613333 {A B : Type'} (x : B) (s : A -> Prop) (f : A -> B) : (term146 A B x s f) = (term147 A B x s f).
Proof. exact (MK_COMB (@lem3613332) (@lem3613331 A B x s f)). Qed.
Lemma lem3613334 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) : (term131 A B s f x) = (term133 A B s x f).
Proof. exact (eq_refl (term131 A B s f x)). Qed.
Lemma lem3613335 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) : ((term130 A B x s f) = (term131 A B s f x)) = ((term145 A B x s f) = (term133 A B s x f)).
Proof. exact (MK_COMB (@lem3613333 A B x s f) (@lem3613334 A B s x f)). Qed.
Lemma lem3613336 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) : (term145 A B x s f) = (term133 A B s x f).
Proof. exact (EQ_MP (@lem3613335 A B s x f) (@lem3613318 A B s f x)). Qed.
Lemma lem3613347 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3613348 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) : (term148 A B x s f) = (term149 A B s x f).
Proof. exact (MK_COMB (@lem3613347) (@lem3613336 A B s x f)). Qed.
Lemma lem3613350 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term24 A x y s) = (term25 A y x s).
Proof. exact (EQ_MP (@lem3612950 A y x s) (@lem3612949 A y x s)). Qed.
Lemma lem3613351 {B : Type'} (y : B) (x : B) (s : B -> Prop) : (term24 B x y s) = (term25 B y x s).
Proof. exact (@lem3613350 B y x s). Qed.
Lemma lem3613352 {A B : Type'} (f : A -> B) (x : A) (x' : B) : (term150 A B x' f x) = (term151 A B f x x').
Proof. exact (@lem3613351 B (f x) x' (@EMPTY B)). Qed.
Lemma lem3613360 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3612932 A x (@lem3612931 A x)). Qed.
Lemma lem3613361 {B : Type'} (x : B) : (@IN B x (@EMPTY B)) = False.
Proof. exact (@lem3613360 B x). Qed.
Lemma lem3613362 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term152 A B x f x') = (term152 A B x f x').
Proof. exact (eq_refl (term152 A B x f x')). Qed.
Lemma lem3613363 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term151 A B f x' x) = (term153 A B x f x').
Proof. exact (MK_COMB (@lem3613362 A B x f x') (@lem3613361 B x)). Qed.
Lemma lem3613365 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem3613366 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term153 A B x f x') = (x = (f x')).
Proof. exact (@lem3613365 (x = (f x'))). Qed.
Lemma lem3613371 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term151 A B f x' x) = (x = (f x')).
Proof. exact (TRANS (@lem3613363 A B x f x') (@lem3613366 A B x f x')). Qed.
Lemma lem3613372 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term150 A B x f x') = (x = (f x')).
Proof. exact (TRANS (@lem3613352 A B f x' x) (@lem3613371 A B x f x')). Qed.
Lemma lem3613373 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (x' : A) : (term127 A B s x f x') = (term154 A B s x f x').
Proof. exact (MK_COMB (@lem3613348 A B s x f) (@lem3613372 A B x f x')). Qed.
Lemma lem3613376 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (x' : A) : (term126 A B x s f x') = (term154 A B s x f x').
Proof. exact (TRANS (@lem3613312 A B s x f x') (@lem3613373 A B s x f x')). Qed.
Lemma lem3613377 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (x' : A) : ((term115 A B x x' s f) = (term126 A B x s f x')) = ((term124 A B x' s x f) = (term154 A B s x f x')).
Proof. exact (MK_COMB (@lem3613308 A B x' s x f) (@lem3613376 A B s x f x')). Qed.
Lemma lem3613382 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term155 A B s f x) = (term156 A B s f x).
Proof. exact (fun_ext (fun x' : B => @lem3613377 A B s x' f x)). Qed.
Lemma lem3613383 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3613384 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term99 A B s f x) = (term157 A B s f x).
Proof. exact (MK_COMB (@lem3613383 B) (@lem3613382 A B s f x)). Qed.
Lemma lem3613389 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : ((term95 A B x s f) = (term96 A B s f x)) = (term157 A B s f x).
Proof. exact (TRANS (@lem3613242 A B s f x) (@lem3613384 A B s f x)). Qed.
Lemma lem3613390 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term157 A B s f x) = ((term95 A B x s f) = (term96 A B s f x)).
Proof. exact (SYM (@lem3613389 A B s f x)). Qed.
Lemma lem3613392 (p : Prop) : p = (term158 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3613393 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term157 A B s f x) = (term159 A B s f x).
Proof. exact (@lem3613392 (term157 A B s f x)). Qed.
Lemma lem3613394 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term159 A B s f x) = (term157 A B s f x).
Proof. exact (SYM (@lem3613393 A B s f x)). Qed.
Lemma lem3613395 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : term160 A B s f x) : term160 A B s f x.
Proof. exact (h1). Qed.
Lemma lem3613398 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : term159 A B s f x) : term159 A B s f x.
Proof. exact (h1). Qed.
Lemma lem3613399 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : term161 A B s f x.
Proof. exact (fun h0 : term159 A B s f x => @lem3613398 A B s f x h0). Qed.
Lemma lem3613400 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : term161 A B s f x) : term161 A B s f x.
Proof. exact (h1). Qed.
Lemma lem3613401 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : term159 A B s f x) : term159 A B s f x.
Proof. exact (h1). Qed.
Lemma lem3613402 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : term159 A B s f x) (h2 : term161 A B s f x) : term159 A B s f x.
Proof. exact (@lem3613400 A B s f x h2 (@lem3613401 A B s f x h1)). Qed.
Lemma lem3613403 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : term159 A B s f x) : term162 A B s f x.
Proof. exact (fun h0 : term161 A B s f x => @lem3613402 A B s f x h1 h0). Qed.
Lemma lem3613404 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : term161 A B s f x) : term161 A B s f x.
Proof. exact (h1). Qed.
Lemma lem3613405 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : term159 A B s f x) (h2 : term161 A B s f x) : term159 A B s f x.
Proof. exact (@lem3613403 A B s f x h1 (@lem3613404 A B s f x h2)). Qed.
Lemma lem3613406 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : term161 A B s f x) : term161 A B s f x.
Proof. exact (fun h0 : term159 A B s f x => @lem3613405 A B s f x h0 h1). Qed.
Lemma lem3613407 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : term163 A B s f x.
Proof. exact (fun h0 : term161 A B s f x => @lem3613406 A B s f x h0). Qed.
Lemma lem3613410 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : term161 A B s f x.
Proof. exact (@lem3613407 A B s f x (@lem3613399 A B s f x)). Qed.
Lemma lem3613411 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : term161 A B s f x.
Proof. exact (@lem3613410 A B s f x). Qed.
Lemma lem3613425 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3613426 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term159 A B s f x) = (term164 A B s f x).
Proof. exact (@lem3613425 (term160 A B s f x)). Qed.
Lemma lem3613428 (t : Prop) : (term165 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3613429 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term164 A B s f x) = (term157 A B s f x).
Proof. exact (@lem3613428 (term157 A B s f x)). Qed.
Lemma lem3613434 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term159 A B s f x) = (term157 A B s f x).
Proof. exact (TRANS (@lem3613426 A B s f x) (@lem3613429 A B s f x)). Qed.
Lemma lem3613539 {A B : Type'} (f : A -> B) (x : A) : (term166 A B f x) = (term167 A B f x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3613434 A B s f x)). Qed.
Lemma lem3613540 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3613541 {A B : Type'} (f : A -> B) (x : A) : (term168 A B f x) = (term169 A B f x).
Proof. exact (MK_COMB (@lem3613540 A) (@lem3613539 A B f x)). Qed.
Lemma lem3613546 {A B : Type'} (x : A) : (term170 A B x) = (term171 A B x).
Proof. exact (fun_ext (fun f : A -> B => @lem3613541 A B f x)). Qed.
Lemma lem3613547 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3613548 {A B : Type'} (x : A) : (term172 A B x) = (term173 A B x).
Proof. exact (MK_COMB (@lem3613547 A B) (@lem3613546 A B x)). Qed.
Lemma lem3613553 {A B : Type'} : (term174 A B) = (term175 A B).
Proof. exact (fun_ext (fun x : A => @lem3613548 A B x)). Qed.
Lemma lem3613554 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3613563 {A B : Type'} : (term176 A B) = (term177 A B).
Proof. exact (MK_COMB (@lem3613554 A) (@lem3613553 A B)). Qed.
Lemma lem3613564 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (x = (f x')) = (x = (f x')).
Proof. exact (eq_refl (x = (f x'))). Qed.
Lemma lem3613569 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (z : A) : (term178 A B s x f z) = (term178 A B s x f z).
Proof. exact (eq_refl (term178 A B s x f z)). Qed.
Lemma lem3613570 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) : (term179 A B s x f) = (term179 A B s x f).
Proof. exact (fun_ext (fun z : A => @lem3613569 A B s x f z)). Qed.
Lemma lem3613571 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3613572 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) : (term133 A B s x f) = (term133 A B s x f).
Proof. exact (MK_COMB (@lem3613571 A) (@lem3613570 A B s x f)). Qed.
Lemma lem3613573 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3613574 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) : (term149 A B s x f) = (term149 A B s x f).
Proof. exact (MK_COMB (@lem3613573) (@lem3613572 A B s x f)). Qed.
Lemma lem3613575 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (x' : A) : (term154 A B s x f x') = (term154 A B s x f x').
Proof. exact (MK_COMB (@lem3613574 A B s x f) (@lem3613564 A B x f x')). Qed.
Lemma lem3613584 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (z : A) : (term121 A B x s x' f z) = (term121 A B x s x' f z).
Proof. exact (eq_refl (term121 A B x s x' f z)). Qed.
Lemma lem3613585 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) : (term123 A B x s x' f) = (term123 A B x s x' f).
Proof. exact (fun_ext (fun z : A => @lem3613584 A B x s x' f z)). Qed.
Lemma lem3613586 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3613587 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) : (term124 A B x s x' f) = (term124 A B x s x' f).
Proof. exact (MK_COMB (@lem3613586 A) (@lem3613585 A B x s x' f)). Qed.
Lemma lem3613588 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3613589 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) : (term125 A B x s x' f) = (term125 A B x s x' f).
Proof. exact (MK_COMB (@lem3613588) (@lem3613587 A B x s x' f)). Qed.
Lemma lem3613590 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (x' : A) : ((term124 A B x' s x f) = (term154 A B s x f x')) = ((term124 A B x' s x f) = (term154 A B s x f x')).
Proof. exact (MK_COMB (@lem3613589 A B x' s x f) (@lem3613575 A B s x f x')). Qed.
Lemma lem3613591 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term156 A B s f x) = (term156 A B s f x).
Proof. exact (fun_ext (fun x' : B => @lem3613590 A B s x' f x)). Qed.
Lemma lem3613592 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3613593 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term157 A B s f x) = (term157 A B s f x).
Proof. exact (MK_COMB (@lem3613592 B) (@lem3613591 A B s f x)). Qed.
Lemma lem3613594 {A B : Type'} (f : A -> B) (x : A) : (term167 A B f x) = (term167 A B f x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3613593 A B s f x)). Qed.
Lemma lem3613595 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3613596 {A B : Type'} (f : A -> B) (x : A) : (term169 A B f x) = (term169 A B f x).
Proof. exact (MK_COMB (@lem3613595 A) (@lem3613594 A B f x)). Qed.
Lemma lem3613597 {A B : Type'} (x : A) : (term171 A B x) = (term171 A B x).
Proof. exact (fun_ext (fun f : A -> B => @lem3613596 A B f x)). Qed.
Lemma lem3613598 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3613599 {A B : Type'} (x : A) : (term173 A B x) = (term173 A B x).
Proof. exact (MK_COMB (@lem3613598 A B) (@lem3613597 A B x)). Qed.
Lemma lem3613600 {A B : Type'} : (term175 A B) = (term175 A B).
Proof. exact (fun_ext (fun x : A => @lem3613599 A B x)). Qed.
Lemma lem3613601 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3613602 {A B : Type'} : (term177 A B) = (term177 A B).
Proof. exact (MK_COMB (@lem3613601 A) (@lem3613600 A B)). Qed.
Lemma lem3613649 {A B : Type'} : (term176 A B) = (term177 A B).
Proof. exact (TRANS (@lem3613563 A B) (@lem3613602 A B)). Qed.
Lemma lem3613650 {A B : Type'} : (term177 A B) = (term176 A B).
Proof. exact (SYM (@lem3613649 A B)). Qed.
Lemma lem3613652 (p : Prop) : p = (term158 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3613653 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : ((term124 A B x s x' f) = (term154 A B s x' f x)) = (term180 A B s x' f x).
Proof. exact (@lem3613652 ((term124 A B x s x' f) = (term154 A B s x' f x))). Qed.
Lemma lem3613654 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term180 A B s x' f x) = ((term124 A B x s x' f) = (term154 A B s x' f x)).
Proof. exact (SYM (@lem3613653 A B s x' f x)). Qed.
Lemma lem3613655 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) (h1 : term181 A B s x' f x) : term181 A B s x' f x.
Proof. exact (h1). Qed.
Lemma lem3613664 {A : Type'} (x : A) (z : A) (s : A -> Prop) : (term182 A x z s) = (term183 A x z s).
Proof. exact (@lem17160 (z = x) (@IN A z s)). Qed.
Lemma lem3613668 {A B : Type'} (x' : B) (f : A -> B) (z : A) : (term184 A B x' f z) = (term184 A B x' f z).
Proof. exact (eq_refl (term184 A B x' f z)). Qed.
Lemma lem3613670 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3613671 {A : Type'} (x : A) (z : A) (s : A -> Prop) : (term185 A x z s) = (term186 A x z s).
Proof. exact (MK_COMB (@lem3613670) (@lem3613664 A x z s)). Qed.
Lemma lem3613672 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (z : A) : (term187 A B x s x' f z) = (term188 A B x s x' f z).
Proof. exact (MK_COMB (@lem3613671 A x z s) (@lem3613668 A B x' f z)). Qed.
Lemma lem3613673 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (z : A) : (term189 A B x s x' f z) = (term187 A B x s x' f z).
Proof. exact (@lem17045 (term25 A x z s) (x' = (f z))). Qed.
Lemma lem3613674 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (z : A) : (term189 A B x s x' f z) = (term188 A B x s x' f z).
Proof. exact (TRANS (@lem3613673 A B x s x' f z) (@lem3613672 A B x s x' f z)). Qed.
Lemma lem3613677 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (z : A) : (term121 A B x s x' f z) = (term121 A B x s x' f z).
Proof. exact (eq_refl (term121 A B x s x' f z)). Qed.
Lemma lem3613678 {A : Type'} (P : A -> Prop) : (term190 A P) = (term191 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem3613679 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) : (term192 A B x s x' f) = (term193 A B x s x' f).
Proof. exact (@lem3613678 A (term123 A B x s x' f)). Qed.
Lemma lem3613680 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (z : A) : (term194 A B x s x' f z) = (term121 A B x s x' f z).
Proof. exact (eq_refl (term194 A B x s x' f z)). Qed.
Lemma lem3613681 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3613682 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (z : A) : (term195 A B x s x' f z) = (term189 A B x s x' f z).
Proof. exact (MK_COMB (@lem3613681) (@lem3613680 A B x s x' f z)). Qed.
Lemma lem3613683 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (z : A) : (term195 A B x s x' f z) = (term188 A B x s x' f z).
Proof. exact (TRANS (@lem3613682 A B x s x' f z) (@lem3613674 A B x s x' f z)). Qed.
Lemma lem3613684 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) : (term196 A B x s x' f) = (term197 A B x s x' f).
Proof. exact (fun_ext (fun z : A => @lem3613683 A B x s x' f z)). Qed.
Lemma lem3613685 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3613686 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) : (term193 A B x s x' f) = (term198 A B x s x' f).
Proof. exact (MK_COMB (@lem3613685 A) (@lem3613684 A B x s x' f)). Qed.
Lemma lem3613687 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) : (term192 A B x s x' f) = (term198 A B x s x' f).
Proof. exact (TRANS (@lem3613679 A B x s x' f) (@lem3613686 A B x s x' f)). Qed.
Lemma lem3613688 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) : (term123 A B x s x' f) = (term123 A B x s x' f).
Proof. exact (fun_ext (fun z : A => @lem3613677 A B x s x' f z)). Qed.
Lemma lem3613689 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3613690 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) : (term124 A B x s x' f) = (term124 A B x s x' f).
Proof. exact (MK_COMB (@lem3613689 A) (@lem3613688 A B x s x' f)). Qed.
Lemma lem3613699 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (z : A) : (term199 A B s x' f z) = (term200 A B s x' f z).
Proof. exact (@lem17045 (@IN A z s) (x' = (f z))). Qed.
Lemma lem3613702 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (z : A) : (term178 A B s x' f z) = (term178 A B s x' f z).
Proof. exact (eq_refl (term178 A B s x' f z)). Qed.
Lemma lem3613703 {A : Type'} (P : A -> Prop) : (term190 A P) = (term191 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem3613704 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) : (term201 A B s x' f) = (term202 A B s x' f).
Proof. exact (@lem3613703 A (term179 A B s x' f)). Qed.
Lemma lem3613705 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (z : A) : (term203 A B s x' f z) = (term178 A B s x' f z).
Proof. exact (eq_refl (term203 A B s x' f z)). Qed.
Lemma lem3613706 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3613707 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (z : A) : (term204 A B s x' f z) = (term199 A B s x' f z).
Proof. exact (MK_COMB (@lem3613706) (@lem3613705 A B s x' f z)). Qed.
Lemma lem3613708 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (z : A) : (term204 A B s x' f z) = (term200 A B s x' f z).
Proof. exact (TRANS (@lem3613707 A B s x' f z) (@lem3613699 A B s x' f z)). Qed.
Lemma lem3613709 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) : (term205 A B s x' f) = (term206 A B s x' f).
Proof. exact (fun_ext (fun z : A => @lem3613708 A B s x' f z)). Qed.
Lemma lem3613710 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3613711 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) : (term202 A B s x' f) = (term207 A B s x' f).
Proof. exact (MK_COMB (@lem3613710 A) (@lem3613709 A B s x' f)). Qed.
Lemma lem3613712 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) : (term201 A B s x' f) = (term207 A B s x' f).
Proof. exact (TRANS (@lem3613704 A B s x' f) (@lem3613711 A B s x' f)). Qed.
Lemma lem3613713 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) : (term179 A B s x' f) = (term179 A B s x' f).
Proof. exact (fun_ext (fun z : A => @lem3613702 A B s x' f z)). Qed.
Lemma lem3613714 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3613715 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) : (term133 A B s x' f) = (term133 A B s x' f).
Proof. exact (MK_COMB (@lem3613714 A) (@lem3613713 A B s x' f)). Qed.
Lemma lem3613716 {A B : Type'} (x' : B) (f : A -> B) (x : A) : (term184 A B x' f x) = (term184 A B x' f x).
Proof. exact (eq_refl (term184 A B x' f x)). Qed.
Lemma lem3613717 {A B : Type'} (x' : B) (f : A -> B) (x : A) : (x' = (f x)) = (x' = (f x)).
Proof. exact (eq_refl (x' = (f x))). Qed.
Lemma lem3613718 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3613719 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) : (term208 A B s x' f) = (term209 A B s x' f).
Proof. exact (MK_COMB (@lem3613718) (@lem3613712 A B s x' f)). Qed.
Lemma lem3613720 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term210 A B s x' f x) = (term211 A B s x' f x).
Proof. exact (MK_COMB (@lem3613719 A B s x' f) (@lem3613716 A B x' f x)). Qed.
Lemma lem3613721 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term212 A B s x' f x) = (term210 A B s x' f x).
Proof. exact (@lem17160 (term133 A B s x' f) (x' = (f x))). Qed.
Lemma lem3613722 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term212 A B s x' f x) = (term211 A B s x' f x).
Proof. exact (TRANS (@lem3613721 A B s x' f x) (@lem3613720 A B s x' f x)). Qed.
Lemma lem3613723 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3613724 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) : (term149 A B s x' f) = (term149 A B s x' f).
Proof. exact (MK_COMB (@lem3613723) (@lem3613715 A B s x' f)). Qed.
Lemma lem3613725 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term154 A B s x' f x) = (term154 A B s x' f x).
Proof. exact (MK_COMB (@lem3613724 A B s x' f) (@lem3613717 A B x' f x)). Qed.
Lemma lem3613726 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3613727 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) : (term213 A B x s x' f) = (term214 A B x s x' f).
Proof. exact (MK_COMB (@lem3613726) (@lem3613687 A B x s x' f)). Qed.
Lemma lem3613728 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term215 A B s x' f x) = (term216 A B s x' f x).
Proof. exact (MK_COMB (@lem3613727 A B x s x' f) (@lem3613725 A B s x' f x)). Qed.
Lemma lem3613729 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3613730 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) : (term217 A B x s x' f) = (term217 A B x s x' f).
Proof. exact (MK_COMB (@lem3613729) (@lem3613690 A B x s x' f)). Qed.
Lemma lem3613731 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term218 A B s x' f x) = (term219 A B s x' f x).
Proof. exact (MK_COMB (@lem3613730 A B x s x' f) (@lem3613722 A B s x' f x)). Qed.
Lemma lem3613732 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3613733 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term220 A B s x' f x) = (term221 A B s x' f x).
Proof. exact (MK_COMB (@lem3613732) (@lem3613731 A B s x' f x)). Qed.
Lemma lem3613734 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term222 A B s x' f x) = (term223 A B s x' f x).
Proof. exact (MK_COMB (@lem3613733 A B s x' f x) (@lem3613728 A B s x' f x)). Qed.
Lemma lem3613735 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term181 A B s x' f x) = (term222 A B s x' f x).
Proof. exact (@lem17646 (term124 A B x s x' f) (term154 A B s x' f x)). Qed.
Lemma lem3613736 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term181 A B s x' f x) = (term223 A B s x' f x).
Proof. exact (TRANS (@lem3613735 A B s x' f x) (@lem3613734 A B s x' f x)). Qed.
Lemma lem3613931 {A : Type'} (P : A -> Prop) (Q : Prop) : (term224 A P Q) = (term225 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3613932 {A : Type'} (P : A -> Prop) (Q : Prop) : (term224 A P Q) = (term225 A P Q).
Proof. exact (@lem3613931 A P Q). Qed.
Lemma lem3613933 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term226 A B s x' f x) = (term227 A B s x' f x).
Proof. exact (@lem3613932 A (term123 A B x s x' f) (term211 A B s x' f x)). Qed.
Lemma lem3613934 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (z : A) : (term194 A B x s x' f z) = (term121 A B x s x' f z).
Proof. exact (eq_refl (term194 A B x s x' f z)). Qed.
Lemma lem3613935 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) : (term228 A B x s x' f) = (term123 A B x s x' f).
Proof. exact (fun_ext (fun z : A => @lem3613934 A B x s x' f z)). Qed.
Lemma lem3613936 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3613937 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) : (term229 A B x s x' f) = (term124 A B x s x' f).
Proof. exact (MK_COMB (@lem3613936 A) (@lem3613935 A B x s x' f)). Qed.
Lemma lem3613938 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3613939 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) : (term230 A B x s x' f) = (term217 A B x s x' f).
Proof. exact (MK_COMB (@lem3613938) (@lem3613937 A B x s x' f)). Qed.
Lemma lem3613940 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term211 A B s x' f x) = (term211 A B s x' f x).
Proof. exact (eq_refl (term211 A B s x' f x)). Qed.
Lemma lem3613941 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term226 A B s x' f x) = (term219 A B s x' f x).
Proof. exact (MK_COMB (@lem3613939 A B x s x' f) (@lem3613940 A B s x' f x)). Qed.
Lemma lem3613942 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3613943 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term231 A B s x' f x) = (term232 A B s x' f x).
Proof. exact (MK_COMB (@lem3613942) (@lem3613941 A B s x' f x)). Qed.
Lemma lem3613944 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (z : A) : (term194 A B x s x' f z) = (term121 A B x s x' f z).
Proof. exact (eq_refl (term194 A B x s x' f z)). Qed.
Lemma lem3613945 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3613946 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (z : A) : (term233 A B x s x' f z) = (term234 A B x s x' f z).
Proof. exact (MK_COMB (@lem3613945) (@lem3613944 A B x s x' f z)). Qed.
Lemma lem3613947 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term211 A B s x' f x) = (term211 A B s x' f x).
Proof. exact (eq_refl (term211 A B s x' f x)). Qed.
Lemma lem3613948 {A B : Type'} (z : A) (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term235 A B z s x' f x) = (term236 A B z s x' f x).
Proof. exact (MK_COMB (@lem3613946 A B x s x' f z) (@lem3613947 A B s x' f x)). Qed.
Lemma lem3613949 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term237 A B s x' f x) = (term238 A B s x' f x).
Proof. exact (fun_ext (fun z : A => @lem3613948 A B z s x' f x)). Qed.
Lemma lem3613950 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3613951 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term227 A B s x' f x) = (term239 A B s x' f x).
Proof. exact (MK_COMB (@lem3613950 A) (@lem3613949 A B s x' f x)). Qed.
Lemma lem3613952 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : ((term226 A B s x' f x) = (term227 A B s x' f x)) = ((term219 A B s x' f x) = (term239 A B s x' f x)).
Proof. exact (MK_COMB (@lem3613943 A B s x' f x) (@lem3613951 A B s x' f x)). Qed.
Lemma lem3613953 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term219 A B s x' f x) = (term239 A B s x' f x).
Proof. exact (EQ_MP (@lem3613952 A B s x' f x) (@lem3613933 A B s x' f x)). Qed.
Lemma lem3613954 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3613955 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term221 A B s x' f x) = (term240 A B s x' f x).
Proof. exact (MK_COMB (@lem3613954) (@lem3613953 A B s x' f x)). Qed.
Lemma lem3613957 {A : Type'} (P : A -> Prop) (Q : Prop) : (term241 A P Q) = (term242 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3613958 {A : Type'} (P : A -> Prop) (Q : Prop) : (term241 A P Q) = (term242 A P Q).
Proof. exact (@lem3613957 A P Q). Qed.
Lemma lem3613959 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term243 A B s x' f x) = (term244 A B s x' f x).
Proof. exact (@lem3613958 A (term179 A B s x' f) (x' = (f x))). Qed.
Lemma lem3613960 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (z : A) : (term203 A B s x' f z) = (term178 A B s x' f z).
Proof. exact (eq_refl (term203 A B s x' f z)). Qed.
Lemma lem3613961 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) : (term245 A B s x' f) = (term179 A B s x' f).
Proof. exact (fun_ext (fun z : A => @lem3613960 A B s x' f z)). Qed.
Lemma lem3613962 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3613963 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) : (term246 A B s x' f) = (term133 A B s x' f).
Proof. exact (MK_COMB (@lem3613962 A) (@lem3613961 A B s x' f)). Qed.
Lemma lem3613964 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3613965 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) : (term247 A B s x' f) = (term149 A B s x' f).
Proof. exact (MK_COMB (@lem3613964) (@lem3613963 A B s x' f)). Qed.
Lemma lem3613966 {A B : Type'} (x' : B) (f : A -> B) (x : A) : (x' = (f x)) = (x' = (f x)).
Proof. exact (eq_refl (x' = (f x))). Qed.
Lemma lem3613967 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term243 A B s x' f x) = (term154 A B s x' f x).
Proof. exact (MK_COMB (@lem3613965 A B s x' f) (@lem3613966 A B x' f x)). Qed.
Lemma lem3613968 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3613969 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term248 A B s x' f x) = (term249 A B s x' f x).
Proof. exact (MK_COMB (@lem3613968) (@lem3613967 A B s x' f x)). Qed.
Lemma lem3613970 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (z : A) : (term203 A B s x' f z) = (term178 A B s x' f z).
Proof. exact (eq_refl (term203 A B s x' f z)). Qed.
Lemma lem3613971 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3613972 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (z : A) : (term250 A B s x' f z) = (term251 A B s x' f z).
Proof. exact (MK_COMB (@lem3613971) (@lem3613970 A B s x' f z)). Qed.
Lemma lem3613973 {A B : Type'} (x' : B) (f : A -> B) (x : A) : (x' = (f x)) = (x' = (f x)).
Proof. exact (eq_refl (x' = (f x))). Qed.
Lemma lem3613974 {A B : Type'} (s : A -> Prop) (z : A) (x' : B) (f : A -> B) (x : A) : (term252 A B s z x' f x) = (term253 A B s z x' f x).
Proof. exact (MK_COMB (@lem3613972 A B s x' f z) (@lem3613973 A B x' f x)). Qed.
Lemma lem3613975 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term254 A B s x' f x) = (term255 A B s x' f x).
Proof. exact (fun_ext (fun z : A => @lem3613974 A B s z x' f x)). Qed.
Lemma lem3613976 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3613977 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term244 A B s x' f x) = (term256 A B s x' f x).
Proof. exact (MK_COMB (@lem3613976 A) (@lem3613975 A B s x' f x)). Qed.
Lemma lem3613978 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : ((term243 A B s x' f x) = (term244 A B s x' f x)) = ((term154 A B s x' f x) = (term256 A B s x' f x)).
Proof. exact (MK_COMB (@lem3613969 A B s x' f x) (@lem3613977 A B s x' f x)). Qed.
Lemma lem3613979 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term154 A B s x' f x) = (term256 A B s x' f x).
Proof. exact (EQ_MP (@lem3613978 A B s x' f x) (@lem3613959 A B s x' f x)). Qed.
Lemma lem3613980 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) : (term214 A B x s x' f) = (term214 A B x s x' f).
Proof. exact (eq_refl (term214 A B x s x' f)). Qed.
Lemma lem3613981 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term216 A B s x' f x) = (term257 A B s x' f x).
Proof. exact (MK_COMB (@lem3613980 A B x s x' f) (@lem3613979 A B s x' f x)). Qed.
Lemma lem3613983 {A : Type'} (P : Prop) (Q : A -> Prop) : (term258 A P Q) = (term259 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3613984 {A : Type'} (P : Prop) (Q : A -> Prop) : (term258 A P Q) = (term259 A P Q).
Proof. exact (@lem3613983 A P Q). Qed.
Lemma lem3613985 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term260 A B s x' f x) = (term261 A B s x' f x).
Proof. exact (@lem3613984 A (term198 A B x s x' f) (term255 A B s x' f x)). Qed.
Lemma lem3613986 {A B : Type'} (s : A -> Prop) (z : A) (x' : B) (f : A -> B) (x : A) : (term262 A B s x' f x z) = (term253 A B s z x' f x).
Proof. exact (eq_refl (term262 A B s x' f x z)). Qed.
Lemma lem3613987 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term263 A B s x' f x) = (term255 A B s x' f x).
Proof. exact (fun_ext (fun z : A => @lem3613986 A B s z x' f x)). Qed.
Lemma lem3613988 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3613989 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term264 A B s x' f x) = (term256 A B s x' f x).
Proof. exact (MK_COMB (@lem3613988 A) (@lem3613987 A B s x' f x)). Qed.
Lemma lem3613990 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) : (term214 A B x s x' f) = (term214 A B x s x' f).
Proof. exact (eq_refl (term214 A B x s x' f)). Qed.
Lemma lem3613991 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term260 A B s x' f x) = (term257 A B s x' f x).
Proof. exact (MK_COMB (@lem3613990 A B x s x' f) (@lem3613989 A B s x' f x)). Qed.
Lemma lem3613992 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3613993 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term265 A B s x' f x) = (term266 A B s x' f x).
Proof. exact (MK_COMB (@lem3613992) (@lem3613991 A B s x' f x)). Qed.
Lemma lem3613994 {A B : Type'} (s : A -> Prop) (z : A) (x' : B) (f : A -> B) (x : A) : (term262 A B s x' f x z) = (term253 A B s z x' f x).
Proof. exact (eq_refl (term262 A B s x' f x z)). Qed.
Lemma lem3613995 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) : (term214 A B x s x' f) = (term214 A B x s x' f).
Proof. exact (eq_refl (term214 A B x s x' f)). Qed.
Lemma lem3613996 {A B : Type'} (s : A -> Prop) (z : A) (x' : B) (f : A -> B) (x : A) : (term267 A B s x' f x z) = (term268 A B s z x' f x).
Proof. exact (MK_COMB (@lem3613995 A B x s x' f) (@lem3613994 A B s z x' f x)). Qed.
Lemma lem3613997 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term269 A B s x' f x) = (term270 A B s x' f x).
Proof. exact (fun_ext (fun z : A => @lem3613996 A B s z x' f x)). Qed.
Lemma lem3613998 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3613999 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term261 A B s x' f x) = (term271 A B s x' f x).
Proof. exact (MK_COMB (@lem3613998 A) (@lem3613997 A B s x' f x)). Qed.
Lemma lem3614000 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : ((term260 A B s x' f x) = (term261 A B s x' f x)) = ((term257 A B s x' f x) = (term271 A B s x' f x)).
Proof. exact (MK_COMB (@lem3613993 A B s x' f x) (@lem3613999 A B s x' f x)). Qed.
Lemma lem3614001 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term257 A B s x' f x) = (term271 A B s x' f x).
Proof. exact (EQ_MP (@lem3614000 A B s x' f x) (@lem3613985 A B s x' f x)). Qed.
Lemma lem3614002 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term216 A B s x' f x) = (term271 A B s x' f x).
Proof. exact (TRANS (@lem3613981 A B s x' f x) (@lem3614001 A B s x' f x)). Qed.
Lemma lem3614003 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term223 A B s x' f x) = (term272 A B s x' f x).
Proof. exact (MK_COMB (@lem3613955 A B s x' f x) (@lem3614002 A B s x' f x)). Qed.
Lemma lem3614005 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term273 A P Q) = (term274 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3614006 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term273 A P Q) = (term274 A P Q).
Proof. exact (@lem3614005 A P Q). Qed.
Lemma lem3614007 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term275 A B s x' f x) = (term276 A B s x' f x).
Proof. exact (@lem3614006 A (term238 A B s x' f x) (term270 A B s x' f x)). Qed.
Lemma lem3614008 {A B : Type'} (z : A) (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term277 A B s x' f x z) = (term236 A B z s x' f x).
Proof. exact (eq_refl (term277 A B s x' f x z)). Qed.
Lemma lem3614009 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term278 A B s x' f x) = (term238 A B s x' f x).
Proof. exact (fun_ext (fun z : A => @lem3614008 A B z s x' f x)). Qed.
Lemma lem3614010 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3614011 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term279 A B s x' f x) = (term239 A B s x' f x).
Proof. exact (MK_COMB (@lem3614010 A) (@lem3614009 A B s x' f x)). Qed.
Lemma lem3614012 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3614013 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term280 A B s x' f x) = (term240 A B s x' f x).
Proof. exact (MK_COMB (@lem3614012) (@lem3614011 A B s x' f x)). Qed.
Lemma lem3614014 {A B : Type'} (s : A -> Prop) (z : A) (x' : B) (f : A -> B) (x : A) : (term281 A B s x' f x z) = (term268 A B s z x' f x).
Proof. exact (eq_refl (term281 A B s x' f x z)). Qed.
Lemma lem3614015 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term282 A B s x' f x) = (term270 A B s x' f x).
Proof. exact (fun_ext (fun z : A => @lem3614014 A B s z x' f x)). Qed.
Lemma lem3614016 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3614017 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term283 A B s x' f x) = (term271 A B s x' f x).
Proof. exact (MK_COMB (@lem3614016 A) (@lem3614015 A B s x' f x)). Qed.
Lemma lem3614018 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term275 A B s x' f x) = (term272 A B s x' f x).
Proof. exact (MK_COMB (@lem3614013 A B s x' f x) (@lem3614017 A B s x' f x)). Qed.
Lemma lem3614019 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3614020 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term284 A B s x' f x) = (term285 A B s x' f x).
Proof. exact (MK_COMB (@lem3614019) (@lem3614018 A B s x' f x)). Qed.
Lemma lem3614021 {A B : Type'} (z : A) (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term277 A B s x' f x z) = (term236 A B z s x' f x).
Proof. exact (eq_refl (term277 A B s x' f x z)). Qed.
Lemma lem3614022 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3614023 {A B : Type'} (z : A) (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term286 A B s x' f x z) = (term287 A B z s x' f x).
Proof. exact (MK_COMB (@lem3614022) (@lem3614021 A B z s x' f x)). Qed.
Lemma lem3614024 {A B : Type'} (s : A -> Prop) (z : A) (x' : B) (f : A -> B) (x : A) : (term281 A B s x' f x z) = (term268 A B s z x' f x).
Proof. exact (eq_refl (term281 A B s x' f x z)). Qed.
Lemma lem3614025 {A B : Type'} (s : A -> Prop) (z : A) (x' : B) (f : A -> B) (x : A) : (term288 A B s x' f x z) = (term289 A B s z x' f x).
Proof. exact (MK_COMB (@lem3614023 A B z s x' f x) (@lem3614024 A B s z x' f x)). Qed.
Lemma lem3614026 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term290 A B s x' f x) = (term291 A B s x' f x).
Proof. exact (fun_ext (fun z : A => @lem3614025 A B s z x' f x)). Qed.
Lemma lem3614027 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3614028 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term276 A B s x' f x) = (term292 A B s x' f x).
Proof. exact (MK_COMB (@lem3614027 A) (@lem3614026 A B s x' f x)). Qed.
Lemma lem3614029 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : ((term275 A B s x' f x) = (term276 A B s x' f x)) = ((term272 A B s x' f x) = (term292 A B s x' f x)).
Proof. exact (MK_COMB (@lem3614020 A B s x' f x) (@lem3614028 A B s x' f x)). Qed.
Lemma lem3614030 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term272 A B s x' f x) = (term292 A B s x' f x).
Proof. exact (EQ_MP (@lem3614029 A B s x' f x) (@lem3614007 A B s x' f x)). Qed.
Lemma lem3614032 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term223 A B s x' f x) = (term292 A B s x' f x).
Proof. exact (TRANS (@lem3614003 A B s x' f x) (@lem3614030 A B s x' f x)). Qed.
Lemma lem3614033 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term181 A B s x' f x) = (term292 A B s x' f x).
Proof. exact (TRANS (@lem3613736 A B s x' f x) (@lem3614032 A B s x' f x)). Qed.
Lemma lem3614034 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) (h1 : term181 A B s x' f x) : term292 A B s x' f x.
Proof. exact (EQ_MP (@lem3614033 A B s x' f x) (@lem3613655 A B s x' f x h1)). Qed.
Lemma lem3614035 {A B : Type'} (s : A -> Prop) (z : A) (x' : B) (f : A -> B) (x : A) (h1 : term289 A B s z x' f x) : term289 A B s z x' f x.
Proof. exact (h1). Qed.
Lemma lem3614060 {A B : Type'} (s : A -> Prop) (z : A) (x' : B) (f : A -> B) (x : A) : (term253 A B s z x' f x) = (term253 A B s z x' f x).
Proof. exact (eq_refl (term253 A B s z x' f x)). Qed.
Lemma lem3614089 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (z : A) : (term188 A B x s x' f z) = (term188 A B x s x' f z).
Proof. exact (eq_refl (term188 A B x s x' f z)). Qed.
Lemma lem3614090 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) : (term197 A B x s x' f) = (term197 A B x s x' f).
Proof. exact (fun_ext (fun z : A => @lem3614089 A B x s x' f z)). Qed.
Lemma lem3614091 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3614092 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) : (term198 A B x s x' f) = (term198 A B x s x' f).
Proof. exact (MK_COMB (@lem3614091 A) (@lem3614090 A B x s x' f)). Qed.
Lemma lem3614093 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3614094 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) : (term214 A B x s x' f) = (term214 A B x s x' f).
Proof. exact (MK_COMB (@lem3614093) (@lem3614092 A B x s x' f)). Qed.
Lemma lem3614095 {A B : Type'} (s : A -> Prop) (z : A) (x' : B) (f : A -> B) (x : A) : (term268 A B s z x' f x) = (term268 A B s z x' f x).
Proof. exact (MK_COMB (@lem3614094 A B x s x' f) (@lem3614060 A B s z x' f x)). Qed.
Lemma lem3614104 {A B : Type'} (x' : B) (f : A -> B) (x : A) : (term184 A B x' f x) = (term184 A B x' f x).
Proof. exact (eq_refl (term184 A B x' f x)). Qed.
Lemma lem3614123 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (z : A) : (term200 A B s x' f z) = (term200 A B s x' f z).
Proof. exact (eq_refl (term200 A B s x' f z)). Qed.
Lemma lem3614124 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) : (term206 A B s x' f) = (term206 A B s x' f).
Proof. exact (fun_ext (fun z : A => @lem3614123 A B s x' f z)). Qed.
Lemma lem3614125 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3614126 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) : (term207 A B s x' f) = (term207 A B s x' f).
Proof. exact (MK_COMB (@lem3614125 A) (@lem3614124 A B s x' f)). Qed.
Lemma lem3614127 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3614128 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) : (term209 A B s x' f) = (term209 A B s x' f).
Proof. exact (MK_COMB (@lem3614127) (@lem3614126 A B s x' f)). Qed.
Lemma lem3614129 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term211 A B s x' f x) = (term211 A B s x' f x).
Proof. exact (MK_COMB (@lem3614128 A B s x' f) (@lem3614104 A B x' f x)). Qed.
Lemma lem3614154 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (z : A) : (term234 A B x s x' f z) = (term234 A B x s x' f z).
Proof. exact (eq_refl (term234 A B x s x' f z)). Qed.
Lemma lem3614155 {A B : Type'} (z : A) (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term236 A B z s x' f x) = (term236 A B z s x' f x).
Proof. exact (MK_COMB (@lem3614154 A B x s x' f z) (@lem3614129 A B s x' f x)). Qed.
Lemma lem3614156 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3614157 {A B : Type'} (z : A) (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term287 A B z s x' f x) = (term287 A B z s x' f x).
Proof. exact (MK_COMB (@lem3614156) (@lem3614155 A B z s x' f x)). Qed.
Lemma lem3614158 {A B : Type'} (s : A -> Prop) (z : A) (x' : B) (f : A -> B) (x : A) : (term289 A B s z x' f x) = (term289 A B s z x' f x).
Proof. exact (MK_COMB (@lem3614157 A B z s x' f x) (@lem3614095 A B s z x' f x)). Qed.
Lemma lem3614159 {A B : Type'} (s : A -> Prop) (z : A) (x' : B) (f : A -> B) (x : A) (h1 : term289 A B s z x' f x) : term289 A B s z x' f x.
Proof. exact (EQ_MP (@lem3614158 A B s z x' f x) (@lem3614035 A B s z x' f x h1)). Qed.
Lemma lem3614160 {A B : Type'} (z : A) (s : A -> Prop) (x' : B) (f : A -> B) (x : A) (h1 : term236 A B z s x' f x) : term236 A B z s x' f x.
Proof. exact (h1). Qed.
Lemma lem3614161 {A B : Type'} (s : A -> Prop) (z : A) (x' : B) (f : A -> B) (x : A) (h1 : term268 A B s z x' f x) : term268 A B s z x' f x.
Proof. exact (h1). Qed.
Lemma lem3614162 {A B : Type'} (z : A) (s : A -> Prop) (x' : B) (f : A -> B) (x : A) (h1 : term236 A B z s x' f x) : term211 A B s x' f x.
Proof. exact (proj2 (@lem3614160 A B z s x' f x h1)). Qed.
Lemma lem3614163 {A B : Type'} (z : A) (s : A -> Prop) (x' : B) (f : A -> B) (x : A) (h1 : term236 A B z s x' f x) : term121 A B x s x' f z.
Proof. exact (proj1 (@lem3614160 A B z s x' f x h1)). Qed.
Lemma lem3614165 {A B : Type'} (z : A) (s : A -> Prop) (x' : B) (f : A -> B) (x : A) (h1 : term236 A B z s x' f x) : term207 A B s x' f.
Proof. exact (proj1 (@lem3614162 A B z s x' f x h1)). Qed.
Lemma lem3614167 {A B : Type'} (z : A) (s : A -> Prop) (x' : B) (f : A -> B) (x : A) (h1 : term236 A B z s x' f x) : term25 A x z s.
Proof. exact (proj1 (@lem3614163 A B z s x' f x h1)). Qed.
Lemma lem3614170 {A B : Type'} (s : A -> Prop) (z : A) (x' : B) (f : A -> B) (x : A) (h1 : term268 A B s z x' f x) : term253 A B s z x' f x.
Proof. exact (proj2 (@lem3614161 A B s z x' f x h1)). Qed.
Lemma lem3614171 {A B : Type'} (s : A -> Prop) (z : A) (x' : B) (f : A -> B) (x : A) (h1 : term268 A B s z x' f x) : term198 A B x s x' f.
Proof. exact (proj1 (@lem3614161 A B s z x' f x h1)). Qed.
Lemma lem3614172 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (z : A) (h1 : term178 A B s x' f z) : term178 A B s x' f z.
Proof. exact (h1). Qed.
Lemma lem3614200 {A : Type'} (z : A) (x : A) (h1 : z = x) : z = x.
Proof. exact (h1). Qed.
Lemma lem3614208 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (z : A) : (term200 A B s x' f z) = (term200 A B s x' f z).
Proof. exact (eq_refl (term200 A B s x' f z)). Qed.
Lemma lem3614209 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) : (term206 A B s x' f) = (term206 A B s x' f).
Proof. exact (fun_ext (fun z : A => @lem3614208 A B s x' f z)). Qed.
Lemma lem3614210 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3614212 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) : (term207 A B s x' f) = (term207 A B s x' f).
Proof. exact (MK_COMB (@lem3614210 A) (@lem3614209 A B s x' f)). Qed.
Lemma lem3614213 {A B : Type'} (z : A) (s : A -> Prop) (x' : B) (f : A -> B) (x : A) (h1 : term236 A B z s x' f x) : term207 A B s x' f.
Proof. exact (EQ_MP (@lem3614212 A B s x' f) (@lem3614165 A B z s x' f x h1)). Qed.
Lemma lem3614225 {A : Type'} (z : A) (s : A -> Prop) (h1 : @IN A z s) : @IN A z s.
Proof. exact (h1). Qed.
Lemma lem3614243 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (z : A) : (term188 A B x s x' f z) = (term293 A B x s x' f z).
Proof. exact (@lem19699 (term294 A z x) (term295 A z s) (term184 A B x' f z)). Qed.
Lemma lem3614244 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) : (term197 A B x s x' f) = (term296 A B x s x' f).
Proof. exact (fun_ext (fun z : A => @lem3614243 A B x s x' f z)). Qed.
Lemma lem3614245 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3614247 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) : (term198 A B x s x' f) = (term297 A B x s x' f).
Proof. exact (MK_COMB (@lem3614245 A) (@lem3614244 A B x s x' f)). Qed.
Lemma lem3614248 {A B : Type'} (s : A -> Prop) (z : A) (x' : B) (f : A -> B) (x : A) (h1 : term268 A B s z x' f x) : term297 A B x s x' f.
Proof. exact (EQ_MP (@lem3614247 A B x s x' f) (@lem3614171 A B s z x' f x h1)). Qed.
Lemma lem3614274 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (z : A) : (term188 A B x s x' f z) = (term293 A B x s x' f z).
Proof. exact (@lem19699 (term294 A z x) (term295 A z s) (term184 A B x' f z)). Qed.
Lemma lem3614275 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) : (term197 A B x s x' f) = (term296 A B x s x' f).
Proof. exact (fun_ext (fun z : A => @lem3614274 A B x s x' f z)). Qed.
Lemma lem3614276 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3614278 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) : (term198 A B x s x' f) = (term297 A B x s x' f).
Proof. exact (MK_COMB (@lem3614276 A) (@lem3614275 A B x s x' f)). Qed.
Lemma lem3614279 {A B : Type'} (s : A -> Prop) (z : A) (x' : B) (f : A -> B) (x : A) (h1 : term268 A B s z x' f x) : term297 A B x s x' f.
Proof. exact (EQ_MP (@lem3614278 A B x s x' f) (@lem3614171 A B s z x' f x h1)). Qed.
Lemma lem3614283 {A B : Type'} (x' : B) (f : A -> B) (x : A) (h1 : x' = (f x)) : x' = (f x).
Proof. exact (h1). Qed.
Lemma lem3614287 {A B : Type'} (_39207 : A) (z : A) (s : A -> Prop) (x' : B) (f : A -> B) (x : A) (h1 : term236 A B z s x' f x) : term298 A B s x' f _39207.
Proof. exact (@lem3614213 A B z s x' f x h1 _39207). Qed.
Lemma lem3614288 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (_39207 : A) : (term298 A B s x' f _39207) = (term200 A B s x' f _39207).
Proof. exact (eq_refl (term298 A B s x' f _39207)). Qed.
Lemma lem3614290 {A B : Type'} (_39208 : A) (s : A -> Prop) (z : A) (x' : B) (f : A -> B) (x : A) (h1 : term268 A B s z x' f x) : term299 A B x s x' f _39208.
Proof. exact (@lem3614248 A B s z x' f x h1 _39208). Qed.
Lemma lem3614291 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (_39208 : A) : (term299 A B x s x' f _39208) = (term293 A B x s x' f _39208).
Proof. exact (eq_refl (term299 A B x s x' f _39208)). Qed.
Lemma lem3614292 {A B : Type'} (_39208 : A) (s : A -> Prop) (z : A) (x' : B) (f : A -> B) (x : A) (h1 : term268 A B s z x' f x) : term293 A B x s x' f _39208.
Proof. exact (EQ_MP (@lem3614291 A B x s x' f _39208) (@lem3614290 A B _39208 s z x' f x h1)). Qed.
Lemma lem3614293 {A B : Type'} (_39209 : A) (s : A -> Prop) (z : A) (x' : B) (f : A -> B) (x : A) (h1 : term268 A B s z x' f x) : term299 A B x s x' f _39209.
Proof. exact (@lem3614279 A B s z x' f x h1 _39209). Qed.
Lemma lem3614294 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (_39209 : A) : (term299 A B x s x' f _39209) = (term293 A B x s x' f _39209).
Proof. exact (eq_refl (term299 A B x s x' f _39209)). Qed.
Lemma lem3614295 {A B : Type'} (_39209 : A) (s : A -> Prop) (z : A) (x' : B) (f : A -> B) (x : A) (h1 : term268 A B s z x' f x) : term293 A B x s x' f _39209.
Proof. exact (EQ_MP (@lem3614294 A B x s x' f _39209) (@lem3614293 A B _39209 s z x' f x h1)). Qed.
Lemma lem3614309 {A B : Type'} (z : A) (s : A -> Prop) (x' : B) (f : A -> B) (x : A) (h1 : term236 A B z s x' f x) : x' = (f z).
Proof. exact (proj2 (@lem3614163 A B z s x' f x h1)). Qed.
Lemma lem3614311 {A : Type'} (z : A) (x : A) (h1 : z = x) : z = x.
Proof. exact (h1). Qed.
Lemma lem3614317 {A B : Type'} (_39207 : A) (z : A) (s : A -> Prop) (x' : B) (f : A -> B) (x : A) (h1 : term236 A B z s x' f x) : term200 A B s x' f _39207.
Proof. exact (EQ_MP (@lem3614288 A B s x' f _39207) (@lem3614287 A B _39207 z s x' f x h1)). Qed.
Lemma lem3614321 {A B : Type'} (z : A) (s : A -> Prop) (x' : B) (f : A -> B) (x : A) (h1 : term236 A B z s x' f x) : x' = (f z).
Proof. exact (proj2 (@lem3614163 A B z s x' f x h1)). Qed.
Lemma lem3614323 {A : Type'} (z : A) (s : A -> Prop) (h1 : @IN A z s) : @IN A z s.
Proof. exact (h1). Qed.
Lemma lem3614327 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (z : A) (h1 : term178 A B s x' f z) : x' = (f z).
Proof. exact (proj2 (@lem3614172 A B s x' f z h1)). Qed.
Lemma lem3614339 {A B : Type'} (_39208 : A) (s : A -> Prop) (z : A) (x' : B) (f : A -> B) (x : A) (h1 : term268 A B s z x' f x) : term200 A B s x' f _39208.
Proof. exact (proj2 (@lem3614292 A B _39208 s z x' f x h1)). Qed.
Lemma lem3614341 {A B : Type'} (x' : B) (f : A -> B) (x : A) (h1 : x' = (f x)) : x' = (f x).
Proof. exact (h1). Qed.
Lemma lem3614347 {A B : Type'} (_39209 : A) (s : A -> Prop) (z : A) (x' : B) (f : A -> B) (x : A) (h1 : term268 A B s z x' f x) : term300 A B x x' f _39209.
Proof. exact (proj1 (@lem3614295 A B _39209 s z x' f x h1)). Qed.
Lemma lem3614395 {A B : Type'} (z : A) (s : A -> Prop) (x' : B) (f : A -> B) (x : A) (h1 : term236 A B z s x' f x) : term184 A B x' f x.
Proof. exact (proj2 (@lem3614162 A B z s x' f x h1)). Qed.
Lemma lem3614396 {A B : Type'} (x' : B) (f : A -> B) : (term301 A B x' f) = (term301 A B x' f).
Proof. exact (eq_refl (term301 A B x' f)). Qed.
Lemma lem3614397 {A B : Type'} (x' : B) (f : A -> B) (z : A) (x : A) (h1 : z = x) : (term302 A B x' f z) = (term302 A B x' f x).
Proof. exact (MK_COMB (@lem3614396 A B x' f) (@lem3614311 A z x h1)). Qed.
Lemma lem3614398 {A B : Type'} (x' : B) (f : A -> B) (x : A) : (term302 A B x' f x) = (x' = (f x)).
Proof. exact (eq_refl (term302 A B x' f x)). Qed.
Lemma lem3614399 {A B : Type'} (x' : B) (f : A -> B) (z : A) : (term303 A B x' f z) = (term303 A B x' f z).
Proof. exact (eq_refl (term303 A B x' f z)). Qed.
Lemma lem3614400 {A B : Type'} (z : A) (x' : B) (f : A -> B) (x : A) : ((term302 A B x' f z) = (term302 A B x' f x)) = ((term302 A B x' f z) = (x' = (f x))).
Proof. exact (MK_COMB (@lem3614399 A B x' f z) (@lem3614398 A B x' f x)). Qed.
Lemma lem3614401 {A B : Type'} (x' : B) (f : A -> B) (z : A) : (term302 A B x' f z) = (x' = (f z)).
Proof. exact (eq_refl (term302 A B x' f z)). Qed.
Lemma lem3614402 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3614403 {A B : Type'} (x' : B) (f : A -> B) (z : A) : (term303 A B x' f z) = (term304 A B x' f z).
Proof. exact (MK_COMB (@lem3614402) (@lem3614401 A B x' f z)). Qed.
Lemma lem3614404 {A B : Type'} (x' : B) (f : A -> B) (x : A) : (x' = (f x)) = (x' = (f x)).
Proof. exact (eq_refl (x' = (f x))). Qed.
Lemma lem3614405 {A B : Type'} (z : A) (x' : B) (f : A -> B) (x : A) : ((term302 A B x' f z) = (x' = (f x))) = ((x' = (f z)) = (x' = (f x))).
Proof. exact (MK_COMB (@lem3614403 A B x' f z) (@lem3614404 A B x' f x)). Qed.
Lemma lem3614406 {A B : Type'} (z : A) (x' : B) (f : A -> B) (x : A) : ((term302 A B x' f z) = (term302 A B x' f x)) = ((x' = (f z)) = (x' = (f x))).
Proof. exact (TRANS (@lem3614400 A B z x' f x) (@lem3614405 A B z x' f x)). Qed.
Lemma lem3614407 {A B : Type'} (x' : B) (f : A -> B) (z : A) (x : A) (h1 : z = x) : (x' = (f z)) = (x' = (f x)).
Proof. exact (EQ_MP (@lem3614406 A B z x' f x) (@lem3614397 A B x' f z x h1)). Qed.
Lemma lem3614408 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (z : A) (x : A) (h1 : term236 A B z s x' f x) (h2 : z = x) : x' = (f x).
Proof. exact (EQ_MP (@lem3614407 A B x' f z x h2) (@lem3614309 A B z s x' f x h1)). Qed.
Lemma lem3614436 {A B : Type'} (f : A -> B) (x : A) : (term305 A B f x) = (term305 A B f x).
Proof. exact (eq_refl (term305 A B f x)). Qed.
Lemma lem3614437 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (z : A) (x : A) (h1 : term236 A B z s x' f x) (h2 : z = x) : (term306 A B f x x') = (term307 A B f x).
Proof. exact (MK_COMB (@lem3614436 A B f x) (@lem3614408 A B s x' f z x h1 h2)). Qed.
Lemma lem3614438 {A B : Type'} (f : A -> B) (x : A) : (term307 A B f x) = (term308 A B f x).
Proof. exact (eq_refl (term307 A B f x)). Qed.
Lemma lem3614439 {A B : Type'} (f : A -> B) (x : A) (x' : B) : (term309 A B f x x') = (term309 A B f x x').
Proof. exact (eq_refl (term309 A B f x x')). Qed.
Lemma lem3614440 {A B : Type'} (x' : B) (f : A -> B) (x : A) : ((term306 A B f x x') = (term307 A B f x)) = ((term306 A B f x x') = (term308 A B f x)).
Proof. exact (MK_COMB (@lem3614439 A B f x x') (@lem3614438 A B f x)). Qed.
Lemma lem3614441 {A B : Type'} (x' : B) (f : A -> B) (x : A) : (term306 A B f x x') = (term184 A B x' f x).
Proof. exact (eq_refl (term306 A B f x x')). Qed.
Lemma lem3614442 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3614443 {A B : Type'} (x' : B) (f : A -> B) (x : A) : (term309 A B f x x') = (term310 A B x' f x).
Proof. exact (MK_COMB (@lem3614442) (@lem3614441 A B x' f x)). Qed.
Lemma lem3614444 {A B : Type'} (f : A -> B) (x : A) : (term308 A B f x) = (term308 A B f x).
Proof. exact (eq_refl (term308 A B f x)). Qed.
Lemma lem3614445 {A B : Type'} (x' : B) (f : A -> B) (x : A) : ((term306 A B f x x') = (term308 A B f x)) = ((term184 A B x' f x) = (term308 A B f x)).
Proof. exact (MK_COMB (@lem3614443 A B x' f x) (@lem3614444 A B f x)). Qed.
Lemma lem3614446 {A B : Type'} (x' : B) (f : A -> B) (x : A) : ((term306 A B f x x') = (term307 A B f x)) = ((term184 A B x' f x) = (term308 A B f x)).
Proof. exact (TRANS (@lem3614440 A B x' f x) (@lem3614445 A B x' f x)). Qed.
Lemma lem3614447 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (z : A) (x : A) (h1 : term236 A B z s x' f x) (h2 : z = x) : (term184 A B x' f x) = (term308 A B f x).
Proof. exact (EQ_MP (@lem3614446 A B x' f x) (@lem3614437 A B s x' f z x h1 h2)). Qed.
Lemma lem3614448 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (z : A) (x : A) (h1 : term236 A B z s x' f x) (h2 : z = x) : term308 A B f x.
Proof. exact (EQ_MP (@lem3614447 A B s x' f z x h1 h2) (@lem3614395 A B z s x' f x h1)). Qed.
Lemma lem3614463 {A B : Type'} (s : A -> Prop) (f : A -> B) (_39207 : A) : (term311 A B s f _39207) = (term311 A B s f _39207).
Proof. exact (eq_refl (term311 A B s f _39207)). Qed.
Lemma lem3614464 {A B : Type'} (_39207 : A) (z : A) (s : A -> Prop) (x' : B) (f : A -> B) (x : A) (h1 : term236 A B z s x' f x) : (term312 A B s f _39207 x') = (term313 A B s _39207 f z).
Proof. exact (MK_COMB (@lem3614463 A B s f _39207) (@lem3614321 A B z s x' f x h1)). Qed.
Lemma lem3614465 {A B : Type'} (s : A -> Prop) (z : A) (f : A -> B) (_39207 : A) : (term313 A B s _39207 f z) = (term314 A B s z f _39207).
Proof. exact (eq_refl (term313 A B s _39207 f z)). Qed.
Lemma lem3614466 {A B : Type'} (s : A -> Prop) (f : A -> B) (_39207 : A) (x' : B) : (term315 A B s f _39207 x') = (term315 A B s f _39207 x').
Proof. exact (eq_refl (term315 A B s f _39207 x')). Qed.
Lemma lem3614467 {A B : Type'} (x' : B) (s : A -> Prop) (z : A) (f : A -> B) (_39207 : A) : ((term312 A B s f _39207 x') = (term313 A B s _39207 f z)) = ((term312 A B s f _39207 x') = (term314 A B s z f _39207)).
Proof. exact (MK_COMB (@lem3614466 A B s f _39207 x') (@lem3614465 A B s z f _39207)). Qed.
Lemma lem3614468 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (_39207 : A) : (term312 A B s f _39207 x') = (term200 A B s x' f _39207).
Proof. exact (eq_refl (term312 A B s f _39207 x')). Qed.
Lemma lem3614469 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3614470 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (_39207 : A) : (term315 A B s f _39207 x') = (term316 A B s x' f _39207).
Proof. exact (MK_COMB (@lem3614469) (@lem3614468 A B s x' f _39207)). Qed.
Lemma lem3614471 {A B : Type'} (s : A -> Prop) (z : A) (f : A -> B) (_39207 : A) : (term314 A B s z f _39207) = (term314 A B s z f _39207).
Proof. exact (eq_refl (term314 A B s z f _39207)). Qed.
Lemma lem3614472 {A B : Type'} (x' : B) (s : A -> Prop) (z : A) (f : A -> B) (_39207 : A) : ((term312 A B s f _39207 x') = (term314 A B s z f _39207)) = ((term200 A B s x' f _39207) = (term314 A B s z f _39207)).
Proof. exact (MK_COMB (@lem3614470 A B s x' f _39207) (@lem3614471 A B s z f _39207)). Qed.
Lemma lem3614473 {A B : Type'} (x' : B) (s : A -> Prop) (z : A) (f : A -> B) (_39207 : A) : ((term312 A B s f _39207 x') = (term313 A B s _39207 f z)) = ((term200 A B s x' f _39207) = (term314 A B s z f _39207)).
Proof. exact (TRANS (@lem3614467 A B x' s z f _39207) (@lem3614472 A B x' s z f _39207)). Qed.
Lemma lem3614474 {A B : Type'} (_39207 : A) (z : A) (s : A -> Prop) (x' : B) (f : A -> B) (x : A) (h1 : term236 A B z s x' f x) : (term200 A B s x' f _39207) = (term314 A B s z f _39207).
Proof. exact (EQ_MP (@lem3614473 A B x' s z f _39207) (@lem3614464 A B _39207 z s x' f x h1)). Qed.
Lemma lem3614475 {A B : Type'} (_39207 : A) (z : A) (s : A -> Prop) (x' : B) (f : A -> B) (x : A) (h1 : term236 A B z s x' f x) : term314 A B s z f _39207.
Proof. exact (EQ_MP (@lem3614474 A B _39207 z s x' f x h1) (@lem3614317 A B _39207 z s x' f x h1)). Qed.
Lemma lem3614502 {A : Type'} (z : A) (s : A -> Prop) (h1 : @IN A z s) : @IN A z s.
Proof. exact (h1). Qed.
Lemma lem3614544 {A B : Type'} (s : A -> Prop) (f : A -> B) (_39208 : A) : (term311 A B s f _39208) = (term311 A B s f _39208).
Proof. exact (eq_refl (term311 A B s f _39208)). Qed.
Lemma lem3614545 {A B : Type'} (_39208 : A) (s : A -> Prop) (x' : B) (f : A -> B) (z : A) (h1 : term178 A B s x' f z) : (term312 A B s f _39208 x') = (term313 A B s _39208 f z).
Proof. exact (MK_COMB (@lem3614544 A B s f _39208) (@lem3614327 A B s x' f z h1)). Qed.
Lemma lem3614546 {A B : Type'} (s : A -> Prop) (z : A) (f : A -> B) (_39208 : A) : (term313 A B s _39208 f z) = (term314 A B s z f _39208).
Proof. exact (eq_refl (term313 A B s _39208 f z)). Qed.
Lemma lem3614547 {A B : Type'} (s : A -> Prop) (f : A -> B) (_39208 : A) (x' : B) : (term315 A B s f _39208 x') = (term315 A B s f _39208 x').
Proof. exact (eq_refl (term315 A B s f _39208 x')). Qed.
Lemma lem3614548 {A B : Type'} (x' : B) (s : A -> Prop) (z : A) (f : A -> B) (_39208 : A) : ((term312 A B s f _39208 x') = (term313 A B s _39208 f z)) = ((term312 A B s f _39208 x') = (term314 A B s z f _39208)).
Proof. exact (MK_COMB (@lem3614547 A B s f _39208 x') (@lem3614546 A B s z f _39208)). Qed.
Lemma lem3614549 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (_39208 : A) : (term312 A B s f _39208 x') = (term200 A B s x' f _39208).
Proof. exact (eq_refl (term312 A B s f _39208 x')). Qed.
Lemma lem3614550 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3614551 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (_39208 : A) : (term315 A B s f _39208 x') = (term316 A B s x' f _39208).
Proof. exact (MK_COMB (@lem3614550) (@lem3614549 A B s x' f _39208)). Qed.
Lemma lem3614552 {A B : Type'} (s : A -> Prop) (z : A) (f : A -> B) (_39208 : A) : (term314 A B s z f _39208) = (term314 A B s z f _39208).
Proof. exact (eq_refl (term314 A B s z f _39208)). Qed.
Lemma lem3614553 {A B : Type'} (x' : B) (s : A -> Prop) (z : A) (f : A -> B) (_39208 : A) : ((term312 A B s f _39208 x') = (term314 A B s z f _39208)) = ((term200 A B s x' f _39208) = (term314 A B s z f _39208)).
Proof. exact (MK_COMB (@lem3614551 A B s x' f _39208) (@lem3614552 A B s z f _39208)). Qed.
Lemma lem3614554 {A B : Type'} (x' : B) (s : A -> Prop) (z : A) (f : A -> B) (_39208 : A) : ((term312 A B s f _39208 x') = (term313 A B s _39208 f z)) = ((term200 A B s x' f _39208) = (term314 A B s z f _39208)).
Proof. exact (TRANS (@lem3614548 A B x' s z f _39208) (@lem3614553 A B x' s z f _39208)). Qed.
Lemma lem3614555 {A B : Type'} (_39208 : A) (s : A -> Prop) (x' : B) (f : A -> B) (z : A) (h1 : term178 A B s x' f z) : (term200 A B s x' f _39208) = (term314 A B s z f _39208).
Proof. exact (EQ_MP (@lem3614554 A B x' s z f _39208) (@lem3614545 A B _39208 s x' f z h1)). Qed.
Lemma lem3614556 {A B : Type'} (_39208 : A) (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (z : A) (h1 : term268 A B s z x' f x) (h2 : term178 A B s x' f z) : term314 A B s z f _39208.
Proof. exact (EQ_MP (@lem3614555 A B _39208 s x' f z h2) (@lem3614339 A B _39208 s z x' f x h1)). Qed.
Lemma lem3614571 {A B : Type'} (x : A) (f : A -> B) (_39209 : A) : (term317 A B x f _39209) = (term317 A B x f _39209).
Proof. exact (eq_refl (term317 A B x f _39209)). Qed.
Lemma lem3614572 {A B : Type'} (_39209 : A) (x' : B) (f : A -> B) (x : A) (h1 : x' = (f x)) : (term318 A B x f _39209 x') = (term319 A B _39209 f x).
Proof. exact (MK_COMB (@lem3614571 A B x f _39209) (@lem3614341 A B x' f x h1)). Qed.
Lemma lem3614573 {A B : Type'} (x : A) (f : A -> B) (_39209 : A) : (term319 A B _39209 f x) = (term320 A B x f _39209).
Proof. exact (eq_refl (term319 A B _39209 f x)). Qed.
Lemma lem3614574 {A B : Type'} (x : A) (f : A -> B) (_39209 : A) (x' : B) : (term321 A B x f _39209 x') = (term321 A B x f _39209 x').
Proof. exact (eq_refl (term321 A B x f _39209 x')). Qed.
Lemma lem3614575 {A B : Type'} (x' : B) (x : A) (f : A -> B) (_39209 : A) : ((term318 A B x f _39209 x') = (term319 A B _39209 f x)) = ((term318 A B x f _39209 x') = (term320 A B x f _39209)).
Proof. exact (MK_COMB (@lem3614574 A B x f _39209 x') (@lem3614573 A B x f _39209)). Qed.
Lemma lem3614576 {A B : Type'} (x : A) (x' : B) (f : A -> B) (_39209 : A) : (term318 A B x f _39209 x') = (term300 A B x x' f _39209).
Proof. exact (eq_refl (term318 A B x f _39209 x')). Qed.
Lemma lem3614577 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3614578 {A B : Type'} (x : A) (x' : B) (f : A -> B) (_39209 : A) : (term321 A B x f _39209 x') = (term322 A B x x' f _39209).
Proof. exact (MK_COMB (@lem3614577) (@lem3614576 A B x x' f _39209)). Qed.
Lemma lem3614579 {A B : Type'} (x : A) (f : A -> B) (_39209 : A) : (term320 A B x f _39209) = (term320 A B x f _39209).
Proof. exact (eq_refl (term320 A B x f _39209)). Qed.
Lemma lem3614580 {A B : Type'} (x' : B) (x : A) (f : A -> B) (_39209 : A) : ((term318 A B x f _39209 x') = (term320 A B x f _39209)) = ((term300 A B x x' f _39209) = (term320 A B x f _39209)).
Proof. exact (MK_COMB (@lem3614578 A B x x' f _39209) (@lem3614579 A B x f _39209)). Qed.
Lemma lem3614581 {A B : Type'} (x' : B) (x : A) (f : A -> B) (_39209 : A) : ((term318 A B x f _39209 x') = (term319 A B _39209 f x)) = ((term300 A B x x' f _39209) = (term320 A B x f _39209)).
Proof. exact (TRANS (@lem3614575 A B x' x f _39209) (@lem3614580 A B x' x f _39209)). Qed.
Lemma lem3614582 {A B : Type'} (_39209 : A) (x' : B) (f : A -> B) (x : A) (h1 : x' = (f x)) : (term300 A B x x' f _39209) = (term320 A B x f _39209).
Proof. exact (EQ_MP (@lem3614581 A B x' x f _39209) (@lem3614572 A B _39209 x' f x h1)). Qed.
Lemma lem3614583 {A B : Type'} (_39209 : A) (s : A -> Prop) (z : A) (x' : B) (f : A -> B) (x : A) (h1 : term268 A B s z x' f x) (h2 : x' = (f x)) : term320 A B x f _39209.
Proof. exact (EQ_MP (@lem3614582 A B _39209 x' f x h2) (@lem3614347 A B _39209 s z x' f x h1)). Qed.
Lemma lem3614631 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem3614632 {B : Type'} (x : B) : x = x.
Proof. exact (@lem3614631 B x). Qed.
Lemma lem3614633 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (@lem3614632 B (f x)). Qed.
Lemma lem3614634 {A B : Type'} (f : A -> B) (x : A) : term323 A B f x.
Proof. exact (fun h0 : term308 A B f x => @lem3614633 A B f x). Qed.
Lemma lem3614636 (p : Prop) : (term324 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3614637 {A B : Type'} (f : A -> B) (x : A) : (term323 A B f x) = ((f x) = (f x)).
Proof. exact (@lem3614636 ((f x) = (f x))). Qed.
Lemma lem3614638 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (EQ_MP (@lem3614637 A B f x) (@lem3614634 A B f x)). Qed.
Lemma lem3614641 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3614643 {A B : Type'} (f : A -> B) (x : A) : (term308 A B f x) = (term325 A B f x).
Proof. exact (@lem3614641 ((f x) = (f x))). Qed.
Lemma lem3614646 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (z : A) (x : A) (h1 : term236 A B z s x' f x) (h2 : z = x) : term325 A B f x.
Proof. exact (EQ_MP (@lem3614643 A B f x) (@lem3614448 A B s x' f z x h1 h2)). Qed.
Lemma lem3614649 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (z : A) (x : A) (h1 : term236 A B z s x' f x) (h2 : z = x) : False.
Proof. exact (@lem3614646 A B s x' f z x h1 h2 (@lem3614638 A B f x)). Qed.
Lemma lem3614650 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (z : A) (x : A) (h1 : term236 A B z s x' f x) (h2 : z = x) : term326.
Proof. exact (fun h0 : ~ False => @lem3614649 A B s x' f z x h1 h2). Qed.
Lemma lem3614652 (p : Prop) : (term324 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3614653 : term326 = False.
Proof. exact (@lem3614652 False). Qed.
Lemma lem3614689 {A : Type'} (z : A) (s : A -> Prop) (h1 : @IN A z s) : @IN A z s.
Proof. exact (h1). Qed.
Lemma lem3614690 {A : Type'} (z : A) (s : A -> Prop) (h1 : @IN A z s) : term327 A z s.
Proof. exact (fun h0 : term295 A z s => @lem3614689 A z s h1). Qed.
Lemma lem3614692 (p : Prop) : (term324 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3614693 {A : Type'} (z : A) (s : A -> Prop) : (term327 A z s) = (@IN A z s).
Proof. exact (@lem3614692 (@IN A z s)). Qed.
Lemma lem3614694 {A : Type'} (z : A) (s : A -> Prop) (h1 : @IN A z s) : @IN A z s.
Proof. exact (EQ_MP (@lem3614693 A z s) (@lem3614690 A z s h1)). Qed.
Lemma lem3614696 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem3614697 {B : Type'} (x : B) : x = x.
Proof. exact (@lem3614696 B x). Qed.
Lemma lem3614698 {A B : Type'} (f : A -> B) (z : A) : (f z) = (f z).
Proof. exact (@lem3614697 B (f z)). Qed.
Lemma lem3614699 {A B : Type'} (f : A -> B) (z : A) : term323 A B f z.
Proof. exact (fun h0 : term308 A B f z => @lem3614698 A B f z). Qed.
Lemma lem3614701 (p : Prop) : (term324 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3614702 {A B : Type'} (f : A -> B) (z : A) : (term323 A B f z) = ((f z) = (f z)).
Proof. exact (@lem3614701 ((f z) = (f z))). Qed.
Lemma lem3614703 {A B : Type'} (f : A -> B) (z : A) : (f z) = (f z).
Proof. exact (EQ_MP (@lem3614702 A B f z) (@lem3614699 A B f z)). Qed.
Lemma lem3614705 (a : Prop) (b : Prop) : (term328 a b) = (term329 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3614706 {A B : Type'} (s : A -> Prop) (z : A) (f : A -> B) (_39207 : A) : (term314 A B s z f _39207) = (term330 A B s z f _39207).
Proof. exact (@lem3614705 (@IN A _39207 s) ((f z) = (f _39207))). Qed.
Lemma lem3614708 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3614709 {A B : Type'} (s : A -> Prop) (z : A) (f : A -> B) (_39207 : A) : (term330 A B s z f _39207) = (term331 A B s z f _39207).
Proof. exact (@lem3614708 (term332 A B s z f _39207)). Qed.
Lemma lem3614710 {A B : Type'} (s : A -> Prop) (z : A) (f : A -> B) (_39207 : A) : (term314 A B s z f _39207) = (term331 A B s z f _39207).
Proof. exact (TRANS (@lem3614706 A B s z f _39207) (@lem3614709 A B s z f _39207)). Qed.
Lemma lem3614712 {A B : Type'} (f : A -> B) (z : A) (s : A -> Prop) (h1 : @IN A z s) : term333 A B s f z.
Proof. exact (conj (@lem3614694 A z s h1) (@lem3614703 A B f z)). Qed.
Lemma lem3614714 {A B : Type'} (_39207 : A) (z : A) (s : A -> Prop) (x' : B) (f : A -> B) (x : A) (h1 : term236 A B z s x' f x) : term331 A B s z f _39207.
Proof. exact (EQ_MP (@lem3614710 A B s z f _39207) (@lem3614475 A B _39207 z s x' f x h1)). Qed.
Lemma lem3614715 {A B : Type'} (_39207 : A) (z : A) (s : A -> Prop) (x' : B) (f : A -> B) (x : A) (h1 : term236 A B z s x' f x) : term331 A B s z f _39207.
Proof. exact (@lem3614714 A B _39207 z s x' f x h1). Qed.
Lemma lem3614716 {A B : Type'} (z : A) (s : A -> Prop) (x' : B) (f : A -> B) (x : A) (h1 : term236 A B z s x' f x) : term334 A B s f z.
Proof. exact (@lem3614715 A B z z s x' f x h1). Qed.
Lemma lem3614719 {A B : Type'} (x' : B) (f : A -> B) (x : A) (z : A) (s : A -> Prop) (h1 : term236 A B z s x' f x) (h2 : @IN A z s) : False.
Proof. exact (@lem3614716 A B z s x' f x h1 (@lem3614712 A B f z s h2)). Qed.
Lemma lem3614720 {A B : Type'} (x' : B) (f : A -> B) (x : A) (z : A) (s : A -> Prop) (h1 : term236 A B z s x' f x) (h2 : @IN A z s) : term326.
Proof. exact (fun h0 : ~ False => @lem3614719 A B x' f x z s h1 h2). Qed.
Lemma lem3614722 (p : Prop) : (term324 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3614723 : term326 = False.
Proof. exact (@lem3614722 False). Qed.
Lemma lem3614724 {A B : Type'} (x' : B) (f : A -> B) (x : A) (z : A) (s : A -> Prop) (h1 : term236 A B z s x' f x) (h2 : @IN A z s) : False.
Proof. exact (EQ_MP (@lem3614723) (@lem3614720 A B x' f x z s h1 h2)). Qed.
Lemma lem3614759 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (z : A) (h1 : term178 A B s x' f z) : @IN A z s.
Proof. exact (proj1 (@lem3614172 A B s x' f z h1)). Qed.
Lemma lem3614760 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (z : A) (h1 : term178 A B s x' f z) : term327 A z s.
Proof. exact (fun h0 : term295 A z s => @lem3614759 A B s x' f z h1). Qed.
Lemma lem3614762 (p : Prop) : (term324 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3614763 {A : Type'} (z : A) (s : A -> Prop) : (term327 A z s) = (@IN A z s).
Proof. exact (@lem3614762 (@IN A z s)). Qed.
Lemma lem3614764 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (z : A) (h1 : term178 A B s x' f z) : @IN A z s.
Proof. exact (EQ_MP (@lem3614763 A z s) (@lem3614760 A B s x' f z h1)). Qed.
Lemma lem3614766 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem3614767 {B : Type'} (x : B) : x = x.
Proof. exact (@lem3614766 B x). Qed.
Lemma lem3614768 {A B : Type'} (f : A -> B) (z : A) : (f z) = (f z).
Proof. exact (@lem3614767 B (f z)). Qed.
Lemma lem3614769 {A B : Type'} (f : A -> B) (z : A) : term323 A B f z.
Proof. exact (fun h0 : term308 A B f z => @lem3614768 A B f z). Qed.
Lemma lem3614771 (p : Prop) : (term324 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3614772 {A B : Type'} (f : A -> B) (z : A) : (term323 A B f z) = ((f z) = (f z)).
Proof. exact (@lem3614771 ((f z) = (f z))). Qed.
Lemma lem3614773 {A B : Type'} (f : A -> B) (z : A) : (f z) = (f z).
Proof. exact (EQ_MP (@lem3614772 A B f z) (@lem3614769 A B f z)). Qed.
Lemma lem3614775 (a : Prop) (b : Prop) : (term328 a b) = (term329 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3614776 {A B : Type'} (s : A -> Prop) (z : A) (f : A -> B) (_39208 : A) : (term314 A B s z f _39208) = (term330 A B s z f _39208).
Proof. exact (@lem3614775 (@IN A _39208 s) ((f z) = (f _39208))). Qed.
Lemma lem3614778 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3614779 {A B : Type'} (s : A -> Prop) (z : A) (f : A -> B) (_39208 : A) : (term330 A B s z f _39208) = (term331 A B s z f _39208).
Proof. exact (@lem3614778 (term332 A B s z f _39208)). Qed.
Lemma lem3614780 {A B : Type'} (s : A -> Prop) (z : A) (f : A -> B) (_39208 : A) : (term314 A B s z f _39208) = (term331 A B s z f _39208).
Proof. exact (TRANS (@lem3614776 A B s z f _39208) (@lem3614779 A B s z f _39208)). Qed.
Lemma lem3614782 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (z : A) (h1 : term178 A B s x' f z) : term333 A B s f z.
Proof. exact (conj (@lem3614764 A B s x' f z h1) (@lem3614773 A B f z)). Qed.
Lemma lem3614784 {A B : Type'} (_39208 : A) (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (z : A) (h1 : term268 A B s z x' f x) (h2 : term178 A B s x' f z) : term331 A B s z f _39208.
Proof. exact (EQ_MP (@lem3614780 A B s z f _39208) (@lem3614556 A B _39208 x s x' f z h1 h2)). Qed.
Lemma lem3614785 {A B : Type'} (_39208 : A) (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (z : A) (h1 : term268 A B s z x' f x) (h2 : term178 A B s x' f z) : term331 A B s z f _39208.
Proof. exact (@lem3614784 A B _39208 x s x' f z h1 h2). Qed.
Lemma lem3614786 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (z : A) (h1 : term268 A B s z x' f x) (h2 : term178 A B s x' f z) : term334 A B s f z.
Proof. exact (@lem3614785 A B z x s x' f z h1 h2). Qed.
Lemma lem3614789 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (z : A) (h1 : term268 A B s z x' f x) (h2 : term178 A B s x' f z) : False.
Proof. exact (@lem3614786 A B x s x' f z h1 h2 (@lem3614782 A B s x' f z h2)). Qed.
Lemma lem3614790 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (z : A) (h1 : term268 A B s z x' f x) (h2 : term178 A B s x' f z) : term326.
Proof. exact (fun h0 : ~ False => @lem3614789 A B x s x' f z h1 h2). Qed.
Lemma lem3614792 (p : Prop) : (term324 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3614793 : term326 = False.
Proof. exact (@lem3614792 False). Qed.
Lemma lem3614829 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3614830 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3614829 A x). Qed.
Lemma lem3614831 {A : Type'} (x : A) : term335 A x.
Proof. exact (fun h0 : term336 A x => @lem3614830 A x). Qed.
Lemma lem3614833 (p : Prop) : (term324 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3614834 {A : Type'} (x : A) : (term335 A x) = (x = x).
Proof. exact (@lem3614833 (x = x)). Qed.
Lemma lem3614835 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem3614834 A x) (@lem3614831 A x)). Qed.
Lemma lem3614837 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem3614838 {B : Type'} (x : B) : x = x.
Proof. exact (@lem3614837 B x). Qed.
Lemma lem3614839 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (@lem3614838 B (f x)). Qed.
Lemma lem3614840 {A B : Type'} (f : A -> B) (x : A) : term323 A B f x.
Proof. exact (fun h0 : term308 A B f x => @lem3614839 A B f x). Qed.
Lemma lem3614842 (p : Prop) : (term324 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3614843 {A B : Type'} (f : A -> B) (x : A) : (term323 A B f x) = ((f x) = (f x)).
Proof. exact (@lem3614842 ((f x) = (f x))). Qed.
Lemma lem3614844 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (EQ_MP (@lem3614843 A B f x) (@lem3614840 A B f x)). Qed.
Lemma lem3614846 (a : Prop) (b : Prop) : (term328 a b) = (term329 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3614847 {A B : Type'} (x : A) (f : A -> B) (_39209 : A) : (term320 A B x f _39209) = (term337 A B x f _39209).
Proof. exact (@lem3614846 (_39209 = x) ((f x) = (f _39209))). Qed.
Lemma lem3614849 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3614850 {A B : Type'} (x : A) (f : A -> B) (_39209 : A) : (term337 A B x f _39209) = (term338 A B x f _39209).
Proof. exact (@lem3614849 (term339 A B x f _39209)). Qed.
Lemma lem3614851 {A B : Type'} (x : A) (f : A -> B) (_39209 : A) : (term320 A B x f _39209) = (term338 A B x f _39209).
Proof. exact (TRANS (@lem3614847 A B x f _39209) (@lem3614850 A B x f _39209)). Qed.
Lemma lem3614853 {A B : Type'} (f : A -> B) (x : A) : term340 A B f x.
Proof. exact (conj (@lem3614835 A x) (@lem3614844 A B f x)). Qed.
Lemma lem3614855 {A B : Type'} (_39209 : A) (s : A -> Prop) (z : A) (x' : B) (f : A -> B) (x : A) (h1 : term268 A B s z x' f x) (h2 : x' = (f x)) : term338 A B x f _39209.
Proof. exact (EQ_MP (@lem3614851 A B x f _39209) (@lem3614583 A B _39209 s z x' f x h1 h2)). Qed.
Lemma lem3614856 {A B : Type'} (_39209 : A) (s : A -> Prop) (z : A) (x' : B) (f : A -> B) (x : A) (h1 : term268 A B s z x' f x) (h2 : x' = (f x)) : term338 A B x f _39209.
Proof. exact (@lem3614855 A B _39209 s z x' f x h1 h2). Qed.
Lemma lem3614857 {A B : Type'} (s : A -> Prop) (z : A) (x' : B) (f : A -> B) (x : A) (h1 : term268 A B s z x' f x) (h2 : x' = (f x)) : term341 A B f x.
Proof. exact (@lem3614856 A B x s z x' f x h1 h2). Qed.
Lemma lem3614860 {A B : Type'} (s : A -> Prop) (z : A) (x' : B) (f : A -> B) (x : A) (h1 : term268 A B s z x' f x) (h2 : x' = (f x)) : False.
Proof. exact (@lem3614857 A B s z x' f x h1 h2 (@lem3614853 A B f x)). Qed.
Lemma lem3614861 {A B : Type'} (s : A -> Prop) (z : A) (x' : B) (f : A -> B) (x : A) (h1 : term268 A B s z x' f x) (h2 : x' = (f x)) : term326.
Proof. exact (fun h0 : ~ False => @lem3614860 A B s z x' f x h1 h2). Qed.
Lemma lem3614863 (p : Prop) : (term324 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3614864 : term326 = False.
Proof. exact (@lem3614863 False). Qed.
Lemma lem3614866 {A B : Type'} (s : A -> Prop) (z : A) (x' : B) (f : A -> B) (x : A) (h1 : term268 A B s z x' f x) (h2 : x' = (f x)) : False.
Proof. exact (EQ_MP (@lem3614864) (@lem3614861 A B s z x' f x h1 h2)). Qed.
Lemma lem3614867 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (z : A) (h1 : term268 A B s z x' f x) (h2 : term178 A B s x' f z) : False.
Proof. exact (EQ_MP (@lem3614793) (@lem3614790 A B x s x' f z h1 h2)). Qed.
Lemma lem3614868 {A B : Type'} (x' : B) (f : A -> B) (x : A) (z : A) (s : A -> Prop) (h1 : term236 A B z s x' f x) (h2 : @IN A z s) : (@IN A z s) = False.
Proof. exact (prop_ext (fun h3 : @IN A z s => @lem3614724 A B x' f x z s h1 h2) (fun h3 : False => @lem3614502 A z s h2)). Qed.
Lemma lem3614870 {A B : Type'} (x' : B) (f : A -> B) (x : A) (z : A) (s : A -> Prop) (h1 : term236 A B z s x' f x) (h2 : @IN A z s) : False.
Proof. exact (EQ_MP (@lem3614868 A B x' f x z s h1 h2) (@lem3614502 A z s h2)). Qed.
Lemma lem3614872 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (z : A) (x : A) (h1 : term236 A B z s x' f x) (h2 : z = x) : False.
Proof. exact (EQ_MP (@lem3614653) (@lem3614650 A B s x' f z x h1 h2)). Qed.
Lemma lem3614873 {A B : Type'} (s : A -> Prop) (z : A) (x' : B) (f : A -> B) (x : A) (h1 : term268 A B s z x' f x) (h2 : x' = (f x)) : (x' = (f x)) = False.
Proof. exact (prop_ext (fun h3 : x' = (f x) => @lem3614866 A B s z x' f x h1 h2) (fun h3 : False => @lem3614341 A B x' f x h2)). Qed.
Lemma lem3614874 {A B : Type'} (s : A -> Prop) (z : A) (x' : B) (f : A -> B) (x : A) (h1 : term268 A B s z x' f x) (h2 : x' = (f x)) : False.
Proof. exact (EQ_MP (@lem3614873 A B s z x' f x h1 h2) (@lem3614341 A B x' f x h2)). Qed.
Lemma lem3614875 {A B : Type'} (x' : B) (f : A -> B) (x : A) (z : A) (s : A -> Prop) (h1 : term236 A B z s x' f x) (h2 : @IN A z s) : (@IN A z s) = False.
Proof. exact (prop_ext (fun h3 : @IN A z s => @lem3614870 A B x' f x z s h1 h2) (fun h3 : False => @lem3614323 A z s h2)). Qed.
Lemma lem3614876 {A B : Type'} (x' : B) (f : A -> B) (x : A) (z : A) (s : A -> Prop) (h1 : term236 A B z s x' f x) (h2 : @IN A z s) : False.
Proof. exact (EQ_MP (@lem3614875 A B x' f x z s h1 h2) (@lem3614323 A z s h2)). Qed.
Lemma lem3614877 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (z : A) (x : A) (h1 : term236 A B z s x' f x) (h2 : z = x) : (z = x) = False.
Proof. exact (prop_ext (fun h3 : z = x => @lem3614872 A B s x' f z x h1 h2) (fun h3 : False => @lem3614311 A z x h2)). Qed.
Lemma lem3614878 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (z : A) (x : A) (h1 : term236 A B z s x' f x) (h2 : z = x) : False.
Proof. exact (EQ_MP (@lem3614877 A B s x' f z x h1 h2) (@lem3614311 A z x h2)). Qed.
Lemma lem3614879 {A B : Type'} (s : A -> Prop) (z : A) (x' : B) (f : A -> B) (x : A) (h1 : term268 A B s z x' f x) (h2 : x' = (f x)) : (x' = (f x)) = False.
Proof. exact (prop_ext (fun h3 : x' = (f x) => @lem3614874 A B s z x' f x h1 h2) (fun h3 : False => @lem3614283 A B x' f x h2)). Qed.
Lemma lem3614880 {A B : Type'} (s : A -> Prop) (z : A) (x' : B) (f : A -> B) (x : A) (h1 : term268 A B s z x' f x) (h2 : x' = (f x)) : False.
Proof. exact (EQ_MP (@lem3614879 A B s z x' f x h1 h2) (@lem3614283 A B x' f x h2)). Qed.
Lemma lem3614881 {A B : Type'} (x' : B) (f : A -> B) (x : A) (z : A) (s : A -> Prop) (h1 : term236 A B z s x' f x) (h2 : @IN A z s) : (@IN A z s) = False.
Proof. exact (prop_ext (fun h3 : @IN A z s => @lem3614876 A B x' f x z s h1 h2) (fun h3 : False => @lem3614225 A z s h2)). Qed.
Lemma lem3614882 {A B : Type'} (x' : B) (f : A -> B) (x : A) (z : A) (s : A -> Prop) (h1 : term236 A B z s x' f x) (h2 : @IN A z s) : False.
Proof. exact (EQ_MP (@lem3614881 A B x' f x z s h1 h2) (@lem3614225 A z s h2)). Qed.
Lemma lem3614883 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (z : A) (x : A) (h1 : term236 A B z s x' f x) (h2 : z = x) : (z = x) = False.
Proof. exact (prop_ext (fun h3 : z = x => @lem3614878 A B s x' f z x h1 h2) (fun h3 : False => @lem3614200 A z x h2)). Qed.
Lemma lem3614884 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (z : A) (x : A) (h1 : term236 A B z s x' f x) (h2 : z = x) : False.
Proof. exact (EQ_MP (@lem3614883 A B s x' f z x h1 h2) (@lem3614200 A z x h2)). Qed.
Lemma lem3614885 {A B : Type'} (s : A -> Prop) (z : A) (x' : B) (f : A -> B) (x : A) (h1 : term268 A B s z x' f x) (h2 : x' = (f x)) : (x' = (f x)) = False.
Proof. exact (prop_ext (fun h3 : x' = (f x) => @lem3614880 A B s z x' f x h1 h2) (fun h3 : False => @lem3614283 A B x' f x h2)). Qed.
Lemma lem3614886 {A B : Type'} (s : A -> Prop) (z : A) (x' : B) (f : A -> B) (x : A) (h1 : term268 A B s z x' f x) (h2 : x' = (f x)) : False.
Proof. exact (EQ_MP (@lem3614885 A B s z x' f x h1 h2) (@lem3614283 A B x' f x h2)). Qed.
Lemma lem3614887 {A B : Type'} (x' : B) (f : A -> B) (x : A) (z : A) (s : A -> Prop) (h1 : term236 A B z s x' f x) (h2 : @IN A z s) : (@IN A z s) = False.
Proof. exact (prop_ext (fun h3 : @IN A z s => @lem3614882 A B x' f x z s h1 h2) (fun h3 : False => @lem3614225 A z s h2)). Qed.
Lemma lem3614888 {A B : Type'} (x' : B) (f : A -> B) (x : A) (z : A) (s : A -> Prop) (h1 : term236 A B z s x' f x) (h2 : @IN A z s) : False.
Proof. exact (EQ_MP (@lem3614887 A B x' f x z s h1 h2) (@lem3614225 A z s h2)). Qed.
Lemma lem3614889 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (z : A) (x : A) (h1 : term236 A B z s x' f x) (h2 : z = x) : (z = x) = False.
Proof. exact (prop_ext (fun h3 : z = x => @lem3614884 A B s x' f z x h1 h2) (fun h3 : False => @lem3614200 A z x h2)). Qed.
Lemma lem3614890 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (z : A) (x : A) (h1 : term236 A B z s x' f x) (h2 : z = x) : False.
Proof. exact (EQ_MP (@lem3614889 A B s x' f z x h1 h2) (@lem3614200 A z x h2)). Qed.
Lemma lem3614891 {A B : Type'} (s : A -> Prop) (z : A) (x' : B) (f : A -> B) (x : A) (h1 : term268 A B s z x' f x) : False.
Proof. exact (or_elim (@lem3614170 A B s z x' f x h1) (fun h0 : term178 A B s x' f z => @lem3614867 A B x s x' f z h1 h0) (fun h0 : x' = (f x) => @lem3614886 A B s z x' f x h1 h0)). Qed.
Lemma lem3614892 {A B : Type'} (z : A) (s : A -> Prop) (x' : B) (f : A -> B) (x : A) (h1 : term236 A B z s x' f x) : False.
Proof. exact (or_elim (@lem3614167 A B z s x' f x h1) (fun h0 : z = x => @lem3614890 A B s x' f z x h1 h0) (fun h0 : @IN A z s => @lem3614888 A B x' f x z s h1 h0)). Qed.
Lemma lem3614893 {A B : Type'} (s : A -> Prop) (z : A) (x' : B) (f : A -> B) (x : A) (h1 : term289 A B s z x' f x) : False.
Proof. exact (or_elim (@lem3614159 A B s z x' f x h1) (fun h0 : term236 A B z s x' f x => @lem3614892 A B z s x' f x h0) (fun h0 : term268 A B s z x' f x => @lem3614891 A B s z x' f x h0)). Qed.
Lemma lem3614894 {A B : Type'} (s : A -> Prop) (z : A) (x' : B) (f : A -> B) (x : A) (h1 : term289 A B s z x' f x) : (term289 A B s z x' f x) = False.
Proof. exact (prop_ext (fun h2 : term289 A B s z x' f x => @lem3614893 A B s z x' f x h1) (fun h2 : False => @lem3614159 A B s z x' f x h1)). Qed.
Lemma lem3614895 {A B : Type'} (s : A -> Prop) (z : A) (x' : B) (f : A -> B) (x : A) (h1 : term289 A B s z x' f x) : False.
Proof. exact (EQ_MP (@lem3614894 A B s z x' f x h1) (@lem3614159 A B s z x' f x h1)). Qed.
Lemma lem3614896 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) (h1 : term181 A B s x' f x) : False.
Proof. exact (ex_elim (@lem3614034 A B s x' f x h1) (fun z : A => fun h0 : term291 A B s x' f x z => @lem3614895 A B s z x' f x h0)). Qed.
Lemma lem3614897 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) (h1 : term181 A B s x' f x) : (term181 A B s x' f x) = False.
Proof. exact (prop_ext (fun h2 : term181 A B s x' f x => @lem3614896 A B s x' f x h1) (fun h2 : False => @lem3613655 A B s x' f x h1)). Qed.
Lemma lem3614898 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) (h1 : term181 A B s x' f x) : False.
Proof. exact (EQ_MP (@lem3614897 A B s x' f x h1) (@lem3613655 A B s x' f x h1)). Qed.
Lemma lem3614899 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : term180 A B s x' f x.
Proof. exact (fun h0 : term181 A B s x' f x => @lem3614898 A B s x' f x h0). Qed.
Lemma lem3614900 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term124 A B x s x' f) = (term154 A B s x' f x).
Proof. exact (EQ_MP (@lem3613654 A B s x' f x) (@lem3614899 A B s x' f x)). Qed.
Lemma lem3614905 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : term157 A B s f x.
Proof. exact (fun x' : B => @lem3614900 A B s x' f x). Qed.
Lemma lem3614910 {A B : Type'} (f : A -> B) (x : A) : term169 A B f x.
Proof. exact (fun s : A -> Prop => @lem3614905 A B s f x). Qed.
Lemma lem3614915 {A B : Type'} (x : A) : term173 A B x.
Proof. exact (fun f : A -> B => @lem3614910 A B f x). Qed.
Lemma lem3614920 {A B : Type'} : term177 A B.
Proof. exact (fun x : A => @lem3614915 A B x). Qed.
Lemma lem3614921 {A B : Type'} : term176 A B.
Proof. exact (EQ_MP (@lem3613650 A B) (@lem3614920 A B)). Qed.
Lemma lem3614922 {A B : Type'} (x : A) : term342 A B x.
Proof. exact (@lem3614921 A B x). Qed.
Lemma lem3614923 {A B : Type'} (x : A) : (term342 A B x) = (term172 A B x).
Proof. exact (eq_refl (term342 A B x)). Qed.
Lemma lem3614924 {A B : Type'} (x : A) : term172 A B x.
Proof. exact (EQ_MP (@lem3614923 A B x) (@lem3614922 A B x)). Qed.
Lemma lem3614925 {A B : Type'} (x : A) (f : A -> B) : term343 A B x f.
Proof. exact (@lem3614924 A B x f). Qed.
Lemma lem3614926 {A B : Type'} (f : A -> B) (x : A) : (term343 A B x f) = (term168 A B f x).
Proof. exact (eq_refl (term343 A B x f)). Qed.
Lemma lem3614927 {A B : Type'} (f : A -> B) (x : A) : term168 A B f x.
Proof. exact (EQ_MP (@lem3614926 A B f x) (@lem3614925 A B x f)). Qed.
Lemma lem3614928 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : term344 A B f x s.
Proof. exact (@lem3614927 A B f x s). Qed.
Lemma lem3614929 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term344 A B f x s) = (term159 A B s f x).
Proof. exact (eq_refl (term344 A B f x s)). Qed.
Lemma lem3614930 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : term159 A B s f x.
Proof. exact (EQ_MP (@lem3614929 A B s f x) (@lem3614928 A B f x s)). Qed.
Lemma lem3614932 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : term159 A B s f x.
Proof. exact (@lem3613411 A B s f x (@lem3614930 A B s f x)). Qed.
Lemma lem3614933 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : term160 A B s f x) : False.
Proof. exact (@lem3614932 A B s f x (@lem3613395 A B s f x h1)). Qed.
Lemma lem3614934 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : term160 A B s f x) : (term160 A B s f x) = False.
Proof. exact (prop_ext (fun h2 : term160 A B s f x => @lem3614933 A B s f x h1) (fun h2 : False => @lem3613395 A B s f x h1)). Qed.
Lemma lem3614935 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : term160 A B s f x) : False.
Proof. exact (EQ_MP (@lem3614934 A B s f x h1) (@lem3613395 A B s f x h1)). Qed.
Lemma lem3614936 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : term159 A B s f x.
Proof. exact (fun h0 : term160 A B s f x => @lem3614935 A B s f x h0). Qed.
Lemma lem3614937 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : term157 A B s f x.
Proof. exact (EQ_MP (@lem3613394 A B s f x) (@lem3614936 A B s f x)). Qed.
Lemma lem3614938 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term95 A B x s f) = (term96 A B s f x).
Proof. exact (EQ_MP (@lem3613390 A B s f x) (@lem3614937 A B s f x)). Qed.
Lemma lem3614954 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term7 A s t) = (term8 A s t).
Proof. exact (EQ_MP (@lem3612917 A s t) (@lem3612916 A s t)). Qed.
Lemma lem3614955 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term7 B s t) = (term8 B s t).
Proof. exact (@lem3614954 B s t). Qed.
Lemma lem3614956 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term97 A B s f x) = (term345 A B s f x).
Proof. exact (@lem3614955 B (term128 A B s f) (term129 A B f x)). Qed.
Lemma lem3614972 {A : Type'} (x : A) (s : A -> Prop) : (term3 A x s) = (@FINITE A s).
Proof. exact (EQ_MP (@lem3612911 A x s) (@lem3612910 A s x)). Qed.
Lemma lem3614973 {B : Type'} (x : B) (s : B -> Prop) : (term3 B x s) = (@FINITE B s).
Proof. exact (@lem3614972 B x s). Qed.
Lemma lem3614974 {A B : Type'} (f : A -> B) (x : A) : (term346 A B f x) = (@FINITE B (@EMPTY B)).
Proof. exact (@lem3614973 B (f x) (@EMPTY B)). Qed.
Lemma lem3614976 {A : Type'} : (@FINITE A (@EMPTY A)) = True.
Proof. exact (EQ_MP (@lem3612905 A) (@lem3612904 A)). Qed.
Lemma lem3614977 {B : Type'} : (@FINITE B (@EMPTY B)) = True.
Proof. exact (@lem3614976 B). Qed.
Lemma lem3614978 {A B : Type'} (f : A -> B) (x : A) : (term346 A B f x) = True.
Proof. exact (TRANS (@lem3614974 A B f x) (@lem3614977 B)). Qed.
Lemma lem3614979 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term347 A B s f) = (term347 A B s f).
Proof. exact (eq_refl (term347 A B s f)). Qed.
Lemma lem3614980 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) : (term345 A B s f x) = (term348 A B s f).
Proof. exact (MK_COMB (@lem3614979 A B s f) (@lem3614978 A B f x)). Qed.
Lemma lem3614982 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem3614983 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term348 A B s f) = (term49 A B s f).
Proof. exact (@lem3614982 (term49 A B s f)). Qed.
Lemma lem3614996 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) : (term345 A B s f x) = (term49 A B s f).
Proof. exact (TRANS (@lem3614980 A B x s f) (@lem3614983 A B s f)). Qed.
Lemma lem3614997 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) : (term97 A B s f x) = (term49 A B s f).
Proof. exact (TRANS (@lem3614956 A B s f x) (@lem3614996 A B x s f)). Qed.
Lemma lem3614998 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term51 A B s f) = (term51 A B s f).
Proof. exact (eq_refl (term51 A B s f)). Qed.
Lemma lem3614999 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) : (term98 A B s f x) = (term349 A B s f).
Proof. exact (MK_COMB (@lem3614998 A B s f) (@lem3614997 A B x s f)). Qed.
Lemma lem3615001 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem3615002 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term349 A B s f) = True.
Proof. exact (@lem3615001 (term49 A B s f)). Qed.
Lemma lem3615005 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term350 A B s f) = (term350 A B s f).
Proof. exact (eq_refl (term350 A B s f)). Qed.
Lemma lem3615006 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term350 A B s f) = ((term349 A B s f) = True).
Proof. exact (eq_refl (term350 A B s f)). Qed.
Lemma lem3615007 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term351 A B s f) = (term351 A B s f).
Proof. exact (eq_refl (term351 A B s f)). Qed.
Lemma lem3615008 {A B : Type'} (s : A -> Prop) (f : A -> B) : ((term350 A B s f) = (term350 A B s f)) = ((term350 A B s f) = ((term349 A B s f) = True)).
Proof. exact (MK_COMB (@lem3615007 A B s f) (@lem3615006 A B s f)). Qed.
Lemma lem3615009 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term350 A B s f) = ((term349 A B s f) = True).
Proof. exact (eq_refl (term350 A B s f)). Qed.
Lemma lem3615010 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3615011 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term351 A B s f) = (term352 A B s f).
Proof. exact (MK_COMB (@lem3615010) (@lem3615009 A B s f)). Qed.
Lemma lem3615012 {A B : Type'} (s : A -> Prop) (f : A -> B) : ((term349 A B s f) = True) = ((term349 A B s f) = True).
Proof. exact (eq_refl ((term349 A B s f) = True)). Qed.
Lemma lem3615013 {A B : Type'} (s : A -> Prop) (f : A -> B) : ((term350 A B s f) = ((term349 A B s f) = True)) = (((term349 A B s f) = True) = ((term349 A B s f) = True)).
Proof. exact (MK_COMB (@lem3615011 A B s f) (@lem3615012 A B s f)). Qed.
Lemma lem3615014 {A B : Type'} (s : A -> Prop) (f : A -> B) : ((term350 A B s f) = (term350 A B s f)) = (((term349 A B s f) = True) = ((term349 A B s f) = True)).
Proof. exact (TRANS (@lem3615008 A B s f) (@lem3615013 A B s f)). Qed.
Lemma lem3615015 {A B : Type'} (s : A -> Prop) (f : A -> B) : ((term349 A B s f) = True) = ((term349 A B s f) = True).
Proof. exact (EQ_MP (@lem3615014 A B s f) (@lem3615005 A B s f)). Qed.
Lemma lem3615016 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term349 A B s f) = True.
Proof. exact (EQ_MP (@lem3615015 A B s f) (@lem3615002 A B s f)). Qed.
Lemma lem3615017 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term98 A B s f x) = True.
Proof. exact (TRANS (@lem3614999 A B x s f) (@lem3615016 A B s f)). Qed.
Lemma lem3615018 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : True = (term98 A B s f x).
Proof. exact (SYM (@lem3615017 A B s f x)). Qed.
Lemma lem3615019 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : term98 A B s f x.
Proof. exact (EQ_MP (@lem3615018 A B s f x) (@lem0)). Qed.
Lemma lem3615020 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : (term95 A B x s f) = (term96 A B s f x)) : term55 A B x s f.
Proof. exact (EQ_MP (@lem3613236 A B s f x h1) (@lem3615019 A B s f x)). Qed.
Lemma lem3615021 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) : ((term95 A B x s f) = (term96 A B s f x)) = (term55 A B x s f).
Proof. exact (prop_ext (fun h1 : (term95 A B x s f) = (term96 A B s f x) => @lem3615020 A B s f x h1) (fun h1 : term55 A B x s f => @lem3614938 A B s f x)). Qed.
Lemma lem3615022 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) : term55 A B x s f.
Proof. exact (EQ_MP (@lem3615021 A B x s f) (@lem3614938 A B s f x)). Qed.
Lemma lem3615027 {A B : Type'} (x : A) (f : A -> B) : term59 A B x f.
Proof. exact (fun s : A -> Prop => @lem3615022 A B x s f). Qed.
Lemma lem3615032 {A B : Type'} (f : A -> B) : term63 A B f.
Proof. exact (fun x : A => @lem3615027 A B x f). Qed.
Lemma lem3615033 {A B : Type'} (f : A -> B) : term65 A B f.
Proof. exact (EQ_MP (@lem3613199 A B f) (@lem3615032 A B f)). Qed.
Lemma lem3615034 {A B : Type'} (f : A -> B) : term74 A B f.
Proof. exact (@lem3613065 A B f (@lem3615033 A B f)). Qed.
Lemma lem3615039 {A B : Type'} : term353 A B.
Proof. exact (fun f : A -> B => @lem3615034 A B f). Qed.
