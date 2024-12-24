Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CHOICE_PAIRED_THM_term_abbrevs.
Require Import EXISTS_PAIR_THM_spec.
Require Import LAMBDA_PAIR_THM_spec.
Require Import PAIR_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm18394_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm19732_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm48213_spec.
Require Import thm48214_spec.
Require Import thm48219_spec.
Require Import thm48220_spec.
Require Import thm51_spec.
Lemma lem56956 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : term0 _5131 _5132 P.
Proof. exact (@lem51006 _5131 _5132 P). Qed.
Lemma lem56957 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term0 _5131 _5132 P) = ((term1 _5131 _5132 P) = (term2 _5131 _5132 P)).
Proof. exact (eq_refl (term0 _5131 _5132 P)). Qed.
Lemma lem56960 {A B : Type'} (x : prod A B) (h1 : (term3 A B x) = x) : (term3 A B x) = x.
Proof. exact (h1). Qed.
Lemma lem56961 {A B : Type'} (x : prod A B) (h1 : (term3 A B x) = x) : x = (term3 A B x).
Proof. exact (SYM (@lem56960 A B x h1)). Qed.
Lemma lem56962 {A B : Type'} (x : prod A B) (h1 : x = (term3 A B x)) : x = (term3 A B x).
Proof. exact (h1). Qed.
Lemma lem56963 {A B : Type'} (x : prod A B) (h1 : x = (term3 A B x)) : (term3 A B x) = x.
Proof. exact (SYM (@lem56962 A B x h1)). Qed.
Lemma lem56964 {A B : Type'} (x : prod A B) : ((term3 A B x) = x) = (x = (term3 A B x)).
Proof. exact (prop_ext (fun h1 : (term3 A B x) = x => @lem56961 A B x h1) (fun h1 : x = (term3 A B x) => @lem56963 A B x h1)). Qed.
Lemma lem56965 {A B : Type'} : (term4 A B) = (term5 A B).
Proof. exact (fun_ext (fun x : prod A B => @lem56964 A B x)). Qed.
Lemma lem56966 {A B : Type'} : (@all (prod A B)) = (@all (prod A B)).
Proof. exact (eq_refl (@all (prod A B))). Qed.
Lemma lem56967 {A B : Type'} : (term6 A B) = (term7 A B).
Proof. exact (MK_COMB (@lem56966 A B) (@lem56965 A B)). Qed.
Lemma lem56968 {A B : Type'} : term7 A B.
Proof. exact (EQ_MP (@lem56967 A B) (@lem48081 A B)). Qed.
Lemma lem56969 {A B : Type'} (x : prod A B) : term8 A B x.
Proof. exact (@lem56968 A B x). Qed.
Lemma lem56970 {A B : Type'} (x : prod A B) : (term8 A B x) = (x = (term3 A B x)).
Proof. exact (eq_refl (term8 A B x)). Qed.
Lemma lem56972 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) : term9 _5146 _5153 _5154 t.
Proof. exact (@lem51291 _5146 _5153 _5154 t). Qed.
Lemma lem56973 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) : (term9 _5146 _5153 _5154 t) = ((term10 _5146 _5153 _5154 t) = (term11 _5146 _5153 _5154 t)).
Proof. exact (eq_refl (term9 _5146 _5153 _5154 t)). Qed.
Lemma lem56979 {A B : Type'} (P : type1413 A B) (Q : type1210 A B) (h1 : term12 A B P Q) : term12 A B P Q.
Proof. exact (h1). Qed.
Lemma lem56980 {A B : Type'} (P : type1413 A B) (Q : type1210 A B) (h1 : term13 A B P Q) : term13 A B P Q.
Proof. exact (h1). Qed.
Lemma lem56981 {A B : Type'} (P : type1413 A B) (h1 : term14 A B P) : term14 A B P.
Proof. exact (h1). Qed.
Lemma lem56982 {A B : Type'} (P : type1413 A B) (x0 : A) (h1 : term15 A B P x0) : term15 A B P x0.
Proof. exact (h1). Qed.
Lemma lem56983 {A B : Type'} (P : type1413 A B) (x0 : A) (y0 : B) (h1 : P x0 y0) : P x0 y0.
Proof. exact (h1). Qed.
Lemma lem56984 {A B : Type'} (P : type1413 A B) (h1 : (term16 A B P) = (term17 A B P)) : (term16 A B P) = (term17 A B P).
Proof. exact (h1). Qed.
Lemma lem56985 {A B : Type'} (Q : type1210 A B) : (term18 A B Q) = (term18 A B Q).
Proof. exact (eq_refl (term18 A B Q)). Qed.
Lemma lem56986 {A B : Type'} (Q : type1210 A B) (P : type1413 A B) (h1 : (term16 A B P) = (term17 A B P)) : (term19 A B Q P) = (term20 A B Q P).
Proof. exact (MK_COMB (@lem56985 A B Q) (@lem56984 A B P h1)). Qed.
Lemma lem56987 {A B : Type'} (Q : type1210 A B) (P : type1413 A B) : (term20 A B Q P) = (term21 A B Q P).
Proof. exact (eq_refl (term20 A B Q P)). Qed.
Lemma lem56988 {A B : Type'} (Q : type1210 A B) (P : type1413 A B) : (term22 A B Q P) = (term22 A B Q P).
Proof. exact (eq_refl (term22 A B Q P)). Qed.
Lemma lem56989 {A B : Type'} (Q : type1210 A B) (P : type1413 A B) : ((term19 A B Q P) = (term20 A B Q P)) = ((term19 A B Q P) = (term21 A B Q P)).
Proof. exact (MK_COMB (@lem56988 A B Q P) (@lem56987 A B Q P)). Qed.
Lemma lem56990 {A B : Type'} (Q : type1210 A B) (P : type1413 A B) : (term19 A B Q P) = (term23 A B Q P).
Proof. exact (eq_refl (term19 A B Q P)). Qed.
Lemma lem56991 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem56992 {A B : Type'} (Q : type1210 A B) (P : type1413 A B) : (term22 A B Q P) = (term24 A B Q P).
Proof. exact (MK_COMB (@lem56991) (@lem56990 A B Q P)). Qed.
Lemma lem56993 {A B : Type'} (Q : type1210 A B) (P : type1413 A B) : (term21 A B Q P) = (term21 A B Q P).
Proof. exact (eq_refl (term21 A B Q P)). Qed.
Lemma lem56994 {A B : Type'} (Q : type1210 A B) (P : type1413 A B) : ((term19 A B Q P) = (term21 A B Q P)) = ((term23 A B Q P) = (term21 A B Q P)).
Proof. exact (MK_COMB (@lem56992 A B Q P) (@lem56993 A B Q P)). Qed.
Lemma lem56995 {A B : Type'} (Q : type1210 A B) (P : type1413 A B) : ((term19 A B Q P) = (term20 A B Q P)) = ((term23 A B Q P) = (term21 A B Q P)).
Proof. exact (TRANS (@lem56989 A B Q P) (@lem56994 A B Q P)). Qed.
Lemma lem56996 {A B : Type'} (Q : type1210 A B) (P : type1413 A B) (h1 : (term16 A B P) = (term17 A B P)) : (term23 A B Q P) = (term21 A B Q P).
Proof. exact (EQ_MP (@lem56995 A B Q P) (@lem56986 A B Q P h1)). Qed.
Lemma lem56997 {A B : Type'} (Q : type1210 A B) (P : type1413 A B) (h1 : (term16 A B P) = (term17 A B P)) : (term21 A B Q P) = (term23 A B Q P).
Proof. exact (SYM (@lem56996 A B Q P h1)). Qed.
Lemma lem57015 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) : (term10 _5146 _5153 _5154 t) = (term11 _5146 _5153 _5154 t).
Proof. exact (EQ_MP (@lem56973 _5146 _5153 _5154 t) (@lem56972 _5146 _5153 _5154 t)). Qed.
Lemma lem57016 {A B : Type'} (t : type1210 A B) : (term25 A B t) = (term26 A B t).
Proof. exact (@lem57015 Prop B A t). Qed.
Lemma lem57017 {A B : Type'} (P : type1413 A B) : (term27 A B P) = (term28 A B P).
Proof. exact (@lem57016 A B (term17 A B P)). Qed.
Lemma lem57018 {A B : Type'} (P : type1413 A B) (p : prod A B) : (term29 A B P p) = (term30 A B P p).
Proof. exact (eq_refl (term29 A B P p)). Qed.
Lemma lem57019 {A B : Type'} (P : type1413 A B) : (term27 A B P) = (term17 A B P).
Proof. exact (fun_ext (fun p : prod A B => @lem57018 A B P p)). Qed.
Lemma lem57020 {A B : Type'} : (@eq ((prod A B) -> Prop)) = (@eq ((prod A B) -> Prop)).
Proof. exact (eq_refl (@eq ((prod A B) -> Prop))). Qed.
Lemma lem57021 {A B : Type'} (P : type1413 A B) : (term31 A B P) = (term32 A B P).
Proof. exact (MK_COMB (@lem57020 A B) (@lem57019 A B P)). Qed.
Lemma lem57022 {A B : Type'} (P : type1413 A B) (x : A) (y : B) : (term33 A B P x y) = (term34 A B P x y).
Proof. exact (eq_refl (term33 A B P x y)). Qed.
Lemma lem57023 {A B : Type'} (f : type1210 A B) (x : A) (y : B) : (term35 A B f x y) = (term35 A B f x y).
Proof. exact (eq_refl (term35 A B f x y)). Qed.
Lemma lem57024 {A B : Type'} (f : type1210 A B) (P : type1413 A B) (x : A) (y : B) : (term36 A B f P x y) = (term37 A B f P x y).
Proof. exact (MK_COMB (@lem57023 A B f x y) (@lem57022 A B P x y)). Qed.
Lemma lem57025 {A B : Type'} (f : type1210 A B) (P : type1413 A B) (x : A) : (term38 A B f P x) = (term39 A B f P x).
Proof. exact (fun_ext (fun y : B => @lem57024 A B f P x y)). Qed.
Lemma lem57026 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem57027 {A B : Type'} (f : type1210 A B) (P : type1413 A B) (x : A) : (term40 A B f P x) = (term41 A B f P x).
Proof. exact (MK_COMB (@lem57026 B) (@lem57025 A B f P x)). Qed.
Lemma lem57028 {A B : Type'} (f : type1210 A B) (P : type1413 A B) : (term42 A B f P) = (term43 A B f P).
Proof. exact (fun_ext (fun x : A => @lem57027 A B f P x)). Qed.
Lemma lem57029 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem57030 {A B : Type'} (f : type1210 A B) (P : type1413 A B) : (term44 A B f P) = (term45 A B f P).
Proof. exact (MK_COMB (@lem57029 A) (@lem57028 A B f P)). Qed.
Lemma lem57031 {A B : Type'} (P : type1413 A B) : (term46 A B P) = (term47 A B P).
Proof. exact (fun_ext (fun f : type1210 A B => @lem57030 A B f P)). Qed.
Lemma lem57032 {A B : Type'} : (@GABS ((prod A B) -> Prop)) = (@GABS ((prod A B) -> Prop)).
Proof. exact (eq_refl (@GABS ((prod A B) -> Prop))). Qed.
Lemma lem57033 {A B : Type'} (P : type1413 A B) : (term28 A B P) = (term48 A B P).
Proof. exact (MK_COMB (@lem57032 A B) (@lem57031 A B P)). Qed.
Lemma lem57034 {A B : Type'} (P : type1413 A B) : ((term27 A B P) = (term28 A B P)) = ((term17 A B P) = (term48 A B P)).
Proof. exact (MK_COMB (@lem57021 A B P) (@lem57033 A B P)). Qed.
Lemma lem57035 {A B : Type'} (P : type1413 A B) : (term17 A B P) = (term48 A B P).
Proof. exact (EQ_MP (@lem57034 A B P) (@lem57017 A B P)). Qed.
Lemma lem57051 {A B : Type'} (y : B) (x : A) : (term49 A B x y) = x.
Proof. exact (EQ_MP (@lem48220 A B y x) (@lem48219 A B x y)). Qed.
Lemma lem57052 {A B : Type'} (y : B) (x : A) : (term49 A B x y) = x.
Proof. exact (@lem57051 A B y x). Qed.
Lemma lem57053 {A B : Type'} (P : type1413 A B) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem57054 {A B : Type'} (y : B) (P : type1413 A B) (x : A) : (term50 A B P x y) = (P x).
Proof. exact (MK_COMB (@lem57053 A B P) (@lem57052 A B y x)). Qed.
Lemma lem57056 {A B : Type'} (x : A) (y : B) : (term51 A B x y) = y.
Proof. exact (EQ_MP (@lem48214 A B x y) (@lem48213 A B x y)). Qed.
Lemma lem57057 {A B : Type'} (x : A) (y : B) : (term51 A B x y) = y.
Proof. exact (@lem57056 A B x y). Qed.
Lemma lem57058 {A B : Type'} (P : type1413 A B) (x : A) (y : B) : (term34 A B P x y) = (P x y).
Proof. exact (MK_COMB (@lem57054 A B y P x) (@lem57057 A B x y)). Qed.
Lemma lem57059 {A B : Type'} (f : type1210 A B) (x : A) (y : B) : (term35 A B f x y) = (term35 A B f x y).
Proof. exact (eq_refl (term35 A B f x y)). Qed.
Lemma lem57060 {A B : Type'} (f : type1210 A B) (P : type1413 A B) (x : A) (y : B) : (term37 A B f P x y) = (term52 A B f P x y).
Proof. exact (MK_COMB (@lem57059 A B f x y) (@lem57058 A B P x y)). Qed.
Lemma lem57061 {A B : Type'} (f : type1210 A B) (P : type1413 A B) (x : A) : (term39 A B f P x) = (term53 A B f P x).
Proof. exact (fun_ext (fun y : B => @lem57060 A B f P x y)). Qed.
Lemma lem57064 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem57065 {A B : Type'} (f : type1210 A B) (P : type1413 A B) (x : A) : (term41 A B f P x) = (term54 A B f P x).
Proof. exact (MK_COMB (@lem57064 B) (@lem57061 A B f P x)). Qed.
Lemma lem57070 {A B : Type'} (f : type1210 A B) (P : type1413 A B) : (term43 A B f P) = (term55 A B f P).
Proof. exact (fun_ext (fun x : A => @lem57065 A B f P x)). Qed.
Lemma lem57073 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem57074 {A B : Type'} (f : type1210 A B) (P : type1413 A B) : (term45 A B f P) = (term56 A B f P).
Proof. exact (MK_COMB (@lem57073 A) (@lem57070 A B f P)). Qed.
Lemma lem57079 {A B : Type'} (P : type1413 A B) : (term47 A B P) = (term57 A B P).
Proof. exact (fun_ext (fun f : type1210 A B => @lem57074 A B f P)). Qed.
Lemma lem57082 {A B : Type'} : (@GABS ((prod A B) -> Prop)) = (@GABS ((prod A B) -> Prop)).
Proof. exact (eq_refl (@GABS ((prod A B) -> Prop))). Qed.
Lemma lem57083 {A B : Type'} (P : type1413 A B) : (term48 A B P) = (term16 A B P).
Proof. exact (MK_COMB (@lem57082 A B) (@lem57079 A B P)). Qed.
Lemma lem57084 {A B : Type'} (P : type1413 A B) : (term17 A B P) = (term16 A B P).
Proof. exact (TRANS (@lem57035 A B P) (@lem57083 A B P)). Qed.
Lemma lem57085 {A B : Type'} (P : type1413 A B) : (term58 A B P) = (term58 A B P).
Proof. exact (eq_refl (term58 A B P)). Qed.
Lemma lem57086 {A B : Type'} (P : type1413 A B) : ((term16 A B P) = (term17 A B P)) = ((term16 A B P) = (term16 A B P)).
Proof. exact (MK_COMB (@lem57085 A B P) (@lem57084 A B P)). Qed.
Lemma lem57088 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem57089 {A B : Type'} (x : type1210 A B) : (x = x) = True.
Proof. exact (@lem57088 (type1210 A B) x). Qed.
Lemma lem57090 {A B : Type'} (P : type1413 A B) : ((term16 A B P) = (term16 A B P)) = True.
Proof. exact (@lem57089 A B (term16 A B P)). Qed.
Lemma lem57091 {A B : Type'} (P : type1413 A B) : ((term16 A B P) = (term17 A B P)) = True.
Proof. exact (TRANS (@lem57086 A B P) (@lem57090 A B P)). Qed.
Lemma lem57092 {A B : Type'} (P : type1413 A B) : True = ((term16 A B P) = (term17 A B P)).
Proof. exact (SYM (@lem57091 A B P)). Qed.
Lemma lem57093 {A B : Type'} (P : type1413 A B) : (term16 A B P) = (term17 A B P).
Proof. exact (EQ_MP (@lem57092 A B P) (@lem0)). Qed.
Lemma lem57132 {A B : Type'} (P : type1210 A B) : term59 A B P.
Proof. exact (@lem19732 (prod A B) P). Qed.
Lemma lem57133 {A B : Type'} (P : type1413 A B) : term60 A B P.
Proof. exact (@lem57132 A B (term17 A B P)). Qed.
Lemma lem57134 {A B : Type'} (P : type1413 A B) : (term61 A B P) = (term62 A B P).
Proof. exact (eq_refl (term61 A B P)). Qed.
Lemma lem57135 {A B : Type'} (P : type1413 A B) (x : prod A B) : (term29 A B P x) = (term30 A B P x).
Proof. exact (eq_refl (term29 A B P x)). Qed.
Lemma lem57136 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem57137 {A B : Type'} (P : type1413 A B) (x : prod A B) : (term63 A B P x) = (term64 A B P x).
Proof. exact (MK_COMB (@lem57136) (@lem57135 A B P x)). Qed.
Lemma lem57138 {A B : Type'} (x : prod A B) (P : type1413 A B) : (term65 A B x P) = (term66 A B x P).
Proof. exact (MK_COMB (@lem57137 A B P x) (@lem57134 A B P)). Qed.
Lemma lem57139 {A B : Type'} (P : type1413 A B) : (term67 A B P) = (term68 A B P).
Proof. exact (fun_ext (fun x : prod A B => @lem57138 A B x P)). Qed.
Lemma lem57140 {A B : Type'} : (@all (prod A B)) = (@all (prod A B)).
Proof. exact (eq_refl (@all (prod A B))). Qed.
Lemma lem57141 {A B : Type'} (P : type1413 A B) : (term60 A B P) = (term69 A B P).
Proof. exact (MK_COMB (@lem57140 A B) (@lem57139 A B P)). Qed.
Lemma lem57142 {A B : Type'} (P : type1413 A B) : term69 A B P.
Proof. exact (EQ_MP (@lem57141 A B P) (@lem57133 A B P)). Qed.
Lemma lem57143 {A B : Type'} : term70 A B.
Proof. exact (fun P : type1413 A B => @lem57142 A B P). Qed.
Lemma lem57144 {A B : Type'} (Q : type1210 A B) (P : type1413 A B) (h1 : term71 A B Q P) : term71 A B Q P.
Proof. exact (h1). Qed.
Lemma lem57145 {A B : Type'} (Q : type1210 A B) (P : type1413 A B) (h1 : term71 A B Q P) : term21 A B Q P.
Proof. exact (@lem57144 A B Q P h1 (@lem57143 A B)). Qed.
Lemma lem57146 {A B : Type'} (Q : type1210 A B) (P : type1413 A B) : term72 A B Q P.
Proof. exact (fun h0 : term71 A B Q P => @lem57145 A B Q P h0). Qed.
Lemma lem57147 {A B : Type'} (_1600 : type472 A B) (h1 : _1600 = (term73 A B)) : _1600 = (term73 A B).
Proof. exact (h1). Qed.
Lemma lem57148 {A B : Type'} (P : type1413 A B) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem57149 {A B : Type'} (P : type1413 A B) (_1600 : type472 A B) (h1 : _1600 = (term73 A B)) : (_1600 P) = (term74 A B P).
Proof. exact (MK_COMB (@lem57147 A B _1600 h1) (@lem57148 A B P)). Qed.
Lemma lem57150 {A B : Type'} (P : type1413 A B) : (term74 A B P) = (term75 A B P).
Proof. exact (eq_refl (term74 A B P)). Qed.
Lemma lem57151 {A B : Type'} (_1600 : type472 A B) (P : type1413 A B) : (term76 A B _1600 P) = (term76 A B _1600 P).
Proof. exact (eq_refl (term76 A B _1600 P)). Qed.
Lemma lem57152 {A B : Type'} (_1600 : type472 A B) (P : type1413 A B) : ((_1600 P) = (term74 A B P)) = ((_1600 P) = (term75 A B P)).
Proof. exact (MK_COMB (@lem57151 A B _1600 P) (@lem57150 A B P)). Qed.
Lemma lem57153 {A B : Type'} (P : type1413 A B) (_1600 : type472 A B) (h1 : _1600 = (term73 A B)) : (_1600 P) = (term75 A B P).
Proof. exact (EQ_MP (@lem57152 A B _1600 P) (@lem57149 A B P _1600 h1)). Qed.
Lemma lem57154 {A B : Type'} (P : type1413 A B) (_1600 : type472 A B) (h1 : _1600 = (term73 A B)) : (term75 A B P) = (_1600 P).
Proof. exact (SYM (@lem57153 A B P _1600 h1)). Qed.
Lemma lem57155 {A B : Type'} (_1600 : type472 A B) (h1 : _1600 = (term73 A B)) : term77 A B _1600.
Proof. exact (fun P : type1413 A B => @lem57154 A B P _1600 h1). Qed.
Lemma lem57156 {A B : Type'} (P : type1413 A B) (_1600 : type472 A B) (h1 : _1600 = (term73 A B)) : term78 A B _1600 P.
Proof. exact (@lem57155 A B _1600 h1 P). Qed.
Lemma lem57157 {A B : Type'} (_1600 : type472 A B) (P : type1413 A B) : (term78 A B _1600 P) = ((term75 A B P) = (_1600 P)).
Proof. exact (eq_refl (term78 A B _1600 P)). Qed.
Lemma lem57160 {A B : Type'} (P : type1413 A B) (_1600 : type472 A B) (h1 : _1600 = (term73 A B)) : (term75 A B P) = (_1600 P).
Proof. exact (EQ_MP (@lem57157 A B _1600 P) (@lem57156 A B P _1600 h1)). Qed.
Lemma lem57161 {A B : Type'} (P : type1413 A B) (_1600 : type472 A B) (h1 : _1600 = (term73 A B)) : (term75 A B P) = (_1600 P).
Proof. exact (@lem57160 A B P _1600 h1). Qed.
Lemma lem57162 {A B : Type'} : (@fst A B) = (@fst A B).
Proof. exact (eq_refl (@fst A B)). Qed.
Lemma lem57163 {A B : Type'} (P : type1413 A B) (_1600 : type472 A B) (h1 : _1600 = (term73 A B)) : (term79 A B P) = (term80 A B _1600 P).
Proof. exact (MK_COMB (@lem57162 A B) (@lem57161 A B P _1600 h1)). Qed.
Lemma lem57164 {A B : Type'} (P : type1413 A B) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem57165 {A B : Type'} (P : type1413 A B) (_1600 : type472 A B) (h1 : _1600 = (term73 A B)) : (term81 A B P) = (term82 A B _1600 P).
Proof. exact (MK_COMB (@lem57164 A B P) (@lem57163 A B P _1600 h1)). Qed.
Lemma lem57167 {A B : Type'} (P : type1413 A B) (_1600 : type472 A B) (h1 : _1600 = (term73 A B)) : (term75 A B P) = (_1600 P).
Proof. exact (EQ_MP (@lem57157 A B _1600 P) (@lem57156 A B P _1600 h1)). Qed.
Lemma lem57168 {A B : Type'} (P : type1413 A B) (_1600 : type472 A B) (h1 : _1600 = (term73 A B)) : (term75 A B P) = (_1600 P).
Proof. exact (@lem57167 A B P _1600 h1). Qed.
Lemma lem57169 {A B : Type'} : (@snd A B) = (@snd A B).
Proof. exact (eq_refl (@snd A B)). Qed.
Lemma lem57170 {A B : Type'} (P : type1413 A B) (_1600 : type472 A B) (h1 : _1600 = (term73 A B)) : (term83 A B P) = (term84 A B _1600 P).
Proof. exact (MK_COMB (@lem57169 A B) (@lem57168 A B P _1600 h1)). Qed.
Lemma lem57171 {A B : Type'} (P : type1413 A B) (_1600 : type472 A B) (h1 : _1600 = (term73 A B)) : (term62 A B P) = (term85 A B _1600 P).
Proof. exact (MK_COMB (@lem57165 A B P _1600 h1) (@lem57170 A B P _1600 h1)). Qed.
Lemma lem57172 {A B : Type'} (P : type1413 A B) (x : prod A B) : (term64 A B P x) = (term64 A B P x).
Proof. exact (eq_refl (term64 A B P x)). Qed.
Lemma lem57173 {A B : Type'} (x : prod A B) (P : type1413 A B) (_1600 : type472 A B) (h1 : _1600 = (term73 A B)) : (term66 A B x P) = (term86 A B x _1600 P).
Proof. exact (MK_COMB (@lem57172 A B P x) (@lem57171 A B P _1600 h1)). Qed.
Lemma lem57174 {A B : Type'} (P : type1413 A B) (_1600 : type472 A B) (h1 : _1600 = (term73 A B)) : (term68 A B P) = (term87 A B _1600 P).
Proof. exact (fun_ext (fun x : prod A B => @lem57173 A B x P _1600 h1)). Qed.
Lemma lem57175 {A B : Type'} : (@all (prod A B)) = (@all (prod A B)).
Proof. exact (eq_refl (@all (prod A B))). Qed.
Lemma lem57176 {A B : Type'} (P : type1413 A B) (_1600 : type472 A B) (h1 : _1600 = (term73 A B)) : (term69 A B P) = (term88 A B _1600 P).
Proof. exact (MK_COMB (@lem57175 A B) (@lem57174 A B P _1600 h1)). Qed.
Lemma lem57177 {A B : Type'} (_1600 : type472 A B) (h1 : _1600 = (term73 A B)) : (term89 A B) = (term90 A B _1600).
Proof. exact (fun_ext (fun P : type1413 A B => @lem57176 A B P _1600 h1)). Qed.
Lemma lem57178 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem57179 {A B : Type'} (_1600 : type472 A B) (h1 : _1600 = (term73 A B)) : (term70 A B) = (term91 A B _1600).
Proof. exact (MK_COMB (@lem57178 A B) (@lem57177 A B _1600 h1)). Qed.
Lemma lem57180 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem57181 {A B : Type'} (_1600 : type472 A B) (h1 : _1600 = (term73 A B)) : (term92 A B) = (term93 A B _1600).
Proof. exact (MK_COMB (@lem57180) (@lem57179 A B _1600 h1)). Qed.
Lemma lem57183 {A B : Type'} (P : type1413 A B) (_1600 : type472 A B) (h1 : _1600 = (term73 A B)) : (term75 A B P) = (_1600 P).
Proof. exact (EQ_MP (@lem57157 A B _1600 P) (@lem57156 A B P _1600 h1)). Qed.
Lemma lem57184 {A B : Type'} (P : type1413 A B) (_1600 : type472 A B) (h1 : _1600 = (term73 A B)) : (term75 A B P) = (_1600 P).
Proof. exact (@lem57183 A B P _1600 h1). Qed.
Lemma lem57185 {A B : Type'} (Q : type1210 A B) : Q = Q.
Proof. exact (eq_refl Q). Qed.
Lemma lem57186 {A B : Type'} (Q : type1210 A B) (P : type1413 A B) (_1600 : type472 A B) (h1 : _1600 = (term73 A B)) : (term21 A B Q P) = (term94 A B Q _1600 P).
Proof. exact (MK_COMB (@lem57185 A B Q) (@lem57184 A B P _1600 h1)). Qed.
Lemma lem57187 {A B : Type'} (Q : type1210 A B) (P : type1413 A B) (_1600 : type472 A B) (h1 : _1600 = (term73 A B)) : (term71 A B Q P) = (term95 A B Q _1600 P).
Proof. exact (MK_COMB (@lem57181 A B _1600 h1) (@lem57186 A B Q P _1600 h1)). Qed.
Lemma lem57188 {A B : Type'} (Q : type1210 A B) (P : type1413 A B) (h1 : term96 A B Q P) : term96 A B Q P.
Proof. exact (h1). Qed.
Lemma lem57189 {A B : Type'} (_1600 : type472 A B) (Q : type1210 A B) (P : type1413 A B) (h1 : term96 A B Q P) : term97 A B Q P _1600.
Proof. exact (@lem57188 A B Q P h1 _1600). Qed.
Lemma lem57190 {A B : Type'} (Q : type1210 A B) (_1600 : type472 A B) (P : type1413 A B) : (term97 A B Q P _1600) = (term95 A B Q _1600 P).
Proof. exact (eq_refl (term97 A B Q P _1600)). Qed.
Lemma lem57191 {A B : Type'} (_1600 : type472 A B) (Q : type1210 A B) (P : type1413 A B) (h1 : term96 A B Q P) : term95 A B Q _1600 P.
Proof. exact (EQ_MP (@lem57190 A B Q _1600 P) (@lem57189 A B _1600 Q P h1)). Qed.
Lemma lem57192 {A B : Type'} (Q : type1210 A B) (P : type1413 A B) (_1600 : type472 A B) (h1 : _1600 = (term73 A B)) : (term95 A B Q _1600 P) = (term71 A B Q P).
Proof. exact (SYM (@lem57187 A B Q P _1600 h1)). Qed.
Lemma lem57193 {A B : Type'} (Q : type1210 A B) (P : type1413 A B) (_1600 : type472 A B) (h1 : term96 A B Q P) (h2 : _1600 = (term73 A B)) : term71 A B Q P.
Proof. exact (EQ_MP (@lem57192 A B Q P _1600 h2) (@lem57191 A B _1600 Q P h1)). Qed.
Lemma lem57194 {A B : Type'} (Q : type1210 A B) (P : type1413 A B) (_1600 : type472 A B) (h1 : _1600 = (term73 A B)) : term98 A B Q P.
Proof. exact (fun h0 : term96 A B Q P => @lem57193 A B Q P _1600 h0 h1). Qed.
Lemma lem57195 {A B : Type'} (Q : type1210 A B) (P : type1413 A B) : term99 A B Q P.
Proof. exact (@lem51 (term71 A B Q P) (term96 A B Q P) (term21 A B Q P)). Qed.
Lemma lem57196 {A B : Type'} (Q : type1210 A B) (P : type1413 A B) (_1600 : type472 A B) (h1 : _1600 = (term73 A B)) : term100 A B Q P.
Proof. exact (@lem57195 A B Q P (@lem57194 A B Q P _1600 h1)). Qed.
Lemma lem57197 {A B : Type'} (Q : type1210 A B) (P : type1413 A B) (_1600 : type472 A B) (h1 : _1600 = (term73 A B)) : term101 A B Q P.
Proof. exact (@lem57196 A B Q P _1600 h1 (@lem57146 A B Q P)). Qed.
Lemma lem57198 {A B : Type'} : (term73 A B) = (term73 A B).
Proof. exact (eq_refl (term73 A B)). Qed.
Lemma lem57199 {A B : Type'} (_1600 : type472 A B) (Q : type1210 A B) (P : type1413 A B) : term102 A B _1600 Q P.
Proof. exact (fun h0 : _1600 = (term73 A B) => @lem57197 A B Q P _1600 h0). Qed.
Lemma lem57200 {A B : Type'} (Q : type1210 A B) (P : type1413 A B) : term103 A B Q P.
Proof. exact (@lem57199 A B (term73 A B) Q P). Qed.
Lemma lem57201 {A B : Type'} (Q : type1210 A B) (P : type1413 A B) : term101 A B Q P.
Proof. exact (@lem57200 A B Q P (@lem57198 A B)). Qed.
Lemma lem57202 {A B : Type'} (Q : type1210 A B) (P : type1413 A B) (h1 : term96 A B Q P) : term96 A B Q P.
Proof. exact (h1). Qed.
Lemma lem57203 {A B : Type'} (Q : type1210 A B) (P : type1413 A B) : term104 A B Q P.
Proof. exact (fun h0 : term96 A B Q P => @lem57202 A B Q P h0). Qed.
Lemma lem57204 {A B : Type'} (Q : type1210 A B) (P : type1413 A B) : term105 A B Q P.
Proof. exact (@lem51 (term96 A B Q P) (term96 A B Q P) (term21 A B Q P)). Qed.
Lemma lem57205 {A B : Type'} (Q : type1210 A B) (P : type1413 A B) : term106 A B Q P.
Proof. exact (@lem57204 A B Q P (@lem57203 A B Q P)). Qed.
Lemma lem57206 {A B : Type'} (Q : type1210 A B) (P : type1413 A B) : term101 A B Q P.
Proof. exact (@lem57205 A B Q P (@lem57201 A B Q P)). Qed.
Lemma lem57207 {A B : Type'} (Q : type1210 A B) (P : type1413 A B) (h1 : term101 A B Q P) : term101 A B Q P.
Proof. exact (h1). Qed.
Lemma lem57208 {A B : Type'} (Q : type1210 A B) (P : type1413 A B) (h1 : term96 A B Q P) : term96 A B Q P.
Proof. exact (h1). Qed.
Lemma lem57209 {A B : Type'} (Q : type1210 A B) (P : type1413 A B) (h1 : term96 A B Q P) (h2 : term101 A B Q P) : term21 A B Q P.
Proof. exact (@lem57207 A B Q P h2 (@lem57208 A B Q P h1)). Qed.
Lemma lem57210 {A B : Type'} (Q : type1210 A B) (P : type1413 A B) (h1 : term96 A B Q P) : term107 A B Q P.
Proof. exact (fun h0 : term101 A B Q P => @lem57209 A B Q P h1 h0). Qed.
Lemma lem57211 {A B : Type'} (Q : type1210 A B) (P : type1413 A B) (h1 : term101 A B Q P) : term101 A B Q P.
Proof. exact (h1). Qed.
Lemma lem57212 {A B : Type'} (Q : type1210 A B) (P : type1413 A B) (h1 : term96 A B Q P) (h2 : term101 A B Q P) : term21 A B Q P.
Proof. exact (@lem57210 A B Q P h1 (@lem57211 A B Q P h2)). Qed.
Lemma lem57213 {A B : Type'} (Q : type1210 A B) (P : type1413 A B) (h1 : term101 A B Q P) : term101 A B Q P.
Proof. exact (fun h0 : term96 A B Q P => @lem57212 A B Q P h0 h1). Qed.
Lemma lem57214 {A B : Type'} (Q : type1210 A B) (P : type1413 A B) : term106 A B Q P.
Proof. exact (fun h0 : term101 A B Q P => @lem57213 A B Q P h0). Qed.
Lemma lem57217 {A B : Type'} (Q : type1210 A B) (P : type1413 A B) : term101 A B Q P.
Proof. exact (@lem57214 A B Q P (@lem57206 A B Q P)). Qed.
Lemma lem57218 {A B : Type'} (Q : type1210 A B) (P : type1413 A B) : term101 A B Q P.
Proof. exact (@lem57217 A B Q P). Qed.
Lemma lem57219 {A B : Type'} (c : type472 A B) (h1 : term91 A B c) : term91 A B c.
Proof. exact (h1). Qed.
Lemma lem57225 {A B : Type'} (x : prod A B) : x = (term3 A B x).
Proof. exact (EQ_MP (@lem56970 A B x) (@lem56969 A B x)). Qed.
Lemma lem57226 {A B : Type'} (x : prod A B) : x = (term3 A B x).
Proof. exact (@lem57225 A B x). Qed.
Lemma lem57227 {A B : Type'} (c : type472 A B) (P : type1413 A B) : (c P) = (term108 A B c P).
Proof. exact (@lem57226 A B (c P)). Qed.
Lemma lem57228 {A B : Type'} (Q : type1210 A B) : Q = Q.
Proof. exact (eq_refl Q). Qed.
Lemma lem57229 {A B : Type'} (Q : type1210 A B) (c : type472 A B) (P : type1413 A B) : (term94 A B Q c P) = (term109 A B Q c P).
Proof. exact (MK_COMB (@lem57228 A B Q) (@lem57227 A B c P)). Qed.
Lemma lem57230 {A B : Type'} (Q : type1210 A B) (c : type472 A B) (P : type1413 A B) : (term109 A B Q c P) = (term94 A B Q c P).
Proof. exact (SYM (@lem57229 A B Q c P)). Qed.
Lemma lem57231 {A B : Type'} (P : type1413 A B) (Q : type1210 A B) (h1 : term13 A B P Q) : term13 A B P Q.
Proof. exact (h1). Qed.
Lemma lem57232 {A B : Type'} (x : A) (P : type1413 A B) (Q : type1210 A B) (h1 : term13 A B P Q) : term110 A B P Q x.
Proof. exact (@lem57231 A B P Q h1 x). Qed.
Lemma lem57233 {A B : Type'} (P : type1413 A B) (Q : type1210 A B) (x : A) : (term110 A B P Q x) = (term111 A B P Q x).
Proof. exact (eq_refl (term110 A B P Q x)). Qed.
Lemma lem57234 {A B : Type'} (x : A) (P : type1413 A B) (Q : type1210 A B) (h1 : term13 A B P Q) : term111 A B P Q x.
Proof. exact (EQ_MP (@lem57233 A B P Q x) (@lem57232 A B x P Q h1)). Qed.
Lemma lem57235 {A B : Type'} (x : A) (y : B) (P : type1413 A B) (Q : type1210 A B) (h1 : term13 A B P Q) : term112 A B P Q x y.
Proof. exact (@lem57234 A B x P Q h1 y). Qed.
Lemma lem57236 {A B : Type'} (P : type1413 A B) (Q : type1210 A B) (x : A) (y : B) : (term112 A B P Q x y) = (term113 A B P Q x y).
Proof. exact (eq_refl (term112 A B P Q x y)). Qed.
Lemma lem57237 {A B : Type'} (x : A) (y : B) (P : type1413 A B) (Q : type1210 A B) (h1 : term13 A B P Q) : term113 A B P Q x y.
Proof. exact (EQ_MP (@lem57236 A B P Q x y) (@lem57235 A B x y P Q h1)). Qed.
Lemma lem57238 {A B : Type'} (P : type1413 A B) (x : A) (y : B) (h1 : P x y) : P x y.
Proof. exact (h1). Qed.
Lemma lem57239 {A B : Type'} (Q : type1210 A B) (P : type1413 A B) (x : A) (y : B) (h1 : term13 A B P Q) (h2 : P x y) : term114 A B Q x y.
Proof. exact (@lem57237 A B x y P Q h1 (@lem57238 A B P x y h2)). Qed.
Lemma lem57240 {A B : Type'} (Q : type1210 A B) (P : type1413 A B) (x : A) (y : B) (h1 : P x y) : term115 A B P Q x y.
Proof. exact (fun h0 : term13 A B P Q => @lem57239 A B Q P x y h0 h1). Qed.
Lemma lem57241 {A B : Type'} (P : type1413 A B) (Q : type1210 A B) (h1 : term13 A B P Q) : term13 A B P Q.
Proof. exact (h1). Qed.
Lemma lem57242 {A B : Type'} (Q : type1210 A B) (P : type1413 A B) (x : A) (y : B) (h1 : term13 A B P Q) (h2 : P x y) : term114 A B Q x y.
Proof. exact (@lem57240 A B Q P x y h2 (@lem57241 A B P Q h1)). Qed.
Lemma lem57243 {A B : Type'} (x : A) (y : B) (P : type1413 A B) (Q : type1210 A B) (h1 : term13 A B P Q) : term113 A B P Q x y.
Proof. exact (fun h0 : P x y => @lem57242 A B Q P x y h1 h0). Qed.
Lemma lem57244 {A B : Type'} (x : A) (P : type1413 A B) (Q : type1210 A B) (h1 : term13 A B P Q) : term111 A B P Q x.
Proof. exact (fun y : B => @lem57243 A B x y P Q h1). Qed.
Lemma lem57245 {A B : Type'} (P : type1413 A B) (Q : type1210 A B) (h1 : term13 A B P Q) : term13 A B P Q.
Proof. exact (fun x : A => @lem57244 A B x P Q h1). Qed.
Lemma lem57246 {A B : Type'} (P : type1413 A B) (Q : type1210 A B) : term116 A B P Q.
Proof. exact (fun h0 : term13 A B P Q => @lem57245 A B P Q h0). Qed.
Lemma lem57247 {A B : Type'} (P : type1413 A B) (Q : type1210 A B) (h1 : term13 A B P Q) : term13 A B P Q.
Proof. exact (@lem57246 A B P Q (@lem56980 A B P Q h1)). Qed.
Lemma lem57248 {A B : Type'} (x : A) (P : type1413 A B) (Q : type1210 A B) (h1 : term13 A B P Q) : term110 A B P Q x.
Proof. exact (@lem57247 A B P Q h1 x). Qed.
Lemma lem57249 {A B : Type'} (P : type1413 A B) (Q : type1210 A B) (x : A) : (term110 A B P Q x) = (term111 A B P Q x).
Proof. exact (eq_refl (term110 A B P Q x)). Qed.
Lemma lem57250 {A B : Type'} (x : A) (P : type1413 A B) (Q : type1210 A B) (h1 : term13 A B P Q) : term111 A B P Q x.
Proof. exact (EQ_MP (@lem57249 A B P Q x) (@lem57248 A B x P Q h1)). Qed.
Lemma lem57251 {A B : Type'} (x : A) (y : B) (P : type1413 A B) (Q : type1210 A B) (h1 : term13 A B P Q) : term112 A B P Q x y.
Proof. exact (@lem57250 A B x P Q h1 y). Qed.
Lemma lem57252 {A B : Type'} (P : type1413 A B) (Q : type1210 A B) (x : A) (y : B) : (term112 A B P Q x y) = (term113 A B P Q x y).
Proof. exact (eq_refl (term112 A B P Q x y)). Qed.
Lemma lem57255 {A B : Type'} (x : A) (y : B) (P : type1413 A B) (Q : type1210 A B) (h1 : term13 A B P Q) : term113 A B P Q x y.
Proof. exact (EQ_MP (@lem57252 A B P Q x y) (@lem57251 A B x y P Q h1)). Qed.
Lemma lem57256 {A B : Type'} (x : A) (y : B) (P : type1413 A B) (Q : type1210 A B) (h1 : term13 A B P Q) : term113 A B P Q x y.
Proof. exact (@lem57255 A B x y P Q h1). Qed.
Lemma lem57257 {A B : Type'} (c : type472 A B) (P : type1413 A B) (Q : type1210 A B) (h1 : term13 A B P Q) : term117 A B Q c P.
Proof. exact (@lem57256 A B (term80 A B c P) (term84 A B c P) P Q h1). Qed.
Lemma lem57258 {A B : Type'} (c : type472 A B) (h1 : term91 A B c) : term91 A B c.
Proof. exact (h1). Qed.
Lemma lem57259 {A B : Type'} (P : type1413 A B) (c : type472 A B) (h1 : term91 A B c) : term118 A B c P.
Proof. exact (@lem57258 A B c h1 P). Qed.
Lemma lem57260 {A B : Type'} (c : type472 A B) (P : type1413 A B) : (term118 A B c P) = (term88 A B c P).
Proof. exact (eq_refl (term118 A B c P)). Qed.
Lemma lem57261 {A B : Type'} (P : type1413 A B) (c : type472 A B) (h1 : term91 A B c) : term88 A B c P.
Proof. exact (EQ_MP (@lem57260 A B c P) (@lem57259 A B P c h1)). Qed.
Lemma lem57262 {A B : Type'} (P : type1413 A B) (x : prod A B) (c : type472 A B) (h1 : term91 A B c) : term119 A B c P x.
Proof. exact (@lem57261 A B P c h1 x). Qed.
Lemma lem57263 {A B : Type'} (x : prod A B) (c : type472 A B) (P : type1413 A B) : (term119 A B c P x) = (term86 A B x c P).
Proof. exact (eq_refl (term119 A B c P x)). Qed.
Lemma lem57264 {A B : Type'} (x : prod A B) (P : type1413 A B) (c : type472 A B) (h1 : term91 A B c) : term86 A B x c P.
Proof. exact (EQ_MP (@lem57263 A B x c P) (@lem57262 A B P x c h1)). Qed.
Lemma lem57265 {A B : Type'} (P : type1413 A B) (x : prod A B) (h1 : term30 A B P x) : term30 A B P x.
Proof. exact (h1). Qed.
Lemma lem57266 {A B : Type'} (c : type472 A B) (P : type1413 A B) (x : prod A B) (h1 : term91 A B c) (h2 : term30 A B P x) : term85 A B c P.
Proof. exact (@lem57264 A B x P c h1 (@lem57265 A B P x h2)). Qed.
Lemma lem57267 {A B : Type'} (c : type472 A B) (P : type1413 A B) (x : prod A B) (h1 : term30 A B P x) : term120 A B c P.
Proof. exact (fun h0 : term91 A B c => @lem57266 A B c P x h0 h1). Qed.
Lemma lem57268 {A B : Type'} (P : type1413 A B) (h1 : term121 A B P) : term121 A B P.
Proof. exact (h1). Qed.
Lemma lem57269 {A B : Type'} (c : type472 A B) (P : type1413 A B) (h1 : term121 A B P) : term120 A B c P.
Proof. exact (ex_elim (@lem57268 A B P h1) (fun x : prod A B => fun h0 : term17 A B P x => @lem57267 A B c P x h0)). Qed.
Lemma lem57270 {A B : Type'} (c : type472 A B) (h1 : term91 A B c) : term91 A B c.
Proof. exact (h1). Qed.
Lemma lem57271 {A B : Type'} (c : type472 A B) (P : type1413 A B) (h1 : term91 A B c) (h2 : term121 A B P) : term85 A B c P.
Proof. exact (@lem57269 A B c P h2 (@lem57270 A B c h1)). Qed.
Lemma lem57272 {A B : Type'} (P : type1413 A B) (c : type472 A B) (h1 : term91 A B c) : term122 A B c P.
Proof. exact (fun h0 : term121 A B P => @lem57271 A B c P h1 h0). Qed.
Lemma lem57273 {A B : Type'} (c : type472 A B) (h1 : term91 A B c) : term123 A B c.
Proof. exact (fun P : type1413 A B => @lem57272 A B P c h1). Qed.
Lemma lem57274 {A B : Type'} (c : type472 A B) : term124 A B c.
Proof. exact (fun h0 : term91 A B c => @lem57273 A B c h0). Qed.
Lemma lem57275 {A B : Type'} (c : type472 A B) (h1 : term91 A B c) : term123 A B c.
Proof. exact (@lem57274 A B c (@lem57219 A B c h1)). Qed.
Lemma lem57276 {A B : Type'} (P : type1413 A B) (c : type472 A B) (h1 : term91 A B c) : term125 A B c P.
Proof. exact (@lem57275 A B c h1 P). Qed.
Lemma lem57277 {A B : Type'} (c : type472 A B) (P : type1413 A B) : (term125 A B c P) = (term122 A B c P).
Proof. exact (eq_refl (term125 A B c P)). Qed.
Lemma lem57280 {A B : Type'} (P : type1413 A B) (c : type472 A B) (h1 : term91 A B c) : term122 A B c P.
Proof. exact (EQ_MP (@lem57277 A B c P) (@lem57276 A B P c h1)). Qed.
Lemma lem57281 {A B : Type'} (P : type1413 A B) (c : type472 A B) (h1 : term91 A B c) : term122 A B c P.
Proof. exact (@lem57280 A B P c h1). Qed.
Lemma lem57287 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term1 _5131 _5132 P) = (term2 _5131 _5132 P).
Proof. exact (EQ_MP (@lem56957 _5131 _5132 P) (@lem56956 _5131 _5132 P)). Qed.
Lemma lem57288 {A B : Type'} (P : type1210 A B) : (term126 A B P) = (term127 A B P).
Proof. exact (@lem57287 B A P). Qed.
Lemma lem57289 {A B : Type'} (P : type1413 A B) : (term128 A B P) = (term129 A B P).
Proof. exact (@lem57288 A B (term17 A B P)). Qed.
Lemma lem57290 {A B : Type'} (P : type1413 A B) (x : prod A B) : (term29 A B P x) = (term30 A B P x).
Proof. exact (eq_refl (term29 A B P x)). Qed.
Lemma lem57291 {A B : Type'} (P : type1413 A B) : (term27 A B P) = (term17 A B P).
Proof. exact (fun_ext (fun x : prod A B => @lem57290 A B P x)). Qed.
Lemma lem57292 {A B : Type'} : (@ex (prod A B)) = (@ex (prod A B)).
Proof. exact (eq_refl (@ex (prod A B))). Qed.
Lemma lem57293 {A B : Type'} (P : type1413 A B) : (term128 A B P) = (term121 A B P).
Proof. exact (MK_COMB (@lem57292 A B) (@lem57291 A B P)). Qed.
Lemma lem57294 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem57295 {A B : Type'} (P : type1413 A B) : (term130 A B P) = (term131 A B P).
Proof. exact (MK_COMB (@lem57294) (@lem57293 A B P)). Qed.
Lemma lem57296 {A B : Type'} (P : type1413 A B) (p1 : A) (p2 : B) : (term33 A B P p1 p2) = (term34 A B P p1 p2).
Proof. exact (eq_refl (term33 A B P p1 p2)). Qed.
Lemma lem57297 {A B : Type'} (P : type1413 A B) (p1 : A) : (term132 A B P p1) = (term133 A B P p1).
Proof. exact (fun_ext (fun p2 : B => @lem57296 A B P p1 p2)). Qed.
Lemma lem57298 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem57299 {A B : Type'} (P : type1413 A B) (p1 : A) : (term134 A B P p1) = (term135 A B P p1).
Proof. exact (MK_COMB (@lem57298 B) (@lem57297 A B P p1)). Qed.
Lemma lem57300 {A B : Type'} (P : type1413 A B) : (term136 A B P) = (term137 A B P).
Proof. exact (fun_ext (fun p1 : A => @lem57299 A B P p1)). Qed.
Lemma lem57301 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem57302 {A B : Type'} (P : type1413 A B) : (term129 A B P) = (term138 A B P).
Proof. exact (MK_COMB (@lem57301 A) (@lem57300 A B P)). Qed.
Lemma lem57303 {A B : Type'} (P : type1413 A B) : ((term128 A B P) = (term129 A B P)) = ((term121 A B P) = (term138 A B P)).
Proof. exact (MK_COMB (@lem57295 A B P) (@lem57302 A B P)). Qed.
Lemma lem57304 {A B : Type'} (P : type1413 A B) : (term121 A B P) = (term138 A B P).
Proof. exact (EQ_MP (@lem57303 A B P) (@lem57289 A B P)). Qed.
Lemma lem57318 {A B : Type'} (y : B) (x : A) : (term49 A B x y) = x.
Proof. exact (EQ_MP (@lem48220 A B y x) (@lem48219 A B x y)). Qed.
Lemma lem57319 {A B : Type'} (y : B) (x : A) : (term49 A B x y) = x.
Proof. exact (@lem57318 A B y x). Qed.
Lemma lem57320 {A B : Type'} (p2 : B) (p1 : A) : (term49 A B p1 p2) = p1.
Proof. exact (@lem57319 A B p2 p1). Qed.
Lemma lem57321 {A B : Type'} (P : type1413 A B) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem57322 {A B : Type'} (p2 : B) (P : type1413 A B) (p1 : A) : (term50 A B P p1 p2) = (P p1).
Proof. exact (MK_COMB (@lem57321 A B P) (@lem57320 A B p2 p1)). Qed.
Lemma lem57324 {A B : Type'} (x : A) (y : B) : (term51 A B x y) = y.
Proof. exact (EQ_MP (@lem48214 A B x y) (@lem48213 A B x y)). Qed.
Lemma lem57325 {A B : Type'} (x : A) (y : B) : (term51 A B x y) = y.
Proof. exact (@lem57324 A B x y). Qed.
Lemma lem57326 {A B : Type'} (p1 : A) (p2 : B) : (term51 A B p1 p2) = p2.
Proof. exact (@lem57325 A B p1 p2). Qed.
Lemma lem57327 {A B : Type'} (P : type1413 A B) (p1 : A) (p2 : B) : (term34 A B P p1 p2) = (P p1 p2).
Proof. exact (MK_COMB (@lem57322 A B p2 P p1) (@lem57326 A B p1 p2)). Qed.
Lemma lem57328 {A B : Type'} (P : type1413 A B) (p1 : A) : (term133 A B P p1) = (term139 A B P p1).
Proof. exact (fun_ext (fun p2 : B => @lem57327 A B P p1 p2)). Qed.
Lemma lem57329 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem57330 {A B : Type'} (P : type1413 A B) (p1 : A) : (term135 A B P p1) = (term15 A B P p1).
Proof. exact (MK_COMB (@lem57329 B) (@lem57328 A B P p1)). Qed.
Lemma lem57337 {A B : Type'} (P : type1413 A B) : (term137 A B P) = (term140 A B P).
Proof. exact (fun_ext (fun p1 : A => @lem57330 A B P p1)). Qed.
Lemma lem57338 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem57339 {A B : Type'} (P : type1413 A B) : (term138 A B P) = (term14 A B P).
Proof. exact (MK_COMB (@lem57338 A) (@lem57337 A B P)). Qed.
Lemma lem57346 {A B : Type'} (P : type1413 A B) : (term121 A B P) = (term14 A B P).
Proof. exact (TRANS (@lem57304 A B P) (@lem57339 A B P)). Qed.
Lemma lem57347 {A B : Type'} (P : type1413 A B) : (term14 A B P) = (term121 A B P).
Proof. exact (SYM (@lem57346 A B P)). Qed.
Lemma lem57349 (p : Prop) : p = (term141 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem57350 {A B : Type'} (P : type1413 A B) : (term14 A B P) = (term142 A B P).
Proof. exact (@lem57349 (term14 A B P)). Qed.
Lemma lem57351 {A B : Type'} (P : type1413 A B) : (term142 A B P) = (term14 A B P).
Proof. exact (SYM (@lem57350 A B P)). Qed.
Lemma lem57352 {A B : Type'} (P : type1413 A B) (h1 : term143 A B P) : term143 A B P.
Proof. exact (h1). Qed.
Lemma lem57355 {A B : Type'} (x0 : A) (y0 : B) (P : type1413 A B) (h1 : term144 A B x0 y0 P) : term144 A B x0 y0 P.
Proof. exact (h1). Qed.
Lemma lem57356 {A B : Type'} (x0 : A) (y0 : B) (P : type1413 A B) : term145 A B x0 y0 P.
Proof. exact (fun h0 : term144 A B x0 y0 P => @lem57355 A B x0 y0 P h0). Qed.
Lemma lem57357 {A B : Type'} (x0 : A) (y0 : B) (P : type1413 A B) (h1 : term145 A B x0 y0 P) : term145 A B x0 y0 P.
Proof. exact (h1). Qed.
Lemma lem57358 {A B : Type'} (x0 : A) (y0 : B) (P : type1413 A B) (h1 : term144 A B x0 y0 P) : term144 A B x0 y0 P.
Proof. exact (h1). Qed.
Lemma lem57359 {A B : Type'} (x0 : A) (y0 : B) (P : type1413 A B) (h1 : term145 A B x0 y0 P) (h2 : term144 A B x0 y0 P) : term144 A B x0 y0 P.
Proof. exact (@lem57357 A B x0 y0 P h1 (@lem57358 A B x0 y0 P h2)). Qed.
Lemma lem57360 {A B : Type'} (x0 : A) (y0 : B) (P : type1413 A B) (h1 : term144 A B x0 y0 P) : term146 A B x0 y0 P.
Proof. exact (fun h0 : term145 A B x0 y0 P => @lem57359 A B x0 y0 P h0 h1). Qed.
Lemma lem57361 {A B : Type'} (x0 : A) (y0 : B) (P : type1413 A B) (h1 : term145 A B x0 y0 P) : term145 A B x0 y0 P.
Proof. exact (h1). Qed.
Lemma lem57362 {A B : Type'} (x0 : A) (y0 : B) (P : type1413 A B) (h1 : term145 A B x0 y0 P) (h2 : term144 A B x0 y0 P) : term144 A B x0 y0 P.
Proof. exact (@lem57360 A B x0 y0 P h2 (@lem57361 A B x0 y0 P h1)). Qed.
Lemma lem57363 {A B : Type'} (x0 : A) (y0 : B) (P : type1413 A B) (h1 : term145 A B x0 y0 P) : term145 A B x0 y0 P.
Proof. exact (fun h0 : term144 A B x0 y0 P => @lem57362 A B x0 y0 P h1 h0). Qed.
Lemma lem57364 {A B : Type'} (x0 : A) (y0 : B) (P : type1413 A B) : term147 A B x0 y0 P.
Proof. exact (fun h0 : term145 A B x0 y0 P => @lem57363 A B x0 y0 P h0). Qed.
Lemma lem57367 {A B : Type'} (x0 : A) (y0 : B) (P : type1413 A B) : term145 A B x0 y0 P.
Proof. exact (@lem57364 A B x0 y0 P (@lem57356 A B x0 y0 P)). Qed.
Lemma lem57368 {A B : Type'} (x0 : A) (y0 : B) (P : type1413 A B) : term145 A B x0 y0 P.
Proof. exact (@lem57367 A B x0 y0 P). Qed.
Lemma lem57384 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem57385 {A B : Type'} (P : type1413 A B) : (term142 A B P) = (term148 A B P).
Proof. exact (@lem57384 (term143 A B P)). Qed.
Lemma lem57387 (t : Prop) : (term149 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem57388 {A B : Type'} (P : type1413 A B) : (term148 A B P) = (term14 A B P).
Proof. exact (@lem57387 (term14 A B P)). Qed.
Lemma lem57393 {A B : Type'} (P : type1413 A B) : (term142 A B P) = (term14 A B P).
Proof. exact (TRANS (@lem57385 A B P) (@lem57388 A B P)). Qed.
Lemma lem57398 {A B : Type'} (P : type1413 A B) (x0 : A) (y0 : B) : (term150 A B P x0 y0) = (term150 A B P x0 y0).
Proof. exact (eq_refl (term150 A B P x0 y0)). Qed.
Lemma lem57399 {A B : Type'} (x0 : A) (y0 : B) (P : type1413 A B) : (term144 A B x0 y0 P) = (term151 A B x0 y0 P).
Proof. exact (MK_COMB (@lem57398 A B P x0 y0) (@lem57393 A B P)). Qed.
Lemma lem57402 {A B : Type'} (y0 : B) (P : type1413 A B) : (term152 A B y0 P) = (term153 A B y0 P).
Proof. exact (fun_ext (fun x0 : A => @lem57399 A B x0 y0 P)). Qed.
Lemma lem57403 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem57404 {A B : Type'} (y0 : B) (P : type1413 A B) : (term154 A B y0 P) = (term155 A B y0 P).
Proof. exact (MK_COMB (@lem57403 A) (@lem57402 A B y0 P)). Qed.
Lemma lem57409 {A B : Type'} (P : type1413 A B) : (term156 A B P) = (term157 A B P).
Proof. exact (fun_ext (fun y0 : B => @lem57404 A B y0 P)). Qed.
Lemma lem57410 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem57411 {A B : Type'} (P : type1413 A B) : (term158 A B P) = (term159 A B P).
Proof. exact (MK_COMB (@lem57410 B) (@lem57409 A B P)). Qed.
Lemma lem57416 {A B : Type'} : (term160 A B) = (term161 A B).
Proof. exact (fun_ext (fun P : type1413 A B => @lem57411 A B P)). Qed.
Lemma lem57417 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem57426 {A B : Type'} : (term162 A B) = (term163 A B).
Proof. exact (MK_COMB (@lem57417 A B) (@lem57416 A B)). Qed.
Lemma lem57427 {A B : Type'} (P : type1413 A B) (p1 : A) (p2 : B) : (P p1 p2) = (P p1 p2).
Proof. exact (eq_refl (P p1 p2)). Qed.
Lemma lem57428 {A B : Type'} (P : type1413 A B) (p1 : A) : (term139 A B P p1) = (term139 A B P p1).
Proof. exact (fun_ext (fun p2 : B => @lem57427 A B P p1 p2)). Qed.
Lemma lem57429 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem57430 {A B : Type'} (P : type1413 A B) (p1 : A) : (term15 A B P p1) = (term15 A B P p1).
Proof. exact (MK_COMB (@lem57429 B) (@lem57428 A B P p1)). Qed.
Lemma lem57431 {A B : Type'} (P : type1413 A B) : (term140 A B P) = (term140 A B P).
Proof. exact (fun_ext (fun p1 : A => @lem57430 A B P p1)). Qed.
Lemma lem57432 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem57433 {A B : Type'} (P : type1413 A B) : (term14 A B P) = (term14 A B P).
Proof. exact (MK_COMB (@lem57432 A) (@lem57431 A B P)). Qed.
Lemma lem57436 {A B : Type'} (P : type1413 A B) (x0 : A) (y0 : B) : (term150 A B P x0 y0) = (term150 A B P x0 y0).
Proof. exact (eq_refl (term150 A B P x0 y0)). Qed.
Lemma lem57437 {A B : Type'} (x0 : A) (y0 : B) (P : type1413 A B) : (term151 A B x0 y0 P) = (term151 A B x0 y0 P).
Proof. exact (MK_COMB (@lem57436 A B P x0 y0) (@lem57433 A B P)). Qed.
Lemma lem57438 {A B : Type'} (y0 : B) (P : type1413 A B) : (term153 A B y0 P) = (term153 A B y0 P).
Proof. exact (fun_ext (fun x0 : A => @lem57437 A B x0 y0 P)). Qed.
Lemma lem57439 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem57440 {A B : Type'} (y0 : B) (P : type1413 A B) : (term155 A B y0 P) = (term155 A B y0 P).
Proof. exact (MK_COMB (@lem57439 A) (@lem57438 A B y0 P)). Qed.
Lemma lem57441 {A B : Type'} (P : type1413 A B) : (term157 A B P) = (term157 A B P).
Proof. exact (fun_ext (fun y0 : B => @lem57440 A B y0 P)). Qed.
Lemma lem57442 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem57443 {A B : Type'} (P : type1413 A B) : (term159 A B P) = (term159 A B P).
Proof. exact (MK_COMB (@lem57442 B) (@lem57441 A B P)). Qed.
Lemma lem57444 {A B : Type'} : (term161 A B) = (term161 A B).
Proof. exact (fun_ext (fun P : type1413 A B => @lem57443 A B P)). Qed.
Lemma lem57445 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem57446 {A B : Type'} : (term163 A B) = (term163 A B).
Proof. exact (MK_COMB (@lem57445 A B) (@lem57444 A B)). Qed.
Lemma lem57481 {A B : Type'} : (term162 A B) = (term163 A B).
Proof. exact (TRANS (@lem57426 A B) (@lem57446 A B)). Qed.
Lemma lem57482 {A B : Type'} : (term163 A B) = (term162 A B).
Proof. exact (SYM (@lem57481 A B)). Qed.
Lemma lem57485 (p : Prop) : p = (term141 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem57486 {A B : Type'} (P : type1413 A B) : (term14 A B P) = (term142 A B P).
Proof. exact (@lem57485 (term14 A B P)). Qed.
Lemma lem57487 {A B : Type'} (P : type1413 A B) : (term142 A B P) = (term14 A B P).
Proof. exact (SYM (@lem57486 A B P)). Qed.
Lemma lem57488 {A B : Type'} (P : type1413 A B) (h1 : term143 A B P) : term143 A B P.
Proof. exact (h1). Qed.
Lemma lem57494 {A B : Type'} (P : type1413 A B) (x0 : A) (y0 : B) (h1 : P x0 y0) : P x0 y0.
Proof. exact (h1). Qed.
Lemma lem57496 {B : Type'} (P : B -> Prop) : (term164 B P) = (term165 B P).
Proof. exact (@lem18394 B P). Qed.
Lemma lem57497 {A B : Type'} (P : type1413 A B) (p1 : A) : (term166 A B P p1) = (term167 A B P p1).
Proof. exact (@lem57496 B (term139 A B P p1)). Qed.
Lemma lem57498 {A B : Type'} (P : type1413 A B) (p1 : A) (p2 : B) : (term168 A B P p1 p2) = (P p1 p2).
Proof. exact (eq_refl (term168 A B P p1 p2)). Qed.
Lemma lem57499 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem57501 {A B : Type'} (P : type1413 A B) (p1 : A) (p2 : B) : (term169 A B P p1 p2) = (term170 A B P p1 p2).
Proof. exact (MK_COMB (@lem57499) (@lem57498 A B P p1 p2)). Qed.
Lemma lem57502 {A B : Type'} (P : type1413 A B) (p1 : A) : (term171 A B P p1) = (term172 A B P p1).
Proof. exact (fun_ext (fun p2 : B => @lem57501 A B P p1 p2)). Qed.
Lemma lem57503 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem57504 {A B : Type'} (P : type1413 A B) (p1 : A) : (term167 A B P p1) = (term173 A B P p1).
Proof. exact (MK_COMB (@lem57503 B) (@lem57502 A B P p1)). Qed.
Lemma lem57505 {A B : Type'} (P : type1413 A B) (p1 : A) : (term166 A B P p1) = (term173 A B P p1).
Proof. exact (TRANS (@lem57497 A B P p1) (@lem57504 A B P p1)). Qed.
Lemma lem57506 {A : Type'} (P : A -> Prop) : (term164 A P) = (term165 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem57507 {A B : Type'} (P : type1413 A B) : (term143 A B P) = (term174 A B P).
Proof. exact (@lem57506 A (term140 A B P)). Qed.
Lemma lem57508 {A B : Type'} (P : type1413 A B) (p1 : A) : (term175 A B P p1) = (term15 A B P p1).
Proof. exact (eq_refl (term175 A B P p1)). Qed.
Lemma lem57509 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem57510 {A B : Type'} (P : type1413 A B) (p1 : A) : (term176 A B P p1) = (term166 A B P p1).
Proof. exact (MK_COMB (@lem57509) (@lem57508 A B P p1)). Qed.
Lemma lem57511 {A B : Type'} (P : type1413 A B) (p1 : A) : (term176 A B P p1) = (term173 A B P p1).
Proof. exact (TRANS (@lem57510 A B P p1) (@lem57505 A B P p1)). Qed.
Lemma lem57512 {A B : Type'} (P : type1413 A B) : (term177 A B P) = (term178 A B P).
Proof. exact (fun_ext (fun p1 : A => @lem57511 A B P p1)). Qed.
Lemma lem57513 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem57514 {A B : Type'} (P : type1413 A B) : (term174 A B P) = (term179 A B P).
Proof. exact (MK_COMB (@lem57513 A) (@lem57512 A B P)). Qed.
Lemma lem57527 {A B : Type'} (P : type1413 A B) : (term143 A B P) = (term179 A B P).
Proof. exact (TRANS (@lem57507 A B P) (@lem57514 A B P)). Qed.
Lemma lem57528 {A B : Type'} (P : type1413 A B) (h1 : term143 A B P) : term179 A B P.
Proof. exact (EQ_MP (@lem57527 A B P) (@lem57488 A B P h1)). Qed.
Lemma lem57534 {A B : Type'} (P : type1413 A B) (x0 : A) (y0 : B) (h1 : P x0 y0) : P x0 y0.
Proof. exact (h1). Qed.
Lemma lem57541 {A B : Type'} (P : type1413 A B) (p1 : A) (p2 : B) : (term170 A B P p1 p2) = (term170 A B P p1 p2).
Proof. exact (eq_refl (term170 A B P p1 p2)). Qed.
Lemma lem57542 {A B : Type'} (P : type1413 A B) (p1 : A) : (term172 A B P p1) = (term172 A B P p1).
Proof. exact (fun_ext (fun p2 : B => @lem57541 A B P p1 p2)). Qed.
Lemma lem57543 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem57544 {A B : Type'} (P : type1413 A B) (p1 : A) : (term173 A B P p1) = (term173 A B P p1).
Proof. exact (MK_COMB (@lem57543 B) (@lem57542 A B P p1)). Qed.
Lemma lem57545 {A B : Type'} (P : type1413 A B) : (term178 A B P) = (term178 A B P).
Proof. exact (fun_ext (fun p1 : A => @lem57544 A B P p1)). Qed.
Lemma lem57546 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem57547 {A B : Type'} (P : type1413 A B) : (term179 A B P) = (term179 A B P).
Proof. exact (MK_COMB (@lem57546 A) (@lem57545 A B P)). Qed.
Lemma lem57548 {A B : Type'} (P : type1413 A B) (h1 : term143 A B P) : term179 A B P.
Proof. exact (EQ_MP (@lem57547 A B P) (@lem57528 A B P h1)). Qed.
Lemma lem57552 {A B : Type'} (P : type1413 A B) (x0 : A) (y0 : B) (h1 : P x0 y0) : P x0 y0.
Proof. exact (h1). Qed.
Lemma lem57554 {A B : Type'} (P : type1413 A B) (p1 : A) (p2 : B) : (term170 A B P p1 p2) = (term170 A B P p1 p2).
Proof. exact (eq_refl (term170 A B P p1 p2)). Qed.
Lemma lem57555 {A B : Type'} (P : type1413 A B) (p1 : A) : (term172 A B P p1) = (term172 A B P p1).
Proof. exact (fun_ext (fun p2 : B => @lem57554 A B P p1 p2)). Qed.
Lemma lem57556 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem57557 {A B : Type'} (P : type1413 A B) (p1 : A) : (term173 A B P p1) = (term173 A B P p1).
Proof. exact (MK_COMB (@lem57556 B) (@lem57555 A B P p1)). Qed.
Lemma lem57558 {A B : Type'} (P : type1413 A B) : (term178 A B P) = (term178 A B P).
Proof. exact (fun_ext (fun p1 : A => @lem57557 A B P p1)). Qed.
Lemma lem57559 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem57561 {A B : Type'} (P : type1413 A B) : (term179 A B P) = (term179 A B P).
Proof. exact (MK_COMB (@lem57559 A) (@lem57558 A B P)). Qed.
Lemma lem57562 {A B : Type'} (P : type1413 A B) (h1 : term143 A B P) : term179 A B P.
Proof. exact (EQ_MP (@lem57561 A B P) (@lem57548 A B P h1)). Qed.
Lemma lem57563 {A B : Type'} (_1601 : A) (P : type1413 A B) (h1 : term143 A B P) : term180 A B P _1601.
Proof. exact (@lem57562 A B P h1 _1601). Qed.
Lemma lem57564 {A B : Type'} (P : type1413 A B) (_1601 : A) : (term180 A B P _1601) = (term173 A B P _1601).
Proof. exact (eq_refl (term180 A B P _1601)). Qed.
Lemma lem57565 {A B : Type'} (_1601 : A) (P : type1413 A B) (h1 : term143 A B P) : term173 A B P _1601.
Proof. exact (EQ_MP (@lem57564 A B P _1601) (@lem57563 A B _1601 P h1)). Qed.
Lemma lem57566 {A B : Type'} (_1601 : A) (_1602 : B) (P : type1413 A B) (h1 : term143 A B P) : term181 A B P _1601 _1602.
Proof. exact (@lem57565 A B _1601 P h1 _1602). Qed.
Lemma lem57567 {A B : Type'} (P : type1413 A B) (_1601 : A) (_1602 : B) : (term181 A B P _1601 _1602) = (term170 A B P _1601 _1602).
Proof. exact (eq_refl (term181 A B P _1601 _1602)). Qed.
Lemma lem57570 {A B : Type'} (P : type1413 A B) (x0 : A) (y0 : B) (h1 : P x0 y0) : P x0 y0.
Proof. exact (h1). Qed.
Lemma lem57572 {A B : Type'} (_1601 : A) (_1602 : B) (P : type1413 A B) (h1 : term143 A B P) : term170 A B P _1601 _1602.
Proof. exact (EQ_MP (@lem57567 A B P _1601 _1602) (@lem57566 A B _1601 _1602 P h1)). Qed.
Lemma lem57574 {A B : Type'} (P : type1413 A B) (x0 : A) (y0 : B) (h1 : P x0 y0) : P x0 y0.
Proof. exact (h1). Qed.
Lemma lem57575 {A B : Type'} (P : type1413 A B) (x0 : A) (y0 : B) (h1 : P x0 y0) : term182 A B P x0 y0.
Proof. exact (fun h0 : term170 A B P x0 y0 => @lem57574 A B P x0 y0 h1). Qed.
Lemma lem57577 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem57578 {A B : Type'} (P : type1413 A B) (x0 : A) (y0 : B) : (term182 A B P x0 y0) = (P x0 y0).
Proof. exact (@lem57577 (P x0 y0)). Qed.
Lemma lem57579 {A B : Type'} (P : type1413 A B) (x0 : A) (y0 : B) (h1 : P x0 y0) : P x0 y0.
Proof. exact (EQ_MP (@lem57578 A B P x0 y0) (@lem57575 A B P x0 y0 h1)). Qed.
Lemma lem57582 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem57584 {A B : Type'} (P : type1413 A B) (_1601 : A) (_1602 : B) : (term170 A B P _1601 _1602) = (term184 A B P _1601 _1602).
Proof. exact (@lem57582 (P _1601 _1602)). Qed.
Lemma lem57587 {A B : Type'} (_1601 : A) (_1602 : B) (P : type1413 A B) (h1 : term143 A B P) : term184 A B P _1601 _1602.
Proof. exact (EQ_MP (@lem57584 A B P _1601 _1602) (@lem57572 A B _1601 _1602 P h1)). Qed.
Lemma lem57588 {A B : Type'} (_1601 : A) (_1602 : B) (P : type1413 A B) (h1 : term143 A B P) : term184 A B P _1601 _1602.
Proof. exact (@lem57587 A B _1601 _1602 P h1). Qed.
Lemma lem57589 {A B : Type'} (x0 : A) (y0 : B) (P : type1413 A B) (h1 : term143 A B P) : term184 A B P x0 y0.
Proof. exact (@lem57588 A B x0 y0 P h1). Qed.
Lemma lem57592 {A B : Type'} (P : type1413 A B) (x0 : A) (y0 : B) (h1 : term143 A B P) (h2 : P x0 y0) : False.
Proof. exact (@lem57589 A B x0 y0 P h1 (@lem57579 A B P x0 y0 h2)). Qed.
Lemma lem57593 {A B : Type'} (P : type1413 A B) (x0 : A) (y0 : B) (h1 : term143 A B P) (h2 : P x0 y0) : term185.
Proof. exact (fun h0 : ~ False => @lem57592 A B P x0 y0 h1 h2). Qed.
Lemma lem57595 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem57596 : term185 = False.
Proof. exact (@lem57595 False). Qed.
Lemma lem57597 {A B : Type'} (P : type1413 A B) (x0 : A) (y0 : B) (h1 : term143 A B P) (h2 : P x0 y0) : False.
Proof. exact (EQ_MP (@lem57596) (@lem57593 A B P x0 y0 h1 h2)). Qed.
Lemma lem57598 {A B : Type'} (P : type1413 A B) (x0 : A) (y0 : B) (h1 : term143 A B P) (h2 : P x0 y0) : (P x0 y0) = False.
Proof. exact (prop_ext (fun h3 : P x0 y0 => @lem57597 A B P x0 y0 h1 h2) (fun h3 : False => @lem57570 A B P x0 y0 h2)). Qed.
Lemma lem57599 {A B : Type'} (P : type1413 A B) (x0 : A) (y0 : B) (h1 : term143 A B P) (h2 : P x0 y0) : False.
Proof. exact (EQ_MP (@lem57598 A B P x0 y0 h1 h2) (@lem57570 A B P x0 y0 h2)). Qed.
Lemma lem57600 {A B : Type'} (P : type1413 A B) (x0 : A) (y0 : B) (h1 : term143 A B P) (h2 : P x0 y0) : (P x0 y0) = False.
Proof. exact (prop_ext (fun h3 : P x0 y0 => @lem57599 A B P x0 y0 h1 h2) (fun h3 : False => @lem57552 A B P x0 y0 h2)). Qed.
Lemma lem57601 {A B : Type'} (P : type1413 A B) (x0 : A) (y0 : B) (h1 : term143 A B P) (h2 : P x0 y0) : False.
Proof. exact (EQ_MP (@lem57600 A B P x0 y0 h1 h2) (@lem57552 A B P x0 y0 h2)). Qed.
Lemma lem57602 {A B : Type'} (P : type1413 A B) (x0 : A) (y0 : B) (h1 : term143 A B P) (h2 : P x0 y0) : (P x0 y0) = False.
Proof. exact (prop_ext (fun h3 : P x0 y0 => @lem57601 A B P x0 y0 h1 h2) (fun h3 : False => @lem57552 A B P x0 y0 h2)). Qed.
Lemma lem57603 {A B : Type'} (P : type1413 A B) (x0 : A) (y0 : B) (h1 : term143 A B P) (h2 : P x0 y0) : False.
Proof. exact (EQ_MP (@lem57602 A B P x0 y0 h1 h2) (@lem57552 A B P x0 y0 h2)). Qed.
Lemma lem57604 {A B : Type'} (P : type1413 A B) (x0 : A) (y0 : B) (h1 : term143 A B P) (h2 : P x0 y0) : (P x0 y0) = False.
Proof. exact (prop_ext (fun h3 : P x0 y0 => @lem57603 A B P x0 y0 h1 h2) (fun h3 : False => @lem57534 A B P x0 y0 h2)). Qed.
Lemma lem57605 {A B : Type'} (P : type1413 A B) (x0 : A) (y0 : B) (h1 : term143 A B P) (h2 : P x0 y0) : False.
Proof. exact (EQ_MP (@lem57604 A B P x0 y0 h1 h2) (@lem57534 A B P x0 y0 h2)). Qed.
Lemma lem57606 {A B : Type'} (P : type1413 A B) (x0 : A) (y0 : B) (h1 : term143 A B P) (h2 : P x0 y0) : (P x0 y0) = False.
Proof. exact (prop_ext (fun h3 : P x0 y0 => @lem57605 A B P x0 y0 h1 h2) (fun h3 : False => @lem57494 A B P x0 y0 h2)). Qed.
Lemma lem57607 {A B : Type'} (P : type1413 A B) (x0 : A) (y0 : B) (h1 : term143 A B P) (h2 : P x0 y0) : False.
Proof. exact (EQ_MP (@lem57606 A B P x0 y0 h1 h2) (@lem57494 A B P x0 y0 h2)). Qed.
Lemma lem57608 {A B : Type'} (P : type1413 A B) (x0 : A) (y0 : B) (h1 : term143 A B P) (h2 : P x0 y0) : (term143 A B P) = False.
Proof. exact (prop_ext (fun h3 : term143 A B P => @lem57607 A B P x0 y0 h1 h2) (fun h3 : False => @lem57488 A B P h1)). Qed.
Lemma lem57609 {A B : Type'} (P : type1413 A B) (x0 : A) (y0 : B) (h1 : term143 A B P) (h2 : P x0 y0) : False.
Proof. exact (EQ_MP (@lem57608 A B P x0 y0 h1 h2) (@lem57488 A B P h1)). Qed.
Lemma lem57610 {A B : Type'} (P : type1413 A B) (x0 : A) (y0 : B) (h1 : P x0 y0) : term142 A B P.
Proof. exact (fun h0 : term143 A B P => @lem57609 A B P x0 y0 h0 h1). Qed.
Lemma lem57611 {A B : Type'} (P : type1413 A B) (x0 : A) (y0 : B) (h1 : P x0 y0) : term14 A B P.
Proof. exact (EQ_MP (@lem57487 A B P) (@lem57610 A B P x0 y0 h1)). Qed.
Lemma lem57612 {A B : Type'} (x0 : A) (y0 : B) (P : type1413 A B) : term151 A B x0 y0 P.
Proof. exact (fun h0 : P x0 y0 => @lem57611 A B P x0 y0 h0). Qed.
Lemma lem57617 {A B : Type'} (y0 : B) (P : type1413 A B) : term155 A B y0 P.
Proof. exact (fun x0 : A => @lem57612 A B x0 y0 P). Qed.
Lemma lem57622 {A B : Type'} (P : type1413 A B) : term159 A B P.
Proof. exact (fun y0 : B => @lem57617 A B y0 P). Qed.
Lemma lem57627 {A B : Type'} : term163 A B.
Proof. exact (fun P : type1413 A B => @lem57622 A B P). Qed.
Lemma lem57628 {A B : Type'} : term162 A B.
Proof. exact (EQ_MP (@lem57482 A B) (@lem57627 A B)). Qed.
Lemma lem57629 {A B : Type'} (P : type1413 A B) : term186 A B P.
Proof. exact (@lem57628 A B P). Qed.
Lemma lem57630 {A B : Type'} (P : type1413 A B) : (term186 A B P) = (term158 A B P).
Proof. exact (eq_refl (term186 A B P)). Qed.
Lemma lem57631 {A B : Type'} (P : type1413 A B) : term158 A B P.
Proof. exact (EQ_MP (@lem57630 A B P) (@lem57629 A B P)). Qed.
Lemma lem57632 {A B : Type'} (P : type1413 A B) (y0 : B) : term187 A B P y0.
Proof. exact (@lem57631 A B P y0). Qed.
Lemma lem57633 {A B : Type'} (y0 : B) (P : type1413 A B) : (term187 A B P y0) = (term154 A B y0 P).
Proof. exact (eq_refl (term187 A B P y0)). Qed.
Lemma lem57634 {A B : Type'} (y0 : B) (P : type1413 A B) : term154 A B y0 P.
Proof. exact (EQ_MP (@lem57633 A B y0 P) (@lem57632 A B P y0)). Qed.
Lemma lem57635 {A B : Type'} (y0 : B) (P : type1413 A B) (x0 : A) : term188 A B y0 P x0.
Proof. exact (@lem57634 A B y0 P x0). Qed.
Lemma lem57636 {A B : Type'} (x0 : A) (y0 : B) (P : type1413 A B) : (term188 A B y0 P x0) = (term144 A B x0 y0 P).
Proof. exact (eq_refl (term188 A B y0 P x0)). Qed.
Lemma lem57637 {A B : Type'} (x0 : A) (y0 : B) (P : type1413 A B) : term144 A B x0 y0 P.
Proof. exact (EQ_MP (@lem57636 A B x0 y0 P) (@lem57635 A B y0 P x0)). Qed.
Lemma lem57639 {A B : Type'} (x0 : A) (y0 : B) (P : type1413 A B) : term144 A B x0 y0 P.
Proof. exact (@lem57368 A B x0 y0 P (@lem57637 A B x0 y0 P)). Qed.
Lemma lem57640 {A B : Type'} (P : type1413 A B) (x0 : A) (y0 : B) (h1 : P x0 y0) : term142 A B P.
Proof. exact (@lem57639 A B x0 y0 P (@lem56983 A B P x0 y0 h1)). Qed.
Lemma lem57641 {A B : Type'} (P : type1413 A B) (x0 : A) (y0 : B) (h1 : term143 A B P) (h2 : P x0 y0) : False.
Proof. exact (@lem57640 A B P x0 y0 h2 (@lem57352 A B P h1)). Qed.
Lemma lem57642 {A B : Type'} (P : type1413 A B) (x0 : A) (y0 : B) (h1 : term143 A B P) (h2 : P x0 y0) : (term143 A B P) = False.
Proof. exact (prop_ext (fun h3 : term143 A B P => @lem57641 A B P x0 y0 h1 h2) (fun h3 : False => @lem57352 A B P h1)). Qed.
Lemma lem57643 {A B : Type'} (P : type1413 A B) (x0 : A) (y0 : B) (h1 : term143 A B P) (h2 : P x0 y0) : False.
Proof. exact (EQ_MP (@lem57642 A B P x0 y0 h1 h2) (@lem57352 A B P h1)). Qed.
Lemma lem57644 {A B : Type'} (P : type1413 A B) (x0 : A) (y0 : B) (h1 : P x0 y0) : term142 A B P.
Proof. exact (fun h0 : term143 A B P => @lem57643 A B P x0 y0 h0 h1). Qed.
Lemma lem57645 {A B : Type'} (P : type1413 A B) (x0 : A) (y0 : B) (h1 : P x0 y0) : term14 A B P.
Proof. exact (EQ_MP (@lem57351 A B P) (@lem57644 A B P x0 y0 h1)). Qed.
Lemma lem57646 {A B : Type'} (P : type1413 A B) (x0 : A) (y0 : B) (h1 : P x0 y0) : term121 A B P.
Proof. exact (EQ_MP (@lem57347 A B P) (@lem57645 A B P x0 y0 h1)). Qed.
Lemma lem57647 {A B : Type'} (c : type472 A B) (P : type1413 A B) (x0 : A) (y0 : B) (h1 : term91 A B c) (h2 : P x0 y0) : term85 A B c P.
Proof. exact (@lem57281 A B P c h1 (@lem57646 A B P x0 y0 h2)). Qed.
Lemma lem57648 {A B : Type'} (Q : type1210 A B) (c : type472 A B) (P : type1413 A B) (x0 : A) (y0 : B) (h1 : term13 A B P Q) (h2 : term91 A B c) (h3 : P x0 y0) : term109 A B Q c P.
Proof. exact (@lem57257 A B c P Q h1 (@lem57647 A B c P x0 y0 h2 h3)). Qed.
Lemma lem57649 {A B : Type'} (Q : type1210 A B) (c : type472 A B) (P : type1413 A B) (x0 : A) (y0 : B) (h1 : term13 A B P Q) (h2 : term91 A B c) (h3 : P x0 y0) : term94 A B Q c P.
Proof. exact (EQ_MP (@lem57230 A B Q c P) (@lem57648 A B Q c P x0 y0 h1 h2 h3)). Qed.
Lemma lem57650 {A B : Type'} (Q : type1210 A B) (c : type472 A B) (P : type1413 A B) (x0 : A) (y0 : B) (h1 : term13 A B P Q) (h2 : term91 A B c) (h3 : P x0 y0) : (term91 A B c) = (term94 A B Q c P).
Proof. exact (prop_ext (fun h4 : term91 A B c => @lem57649 A B Q c P x0 y0 h1 h2 h3) (fun h4 : term94 A B Q c P => @lem57219 A B c h2)). Qed.
Lemma lem57651 {A B : Type'} (Q : type1210 A B) (c : type472 A B) (P : type1413 A B) (x0 : A) (y0 : B) (h1 : term13 A B P Q) (h2 : term91 A B c) (h3 : P x0 y0) : term94 A B Q c P.
Proof. exact (EQ_MP (@lem57650 A B Q c P x0 y0 h1 h2 h3) (@lem57219 A B c h2)). Qed.
Lemma lem57652 {A B : Type'} (c : type472 A B) (Q : type1210 A B) (P : type1413 A B) (x0 : A) (y0 : B) (h1 : term13 A B P Q) (h2 : P x0 y0) : term95 A B Q c P.
Proof. exact (fun h0 : term91 A B c => @lem57651 A B Q c P x0 y0 h1 h0 h2). Qed.
Lemma lem57657 {A B : Type'} (Q : type1210 A B) (P : type1413 A B) (x0 : A) (y0 : B) (h1 : term13 A B P Q) (h2 : P x0 y0) : term96 A B Q P.
Proof. exact (fun c : type472 A B => @lem57652 A B c Q P x0 y0 h1 h2). Qed.
Lemma lem57659 {A B : Type'} (Q : type1210 A B) (P : type1413 A B) (x0 : A) (y0 : B) (h1 : term13 A B P Q) (h2 : P x0 y0) : term21 A B Q P.
Proof. exact (@lem57218 A B Q P (@lem57657 A B Q P x0 y0 h1 h2)). Qed.
Lemma lem57660 {A B : Type'} (Q : type1210 A B) (P : type1413 A B) (x0 : A) (y0 : B) (h1 : term13 A B P Q) (h2 : (term16 A B P) = (term17 A B P)) (h3 : P x0 y0) : term23 A B Q P.
Proof. exact (EQ_MP (@lem56997 A B Q P h2) (@lem57659 A B Q P x0 y0 h1 h3)). Qed.
Lemma lem57661 {A B : Type'} (Q : type1210 A B) (P : type1413 A B) (x0 : A) (y0 : B) (h1 : term13 A B P Q) (h2 : P x0 y0) : ((term16 A B P) = (term17 A B P)) = (term23 A B Q P).
Proof. exact (prop_ext (fun h3 : (term16 A B P) = (term17 A B P) => @lem57660 A B Q P x0 y0 h1 h3 h2) (fun h3 : term23 A B Q P => @lem57093 A B P)). Qed.
Lemma lem57662 {A B : Type'} (Q : type1210 A B) (P : type1413 A B) (x0 : A) (y0 : B) (h1 : term13 A B P Q) (h2 : P x0 y0) : term23 A B Q P.
Proof. exact (EQ_MP (@lem57661 A B Q P x0 y0 h1 h2) (@lem57093 A B P)). Qed.
Lemma lem57663 {A B : Type'} (P : type1413 A B) (Q : type1210 A B) (h1 : term12 A B P Q) : term13 A B P Q.
Proof. exact (proj2 (@lem56979 A B P Q h1)). Qed.
Lemma lem57664 {A B : Type'} (P : type1413 A B) (Q : type1210 A B) (h1 : term12 A B P Q) : term14 A B P.
Proof. exact (proj1 (@lem56979 A B P Q h1)). Qed.
Lemma lem57665 {A B : Type'} (Q : type1210 A B) (P : type1413 A B) (x0 : A) (y0 : B) (h1 : term13 A B P Q) (h2 : P x0 y0) : (term13 A B P Q) = (term23 A B Q P).
Proof. exact (prop_ext (fun h3 : term13 A B P Q => @lem57662 A B Q P x0 y0 h1 h2) (fun h3 : term23 A B Q P => @lem56980 A B P Q h1)). Qed.
Lemma lem57666 {A B : Type'} (Q : type1210 A B) (P : type1413 A B) (x0 : A) (y0 : B) (h1 : term13 A B P Q) (h2 : P x0 y0) : term23 A B Q P.
Proof. exact (EQ_MP (@lem57665 A B Q P x0 y0 h1 h2) (@lem56980 A B P Q h1)). Qed.
Lemma lem57667 {A B : Type'} (Q : type1210 A B) (P : type1413 A B) (x0 : A) (y0 : B) (h1 : term13 A B P Q) (h2 : P x0 y0) : (P x0 y0) = (term23 A B Q P).
Proof. exact (prop_ext (fun h3 : P x0 y0 => @lem57666 A B Q P x0 y0 h1 h2) (fun h3 : term23 A B Q P => @lem56983 A B P x0 y0 h2)). Qed.
Lemma lem57668 {A B : Type'} (Q : type1210 A B) (P : type1413 A B) (x0 : A) (y0 : B) (h1 : term13 A B P Q) (h2 : P x0 y0) : term23 A B Q P.
Proof. exact (EQ_MP (@lem57667 A B Q P x0 y0 h1 h2) (@lem56983 A B P x0 y0 h2)). Qed.
Lemma lem57669 {A B : Type'} (Q : type1210 A B) (P : type1413 A B) (x0 : A) (h1 : term13 A B P Q) (h2 : term15 A B P x0) : term23 A B Q P.
Proof. exact (ex_elim (@lem56982 A B P x0 h2) (fun y0 : B => fun h0 : term139 A B P x0 y0 => @lem57668 A B Q P x0 y0 h1 h0)). Qed.
Lemma lem57670 {A B : Type'} (Q : type1210 A B) (P : type1413 A B) (h1 : term13 A B P Q) (h2 : term14 A B P) : term23 A B Q P.
Proof. exact (ex_elim (@lem56981 A B P h2) (fun x0 : A => fun h0 : term140 A B P x0 => @lem57669 A B Q P x0 h1 h0)). Qed.
Lemma lem57671 {A B : Type'} (P : type1413 A B) (Q : type1210 A B) (h1 : term14 A B P) (h2 : term12 A B P Q) : (term13 A B P Q) = (term23 A B Q P).
Proof. exact (prop_ext (fun h3 : term13 A B P Q => @lem57670 A B Q P h3 h1) (fun h3 : term23 A B Q P => @lem57663 A B P Q h2)). Qed.
Lemma lem57672 {A B : Type'} (P : type1413 A B) (Q : type1210 A B) (h1 : term14 A B P) (h2 : term12 A B P Q) : term23 A B Q P.
Proof. exact (EQ_MP (@lem57671 A B P Q h1 h2) (@lem57663 A B P Q h2)). Qed.
Lemma lem57673 {A B : Type'} (P : type1413 A B) (Q : type1210 A B) (h1 : term12 A B P Q) : (term14 A B P) = (term23 A B Q P).
Proof. exact (prop_ext (fun h2 : term14 A B P => @lem57672 A B P Q h2 h1) (fun h2 : term23 A B Q P => @lem57664 A B P Q h1)). Qed.
Lemma lem57674 {A B : Type'} (P : type1413 A B) (Q : type1210 A B) (h1 : term12 A B P Q) : term23 A B Q P.
Proof. exact (EQ_MP (@lem57673 A B P Q h1) (@lem57664 A B P Q h1)). Qed.
Lemma lem57675 {A B : Type'} (Q : type1210 A B) (P : type1413 A B) : term189 A B Q P.
Proof. exact (fun h0 : term12 A B P Q => @lem57674 A B P Q h0). Qed.
Lemma lem57681 {A B : Type'} (P : type1413 A B) : term190 A B P.
Proof. exact (fun Q : type1210 A B => @lem57675 A B Q P). Qed.
Lemma lem57687 {A B : Type'} : term191 A B.
Proof. exact (fun P : type1413 A B => @lem57681 A B P). Qed.
