Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_INDUCT_STRONG_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import FINITE_INDUCT_spec.
Require Import FINITE_RULES_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17646_spec.
Require Import thm1842_spec.
Require Import thm19490_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211692_spec.
Require Import thm3211693_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem3556974 {A : Type'} (x : A) (s : A -> Prop) : term0 A x s.
Proof. exact (@lem9784 (@IN A x s)). Qed.
Lemma lem3556975 {A : Type'} (x : A) (s : A -> Prop) : (term0 A x s) = (term1 A x s).
Proof. exact (eq_refl (term0 A x s)). Qed.
Lemma lem3556976 {A : Type'} (x : A) (s : A -> Prop) : term1 A x s.
Proof. exact (EQ_MP (@lem3556975 A x s) (@lem3556974 A x s)). Qed.
Lemma lem3556977 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem3556978 {A : Type'} (x : A) (s : A -> Prop) (h1 : term2 A x s) : term2 A x s.
Proof. exact (h1). Qed.
Lemma lem3556979 {A : Type'} (h1 : term3 A) : term3 A.
Proof. exact (h1). Qed.
Lemma lem3556980 {A : Type'} (FINITE' : type686 A) (h1 : term3 A) : term4 A FINITE'.
Proof. exact (@lem3556979 A h1 FINITE'). Qed.
Lemma lem3556981 {A : Type'} (FINITE' : type686 A) : (term4 A FINITE') = (term5 A FINITE').
Proof. exact (eq_refl (term4 A FINITE')). Qed.
Lemma lem3556982 {A : Type'} (FINITE' : type686 A) (h1 : term3 A) : term5 A FINITE'.
Proof. exact (EQ_MP (@lem3556981 A FINITE') (@lem3556980 A FINITE' h1)). Qed.
Lemma lem3556983 {A : Type'} (FINITE' : type686 A) (h1 : term6 A FINITE') : term6 A FINITE'.
Proof. exact (h1). Qed.
Lemma lem3556984 {A : Type'} (FINITE' : type686 A) (h1 : term3 A) (h2 : term6 A FINITE') : term7 A FINITE'.
Proof. exact (@lem3556982 A FINITE' h1 (@lem3556983 A FINITE' h2)). Qed.
Lemma lem3556985 {A : Type'} (FINITE' : type686 A) (h1 : term6 A FINITE') : term8 A FINITE'.
Proof. exact (fun h0 : term3 A => @lem3556984 A FINITE' h0 h1). Qed.
Lemma lem3556986 {A : Type'} (h1 : term3 A) : term3 A.
Proof. exact (h1). Qed.
Lemma lem3556987 {A : Type'} (FINITE' : type686 A) (h1 : term3 A) (h2 : term6 A FINITE') : term7 A FINITE'.
Proof. exact (@lem3556985 A FINITE' h2 (@lem3556986 A h1)). Qed.
Lemma lem3556988 {A : Type'} (FINITE' : type686 A) (h1 : term3 A) : term5 A FINITE'.
Proof. exact (fun h0 : term6 A FINITE' => @lem3556987 A FINITE' h1 h0). Qed.
Lemma lem3556989 {A : Type'} (h1 : term3 A) : term3 A.
Proof. exact (fun FINITE' : type686 A => @lem3556988 A FINITE' h1). Qed.
Lemma lem3556990 {A : Type'} : term9 A.
Proof. exact (fun h0 : term3 A => @lem3556989 A h0). Qed.
Lemma lem3556991 {A : Type'} : term3 A.
Proof. exact (@lem3556990 A (@lem3197567 A)). Qed.
Lemma lem3556992 {A : Type'} (FINITE' : type686 A) : term4 A FINITE'.
Proof. exact (@lem3556991 A FINITE'). Qed.
Lemma lem3556993 {A : Type'} (FINITE' : type686 A) : (term4 A FINITE') = (term5 A FINITE').
Proof. exact (eq_refl (term4 A FINITE')). Qed.
Lemma lem3557005 {A : Type'} (P : type686 A) (h1 : term10 A P) : term10 A P.
Proof. exact (h1). Qed.
Lemma lem3557006 {A : Type'} (P : type686 A) (h1 : term11 A P) : term11 A P.
Proof. exact (h1). Qed.
Lemma lem3557007 {A : Type'} (P : type686 A) (h1 : P (@EMPTY A)) : P (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem3557008 {A : Type'} (P : type686 A) (h1 : term12 A P) : term12 A P.
Proof. exact (h1). Qed.
Lemma lem3557010 (p : Prop) : p = (term13 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3557011 {A : Type'} (P : type686 A) : (term14 A P) = (term15 A P).
Proof. exact (@lem3557010 (term14 A P)). Qed.
Lemma lem3557012 {A : Type'} (P : type686 A) : (term15 A P) = (term14 A P).
Proof. exact (SYM (@lem3557011 A P)). Qed.
Lemma lem3557013 {A : Type'} (P : type686 A) (h1 : term16 A P) : term16 A P.
Proof. exact (h1). Qed.
Lemma lem3557016 {A : Type'} (P : type686 A) (h1 : term15 A P) : term15 A P.
Proof. exact (h1). Qed.
Lemma lem3557017 {A : Type'} (P : type686 A) : term17 A P.
Proof. exact (fun h0 : term15 A P => @lem3557016 A P h0). Qed.
Lemma lem3557018 {A : Type'} (P : type686 A) (h1 : term17 A P) : term17 A P.
Proof. exact (h1). Qed.
Lemma lem3557019 {A : Type'} (P : type686 A) (h1 : term15 A P) : term15 A P.
Proof. exact (h1). Qed.
Lemma lem3557020 {A : Type'} (P : type686 A) (h1 : term15 A P) (h2 : term17 A P) : term15 A P.
Proof. exact (@lem3557018 A P h2 (@lem3557019 A P h1)). Qed.
Lemma lem3557021 {A : Type'} (P : type686 A) (h1 : term15 A P) : term18 A P.
Proof. exact (fun h0 : term17 A P => @lem3557020 A P h1 h0). Qed.
Lemma lem3557022 {A : Type'} (P : type686 A) (h1 : term17 A P) : term17 A P.
Proof. exact (h1). Qed.
Lemma lem3557023 {A : Type'} (P : type686 A) (h1 : term15 A P) (h2 : term17 A P) : term15 A P.
Proof. exact (@lem3557021 A P h1 (@lem3557022 A P h2)). Qed.
Lemma lem3557024 {A : Type'} (P : type686 A) (h1 : term17 A P) : term17 A P.
Proof. exact (fun h0 : term15 A P => @lem3557023 A P h0 h1). Qed.
Lemma lem3557025 {A : Type'} (P : type686 A) : term19 A P.
Proof. exact (fun h0 : term17 A P => @lem3557024 A P h0). Qed.
Lemma lem3557028 {A : Type'} (P : type686 A) : term17 A P.
Proof. exact (@lem3557025 A P (@lem3557017 A P)). Qed.
Lemma lem3557029 {A : Type'} (P : type686 A) : term17 A P.
Proof. exact (@lem3557028 A P). Qed.
Lemma lem3557035 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3557036 {A : Type'} (P : type686 A) : (term15 A P) = (term20 A P).
Proof. exact (@lem3557035 (term16 A P)). Qed.
Lemma lem3557038 (t : Prop) : (term21 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3557039 {A : Type'} (P : type686 A) : (term20 A P) = (term14 A P).
Proof. exact (@lem3557038 (term14 A P)). Qed.
Lemma lem3557042 {A : Type'} (P : type686 A) : (term15 A P) = (term14 A P).
Proof. exact (TRANS (@lem3557036 A P) (@lem3557039 A P)). Qed.
Lemma lem3557057 {A : Type'} : (term22 A) = (term23 A).
Proof. exact (fun_ext (fun P : type686 A => @lem3557042 A P)). Qed.
Lemma lem3557058 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem3557067 {A : Type'} : (term24 A) = (term25 A).
Proof. exact (MK_COMB (@lem3557058 A) (@lem3557057 A)). Qed.
Lemma lem3557072 {A : Type'} (P : type686 A) (s : A -> Prop) : (term26 A P s) = (term26 A P s).
Proof. exact (eq_refl (term26 A P s)). Qed.
Lemma lem3557073 {A : Type'} (P : type686 A) : (term27 A P) = (term27 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3557072 A P s)). Qed.
Lemma lem3557074 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3557075 {A : Type'} (P : type686 A) : (term7 A P) = (term7 A P).
Proof. exact (MK_COMB (@lem3557074 A) (@lem3557073 A P)). Qed.
Lemma lem3557084 {A : Type'} (P : type686 A) (s : A -> Prop) : (term28 A P s) = (term28 A P s).
Proof. exact (eq_refl (term28 A P s)). Qed.
Lemma lem3557085 {A : Type'} (P : type686 A) : (term29 A P) = (term29 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3557084 A P s)). Qed.
Lemma lem3557086 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3557087 {A : Type'} (P : type686 A) : (term12 A P) = (term12 A P).
Proof. exact (MK_COMB (@lem3557086 A) (@lem3557085 A P)). Qed.
Lemma lem3557088 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3557089 {A : Type'} (P : type686 A) : (term30 A P) = (term30 A P).
Proof. exact (MK_COMB (@lem3557088) (@lem3557087 A P)). Qed.
Lemma lem3557090 {A : Type'} (P : type686 A) : (term14 A P) = (term14 A P).
Proof. exact (MK_COMB (@lem3557089 A P) (@lem3557075 A P)). Qed.
Lemma lem3557091 {A : Type'} : (term23 A) = (term23 A).
Proof. exact (fun_ext (fun P : type686 A => @lem3557090 A P)). Qed.
Lemma lem3557092 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem3557093 {A : Type'} : (term25 A) = (term25 A).
Proof. exact (MK_COMB (@lem3557092 A) (@lem3557091 A)). Qed.
Lemma lem3557122 {A : Type'} : (term24 A) = (term25 A).
Proof. exact (TRANS (@lem3557067 A) (@lem3557093 A)). Qed.
Lemma lem3557123 {A : Type'} : (term25 A) = (term24 A).
Proof. exact (SYM (@lem3557122 A)). Qed.
Lemma lem3557124 {A : Type'} (P : type686 A) (h1 : term12 A P) : term12 A P.
Proof. exact (h1). Qed.
Lemma lem3557127 (p : Prop) : p = (term13 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3557128 {A : Type'} (P : type686 A) (s : A -> Prop) : (P s) = (term31 A P s).
Proof. exact (@lem3557127 (P s)). Qed.
Lemma lem3557129 {A : Type'} (P : type686 A) (s : A -> Prop) : (term31 A P s) = (P s).
Proof. exact (SYM (@lem3557128 A P s)). Qed.
Lemma lem3557130 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term32 A P s) : term32 A P s.
Proof. exact (h1). Qed.
Lemma lem3557141 {A : Type'} (P : type686 A) (s : A -> Prop) : (term28 A P s) = (term33 A P s).
Proof. exact (@lem17265 (@FINITE A s) (term34 A P s)). Qed.
Lemma lem3557142 {A : Type'} (P : type686 A) : (term29 A P) = (term35 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3557141 A P s)). Qed.
Lemma lem3557143 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3557196 {A : Type'} (P : type686 A) : (term12 A P) = (term36 A P).
Proof. exact (MK_COMB (@lem3557143 A) (@lem3557142 A P)). Qed.
Lemma lem3557197 {A : Type'} (P : type686 A) (h1 : term12 A P) : term36 A P.
Proof. exact (EQ_MP (@lem3557196 A P) (@lem3557124 A P h1)). Qed.
Lemma lem3557203 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem3557209 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term32 A P s) : term32 A P s.
Proof. exact (h1). Qed.
Lemma lem3557226 {A : Type'} (P : type686 A) (s : A -> Prop) : (term33 A P s) = (term33 A P s).
Proof. exact (eq_refl (term33 A P s)). Qed.
Lemma lem3557227 {A : Type'} (P : type686 A) : (term35 A P) = (term35 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3557226 A P s)). Qed.
Lemma lem3557228 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3557229 {A : Type'} (P : type686 A) : (term36 A P) = (term36 A P).
Proof. exact (MK_COMB (@lem3557228 A) (@lem3557227 A P)). Qed.
Lemma lem3557230 {A : Type'} (P : type686 A) (h1 : term12 A P) : term36 A P.
Proof. exact (EQ_MP (@lem3557229 A P) (@lem3557197 A P h1)). Qed.
Lemma lem3557234 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem3557240 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term32 A P s) : term32 A P s.
Proof. exact (h1). Qed.
Lemma lem3557258 {A : Type'} (P : type686 A) (s : A -> Prop) : (term33 A P s) = (term37 A P s).
Proof. exact (@lem19490 (@FINITE A s) (term38 A s) (P s)). Qed.
Lemma lem3557259 {A : Type'} (P : type686 A) : (term35 A P) = (term39 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3557258 A P s)). Qed.
Lemma lem3557260 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3557262 {A : Type'} (P : type686 A) : (term36 A P) = (term40 A P).
Proof. exact (MK_COMB (@lem3557260 A) (@lem3557259 A P)). Qed.
Lemma lem3557263 {A : Type'} (P : type686 A) (h1 : term12 A P) : term40 A P.
Proof. exact (EQ_MP (@lem3557262 A P) (@lem3557230 A P h1)). Qed.
Lemma lem3557267 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem3557271 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term32 A P s) : term32 A P s.
Proof. exact (h1). Qed.
Lemma lem3557272 {A : Type'} (_38133 : A -> Prop) (P : type686 A) (h1 : term12 A P) : term41 A P _38133.
Proof. exact (@lem3557263 A P h1 _38133). Qed.
Lemma lem3557273 {A : Type'} (P : type686 A) (_38133 : A -> Prop) : (term41 A P _38133) = (term37 A P _38133).
Proof. exact (eq_refl (term41 A P _38133)). Qed.
Lemma lem3557274 {A : Type'} (_38133 : A -> Prop) (P : type686 A) (h1 : term12 A P) : term37 A P _38133.
Proof. exact (EQ_MP (@lem3557273 A P _38133) (@lem3557272 A _38133 P h1)). Qed.
Lemma lem3557278 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem3557280 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term32 A P s) : term32 A P s.
Proof. exact (h1). Qed.
Lemma lem3557292 {A : Type'} (_38133 : A -> Prop) (P : type686 A) (h1 : term12 A P) : term42 A P _38133.
Proof. exact (proj2 (@lem3557274 A _38133 P h1)). Qed.
Lemma lem3557294 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem3557295 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : term43 A s.
Proof. exact (fun h0 : term38 A s => @lem3557294 A s h1). Qed.
Lemma lem3557297 (p : Prop) : (term44 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3557298 {A : Type'} (s : A -> Prop) : (term43 A s) = (@FINITE A s).
Proof. exact (@lem3557297 (@FINITE A s)). Qed.
Lemma lem3557299 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (EQ_MP (@lem3557298 A s) (@lem3557295 A s h1)). Qed.
Lemma lem3557305 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3557306 {A : Type'} (P : type686 A) (_38133 : A -> Prop) : (term42 A P _38133) = (term45 A P _38133).
Proof. exact (@lem3557305 (P _38133) (term38 A _38133)). Qed.
Lemma lem3557312 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3557313 {A : Type'} (P : type686 A) (_38133 : A -> Prop) : (term46 A P _38133) = (term47 A P _38133).
Proof. exact (MK_COMB (@lem3557312) (@lem3557306 A P _38133)). Qed.
Lemma lem3557319 {A : Type'} (P : type686 A) (_38133 : A -> Prop) : (term45 A P _38133) = (term45 A P _38133).
Proof. exact (eq_refl (term45 A P _38133)). Qed.
Lemma lem3557320 {A : Type'} (P : type686 A) (_38133 : A -> Prop) : ((term42 A P _38133) = (term45 A P _38133)) = ((term45 A P _38133) = (term45 A P _38133)).
Proof. exact (MK_COMB (@lem3557313 A P _38133) (@lem3557319 A P _38133)). Qed.
Lemma lem3557322 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3557323 (x : Prop) : (x = x) = True.
Proof. exact (@lem3557322 Prop x). Qed.
Lemma lem3557324 {A : Type'} (P : type686 A) (_38133 : A -> Prop) : ((term45 A P _38133) = (term45 A P _38133)) = True.
Proof. exact (@lem3557323 (term45 A P _38133)). Qed.
Lemma lem3557325 {A : Type'} (P : type686 A) (_38133 : A -> Prop) : ((term42 A P _38133) = (term45 A P _38133)) = True.
Proof. exact (TRANS (@lem3557320 A P _38133) (@lem3557324 A P _38133)). Qed.
Lemma lem3557326 {A : Type'} (P : type686 A) (_38133 : A -> Prop) : True = ((term42 A P _38133) = (term45 A P _38133)).
Proof. exact (SYM (@lem3557325 A P _38133)). Qed.
Lemma lem3557327 {A : Type'} (P : type686 A) (_38133 : A -> Prop) : (term42 A P _38133) = (term45 A P _38133).
Proof. exact (EQ_MP (@lem3557326 A P _38133) (@lem0)). Qed.
Lemma lem3557328 {A : Type'} (_38133 : A -> Prop) (P : type686 A) (h1 : term12 A P) : term45 A P _38133.
Proof. exact (EQ_MP (@lem3557327 A P _38133) (@lem3557292 A _38133 P h1)). Qed.
Lemma lem3557330 (b : Prop) (a : Prop) : (a \/ b) = (term48 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3557331 {A : Type'} (P : type686 A) (_38133 : A -> Prop) : (term45 A P _38133) = (term49 A P _38133).
Proof. exact (@lem3557330 (term38 A _38133) (P _38133)). Qed.
Lemma lem3557333 (a : Prop) : (term21 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3557334 {A : Type'} (_38133 : A -> Prop) : (term50 A _38133) = (@FINITE A _38133).
Proof. exact (@lem3557333 (@FINITE A _38133)). Qed.
Lemma lem3557335 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3557336 {A : Type'} (_38133 : A -> Prop) : (term51 A _38133) = (term52 A _38133).
Proof. exact (MK_COMB (@lem3557335) (@lem3557334 A _38133)). Qed.
Lemma lem3557337 {A : Type'} (P : type686 A) (_38133 : A -> Prop) : (P _38133) = (P _38133).
Proof. exact (eq_refl (P _38133)). Qed.
Lemma lem3557338 {A : Type'} (P : type686 A) (_38133 : A -> Prop) : (term49 A P _38133) = (term26 A P _38133).
Proof. exact (MK_COMB (@lem3557336 A _38133) (@lem3557337 A P _38133)). Qed.
Lemma lem3557339 {A : Type'} (P : type686 A) (_38133 : A -> Prop) : (term45 A P _38133) = (term26 A P _38133).
Proof. exact (TRANS (@lem3557331 A P _38133) (@lem3557338 A P _38133)). Qed.
Lemma lem3557342 {A : Type'} (_38133 : A -> Prop) (P : type686 A) (h1 : term12 A P) : term26 A P _38133.
Proof. exact (EQ_MP (@lem3557339 A P _38133) (@lem3557328 A _38133 P h1)). Qed.
Lemma lem3557343 {A : Type'} (_38133 : A -> Prop) (P : type686 A) (h1 : term12 A P) : term26 A P _38133.
Proof. exact (@lem3557342 A _38133 P h1). Qed.
Lemma lem3557344 {A : Type'} (s : A -> Prop) (P : type686 A) (h1 : term12 A P) : term26 A P s.
Proof. exact (@lem3557343 A s P h1). Qed.
Lemma lem3557347 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term12 A P) (h2 : @FINITE A s) : P s.
Proof. exact (@lem3557344 A s P h1 (@lem3557299 A s h2)). Qed.
Lemma lem3557348 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term12 A P) (h2 : @FINITE A s) : term53 A P s.
Proof. exact (fun h0 : term32 A P s => @lem3557347 A P s h1 h2). Qed.
Lemma lem3557350 (p : Prop) : (term44 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3557351 {A : Type'} (P : type686 A) (s : A -> Prop) : (term53 A P s) = (P s).
Proof. exact (@lem3557350 (P s)). Qed.
Lemma lem3557352 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term12 A P) (h2 : @FINITE A s) : P s.
Proof. exact (EQ_MP (@lem3557351 A P s) (@lem3557348 A P s h1 h2)). Qed.
Lemma lem3557355 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3557357 {A : Type'} (P : type686 A) (s : A -> Prop) : (term32 A P s) = (term54 A P s).
Proof. exact (@lem3557355 (P s)). Qed.
Lemma lem3557360 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term32 A P s) : term54 A P s.
Proof. exact (EQ_MP (@lem3557357 A P s) (@lem3557280 A P s h1)). Qed.
Lemma lem3557363 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term12 A P) (h2 : @FINITE A s) (h3 : term32 A P s) : False.
Proof. exact (@lem3557360 A P s h3 (@lem3557352 A P s h1 h2)). Qed.
Lemma lem3557364 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term12 A P) (h2 : @FINITE A s) (h3 : term32 A P s) : term55.
Proof. exact (fun h0 : ~ False => @lem3557363 A P s h1 h2 h3). Qed.
Lemma lem3557366 (p : Prop) : (term44 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3557367 : term55 = False.
Proof. exact (@lem3557366 False). Qed.
Lemma lem3557368 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term12 A P) (h2 : @FINITE A s) (h3 : term32 A P s) : False.
Proof. exact (EQ_MP (@lem3557367) (@lem3557364 A P s h1 h2 h3)). Qed.
Lemma lem3557369 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term12 A P) (h2 : @FINITE A s) (h3 : term32 A P s) : (term32 A P s) = False.
Proof. exact (prop_ext (fun h4 : term32 A P s => @lem3557368 A P s h1 h2 h3) (fun h4 : False => @lem3557280 A P s h3)). Qed.
Lemma lem3557370 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term12 A P) (h2 : @FINITE A s) (h3 : term32 A P s) : False.
Proof. exact (EQ_MP (@lem3557369 A P s h1 h2 h3) (@lem3557280 A P s h3)). Qed.
Lemma lem3557371 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term12 A P) (h2 : @FINITE A s) (h3 : term32 A P s) : (@FINITE A s) = False.
Proof. exact (prop_ext (fun h4 : @FINITE A s => @lem3557370 A P s h1 h2 h3) (fun h4 : False => @lem3557278 A s h2)). Qed.
Lemma lem3557372 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term12 A P) (h2 : @FINITE A s) (h3 : term32 A P s) : False.
Proof. exact (EQ_MP (@lem3557371 A P s h1 h2 h3) (@lem3557278 A s h2)). Qed.
Lemma lem3557373 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term12 A P) (h2 : @FINITE A s) (h3 : term32 A P s) : (term32 A P s) = False.
Proof. exact (prop_ext (fun h4 : term32 A P s => @lem3557372 A P s h1 h2 h3) (fun h4 : False => @lem3557271 A P s h3)). Qed.
Lemma lem3557374 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term12 A P) (h2 : @FINITE A s) (h3 : term32 A P s) : False.
Proof. exact (EQ_MP (@lem3557373 A P s h1 h2 h3) (@lem3557271 A P s h3)). Qed.
Lemma lem3557375 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term12 A P) (h2 : @FINITE A s) (h3 : term32 A P s) : (@FINITE A s) = False.
Proof. exact (prop_ext (fun h4 : @FINITE A s => @lem3557374 A P s h1 h2 h3) (fun h4 : False => @lem3557267 A s h2)). Qed.
Lemma lem3557376 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term12 A P) (h2 : @FINITE A s) (h3 : term32 A P s) : False.
Proof. exact (EQ_MP (@lem3557375 A P s h1 h2 h3) (@lem3557267 A s h2)). Qed.
Lemma lem3557377 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term12 A P) (h2 : @FINITE A s) (h3 : term32 A P s) : (term32 A P s) = False.
Proof. exact (prop_ext (fun h4 : term32 A P s => @lem3557376 A P s h1 h2 h3) (fun h4 : False => @lem3557271 A P s h3)). Qed.
Lemma lem3557378 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term12 A P) (h2 : @FINITE A s) (h3 : term32 A P s) : False.
Proof. exact (EQ_MP (@lem3557377 A P s h1 h2 h3) (@lem3557271 A P s h3)). Qed.
Lemma lem3557379 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term12 A P) (h2 : @FINITE A s) (h3 : term32 A P s) : (@FINITE A s) = False.
Proof. exact (prop_ext (fun h4 : @FINITE A s => @lem3557378 A P s h1 h2 h3) (fun h4 : False => @lem3557267 A s h2)). Qed.
Lemma lem3557380 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term12 A P) (h2 : @FINITE A s) (h3 : term32 A P s) : False.
Proof. exact (EQ_MP (@lem3557379 A P s h1 h2 h3) (@lem3557267 A s h2)). Qed.
Lemma lem3557381 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term12 A P) (h2 : @FINITE A s) (h3 : term32 A P s) : (term32 A P s) = False.
Proof. exact (prop_ext (fun h4 : term32 A P s => @lem3557380 A P s h1 h2 h3) (fun h4 : False => @lem3557240 A P s h3)). Qed.
Lemma lem3557382 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term12 A P) (h2 : @FINITE A s) (h3 : term32 A P s) : False.
Proof. exact (EQ_MP (@lem3557381 A P s h1 h2 h3) (@lem3557240 A P s h3)). Qed.
Lemma lem3557383 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term12 A P) (h2 : @FINITE A s) (h3 : term32 A P s) : (@FINITE A s) = False.
Proof. exact (prop_ext (fun h4 : @FINITE A s => @lem3557382 A P s h1 h2 h3) (fun h4 : False => @lem3557234 A s h2)). Qed.
Lemma lem3557384 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term12 A P) (h2 : @FINITE A s) (h3 : term32 A P s) : False.
Proof. exact (EQ_MP (@lem3557383 A P s h1 h2 h3) (@lem3557234 A s h2)). Qed.
Lemma lem3557385 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term12 A P) (h2 : @FINITE A s) (h3 : term32 A P s) : (term32 A P s) = False.
Proof. exact (prop_ext (fun h4 : term32 A P s => @lem3557384 A P s h1 h2 h3) (fun h4 : False => @lem3557209 A P s h3)). Qed.
Lemma lem3557386 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term12 A P) (h2 : @FINITE A s) (h3 : term32 A P s) : False.
Proof. exact (EQ_MP (@lem3557385 A P s h1 h2 h3) (@lem3557209 A P s h3)). Qed.
Lemma lem3557387 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term12 A P) (h2 : @FINITE A s) (h3 : term32 A P s) : (@FINITE A s) = False.
Proof. exact (prop_ext (fun h4 : @FINITE A s => @lem3557386 A P s h1 h2 h3) (fun h4 : False => @lem3557203 A s h2)). Qed.
Lemma lem3557388 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term12 A P) (h2 : @FINITE A s) (h3 : term32 A P s) : False.
Proof. exact (EQ_MP (@lem3557387 A P s h1 h2 h3) (@lem3557203 A s h2)). Qed.
Lemma lem3557389 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term12 A P) (h2 : @FINITE A s) (h3 : term32 A P s) : (term32 A P s) = False.
Proof. exact (prop_ext (fun h4 : term32 A P s => @lem3557388 A P s h1 h2 h3) (fun h4 : False => @lem3557130 A P s h3)). Qed.
Lemma lem3557390 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term12 A P) (h2 : @FINITE A s) (h3 : term32 A P s) : False.
Proof. exact (EQ_MP (@lem3557389 A P s h1 h2 h3) (@lem3557130 A P s h3)). Qed.
Lemma lem3557391 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term12 A P) (h2 : @FINITE A s) : term31 A P s.
Proof. exact (fun h0 : term32 A P s => @lem3557390 A P s h1 h2 h0). Qed.
Lemma lem3557392 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term12 A P) (h2 : @FINITE A s) : P s.
Proof. exact (EQ_MP (@lem3557129 A P s) (@lem3557391 A P s h1 h2)). Qed.
Lemma lem3557393 {A : Type'} (s : A -> Prop) (P : type686 A) (h1 : term12 A P) : term26 A P s.
Proof. exact (fun h0 : @FINITE A s => @lem3557392 A P s h1 h0). Qed.
Lemma lem3557398 {A : Type'} (P : type686 A) (h1 : term12 A P) : term7 A P.
Proof. exact (fun s : A -> Prop => @lem3557393 A s P h1). Qed.
Lemma lem3557399 {A : Type'} (P : type686 A) : term14 A P.
Proof. exact (fun h0 : term12 A P => @lem3557398 A P h0). Qed.
Lemma lem3557404 {A : Type'} : term25 A.
Proof. exact (fun P : type686 A => @lem3557399 A P). Qed.
Lemma lem3557405 {A : Type'} : term24 A.
Proof. exact (EQ_MP (@lem3557123 A) (@lem3557404 A)). Qed.
Lemma lem3557406 {A : Type'} (P : type686 A) : term56 A P.
Proof. exact (@lem3557405 A P). Qed.
Lemma lem3557407 {A : Type'} (P : type686 A) : (term56 A P) = (term15 A P).
Proof. exact (eq_refl (term56 A P)). Qed.
Lemma lem3557408 {A : Type'} (P : type686 A) : term15 A P.
Proof. exact (EQ_MP (@lem3557407 A P) (@lem3557406 A P)). Qed.
Lemma lem3557410 {A : Type'} (P : type686 A) : term15 A P.
Proof. exact (@lem3557029 A P (@lem3557408 A P)). Qed.
Lemma lem3557411 {A : Type'} (P : type686 A) (h1 : term16 A P) : False.
Proof. exact (@lem3557410 A P (@lem3557013 A P h1)). Qed.
Lemma lem3557412 {A : Type'} (P : type686 A) (h1 : term16 A P) : (term16 A P) = False.
Proof. exact (prop_ext (fun h2 : term16 A P => @lem3557411 A P h1) (fun h2 : False => @lem3557013 A P h1)). Qed.
Lemma lem3557413 {A : Type'} (P : type686 A) (h1 : term16 A P) : False.
Proof. exact (EQ_MP (@lem3557412 A P h1) (@lem3557013 A P h1)). Qed.
Lemma lem3557414 {A : Type'} (P : type686 A) : term15 A P.
Proof. exact (fun h0 : term16 A P => @lem3557413 A P h0). Qed.
Lemma lem3557415 {A : Type'} (P : type686 A) : term14 A P.
Proof. exact (EQ_MP (@lem3557012 A P) (@lem3557414 A P)). Qed.
Lemma lem3557417 {A : Type'} (FINITE' : type686 A) : term5 A FINITE'.
Proof. exact (EQ_MP (@lem3556993 A FINITE') (@lem3556992 A FINITE')). Qed.
Lemma lem3557418 {A : Type'} (FINITE' : type686 A) : term5 A FINITE'.
Proof. exact (@lem3557417 A FINITE'). Qed.
Lemma lem3557419 {A : Type'} (P : type686 A) : term57 A P.
Proof. exact (@lem3557418 A (term58 A P)). Qed.
Lemma lem3557420 {A : Type'} (P : type686 A) : (term59 A P) = (term60 A P).
Proof. exact (eq_refl (term59 A P)). Qed.
Lemma lem3557421 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3557422 {A : Type'} (P : type686 A) : (term61 A P) = (term62 A P).
Proof. exact (MK_COMB (@lem3557421) (@lem3557420 A P)). Qed.
Lemma lem3557423 {A : Type'} (P : type686 A) (s : A -> Prop) : (term63 A P s) = (term34 A P s).
Proof. exact (eq_refl (term63 A P s)). Qed.
Lemma lem3557424 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3557425 {A : Type'} (P : type686 A) (s : A -> Prop) : (term64 A P s) = (term65 A P s).
Proof. exact (MK_COMB (@lem3557424) (@lem3557423 A P s)). Qed.
Lemma lem3557426 {A : Type'} (P : type686 A) (x : A) (s : A -> Prop) : (term66 A P x s) = (term67 A P x s).
Proof. exact (eq_refl (term66 A P x s)). Qed.
Lemma lem3557427 {A : Type'} (P : type686 A) (x : A) (s : A -> Prop) : (term68 A P x s) = (term69 A P x s).
Proof. exact (MK_COMB (@lem3557425 A P s) (@lem3557426 A P x s)). Qed.
Lemma lem3557428 {A : Type'} (P : type686 A) (x : A) : (term70 A P x) = (term71 A P x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3557427 A P x s)). Qed.
Lemma lem3557429 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3557430 {A : Type'} (P : type686 A) (x : A) : (term72 A P x) = (term73 A P x).
Proof. exact (MK_COMB (@lem3557429 A) (@lem3557428 A P x)). Qed.
Lemma lem3557431 {A : Type'} (P : type686 A) : (term74 A P) = (term75 A P).
Proof. exact (fun_ext (fun x : A => @lem3557430 A P x)). Qed.
Lemma lem3557432 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3557433 {A : Type'} (P : type686 A) : (term76 A P) = (term77 A P).
Proof. exact (MK_COMB (@lem3557432 A) (@lem3557431 A P)). Qed.
Lemma lem3557434 {A : Type'} (P : type686 A) : (term78 A P) = (term79 A P).
Proof. exact (MK_COMB (@lem3557422 A P) (@lem3557433 A P)). Qed.
Lemma lem3557435 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3557436 {A : Type'} (P : type686 A) : (term80 A P) = (term81 A P).
Proof. exact (MK_COMB (@lem3557435) (@lem3557434 A P)). Qed.
Lemma lem3557437 {A : Type'} (P : type686 A) (s : A -> Prop) : (term63 A P s) = (term34 A P s).
Proof. exact (eq_refl (term63 A P s)). Qed.
Lemma lem3557438 {A : Type'} (s : A -> Prop) : (term52 A s) = (term52 A s).
Proof. exact (eq_refl (term52 A s)). Qed.
Lemma lem3557439 {A : Type'} (P : type686 A) (s : A -> Prop) : (term82 A P s) = (term28 A P s).
Proof. exact (MK_COMB (@lem3557438 A s) (@lem3557437 A P s)). Qed.
Lemma lem3557440 {A : Type'} (P : type686 A) : (term83 A P) = (term29 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3557439 A P s)). Qed.
Lemma lem3557441 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3557442 {A : Type'} (P : type686 A) : (term84 A P) = (term12 A P).
Proof. exact (MK_COMB (@lem3557441 A) (@lem3557440 A P)). Qed.
Lemma lem3557443 {A : Type'} (P : type686 A) : (term57 A P) = (term85 A P).
Proof. exact (MK_COMB (@lem3557436 A P) (@lem3557442 A P)). Qed.
Lemma lem3557444 {A : Type'} (P : type686 A) : term85 A P.
Proof. exact (EQ_MP (@lem3557443 A P) (@lem3557419 A P)). Qed.
Lemma lem3557445 {A : Type'} : term86 A.
Proof. exact (proj2 (@lem3197565 A)). Qed.
Lemma lem3557446 {A : Type'} (x : A) : term87 A x.
Proof. exact (@lem3557445 A x). Qed.
Lemma lem3557447 {A : Type'} (x : A) : (term87 A x) = (term88 A x).
Proof. exact (eq_refl (term87 A x)). Qed.
Lemma lem3557448 {A : Type'} (x : A) : term88 A x.
Proof. exact (EQ_MP (@lem3557447 A x) (@lem3557446 A x)). Qed.
Lemma lem3557449 {A : Type'} (x : A) (s : A -> Prop) : term89 A x s.
Proof. exact (@lem3557448 A x s). Qed.
Lemma lem3557450 {A : Type'} (x : A) (s : A -> Prop) : (term89 A x s) = (term90 A x s).
Proof. exact (eq_refl (term89 A x s)). Qed.
Lemma lem3557451 {A : Type'} (x : A) (s : A -> Prop) : term90 A x s.
Proof. exact (EQ_MP (@lem3557450 A x s) (@lem3557449 A x s)). Qed.
Lemma lem3557452 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem3557453 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : term91 A x s.
Proof. exact (@lem3557451 A x s (@lem3557452 A s h1)). Qed.
Lemma lem3557454 {A : Type'} (x : A) (s : A -> Prop) : (term91 A x s) = ((term91 A x s) = True).
Proof. exact (@lem7 (term91 A x s)). Qed.
Lemma lem3557455 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : (term91 A x s) = True.
Proof. exact (EQ_MP (@lem3557454 A x s) (@lem3557453 A x s h1)). Qed.
Lemma lem3557461 {A : Type'} : @FINITE A (@EMPTY A).
Proof. exact (proj1 (@lem3197565 A)). Qed.
Lemma lem3557462 {A : Type'} : (@FINITE A (@EMPTY A)) = ((@FINITE A (@EMPTY A)) = True).
Proof. exact (@lem7 (@FINITE A (@EMPTY A))). Qed.
Lemma lem3557464 {A : Type'} (P : type686 A) : (P (@EMPTY A)) = ((P (@EMPTY A)) = True).
Proof. exact (@lem7 (P (@EMPTY A))). Qed.
Lemma lem3557486 {A : Type'} : (@FINITE A (@EMPTY A)) = True.
Proof. exact (EQ_MP (@lem3557462 A) (@lem3557461 A)). Qed.
Lemma lem3557487 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3557488 {A : Type'} : (term92 A) = (and True).
Proof. exact (MK_COMB (@lem3557487) (@lem3557486 A)). Qed.
Lemma lem3557490 {A : Type'} (P : type686 A) (h1 : P (@EMPTY A)) : (P (@EMPTY A)) = True.
Proof. exact (EQ_MP (@lem3557464 A P) (@lem3557007 A P h1)). Qed.
Lemma lem3557491 {A : Type'} (P : type686 A) (h1 : P (@EMPTY A)) : (term60 A P) = (True /\ True).
Proof. exact (MK_COMB (@lem3557488 A) (@lem3557490 A P h1)). Qed.
Lemma lem3557493 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3557494 : (True /\ True) = True.
Proof. exact (@lem3557493 True). Qed.
Lemma lem3557495 {A : Type'} (P : type686 A) (h1 : P (@EMPTY A)) : (term60 A P) = True.
Proof. exact (TRANS (@lem3557491 A P h1) (@lem3557494)). Qed.
Lemma lem3557496 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3557497 {A : Type'} (P : type686 A) (h1 : P (@EMPTY A)) : (term62 A P) = (and True).
Proof. exact (MK_COMB (@lem3557496) (@lem3557495 A P h1)). Qed.
Lemma lem3557509 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term93 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem3557510 (p : Prop) (q : Prop) (p' : Prop) : term94 p q p'.
Proof. exact (fun q' : Prop => @lem3557509 p q p' q'). Qed.
Lemma lem3557511 (p : Prop) (q : Prop) : term95 p q.
Proof. exact (fun p' : Prop => @lem3557510 p q p'). Qed.
Lemma lem3557512 {A : Type'} (P : type686 A) (x : A) (s : A -> Prop) : term96 A P x s.
Proof. exact (@lem3557511 (term34 A P s) (term67 A P x s)). Qed.
Lemma lem3557513 {A : Type'} (P : type686 A) (x : A) (s : A -> Prop) (p' : Prop) : term97 A P x s p'.
Proof. exact (@lem3557512 A P x s p'). Qed.
Lemma lem3557514 {A : Type'} (P : type686 A) (x : A) (s : A -> Prop) (p' : Prop) : (term97 A P x s p') = (term98 A P x s p').
Proof. exact (eq_refl (term97 A P x s p')). Qed.
Lemma lem3557515 {A : Type'} (P : type686 A) (x : A) (s : A -> Prop) (p' : Prop) : term98 A P x s p'.
Proof. exact (EQ_MP (@lem3557514 A P x s p') (@lem3557513 A P x s p')). Qed.
Lemma lem3557516 {A : Type'} (P : type686 A) (x : A) (s : A -> Prop) (p' : Prop) (q' : Prop) : term99 A P x s p' q'.
Proof. exact (@lem3557515 A P x s p' q'). Qed.
Lemma lem3557517 {A : Type'} (P : type686 A) (x : A) (s : A -> Prop) (p' : Prop) (q' : Prop) : (term99 A P x s p' q') = (term100 A P x s p' q').
Proof. exact (eq_refl (term99 A P x s p' q')). Qed.
Lemma lem3557518 {A : Type'} (P : type686 A) (x : A) (s : A -> Prop) (p' : Prop) (q' : Prop) : term100 A P x s p' q'.
Proof. exact (EQ_MP (@lem3557517 A P x s p' q') (@lem3557516 A P x s p' q')). Qed.
Lemma lem3557521 {A : Type'} (P : type686 A) (s : A -> Prop) : (term34 A P s) = (term34 A P s).
Proof. exact (eq_refl (term34 A P s)). Qed.
Lemma lem3557522 {A : Type'} (x : A) (P : type686 A) (s : A -> Prop) (q' : Prop) : term101 A x P s q'.
Proof. exact (@lem3557518 A P x s (term34 A P s) q'). Qed.
Lemma lem3557523 {A : Type'} (x : A) (P : type686 A) (s : A -> Prop) (q' : Prop) : term102 A x P s q'.
Proof. exact (@lem3557522 A x P s q' (@lem3557521 A P s)). Qed.
Lemma lem3557524 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term34 A P s) : term34 A P s.
Proof. exact (h1). Qed.
Lemma lem3557528 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term34 A P s) : @FINITE A s.
Proof. exact (proj1 (@lem3557524 A P s h1)). Qed.
Lemma lem3557529 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem3557534 {A : Type'} (x : A) (s : A -> Prop) : term103 A x s.
Proof. exact (fun h0 : @FINITE A s => @lem3557455 A x s h0). Qed.
Lemma lem3557535 {A : Type'} (x : A) (s : A -> Prop) : term103 A x s.
Proof. exact (@lem3557534 A x s). Qed.
Lemma lem3557537 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term34 A P s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem3557529 A s) (@lem3557528 A P s h1)). Qed.
Lemma lem3557538 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term34 A P s) : True = (@FINITE A s).
Proof. exact (SYM (@lem3557537 A P s h1)). Qed.
Lemma lem3557539 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term34 A P s) : @FINITE A s.
Proof. exact (EQ_MP (@lem3557538 A P s h1) (@lem0)). Qed.
Lemma lem3557540 {A : Type'} (x : A) (P : type686 A) (s : A -> Prop) (h1 : term34 A P s) : (term91 A x s) = True.
Proof. exact (@lem3557535 A x s (@lem3557539 A P s h1)). Qed.
Lemma lem3557541 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3557542 {A : Type'} (x : A) (P : type686 A) (s : A -> Prop) (h1 : term34 A P s) : (term104 A x s) = (and True).
Proof. exact (MK_COMB (@lem3557541) (@lem3557540 A x P s h1)). Qed.
Lemma lem3557568 {A : Type'} (P : type686 A) (x : A) (s : A -> Prop) : (term105 A P x s) = (term105 A P x s).
Proof. exact (eq_refl (term105 A P x s)). Qed.
Lemma lem3557569 {A : Type'} (x : A) (P : type686 A) (s : A -> Prop) (h1 : term34 A P s) : (term67 A P x s) = (term106 A P x s).
Proof. exact (MK_COMB (@lem3557542 A x P s h1) (@lem3557568 A P x s)). Qed.
Lemma lem3557571 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3557572 {A : Type'} (P : type686 A) (x : A) (s : A -> Prop) : (term106 A P x s) = (term105 A P x s).
Proof. exact (@lem3557571 (term105 A P x s)). Qed.
Lemma lem3557598 {A : Type'} (x : A) (P : type686 A) (s : A -> Prop) (h1 : term34 A P s) : (term67 A P x s) = (term105 A P x s).
Proof. exact (TRANS (@lem3557569 A x P s h1) (@lem3557572 A P x s)). Qed.
Lemma lem3557599 {A : Type'} (P : type686 A) (x : A) (s : A -> Prop) : term107 A P x s.
Proof. exact (fun h0 : term34 A P s => @lem3557598 A x P s h0). Qed.
Lemma lem3557600 {A : Type'} (P : type686 A) (x : A) (s : A -> Prop) : term108 A P x s.
Proof. exact (@lem3557523 A x P s (term105 A P x s)). Qed.
Lemma lem3557601 {A : Type'} (P : type686 A) (x : A) (s : A -> Prop) : (term69 A P x s) = (term109 A P x s).
Proof. exact (@lem3557600 A P x s (@lem3557599 A P x s)). Qed.
Lemma lem3557667 {A : Type'} (P : type686 A) (x : A) : (term71 A P x) = (term110 A P x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3557601 A P x s)). Qed.
Lemma lem3557733 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3557734 {A : Type'} (P : type686 A) (x : A) : (term73 A P x) = (term111 A P x).
Proof. exact (MK_COMB (@lem3557733 A) (@lem3557667 A P x)). Qed.
Lemma lem3557804 {A : Type'} (P : type686 A) : (term75 A P) = (term112 A P).
Proof. exact (fun_ext (fun x : A => @lem3557734 A P x)). Qed.
Lemma lem3557874 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3557875 {A : Type'} (P : type686 A) : (term77 A P) = (term113 A P).
Proof. exact (MK_COMB (@lem3557874 A) (@lem3557804 A P)). Qed.
Lemma lem3557949 {A : Type'} (P : type686 A) (h1 : P (@EMPTY A)) : (term79 A P) = (term114 A P).
Proof. exact (MK_COMB (@lem3557497 A P h1) (@lem3557875 A P)). Qed.
Lemma lem3557951 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3557952 {A : Type'} (P : type686 A) : (term114 A P) = (term113 A P).
Proof. exact (@lem3557951 (term113 A P)). Qed.
Lemma lem3558026 {A : Type'} (P : type686 A) (h1 : P (@EMPTY A)) : (term79 A P) = (term113 A P).
Proof. exact (TRANS (@lem3557949 A P h1) (@lem3557952 A P)). Qed.
Lemma lem3558027 {A : Type'} (P : type686 A) (h1 : P (@EMPTY A)) : (term113 A P) = (term79 A P).
Proof. exact (SYM (@lem3558026 A P h1)). Qed.
Lemma lem3558028 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term34 A P s) : term34 A P s.
Proof. exact (h1). Qed.
Lemma lem3558029 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : P s) : P s.
Proof. exact (h1). Qed.
Lemma lem3558030 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem3558060 {A : Type'} (P : type686 A) (s : A -> Prop) : (P s) = ((P s) = True).
Proof. exact (@lem7 (P s)). Qed.
Lemma lem3558065 {A : Type'} (x : A) (s : A -> Prop) (h1 : (@INSERT A x s) = s) : (@INSERT A x s) = s.
Proof. exact (h1). Qed.
Lemma lem3558066 {A : Type'} (P : type686 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem3558067 {A : Type'} (P : type686 A) (x : A) (s : A -> Prop) (h1 : (@INSERT A x s) = s) : (term105 A P x s) = (P s).
Proof. exact (MK_COMB (@lem3558066 A P) (@lem3558065 A x s h1)). Qed.
Lemma lem3558069 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : P s) : (P s) = True.
Proof. exact (EQ_MP (@lem3558060 A P s) (@lem3558029 A P s h1)). Qed.
Lemma lem3558070 {A : Type'} (P : type686 A) (x : A) (s : A -> Prop) (h1 : P s) (h2 : (@INSERT A x s) = s) : (term105 A P x s) = True.
Proof. exact (TRANS (@lem3558067 A P x s h2) (@lem3558069 A P s h1)). Qed.
Lemma lem3558071 {A : Type'} (P : type686 A) (x : A) (s : A -> Prop) (h1 : P s) (h2 : (@INSERT A x s) = s) : True = (term105 A P x s).
Proof. exact (SYM (@lem3558070 A P x s h1 h2)). Qed.
Lemma lem3558072 {A : Type'} (P : type686 A) (x : A) (s : A -> Prop) (h1 : P s) (h2 : (@INSERT A x s) = s) : term105 A P x s.
Proof. exact (EQ_MP (@lem3558071 A P x s h1 h2) (@lem0)). Qed.
Lemma lem3558078 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term115 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3558079 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term115 A s t).
Proof. exact (@lem3558078 A s t). Qed.
Lemma lem3558080 {A : Type'} (x : A) (s : A -> Prop) : ((@INSERT A x s) = s) = (term116 A x s).
Proof. exact (@lem3558079 A (@INSERT A x s) s). Qed.
Lemma lem3558089 {A : Type'} (x : A) (s : A -> Prop) : (term117 A x s) = (term117 A x s).
Proof. exact (eq_refl (term117 A x s)). Qed.
Lemma lem3558090 {A : Type'} (x : A) (s : A -> Prop) : (term118 A x s) = (term119 A x s).
Proof. exact (MK_COMB (@lem3558089 A x s) (@lem3558080 A x s)). Qed.
Lemma lem3558093 {A : Type'} (x : A) (s : A -> Prop) : (term119 A x s) = (term118 A x s).
Proof. exact (SYM (@lem3558090 A x s)). Qed.
Lemma lem3558097 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3558098 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3558097 A P x). Qed.
Lemma lem3558099 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3558098 A s x). Qed.
Lemma lem3558100 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3558101 {A : Type'} (s : A -> Prop) (x : A) : (term117 A x s) = (term120 A s x).
Proof. exact (MK_COMB (@lem3558100) (@lem3558099 A s x)). Qed.
Lemma lem3558109 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term121 A x y s) = (term122 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3558110 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term121 A x y s) = (term122 A y x s).
Proof. exact (@lem3558109 A y x s). Qed.
Lemma lem3558111 {A : Type'} (x : A) (x' : A) (s : A -> Prop) : (term121 A x' x s) = (term122 A x x' s).
Proof. exact (@lem3558110 A x x' s). Qed.
Lemma lem3558117 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3558118 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3558117 A P x). Qed.
Lemma lem3558119 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3558118 A s x'). Qed.
Lemma lem3558120 {A : Type'} (x' : A) (x : A) : (term123 A x' x) = (term123 A x' x).
Proof. exact (eq_refl (term123 A x' x)). Qed.
Lemma lem3558121 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term122 A x x' s) = (term124 A x s x').
Proof. exact (MK_COMB (@lem3558120 A x' x) (@lem3558119 A s x')). Qed.
Lemma lem3558124 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term121 A x' x s) = (term124 A x s x').
Proof. exact (TRANS (@lem3558111 A x x' s) (@lem3558121 A x s x')). Qed.
Lemma lem3558125 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3558126 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term125 A x' x s) = (term126 A x s x').
Proof. exact (MK_COMB (@lem3558125) (@lem3558124 A x s x')). Qed.
Lemma lem3558128 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3558129 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3558128 A P x). Qed.
Lemma lem3558130 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3558129 A s x'). Qed.
Lemma lem3558131 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : ((term121 A x' x s) = (@IN A x' s)) = ((term124 A x s x') = (s x')).
Proof. exact (MK_COMB (@lem3558126 A x s x') (@lem3558130 A s x')). Qed.
Lemma lem3558134 {A : Type'} (x : A) (s : A -> Prop) : (term127 A x s) = (term128 A x s).
Proof. exact (fun_ext (fun x' : A => @lem3558131 A x s x')). Qed.
Lemma lem3558135 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3558136 {A : Type'} (x : A) (s : A -> Prop) : (term116 A x s) = (term129 A x s).
Proof. exact (MK_COMB (@lem3558135 A) (@lem3558134 A x s)). Qed.
Lemma lem3558141 {A : Type'} (x : A) (s : A -> Prop) : (term119 A x s) = (term130 A x s).
Proof. exact (MK_COMB (@lem3558101 A s x) (@lem3558136 A x s)). Qed.
Lemma lem3558144 {A : Type'} (x : A) (s : A -> Prop) : (term130 A x s) = (term119 A x s).
Proof. exact (SYM (@lem3558141 A x s)). Qed.
Lemma lem3558146 (p : Prop) : p = (term13 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3558147 {A : Type'} (x : A) (s : A -> Prop) : (term130 A x s) = (term131 A x s).
Proof. exact (@lem3558146 (term130 A x s)). Qed.
Lemma lem3558148 {A : Type'} (x : A) (s : A -> Prop) : (term131 A x s) = (term130 A x s).
Proof. exact (SYM (@lem3558147 A x s)). Qed.
Lemma lem3558149 {A : Type'} (x : A) (s : A -> Prop) (h1 : term132 A x s) : term132 A x s.
Proof. exact (h1). Qed.
Lemma lem3558152 {A : Type'} (x : A) (s : A -> Prop) (h1 : term131 A x s) : term131 A x s.
Proof. exact (h1). Qed.
Lemma lem3558153 {A : Type'} (x : A) (s : A -> Prop) : term133 A x s.
Proof. exact (fun h0 : term131 A x s => @lem3558152 A x s h0). Qed.
Lemma lem3558154 {A : Type'} (x : A) (s : A -> Prop) (h1 : term133 A x s) : term133 A x s.
Proof. exact (h1). Qed.
Lemma lem3558155 {A : Type'} (x : A) (s : A -> Prop) (h1 : term131 A x s) : term131 A x s.
Proof. exact (h1). Qed.
Lemma lem3558156 {A : Type'} (x : A) (s : A -> Prop) (h1 : term131 A x s) (h2 : term133 A x s) : term131 A x s.
Proof. exact (@lem3558154 A x s h2 (@lem3558155 A x s h1)). Qed.
Lemma lem3558157 {A : Type'} (x : A) (s : A -> Prop) (h1 : term131 A x s) : term134 A x s.
Proof. exact (fun h0 : term133 A x s => @lem3558156 A x s h1 h0). Qed.
Lemma lem3558158 {A : Type'} (x : A) (s : A -> Prop) (h1 : term133 A x s) : term133 A x s.
Proof. exact (h1). Qed.
Lemma lem3558159 {A : Type'} (x : A) (s : A -> Prop) (h1 : term131 A x s) (h2 : term133 A x s) : term131 A x s.
Proof. exact (@lem3558157 A x s h1 (@lem3558158 A x s h2)). Qed.
Lemma lem3558160 {A : Type'} (x : A) (s : A -> Prop) (h1 : term133 A x s) : term133 A x s.
Proof. exact (fun h0 : term131 A x s => @lem3558159 A x s h0 h1). Qed.
Lemma lem3558161 {A : Type'} (x : A) (s : A -> Prop) : term135 A x s.
Proof. exact (fun h0 : term133 A x s => @lem3558160 A x s h0). Qed.
Lemma lem3558164 {A : Type'} (x : A) (s : A -> Prop) : term133 A x s.
Proof. exact (@lem3558161 A x s (@lem3558153 A x s)). Qed.
Lemma lem3558165 {A : Type'} (x : A) (s : A -> Prop) : term133 A x s.
Proof. exact (@lem3558164 A x s). Qed.
Lemma lem3558175 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3558176 {A : Type'} (x : A) (s : A -> Prop) : (term131 A x s) = (term136 A x s).
Proof. exact (@lem3558175 (term132 A x s)). Qed.
Lemma lem3558178 (t : Prop) : (term21 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3558179 {A : Type'} (x : A) (s : A -> Prop) : (term136 A x s) = (term130 A x s).
Proof. exact (@lem3558178 (term130 A x s)). Qed.
Lemma lem3558182 {A : Type'} (x : A) (s : A -> Prop) : (term131 A x s) = (term130 A x s).
Proof. exact (TRANS (@lem3558176 A x s) (@lem3558179 A x s)). Qed.
Lemma lem3558189 {A : Type'} (s : A -> Prop) : (term137 A s) = (term138 A s).
Proof. exact (fun_ext (fun x : A => @lem3558182 A x s)). Qed.
Lemma lem3558190 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3558191 {A : Type'} (s : A -> Prop) : (term139 A s) = (term140 A s).
Proof. exact (MK_COMB (@lem3558190 A) (@lem3558189 A s)). Qed.
Lemma lem3558196 {A : Type'} : (term141 A) = (term142 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3558191 A s)). Qed.
Lemma lem3558197 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3558206 {A : Type'} : (term143 A) = (term144 A).
Proof. exact (MK_COMB (@lem3558197 A) (@lem3558196 A)). Qed.
Lemma lem3558215 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : ((term124 A x s x') = (s x')) = ((term124 A x s x') = (s x')).
Proof. exact (eq_refl ((term124 A x s x') = (s x'))). Qed.
Lemma lem3558216 {A : Type'} (x : A) (s : A -> Prop) : (term128 A x s) = (term128 A x s).
Proof. exact (fun_ext (fun x' : A => @lem3558215 A x s x')). Qed.
Lemma lem3558217 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3558218 {A : Type'} (x : A) (s : A -> Prop) : (term129 A x s) = (term129 A x s).
Proof. exact (MK_COMB (@lem3558217 A) (@lem3558216 A x s)). Qed.
Lemma lem3558221 {A : Type'} (s : A -> Prop) (x : A) : (term120 A s x) = (term120 A s x).
Proof. exact (eq_refl (term120 A s x)). Qed.
Lemma lem3558222 {A : Type'} (x : A) (s : A -> Prop) : (term130 A x s) = (term130 A x s).
Proof. exact (MK_COMB (@lem3558221 A s x) (@lem3558218 A x s)). Qed.
Lemma lem3558223 {A : Type'} (s : A -> Prop) : (term138 A s) = (term138 A s).
Proof. exact (fun_ext (fun x : A => @lem3558222 A x s)). Qed.
Lemma lem3558224 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3558225 {A : Type'} (s : A -> Prop) : (term140 A s) = (term140 A s).
Proof. exact (MK_COMB (@lem3558224 A) (@lem3558223 A s)). Qed.
Lemma lem3558226 {A : Type'} : (term142 A) = (term142 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3558225 A s)). Qed.
Lemma lem3558227 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3558228 {A : Type'} : (term144 A) = (term144 A).
Proof. exact (MK_COMB (@lem3558227 A) (@lem3558226 A)). Qed.
Lemma lem3558253 {A : Type'} : (term143 A) = (term144 A).
Proof. exact (TRANS (@lem3558206 A) (@lem3558228 A)). Qed.
Lemma lem3558254 {A : Type'} : (term144 A) = (term143 A).
Proof. exact (SYM (@lem3558253 A)). Qed.
Lemma lem3558257 (p : Prop) : p = (term13 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3558258 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : ((term124 A x s x') = (s x')) = (term145 A x s x').
Proof. exact (@lem3558257 ((term124 A x s x') = (s x'))). Qed.
Lemma lem3558259 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term145 A x s x') = ((term124 A x s x') = (s x')).
Proof. exact (SYM (@lem3558258 A x s x')). Qed.
Lemma lem3558260 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term146 A x s x') : term146 A x s x'.
Proof. exact (h1). Qed.
Lemma lem3558266 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3558275 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term147 A x s x') = (term148 A x s x').
Proof. exact (@lem17160 (x' = x) (s x')). Qed.
Lemma lem3558280 {A : Type'} (s : A -> Prop) (x' : A) : (s x') = (s x').
Proof. exact (eq_refl (s x')). Qed.
Lemma lem3558281 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3558282 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term149 A x s x') = (term150 A x s x').
Proof. exact (MK_COMB (@lem3558281) (@lem3558275 A x s x')). Qed.
Lemma lem3558283 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term151 A x s x') = (term152 A x s x').
Proof. exact (MK_COMB (@lem3558282 A x s x') (@lem3558280 A s x')). Qed.
Lemma lem3558288 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term153 A x s x') = (term153 A x s x').
Proof. exact (eq_refl (term153 A x s x')). Qed.
Lemma lem3558289 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term154 A x s x') = (term155 A x s x').
Proof. exact (MK_COMB (@lem3558288 A x s x') (@lem3558283 A x s x')). Qed.
Lemma lem3558290 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term146 A x s x') = (term154 A x s x').
Proof. exact (@lem17646 (term124 A x s x') (s x')). Qed.
Lemma lem3558295 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term146 A x s x') = (term155 A x s x').
Proof. exact (TRANS (@lem3558290 A x s x') (@lem3558289 A x s x')). Qed.
Lemma lem3558300 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3558344 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term146 A x s x') : term155 A x s x'.
Proof. exact (EQ_MP (@lem3558295 A x s x') (@lem3558260 A x s x' h1)). Qed.
Lemma lem3558345 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term156 A x s x') : term156 A x s x'.
Proof. exact (h1). Qed.
Lemma lem3558346 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term152 A x s x') : term152 A x s x'.
Proof. exact (h1). Qed.
Lemma lem3558348 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term156 A x s x') : term124 A x s x'.
Proof. exact (proj1 (@lem3558345 A x s x' h1)). Qed.
Lemma lem3558352 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term152 A x s x') : term148 A x s x'.
Proof. exact (proj1 (@lem3558346 A x s x' h1)). Qed.
Lemma lem3558358 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3558366 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3558378 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3558396 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3558398 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term156 A x s x') : term157 A s x'.
Proof. exact (proj2 (@lem3558345 A x s x' h1)). Qed.
Lemma lem3558400 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3558404 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term156 A x s x') : term157 A s x'.
Proof. exact (proj2 (@lem3558345 A x s x' h1)). Qed.
Lemma lem3558406 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3558414 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term152 A x s x') : term157 A s x'.
Proof. exact (proj2 (@lem3558352 A x s x' h1)). Qed.
Lemma lem3558442 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3558443 {A : Type'} (s : A -> Prop) : (term158 A s) = (term158 A s).
Proof. exact (eq_refl (term158 A s)). Qed.
Lemma lem3558444 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : x' = x) : (term159 A s x') = (term159 A s x).
Proof. exact (MK_COMB (@lem3558443 A s) (@lem3558400 A x' x h1)). Qed.
Lemma lem3558445 {A : Type'} (s : A -> Prop) (x : A) : (term159 A s x) = (term157 A s x).
Proof. exact (eq_refl (term159 A s x)). Qed.
Lemma lem3558446 {A : Type'} (s : A -> Prop) (x' : A) : (term160 A s x') = (term160 A s x').
Proof. exact (eq_refl (term160 A s x')). Qed.
Lemma lem3558447 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : ((term159 A s x') = (term159 A s x)) = ((term159 A s x') = (term157 A s x)).
Proof. exact (MK_COMB (@lem3558446 A s x') (@lem3558445 A s x)). Qed.
Lemma lem3558448 {A : Type'} (s : A -> Prop) (x' : A) : (term159 A s x') = (term157 A s x').
Proof. exact (eq_refl (term159 A s x')). Qed.
Lemma lem3558449 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3558450 {A : Type'} (s : A -> Prop) (x' : A) : (term160 A s x') = (term161 A s x').
Proof. exact (MK_COMB (@lem3558449) (@lem3558448 A s x')). Qed.
Lemma lem3558451 {A : Type'} (s : A -> Prop) (x : A) : (term157 A s x) = (term157 A s x).
Proof. exact (eq_refl (term157 A s x)). Qed.
Lemma lem3558452 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : ((term159 A s x') = (term157 A s x)) = ((term157 A s x') = (term157 A s x)).
Proof. exact (MK_COMB (@lem3558450 A s x') (@lem3558451 A s x)). Qed.
Lemma lem3558453 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : ((term159 A s x') = (term159 A s x)) = ((term157 A s x') = (term157 A s x)).
Proof. exact (TRANS (@lem3558447 A x' s x) (@lem3558452 A x' s x)). Qed.
Lemma lem3558454 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : x' = x) : (term157 A s x') = (term157 A s x).
Proof. exact (EQ_MP (@lem3558453 A x' s x) (@lem3558444 A s x' x h1)). Qed.
Lemma lem3558455 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term156 A x s x') (h2 : x' = x) : term157 A s x.
Proof. exact (EQ_MP (@lem3558454 A s x' x h2) (@lem3558398 A x s x' h1)). Qed.
Lemma lem3558457 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3558458 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : term162 A s x.
Proof. exact (fun h0 : term157 A s x => @lem3558457 A s x h1). Qed.
Lemma lem3558460 (p : Prop) : (term44 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3558461 {A : Type'} (s : A -> Prop) (x : A) : (term162 A s x) = (s x).
Proof. exact (@lem3558460 (s x)). Qed.
Lemma lem3558462 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (EQ_MP (@lem3558461 A s x) (@lem3558458 A s x h1)). Qed.
Lemma lem3558465 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3558467 {A : Type'} (s : A -> Prop) (x : A) : (term157 A s x) = (term163 A s x).
Proof. exact (@lem3558465 (s x)). Qed.
Lemma lem3558470 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term156 A x s x') (h2 : x' = x) : term163 A s x.
Proof. exact (EQ_MP (@lem3558467 A s x) (@lem3558455 A s x' x h1 h2)). Qed.
Lemma lem3558473 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term156 A x s x') (h3 : x' = x) : False.
Proof. exact (@lem3558470 A s x' x h2 h3 (@lem3558462 A s x h1)). Qed.
Lemma lem3558474 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term156 A x s x') (h3 : x' = x) : term55.
Proof. exact (fun h0 : ~ False => @lem3558473 A s x' x h1 h2 h3). Qed.
Lemma lem3558476 (p : Prop) : (term44 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3558477 : term55 = False.
Proof. exact (@lem3558476 False). Qed.
Lemma lem3558478 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term156 A x s x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3558477) (@lem3558474 A s x' x h1 h2 h3)). Qed.
Lemma lem3558480 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3558481 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : term162 A s x'.
Proof. exact (fun h0 : term157 A s x' => @lem3558480 A s x' h1). Qed.
Lemma lem3558483 (p : Prop) : (term44 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3558484 {A : Type'} (s : A -> Prop) (x' : A) : (term162 A s x') = (s x').
Proof. exact (@lem3558483 (s x')). Qed.
Lemma lem3558485 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (EQ_MP (@lem3558484 A s x') (@lem3558481 A s x' h1)). Qed.
Lemma lem3558488 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3558490 {A : Type'} (s : A -> Prop) (x' : A) : (term157 A s x') = (term163 A s x').
Proof. exact (@lem3558488 (s x')). Qed.
Lemma lem3558493 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term156 A x s x') : term163 A s x'.
Proof. exact (EQ_MP (@lem3558490 A s x') (@lem3558404 A x s x' h1)). Qed.
Lemma lem3558496 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term156 A x s x') : False.
Proof. exact (@lem3558493 A x s x' h2 (@lem3558485 A s x' h1)). Qed.
Lemma lem3558497 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term156 A x s x') : term55.
Proof. exact (fun h0 : ~ False => @lem3558496 A x s x' h1 h2). Qed.
Lemma lem3558499 (p : Prop) : (term44 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3558500 : term55 = False.
Proof. exact (@lem3558499 False). Qed.
Lemma lem3558501 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term156 A x s x') : False.
Proof. exact (EQ_MP (@lem3558500) (@lem3558497 A x s x' h1 h2)). Qed.
Lemma lem3558517 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term152 A x s x') : s x'.
Proof. exact (proj2 (@lem3558346 A x s x' h1)). Qed.
Lemma lem3558518 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term152 A x s x') : term162 A s x'.
Proof. exact (fun h0 : term157 A s x' => @lem3558517 A x s x' h1). Qed.
Lemma lem3558520 (p : Prop) : (term44 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3558521 {A : Type'} (s : A -> Prop) (x' : A) : (term162 A s x') = (s x').
Proof. exact (@lem3558520 (s x')). Qed.
Lemma lem3558522 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term152 A x s x') : s x'.
Proof. exact (EQ_MP (@lem3558521 A s x') (@lem3558518 A x s x' h1)). Qed.
Lemma lem3558525 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3558527 {A : Type'} (s : A -> Prop) (x' : A) : (term157 A s x') = (term163 A s x').
Proof. exact (@lem3558525 (s x')). Qed.
Lemma lem3558530 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term152 A x s x') : term163 A s x'.
Proof. exact (EQ_MP (@lem3558527 A s x') (@lem3558414 A x s x' h1)). Qed.
Lemma lem3558533 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term152 A x s x') : False.
Proof. exact (@lem3558530 A x s x' h1 (@lem3558522 A x s x' h1)). Qed.
Lemma lem3558534 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term152 A x s x') : term55.
Proof. exact (fun h0 : ~ False => @lem3558533 A x s x' h1). Qed.
Lemma lem3558536 (p : Prop) : (term44 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3558537 : term55 = False.
Proof. exact (@lem3558536 False). Qed.
Lemma lem3558538 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term152 A x s x') : False.
Proof. exact (EQ_MP (@lem3558537) (@lem3558534 A x s x' h1)). Qed.
Lemma lem3558539 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term156 A x s x') (h3 : x' = x) : (s x) = False.
Proof. exact (prop_ext (fun h4 : s x => @lem3558478 A s x' x h1 h2 h3) (fun h4 : False => @lem3558442 A s x h1)). Qed.
Lemma lem3558541 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term156 A x s x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3558539 A s x' x h1 h2 h3) (@lem3558442 A s x h1)). Qed.
Lemma lem3558542 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term156 A x s x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3558501 A x s x' h1 h2) (fun h3 : False => @lem3558406 A s x' h1)). Qed.
Lemma lem3558543 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term156 A x s x') : False.
Proof. exact (EQ_MP (@lem3558542 A x s x' h1 h2) (@lem3558406 A s x' h1)). Qed.
Lemma lem3558544 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term156 A x s x') (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3558541 A s x' x h1 h2 h3) (fun h4 : False => @lem3558400 A x' x h3)). Qed.
Lemma lem3558545 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term156 A x s x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3558544 A s x' x h1 h2 h3) (@lem3558400 A x' x h3)). Qed.
Lemma lem3558546 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term156 A x s x') (h3 : x' = x) : (s x) = False.
Proof. exact (prop_ext (fun h4 : s x => @lem3558545 A s x' x h1 h2 h3) (fun h4 : False => @lem3558396 A s x h1)). Qed.
Lemma lem3558547 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term156 A x s x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3558546 A s x' x h1 h2 h3) (@lem3558396 A s x h1)). Qed.
Lemma lem3558548 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term156 A x s x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3558543 A x s x' h1 h2) (fun h3 : False => @lem3558378 A s x' h1)). Qed.
Lemma lem3558549 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term156 A x s x') : False.
Proof. exact (EQ_MP (@lem3558548 A x s x' h1 h2) (@lem3558378 A s x' h1)). Qed.
Lemma lem3558550 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term156 A x s x') (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3558547 A s x' x h1 h2 h3) (fun h4 : False => @lem3558366 A x' x h3)). Qed.
Lemma lem3558551 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term156 A x s x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3558550 A s x' x h1 h2 h3) (@lem3558366 A x' x h3)). Qed.
Lemma lem3558552 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term156 A x s x') (h3 : x' = x) : (s x) = False.
Proof. exact (prop_ext (fun h4 : s x => @lem3558551 A s x' x h1 h2 h3) (fun h4 : False => @lem3558358 A s x h1)). Qed.
Lemma lem3558553 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term156 A x s x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3558552 A s x' x h1 h2 h3) (@lem3558358 A s x h1)). Qed.
Lemma lem3558554 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term156 A x s x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3558549 A x s x' h1 h2) (fun h3 : False => @lem3558378 A s x' h1)). Qed.
Lemma lem3558555 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term156 A x s x') : False.
Proof. exact (EQ_MP (@lem3558554 A x s x' h1 h2) (@lem3558378 A s x' h1)). Qed.
Lemma lem3558556 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term156 A x s x') (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3558553 A s x' x h1 h2 h3) (fun h4 : False => @lem3558366 A x' x h3)). Qed.
Lemma lem3558557 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term156 A x s x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3558556 A s x' x h1 h2 h3) (@lem3558366 A x' x h3)). Qed.
Lemma lem3558558 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term156 A x s x') (h3 : x' = x) : (s x) = False.
Proof. exact (prop_ext (fun h4 : s x => @lem3558557 A s x' x h1 h2 h3) (fun h4 : False => @lem3558358 A s x h1)). Qed.
Lemma lem3558559 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term156 A x s x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3558558 A s x' x h1 h2 h3) (@lem3558358 A s x h1)). Qed.
Lemma lem3558560 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x) (h2 : term156 A x s x') : False.
Proof. exact (or_elim (@lem3558348 A x s x' h2) (fun h0 : x' = x => @lem3558559 A s x' x h1 h2 h0) (fun h0 : s x' => @lem3558555 A x s x' h0 h2)). Qed.
Lemma lem3558561 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : term146 A x s x') (h2 : s x) : False.
Proof. exact (or_elim (@lem3558344 A x s x' h1) (fun h0 : term156 A x s x' => @lem3558560 A x s x' h2 h0) (fun h0 : term152 A x s x' => @lem3558538 A x s x' h0)). Qed.
Lemma lem3558562 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : term146 A x s x') (h2 : s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3558561 A x' s x h1 h2) (fun h3 : False => @lem3558300 A s x h2)). Qed.
Lemma lem3558563 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : term146 A x s x') (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3558562 A x' s x h1 h2) (@lem3558300 A s x h2)). Qed.
Lemma lem3558564 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : term146 A x s x') (h2 : s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3558563 A x' s x h1 h2) (fun h3 : False => @lem3558266 A s x h2)). Qed.
Lemma lem3558565 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : term146 A x s x') (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3558564 A x' s x h1 h2) (@lem3558266 A s x h2)). Qed.
Lemma lem3558566 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : term146 A x s x') (h2 : s x) : (term146 A x s x') = False.
Proof. exact (prop_ext (fun h3 : term146 A x s x' => @lem3558565 A x' s x h1 h2) (fun h3 : False => @lem3558260 A x s x' h1)). Qed.
Lemma lem3558567 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : term146 A x s x') (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3558566 A x' s x h1 h2) (@lem3558260 A x s x' h1)). Qed.
Lemma lem3558568 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : s x) : term145 A x s x'.
Proof. exact (fun h0 : term146 A x s x' => @lem3558567 A x' s x h0 h1). Qed.
Lemma lem3558569 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : s x) : (term124 A x s x') = (s x').
Proof. exact (EQ_MP (@lem3558259 A x s x') (@lem3558568 A x' s x h1)). Qed.
Lemma lem3558574 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : term129 A x s.
Proof. exact (fun x' : A => @lem3558569 A x' s x h1). Qed.
Lemma lem3558575 {A : Type'} (x : A) (s : A -> Prop) : term130 A x s.
Proof. exact (fun h0 : s x => @lem3558574 A s x h0). Qed.
Lemma lem3558580 {A : Type'} (s : A -> Prop) : term140 A s.
Proof. exact (fun x : A => @lem3558575 A x s). Qed.
Lemma lem3558585 {A : Type'} : term144 A.
Proof. exact (fun s : A -> Prop => @lem3558580 A s). Qed.
Lemma lem3558586 {A : Type'} : term143 A.
Proof. exact (EQ_MP (@lem3558254 A) (@lem3558585 A)). Qed.
Lemma lem3558587 {A : Type'} (s : A -> Prop) : term164 A s.
Proof. exact (@lem3558586 A s). Qed.
Lemma lem3558588 {A : Type'} (s : A -> Prop) : (term164 A s) = (term139 A s).
Proof. exact (eq_refl (term164 A s)). Qed.
Lemma lem3558589 {A : Type'} (s : A -> Prop) : term139 A s.
Proof. exact (EQ_MP (@lem3558588 A s) (@lem3558587 A s)). Qed.
Lemma lem3558590 {A : Type'} (s : A -> Prop) (x : A) : term165 A s x.
Proof. exact (@lem3558589 A s x). Qed.
Lemma lem3558591 {A : Type'} (x : A) (s : A -> Prop) : (term165 A s x) = (term131 A x s).
Proof. exact (eq_refl (term165 A s x)). Qed.
Lemma lem3558592 {A : Type'} (x : A) (s : A -> Prop) : term131 A x s.
Proof. exact (EQ_MP (@lem3558591 A x s) (@lem3558590 A s x)). Qed.
Lemma lem3558594 {A : Type'} (x : A) (s : A -> Prop) : term131 A x s.
Proof. exact (@lem3558165 A x s (@lem3558592 A x s)). Qed.
Lemma lem3558595 {A : Type'} (x : A) (s : A -> Prop) (h1 : term132 A x s) : False.
Proof. exact (@lem3558594 A x s (@lem3558149 A x s h1)). Qed.
Lemma lem3558596 {A : Type'} (x : A) (s : A -> Prop) (h1 : term132 A x s) : (term132 A x s) = False.
Proof. exact (prop_ext (fun h2 : term132 A x s => @lem3558595 A x s h1) (fun h2 : False => @lem3558149 A x s h1)). Qed.
Lemma lem3558597 {A : Type'} (x : A) (s : A -> Prop) (h1 : term132 A x s) : False.
Proof. exact (EQ_MP (@lem3558596 A x s h1) (@lem3558149 A x s h1)). Qed.
Lemma lem3558598 {A : Type'} (x : A) (s : A -> Prop) : term131 A x s.
Proof. exact (fun h0 : term132 A x s => @lem3558597 A x s h0). Qed.
Lemma lem3558599 {A : Type'} (x : A) (s : A -> Prop) : term130 A x s.
Proof. exact (EQ_MP (@lem3558148 A x s) (@lem3558598 A x s)). Qed.
Lemma lem3558600 {A : Type'} (x : A) (s : A -> Prop) : term119 A x s.
Proof. exact (EQ_MP (@lem3558144 A x s) (@lem3558599 A x s)). Qed.
Lemma lem3558601 {A : Type'} (x : A) (s : A -> Prop) : term118 A x s.
Proof. exact (EQ_MP (@lem3558093 A x s) (@lem3558600 A x s)). Qed.
Lemma lem3558602 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : (@INSERT A x s) = s.
Proof. exact (@lem3558601 A x s (@lem3556977 A x s h1)). Qed.
Lemma lem3558603 {A : Type'} (P : type686 A) (x : A) (s : A -> Prop) (h1 : P s) (h2 : @IN A x s) : ((@INSERT A x s) = s) = (term105 A P x s).
Proof. exact (prop_ext (fun h3 : (@INSERT A x s) = s => @lem3558072 A P x s h1 h3) (fun h3 : term105 A P x s => @lem3558602 A x s h2)). Qed.
Lemma lem3558604 {A : Type'} (P : type686 A) (x : A) (s : A -> Prop) (h1 : P s) (h2 : @IN A x s) : term105 A P x s.
Proof. exact (EQ_MP (@lem3558603 A P x s h1 h2) (@lem3558602 A x s h2)). Qed.
Lemma lem3558605 {A : Type'} (P : type686 A) (h1 : term11 A P) : term11 A P.
Proof. exact (h1). Qed.
Lemma lem3558606 {A : Type'} (x : A) (P : type686 A) (h1 : term11 A P) : term166 A P x.
Proof. exact (@lem3558605 A P h1 x). Qed.
Lemma lem3558607 {A : Type'} (P : type686 A) (x : A) : (term166 A P x) = (term167 A P x).
Proof. exact (eq_refl (term166 A P x)). Qed.
Lemma lem3558608 {A : Type'} (x : A) (P : type686 A) (h1 : term11 A P) : term167 A P x.
Proof. exact (EQ_MP (@lem3558607 A P x) (@lem3558606 A x P h1)). Qed.
Lemma lem3558609 {A : Type'} (x : A) (s : A -> Prop) (P : type686 A) (h1 : term11 A P) : term168 A P x s.
Proof. exact (@lem3558608 A x P h1 s). Qed.
Lemma lem3558610 {A : Type'} (P : type686 A) (x : A) (s : A -> Prop) : (term168 A P x s) = (term169 A P x s).
Proof. exact (eq_refl (term168 A P x s)). Qed.
Lemma lem3558611 {A : Type'} (x : A) (s : A -> Prop) (P : type686 A) (h1 : term11 A P) : term169 A P x s.
Proof. exact (EQ_MP (@lem3558610 A P x s) (@lem3558609 A x s P h1)). Qed.
Lemma lem3558612 {A : Type'} (P : type686 A) (x : A) (s : A -> Prop) (h1 : term170 A P x s) : term170 A P x s.
Proof. exact (h1). Qed.
Lemma lem3558613 {A : Type'} (P : type686 A) (x : A) (s : A -> Prop) (h1 : term11 A P) (h2 : term170 A P x s) : term105 A P x s.
Proof. exact (@lem3558611 A x s P h1 (@lem3558612 A P x s h2)). Qed.
Lemma lem3558614 {A : Type'} (P : type686 A) (x : A) (s : A -> Prop) (h1 : term170 A P x s) : term171 A P x s.
Proof. exact (fun h0 : term11 A P => @lem3558613 A P x s h0 h1). Qed.
Lemma lem3558615 {A : Type'} (P : type686 A) (h1 : term11 A P) : term11 A P.
Proof. exact (h1). Qed.
Lemma lem3558616 {A : Type'} (P : type686 A) (x : A) (s : A -> Prop) (h1 : term11 A P) (h2 : term170 A P x s) : term105 A P x s.
Proof. exact (@lem3558614 A P x s h2 (@lem3558615 A P h1)). Qed.
Lemma lem3558617 {A : Type'} (x : A) (s : A -> Prop) (P : type686 A) (h1 : term11 A P) : term169 A P x s.
Proof. exact (fun h0 : term170 A P x s => @lem3558616 A P x s h1 h0). Qed.
Lemma lem3558618 {A : Type'} (x : A) (P : type686 A) (h1 : term11 A P) : term167 A P x.
Proof. exact (fun s : A -> Prop => @lem3558617 A x s P h1). Qed.
Lemma lem3558619 {A : Type'} (P : type686 A) (h1 : term11 A P) : term11 A P.
Proof. exact (fun x : A => @lem3558618 A x P h1). Qed.
Lemma lem3558620 {A : Type'} (P : type686 A) : term172 A P.
Proof. exact (fun h0 : term11 A P => @lem3558619 A P h0). Qed.
Lemma lem3558621 {A : Type'} (P : type686 A) (h1 : term11 A P) : term11 A P.
Proof. exact (@lem3558620 A P (@lem3557006 A P h1)). Qed.
Lemma lem3558622 {A : Type'} (x : A) (P : type686 A) (h1 : term11 A P) : term166 A P x.
Proof. exact (@lem3558621 A P h1 x). Qed.
Lemma lem3558623 {A : Type'} (P : type686 A) (x : A) : (term166 A P x) = (term167 A P x).
Proof. exact (eq_refl (term166 A P x)). Qed.
Lemma lem3558624 {A : Type'} (x : A) (P : type686 A) (h1 : term11 A P) : term167 A P x.
Proof. exact (EQ_MP (@lem3558623 A P x) (@lem3558622 A x P h1)). Qed.
Lemma lem3558625 {A : Type'} (x : A) (s : A -> Prop) (P : type686 A) (h1 : term11 A P) : term168 A P x s.
Proof. exact (@lem3558624 A x P h1 s). Qed.
Lemma lem3558626 {A : Type'} (P : type686 A) (x : A) (s : A -> Prop) : (term168 A P x s) = (term169 A P x s).
Proof. exact (eq_refl (term168 A P x s)). Qed.
Lemma lem3558629 {A : Type'} (x : A) (s : A -> Prop) (P : type686 A) (h1 : term11 A P) : term169 A P x s.
Proof. exact (EQ_MP (@lem3558626 A P x s) (@lem3558625 A x s P h1)). Qed.
Lemma lem3558630 {A : Type'} (x : A) (s : A -> Prop) (P : type686 A) (h1 : term11 A P) : term169 A P x s.
Proof. exact (@lem3558629 A x s P h1). Qed.
Lemma lem3558641 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem3558643 {A : Type'} (P : type686 A) (s : A -> Prop) : (P s) = ((P s) = True).
Proof. exact (@lem7 (P s)). Qed.
Lemma lem3558645 {A : Type'} (x : A) (s : A -> Prop) : term173 A x s.
Proof. exact (@lem82 (@IN A x s)). Qed.
Lemma lem3558650 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : P s) : (P s) = True.
Proof. exact (EQ_MP (@lem3558643 A P s) (@lem3558029 A P s h1)). Qed.
Lemma lem3558651 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3558652 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : P s) : (term174 A P s) = (and True).
Proof. exact (MK_COMB (@lem3558651) (@lem3558650 A P s h1)). Qed.
Lemma lem3558656 {A : Type'} (x : A) (s : A -> Prop) (h1 : term2 A x s) : (@IN A x s) = False.
Proof. exact (@lem3558645 A x s (@lem3556978 A x s h1)). Qed.
Lemma lem3558657 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3558658 {A : Type'} (x : A) (s : A -> Prop) (h1 : term2 A x s) : (term2 A x s) = (~ False).
Proof. exact (MK_COMB (@lem3558657) (@lem3558656 A x s h1)). Qed.
Lemma lem3558660 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem3558661 {A : Type'} (x : A) (s : A -> Prop) (h1 : term2 A x s) : (term2 A x s) = True.
Proof. exact (TRANS (@lem3558658 A x s h1) (@lem3558660)). Qed.
Lemma lem3558662 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3558663 {A : Type'} (x : A) (s : A -> Prop) (h1 : term2 A x s) : (term175 A x s) = (and True).
Proof. exact (MK_COMB (@lem3558662) (@lem3558661 A x s h1)). Qed.
Lemma lem3558665 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem3558641 A s) (@lem3558030 A s h1)). Qed.
Lemma lem3558666 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term2 A x s) : (term176 A x s) = (True /\ True).
Proof. exact (MK_COMB (@lem3558663 A x s h2) (@lem3558665 A s h1)). Qed.
Lemma lem3558668 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3558669 : (True /\ True) = True.
Proof. exact (@lem3558668 True). Qed.
Lemma lem3558670 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term2 A x s) : (term176 A x s) = True.
Proof. exact (TRANS (@lem3558666 A x s h1 h2) (@lem3558669)). Qed.
Lemma lem3558671 {A : Type'} (x : A) (P : type686 A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term2 A x s) (h3 : P s) : (term170 A P x s) = (True /\ True).
Proof. exact (MK_COMB (@lem3558652 A P s h3) (@lem3558670 A x s h1 h2)). Qed.
Lemma lem3558673 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3558674 : (True /\ True) = True.
Proof. exact (@lem3558673 True). Qed.
Lemma lem3558675 {A : Type'} (x : A) (P : type686 A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term2 A x s) (h3 : P s) : (term170 A P x s) = True.
Proof. exact (TRANS (@lem3558671 A x P s h1 h2 h3) (@lem3558674)). Qed.
Lemma lem3558676 {A : Type'} (x : A) (P : type686 A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term2 A x s) (h3 : P s) : True = (term170 A P x s).
Proof. exact (SYM (@lem3558675 A x P s h1 h2 h3)). Qed.
Lemma lem3558677 {A : Type'} (x : A) (P : type686 A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term2 A x s) (h3 : P s) : term170 A P x s.
Proof. exact (EQ_MP (@lem3558676 A x P s h1 h2 h3) (@lem0)). Qed.
Lemma lem3558678 {A : Type'} (x : A) (P : type686 A) (s : A -> Prop) (h1 : term11 A P) (h2 : @FINITE A s) (h3 : term2 A x s) (h4 : P s) : term105 A P x s.
Proof. exact (@lem3558630 A x s P h1 (@lem3558677 A x P s h2 h3 h4)). Qed.
Lemma lem3558680 {A : Type'} (x : A) (P : type686 A) (s : A -> Prop) (h1 : term11 A P) (h2 : @FINITE A s) (h3 : P s) : term105 A P x s.
Proof. exact (or_elim (@lem3556976 A x s) (fun h0 : @IN A x s => @lem3558604 A P x s h3 h0) (fun h0 : term2 A x s => @lem3558678 A x P s h1 h2 h0 h3)). Qed.
Lemma lem3558681 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term34 A P s) : P s.
Proof. exact (proj2 (@lem3558028 A P s h1)). Qed.
Lemma lem3558682 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term34 A P s) : @FINITE A s.
Proof. exact (proj1 (@lem3558028 A P s h1)). Qed.
Lemma lem3558683 {A : Type'} (x : A) (P : type686 A) (s : A -> Prop) (h1 : term11 A P) (h2 : @FINITE A s) (h3 : P s) : (P s) = (term105 A P x s).
Proof. exact (prop_ext (fun h4 : P s => @lem3558680 A x P s h1 h2 h3) (fun h4 : term105 A P x s => @lem3558029 A P s h3)). Qed.
Lemma lem3558684 {A : Type'} (x : A) (P : type686 A) (s : A -> Prop) (h1 : term11 A P) (h2 : @FINITE A s) (h3 : P s) : term105 A P x s.
Proof. exact (EQ_MP (@lem3558683 A x P s h1 h2 h3) (@lem3558029 A P s h3)). Qed.
Lemma lem3558685 {A : Type'} (x : A) (P : type686 A) (s : A -> Prop) (h1 : term11 A P) (h2 : @FINITE A s) (h3 : P s) : (@FINITE A s) = (term105 A P x s).
Proof. exact (prop_ext (fun h4 : @FINITE A s => @lem3558684 A x P s h1 h2 h3) (fun h4 : term105 A P x s => @lem3558030 A s h2)). Qed.
Lemma lem3558686 {A : Type'} (x : A) (P : type686 A) (s : A -> Prop) (h1 : term11 A P) (h2 : @FINITE A s) (h3 : P s) : term105 A P x s.
Proof. exact (EQ_MP (@lem3558685 A x P s h1 h2 h3) (@lem3558030 A s h2)). Qed.
Lemma lem3558687 {A : Type'} (x : A) (P : type686 A) (s : A -> Prop) (h1 : term11 A P) (h2 : @FINITE A s) (h3 : term34 A P s) : (P s) = (term105 A P x s).
Proof. exact (prop_ext (fun h4 : P s => @lem3558686 A x P s h1 h2 h4) (fun h4 : term105 A P x s => @lem3558681 A P s h3)). Qed.
Lemma lem3558688 {A : Type'} (x : A) (P : type686 A) (s : A -> Prop) (h1 : term11 A P) (h2 : @FINITE A s) (h3 : term34 A P s) : term105 A P x s.
Proof. exact (EQ_MP (@lem3558687 A x P s h1 h2 h3) (@lem3558681 A P s h3)). Qed.
Lemma lem3558689 {A : Type'} (x : A) (P : type686 A) (s : A -> Prop) (h1 : term11 A P) (h2 : term34 A P s) : (@FINITE A s) = (term105 A P x s).
Proof. exact (prop_ext (fun h3 : @FINITE A s => @lem3558688 A x P s h1 h3 h2) (fun h3 : term105 A P x s => @lem3558682 A P s h2)). Qed.
Lemma lem3558690 {A : Type'} (x : A) (P : type686 A) (s : A -> Prop) (h1 : term11 A P) (h2 : term34 A P s) : term105 A P x s.
Proof. exact (EQ_MP (@lem3558689 A x P s h1 h2) (@lem3558682 A P s h2)). Qed.
Lemma lem3558691 {A : Type'} (x : A) (s : A -> Prop) (P : type686 A) (h1 : term11 A P) : term109 A P x s.
Proof. exact (fun h0 : term34 A P s => @lem3558690 A x P s h1 h0). Qed.
Lemma lem3558696 {A : Type'} (x : A) (P : type686 A) (h1 : term11 A P) : term111 A P x.
Proof. exact (fun s : A -> Prop => @lem3558691 A x s P h1). Qed.
Lemma lem3558701 {A : Type'} (P : type686 A) (h1 : term11 A P) : term113 A P.
Proof. exact (fun x : A => @lem3558696 A x P h1). Qed.
Lemma lem3558702 {A : Type'} (P : type686 A) (h1 : term11 A P) (h2 : P (@EMPTY A)) : term79 A P.
Proof. exact (EQ_MP (@lem3558027 A P h2) (@lem3558701 A P h1)). Qed.
Lemma lem3558703 {A : Type'} (P : type686 A) (h1 : term11 A P) (h2 : P (@EMPTY A)) : term12 A P.
Proof. exact (@lem3557444 A P (@lem3558702 A P h1 h2)). Qed.
Lemma lem3558704 {A : Type'} (P : type686 A) (h1 : term12 A P) : term7 A P.
Proof. exact (@lem3557415 A P (@lem3557008 A P h1)). Qed.
Lemma lem3558705 {A : Type'} (P : type686 A) (h1 : term11 A P) (h2 : P (@EMPTY A)) : (term12 A P) = (term7 A P).
Proof. exact (prop_ext (fun h3 : term12 A P => @lem3558704 A P h3) (fun h3 : term7 A P => @lem3558703 A P h1 h2)). Qed.
Lemma lem3558706 {A : Type'} (P : type686 A) (h1 : term11 A P) (h2 : P (@EMPTY A)) : term7 A P.
Proof. exact (EQ_MP (@lem3558705 A P h1 h2) (@lem3558703 A P h1 h2)). Qed.
Lemma lem3558707 {A : Type'} (P : type686 A) (h1 : term10 A P) : term11 A P.
Proof. exact (proj2 (@lem3557005 A P h1)). Qed.
Lemma lem3558708 {A : Type'} (P : type686 A) (h1 : term10 A P) : P (@EMPTY A).
Proof. exact (proj1 (@lem3557005 A P h1)). Qed.
Lemma lem3558709 {A : Type'} (P : type686 A) (h1 : term11 A P) (h2 : P (@EMPTY A)) : (term11 A P) = (term7 A P).
Proof. exact (prop_ext (fun h3 : term11 A P => @lem3558706 A P h1 h2) (fun h3 : term7 A P => @lem3557006 A P h1)). Qed.
Lemma lem3558710 {A : Type'} (P : type686 A) (h1 : term11 A P) (h2 : P (@EMPTY A)) : term7 A P.
Proof. exact (EQ_MP (@lem3558709 A P h1 h2) (@lem3557006 A P h1)). Qed.
Lemma lem3558711 {A : Type'} (P : type686 A) (h1 : term11 A P) (h2 : P (@EMPTY A)) : (P (@EMPTY A)) = (term7 A P).
Proof. exact (prop_ext (fun h3 : P (@EMPTY A) => @lem3558710 A P h1 h2) (fun h3 : term7 A P => @lem3557007 A P h2)). Qed.
Lemma lem3558712 {A : Type'} (P : type686 A) (h1 : term11 A P) (h2 : P (@EMPTY A)) : term7 A P.
Proof. exact (EQ_MP (@lem3558711 A P h1 h2) (@lem3557007 A P h2)). Qed.
Lemma lem3558713 {A : Type'} (P : type686 A) (h1 : P (@EMPTY A)) (h2 : term10 A P) : (term11 A P) = (term7 A P).
Proof. exact (prop_ext (fun h3 : term11 A P => @lem3558712 A P h3 h1) (fun h3 : term7 A P => @lem3558707 A P h2)). Qed.
Lemma lem3558714 {A : Type'} (P : type686 A) (h1 : P (@EMPTY A)) (h2 : term10 A P) : term7 A P.
Proof. exact (EQ_MP (@lem3558713 A P h1 h2) (@lem3558707 A P h2)). Qed.
Lemma lem3558715 {A : Type'} (P : type686 A) (h1 : term10 A P) : (P (@EMPTY A)) = (term7 A P).
Proof. exact (prop_ext (fun h2 : P (@EMPTY A) => @lem3558714 A P h2 h1) (fun h2 : term7 A P => @lem3558708 A P h1)). Qed.
Lemma lem3558716 {A : Type'} (P : type686 A) (h1 : term10 A P) : term7 A P.
Proof. exact (EQ_MP (@lem3558715 A P h1) (@lem3558708 A P h1)). Qed.
Lemma lem3558717 {A : Type'} (P : type686 A) : term177 A P.
Proof. exact (fun h0 : term10 A P => @lem3558716 A P h0). Qed.
Lemma lem3558722 {A : Type'} : term178 A.
Proof. exact (fun P : type686 A => @lem3558717 A P). Qed.
