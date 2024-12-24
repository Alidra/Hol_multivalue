Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INTER_SUBSET_term_abbrevs.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211710_spec.
Require Import thm3211711_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Lemma lem3255923 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3255924 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (@lem3255923 A s t). Qed.
Lemma lem3255925 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term1 A t s) = (term2 A t s).
Proof. exact (@lem3255924 A (@INTER A s t) s). Qed.
Lemma lem3255932 {A : Type'} (s : A -> Prop) : (term3 A s) = (term4 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3255925 A t s)). Qed.
Lemma lem3255933 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3255934 {A : Type'} (s : A -> Prop) : (term5 A s) = (term6 A s).
Proof. exact (MK_COMB (@lem3255933 A) (@lem3255932 A s)). Qed.
Lemma lem3255939 {A : Type'} : (term7 A) = (term8 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3255934 A s)). Qed.
Lemma lem3255940 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3255941 {A : Type'} : (term9 A) = (term10 A).
Proof. exact (MK_COMB (@lem3255940 A) (@lem3255939 A)). Qed.
Lemma lem3255946 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3255947 {A : Type'} : (term11 A) = (term12 A).
Proof. exact (MK_COMB (@lem3255946) (@lem3255941 A)). Qed.
Lemma lem3255957 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3255958 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (@lem3255957 A s t). Qed.
Lemma lem3255959 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term13 A t s) = (term14 A t s).
Proof. exact (@lem3255958 A (@INTER A t s) s). Qed.
Lemma lem3255966 {A : Type'} (s : A -> Prop) : (term15 A s) = (term16 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3255959 A t s)). Qed.
Lemma lem3255967 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3255968 {A : Type'} (s : A -> Prop) : (term17 A s) = (term18 A s).
Proof. exact (MK_COMB (@lem3255967 A) (@lem3255966 A s)). Qed.
Lemma lem3255973 {A : Type'} : (term19 A) = (term20 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3255968 A s)). Qed.
Lemma lem3255974 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3255975 {A : Type'} : (term21 A) = (term22 A).
Proof. exact (MK_COMB (@lem3255974 A) (@lem3255973 A)). Qed.
Lemma lem3255980 {A : Type'} : (term23 A) = (term24 A).
Proof. exact (MK_COMB (@lem3255947 A) (@lem3255975 A)). Qed.
Lemma lem3255983 {A : Type'} : (term24 A) = (term23 A).
Proof. exact (SYM (@lem3255980 A)). Qed.
Lemma lem3256001 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term25 A x s t) = (term26 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3256002 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term25 A x s t) = (term26 A s x t).
Proof. exact (@lem3256001 A s x t). Qed.
Lemma lem3256006 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3256007 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3256006 A P x). Qed.
Lemma lem3256008 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3256007 A s x). Qed.
Lemma lem3256009 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3256010 {A : Type'} (s : A -> Prop) (x : A) : (term27 A x s) = (term28 A s x).
Proof. exact (MK_COMB (@lem3256009) (@lem3256008 A s x)). Qed.
Lemma lem3256012 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3256013 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3256012 A P x). Qed.
Lemma lem3256014 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3256013 A t x). Qed.
Lemma lem3256015 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term26 A s x t) = (term29 A s t x).
Proof. exact (MK_COMB (@lem3256010 A s x) (@lem3256014 A t x)). Qed.
Lemma lem3256018 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term25 A x s t) = (term29 A s t x).
Proof. exact (TRANS (@lem3256002 A s x t) (@lem3256015 A s t x)). Qed.
Lemma lem3256019 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3256020 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term30 A x s t) = (term31 A s t x).
Proof. exact (MK_COMB (@lem3256019) (@lem3256018 A s t x)). Qed.
Lemma lem3256022 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3256023 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3256022 A P x). Qed.
Lemma lem3256024 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3256023 A s x). Qed.
Lemma lem3256025 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term32 A t x s) = (term33 A t s x).
Proof. exact (MK_COMB (@lem3256020 A s t x) (@lem3256024 A s x)). Qed.
Lemma lem3256028 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term34 A t s) = (term35 A t s).
Proof. exact (fun_ext (fun x : A => @lem3256025 A t s x)). Qed.
Lemma lem3256029 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3256030 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term2 A t s) = (term36 A t s).
Proof. exact (MK_COMB (@lem3256029 A) (@lem3256028 A t s)). Qed.
Lemma lem3256035 {A : Type'} (s : A -> Prop) : (term4 A s) = (term37 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3256030 A t s)). Qed.
Lemma lem3256036 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3256037 {A : Type'} (s : A -> Prop) : (term6 A s) = (term38 A s).
Proof. exact (MK_COMB (@lem3256036 A) (@lem3256035 A s)). Qed.
Lemma lem3256042 {A : Type'} : (term8 A) = (term39 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3256037 A s)). Qed.
Lemma lem3256043 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3256044 {A : Type'} : (term10 A) = (term40 A).
Proof. exact (MK_COMB (@lem3256043 A) (@lem3256042 A)). Qed.
Lemma lem3256049 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3256050 {A : Type'} : (term12 A) = (term41 A).
Proof. exact (MK_COMB (@lem3256049) (@lem3256044 A)). Qed.
Lemma lem3256066 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term25 A x s t) = (term26 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3256067 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term25 A x s t) = (term26 A s x t).
Proof. exact (@lem3256066 A s x t). Qed.
Lemma lem3256068 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : (term25 A x t s) = (term26 A t x s).
Proof. exact (@lem3256067 A t x s). Qed.
Lemma lem3256072 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3256073 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3256072 A P x). Qed.
Lemma lem3256074 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3256073 A t x). Qed.
Lemma lem3256075 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3256076 {A : Type'} (t : A -> Prop) (x : A) : (term27 A x t) = (term28 A t x).
Proof. exact (MK_COMB (@lem3256075) (@lem3256074 A t x)). Qed.
Lemma lem3256078 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3256079 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3256078 A P x). Qed.
Lemma lem3256080 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3256079 A s x). Qed.
Lemma lem3256081 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term26 A t x s) = (term29 A t s x).
Proof. exact (MK_COMB (@lem3256076 A t x) (@lem3256080 A s x)). Qed.
Lemma lem3256084 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term25 A x t s) = (term29 A t s x).
Proof. exact (TRANS (@lem3256068 A t x s) (@lem3256081 A t s x)). Qed.
Lemma lem3256085 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3256086 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term30 A x t s) = (term31 A t s x).
Proof. exact (MK_COMB (@lem3256085) (@lem3256084 A t s x)). Qed.
Lemma lem3256088 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3256089 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3256088 A P x). Qed.
Lemma lem3256090 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3256089 A s x). Qed.
Lemma lem3256091 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term42 A t x s) = (term43 A t s x).
Proof. exact (MK_COMB (@lem3256086 A t s x) (@lem3256090 A s x)). Qed.
Lemma lem3256094 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term44 A t s) = (term45 A t s).
Proof. exact (fun_ext (fun x : A => @lem3256091 A t s x)). Qed.
Lemma lem3256095 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3256096 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term14 A t s) = (term46 A t s).
Proof. exact (MK_COMB (@lem3256095 A) (@lem3256094 A t s)). Qed.
Lemma lem3256101 {A : Type'} (s : A -> Prop) : (term16 A s) = (term47 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3256096 A t s)). Qed.
Lemma lem3256102 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3256103 {A : Type'} (s : A -> Prop) : (term18 A s) = (term48 A s).
Proof. exact (MK_COMB (@lem3256102 A) (@lem3256101 A s)). Qed.
Lemma lem3256108 {A : Type'} : (term20 A) = (term49 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3256103 A s)). Qed.
Lemma lem3256109 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3256110 {A : Type'} : (term22 A) = (term50 A).
Proof. exact (MK_COMB (@lem3256109 A) (@lem3256108 A)). Qed.
Lemma lem3256115 {A : Type'} : (term24 A) = (term51 A).
Proof. exact (MK_COMB (@lem3256050 A) (@lem3256110 A)). Qed.
Lemma lem3256118 {A : Type'} : (term51 A) = (term24 A).
Proof. exact (SYM (@lem3256115 A)). Qed.
Lemma lem3256120 (p : Prop) : p = (term52 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3256121 {A : Type'} : (term51 A) = (term53 A).
Proof. exact (@lem3256120 (term51 A)). Qed.
Lemma lem3256122 {A : Type'} : (term53 A) = (term51 A).
Proof. exact (SYM (@lem3256121 A)). Qed.
Lemma lem3256123 {A : Type'} (h1 : term54 A) : term54 A.
Proof. exact (h1). Qed.
Lemma lem3256126 {A : Type'} (h1 : term53 A) : term53 A.
Proof. exact (h1). Qed.
Lemma lem3256127 {A : Type'} : term55 A.
Proof. exact (fun h0 : term53 A => @lem3256126 A h0). Qed.
Lemma lem3256128 {A : Type'} (h1 : term55 A) : term55 A.
Proof. exact (h1). Qed.
Lemma lem3256129 {A : Type'} (h1 : term53 A) : term53 A.
Proof. exact (h1). Qed.
Lemma lem3256130 {A : Type'} (h1 : term53 A) (h2 : term55 A) : term53 A.
Proof. exact (@lem3256128 A h2 (@lem3256129 A h1)). Qed.
Lemma lem3256131 {A : Type'} (h1 : term53 A) : term56 A.
Proof. exact (fun h0 : term55 A => @lem3256130 A h1 h0). Qed.
Lemma lem3256132 {A : Type'} (h1 : term55 A) : term55 A.
Proof. exact (h1). Qed.
Lemma lem3256133 {A : Type'} (h1 : term53 A) (h2 : term55 A) : term53 A.
Proof. exact (@lem3256131 A h1 (@lem3256132 A h2)). Qed.
Lemma lem3256134 {A : Type'} (h1 : term55 A) : term55 A.
Proof. exact (fun h0 : term53 A => @lem3256133 A h0 h1). Qed.
Lemma lem3256135 {A : Type'} : term57 A.
Proof. exact (fun h0 : term55 A => @lem3256134 A h0). Qed.
Lemma lem3256138 {A : Type'} : term55 A.
Proof. exact (@lem3256135 A (@lem3256127 A)). Qed.
Lemma lem3256139 {A : Type'} : term55 A.
Proof. exact (@lem3256138 A). Qed.
Lemma lem3256141 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3256142 {A : Type'} : (term53 A) = (term58 A).
Proof. exact (@lem3256141 (term54 A)). Qed.
Lemma lem3256144 (t : Prop) : (term59 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3256145 {A : Type'} : (term58 A) = (term51 A).
Proof. exact (@lem3256144 (term51 A)). Qed.
Lemma lem3256184 {A : Type'} : (term53 A) = (term51 A).
Proof. exact (TRANS (@lem3256142 A) (@lem3256145 A)). Qed.
Lemma lem3256193 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term43 A t s x) = (term43 A t s x).
Proof. exact (eq_refl (term43 A t s x)). Qed.
Lemma lem3256194 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term45 A t s) = (term45 A t s).
Proof. exact (fun_ext (fun x : A => @lem3256193 A t s x)). Qed.
Lemma lem3256195 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3256196 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term46 A t s) = (term46 A t s).
Proof. exact (MK_COMB (@lem3256195 A) (@lem3256194 A t s)). Qed.
Lemma lem3256197 {A : Type'} (s : A -> Prop) : (term47 A s) = (term47 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3256196 A t s)). Qed.
Lemma lem3256198 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3256199 {A : Type'} (s : A -> Prop) : (term48 A s) = (term48 A s).
Proof. exact (MK_COMB (@lem3256198 A) (@lem3256197 A s)). Qed.
Lemma lem3256200 {A : Type'} : (term49 A) = (term49 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3256199 A s)). Qed.
Lemma lem3256201 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3256202 {A : Type'} : (term50 A) = (term50 A).
Proof. exact (MK_COMB (@lem3256201 A) (@lem3256200 A)). Qed.
Lemma lem3256211 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term33 A t s x) = (term33 A t s x).
Proof. exact (eq_refl (term33 A t s x)). Qed.
Lemma lem3256212 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term35 A t s) = (term35 A t s).
Proof. exact (fun_ext (fun x : A => @lem3256211 A t s x)). Qed.
Lemma lem3256213 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3256214 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term36 A t s) = (term36 A t s).
Proof. exact (MK_COMB (@lem3256213 A) (@lem3256212 A t s)). Qed.
Lemma lem3256215 {A : Type'} (s : A -> Prop) : (term37 A s) = (term37 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3256214 A t s)). Qed.
Lemma lem3256216 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3256217 {A : Type'} (s : A -> Prop) : (term38 A s) = (term38 A s).
Proof. exact (MK_COMB (@lem3256216 A) (@lem3256215 A s)). Qed.
Lemma lem3256218 {A : Type'} : (term39 A) = (term39 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3256217 A s)). Qed.
Lemma lem3256219 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3256220 {A : Type'} : (term40 A) = (term40 A).
Proof. exact (MK_COMB (@lem3256219 A) (@lem3256218 A)). Qed.
Lemma lem3256221 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3256222 {A : Type'} : (term41 A) = (term41 A).
Proof. exact (MK_COMB (@lem3256221) (@lem3256220 A)). Qed.
Lemma lem3256223 {A : Type'} : (term51 A) = (term51 A).
Proof. exact (MK_COMB (@lem3256222 A) (@lem3256202 A)). Qed.
Lemma lem3256272 {A : Type'} : (term53 A) = (term51 A).
Proof. exact (TRANS (@lem3256184 A) (@lem3256223 A)). Qed.
Lemma lem3256273 {A : Type'} : (term51 A) = (term53 A).
Proof. exact (SYM (@lem3256272 A)). Qed.
Lemma lem3256275 (p : Prop) : p = (term52 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3256276 {A : Type'} : (term51 A) = (term53 A).
Proof. exact (@lem3256275 (term51 A)). Qed.
Lemma lem3256277 {A : Type'} : (term53 A) = (term51 A).
Proof. exact (SYM (@lem3256276 A)). Qed.
Lemma lem3256278 {A : Type'} (h1 : term54 A) : term54 A.
Proof. exact (h1). Qed.
Lemma lem3256289 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term60 A t s x) = (term61 A t s x).
Proof. exact (@lem17362 (term29 A s t x) (s x)). Qed.
Lemma lem3256290 {A : Type'} (P : A -> Prop) : (term62 A P) = (term63 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3256291 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term64 A t s) = (term65 A t s).
Proof. exact (@lem3256290 A (term35 A t s)). Qed.
Lemma lem3256292 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term66 A t s x) = (term33 A t s x).
Proof. exact (eq_refl (term66 A t s x)). Qed.
Lemma lem3256293 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3256294 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term67 A t s x) = (term60 A t s x).
Proof. exact (MK_COMB (@lem3256293) (@lem3256292 A t s x)). Qed.
Lemma lem3256295 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term67 A t s x) = (term61 A t s x).
Proof. exact (TRANS (@lem3256294 A t s x) (@lem3256289 A t s x)). Qed.
Lemma lem3256296 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term68 A t s) = (term69 A t s).
Proof. exact (fun_ext (fun x : A => @lem3256295 A t s x)). Qed.
Lemma lem3256297 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3256298 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term65 A t s) = (term70 A t s).
Proof. exact (MK_COMB (@lem3256297 A) (@lem3256296 A t s)). Qed.
Lemma lem3256299 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term64 A t s) = (term70 A t s).
Proof. exact (TRANS (@lem3256291 A t s) (@lem3256298 A t s)). Qed.
Lemma lem3256300 {A : Type'} (P : type686 A) : (term71 A P) = (term72 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem3256301 {A : Type'} (s : A -> Prop) : (term73 A s) = (term74 A s).
Proof. exact (@lem3256300 A (term37 A s)). Qed.
Lemma lem3256302 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term75 A s t) = (term36 A t s).
Proof. exact (eq_refl (term75 A s t)). Qed.
Lemma lem3256303 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3256304 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term76 A s t) = (term64 A t s).
Proof. exact (MK_COMB (@lem3256303) (@lem3256302 A t s)). Qed.
Lemma lem3256305 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term76 A s t) = (term70 A t s).
Proof. exact (TRANS (@lem3256304 A t s) (@lem3256299 A t s)). Qed.
Lemma lem3256306 {A : Type'} (s : A -> Prop) : (term77 A s) = (term78 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3256305 A t s)). Qed.
Lemma lem3256307 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3256308 {A : Type'} (s : A -> Prop) : (term74 A s) = (term79 A s).
Proof. exact (MK_COMB (@lem3256307 A) (@lem3256306 A s)). Qed.
Lemma lem3256309 {A : Type'} (s : A -> Prop) : (term73 A s) = (term79 A s).
Proof. exact (TRANS (@lem3256301 A s) (@lem3256308 A s)). Qed.
Lemma lem3256310 {A : Type'} (P : type686 A) : (term71 A P) = (term72 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem3256311 {A : Type'} : (term80 A) = (term81 A).
Proof. exact (@lem3256310 A (term39 A)). Qed.
Lemma lem3256312 {A : Type'} (s : A -> Prop) : (term82 A s) = (term38 A s).
Proof. exact (eq_refl (term82 A s)). Qed.
Lemma lem3256313 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3256314 {A : Type'} (s : A -> Prop) : (term83 A s) = (term73 A s).
Proof. exact (MK_COMB (@lem3256313) (@lem3256312 A s)). Qed.
Lemma lem3256315 {A : Type'} (s : A -> Prop) : (term83 A s) = (term79 A s).
Proof. exact (TRANS (@lem3256314 A s) (@lem3256309 A s)). Qed.
Lemma lem3256316 {A : Type'} : (term84 A) = (term85 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3256315 A s)). Qed.
Lemma lem3256317 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3256318 {A : Type'} : (term81 A) = (term86 A).
Proof. exact (MK_COMB (@lem3256317 A) (@lem3256316 A)). Qed.
Lemma lem3256319 {A : Type'} : (term80 A) = (term86 A).
Proof. exact (TRANS (@lem3256311 A) (@lem3256318 A)). Qed.
Lemma lem3256330 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term87 A t s x) = (term88 A t s x).
Proof. exact (@lem17362 (term29 A t s x) (s x)). Qed.
Lemma lem3256331 {A : Type'} (P : A -> Prop) : (term62 A P) = (term63 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3256332 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term89 A t s) = (term90 A t s).
Proof. exact (@lem3256331 A (term45 A t s)). Qed.
Lemma lem3256333 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term91 A t s x) = (term43 A t s x).
Proof. exact (eq_refl (term91 A t s x)). Qed.
Lemma lem3256334 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3256335 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term92 A t s x) = (term87 A t s x).
Proof. exact (MK_COMB (@lem3256334) (@lem3256333 A t s x)). Qed.
Lemma lem3256336 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term92 A t s x) = (term88 A t s x).
Proof. exact (TRANS (@lem3256335 A t s x) (@lem3256330 A t s x)). Qed.
Lemma lem3256337 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term93 A t s) = (term94 A t s).
Proof. exact (fun_ext (fun x : A => @lem3256336 A t s x)). Qed.
Lemma lem3256338 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3256339 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term90 A t s) = (term95 A t s).
Proof. exact (MK_COMB (@lem3256338 A) (@lem3256337 A t s)). Qed.
Lemma lem3256340 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term89 A t s) = (term95 A t s).
Proof. exact (TRANS (@lem3256332 A t s) (@lem3256339 A t s)). Qed.
Lemma lem3256341 {A : Type'} (P : type686 A) : (term71 A P) = (term72 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem3256342 {A : Type'} (s : A -> Prop) : (term96 A s) = (term97 A s).
Proof. exact (@lem3256341 A (term47 A s)). Qed.
Lemma lem3256343 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term98 A s t) = (term46 A t s).
Proof. exact (eq_refl (term98 A s t)). Qed.
Lemma lem3256344 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3256345 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term99 A s t) = (term89 A t s).
Proof. exact (MK_COMB (@lem3256344) (@lem3256343 A t s)). Qed.
Lemma lem3256346 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term99 A s t) = (term95 A t s).
Proof. exact (TRANS (@lem3256345 A t s) (@lem3256340 A t s)). Qed.
Lemma lem3256347 {A : Type'} (s : A -> Prop) : (term100 A s) = (term101 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3256346 A t s)). Qed.
Lemma lem3256348 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3256349 {A : Type'} (s : A -> Prop) : (term97 A s) = (term102 A s).
Proof. exact (MK_COMB (@lem3256348 A) (@lem3256347 A s)). Qed.
Lemma lem3256350 {A : Type'} (s : A -> Prop) : (term96 A s) = (term102 A s).
Proof. exact (TRANS (@lem3256342 A s) (@lem3256349 A s)). Qed.
Lemma lem3256351 {A : Type'} (P : type686 A) : (term71 A P) = (term72 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem3256352 {A : Type'} : (term103 A) = (term104 A).
Proof. exact (@lem3256351 A (term49 A)). Qed.
Lemma lem3256353 {A : Type'} (s : A -> Prop) : (term105 A s) = (term48 A s).
Proof. exact (eq_refl (term105 A s)). Qed.
Lemma lem3256354 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3256355 {A : Type'} (s : A -> Prop) : (term106 A s) = (term96 A s).
Proof. exact (MK_COMB (@lem3256354) (@lem3256353 A s)). Qed.
Lemma lem3256356 {A : Type'} (s : A -> Prop) : (term106 A s) = (term102 A s).
Proof. exact (TRANS (@lem3256355 A s) (@lem3256350 A s)). Qed.
Lemma lem3256357 {A : Type'} : (term107 A) = (term108 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3256356 A s)). Qed.
Lemma lem3256358 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3256359 {A : Type'} : (term104 A) = (term109 A).
Proof. exact (MK_COMB (@lem3256358 A) (@lem3256357 A)). Qed.
Lemma lem3256360 {A : Type'} : (term103 A) = (term109 A).
Proof. exact (TRANS (@lem3256352 A) (@lem3256359 A)). Qed.
Lemma lem3256361 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3256362 {A : Type'} : (term110 A) = (term111 A).
Proof. exact (MK_COMB (@lem3256361) (@lem3256319 A)). Qed.
Lemma lem3256363 {A : Type'} : (term112 A) = (term113 A).
Proof. exact (MK_COMB (@lem3256362 A) (@lem3256360 A)). Qed.
Lemma lem3256364 {A : Type'} : (term54 A) = (term112 A).
Proof. exact (@lem17045 (term40 A) (term50 A)). Qed.
Lemma lem3256365 {A : Type'} : (term54 A) = (term113 A).
Proof. exact (TRANS (@lem3256364 A) (@lem3256363 A)). Qed.
Lemma lem3256480 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term114 A P Q) = (term115 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3256481 {A : Type'} (P : type686 A) (Q : type686 A) : (term116 A P Q) = (term117 A P Q).
Proof. exact (@lem3256480 (A -> Prop) P Q). Qed.
Lemma lem3256482 {A : Type'} : (term118 A) = (term119 A).
Proof. exact (@lem3256481 A (term85 A) (term108 A)). Qed.
Lemma lem3256483 {A : Type'} (s : A -> Prop) : (term120 A s) = (term79 A s).
Proof. exact (eq_refl (term120 A s)). Qed.
Lemma lem3256484 {A : Type'} : (term121 A) = (term85 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3256483 A s)). Qed.
Lemma lem3256485 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3256486 {A : Type'} : (term122 A) = (term86 A).
Proof. exact (MK_COMB (@lem3256485 A) (@lem3256484 A)). Qed.
Lemma lem3256487 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3256488 {A : Type'} : (term123 A) = (term111 A).
Proof. exact (MK_COMB (@lem3256487) (@lem3256486 A)). Qed.
Lemma lem3256489 {A : Type'} (s : A -> Prop) : (term124 A s) = (term102 A s).
Proof. exact (eq_refl (term124 A s)). Qed.
Lemma lem3256490 {A : Type'} : (term125 A) = (term108 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3256489 A s)). Qed.
Lemma lem3256491 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3256492 {A : Type'} : (term126 A) = (term109 A).
Proof. exact (MK_COMB (@lem3256491 A) (@lem3256490 A)). Qed.
Lemma lem3256493 {A : Type'} : (term118 A) = (term113 A).
Proof. exact (MK_COMB (@lem3256488 A) (@lem3256492 A)). Qed.
Lemma lem3256494 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3256495 {A : Type'} : (term127 A) = (term128 A).
Proof. exact (MK_COMB (@lem3256494) (@lem3256493 A)). Qed.
Lemma lem3256496 {A : Type'} (s : A -> Prop) : (term120 A s) = (term79 A s).
Proof. exact (eq_refl (term120 A s)). Qed.
Lemma lem3256497 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3256498 {A : Type'} (s : A -> Prop) : (term129 A s) = (term130 A s).
Proof. exact (MK_COMB (@lem3256497) (@lem3256496 A s)). Qed.
Lemma lem3256499 {A : Type'} (s : A -> Prop) : (term124 A s) = (term102 A s).
Proof. exact (eq_refl (term124 A s)). Qed.
Lemma lem3256500 {A : Type'} (s : A -> Prop) : (term131 A s) = (term132 A s).
Proof. exact (MK_COMB (@lem3256498 A s) (@lem3256499 A s)). Qed.
Lemma lem3256501 {A : Type'} : (term133 A) = (term134 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3256500 A s)). Qed.
Lemma lem3256502 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3256503 {A : Type'} : (term119 A) = (term135 A).
Proof. exact (MK_COMB (@lem3256502 A) (@lem3256501 A)). Qed.
Lemma lem3256504 {A : Type'} : ((term118 A) = (term119 A)) = ((term113 A) = (term135 A)).
Proof. exact (MK_COMB (@lem3256495 A) (@lem3256503 A)). Qed.
Lemma lem3256505 {A : Type'} : (term113 A) = (term135 A).
Proof. exact (EQ_MP (@lem3256504 A) (@lem3256482 A)). Qed.
Lemma lem3256507 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term114 A P Q) = (term115 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3256508 {A : Type'} (P : type686 A) (Q : type686 A) : (term116 A P Q) = (term117 A P Q).
Proof. exact (@lem3256507 (A -> Prop) P Q). Qed.
Lemma lem3256509 {A : Type'} (s : A -> Prop) : (term136 A s) = (term137 A s).
Proof. exact (@lem3256508 A (term78 A s) (term101 A s)). Qed.
Lemma lem3256510 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term138 A s t) = (term70 A t s).
Proof. exact (eq_refl (term138 A s t)). Qed.
Lemma lem3256511 {A : Type'} (s : A -> Prop) : (term139 A s) = (term78 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3256510 A t s)). Qed.
Lemma lem3256512 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3256513 {A : Type'} (s : A -> Prop) : (term140 A s) = (term79 A s).
Proof. exact (MK_COMB (@lem3256512 A) (@lem3256511 A s)). Qed.
Lemma lem3256514 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3256515 {A : Type'} (s : A -> Prop) : (term141 A s) = (term130 A s).
Proof. exact (MK_COMB (@lem3256514) (@lem3256513 A s)). Qed.
Lemma lem3256516 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term142 A s t) = (term95 A t s).
Proof. exact (eq_refl (term142 A s t)). Qed.
Lemma lem3256517 {A : Type'} (s : A -> Prop) : (term143 A s) = (term101 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3256516 A t s)). Qed.
Lemma lem3256518 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3256519 {A : Type'} (s : A -> Prop) : (term144 A s) = (term102 A s).
Proof. exact (MK_COMB (@lem3256518 A) (@lem3256517 A s)). Qed.
Lemma lem3256520 {A : Type'} (s : A -> Prop) : (term136 A s) = (term132 A s).
Proof. exact (MK_COMB (@lem3256515 A s) (@lem3256519 A s)). Qed.
Lemma lem3256521 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3256522 {A : Type'} (s : A -> Prop) : (term145 A s) = (term146 A s).
Proof. exact (MK_COMB (@lem3256521) (@lem3256520 A s)). Qed.
Lemma lem3256523 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term138 A s t) = (term70 A t s).
Proof. exact (eq_refl (term138 A s t)). Qed.
Lemma lem3256524 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3256525 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term147 A s t) = (term148 A t s).
Proof. exact (MK_COMB (@lem3256524) (@lem3256523 A t s)). Qed.
Lemma lem3256526 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term142 A s t) = (term95 A t s).
Proof. exact (eq_refl (term142 A s t)). Qed.
Lemma lem3256527 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term149 A s t) = (term150 A t s).
Proof. exact (MK_COMB (@lem3256525 A t s) (@lem3256526 A t s)). Qed.
Lemma lem3256528 {A : Type'} (s : A -> Prop) : (term151 A s) = (term152 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3256527 A t s)). Qed.
Lemma lem3256529 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3256530 {A : Type'} (s : A -> Prop) : (term137 A s) = (term153 A s).
Proof. exact (MK_COMB (@lem3256529 A) (@lem3256528 A s)). Qed.
Lemma lem3256531 {A : Type'} (s : A -> Prop) : ((term136 A s) = (term137 A s)) = ((term132 A s) = (term153 A s)).
Proof. exact (MK_COMB (@lem3256522 A s) (@lem3256530 A s)). Qed.
Lemma lem3256532 {A : Type'} (s : A -> Prop) : (term132 A s) = (term153 A s).
Proof. exact (EQ_MP (@lem3256531 A s) (@lem3256509 A s)). Qed.
Lemma lem3256534 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term114 A P Q) = (term115 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3256535 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term114 A P Q) = (term115 A P Q).
Proof. exact (@lem3256534 A P Q). Qed.
Lemma lem3256536 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term154 A t s) = (term155 A t s).
Proof. exact (@lem3256535 A (term69 A t s) (term94 A t s)). Qed.
Lemma lem3256537 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term156 A t s x) = (term61 A t s x).
Proof. exact (eq_refl (term156 A t s x)). Qed.
Lemma lem3256538 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term157 A t s) = (term69 A t s).
Proof. exact (fun_ext (fun x : A => @lem3256537 A t s x)). Qed.
Lemma lem3256539 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3256540 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term158 A t s) = (term70 A t s).
Proof. exact (MK_COMB (@lem3256539 A) (@lem3256538 A t s)). Qed.
Lemma lem3256541 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3256542 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term159 A t s) = (term148 A t s).
Proof. exact (MK_COMB (@lem3256541) (@lem3256540 A t s)). Qed.
Lemma lem3256543 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term160 A t s x) = (term88 A t s x).
Proof. exact (eq_refl (term160 A t s x)). Qed.
Lemma lem3256544 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term161 A t s) = (term94 A t s).
Proof. exact (fun_ext (fun x : A => @lem3256543 A t s x)). Qed.
Lemma lem3256545 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3256546 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term162 A t s) = (term95 A t s).
Proof. exact (MK_COMB (@lem3256545 A) (@lem3256544 A t s)). Qed.
Lemma lem3256547 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term154 A t s) = (term150 A t s).
Proof. exact (MK_COMB (@lem3256542 A t s) (@lem3256546 A t s)). Qed.
Lemma lem3256548 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3256549 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term163 A t s) = (term164 A t s).
Proof. exact (MK_COMB (@lem3256548) (@lem3256547 A t s)). Qed.
Lemma lem3256550 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term156 A t s x) = (term61 A t s x).
Proof. exact (eq_refl (term156 A t s x)). Qed.
Lemma lem3256551 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3256552 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term165 A t s x) = (term166 A t s x).
Proof. exact (MK_COMB (@lem3256551) (@lem3256550 A t s x)). Qed.
Lemma lem3256553 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term160 A t s x) = (term88 A t s x).
Proof. exact (eq_refl (term160 A t s x)). Qed.
Lemma lem3256554 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term167 A t s x) = (term168 A t s x).
Proof. exact (MK_COMB (@lem3256552 A t s x) (@lem3256553 A t s x)). Qed.
Lemma lem3256555 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term169 A t s) = (term170 A t s).
Proof. exact (fun_ext (fun x : A => @lem3256554 A t s x)). Qed.
Lemma lem3256556 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3256557 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term155 A t s) = (term171 A t s).
Proof. exact (MK_COMB (@lem3256556 A) (@lem3256555 A t s)). Qed.
Lemma lem3256558 {A : Type'} (t : A -> Prop) (s : A -> Prop) : ((term154 A t s) = (term155 A t s)) = ((term150 A t s) = (term171 A t s)).
Proof. exact (MK_COMB (@lem3256549 A t s) (@lem3256557 A t s)). Qed.
Lemma lem3256559 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term150 A t s) = (term171 A t s).
Proof. exact (EQ_MP (@lem3256558 A t s) (@lem3256536 A t s)). Qed.
Lemma lem3256560 {A : Type'} (s : A -> Prop) : (term152 A s) = (term172 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3256559 A t s)). Qed.
Lemma lem3256561 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3256562 {A : Type'} (s : A -> Prop) : (term153 A s) = (term173 A s).
Proof. exact (MK_COMB (@lem3256561 A) (@lem3256560 A s)). Qed.
Lemma lem3256563 {A : Type'} (s : A -> Prop) : (term132 A s) = (term173 A s).
Proof. exact (TRANS (@lem3256532 A s) (@lem3256562 A s)). Qed.
Lemma lem3256564 {A : Type'} : (term134 A) = (term174 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3256563 A s)). Qed.
Lemma lem3256565 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3256566 {A : Type'} : (term135 A) = (term175 A).
Proof. exact (MK_COMB (@lem3256565 A) (@lem3256564 A)). Qed.
Lemma lem3256568 {A : Type'} : (term113 A) = (term175 A).
Proof. exact (TRANS (@lem3256505 A) (@lem3256566 A)). Qed.
Lemma lem3256569 {A : Type'} : (term54 A) = (term175 A).
Proof. exact (TRANS (@lem3256365 A) (@lem3256568 A)). Qed.
Lemma lem3256570 {A : Type'} (h1 : term54 A) : term175 A.
Proof. exact (EQ_MP (@lem3256569 A) (@lem3256278 A h1)). Qed.
Lemma lem3256571 {A : Type'} (s : A -> Prop) (h1 : term173 A s) : term173 A s.
Proof. exact (h1). Qed.
Lemma lem3256572 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term171 A t s) : term171 A t s.
Proof. exact (h1). Qed.
Lemma lem3256611 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term168 A t s x) : term168 A t s x.
Proof. exact (h1). Qed.
Lemma lem3256612 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term61 A t s x) : term61 A t s x.
Proof. exact (h1). Qed.
Lemma lem3256613 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term88 A t s x) : term88 A t s x.
Proof. exact (h1). Qed.
Lemma lem3256615 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term61 A t s x) : term29 A s t x.
Proof. exact (proj1 (@lem3256612 A t s x h1)). Qed.
Lemma lem3256619 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term88 A t s x) : term29 A t s x.
Proof. exact (proj1 (@lem3256613 A t s x h1)). Qed.
Lemma lem3256647 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term61 A t s x) : term176 A s x.
Proof. exact (proj2 (@lem3256612 A t s x h1)). Qed.
Lemma lem3256653 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term88 A t s x) : term176 A s x.
Proof. exact (proj2 (@lem3256613 A t s x h1)). Qed.
Lemma lem3256659 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term61 A t s x) : s x.
Proof. exact (proj1 (@lem3256615 A t s x h1)). Qed.
Lemma lem3256660 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term61 A t s x) : term177 A s x.
Proof. exact (fun h0 : term176 A s x => @lem3256659 A t s x h1). Qed.
Lemma lem3256662 (p : Prop) : (term178 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3256663 {A : Type'} (s : A -> Prop) (x : A) : (term177 A s x) = (s x).
Proof. exact (@lem3256662 (s x)). Qed.
Lemma lem3256664 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term61 A t s x) : s x.
Proof. exact (EQ_MP (@lem3256663 A s x) (@lem3256660 A t s x h1)). Qed.
Lemma lem3256667 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3256669 {A : Type'} (s : A -> Prop) (x : A) : (term176 A s x) = (term179 A s x).
Proof. exact (@lem3256667 (s x)). Qed.
Lemma lem3256672 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term61 A t s x) : term179 A s x.
Proof. exact (EQ_MP (@lem3256669 A s x) (@lem3256647 A t s x h1)). Qed.
Lemma lem3256675 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term61 A t s x) : False.
Proof. exact (@lem3256672 A t s x h1 (@lem3256664 A t s x h1)). Qed.
Lemma lem3256676 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term61 A t s x) : term180.
Proof. exact (fun h0 : ~ False => @lem3256675 A t s x h1). Qed.
Lemma lem3256678 (p : Prop) : (term178 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3256679 : term180 = False.
Proof. exact (@lem3256678 False). Qed.
Lemma lem3256680 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term61 A t s x) : False.
Proof. exact (EQ_MP (@lem3256679) (@lem3256676 A t s x h1)). Qed.
Lemma lem3256682 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term88 A t s x) : s x.
Proof. exact (proj2 (@lem3256619 A t s x h1)). Qed.
Lemma lem3256683 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term88 A t s x) : term177 A s x.
Proof. exact (fun h0 : term176 A s x => @lem3256682 A t s x h1). Qed.
Lemma lem3256685 (p : Prop) : (term178 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3256686 {A : Type'} (s : A -> Prop) (x : A) : (term177 A s x) = (s x).
Proof. exact (@lem3256685 (s x)). Qed.
Lemma lem3256687 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term88 A t s x) : s x.
Proof. exact (EQ_MP (@lem3256686 A s x) (@lem3256683 A t s x h1)). Qed.
Lemma lem3256690 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3256692 {A : Type'} (s : A -> Prop) (x : A) : (term176 A s x) = (term179 A s x).
Proof. exact (@lem3256690 (s x)). Qed.
Lemma lem3256695 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term88 A t s x) : term179 A s x.
Proof. exact (EQ_MP (@lem3256692 A s x) (@lem3256653 A t s x h1)). Qed.
Lemma lem3256698 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term88 A t s x) : False.
Proof. exact (@lem3256695 A t s x h1 (@lem3256687 A t s x h1)). Qed.
Lemma lem3256699 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term88 A t s x) : term180.
Proof. exact (fun h0 : ~ False => @lem3256698 A t s x h1). Qed.
Lemma lem3256701 (p : Prop) : (term178 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3256702 : term180 = False.
Proof. exact (@lem3256701 False). Qed.
Lemma lem3256703 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term88 A t s x) : False.
Proof. exact (EQ_MP (@lem3256702) (@lem3256699 A t s x h1)). Qed.
Lemma lem3256704 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term168 A t s x) : False.
Proof. exact (or_elim (@lem3256611 A t s x h1) (fun h0 : term61 A t s x => @lem3256680 A t s x h0) (fun h0 : term88 A t s x => @lem3256703 A t s x h0)). Qed.
Lemma lem3256705 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term168 A t s x) : (term168 A t s x) = False.
Proof. exact (prop_ext (fun h2 : term168 A t s x => @lem3256704 A t s x h1) (fun h2 : False => @lem3256611 A t s x h1)). Qed.
Lemma lem3256706 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term168 A t s x) : False.
Proof. exact (EQ_MP (@lem3256705 A t s x h1) (@lem3256611 A t s x h1)). Qed.
Lemma lem3256707 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term171 A t s) : False.
Proof. exact (ex_elim (@lem3256572 A t s h1) (fun x : A => fun h0 : term170 A t s x => @lem3256706 A t s x h0)). Qed.
Lemma lem3256708 {A : Type'} (s : A -> Prop) (h1 : term173 A s) : False.
Proof. exact (ex_elim (@lem3256571 A s h1) (fun t : A -> Prop => fun h0 : term172 A s t => @lem3256707 A t s h0)). Qed.
Lemma lem3256709 {A : Type'} (h1 : term54 A) : False.
Proof. exact (ex_elim (@lem3256570 A h1) (fun s : A -> Prop => fun h0 : term174 A s => @lem3256708 A s h0)). Qed.
Lemma lem3256710 {A : Type'} (h1 : term54 A) : (term54 A) = False.
Proof. exact (prop_ext (fun h2 : term54 A => @lem3256709 A h1) (fun h2 : False => @lem3256278 A h1)). Qed.
Lemma lem3256711 {A : Type'} (h1 : term54 A) : False.
Proof. exact (EQ_MP (@lem3256710 A h1) (@lem3256278 A h1)). Qed.
Lemma lem3256712 {A : Type'} : term53 A.
Proof. exact (fun h0 : term54 A => @lem3256711 A h0). Qed.
Lemma lem3256713 {A : Type'} : term51 A.
Proof. exact (EQ_MP (@lem3256277 A) (@lem3256712 A)). Qed.
Lemma lem3256714 {A : Type'} : term53 A.
Proof. exact (EQ_MP (@lem3256273 A) (@lem3256713 A)). Qed.
Lemma lem3256716 {A : Type'} : term53 A.
Proof. exact (@lem3256139 A (@lem3256714 A)). Qed.
Lemma lem3256717 {A : Type'} (h1 : term54 A) : False.
Proof. exact (@lem3256716 A (@lem3256123 A h1)). Qed.
Lemma lem3256718 {A : Type'} (h1 : term54 A) : (term54 A) = False.
Proof. exact (prop_ext (fun h2 : term54 A => @lem3256717 A h1) (fun h2 : False => @lem3256123 A h1)). Qed.
Lemma lem3256719 {A : Type'} (h1 : term54 A) : False.
Proof. exact (EQ_MP (@lem3256718 A h1) (@lem3256123 A h1)). Qed.
Lemma lem3256720 {A : Type'} : term53 A.
Proof. exact (fun h0 : term54 A => @lem3256719 A h0). Qed.
Lemma lem3256721 {A : Type'} : term51 A.
Proof. exact (EQ_MP (@lem3256122 A) (@lem3256720 A)). Qed.
Lemma lem3256722 {A : Type'} : term24 A.
Proof. exact (EQ_MP (@lem3256118 A) (@lem3256721 A)). Qed.
Lemma lem3256723 {A : Type'} : term23 A.
Proof. exact (EQ_MP (@lem3255983 A) (@lem3256722 A)). Qed.
