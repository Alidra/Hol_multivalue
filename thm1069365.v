Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1069365_term_abbrevs.
Require Import thm0_spec.
Require Import thm32_spec.
Require Import thm37_spec.
Require Import thm51_spec.
Require Import thm9103_spec.
Require Import thm9104_spec.
Require Import thm9120_spec.
Lemma lem1069017 {A : Type'} (a : recspace A) (NONE' : recspace A) (h1 : a = NONE') : a = NONE'.
Proof. exact (h1). Qed.
Lemma lem1069018 {A : Type'} (option' : type1338 A) (NONE' : recspace A) (h1 : option' NONE') : option' NONE'.
Proof. exact (h1). Qed.
Lemma lem1069019 {A : Type'} (option' : type1338 A) : option' = option'.
Proof. exact (eq_refl option'). Qed.
Lemma lem1069020 {A : Type'} (option' : type1338 A) (a : recspace A) (NONE' : recspace A) (h1 : a = NONE') : (option' a) = (option' NONE').
Proof. exact (MK_COMB (@lem1069019 A option') (@lem1069017 A a NONE' h1)). Qed.
Lemma lem1069021 {A : Type'} (option' : type1338 A) (a : recspace A) (NONE' : recspace A) (h1 : a = NONE') : (option' NONE') = (option' a).
Proof. exact (SYM (@lem1069020 A option' a NONE' h1)). Qed.
Lemma lem1069022 {A : Type'} (option' : type1338 A) (a : recspace A) (NONE' : recspace A) (h1 : option' NONE') (h2 : a = NONE') : option' a.
Proof. exact (EQ_MP (@lem1069021 A option' a NONE' h2) (@lem1069018 A option' NONE' h1)). Qed.
Lemma lem1069023 {A : Type'} (a : recspace A) (option' : type1338 A) (NONE' : recspace A) (h1 : option' NONE') : term0 A NONE' option' a.
Proof. exact (fun h0 : a = NONE' => @lem1069022 A option' a NONE' h1 h0). Qed.
Lemma lem1069024 {A : Type'} (a : recspace A) (NONE' : recspace A) (h1 : a = NONE') : a = NONE'.
Proof. exact (h1). Qed.
Lemma lem1069025 {A : Type'} (option' : type1338 A) (a : recspace A) (NONE' : recspace A) (h1 : option' NONE') (h2 : a = NONE') : option' a.
Proof. exact (@lem1069023 A a option' NONE' h1 (@lem1069024 A a NONE' h2)). Qed.
Lemma lem1069026 {A : Type'} (a : recspace A) (option' : type1338 A) (NONE' : recspace A) (h1 : option' NONE') : term0 A NONE' option' a.
Proof. exact (fun h0 : a = NONE' => @lem1069025 A option' a NONE' h1 h0). Qed.
Lemma lem1069027 {A : Type'} (option' : type1338 A) (NONE' : recspace A) (h1 : option' NONE') : term1 A NONE' option'.
Proof. exact (fun a : recspace A => @lem1069026 A a option' NONE' h1). Qed.
Lemma lem1069028 {A : Type'} (NONE' : recspace A) (option' : type1338 A) (h1 : term1 A NONE' option') : term1 A NONE' option'.
Proof. exact (h1). Qed.
Lemma lem1069029 {A : Type'} (NONE' : recspace A) (option' : type1338 A) (h1 : term1 A NONE' option') : term2 A option' NONE'.
Proof. exact (@lem1069028 A NONE' option' h1 NONE'). Qed.
Lemma lem1069030 {A : Type'} (option' : type1338 A) (NONE' : recspace A) : (term2 A option' NONE') = (term3 A option' NONE').
Proof. exact (eq_refl (term2 A option' NONE')). Qed.
Lemma lem1069031 {A : Type'} (NONE' : recspace A) (option' : type1338 A) (h1 : term1 A NONE' option') : term3 A option' NONE'.
Proof. exact (EQ_MP (@lem1069030 A option' NONE') (@lem1069029 A NONE' option' h1)). Qed.
Lemma lem1069032 {A : Type'} (NONE' : recspace A) : NONE' = NONE'.
Proof. exact (eq_refl NONE'). Qed.
Lemma lem1069033 {A : Type'} (NONE' : recspace A) (option' : type1338 A) (h1 : term1 A NONE' option') : option' NONE'.
Proof. exact (@lem1069031 A NONE' option' h1 (@lem1069032 A NONE')). Qed.
Lemma lem1069034 {A : Type'} (option' : type1338 A) (NONE' : recspace A) : term4 A option' NONE'.
Proof. exact (fun h0 : term1 A NONE' option' => @lem1069033 A NONE' option' h0). Qed.
Lemma lem1069035 {A : Type'} (NONE' : recspace A) (option' : type1338 A) : term5 A NONE' option'.
Proof. exact (fun h0 : option' NONE' => @lem1069027 A option' NONE' h0). Qed.
Lemma lem1069036 {A : Type'} (option' : type1338 A) (NONE' : recspace A) : term6 A option' NONE'.
Proof. exact (conj (@lem1069035 A NONE' option') (@lem1069034 A option' NONE')). Qed.
Lemma lem1069037 {A : Type'} (NONE' : recspace A) (option' : type1338 A) : (term6 A option' NONE') = ((option' NONE') = (term1 A NONE' option')).
Proof. exact (@lem32 (option' NONE') (term1 A NONE' option')). Qed.
Lemma lem1069038 {A : Type'} (NONE' : recspace A) (option' : type1338 A) : (option' NONE') = (term1 A NONE' option').
Proof. exact (EQ_MP (@lem1069037 A NONE' option') (@lem1069036 A option' NONE')). Qed.
Lemma lem1069039 {A : Type'} (NONE' : recspace A) (option' : type1338 A) (a : recspace A) (h1 : term0 A NONE' option' a) : term0 A NONE' option' a.
Proof. exact (h1). Qed.
Lemma lem1069040 {A : Type'} (a : recspace A) (NONE' : recspace A) (h1 : a = NONE') : a = NONE'.
Proof. exact (h1). Qed.
Lemma lem1069041 {A : Type'} (NONE' : recspace A) (option' : type1338 A) (a : recspace A) (h1 : a = NONE') (h2 : term0 A NONE' option' a) : option' a.
Proof. exact (@lem1069039 A NONE' option' a h2 (@lem1069040 A a NONE' h1)). Qed.
Lemma lem1069042 {A : Type'} (option' : type1338 A) (a : recspace A) (NONE' : recspace A) (h1 : a = NONE') : term7 A NONE' option' a.
Proof. exact (fun h0 : term0 A NONE' option' a => @lem1069041 A NONE' option' a h1 h0). Qed.
Lemma lem1069043 {A : Type'} (NONE' : recspace A) (option' : type1338 A) (a : recspace A) (h1 : term0 A NONE' option' a) : term0 A NONE' option' a.
Proof. exact (h1). Qed.
Lemma lem1069044 {A : Type'} (NONE' : recspace A) (option' : type1338 A) (a : recspace A) (h1 : a = NONE') (h2 : term0 A NONE' option' a) : option' a.
Proof. exact (@lem1069042 A option' a NONE' h1 (@lem1069043 A NONE' option' a h2)). Qed.
Lemma lem1069045 {A : Type'} (NONE' : recspace A) (option' : type1338 A) (a : recspace A) (h1 : term0 A NONE' option' a) : term0 A NONE' option' a.
Proof. exact (fun h0 : a = NONE' => @lem1069044 A NONE' option' a h0 h1). Qed.
Lemma lem1069046 {A : Type'} (NONE' : recspace A) (option' : type1338 A) (a : recspace A) (h1 : term0 A NONE' option' a) : term0 A NONE' option' a.
Proof. exact (h1). Qed.
Lemma lem1069047 {A : Type'} (a : recspace A) (NONE' : recspace A) (h1 : a = NONE') : a = NONE'.
Proof. exact (h1). Qed.
Lemma lem1069048 {A : Type'} (NONE' : recspace A) (option' : type1338 A) (a : recspace A) (h1 : a = NONE') (h2 : term0 A NONE' option' a) : option' a.
Proof. exact (@lem1069046 A NONE' option' a h2 (@lem1069047 A a NONE' h1)). Qed.
Lemma lem1069049 {A : Type'} (NONE' : recspace A) (option' : type1338 A) (a : recspace A) (h1 : term0 A NONE' option' a) : term0 A NONE' option' a.
Proof. exact (fun h0 : a = NONE' => @lem1069048 A NONE' option' a h0 h1). Qed.
Lemma lem1069050 {A : Type'} (NONE' : recspace A) (option' : type1338 A) (a : recspace A) : term8 A NONE' option' a.
Proof. exact (fun h0 : term0 A NONE' option' a => @lem1069049 A NONE' option' a h0). Qed.
Lemma lem1069051 {A : Type'} (NONE' : recspace A) (option' : type1338 A) (a : recspace A) : term8 A NONE' option' a.
Proof. exact (fun h0 : term0 A NONE' option' a => @lem1069045 A NONE' option' a h0). Qed.
Lemma lem1069052 {A : Type'} (NONE' : recspace A) (option' : type1338 A) (a : recspace A) : term9 A NONE' option' a.
Proof. exact (conj (@lem1069051 A NONE' option' a) (@lem1069050 A NONE' option' a)). Qed.
Lemma lem1069053 {A : Type'} (NONE' : recspace A) (option' : type1338 A) (a : recspace A) : (term9 A NONE' option' a) = ((term0 A NONE' option' a) = (term0 A NONE' option' a)).
Proof. exact (@lem32 (term0 A NONE' option' a) (term0 A NONE' option' a)). Qed.
Lemma lem1069054 {A : Type'} (NONE' : recspace A) (option' : type1338 A) (a : recspace A) : (term0 A NONE' option' a) = (term0 A NONE' option' a).
Proof. exact (EQ_MP (@lem1069053 A NONE' option' a) (@lem1069052 A NONE' option' a)). Qed.
Lemma lem1069055 {A : Type'} (NONE' : recspace A) (option' : type1338 A) : (term10 A NONE' option') = (term10 A NONE' option').
Proof. exact (fun_ext (fun a : recspace A => @lem1069054 A NONE' option' a)). Qed.
Lemma lem1069056 {A : Type'} : (@all (recspace A)) = (@all (recspace A)).
Proof. exact (eq_refl (@all (recspace A))). Qed.
Lemma lem1069057 {A : Type'} (NONE' : recspace A) (option' : type1338 A) : (term1 A NONE' option') = (term1 A NONE' option').
Proof. exact (MK_COMB (@lem1069056 A) (@lem1069055 A NONE' option')). Qed.
Lemma lem1069058 {A : Type'} (NONE' : recspace A) (option' : type1338 A) : (option' NONE') = (term1 A NONE' option').
Proof. exact (TRANS (@lem1069038 A NONE' option') (@lem1069057 A NONE' option')). Qed.
Lemma lem1069059 {A : Type'} (a : recspace A) (SOME' : type1432 A) (a' : A) (h1 : a = (SOME' a')) : a = (SOME' a').
Proof. exact (h1). Qed.
Lemma lem1069060 {A : Type'} (option' : type1338 A) (SOME' : type1432 A) (h1 : term11 A option' SOME') : term11 A option' SOME'.
Proof. exact (h1). Qed.
Lemma lem1069061 {A : Type'} (a : A) (option' : type1338 A) (SOME' : type1432 A) (h1 : term11 A option' SOME') : term12 A option' SOME' a.
Proof. exact (@lem1069060 A option' SOME' h1 a). Qed.
Lemma lem1069062 {A : Type'} (option' : type1338 A) (SOME' : type1432 A) (a : A) : (term12 A option' SOME' a) = (term13 A option' SOME' a).
Proof. exact (eq_refl (term12 A option' SOME' a)). Qed.
Lemma lem1069063 {A : Type'} (a : A) (option' : type1338 A) (SOME' : type1432 A) (h1 : term11 A option' SOME') : term13 A option' SOME' a.
Proof. exact (EQ_MP (@lem1069062 A option' SOME' a) (@lem1069061 A a option' SOME' h1)). Qed.
Lemma lem1069064 {A : Type'} (option' : type1338 A) : option' = option'.
Proof. exact (eq_refl option'). Qed.
Lemma lem1069065 {A : Type'} (option' : type1338 A) (a : recspace A) (SOME' : type1432 A) (a' : A) (h1 : a = (SOME' a')) : (option' a) = (term13 A option' SOME' a').
Proof. exact (MK_COMB (@lem1069064 A option') (@lem1069059 A a SOME' a' h1)). Qed.
Lemma lem1069066 {A : Type'} (option' : type1338 A) (a : recspace A) (SOME' : type1432 A) (a' : A) (h1 : a = (SOME' a')) : (term13 A option' SOME' a') = (option' a).
Proof. exact (SYM (@lem1069065 A option' a SOME' a' h1)). Qed.
Lemma lem1069067 {A : Type'} (option' : type1338 A) (a : recspace A) (SOME' : type1432 A) (a' : A) (h1 : term11 A option' SOME') (h2 : a = (SOME' a')) : option' a.
Proof. exact (EQ_MP (@lem1069066 A option' a SOME' a' h2) (@lem1069063 A a' option' SOME' h1)). Qed.
Lemma lem1069068 {A : Type'} (a : A) (a' : recspace A) (option' : type1338 A) (SOME' : type1432 A) (h1 : term11 A option' SOME') : term14 A SOME' a option' a'.
Proof. exact (fun h0 : a' = (SOME' a) => @lem1069067 A option' a' SOME' a h1 h0). Qed.
Lemma lem1069069 {A : Type'} (a : recspace A) (SOME' : type1432 A) (a' : A) (h1 : a = (SOME' a')) : a = (SOME' a').
Proof. exact (h1). Qed.
Lemma lem1069070 {A : Type'} (option' : type1338 A) (a : recspace A) (SOME' : type1432 A) (a' : A) (h1 : term11 A option' SOME') (h2 : a = (SOME' a')) : option' a.
Proof. exact (@lem1069068 A a' a option' SOME' h1 (@lem1069069 A a SOME' a' h2)). Qed.
Lemma lem1069071 {A : Type'} (a : A) (a' : recspace A) (option' : type1338 A) (SOME' : type1432 A) (h1 : term11 A option' SOME') : term14 A SOME' a option' a'.
Proof. exact (fun h0 : a' = (SOME' a) => @lem1069070 A option' a' SOME' a h1 h0). Qed.
Lemma lem1069072 {A : Type'} (a : recspace A) (option' : type1338 A) (SOME' : type1432 A) (h1 : term11 A option' SOME') : term15 A SOME' option' a.
Proof. exact (fun a' : A => @lem1069071 A a' a option' SOME' h1). Qed.
Lemma lem1069073 {A : Type'} (option' : type1338 A) (SOME' : type1432 A) (h1 : term11 A option' SOME') : term16 A SOME' option'.
Proof. exact (fun a : recspace A => @lem1069072 A a option' SOME' h1). Qed.
Lemma lem1069074 {A : Type'} (SOME' : type1432 A) (option' : type1338 A) (h1 : term16 A SOME' option') : term16 A SOME' option'.
Proof. exact (h1). Qed.
Lemma lem1069075 {A : Type'} (a : A) (SOME' : type1432 A) (option' : type1338 A) (h1 : term16 A SOME' option') : term17 A option' SOME' a.
Proof. exact (@lem1069074 A SOME' option' h1 (SOME' a)). Qed.
Lemma lem1069076 {A : Type'} (option' : type1338 A) (SOME' : type1432 A) (a : A) : (term17 A option' SOME' a) = (term18 A option' SOME' a).
Proof. exact (eq_refl (term17 A option' SOME' a)). Qed.
Lemma lem1069077 {A : Type'} (a : A) (SOME' : type1432 A) (option' : type1338 A) (h1 : term16 A SOME' option') : term18 A option' SOME' a.
Proof. exact (EQ_MP (@lem1069076 A option' SOME' a) (@lem1069075 A a SOME' option' h1)). Qed.
Lemma lem1069078 {A : Type'} (a : A) (SOME' : type1432 A) (option' : type1338 A) (h1 : term16 A SOME' option') : term19 A option' SOME' a.
Proof. exact (@lem1069077 A a SOME' option' h1 a). Qed.
Lemma lem1069079 {A : Type'} (option' : type1338 A) (SOME' : type1432 A) (a : A) : (term19 A option' SOME' a) = (term20 A option' SOME' a).
Proof. exact (eq_refl (term19 A option' SOME' a)). Qed.
Lemma lem1069080 {A : Type'} (a : A) (SOME' : type1432 A) (option' : type1338 A) (h1 : term16 A SOME' option') : term20 A option' SOME' a.
Proof. exact (EQ_MP (@lem1069079 A option' SOME' a) (@lem1069078 A a SOME' option' h1)). Qed.
Lemma lem1069081 {A : Type'} (SOME' : type1432 A) (a : A) : (SOME' a) = (SOME' a).
Proof. exact (eq_refl (SOME' a)). Qed.
Lemma lem1069082 {A : Type'} (a : A) (SOME' : type1432 A) (option' : type1338 A) (h1 : term16 A SOME' option') : term13 A option' SOME' a.
Proof. exact (@lem1069080 A a SOME' option' h1 (@lem1069081 A SOME' a)). Qed.
Lemma lem1069083 {A : Type'} (SOME' : type1432 A) (option' : type1338 A) (h1 : term16 A SOME' option') : term11 A option' SOME'.
Proof. exact (fun a : A => @lem1069082 A a SOME' option' h1). Qed.
Lemma lem1069084 {A : Type'} (option' : type1338 A) (SOME' : type1432 A) : term21 A option' SOME'.
Proof. exact (fun h0 : term16 A SOME' option' => @lem1069083 A SOME' option' h0). Qed.
Lemma lem1069085 {A : Type'} (SOME' : type1432 A) (option' : type1338 A) : term22 A SOME' option'.
Proof. exact (fun h0 : term11 A option' SOME' => @lem1069073 A option' SOME' h0). Qed.
Lemma lem1069086 {A : Type'} (option' : type1338 A) (SOME' : type1432 A) : term23 A option' SOME'.
Proof. exact (conj (@lem1069085 A SOME' option') (@lem1069084 A option' SOME')). Qed.
Lemma lem1069087 {A : Type'} (SOME' : type1432 A) (option' : type1338 A) : (term23 A option' SOME') = ((term11 A option' SOME') = (term16 A SOME' option')).
Proof. exact (@lem32 (term11 A option' SOME') (term16 A SOME' option')). Qed.
Lemma lem1069088 {A : Type'} (SOME' : type1432 A) (option' : type1338 A) : (term11 A option' SOME') = (term16 A SOME' option').
Proof. exact (EQ_MP (@lem1069087 A SOME' option') (@lem1069086 A option' SOME')). Qed.
Lemma lem1069089 {A : Type'} (SOME' : type1432 A) (option' : type1338 A) (a : recspace A) (h1 : term15 A SOME' option' a) : term15 A SOME' option' a.
Proof. exact (h1). Qed.
Lemma lem1069090 {A : Type'} (a : A) (SOME' : type1432 A) (option' : type1338 A) (a' : recspace A) (h1 : term15 A SOME' option' a') : term24 A SOME' option' a' a.
Proof. exact (@lem1069089 A SOME' option' a' h1 a). Qed.
Lemma lem1069091 {A : Type'} (SOME' : type1432 A) (a : A) (option' : type1338 A) (a' : recspace A) : (term24 A SOME' option' a' a) = (term14 A SOME' a option' a').
Proof. exact (eq_refl (term24 A SOME' option' a' a)). Qed.
Lemma lem1069092 {A : Type'} (a : A) (SOME' : type1432 A) (option' : type1338 A) (a' : recspace A) (h1 : term15 A SOME' option' a') : term14 A SOME' a option' a'.
Proof. exact (EQ_MP (@lem1069091 A SOME' a option' a') (@lem1069090 A a SOME' option' a' h1)). Qed.
Lemma lem1069093 {A : Type'} (a : recspace A) (SOME' : type1432 A) (a' : A) (h1 : a = (SOME' a')) : a = (SOME' a').
Proof. exact (h1). Qed.
Lemma lem1069094 {A : Type'} (option' : type1338 A) (a : recspace A) (SOME' : type1432 A) (a' : A) (h1 : term15 A SOME' option' a) (h2 : a = (SOME' a')) : option' a.
Proof. exact (@lem1069092 A a' SOME' option' a h1 (@lem1069093 A a SOME' a' h2)). Qed.
Lemma lem1069095 {A : Type'} (option' : type1338 A) (a : recspace A) (SOME' : type1432 A) (a' : A) (h1 : a = (SOME' a')) : term25 A SOME' option' a.
Proof. exact (fun h0 : term15 A SOME' option' a => @lem1069094 A option' a SOME' a' h0 h1). Qed.
Lemma lem1069096 {A : Type'} (a : recspace A) (SOME' : type1432 A) (h1 : term26 A a SOME') : term26 A a SOME'.
Proof. exact (h1). Qed.
Lemma lem1069097 {A : Type'} (option' : type1338 A) (a : recspace A) (SOME' : type1432 A) (h1 : term26 A a SOME') : term25 A SOME' option' a.
Proof. exact (ex_elim (@lem1069096 A a SOME' h1) (fun a' : A => fun h0 : term27 A a SOME' a' => @lem1069095 A option' a SOME' a' h0)). Qed.
Lemma lem1069098 {A : Type'} (SOME' : type1432 A) (option' : type1338 A) (a : recspace A) (h1 : term15 A SOME' option' a) : term15 A SOME' option' a.
Proof. exact (h1). Qed.
Lemma lem1069099 {A : Type'} (option' : type1338 A) (a : recspace A) (SOME' : type1432 A) (h1 : term15 A SOME' option' a) (h2 : term26 A a SOME') : option' a.
Proof. exact (@lem1069097 A option' a SOME' h2 (@lem1069098 A SOME' option' a h1)). Qed.
Lemma lem1069100 {A : Type'} (SOME' : type1432 A) (option' : type1338 A) (a : recspace A) (h1 : term15 A SOME' option' a) : term28 A SOME' option' a.
Proof. exact (fun h0 : term26 A a SOME' => @lem1069099 A option' a SOME' h1 h0). Qed.
Lemma lem1069101 {A : Type'} (SOME' : type1432 A) (option' : type1338 A) (a : recspace A) (h1 : term28 A SOME' option' a) : term28 A SOME' option' a.
Proof. exact (h1). Qed.
Lemma lem1069102 {A : Type'} (a : recspace A) (SOME' : type1432 A) (a' : A) (h1 : a = (SOME' a')) : a = (SOME' a').
Proof. exact (h1). Qed.
Lemma lem1069103 {A : Type'} (a : recspace A) (SOME' : type1432 A) (a' : A) (h1 : a = (SOME' a')) : term26 A a SOME'.
Proof. exact (ex_intro (term27 A a SOME') a' (@lem1069102 A a SOME' a' h1)). Qed.
Lemma lem1069104 {A : Type'} (a : A) (SOME' : type1432 A) (option' : type1338 A) (a' : recspace A) (h1 : a' = (SOME' a)) (h2 : term28 A SOME' option' a') : option' a'.
Proof. exact (@lem1069101 A SOME' option' a' h2 (@lem1069103 A a' SOME' a h1)). Qed.
Lemma lem1069105 {A : Type'} (a : A) (SOME' : type1432 A) (option' : type1338 A) (a' : recspace A) (h1 : term28 A SOME' option' a') : term14 A SOME' a option' a'.
Proof. exact (fun h0 : a' = (SOME' a) => @lem1069104 A a SOME' option' a' h0 h1). Qed.
Lemma lem1069106 {A : Type'} (SOME' : type1432 A) (option' : type1338 A) (a : recspace A) (h1 : term28 A SOME' option' a) : term15 A SOME' option' a.
Proof. exact (fun a' : A => @lem1069105 A a' SOME' option' a h1). Qed.
Lemma lem1069107 {A : Type'} (SOME' : type1432 A) (option' : type1338 A) (a : recspace A) : term29 A SOME' option' a.
Proof. exact (fun h0 : term28 A SOME' option' a => @lem1069106 A SOME' option' a h0). Qed.
Lemma lem1069108 {A : Type'} (SOME' : type1432 A) (option' : type1338 A) (a : recspace A) : term30 A SOME' option' a.
Proof. exact (fun h0 : term15 A SOME' option' a => @lem1069100 A SOME' option' a h0). Qed.
Lemma lem1069109 {A : Type'} (SOME' : type1432 A) (option' : type1338 A) (a : recspace A) : term31 A SOME' option' a.
Proof. exact (conj (@lem1069108 A SOME' option' a) (@lem1069107 A SOME' option' a)). Qed.
Lemma lem1069110 {A : Type'} (SOME' : type1432 A) (option' : type1338 A) (a : recspace A) : (term31 A SOME' option' a) = ((term15 A SOME' option' a) = (term28 A SOME' option' a)).
Proof. exact (@lem32 (term15 A SOME' option' a) (term28 A SOME' option' a)). Qed.
Lemma lem1069111 {A : Type'} (SOME' : type1432 A) (option' : type1338 A) (a : recspace A) : (term15 A SOME' option' a) = (term28 A SOME' option' a).
Proof. exact (EQ_MP (@lem1069110 A SOME' option' a) (@lem1069109 A SOME' option' a)). Qed.
Lemma lem1069112 {A : Type'} (SOME' : type1432 A) (option' : type1338 A) : (term32 A SOME' option') = (term33 A SOME' option').
Proof. exact (fun_ext (fun a : recspace A => @lem1069111 A SOME' option' a)). Qed.
Lemma lem1069113 {A : Type'} : (@all (recspace A)) = (@all (recspace A)).
Proof. exact (eq_refl (@all (recspace A))). Qed.
Lemma lem1069114 {A : Type'} (SOME' : type1432 A) (option' : type1338 A) : (term16 A SOME' option') = (term34 A SOME' option').
Proof. exact (MK_COMB (@lem1069113 A) (@lem1069112 A SOME' option')). Qed.
Lemma lem1069115 {A : Type'} (SOME' : type1432 A) (option' : type1338 A) : (term11 A option' SOME') = (term34 A SOME' option').
Proof. exact (TRANS (@lem1069088 A SOME' option') (@lem1069114 A SOME' option')). Qed.
Lemma lem1069117 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem9104 A x) (@lem9103 A x)). Qed.
Lemma lem1069118 (x : Prop) : (x = x) = True.
Proof. exact (@lem1069117 Prop x). Qed.
Lemma lem1069119 {A : Type'} (NONE' : recspace A) (SOME' : type1432 A) (option' : type1338 A) : ((term35 A NONE' SOME' option') = (term35 A NONE' SOME' option')) = True.
Proof. exact (@lem1069118 (term35 A NONE' SOME' option')). Qed.
Lemma lem1069120 {A : Type'} (NONE' : recspace A) (SOME' : type1432 A) (option' : type1338 A) : True = ((term35 A NONE' SOME' option') = (term35 A NONE' SOME' option')).
Proof. exact (SYM (@lem1069119 A NONE' SOME' option')). Qed.
Lemma lem1069121 {A : Type'} (NONE' : recspace A) (SOME' : type1432 A) (option' : type1338 A) : (term35 A NONE' SOME' option') = (term35 A NONE' SOME' option').
Proof. exact (EQ_MP (@lem1069120 A NONE' SOME' option') (@lem0)). Qed.
Lemma lem1069122 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1069123 {A : Type'} (NONE' : recspace A) (option' : type1338 A) : (term36 A option' NONE') = (term37 A NONE' option').
Proof. exact (MK_COMB (@lem1069122) (@lem1069058 A NONE' option')). Qed.
Lemma lem1069124 {A : Type'} (NONE' : recspace A) (SOME' : type1432 A) (option' : type1338 A) : (term38 A NONE' option' SOME') = (term35 A NONE' SOME' option').
Proof. exact (MK_COMB (@lem1069123 A NONE' option') (@lem1069115 A SOME' option')). Qed.
Lemma lem1069125 {A : Type'} (NONE' : recspace A) (SOME' : type1432 A) (option' : type1338 A) : (term38 A NONE' option' SOME') = (term35 A NONE' SOME' option').
Proof. exact (TRANS (@lem1069124 A NONE' SOME' option') (@lem1069121 A NONE' SOME' option')). Qed.
Lemma lem1069126 {A : Type'} (NONE' : recspace A) (SOME' : type1432 A) (option' : type1338 A) (h1 : term35 A NONE' SOME' option') : term35 A NONE' SOME' option'.
Proof. exact (h1). Qed.
Lemma lem1069127 {A : Type'} (NONE' : recspace A) (SOME' : type1432 A) (option' : type1338 A) (h1 : term35 A NONE' SOME' option') : term34 A SOME' option'.
Proof. exact (proj2 (@lem1069126 A NONE' SOME' option' h1)). Qed.
Lemma lem1069128 {A : Type'} (NONE' : recspace A) (SOME' : type1432 A) (option' : type1338 A) (h1 : term35 A NONE' SOME' option') : term1 A NONE' option'.
Proof. exact (proj1 (@lem1069126 A NONE' SOME' option' h1)). Qed.
Lemma lem1069129 {A : Type'} (a : recspace A) (NONE' : recspace A) (SOME' : type1432 A) (option' : type1338 A) (h1 : term35 A NONE' SOME' option') : term39 A NONE' option' a.
Proof. exact (@lem1069128 A NONE' SOME' option' h1 a). Qed.
Lemma lem1069130 {A : Type'} (NONE' : recspace A) (option' : type1338 A) (a : recspace A) : (term39 A NONE' option' a) = (term0 A NONE' option' a).
Proof. exact (eq_refl (term39 A NONE' option' a)). Qed.
Lemma lem1069131 {A : Type'} (a : recspace A) (NONE' : recspace A) (SOME' : type1432 A) (option' : type1338 A) (h1 : term35 A NONE' SOME' option') : term0 A NONE' option' a.
Proof. exact (EQ_MP (@lem1069130 A NONE' option' a) (@lem1069129 A a NONE' SOME' option' h1)). Qed.
Lemma lem1069132 {A : Type'} (a : recspace A) (NONE' : recspace A) (h1 : a = NONE') : a = NONE'.
Proof. exact (h1). Qed.
Lemma lem1069133 {A : Type'} (SOME' : type1432 A) (option' : type1338 A) (a : recspace A) (NONE' : recspace A) (h1 : term35 A NONE' SOME' option') (h2 : a = NONE') : option' a.
Proof. exact (@lem1069131 A a NONE' SOME' option' h1 (@lem1069132 A a NONE' h2)). Qed.
Lemma lem1069134 {A : Type'} (SOME' : type1432 A) (option' : type1338 A) (a : recspace A) (NONE' : recspace A) (h1 : a = NONE') : term40 A NONE' SOME' option' a.
Proof. exact (fun h0 : term35 A NONE' SOME' option' => @lem1069133 A SOME' option' a NONE' h0 h1). Qed.
Lemma lem1069135 {A : Type'} (a : recspace A) (NONE' : recspace A) (SOME' : type1432 A) (option' : type1338 A) (h1 : term35 A NONE' SOME' option') : term41 A SOME' option' a.
Proof. exact (@lem1069127 A NONE' SOME' option' h1 a). Qed.
Lemma lem1069136 {A : Type'} (SOME' : type1432 A) (option' : type1338 A) (a : recspace A) : (term41 A SOME' option' a) = (term28 A SOME' option' a).
Proof. exact (eq_refl (term41 A SOME' option' a)). Qed.
Lemma lem1069137 {A : Type'} (a : recspace A) (NONE' : recspace A) (SOME' : type1432 A) (option' : type1338 A) (h1 : term35 A NONE' SOME' option') : term28 A SOME' option' a.
Proof. exact (EQ_MP (@lem1069136 A SOME' option' a) (@lem1069135 A a NONE' SOME' option' h1)). Qed.
Lemma lem1069138 {A : Type'} (a : recspace A) (SOME' : type1432 A) (h1 : term26 A a SOME') : term26 A a SOME'.
Proof. exact (h1). Qed.
Lemma lem1069139 {A : Type'} (a : recspace A) (NONE' : recspace A) (SOME' : type1432 A) (option' : type1338 A) (h1 : term26 A a SOME') (h2 : term35 A NONE' SOME' option') : option' a.
Proof. exact (@lem1069137 A a NONE' SOME' option' h2 (@lem1069138 A a SOME' h1)). Qed.
Lemma lem1069140 {A : Type'} (NONE' : recspace A) (option' : type1338 A) (a : recspace A) (SOME' : type1432 A) (h1 : term26 A a SOME') : term40 A NONE' SOME' option' a.
Proof. exact (fun h0 : term35 A NONE' SOME' option' => @lem1069139 A a NONE' SOME' option' h1 h0). Qed.
Lemma lem1069141 {A : Type'} (NONE' : recspace A) (a : recspace A) (SOME' : type1432 A) (h1 : term42 A NONE' a SOME') : term42 A NONE' a SOME'.
Proof. exact (h1). Qed.
Lemma lem1069142 {A : Type'} (option' : type1338 A) (NONE' : recspace A) (a : recspace A) (SOME' : type1432 A) (h1 : term42 A NONE' a SOME') : term40 A NONE' SOME' option' a.
Proof. exact (or_elim (@lem1069141 A NONE' a SOME' h1) (fun h0 : a = NONE' => @lem1069134 A SOME' option' a NONE' h0) (fun h0 : term26 A a SOME' => @lem1069140 A NONE' option' a SOME' h0)). Qed.
Lemma lem1069143 {A : Type'} (NONE' : recspace A) (SOME' : type1432 A) (option' : type1338 A) (h1 : term35 A NONE' SOME' option') : term35 A NONE' SOME' option'.
Proof. exact (h1). Qed.
Lemma lem1069144 {A : Type'} (option' : type1338 A) (NONE' : recspace A) (a : recspace A) (SOME' : type1432 A) (h1 : term35 A NONE' SOME' option') (h2 : term42 A NONE' a SOME') : option' a.
Proof. exact (@lem1069142 A option' NONE' a SOME' h2 (@lem1069143 A NONE' SOME' option' h1)). Qed.
Lemma lem1069145 {A : Type'} (a : recspace A) (NONE' : recspace A) (SOME' : type1432 A) (option' : type1338 A) (h1 : term35 A NONE' SOME' option') : term43 A NONE' SOME' option' a.
Proof. exact (fun h0 : term42 A NONE' a SOME' => @lem1069144 A option' NONE' a SOME' h1 h0). Qed.
Lemma lem1069146 {A : Type'} (NONE' : recspace A) (SOME' : type1432 A) (option' : type1338 A) (h1 : term35 A NONE' SOME' option') : term44 A NONE' SOME' option'.
Proof. exact (fun a : recspace A => @lem1069145 A a NONE' SOME' option' h1). Qed.
Lemma lem1069147 {A : Type'} (NONE' : recspace A) (SOME' : type1432 A) (option' : type1338 A) (h1 : term44 A NONE' SOME' option') : term44 A NONE' SOME' option'.
Proof. exact (h1). Qed.
Lemma lem1069148 {A : Type'} (a : recspace A) (NONE' : recspace A) (SOME' : type1432 A) (option' : type1338 A) (h1 : term44 A NONE' SOME' option') : term45 A NONE' SOME' option' a.
Proof. exact (@lem1069147 A NONE' SOME' option' h1 a). Qed.
Lemma lem1069149 {A : Type'} (NONE' : recspace A) (SOME' : type1432 A) (option' : type1338 A) (a : recspace A) : (term45 A NONE' SOME' option' a) = (term43 A NONE' SOME' option' a).
Proof. exact (eq_refl (term45 A NONE' SOME' option' a)). Qed.
Lemma lem1069150 {A : Type'} (a : recspace A) (NONE' : recspace A) (SOME' : type1432 A) (option' : type1338 A) (h1 : term44 A NONE' SOME' option') : term43 A NONE' SOME' option' a.
Proof. exact (EQ_MP (@lem1069149 A NONE' SOME' option' a) (@lem1069148 A a NONE' SOME' option' h1)). Qed.
Lemma lem1069151 {A : Type'} (NONE' : recspace A) (a : recspace A) (SOME' : type1432 A) (h1 : term42 A NONE' a SOME') : term42 A NONE' a SOME'.
Proof. exact (h1). Qed.
Lemma lem1069152 {A : Type'} (option' : type1338 A) (NONE' : recspace A) (a : recspace A) (SOME' : type1432 A) (h1 : term44 A NONE' SOME' option') (h2 : term42 A NONE' a SOME') : option' a.
Proof. exact (@lem1069150 A a NONE' SOME' option' h1 (@lem1069151 A NONE' a SOME' h2)). Qed.
Lemma lem1069153 {A : Type'} (option' : type1338 A) (NONE' : recspace A) (a : recspace A) (SOME' : type1432 A) (h1 : term42 A NONE' a SOME') : term46 A NONE' SOME' option' a.
Proof. exact (fun h0 : term44 A NONE' SOME' option' => @lem1069152 A option' NONE' a SOME' h0 h1). Qed.
Lemma lem1069154 {A : Type'} (a : recspace A) (SOME' : type1432 A) (h1 : term26 A a SOME') : term26 A a SOME'.
Proof. exact (h1). Qed.
Lemma lem1069155 {A : Type'} (NONE' : recspace A) (a : recspace A) (SOME' : type1432 A) (h1 : term26 A a SOME') : term42 A NONE' a SOME'.
Proof. exact (or_intro2 (a = NONE') (@lem1069154 A a SOME' h1)). Qed.
Lemma lem1069156 {A : Type'} (NONE' : recspace A) (option' : type1338 A) (a : recspace A) (SOME' : type1432 A) (h1 : term26 A a SOME') : (term42 A NONE' a SOME') = (term46 A NONE' SOME' option' a).
Proof. exact (prop_ext (fun h2 : term42 A NONE' a SOME' => @lem1069153 A option' NONE' a SOME' h2) (fun h2 : term46 A NONE' SOME' option' a => @lem1069155 A NONE' a SOME' h1)). Qed.
Lemma lem1069157 {A : Type'} (NONE' : recspace A) (option' : type1338 A) (a : recspace A) (SOME' : type1432 A) (h1 : term26 A a SOME') : term46 A NONE' SOME' option' a.
Proof. exact (EQ_MP (@lem1069156 A NONE' option' a SOME' h1) (@lem1069155 A NONE' a SOME' h1)). Qed.
Lemma lem1069158 {A : Type'} (a : recspace A) (NONE' : recspace A) (h1 : a = NONE') : a = NONE'.
Proof. exact (h1). Qed.
Lemma lem1069159 {A : Type'} (SOME' : type1432 A) (a : recspace A) (NONE' : recspace A) (h1 : a = NONE') : term42 A NONE' a SOME'.
Proof. exact (or_intro1 (@lem1069158 A a NONE' h1) (term26 A a SOME')). Qed.
Lemma lem1069160 {A : Type'} (SOME' : type1432 A) (option' : type1338 A) (a : recspace A) (NONE' : recspace A) (h1 : a = NONE') : (term42 A NONE' a SOME') = (term46 A NONE' SOME' option' a).
Proof. exact (prop_ext (fun h2 : term42 A NONE' a SOME' => @lem1069153 A option' NONE' a SOME' h2) (fun h2 : term46 A NONE' SOME' option' a => @lem1069159 A SOME' a NONE' h1)). Qed.
Lemma lem1069161 {A : Type'} (SOME' : type1432 A) (option' : type1338 A) (a : recspace A) (NONE' : recspace A) (h1 : a = NONE') : term46 A NONE' SOME' option' a.
Proof. exact (EQ_MP (@lem1069160 A SOME' option' a NONE' h1) (@lem1069159 A SOME' a NONE' h1)). Qed.
Lemma lem1069162 {A : Type'} (NONE' : recspace A) (SOME' : type1432 A) (option' : type1338 A) (h1 : term44 A NONE' SOME' option') : term44 A NONE' SOME' option'.
Proof. exact (h1). Qed.
Lemma lem1069163 {A : Type'} (NONE' : recspace A) (option' : type1338 A) (a : recspace A) (SOME' : type1432 A) (h1 : term44 A NONE' SOME' option') (h2 : term26 A a SOME') : option' a.
Proof. exact (@lem1069157 A NONE' option' a SOME' h2 (@lem1069162 A NONE' SOME' option' h1)). Qed.
Lemma lem1069164 {A : Type'} (a : recspace A) (NONE' : recspace A) (SOME' : type1432 A) (option' : type1338 A) (h1 : term44 A NONE' SOME' option') : term28 A SOME' option' a.
Proof. exact (fun h0 : term26 A a SOME' => @lem1069163 A NONE' option' a SOME' h1 h0). Qed.
Lemma lem1069165 {A : Type'} (NONE' : recspace A) (SOME' : type1432 A) (option' : type1338 A) (h1 : term44 A NONE' SOME' option') : term34 A SOME' option'.
Proof. exact (fun a : recspace A => @lem1069164 A a NONE' SOME' option' h1). Qed.
Lemma lem1069166 {A : Type'} (NONE' : recspace A) (SOME' : type1432 A) (option' : type1338 A) (h1 : term44 A NONE' SOME' option') : term44 A NONE' SOME' option'.
Proof. exact (h1). Qed.
Lemma lem1069167 {A : Type'} (SOME' : type1432 A) (option' : type1338 A) (a : recspace A) (NONE' : recspace A) (h1 : term44 A NONE' SOME' option') (h2 : a = NONE') : option' a.
Proof. exact (@lem1069161 A SOME' option' a NONE' h2 (@lem1069166 A NONE' SOME' option' h1)). Qed.
Lemma lem1069168 {A : Type'} (a : recspace A) (NONE' : recspace A) (SOME' : type1432 A) (option' : type1338 A) (h1 : term44 A NONE' SOME' option') : term0 A NONE' option' a.
Proof. exact (fun h0 : a = NONE' => @lem1069167 A SOME' option' a NONE' h1 h0). Qed.
Lemma lem1069169 {A : Type'} (NONE' : recspace A) (SOME' : type1432 A) (option' : type1338 A) (h1 : term44 A NONE' SOME' option') : term1 A NONE' option'.
Proof. exact (fun a : recspace A => @lem1069168 A a NONE' SOME' option' h1). Qed.
Lemma lem1069170 {A : Type'} (NONE' : recspace A) (SOME' : type1432 A) (option' : type1338 A) (h1 : term44 A NONE' SOME' option') : term35 A NONE' SOME' option'.
Proof. exact (conj (@lem1069169 A NONE' SOME' option' h1) (@lem1069165 A NONE' SOME' option' h1)). Qed.
Lemma lem1069171 {A : Type'} (NONE' : recspace A) (SOME' : type1432 A) (option' : type1338 A) : term47 A NONE' SOME' option'.
Proof. exact (fun h0 : term44 A NONE' SOME' option' => @lem1069170 A NONE' SOME' option' h0). Qed.
Lemma lem1069172 {A : Type'} (NONE' : recspace A) (SOME' : type1432 A) (option' : type1338 A) : term48 A NONE' SOME' option'.
Proof. exact (fun h0 : term35 A NONE' SOME' option' => @lem1069146 A NONE' SOME' option' h0). Qed.
Lemma lem1069173 {A : Type'} (NONE' : recspace A) (SOME' : type1432 A) (option' : type1338 A) : term49 A NONE' SOME' option'.
Proof. exact (conj (@lem1069172 A NONE' SOME' option') (@lem1069171 A NONE' SOME' option')). Qed.
Lemma lem1069174 {A : Type'} (NONE' : recspace A) (SOME' : type1432 A) (option' : type1338 A) : (term49 A NONE' SOME' option') = ((term35 A NONE' SOME' option') = (term44 A NONE' SOME' option')).
Proof. exact (@lem32 (term35 A NONE' SOME' option') (term44 A NONE' SOME' option')). Qed.
Lemma lem1069175 {A : Type'} (NONE' : recspace A) (SOME' : type1432 A) (option' : type1338 A) : (term35 A NONE' SOME' option') = (term44 A NONE' SOME' option').
Proof. exact (EQ_MP (@lem1069174 A NONE' SOME' option') (@lem1069173 A NONE' SOME' option')). Qed.
Lemma lem1069176 {A : Type'} (NONE' : recspace A) (SOME' : type1432 A) (option' : type1338 A) : (term38 A NONE' option' SOME') = (term44 A NONE' SOME' option').
Proof. exact (TRANS (@lem1069125 A NONE' SOME' option') (@lem1069175 A NONE' SOME' option')). Qed.
Lemma lem1069177 {A : Type'} (NONE' : recspace A) (option' : type1338 A) (SOME' : type1432 A) : (term44 A NONE' SOME' option') = (term38 A NONE' option' SOME').
Proof. exact (SYM (@lem1069176 A NONE' SOME' option')). Qed.
Lemma lem1069178 {A : Type'} (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : option' = (term50 A NONE' SOME')) : option' = (term50 A NONE' SOME').
Proof. exact (h1). Qed.
Lemma lem1069179 {A : Type'} (a : recspace A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1069180 {A : Type'} (a : recspace A) (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : option' = (term50 A NONE' SOME')) : (option' a) = (term51 A NONE' SOME' a).
Proof. exact (MK_COMB (@lem1069178 A option' NONE' SOME' h1) (@lem1069179 A a)). Qed.
Lemma lem1069181 {A : Type'} (NONE' : recspace A) (SOME' : type1432 A) (a : recspace A) : (term51 A NONE' SOME' a) = (term52 A NONE' SOME' a).
Proof. exact (eq_refl (term51 A NONE' SOME' a)). Qed.
Lemma lem1069182 {A : Type'} (option' : type1338 A) (a : recspace A) : (term53 A option' a) = (term53 A option' a).
Proof. exact (eq_refl (term53 A option' a)). Qed.
Lemma lem1069183 {A : Type'} (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (a : recspace A) : ((option' a) = (term51 A NONE' SOME' a)) = ((option' a) = (term52 A NONE' SOME' a)).
Proof. exact (MK_COMB (@lem1069182 A option' a) (@lem1069181 A NONE' SOME' a)). Qed.
Lemma lem1069184 {A : Type'} (a : recspace A) (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : option' = (term50 A NONE' SOME')) : (option' a) = (term52 A NONE' SOME' a).
Proof. exact (EQ_MP (@lem1069183 A option' NONE' SOME' a) (@lem1069180 A a option' NONE' SOME' h1)). Qed.
Lemma lem1069185 {A : Type'} (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : option' = (term50 A NONE' SOME')) : term54 A option' NONE' SOME'.
Proof. exact (fun a : recspace A => @lem1069184 A a option' NONE' SOME' h1). Qed.
Lemma lem1069186 {A : Type'} (a : recspace A) (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : option' = (term50 A NONE' SOME')) : term55 A option' NONE' SOME' a.
Proof. exact (@lem1069185 A option' NONE' SOME' h1 a). Qed.
Lemma lem1069187 {A : Type'} (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (a : recspace A) : (term55 A option' NONE' SOME' a) = ((option' a) = (term52 A NONE' SOME' a)).
Proof. exact (eq_refl (term55 A option' NONE' SOME' a)). Qed.
Lemma lem1069188 {A : Type'} (a : recspace A) (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : option' = (term50 A NONE' SOME')) : (option' a) = (term52 A NONE' SOME' a).
Proof. exact (EQ_MP (@lem1069187 A option' NONE' SOME' a) (@lem1069186 A a option' NONE' SOME' h1)). Qed.
Lemma lem1069191 {A : Type'} (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (a : recspace A) : term56 A option' NONE' SOME' a.
Proof. exact (@lem37 (option' a) (term52 A NONE' SOME' a)). Qed.
Lemma lem1069192 {A : Type'} (a : recspace A) (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : option' = (term50 A NONE' SOME')) : term57 A option' NONE' SOME' a.
Proof. exact (@lem1069191 A option' NONE' SOME' a (@lem1069188 A a option' NONE' SOME' h1)). Qed.
Lemma lem1069193 {A : Type'} (option' : type1338 A) (a : recspace A) (h1 : option' a) : option' a.
Proof. exact (h1). Qed.
Lemma lem1069194 {A : Type'} (a : recspace A) (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : option' a) (h2 : option' = (term50 A NONE' SOME')) : term52 A NONE' SOME' a.
Proof. exact (@lem1069192 A a option' NONE' SOME' h2 (@lem1069193 A option' a h1)). Qed.
Lemma lem1069195 {A : Type'} (option' : type1338 A) (a : recspace A) (option'' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : option'' a) (h2 : option'' = (term50 A NONE' SOME')) : term58 A NONE' SOME' a option'.
Proof. exact (@lem1069194 A a option'' NONE' SOME' h1 h2 option'). Qed.
Lemma lem1069196 {A : Type'} (NONE' : recspace A) (SOME' : type1432 A) (option' : type1338 A) (a : recspace A) : (term58 A NONE' SOME' a option') = (term46 A NONE' SOME' option' a).
Proof. exact (eq_refl (term58 A NONE' SOME' a option')). Qed.
Lemma lem1069197 {A : Type'} (option' : type1338 A) (a : recspace A) (option'' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : option'' a) (h2 : option'' = (term50 A NONE' SOME')) : term46 A NONE' SOME' option' a.
Proof. exact (EQ_MP (@lem1069196 A NONE' SOME' option' a) (@lem1069195 A option' a option'' NONE' SOME' h1 h2)). Qed.
Lemma lem1069198 {A : Type'} (NONE' : recspace A) (SOME' : type1432 A) (option' : type1338 A) (h1 : term44 A NONE' SOME' option') : term44 A NONE' SOME' option'.
Proof. exact (h1). Qed.
Lemma lem1069199 {A : Type'} (option' : type1338 A) (a : recspace A) (option'' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : term44 A NONE' SOME' option') (h2 : option'' a) (h3 : option'' = (term50 A NONE' SOME')) : option' a.
Proof. exact (@lem1069197 A option' a option'' NONE' SOME' h2 h3 (@lem1069198 A NONE' SOME' option' h1)). Qed.
Lemma lem1069200 {A : Type'} (a : recspace A) (option' : type1338 A) (option'' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : term44 A NONE' SOME' option') (h2 : option'' = (term50 A NONE' SOME')) : term59 A option'' option' a.
Proof. exact (fun h0 : option'' a => @lem1069199 A option' a option'' NONE' SOME' h1 h0 h2). Qed.
Lemma lem1069201 {A : Type'} (option' : type1338 A) (option'' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : term44 A NONE' SOME' option') (h2 : option'' = (term50 A NONE' SOME')) : term60 A option'' option'.
Proof. exact (fun a : recspace A => @lem1069200 A a option' option'' NONE' SOME' h1 h2). Qed.
Lemma lem1069202 {A : Type'} (option' : type1338 A) (option'' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : option'' = (term50 A NONE' SOME')) : term61 A NONE' SOME' option'' option'.
Proof. exact (fun h0 : term44 A NONE' SOME' option' => @lem1069201 A option' option'' NONE' SOME' h0 h1). Qed.
Lemma lem1069203 {A : Type'} (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : option' = (term50 A NONE' SOME')) : term62 A NONE' SOME' option'.
Proof. exact (fun option'' : type1338 A => @lem1069202 A option'' option' NONE' SOME' h1). Qed.
Lemma lem1069204 {A : Type'} (NONE' : recspace A) (SOME' : type1432 A) (h1 : term63 A NONE' SOME') : term63 A NONE' SOME'.
Proof. exact (h1). Qed.
Lemma lem1069205 {A : Type'} (NONE' : recspace A) (SOME' : type1432 A) (option' : type1338 A) (h1 : term44 A NONE' SOME' option') : term44 A NONE' SOME' option'.
Proof. exact (h1). Qed.
Lemma lem1069206 {A : Type'} (option' : type1338 A) (option'' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : option'' = (term50 A NONE' SOME')) : term64 A NONE' SOME' option'' option'.
Proof. exact (@lem1069203 A option'' NONE' SOME' h1 option'). Qed.
Lemma lem1069207 {A : Type'} (NONE' : recspace A) (SOME' : type1432 A) (option' : type1338 A) (option'' : type1338 A) : (term64 A NONE' SOME' option' option'') = (term61 A NONE' SOME' option' option'').
Proof. exact (eq_refl (term64 A NONE' SOME' option' option'')). Qed.
Lemma lem1069208 {A : Type'} (option' : type1338 A) (option'' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : option'' = (term50 A NONE' SOME')) : term61 A NONE' SOME' option'' option'.
Proof. exact (EQ_MP (@lem1069207 A NONE' SOME' option'' option') (@lem1069206 A option' option'' NONE' SOME' h1)). Qed.
Lemma lem1069209 {A : Type'} (option' : type1338 A) (option'' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : term44 A NONE' SOME' option') (h2 : option'' = (term50 A NONE' SOME')) : term60 A option'' option'.
Proof. exact (@lem1069208 A option' option'' NONE' SOME' h2 (@lem1069205 A NONE' SOME' option' h1)). Qed.
Lemma lem1069210 {A : Type'} (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : term63 A NONE' SOME') : term65 A NONE' SOME' option'.
Proof. exact (@lem1069204 A NONE' SOME' h1 option'). Qed.
Lemma lem1069211 {A : Type'} (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) : (term65 A NONE' SOME' option') = (term66 A option' NONE' SOME').
Proof. exact (eq_refl (term65 A NONE' SOME' option')). Qed.
Lemma lem1069212 {A : Type'} (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : term63 A NONE' SOME') : term66 A option' NONE' SOME'.
Proof. exact (EQ_MP (@lem1069211 A option' NONE' SOME') (@lem1069210 A option' NONE' SOME' h1)). Qed.
Lemma lem1069213 {A : Type'} (option' : type1338 A) (option'' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : term63 A NONE' SOME') : term67 A option' NONE' SOME' option''.
Proof. exact (@lem1069212 A option' NONE' SOME' h1 option''). Qed.
Lemma lem1069214 {A : Type'} (option' : type1338 A) (option'' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) : (term67 A option' NONE' SOME' option'') = (term68 A option' option'' NONE' SOME').
Proof. exact (eq_refl (term67 A option' NONE' SOME' option'')). Qed.
Lemma lem1069215 {A : Type'} (option' : type1338 A) (option'' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : term63 A NONE' SOME') : term68 A option' option'' NONE' SOME'.
Proof. exact (EQ_MP (@lem1069214 A option' option'' NONE' SOME') (@lem1069213 A option' option'' NONE' SOME' h1)). Qed.
Lemma lem1069216 {A : Type'} (option' : type1338 A) (option'' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : term63 A NONE' SOME') (h2 : term44 A NONE' SOME' option') (h3 : option'' = (term50 A NONE' SOME')) : term69 A NONE' SOME'.
Proof. exact (@lem1069215 A option'' option' NONE' SOME' h1 (@lem1069209 A option' option'' NONE' SOME' h2 h3)). Qed.
Lemma lem1069217 {A : Type'} (a : recspace A) (NONE' : recspace A) (SOME' : type1432 A) (option' : type1338 A) (h1 : term44 A NONE' SOME' option') : term45 A NONE' SOME' option' a.
Proof. exact (@lem1069205 A NONE' SOME' option' h1 a). Qed.
Lemma lem1069218 {A : Type'} (NONE' : recspace A) (SOME' : type1432 A) (option' : type1338 A) (a : recspace A) : (term45 A NONE' SOME' option' a) = (term43 A NONE' SOME' option' a).
Proof. exact (eq_refl (term45 A NONE' SOME' option' a)). Qed.
Lemma lem1069219 {A : Type'} (a : recspace A) (NONE' : recspace A) (SOME' : type1432 A) (option' : type1338 A) (h1 : term44 A NONE' SOME' option') : term43 A NONE' SOME' option' a.
Proof. exact (EQ_MP (@lem1069218 A NONE' SOME' option' a) (@lem1069217 A a NONE' SOME' option' h1)). Qed.
Lemma lem1069220 {A : Type'} (a : recspace A) (option' : type1338 A) (option'' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : term63 A NONE' SOME') (h2 : term44 A NONE' SOME' option') (h3 : option'' = (term50 A NONE' SOME')) : term70 A NONE' SOME' a.
Proof. exact (@lem1069216 A option' option'' NONE' SOME' h1 h2 h3 a). Qed.
Lemma lem1069221 {A : Type'} (NONE' : recspace A) (a : recspace A) (SOME' : type1432 A) : (term70 A NONE' SOME' a) = (term71 A NONE' a SOME').
Proof. exact (eq_refl (term70 A NONE' SOME' a)). Qed.
Lemma lem1069222 {A : Type'} (a : recspace A) (option' : type1338 A) (option'' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : term63 A NONE' SOME') (h2 : term44 A NONE' SOME' option') (h3 : option'' = (term50 A NONE' SOME')) : term71 A NONE' a SOME'.
Proof. exact (EQ_MP (@lem1069221 A NONE' a SOME') (@lem1069220 A a option' option'' NONE' SOME' h1 h2 h3)). Qed.
Lemma lem1069223 {A : Type'} (NONE' : recspace A) (SOME' : type1432 A) (option' : type1338 A) (a : recspace A) : term72 A NONE' SOME' option' a.
Proof. exact (@lem51 (term42 A NONE' a SOME') (term42 A NONE' a SOME') (option' a)). Qed.
Lemma lem1069224 {A : Type'} (a : recspace A) (option' : type1338 A) (option'' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : term63 A NONE' SOME') (h2 : term44 A NONE' SOME' option') (h3 : option'' = (term50 A NONE' SOME')) : term73 A NONE' SOME' option' a.
Proof. exact (@lem1069223 A NONE' SOME' option' a (@lem1069222 A a option' option'' NONE' SOME' h1 h2 h3)). Qed.
Lemma lem1069225 {A : Type'} (a : recspace A) (option' : type1338 A) (option'' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : term63 A NONE' SOME') (h2 : term44 A NONE' SOME' option') (h3 : option'' = (term50 A NONE' SOME')) : term43 A NONE' SOME' option' a.
Proof. exact (@lem1069224 A a option' option'' NONE' SOME' h1 h2 h3 (@lem1069219 A a NONE' SOME' option' h2)). Qed.
Lemma lem1069226 {A : Type'} (NONE' : recspace A) (a : recspace A) (SOME' : type1432 A) (h1 : term42 A NONE' a SOME') : term42 A NONE' a SOME'.
Proof. exact (h1). Qed.
Lemma lem1069227 {A : Type'} (option' : type1338 A) (option'' : type1338 A) (NONE' : recspace A) (a : recspace A) (SOME' : type1432 A) (h1 : term63 A NONE' SOME') (h2 : term44 A NONE' SOME' option') (h3 : option'' = (term50 A NONE' SOME')) (h4 : term42 A NONE' a SOME') : option' a.
Proof. exact (@lem1069225 A a option' option'' NONE' SOME' h1 h2 h3 (@lem1069226 A NONE' a SOME' h4)). Qed.
Lemma lem1069228 {A : Type'} (option' : type1338 A) (option'' : type1338 A) (NONE' : recspace A) (a : recspace A) (SOME' : type1432 A) (h1 : term63 A NONE' SOME') (h2 : option'' = (term50 A NONE' SOME')) (h3 : term42 A NONE' a SOME') : term46 A NONE' SOME' option' a.
Proof. exact (fun h0 : term44 A NONE' SOME' option' => @lem1069227 A option' option'' NONE' a SOME' h1 h0 h2 h3). Qed.
Lemma lem1069229 {A : Type'} (option' : type1338 A) (NONE' : recspace A) (a : recspace A) (SOME' : type1432 A) (h1 : term63 A NONE' SOME') (h2 : option' = (term50 A NONE' SOME')) (h3 : term42 A NONE' a SOME') : term52 A NONE' SOME' a.
Proof. exact (fun option'' : type1338 A => @lem1069228 A option'' option' NONE' a SOME' h1 h2 h3). Qed.
Lemma lem1069230 {A : Type'} (a : recspace A) (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : option' = (term50 A NONE' SOME')) : term55 A option' NONE' SOME' a.
Proof. exact (@lem1069185 A option' NONE' SOME' h1 a). Qed.
Lemma lem1069231 {A : Type'} (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (a : recspace A) : (term55 A option' NONE' SOME' a) = ((option' a) = (term52 A NONE' SOME' a)).
Proof. exact (eq_refl (term55 A option' NONE' SOME' a)). Qed.
Lemma lem1069232 {A : Type'} (a : recspace A) (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : option' = (term50 A NONE' SOME')) : (option' a) = (term52 A NONE' SOME' a).
Proof. exact (EQ_MP (@lem1069231 A option' NONE' SOME' a) (@lem1069230 A a option' NONE' SOME' h1)). Qed.
Lemma lem1069233 {A : Type'} (a : recspace A) (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : option' = (term50 A NONE' SOME')) : (term52 A NONE' SOME' a) = (option' a).
Proof. exact (SYM (@lem1069232 A a option' NONE' SOME' h1)). Qed.
Lemma lem1069234 {A : Type'} (option' : type1338 A) (NONE' : recspace A) (a : recspace A) (SOME' : type1432 A) (h1 : term63 A NONE' SOME') (h2 : option' = (term50 A NONE' SOME')) (h3 : term42 A NONE' a SOME') : option' a.
Proof. exact (EQ_MP (@lem1069233 A a option' NONE' SOME' h2) (@lem1069229 A option' NONE' a SOME' h1 h2 h3)). Qed.
Lemma lem1069235 {A : Type'} (a : recspace A) (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : term63 A NONE' SOME') (h2 : option' = (term50 A NONE' SOME')) : term43 A NONE' SOME' option' a.
Proof. exact (fun h0 : term42 A NONE' a SOME' => @lem1069234 A option' NONE' a SOME' h1 h2 h0). Qed.
Lemma lem1069236 {A : Type'} (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : term63 A NONE' SOME') (h2 : option' = (term50 A NONE' SOME')) : term44 A NONE' SOME' option'.
Proof. exact (fun a : recspace A => @lem1069235 A a option' NONE' SOME' h1 h2). Qed.
Lemma lem1069239 {A : Type'} (NONE' : recspace A) (SOME' : type1432 A) (a : recspace A) : (term74 A NONE' SOME' a) = (term74 A NONE' SOME' a).
Proof. exact (eq_refl (term74 A NONE' SOME' a)). Qed.
Lemma lem1069240 {A : Type'} (NONE' : recspace A) (a : recspace A) (SOME' : type1432 A) : (term74 A NONE' SOME' a) = (term42 A NONE' a SOME').
Proof. exact (eq_refl (term74 A NONE' SOME' a)). Qed.
Lemma lem1069241 {A : Type'} (NONE' : recspace A) (SOME' : type1432 A) (a : recspace A) : (term75 A NONE' SOME' a) = (term75 A NONE' SOME' a).
Proof. exact (eq_refl (term75 A NONE' SOME' a)). Qed.
Lemma lem1069242 {A : Type'} (NONE' : recspace A) (a : recspace A) (SOME' : type1432 A) : ((term74 A NONE' SOME' a) = (term74 A NONE' SOME' a)) = ((term74 A NONE' SOME' a) = (term42 A NONE' a SOME')).
Proof. exact (MK_COMB (@lem1069241 A NONE' SOME' a) (@lem1069240 A NONE' a SOME')). Qed.
Lemma lem1069243 {A : Type'} (NONE' : recspace A) (a : recspace A) (SOME' : type1432 A) : (term74 A NONE' SOME' a) = (term42 A NONE' a SOME').
Proof. exact (EQ_MP (@lem1069242 A NONE' a SOME') (@lem1069239 A NONE' SOME' a)). Qed.
Lemma lem1069244 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1069245 {A : Type'} (NONE' : recspace A) (a : recspace A) (SOME' : type1432 A) : (term76 A NONE' SOME' a) = (term77 A NONE' a SOME').
Proof. exact (MK_COMB (@lem1069244) (@lem1069243 A NONE' a SOME')). Qed.
Lemma lem1069246 {A : Type'} (option' : type1338 A) (a : recspace A) : (option' a) = (option' a).
Proof. exact (eq_refl (option' a)). Qed.
Lemma lem1069247 {A : Type'} (NONE' : recspace A) (SOME' : type1432 A) (option' : type1338 A) (a : recspace A) : (term78 A NONE' SOME' option' a) = (term43 A NONE' SOME' option' a).
Proof. exact (MK_COMB (@lem1069245 A NONE' a SOME') (@lem1069246 A option' a)). Qed.
Lemma lem1069248 {A : Type'} (NONE' : recspace A) (a : recspace A) (SOME' : type1432 A) : (term77 A NONE' a SOME') = (term77 A NONE' a SOME').
Proof. exact (eq_refl (term77 A NONE' a SOME')). Qed.
Lemma lem1069249 {A : Type'} (NONE' : recspace A) (a : recspace A) (SOME' : type1432 A) : (term79 A NONE' SOME' a) = (term71 A NONE' a SOME').
Proof. exact (MK_COMB (@lem1069248 A NONE' a SOME') (@lem1069243 A NONE' a SOME')). Qed.
Lemma lem1069250 {A : Type'} (option' : type1338 A) (a : recspace A) : (term80 A option' a) = (term80 A option' a).
Proof. exact (eq_refl (term80 A option' a)). Qed.
Lemma lem1069251 {A : Type'} (option' : type1338 A) (NONE' : recspace A) (a : recspace A) (SOME' : type1432 A) : (term81 A option' NONE' SOME' a) = (term82 A option' NONE' a SOME').
Proof. exact (MK_COMB (@lem1069250 A option' a) (@lem1069243 A NONE' a SOME')). Qed.
Lemma lem1069252 {A : Type'} (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) : (term83 A option' NONE' SOME') = (term84 A option' NONE' SOME').
Proof. exact (fun_ext (fun a : recspace A => @lem1069251 A option' NONE' a SOME')). Qed.
Lemma lem1069253 {A : Type'} : (@all (recspace A)) = (@all (recspace A)).
Proof. exact (eq_refl (@all (recspace A))). Qed.
Lemma lem1069254 {A : Type'} (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) : (term85 A option' NONE' SOME') = (term86 A option' NONE' SOME').
Proof. exact (MK_COMB (@lem1069253 A) (@lem1069252 A option' NONE' SOME')). Qed.
Lemma lem1069255 {A : Type'} (NONE' : recspace A) (SOME' : type1432 A) : (term87 A NONE' SOME') = (term88 A NONE' SOME').
Proof. exact (fun_ext (fun a : recspace A => @lem1069249 A NONE' a SOME')). Qed.
Lemma lem1069256 {A : Type'} : (@all (recspace A)) = (@all (recspace A)).
Proof. exact (eq_refl (@all (recspace A))). Qed.
Lemma lem1069257 {A : Type'} (NONE' : recspace A) (SOME' : type1432 A) : (term89 A NONE' SOME') = (term69 A NONE' SOME').
Proof. exact (MK_COMB (@lem1069256 A) (@lem1069255 A NONE' SOME')). Qed.
Lemma lem1069258 {A : Type'} (NONE' : recspace A) (SOME' : type1432 A) (option' : type1338 A) : (term90 A NONE' SOME' option') = (term91 A NONE' SOME' option').
Proof. exact (fun_ext (fun a : recspace A => @lem1069247 A NONE' SOME' option' a)). Qed.
Lemma lem1069259 {A : Type'} : (@all (recspace A)) = (@all (recspace A)).
Proof. exact (eq_refl (@all (recspace A))). Qed.
Lemma lem1069260 {A : Type'} (NONE' : recspace A) (SOME' : type1432 A) (option' : type1338 A) : (term92 A NONE' SOME' option') = (term44 A NONE' SOME' option').
Proof. exact (MK_COMB (@lem1069259 A) (@lem1069258 A NONE' SOME' option')). Qed.
Lemma lem1069261 {A : Type'} (NONE' : recspace A) (SOME' : type1432 A) (option' : type1338 A) : (term44 A NONE' SOME' option') = (term92 A NONE' SOME' option').
Proof. exact (SYM (@lem1069260 A NONE' SOME' option')). Qed.
Lemma lem1069262 {A : Type'} (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : term63 A NONE' SOME') (h2 : option' = (term50 A NONE' SOME')) : term92 A NONE' SOME' option'.
Proof. exact (EQ_MP (@lem1069261 A NONE' SOME' option') (@lem1069236 A option' NONE' SOME' h1 h2)). Qed.
Lemma lem1069263 {A : Type'} (NONE' : recspace A) (SOME' : type1432 A) (h1 : term63 A NONE' SOME') : term93 A NONE' SOME'.
Proof. exact (@lem1069204 A NONE' SOME' h1 (term94 A NONE' SOME')). Qed.
Lemma lem1069264 {A : Type'} (NONE' : recspace A) (SOME' : type1432 A) : (term93 A NONE' SOME') = (term95 A NONE' SOME').
Proof. exact (eq_refl (term93 A NONE' SOME')). Qed.
Lemma lem1069265 {A : Type'} (NONE' : recspace A) (SOME' : type1432 A) (h1 : term63 A NONE' SOME') : term95 A NONE' SOME'.
Proof. exact (EQ_MP (@lem1069264 A NONE' SOME') (@lem1069263 A NONE' SOME' h1)). Qed.
Lemma lem1069266 {A : Type'} (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : term63 A NONE' SOME') : term96 A NONE' SOME' option'.
Proof. exact (@lem1069265 A NONE' SOME' h1 option'). Qed.
Lemma lem1069267 {A : Type'} (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) : (term96 A NONE' SOME' option') = (term97 A option' NONE' SOME').
Proof. exact (eq_refl (term96 A NONE' SOME' option')). Qed.
Lemma lem1069268 {A : Type'} (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : term63 A NONE' SOME') : term97 A option' NONE' SOME'.
Proof. exact (EQ_MP (@lem1069267 A option' NONE' SOME') (@lem1069266 A option' NONE' SOME' h1)). Qed.
Lemma lem1069269 {A : Type'} (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : term63 A NONE' SOME') (h2 : option' = (term50 A NONE' SOME')) : term69 A NONE' SOME'.
Proof. exact (@lem1069268 A option' NONE' SOME' h1 (@lem1069262 A option' NONE' SOME' h1 h2)). Qed.
Lemma lem1069270 {A : Type'} (NONE' : recspace A) (SOME' : type1432 A) : (term69 A NONE' SOME') = (term89 A NONE' SOME').
Proof. exact (SYM (@lem1069257 A NONE' SOME')). Qed.
Lemma lem1069271 {A : Type'} (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : term63 A NONE' SOME') (h2 : option' = (term50 A NONE' SOME')) : term89 A NONE' SOME'.
Proof. exact (EQ_MP (@lem1069270 A NONE' SOME') (@lem1069269 A option' NONE' SOME' h1 h2)). Qed.
Lemma lem1069272 {A : Type'} (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : option' = (term50 A NONE' SOME')) : term98 A option' NONE' SOME'.
Proof. exact (@lem1069203 A option' NONE' SOME' h1 (term94 A NONE' SOME')). Qed.
Lemma lem1069273 {A : Type'} (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) : (term98 A option' NONE' SOME') = (term99 A option' NONE' SOME').
Proof. exact (eq_refl (term98 A option' NONE' SOME')). Qed.
Lemma lem1069274 {A : Type'} (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : option' = (term50 A NONE' SOME')) : term99 A option' NONE' SOME'.
Proof. exact (EQ_MP (@lem1069273 A option' NONE' SOME') (@lem1069272 A option' NONE' SOME' h1)). Qed.
Lemma lem1069275 {A : Type'} (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : term63 A NONE' SOME') (h2 : option' = (term50 A NONE' SOME')) : term85 A option' NONE' SOME'.
Proof. exact (@lem1069274 A option' NONE' SOME' h2 (@lem1069271 A option' NONE' SOME' h1 h2)). Qed.
Lemma lem1069276 {A : Type'} (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : term63 A NONE' SOME') (h2 : option' = (term50 A NONE' SOME')) : term86 A option' NONE' SOME'.
Proof. exact (EQ_MP (@lem1069254 A option' NONE' SOME') (@lem1069275 A option' NONE' SOME' h1 h2)). Qed.
Lemma lem1069277 {A : Type'} (a : recspace A) (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : term63 A NONE' SOME') (h2 : option' = (term50 A NONE' SOME')) : term45 A NONE' SOME' option' a.
Proof. exact (@lem1069236 A option' NONE' SOME' h1 h2 a). Qed.
Lemma lem1069278 {A : Type'} (NONE' : recspace A) (SOME' : type1432 A) (option' : type1338 A) (a : recspace A) : (term45 A NONE' SOME' option' a) = (term43 A NONE' SOME' option' a).
Proof. exact (eq_refl (term45 A NONE' SOME' option' a)). Qed.
Lemma lem1069279 {A : Type'} (a : recspace A) (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : term63 A NONE' SOME') (h2 : option' = (term50 A NONE' SOME')) : term43 A NONE' SOME' option' a.
Proof. exact (EQ_MP (@lem1069278 A NONE' SOME' option' a) (@lem1069277 A a option' NONE' SOME' h1 h2)). Qed.
Lemma lem1069280 {A : Type'} (a : recspace A) (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : term63 A NONE' SOME') (h2 : option' = (term50 A NONE' SOME')) : term100 A option' NONE' SOME' a.
Proof. exact (@lem1069276 A option' NONE' SOME' h1 h2 a). Qed.
Lemma lem1069281 {A : Type'} (option' : type1338 A) (NONE' : recspace A) (a : recspace A) (SOME' : type1432 A) : (term100 A option' NONE' SOME' a) = (term82 A option' NONE' a SOME').
Proof. exact (eq_refl (term100 A option' NONE' SOME' a)). Qed.
Lemma lem1069282 {A : Type'} (a : recspace A) (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : term63 A NONE' SOME') (h2 : option' = (term50 A NONE' SOME')) : term82 A option' NONE' a SOME'.
Proof. exact (EQ_MP (@lem1069281 A option' NONE' a SOME') (@lem1069280 A a option' NONE' SOME' h1 h2)). Qed.
Lemma lem1069283 {A : Type'} (a : recspace A) (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : term63 A NONE' SOME') (h2 : option' = (term50 A NONE' SOME')) : term101 A NONE' SOME' option' a.
Proof. exact (conj (@lem1069282 A a option' NONE' SOME' h1 h2) (@lem1069279 A a option' NONE' SOME' h1 h2)). Qed.
Lemma lem1069284 {A : Type'} (option' : type1338 A) (NONE' : recspace A) (a : recspace A) (SOME' : type1432 A) : (term101 A NONE' SOME' option' a) = ((option' a) = (term42 A NONE' a SOME')).
Proof. exact (@lem32 (option' a) (term42 A NONE' a SOME')). Qed.
Lemma lem1069285 {A : Type'} (a : recspace A) (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : term63 A NONE' SOME') (h2 : option' = (term50 A NONE' SOME')) : (option' a) = (term42 A NONE' a SOME').
Proof. exact (EQ_MP (@lem1069284 A option' NONE' a SOME') (@lem1069283 A a option' NONE' SOME' h1 h2)). Qed.
Lemma lem1069290 {A : Type'} (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : term63 A NONE' SOME') (h2 : option' = (term50 A NONE' SOME')) : term44 A NONE' SOME' option'.
Proof. exact (fun a : recspace A => @lem1069235 A a option' NONE' SOME' h1 h2). Qed.
Lemma lem1069291 {A : Type'} (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : term63 A NONE' SOME') (h2 : option' = (term50 A NONE' SOME')) : term102 A option' NONE' SOME'.
Proof. exact (fun a : recspace A => @lem1069285 A a option' NONE' SOME' h1 h2). Qed.
Lemma lem1069292 {A : Type'} (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : term63 A NONE' SOME') (h2 : option' = (term50 A NONE' SOME')) : term62 A NONE' SOME' option'.
Proof. exact (fun option'' : type1338 A => @lem1069202 A option'' option' NONE' SOME' h2). Qed.
Lemma lem1069293 {A : Type'} (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : term63 A NONE' SOME') (h2 : option' = (term50 A NONE' SOME')) : term38 A NONE' option' SOME'.
Proof. exact (EQ_MP (@lem1069177 A NONE' option' SOME') (@lem1069290 A option' NONE' SOME' h1 h2)). Qed.
Lemma lem1069307 {A : Type'} (NONE' : recspace A) (option' : type1338 A) (SOME' : type1432 A) : (term44 A NONE' SOME' option') = (term38 A NONE' option' SOME').
Proof. exact (SYM (@lem1069176 A NONE' SOME' option')). Qed.
Lemma lem1069308 {A : Type'} (NONE' : recspace A) (option' : type1338 A) (SOME' : type1432 A) : (term44 A NONE' SOME' option') = (term38 A NONE' option' SOME').
Proof. exact (@lem1069307 A NONE' option' SOME'). Qed.
Lemma lem1069309 {A : Type'} (NONE' : recspace A) (option' : type1338 A) (SOME' : type1432 A) : (term44 A NONE' SOME' option') = (term38 A NONE' option' SOME').
Proof. exact (@lem1069308 A NONE' option' SOME'). Qed.
Lemma lem1069310 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1069311 {A : Type'} (NONE' : recspace A) (option' : type1338 A) (SOME' : type1432 A) : (term103 A NONE' SOME' option') = (term104 A NONE' option' SOME').
Proof. exact (MK_COMB (@lem1069310) (@lem1069309 A NONE' option' SOME')). Qed.
Lemma lem1069336 {A : Type'} (option' : type1338 A) (option'' : type1338 A) : (term60 A option' option'') = (term60 A option' option'').
Proof. exact (eq_refl (term60 A option' option'')). Qed.
Lemma lem1069337 {A : Type'} (NONE' : recspace A) (SOME' : type1432 A) (option' : type1338 A) (option'' : type1338 A) : (term61 A NONE' SOME' option' option'') = (term105 A NONE' SOME' option' option'').
Proof. exact (MK_COMB (@lem1069311 A NONE' option'' SOME') (@lem1069336 A option' option'')). Qed.
Lemma lem1069338 {A : Type'} (NONE' : recspace A) (SOME' : type1432 A) (option' : type1338 A) : (term106 A NONE' SOME' option') = (term107 A NONE' SOME' option').
Proof. exact (fun_ext (fun option'' : type1338 A => @lem1069337 A NONE' SOME' option' option'')). Qed.
Lemma lem1069339 {A : Type'} : (@all ((recspace A) -> Prop)) = (@all ((recspace A) -> Prop)).
Proof. exact (eq_refl (@all ((recspace A) -> Prop))). Qed.
Lemma lem1069340 {A : Type'} (NONE' : recspace A) (SOME' : type1432 A) (option' : type1338 A) : (term62 A NONE' SOME' option') = (term108 A NONE' SOME' option').
Proof. exact (MK_COMB (@lem1069339 A) (@lem1069338 A NONE' SOME' option')). Qed.
Lemma lem1069341 {A : Type'} (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : term63 A NONE' SOME') (h2 : option' = (term50 A NONE' SOME')) : term108 A NONE' SOME' option'.
Proof. exact (EQ_MP (@lem1069340 A NONE' SOME' option') (@lem1069292 A option' NONE' SOME' h1 h2)). Qed.
Lemma lem1069342 {A : Type'} (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : term63 A NONE' SOME') (h2 : option' = (term50 A NONE' SOME')) : term109 A option' NONE' SOME'.
Proof. exact (conj (@lem1069341 A option' NONE' SOME' h1 h2) (@lem1069291 A option' NONE' SOME' h1 h2)). Qed.
Lemma lem1069343 {A : Type'} (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : term63 A NONE' SOME') (h2 : option' = (term50 A NONE' SOME')) : term110 A option' NONE' SOME'.
Proof. exact (conj (@lem1069293 A option' NONE' SOME' h1 h2) (@lem1069342 A option' NONE' SOME' h1 h2)). Qed.
Lemma lem1069345 {A : Type'} (NONE' : recspace A) (a : recspace A) (SOME' : type1432 A) : term111 A NONE' a SOME'.
Proof. exact (@lem9120 (term42 A NONE' a SOME')). Qed.
Lemma lem1069346 {A : Type'} (NONE' : recspace A) (a : recspace A) (SOME' : type1432 A) : (term111 A NONE' a SOME') = (term71 A NONE' a SOME').
Proof. exact (eq_refl (term111 A NONE' a SOME')). Qed.
Lemma lem1069347 {A : Type'} (NONE' : recspace A) (a : recspace A) (SOME' : type1432 A) : term71 A NONE' a SOME'.
Proof. exact (EQ_MP (@lem1069346 A NONE' a SOME') (@lem1069345 A NONE' a SOME')). Qed.
Lemma lem1069352 {A : Type'} (NONE' : recspace A) (SOME' : type1432 A) : term69 A NONE' SOME'.
Proof. exact (fun a : recspace A => @lem1069347 A NONE' a SOME'). Qed.
Lemma lem1069353 {A : Type'} (option' : type1338 A) (option'' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) : term68 A option' option'' NONE' SOME'.
Proof. exact (fun h0 : term60 A option' option'' => @lem1069352 A NONE' SOME'). Qed.
Lemma lem1069358 {A : Type'} (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) : term66 A option' NONE' SOME'.
Proof. exact (fun option'' : type1338 A => @lem1069353 A option' option'' NONE' SOME'). Qed.
Lemma lem1069363 {A : Type'} (NONE' : recspace A) (SOME' : type1432 A) : term63 A NONE' SOME'.
Proof. exact (fun option' : type1338 A => @lem1069358 A option' NONE' SOME'). Qed.
Lemma lem1069364 {A : Type'} (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : option' = (term50 A NONE' SOME')) : (term63 A NONE' SOME') = (term110 A option' NONE' SOME').
Proof. exact (prop_ext (fun h2 : term63 A NONE' SOME' => @lem1069343 A option' NONE' SOME' h2 h1) (fun h2 : term110 A option' NONE' SOME' => @lem1069363 A NONE' SOME')). Qed.
Lemma lem1069365 {A : Type'} (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : option' = (term50 A NONE' SOME')) : term110 A option' NONE' SOME'.
Proof. exact (EQ_MP (@lem1069364 A option' NONE' SOME' h1) (@lem1069363 A NONE' SOME')). Qed.
