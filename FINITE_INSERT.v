Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_INSERT_term_abbrevs.
Require Import FINITE_RULES_spec.
Require Import FINITE_SUBSET_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17160_spec.
Require Import thm1842_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm32_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211692_spec.
Require Import thm3211693_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Require Import thm7_spec.
Lemma lem3607910 {A : Type'} : term0 A.
Proof. exact (proj2 (@lem3197565 A)). Qed.
Lemma lem3607911 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem3607912 {A : Type'} (x : A) (h1 : term0 A) : term1 A x.
Proof. exact (@lem3607911 A h1 x). Qed.
Lemma lem3607913 {A : Type'} (x : A) : (term1 A x) = (term2 A x).
Proof. exact (eq_refl (term1 A x)). Qed.
Lemma lem3607914 {A : Type'} (x : A) (h1 : term0 A) : term2 A x.
Proof. exact (EQ_MP (@lem3607913 A x) (@lem3607912 A x h1)). Qed.
Lemma lem3607915 {A : Type'} (x : A) (s : A -> Prop) (h1 : term0 A) : term3 A x s.
Proof. exact (@lem3607914 A x h1 s). Qed.
Lemma lem3607916 {A : Type'} (x : A) (s : A -> Prop) : (term3 A x s) = (term4 A x s).
Proof. exact (eq_refl (term3 A x s)). Qed.
Lemma lem3607917 {A : Type'} (x : A) (s : A -> Prop) (h1 : term0 A) : term4 A x s.
Proof. exact (EQ_MP (@lem3607916 A x s) (@lem3607915 A x s h1)). Qed.
Lemma lem3607918 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem3607919 {A : Type'} (x : A) (s : A -> Prop) (h1 : term0 A) (h2 : @FINITE A s) : term5 A x s.
Proof. exact (@lem3607917 A x s h1 (@lem3607918 A s h2)). Qed.
Lemma lem3607920 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : term6 A x s.
Proof. exact (fun h0 : term0 A => @lem3607919 A x s h0 h1). Qed.
Lemma lem3607921 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem3607922 {A : Type'} (x : A) (s : A -> Prop) (h1 : term0 A) (h2 : @FINITE A s) : term5 A x s.
Proof. exact (@lem3607920 A x s h2 (@lem3607921 A h1)). Qed.
Lemma lem3607923 {A : Type'} (x : A) (s : A -> Prop) (h1 : term0 A) : term4 A x s.
Proof. exact (fun h0 : @FINITE A s => @lem3607922 A x s h1 h0). Qed.
Lemma lem3607924 {A : Type'} (x : A) (h1 : term0 A) : term2 A x.
Proof. exact (fun s : A -> Prop => @lem3607923 A x s h1). Qed.
Lemma lem3607925 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (fun x : A => @lem3607924 A x h1). Qed.
Lemma lem3607926 {A : Type'} : term7 A.
Proof. exact (fun h0 : term0 A => @lem3607925 A h0). Qed.
Lemma lem3607927 {A : Type'} : term0 A.
Proof. exact (@lem3607926 A (@lem3607910 A)). Qed.
Lemma lem3607928 {A : Type'} (x : A) : term1 A x.
Proof. exact (@lem3607927 A x). Qed.
Lemma lem3607929 {A : Type'} (x : A) : (term1 A x) = (term2 A x).
Proof. exact (eq_refl (term1 A x)). Qed.
Lemma lem3607930 {A : Type'} (x : A) : term2 A x.
Proof. exact (EQ_MP (@lem3607929 A x) (@lem3607928 A x)). Qed.
Lemma lem3607931 {A : Type'} (x : A) (s : A -> Prop) : term3 A x s.
Proof. exact (@lem3607930 A x s). Qed.
Lemma lem3607932 {A : Type'} (x : A) (s : A -> Prop) : (term3 A x s) = (term4 A x s).
Proof. exact (eq_refl (term3 A x s)). Qed.
Lemma lem3607944 {A : Type'} (h1 : term8 A) : term8 A.
Proof. exact (h1). Qed.
Lemma lem3607945 {A : Type'} (s : A -> Prop) (h1 : term8 A) : term9 A s.
Proof. exact (@lem3607944 A h1 s). Qed.
Lemma lem3607946 {A : Type'} (s : A -> Prop) : (term9 A s) = (term10 A s).
Proof. exact (eq_refl (term9 A s)). Qed.
Lemma lem3607947 {A : Type'} (s : A -> Prop) (h1 : term8 A) : term10 A s.
Proof. exact (EQ_MP (@lem3607946 A s) (@lem3607945 A s h1)). Qed.
Lemma lem3607948 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term8 A) : term11 A s t.
Proof. exact (@lem3607947 A s h1 t). Qed.
Lemma lem3607949 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term11 A s t) = (term12 A t s).
Proof. exact (eq_refl (term11 A s t)). Qed.
Lemma lem3607950 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term8 A) : term12 A t s.
Proof. exact (EQ_MP (@lem3607949 A t s) (@lem3607948 A s t h1)). Qed.
Lemma lem3607951 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term13 A s t) : term13 A s t.
Proof. exact (h1). Qed.
Lemma lem3607952 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term8 A) (h2 : term13 A s t) : @FINITE A s.
Proof. exact (@lem3607950 A t s h1 (@lem3607951 A s t h2)). Qed.
Lemma lem3607953 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term13 A s t) : term14 A s.
Proof. exact (fun h0 : term8 A => @lem3607952 A s t h0 h1). Qed.
Lemma lem3607954 {A : Type'} (s : A -> Prop) (h1 : term15 A s) : term15 A s.
Proof. exact (h1). Qed.
Lemma lem3607955 {A : Type'} (s : A -> Prop) (h1 : term15 A s) : term14 A s.
Proof. exact (ex_elim (@lem3607954 A s h1) (fun t : A -> Prop => fun h0 : term16 A s t => @lem3607953 A s t h0)). Qed.
Lemma lem3607956 {A : Type'} (h1 : term8 A) : term8 A.
Proof. exact (h1). Qed.
Lemma lem3607957 {A : Type'} (s : A -> Prop) (h1 : term8 A) (h2 : term15 A s) : @FINITE A s.
Proof. exact (@lem3607955 A s h2 (@lem3607956 A h1)). Qed.
Lemma lem3607958 {A : Type'} (s : A -> Prop) (h1 : term8 A) : term17 A s.
Proof. exact (fun h0 : term15 A s => @lem3607957 A s h1 h0). Qed.
Lemma lem3607959 {A : Type'} (h1 : term8 A) : term18 A.
Proof. exact (fun s : A -> Prop => @lem3607958 A s h1). Qed.
Lemma lem3607960 {A : Type'} : term19 A.
Proof. exact (fun h0 : term8 A => @lem3607959 A h0). Qed.
Lemma lem3607961 {A : Type'} : term18 A.
Proof. exact (@lem3607960 A (@lem3599924 A)). Qed.
Lemma lem3607962 {A : Type'} (s : A -> Prop) : term20 A s.
Proof. exact (@lem3607961 A s). Qed.
Lemma lem3607963 {A : Type'} (s : A -> Prop) : (term20 A s) = (term17 A s).
Proof. exact (eq_refl (term20 A s)). Qed.
Lemma lem3607965 {A : Type'} (x : A) (s : A -> Prop) (h1 : term5 A x s) : term5 A x s.
Proof. exact (h1). Qed.
Lemma lem3607966 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem3607968 {A : Type'} (s : A -> Prop) : term17 A s.
Proof. exact (EQ_MP (@lem3607963 A s) (@lem3607962 A s)). Qed.
Lemma lem3607969 {A : Type'} (s : A -> Prop) : term17 A s.
Proof. exact (@lem3607968 A s). Qed.
Lemma lem3607970 {A : Type'} (x : A) (s : A -> Prop) : (term5 A x s) = ((term5 A x s) = True).
Proof. exact (@lem7 (term5 A x s)). Qed.
Lemma lem3607975 {A : Type'} (x : A) (s : A -> Prop) (h1 : term5 A x s) : (term5 A x s) = True.
Proof. exact (EQ_MP (@lem3607970 A x s) (@lem3607965 A x s h1)). Qed.
Lemma lem3607976 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3607977 {A : Type'} (x : A) (s : A -> Prop) (h1 : term5 A x s) : (term21 A x s) = (and True).
Proof. exact (MK_COMB (@lem3607976) (@lem3607975 A x s h1)). Qed.
Lemma lem3607978 {A : Type'} (x : A) (s : A -> Prop) : (term22 A x s) = (term22 A x s).
Proof. exact (eq_refl (term22 A x s)). Qed.
Lemma lem3607979 {A : Type'} (x : A) (s : A -> Prop) (h1 : term5 A x s) : (term23 A x s) = (term24 A x s).
Proof. exact (MK_COMB (@lem3607977 A x s h1) (@lem3607978 A x s)). Qed.
Lemma lem3607981 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3607982 {A : Type'} (x : A) (s : A -> Prop) : (term24 A x s) = (term22 A x s).
Proof. exact (@lem3607981 (term22 A x s)). Qed.
Lemma lem3607983 {A : Type'} (x : A) (s : A -> Prop) (h1 : term5 A x s) : (term23 A x s) = (term22 A x s).
Proof. exact (TRANS (@lem3607979 A x s h1) (@lem3607982 A x s)). Qed.
Lemma lem3607984 {A : Type'} (x : A) (s : A -> Prop) (h1 : term5 A x s) : (term22 A x s) = (term23 A x s).
Proof. exact (SYM (@lem3607983 A x s h1)). Qed.
Lemma lem3607986 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term25 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3607987 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term25 A s t).
Proof. exact (@lem3607986 A s t). Qed.
Lemma lem3607988 {A : Type'} (x : A) (s : A -> Prop) : (term22 A x s) = (term26 A x s).
Proof. exact (@lem3607987 A s (@INSERT A x s)). Qed.
Lemma lem3607995 {A : Type'} (x : A) (s : A -> Prop) : (term26 A x s) = (term22 A x s).
Proof. exact (SYM (@lem3607988 A x s)). Qed.
Lemma lem3608003 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3608004 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3608003 A P x). Qed.
Lemma lem3608005 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3608004 A s x'). Qed.
Lemma lem3608006 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3608007 {A : Type'} (s : A -> Prop) (x' : A) : (term27 A x' s) = (term28 A s x').
Proof. exact (MK_COMB (@lem3608006) (@lem3608005 A s x')). Qed.
Lemma lem3608009 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term29 A x y s) = (term30 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3608010 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term29 A x y s) = (term30 A y x s).
Proof. exact (@lem3608009 A y x s). Qed.
Lemma lem3608011 {A : Type'} (x : A) (x' : A) (s : A -> Prop) : (term29 A x' x s) = (term30 A x x' s).
Proof. exact (@lem3608010 A x x' s). Qed.
Lemma lem3608017 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3608018 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3608017 A P x). Qed.
Lemma lem3608019 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3608018 A s x'). Qed.
Lemma lem3608020 {A : Type'} (x' : A) (x : A) : (term31 A x' x) = (term31 A x' x).
Proof. exact (eq_refl (term31 A x' x)). Qed.
Lemma lem3608021 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term30 A x x' s) = (term32 A x s x').
Proof. exact (MK_COMB (@lem3608020 A x' x) (@lem3608019 A s x')). Qed.
Lemma lem3608024 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term29 A x' x s) = (term32 A x s x').
Proof. exact (TRANS (@lem3608011 A x x' s) (@lem3608021 A x s x')). Qed.
Lemma lem3608025 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term33 A x' x s) = (term34 A x s x').
Proof. exact (MK_COMB (@lem3608007 A s x') (@lem3608024 A x s x')). Qed.
Lemma lem3608028 {A : Type'} (x : A) (s : A -> Prop) : (term35 A x s) = (term36 A x s).
Proof. exact (fun_ext (fun x' : A => @lem3608025 A x s x')). Qed.
Lemma lem3608029 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3608030 {A : Type'} (x : A) (s : A -> Prop) : (term26 A x s) = (term37 A x s).
Proof. exact (MK_COMB (@lem3608029 A) (@lem3608028 A x s)). Qed.
Lemma lem3608035 {A : Type'} (x : A) (s : A -> Prop) : (term37 A x s) = (term26 A x s).
Proof. exact (SYM (@lem3608030 A x s)). Qed.
Lemma lem3608037 (p : Prop) : p = (term38 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3608038 {A : Type'} (x : A) (s : A -> Prop) : (term37 A x s) = (term39 A x s).
Proof. exact (@lem3608037 (term37 A x s)). Qed.
Lemma lem3608039 {A : Type'} (x : A) (s : A -> Prop) : (term39 A x s) = (term37 A x s).
Proof. exact (SYM (@lem3608038 A x s)). Qed.
Lemma lem3608040 {A : Type'} (x : A) (s : A -> Prop) (h1 : term40 A x s) : term40 A x s.
Proof. exact (h1). Qed.
Lemma lem3608043 {A : Type'} (x : A) (s : A -> Prop) (h1 : term39 A x s) : term39 A x s.
Proof. exact (h1). Qed.
Lemma lem3608044 {A : Type'} (x : A) (s : A -> Prop) : term41 A x s.
Proof. exact (fun h0 : term39 A x s => @lem3608043 A x s h0). Qed.
Lemma lem3608045 {A : Type'} (x : A) (s : A -> Prop) (h1 : term41 A x s) : term41 A x s.
Proof. exact (h1). Qed.
Lemma lem3608046 {A : Type'} (x : A) (s : A -> Prop) (h1 : term39 A x s) : term39 A x s.
Proof. exact (h1). Qed.
Lemma lem3608047 {A : Type'} (x : A) (s : A -> Prop) (h1 : term39 A x s) (h2 : term41 A x s) : term39 A x s.
Proof. exact (@lem3608045 A x s h2 (@lem3608046 A x s h1)). Qed.
Lemma lem3608048 {A : Type'} (x : A) (s : A -> Prop) (h1 : term39 A x s) : term42 A x s.
Proof. exact (fun h0 : term41 A x s => @lem3608047 A x s h1 h0). Qed.
Lemma lem3608049 {A : Type'} (x : A) (s : A -> Prop) (h1 : term41 A x s) : term41 A x s.
Proof. exact (h1). Qed.
Lemma lem3608050 {A : Type'} (x : A) (s : A -> Prop) (h1 : term39 A x s) (h2 : term41 A x s) : term39 A x s.
Proof. exact (@lem3608048 A x s h1 (@lem3608049 A x s h2)). Qed.
Lemma lem3608051 {A : Type'} (x : A) (s : A -> Prop) (h1 : term41 A x s) : term41 A x s.
Proof. exact (fun h0 : term39 A x s => @lem3608050 A x s h0 h1). Qed.
Lemma lem3608052 {A : Type'} (x : A) (s : A -> Prop) : term43 A x s.
Proof. exact (fun h0 : term41 A x s => @lem3608051 A x s h0). Qed.
Lemma lem3608055 {A : Type'} (x : A) (s : A -> Prop) : term41 A x s.
Proof. exact (@lem3608052 A x s (@lem3608044 A x s)). Qed.
Lemma lem3608056 {A : Type'} (x : A) (s : A -> Prop) : term41 A x s.
Proof. exact (@lem3608055 A x s). Qed.
Lemma lem3608066 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3608067 {A : Type'} (x : A) (s : A -> Prop) : (term39 A x s) = (term44 A x s).
Proof. exact (@lem3608066 (term40 A x s)). Qed.
Lemma lem3608069 (t : Prop) : (term45 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3608070 {A : Type'} (x : A) (s : A -> Prop) : (term44 A x s) = (term37 A x s).
Proof. exact (@lem3608069 (term37 A x s)). Qed.
Lemma lem3608075 {A : Type'} (x : A) (s : A -> Prop) : (term39 A x s) = (term37 A x s).
Proof. exact (TRANS (@lem3608067 A x s) (@lem3608070 A x s)). Qed.
Lemma lem3608080 {A : Type'} (s : A -> Prop) : (term46 A s) = (term47 A s).
Proof. exact (fun_ext (fun x : A => @lem3608075 A x s)). Qed.
Lemma lem3608081 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3608082 {A : Type'} (s : A -> Prop) : (term48 A s) = (term49 A s).
Proof. exact (MK_COMB (@lem3608081 A) (@lem3608080 A s)). Qed.
Lemma lem3608087 {A : Type'} : (term50 A) = (term51 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3608082 A s)). Qed.
Lemma lem3608088 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3608097 {A : Type'} : (term52 A) = (term53 A).
Proof. exact (MK_COMB (@lem3608088 A) (@lem3608087 A)). Qed.
Lemma lem3608106 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term34 A x s x') = (term34 A x s x').
Proof. exact (eq_refl (term34 A x s x')). Qed.
Lemma lem3608107 {A : Type'} (x : A) (s : A -> Prop) : (term36 A x s) = (term36 A x s).
Proof. exact (fun_ext (fun x' : A => @lem3608106 A x s x')). Qed.
Lemma lem3608108 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3608109 {A : Type'} (x : A) (s : A -> Prop) : (term37 A x s) = (term37 A x s).
Proof. exact (MK_COMB (@lem3608108 A) (@lem3608107 A x s)). Qed.
Lemma lem3608110 {A : Type'} (s : A -> Prop) : (term47 A s) = (term47 A s).
Proof. exact (fun_ext (fun x : A => @lem3608109 A x s)). Qed.
Lemma lem3608111 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3608112 {A : Type'} (s : A -> Prop) : (term49 A s) = (term49 A s).
Proof. exact (MK_COMB (@lem3608111 A) (@lem3608110 A s)). Qed.
Lemma lem3608113 {A : Type'} : (term51 A) = (term51 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3608112 A s)). Qed.
Lemma lem3608114 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3608115 {A : Type'} : (term53 A) = (term53 A).
Proof. exact (MK_COMB (@lem3608114 A) (@lem3608113 A)). Qed.
Lemma lem3608140 {A : Type'} : (term52 A) = (term53 A).
Proof. exact (TRANS (@lem3608097 A) (@lem3608115 A)). Qed.
Lemma lem3608141 {A : Type'} : (term53 A) = (term52 A).
Proof. exact (SYM (@lem3608140 A)). Qed.
Lemma lem3608144 (p : Prop) : p = (term38 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3608145 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term32 A x s x') = (term54 A x s x').
Proof. exact (@lem3608144 (term32 A x s x')). Qed.
Lemma lem3608146 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term54 A x s x') = (term32 A x s x').
Proof. exact (SYM (@lem3608145 A x s x')). Qed.
Lemma lem3608147 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term55 A x s x') : term55 A x s x'.
Proof. exact (h1). Qed.
Lemma lem3608153 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3608164 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term55 A x s x') = (term56 A x s x').
Proof. exact (@lem17160 (x' = x) (s x')). Qed.
Lemma lem3608169 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3608185 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term55 A x s x') : term56 A x s x'.
Proof. exact (EQ_MP (@lem3608164 A x s x') (@lem3608147 A x s x' h1)). Qed.
Lemma lem3608191 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3608201 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3608205 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term55 A x s x') : term57 A s x'.
Proof. exact (proj2 (@lem3608185 A x s x' h1)). Qed.
Lemma lem3608221 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3608222 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : term58 A s x'.
Proof. exact (fun h0 : term57 A s x' => @lem3608221 A s x' h1). Qed.
Lemma lem3608224 (p : Prop) : (term59 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3608225 {A : Type'} (s : A -> Prop) (x' : A) : (term58 A s x') = (s x').
Proof. exact (@lem3608224 (s x')). Qed.
Lemma lem3608226 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (EQ_MP (@lem3608225 A s x') (@lem3608222 A s x' h1)). Qed.
Lemma lem3608229 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3608231 {A : Type'} (s : A -> Prop) (x' : A) : (term57 A s x') = (term60 A s x').
Proof. exact (@lem3608229 (s x')). Qed.
Lemma lem3608234 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term55 A x s x') : term60 A s x'.
Proof. exact (EQ_MP (@lem3608231 A s x') (@lem3608205 A x s x' h1)). Qed.
Lemma lem3608237 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term55 A x s x') (h2 : s x') : False.
Proof. exact (@lem3608234 A x s x' h1 (@lem3608226 A s x' h2)). Qed.
Lemma lem3608238 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term55 A x s x') (h2 : s x') : term61.
Proof. exact (fun h0 : ~ False => @lem3608237 A x s x' h1 h2). Qed.
Lemma lem3608240 (p : Prop) : (term59 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3608241 : term61 = False.
Proof. exact (@lem3608240 False). Qed.
Lemma lem3608242 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term55 A x s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3608241) (@lem3608238 A x s x' h1 h2)). Qed.
Lemma lem3608243 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term55 A x s x') (h2 : s x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3608242 A x s x' h1 h2) (fun h3 : False => @lem3608201 A s x' h2)). Qed.
Lemma lem3608244 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term55 A x s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3608243 A x s x' h1 h2) (@lem3608201 A s x' h2)). Qed.
Lemma lem3608245 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term55 A x s x') (h2 : s x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3608244 A x s x' h1 h2) (fun h3 : False => @lem3608191 A s x' h2)). Qed.
Lemma lem3608246 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term55 A x s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3608245 A x s x' h1 h2) (@lem3608191 A s x' h2)). Qed.
Lemma lem3608247 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term55 A x s x') (h2 : s x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3608246 A x s x' h1 h2) (fun h3 : False => @lem3608191 A s x' h2)). Qed.
Lemma lem3608248 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term55 A x s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3608247 A x s x' h1 h2) (@lem3608191 A s x' h2)). Qed.
Lemma lem3608249 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term55 A x s x') (h2 : s x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3608248 A x s x' h1 h2) (fun h3 : False => @lem3608169 A s x' h2)). Qed.
Lemma lem3608250 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term55 A x s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3608249 A x s x' h1 h2) (@lem3608169 A s x' h2)). Qed.
Lemma lem3608251 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term55 A x s x') (h2 : s x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3608250 A x s x' h1 h2) (fun h3 : False => @lem3608153 A s x' h2)). Qed.
Lemma lem3608252 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term55 A x s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3608251 A x s x' h1 h2) (@lem3608153 A s x' h2)). Qed.
Lemma lem3608253 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term55 A x s x') (h2 : s x') : (term55 A x s x') = False.
Proof. exact (prop_ext (fun h3 : term55 A x s x' => @lem3608252 A x s x' h1 h2) (fun h3 : False => @lem3608147 A x s x' h1)). Qed.
Lemma lem3608254 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term55 A x s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3608253 A x s x' h1 h2) (@lem3608147 A x s x' h1)). Qed.
Lemma lem3608255 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x') : term54 A x s x'.
Proof. exact (fun h0 : term55 A x s x' => @lem3608254 A x s x' h0 h1). Qed.
Lemma lem3608256 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x') : term32 A x s x'.
Proof. exact (EQ_MP (@lem3608146 A x s x') (@lem3608255 A x s x' h1)). Qed.
Lemma lem3608257 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : term34 A x s x'.
Proof. exact (fun h0 : s x' => @lem3608256 A x s x' h0). Qed.
Lemma lem3608262 {A : Type'} (x : A) (s : A -> Prop) : term37 A x s.
Proof. exact (fun x' : A => @lem3608257 A x s x'). Qed.
Lemma lem3608267 {A : Type'} (s : A -> Prop) : term49 A s.
Proof. exact (fun x : A => @lem3608262 A x s). Qed.
Lemma lem3608272 {A : Type'} : term53 A.
Proof. exact (fun s : A -> Prop => @lem3608267 A s). Qed.
Lemma lem3608273 {A : Type'} : term52 A.
Proof. exact (EQ_MP (@lem3608141 A) (@lem3608272 A)). Qed.
Lemma lem3608274 {A : Type'} (s : A -> Prop) : term62 A s.
Proof. exact (@lem3608273 A s). Qed.
Lemma lem3608275 {A : Type'} (s : A -> Prop) : (term62 A s) = (term48 A s).
Proof. exact (eq_refl (term62 A s)). Qed.
Lemma lem3608276 {A : Type'} (s : A -> Prop) : term48 A s.
Proof. exact (EQ_MP (@lem3608275 A s) (@lem3608274 A s)). Qed.
Lemma lem3608277 {A : Type'} (s : A -> Prop) (x : A) : term63 A s x.
Proof. exact (@lem3608276 A s x). Qed.
Lemma lem3608278 {A : Type'} (x : A) (s : A -> Prop) : (term63 A s x) = (term39 A x s).
Proof. exact (eq_refl (term63 A s x)). Qed.
Lemma lem3608279 {A : Type'} (x : A) (s : A -> Prop) : term39 A x s.
Proof. exact (EQ_MP (@lem3608278 A x s) (@lem3608277 A s x)). Qed.
Lemma lem3608281 {A : Type'} (x : A) (s : A -> Prop) : term39 A x s.
Proof. exact (@lem3608056 A x s (@lem3608279 A x s)). Qed.
Lemma lem3608282 {A : Type'} (x : A) (s : A -> Prop) (h1 : term40 A x s) : False.
Proof. exact (@lem3608281 A x s (@lem3608040 A x s h1)). Qed.
Lemma lem3608283 {A : Type'} (x : A) (s : A -> Prop) (h1 : term40 A x s) : (term40 A x s) = False.
Proof. exact (prop_ext (fun h2 : term40 A x s => @lem3608282 A x s h1) (fun h2 : False => @lem3608040 A x s h1)). Qed.
Lemma lem3608284 {A : Type'} (x : A) (s : A -> Prop) (h1 : term40 A x s) : False.
Proof. exact (EQ_MP (@lem3608283 A x s h1) (@lem3608040 A x s h1)). Qed.
Lemma lem3608285 {A : Type'} (x : A) (s : A -> Prop) : term39 A x s.
Proof. exact (fun h0 : term40 A x s => @lem3608284 A x s h0). Qed.
Lemma lem3608286 {A : Type'} (x : A) (s : A -> Prop) : term37 A x s.
Proof. exact (EQ_MP (@lem3608039 A x s) (@lem3608285 A x s)). Qed.
Lemma lem3608287 {A : Type'} (x : A) (s : A -> Prop) : term26 A x s.
Proof. exact (EQ_MP (@lem3608035 A x s) (@lem3608286 A x s)). Qed.
Lemma lem3608288 {A : Type'} (x : A) (s : A -> Prop) : term22 A x s.
Proof. exact (EQ_MP (@lem3607995 A x s) (@lem3608287 A x s)). Qed.
Lemma lem3608289 {A : Type'} (x : A) (s : A -> Prop) (h1 : term5 A x s) : term23 A x s.
Proof. exact (EQ_MP (@lem3607984 A x s h1) (@lem3608288 A x s)). Qed.
Lemma lem3608290 {A : Type'} (x : A) (s : A -> Prop) (h1 : term5 A x s) : term15 A s.
Proof. exact (ex_intro (term16 A s) (@INSERT A x s) (@lem3608289 A x s h1)). Qed.
Lemma lem3608291 {A : Type'} (x : A) (s : A -> Prop) (h1 : term5 A x s) : @FINITE A s.
Proof. exact (@lem3607969 A s (@lem3608290 A x s h1)). Qed.
Lemma lem3608293 {A : Type'} (x : A) (s : A -> Prop) : term4 A x s.
Proof. exact (EQ_MP (@lem3607932 A x s) (@lem3607931 A x s)). Qed.
Lemma lem3608294 {A : Type'} (x : A) (s : A -> Prop) : term4 A x s.
Proof. exact (@lem3608293 A x s). Qed.
Lemma lem3608295 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem3608298 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem3608295 A s) (@lem3607966 A s h1)). Qed.
Lemma lem3608299 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : True = (@FINITE A s).
Proof. exact (SYM (@lem3608298 A s h1)). Qed.
Lemma lem3608300 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (EQ_MP (@lem3608299 A s h1) (@lem0)). Qed.
Lemma lem3608301 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : term5 A x s.
Proof. exact (@lem3608294 A x s (@lem3608300 A s h1)). Qed.
Lemma lem3608302 {A : Type'} (x : A) (s : A -> Prop) : term4 A x s.
Proof. exact (fun h0 : @FINITE A s => @lem3608301 A x s h0). Qed.
Lemma lem3608303 {A : Type'} (x : A) (s : A -> Prop) : term64 A x s.
Proof. exact (fun h0 : term5 A x s => @lem3608291 A x s h0). Qed.
Lemma lem3608304 {A : Type'} (x : A) (s : A -> Prop) : term65 A x s.
Proof. exact (conj (@lem3608303 A x s) (@lem3608302 A x s)). Qed.
Lemma lem3608305 {A : Type'} (x : A) (s : A -> Prop) : (term65 A x s) = ((term5 A x s) = (@FINITE A s)).
Proof. exact (@lem32 (term5 A x s) (@FINITE A s)). Qed.
Lemma lem3608306 {A : Type'} (x : A) (s : A -> Prop) : (term5 A x s) = (@FINITE A s).
Proof. exact (EQ_MP (@lem3608305 A x s) (@lem3608304 A x s)). Qed.
Lemma lem3608311 {A : Type'} (s : A -> Prop) : term66 A s.
Proof. exact (fun x : A => @lem3608306 A x s). Qed.
Lemma lem3608316 {A : Type'} : term67 A.
Proof. exact (fun s : A -> Prop => @lem3608311 A s). Qed.
