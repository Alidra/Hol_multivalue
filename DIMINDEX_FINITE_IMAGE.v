Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIMINDEX_FINITE_IMAGE_term_abbrevs.
Require Import FINITE_FINITE_IMAGE_spec.
Require Import HAS_SIZE_spec.
Require Import HAS_SIZE_FINITE_IMAGE_spec.
Require Import dimindex_spec.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem7607928 {_100044 : Type'} (s : _100044 -> Prop) : term0 _100044 s.
Proof. exact (@lem3863773 _100044 s). Qed.
Lemma lem7607929 {_100044 : Type'} (s : _100044 -> Prop) : (term0 _100044 s) = (term1 _100044 s).
Proof. exact (eq_refl (term0 _100044 s)). Qed.
Lemma lem7607930 {_100044 : Type'} (s : _100044 -> Prop) : term1 _100044 s.
Proof. exact (EQ_MP (@lem7607929 _100044 s) (@lem7607928 _100044 s)). Qed.
Lemma lem7607931 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : term2 _100044 s n.
Proof. exact (@lem7607930 _100044 s n). Qed.
Lemma lem7607932 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (term2 _100044 s n) = ((@HAS_SIZE _100044 s n) = (term3 _100044 s n)).
Proof. exact (eq_refl (term2 _100044 s n)). Qed.
Lemma lem7607934 {A : Type'} : (@FINITE (finite_image A) (@UNIV (finite_image A))) = ((@FINITE (finite_image A) (@UNIV (finite_image A))) = True).
Proof. exact (@lem7 (@FINITE (finite_image A) (@UNIV (finite_image A)))). Qed.
Lemma lem7607936 {A : Type'} : term4 A.
Proof. exact (@lem7605765 A). Qed.
Lemma lem7607937 {A : Type'} (t : A -> Prop) : term5 A t.
Proof. exact (@lem7607936 A t). Qed.
Lemma lem7607938 {A : Type'} (t : A -> Prop) : (term5 A t) = (term6 A t).
Proof. exact (eq_refl (term5 A t)). Qed.
Lemma lem7607939 {A : Type'} (t : A -> Prop) : term6 A t.
Proof. exact (EQ_MP (@lem7607938 A t) (@lem7607937 A t)). Qed.
Lemma lem7607940 {A : Type'} (s : A -> Prop) : term7 A s.
Proof. exact (@lem7590231 A s). Qed.
Lemma lem7607941 {A : Type'} (s : A -> Prop) : (term7 A s) = ((@dimindex A s) = (term8 A)).
Proof. exact (eq_refl (term7 A s)). Qed.
Lemma lem7607944 {A : Type'} (s : A -> Prop) : (@dimindex A s) = (term8 A).
Proof. exact (EQ_MP (@lem7607941 A s) (@lem7607940 A s)). Qed.
Lemma lem7607945 {A : Type'} (s : type33 A) : (@dimindex (finite_image A) s) = (term9 A).
Proof. exact (@lem7607944 (finite_image A) s). Qed.
Lemma lem7607946 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7607947 {A : Type'} (s : type33 A) : (term10 A s) = (term11 A).
Proof. exact (MK_COMB (@lem7607946) (@lem7607945 A s)). Qed.
Lemma lem7607948 {A : Type'} (t : A -> Prop) : (@dimindex A t) = (@dimindex A t).
Proof. exact (eq_refl (@dimindex A t)). Qed.
Lemma lem7607949 {A : Type'} (s : type33 A) (t : A -> Prop) : ((@dimindex (finite_image A) s) = (@dimindex A t)) = ((term9 A) = (@dimindex A t)).
Proof. exact (MK_COMB (@lem7607947 A s) (@lem7607948 A t)). Qed.
Lemma lem7607950 {A : Type'} (s : type33 A) (t : A -> Prop) : ((term9 A) = (@dimindex A t)) = ((@dimindex (finite_image A) s) = (@dimindex A t)).
Proof. exact (SYM (@lem7607949 A s t)). Qed.
Lemma lem7607954 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term12 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7607955 (p : Prop) (q : Prop) (p' : Prop) : term13 p q p'.
Proof. exact (fun q' : Prop => @lem7607954 p q p' q'). Qed.
Lemma lem7607956 (p : Prop) (q : Prop) : term14 p q.
Proof. exact (fun p' : Prop => @lem7607955 p q p'). Qed.
Lemma lem7607957 {A : Type'} (t : A -> Prop) : term15 A t.
Proof. exact (@lem7607956 (term6 A t) ((term9 A) = (@dimindex A t))). Qed.
Lemma lem7607958 {A : Type'} (t : A -> Prop) (p' : Prop) : term16 A t p'.
Proof. exact (@lem7607957 A t p'). Qed.
Lemma lem7607959 {A : Type'} (t : A -> Prop) (p' : Prop) : (term16 A t p') = (term17 A t p').
Proof. exact (eq_refl (term16 A t p')). Qed.
Lemma lem7607960 {A : Type'} (t : A -> Prop) (p' : Prop) : term17 A t p'.
Proof. exact (EQ_MP (@lem7607959 A t p') (@lem7607958 A t p')). Qed.
Lemma lem7607961 {A : Type'} (t : A -> Prop) (p' : Prop) (q' : Prop) : term18 A t p' q'.
Proof. exact (@lem7607960 A t p' q'). Qed.
Lemma lem7607962 {A : Type'} (t : A -> Prop) (p' : Prop) (q' : Prop) : (term18 A t p' q') = (term19 A t p' q').
Proof. exact (eq_refl (term18 A t p' q')). Qed.
Lemma lem7607963 {A : Type'} (t : A -> Prop) (p' : Prop) (q' : Prop) : term19 A t p' q'.
Proof. exact (EQ_MP (@lem7607962 A t p' q') (@lem7607961 A t p' q')). Qed.
Lemma lem7607965 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (@HAS_SIZE _100044 s n) = (term3 _100044 s n).
Proof. exact (EQ_MP (@lem7607932 _100044 s n) (@lem7607931 _100044 s n)). Qed.
Lemma lem7607966 {A : Type'} (s : type33 A) (n : nat) : (@HAS_SIZE (finite_image A) s n) = (term20 A s n).
Proof. exact (@lem7607965 (finite_image A) s n). Qed.
Lemma lem7607967 {A : Type'} (t : A -> Prop) : (term6 A t) = (term21 A t).
Proof. exact (@lem7607966 A (@UNIV (finite_image A)) (@dimindex A t)). Qed.
Lemma lem7607971 {A : Type'} : (@FINITE (finite_image A) (@UNIV (finite_image A))) = True.
Proof. exact (EQ_MP (@lem7607934 A) (@lem7607927 A)). Qed.
Lemma lem7607972 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7607973 {A : Type'} : (term22 A) = (and True).
Proof. exact (MK_COMB (@lem7607972) (@lem7607971 A)). Qed.
Lemma lem7607976 {A : Type'} (t : A -> Prop) : ((@CARD (finite_image A) (@UNIV (finite_image A))) = (@dimindex A t)) = ((@CARD (finite_image A) (@UNIV (finite_image A))) = (@dimindex A t)).
Proof. exact (eq_refl ((@CARD (finite_image A) (@UNIV (finite_image A))) = (@dimindex A t))). Qed.
Lemma lem7607977 {A : Type'} (t : A -> Prop) : (term21 A t) = (term23 A t).
Proof. exact (MK_COMB (@lem7607973 A) (@lem7607976 A t)). Qed.
Lemma lem7607979 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7607980 {A : Type'} (t : A -> Prop) : (term23 A t) = ((@CARD (finite_image A) (@UNIV (finite_image A))) = (@dimindex A t)).
Proof. exact (@lem7607979 ((@CARD (finite_image A) (@UNIV (finite_image A))) = (@dimindex A t))). Qed.
Lemma lem7607983 {A : Type'} (t : A -> Prop) : (term21 A t) = ((@CARD (finite_image A) (@UNIV (finite_image A))) = (@dimindex A t)).
Proof. exact (TRANS (@lem7607977 A t) (@lem7607980 A t)). Qed.
Lemma lem7607984 {A : Type'} (t : A -> Prop) : (term6 A t) = ((@CARD (finite_image A) (@UNIV (finite_image A))) = (@dimindex A t)).
Proof. exact (TRANS (@lem7607967 A t) (@lem7607983 A t)). Qed.
Lemma lem7607985 {A : Type'} (t : A -> Prop) (q' : Prop) : term24 A t q'.
Proof. exact (@lem7607963 A t ((@CARD (finite_image A) (@UNIV (finite_image A))) = (@dimindex A t)) q'). Qed.
Lemma lem7607986 {A : Type'} (t : A -> Prop) (q' : Prop) : term25 A t q'.
Proof. exact (@lem7607985 A t q' (@lem7607984 A t)). Qed.
Lemma lem7607991 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term26 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem7607992 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term27 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem7607991 _2963 g t e g' t' e'). Qed.
Lemma lem7607993 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term28 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem7607992 _2963 g t e g' t'). Qed.
Lemma lem7607994 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term29 _2963 g t e.
Proof. exact (fun g' : Prop => @lem7607993 _2963 g t e g'). Qed.
Lemma lem7607995 (g : Prop) (t : nat) (e : nat) : term30 g t e.
Proof. exact (@lem7607994 nat g t e). Qed.
Lemma lem7607996 {A : Type'} : term31 A.
Proof. exact (@lem7607995 (@FINITE (finite_image A) (@UNIV (finite_image A))) (@CARD (finite_image A) (@UNIV (finite_image A))) term32). Qed.
Lemma lem7607997 {A : Type'} (g' : Prop) : term33 A g'.
Proof. exact (@lem7607996 A g'). Qed.
Lemma lem7607998 {A : Type'} (g' : Prop) : (term33 A g') = (term34 A g').
Proof. exact (eq_refl (term33 A g')). Qed.
Lemma lem7607999 {A : Type'} (g' : Prop) : term34 A g'.
Proof. exact (EQ_MP (@lem7607998 A g') (@lem7607997 A g')). Qed.
Lemma lem7608000 {A : Type'} (g' : Prop) (t' : nat) : term35 A g' t'.
Proof. exact (@lem7607999 A g' t'). Qed.
Lemma lem7608001 {A : Type'} (g' : Prop) (t' : nat) : (term35 A g' t') = (term36 A g' t').
Proof. exact (eq_refl (term35 A g' t')). Qed.
Lemma lem7608002 {A : Type'} (g' : Prop) (t' : nat) : term36 A g' t'.
Proof. exact (EQ_MP (@lem7608001 A g' t') (@lem7608000 A g' t')). Qed.
Lemma lem7608003 {A : Type'} (g' : Prop) (t' : nat) (e' : nat) : term37 A g' t' e'.
Proof. exact (@lem7608002 A g' t' e'). Qed.
Lemma lem7608004 {A : Type'} (g' : Prop) (t' : nat) (e' : nat) : (term37 A g' t' e') = (term38 A g' t' e').
Proof. exact (eq_refl (term37 A g' t' e')). Qed.
Lemma lem7608005 {A : Type'} (g' : Prop) (t' : nat) (e' : nat) : term38 A g' t' e'.
Proof. exact (EQ_MP (@lem7608004 A g' t' e') (@lem7608003 A g' t' e')). Qed.
Lemma lem7608007 {A : Type'} : (@FINITE (finite_image A) (@UNIV (finite_image A))) = True.
Proof. exact (EQ_MP (@lem7607934 A) (@lem7607927 A)). Qed.
Lemma lem7608008 {A : Type'} (t' : nat) (e' : nat) : term39 A t' e'.
Proof. exact (@lem7608005 A True t' e'). Qed.
Lemma lem7608009 {A : Type'} (t' : nat) (e' : nat) : term40 A t' e'.
Proof. exact (@lem7608008 A t' e' (@lem7608007 A)). Qed.
Lemma lem7608016 {A : Type'} (t : A -> Prop) (h1 : (@CARD (finite_image A) (@UNIV (finite_image A))) = (@dimindex A t)) : (@CARD (finite_image A) (@UNIV (finite_image A))) = (@dimindex A t).
Proof. exact (h1). Qed.
Lemma lem7608017 {A : Type'} (t : A -> Prop) (h1 : (@CARD (finite_image A) (@UNIV (finite_image A))) = (@dimindex A t)) : term41 A t.
Proof. exact (fun h0 : True => @lem7608016 A t h1). Qed.
Lemma lem7608018 {A : Type'} (t : A -> Prop) (e' : nat) : term42 A t e'.
Proof. exact (@lem7608009 A (@dimindex A t) e'). Qed.
Lemma lem7608019 {A : Type'} (e' : nat) (t : A -> Prop) (h1 : (@CARD (finite_image A) (@UNIV (finite_image A))) = (@dimindex A t)) : term43 A t e'.
Proof. exact (@lem7608018 A t e' (@lem7608017 A t h1)). Qed.
Lemma lem7608023 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem7608024 : term44.
Proof. exact (fun h0 : ~ True => @lem7608023). Qed.
Lemma lem7608025 {A : Type'} (t : A -> Prop) (h1 : (@CARD (finite_image A) (@UNIV (finite_image A))) = (@dimindex A t)) : term45 A t.
Proof. exact (@lem7608019 A term32 t h1). Qed.
Lemma lem7608026 {A : Type'} (t : A -> Prop) (h1 : (@CARD (finite_image A) (@UNIV (finite_image A))) = (@dimindex A t)) : (term9 A) = (term46 A t).
Proof. exact (@lem7608025 A t h1 (@lem7608024)). Qed.
Lemma lem7608028 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem7608029 (t2 : nat) (t1 : nat) : (@COND nat True t1 t2) = t1.
Proof. exact (@lem7608028 nat t2 t1). Qed.
Lemma lem7608030 {A : Type'} (t : A -> Prop) : (term46 A t) = (@dimindex A t).
Proof. exact (@lem7608029 term32 (@dimindex A t)). Qed.
Lemma lem7608031 {A : Type'} (t : A -> Prop) (h1 : (@CARD (finite_image A) (@UNIV (finite_image A))) = (@dimindex A t)) : (term9 A) = (@dimindex A t).
Proof. exact (TRANS (@lem7608026 A t h1) (@lem7608030 A t)). Qed.
Lemma lem7608032 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7608033 {A : Type'} (t : A -> Prop) (h1 : (@CARD (finite_image A) (@UNIV (finite_image A))) = (@dimindex A t)) : (term11 A) = (term47 A t).
Proof. exact (MK_COMB (@lem7608032) (@lem7608031 A t h1)). Qed.
Lemma lem7608034 {A : Type'} (t : A -> Prop) : (@dimindex A t) = (@dimindex A t).
Proof. exact (eq_refl (@dimindex A t)). Qed.
Lemma lem7608035 {A : Type'} (t : A -> Prop) (h1 : (@CARD (finite_image A) (@UNIV (finite_image A))) = (@dimindex A t)) : ((term9 A) = (@dimindex A t)) = ((@dimindex A t) = (@dimindex A t)).
Proof. exact (MK_COMB (@lem7608033 A t h1) (@lem7608034 A t)). Qed.
Lemma lem7608037 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7608038 (x : nat) : (x = x) = True.
Proof. exact (@lem7608037 nat x). Qed.
Lemma lem7608039 {A : Type'} (t : A -> Prop) : ((@dimindex A t) = (@dimindex A t)) = True.
Proof. exact (@lem7608038 (@dimindex A t)). Qed.
Lemma lem7608040 {A : Type'} (t : A -> Prop) (h1 : (@CARD (finite_image A) (@UNIV (finite_image A))) = (@dimindex A t)) : ((term9 A) = (@dimindex A t)) = True.
Proof. exact (TRANS (@lem7608035 A t h1) (@lem7608039 A t)). Qed.
Lemma lem7608041 {A : Type'} (t : A -> Prop) : term48 A t.
Proof. exact (fun h0 : (@CARD (finite_image A) (@UNIV (finite_image A))) = (@dimindex A t) => @lem7608040 A t h0). Qed.
Lemma lem7608042 {A : Type'} (t : A -> Prop) : term49 A t.
Proof. exact (@lem7607986 A t True). Qed.
Lemma lem7608043 {A : Type'} (t : A -> Prop) : (term50 A t) = (term51 A t).
Proof. exact (@lem7608042 A t (@lem7608041 A t)). Qed.
Lemma lem7608047 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7608048 {A : Type'} (t : A -> Prop) : (term51 A t) = True.
Proof. exact (@lem7608047 ((@CARD (finite_image A) (@UNIV (finite_image A))) = (@dimindex A t))). Qed.
Lemma lem7608049 {A : Type'} (t : A -> Prop) : (term50 A t) = True.
Proof. exact (TRANS (@lem7608043 A t) (@lem7608048 A t)). Qed.
Lemma lem7608050 {A : Type'} (t : A -> Prop) : True = (term50 A t).
Proof. exact (SYM (@lem7608049 A t)). Qed.
Lemma lem7608051 {A : Type'} (t : A -> Prop) : term50 A t.
Proof. exact (EQ_MP (@lem7608050 A t) (@lem0)). Qed.
Lemma lem7608052 {A : Type'} (t : A -> Prop) : (term9 A) = (@dimindex A t).
Proof. exact (@lem7608051 A t (@lem7607939 A t)). Qed.
Lemma lem7608053 {A : Type'} (s : type33 A) (t : A -> Prop) : (@dimindex (finite_image A) s) = (@dimindex A t).
Proof. exact (EQ_MP (@lem7607950 A s t) (@lem7608052 A t)). Qed.
Lemma lem7608058 {A : Type'} (s : type33 A) : term52 A s.
Proof. exact (fun t : A -> Prop => @lem7608053 A s t). Qed.
Lemma lem7608063 {A : Type'} : term53 A.
Proof. exact (fun s : type33 A => @lem7608058 A s). Qed.
